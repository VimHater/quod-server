// Package llm talks to the DeepSeek chat completions API and wraps the
// prompts used by the prover: splitting input into statements, formalizing
// them in Lean, back-translating, proving with compiler feedback, explaining.
package llm

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/rand/v2"
	"net/http"
	"os"
	"strconv"
	"strings"
	"time"
)

const DefaultBaseURL = "https://api.deepseek.com"

// Model ids (see GET /models).
const (
	ModelFlash = "deepseek-flash"
	ModelPro   = "deepseek-v4-pro"
)

// Effort is DeepSeek's reasoning_effort. EffortNone disables thinking.
type Effort string

const (
	EffortDefault Effort = "" // server default ("high")
	EffortNone    Effort = "none"
	EffortLow     Effort = "low"
	EffortHigh    Effort = "high"
	EffortMax     Effort = "max"
)

// Message is one chat turn. Reasoning from earlier turns is never sent back:
// without tools the API ignores it anyway.
type Message struct {
	Role    string `json:"role"` // "system" | "user" | "assistant" | "tool"
	Content string `json:"content"`
	// ReasoningContent must be sent back on assistant messages when tools
	// are in use (thinking mode); without tools the API ignores it.
	ReasoningContent string     `json:"reasoning_content,omitempty"`
	ToolCalls        []ToolCall `json:"tool_calls,omitempty"`   // assistant: calls requested
	ToolCallID       string     `json:"tool_call_id,omitempty"` // tool: which call this answers
}

// Tool describes a function the model may call (OpenAI-compatible).
type Tool struct {
	Type     string       `json:"type"` // "function"
	Function ToolFunction `json:"function"`
}

// ToolFunction is a tool's name, description and JSON-schema parameters.
type ToolFunction struct {
	Name        string          `json:"name"`
	Description string          `json:"description"`
	Parameters  json.RawMessage `json:"parameters"`
}

// ToolCall is one call the model asked for. Arguments is a JSON object as text.
type ToolCall struct {
	ID       string `json:"id"`
	Type     string `json:"type"` // "function"
	Function struct {
		Name      string `json:"name"`
		Arguments string `json:"arguments"`
	} `json:"function"`
}

// ToolResult builds the message answering a call.
func ToolResult(callID, content string) Message {
	return Message{Role: "tool", ToolCallID: callID, Content: content}
}

func System(s string) Message    { return Message{Role: "system", Content: s} }
func User(s string) Message      { return Message{Role: "user", Content: s} }
func Assistant(s string) Message { return Message{Role: "assistant", Content: s} }

// Request is one chat completion call.
type Request struct {
	Model       string
	Messages    []Message
	Effort      Effort
	MaxTokens   int      // 0 = server default (64K in thinking mode)
	JSON        bool     // response_format json_object; prompt must mention "json"
	Temperature *float64 // ignored by the API in thinking mode
	// Tools the model may call; the response then may carry ToolCalls
	// (FinishReason "tool_calls") instead of a final answer.
	Tools []Tool
	// OnProgress, if set, makes the call stream and is invoked as output
	// arrives (from the HTTP goroutine; keep it fast). The Response is the
	// same as without streaming.
	OnProgress func(Progress)
}

// Progress reports streamed output so far. Chunks approximate tokens (the
// API sends about one token per chunk; exact counts arrive in Usage).
type Progress struct {
	ReasoningChunks int
	ContentChunks   int
}

// Usage is token accounting for one call.
type Usage struct {
	PromptTokens          int `json:"prompt_tokens"`
	CompletionTokens      int `json:"completion_tokens"`
	TotalTokens           int `json:"total_tokens"`
	PromptCacheHitTokens  int `json:"prompt_cache_hit_tokens"`
	PromptCacheMissTokens int `json:"prompt_cache_miss_tokens"`
	CompletionDetails     *struct {
		ReasoningTokens int `json:"reasoning_tokens"`
	} `json:"completion_tokens_details,omitempty"`
}

// ReasoningTokens is the part of CompletionTokens spent thinking.
func (u Usage) ReasoningTokens() int {
	if u.CompletionDetails == nil {
		return 0
	}
	return u.CompletionDetails.ReasoningTokens
}

// Response is the result of one call.
type Response struct {
	Model        string
	Content      string
	Reasoning    string // chain of thought (thinking mode only)
	ToolCalls    []ToolCall
	FinishReason string // stop | length | tool_calls | content_filter | ...
	Usage        Usage
	CostUSD      float64
	Latency      time.Duration
}

// Chatter is the interface the prompt layer depends on (fake it in tests).
type Chatter interface {
	Chat(ctx context.Context, req Request) (*Response, error)
}

// APIError is a non-2xx response or an unusable completion.
type APIError struct {
	Status    int // HTTP status; 0 for in-body failures
	Message   string
	Retryable bool
}

func (e *APIError) Error() string {
	if e.Status == 0 {
		return "deepseek: " + e.Message
	}
	return fmt.Sprintf("deepseek: HTTP %d: %s", e.Status, e.Message)
}

// ErrTruncated means the model hit max_tokens before finishing.
var ErrTruncated = errors.New("deepseek: response truncated (finish_reason=length)")

// Client is a minimal DeepSeek client using net/http.
type Client struct {
	BaseURL    string
	APIKey     string
	HTTP       *http.Client
	MaxRetries int           // retries for 429/5xx/network errors; default 4
	RetryBase  time.Duration // first backoff; default 2s
	Pricing    Pricing       // for Response.CostUSD; default DefaultPricing
	Now        func() time.Time
}

// NewClient returns a client for apiKey with defaults.
func NewClient(apiKey string) *Client {
	return &Client{
		BaseURL: DefaultBaseURL,
		APIKey:  apiKey,
		// No overall timeout: thinking can take minutes and queued requests
		// stream keep-alive lines. Bound calls with ctx instead.
		HTTP:       &http.Client{},
		MaxRetries: 4,
		RetryBase:  2 * time.Second,
		Pricing:    DefaultPricing,
		Now:        time.Now,
	}
}

// NewClientFromEnv reads LLM_API_KEY / LLM_BASE_URL, falling back to
// DEEPSEEK_API_KEY / DEEPSEEK_BASE_URL. Any OpenAI-compatible endpoint
// works (e.g. a local 9router at http://localhost:20128/v1).
func NewClientFromEnv() (*Client, error) {
	key := strings.TrimSpace(firstEnv("LLM_API_KEY", "DEEPSEEK_API_KEY"))
	if key == "" {
		return nil, errors.New("LLM_API_KEY (or DEEPSEEK_API_KEY) is not set")
	}
	c := NewClient(key)
	if u := strings.TrimSpace(firstEnv("LLM_BASE_URL", "DEEPSEEK_BASE_URL")); u != "" {
		c.BaseURL = strings.TrimRight(u, "/")
	}
	return c, nil
}

func firstEnv(names ...string) string {
	for _, n := range names {
		if v := os.Getenv(n); v != "" {
			return v
		}
	}
	return ""
}

// usesMaxTokens reports whether model takes the legacy max_tokens field.
// OpenAI reasoning models (gpt-5, o-series) reject it and require
// max_completion_tokens instead.
func usesMaxTokens(model string) bool {
	return strings.HasPrefix(strings.ToLower(model), "deepseek")
}

type wireRequest struct {
	Model           string          `json:"model"`
	Messages        []Message       `json:"messages"`
	Tools           []Tool          `json:"tools,omitempty"`
	ReasoningEffort Effort          `json:"reasoning_effort,omitempty"`
	MaxTokens       int             `json:"max_tokens,omitempty"`
	MaxCompletion   int             `json:"max_completion_tokens,omitempty"`
	ResponseFormat  *responseFormat `json:"response_format,omitempty"`
	Temperature     *float64        `json:"temperature,omitempty"`
	Stream          bool            `json:"stream"`
	StreamOptions   *streamOptions  `json:"stream_options,omitempty"`
}

type streamOptions struct {
	IncludeUsage bool `json:"include_usage"`
}

type responseFormat struct {
	Type string `json:"type"`
}

type wireResponse struct {
	Model   string `json:"model"`
	Choices []struct {
		Message struct {
			Content          *string    `json:"content"`
			ReasoningContent *string    `json:"reasoning_content"`
			ToolCalls        []ToolCall `json:"tool_calls"`
		} `json:"message"`
		FinishReason string `json:"finish_reason"`
	} `json:"choices"`
	Usage Usage `json:"usage"`
}

// Chat performs one completion with retries on transient failures.
func (c *Client) Chat(ctx context.Context, req Request) (*Response, error) {
	if req.Model == "" {
		return nil, errors.New("deepseek: model not set")
	}
	wr := wireRequest{
		Model:           req.Model,
		Messages:        req.Messages,
		ReasoningEffort: req.Effort,
		Temperature:     req.Temperature,
		Tools:           req.Tools,
	}
	if usesMaxTokens(req.Model) {
		wr.MaxTokens = req.MaxTokens
	} else {
		wr.MaxCompletion = req.MaxTokens
	}
	if req.JSON {
		wr.ResponseFormat = &responseFormat{Type: "json_object"}
	}
	if req.OnProgress != nil {
		wr.Stream = true
		wr.StreamOptions = &streamOptions{IncludeUsage: true}
	}
	body, err := json.Marshal(wr)
	if err != nil {
		return nil, err
	}

	maxRetries := c.MaxRetries
	var lastErr error
	for attempt := 0; ; attempt++ {
		resp, retryAfter, err := c.once(ctx, body, req.OnProgress)
		if err == nil || errors.Is(err, ErrTruncated) {
			// Truncation is not transient; return the partial response so the
			// caller still sees its cost and can decide what to do.
			return resp, err
		}
		lastErr = err
		var ae *APIError
		retryable := ctx.Err() == nil && (!errors.As(err, &ae) || ae.Retryable)
		if !retryable || attempt >= maxRetries {
			return nil, lastErr
		}
		wait := retryAfter
		if wait == 0 {
			base := c.RetryBase
			if base == 0 {
				base = 2 * time.Second
			}
			wait = base << attempt
			wait += time.Duration(rand.Int64N(int64(wait)/2 + 1)) // jitter
		}
		select {
		case <-time.After(wait):
		case <-ctx.Done():
			return nil, fmt.Errorf("%w (last error: %v)", ctx.Err(), lastErr)
		}
	}
}

func (c *Client) once(ctx context.Context, body []byte, onProgress func(Progress)) (*Response, time.Duration, error) {
	now := c.Now
	if now == nil {
		now = time.Now
	}
	start := now()
	hreq, err := http.NewRequestWithContext(ctx, http.MethodPost, strings.TrimRight(c.BaseURL, "/")+"/chat/completions", bytes.NewReader(body))
	if err != nil {
		return nil, 0, err
	}
	hreq.Header.Set("Content-Type", "application/json")
	if onProgress != nil {
		hreq.Header.Set("Accept", "text/event-stream")
	} else {
		hreq.Header.Set("Accept", "application/json")
	}
	hreq.Header.Set("Authorization", "Bearer "+c.APIKey)

	hc := c.HTTP
	if hc == nil {
		hc = http.DefaultClient
	}
	hresp, err := hc.Do(hreq)
	if err != nil {
		return nil, 0, err // network error: retryable (unless ctx is done)
	}
	defer hresp.Body.Close()

	if hresp.StatusCode/100 != 2 {
		raw, _ := io.ReadAll(io.LimitReader(hresp.Body, 1<<20))
		ae := &APIError{Status: hresp.StatusCode, Message: errorMessage(raw)}
		switch hresp.StatusCode {
		case http.StatusTooManyRequests, http.StatusInternalServerError, http.StatusBadGateway,
			http.StatusServiceUnavailable, http.StatusGatewayTimeout:
			ae.Retryable = true
		}
		return nil, retryAfter(hresp.Header.Get("Retry-After")), ae
	}

	var r *Response
	if onProgress != nil {
		r, err = readStream(hresp.Body, onProgress)
	} else {
		r, err = readJSON(hresp.Body)
	}
	if err != nil {
		return nil, 0, err
	}
	r.Latency = now().Sub(start)
	r.CostUSD = c.pricing().Cost(r.Model, r.Usage, start)

	switch r.FinishReason {
	case "insufficient_system_resource", "aborted":
		return nil, 0, &APIError{Message: "finish_reason=" + r.FinishReason, Retryable: true}
	case "length":
		return r, 0, ErrTruncated
	}
	return r, 0, nil
}

func readJSON(body io.Reader) (*Response, error) {
	raw, err := io.ReadAll(io.LimitReader(body, 32<<20))
	if err != nil {
		return nil, err
	}
	// Body may be preceded by keep-alive blank lines; json skips whitespace.
	var wr wireResponse
	if err := json.Unmarshal(bytes.TrimSpace(raw), &wr); err != nil {
		return nil, &APIError{Message: fmt.Sprintf("decoding response: %v", err), Retryable: true}
	}
	if len(wr.Choices) == 0 {
		return nil, &APIError{Message: "response has no choices", Retryable: true}
	}
	ch := wr.Choices[0]
	r := &Response{Model: wr.Model, FinishReason: ch.FinishReason, Usage: wr.Usage, ToolCalls: ch.Message.ToolCalls}
	if ch.Message.Content != nil {
		r.Content = *ch.Message.Content
	}
	if ch.Message.ReasoningContent != nil {
		r.Reasoning = *ch.Message.ReasoningContent
	}
	return r, nil
}

type streamChunk struct {
	Model   string `json:"model"`
	Choices []struct {
		Delta struct {
			Content          *string `json:"content"`
			ReasoningContent *string `json:"reasoning_content"`
			ToolCalls        []struct {
				Index    int    `json:"index"`
				ID       string `json:"id"`
				Type     string `json:"type"`
				Function struct {
					Name      string `json:"name"`
					Arguments string `json:"arguments"`
				} `json:"function"`
			} `json:"tool_calls"`
		} `json:"delta"`
		FinishReason *string `json:"finish_reason"`
	} `json:"choices"`
	Usage *Usage `json:"usage"`
}

// readStream assembles a Response from an SSE stream ("data: {...}" lines,
// ": keep-alive" comments, terminated by "data: [DONE]").
func readStream(body io.Reader, onProgress func(Progress)) (*Response, error) {
	sc := bufio.NewScanner(body)
	sc.Buffer(make([]byte, 64<<10), 8<<20)
	var content, reasoning strings.Builder
	var calls []ToolCall
	var p Progress
	r := &Response{}
	done := false
	for sc.Scan() {
		line := sc.Text()
		data, ok := strings.CutPrefix(line, "data:")
		if !ok {
			continue // blank separators and ": keep-alive" comments
		}
		data = strings.TrimSpace(data)
		if data == "[DONE]" {
			done = true
			break
		}
		var ch streamChunk
		if err := json.Unmarshal([]byte(data), &ch); err != nil {
			return nil, &APIError{Message: fmt.Sprintf("decoding stream chunk: %v", err), Retryable: true}
		}
		if ch.Model != "" {
			r.Model = ch.Model
		}
		if ch.Usage != nil {
			r.Usage = *ch.Usage
		}
		for _, c := range ch.Choices {
			if d := c.Delta.ReasoningContent; d != nil && *d != "" {
				reasoning.WriteString(*d)
				p.ReasoningChunks++
			}
			if d := c.Delta.Content; d != nil && *d != "" {
				content.WriteString(*d)
				p.ContentChunks++
			}
			// Tool calls stream as fragments keyed by index: the first carries
			// id and name, later ones append to the arguments string.
			for _, tc := range c.Delta.ToolCalls {
				for len(calls) <= tc.Index {
					calls = append(calls, ToolCall{Type: "function"})
				}
				cur := &calls[tc.Index]
				if tc.ID != "" {
					cur.ID = tc.ID
				}
				if tc.Type != "" {
					cur.Type = tc.Type
				}
				cur.Function.Name += tc.Function.Name
				cur.Function.Arguments += tc.Function.Arguments
				p.ContentChunks++
			}
			if c.FinishReason != nil && *c.FinishReason != "" {
				r.FinishReason = *c.FinishReason
			}
		}
		onProgress(p)
	}
	if err := sc.Err(); err != nil {
		return nil, err // connection dropped mid-stream: retryable
	}
	if !done && r.FinishReason == "" {
		return nil, &APIError{Message: "stream ended early", Retryable: true}
	}
	r.Content, r.Reasoning, r.ToolCalls = content.String(), reasoning.String(), calls
	return r, nil
}

func (c *Client) pricing() Pricing {
	if c.Pricing == nil {
		return DefaultPricing
	}
	return c.Pricing
}

func errorMessage(raw []byte) string {
	var e struct {
		Error struct {
			Message string `json:"message"`
			Type    string `json:"type"`
		} `json:"error"`
	}
	if json.Unmarshal(bytes.TrimSpace(raw), &e) == nil && e.Error.Message != "" {
		return e.Error.Message
	}
	s := strings.TrimSpace(string(raw))
	if len(s) > 500 {
		s = s[:500] + "..."
	}
	return s
}

func retryAfter(h string) time.Duration {
	if h == "" {
		return 0
	}
	if secs, err := strconv.Atoi(h); err == nil && secs >= 0 {
		return time.Duration(secs) * time.Second
	}
	if t, err := http.ParseTime(h); err == nil {
		return max(time.Until(t), 0)
	}
	return 0
}
