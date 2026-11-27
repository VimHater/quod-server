package main

import (
	"fmt"
	"os"
	"strings"
)

// modelRef is a model id plus the endpoint that serves it. Empty URL means
// the default endpoint (LLM_BASE_URL / DEEPSEEK_BASE_URL).
type modelRef struct {
	Model    string
	Endpoint string // name after '@', "" for the default
	URL, Key string
}

func (m modelRef) String() string {
	if m.Endpoint == "" {
		return m.Model
	}
	return m.Model + "@" + m.Endpoint
}

// parseModelRef reads "model" or "model@name". A named endpoint is
// configured in the environment / .env:
//
//	LLM_ENDPOINT_LOCAL=http://localhost:20128/v1
//	LLM_ENDPOINT_LOCAL_KEY=sk-...
func parseModelRef(s string) (modelRef, error) {
	s = strings.TrimSpace(s)
	model, name, found := strings.Cut(s, "@")
	if model == "" {
		return modelRef{}, fmt.Errorf("empty model in %q", s)
	}
	if !found {
		return modelRef{Model: model}, nil
	}
	env := "LLM_ENDPOINT_" + strings.ToUpper(strings.NewReplacer("-", "_", ".", "_").Replace(name))
	url := strings.TrimSpace(os.Getenv(env))
	if url == "" {
		return modelRef{}, fmt.Errorf("model %q: endpoint %q is not configured (set %s and %s_KEY in .env)", s, name, env, env)
	}
	return modelRef{Model: model, Endpoint: name, URL: url, Key: strings.TrimSpace(os.Getenv(env + "_KEY"))}, nil
}
