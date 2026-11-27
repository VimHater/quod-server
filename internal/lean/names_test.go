package lean

import (
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

var testNames = []string{
	"EuclideanGeometry.angle_eq_angle_of_dist_eq",
	"EuclideanGeometry.angle_comm",
	"EuclideanGeometry.angle_add_angle_add_angle_eq_pi",
	"EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi",
	"InnerProductGeometry.angle_comm",
	"Nat.dvd_of_mod_eq_zero",
	"Int.emod_emod_of_dvd",
	"mul_le_mul_right",
	"mul_le_mul_left",
	"mul_lt_mul_of_pos_right",
	"Real.sqrt_nonneg",
	"sq_nonneg",
	// generated declarations, never suggested
	"Nat.dvd_of_mod_eq_zero.eq_1",
	"Foo.match_1",
	"Foo.proof_2",
	"Foo.mk.injEq",
	"Foo.rec",
	"Foo._unfold",
}

func TestNameIndexDropsGenerated(t *testing.T) {
	x := NewNameIndex(testNames)
	for _, n := range []string{"Foo.match_1", "Foo.proof_2", "Foo.mk.injEq", "Foo.rec", "Foo._unfold", "Nat.dvd_of_mod_eq_zero.eq_1"} {
		if x.Has(n) {
			t.Errorf("generated name %q indexed", n)
		}
	}
	if !x.Has("sq_nonneg") || !x.Has("_root_.sq_nonneg") {
		t.Error("real name missing")
	}
	if x.Len() != 12 {
		t.Errorf("Len = %d, want 12", x.Len())
	}
}

func TestSimilar(t *testing.T) {
	x := NewNameIndex(testNames)
	for _, c := range []struct{ query, want string }{
		// the guesses gpt-6-luna made for the isosceles theorem
		{"EuclideanGeometry.angle_eq_of_dist_eq", "EuclideanGeometry.angle_eq_angle_of_dist_eq"},
		{"EuclideanGeometry.angle_eq_of_dist_eq_of_dist_eq", "EuclideanGeometry.angle_eq_angle_of_dist_eq"},
		// right lemma, wrong namespace
		{"Int.dvd_of_mod_eq_zero", "Nat.dvd_of_mod_eq_zero"},
		{"dvd_of_mod_eq_zero", "Nat.dvd_of_mod_eq_zero"},
		// typo
		{"mul_le_mul_rigth", "mul_le_mul_right"},
		{"Real.sqrt_nonnegative", "Real.sqrt_nonneg"},
	} {
		got := x.Similar(c.query, 3)
		if len(got) == 0 || got[0] != c.want {
			t.Errorf("Similar(%q) = %v, want %q first", c.query, got, c.want)
		}
	}
	// Same last component: prefer the query's namespace.
	if got := x.Similar("EuclideanGeometry.angle_commm", 2); got[0] != "EuclideanGeometry.angle_comm" {
		t.Errorf("namespace preference: %v", got)
	}
	if got := x.Similar("completely_unrelated_thing_xyz", 3); len(got) != 0 {
		t.Errorf("unrelated query matched %v", got)
	}
	if got := x.Similar("sq_nonneg", 3); len(got) > 0 && got[0] == "sq_nonneg" {
		t.Error("query itself suggested")
	}
}

func TestLoadNameIndex(t *testing.T) {
	p := filepath.Join(t.TempDir(), "names.txt")
	if err := os.WriteFile(p, []byte(strings.Join(testNames, "\n")+"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	x, err := LoadNameIndex(p)
	if err != nil || x.Len() != 12 {
		t.Fatalf("LoadNameIndex: %v, len %d", err, x.Len())
	}
}

func TestUnknownIdents(t *testing.T) {
	mk := func(data string) Diagnostic { return diagnose(Message{Severity: "error", Data: data}) }
	ds := []Diagnostic{
		mk("Unknown identifier `EuclideanGeometry.angle_eq_of_dist_eq`"),
		mk("unknown constant 'Nat.foo_bar'"),
		mk("Unknown identifier `EuclideanGeometry.angle_eq_of_dist_eq`"), // duplicate
		mk("linarith failed to find a contradiction"),
		mk("unknown identifier '«weird name»'"),
	}
	got := UnknownIdents(ds)
	want := []string{"EuclideanGeometry.angle_eq_of_dist_eq", "Nat.foo_bar"}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("UnknownIdents = %v, want %v", got, want)
	}
}
