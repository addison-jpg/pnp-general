package pins

import (
	"os"
	"path/filepath"
	"runtime"
	"testing"
)

func write(t *testing.T, root, rel, body string) {
	t.Helper()
	full := filepath.Join(root, filepath.FromSlash(rel))
	if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(full, []byte(body), 0o644); err != nil {
		t.Fatal(err)
	}
}

func tree(t *testing.T) string {
	root := t.TempDir()
	write(t, root, "tools/check-lean.mjs", "checker")
	write(t, root, "lean/CheckLemma.lean", "verifier")
	write(t, root, "lean/lakefile.toml", "lake")
	write(t, root, "lean/lake-manifest.json", "{}")
	write(t, root, "lean/lean-toolchain", "leanprover/lean4:v4.36.0\n")
	write(t, root, "lean/PEqualNP/Defs.lean", "import PEqualNP.Defs.Base")
	write(t, root, "lean/PEqualNP/Defs/Base.lean", "def a := 1")
	write(t, root, "lean/PEqualNP/Defs/Sub/More.lean", "def b := 2")
	return root
}

func pinned(t *testing.T, root string) *Pins {
	p, err := Make(root, "o/r", "abc")
	if err != nil {
		t.Fatal(err)
	}
	return p
}

func kinds(ps []Problem) string {
	s := ""
	for _, p := range ps {
		s += p.String() + ";"
	}
	return s
}

func TestCleanTreeVerifies(t *testing.T) {
	root := tree(t)
	p := pinned(t, root)
	if probs, err := p.Verify(root); err != nil || len(probs) != 0 {
		t.Fatalf("clean tree refused: %v %v", err, kinds(probs))
	}
	if p.Toolchain != "leanprover/lean4:v4.36.0" {
		t.Fatalf("toolchain %q", p.Toolchain)
	}
}

func TestChangedDefinitionIsRefused(t *testing.T) {
	root := tree(t)
	p := pinned(t, root)
	write(t, root, "lean/PEqualNP/Defs/Base.lean", "def a := 2") // a definition quietly changed
	probs, _ := p.Verify(root)
	if kinds(probs) != "changed lean/PEqualNP/Defs/Base.lean;" {
		t.Fatalf("got %s", kinds(probs))
	}
}

func TestOneByteInTheVerifierIsRefused(t *testing.T) {
	root := tree(t)
	p := pinned(t, root)
	write(t, root, "lean/CheckLemma.lean", "verifier ")
	probs, _ := p.Verify(root)
	if kinds(probs) != "changed lean/CheckLemma.lean;" {
		t.Fatalf("got %s", kinds(probs))
	}
}

func TestExtraFileInDefsIsRefused(t *testing.T) {
	root := tree(t)
	p := pinned(t, root)
	write(t, root, "lean/PEqualNP/Defs/Evil.lean", "def a := 3")
	write(t, root, "lean/PEqualNP/Defs/notes.txt", "x") // any extension
	probs, _ := p.Verify(root)
	if kinds(probs) != "extra lean/PEqualNP/Defs/Evil.lean;extra lean/PEqualNP/Defs/notes.txt;" {
		t.Fatalf("got %s", kinds(probs))
	}
}

func TestMissingFileIsRefused(t *testing.T) {
	root := tree(t)
	p := pinned(t, root)
	if err := os.Remove(filepath.Join(root, "lean", "PEqualNP", "Defs", "Sub", "More.lean")); err != nil {
		t.Fatal(err)
	}
	probs, _ := p.Verify(root)
	if kinds(probs) != "missing lean/PEqualNP/Defs/Sub/More.lean;" {
		t.Fatalf("got %s", kinds(probs))
	}
}

func TestLakefileLeanBesideTomlIsRefused(t *testing.T) {
	root := tree(t)
	p := pinned(t, root)
	write(t, root, "lean/lakefile.lean", "import Lake")
	probs, _ := p.Verify(root)
	if kinds(probs) != "forbidden lean/lakefile.lean;" {
		t.Fatalf("got %s", kinds(probs))
	}
}

func TestCheckerSuiteDirectoryAppearingIsRefused(t *testing.T) {
	root := tree(t)
	p := pinned(t, root)
	write(t, root, "lean/CheckerSuite/Fake.lean", "x")
	probs, _ := p.Verify(root)
	if kinds(probs) != "extra lean/CheckerSuite/Fake.lean;" {
		t.Fatalf("got %s", kinds(probs))
	}
}

func TestSymlinkInsteadOfFileIsRefused(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("symlinks need privileges on Windows")
	}
	root := tree(t)
	p := pinned(t, root)
	target := filepath.Join(root, "elsewhere.lean")
	if err := os.WriteFile(target, []byte("def a := 1"), 0o644); err != nil { // same bytes as Base.lean
		t.Fatal(err)
	}
	base := filepath.Join(root, "lean", "PEqualNP", "Defs", "Base.lean")
	os.Remove(base)
	if err := os.Symlink(target, base); err != nil {
		t.Fatal(err)
	}
	probs, _ := p.Verify(root)
	if kinds(probs) != "not-a-plain-file lean/PEqualNP/Defs/Base.lean;" {
		t.Fatalf("got %s", kinds(probs))
	}
}

func TestDigestChangesWithAnyPin(t *testing.T) {
	root := tree(t)
	a := pinned(t, root).Digest()
	write(t, root, "lean/PEqualNP/Defs/Base.lean", "def a := 9")
	if b := pinned(t, root).Digest(); a == b {
		t.Fatal("digest did not change")
	}
}
