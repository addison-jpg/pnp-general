// Package pins binds an executable to one exact state of this fork.
//
// The verdict of the checker is made by lean/CheckLemma.lean, read against the definitions root
// lean/PEqualNP/Defs, built by the toolchain and Mathlib that lean/lean-toolchain and
// lean/lake-manifest.json name, and driven by tools/check-lean.mjs. If any of those differ from
// what the executable was built from, a verdict it printed would not be a verdict of THIS fork.
// So the executable carries the SHA-256 of every one of those files, and refuses a tree that is
// not byte for byte the same set of files: changed, missing, extra, or not a plain file.
package pins

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// Entry is one pinned file: its slash path below the tree root and the SHA-256 of its raw bytes.
type Entry struct {
	Path   string `json:"path"`
	SHA256 string `json:"sha256"`
}

// Pins is everything an executable is bound to.
type Pins struct {
	Fork      string  `json:"fork"`      // owner/repo the pins were taken from
	Commit    string  `json:"commit"`    // commit they were taken from (informational: the hashes are what bind)
	Toolchain string  `json:"toolchain"` // contents of lean/lean-toolchain
	Files     []Entry `json:"files"`     // sorted by path
}

// Files are single files the verdict depends on. Dirs are directories of which EVERY file, of any
// extension, is pinned: a stray extra file there would be read as a definition. Forbidden paths
// must not exist (the checker faults on a lakefile.lean beside the committed lakefile.toml).
var (
	Files = []string{
		"tools/check-lean.mjs",
		"lean/CheckLemma.lean",
		"lean/lakefile.toml",
		"lean/lake-manifest.json",
		"lean/lean-toolchain",
		"lean/PEqualNP/Defs.lean",
	}
	Dirs      = []string{"lean/PEqualNP/Defs", "lean/CheckerSuite"}
	Forbidden = []string{"lean/lakefile.lean"}
)

// Problem is one way a tree differs from the pins.
type Problem struct {
	Kind string // changed, missing, extra, not-a-plain-file, forbidden
	Path string
}

func (p Problem) String() string { return p.Kind + " " + p.Path }

func hashFile(path string) (string, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	h := sha256.Sum256(b)
	return hex.EncodeToString(h[:]), nil
}

// plain reports whether path is a regular file and not a symlink or anything else.
func plain(path string) (exists, ok bool) {
	st, err := os.Lstat(path)
	if err != nil {
		return false, false
	}
	return true, st.Mode().IsRegular()
}

// scan reads the tree at root and returns the hash of every file the pins cover, plus the
// problems that are visible from the tree alone (not-a-plain-file, forbidden).
func scan(root string) (map[string]string, []Problem, error) {
	got := map[string]string{}
	var probs []Problem
	add := func(rel string) error {
		full := filepath.Join(root, filepath.FromSlash(rel))
		exists, ok := plain(full)
		if !exists {
			return nil
		}
		if !ok {
			probs = append(probs, Problem{"not-a-plain-file", rel})
			return nil
		}
		h, err := hashFile(full)
		if err != nil {
			return err
		}
		got[rel] = h
		return nil
	}
	for _, f := range Files {
		if err := add(f); err != nil {
			return nil, nil, err
		}
	}
	for _, d := range Dirs {
		base := filepath.Join(root, filepath.FromSlash(d))
		if _, err := os.Lstat(base); err != nil {
			continue
		}
		err := filepath.WalkDir(base, func(p string, de fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if de.IsDir() {
				return nil
			}
			rel, err := filepath.Rel(root, p)
			if err != nil {
				return err
			}
			return add(filepath.ToSlash(rel))
		})
		if err != nil {
			return nil, nil, err
		}
	}
	for _, f := range Forbidden {
		if exists, _ := plain(filepath.Join(root, filepath.FromSlash(f))); exists {
			probs = append(probs, Problem{"forbidden", f})
		}
	}
	return got, probs, nil
}

// Make pins the tree at root.
func Make(root, fork, commit string) (*Pins, error) {
	got, probs, err := scan(root)
	if err != nil {
		return nil, err
	}
	if len(probs) > 0 {
		return nil, fmt.Errorf("cannot pin this tree: %v", probs)
	}
	tc, err := os.ReadFile(filepath.Join(root, "lean", "lean-toolchain"))
	if err != nil {
		return nil, err
	}
	p := &Pins{Fork: fork, Commit: commit, Toolchain: strings.TrimSpace(string(tc))}
	for path, h := range got {
		p.Files = append(p.Files, Entry{path, h})
	}
	sort.Slice(p.Files, func(i, j int) bool { return p.Files[i].Path < p.Files[j].Path })
	return p, nil
}

// Verify compares the tree at root with the pins and returns every difference, sorted.
func (p *Pins) Verify(root string) ([]Problem, error) {
	got, probs, err := scan(root)
	if err != nil {
		return nil, err
	}
	want := map[string]string{}
	for _, e := range p.Files {
		want[e.Path] = e.SHA256
	}
	for path, h := range want {
		g, ok := got[path]
		switch {
		case !ok:
			// A path that failed the plain-file test is reported once, as that.
			dup := false
			for _, q := range probs {
				if q.Path == path {
					dup = true
				}
			}
			if !dup {
				probs = append(probs, Problem{"missing", path})
			}
		case g != h:
			probs = append(probs, Problem{"changed", path})
		}
	}
	for path := range got {
		if _, ok := want[path]; !ok {
			probs = append(probs, Problem{"extra", path})
		}
	}
	sort.Slice(probs, func(i, j int) bool {
		if probs[i].Path != probs[j].Path {
			return probs[i].Path < probs[j].Path
		}
		return probs[i].Kind < probs[j].Kind
	})
	return probs, nil
}

// Digest is one SHA-256 over the whole pin set, to quote in a message or on the board.
func (p *Pins) Digest() string {
	var b strings.Builder
	for _, e := range p.Files {
		b.WriteString(e.SHA256 + "  " + e.Path + "\n")
	}
	h := sha256.Sum256([]byte(b.String()))
	return hex.EncodeToString(h[:])
}

// Parse reads pins from JSON.
func Parse(b []byte) (*Pins, error) {
	var p Pins
	if err := json.Unmarshal(b, &p); err != nil {
		return nil, err
	}
	if len(p.Files) == 0 {
		return nil, fmt.Errorf("no files are pinned")
	}
	return &p, nil
}
