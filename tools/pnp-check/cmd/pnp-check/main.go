// pnp-check: a checker front end bound to one exact state of this fork (addison-jpg/pnp-general).
//
// Stage 1 (this file): it knows what it is bound to, and refuses any tree that is not that.
//
//	pnp-check version             what this build is bound to
//	pnp-check verify-tree [DIR]   exit 0 if DIR (default: the current directory) is byte for byte
//	                              the pinned fork; exit 1 and list every difference otherwise
//
// Exit codes follow the checker's: 0 ok, 1 refused, 3 could not run (usage, unreadable tree).
package main

import (
	_ "embed"
	"fmt"
	"os"

	"github.com/addison-jpg/pnp-general/tools/pnp-check/internal/pins"
)

// Version is set by the build (-ldflags "-X main.Version=...").
var Version = "0.1.0-stage1"

//go:embed pins.json
var pinsJSON []byte

func fault(format string, a ...any) {
	fmt.Fprintf(os.Stderr, "CHECKER FAULT: "+format+"\n", a...)
	os.Exit(3)
}

func main() {
	p, err := pins.Parse(pinsJSON)
	if err != nil {
		fault("the pins built into this executable are unreadable: %v", err)
	}
	if len(os.Args) < 2 {
		fault("usage: pnp-check version | verify-tree [DIR]")
	}
	switch os.Args[1] {
	case "version":
		fmt.Printf("pnp-check %s\nfork      %s\ncommit    %s\ntoolchain %s\npinned    %d files\ndigest    %s\n",
			Version, p.Fork, p.Commit, p.Toolchain, len(p.Files), p.Digest())
	case "verify-tree":
		dir := "."
		if len(os.Args) > 2 {
			dir = os.Args[2]
		}
		probs, err := p.Verify(dir)
		if err != nil {
			fault("cannot read the tree %s: %v", dir, err)
		}
		if len(probs) > 0 {
			for _, pr := range probs {
				fmt.Println("REFUSED " + pr.String())
			}
			fmt.Printf("REFUSED (not-this-fork): %d difference(s) from %s at %s; nothing was judged\n", len(probs), p.Fork, shortCommit(p.Commit))
			os.Exit(1)
		}
		fmt.Printf("OK this tree is %s at %s (%d pinned files, digest %.16s)\n", p.Fork, shortCommit(p.Commit), len(p.Files), p.Digest())
	default:
		fault("unknown command %q (version | verify-tree [DIR])", os.Args[1])
	}
}

func shortCommit(c string) string {
	if len(c) > 12 {
		return c[:12]
	}
	return c
}
