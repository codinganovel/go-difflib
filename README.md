go-difflib
==========

THIS PACKAGE IS NO LONGER MAINTAINED BY THE ORIGINAL AUTHOR.

At this point, I have no longer the time nor the interest to work on go-difflib. I apologize for the inconvenience.

**UPDATE**: This fork is now minimally maintained as I've started using it in a personal project. Basic functionality and Go compatibility will be preserved. Recent updates add ndiff options, byte-oriented adapters, and intraline hints with junk filters.

[![GoDoc](https://godoc.org/github.com/codinganovel/go-difflib/difflib?status.svg)](https://godoc.org/github.com/codinganovel/go-difflib/difflib)

Go-difflib is a partial port of python 3 difflib package. Its main goal
was to make unified and context diff available in pure Go, mostly for
testing purposes.

The following class and functions (and related tests) have be ported:

* `SequenceMatcher`
* `unified_diff()`
* `context_diff()`
* `get_close_matches()` (as `GetCloseMatches`)
* `ndiff()` + `restore()` (as `NDiff`, `NDiffWith`, `NDiffBytes`, and `Restore`)
* `Differ` (with intraline "? " hints; honors line/char junk filters)
* Byte adapters for unified/context diffs (`GetUnifiedDiffBytes`, `GetContextDiffBytes`)

## Installation

```bash
go get github.com/codinganovel/go-difflib/difflib
```

### More Examples

Close matches (fuzzy suggestions):

```go
matches := difflib.GetCloseMatches(
    "appel",
    []string{"ape", "apple", "peach", "puppy"},
    3, 0.6,
)
// matches => []string{"apple", "ape"}
```

Basic ndiff + restore (human-friendly line deltas):

```go
a := difflib.SplitLines("one\ntwo\nthree\n")
b := difflib.SplitLines("zero\none\nthree\n")
delta := difflib.NDiff(a, b)

// Reconstruct originals from the delta
a2 := difflib.Restore(delta, 1) // == a
b2 := difflib.Restore(delta, 2) // == b
```

Intraline hints with Differ (shows character-level changes using "? "):

```go
d := &difflib.Differ{}
delta := d.Compare(
    difflib.SplitLines("abc\n"),
    difflib.SplitLines("axc\n"),
)
// Emits lines prefixed with:
//   "  " (equal), "- " (delete), "+ " (insert), "? " (intraline guide)
```

NDiff with options (line/char junk filters, intraline hints):

```go
delta := difflib.NDiffWith(
    difflib.SplitLines("abc\n"),
    difflib.SplitLines("axc\n"),
    difflib.NDiffOptions{Intraline: true, CharJunk: difflib.IsCharacterJunk},
)
```

Byte-oriented ndiff (no intraline hints, binary safe):

```go
out := difflib.NDiffBytes([]byte("one\ntwo\n"), []byte("one\n2\n"), difflib.NDiffOptions{})
fmt.Print(string(out))
```

Unified/Context diffs (bytes):

```go
u, _ := difflib.GetUnifiedDiffBytes(difflib.UnifiedDiffBytes{A: a, B: b, FromFile: "A", ToFile: "B", Context: 3})
c, _ := difflib.GetContextDiffBytes(difflib.ContextDiffBytes{A: a, B: b, FromFile: "A", ToFile: "B", Context: 3, Eol: []byte{'\n'}})
```

### Notes

- `NDiff` remains a simple, line-only API for compatibility. Use `NDiffWith` for intraline and junk filters.
- `Differ.Compare` honors `LineJunk`/`CharJunk` and emits intraline `"? "` hints.
- Byte adapters avoid decoding and are safe for non‑UTF‑8 data; intraline is disabled in `NDiffBytes`.
- `HtmlDiff` is not yet implemented; see `TO-DO.md` for remaining parity tasks.

## API

`NDiff`

```go
func NDiff(a, b []string) []string
```

- Emits ndiff-style lines with prefixes: `"  "` (equal), `"- "` (delete), `"+ "` (insert).
- Does not include intraline `"? "` guide lines; use `NDiffWith` (with `Intraline: true`) or `Differ` for those.
- Inputs should be `SplitLines(...)` output to preserve end-of-line markers.
- Output is suitable for `Restore` to reconstruct either original sequence.

`Restore`

```go
func Restore(delta []string, which int) []string
```

- Reconstructs sequence 1 (`which == 1`) or sequence 2 (`which == 2`) from an ndiff delta.
- Ignores lines prefixed with `"? "` if present.
- Returns `nil` for invalid `which` values.

`Differ`

```go
type Differ struct {
    LineJunk func(string) bool
    CharJunk func(rune) bool
}

func (d *Differ) Compare(a, b []string) []string
```

- Produces ndiff-style output, including intraline `"? "` hints for replacements.
- Intraline markers: `^` for replacements, `-` under deletions (aline), `+` under insertions (bline).
- Trailing spaces may appear in `"? "` lines to align markers with characters; examples trim them for readability.
- Current implementation pairs replaced lines greedily; advanced "fancy replace" heuristics are planned.

`NDiffWith`

```go
type NDiffOptions struct {
    LineJunk  func(string) bool
    CharJunk  func(rune) bool
    Intraline bool
}

func NDiffWith(a, b []string, opts NDiffOptions) []string
```

- Like `NDiff`, with optional intraline hints and junk filters applied.
- When `Intraline` is true, `CharJunk` defaults to `IsCharacterJunk` if nil.

`NDiffBytes`

```go
func NDiffBytes(a, b []byte, opts NDiffOptions) []byte
```

- Byte-safe ndiff; intraline is disabled even if requested.
- Use when inputs are arbitrary bytes or not valid UTF‑8.

`UnifiedDiffBytes` / `ContextDiffBytes`

```go
type UnifiedDiffBytes struct { /* ... */ }
func GetUnifiedDiffBytes(diff UnifiedDiffBytes) ([]byte, error)
type ContextDiffBytes = UnifiedDiffBytes
func GetContextDiffBytes(diff ContextDiffBytes) ([]byte, error)
```

- Byte-oriented wrappers over unified/context diffs; preserve formatting and headers.

### Quick Start

Diffs are configured with Unified (or ContextDiff) structures, and can
be output to an io.Writer or returned as a string.

```Go
diff := difflib.UnifiedDiff{
    A:        difflib.SplitLines("foo\nbar\n"),
    B:        difflib.SplitLines("foo\nbaz\n"),
    FromFile: "Original",
    ToFile:   "Current",
    Context:  3,
}
text, _ := difflib.GetUnifiedDiffString(diff)
fmt.Printf(text)
```

would output:

```
--- Original
+++ Current
@@ -1,3 +1,3 @@
 foo
-bar
+baz
```
