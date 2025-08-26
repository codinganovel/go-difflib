// Package difflib is a partial port of Python difflib module.
//
// It provides tools to compare sequences of strings and generate textual diffs.
//
// The following class and functions have been ported:
//
// - SequenceMatcher
//
// - unified_diff
//
// - context_diff
//
// Getting unified diffs was the main goal of the port. Keep in mind this code
// is mostly suitable to output text differences in a human friendly way, there
// are no guarantees generated diffs are consumable by patch(1).
package difflib

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"sort"
	"strings"
	"unicode/utf8"
)

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func calculateRatio(matches, length int) float64 {
	if length > 0 {
		return 2.0 * float64(matches) / float64(length)
	}
	return 1.0
}

type Match struct {
	A    int
	B    int
	Size int
}

type OpCode struct {
	Tag byte
	I1  int
	I2  int
	J1  int
	J2  int
}

// SequenceMatcher compares sequence of strings. The basic
// algorithm predates, and is a little fancier than, an algorithm
// published in the late 1980's by Ratcliff and Obershelp under the
// hyperbolic name "gestalt pattern matching".  The basic idea is to find
// the longest contiguous matching subsequence that contains no "junk"
// elements (R-O doesn't address junk).  The same idea is then applied
// recursively to the pieces of the sequences to the left and to the right
// of the matching subsequence.  This does not yield minimal edit
// sequences, but does tend to yield matches that "look right" to people.
//
// SequenceMatcher tries to compute a "human-friendly diff" between two
// sequences.  Unlike e.g. UNIX(tm) diff, the fundamental notion is the
// longest *contiguous* & junk-free matching subsequence.  That's what
// catches peoples' eyes.  The Windows(tm) windiff has another interesting
// notion, pairing up elements that appear uniquely in each sequence.
// That, and the method here, appear to yield more intuitive difference
// reports than does diff.  This method appears to be the least vulnerable
// to synching up on blocks of "junk lines", though (like blank lines in
// ordinary text files, or maybe "<P>" lines in HTML files).  That may be
// because this is the only method of the 3 that has a *concept* of
// "junk" <wink>.
//
// Timing:  Basic R-O is cubic time worst case and quadratic time expected
// case.  SequenceMatcher is quadratic time for the worst case and has
// expected-case behavior dependent in a complicated way on how many
// elements the sequences have in common; best case time is linear.
type SequenceMatcher struct {
	a              []string
	b              []string
	b2j            map[string][]int
	IsJunk         func(string) bool
	autoJunk       bool
	bJunk          map[string]struct{}
	matchingBlocks []Match
	fullBCount     map[string]int
	bPopular       map[string]struct{}
	opCodes        []OpCode
}

func NewMatcher(a, b []string) *SequenceMatcher {
	m := SequenceMatcher{autoJunk: true}
	m.SetSeqs(a, b)
	return &m
}

func NewMatcherWithJunk(a, b []string, autoJunk bool,
	isJunk func(string) bool) *SequenceMatcher {

	m := SequenceMatcher{IsJunk: isJunk, autoJunk: autoJunk}
	m.SetSeqs(a, b)
	return &m
}

// Set two sequences to be compared.
func (m *SequenceMatcher) SetSeqs(a, b []string) {
	m.SetSeq1(a)
	m.SetSeq2(b)
}

// Set the first sequence to be compared. The second sequence to be compared is
// not changed.
//
// SequenceMatcher computes and caches detailed information about the second
// sequence, so if you want to compare one sequence S against many sequences,
// use .SetSeq2(s) once and call .SetSeq1(x) repeatedly for each of the other
// sequences.
//
// See also SetSeqs() and SetSeq2().
func (m *SequenceMatcher) SetSeq1(a []string) {
	m.a = a
	m.matchingBlocks = nil
	m.opCodes = nil
}

// Set the second sequence to be compared. The first sequence to be compared is
// not changed.
func (m *SequenceMatcher) SetSeq2(b []string) {
	m.b = b
	m.matchingBlocks = nil
	m.opCodes = nil
	m.fullBCount = nil
	m.chainB()
}

func (m *SequenceMatcher) chainB() {
	// Populate line -> index mapping
	b2j := map[string][]int{}
	for i, s := range m.b {
		indices := b2j[s]
		indices = append(indices, i)
		b2j[s] = indices
	}

	// Purge junk elements
	m.bJunk = map[string]struct{}{}
	if m.IsJunk != nil {
		junk := m.bJunk
		for s, _ := range b2j {
			if m.IsJunk(s) {
				junk[s] = struct{}{}
			}
		}
		for s, _ := range junk {
			delete(b2j, s)
		}
	}

	// Purge remaining popular elements
	popular := map[string]struct{}{}
	n := len(m.b)
	if m.autoJunk && n >= 200 {
		ntest := n/100 + 1
		for s, indices := range b2j {
			if len(indices) > ntest {
				popular[s] = struct{}{}
			}
		}
		for s, _ := range popular {
			delete(b2j, s)
		}
	}
	m.bPopular = popular
	m.b2j = b2j
}

func (m *SequenceMatcher) isBJunk(s string) bool {
	_, ok := m.bJunk[s]
	return ok
}

// Find longest matching block in a[alo:ahi] and b[blo:bhi].
//
// If IsJunk is not defined:
//
// Return (i,j,k) such that a[i:i+k] is equal to b[j:j+k], where
//
//	alo <= i <= i+k <= ahi
//	blo <= j <= j+k <= bhi
//
// and for all (i',j',k') meeting those conditions,
//
//	k >= k'
//	i <= i'
//	and if i == i', j <= j'
//
// In other words, of all maximal matching blocks, return one that
// starts earliest in a, and of all those maximal matching blocks that
// start earliest in a, return the one that starts earliest in b.
//
// If IsJunk is defined, first the longest matching block is
// determined as above, but with the additional restriction that no
// junk element appears in the block.  Then that block is extended as
// far as possible by matching (only) junk elements on both sides.  So
// the resulting block never matches on junk except as identical junk
// happens to be adjacent to an "interesting" match.
//
// If no blocks match, return (alo, blo, 0).
func (m *SequenceMatcher) findLongestMatch(alo, ahi, blo, bhi int) Match {
	// CAUTION:  stripping common prefix or suffix would be incorrect.
	// E.g.,
	//    ab
	//    acab
	// Longest matching block is "ab", but if common prefix is
	// stripped, it's "a" (tied with "b").  UNIX(tm) diff does so
	// strip, so ends up claiming that ab is changed to acab by
	// inserting "ca" in the middle.  That's minimal but unintuitive:
	// "it's obvious" that someone inserted "ac" at the front.
	// Windiff ends up at the same place as diff, but by pairing up
	// the unique 'b's and then matching the first two 'a's.
	besti, bestj, bestsize := alo, blo, 0

	// find longest junk-free match
	// during an iteration of the loop, j2len[j] = length of longest
	// junk-free match ending with a[i-1] and b[j]
	j2len := map[int]int{}
	for i := alo; i != ahi; i++ {
		// look at all instances of a[i] in b; note that because
		// b2j has no junk keys, the loop is skipped if a[i] is junk
		newj2len := map[int]int{}
		for _, j := range m.b2j[m.a[i]] {
			// a[i] matches b[j]
			if j < blo {
				continue
			}
			if j >= bhi {
				break
			}
			k := j2len[j-1] + 1
			newj2len[j] = k
			if k > bestsize {
				besti, bestj, bestsize = i-k+1, j-k+1, k
			}
		}
		j2len = newj2len
	}

	// Extend the best by non-junk elements on each end.  In particular,
	// "popular" non-junk elements aren't in b2j, which greatly speeds
	// the inner loop above, but also means "the best" match so far
	// doesn't contain any junk *or* popular non-junk elements.
	for besti > alo && bestj > blo && !m.isBJunk(m.b[bestj-1]) &&
		m.a[besti-1] == m.b[bestj-1] {
		besti, bestj, bestsize = besti-1, bestj-1, bestsize+1
	}
	for besti+bestsize < ahi && bestj+bestsize < bhi &&
		!m.isBJunk(m.b[bestj+bestsize]) &&
		m.a[besti+bestsize] == m.b[bestj+bestsize] {
		bestsize += 1
	}

	// Now that we have a wholly interesting match (albeit possibly
	// empty!), we may as well suck up the matching junk on each
	// side of it too.  Can't think of a good reason not to, and it
	// saves post-processing the (possibly considerable) expense of
	// figuring out what to do with it.  In the case of an empty
	// interesting match, this is clearly the right thing to do,
	// because no other kind of match is possible in the regions.
	for besti > alo && bestj > blo && m.isBJunk(m.b[bestj-1]) &&
		m.a[besti-1] == m.b[bestj-1] {
		besti, bestj, bestsize = besti-1, bestj-1, bestsize+1
	}
	for besti+bestsize < ahi && bestj+bestsize < bhi &&
		m.isBJunk(m.b[bestj+bestsize]) &&
		m.a[besti+bestsize] == m.b[bestj+bestsize] {
		bestsize += 1
	}

	return Match{A: besti, B: bestj, Size: bestsize}
}

// Return list of triples describing matching subsequences.
//
// Each triple is of the form (i, j, n), and means that
// a[i:i+n] == b[j:j+n].  The triples are monotonically increasing in
// i and in j. It's also guaranteed that if (i, j, n) and (i', j', n') are
// adjacent triples in the list, and the second is not the last triple in the
// list, then i+n != i' or j+n != j'. IOW, adjacent triples never describe
// adjacent equal blocks.
//
// The last triple is a dummy, (len(a), len(b), 0), and is the only
// triple with n==0.
func (m *SequenceMatcher) GetMatchingBlocks() []Match {
	if m.matchingBlocks != nil {
		return m.matchingBlocks
	}

	var matchBlocks func(alo, ahi, blo, bhi int, matched []Match) []Match
	matchBlocks = func(alo, ahi, blo, bhi int, matched []Match) []Match {
		match := m.findLongestMatch(alo, ahi, blo, bhi)
		i, j, k := match.A, match.B, match.Size
		if match.Size > 0 {
			if alo < i && blo < j {
				matched = matchBlocks(alo, i, blo, j, matched)
			}
			matched = append(matched, match)
			if i+k < ahi && j+k < bhi {
				matched = matchBlocks(i+k, ahi, j+k, bhi, matched)
			}
		}
		return matched
	}
	matched := matchBlocks(0, len(m.a), 0, len(m.b), nil)

	// It's possible that we have adjacent equal blocks in the
	// matching_blocks list now.
	nonAdjacent := []Match{}
	i1, j1, k1 := 0, 0, 0
	for _, b := range matched {
		// Is this block adjacent to i1, j1, k1?
		i2, j2, k2 := b.A, b.B, b.Size
		if i1+k1 == i2 && j1+k1 == j2 {
			// Yes, so collapse them -- this just increases the length of
			// the first block by the length of the second, and the first
			// block so lengthened remains the block to compare against.
			k1 += k2
		} else {
			// Not adjacent.  Remember the first block (k1==0 means it's
			// the dummy we started with), and make the second block the
			// new block to compare against.
			if k1 > 0 {
				nonAdjacent = append(nonAdjacent, Match{i1, j1, k1})
			}
			i1, j1, k1 = i2, j2, k2
		}
	}
	if k1 > 0 {
		nonAdjacent = append(nonAdjacent, Match{i1, j1, k1})
	}

	nonAdjacent = append(nonAdjacent, Match{len(m.a), len(m.b), 0})
	m.matchingBlocks = nonAdjacent
	return m.matchingBlocks
}

// Return list of 5-tuples describing how to turn a into b.
//
// Each tuple is of the form (tag, i1, i2, j1, j2).  The first tuple
// has i1 == j1 == 0, and remaining tuples have i1 == the i2 from the
// tuple preceding it, and likewise for j1 == the previous j2.
//
// The tags are characters, with these meanings:
//
// 'r' (replace):  a[i1:i2] should be replaced by b[j1:j2]
//
// 'd' (delete):   a[i1:i2] should be deleted, j1==j2 in this case.
//
// 'i' (insert):   b[j1:j2] should be inserted at a[i1:i1], i1==i2 in this case.
//
// 'e' (equal):    a[i1:i2] == b[j1:j2]
func (m *SequenceMatcher) GetOpCodes() []OpCode {
	if m.opCodes != nil {
		return m.opCodes
	}
	i, j := 0, 0
	matching := m.GetMatchingBlocks()
	opCodes := make([]OpCode, 0, len(matching))
	for _, m := range matching {
		//  invariant:  we've pumped out correct diffs to change
		//  a[:i] into b[:j], and the next matching block is
		//  a[ai:ai+size] == b[bj:bj+size]. So we need to pump
		//  out a diff to change a[i:ai] into b[j:bj], pump out
		//  the matching block, and move (i,j) beyond the match
		ai, bj, size := m.A, m.B, m.Size
		tag := byte(0)
		if i < ai && j < bj {
			tag = 'r'
		} else if i < ai {
			tag = 'd'
		} else if j < bj {
			tag = 'i'
		}
		if tag > 0 {
			opCodes = append(opCodes, OpCode{tag, i, ai, j, bj})
		}
		i, j = ai+size, bj+size
		// the list of matching blocks is terminated by a
		// sentinel with size 0
		if size > 0 {
			opCodes = append(opCodes, OpCode{'e', ai, i, bj, j})
		}
	}
	m.opCodes = opCodes
	return m.opCodes
}

// Isolate change clusters by eliminating ranges with no changes.
//
// Return a generator of groups with up to n lines of context.
// Each group is in the same format as returned by GetOpCodes().
func (m *SequenceMatcher) GetGroupedOpCodes(n int) [][]OpCode {
	if n < 0 {
		n = 3
	}
	codes := m.GetOpCodes()
	if len(codes) == 0 {
		codes = []OpCode{OpCode{'e', 0, 1, 0, 1}}
	}
	// Fixup leading and trailing groups if they show no changes.
	if codes[0].Tag == 'e' {
		c := codes[0]
		i1, i2, j1, j2 := c.I1, c.I2, c.J1, c.J2
		codes[0] = OpCode{c.Tag, max(i1, i2-n), i2, max(j1, j2-n), j2}
	}
	if codes[len(codes)-1].Tag == 'e' {
		c := codes[len(codes)-1]
		i1, i2, j1, j2 := c.I1, c.I2, c.J1, c.J2
		codes[len(codes)-1] = OpCode{c.Tag, i1, min(i2, i1+n), j1, min(j2, j1+n)}
	}
	nn := n + n
	groups := [][]OpCode{}
	group := []OpCode{}
	for _, c := range codes {
		i1, i2, j1, j2 := c.I1, c.I2, c.J1, c.J2
		// End the current group and start a new one whenever
		// there is a large range with no changes.
		if c.Tag == 'e' && i2-i1 > nn {
			group = append(group, OpCode{c.Tag, i1, min(i2, i1+n),
				j1, min(j2, j1+n)})
			groups = append(groups, group)
			group = []OpCode{}
			i1, j1 = max(i1, i2-n), max(j1, j2-n)
		}
		group = append(group, OpCode{c.Tag, i1, i2, j1, j2})
	}
	if len(group) > 0 && !(len(group) == 1 && group[0].Tag == 'e') {
		groups = append(groups, group)
	}
	return groups
}

// Return a measure of the sequences' similarity (float in [0,1]).
//
// Where T is the total number of elements in both sequences, and
// M is the number of matches, this is 2.0*M / T.
// Note that this is 1 if the sequences are identical, and 0 if
// they have nothing in common.
//
// .Ratio() is expensive to compute if you haven't already computed
// .GetMatchingBlocks() or .GetOpCodes(), in which case you may
// want to try .QuickRatio() or .RealQuickRation() first to get an
// upper bound.
func (m *SequenceMatcher) Ratio() float64 {
	matches := 0
	for _, m := range m.GetMatchingBlocks() {
		matches += m.Size
	}
	return calculateRatio(matches, len(m.a)+len(m.b))
}

// Return an upper bound on ratio() relatively quickly.
//
// This isn't defined beyond that it is an upper bound on .Ratio(), and
// is faster to compute.
func (m *SequenceMatcher) QuickRatio() float64 {
	// viewing a and b as multisets, set matches to the cardinality
	// of their intersection; this counts the number of matches
	// without regard to order, so is clearly an upper bound
	if m.fullBCount == nil {
		m.fullBCount = map[string]int{}
		for _, s := range m.b {
			m.fullBCount[s] = m.fullBCount[s] + 1
		}
	}

	// avail[x] is the number of times x appears in 'b' less the
	// number of times we've seen it in 'a' so far ... kinda
	avail := map[string]int{}
	matches := 0
	for _, s := range m.a {
		n, ok := avail[s]
		if !ok {
			n = m.fullBCount[s]
		}
		avail[s] = n - 1
		if n > 0 {
			matches += 1
		}
	}
	return calculateRatio(matches, len(m.a)+len(m.b))
}

// Return an upper bound on ratio() very quickly.
//
// This isn't defined beyond that it is an upper bound on .Ratio(), and
// is faster to compute than either .Ratio() or .QuickRatio().
func (m *SequenceMatcher) RealQuickRatio() float64 {
	la, lb := len(m.a), len(m.b)
	return calculateRatio(min(la, lb), la+lb)
}

// Convert range to the "ed" format
func formatRangeUnified(start, stop int) string {
	// Per the diff spec at http://www.unix.org/single_unix_specification/
	beginning := start + 1 // lines start numbering with one
	length := stop - start
	if length == 1 {
		return fmt.Sprintf("%d", beginning)
	}
	if length == 0 {
		beginning -= 1 // empty ranges begin at line just before the range
	}
	return fmt.Sprintf("%d,%d", beginning, length)
}

// Unified diff parameters
type UnifiedDiff struct {
	A        []string // First sequence lines
	FromFile string   // First file name
	FromDate string   // First file time
	B        []string // Second sequence lines
	ToFile   string   // Second file name
	ToDate   string   // Second file time
	Eol      string   // Headers end of line, defaults to LF
	Context  int      // Number of context lines
}

// Compare two sequences of lines; generate the delta as a unified diff.
//
// Unified diffs are a compact way of showing line changes and a few
// lines of context.  The number of context lines is set by 'n' which
// defaults to three.
//
// By default, the diff control lines (those with ---, +++, or @@) are
// created with a trailing newline.  This is helpful so that inputs
// created from file.readlines() result in diffs that are suitable for
// file.writelines() since both the inputs and outputs have trailing
// newlines.
//
// For inputs that do not have trailing newlines, set the lineterm
// argument to "" so that the output will be uniformly newline free.
//
// The unidiff format normally has a header for filenames and modification
// times.  Any or all of these may be specified using strings for
// 'fromfile', 'tofile', 'fromfiledate', and 'tofiledate'.
// The modification times are normally expressed in the ISO 8601 format.
func WriteUnifiedDiff(writer io.Writer, diff UnifiedDiff) error {
	buf := bufio.NewWriter(writer)
	defer buf.Flush()
	wf := func(format string, args ...interface{}) error {
		_, err := buf.WriteString(fmt.Sprintf(format, args...))
		return err
	}
	ws := func(s string) error {
		_, err := buf.WriteString(s)
		return err
	}

	if len(diff.Eol) == 0 {
		diff.Eol = "\n"
	}

	started := false
	m := NewMatcher(diff.A, diff.B)
	for _, g := range m.GetGroupedOpCodes(diff.Context) {
		if !started {
			started = true
			fromDate := ""
			if len(diff.FromDate) > 0 {
				fromDate = "\t" + diff.FromDate
			}
			toDate := ""
			if len(diff.ToDate) > 0 {
				toDate = "\t" + diff.ToDate
			}
			if diff.FromFile != "" || diff.ToFile != "" {
				err := wf("--- %s%s%s", diff.FromFile, fromDate, diff.Eol)
				if err != nil {
					return err
				}
				err = wf("+++ %s%s%s", diff.ToFile, toDate, diff.Eol)
				if err != nil {
					return err
				}
			}
		}
		first, last := g[0], g[len(g)-1]
		range1 := formatRangeUnified(first.I1, last.I2)
		range2 := formatRangeUnified(first.J1, last.J2)
		if err := wf("@@ -%s +%s @@%s", range1, range2, diff.Eol); err != nil {
			return err
		}
		for _, c := range g {
			i1, i2, j1, j2 := c.I1, c.I2, c.J1, c.J2
			if c.Tag == 'e' {
				for _, line := range diff.A[i1:i2] {
					if err := ws(" " + line); err != nil {
						return err
					}
				}
				continue
			}
			if c.Tag == 'r' || c.Tag == 'd' {
				for _, line := range diff.A[i1:i2] {
					if err := ws("-" + line); err != nil {
						return err
					}
				}
			}
			if c.Tag == 'r' || c.Tag == 'i' {
				for _, line := range diff.B[j1:j2] {
					if err := ws("+" + line); err != nil {
						return err
					}
				}
			}
		}
	}
	return nil
}

// Like WriteUnifiedDiff but returns the diff a string.
func GetUnifiedDiffString(diff UnifiedDiff) (string, error) {
	w := &bytes.Buffer{}
	err := WriteUnifiedDiff(w, diff)
	return string(w.Bytes()), err
}

// Convert range to the "ed" format.
func formatRangeContext(start, stop int) string {
	// Per the diff spec at http://www.unix.org/single_unix_specification/
	beginning := start + 1 // lines start numbering with one
	length := stop - start
	if length == 0 {
		beginning -= 1 // empty ranges begin at line just before the range
	}
	if length <= 1 {
		return fmt.Sprintf("%d", beginning)
	}
	return fmt.Sprintf("%d,%d", beginning, beginning+length-1)
}

type ContextDiff UnifiedDiff

// Compare two sequences of lines; generate the delta as a context diff.
//
// Context diffs are a compact way of showing line changes and a few
// lines of context. The number of context lines is set by diff.Context
// which defaults to three.
//
// By default, the diff control lines (those with *** or ---) are
// created with a trailing newline.
//
// For inputs that do not have trailing newlines, set the diff.Eol
// argument to "" so that the output will be uniformly newline free.
//
// The context diff format normally has a header for filenames and
// modification times.  Any or all of these may be specified using
// strings for diff.FromFile, diff.ToFile, diff.FromDate, diff.ToDate.
// The modification times are normally expressed in the ISO 8601 format.
// If not specified, the strings default to blanks.
func WriteContextDiff(writer io.Writer, diff ContextDiff) error {
	buf := bufio.NewWriter(writer)
	defer buf.Flush()
	var diffErr error
	wf := func(format string, args ...interface{}) {
		_, err := buf.WriteString(fmt.Sprintf(format, args...))
		if diffErr == nil && err != nil {
			diffErr = err
		}
	}
	ws := func(s string) {
		_, err := buf.WriteString(s)
		if diffErr == nil && err != nil {
			diffErr = err
		}
	}

	if len(diff.Eol) == 0 {
		diff.Eol = "\n"
	}

	prefix := map[byte]string{
		'i': "+ ",
		'd': "- ",
		'r': "! ",
		'e': "  ",
	}

	started := false
	m := NewMatcher(diff.A, diff.B)
	for _, g := range m.GetGroupedOpCodes(diff.Context) {
		if !started {
			started = true
			fromDate := ""
			if len(diff.FromDate) > 0 {
				fromDate = "\t" + diff.FromDate
			}
			toDate := ""
			if len(diff.ToDate) > 0 {
				toDate = "\t" + diff.ToDate
			}
			if diff.FromFile != "" || diff.ToFile != "" {
				wf("*** %s%s%s", diff.FromFile, fromDate, diff.Eol)
				wf("--- %s%s%s", diff.ToFile, toDate, diff.Eol)
			}
		}

		first, last := g[0], g[len(g)-1]
		ws("***************" + diff.Eol)

		range1 := formatRangeContext(first.I1, last.I2)
		wf("*** %s ****%s", range1, diff.Eol)
		for _, c := range g {
			if c.Tag == 'r' || c.Tag == 'd' {
				for _, cc := range g {
					if cc.Tag == 'i' {
						continue
					}
					for _, line := range diff.A[cc.I1:cc.I2] {
						ws(prefix[cc.Tag] + line)
					}
				}
				break
			}
		}

		range2 := formatRangeContext(first.J1, last.J2)
		wf("--- %s ----%s", range2, diff.Eol)
		for _, c := range g {
			if c.Tag == 'r' || c.Tag == 'i' {
				for _, cc := range g {
					if cc.Tag == 'd' {
						continue
					}
					for _, line := range diff.B[cc.J1:cc.J2] {
						ws(prefix[cc.Tag] + line)
					}
				}
				break
			}
		}
	}
	return diffErr
}

// Like WriteContextDiff but returns the diff a string.
func GetContextDiffString(diff ContextDiff) (string, error) {
	w := &bytes.Buffer{}
	err := WriteContextDiff(w, diff)
	return string(w.Bytes()), err
}

// UnifiedDiffBytes mirrors UnifiedDiff but takes raw byte content and Eol as bytes.
type UnifiedDiffBytes struct {
	A        []byte
	FromFile string
	FromDate string
	B        []byte
	ToFile   string
	ToDate   string
	Eol      []byte
	Context  int
}

// WriteUnifiedDiffBytes is a byte-oriented adapter that splits inputs on '\n'
// (preserving newlines), delegates to WriteUnifiedDiff, and writes byte output.
func WriteUnifiedDiffBytes(w io.Writer, diff UnifiedDiffBytes) error {
	a := SplitLinesBytes(diff.A)
	b := SplitLinesBytes(diff.B)

	// Convert to []string without interpreting as UTF-8.
	as := make([]string, len(a))
	for i := range a {
		as[i] = string(a[i])
	}
	bs := make([]string, len(b))
	for i := range b {
		bs[i] = string(b[i])
	}

	sd := UnifiedDiff{
		A:        as,
		FromFile: diff.FromFile,
		FromDate: diff.FromDate,
		B:        bs,
		ToFile:   diff.ToFile,
		ToDate:   diff.ToDate,
		Eol:      string(diff.Eol),
		Context:  diff.Context,
	}
	// Use WriteUnifiedDiff into a bytes.Buffer, then write raw bytes to w.
	var buf bytes.Buffer
	if err := WriteUnifiedDiff(&buf, sd); err != nil {
		return err
	}
	_, err := w.Write(buf.Bytes())
	return err
}

// GetUnifiedDiffBytes is like WriteUnifiedDiffBytes but returns the diff as bytes.
func GetUnifiedDiffBytes(diff UnifiedDiffBytes) ([]byte, error) {
	var buf bytes.Buffer
	if err := WriteUnifiedDiffBytes(&buf, diff); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

// ContextDiffBytes mirrors ContextDiff/UnifiedDiff but takes raw bytes.
type ContextDiffBytes UnifiedDiffBytes

// WriteContextDiffBytes is a byte-oriented adapter for context diffs.
func WriteContextDiffBytes(w io.Writer, diff ContextDiffBytes) error {
	a := SplitLinesBytes(diff.A)
	b := SplitLinesBytes(diff.B)

	as := make([]string, len(a))
	for i := range a {
		as[i] = string(a[i])
	}
	bs := make([]string, len(b))
	for i := range b {
		bs[i] = string(b[i])
	}

	sd := ContextDiff{
		A:        as,
		FromFile: diff.FromFile,
		FromDate: diff.FromDate,
		B:        bs,
		ToFile:   diff.ToFile,
		ToDate:   diff.ToDate,
		Eol:      string(diff.Eol),
		Context:  diff.Context,
	}
	var buf bytes.Buffer
	if err := WriteContextDiff(&buf, sd); err != nil {
		return err
	}
	_, err := w.Write(buf.Bytes())
	return err
}

// GetContextDiffBytes returns a context diff as bytes.
func GetContextDiffBytes(diff ContextDiffBytes) ([]byte, error) {
	var buf bytes.Buffer
	if err := WriteContextDiffBytes(&buf, diff); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

// Split a string on "\n" while preserving them. The output can be used
// as input for UnifiedDiff and ContextDiff structures.
func SplitLines(s string) []string {
	lines := strings.SplitAfter(s, "\n")
	lines[len(lines)-1] += "\n"
	return lines
}

// SplitLinesBytes splits on '\n' while preserving them and ensures the last
// element ends with a trailing '\n', mirroring SplitLines semantics.
func SplitLinesBytes(b []byte) [][]byte {
	parts := bytes.SplitAfter(b, []byte{'\n'})
	parts[len(parts)-1] = append(parts[len(parts)-1], '\n')
	return parts
}

// IsLineJunk reports whether a line is ignorable: blank or containing only a single '#',
// possibly surrounded by whitespace. Trailing "\n" is ignored for the purpose of this check.
// This mirrors Python difflib's IS_LINE_JUNK default.
func IsLineJunk(line string) bool {
	if strings.HasSuffix(line, "\n") {
		line = strings.TrimSuffix(line, "\n")
	}
	t := strings.TrimSpace(line)
	return t == "" || t == "#"
}

// IsCharacterJunk reports whether a rune is ignorable: a space or a tab.
// This mirrors Python difflib's IS_CHARACTER_JUNK default.
func IsCharacterJunk(r rune) bool { return r == ' ' || r == '\t' }

// GetCloseMatches returns a list (up to n) of the best "good enough" matches
// from possibilities for the given word. Only candidates scoring at least
// cutoff (in [0.0, 1.0]) are returned, ordered by similarity descending and
// then by original order for ties. If n <= 0 or cutoff is outside [0,1],
// it returns an empty slice.
func GetCloseMatches(word string, possibilities []string, n int, cutoff float64) []string {
	if n <= 0 || cutoff < 0.0 || cutoff > 1.0 {
		return nil
	}

	// Helper to split into runes as []string elements for SequenceMatcher.
	splitRunes := func(s string) []string {
		// Allocate approximately len(s) elements; final may be smaller for multibyte runes.
		out := make([]string, 0, len(s))
		for _, r := range s {
			out = append(out, string(r))
		}
		return out
	}

	mb := splitRunes(word)
	m := NewMatcher(nil, mb)

	type cand struct {
		score float64
		idx   int
		val   string
	}
	results := make([]cand, 0, len(possibilities))
	for i, p := range possibilities {
		ma := splitRunes(p)
		m.SetSeq1(ma)
		if m.RealQuickRatio() >= cutoff && m.QuickRatio() >= cutoff {
			s := m.Ratio()
			if s >= cutoff {
				results = append(results, cand{score: s, idx: i, val: p})
			}
		}
	}

	sort.SliceStable(results, func(i, j int) bool {
		if results[i].score == results[j].score {
			return results[i].idx < results[j].idx // preserve original order on ties
		}
		return results[i].score > results[j].score
	})

	if len(results) > n {
		results = results[:n]
	}
	out := make([]string, len(results))
	for i, c := range results {
		out[i] = c.val
	}
	return out
}

// NDiff returns a basic human-readable delta between a and b (lists of lines),
// using prefixes similar to Python's difflib.ndiff:
//
//	"- " line unique to sequence a
//	"+ " line unique to sequence b
//	"  " line common to both sequences
//
// This basic version does not include intraline "? " guide lines.
func NDiff(a, b []string) []string {
	m := NewMatcher(a, b)
	var out []string
	for _, op := range m.GetOpCodes() {
		switch op.Tag {
		case 'e':
			for _, line := range a[op.I1:op.I2] {
				out = append(out, "  "+line)
			}
		case 'd':
			for _, line := range a[op.I1:op.I2] {
				out = append(out, "- "+line)
			}
		case 'i':
			for _, line := range b[op.J1:op.J2] {
				out = append(out, "+ "+line)
			}
		case 'r':
			for _, line := range a[op.I1:op.I2] {
				out = append(out, "- "+line)
			}
			for _, line := range b[op.J1:op.J2] {
				out = append(out, "+ "+line)
			}
		}
	}
	return out
}

// NDiffOptions customizes NDiffWith behavior.
//
// LineJunk: optional filter to treat some lines as ignorable during matching
// (e.g., blank lines). When set, it's passed to the line-level matcher.
// CharJunk: optional filter for intraline comparison to ignore characters
// (e.g., spaces or tabs); defaults to IsCharacterJunk if nil.
// Intraline: when true, include "? " guide lines showing intraline changes.
// If false, output matches basic NDiff-style output without guide lines.
type NDiffOptions struct {
	LineJunk  func(string) bool
	CharJunk  func(rune) bool
	Intraline bool
}

// NDiffWith returns a human-readable delta between a and b with options.
// It preserves NDiff formatting and, when Intraline is true, adds "? " guide lines
// similar to Python's difflib.ndiff.
func NDiffWith(a, b []string, opts NDiffOptions) []string {
	if opts.Intraline {
		d := &Differ{LineJunk: opts.LineJunk, CharJunk: opts.CharJunk}
		return d.Compare(a, b)
	}
	// No intraline: keep basic output, but still honor LineJunk for matching.
	m := NewMatcherWithJunk(a, b, true, opts.LineJunk)
	var out []string
	for _, op := range m.GetOpCodes() {
		switch op.Tag {
		case 'e':
			for _, line := range a[op.I1:op.I2] {
				out = append(out, "  "+line)
			}
		case 'd':
			for _, line := range a[op.I1:op.I2] {
				out = append(out, "- "+line)
			}
		case 'i':
			for _, line := range b[op.J1:op.J2] {
				out = append(out, "+ "+line)
			}
		case 'r':
			for _, line := range a[op.I1:op.I2] {
				out = append(out, "- "+line)
			}
			for _, line := range b[op.J1:op.J2] {
				out = append(out, "+ "+line)
			}
		}
	}
	return out
}

// NDiffBytes is a thin adapter that produces ndiff-style output for byte
// sequences. It splits inputs on '\n' (preserving newlines) and delegates to
// the string-based NDiffWith. Intraline hints are disabled to avoid rune
// decoding of arbitrary bytes; opts.Intraline is ignored.
func NDiffBytes(a, b []byte, opts NDiffOptions) []byte {
	al := SplitLinesBytes(a)
	bl := SplitLinesBytes(b)

	// Convert to []string without interpreting as UTF-8 (Go strings are raw bytes).
	as := make([]string, len(al))
	for i := range al {
		as[i] = string(al[i])
	}
	bs := make([]string, len(bl))
	for i := range bl {
		bs[i] = string(bl[i])
	}

	// Disable intraline for byte mode to stay byte-safe.
	opts.Intraline = false
	lines := NDiffWith(as, bs, opts)
	// Join into a single byte slice.
	var buf bytes.Buffer
	for _, s := range lines {
		buf.WriteString(s)
	}
	return buf.Bytes()
}

// Restore reconstructs one of the original sequences (1 or 2) from an ndiff
// style delta (as produced by NDiff). Lines starting with "? " are ignored if
// present. Returns nil if 'which' is not 1 or 2.
func Restore(delta []string, which int) []string {
	if which != 1 && which != 2 {
		return nil
	}
	keepPrefix := "  "
	wantPrefix := "- "
	if which == 2 {
		wantPrefix = "+ "
	}
	var out []string
	for _, d := range delta {
		if len(d) < 2 {
			continue
		}
		prefix := d[:2]
		if prefix == keepPrefix || prefix == wantPrefix {
			out = append(out, d[2:])
		}
		// ignore other prefixes (e.g., "+ " when which==1, "- " when which==2, and "? ")
	}
	return out
}

// Differ produces human-readable deltas from sequences of lines of text.
// It can emit intraline "? " guide lines highlighting character-level changes.
type Differ struct {
	// LineJunk filters ignorable lines. Currently unused in Compare scaffolding.
	LineJunk func(string) bool
	// CharJunk filters ignorable characters when computing intraline hints.
	// Currently unused; placeholder for parity with Python API.
	CharJunk func(rune) bool
}

// Compare returns an ndiff-style delta including intraline hints for replacements.
// Prefixes:
//
//	"- " line unique to sequence a
//	"+ " line unique to sequence b
//	"  " line common to both sequences
//	"? " intraline difference guides (only for replacements)
func (d *Differ) Compare(a, b []string) []string {
	// Honor LineJunk by passing it to the matcher when provided.
	var m *SequenceMatcher
	if d.LineJunk != nil {
		m = NewMatcherWithJunk(a, b, true, d.LineJunk)
	} else {
		m = NewMatcher(a, b)
	}
	var out []string
	for _, op := range m.GetOpCodes() {
		switch op.Tag {
		case 'e':
			for _, line := range a[op.I1:op.I2] {
				out = append(out, "  "+line)
			}
		case 'd':
			for _, line := range a[op.I1:op.I2] {
				out = append(out, "- "+line)
			}
		case 'i':
			for _, line := range b[op.J1:op.J2] {
				out = append(out, "+ "+line)
			}
		case 'r':
			// Pair up lines greedily; remaining are treated as pure inserts/deletes.
			as := a[op.I1:op.I2]
			bs := b[op.J1:op.J2]
			n := min(len(as), len(bs))
			for i := 0; i < n; i++ {
				aline := as[i]
				bline := bs[i]
				atags, btags := buildIntralineTagsWith(aline, bline, d.CharJunk)
				out = append(out, "- "+aline)
				if atags != "" {
					out = append(out, "? "+atags+"\n")
				}
				out = append(out, "+ "+bline)
				if btags != "" {
					out = append(out, "? "+btags+"\n")
				}
			}
			// Remaining deletions
			for _, line := range as[n:] {
				out = append(out, "- "+line)
			}
			// Remaining insertions
			for _, line := range bs[n:] {
				out = append(out, "+ "+line)
			}
		}
	}
	return out
}

// buildIntralineTags returns tag strings (without trailing newline) for aline and bline,
// using '^' for replacements, '-' for deletions (aline only) and '+' for insertions (bline only).
func buildIntralineTagsWith(aline, bline string, charJunk func(rune) bool) (string, string) {
	// Strip trailing newlines for alignment purposes
	if strings.HasSuffix(aline, "\n") {
		aline = strings.TrimSuffix(aline, "\n")
	}
	if strings.HasSuffix(bline, "\n") {
		bline = strings.TrimSuffix(bline, "\n")
	}

	split := func(s string) []string {
		out := make([]string, 0, len(s))
		for _, r := range s {
			out = append(out, string(r))
		}
		return out
	}
	ma := split(aline)
	mb := split(bline)
	// Default to IsCharacterJunk if not provided.
	var cj = charJunk
	if cj == nil {
		cj = IsCharacterJunk
	}
	isJunk := func(s string) bool {
		r, _ := utf8.DecodeRuneInString(s)
		return cj(r)
	}
	sm := NewMatcherWithJunk(ma, mb, true, isJunk)
	var atags, btags strings.Builder
	for _, oc := range sm.GetOpCodes() {
		switch oc.Tag {
		case 'e':
			for i := 0; i < oc.I2-oc.I1; i++ {
				atags.WriteByte(' ')
			}
			for j := 0; j < oc.J2-oc.J1; j++ {
				btags.WriteByte(' ')
			}
		case 'r':
			for i := 0; i < oc.I2-oc.I1; i++ {
				atags.WriteByte('^')
			}
			for j := 0; j < oc.J2-oc.J1; j++ {
				btags.WriteByte('^')
			}
		case 'd':
			for i := 0; i < oc.I2-oc.I1; i++ {
				atags.WriteByte('-')
			}
		case 'i':
			for j := 0; j < oc.J2-oc.J1; j++ {
				btags.WriteByte('+')
			}
		}
	}
	aTag := atags.String()
	bTag := btags.String()
	if strings.TrimSpace(aTag) == "" {
		aTag = ""
	}
	if strings.TrimSpace(bTag) == "" {
		bTag = ""
	}
	return aTag, bTag
}
