package difflib

import (
	"bytes"
	"fmt"
	"math"
	"reflect"
	"strings"
	"testing"
)

func assertAlmostEqual(t *testing.T, a, b float64, places int) {
	if math.Abs(a-b) > math.Pow10(-places) {
		t.Errorf("%.7f != %.7f", a, b)
	}
}

func assertEqual(t *testing.T, a, b interface{}) {
	if !reflect.DeepEqual(a, b) {
		t.Errorf("%v != %v", a, b)
	}
}

func splitChars(s string) []string {
	chars := make([]string, 0, len(s))
	// Assume ASCII inputs
	for i := 0; i != len(s); i++ {
		chars = append(chars, string(s[i]))
	}
	return chars
}

func TestSequenceMatcherRatio(t *testing.T) {
	s := NewMatcher(splitChars("abcd"), splitChars("bcde"))
	assertEqual(t, s.Ratio(), 0.75)
	assertEqual(t, s.QuickRatio(), 0.75)
	assertEqual(t, s.RealQuickRatio(), 1.0)
}

func TestGetOptCodes(t *testing.T) {
	a := "qabxcd"
	b := "abycdf"
	s := NewMatcher(splitChars(a), splitChars(b))
	w := &bytes.Buffer{}
	for _, op := range s.GetOpCodes() {
		fmt.Fprintf(w, "%s a[%d:%d], (%s) b[%d:%d] (%s)\n", string(op.Tag),
			op.I1, op.I2, a[op.I1:op.I2], op.J1, op.J2, b[op.J1:op.J2])
	}
	result := w.String()
	expected := `d a[0:1], (q) b[0:0] ()
e a[1:3], (ab) b[0:2] (ab)
r a[3:4], (x) b[2:3] (y)
e a[4:6], (cd) b[3:5] (cd)
i a[6:6], () b[5:6] (f)
`
	if expected != result {
		t.Errorf("unexpected op codes: \n%s", result)
	}
}

func TestGroupedOpCodes(t *testing.T) {
	a := []string{}
	for i := 0; i != 39; i++ {
		a = append(a, fmt.Sprintf("%02d", i))
	}
	b := []string{}
	b = append(b, a[:8]...)
	b = append(b, " i")
	b = append(b, a[8:19]...)
	b = append(b, " x")
	b = append(b, a[20:22]...)
	b = append(b, a[27:34]...)
	b = append(b, " y")
	b = append(b, a[35:]...)
	s := NewMatcher(a, b)
	w := &bytes.Buffer{}
	for _, g := range s.GetGroupedOpCodes(-1) {
		fmt.Fprintf(w, "group\n")
		for _, op := range g {
			fmt.Fprintf(w, "  %s, %d, %d, %d, %d\n", string(op.Tag),
				op.I1, op.I2, op.J1, op.J2)
		}
	}
	result := w.String()
	expected := `group
  e, 5, 8, 5, 8
  i, 8, 8, 8, 9
  e, 8, 11, 9, 12
group
  e, 16, 19, 17, 20
  r, 19, 20, 20, 21
  e, 20, 22, 21, 23
  d, 22, 27, 23, 23
  e, 27, 30, 23, 26
group
  e, 31, 34, 27, 30
  r, 34, 35, 30, 31
  e, 35, 38, 31, 34
`
	if expected != result {
		t.Errorf("unexpected op codes: \n%s", result)
	}
}

func ExampleWriteUnifiedDiff() {
	a := `one
two
three
four
fmt.Printf("%s,%T",a,b)`
	b := `zero
one
three
four`
	diff := UnifiedDiff{
		A:        SplitLines(a),
		B:        SplitLines(b),
		FromFile: "Original",
		FromDate: "2005-01-26 23:30:50",
		ToFile:   "Current",
		ToDate:   "2010-04-02 10:20:52",
		Context:  3,
	}
	result, _ := GetUnifiedDiffString(diff)
	fmt.Println(strings.Replace(result, "\t", " ", -1))
	// Output:
	// --- Original 2005-01-26 23:30:50
	// +++ Current 2010-04-02 10:20:52
	// @@ -1,5 +1,4 @@
	// +zero
	//  one
	// -two
	//  three
	//  four
	// -fmt.Printf("%s,%T",a,b)
}

func ExampleWriteContextDiff() {
	a := `one
two
three
four
fmt.Printf("%s,%T",a,b)`
	b := `zero
one
tree
four`
	diff := ContextDiff{
		A:        SplitLines(a),
		B:        SplitLines(b),
		FromFile: "Original",
		ToFile:   "Current",
		Context:  3,
		Eol:      "\n",
	}
	result, _ := GetContextDiffString(diff)
	fmt.Print(strings.Replace(result, "\t", " ", -1))
	// Output:
	// *** Original
	// --- Current
	// ***************
	// *** 1,5 ****
	//   one
	// ! two
	// ! three
	//   four
	// - fmt.Printf("%s,%T",a,b)
	// --- 1,4 ----
	// + zero
	//   one
	// ! tree
	//   four
}

func ExampleGetContextDiffString() {
	a := `one
two
three
four`
	b := `zero
one
tree
four`
	diff := ContextDiff{
		A:        SplitLines(a),
		B:        SplitLines(b),
		FromFile: "Original",
		ToFile:   "Current",
		Context:  3,
		Eol:      "\n",
	}
	result, _ := GetContextDiffString(diff)
	fmt.Printf(strings.Replace(result, "\t", " ", -1))
	// Output:
	// *** Original
	// --- Current
	// ***************
	// *** 1,4 ****
	//   one
	// ! two
	// ! three
	//   four
	// --- 1,4 ----
	// + zero
	//   one
	// ! tree
	//   four
}

func ExampleGetUnifiedDiffBytes() {
	a := []byte("one\ntwo\nthree\nfour\nfmt.Printf(\"%s,%T\",a,b)")
	b := []byte("zero\none\nthree\nfour")
	diff := UnifiedDiffBytes{
		A:        a,
		B:        b,
		FromFile: "Original",
		FromDate: "2005-01-26 23:30:50",
		ToFile:   "Current",
		ToDate:   "2010-04-02 10:20:52",
		Context:  3,
	}
	out, _ := GetUnifiedDiffBytes(diff)
	// Print as string for example purposes (raw bytes are fine here).
	fmt.Println(strings.Replace(string(out), "\t", " ", -1))
	// Output:
	// --- Original 2005-01-26 23:30:50
	// +++ Current 2010-04-02 10:20:52
	// @@ -1,5 +1,4 @@
	// +zero
	//  one
	// -two
	//  three
	//  four
	// -fmt.Printf("%s,%T",a,b)
}

func TestUnifiedDiffBytes_EqualsStringUnified_ASCII(t *testing.T) {
	a := []byte("one\ntwo\nthree\nfour\n")
	b := []byte("zero\none\nthree\nfour\n")
	by, err := GetUnifiedDiffBytes(UnifiedDiffBytes{A: a, B: b, FromFile: "A", ToFile: "B", Context: 3})
	if err != nil {
		t.Fatalf("bytes unified diff error: %v", err)
	}
	st, err := GetUnifiedDiffString(UnifiedDiff{A: SplitLines(string(a)), B: SplitLines(string(b)), FromFile: "A", ToFile: "B", Context: 3})
	if err != nil {
		t.Fatalf("string unified diff error: %v", err)
	}
	if string(by) != st {
		t.Fatalf("unified bytes != string\nGot:\n%s\nWant:\n%s", string(by), st)
	}
}

func TestContextDiffBytes_EqualsStringContext_ASCII(t *testing.T) {
	a := []byte("one\ntwo\nthree\nfour\n")
	b := []byte("zero\none\nthree\nfour\n")
	by, err := GetContextDiffBytes(ContextDiffBytes{A: a, B: b, FromFile: "A", ToFile: "B", Context: 3})
	if err != nil {
		t.Fatalf("bytes context diff error: %v", err)
	}
	st, err := GetContextDiffString(ContextDiff{A: SplitLines(string(a)), B: SplitLines(string(b)), FromFile: "A", ToFile: "B", Context: 3, Eol: "\n"})
	if err != nil {
		t.Fatalf("string context diff error: %v", err)
	}
	if string(by) != st {
		t.Fatalf("context bytes != string\nGot:\n%s\nWant:\n%s", string(by), st)
	}
}

func TestUnifiedDiffBytes_BinarySafety(t *testing.T) {
	// Contains NUL and 0xFF bytes
	a := []byte{'a', 0x00, 'b', '\n', 0xFF, 'x', '\n'}
	b := []byte{'a', 0x00, 'c', '\n', 0xFF, 'x', '\n'}
	_, err := GetUnifiedDiffBytes(UnifiedDiffBytes{A: a, B: b, Context: 1})
	if err != nil {
		t.Fatalf("unexpected error on binary unified diff: %v", err)
	}
}

func TestContextDiffBytes_BinarySafety(t *testing.T) {
	a := []byte{'a', 0x00, 'b', '\n'}
	b := []byte{'a', 0x00, 'c', '\n'}
	_, err := GetContextDiffBytes(ContextDiffBytes{A: a, B: b, Context: 1, Eol: []byte{'\n'}})
	if err != nil {
		t.Fatalf("unexpected error on binary context diff: %v", err)
	}
}

func TestNDiffBytes_BinarySafety(t *testing.T) {
	a := []byte{'x', 0x00, 'y', '\n'}
	b := []byte{'x', 0x00, 'z', '\n'}
	out := NDiffBytes(a, b, NDiffOptions{})
	if len(out) == 0 {
		t.Fatalf("unexpected empty result for binary ndiff")
	}
	// Should not contain '? ' intraline guides in bytes mode
	if strings.Contains(string(out), "? ") {
		t.Fatalf("bytes ndiff should not emit intraline guides; got:\n%s", string(out))
	}
}

func rep(s string, count int) string {
	return strings.Repeat(s, count)
}

func TestWithAsciiOneInsert(t *testing.T) {
	sm := NewMatcher(splitChars(rep("b", 100)),
		splitChars("a"+rep("b", 100)))
	assertAlmostEqual(t, sm.Ratio(), 0.995, 3)
	assertEqual(t, sm.GetOpCodes(),
		[]OpCode{{'i', 0, 0, 0, 1}, {'e', 0, 100, 1, 101}})
	assertEqual(t, len(sm.bPopular), 0)

	sm = NewMatcher(splitChars(rep("b", 100)),
		splitChars(rep("b", 50)+"a"+rep("b", 50)))
	assertAlmostEqual(t, sm.Ratio(), 0.995, 3)
	assertEqual(t, sm.GetOpCodes(),
		[]OpCode{{'e', 0, 50, 0, 50}, {'i', 50, 50, 50, 51}, {'e', 50, 100, 51, 101}})
	assertEqual(t, len(sm.bPopular), 0)
}

func TestWithAsciiOnDelete(t *testing.T) {
	sm := NewMatcher(splitChars(rep("a", 40)+"c"+rep("b", 40)),
		splitChars(rep("a", 40)+rep("b", 40)))
	assertAlmostEqual(t, sm.Ratio(), 0.994, 3)
	assertEqual(t, sm.GetOpCodes(),
		[]OpCode{{'e', 0, 40, 0, 40}, {'d', 40, 41, 40, 40}, {'e', 41, 81, 40, 80}})
}

func TestWithAsciiBJunk(t *testing.T) {
	isJunk := func(s string) bool {
		return s == " "
	}
	sm := NewMatcherWithJunk(splitChars(rep("a", 40)+rep("b", 40)),
		splitChars(rep("a", 44)+rep("b", 40)), true, isJunk)
	assertEqual(t, sm.bJunk, map[string]struct{}{})

	sm = NewMatcherWithJunk(splitChars(rep("a", 40)+rep("b", 40)),
		splitChars(rep("a", 44)+rep("b", 40)+rep(" ", 20)), false, isJunk)
	assertEqual(t, sm.bJunk, map[string]struct{}{" ": struct{}{}})

	isJunk = func(s string) bool {
		return s == " " || s == "b"
	}
	sm = NewMatcherWithJunk(splitChars(rep("a", 40)+rep("b", 40)),
		splitChars(rep("a", 44)+rep("b", 40)+rep(" ", 20)), false, isJunk)
	assertEqual(t, sm.bJunk, map[string]struct{}{" ": struct{}{}, "b": struct{}{}})
}

func TestSFBugsRatioForNullSeqn(t *testing.T) {
	sm := NewMatcher(nil, nil)
	assertEqual(t, sm.Ratio(), 1.0)
	assertEqual(t, sm.QuickRatio(), 1.0)
	assertEqual(t, sm.RealQuickRatio(), 1.0)
}

func TestSFBugsComparingEmptyLists(t *testing.T) {
	groups := NewMatcher(nil, nil).GetGroupedOpCodes(-1)
	assertEqual(t, len(groups), 0)
	diff := UnifiedDiff{
		FromFile: "Original",
		ToFile:   "Current",
		Context:  3,
	}
	result, err := GetUnifiedDiffString(diff)
	assertEqual(t, err, nil)
	assertEqual(t, result, "")
}

func TestOutputFormatRangeFormatUnified(t *testing.T) {
	// Per the diff spec at http://www.unix.org/single_unix_specification/
	//
	// Each <range> field shall be of the form:
	//   %1d", <beginning line number>  if the range contains exactly one line,
	// and:
	//  "%1d,%1d", <beginning line number>, <number of lines> otherwise.
	// If a range is empty, its beginning line number shall be the number of
	// the line just before the range, or 0 if the empty range starts the file.
	fm := formatRangeUnified
	assertEqual(t, fm(3, 3), "3,0")
	assertEqual(t, fm(3, 4), "4")
	assertEqual(t, fm(3, 5), "4,2")
	assertEqual(t, fm(3, 6), "4,3")
	assertEqual(t, fm(0, 0), "0,0")
}

func TestOutputFormatRangeFormatContext(t *testing.T) {
	// Per the diff spec at http://www.unix.org/single_unix_specification/
	//
	// The range of lines in file1 shall be written in the following format
	// if the range contains two or more lines:
	//     "*** %d,%d ****\n", <beginning line number>, <ending line number>
	// and the following format otherwise:
	//     "*** %d ****\n", <ending line number>
	// The ending line number of an empty range shall be the number of the preceding line,
	// or 0 if the range is at the start of the file.
	//
	// Next, the range of lines in file2 shall be written in the following format
	// if the range contains two or more lines:
	//     "--- %d,%d ----\n", <beginning line number>, <ending line number>
	// and the following format otherwise:
	//     "--- %d ----\n", <ending line number>
	fm := formatRangeContext
	assertEqual(t, fm(3, 3), "3")
	assertEqual(t, fm(3, 4), "4")
	assertEqual(t, fm(3, 5), "4,5")
	assertEqual(t, fm(3, 6), "4,6")
	assertEqual(t, fm(0, 0), "0")
}

func TestOutputFormatTabDelimiter(t *testing.T) {
	diff := UnifiedDiff{
		A:        splitChars("one"),
		B:        splitChars("two"),
		FromFile: "Original",
		FromDate: "2005-01-26 23:30:50",
		ToFile:   "Current",
		ToDate:   "2010-04-12 10:20:52",
		Eol:      "\n",
	}
	ud, err := GetUnifiedDiffString(diff)
	assertEqual(t, err, nil)
	assertEqual(t, SplitLines(ud)[:2], []string{
		"--- Original\t2005-01-26 23:30:50\n",
		"+++ Current\t2010-04-12 10:20:52\n",
	})
	cd, err := GetContextDiffString(ContextDiff(diff))
	assertEqual(t, err, nil)
	assertEqual(t, SplitLines(cd)[:2], []string{
		"*** Original\t2005-01-26 23:30:50\n",
		"--- Current\t2010-04-12 10:20:52\n",
	})
}

func TestOutputFormatNoTrailingTabOnEmptyFiledate(t *testing.T) {
	diff := UnifiedDiff{
		A:        splitChars("one"),
		B:        splitChars("two"),
		FromFile: "Original",
		ToFile:   "Current",
		Eol:      "\n",
	}
	ud, err := GetUnifiedDiffString(diff)
	assertEqual(t, err, nil)
	assertEqual(t, SplitLines(ud)[:2], []string{"--- Original\n", "+++ Current\n"})

	cd, err := GetContextDiffString(ContextDiff(diff))
	assertEqual(t, err, nil)
	assertEqual(t, SplitLines(cd)[:2], []string{"*** Original\n", "--- Current\n"})
}

func TestOmitFilenames(t *testing.T) {
	diff := UnifiedDiff{
		A:   SplitLines("o\nn\ne\n"),
		B:   SplitLines("t\nw\no\n"),
		Eol: "\n",
	}
	ud, err := GetUnifiedDiffString(diff)
	assertEqual(t, err, nil)
	assertEqual(t, SplitLines(ud), []string{
		"@@ -0,0 +1,2 @@\n",
		"+t\n",
		"+w\n",
		"@@ -2,2 +3,0 @@\n",
		"-n\n",
		"-e\n",
		"\n",
	})

	cd, err := GetContextDiffString(ContextDiff(diff))
	assertEqual(t, err, nil)
	assertEqual(t, SplitLines(cd), []string{
		"***************\n",
		"*** 0 ****\n",
		"--- 1,2 ----\n",
		"+ t\n",
		"+ w\n",
		"***************\n",
		"*** 2,3 ****\n",
		"- n\n",
		"- e\n",
		"--- 3 ----\n",
		"\n",
	})
}

func TestSplitLines(t *testing.T) {
	allTests := []struct {
		input string
		want  []string
	}{
		{"foo", []string{"foo\n"}},
		{"foo\nbar", []string{"foo\n", "bar\n"}},
		{"foo\nbar\n", []string{"foo\n", "bar\n", "\n"}},
	}
	for _, test := range allTests {
		assertEqual(t, SplitLines(test.input), test.want)
	}
}

func benchmarkSplitLines(b *testing.B, count int) {
	str := strings.Repeat("foo\n", count)

	b.ResetTimer()

	n := 0
	for i := 0; i < b.N; i++ {
		n += len(SplitLines(str))
	}
}

func BenchmarkSplitLines100(b *testing.B) {
	benchmarkSplitLines(b, 100)
}

func BenchmarkSplitLines10000(b *testing.B) {
	benchmarkSplitLines(b, 10000)
}

func ExampleGetCloseMatches() {
	matches := GetCloseMatches("appel", []string{"ape", "apple", "peach", "puppy"}, 2, 0.6)
	fmt.Println(matches)
	// Output:
	// [apple ape]
}

func ExampleNDiff() {
	a := SplitLines("one\ntwo\nthree")
	b := SplitLines("zero\none\nthree")
	delta := NDiff(a, b)
	fmt.Print(strings.Join(delta, ""))
	// Output:
	// + zero
	//   one
	// - two
	//   three
}

func ExampleNDiffBytes() {
	a := []byte("one\ntwo\nthree")
	b := []byte("zero\none\nthree")
	delta := NDiffBytes(a, b, NDiffOptions{})
	fmt.Print(string(delta))
	// Output:
	// + zero
	//   one
	// - two
	//   three
}

func ExampleNDiffWith() {
	a := SplitLines("abc")
	b := SplitLines("axc")
	delta := NDiffWith(a, b, NDiffOptions{Intraline: true})
	// Trim trailing spaces on intraline lines for stable example output.
	for i, s := range delta {
		if strings.HasPrefix(s, "? ") {
			s = strings.TrimRight(s, " \n") + "\n"
			delta[i] = s
		}
	}
	fmt.Print(strings.Join(delta, ""))
	// Output:
	// - abc
	// ?  ^
	// + axc
	// ?  ^
}

func TestNDiffWith_NoIntraline_EqualsNDiff(t *testing.T) {
	a := SplitLines("one\ntwo\nthree")
	b := SplitLines("zero\none\nthree")
	got := NDiffWith(a, b, NDiffOptions{Intraline: false})
	want := NDiff(a, b)
	if strings.Join(got, "") != strings.Join(want, "") {
		t.Fatalf("NDiffWith (no intraline) != NDiff\nGot:\n%s\nWant:\n%s", strings.Join(got, ""), strings.Join(want, ""))
	}
}

func TestNDiffBytes_EqualsStringNDiff_ASCII(t *testing.T) {
	a := []byte("one\ntwo\nthree")
	b := []byte("zero\none\nthree")
	got := string(NDiffBytes(a, b, NDiffOptions{}))
	want := strings.Join(NDiff(SplitLines(string(a)), SplitLines(string(b))), "")
	if got != want {
		t.Fatalf("NDiffBytes != NDiff (ASCII)\nGot:\n%s\nWant:\n%s", got, want)
	}
}

func TestNDiffBytes_IgnoresIntralineOption(t *testing.T) {
	a := []byte("abc")
	b := []byte("axc")
	// Even if Intraline is requested, bytes mode should not emit '? ' lines.
	out := string(NDiffBytes(a, b, NDiffOptions{Intraline: true}))
	if strings.Contains(out, "? ") {
		t.Fatalf("bytes adapter should not emit intraline guides; got:\n%s", out)
	}
}

func ExampleDiffer_Compare() {
	d := &Differ{}
	delta := d.Compare(SplitLines("abc"), SplitLines("axc"))
	// Trim trailing spaces on intraline lines for stable example output.
	for i, s := range delta {
		if strings.HasPrefix(s, "? ") {
			s = strings.TrimRight(s, " \n") + "\n"
			delta[i] = s
		}
	}
	fmt.Print(strings.Join(delta, ""))
	// Output:
	// - abc
	// ?  ^
	// + axc
	// ?  ^
}

func TestIsLineJunk(t *testing.T) {
	// Blank
	assertEqual(t, IsLineJunk("\n"), true)
	assertEqual(t, IsLineJunk("   \n"), true)
	// Only '#'
	assertEqual(t, IsLineJunk("  #   \n"), true)
	// Non-junk
	assertEqual(t, IsLineJunk("hello\n"), false)
	assertEqual(t, IsLineJunk("#notjunk\n"), false)
}

func TestIsCharacterJunk(t *testing.T) {
	assertEqual(t, IsCharacterJunk(' '), true)
	assertEqual(t, IsCharacterJunk('\t'), true)
	assertEqual(t, IsCharacterJunk('\n'), false)
	assertEqual(t, IsCharacterJunk('x'), false)
}

func TestGetCloseMatches(t *testing.T) {
	poss := []string{"ape", "apple", "peach", "puppy"}
	got := GetCloseMatches("appel", poss, 3, 0.6)
	// Expect order by score desc with ties by original order; Python example yields ["apple", "ape"].
	assertEqual(t, got[:2], []string{"apple", "ape"})

	// Edge cases
	assertEqual(t, GetCloseMatches("", poss, 0, 0.6) == nil, true)
	assertEqual(t, GetCloseMatches("abc", poss, 3, -0.1) == nil, true)
	assertEqual(t, GetCloseMatches("abc", poss, 3, 1.1) == nil, true)

	// High cutoff yields empty
	assertEqual(t, len(GetCloseMatches("appel", poss, 3, 0.95)) == 0, true)
}

func TestNDiffRestoreRoundTrip(t *testing.T) {
	a := SplitLines("  1. Beautiful is better than ugly.\n  2. Explicit is better than implicit.\n  3. Simple is better than complex.\n  4. Complex is better than complicated.\n")
	b := SplitLines("  1. Beautiful is better than ugly.\n  3.   Simple is better than complex.\n  4. Complicated is better than complex.\n  5. Flat is better than nested.\n")

	delta := NDiff(a, b)
	a2 := Restore(delta, 1)
	b2 := Restore(delta, 2)

	assertEqual(t, a2, a)
	assertEqual(t, b2, b)

	// Ensure no '? ' lines are present in the basic ndiff output
	for _, line := range delta {
		if len(line) >= 2 {
			p := line[:2]
			if p != "  " && p != "+ " && p != "- " {
				t.Fatalf("unexpected ndiff prefix: %q in line %q", p, line)
			}
		}
	}
}

func TestDifferRestoreRoundTrip(t *testing.T) {
	a := SplitLines("one two three\nalpha beta\n")
	b := SplitLines("one tree three\nalpha bet\n")
	d := &Differ{}
	delta := d.Compare(a, b)
	a2 := Restore(delta, 1)
	b2 := Restore(delta, 2)
	assertEqual(t, a2, a)
	assertEqual(t, b2, b)
}

func TestDifferIntralineSimple(t *testing.T) {
	a := SplitLines("abc\n")
	b := SplitLines("axc\n")
	d := &Differ{}
	delta := d.Compare(a, b)
	// Allow an optional final equal newline entry (since SplitLines adds a terminal "\n").
	if !(len(delta) == 4 || len(delta) == 5) {
		t.Fatalf("unexpected delta length: %d (%v)", len(delta), delta)
	}
	// First four entries should be the replacement pair with intraline guides.
	assertEqual(t, delta[0], "- abc\n")
	if !(strings.HasPrefix(delta[1], "? ") && strings.Contains(delta[1], " ^ ") && strings.HasSuffix(delta[1], "\n")) {
		t.Fatalf("unexpected intraline for a: %q", delta[1])
	}
	assertEqual(t, delta[2], "+ axc\n")
	if !(strings.HasPrefix(delta[3], "? ") && strings.Contains(delta[3], " ^ ") && strings.HasSuffix(delta[3], "\n")) {
		t.Fatalf("unexpected intraline for b: %q", delta[3])
	}
	if len(delta) == 5 {
		assertEqual(t, delta[4], "  \n")
	}
}

func TestDifferFancyReplace_CrossAlignExact(t *testing.T) {
    // Case where the best alignment is cross-wise: one line moves positions.
    // Greedy pairing would compare unrelated lines first; fancyReplace should
    // find the exact match and split around it.
    a := SplitLines("abcd\nwxyz\n")
    b := SplitLines("wxyz\nabcq\n")
    d := &Differ{Fancy: true}
    delta := d.Compare(a, b)
    // Expect the exact-match line to be recognized as equal and the others as
    // delete/insert; trailing blank line equal (from SplitLines).
    want := []string{
        "- abcd\n",
        "  wxyz\n",
        "+ abcq\n",
        "  \n",
    }
    assertEqual(t, delta, want)
}

func TestDifferFancyReplace_MultiLineWithIntraline(t *testing.T) {
    // No exact equal lines inside the replacement block; fancyReplace should
    // align most-similar pairs and emit intraline guides for character diffs.
    a := SplitLines("spam and eggs\nfoo bar baz\nalpha beta")
    b := SplitLines("spam n eggs\nalpha bet\nfoo buz baz")
    d := &Differ{Fancy: true}
    delta := d.Compare(a, b)

    // Helper to confirm order: "- aline" appears before "+ bline" somewhere.
    hasOrderedPair := func(aline, bline string) bool {
        aidx, bidx := -1, -1
        for i := 0; i < len(delta); i++ {
            if delta[i] == "- "+aline+"\n" && aidx < 0 {
                aidx = i
            }
            if delta[i] == "+ "+bline+"\n" && bidx < 0 {
                bidx = i
            }
        }
        return aidx >= 0 && bidx >= 0 && aidx < bidx
    }

    if !hasOrderedPair("spam and eggs", "spam n eggs") {
        t.Fatalf("expected pair for spam line not found; delta:\n%s", strings.Join(delta, ""))
    }
    if !hasOrderedPair("foo bar baz", "foo buz baz") {
        t.Fatalf("expected pair for foo line not found; delta:\n%s", strings.Join(delta, ""))
    }
    if !hasOrderedPair("alpha beta", "alpha bet") {
        t.Fatalf("expected pair for alpha line not found; delta:\n%s", strings.Join(delta, ""))
    }

    // Ensure at least one intraline guide was emitted somewhere.
    sawGuide := false
    for _, s := range delta {
        if strings.HasPrefix(s, "? ") {
            sawGuide = true
            break
        }
    }
    if !sawGuide {
        t.Fatalf("expected at least one intraline '? ' guide; delta:\n%s", strings.Join(delta, ""))
    }
}

func TestDifferIntralineTabsPreserved(t *testing.T) {
    // Ensure intraline guide preserves tabs in the tag line to match visual columns.
    // Example: change after a tab should keep the tab in '? ' line.
    a := SplitLines("col1\tvalue\n")
    b := SplitLines("col1\tvalux\n")
    d := &Differ{Fancy: true, PreserveWS: true}
    delta := d.Compare(a, b)
    // Expect a replacement with intraline; find '? ' lines and ensure they include a tab.
    sawTabInGuide := false
    for _, s := range delta {
        if strings.HasPrefix(s, "? ") {
            if strings.ContainsRune(s, '\t') {
                sawTabInGuide = true
                break
            }
        }
    }
    if !sawTabInGuide {
        t.Fatalf("expected intraline guide to preserve tabs; delta:\n%s", strings.Join(delta, ""))
    }
}
