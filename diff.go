package t9njson

import (
	"encoding/json"
	"fmt"
	"github.com/sergi/go-diff/diffmatchpatch"
	"golang.org/x/exp/constraints"
	"io"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode"
	"unicode/utf8"
)

func MapToText(d map[string]string) string {
	keys := getKeys(d)
	var s string
	for _, k := range keys {
		s += d[k] + "\n\n"
	}
	return s
}

func TextToMap(text, path string) map[string]string {
	doc := map[string]string{}
	curLine := ""
	lastNewLine := 0
	lastLineLen := len(strconv.Itoa(len(strings.Split(text, "\n"))))
	for i, line := range strings.Split(text, "\n") {
		if curLine == "" && strings.TrimSpace(line) != "" {
			lastNewLine = i
		}
		if strings.TrimSpace(line) == "" {
			if curLine == "" {
				doc[fmt.Sprintf("%s:%0"+strconv.Itoa(lastLineLen)+"d", path, lastNewLine)] += "\n"
				continue
			}
			curLine = strings.TrimSpace(curLine)
			doc[fmt.Sprintf("%s:%0"+strconv.Itoa(lastLineLen)+"d", path, lastNewLine)] = curLine
			curLine = ""
			continue
		}
		curLine += line + "\n"
	}
	if curLine != "" {
		doc[fmt.Sprintf("%s:%0"+strconv.Itoa(lastLineLen)+"d", path, lastNewLine)] = curLine
	}
	return doc
}

func getKeys(doc map[string]string) []string {
	keys := make([]string, 0, len(doc))
	for k := range doc {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

func max[T constraints.Ordered](s []T) T {
	if len(s) == 0 {
		var zero T
		return zero
	}
	m := s[0]
	for _, v := range s {
		if m < v {
			m = v
		}
	}
	return m
}

func min[T constraints.Ordered](s []T) T {
	if len(s) == 0 {
		var zero T
		return zero
	}
	m := s[0]
	for _, v := range s {
		if m > v {
			m = v
		}
	}
	return m
}

type lexTree struct {
	isLeaf   bool
	tree     map[rune]*lexTree
	used     map[string]bool
	maxDepth int
}

func (t *lexTree) Add(s string) {
	if t.used == nil {
		t.used = make(map[string]bool)
	}
	t.used[s] = true
	t.add(s)
}
func (t *lexTree) add(s string) int {
	if t.tree == nil {
		t.tree = make(map[rune]*lexTree)
	}
	if t.used == nil {
		t.used = make(map[string]bool)
	}
	if s == "" {
		t.isLeaf = true
		return 0
	}
	n, e := t.tree[rune(s[0])]
	if !e {
		n = &lexTree{}
		t.tree[rune(s[0])] = n
	}
	depth := n.add(s[1:]) + 1
	t.maxDepth = max([]int{t.maxDepth, depth})
	return t.maxDepth
}

func (t *lexTree) findNewBetween(prev, next string) string {
	if prev == "" {
		prev = string('0' - 1)
	}
	if next == "" {
		next = string('z' + 1)
	}
	if prev[0] == next[0] {
		return string(prev[0]) + t.tree[rune(prev[0])].findNewBetween(prev[1:], next[1:])
	}
	minDepth := 100000
	minDepthI := prev[0]
	mean := next[0]/2 + prev[0]/2
	for i := prev[0]; i < next[0]; i++ {
		if i < '0' {
			continue
		}
		if t.tree[rune(i)] == nil {
			if minDepth > 0 {
				minDepth = 0
				minDepthI = i
			} else {
				dif := max([]uint8{mean - i, i - mean})
				if int(dif) > minDepth {
					minDepth = int(dif) * -1
					minDepthI = i
				}
			}
		} else {
			maxDepth := t.tree[rune(i)].maxDepth
			if maxDepth < minDepth {
				minDepth = maxDepth
				minDepthI = i
			}
		}
	}
	if t.tree[rune(minDepthI)] == nil {
		t.Add(string(minDepthI))
		return string(minDepthI)
	}
	newPrev := ""
	if prev[0] == minDepthI {
		newPrev = prev[1:]
	}
	return string(minDepthI) + t.tree[rune(minDepthI)].findNewBetween(newPrev, "")
}

var asciiSpace = [256]uint8{'\t': 1, '\n': 1, '\v': 1, '\f': 1, '\r': 1, ' ': 1}

func trimSpaceSuffix(s string) string {
	stop := len(s)
	for ; stop > 0; stop-- {
		c := s[stop-1]
		if c >= utf8.RuneSelf {
			return strings.TrimFunc(s[:stop], unicode.IsSpace)
		}
		if asciiSpace[c] == 0 {
			break
		}
	}
	return s[:stop]
}

type Doc struct {
	Doc      map[string]string
	UsedKeys []string
}

// WithPreservedKeysAndOrder returns a new Doc preserving the order of the keys and the keys of paragraphs that didn't change much
func WithPreservedKeysAndOrder(newText, path string, docPrevVersion map[string]string, usedKeys []string) *Doc {
	keysPrefix := path
	if len(docPrevVersion) != 0 {
		for k := range docPrevVersion {
			keysPrefix = strings.Split(k, ":")[0]
			break
		}
	}
	if docPrevVersion == nil || (len(docPrevVersion) == 0 && len(usedKeys) == 0) {
		docNew := TextToMap(newText, keysPrefix)
		for k := range docNew {
			usedKeys = append(usedKeys, k)
		}
		sort.Strings(usedKeys)
		return &Doc{TextToMap(newText, keysPrefix), usedKeys}
	}
	if usedKeys == nil {
		usedKeys = make([]string, 0, len(docPrevVersion))
	}
	// Preserve the keys when the paragraphs have been reordered
	// Use keys that are lexicographically between the keys around if a paragraph has been inserted

	prevText := MapToText(docPrevVersion)

	d := diffmatchpatch.New()
	diff := d.DiffBisect(prevText, newText, time.Now().Add(time.Minute))
	// fmt.Println(d.DiffPrettyText(diff))

	// add two maps with keys corresponding to the start line of the paragraph
	docPrevKeys := getKeys(docPrevVersion)
	// saveToFile("docFirstLines.md", []byte(prevText))


	diffUnified := []diffmatchpatch.Diff{}
	cf := 0
	for j, d := range append(diff, diffmatchpatch.Diff{Type: 3, Text: ""}) {
		if diff[cf].Type != d.Type {
			text := ""
			for _, d_ := range diff[cf:j] {
				text += strings.ReplaceAll(d_.Text, "\n\r", "\n")
			}
			diffUnified = append(diffUnified, diffmatchpatch.Diff{Type: diff[cf].Type, Text: text})
			cf = j
		}
	}
	diff = diffUnified

	// When lines (but not paragraphs) are added, the diff can show the paragraph ending with a single \n at the end,
	// the insertion with a single \n at the end, and leave a single \n at the beginning of the next paragraph.
	// We need to move the \n down the road: from the end of the paragraph to the beginning of the insertion, from the end of the insertion
	// to the beginning of the next paragraph.

	for i, d := range diff {
		if i < 2 {
			continue
		}
		if d.Type == diffmatchpatch.DiffEqual && diff[i-1].Type == diffmatchpatch.DiffInsert && diff[i-2].Type == diffmatchpatch.DiffEqual {
			if strings.HasPrefix(diff[i].Text, "\n") && strings.HasSuffix(diff[i-1].Text, "\n") && strings.HasSuffix(diff[i-2].Text, "\n") {
				diff[i].Text = "\n" + diff[i].Text
				diff[i-1].Text = "\n" + strings.TrimSuffix(diff[i-1].Text, "\n")
				diff[i-2].Text = strings.TrimSuffix(diff[i-2].Text, "\n")
			}
		}
	}

	diffSepByLines := make([]diffmatchpatch.Diff, 0)
	for j, d := range diff {
		s := strings.Split(d.Text, "\n\n")
		for i, sc := range s {
			if i == 0 && j > 0 {
				if d.Type == diff[j-1].Type && !strings.HasSuffix(diff[j-1].Text, "\n\n") {
					diffSepByLines[len(diffSepByLines)-1].Text += sc
					continue
				}
			}
			if i < len(s)-1 {
				sc += "\n\n"
			}
			diffSepByLines = append(diffSepByLines, diffmatchpatch.Diff{Text: sc, Type: d.Type})
		}
	}
	diffI := 0
	type diffLine struct {
		Key         string
		PreviousKey string
		NextKey     string
		OldLine     string
		NewLine     string
	}
	lines := make([]diffLine, 0)
	leftoverDiffNs := ""
	leftoverTextNs := ""
	for i := range docPrevKeys {
		k := docPrevKeys[i]
		previousKey := ""
		if i > 0 {
			previousKey = docPrevKeys[i-1]
		}
		nextKey := ""
		if i < len(docPrevKeys)-1 {
			nextKey = docPrevKeys[i+1]
		}
		if strings.HasSuffix(diffSepByLines[diffI].Text, "\n\n") && diffSepByLines[diffI].Type == diffmatchpatch.DiffInsert {
			lines = append(lines, diffLine{
				PreviousKey: previousKey,
				NextKey:     k,
				NewLine:     strings.TrimSuffix(diffSepByLines[diffI].Text, "\n\n"),
			})
			i--
			diffI++
			continue
		}
		if docPrevVersion[k]+"\n\n" == diffSepByLines[diffI].Text && diffSepByLines[diffI].Type == diffmatchpatch.DiffEqual {
			lines = append(lines, diffLine{
				Key:         k,
				PreviousKey: previousKey,
				NextKey:     nextKey,
				OldLine:     docPrevVersion[k],
				NewLine:     docPrevVersion[k],
			})
			diffI++
			continue
		}
		if docPrevVersion[k]+"\n\n" == diffSepByLines[diffI].Text && diffSepByLines[diffI].Type == diffmatchpatch.DiffDelete {
			lines = append(lines, diffLine{
				Key:         k,
				PreviousKey: previousKey,
				NextKey:     nextKey,
				OldLine:     docPrevVersion[k],
				NewLine:     "",
			})
			diffI++
			continue
		}
		oldLine := leftoverTextNs + docPrevVersion[k]
		oldLineLeft := ""
		oldLineRight := oldLine + "\n\n"
		newLine := leftoverDiffNs + ""
		diffIStart := diffI
		correctLine := true
		for {
			switch diffSepByLines[diffI].Type {
			case diffmatchpatch.DiffEqual:
				newLine += diffSepByLines[diffI].Text
				oldLineLeft += diffSepByLines[diffI].Text
				if !strings.HasPrefix(oldLineRight, diffSepByLines[diffI].Text) {
					fmt.Println("unexpected inconsistency on Equal", oldLineRight, "text", diffSepByLines[diffI].Text)
					fmt.Println(oldLineRight[:min([]int{len(diffSepByLines[diffI].Text), len(oldLineRight)})])
					for symb := 0; symb < min([]int{len(diffSepByLines[diffI].Text), len(oldLineRight)}); symb++ {
						fmt.Println(symb, diffSepByLines[diffI].Text[symb], oldLineRight[symb])
					}
					correctLine = false
				}
				oldLineRight = strings.TrimPrefix(oldLineRight, diffSepByLines[diffI].Text)
			case diffmatchpatch.DiffInsert:
				newLine += diffSepByLines[diffI].Text
				oldLineLeft += diffSepByLines[diffI].Text
			case diffmatchpatch.DiffDelete:
				if !strings.HasPrefix(oldLineRight, diffSepByLines[diffI].Text) {
					fmt.Println("unexpected inconsistency on Delete", oldLineRight, "text", diffSepByLines[diffI].Text)
					correctLine = false
				}
				oldLineRight = strings.TrimPrefix(oldLineRight, diffSepByLines[diffI].Text)
			default:
			}
			diffI++
			if strings.Contains(diffSepByLines[diffI-1].Text, "\n\n") {
				break
			}
			if diffI == len(diffSepByLines) {
				break
			}
		}
		newLine = strings.TrimSuffix(newLine, "\n\n")
		endTextNs := strings.TrimPrefix(oldLineRight, trimSpaceSuffix(oldLineRight))
		endDiffNs := strings.TrimPrefix(newLine, trimSpaceSuffix(newLine))
		leftoverDiffNs = strings.TrimPrefix(endDiffNs, endTextNs)
		leftoverTextNs = strings.TrimPrefix(endTextNs, endDiffNs)
		if strings.TrimSpace(oldLineRight) != "" || strings.TrimSpace(newLine) != strings.TrimSpace(oldLineLeft) {
			correctLine = false
		}
		if !correctLine {
			fmt.Println("Unexpected inconsistency", oldLine, newLine, diffIStart, diffI, len(diffSepByLines))
			fmt.Printf("%+v", diffSepByLines[diffIStart:diffI])
			break
		}
		updateDistance := d.DiffLevenshtein(d.DiffBisect(oldLine, newLine, time.Now().Add(time.Minute)))
		oldLineLen := utf8.RuneCountInString(oldLine)
		newLineLen := utf8.RuneCountInString(newLine)
		if updateDistance < max([]int{oldLineLen, newLineLen})-min([]int{oldLineLen, newLineLen})+max([]int{oldLineLen, newLineLen})/2 ||
			i == 0 {
			if strings.TrimSpace(strings.ReplaceAll(docPrevVersion[k], "\n\r", "\n")) == strings.TrimSpace(newLine) {
				// if the change is caused only by the replacements made here, don't make that change
				newLine = docPrevVersion[k]
			}
			lines = append(lines, diffLine{
				Key:         k,
				PreviousKey: previousKey,
				NextKey:     nextKey,
				OldLine:     docPrevVersion[k],
				NewLine:     newLine,
			})
		} else {
			lines = append(lines, diffLine{
				Key:         k,
				PreviousKey: previousKey,
				NextKey:     nextKey,
				OldLine:     docPrevVersion[k],
				NewLine:     "",
			})
			lines = append(lines, diffLine{
				PreviousKey: previousKey,
				NextKey:     nextKey,
				OldLine:     "",
				NewLine:     newLine,
			})
		}
	}

	lTree := lexTree{}
	uKeys := map[string]bool{}
	for _, l := range lines {
		if l.Key != "" {
			uKeys[l.Key] = true
			lTree.Add(l.Key)
		}
	}
	for _, k := range usedKeys {
		lTree.Add(k)
	}
	usedKeys = []string{}
	for k := range uKeys {
		usedKeys = append(usedKeys, k)
	}

	docNew := map[string]string{}

	for i, l := range lines {
		if l.NewLine == "" {
			continue
		}
		if l.Key == "" {
			if l.PreviousKey == "" {
				fmt.Printf("%+v", l)
				fmt.Println("Both the key ond the previous key are empty", i, l)
				break
			}
			l.Key = lTree.findNewBetween(l.PreviousKey, l.NextKey)
			lTree.Add(l.Key)
			usedKeys = append(usedKeys, l.Key)
		}
		docNew[l.Key] = l.NewLine
	}
	sort.Strings(usedKeys)
	return &Doc{docNew, usedKeys}
}

func UpdateT9nJson(filePath string) error {
	text, err := readFile(filePath)
	if err != nil {
		return err
	}
	ext := filepath.Ext(filePath)
	dir, path := filepath.Split(filePath)
	path = strings.TrimSuffix(path, ext)

	var prevDoc map[string]string
	f, err := readFile(dir + string(os.PathSeparator) + path + ".json")
	if err != nil {
		prevDoc = nil
	} else {
		err = json.Unmarshal(f, &prevDoc)
		if err != nil {
			return err
		}
	}

	var usedKeys []string
	usedKeysF, err := readFile(dir + string(os.PathSeparator) + path + ".usedKeys.json")
	if err != nil {
		usedKeys = nil
	} else {
		err = json.Unmarshal(usedKeysF, &usedKeys)
		if err != nil {
			return err
		}
	}
	doc := WithPreservedKeysAndOrder(string(text), path, prevDoc, usedKeys)
	j, err := json.Marshal(doc.Doc)
	if err != nil {
		return err
	}
	for i, d := range prevDoc {
		_, exists := doc.Doc[i]
		if !exists {
			fmt.Println("Deleted key", i)
			fmt.Println(d)
		}
	}
	for i, d := range doc.Doc{
		old, exists := prevDoc[i]
		if !exists {
			fmt.Println("New key", i)
			fmt.Println(d)
			continue
		}
		if old != d {
			fmt.Println("Changed string", i)
			fmt.Println("Old:", old)
			fmt.Println("New:", d)
		}
	}
	saveToFile(dir+string(os.PathSeparator)+path+".json.old", f)
	saveToFile(dir+string(os.PathSeparator)+path+".json", j)
	// save used keys to json
	j, err = json.Marshal(doc.UsedKeys)
	if err != nil {
		return err
	}
	saveToFile(dir+string(os.PathSeparator)+path+".usedKeys.json", j)
	return nil
}

func readFile(path string) ([]byte, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer file.Close()
	return io.ReadAll(file)
}

func saveToFile(filename string, data []byte) {
	out, err := os.OpenFile(filename, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, 0666)
	if err != nil {
		panic(err)
	}
	defer out.Close()
	_, err = out.Write(data)
	if err != nil {
		panic(err)
	}
	out.Sync()
}
