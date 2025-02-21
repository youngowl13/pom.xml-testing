package main

import (
	"encoding/xml"
	"fmt"
	"html/template"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"
)

// -------------------------------------------------------------------------------------
// CONFIG & CONSTANTS
// -------------------------------------------------------------------------------------

const (
	localPOMCacheDir = ".pom-cache"     // local cache for remote POM files
	pomWorkerCount   = 10               // concurrency worker pool
	fetchTimeout     = 30 * time.Second // HTTP GET timeout
)

// -------------------------------------------------------------------------------------
// GLOBALS
// -------------------------------------------------------------------------------------

var (
	pomRequests = make(chan fetchRequest, 50)
	wgWorkers   sync.WaitGroup

	pomCache    sync.Map // key="group:artifact:version" => *MavenPOM
	parentVisit sync.Map // detect parent cycles if needed

	channelOpen  = true
	channelMutex sync.Mutex
)

var spdxLicenseMap = map[string]struct {
	Name     string
	Copyleft bool
}{
	"MIT":          {Name: "MIT License", Copyleft: false},
	"Apache-2.0":   {Name: "Apache License 2.0", Copyleft: false},
	"BSD-2-CLAUSE": {Name: "BSD 2-Clause", Copyleft: false},
	"BSD-3-CLAUSE": {Name: "BSD 3-Clause", Copyleft: false},
	"MPL-2.0":      {Name: "Mozilla Public License 2.0", Copyleft: true},
	"LGPL-2.1":     {Name: "GNU Lesser GPL v2.1", Copyleft: true},
	"LGPL-3.0":     {Name: "GNU Lesser GPL v3.0", Copyleft: true},
	"GPL-2.0":      {Name: "GNU GPL v2.0", Copyleft: true},
	"GPL-3.0":      {Name: "GNU GPL v3.0", Copyleft: true},
	"AGPL-3.0":     {Name: "GNU Affero GPL v3.0", Copyleft: true},
}

// -------------------------------------------------------------------------------------
// DATA STRUCTURES
// -------------------------------------------------------------------------------------

type License struct {
	Name string `xml:"name"`
	URL  string `xml:"url"`
}

type POMDep struct {
	GroupID    string `xml:"groupId"`
	ArtifactID string `xml:"artifactId"`
	Version    string `xml:"version"`
	Scope      string `xml:"scope"`
	Optional   string `xml:"optional"`
}

type MavenPOM struct {
	XMLName        xml.Name  `xml:"project"`
	Licenses       []License `xml:"licenses>license"`
	Dependencies   []POMDep  `xml:"dependencies>dependency"`
	DependencyMgmt struct {
		Dependencies []POMDep `xml:"dependencies>dependency"`
	} `xml:"dependencyManagement"`
}

type DependencyNode struct {
	Name       string
	Version    string
	License    string
	Copyleft   bool
	Parent     string // "direct" or "group/artifact:version"
	Transitive []*DependencyNode
}

type ExtendedDep struct {
	Display string
	Lookup  string
	Parent  string
	License string
}

// For each discovered pom.xml we produce one section
type PomReportSection struct {
	FilePath        string
	DirectDeps      map[string]string // direct from local pom.xml
	AllDeps         map[string]ExtendedDep
	DependencyTree  []*DependencyNode
	TransitiveCount int
	DirectCount     int
	IndirectCount   int
	CopyleftCount   int
	UnknownCount    int
}

// BFS state
type depState struct {
	Version string
	Depth   int
}

type queueItem struct {
	GroupArtifact string
	Version       string
	Depth         int
	ParentNode    *DependencyNode
}

// concurrency
type fetchRequest struct {
	GroupID    string
	ArtifactID string
	Version    string
	ResultChan chan fetchResult
}

type fetchResult struct {
	POM *MavenPOM
	Err error
}

// -------------------------------------------------------------------------------------
// 1) Find ALL pom.xml files
// -------------------------------------------------------------------------------------

func findAllPOMFiles(root string) ([]string, error) {
	var pomFiles []string
	err := filepath.Walk(root, func(path string, info os.FileInfo, e error) error {
		if e != nil {
			return e
		}
		if !info.IsDir() && strings.EqualFold(info.Name(), "pom.xml") {
			pomFiles = append(pomFiles, path)
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	if len(pomFiles) == 0 {
		return nil, fmt.Errorf("no pom.xml files found in %s", root)
	}
	return pomFiles, nil
}

// parseOneLocalPOMFile extracts direct dependencies from that local pom.xml
func parseOneLocalPOMFile(filePath string) (map[string]string, error) {
	data, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("cannot read local pom.xml '%s': %v", filePath, err)
	}
	var pom MavenPOM
	if e2 := xml.Unmarshal(data, &pom); e2 != nil {
		return nil, fmt.Errorf("error parsing local pom.xml '%s': %v", filePath, e2)
	}
	depMap := make(map[string]string)
	for _, d := range pom.Dependencies {
		if skipScope(d.Scope, d.Optional) {
			continue
		}
		g := d.GroupID
		a := d.ArtifactID
		v := d.Version
		if v == "" {
			v = "unknown"
		}
		key := g + "/" + a
		depMap[key] = v
	}
	return depMap, nil
}

// skip test/provided/system or optional
func skipScope(scope, optional string) bool {
	s := strings.ToLower(strings.TrimSpace(scope))
	if s == "test" || s == "provided" || s == "system" {
		return true
	}
	if strings.EqualFold(strings.TrimSpace(optional), "true") {
		return true
	}
	return false
}

// -------------------------------------------------------------------------------------
// BFS
// -------------------------------------------------------------------------------------

func buildTransitiveClosure(sections []PomReportSection) {
	for i := range sections {
		sec := &sections[i]
		fmt.Printf("BFS: Building transitive closure for %s\n", sec.FilePath)

		allDeps := make(map[string]ExtendedDep) // key="group/artifact@version" => ExtendedDep

		// fill direct
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			allDeps[key] = ExtendedDep{
				Display: ver,
				Lookup:  ver,
				Parent:  "direct",
				License: "",
			}
		}
		stateMap := make(map[string]depState)
		nodeMap := make(map[string]*DependencyNode)
		var rootNodes []*DependencyNode
		var queue []queueItem
		visited := make(map[string]bool)

		// BFS init from direct
		for ga, ver := range sec.DirectDeps {
			key := ga + "@" + ver
			visited[key] = true
			node := &DependencyNode{
				Name:    ga,
				Version: ver,
				Parent:  "direct",
			}
			rootNodes = append(rootNodes, node)
			nodeMap[key] = node
			stateMap[key] = depState{Version: ver, Depth: 1}
			queue = append(queue, queueItem{
				GroupArtifact: ga,
				Version:       ver,
				Depth:         1,
				ParentNode:    node,
			})
		}

		for len(queue) > 0 {
			it := queue[0]
			queue = queue[1:]
			fmt.Printf("BFS: Processing %s@%s (depth %d)\n", it.GroupArtifact, it.Version, it.Depth)
			group, artifact := splitGA(it.GroupArtifact)
			if group == "" || artifact == "" {
				continue
			}
			if strings.ToLower(it.Version) == "unknown" {
				fmt.Printf("BFS: version is 'unknown'; skipping sub-deps.\n")
				continue
			}
			pom, err := concurrentFetchPOM(group, artifact, it.Version)
			if err != nil || pom == nil {
				fmt.Printf("BFS: skipping %s:%s => fetch error or nil\n", group, artifact)
				continue
			}
			// attach license
			if it.ParentNode != nil {
				lic := detectLicense(pom)
				it.ParentNode.License = lic
				it.ParentNode.Copyleft = isCopyleft(lic)
			}
			// parse sub-deps
			for _, d := range pom.Dependencies {
				if skipScope(d.Scope, d.Optional) {
					continue
				}
				childGA := d.GroupID + "/" + d.ArtifactID
				cv := d.Version
				if cv == "" {
					cv = "unknown"
				}
				childDepth := it.Depth + 1
				childKey := childGA + "@" + cv
				if _, found := visited[childKey]; found {
					continue
				}
				visited[childKey] = true
				curSt, seen := stateMap[childKey]
				if !seen {
					stateMap[childKey] = depState{Version: cv, Depth: childDepth}
					childNode := &DependencyNode{
						Name:    childGA,
						Version: cv,
						Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
					}
					nodeMap[childKey] = childNode
					allDeps[childKey] = ExtendedDep{
						Display: cv,
						Lookup:  cv,
						Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
						License: "",
					}
					if it.ParentNode != nil {
						it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
					}
					queue = append(queue, queueItem{
						GroupArtifact: childGA,
						Version:       cv,
						Depth:         childDepth,
						ParentNode:    childNode,
					})
				} else {
					if childDepth < curSt.Depth {
						stateMap[childKey] = depState{Version: cv, Depth: childDepth}
						childNode, ok := nodeMap[childKey]
						if !ok {
							childNode = &DependencyNode{
								Name:    childGA,
								Version: cv,
								Parent:  fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version),
							}
							nodeMap[childKey] = childNode
						} else {
							childNode.Version = cv
							childNode.Parent  = fmt.Sprintf("%s:%s", it.GroupArtifact, it.Version)
						}
						if it.ParentNode != nil {
							it.ParentNode.Transitive = append(it.ParentNode.Transitive, childNode)
						}
						queue = append(queue, queueItem{
							GroupArtifact: childGA,
							Version:       cv,
							Depth:         childDepth,
							ParentNode:    childNode,
						})
					}
				}
			}
		}
		// fill BFS
		for _, root := range rootNodes {
			fillDepMap(root, allDeps)
		}
		sec.AllDeps = allDeps
		sec.DependencyTree = rootNodes
		total := len(allDeps)
		directCount := 0
		for k, ext := range allDeps {
			if ext.Parent == "direct" || strings.HasSuffix(k, "@unknown") {
				directCount++
			}
		}
		sec.TransitiveCount = total - directCount
	}
}

// fill BFS final
func fillDepMap(n *DependencyNode, all map[string]ExtendedDep) {
	key := n.Name + "@" + n.Version
	info, exists := all[key]
	if !exists {
		info = ExtendedDep{
			Display: n.Version,
			Lookup:  n.Version,
			Parent:  n.Parent,
		}
	} else {
		info.Display = n.Version
		info.Lookup  = n.Version
		info.Parent  = n.Parent
	}
	info.License = n.License
	all[key] = info
	for _, c := range n.Transitive {
		fillDepMap(c, all)
	}
}

// concurrency worker
func pomFetchWorker() {
	defer wgWorkers.Done()
	for req := range pomRequests {
		fmt.Printf("Worker fetch => %s:%s:%s\n", req.GroupID, req.ArtifactID, req.Version)
		pom, err := fetchRemotePOM(req.GroupID, req.ArtifactID, req.Version)
		req.ResultChan <- fetchResult{pom, err}
	}
}

func concurrentFetchPOM(g, a, v string) (*MavenPOM, error) {
	key := fmt.Sprintf("%s:%s:%s", g, a, v)
	if c, ok := pomCache.Load(key); ok {
		fmt.Printf("concurrentFetchPOM: Cache HIT for %s\n", key)
		return c.(*MavenPOM), nil
	}
	channelMutex.Lock()
	open := channelOpen
	channelMutex.Unlock()
	if !open {
		fmt.Printf("concurrentFetchPOM: channel closed => direct fetch for %s\n", key)
		pom, err := fetchRemotePOM(g, a, v)
		if err == nil && pom != nil {
			pomCache.Store(key, pom)
		}
		return pom, err
	}
	req := fetchRequest{
		GroupID:    g,
		ArtifactID: a,
		Version:    v,
		ResultChan: make(chan fetchResult, 1),
	}
	pomRequests <- req
	res := <-req.ResultChan
	if res.Err == nil && res.POM != nil {
		pomCache.Store(key, res.POM)
	}
	return res.POM, res.Err
}

// fetchRemotePOM tries central & google
func fetchRemotePOM(g, a, v string) (*MavenPOM, error) {
	groupPath := strings.ReplaceAll(g, ".", "/")
	urlC := fmt.Sprintf("https://repo1.maven.org/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	urlG := fmt.Sprintf("https://dl.google.com/dl/android/maven2/%s/%s/%s/%s-%s.pom", groupPath, a, v, a, v)
	fmt.Printf("fetchRemotePOM => Trying central: %s\n", urlC)
	if pm, e := fetchPOMFromURL(urlC); e == nil && pm != nil {
		pomCache.Store(fmt.Sprintf("%s:%s:%s", g, a, v), pm)
		return pm, nil
	}
	fmt.Printf("fetchRemotePOM => Trying google: %s\n", urlG)
	if pm, e2 := fetchPOMFromURL(urlG); e2 == nil && pm != nil {
		pomCache.Store(fmt.Sprintf("%s:%s:%s", g, a, v), pm)
		return pm, nil
	}
	return nil, fmt.Errorf("could not fetch remote POM for %s:%s:%s", g, a, v)
}

func fetchPOMFromURL(url string) (*MavenPOM, error) {
	client := http.Client{Timeout: fetchTimeout}
	resp, err := client.Get(url)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("HTTP %d for %s", resp.StatusCode, url)
	}
	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}
	var pom MavenPOM
	if e2 := xml.Unmarshal(data, &pom); e2 != nil {
		return nil, e2
	}
	return &pom, nil
}

// detectLicense
func detectLicense(pom *MavenPOM) string {
	if len(pom.Licenses) == 0 {
		return "Unknown"
	}
	lic := strings.TrimSpace(pom.Licenses[0].Name)
	if lic == "" {
		return "Unknown"
	}
	up := strings.ToUpper(lic)
	for spdxID, data := range spdxLicenseMap {
		if strings.EqualFold(lic, spdxID) || up == strings.ToUpper(spdxID) {
			return data.Name
		}
	}
	return lic
}

// isCopyleft
func isCopyleft(name string) bool {
	for spdxID, data := range spdxLicenseMap {
		if data.Copyleft && (strings.EqualFold(name, data.Name) || strings.EqualFold(name, spdxID)) {
			return true
		}
	}
	copyleftKeywords := []string{
		"GPL", "LGPL", "AGPL", "CC BY-SA", "CC-BY-SA", "MPL", "EPL", "CPL",
		"CDDL", "EUPL", "Affero", "OSL", "CeCILL",
		"GNU General Public License",
		"GNU Lesser General Public License",
		"Mozilla Public License",
		"Common Development and Distribution License",
		"Eclipse Public License",
		"Common Public License",
		"European Union Public License",
		"Open Software License",
	}
	up := strings.ToUpper(name)
	for _, kw := range copyleftKeywords {
		if strings.Contains(up, strings.ToUpper(kw)) {
			return true
		}
	}
	return false
}

// splitGA => "group/artifact" => (group, artifact)
func splitGA(ga string) (string, string) {
	parts := strings.Split(ga, "/")
	if len(parts) != 2 {
		return "", ""
	}
	return parts[0], parts[1]
}

// -------------------------------------------------------------------------------------
// HTML REPORT
// -------------------------------------------------------------------------------------

func buildTreeHTML(node *DependencyNode, level int) string {
	class := "non-copyleft"
	if node.License == "Unknown" {
		class = "unknown-license"
	} else if node.Copyleft {
		class = "copyleft"
	}
	summary := fmt.Sprintf("%s@%s (License: %s)", node.Name, node.Version, node.License)
	var sb strings.Builder
	sb.WriteString(fmt.Sprintf(`<details class="%s" style="margin-left:%dem;">`, class, level))
	sb.WriteString(fmt.Sprintf(`<summary>%s</summary>`, template.HTMLEscapeString(summary)))
	for _, c := range node.Transitive {
		sb.WriteString(buildTreeHTML(c, level+1))
	}
	sb.WriteString("</details>")
	return sb.String()
}

func buildTreesHTML(nodes []*DependencyNode) template.HTML {
	var buf strings.Builder
	for _, n := range nodes {
		buf.WriteString(buildTreeHTML(n, 0))
	}
	return template.HTML(buf.String())
}

func generateHTMLReport(sections []PomReportSection) error {
	outDir := "./license-checker"
	if err := os.MkdirAll(outDir, 0755); err != nil {
		return err
	}
	const tmplSrc = `<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Multi-POM Dependency License Report</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 20px; }
    h1 { color: #2c3e50; }
    h2 { margin-top: 40px; }
    table { width: 100%; border-collapse: collapse; margin-bottom: 40px; }
    th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
    th { background-color: #f2f2f2; }
    tr:nth-child(even) { background-color: #f9f9f9; }
    a { color: #3498db; text-decoration: none; }
    a:hover { text-decoration: underline; }
    tr.copyleft { background-color: #ffdddd; }
    tr.non-copyleft { background-color: #ddffdd; }
    tr.unknown-license { background-color: #ffffdd; }

    details.copyleft > summary {
      background-color: #ffdddd; padding: 2px 4px; border-radius: 4px;
    }
    details.unknown-license > summary {
      background-color: #ffffdd; padding: 2px 4px; border-radius: 4px;
    }
    details.non-copyleft > summary {
      background-color: #ddffdd; padding: 2px 4px; border-radius: 4px;
    }
  </style>
</head>
<body>
  <h1>Multi-POM Dependency License Report</h1>
  {{ range . }}
    <h2>POM File: {{ .FilePath }}</h2>
    <p>
      <strong>Direct Dependencies:</strong> {{ .DirectCount }}<br>
      <strong>Indirect Dependencies:</strong> {{ .IndirectCount }}<br>
      <strong>Copyleft Dependencies:</strong> {{ .CopyleftCount }}<br>
      <strong>Unknown License Dependencies:</strong> {{ .UnknownCount }}
    </p>
    <h3>Dependency Table</h3>
    <table>
      <thead>
        <tr>
          <th>Dependency</th>
          <th>Version</th>
          <th>Parent</th>
          <th>License</th>
          <th>Project Details</th>
          <th>POM File</th>
        </tr>
      </thead>
      <tbody>
        {{ range $dep, $info := .AllDeps }}
          {{ if eq $info.License "Unknown" }}
            <tr class="unknown-license">
          {{ else if isCopyleft $info.License }}
            <tr class="copyleft">
          {{ else }}
            <tr class="non-copyleft">
          {{ end }}
            <td>{{ $dep }}</td>
            <td>{{ $info.Display }}</td>
            <td>{{ $info.Parent }}</td>
            <td>{{ $info.License }}</td>
            <td><a href="https://www.google.com/search?q={{ $dep }}+{{ $info.Lookup }}+license" target="_blank">Search</a></td>
            <td><a href="https://repo1.maven.org/maven2/{{ $dep }}/{{ $info.Lookup }}" target="_blank">POM Link</a></td>
          </tr>
        {{ end }}
      </tbody>
    </table>

    <h3>Dependency Tree</h3>
    {{ buildTreesHTML .DependencyTree }}
  {{ end }}
</body>
</html>
`
	tmpl, err := template.New("report").Funcs(template.FuncMap{
		"buildTreesHTML": buildTreesHTML,
		"isCopyleft":     isCopyleft,
	}).Parse(tmplSrc)
	if err != nil {
		return err
	}
	outPath := filepath.Join(outDir, "dependency-license-report.html")
	f, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer f.Close()
	if e2 := tmpl.Execute(f, sections); e2 != nil {
		return e2
	}
	fmt.Printf("✅ Report generated at %s\n", outPath)
	return nil
}

// -------------------------------------------------------------------------------------
// MAIN
// -------------------------------------------------------------------------------------

func main() {
	// Start concurrency pool
	for i := 0; i < pomWorkerCount; i++ {
		wgWorkers.Add(1)
		go pomFetchWorker()
	}

	fmt.Println("Starting multi-POM dependency analysis...")

	pomFiles, err := findAllPOMFiles(".")
	if err != nil {
		fmt.Printf("Error finding pom.xml files: %v\n", err)
		os.Exit(1)
	}
	if len(pomFiles) == 0 {
		fmt.Println("No pom.xml found.")
		os.Exit(0)
	}
	fmt.Printf("Found %d pom.xml file(s):\n", len(pomFiles))
	for _, pf := range pomFiles {
		fmt.Printf(" - %s\n", pf)
	}

	var sections []PomReportSection
	for _, pf := range pomFiles {
		directDeps, e2 := parseOneLocalPOMFile(pf)
		if e2 != nil {
			fmt.Printf("Error parsing local POM %s: %v\n", pf, e2)
			continue
		}
		sections = append(sections, PomReportSection{
			FilePath:   pf,
			DirectDeps: directDeps,
			AllDeps:    make(map[string]ExtendedDep),
		})
	}

	if len(sections) == 0 {
		fmt.Println("No valid pom.xml files to process; exiting.")
		os.Exit(0)
	}

	fmt.Println("Building BFS concurrency for transitive dependencies across discovered POMs...")
	buildTransitiveClosure(sections)

	// close concurrency channel
	channelMutex.Lock()
	channelOpen = false
	channelMutex.Unlock()
	close(pomRequests)
	wgWorkers.Wait()

	// compute final summary for each POM file
	for i := range sections {
		sec := &sections[i]
		var directCount, indirectCount, copyleftCount, unknownCount int
		for k, info := range sec.AllDeps {
			if info.Parent == "direct" || strings.HasSuffix(k, "@unknown") {
				directCount++
			} else {
				indirectCount++
			}
			if isCopyleft(info.License) {
				copyleftCount++
			}
			if info.License == "Unknown" {
				unknownCount++
			}
		}
		sec.DirectCount = directCount
		sec.IndirectCount = indirectCount
		sec.CopyleftCount = copyleftCount
		sec.UnknownCount  = unknownCount
	}

	fmt.Println("Generating HTML report with summary, parent column, BFS tree for each POM...")
	if err := generateHTMLReport(sections); err != nil {
		fmt.Printf("Error generating HTML: %v\n", err)
		os.Exit(1)
	}

	fmt.Println("Analysis complete.")
}
