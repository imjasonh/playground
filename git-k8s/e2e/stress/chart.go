package main

import (
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"html"
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"syscall"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
)

type series struct {
	name  string
	color string
	pts   [][2]float64
	step  bool
	dash  bool
}

var palette = []string{"#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd", "#8c564b", "#e377c2", "#7f7f7f", "#bcbd22", "#17becf"}

// chartCmd draws, for the runs it's given, the cumulative landings and the
// total queue depth of every run on one chart each, and each run's queue
// depths, test Pods, and CPU use.
func chartCmd(args []string) error {
	fs := flag.NewFlagSet("chart", flag.ExitOnError)
	out := fs.String("out", ".", "directory for the charts")
	png := fs.Bool("png", true, "also write PNG files, with headless Chrome")
	_ = fs.Parse(args)
	if err := os.MkdirAll(*out, 0o755); err != nil {
		return err
	}
	var landings, queues []series
	var files []string
	xmax := 0.0
	for i, dir := range fs.Args() {
		run, err := loadRun(dir)
		if err != nil {
			return err
		}
		b, err := os.ReadFile(filepath.Join(dir, "summary.json"))
		if err != nil {
			return err
		}
		var s summary
		if err := json.Unmarshal(b, &s); err != nil {
			return err
		}
		label := filepath.Base(dir)
		color := palette[i%len(palette)]
		planned := map[string]bool{}
		for _, bp := range run.plan.Branches {
			planned[gitk8s.BranchObjectName(bp.Repo, bp.Name)] = true
		}
		seen := map[string]bool{}
		var times []float64
		for _, rc := range run.recs {
			if rc.Kind == "event" && rc.event.Reason == "Landed" && rc.event.NS == run.plan.NS && planned[rc.event.Object] && !seen[rc.event.Object] {
				seen[rc.event.Object] = true
				times = append(times, secs(evTime(rc).Sub(s.Start)))
			}
		}
		slices.Sort(times)
		pts := [][2]float64{{0, 0}}
		for k, t := range times {
			pts = append(pts, [2]float64{t, float64(k + 1)})
		}
		landings = append(landings, series{name: label, color: color, pts: pts, step: true})
		end := s.LastLanding + 20
		xmax = max(xmax, end)

		var total [][2]float64
		perRepo := map[string][][2]float64{}
		var pods [][2]float64
		for _, rc := range run.recs {
			if rc.Kind != "tick" {
				continue
			}
			x := secs(rc.T.Sub(s.Start))
			if x < -10 || x > end {
				continue
			}
			sum := 0
			for key, tp := range rc.tick.Parents {
				sum += tp.Queue
				repo := strings.TrimPrefix(key, run.plan.NS+"/")
				perRepo[repo] = append(perRepo[repo], [2]float64{x, float64(tp.Queue)})
			}
			total = append(total, [2]float64{x, float64(sum)})
			pods = append(pods, [2]float64{x, float64(rc.tick.Pods)})
		}
		queues = append(queues, series{name: label, color: color, pts: total, step: true})

		var detail []series
		for j, repo := range sortedKeys(perRepo) {
			detail = append(detail, series{name: "queue " + repo, color: palette[j%len(palette)], pts: perRepo[repo], step: true})
		}
		if s.Gotest {
			detail = append(detail, series{name: "test Pods running", color: "#000000", pts: pods, step: true, dash: true})
		}
		name := filepath.Join(*out, label+"-queue.svg")
		if err := os.WriteFile(name, []byte(lineChart(label+": queue depth and test Pods", "seconds after the first push", "branches or Pods", detail, -10, end)), 0o644); err != nil {
			return err
		}
		files = append(files, name)

		cpu := cpuSeries(run, s.Start, end)
		name = filepath.Join(*out, label+"-cpu.svg")
		if err := os.WriteFile(name, []byte(lineChart(label+": kind node CPU (5 s mean)", "seconds after the first push", "cores", cpu, -10, end)), 0o644); err != nil {
			return err
		}
		files = append(files, name)
	}
	name := filepath.Join(*out, "landings.svg")
	if err := os.WriteFile(name, []byte(lineChart("Cumulative landings", "seconds after the first push", "branches landed", landings, 0, xmax)), 0o644); err != nil {
		return err
	}
	files = append(files, name)
	name = filepath.Join(*out, "queue-depth.svg")
	if err := os.WriteFile(name, []byte(lineChart("Branches in merge queues, all repositories", "seconds after the first push", "branches", queues, -10, xmax)), 0o644); err != nil {
		return err
	}
	files = append(files, name)
	if !*png {
		return nil
	}
	chrome := findChrome()
	if chrome == "" {
		return fmt.Errorf("wrote the SVG files to %s, but found no Chrome or Chromium to make PNG files with; pass -png=false to skip them", *out)
	}
	var errs []error
	for _, f := range files {
		if err := toPNG(chrome, f); err != nil {
			errs = append(errs, err)
		}
	}
	return errors.Join(errs...)
}

// findChrome returns the path of Chrome or Chromium, or "" if neither is on
// PATH.
func findChrome() string {
	for _, name := range []string{"google-chrome", "google-chrome-stable", "chromium", "chromium-browser"} {
		if p, err := exec.LookPath(name); err == nil {
			return p
		}
	}
	return ""
}

// cpuSeries returns the node's CPU use and its biggest groups, as 5-second
// means.
func cpuSeries(run *runData, start time.Time, end float64) []series {
	groupOf := func(g string) string {
		switch {
		case g == "test-pods", g == "git-k8s", g == "go-cache":
			return g
		case strings.HasPrefix(g, "check-"):
			return "check Deployments"
		// Some recorded runs count the control plane's static Pods as
		// unknown-pods.
		case g == "kube-apiserver", g == "etcd", g == "kube-controller-manager", g == "kube-scheduler", g == "unknown-pods":
			return "control plane"
		}
		return "rest of the node"
	}
	order := []string{"node", "test-pods", "check Deployments", "git-k8s", "control plane", "go-cache", "rest of the node"}
	raw := map[string][][2]float64{}
	first := true
	for _, rc := range run.recs {
		if rc.Kind != "cpu" {
			continue
		}
		// In some recorded runs, the first sample counts all the CPU that
		// each Pod had used since it started.
		if first {
			first = false
			continue
		}
		x := secs(rc.T.Sub(start))
		if x < -15 || x > end+5 {
			continue
		}
		vals := map[string]float64{"node": rc.cpu.Node}
		for g, v := range rc.cpu.Groups {
			vals[groupOf(g)] += v
		}
		for _, name := range order {
			raw[name] = append(raw[name], [2]float64{x, vals[name]})
		}
	}
	var out []series
	for i, name := range order {
		pts := raw[name]
		var smooth [][2]float64
		for j := range pts {
			lo := max(0, j-2)
			hi := min(len(pts), j+3)
			sum := 0.0
			for _, p := range pts[lo:hi] {
				sum += p[1]
			}
			smooth = append(smooth, [2]float64{pts[j][0], sum / float64(hi-lo)})
		}
		out = append(out, series{name: name, color: palette[i%len(palette)], pts: smooth, dash: name == "node"})
	}
	return out
}

func niceStep(raw float64) float64 {
	if raw <= 0 {
		return 1
	}
	exp := math.Floor(math.Log10(raw))
	f := raw / math.Pow(10, exp)
	var nf float64
	switch {
	case f < 1.5:
		nf = 1
	case f < 3:
		nf = 2
	case f < 7:
		nf = 5
	default:
		nf = 10
	}
	return nf * math.Pow(10, exp)
}

// tickLabel rounds v for an axis label. math.Ceil of a small negative
// number is -0, which %g prints with a minus sign.
func tickLabel(v float64) float64 {
	v = math.Round(v*100) / 100
	if v == 0 {
		return 0
	}
	return v
}

func lineChart(title, xlabel, ylabel string, ss []series, xmin, xmax float64) string {
	const w, h = 960.0, 540.0
	const ml, mr, mt, mb = 70.0, 210.0, 50.0, 60.0
	pw, ph := w-ml-mr, h-mt-mb
	if xmax <= xmin {
		xmax = xmin + 1
	}
	ymax := 0.0
	for _, s := range ss {
		for _, p := range s.pts {
			if p[0] >= xmin && p[0] <= xmax {
				ymax = max(ymax, p[1])
			}
		}
	}
	if ymax == 0 {
		ymax = 1
	}
	ystep := niceStep(ymax / 5)
	ymax = math.Ceil(ymax/ystep) * ystep
	xstep := niceStep((xmax - xmin) / 8)
	X := func(x float64) float64 { return ml + (min(max(x, xmin), xmax)-xmin)/(xmax-xmin)*pw }
	Y := func(y float64) float64 { return mt + ph - y/ymax*ph }
	var b strings.Builder
	p := func(format string, args ...any) { fmt.Fprintf(&b, format, args...) }
	p(`<svg xmlns="http://www.w3.org/2000/svg" width="%.0f" height="%.0f" viewBox="0 0 %.0f %.0f" font-family="DejaVu Sans, Helvetica, Arial, sans-serif" font-size="13">`+"\n", w, h, w, h)
	p(`<rect width="100%%" height="100%%" fill="#ffffff"/>` + "\n")
	p(`<text x="%.0f" y="28" font-size="17" font-weight="bold">%s</text>`+"\n", ml, html.EscapeString(title))
	for y := 0.0; y <= ymax+ystep/2; y += ystep {
		p(`<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#e5e5e5"/>`+"\n", ml, Y(y), ml+pw, Y(y))
		p(`<text x="%.1f" y="%.1f" text-anchor="end" fill="#444">%g</text>`+"\n", ml-8, Y(y)+4, tickLabel(y))
	}
	for x := math.Ceil(xmin/xstep) * xstep; x <= xmax+xstep/100; x += xstep {
		p(`<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#f0f0f0"/>`+"\n", X(x), mt, X(x), mt+ph)
		p(`<text x="%.1f" y="%.1f" text-anchor="middle" fill="#444">%g</text>`+"\n", X(x), mt+ph+20, tickLabel(x))
	}
	p(`<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="none" stroke="#888"/>`+"\n", ml, mt, pw, ph)
	p(`<text x="%.1f" y="%.1f" text-anchor="middle">%s</text>`+"\n", ml+pw/2, h-15, html.EscapeString(xlabel))
	p(`<text transform="translate(18 %.1f) rotate(-90)" text-anchor="middle">%s</text>`+"\n", mt+ph/2, html.EscapeString(ylabel))
	for i, s := range ss {
		var d strings.Builder
		started := false
		for _, pt := range s.pts {
			if pt[0] < xmin || pt[0] > xmax {
				continue
			}
			switch {
			case !started:
				fmt.Fprintf(&d, "M%.1f %.1f", X(pt[0]), Y(pt[1]))
				started = true
			case s.step:
				fmt.Fprintf(&d, " H%.1f V%.1f", X(pt[0]), Y(pt[1]))
			default:
				fmt.Fprintf(&d, " L%.1f %.1f", X(pt[0]), Y(pt[1]))
			}
		}
		if s.step && started {
			fmt.Fprintf(&d, " H%.1f", X(xmax))
		}
		dash := ""
		if s.dash {
			dash = ` stroke-dasharray="6 4"`
		}
		p(`<path d="%s" fill="none" stroke="%s" stroke-width="2"%s/>`+"\n", d.String(), s.color, dash)
		ly := mt + 14 + float64(i)*20
		p(`<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="%s" stroke-width="3"%s/>`+"\n", ml+pw+14, ly-4, ml+pw+38, ly-4, s.color, dash)
		p(`<text x="%.1f" y="%.1f">%s</text>`+"\n", ml+pw+44, ly, html.EscapeString(s.name))
	}
	p("</svg>\n")
	return b.String()
}

// toPNG renders an SVG file to a PNG file next to it with headless Chrome,
// which writes the screenshot but doesn't always exit, so toPNG stops it
// once the file is complete.
func toPNG(chrome, svgPath string) error {
	svg, err := os.ReadFile(svgPath)
	if err != nil {
		return err
	}
	base := strings.TrimSuffix(svgPath, ".svg")
	page, png := base+".html", base+".png"
	if err := os.WriteFile(page, []byte("<!doctype html><html><head><style>html,body{margin:0;background:#fff}</style></head><body>"+string(svg)+"</body></html>"), 0o644); err != nil {
		return err
	}
	defer os.Remove(page)
	_ = os.Remove(png)
	profile, err := os.MkdirTemp("", "stress-chrome-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(profile)
	abs, _ := filepath.Abs(page)
	cmd := exec.Command(chrome, "--headless=new", "--disable-gpu", "--no-sandbox", "--hide-scrollbars", "--no-first-run",
		"--user-data-dir="+profile, "--window-size=960,540", "--screenshot="+png, "file://"+abs)
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}
	if err := cmd.Start(); err != nil {
		return err
	}
	done := make(chan error, 1)
	go func() { done <- cmd.Wait() }()
	stop := func() {
		_ = syscall.Kill(-cmd.Process.Pid, syscall.SIGKILL)
		<-done
	}
	deadline := time.Now().Add(30 * time.Second)
	lastSize := int64(-1)
	for time.Now().Before(deadline) {
		select {
		case <-done:
			if fi, err := os.Stat(png); err == nil && fi.Size() > 0 {
				return nil
			}
			return fmt.Errorf("chrome exited without writing %s", png)
		case <-time.After(300 * time.Millisecond):
		}
		if fi, err := os.Stat(png); err == nil && fi.Size() > 0 {
			if fi.Size() == lastSize {
				stop()
				return nil
			}
			lastSize = fi.Size()
		}
	}
	stop()
	return fmt.Errorf("chrome didn't write %s within 30 seconds", png)
}
