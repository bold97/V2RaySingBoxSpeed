package main

import (
	"context"
	"crypto/tls"
	"encoding/base64"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"golang.org/x/net/proxy"
)

// ================= 数据结构 =================

type Node struct {
	Name         string
	Protocol     string
	RawLink      string
	Host         string
	Port         int
	Password     string
	UUID         string
	Flow         string
	Security     string
	SNI          string
	PublicKey    string
	ShortID      string
	Fingerprint  string
	Hy2PortRange string
	Network      string
	WSPath       string
	WSHost       string
	Insecure     bool
}

type TestResult struct {
	Node    Node          `json:"node"`
	Latency time.Duration `json:"latency_ns"`
	Mbps    float64       `json:"mbps"`
	Alive   bool          `json:"alive"`
	ErrMsg  string        `json:"error,omitempty"`
}

// ================= 引擎 =================

type Engine string

const (
	EngineAuto    Engine = "auto"
	EngineSingBox Engine = "singbox"
	EngineXray    Engine = "xray"
)

func resolveEngine(pref Engine, proto string) Engine {
	if pref == EngineSingBox || pref == EngineXray {
		return pref
	}
	if proto == "hysteria2" {
		return EngineSingBox
	}
	return EngineXray
}

// ================= 命令行参数 =================

var (
	flagURL         = flag.String("url", "", "订阅地址")
	flagSingBox     = flag.String("singbox", "", "sing-box 路径")
	flagXray        = flag.String("xray", "", "xray 路径")
	flagEngine      = flag.String("engine", "auto", "引擎: auto | singbox | xray")
	flagConcurrency = flag.Int("c", 5, "并发数")
	flagTimeout     = flag.Duration("t", 6*time.Second, "延迟测试超时")
	flagSpeed       = flag.Bool("speed", false, "测下载速度")
	flagSpeedSecs   = flag.Int("speedsecs", 8, "测速时长（秒）")
	flagJSON        = flag.Bool("json", false, "JSON 输出")
)

// ================= 显示宽度 =================

func runeWidth(r rune) int {
	switch {
	case r >= 0x1100 && r <= 0x115F,
		r >= 0x2E80 && r <= 0xA4CF,
		r >= 0xAC00 && r <= 0xD7A3,
		r >= 0xF900 && r <= 0xFAFF,
		r >= 0xFE30 && r <= 0xFE4F,
		r >= 0xFF00 && r <= 0xFF60,
		r >= 0xFFE0 && r <= 0xFFE6,
		r >= 0x1F300 && r <= 0x1F64F,
		r >= 0x1F900 && r <= 0x1F9FF,
		r >= 0x20000 && r <= 0x2FFFD,
		r >= 0x30000 && r <= 0x3FFFD:
		return 2
	}
	return 1
}

func strWidth(s string) int {
	w := 0
	for _, r := range s {
		w += runeWidth(r)
	}
	return w
}

func padRight(s string, width int) string {
	w := strWidth(s)
	if w >= width {
		return s
	}
	return s + strings.Repeat(" ", width-w)
}

func truncateDisplay(s string, width int) string {
	if strWidth(s) <= width {
		return s
	}
	w := 0
	var b strings.Builder
	for _, r := range s {
		rw := runeWidth(r)
		if w+rw > width-1 {
			break
		}
		b.WriteRune(r)
		w += rw
	}
	b.WriteString("…")
	return b.String()
}

// ================= 订阅 =================

func fetchSubscription(subURL string) ([]Node, error) {
	tlsCfg := &tls.Config{
		CurvePreferences: []tls.CurveID{
			tls.X25519, tls.CurveP256, tls.CurveP384, tls.CurveP521,
		},
		MinVersion: tls.VersionTLS12,
	}
	transport := &http.Transport{
		TLSClientConfig:     tlsCfg,
		TLSHandshakeTimeout: 20 * time.Second,
		DialContext: (&net.Dialer{
			Timeout: 15 * time.Second, KeepAlive: 30 * time.Second,
		}).DialContext,
		ForceAttemptHTTP2: true,
	}
	client := &http.Client{Timeout: 90 * time.Second, Transport: transport}

	var body []byte
	for attempt := 1; attempt <= 3; attempt++ {
		req, err := http.NewRequest("GET", subURL, nil)
		if err != nil {
			return nil, err
		}
		req.Header.Set("User-Agent", "v2rayN/7.0")
		req.Header.Set("Accept", "*/*")

		resp, err := client.Do(req)
		if err != nil {
			if attempt < 3 {
				fmt.Printf("  拉取失败 (第 %d 次): %v\n", attempt, err)
				time.Sleep(time.Duration(attempt) * time.Second)
				continue
			}
			return nil, err
		}
		if resp.StatusCode != http.StatusOK {
			resp.Body.Close()
			if attempt < 3 {
				time.Sleep(time.Duration(attempt) * time.Second)
				continue
			}
			return nil, fmt.Errorf("HTTP %s", resp.Status)
		}
		body, err = io.ReadAll(resp.Body)
		resp.Body.Close()
		if err != nil {
			if attempt < 3 {
				time.Sleep(time.Duration(attempt) * time.Second)
				continue
			}
			return nil, err
		}
		break
	}

	text := string(body)
	if decoded, err := base64.StdEncoding.DecodeString(strings.TrimSpace(text)); err == nil && len(decoded) > 0 {
		text = string(decoded)
	}

	var nodes []Node
	for _, line := range strings.Split(text, "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		if n, err := parseNode(line); err == nil {
			nodes = append(nodes, n)
		}
	}
	return nodes, nil
}

func parseNode(link string) (Node, error) {
	switch {
	case strings.HasPrefix(link, "trojan://"):
		return parseTrojan(link)
	case strings.HasPrefix(link, "vless://"):
		return parseVless(link)
	case strings.HasPrefix(link, "hysteria2://"), strings.HasPrefix(link, "hy2://"):
		return parseHysteria2(link)
	}
	return Node{}, fmt.Errorf("unsupported")
}

func parseTrojan(link string) (Node, error) {
	u, err := url.Parse(link)
	if err != nil {
		return Node{}, err
	}
	q := u.Query()
	port, _ := strconv.Atoi(u.Port())
	n := Node{
		Name: u.Fragment, Protocol: "trojan", RawLink: link,
		Host: u.Hostname(), Port: port,
		Password: u.User.Username(),
		SNI:      q.Get("sni"),
		Network:  q.Get("type"),
		WSPath:   q.Get("path"),
		WSHost:   q.Get("host"),
		Insecure: q.Get("allowInsecure") == "1",
	}
	if n.Network == "" {
		n.Network = "tcp"
	}
	return n, nil
}

func parseVless(link string) (Node, error) {
	u, err := url.Parse(link)
	if err != nil {
		return Node{}, err
	}
	q := u.Query()
	port, _ := strconv.Atoi(u.Port())
	n := Node{
		Name: u.Fragment, Protocol: "vless", RawLink: link,
		Host: u.Hostname(), Port: port,
		UUID:        u.User.Username(),
		Flow:        q.Get("flow"),
		Security:    q.Get("security"),
		SNI:         q.Get("sni"),
		PublicKey:   q.Get("pbk"),
		ShortID:     q.Get("sid"),
		Fingerprint: q.Get("fp"),
		Network:     q.Get("type"),
	}
	if n.Fingerprint == "" {
		n.Fingerprint = "chrome"
	}
	if n.SNI == "" {
		n.SNI = q.Get("servername")
	}
	if n.Network == "" {
		n.Network = "tcp"
	}
	return n, nil
}

func parseHysteria2(link string) (Node, error) {
	u, err := url.Parse(link)
	if err != nil {
		return Node{}, err
	}
	q := u.Query()
	port, _ := strconv.Atoi(u.Port())
	mp := q.Get("mport")
	if mp != "" {
		mp = strings.ReplaceAll(mp, "-", ":")
	}
	return Node{
		Name: u.Fragment, Protocol: "hysteria2", RawLink: link,
		Host: u.Hostname(), Port: port,
		Password:     u.User.Username(),
		SNI:          q.Get("sni"),
		Hy2PortRange: mp,
		Insecure:     q.Get("insecure") == "1",
	}, nil
}

// ================= sing-box 配置 =================

func buildSingBoxConfig(node Node, socksPort int) ([]byte, error) {
	var outbound map[string]interface{}

	switch node.Protocol {
	case "trojan":
		outbound = map[string]interface{}{
			"type": "trojan", "server": node.Host, "server_port": node.Port,
			"password": node.Password,
			"tls": map[string]interface{}{
				"enabled": true, "server_name": node.SNI, "insecure": node.Insecure,
			},
		}
		if node.Network == "ws" {
			outbound["transport"] = map[string]interface{}{
				"type": "ws", "path": node.WSPath,
				"headers": map[string]string{"Host": node.WSHost},
			}
		}
	case "vless":
		tlsMap := map[string]interface{}{
			"enabled": true, "server_name": node.SNI,
			"utls": map[string]interface{}{"enabled": true, "fingerprint": node.Fingerprint},
		}
		if node.Security == "reality" {
			tlsMap["reality"] = map[string]interface{}{
				"enabled": true, "public_key": node.PublicKey, "short_id": node.ShortID,
			}
		}
		outbound = map[string]interface{}{
			"type": "vless", "server": node.Host, "server_port": node.Port,
			"uuid": node.UUID, "flow": node.Flow, "tls": tlsMap,
		}
	case "hysteria2":
		ob := map[string]interface{}{
			"type": "hysteria2", "server": node.Host, "server_port": node.Port,
			"password": node.Password,
			"tls": map[string]interface{}{
				"enabled": true, "server_name": node.SNI, "insecure": true,
			},
		}
		if node.Hy2PortRange != "" {
			ob["server_ports"] = []string{node.Hy2PortRange}
		}
		outbound = ob
	default:
		return nil, fmt.Errorf("unsupported")
	}

	cfg := map[string]interface{}{
		"log": map[string]interface{}{"level": "error"},
		"inbounds": []map[string]interface{}{{
			"type": "socks", "tag": "in",
			"listen": "127.0.0.1", "listen_port": socksPort,
		}},
		"outbounds": []interface{}{outbound},
	}
	return json.MarshalIndent(cfg, "", "  ")
}

// ================= xray 配置 =================

func buildXrayConfig(node Node, socksPort int) ([]byte, error) {
	var outbound map[string]interface{}

	switch node.Protocol {
	case "trojan":
		outbound = map[string]interface{}{
			"protocol": "trojan",
			"settings": map[string]interface{}{
				"servers": []map[string]interface{}{{
					"address":  node.Host,
					"port":     node.Port,
					"password": node.Password,
				}},
			},
			"streamSettings": xrayStreamSettings(node),
		}
	case "vless":
		outbound = map[string]interface{}{
			"protocol": "vless",
			"settings": map[string]interface{}{
				"vnext": []map[string]interface{}{{
					"address": node.Host,
					"port":    node.Port,
					"users": []map[string]interface{}{{
						"id":         node.UUID,
						"encryption": "none",
						"flow":       node.Flow,
					}},
				}},
			},
			"streamSettings": xrayStreamSettings(node),
		}
	case "hysteria2":
		hs := map[string]interface{}{
			"version": 2,
			"auth":    node.Password,
		}
		if node.Hy2PortRange != "" {
			hs["server_ports"] = []string{node.Hy2PortRange}
		}
		outbound = map[string]interface{}{
			"protocol": "hysteria",
			"settings": map[string]interface{}{
				"version":  2,
				"address":  node.Host,
				"port":     node.Port,
				"password": node.Password,
			},
			"streamSettings": map[string]interface{}{
				"method":           "hysteria",
				"hysteriaSettings": hs,
				"security":         "tls",
				"tlsSettings": map[string]interface{}{
					"serverName":    node.SNI,
					"allowInsecure": true,
				},
			},
		}
	default:
		return nil, fmt.Errorf("xray 不支持: %s", node.Protocol)
	}

	cfg := map[string]interface{}{
		"log": map[string]interface{}{"loglevel": "warning"},
		"inbounds": []map[string]interface{}{{
			"listen":   "127.0.0.1",
			"port":     socksPort,
			"protocol": "socks",
			"settings": map[string]interface{}{"auth": "noauth", "udp": false},
		}},
		"outbounds": []interface{}{outbound},
	}
	return json.MarshalIndent(cfg, "", "  ")
}

func xrayStreamSettings(node Node) map[string]interface{} {
	ss := map[string]interface{}{
		"network":  node.Network,
		"security": "none",
	}
	if node.Network == "ws" {
		ss["wsSettings"] = map[string]interface{}{
			"path":    node.WSPath,
			"headers": map[string]string{"Host": node.WSHost},
		}
	}

	if node.Security == "reality" {
		ss["security"] = "reality"
		ss["realitySettings"] = map[string]interface{}{
			"serverName":  node.SNI,
			"publicKey":   node.PublicKey,
			"shortId":     node.ShortID,
			"fingerprint": node.Fingerprint,
			"spiderX":     "/",
		}
	} else if node.Insecure || node.SNI != "" {
		ss["security"] = "tls"
		ss["tlsSettings"] = map[string]interface{}{
			"serverName":    node.SNI,
			"allowInsecure": node.Insecure,
		}
	}
	return ss
}

// ================= 进程 =================

func newSysProcAttr() *syscall.SysProcAttr {
	attr := &syscall.SysProcAttr{}
	v := reflect.ValueOf(attr).Elem()
	if f := v.FieldByName("HideWindow"); f.IsValid() && f.CanSet() && f.Kind() == reflect.Bool {
		f.SetBool(true)
	}
	return attr
}

type proxyProcess struct {
	cmd     *exec.Cmd
	cfgPath string
}

func (p *proxyProcess) Close() {
	if p.cmd != nil && p.cmd.Process != nil {
		_ = p.cmd.Process.Kill()
		_ = p.cmd.Wait()
	}
	if p.cfgPath != "" {
		_ = os.Remove(p.cfgPath)
	}
}

func startProxy(engine Engine, binPath, cfgJSON string, socksPort int) (*proxyProcess, error) {
	f, err := os.CreateTemp("", "proxy-*.json")
	if err != nil {
		return nil, err
	}
	f.WriteString(cfgJSON)
	f.Close()

	cmd := exec.Command(binPath, "run", "-c", f.Name())
	cmd.SysProcAttr = newSysProcAttr()

	if err := cmd.Start(); err != nil {
		os.Remove(f.Name())
		return nil, fmt.Errorf("启动 %s 失败: %w", engine, err)
	}

	addr := fmt.Sprintf("127.0.0.1:%d", socksPort)
	ready := false
	for i := 0; i < 30; i++ {
		conn, err := net.DialTimeout("tcp", addr, 200*time.Millisecond)
		if err == nil {
			conn.Close()
			ready = true
			break
		}
		time.Sleep(100 * time.Millisecond)
	}
	if !ready {
		cmd.Process.Kill()
		cmd.Wait()
		os.Remove(f.Name())
		return nil, fmt.Errorf("%s 未就绪", engine)
	}
	return &proxyProcess{cmd: cmd, cfgPath: f.Name()}, nil
}

func freePort() (int, error) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return 0, err
	}
	defer l.Close()
	return l.Addr().(*net.TCPAddr).Port, nil
}

// ================= 测试 =================

func newSocksClient(port int, timeout time.Duration) (*http.Client, error) {
	dialer, err := proxy.SOCKS5("tcp", fmt.Sprintf("127.0.0.1:%d", port), nil, proxy.Direct)
	if err != nil {
		return nil, err
	}
	return &http.Client{
		Timeout: timeout,
		Transport: &http.Transport{
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				return dialer.Dial(network, addr)
			},
		},
		CheckRedirect: func(req *http.Request, via []*http.Request) error {
			return http.ErrUseLastResponse
		},
	}, nil
}

func measureLatency(client *http.Client) (time.Duration, error) {
	var best time.Duration
	for i := 0; i < 3; i++ {
		start := time.Now()
		resp, err := client.Get("http://cp.cloudflare.com/generate_204")
		if err != nil {
			continue
		}
		io.Copy(io.Discard, resp.Body)
		resp.Body.Close()
		if d := time.Since(start); best == 0 || d < best {
			best = d
		}
	}
	if best == 0 {
		return 0, fmt.Errorf("全部延迟测试失败")
	}
	return best, nil
}

func measureSpeed(port int, secs int) float64 {
	client, err := newSocksClient(port, time.Duration(secs+5)*time.Second)
	if err != nil {
		return 0
	}
	ctx, cancel := context.WithTimeout(context.Background(), time.Duration(secs)*time.Second)
	defer cancel()

	req, _ := http.NewRequestWithContext(ctx, "GET",
		"https://speed.cloudflare.com/__down?bytes=100000000", nil)
	resp, err := client.Do(req)
	if err != nil || resp == nil {
		return 0
	}
	defer resp.Body.Close()

	start := time.Now()
	var total int64
	buf := make([]byte, 32*1024)
	for {
		n, err := resp.Body.Read(buf)
		total += int64(n)
		if err != nil {
			break
		}
		if time.Since(start) >= time.Duration(secs)*time.Second {
			break
		}
	}
	elapsed := time.Since(start).Seconds()
	if elapsed < 0.5 || total == 0 {
		return 0
	}
	return float64(total*8) / elapsed / 1e6
}

func testNode(enginePref Engine, singBoxPath, xrayPath string, node Node, doSpeed bool, speedSecs int, timeout time.Duration) TestResult {
	r := TestResult{Node: node}

	engine := resolveEngine(enginePref, node.Protocol)
	binPath := xrayPath
	if engine == EngineSingBox {
		binPath = singBoxPath
	}
	if binPath == "" {
		r.ErrMsg = fmt.Sprintf("未找到 %s", engine)
		return r
	}

	socksPort, _ := freePort()
	var cfg []byte
	var err error
	if engine == EngineXray {
		cfg, err = buildXrayConfig(node, socksPort)
	} else {
		cfg, err = buildSingBoxConfig(node, socksPort)
	}
	if err != nil {
		r.ErrMsg = err.Error()
		return r
	}

	proc, err := startProxy(engine, binPath, string(cfg), socksPort)
	if err != nil {
		r.ErrMsg = err.Error()
		return r
	}
	defer proc.Close()

	client, _ := newSocksClient(socksPort, timeout)
	lat, err := measureLatency(client)
	if err != nil {
		r.ErrMsg = err.Error()
		return r
	}
	r.Latency = lat
	r.Alive = true

	if doSpeed {
		r.Mbps = measureSpeed(socksPort, speedSecs)
	}
	return r
}

// ================= 查找二进制 =================

func findBinary(userPath, name string) string {
	var cands []string
	if userPath != "" {
		cands = append(cands, userPath)
	}
	if exe, err := os.Executable(); err == nil {
		dir := filepath.Dir(exe)
		cands = append(cands,
			filepath.Join(dir, name, name+".exe"),
			filepath.Join(dir, name+".exe"),
			filepath.Join(dir, name),
		)
	}
	if runtime.GOOS == "windows" {
		cands = append(cands, name+`\`+name+".exe", name+".exe")
	} else {
		cands = append(cands, "./"+name, name, "/usr/local/bin/"+name)
	}
	for _, c := range cands {
		if c == "" {
			continue
		}
		if abs, err := filepath.Abs(c); err == nil {
			if _, err := os.Stat(abs); err == nil {
				return abs
			}
		}
		if lp, err := exec.LookPath(c); err == nil {
			return lp
		}
	}
	return ""
}

// ================= 表格列宽 =================

const (
	colNum    = 4
	colProto  = 10
	colName   = 30
	colAddr   = 32
	colLat    = 12
	colDown   = 12
	colStatus = 55
)

// ================= main =================

func main() {
	flag.Parse()

	subURL := *flagURL
	if subURL == "" && flag.NArg() > 0 {
		subURL = flag.Arg(0)
	}
	if subURL == "" {
		fmt.Println("用法: subspeed -url <订阅地址> [-singbox 路径] [-xray 路径] [-engine auto|singbox|xray]")
		os.Exit(1)
	}

	singBoxPath := findBinary(*flagSingBox, "sing-box")
	xrayPath := findBinary(*flagXray, "xray")

	enginePref := Engine(*flagEngine)
	if enginePref == EngineXray && xrayPath == "" {
		fmt.Println("未找到 xray")
		os.Exit(1)
	}
	if enginePref == EngineSingBox && singBoxPath == "" {
		fmt.Println("未找到 sing-box")
		os.Exit(1)
	}
	if enginePref == EngineAuto && (singBoxPath == "" || xrayPath == "") {
		fmt.Println("auto 模式需要同时找到 sing-box 和 xray")
		os.Exit(1)
	}

	fmt.Printf("引擎: %s\n", enginePref)
	if singBoxPath != "" {
		fmt.Printf("  sing-box: %s\n", singBoxPath)
	}
	if xrayPath != "" {
		fmt.Printf("  xray:     %s\n", xrayPath)
	}

	fmt.Println("正在拉取订阅...")
	nodes, err := fetchSubscription(subURL)
	if err != nil {
		fmt.Printf("失败: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("解析到 %d 个节点（并发 %d）\n\n", len(nodes), *flagConcurrency)
	if len(nodes) == 0 {
		return
	}

	sem := make(chan struct{}, *flagConcurrency)
	results := make([]TestResult, len(nodes))
	var wg sync.WaitGroup
	var done int64
	total := int64(len(nodes))

	for i, node := range nodes {
		wg.Add(1)
		go func(idx int, n Node) {
			defer wg.Done()
			sem <- struct{}{}
			defer func() { <-sem }()

			res := testNode(enginePref, singBoxPath, xrayPath, n, *flagSpeed, *flagSpeedSecs, *flagTimeout)
			results[idx] = res

			cur := atomic.AddInt64(&done, 1)
			tag := "FAIL"
			detail := res.ErrMsg
			if res.Alive {
				tag = "  OK"
				detail = res.Latency.Round(time.Millisecond).String()
				if *flagSpeed {
					detail += fmt.Sprintf("  %.2f Mbps", res.Mbps)
				}
			}
			detail = truncateDisplay(detail, 50)

			name := n.Name
			if name == "" {
				name = fmt.Sprintf("%s:%d", n.Host, n.Port)
			}
			name = truncateDisplay(name, 24)

			fmt.Printf("[%3d/%d] %s %s %s  %s\n",
				cur, total, padRight(n.Protocol, colProto),
				padRight(name, 26), tag, detail)
		}(i, node)
	}
	wg.Wait()

	// ===== 成功在上，失败在下 =====
	var success, failed []TestResult
	for _, r := range results {
		if r.Alive {
			success = append(success, r)
		} else {
			failed = append(failed, r)
		}
	}
	sort.Slice(success, func(i, j int) bool {
		return success[i].Latency < success[j].Latency
	})
	sort.Slice(failed, func(i, j int) bool {
		if failed[i].Node.Protocol != failed[j].Node.Protocol {
			return failed[i].Node.Protocol < failed[j].Node.Protocol
		}
		return failed[i].Node.Name < failed[j].Node.Name
	})
	ordered := append(append([]TestResult{}, success...), failed...)

	if *flagJSON {
		out, _ := json.MarshalIndent(ordered, "", "  ")
		fmt.Println(string(out))
		return
	}

	totalWidth := colNum + 1 + colProto + 1 + colName + 1 + colAddr + 1 + colLat + 1 + colDown + 1 + colStatus

	fmt.Printf("\n========== 结果（成功 %d / 失败 %d） ==========\n", len(success), len(failed))

	if *flagSpeed {
		fmt.Printf("%s %s %s %s %s %s %s\n",
			padRight("#", colNum), padRight("PROTO", colProto),
			padRight("NAME", colName), padRight("ADDRESS", colAddr),
			padRight("LATENCY", colLat), padRight("DOWN", colDown), "STATUS")
	} else {
		fmt.Printf("%s %s %s %s %s %s\n",
			padRight("#", colNum), padRight("PROTO", colProto),
			padRight("NAME", colName), padRight("ADDRESS", colAddr),
			padRight("LATENCY", colLat), "STATUS")
	}
	fmt.Println(strings.Repeat("-", totalWidth))

	sepInserted := false
	for i, r := range ordered {
		if !r.Alive && !sepInserted && len(success) > 0 {
			fmt.Println(strings.Repeat("·", totalWidth))
			sepInserted = true
		}

		name := r.Node.Name
		if name == "" {
			name = "-"
		}
		name = truncateDisplay(name, colName-2)

		addr := truncateDisplay(fmt.Sprintf("%s:%d", r.Node.Host, r.Node.Port), colAddr-2)

		var latStr, downStr, status string
		if r.Alive {
			latStr = r.Latency.Round(time.Millisecond).String()
			if *flagSpeed {
				downStr = fmt.Sprintf("%.2f", r.Mbps)
			}
			status = "OK"
		} else {
			latStr = "-"
			downStr = "-"
			status = "FAIL: " + truncateDisplay(r.ErrMsg, colStatus)
		}

		if *flagSpeed {
			fmt.Printf("%s %s %s %s %s %s %s\n",
				padRight(fmt.Sprintf("%d", i+1), colNum),
				padRight(r.Node.Protocol, colProto),
				padRight(name, colName),
				padRight(addr, colAddr),
				padRight(latStr, colLat),
				padRight(downStr, colDown),
				status)
		} else {
			fmt.Printf("%s %s %s %s %s %s\n",
				padRight(fmt.Sprintf("%d", i+1), colNum),
				padRight(r.Node.Protocol, colProto),
				padRight(name, colName),
				padRight(addr, colAddr),
				padRight(latStr, colLat),
				status)
		}
	}

	// 协议汇总
	fmt.Println("\n========== 协议汇总 ==========")
	type stat struct{ ok, total int }
	stats := map[string]*stat{}
	for _, r := range results {
		s, exist := stats[r.Node.Protocol]
		if !exist {
			s = &stat{}
			stats[r.Node.Protocol] = s
		}
		s.total++
		if r.Alive {
			s.ok++
		}
	}
	protos := make([]string, 0, len(stats))
	for p := range stats {
		protos = append(protos, p)
	}
	sort.Strings(protos)
	for _, p := range protos {
		s := stats[p]
		fmt.Printf("%-10s OK=%d / %d\n", p, s.ok, s.total)
	}
}