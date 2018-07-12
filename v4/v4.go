package main

import (
	"bytes"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"io"
	"io/ioutil"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

type (
	Game struct {
		ID string `json:"id"`
	}
	GameStep struct {
		Answer []byte
		Swap   [2]int
		Hit    int `json:"hit"`
	}

	Client struct {
		counter     int32
		connections []*tls.Conn
	}
	Watch time.Time
)

func NewClient() (*Client, error) {
	client := &Client{-1, make([]*tls.Conn, 50)}
	for i, _ := range client.connections {
		c, err := tls.Dial("tcp", "apiv2.twitcasting.tv:443", &tls.Config{
			CipherSuites: []uint16{tls.TLS_RSA_WITH_RC4_128_SHA},
		})
		if err != nil {
			return nil, err
		}
		client.connections[i] = c
	}
	return client, nil
}
func (c *Client) Request(method, path, body string) ([]byte, error) {
	req := []string{
		method + " " + path + " HTTP/1.1",
		"Host: apiv2.twitcasting.tv",
		"Authorization: Bearer dummy--token--dummy--token",
	}

	if method == "POST" {
		req = append(req, "Content-Length: "+strconv.Itoa(len(body)), "", body)
	}
	req = append(req, "", "")

	conn := c.connections[atomic.AddInt32(&c.counter, 1)]
	if _, err := io.WriteString(conn, strings.Join(req, "\r\n")); err != nil {
		return nil, err
	}
	if err := conn.CloseWrite(); err != nil {
		return nil, err
	}

	response, err := ioutil.ReadAll(conn)
	if err != nil {
		return nil, err
	}

	return bytes.Split(response, []byte("\r\n\r\n"))[1], nil
}

func (w Watch) Log(format string, args ...interface{}) {
	fmt.Printf("[%dms] >>> ", (time.Now().UnixNano()-time.Time(w).UnixNano())/1000/1000)
	fmt.Printf(format, args...)
}

func main() {
	steps := []GameStep{{
		Answer: []byte("0123456789"),
	}}
	for i := 0; i < 10; i++ {
		for j := i + 1; j < 10; j++ {
			s := append([]byte{}, steps[0].Answer...)
			s[i] = steps[0].Answer[j]
			s[j] = steps[0].Answer[i]
			steps = append(steps, GameStep{
				Answer: s,
				Swap:   [2]int{i, j},
			})
		}
	}

	z3vars := "v0 v1 v2 v3 v4 v5 v6 v7 v8 v9"
	z3script := &bytes.Buffer{}
	for _, v := range strings.Split(z3vars, " ") {
		z3script.WriteString("(declare-const " + v + " Int)")
		z3script.WriteString("(assert (> " + v + " -1))")
		z3script.WriteString("(assert (< " + v + " 10))")
	}
	z3script.WriteString("(assert (distinct " + z3vars + "))")

	z3 := exec.Command("z3", "-in")
	z3in, err := z3.StdinPipe()
	if err != nil {
		panic(err)
	}
	z3out, err := z3.StdoutPipe()
	if err != nil {
		panic(err)
	}
	if err := z3.Start(); err != nil {
		panic(err)
	}

	client, err := NewClient()
	if err != nil {
		panic(err)
	}

	watch := Watch(time.Now())

	rawGame, err := client.Request("GET", "/internships/2018/games?level=10", "")
	if err != nil {
		panic(err)
	}

	game := Game{}
	if err := json.Unmarshal(rawGame, &game); err != nil {
		panic(err)
	}
	if game.ID == "" {
		watch.Log("The game has already started: %s\n", rawGame)
		time.Sleep(20 * time.Second) // 前のゲームが終わるまで待つ
		return
	}

	watch.Log("Game %#v started\n", game)

	wg := &sync.WaitGroup{}
	wg.Add(len(steps))

	for i, _ := range steps {
		go func(step *GameStep) {
			rawResult, err := client.Request("POST", "/internships/2018/games/"+game.ID, "{\"answer\":\""+string(step.Answer)+"\"}")
			if err != nil {
				panic(err)
			}
			if err := json.Unmarshal(rawResult, step); err != nil {
				panic(err)
			}
			watch.Log("Step %s\n", rawResult)
			wg.Done()
		}(&steps[i])
	}
	wg.Wait()

	for _, step := range steps {
		diff := step.Hit - steps[0].Hit
		a := strconv.Itoa(step.Swap[0])
		b := strconv.Itoa(step.Swap[1])

		if diff == 2 {
			z3script.WriteString("(assert (= v" + a + " " + b + "))")
			z3script.WriteString("(assert (= v" + b + " " + a + "))")
		} else if diff == 1 {
			z3script.WriteString("(assert (not (= v" + a + " " + a + ")))")
			z3script.WriteString("(assert (not (= v" + b + " " + b + ")))")
			z3script.WriteString("(assert (xor (= v" + a + " " + b + ") (= v" + b + " " + a + ")))")
		} else if diff == 0 {
			z3script.WriteString("(assert (not (= v" + a + " " + a + ")))")
			z3script.WriteString("(assert (not (= v" + b + " " + b + ")))")
			z3script.WriteString("(assert (not (= v" + a + " " + b + ")))")
			z3script.WriteString("(assert (not (= v" + b + " " + a + ")))")
		} else if diff == -1 {
			z3script.WriteString("(assert (xor (= v" + a + " " + a + ") (= v" + b + " " + b + ")))")
			z3script.WriteString("(assert (not (= v" + a + " " + b + ")))")
			z3script.WriteString("(assert (not (= v" + b + " " + a + ")))")
		} else if diff == -2 {
			z3script.WriteString("(assert (= v" + a + " " + a + "))")
			z3script.WriteString("(assert (= v" + b + " " + b + "))")
		}
	}

	z3script.WriteString("(check-sat)")
	z3script.WriteString("(get-value (" + z3vars + "))")

	if _, err := z3in.Write(z3script.Bytes()); err != nil {
		panic(err)
	}
	z3in.Close()

	z3result, err := ioutil.ReadAll(z3out)
	if err != nil {
		panic(err)
	}

	answer := make([]byte, 0, 10)
	for _, line := range bytes.Split(z3result, []byte("\n")) {
		if len(line) > 5 {
			answer = append(answer, line[5])
		}
	}

	watch.Log("Answer %s found\n", answer)

	rawResult, err := client.Request("POST", "/internships/2018/games/"+game.ID, "{\"answer\":\""+string(answer)+"\"}")
	if err != nil {
		panic(err)
	}

	watch.Log("Finished: %s\n", rawResult)
}
