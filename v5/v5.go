package main

// #cgo CFLAGS: -Ofast
// #cgo LDFLAGS: -lyices
// #include <yices.h>
import "C"

import (
	"bytes"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"io"
	"io/ioutil"
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

func Value(x int) _Ctype_term_t {
	return C.yices_int32(C.int(x))
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

	C.yices_init()
	intType := C.yices_int_type()
	ctx := C.yices_new_context(nil)

	vs := make([]_Ctype_term_t, 10)
	for i, _ := range vs {
		vs[i] = C.yices_new_uninterpreted_term(intType)
		C.yices_assert_formula(ctx, C.yices_arith_geq0_atom(vs[i]))
		C.yices_assert_formula(ctx, C.yices_arith_lt_atom(vs[i], Value(10)))
	}
	C.yices_assert_formula(ctx, C.yices_distinct(10, &vs[0]))

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

	// watch.Log("Game %#v started\n", game)

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
			// watch.Log("Step %s\n", rawResult)
			wg.Done()
		}(&steps[i])
	}
	wg.Wait()

	for _, step := range steps {
		diff := step.Hit - steps[0].Hit
		a, b := step.Swap[0], step.Swap[1]

		if diff == 2 {
			C.yices_assert_formula(ctx, C.yices_eq(vs[a], Value(b)))
			C.yices_assert_formula(ctx, C.yices_eq(vs[b], Value(a)))
		} else if diff == 1 {
			C.yices_assert_formula(ctx, C.yices_neq(vs[a], Value(a)))
			C.yices_assert_formula(ctx, C.yices_neq(vs[b], Value(b)))
			C.yices_assert_formula(ctx, C.yices_xor2(C.yices_eq(vs[a], Value(b)), C.yices_eq(vs[b], Value(a))))
		} else if diff == 0 {
			C.yices_assert_formula(ctx, C.yices_neq(vs[a], Value(a)))
			C.yices_assert_formula(ctx, C.yices_neq(vs[b], Value(b)))
			C.yices_assert_formula(ctx, C.yices_neq(vs[a], Value(b)))
			C.yices_assert_formula(ctx, C.yices_neq(vs[b], Value(a)))
		} else if diff == -1 {
			C.yices_assert_formula(ctx, C.yices_xor2(C.yices_eq(vs[a], Value(a)), C.yices_eq(vs[b], Value(b))))
			C.yices_assert_formula(ctx, C.yices_neq(vs[a], Value(b)))
			C.yices_assert_formula(ctx, C.yices_neq(vs[b], Value(a)))
		} else if diff == -2 {
			C.yices_assert_formula(ctx, C.yices_eq(vs[a], Value(a)))
			C.yices_assert_formula(ctx, C.yices_eq(vs[b], Value(b)))
		}
	}

	if C.yices_check_context(ctx, nil) != C.STATUS_SAT {
		watch.Log("unsat\n") // 必ずsatであるはずだが……
		return
	}

	model := C.yices_get_model(ctx, 0)
	answer := make([]byte, 10)

	for i, v := range vs {
		var result C.int
		C.yices_get_int32_value(model, v, &result)
		answer[i] = byte(result) + 48
	}

	// watch.Log("Answer %s found\n", answer)

	rawResult, err := client.Request("POST", "/internships/2018/games/"+game.ID, "{\"answer\":\""+string(answer)+"\"}")
	if err != nil {
		panic(err)
	}

	watch.Log("Finished: %s\n", rawResult)
}
