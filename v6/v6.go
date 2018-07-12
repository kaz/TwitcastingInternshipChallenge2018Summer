package main

// #cgo CFLAGS: -Ofast
// #cgo LDFLAGS: -lyices
// #include <yices.h>
import "C"

import (
	"bytes"
	"crypto/tls"
	"fmt"
	"io/ioutil"
	"math/rand"
	"net/http"
	"runtime"
	"strconv"
	"sync"
	"sync/atomic"
	"time"
)

type (
	GameStep struct {
		Answer []byte
		Swap   [2]int
		Hit    int8
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
	req := &bytes.Buffer{}
	req.WriteString(method + " " + path + " HTTP/1.1\r\n")
	req.WriteString("Host: apiv2.twitcasting.tv\r\n")
	req.WriteString("Authorization: Bearer dummy--token--dummy--token\r\n")

	if method == "POST" {
		req.WriteString("Content-Length: " + strconv.Itoa(len(body)) + "\r\n\r\n")
		req.WriteString(body)
	}
	req.WriteString("\r\n\r\n")

	conn := c.connections[atomic.AddInt32(&c.counter, 1)]
	if _, err := conn.Write(req.Bytes()); err != nil {
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
	runtime.GOMAXPROCS(2)

	base := GameStep{Answer: []byte("0123456789")}
	steps := make([]GameStep, 0, 50)
	for i := 0; i < 10; i++ {
		for j := i + 1; j < 10; j++ {
			answer := append([]byte{}, base.Answer...)
			answer[i], answer[j] = base.Answer[j], base.Answer[i]
			steps = append(steps, GameStep{answer, [2]int{i, j}, 0})
		}
	}
	for i := len(steps) - 1; i >= 0; i-- {
		j := rand.Intn(i + 1)
		steps[i], steps[j] = steps[j], steps[i]
	}
	steps = append([]GameStep{base}, steps[:15]...)

	C.yices_init()
	intType := C.yices_int_type()
	ctx := C.yices_new_context(nil)

	vs := make([]_Ctype_term_t, 10)
	fs := make([]_Ctype_term_t, 0, 256)
	for i, _ := range vs {
		vs[i] = C.yices_new_uninterpreted_term(intType)
		fs = append(fs, C.yices_arith_geq0_atom(vs[i]), C.yices_arith_lt_atom(vs[i], Value(10)))
	}
	fs = append(fs, C.yices_distinct(_Ctype_uint(len(vs)), &vs[0]))

	client, err := NewClient()
	if err != nil {
		panic(err)
	}

	watch := Watch(time.Now())

	rawGame, err := client.Request("GET", "/internships/2018/games?level=10", "")
	if err != nil {
		panic(err)
	}
	if len(rawGame) != 41 {
		watch.Log("The game has already started: %s\n", rawGame)
		if _, err := http.Get("http://127.0.0.1:3000"); err != nil {
			panic(err)
			time.Sleep(20 * time.Second)
		}
		return
	}

	gameId := string(rawGame[7:39])
	// watch.Log("Game %s started\n", gameId)

	wg := &sync.WaitGroup{}
	wg.Add(len(steps))

	for i, _ := range steps {
		go func(step *GameStep) {
			rawResult, err := client.Request("POST", "/internships/2018/games/"+gameId, "{\"answer\":\""+string(step.Answer)+"\"}")
			if err != nil {
				panic(err)
			}
			step.Hit = int8(rawResult[7]) - 48
			wg.Done()

			// watch.Log("Step %s\n", rawResult)
		}(&steps[i])
	}
	wg.Wait()

	for _, step := range steps {
		a, b := step.Swap[0], step.Swap[1]
		switch step.Hit - steps[0].Hit {
		case 2:
			fs = append(fs,
				C.yices_eq(vs[a], Value(b)),
				C.yices_eq(vs[b], Value(a)),
			)
		case 1:
			fs = append(fs,
				C.yices_neq(vs[a], Value(a)),
				C.yices_neq(vs[b], Value(b)),
				C.yices_xor2(C.yices_eq(vs[a], Value(b)), C.yices_eq(vs[b], Value(a))),
			)
		case 0:
			fs = append(fs,
				C.yices_neq(vs[a], Value(a)),
				C.yices_neq(vs[b], Value(b)),
				C.yices_neq(vs[a], Value(b)),
				C.yices_neq(vs[b], Value(a)),
			)
		case -1:
			fs = append(fs,
				C.yices_xor2(C.yices_eq(vs[a], Value(a)), C.yices_eq(vs[b], Value(b))),
				C.yices_neq(vs[a], Value(b)),
				C.yices_neq(vs[b], Value(a)),
			)
		case -2:
			fs = append(fs,
				C.yices_eq(vs[a], Value(a)),
				C.yices_eq(vs[b], Value(b)),
			)
		}
	}

	C.yices_assert_formula(ctx, C.yices_and(_Ctype_uint(len(fs)), &fs[0]))
	if C.yices_check_context(ctx, nil) != C.STATUS_SAT {
		watch.Log("unsat\n") // 必ずsatであるはずだが……
		return
	}

	model := C.yices_get_model(ctx, 0)
	answer := make([]byte, len(vs))

	for i, v := range vs {
		var result C.int
		C.yices_get_int32_value(model, v, &result)
		answer[i] = byte(result) + 48
	}

	// watch.Log("Answer %s found\n", answer)

	rawResult, err := client.Request("POST", "/internships/2018/games/"+gameId, "{\"answer\":\""+string(answer)+"\"}")
	if err != nil {
		panic(err)
	}

	watch.Log("Finished: %s\n", rawResult)
}
