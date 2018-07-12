"use strict";

const tls = require("tls");
const child_process = require("child_process");

process.on("unhandledRejection", err => console.error(err));

const z3runtime = () => {
	const z3 = child_process.spawn("z3", ["-in"]);
	return code => new Promise(resolve => {
		const chunks = [];
		z3.stdout.on("data", chunk => chunks.push(chunk));
		z3.stdout.on("end", () => {
			const data = Buffer.concat(chunks).toString("utf8").split("\n");
			if(data[0].trim() != "sat"){
				throw data;
			}
			resolve(data.map(s => s[5]).join("").trim());
		});

		z3.stdin.write(code);
		z3.stdin.end();
	});
};

const connect = () => new Promise(resolve => {
	const socket = tls.connect({
		host: "apiv2.twitcasting.tv",
		port: 443,
		secureContext: tls.createSecureContext({ciphers: "AES128-SHA"}),
	}, () => resolve(data => new Promise(resolve => {
		const chunks = [];
		socket.on("data", chunk => chunks.push(chunk));
		socket.on("end", () => {
			const [, raw] = Buffer.concat(chunks).toString("utf8").split("\r\n\r\n");
			resolve(JSON.parse(raw));
		});

		socket.write(data);
		socket.end();
	})));
});
const gameStart = async () => {
	const pool = await Promise.all(Array(64).fill(null).map(connect));
	const req = (method, path, body) => pool.pop()([
		`${method} ${path} HTTP/1.1`,
		"Host: apiv2.twitcasting.tv",
		"Authorization: Bearer dummy--token--dummy--token",
		body ? `Content-Length: ${body.length}` : "",
		"",
		body,
	].join("\r\n"));

	const result = await req("GET", "/internships/2018/games?level=10", "");
	if(!result.id){
		throw result;
	}
	return answer => req("POST", `/internships/2018/games/${result.id}`, JSON.stringify({answer}));
};

const patterns = [{answer: "0123456789".split("").map(i => parseInt(i))}];
for(let i = 0; i < 10; i++){
	for(let j = i+1; j < 10; j++){
		const answer = [].concat(patterns[0].answer);
		[answer[i], answer[j]] = [answer[j], answer[i]];
		patterns.push({answer, swap: [i, j]});
	}
}

(async () => {
	const z3 = z3runtime();
	const z3vars = Array(10).fill(null).map((_, i) => `x${i}`).join(" ");
	const z3script = [];
	for(const v of z3vars.split(" ")){
		z3script.push(`(declare-const ${v} Int)`);
		z3script.push(`(assert (>= ${v} 0))`);
		z3script.push(`(assert (<= ${v} 9))`);
	}

	const start = new Date;
	const challenge = await gameStart();
	console.log("Game started!", new Date, new Date - start);

	const results = await Promise.all(patterns.map(async pattern => {
		const result = await challenge(pattern.answer.join(""));
		console.log(result, new Date, new Date - start);

		pattern.hit = result.hit;
		return pattern;
	}));

	for(const result of results.slice(1)){
		const diff = result.hit - results[0].hit;
		console.log(result, new Date, new Date - start);

		const {answer, swap: [A, B]} = result;
		if(diff == 2){
			z3script.push(`(assert (= x${A} ${B}))`);
			z3script.push(`(assert (= x${B} ${A}))`);
		}else if(diff == 1){
			z3script.push(`(assert (not (= x${A} ${A})))`);
			z3script.push(`(assert (not (= x${B} ${B})))`);
			z3script.push(`(assert (xor (= x${A} ${B}) (= x${B} ${A})))`);
		}else if(diff == 0){
			z3script.push(`(assert (not (= x${A} ${A})))`);
			z3script.push(`(assert (not (= x${B} ${B})))`);
			z3script.push(`(assert (not (= x${A} ${B})))`);
			z3script.push(`(assert (not (= x${B} ${A})))`);
		}else if(diff == -1){
			z3script.push(`(assert (xor (= x${A} ${A}) (= x${B} ${B})))`);
			z3script.push(`(assert (not (= x${A} ${B})))`);
			z3script.push(`(assert (not (= x${B} ${A})))`);
		}else if(diff == -2){
			z3script.push(`(assert (= x${A} ${A}))`);
			z3script.push(`(assert (= x${B} ${B}))`);
		}
	}

	z3script.push(`(assert (distinct ${z3vars}))`);
	z3script.push("(check-sat)");
	z3script.push(`(get-value (${z3vars}))`);

	const answer = await z3(z3script.join("\n"));
	console.log(`OK, answer is ${answer}`, new Date, new Date - start);
	console.log(await challenge(answer.trim()));
})();
