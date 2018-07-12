"use strict";

const tls = require("tls");
const child_process = require("child_process");

process.on("unhandledRejection", err => console.error(err));

const pythonRuntime = () => {
	const py = child_process.spawn("python3");
	return code => new Promise(resolve => {
		py.stdout.setEncoding("ascii");
		py.stdout.on("data", resolve);
		py.stdin.write(code);
		py.stdin.end();
	});
};

const connect = () => new Promise(resolve => {
	const socket = tls.connect({
		host: "apiv2.twitcasting.tv",
		port: 443,
		secureContext: tls.createSecureContext({ciphers: "AES128-SHA"}),
	}, () => resolve(data => new Promise(resolve => {
		socket.write(data);
		socket.end();

		const chunks = [];
		socket.on("data", chunk => chunks.push(chunk));
		socket.on("end", () => {
			const [, raw] = Buffer.concat(chunks).toString("utf8").split("\r\n\r\n");
			resolve(JSON.parse(raw));
		});
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
	const runtime = pythonRuntime();

	const start = new Date;
	const challenge = await gameStart();

	const results = await Promise.all(patterns.map(async pattern => {
		const result = await challenge(pattern.answer.join(""));
		console.log(result, new Date, new Date - start);

		pattern.hit = result.hit;
		return pattern;
	}));

	const z3 = [
		"from z3 import *",
		"s = Solver()",
		"x = [Int('x%d' % i) for i in range(10)]",
		"s.add(Distinct(x))",
		"for i in range(10):",
		"	s.add(0 <= x[i], x[i] < 10)",
	];

	for(const result of results.slice(1)){
		const diff = result.hit - results[0].hit;
		result.diff = result.hit - results[0].hit;
		console.log(result, new Date, new Date - start);

		const {answer, swap: [A, B]} = result;
		if(result.diff == 2){
			z3.push(`s.add(x[${A}] == ${B}, x[${B}] == ${A})`);
		}else if(result.diff == 1){
			z3.push(`s.add(x[${A}] != ${A}, x[${B}] != ${B}, Or(And(x[${A}] == ${B}, x[${B}] != ${A}), And(x[${A}] != ${B}, x[${B}] == ${A})))`);
		}else if(result.diff == 0){
			z3.push(`s.add(x[${A}] != ${A}, x[${B}] != ${B}, x[${A}] != ${B}, x[${B}] != ${A})`);
		}else if(result.diff == -1){
			z3.push(`s.add(Or(And(x[${A}] == ${A}, x[${B}] != ${B}), And(x[${A}] != ${A}, x[${B}] == ${B})), x[${A}] != ${B}, x[${B}] != ${A})`);
		}else if(result.diff == -2){
			z3.push(`s.add(x[${A}] == ${A}, x[${B}] == ${B})`);
		}
	}

	z3.push("s.check()");
	z3.push("m = s.model()");
	z3.push("print(''.join([str(m[var]) for var in x]))");

	const answer = await runtime(z3.join("\n"));
	console.log(`OK, answer is ${answer}`, new Date, new Date - start);
	console.log(await challenge(answer.trim()));
})();
