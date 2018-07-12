"use strict";

const tls = require("tls");

const API_ENDPOINT = "https://apiv2.twitcasting.tv/internships/2018/games";
const TOKEN = "dummy--token--dummy--token";

process.on("unhandledRejection", ({error}) => console.error(error));

const connect = () => new Promise(resolve => {
	const socket = tls.connect({
		host: "202.239.41.35",
		port: 443,
		rejectUnauthorized: false,
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
		result.id = result.error.message.split(" ")[2];
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

const all = [];
const find = (usedArray, availableSet) => {
	if(!availableSet.size){
		return all.push(usedArray);
	}
	for(const n of availableSet){
		const newSet = new Set(availableSet);
		newSet.delete(n);
		find([n].concat(usedArray), newSet);
	}
};
find([], new Set(patterns[0].answer));

const Koa = require("koa");
const app = new Koa();

app.use(async ctx => {
	const start = new Date;
	const challenge = await gameStart();

	const results = await Promise.all(patterns.map(async pattern => {
		const result = await challenge(pattern.answer.join(""));
		console.log(result, new Date, new Date - start);

		pattern.hit = result.hit;
		return pattern;
	}));

	const constraints = [];

	for(const result of results.slice(1)){
		const diff = result.hit - results[0].hit;
		if(isNaN(diff)){
			ctx.status = 500;
			ctx.body = "failed";
			return;
		}

		result.diff = result.hit - results[0].hit;
		console.log(result, new Date, new Date - start);

		const {answer, swap: [A, B]} = result;
		if(result.diff == 2){
			constraints.push(c => c[A] == B && c[B] == A);
		}else if(result.diff == 1){
			constraints.push(c => c[A] != A && c[B] != B && ((c[A] == B && c[B] != A) || (c[A] != B && c[B] == A)));
		}else if(result.diff == 0){
			constraints.push(c => c[A] != A && c[B] != B && c[A] != B && c[B] != A);
		}else if(result.diff == -1){
			constraints.push(c => ((c[A] == A && c[B] != B) || (c[A] != A && c[B] == B)) && c[A] != B && c[B] != A);
		}else if(result.diff == -2){
			constraints.push(c => c[A] == A && c[B] == B);
		}
	}

	all.forEach(async a => {
		if(!constraints.some(c => !c(a))){
			console.log(await challenge(a.join("")), new Date, new Date - start);
		}
	});

	ctx.body = "ok";
});

console.log("Listening...");
app.listen(3000);
