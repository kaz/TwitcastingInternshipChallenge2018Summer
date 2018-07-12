"use strict";

const request = require("request-promise-native");

const API_ENDPOINT = "https://apiv2.twitcasting.tv/internships/2018/games";
const TOKEN = "dummy--token--dummy--token";

process.on("unhandledRejection", ({error}) => console.error(error));

const req = request.defaults({
	json: true,
	headers: {"Authorization": `Bearer ${TOKEN}`},
	pool: {maxSockets: 64},
	forever: true,
});
const gameStart = () => req({
	method: "GET",
	uri: `${API_ENDPOINT}?level=10`,
}).then(({id}) => answer => req({
	method: "POST",
	uri: `${API_ENDPOINT}/${id}`,
	body: {answer},
}));

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

(async () => {
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

})();
