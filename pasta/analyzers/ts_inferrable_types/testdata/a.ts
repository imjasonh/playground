const a: string = "a"; // want "type `string` is inferrable"
const n: number = 1; // want "type `number` is inferrable"
const b: boolean = true; // want "type `boolean` is inferrable"
const f: boolean = false; // want "type `boolean` is inferrable"

const s = "already inferred";
let z: number;
const fromCall: number = Number("1");

function g(
    x: string = "hi", // want "type `string` is inferrable"
    y: number = 5, // want "type `number` is inferrable"
    z: boolean = true, // want "type `boolean` is inferrable"
) {
    return x + y + String(z);
}

function h(x: string) {
    return x;
}
