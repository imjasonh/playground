export function greet(name) {
  return `hello, ${name}`;
}

export function main() {
  for (let i = 0; i < 3; i++) {
    console.log(i, greet("world"));
  }
}

main();
