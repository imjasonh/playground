// Good
el.textContent = "Safe text";
el.replaceChildren();

// Bad
el.innerHTML = "<div>Unsafe</div>"; // want "direct assignment to innerHTML can lead to XSS"
