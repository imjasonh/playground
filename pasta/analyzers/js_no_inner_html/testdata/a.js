// Good
el.textContent = "Safe text";
el.replaceChildren();
el.innerHTML = DOMPurify.sanitize(html);

// Bad: auto-fixable empty-string clears
el.innerHTML = ""; // want "use replaceChildren() instead of assigning empty string to innerHTML"
list.innerHTML = ''; // want "use replaceChildren() instead of assigning empty string to innerHTML"
panel.innerHTML = ``; // want "use replaceChildren() instead of assigning empty string to innerHTML"

// Bad: non-empty HTML assignment
el.innerHTML = "<div>Unsafe</div>"; // want "direct assignment to innerHTML can lead to XSS"
