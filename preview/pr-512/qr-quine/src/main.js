import { D } from "./encode.js";
import { quine } from "./quine.js";

const button = document.querySelector("#copy");
button.addEventListener("click", async () => {
  try {
    await navigator.clipboard.writeText(quine);
  } catch {
    const area = document.createElement("textarea");
    area.value = quine;
    document.body.appendChild(area);
    area.select();
    const ok = document.execCommand("copy");
    area.remove();
    if (!ok) {
      button.textContent = "Copy failed";
      return;
    }
  }
  button.textContent = "Copied";
});

// The symbol on this page encodes the page address. The iPhone Camera app
// opens an http(s) URL. It reads a data: URL and then reports that it found
// no usable data.
D(location.href);
document.querySelector("#qr").appendChild(document.querySelector("canvas"));
