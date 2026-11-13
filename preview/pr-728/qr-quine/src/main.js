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

D(quine);
document.querySelector("#qr").appendChild(document.querySelector("canvas"));
