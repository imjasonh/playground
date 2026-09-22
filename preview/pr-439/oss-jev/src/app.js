import { compileModel } from "./compile.js";
import { fetchBundle, openCache } from "./fetch-bundle.js";
import { formatBytes, getModel, listModels } from "./models.js";
import { getPreset, PRESETS } from "./presets.js";
import { questionFromDraft } from "./questions.js";
import { systemOne } from "./systemone.js";
import { createWhitespaceTokenizer, kevSpecialIdsFromLookup } from "./tokenizer.js";
import { detectWebGPU, preferWebGpu } from "./webgpu.js";

const modelSelect = document.querySelector("#model");
const backendSelect = document.querySelector("#backend");
const compileButton = document.querySelector("#compile");
const unloadButton = document.querySelector("#unload");
const modelStatus = document.querySelector("#model-status");
const progressEl = document.querySelector("#progress");
const presetSelect = document.querySelector("#preset");
const stateInput = document.querySelector("#state");
const questionsEl = document.querySelector("#questions");
const addQuestionButton = document.querySelector("#add-question");
const runButton = document.querySelector("#run");
const resultEl = document.querySelector("#result");
const resultEmpty = document.querySelector("#result-empty");
const logEl = document.querySelector("#log");
const gpuStatus = document.querySelector("#gpu-status");

const state = {
  compiled: null,
  files: null,
  detected: null,
  cache: null,
  log: [],
};

function questionCard(draft = { kind: "choice", instructions: "", options: "" }) {
  const article = document.createElement("article");
  article.className = "question";
  article.innerHTML = `
    <label>
      <span>Type</span>
      <select data-field="kind">
        <option value="choice">Choice</option>
        <option value="score">Score</option>
        <option value="noul">Yes / no</option>
      </select>
    </label>
    <label>
      <span>Instructions</span>
      <textarea data-field="instructions" rows="2"></textarea>
    </label>
    <label data-options>
      <span>Options or levels, one per line</span>
      <textarea data-field="options" rows="4"></textarea>
    </label>
    <button type="button" class="link" data-remove>Remove</button>
  `;
  article.querySelector('[data-field="kind"]').value = draft.kind;
  article.querySelector('[data-field="instructions"]').value = draft.instructions;
  article.querySelector('[data-field="options"]').value = draft.options ?? "";
  syncOptionVisibility(article);
  article.querySelector('[data-field="kind"]').addEventListener("change", () => {
    syncOptionVisibility(article);
  });
  article.querySelector("[data-remove]").addEventListener("click", () => {
    if (questionsEl.querySelectorAll(".question").length === 1) {
      return;
    }
    article.remove();
  });
  return article;
}

function syncOptionVisibility(article) {
  const kind = article.querySelector('[data-field="kind"]').value;
  article.querySelector("[data-options]").hidden = kind === "noul";
}

function readQuestions() {
  return [...questionsEl.querySelectorAll(".question")].map((article) =>
    questionFromDraft(
      article.querySelector('[data-field="kind"]').value,
      article.querySelector('[data-field="instructions"]').value,
      article.querySelector('[data-field="options"]').value,
    ),
  );
}

function applyPreset(id) {
  const preset = getPreset(id);
  stateInput.value = preset.state;
  questionsEl.replaceChildren();
  questionsEl.append(
    questionCard({
      kind: preset.kind,
      instructions: preset.instructions,
      options: preset.options,
    }),
  );
  for (const extra of preset.extra ?? []) {
    questionsEl.append(questionCard(extra));
  }
}

function setStatus(text) {
  modelStatus.textContent = text;
}

function logLine(text) {
  state.log.push(text);
  logEl.textContent = state.log.join("\n");
}

function formatMs(ms) {
  if (ms < 1000) {
    return `${Math.round(ms)} ms`;
  }
  return `${(ms / 1000).toFixed(2)} s`;
}

function renderResult(result) {
  resultEmpty.hidden = true;
  resultEl.replaceChildren();
  for (const [id, answer] of Object.entries(result.answers)) {
    const block = document.createElement("article");
    block.className = "answer";
    const heading = document.createElement("h3");
    heading.textContent = headline(answer);
    block.append(heading);
    for (const [label, probability] of bars(answer)) {
      const row = document.createElement("div");
      row.className = "bar";
      const name = document.createElement("span");
      name.textContent = label;
      const meter = document.createElement("span");
      meter.className = "meter";
      meter.style.setProperty("--p", String(probability));
      const value = document.createElement("span");
      value.textContent = percent(probability);
      row.append(name, meter, value);
      block.append(row);
    }
    const meta = document.createElement("p");
    meta.className = "answer-meta";
    meta.textContent = `Confidence ${percent(answer.confidence)}`;
    block.append(meta);
    block.dataset.answerId = id;
    resultEl.append(block);
  }
  const usage = document.createElement("p");
  usage.className = "usage";
  usage.textContent = `${result.usage.input_tokens} tokens, ${result.latency_ms} ms, ${result.model}`;
  resultEl.append(usage);
}

function headline(answer) {
  if (answer.type === "choice") {
    return answer.choice;
  }
  if (answer.type === "score") {
    return answer.score.toFixed(2);
  }
  return answer.noul >= 0.5 ? "Yes" : "No";
}

function bars(answer) {
  if (answer.type === "choice") {
    return Object.entries(answer.probabilities);
  }
  if (answer.type === "score") {
    return Object.entries(answer.probabilities).map(([index, probability]) => [
      answer.legend[index] ?? `level ${index}`,
      probability,
    ]);
  }
  return [
    ["true", answer.noul],
    ["false", 1 - answer.noul],
  ];
}

function percent(value) {
  return `${(value * 100).toFixed(1)}%`;
}

function fillModelSelect() {
  for (const model of listModels()) {
    const option = document.createElement("option");
    option.value = model.id;
    option.textContent = `${model.title} (${formatBytes(model.bytes)})`;
    modelSelect.append(option);
  }
}

function fillPresets() {
  for (const preset of PRESETS) {
    const option = document.createElement("option");
    option.value = preset.id;
    option.textContent = preset.title;
    presetSelect.append(option);
  }
}

function describeModel() {
  const model = getModel(modelSelect.value);
  setStatus(model.description);
}

async function compile() {
  const model = getModel(modelSelect.value);
  compileButton.disabled = true;
  unloadButton.disabled = true;
  runButton.disabled = true;
  progressEl.hidden = true;
  progressEl.removeAttribute("value");
  try {
    let files = {};
    if (model.files.length > 0) {
      setStatus(`Fetching ${model.title}…`);
      const started = performance.now();
      files = await fetchBundle(model, {
        cache: state.cache,
        onProgress({ file, received, total, cached }) {
          if (cached) {
            return;
          }
          if (total) {
            progressEl.hidden = false;
            progressEl.max = 1;
            progressEl.value = received / total;
          }
          setStatus(`Fetching ${file} (${formatBytes(received)}${total ? ` / ${formatBytes(total)}` : ""})`);
        },
      });
      logLine(`fetch ${model.id} ${formatMs(performance.now() - started)}`);
    }
    setStatus(`Compiling ${model.title} on ${backendSelect.value}…`);
    progressEl.hidden = true;
    const compiled = await compileModel({
      model,
      files,
      backendChoice: backendSelect.value,
      detected: state.detected,
    });
    state.compiled = { ...compiled, model };
    state.files = files;
    logLine(`compile ${model.id} ${compiled.backend} ${formatMs(compiled.compileMs)}`);
    setStatus(
      `${model.title} ready on ${compiled.backend}. ${compiled.tokenizer ? `vocab ${compiled.tokenizer.vocabSize}.` : "Fixture tokenizer."}`,
    );
    runButton.disabled = false;
    unloadButton.disabled = false;
  } catch (error) {
    setStatus(error.message);
    logLine(`error ${error.message}`);
  } finally {
    compileButton.disabled = false;
    progressEl.hidden = true;
  }
}

async function unload() {
  await state.compiled?.session.release();
  state.compiled = null;
  runButton.disabled = true;
  unloadButton.disabled = true;
  setStatus("Unloaded.");
  logLine("unload");
}

function encoderFor(compiled) {
  if (compiled.tokenizer) {
    return compiled.tokenizer;
  }
  return createWhitespaceTokenizer();
}

function kevIdsFromCompiled(compiled, tokenizer) {
  if (compiled.kevSpecialIds) {
    return compiled.kevSpecialIds;
  }
  const known = {
    "<|fim_prefix|>": 10,
    "<|fim_middle|>": 11,
    "<|box_start|>": 12,
    "<|box_end|>": 13,
    "<|fim_suffix|>": 14,
  };
  return kevSpecialIdsFromLookup((token) => known[token] ?? tokenizer.encode(token)[0]);
}

async function run() {
  if (!state.compiled) {
    return;
  }
  runButton.disabled = true;
  try {
    const questions = readQuestions();
    const named = Object.fromEntries(questions.map((question, index) => [`q${index + 1}`, question]));
    const tokenizer = encoderFor(state.compiled);
    const result = await systemOne({
      session: state.compiled.session,
      family: state.compiled.model.family,
      encode: (text) => tokenizer.encode(text),
      specialIds: tokenizer.ids ?? createWhitespaceTokenizer().ids,
      kevSpecialIds: kevIdsFromCompiled(state.compiled, tokenizer),
      config: state.compiled.config,
      state: stateInput.value,
      questions: named,
    });
    renderResult(result);
    logLine(`run ${result.usage.input_tokens} tok ${result.latency_ms} ms`);
  } catch (error) {
    resultEmpty.hidden = false;
    resultEmpty.textContent = error.message;
    resultEl.replaceChildren();
    logLine(`error ${error.message}`);
  } finally {
    runButton.disabled = false;
  }
}

async function start() {
  fillModelSelect();
  fillPresets();
  applyPreset(PRESETS[0].id);
  describeModel();
  state.cache = await openCache();
  state.detected = await detectWebGPU();
  if (state.detected.available) {
    const info = state.detected.info;
    gpuStatus.textContent = `WebGPU ${info.description || info.vendor || "adapter"}`;
  } else {
    gpuStatus.textContent = state.detected.reason;
    if (preferWebGpu("auto", state.detected) === false && backendSelect.value === "auto") {
      backendSelect.value = "wasm";
    }
  }
}

modelSelect.addEventListener("change", describeModel);
presetSelect.addEventListener("change", () => applyPreset(presetSelect.value));
compileButton.addEventListener("click", () => {
  compile();
});
unloadButton.addEventListener("click", () => {
  unload();
});
addQuestionButton.addEventListener("click", () => {
  questionsEl.append(questionCard());
});
runButton.addEventListener("click", () => {
  run();
});

start();
