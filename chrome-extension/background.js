import { startInsights } from "./background_insights.js";
import { start } from "./controller.js";

start(chrome);
startInsights(chrome, typeof LanguageModel === "undefined" ? null : LanguageModel);
