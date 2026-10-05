/**
 * The only tools that an agent can have. Cursor's backend enforces the
 * list. None of these tools runs commands, because the agent's container
 * holds the API key and reaches Cursor's API: an agent that runs the
 * repository's code needs another sandbox.
 */
export const READ_TOOLS = ["read", "grep", "glob", "ls"] as const;

/** The tools that change files, which only a task that edits can have. */
export const EDIT_TOOLS = ["edit", "delete"] as const;

const ALL_TOOLS: readonly string[] = [...READ_TOOLS, ...EDIT_TOOLS];

/** Returns the tools that the task lists, or else all that it allows. */
export function toolsFor(task: { edit: boolean; tools?: string[] }): string[] {
  if (task.tools?.length) {
    return [...task.tools];
  }
  return task.edit ? [...ALL_TOOLS] : [...READ_TOOLS];
}

/** Throws unless tools lists only tools that a task, which edits if edit is true, can have. */
export function checkTools(tools: unknown, edit: boolean): void {
  if (!Array.isArray(tools) || tools.length === 0) {
    throw new Error("AGENT_TASK.tools must be a list of tool names");
  }
  for (const tool of tools) {
    if (typeof tool !== "string" || !ALL_TOOLS.includes(tool)) {
      throw new Error(`AGENT_TASK.tools can hold only ${ALL_TOOLS.join(", ")}`);
    }
    if (!edit && !(READ_TOOLS as readonly string[]).includes(tool)) {
      throw new Error(`AGENT_TASK.tools can't hold ${tool} unless the task edits files`);
    }
  }
}
