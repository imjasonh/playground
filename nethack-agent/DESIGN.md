# NetHack agent harness

This harness lets a Cursor agent play NetHack by sending keystrokes and reading the terminal. It does not teach the game. A later life sees only the notes and key sequences that earlier lives wrote, plus the screens the process printed when those lives ended.

That is a reasonable way to study whether an agent can learn a long game from play. It is not how the agents that make progress on NetHack usually work, and it is not a plan that ascends any time soon.

## How agents usually play this game

Four patterns show up. They do not match a request to teach nothing and still eventually beat the game.

Reinforcement learning treats NetHack as a Markov decision process. The [NetHack Learning Environment](https://arxiv.org/abs/2006.13760) exposes glyphs, messages, and stats. A policy network plays millions of games and gets a reward. Nobody pastes the wiki into the prompt. The agent also cannot write down what it learned. The best published neural agents still die in the early dungeon. In-game score is a poor target: camping and killing respawns raises the score without getting closer to the Amulet. A scout metric, tiles newly seen, is a better proxy, and even that is research, not a solved game. The original NLE paper defines solved as ten consecutive ascensions on unseen seeds with a random role, race, alignment, and gender. That bar is still open.

Hand-written bots are the ones that ascend. AutoAscend, the 2021 NeurIPS NetHack Challenge winner, is a graph of strategies for combat, exploration, item identification, and Sokoban. It encodes the spoiler knowledge in code. That is the opposite of teaching nothing.

One-shot language models get the rules, a legal-action API, and a short horizon. NetPlay (Jeurissen et al., 2024) wrapped GPT-4 around isolated skills, including navigation borrowed from AutoAscend. The model follows a narrow instruction and wanders when asked to play. Zero-shot NetHack from a prompt is a known weak baseline.

Skill libraries are the nearest cousin of this harness. Voyager, on Minecraft, writes code skills after an episode and retrieves them later. The agent invents the curriculum. That is the right family if the point is progressive learning from the model's own experience. It has not been the way anyone has beaten vanilla NetHack. A NetHack life is long, the key set is large, and permadeath punishes a model that pays a full completion to press one key.

Agents that beat games either search a tiny discrete game very deeply, optimize a reward for a long time, or run a program a human already wrote. An agent that keeps a notebook and tries again is a real research setup. It is the unusual one.

## What "teach it nothing" can mean

The weights already contain NetHack. The interface will also give the game away. A status line that says `Dlvl:1` is the game talking, and a model that has seen the wiki will recognize it. This harness does not try to erase that. It refuses to add a second teacher.

The prompt does not name the game, list commands, or describe a win. The workspace the agent runs in is empty. Built-in tools are off, so it cannot open the source, the wiki, or a shell. `settingSources` is empty, so it does not load this repo's skills.

What it does get:

- the current screen, unedited
- a line-by-line difference from the previous screen, as text, with no labels for what changed
- notes it wrote
- key sequences it saved
- the final screen of recent lives, exactly as the process printed it
- a JSON shape for sending keys and filing those notes

The last item is the harness contract. Without it the agent has no way to act and no reason to write anything down. It is not a rulebook.

Death messages, menus, and questions the binary prints belong to the game. If the process shows them, the agent sees them. Pre-answering character selection, setting a role, or pointing `OPTIONS` at a spoiled config would be coaching. The tty backend does not do that. It clears `NETHACKOPTIONS` and leaves the binary's own prompts on the screen.

## The loop

One life is one process. The agent conversation lasts for that life only, so it can keep short-term context while the screen is still relevant. When the process ends, the conversation ends.

A new life starts a new agent. The only things that carry over are the notebook, saved key sequences, and archived ending screens. If the agent did not write a lesson down, the next life does not have it. Conversation memory is not a notebook.

Each turn the agent returns one JSON object. `keys` is sent as bytes. `note` is stored. `save` stores a key sequence under a name the agent chose. `run` sends a sequence the agent already stored, so a later life can repeat something it found without a model call per key. `quit` closes the process from the outside. It is not mapped to a game key. That mapping would be a lesson, and for this game it would also be the wrong key.

The harness does not parse hit points, dungeon level, or score. Those strings may appear on the screen. Recording them as structured reward would be a decision about what progress is. The record keeps the raw screen, the turn count, and why the life stopped: the process exited, the agent closed it, the turn budget ran out, or the backend failed.

## Why this will not ascend soon

A successful NetHack game is tens of thousands of turns, with identification puzzles, food, and branches that a single notebook will not compress by accident. A model turn per key does not survive the budget. The `run` field is the first hole in that wall. The agent can file a procedure it has already watched, and the harness replays it. The harness still does not supply procedures of its own, and it will not grow an `explore_level` skill out of AutoAscend. If a procedure exists, some earlier life wrote the keys.

Even with that, the early result is menu flailing, death, and notes that mix real observations with spoilers from pretraining. Those spoilers are data. A note that names a danger is a hypothesis until a screen agrees. The prompt says that once. It does not quiz the agent about sources. Source tags would become theater.

Useful later work, still without a manual:

- a recall action so the agent can pull an old transcript that did not fit in the prompt
- a check that a new note quotes a screen line from this life, so the notebook cannot grow from memory alone
- a second agent that only criticizes notes against transcripts, with the same information diet
- seeds and held-out starts, once the binary supports them, so a procedure is not a route through one dungeon

The learning notebook is only written from the real `nethack` process. A fake screen exists so tests can check the loop without the binary and without an API key. `play` refuses that screen, and a notebook directory on a fake run throws. Tests must not be treated as practice.

## What the code does

`tty` runs `/usr/games/nethack` when that binary exists, otherwise `nethack`, and shows the terminal buffer. `npm run play` always uses that process. It resumes `notebook/` and writes the notes back there. Per-run transcripts still land under `results/`.

`fake` is a test double. It is not a NetHack simulator, and the prompt does not describe it. It cannot update `notebook/`.

`mock` agents exist only inside unit tests. The play command uses a local Cursor agent with no built-in tools.
