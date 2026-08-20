# It's Not _Jaws_

Months ago, my kids and I came up with a fun guessing game. The rules are simple:

> One person picks a movie that we’ve all seen, and keeps it secret. Everyone else takes turns guessing movie titles; if we guessed correctly, we win. If not, the person responds with a clue in the form of, “it’s not X, but like X, it _______”, giving a signal to “triangulate” the answer.

It’s a pretty fun game! Try it with your own friends and family! Sort of like Wordle for movie lovers.

Around the time Fable came out, I wondered if the model was sophisticated enough to understand and follow these rules. And, much to my surprise, on my very first game, Fable’s thinking traces (which were visible to me) included the name of the movie. This made the game a little… easy.

Repeated attempts to prompt the model not to leak the answer were somewhat successful, but I could never reliably stamp it out.

I tried a few other models, and after some attempt eventually even had some good fun games! Try it with your own local LLM model!

This morning I wondered whether I could systematize this experience and try to find the “best” model for this game. “Best” is a little complicated, since it includes both a.) picking a good target movie, b.) giving useful clues so the game is fun, c.) crucially, not leaking the answer, or too many extra clues in thinking traces.

When I got to work, I used the [Cursor SDK](https://cursor.com/docs/sdk/typescript) to build an agent harness to match up a series of models against each other in successive games.

Some interesting findings:

1. Composer 2.5 is the most likely model to leak the full title — in 12 games, it directly said the answer 11 times.
2. Clue leaks are an endemic problem among Fable, GPT 5.5 and 5.6-Sol. All three leaked clues in 8 of 12 games. Fable never leaked the full title though.
3. Grok 4.5 didn’t leak a single clue or title in its 12 matchups! It still lost every game, which might indicate weak movie choices or clues that are too strong.
4. All of the models tend to pick the same ~3 movies (_The Lion King_, _Truman Show_, _Shawshank_) so these are good guesses if you're ever up against an agent.

Anyway, I don’t know what this could be useful for, but it was super fun to build! I encourage you to have fun ideas and experiment with them, it’s one of the last things that make us truly human.

You can see one matchup [here](https://github.com/imjasonh/playground/actions/runs/31191985994). It takes 30m and costs ~$20 to run, if you feel like reproducing my results. PRs welcome!

And if we’re ever hanging out and you want to play a game, I’d be happy to give it a go.

PS: the game is called “It’s Not _Jaws_” because there’s an extra rule where you cannot under any circumstances choose Jaws as the answer. I didn’t tell the models this, but they still never picked _Jaws_ as the answer.
