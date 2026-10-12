# NYT Crossword

Solve times for my daily NYT crossword, one line per weekday, plus the puzzles
I started and did not finish.

The page reads a JSON file. A scheduled job writes that file. The browser does
not call the NYT API.

## Publish stats

[`.github/workflows/nyt-crossword-scrape.yml`](../.github/workflows/nyt-crossword-scrape.yml)
runs every day at 01:17 UTC (8:17 PM Eastern Standard Time, 9:17 PM Eastern
Daylight Time) and when you start it by hand.

Create a repository Actions secret named `NYT_COOKIE`. The value is the `NYT-S`
cookie from a browser signed in to nytimes.com.

1. Open nytimes.com and sign in.
2. In developer tools, open the cookie list for `nytimes.com`.
3. Copy the `NYT-S` value.
4. In the repository settings, create an Actions secret named `NYT_COOKIE` and paste that value.

The job writes `nyt-crossword/data/stats.json` on the `gh-pages` branch. It
does not commit stats to `main`. The workflow shares the `gh-pages-publish`
concurrency group with deploy, preview, and cleanup.

The puzzle list does not include solve time, so the first run requests a game
record for every solved puzzle back to 2005-01-01. Later runs request puzzles
that are unfinished or that do not have a stored time yet. The list endpoint
rejects ranges longer than 100 days, so the job walks the calendar in 100-day
windows, the same limit as the
[original scraper](https://gist.github.com/imjasonh/bc67910c96d17a37044cbd742810294f).

You can set a start and end print date when you run the workflow by hand. An
empty end date means today in New York.

## Filters

The chart is the median solve time for each weekday. **Hide unusually long
solves** drops times above that weekday's upper fence (third quartile plus 1.5
times the interquartile range), computed on the years in the range. **Ignore
solves longer than** drops anything over the number of minutes you enter.
**Ignore date** keeps one print date out of the medians. Those choices stay in
this browser.

A partially solved puzzle has some squares filled and is not solved. The date
links to that puzzle on nytimes.com.

## Run locally

```bash
cd nyt-crossword
npm test
npm start
```

`npm start` serves the page with the bundled sample. To scrape into `./data`:

```bash
NYT_COOKIE="the NYT-S cookie value" npm run scrape
```

`data/` is gitignored.
