# NYT Crossword

Solve times for my daily NYT crossword, one line per weekday, plus the puzzles
I started and did not finish. The page also counts completed puzzles for each
year and links to the ones I have not completed.

The page reads a JSON file. A scheduled job writes that file. The browser does
not call the NYT API. A PR preview has no copy of that file, so it reads
`nyt-crossword/data/stats.json` from the published site, which is the current
`gh-pages` head. `sample/stats.json` is test input. The page does not load it.
The chart, the medians, and the year list start at 2014. Earlier solves stay in the file.

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

The puzzle list does not include solve time. The job reads `playTimeSeconds`
from the crossword state endpoint, 30 puzzles at a time. The per-puzzle
`/v6/game/{id}.json` URL used by the
[original scraper](https://gist.github.com/imjasonh/bc67910c96d17a37044cbd742810294f)
returns 404 for these solves, so the job does not call it. The default first
print date is 2014-01-01. A solved puzzle that already has a time is not
requested again, and a 100-day window is not listed again when every day in
it is one of those solves. If a later listing says that puzzle is not solved,
the stored solve is dropped, and that does not add a request. A puzzle the list
flags as solved is still treated as unsolved when its grid is under 100%
filled. An open puzzle
is requested when it is new or the list shows a change. The list endpoint rejects ranges longer than 100 days,
so the job walks the calendar in 100-day windows, the same limit as that
scraper.

You can set a start and end print date when you run the workflow by hand. An
empty end date means today in New York.

## Completed by year

The top of the page states the current streak: how many days it has run, and
the print date it started. That date is the first puzzle after the last one
not completed. A puzzle is
completed when the puzzle list says it is solved, or when its print date is
in `completed.json`. An open puzzle dated today does not end the run. The
year table counts completed puzzles out of all puzzles in that year. Open
the list under a year to see every puzzle not completed, including ones
never opened, each linked to nytimes.com.

The list endpoint already returns every puzzle in a date range with its
solved flag, so this needs no requests beyond the ones the scrape makes.

## Finished puzzles the list leaves open

`completed.json` lists print dates that count as solved when the puzzle list
reports the grid under 100% filled. NYT sometimes reports a finished puzzle
that way. Add the print date and commit the file. The page counts that
puzzle as completed. The scrape keeps its stored time and does not mark it
open again.

## Excluded solves

`excluded.json` lists print dates that stay off the chart and out of the
medians. Add a date there and commit it. The page does not list those solves.
A date can be a short solve or a long one. Use it for solves that are not real
times, such as a puzzle solved on paper and typed in afterward.

The **Best** column in the weekday table is the fastest time for that weekday
in the selected years, with each date in `excluded.json` left out. It links to
that puzzle. **Hide outliers** does not affect it.

**Hide outliers** also drops times outside the usual range for that weekday,
short or long. That range is the first quartile minus 1.5 times the
interquartile range, through the third quartile plus the same amount. It is
computed in the browser from the years on screen. It is not written to the
file.

## Unsolved

A puzzle in **Unsolved** was started and not solved. The date links to that
puzzle on nytimes.com.

## Run locally

```bash
cd nyt-crossword
npm test
npm start
```

`npm start` serves the page, which reads `./data/stats.json`. To scrape into `./data`:

```bash
NYT_COOKIE="the NYT-S cookie value" npm run scrape
```

`data/` is gitignored.
