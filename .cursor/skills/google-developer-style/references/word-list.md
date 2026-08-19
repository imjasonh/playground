# Word list (working subset)

Preferred terms for comments and documentation. When a term isn't here, use the [official word list](https://developers.google.com/style/word-list) or the first spelling in Merriam-Webster.

**Don't use** means replace the term. **Avoid** means rewrite when you can; a precise use is OK if you define it.

## Prefer these replacements

| Avoid or don't use | Prefer |
| --- | --- |
| above / below (in a doc) | earlier, preceding / later, following |
| above / below (versions) | later / earlier |
| access (vague verb) | see, edit, find, use, view |
| actionable | useful, or omit |
| aka | also known as, or parentheses |
| allows you to | lets you |
| and/or | *and*, *or*, or spell out both cases |
| as (for because) | because |
| as of this writing, currently, presently, soon, new, latest | omit, or give a date or version |
| at this time, please note | omit |
| blacklist / whitelist / graylist | denylist, blocklist / allowlist, safelist / provisional list (or name the actual action) |
| blast radius | affected area, spatial impact |
| checkbox: check / uncheck / deselect | select / clear |
| click here | descriptive link text |
| click on | click (desktop), tap (touch) |
| comprise | consist of, contain, include |
| crazy, insane, lame, sane, sanity check | unexpected, invalid, valid, quick check, coherence check |
| desire, desired | want, need |
| disable (for broken) | inactive, unavailable, turn off |
| dummy variable (placeholder) | placeholder |
| e.g., i.e. | for example, that is |
| easy, easily, simple, simply, just | omit |
| etc., and so on | name the items, or *such as* without a trailing *etc.* |
| execute (generic) | run, start, call — unless the API name is `execute` |
| filename as a verb or plural | the `NAME` file / files |
| foo, bar, baz | realistic example names |
| frontend / front-end / front end | front end (noun), front-end (adjective) — but this repo often uses *browser app*; match local usage |
| hang (process) | stop responding, become unresponsive |
| higher / lower (versions) | later / earlier |
| k8s | Kubernetes |
| kill, terminate (generic stop) | stop, exit, cancel, end |
| let's | imperative ("Add a handler.") |
| leverage, utilize (for use) | use |
| login (verb) | sign in (verb); login (noun or adjective) is OK |
| master / slave | primary / replica, main / secondary, leader / follower, controller / worker |
| may (possibility) | can, might |
| native (vague) | built-in, or a specific term |
| once (for after) | after |
| please (in instructions) | omit |
| since (for because) | because |
| should | *must*, *can*, *might*, or "We recommend…" |
| spin up | create, start |
| ssh as a verb | connect by using SSH; use the `ssh` command |
| tarball, unzip, untar | tar file; extract |
| via | by using, through |
| vice versa | spell out both directions |
| vs. | versus |
| we (meaning the reader) | you |
| will (for current behavior) | present tense |

## Spelling and closed forms

Use American spelling. Use the first Merriam-Webster form when both exist (`canceled`, not `cancelled`).

| Term | Form |
| --- | --- |
| backend | one word |
| codebase | one word |
| data | singular mass noun (*the data is*, *less data*) |
| data center | two words |
| dialog (UI) | not *dialogue* |
| drop-down | adjective only; prefer *list* or *menu* |
| email | not *e-mail* |
| filename | one word |
| filesystem | follow the project; Google often uses *file system* |
| internet | lowercase |
| lifecycle | one word |
| runtime (environment) | one word; *run time* for "at execution time" |
| setup / set up | noun or adjective / verb |
| sign-in / sign in | noun or adjective / verb |
| timestamp | one word |
| Unicode, UTF-8 | as shown |
| Unix-like | hyphenated |
| US | not *U.S.* or *America* for the country |

## Grammar and function words

- **a / an:** use *a* before a consonant *sound* (*a SQL*, *a hex value*, *an hour*, *an SQL* is wrong if you pronounce "sequel").
- **as / since:** use *because* for causation.
- **between / among:** *between* for distinct items (even more than two); *among* for a group.
- **can / might / must:** permission or ability / uncertain possibility / requirement.
- **each:** not a synonym for *all*.
- **enable:** prefer *lets you* over *enables you to*. Don't use *enable* to mean "turn on" if the UI says *turn on*.
- **then:** keep *then* in *if…then* statements.
- **this / that:** follow with a noun when you can (*this setting*, not bare *this*).
- **using:** write *by using* when *using* could attach to the wrong noun.
- **which / that:** comma + *which* for extra information; *that* for a restriction.

## Inclusive and figurative terms (don't use)

Replace or write around: *abort* (prefer stop, exit, cancel), *black-box* (opaque-box testing, synthetic monitoring), *blackhat*, *blind* to, *break-glass* (emergency access), *brown bag*, *cripple*, *dumb down*, *hang* (except the HANGUP signal), *man-in-the-middle* (on-path attacker), *man hours*, *master*/*slave*, *mom test*, *monkey test*, *native* for people, *sanity check*, *sexy*, *sherpa*, *shift left* (move earlier), *single pane of glass*, *slave*, *tl;dr*, *tribal knowledge*, *war room*, *whitelist*.

If the identifier exists only in third-party code, cite it in code font once and use the preferred term afterward.

## UI verbs

| Action | Verb |
| --- | --- |
| Mouse, desktop | click (not *click on*) |
| Touch | tap |
| Mechanical button | press |
| Checkbox on | select |
| Checkbox off | clear |
| Choose from options | select |
| Enter text | enter (not *type*, unless typing is the point) |
| Reveal a collapsed control | expand |
| Menu path | **File** > **Save** (or the project's existing pattern) |

Don't call a link a button. Don't use *under* for a labeled field; write "In the **Name** field, enter…".
