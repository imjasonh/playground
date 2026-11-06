---
marp: true
title: Conway's Game of Life
theme: gaia
class: invert
paginate: true
lang: en-US
style: |
  section {
    font-size: 32px;
  }
  pre {
    font-size: 30px;
    line-height: 1.1;
    background: transparent;
    border: 0;
  }
  pre code {
    background: transparent;
    color: var(--color-foreground);
  }
  .row {
    display: flex;
    justify-content: center;
    gap: 64px;
    align-items: flex-start;
  }
  .row > div {
    flex: 0 0 300px;
  }
  .row.four > div {
    flex-basis: 220px;
  }
  .row pre code {
    font-size: 40px;
    line-height: 1.1;
  }
  .row p {
    margin: 8px 0 0;
    font-size: 26px;
    text-align: center;
  }
  table {
    font-size: 32px;
  }
---

<!-- _class: lead invert -->
<!-- _paginate: false -->

# Conway's Game of Life

A grid, two states, and four rules

<!--
In 1970 the mathematician John Conway invented a game with no players. You set up a pattern of cells on a grid, press go, and watch. Martin Gardner wrote about it in Scientific American that October, and people have been finding new patterns ever since. Here's how it works, and why something so simple turned out to be as powerful as a computer.
-->

---

# The board

- An endless grid of square cells
- Each cell is alive or dead
- Each cell has eight neighbors
- Every cell updates at once, each generation

<!--
The board is a grid that goes on forever in every direction. Each square is a cell, and each cell is either alive or dead. A cell's neighbors are the eight cells that touch it, including the diagonals. Time moves in steps called generations, and on each step every cell on the board updates at the same moment.
-->

---

# The rules

| A cell that is | with this many live neighbors | becomes |
| --- | :---: | --- |
| alive | 0 or 1 | dead |
| alive | 2 or 3 | alive |
| alive | 4 or more | dead |
| dead | exactly 3 | alive |

<!--
Here are all the rules. A live cell with fewer than two live neighbors dies, as if from loneliness. A live cell with two or three neighbors survives. A live cell with four or more dies of overcrowding. And a dead cell with exactly three live neighbors comes to life. That's it. Fans write it as B three slash S two three: born on three, survive on two or three.
-->

---

# Still lifes never change

<div class="row">
<div>

```text
. . . .
. # # .
. # # .
. . . .
```

Block

</div>
<div>

```text
. . . . . .
. . # # . .
. # . . # .
. . # # . .
. . . . . .
```

Beehive

</div>
</div>

<!--
Some patterns settle down and stop. These are still lifes. In the block, every live cell has exactly three live neighbors, so all four survive, and no dead cell has exactly three, so nothing is born. The beehive is stable for the same reason. Most random starting patterns end up as a scatter of blocks, beehives, and a few other still lifes.
-->

---

# Oscillators repeat

<div class="row">
<div>

```text
. . . . .
. . # . .
. . # . .
. . # . .
. . . . .
```

Generation 1

</div>
<div>

```text
. . . . .
. . . . .
. # # # .
. . . . .
. . . . .
```

Generation 2

</div>
</div>

<!--
Other patterns cycle forever. This one is the blinker. The middle cell always has two neighbors, so it survives. The two end cells have only one neighbor each, so they die. Meanwhile the cells to the left and right of the middle each see three live neighbors, so they're born. The line flips from vertical to horizontal and back, with a period of two generations.
-->

---

# The glider travels

<div class="row four">
<div>

```text
. # . .
. . # .
# # # .
. . . .
```

</div>
<div>

```text
. . . .
# . # .
. # # .
. # . .
```

</div>
<div>

```text
. . . .
. . # .
# . # .
. # # .
```

</div>
<div>

```text
. . . .
. # . .
. . # #
. # # .
```

</div>
</div>

<!--
Then there are spaceships, which move. The smallest is the glider: five cells that cycle through four shapes. After four generations it looks exactly like it did at the start, shifted one cell down and one cell to the right. So it crawls diagonally across the board forever, at a quarter of the fastest speed anything in Life can go.
-->

---

# Guns make gliders

- Conway offered $50 for a pattern that grows forever
- Bill Gosper's team at MIT won it in November 1970
- The Gosper glider gun fires a new glider every 30 generations

<!--
Conway guessed that no pattern could grow without limit, and offered a fifty dollar prize to anyone who could prove him right or wrong. A month after Gardner's column, Bill Gosper and a group at M I T found a pattern that fires a new glider every thirty generations. It runs forever, and the number of live cells keeps growing. Conway paid up.
-->

---

# Life can compute anything

- Gliders carry signals
- Colliding streams of gliders act as logic gates
- Gates combine into memory and a processor

<!--
That gun was the key to something bigger. A stream of gliders can carry a signal, where a glider means one and a gap means zero. Aim two streams at each other and the collisions behave like logic gates. From gates you can build memory, counters, and eventually a whole computer. Conway showed that Life is universal: given a big enough board, it can compute anything a laptop can.
-->

---

# Some questions have no answer

- Will this pattern ever die out?
- No algorithm can decide that for every pattern
- The only general method is to run it and watch

<!--
Being universal has a strange consequence. Because Life can simulate any computer, asking whether a pattern eventually dies out is as hard as asking whether a program eventually stops, and Alan Turing proved that no algorithm can answer that in general. For four rules on a grid of squares, that is a remarkable amount of depth.
-->

---

<!-- _class: lead invert -->

# Try it

Draw a pattern in **life-lab** in this playground and print its history in 3D

<!--
The best way to understand Life is to play with it. Draw a pattern, step it forward, and see whether it dies, settles, or flies away. The life lab app in this playground lets you draw a starting pattern and turn its history into a 3D printable sculpture, with time running up the vertical axis. Gliders become little diagonal staircases.
-->
