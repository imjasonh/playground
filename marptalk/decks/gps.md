---
marp: true
title: How GPS finds you
theme: uncover
paginate: true
lang: en-US
style: |
  section {
    font-size: 34px;
  }
  section.lead h1 {
    font-size: 72px;
  }
  strong {
    color: #2563eb;
  }
  table {
    font-size: 34px;
  }
  svg {
    display: block;
    margin: 0 auto;
  }
  .big {
    font-size: 96px;
    font-weight: 700;
    margin: 0;
  }
---

<!-- _class: lead -->
<!-- _paginate: false -->

# How GPS finds you

Time, distance, and relativity

<!--
Your phone can tell where you are to within a few meters, almost anywhere on Earth, without sending a single bit to space. It only listens. The trick is that GPS is really a system for measuring time very precisely, and position falls out of the arithmetic. Let's work through it, one satellite at a time.
-->

---

# Clocks in orbit

- About 30 satellites
- 20,200 km up, two orbits a day
- Atomic clocks on board
- Each one broadcasts its time and position

<!--
The GPS constellation has about thirty working satellites, run by the United States Space Force. They orbit roughly twenty thousand kilometers up and go around the Earth about twice a day. Each one carries atomic clocks, and each one constantly broadcasts two things: the exact time the signal left, and where the satellite was at that moment.
-->

---

# Time becomes distance

<p class="big">1 ns ≈ 30 cm</p>

Signal delay × speed of light = range

<!--
Radio signals travel at the speed of light. Your receiver notes when each signal arrives, subtracts the time stamped inside it, and multiplies by the speed of light to get the distance to that satellite. Light covers about thirty centimeters in a nanosecond, so the timing has to be extremely precise. An error of one millionth of a second puts you three hundred meters off.
-->

---

# Spheres intersect

<svg viewBox="100 0 820 560" width="760" role="img" aria-label="Three circles centered on three satellites meet at one point, your position">
  <circle cx="330" cy="200" r="197.2" fill="#2563eb" fill-opacity="0.07" stroke="#2563eb" stroke-width="3" />
  <circle cx="690" cy="215" r="208.1" fill="#dc2626" fill-opacity="0.07" stroke="#dc2626" stroke-width="3" />
  <circle cx="560" cy="410" r="125.3" fill="#16a34a" fill-opacity="0.07" stroke="#16a34a" stroke-width="3" />
  <line x1="330" y1="200" x2="500" y2="300" stroke="#2563eb" stroke-width="2" stroke-dasharray="6 6" />
  <circle cx="330" cy="200" r="16" fill="#2563eb" />
  <text x="330" y="207" text-anchor="middle" font-size="20" font-weight="700" fill="#ffffff">1</text>
  <line x1="690" y1="215" x2="500" y2="300" stroke="#dc2626" stroke-width="2" stroke-dasharray="6 6" />
  <circle cx="690" cy="215" r="16" fill="#dc2626" />
  <text x="690" y="222" text-anchor="middle" font-size="20" font-weight="700" fill="#ffffff">2</text>
  <line x1="560" y1="410" x2="500" y2="300" stroke="#16a34a" stroke-width="2" stroke-dasharray="6 6" />
  <circle cx="560" cy="410" r="16" fill="#16a34a" />
  <text x="560" y="417" text-anchor="middle" font-size="20" font-weight="700" fill="#ffffff">3</text>
  <circle cx="500" cy="300" r="10" fill="currentColor" />
  <text x="480" y="310" text-anchor="end" font-size="30" font-weight="700" stroke="#ffffff" stroke-width="8" fill="#ffffff">you</text>
  <text x="480" y="310" text-anchor="end" font-size="30" font-weight="700" fill="currentColor">you</text>
</svg>

<!--
One distance tells you that you're somewhere on a sphere around that satellite. Two spheres meet in a circle, and a third cuts that circle at two points. One of them is usually far out in space, so the receiver throws it away. This flat picture shows the idea with circles. Each circle is every point at the measured distance from one satellite, and only your position is on all three. That's trilateration.
-->

---

# Why it takes four

- Your phone's clock is cheap quartz
- Its error is a fourth unknown: x, y, z, and **t**
- Four satellites, four equations

<!--
There's a catch. Your phone doesn't have an atomic clock. Its quartz clock might be off by a whole millisecond, which is three hundred kilometers of error. So the receiver treats its own clock error as a fourth unknown, next to the three coordinates. Four unknowns need four equations, which means four satellites. As a bonus, solving them makes your phone's clock nearly as good as the satellites'.
-->

---

# Relativity is in the math

| Effect | Clock drift per day |
| --- | ---: |
| Weaker gravity (general) | +45 µs |
| Orbital speed (special) | −7 µs |
| **Net** | **+38 µs** |

<!--
Now for Einstein. Up in orbit, gravity is weaker, and general relativity says clocks there run faster, by about forty five microseconds a day. The satellites also move fast, and special relativity slows them by about seven. The net effect is thirty eight microseconds a day. Left uncorrected, that would add roughly ten kilometers of error every day. So the satellite clocks are tuned to tick slightly slow before launch.
-->

---

# What still goes wrong

- The ionosphere slows the signal
- Buildings reflect it
- Satellites bunched in one part of the sky

<!--
Even with perfect clocks, the signal has a rough trip. Charged gas high in the atmosphere, the ionosphere, slows it down by a varying amount. In cities, signals bounce off buildings and arrive late, which is why your blue dot wanders downtown. And if the visible satellites sit close together in the sky, small errors grow into large ones. Under open sky, a phone usually lands within about five meters.
-->

---

# How phones do better

- Two frequencies cancel most ionosphere delay
- Galileo, GLONASS, and BeiDou add more satellites
- Assisted GPS downloads orbit data over the network

<!--
Modern phones fight back in three ways. Newer chips listen on two frequencies, and because the ionosphere delays each one differently, comparing them cancels most of the error. Phones also use Europe's Galileo, Russia's GLONASS, and China's BeiDou, so far more satellites are in view. And assisted GPS downloads the orbit data over the cell network, so a fix takes seconds instead of a minute.
-->

---

<!-- _class: lead -->

# Recap

Time → distance → position

<!--
So every time your map shows a blue dot, your phone has timed radio signals from at least four satellites, turned those times into distances, solved for its position and its own clock error, and relied on corrections from both of Einstein's theories of relativity. All of that happens many times a second, from signals weaker than the background noise.
-->
