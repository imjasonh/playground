export const BOARD = Object.freeze({
  width: 720,
  height: 1080,
  barLeftX: 70,
  barRightX: 650,
  minBarY: 138,
  maxBarY: 1010,
  resetBarY: 1010,
  maxTilt: 190,
  barSpeed: 430,
  barRadius: 9,
  ballRadius: 19,
  ballOffset: 28,
  gravity: 3900,
  rollingDrag: 1.25,
  maxBallSpeed: 960,
  edgeBounce: 0.36,
  captureRadius: 28,
  fallDuration: 0.62,
  resetGrace: 0.5,
});

export const HOLES = Object.freeze(
  [
    { id: 1, x: 485, y: 870, radius: 32 },
    { id: 2, x: 210, y: 785, radius: 32 },
    { id: 3, x: 550, y: 705, radius: 32 },
    { id: 4, x: 350, y: 620, radius: 32 },
    { id: 5, x: 145, y: 530, radius: 32 },
    { id: 6, x: 495, y: 455, radius: 32 },
    { id: 7, x: 270, y: 365, radius: 32 },
    { id: 8, x: 570, y: 285, radius: 32 },
    { id: 9, x: 170, y: 205, radius: 32 },
    { id: 10, x: 420, y: 132, radius: 32 },
  ].map(Object.freeze),
);

const clamp = (value, min, max) => Math.min(max, Math.max(min, value));

export function axisFromDrag(startY, currentY, travel = 58) {
  if (!Number.isFinite(startY) || !Number.isFinite(currentY) || travel <= 0) {
    return 0;
  }

  return clamp((startY - currentY) / travel, -1, 1);
}

export function pointToSegmentDistanceSquared(px, py, ax, ay, bx, by) {
  const dx = bx - ax;
  const dy = by - ay;
  const lengthSquared = dx * dx + dy * dy;

  if (lengthSquared === 0) {
    return (px - ax) ** 2 + (py - ay) ** 2;
  }

  const amount = clamp(((px - ax) * dx + (py - ay) * dy) / lengthSquared, 0, 1);
  const nearestX = ax + amount * dx;
  const nearestY = ay + amount * dy;
  return (px - nearestX) ** 2 + (py - nearestY) ** 2;
}

export class ColdClimbGame {
  constructor() {
    this.events = [];
    this.phase = "ready";
    this.level = 0;
    this.score = 0;
    this.lives = 3;
    this.leftControl = 0;
    this.rightControl = 0;
    this.leftBarY = BOARD.resetBarY;
    this.rightBarY = BOARD.resetBarY;
    this.ballX = BOARD.width / 2;
    this.ballVelocityX = 0;
    this.roundTime = 0;
    this.roundGrace = BOARD.resetGrace;
    this.fall = null;
  }

  get target() {
    return HOLES[this.level] ?? null;
  }

  get ballY() {
    if (this.phase === "falling" && this.fall) {
      const progress = Math.min(1, this.fall.elapsed / BOARD.fallDuration);
      const eased = progress * progress;
      return this.fall.originY + (this.fall.hole.y - this.fall.originY) * eased;
    }

    return this.barYAt(this.ballX) - BOARD.ballOffset;
  }

  get ballScale() {
    if (this.phase !== "falling" || !this.fall) {
      return 1;
    }

    const progress = Math.min(1, this.fall.elapsed / BOARD.fallDuration);
    return 1 - progress * 0.72;
  }

  barYAt(x) {
    const amount = clamp(
      (x - BOARD.barLeftX) / (BOARD.barRightX - BOARD.barLeftX),
      0,
      1,
    );
    return this.leftBarY + (this.rightBarY - this.leftBarY) * amount;
  }

  start() {
    this.phase = "playing";
    this.level = 0;
    this.score = 0;
    this.lives = 3;
    this.events.length = 0;
    this.#resetRound();
    this.events.push({ type: "started", target: this.target });
  }

  setControls(left, right) {
    this.leftControl = clamp(Number.isFinite(left) ? left : 0, -1, 1);
    this.rightControl = clamp(Number.isFinite(right) ? right : 0, -1, 1);
  }

  update(deltaSeconds) {
    if (!Number.isFinite(deltaSeconds) || deltaSeconds <= 0) {
      return;
    }

    let remaining = Math.min(deltaSeconds, 0.1);
    while (remaining > 0) {
      const step = Math.min(remaining, 1 / 120);
      this.#step(step);
      remaining -= step;
    }
  }

  consumeEvents() {
    return this.events.splice(0);
  }

  #step(deltaSeconds) {
    if (this.phase === "falling") {
      this.fall.elapsed += deltaSeconds;
      if (this.fall.elapsed >= BOARD.fallDuration) {
        this.#finishFall();
      }
      return;
    }

    if (this.phase !== "playing") {
      return;
    }

    const previousX = this.ballX;
    const previousY = this.ballY;

    this.#moveBar(deltaSeconds);
    this.#rollBall(deltaSeconds);

    this.roundTime += deltaSeconds;
    this.roundGrace = Math.max(0, this.roundGrace - deltaSeconds);

    if (this.roundGrace === 0) {
      this.#checkHoles(previousX, previousY, this.ballX, this.ballY);
    }
  }

  #moveBar(deltaSeconds) {
    let nextLeft =
      this.leftBarY - this.leftControl * BOARD.barSpeed * deltaSeconds;
    let nextRight =
      this.rightBarY - this.rightControl * BOARD.barSpeed * deltaSeconds;

    nextLeft = clamp(nextLeft, BOARD.minBarY, BOARD.maxBarY);
    nextRight = clamp(nextRight, BOARD.minBarY, BOARD.maxBarY);

    const difference = nextRight - nextLeft;
    if (difference > BOARD.maxTilt) {
      if (Math.abs(this.leftControl) > Math.abs(this.rightControl)) {
        nextLeft = nextRight - BOARD.maxTilt;
      } else {
        nextRight = nextLeft + BOARD.maxTilt;
      }
    } else if (difference < -BOARD.maxTilt) {
      if (Math.abs(this.rightControl) > Math.abs(this.leftControl)) {
        nextRight = nextLeft - BOARD.maxTilt;
      } else {
        nextLeft = nextRight + BOARD.maxTilt;
      }
    }

    this.leftBarY = clamp(nextLeft, BOARD.minBarY, BOARD.maxBarY);
    this.rightBarY = clamp(nextRight, BOARD.minBarY, BOARD.maxBarY);
  }

  #rollBall(deltaSeconds) {
    const width = BOARD.barRightX - BOARD.barLeftX;
    const slope = (this.rightBarY - this.leftBarY) / width;
    this.ballVelocityX += BOARD.gravity * slope * deltaSeconds;
    this.ballVelocityX *= Math.exp(-BOARD.rollingDrag * deltaSeconds);
    this.ballVelocityX = clamp(
      this.ballVelocityX,
      -BOARD.maxBallSpeed,
      BOARD.maxBallSpeed,
    );
    this.ballX += this.ballVelocityX * deltaSeconds;

    const minimumX = BOARD.barLeftX + BOARD.ballRadius;
    const maximumX = BOARD.barRightX - BOARD.ballRadius;

    if (this.ballX < minimumX) {
      this.ballX = minimumX;
      this.ballVelocityX = Math.abs(this.ballVelocityX) * BOARD.edgeBounce;
      this.events.push({ type: "edge", side: "left" });
    } else if (this.ballX > maximumX) {
      this.ballX = maximumX;
      this.ballVelocityX = -Math.abs(this.ballVelocityX) * BOARD.edgeBounce;
      this.events.push({ type: "edge", side: "right" });
    }
  }

  #checkHoles(previousX, previousY, nextX, nextY) {
    const captureDistanceSquared = BOARD.captureRadius ** 2;
    let capturedHole = null;
    let closestDistanceSquared = Number.POSITIVE_INFINITY;

    for (const hole of HOLES) {
      const distanceSquared = pointToSegmentDistanceSquared(
        hole.x,
        hole.y,
        previousX,
        previousY,
        nextX,
        nextY,
      );

      if (
        distanceSquared <= captureDistanceSquared &&
        distanceSquared < closestDistanceSquared
      ) {
        capturedHole = hole;
        closestDistanceSquared = distanceSquared;
      }
    }

    if (capturedHole) {
      this.#beginFall(capturedHole);
    }
  }

  #beginFall(hole) {
    const success = hole.id === this.target?.id;
    this.phase = "falling";
    this.leftControl = 0;
    this.rightControl = 0;
    this.fall = {
      hole,
      success,
      elapsed: 0,
      originX: this.ballX,
      originY: this.barYAt(this.ballX) - BOARD.ballOffset,
    };
    this.events.push({ type: "hole", hole, success });
  }

  #finishFall() {
    const { success, hole } = this.fall;

    if (success) {
      const timeBonus = Math.max(0, Math.floor((22 - this.roundTime) * 25));
      const points = 1000 + this.level * 250 + timeBonus;
      this.score += points;
      this.level += 1;

      if (this.level >= HOLES.length) {
        this.phase = "won";
        this.fall = null;
        this.events.push({ type: "won", points, score: this.score });
        return;
      }

      this.#resetRound();
      this.events.push({
        type: "target",
        target: this.target,
        points,
        score: this.score,
      });
      return;
    }

    this.lives -= 1;
    if (this.lives <= 0) {
      this.phase = "gameover";
      this.fall = null;
      this.events.push({ type: "gameover", hole, score: this.score });
      return;
    }

    this.#resetRound();
    this.events.push({ type: "retry", hole, lives: this.lives });
  }

  #resetRound() {
    this.phase = "playing";
    this.leftControl = 0;
    this.rightControl = 0;
    this.leftBarY = BOARD.resetBarY;
    this.rightBarY = BOARD.resetBarY;
    this.ballX = BOARD.width / 2;
    this.ballVelocityX = 0;
    this.roundTime = 0;
    this.roundGrace = BOARD.resetGrace;
    this.fall = null;
  }
}
