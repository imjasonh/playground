import C3BootProofs.Proofs.Sha512Round
import C3BootProofs.Proofs.Sha256Loop

/-!
# `compress512`: one schedule step

The schedule loop, from 0x11A to 0x1F0, fills `W[16]` to `W[79]` in the
640-byte array at `F + 0xD8`. Each pass computes `W[t]` from `W[t - 2]`,
`W[t - 7]`, `W[t - 15]`, and `W[t - 16]`, which it loads from below the
pointer in `a1`, and stores it at `a1`.
-/

namespace C3.RV32

open C3.Image

def s5Sched : List BInstr :=
  [.lw (29 : Fin 32) a1 0xFFFFFFF0,
   .lw a2 a1 0xFFFFFFF4,
   .lw (5 : Fin 32) a1 0xFFFFFFC8,
   .lw (17 : Fin 32) a1 0xFFFFFFCC,
   .aluImm .srl a5 (29 : Fin 32) 0x13,
   .aluImm .sll (8 : Fin 32) a2 0xD,
   .aluImm .srl a0 a2 0x13,
   .aluImm .sll a3 (29 : Fin 32) 0xD,
   .aluImm .srl (6 : Fin 32) a2 0x1D,
   .aluImm .srl (9 : Fin 32) (29 : Fin 32) 0x1D,
   .alu .or a4 (8 : Fin 32) a5,
   .alu .or a0 a0 a3,
   .aluImm .sll a3 a2 0x3,
   .aluImm .sll a5 (29 : Fin 32) 0x3,
   .alu .or a3 a3 (9 : Fin 32),
   .alu .or a5 a5 (6 : Fin 32),
   .alu .xor (28 : Fin 32) a0 a3,
   .lw (6 : Fin 32) a1 0xFFFFFF80,
   .lw (7 : Fin 32) a1 0xFFFFFF84,
   .lw a3 a1 0xFFFFFF88,
   .lw (8 : Fin 32) a1 0xFFFFFF8C,
   .aluImm .sll (9 : Fin 32) a2 0x1A,
   .aluImm .srl a0 (29 : Fin 32) 0x6,
   .alu .xor a5 a5 a4,
   .alu .or a0 a0 (9 : Fin 32),
   .aluImm .srl a2 a2 0x6,
   .alu .xor (29 : Fin 32) a5 a0,
   .aluImm .srl (9 : Fin 32) (8 : Fin 32) 0x1,
   .aluImm .sll a5 a3 0x1F,
   .alu .xor (28 : Fin 32) (28 : Fin 32) a2,
   .alu .or a2 a5 (9 : Fin 32),
   .aluImm .srl a5 a3 0x1,
   .aluImm .sll (9 : Fin 32) (8 : Fin 32) 0x1F,
   .alu .or a5 a5 (9 : Fin 32),
   .aluImm .srl (9 : Fin 32) (8 : Fin 32) 0x8,
   .aluImm .srl a0 a3 0x8,
   .aluImm .sll a4 (8 : Fin 32) 0x18,
   .alu .or a0 a0 a4,
   .aluImm .sll a4 a3 0x18,
   .alu .or a4 a4 (9 : Fin 32),
   .alu .xor a0 a0 a5,
   .alu .xor a2 a2 a4,
   .aluImm .sll a4 (8 : Fin 32) 0x19,
   .aluImm .srl a3 a3 0x7,
   .aluImm .srl (8 : Fin 32) (8 : Fin 32) 0x7,
   .alu .or a3 a3 a4,
   .alu .xor a2 a2 (8 : Fin 32),
   .alu .xor a0 a0 a3,
   .alu .add (6 : Fin 32) (6 : Fin 32) (5 : Fin 32),
   .alu .add (17 : Fin 32) (17 : Fin 32) (7 : Fin 32),
   .alu .sltu a3 (6 : Fin 32) (5 : Fin 32),
   .alu .add a3 a3 (17 : Fin 32),
   .alu .add (29 : Fin 32) (29 : Fin 32) (6 : Fin 32),
   .alu .add a3 a3 (28 : Fin 32),
   .alu .sltu a4 (29 : Fin 32) (6 : Fin 32),
   .alu .add a0 a0 (29 : Fin 32),
   .alu .add a2 a2 a3,
   .alu .sltu a3 a0 (29 : Fin 32),
   .alu .add a2 a2 a4,
   .alu .add a2 a2 a3]

def s5SchedS0 : List BInstr :=
  [.lw (29 : Fin 32) a1 0xFFFFFFF0,
   .lw a2 a1 0xFFFFFFF4,
   .lw (5 : Fin 32) a1 0xFFFFFFC8,
   .lw a7 a1 0xFFFFFFCC,
   .aluImm .srl a5 (29 : Fin 32) 0x13,
   .aluImm .sll (8 : Fin 32) a2 0xD,
   .aluImm .srl a0 a2 0x13,
   .aluImm .sll a3 (29 : Fin 32) 0xD,
   .aluImm .srl (6 : Fin 32) a2 0x1D,
   .aluImm .srl (9 : Fin 32) (29 : Fin 32) 0x1D,
   .alu .or a4 (8 : Fin 32) a5,
   .alu .or a0 a0 a3]

def s5SchedS1 : List BInstr :=
  [.aluImm .sll a3 a2 0x3,
   .aluImm .sll a5 (29 : Fin 32) 0x3,
   .alu .or a3 a3 (9 : Fin 32),
   .alu .or a5 a5 (6 : Fin 32),
   .alu .xor (28 : Fin 32) a0 a3,
   .lw (6 : Fin 32) a1 0xFFFFFF80,
   .lw (7 : Fin 32) a1 0xFFFFFF84,
   .lw a3 a1 0xFFFFFF88,
   .lw (8 : Fin 32) a1 0xFFFFFF8C,
   .aluImm .sll (9 : Fin 32) a2 0x1A,
   .aluImm .srl a0 (29 : Fin 32) 0x6,
   .alu .xor a5 a5 a4]

def s5SchedS2 : List BInstr :=
  [.alu .or a0 a0 (9 : Fin 32),
   .aluImm .srl a2 a2 0x6,
   .alu .xor (29 : Fin 32) a5 a0,
   .aluImm .srl (9 : Fin 32) (8 : Fin 32) 0x1,
   .aluImm .sll a5 a3 0x1F,
   .alu .xor (28 : Fin 32) (28 : Fin 32) a2,
   .alu .or a2 a5 (9 : Fin 32),
   .aluImm .srl a5 a3 0x1,
   .aluImm .sll (9 : Fin 32) (8 : Fin 32) 0x1F,
   .alu .or a5 a5 (9 : Fin 32),
   .aluImm .srl (9 : Fin 32) (8 : Fin 32) 0x8,
   .aluImm .srl a0 a3 0x8]

def s5SchedS3 : List BInstr :=
  [.aluImm .sll a4 (8 : Fin 32) 0x18,
   .alu .or a0 a0 a4,
   .aluImm .sll a4 a3 0x18,
   .alu .or a4 a4 (9 : Fin 32),
   .alu .xor a0 a0 a5,
   .alu .xor a2 a2 a4,
   .aluImm .sll a4 (8 : Fin 32) 0x19,
   .aluImm .srl a3 a3 0x7,
   .aluImm .srl (8 : Fin 32) (8 : Fin 32) 0x7,
   .alu .or a3 a3 a4,
   .alu .xor a2 a2 (8 : Fin 32),
   .alu .xor a0 a0 a3]

def s5SchedS4 : List BInstr :=
  [.alu .add (6 : Fin 32) (6 : Fin 32) (5 : Fin 32),
   .alu .add a7 a7 (7 : Fin 32),
   .alu .sltu a3 (6 : Fin 32) (5 : Fin 32),
   .alu .add a3 a3 a7,
   .alu .add (29 : Fin 32) (29 : Fin 32) (6 : Fin 32),
   .alu .add a3 a3 (28 : Fin 32),
   .alu .sltu a4 (29 : Fin 32) (6 : Fin 32),
   .alu .add a0 a0 (29 : Fin 32),
   .alu .add a2 a2 a3,
   .alu .sltu a3 a0 (29 : Fin 32),
   .alu .add a2 a2 a4,
   .alu .add a2 a2 a3]

theorem s5Sched_split : s5Sched = s5SchedS0 ++ s5SchedS1 ++ s5SchedS2 ++ s5SchedS3 ++ s5SchedS4 := rfl

set_option maxRecDepth 100000 in
theorem s5SchedS0_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5SchedS0 (M, f) = (M, g) ∧ ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Word,
      memLoad32 M (f a1 + 0xFFFFFFF0) = v0 ∧
      memLoad32 M (f a1 + 0xFFFFFFF4) = v1 ∧
      memLoad32 M (f a1 + 0xFFFFFFC8) = v2 ∧
      memLoad32 M (f a1 + 0xFFFFFFCC) = v3 ∧
      aluEval .srl v0 0x13 = v4 ∧
      aluEval .sll v1 0xD = v5 ∧
      aluEval .srl v1 0x13 = v6 ∧
      aluEval .sll v0 0xD = v7 ∧
      aluEval .srl v1 0x1D = v8 ∧
      aluEval .srl v0 0x1D = v9 ∧
      aluEval .or v5 v4 = v10 ∧
      aluEval .or v6 v7 = v11 ∧
      g (5 : Fin 32) = v2 ∧
      g (6 : Fin 32) = v8 ∧
      g (9 : Fin 32) = v9 ∧
      g a0 = v11 ∧
      g a1 = f a1 ∧
      g a2 = v1 ∧
      g a4 = v10 ∧
      g a7 = v3 ∧
      g (29 : Fin 32) = v0 :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5SchedS1_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5SchedS1 (M, f) = (M, g) ∧ ∃ v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : Word,
      aluEval .sll (f a2) 0x3 = v12 ∧
      aluEval .sll (f (29 : Fin 32)) 0x3 = v13 ∧
      aluEval .or v12 (f (9 : Fin 32)) = v14 ∧
      aluEval .or v13 (f (6 : Fin 32)) = v15 ∧
      aluEval .xor (f a0) v14 = v16 ∧
      memLoad32 M (f a1 + 0xFFFFFF80) = v17 ∧
      memLoad32 M (f a1 + 0xFFFFFF84) = v18 ∧
      memLoad32 M (f a1 + 0xFFFFFF88) = v19 ∧
      memLoad32 M (f a1 + 0xFFFFFF8C) = v20 ∧
      aluEval .sll (f a2) 0x1A = v21 ∧
      aluEval .srl (f (29 : Fin 32)) 0x6 = v22 ∧
      aluEval .xor v15 (f a4) = v23 ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = v17 ∧
      g (7 : Fin 32) = v18 ∧
      g (8 : Fin 32) = v20 ∧
      g (9 : Fin 32) = v21 ∧
      g a0 = v22 ∧
      g a2 = f a2 ∧
      g a3 = v19 ∧
      g a5 = v23 ∧
      g a7 = f a7 ∧
      g (28 : Fin 32) = v16 :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5SchedS2_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5SchedS2 (M, f) = (M, g) ∧ ∃ v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 : Word,
      aluEval .or (f a0) (f (9 : Fin 32)) = v24 ∧
      aluEval .srl (f a2) 0x6 = v25 ∧
      aluEval .xor (f a5) v24 = v26 ∧
      aluEval .srl (f (8 : Fin 32)) 0x1 = v27 ∧
      aluEval .sll (f a3) 0x1F = v28 ∧
      aluEval .xor (f (28 : Fin 32)) v25 = v29 ∧
      aluEval .or v28 v27 = v30 ∧
      aluEval .srl (f a3) 0x1 = v31 ∧
      aluEval .sll (f (8 : Fin 32)) 0x1F = v32 ∧
      aluEval .or v31 v32 = v33 ∧
      aluEval .srl (f (8 : Fin 32)) 0x8 = v34 ∧
      aluEval .srl (f a3) 0x8 = v35 ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g (8 : Fin 32) = f (8 : Fin 32) ∧
      g (9 : Fin 32) = v34 ∧
      g a0 = v35 ∧
      g a2 = v30 ∧
      g a3 = f a3 ∧
      g a5 = v33 ∧
      g a7 = f a7 ∧
      g (28 : Fin 32) = v29 ∧
      g (29 : Fin 32) = v26 :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5SchedS3_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5SchedS3 (M, f) = (M, g) ∧ ∃ v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 : Word,
      aluEval .sll (f (8 : Fin 32)) 0x18 = v36 ∧
      aluEval .or (f a0) v36 = v37 ∧
      aluEval .sll (f a3) 0x18 = v38 ∧
      aluEval .or v38 (f (9 : Fin 32)) = v39 ∧
      aluEval .xor v37 (f a5) = v40 ∧
      aluEval .xor (f a2) v39 = v41 ∧
      aluEval .sll (f (8 : Fin 32)) 0x19 = v42 ∧
      aluEval .srl (f a3) 0x7 = v43 ∧
      aluEval .srl (f (8 : Fin 32)) 0x7 = v44 ∧
      aluEval .or v43 v42 = v45 ∧
      aluEval .xor v41 v44 = v46 ∧
      aluEval .xor v40 v45 = v47 ∧
      g (5 : Fin 32) = f (5 : Fin 32) ∧
      g (6 : Fin 32) = f (6 : Fin 32) ∧
      g (7 : Fin 32) = f (7 : Fin 32) ∧
      g a0 = v47 ∧
      g a2 = v46 ∧
      g a7 = f a7 ∧
      g (28 : Fin 32) = f (28 : Fin 32) ∧
      g (29 : Fin 32) = f (29 : Fin 32) :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem s5SchedS4_dag (M : Word → BitVec 8) (f : Fin 32 → Word) :
    ∃ g : Fin 32 → Word, runBlock s5SchedS4 (M, f) = (M, g) ∧ ∃ v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 : Word,
      aluEval .add (f (6 : Fin 32)) (f (5 : Fin 32)) = v48 ∧
      aluEval .add (f a7) (f (7 : Fin 32)) = v49 ∧
      aluEval .sltu v48 (f (5 : Fin 32)) = v50 ∧
      aluEval .add v50 v49 = v51 ∧
      aluEval .add (f (29 : Fin 32)) v48 = v52 ∧
      aluEval .add v51 (f (28 : Fin 32)) = v53 ∧
      aluEval .sltu v52 v48 = v54 ∧
      aluEval .add (f a0) v52 = v55 ∧
      aluEval .add (f a2) v53 = v56 ∧
      aluEval .sltu v55 v52 = v57 ∧
      aluEval .add v56 v54 = v58 ∧
      aluEval .add v58 v57 = v59 ∧
      g a0 = v55 ∧
      g a2 = v59 :=
  ⟨_, rfl, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
/-- One schedule step's arithmetic, from 0x124 to 0x1E4: `W[t]` in `a0` and `a2`. -/
theorem s5Sched_run {M : Word → BitVec 8} {f : Fin 32 → Word} {w : Nat → Sha512.W64} {t : Nat} {p : Word}
    (hp : f a1 = p)
    (hw2l : memLoad32 M (p + 0xFFFFFFF0) = lo64 (w (t - 2))) (hw2h : memLoad32 M (p + 0xFFFFFFF4) = hi64 (w (t - 2)))
    (hw7l : memLoad32 M (p + 0xFFFFFFC8) = lo64 (w (t - 7))) (hw7h : memLoad32 M (p + 0xFFFFFFCC) = hi64 (w (t - 7)))
    (hw16l : memLoad32 M (p + 0xFFFFFF80) = lo64 (w (t - 16))) (hw16h : memLoad32 M (p + 0xFFFFFF84) = hi64 (w (t - 16)))
    (hw15l : memLoad32 M (p + 0xFFFFFF88) = lo64 (w (t - 15))) (hw15h : memLoad32 M (p + 0xFFFFFF8C) = hi64 (w (t - 15))) :
    (runBlock s5Sched (M, f)).1 = M ∧
    (runBlock s5Sched (M, f)).2 a0 = lo64 (Sha512.smallSigma1 (w (t - 2)) + w (t - 7) + Sha512.smallSigma0 (w (t - 15)) + w (t - 16)) ∧
    (runBlock s5Sched (M, f)).2 a2 = hi64 (Sha512.smallSigma1 (w (t - 2)) + w (t - 7) + Sha512.smallSigma0 (w (t - 15)) + w (t - 16)) := by
  refine ⟨rfl, ?_⟩
  have E : runBlock s5Sched (M, f) = runBlock s5SchedS4 (runBlock s5SchedS3 (runBlock s5SchedS2 (runBlock s5SchedS1 (runBlock s5SchedS0 (M, f))))) := by
    rw [s5Sched_split]; simp only [runBlock_append]
  obtain ⟨f1, e1, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, F1_5, F1_6, F1_9, F1_10, F1_11, F1_12, F1_14, F1_17, F1_29⟩ := s5SchedS0_dag M f
  rw [e1] at E
  rw [hp] at h0
  rw [hp] at h1
  rw [hp] at h2
  rw [hp] at h3
  rw [hp] at F1_11
  obtain ⟨f2, e2, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, F2_5, F2_6, F2_7, F2_8, F2_9, F2_10, F2_12, F2_13, F2_15, F2_17, F2_28⟩ := s5SchedS1_dag M f1
  rw [e2] at E
  rw [F1_12] at h12
  rw [F1_29] at h13
  rw [F1_9] at h14
  rw [F1_6] at h15
  rw [F1_10] at h16
  rw [F1_11] at h17
  rw [F1_11] at h18
  rw [F1_11] at h19
  rw [F1_11] at h20
  rw [F1_12] at h21
  rw [F1_29] at h22
  rw [F1_14] at h23
  rw [F1_5] at F2_5
  rw [F1_12] at F2_12
  rw [F1_17] at F2_17
  obtain ⟨f3, e3, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, F3_5, F3_6, F3_7, F3_8, F3_9, F3_10, F3_12, F3_13, F3_15, F3_17, F3_28, F3_29⟩ := s5SchedS2_dag M f2
  rw [e3] at E
  rw [F2_10, F2_9] at h24
  rw [F2_12] at h25
  rw [F2_15] at h26
  rw [F2_8] at h27
  rw [F2_13] at h28
  rw [F2_28] at h29
  rw [F2_13] at h31
  rw [F2_8] at h32
  rw [F2_8] at h34
  rw [F2_13] at h35
  rw [F2_5] at F3_5
  rw [F2_6] at F3_6
  rw [F2_7] at F3_7
  rw [F2_8] at F3_8
  rw [F2_13] at F3_13
  rw [F2_17] at F3_17
  obtain ⟨f4, e4, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, F4_5, F4_6, F4_7, F4_10, F4_12, F4_17, F4_28, F4_29⟩ := s5SchedS3_dag M f3
  rw [e4] at E
  rw [F3_8] at h36
  rw [F3_10] at h37
  rw [F3_13] at h38
  rw [F3_9] at h39
  rw [F3_15] at h40
  rw [F3_12] at h41
  rw [F3_8] at h42
  rw [F3_13] at h43
  rw [F3_8] at h44
  rw [F3_5] at F4_5
  rw [F3_6] at F4_6
  rw [F3_7] at F4_7
  rw [F3_17] at F4_17
  rw [F3_28] at F4_28
  rw [F3_29] at F4_29
  obtain ⟨f5, e5, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, F5_10, F5_12⟩ := s5SchedS4_dag M f4
  rw [e5] at E
  rw [F4_6, F4_5] at h48
  rw [F4_17, F4_7] at h49
  rw [F4_5] at h50
  rw [F4_29] at h52
  rw [F4_28] at h53
  rw [F4_10] at h55
  rw [F4_12] at h56
  simp only [E]
  rw [F5_10, F5_12]
  have s0 : v0 = lo64 (w (t - 2)) := by rw [← h0]; exact hw2l
  have s1 : v1 = hi64 (w (t - 2)) := by rw [← h1]; exact hw2h
  have s2 : v2 = lo64 (w (t - 7)) := by rw [← h2]; exact hw7l
  have s3 : v3 = hi64 (w (t - 7)) := by rw [← h3]; exact hw7h
  have s10 : v10 = lo64 ((w (t - 2)).rotateRight 19) := by
    rw [← h10, ← h5, ← h4, s1, s0, lo64_rotr (r := 19) (w (t - 2)) (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s11 : v11 = hi64 ((w (t - 2)).rotateRight 19) := by
    rw [← h11, ← h6, ← h7, s1, s0, hi64_rotr (r := 19) (w (t - 2)) (by decide) (by decide)]; rfl
  have s14 : v14 = hi64 ((w (t - 2)).rotateRight 61) := by
    rw [← h14, ← h12, ← h9, s1, s0, hi64_rotr' (r := 61) (w (t - 2)) (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s15 : v15 = lo64 ((w (t - 2)).rotateRight 61) := by
    rw [← h15, ← h13, ← h8, s0, s1, lo64_rotr' (r := 61) (w (t - 2)) (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s16 : v16 = hi64 (((w (t - 2)).rotateRight 19) ^^^ ((w (t - 2)).rotateRight 61)) := by rw [← h16, s11, s14, hi64_xor ((w (t - 2)).rotateRight 19) ((w (t - 2)).rotateRight 61)]; rfl
  have s17 : v17 = lo64 (w (t - 16)) := by rw [← h17]; exact hw16l
  have s18 : v18 = hi64 (w (t - 16)) := by rw [← h18]; exact hw16h
  have s19 : v19 = lo64 (w (t - 15)) := by rw [← h19]; exact hw15l
  have s20 : v20 = hi64 (w (t - 15)) := by rw [← h20]; exact hw15h
  have s23 : v23 = lo64 (((w (t - 2)).rotateRight 61) ^^^ ((w (t - 2)).rotateRight 19)) := by rw [← h23, s15, s10, lo64_xor ((w (t - 2)).rotateRight 61) ((w (t - 2)).rotateRight 19)]; rfl
  have s24 : v24 = lo64 ((w (t - 2)) >>> 6) := by
    rw [← h24, ← h22, ← h21, s0, s1, lo64_shr (r := 6) (w (t - 2)) (by decide) (by decide)]; rfl
  have s25 : v25 = hi64 ((w (t - 2)) >>> 6) := by rw [← h25, s1, hi64_shr 6 (w (t - 2))]; rfl
  have s26 : v26 = lo64 ((((w (t - 2)).rotateRight 61) ^^^ ((w (t - 2)).rotateRight 19)) ^^^ ((w (t - 2)) >>> 6)) := by rw [← h26, s23, s24, lo64_xor (((w (t - 2)).rotateRight 61) ^^^ ((w (t - 2)).rotateRight 19)) ((w (t - 2)) >>> 6)]; rfl
  have s29 : v29 = hi64 ((((w (t - 2)).rotateRight 19) ^^^ ((w (t - 2)).rotateRight 61)) ^^^ ((w (t - 2)) >>> 6)) := by rw [← h29, s16, s25, hi64_xor (((w (t - 2)).rotateRight 19) ^^^ ((w (t - 2)).rotateRight 61)) ((w (t - 2)) >>> 6)]; rfl
  have s30 : v30 = hi64 ((w (t - 15)).rotateRight 1) := by
    rw [← h30, ← h28, ← h27, s19, s20, hi64_rotr (r := 1) (w (t - 15)) (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s33 : v33 = lo64 ((w (t - 15)).rotateRight 1) := by
    rw [← h33, ← h31, ← h32, s19, s20, lo64_rotr (r := 1) (w (t - 15)) (by decide) (by decide)]; rfl
  have s37 : v37 = lo64 ((w (t - 15)).rotateRight 8) := by
    rw [← h37, ← h35, ← h36, s19, s20, lo64_rotr (r := 8) (w (t - 15)) (by decide) (by decide)]; rfl
  have s39 : v39 = hi64 ((w (t - 15)).rotateRight 8) := by
    rw [← h39, ← h38, ← h34, s19, s20, hi64_rotr (r := 8) (w (t - 15)) (by decide) (by decide)]; exact BitVec.or_comm _ _
  have s40 : v40 = lo64 (((w (t - 15)).rotateRight 8) ^^^ ((w (t - 15)).rotateRight 1)) := by rw [← h40, s37, s33, lo64_xor ((w (t - 15)).rotateRight 8) ((w (t - 15)).rotateRight 1)]; rfl
  have s41 : v41 = hi64 (((w (t - 15)).rotateRight 1) ^^^ ((w (t - 15)).rotateRight 8)) := by rw [← h41, s30, s39, hi64_xor ((w (t - 15)).rotateRight 1) ((w (t - 15)).rotateRight 8)]; rfl
  have s44 : v44 = hi64 ((w (t - 15)) >>> 7) := by rw [← h44, s20, hi64_shr 7 (w (t - 15))]; rfl
  have s45 : v45 = lo64 ((w (t - 15)) >>> 7) := by
    rw [← h45, ← h43, ← h42, s19, s20, lo64_shr (r := 7) (w (t - 15)) (by decide) (by decide)]; rfl
  have s46 : v46 = hi64 ((((w (t - 15)).rotateRight 1) ^^^ ((w (t - 15)).rotateRight 8)) ^^^ ((w (t - 15)) >>> 7)) := by rw [← h46, s41, s44, hi64_xor (((w (t - 15)).rotateRight 1) ^^^ ((w (t - 15)).rotateRight 8)) ((w (t - 15)) >>> 7)]; rfl
  have s47 : v47 = lo64 ((((w (t - 15)).rotateRight 8) ^^^ ((w (t - 15)).rotateRight 1)) ^^^ ((w (t - 15)) >>> 7)) := by rw [← h47, s40, s45, lo64_xor (((w (t - 15)).rotateRight 8) ^^^ ((w (t - 15)).rotateRight 1)) ((w (t - 15)) >>> 7)]; rfl
  have c26 : v26 = lo64 (Sha512.smallSigma1 (w (t - 2))) := by
    rw [s26, show ((((w (t - 2)).rotateRight 61) ^^^ ((w (t - 2)).rotateRight 19)) ^^^ ((w (t - 2)) >>> 6)) = (Sha512.smallSigma1 (w (t - 2))) by unfold Sha512.smallSigma1 Sha512.rotr; ac_rfl]
  have c29 : v29 = hi64 (Sha512.smallSigma1 (w (t - 2))) := by
    rw [s29, show ((((w (t - 2)).rotateRight 19) ^^^ ((w (t - 2)).rotateRight 61)) ^^^ ((w (t - 2)) >>> 6)) = (Sha512.smallSigma1 (w (t - 2))) by unfold Sha512.smallSigma1 Sha512.rotr; ac_rfl]
  have c47 : v47 = lo64 (Sha512.smallSigma0 (w (t - 15))) := by
    rw [s47, show ((((w (t - 15)).rotateRight 8) ^^^ ((w (t - 15)).rotateRight 1)) ^^^ ((w (t - 15)) >>> 7)) = (Sha512.smallSigma0 (w (t - 15))) by unfold Sha512.smallSigma0 Sha512.rotr; ac_rfl]
  have c46 : v46 = hi64 (Sha512.smallSigma0 (w (t - 15))) := by
    rw [s46, show ((((w (t - 15)).rotateRight 1) ^^^ ((w (t - 15)).rotateRight 8)) ^^^ ((w (t - 15)) >>> 7)) = (Sha512.smallSigma0 (w (t - 15))) by unfold Sha512.smallSigma0 Sha512.rotr; ac_rfl]
  have n48 : v48.toNat = (v17.toNat + v2.toNat) % 2 ^ 32 := by rw [← h48]; exact BitVec.toNat_add _ _
  have n49 : v49.toNat = (v3.toNat + v18.toNat) % 2 ^ 32 := by rw [← h49]; exact BitVec.toNat_add _ _
  have n50 : v50.toNat = (v17.toNat + v2.toNat) / 2 ^ 32 := by
    rw [← h50, ← h48]; exact sltu_carry' _ _
  have n51 : v51.toNat = (v50.toNat + v49.toNat) % 2 ^ 32 := by rw [← h51]; exact BitVec.toNat_add _ _
  have n52 : v52.toNat = (v26.toNat + v48.toNat) % 2 ^ 32 := by rw [← h52]; exact BitVec.toNat_add _ _
  have n53 : v53.toNat = (v51.toNat + v29.toNat) % 2 ^ 32 := by rw [← h53]; exact BitVec.toNat_add _ _
  have n54 : v54.toNat = (v26.toNat + v48.toNat) / 2 ^ 32 := by
    rw [← h54, ← h52]; exact sltu_carry' _ _
  have n55 : v55.toNat = (v47.toNat + v52.toNat) % 2 ^ 32 := by rw [← h55]; exact BitVec.toNat_add _ _
  have n56 : v56.toNat = (v46.toNat + v53.toNat) % 2 ^ 32 := by rw [← h56]; exact BitVec.toNat_add _ _
  have n57 : v57.toNat = (v47.toNat + v52.toNat) / 2 ^ 32 := by
    rw [← h57, ← h55]; exact sltu_carry' _ _
  have n58 : v58.toNat = (v56.toNat + v54.toNat) % 2 ^ 32 := by rw [← h58]; exact BitVec.toNat_add _ _
  have n59 : v59.toNat = (v58.toNat + v57.toNat) % 2 ^ 32 := by rw [← h59]; exact BitVec.toNat_add _ _
  have A16 : HoldsN v17 v18.toNat (w (t - 16)) := by rw [s17, s18]; exact holdsN_atom _
  have A7 : HoldsN v2 v3.toNat (w (t - 7)) := by rw [s2, s3]; exact holdsN_atom _
  have As1 : HoldsN v26 v29.toNat (Sha512.smallSigma1 (w (t - 2))) := by rw [c26, c29]; exact holdsN_atom _
  have As0 : HoldsN v47 v46.toNat (Sha512.smallSigma0 (w (t - 15))) := by rw [c47, c46]; exact holdsN_atom _
  have R := holdsN_halves (holdsN_add' (holdsN_add' (holdsN_add A16 A7 n48 n50) As1 n52 n54) As0 n55 n57)
    (dm_add n59 (dm_add n58 (dm_add n56 (dm_leaf v46) (dm_add n53 (dm_add n51 (dm_leaf v50)
      (dm_add n49 (dm_leaf v3) (dm_leaf v18))) (dm_leaf v29))) (dm_leaf v54)) (dm_leaf v57)) (by ac_rfl)
  have e : w (t - 16) + w (t - 7) + Sha512.smallSigma1 (w (t - 2)) + Sha512.smallSigma0 (w (t - 15)) =
      Sha512.smallSigma1 (w (t - 2)) + w (t - 7) + Sha512.smallSigma0 (w (t - 15)) + w (t - 16) := by ac_rfl
  rw [e] at R
  exact ⟨R.1, R.2⟩

/-- The pass's stores and pointer steps, from 0x1E4 to 0x1EC. -/
def s5SchTail : List BInstr :=
  [.sw a1 a0 0x0, .sw a1 a2 0x4, .aluImm .add a6 a6 0xFFFFFFFF, .aluImm .add a1 a1 0x8]

/-- The loop's setup at 0x11A: the pass count and the first output slot. -/
def s5SchHead : List BInstr := [.aluImm .add a6 x0 0x40, .alu .add a1 x0 (8 : Fin 32)]

section
set_option maxRecDepth 100000
theorem s5Sched_end : blockEnd sha512CompressCode 0x124 s5Sched = some 0x1E4 := by decide
theorem s5SchTail_end : blockEnd sha512CompressCode 0x1E4 s5SchTail = some 0x1EC := by decide
theorem s5SchHead_end : blockEnd sha512CompressCode 0x11A s5SchHead = some 0x120 := by decide
end

set_option maxRecDepth 100000 in
theorem s5Sched_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f a1).toNat % 4 = 0) : BlockOk base len s5Sched (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5Sched, upd, ↓reduceIte, and_true, true_and]
  exact ⟨aligned_add h (by decide), aligned_add h (by decide), aligned_add h (by decide),
    aligned_add h (by decide), aligned_add h (by decide), aligned_add h (by decide), aligned_add h (by decide),
    aligned_add h (by decide)⟩

/-- The registers the schedule loop never writes. -/
def s5SchKeep (q : Fin 32) : Bool := q.val ∉ [0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29]

set_option maxRecDepth 100000 in
theorem s5SchKeep_dst : ∀ q, s5SchKeep q = true → q ∉ s5Sched.filterMap BInstr.dst := by decide

/-- The address of `W[s]`'s low word in the array at `F + 0xD8`. -/
def wslot (F : Word) (s : Nat) : Word := F + BitVec.ofNat 32 (0xD8 + 8 * s)

/-- `W[s]`'s halves are in its slot. -/
def WIn (M : Word → BitVec 8) (F : Word) (w : Nat → Sha512.W64) (s : Nat) : Prop :=
  memLoad32 M (wslot F s) = lo64 (w s) ∧ memLoad32 M (wslot F s + 4) = hi64 (w s)

/-- The schedule's recurrence, section 6.4.2 step 1. -/
def S5Rec (w : Nat → Sha512.W64) : Prop :=
  ∀ t, 16 ≤ t → t < 80 →
    w t = Sha512.smallSigma1 (w (t - 2)) + w (t - 7) + Sha512.smallSigma0 (w (t - 15)) + w (t - 16)

theorem addr_lo (F : Word) {a d on : Nat} (o : Word) (ho : o.toNat = on)
    (h : (a + on) % 2 ^ 32 = (0xD8 + 8 * d) % 2 ^ 32) : F + BitVec.ofNat 32 a + o = wslot F d := by
  unfold wslot
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, ho]
  omega

theorem addr_hi (F : Word) {a d on : Nat} (o : Word) (ho : o.toNat = on)
    (h : (a + on) % 2 ^ 32 = (0xD8 + 8 * d + 4) % 2 ^ 32) : F + BitVec.ofNat 32 a + o = wslot F d + 4 := by
  unfold wslot
  rw [BitVec.add_assoc, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, ho,
    show (4 : Word).toNat = 4 from rfl]
  omega

/-- What the schedule loop needs: an even `P`, and the array's last 0x200
bytes aligned and apart from the code. -/
structure S5SchS (P F : Word) : Prop where
  hP : P.toNat % 2 = 0
  hF : F.toNat % 4 = 0
  hFw : F.toNat + 0x390 ≤ 2 ^ 32
  sC : Sep (F + BitVec.ofNat 32 0x158) 0x200 P sha512CompressCode.length

/-- What holds at `off` after `j` passes: `W[0]` to `W[15 + j]` are in the
array, and memory outside `W[16]` to `W[79]` is `Mb`'s. -/
structure S5Sch (P F : Word) (w : Nat → Sha512.W64) (Mb : Word → BitVec 8) (g : Fin 32 → Word) (j off : Nat)
    (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m off (reg m)
  code : CodeIn M P sha512CompressCode
  r16 : reg m a6 = BitVec.ofNat 32 (64 - j)
  r11 : reg m a1 = F + BitVec.ofNat 32 (0x158 + 8 * j)
  win : ∀ s, s < 16 + j → WIn M F w s
  fr : ∀ x, Sep (F + BitVec.ofNat 32 0x158) 0x200 x 1 → M x = Mb x
  keep : ∀ q, s5SchKeep q = true → reg m q = g q

theorem wslot_sep {F : Word} (_hFw : F.toNat + 0x390 ≤ 2 ^ 32) {s s' : Nat} (h : s ≠ s') (hs : s < 80) (hs' : s' < 80)
    {a b : Nat} (ha : a ≤ 4) (hb : b ≤ 4) :
    Sep (wslot F s + BitVec.ofNat 32 a) 4 (wslot F s' + BitVec.ofNat 32 b) 4 := by
  unfold wslot
  rw [add_ofNat_assoc, add_ofNat_assoc]
  exact sep_offsets F (by omega) (by omega) (by omega)

theorem wslot_lohi {F : Word} (_hFw : F.toNat + 0x390 ≤ 2 ^ 32) {s : Nat} (hs : s < 80) :
    Sep (wslot F s) 4 (wslot F s + 4) 4 := by
  unfold wslot
  rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  exact sep_offsets F (by omega) (by omega) (by omega)

theorem bne_pos {k : Nat} (h0 : 0 < k) (h1 : k < 2 ^ 32) : branchTaken .bne (BitVec.ofNat 32 k) 0 = true := by
  unfold branchTaken
  rw [bne_iff_ne]
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1] at this
  exact absurd this (by show k ≠ 0; omega)

theorem ofNat_sub1 {k : Nat} (h : 0 < k) (h1 : k < 2 ^ 32) :
    aluEval .add (BitVec.ofNat 32 k) 0xFFFFFFFF = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 k + 0xFFFFFFFF).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 0xFFFFFFFF from rfl]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- One pass, from 0x124 to the branch at 0x1EC: `W[16 + j]` into its slot. -/
theorem s5_sch_body {P F : Word} {w : Nat → Sha512.W64} {Mb M : Word → BitVec 8} {g : Fin 32 → Word} {j : Nat}
    {m : Machine} (S : S5SchS P F) (hw : S5Rec w) (I : S5Sch P F w Mb g j 0x124 M m) (hj : j < 64) :
    ∃ m' M', Steps m m' ∧ S5Sch P F w Mb g (j + 1) 0x1EC M' m' := by
  have hFw := S.hFw
  have W := fun d (hd : d < 16 + j) => I.win d hd
  obtain ⟨E1, Elo, Ehi⟩ := s5Sched_run (M := M) (f := reg m) (w := w) (t := 16 + j) I.r11
    (by rw [addr_lo F (o := 0xFFFFFFF0) (on := 0xFFFFFFF0) rfl (d := 16 + j - 2) (by omega)]; exact (W _ (by omega)).1)
    (by rw [addr_hi F (o := 0xFFFFFFF4) (on := 0xFFFFFFF4) rfl (d := 16 + j - 2) (by omega)]; exact (W _ (by omega)).2)
    (by rw [addr_lo F (o := 0xFFFFFFC8) (on := 0xFFFFFFC8) rfl (d := 16 + j - 7) (by omega)]; exact (W _ (by omega)).1)
    (by rw [addr_hi F (o := 0xFFFFFFCC) (on := 0xFFFFFFCC) rfl (d := 16 + j - 7) (by omega)]; exact (W _ (by omega)).2)
    (by rw [addr_lo F (o := 0xFFFFFF80) (on := 0xFFFFFF80) rfl (d := 16 + j - 16) (by omega)]; exact (W _ (by omega)).1)
    (by rw [addr_hi F (o := 0xFFFFFF84) (on := 0xFFFFFF84) rfl (d := 16 + j - 16) (by omega)]; exact (W _ (by omega)).2)
    (by rw [addr_lo F (o := 0xFFFFFF88) (on := 0xFFFFFF88) rfl (d := 16 + j - 15) (by omega)]; exact (W _ (by omega)).1)
    (by rw [addr_hi F (o := 0xFFFFFF8C) (on := 0xFFFFFF8C) rfl (d := 16 + j - 15) (by omega)]; exact (W _ (by omega)).2)
  rw [← hw (16 + j) (by omega) (by omega)] at Elo Ehi
  obtain ⟨m1, c1, u1⟩ := St.block s5Sched I.st I.code s5Sched_end
    (s5Sched_ok (by rw [I.r11]; exact aligned_add S.hF (by omega)))
  rw [E1] at u1
  obtain ⟨f1, hf1⟩ : ∃ f1, (runBlock s5Sched (M, reg m)).2 = f1 := ⟨_, rfl⟩
  rw [hf1] at u1 Elo Ehi
  have k1 : ∀ q, q ∉ s5Sched.filterMap BInstr.dst → f1 q = reg m q := fun q hq => by
    rw [← hf1]; exact runBlock_reg _ M _ q I.st.zero hq
  have A : F + BitVec.ofNat 32 (0x158 + 8 * j) = wslot F (16 + j) := by
    unfold wslot; congr 2; omega
  have a11 : f1 a1 = wslot F (16 + j) := by rw [k1 a1 (by decide), I.r11, A]
  have a16 : f1 a6 = BitVec.ofNat 32 (64 - j) := by rw [k1 a6 (by decide), I.r16]
  have sA : Sep (wslot F (16 + j)) 4 P sha512CompressCode.length := by
    rw [← A, ← add_ofNat_assoc]; exact S.sC.sub (c := 8 * j) (by omega)
  have sA4 : Sep (wslot F (16 + j) + 4) 4 P sha512CompressCode.length := by
    rw [← A, show (4 : Word) = BitVec.ofNat 32 4 from rfl, ← add_ofNat_assoc, add_ofNat_assoc]
    exact S.sC.sub (c := 8 * j + 4) (by omega)
  have al : (wslot F (16 + j)).toNat % 4 = 0 := aligned_add S.hF (by omega)
  have al4 : (wslot F (16 + j) + 4).toNat % 4 = 0 := by
    unfold wslot; rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
    exact aligned_add S.hF (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block s5SchTail u1 I.code s5SchTail_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5SchTail, and_true]
    rw [a11, add_lit_zero]
    exact ⟨⟨al, sA⟩, al4, sA4⟩)
  simp only [runBlock, BInstr.run, s5SchTail] at u2
  rw [a11, add_lit_zero, Elo, Ehi] at u2
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 (memStore32 M (wslot F (16 + j)) (lo64 (w (16 + j)))) (wslot F (16 + j) + 4)
      (hi64 (w (16 + j))) = M2 := ⟨_, rfl⟩
  rw [hM2] at u2
  refine ⟨m2, M2, c1.trans c2, ⟨u2.self, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [← hM2]; exact (I.code.store32 sA).store32 sA4
  · rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [a16, ofNat_sub1 (by omega) (by omega)]; congr 1
  · rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [a11, ← A]; show _ + BitVec.ofNat 32 8 = _
    rw [add_ofNat_assoc]; congr 2
  · intro s hs
    by_cases h : s = 16 + j
    · subst h
      refine ⟨?_, ?_⟩
      · rw [← hM2, memLoad32_store32_sep (wslot_lohi hFw (by omega)).symm]
        exact memLoad32_store32_same _ _ _
      · rw [← hM2]; exact memLoad32_store32_same _ _ _
    · have hs' : s < 16 + j := by omega
      have e0 : Sep (wslot F s) 4 (wslot F (16 + j)) 4 := by
        have := wslot_sep hFw h (by omega) (by omega) (a := 0) (b := 0) (by omega) (by omega)
        rw [add_ofNat_zero, add_ofNat_zero] at this; exact this
      have e1 : Sep (wslot F s) 4 (wslot F (16 + j) + 4) 4 := by
        have := wslot_sep hFw h (by omega) (by omega) (a := 0) (b := 4) (by omega) (by omega)
        rw [add_ofNat_zero] at this; exact this
      have e2 : Sep (wslot F s + 4) 4 (wslot F (16 + j)) 4 := by
        have := wslot_sep hFw h (by omega) (by omega) (a := 4) (b := 0) (by omega) (by omega)
        rw [add_ofNat_zero] at this; exact this
      have e3 : Sep (wslot F s + 4) 4 (wslot F (16 + j) + 4) 4 :=
        wslot_sep hFw h (by omega) (by omega) (a := 4) (b := 4) (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · rw [← hM2, memLoad32_store32_sep e1.symm, memLoad32_store32_sep e0.symm]; exact (W s hs').1
      · rw [← hM2, memLoad32_store32_sep e3.symm, memLoad32_store32_sep e2.symm]; exact (W s hs').2
  · intro x hx
    rw [← hM2, memStore32_get_sep, memStore32_get_sep, I.fr x hx]
    · rw [← A, ← add_ofNat_assoc]; exact hx.sub (c := 8 * j) (l := 4) (by omega)
    · rw [← A, show (4 : Word) = BitVec.ofNat 32 4 from rfl, ← add_ofNat_assoc, add_ofNat_assoc]
      exact hx.sub (c := 8 * j + 4) (l := 4) (by omega)
  · intro q hq
    rw [u2.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, k1 q (s5SchKeep_dst q hq), I.keep q hq]

/-- Another pass follows: the branch at 0x1EC back to 0x124. -/
theorem s5_sch_next {P F : Word} {w : Nat → Sha512.W64} {Mb M : Word → BitVec 8} {g : Fin 32 → Word} {j : Nat}
    {m : Machine} (I : S5Sch P F w Mb g j 0x1EC M m) (hj : j < 64) :
    ∃ m', Steps m m' ∧ S5Sch P F w Mb g j 0x124 M m' := by
  obtain ⟨m1, d1, u1⟩ := I.st.taken I.code 0x124 s5_at_1ec (by decide)
    (by rw [I.r16, I.st.zero]; exact bne_pos (by omega) (by omega))
  exact ⟨m1, .cons d1 (.refl _), ⟨u1.self, I.code, by rw [u1.regs]; exact I.r16, by rw [u1.regs]; exact I.r11,
    I.win, I.fr, fun q hq => by rw [u1.regs]; exact I.keep q hq⟩⟩

/-- After the last pass: the fall-through at 0x1EC to 0x1F0. -/
theorem s5_sch_exit {P F : Word} {w : Nat → Sha512.W64} {Mb M : Word → BitVec 8} {g : Fin 32 → Word}
    {m : Machine} (I : S5Sch P F w Mb g 64 0x1EC M m) :
    ∃ m', Steps m m' ∧ S5Sch P F w Mb g 64 0x1F0 M m' := by
  obtain ⟨m1, d1, u1⟩ := I.st.notTaken I.code 0x1F0 s5_at_1ec (by decide)
    (by rw [I.r16, I.st.zero]; decide)
  exact ⟨m1, .cons d1 (.refl _), ⟨u1.self, I.code, by rw [u1.regs]; exact I.r16, by rw [u1.regs]; exact I.r11,
    I.win, I.fr, fun q hq => by rw [u1.regs]; exact I.keep q hq⟩⟩

/-- The passes from pass `j` to the loop's exit. -/
theorem s5_sch_from {P F : Word} {w : Nat → Sha512.W64} {Mb : Word → BitVec 8} {g : Fin 32 → Word}
    (S : S5SchS P F) (hw : S5Rec w) :
    ∀ k j (M : Word → BitVec 8) (m : Machine), j + k + 1 = 64 → S5Sch P F w Mb g j 0x124 M m →
      ∃ m' M', Steps m m' ∧ S5Sch P F w Mb g 64 0x1F0 M' m'
  | 0, j, M, m, h, I => by
    obtain ⟨m1, M1, c1, J⟩ := s5_sch_body S hw I (by omega)
    rw [show j + 1 = 64 by omega] at J
    obtain ⟨m2, c2, J2⟩ := s5_sch_exit J
    exact ⟨m2, M1, c1.trans c2, J2⟩
  | k + 1, j, M, m, h, I => by
    obtain ⟨m1, M1, c1, J⟩ := s5_sch_body S hw I (by omega)
    obtain ⟨m2, c2, J2⟩ := s5_sch_next J (by omega)
    obtain ⟨m3, M3, c3, J3⟩ := s5_sch_from S hw k (j + 1) M1 m2 (by omega) J2
    exact ⟨m3, M3, c1.trans (c2.trans c3), J3⟩

set_option maxRecDepth 100000 in
/-- The whole loop, from 0x11A with `W[0]` to `W[15]` in the array and the
array's end in `s0`, to 0x1F0 with all 80 words in it. -/
theorem s5_sched {P F : Word} {w : Nat → Sha512.W64} {M : Word → BitVec 8} {m : Machine}
    (S : S5SchS P F) (hw : S5Rec w) (st : St M P m 0x11A (reg m)) (code : CodeIn M P sha512CompressCode)
    (h8 : reg m 8 = F + BitVec.ofNat 32 0x158) (win : ∀ s, s < 16 → WIn M F w s) :
    ∃ m' M', Steps m m' ∧ S5Sch P F w M (reg m) 64 0x1F0 M' m' := by
  obtain ⟨m1, c1, u1⟩ := St.block s5SchHead st code s5SchHead_end (by simp [BlockOk, BInstr.ok, s5SchHead])
  simp only [runBlock, BInstr.run, s5SchHead] at u1
  obtain ⟨m2, d2, u2⟩ := u1.self.notTaken code 0x124 s5_at_120 (by decide) (by
    simp only [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [show reg m x0 = 0 from st.zero]; decide)
  have I0 : S5Sch P F w M (reg m) 0 0x124 M m2 := by
    refine ⟨u2.self, code, ?_, ?_, fun s hs => win s hs, fun _ _ => rfl, fun q hq => ?_⟩
    · simp only [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [show reg m x0 = 0 from st.zero]; rfl
    · simp only [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [h8]; exact BitVec.zero_add _
    · rw [u2.regs, u1.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl]
  obtain ⟨m3, M3, c3, I3⟩ := s5_sch_from S hw 63 0 M m2 rfl I0
  exact ⟨m3, M3, c1.trans (.cons d2 c3), I3⟩

end C3.RV32
