import OMAStatements.S_oeis_a063043
import Mathlib

open OMA.S_oeis_a063043

namespace P063043

theorem pneg (k : ℕ) (h : ¬ (k + 1).Prime) : primeAtMost (k + 1) = primeAtMost k := by
  simp [primeAtMost, h]

theorem ppos (k : ℕ) (h : (k + 1).Prime) : primeAtMost (k + 1) = k + 1 := by
  simp [primeAtMost, h]

theorem st3 : step 3 = 7 := by
  unfold step
  rw [if_pos (by norm_num), show 3 - 1 = 2 by norm_num, ppos 1 (by norm_num)]

theorem st7 : step 7 = 36 := by
  unfold step
  rw [if_pos (by norm_num), show 7 - 1 = 6 by norm_num, pneg 5 (by norm_num), ppos 4 (by norm_num)]

theorem st9 : step 9 = 3 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 9 = 3 by norm_num]

theorem st17 : step 17 = 222 := by
  unfold step
  rw [if_pos (by norm_num), show 17 - 1 = 16 by norm_num, pneg 15 (by norm_num), pneg 14 (by norm_num), pneg 13 (by norm_num), ppos 12 (by norm_num)]

theorem st18 : step 18 = 9 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 18 = 2 by norm_num]

theorem st23 : step 23 = 438 := by
  unfold step
  rw [if_pos (by norm_num), show 23 - 1 = 22 by norm_num, pneg 21 (by norm_num), pneg 20 (by norm_num), pneg 19 (by norm_num), ppos 18 (by norm_num)]

theorem st27 : step 27 = 9 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 27 = 3 by norm_num]

theorem st29 : step 29 = 668 := by
  unfold step
  rw [if_pos (by norm_num), show 29 - 1 = 28 by norm_num, pneg 27 (by norm_num), pneg 26 (by norm_num), pneg 25 (by norm_num), pneg 24 (by norm_num), pneg 23 (by norm_num), ppos 22 (by norm_num)]

theorem st36 : step 36 = 18 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 36 = 2 by norm_num]

theorem st37 : step 37 = 1148 := by
  unfold step
  rw [if_pos (by norm_num), show 37 - 1 = 36 by norm_num, pneg 35 (by norm_num), pneg 34 (by norm_num), pneg 33 (by norm_num), pneg 32 (by norm_num), pneg 31 (by norm_num), ppos 30 (by norm_num)]

theorem st41 : step 41 = 1518 := by
  unfold step
  rw [if_pos (by norm_num), show 41 - 1 = 40 by norm_num, pneg 39 (by norm_num), pneg 38 (by norm_num), pneg 37 (by norm_num), ppos 36 (by norm_num)]

theorem st73 : step 73 = 5184 := by
  unfold step
  rw [if_pos (by norm_num), show 73 - 1 = 72 by norm_num, pneg 71 (by norm_num), ppos 70 (by norm_num)]

theorem st81 : step 81 = 27 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 81 = 3 by norm_num]

theorem st111 : step 111 = 37 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 111 = 3 by norm_num]

theorem st162 : step 162 = 81 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 162 = 2 by norm_num]

theorem st167 : step 167 = 27222 := by
  unfold step
  rw [if_pos (by norm_num), show 167 - 1 = 166 by norm_num, pneg 165 (by norm_num), pneg 164 (by norm_num), pneg 163 (by norm_num), ppos 162 (by norm_num)]

theorem st219 : step 219 = 73 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 219 = 3 by norm_num]

theorem st222 : step 222 = 111 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 222 = 2 by norm_num]

theorem st253 : step 253 = 23 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 253 = 11 by norm_num]

theorem st287 : step 287 = 41 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 287 = 7 by norm_num]

theorem st324 : step 324 = 162 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 324 = 2 by norm_num]

theorem st334 : step 334 = 167 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 334 = 2 by norm_num]

theorem st349 : step 349 = 121104 := by
  unfold step
  rw [if_pos (by norm_num), show 349 - 1 = 348 by norm_num, pneg 347 (by norm_num), ppos 346 (by norm_num)]

theorem st438 : step 438 = 219 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 438 = 2 by norm_num]

theorem st574 : step 574 = 287 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 574 = 2 by norm_num]

theorem st648 : step 648 = 324 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 648 = 2 by norm_num]

theorem st668 : step 668 = 334 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 668 = 2 by norm_num]

theorem st759 : step 759 = 253 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 759 = 3 by norm_num]

theorem st841 : step 841 = 29 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 841 = 29 by norm_num]

theorem st1148 : step 1148 = 574 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 1148 = 2 by norm_num]

theorem st1296 : step 1296 = 648 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 1296 = 2 by norm_num]

theorem st1518 : step 1518 = 759 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 1518 = 2 by norm_num]

theorem st2523 : step 2523 = 841 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 2523 = 3 by norm_num]

theorem st2592 : step 2592 = 1296 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 2592 = 2 by norm_num]

theorem st4537 : step 4537 = 349 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 4537 = 13 by norm_num]

theorem st5184 : step 5184 = 2592 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 5184 = 2 by norm_num]

theorem st7569 : step 7569 = 2523 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 7569 = 3 by norm_num]

theorem st13611 : step 13611 = 4537 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 13611 = 3 by norm_num]

theorem st15138 : step 15138 = 7569 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 15138 = 2 by norm_num]

theorem st27222 : step 27222 = 13611 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 27222 = 2 by norm_num]

theorem st30276 : step 30276 = 15138 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 30276 = 2 by norm_num]

theorem st60552 : step 60552 = 30276 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 60552 = 2 by norm_num]

theorem st121104 : step 121104 = 60552 := by
  unfold step
  rw [if_neg (by norm_num), show Nat.minFac 121104 = 2 by norm_num]

theorem a0 : orbit 17 0 = 17 := rfl
theorem a1 : orbit 17 1 = 222 := by
  show step (orbit 17 0) = _
  rw [a0, st17]
theorem a2 : orbit 17 2 = 111 := by
  show step (orbit 17 1) = _
  rw [a1, st222]
theorem a3 : orbit 17 3 = 37 := by
  show step (orbit 17 2) = _
  rw [a2, st111]
theorem a4 : orbit 17 4 = 1148 := by
  show step (orbit 17 3) = _
  rw [a3, st37]
theorem a5 : orbit 17 5 = 574 := by
  show step (orbit 17 4) = _
  rw [a4, st1148]
theorem a6 : orbit 17 6 = 287 := by
  show step (orbit 17 5) = _
  rw [a5, st574]
theorem a7 : orbit 17 7 = 41 := by
  show step (orbit 17 6) = _
  rw [a6, st287]
theorem a8 : orbit 17 8 = 1518 := by
  show step (orbit 17 7) = _
  rw [a7, st41]
theorem a9 : orbit 17 9 = 759 := by
  show step (orbit 17 8) = _
  rw [a8, st1518]
theorem a10 : orbit 17 10 = 253 := by
  show step (orbit 17 9) = _
  rw [a9, st759]
theorem a11 : orbit 17 11 = 23 := by
  show step (orbit 17 10) = _
  rw [a10, st253]
theorem a12 : orbit 17 12 = 438 := by
  show step (orbit 17 11) = _
  rw [a11, st23]
theorem a13 : orbit 17 13 = 219 := by
  show step (orbit 17 12) = _
  rw [a12, st438]
theorem a14 : orbit 17 14 = 73 := by
  show step (orbit 17 13) = _
  rw [a13, st219]
theorem a15 : orbit 17 15 = 5184 := by
  show step (orbit 17 14) = _
  rw [a14, st73]
theorem a16 : orbit 17 16 = 2592 := by
  show step (orbit 17 15) = _
  rw [a15, st5184]
theorem a17 : orbit 17 17 = 1296 := by
  show step (orbit 17 16) = _
  rw [a16, st2592]
theorem a18 : orbit 17 18 = 648 := by
  show step (orbit 17 17) = _
  rw [a17, st1296]
theorem a19 : orbit 17 19 = 324 := by
  show step (orbit 17 18) = _
  rw [a18, st648]
theorem a20 : orbit 17 20 = 162 := by
  show step (orbit 17 19) = _
  rw [a19, st324]
theorem a21 : orbit 17 21 = 81 := by
  show step (orbit 17 20) = _
  rw [a20, st162]
theorem a22 : orbit 17 22 = 27 := by
  show step (orbit 17 21) = _
  rw [a21, st81]
theorem a23 : orbit 17 23 = 9 := by
  show step (orbit 17 22) = _
  rw [a22, st27]
theorem a24 : orbit 17 24 = 3 := by
  show step (orbit 17 23) = _
  rw [a23, st9]
theorem a25 : orbit 17 25 = 7 := by
  show step (orbit 17 24) = _
  rw [a24, st3]
theorem a26 : orbit 17 26 = 36 := by
  show step (orbit 17 25) = _
  rw [a25, st7]
theorem a27 : orbit 17 27 = 18 := by
  show step (orbit 17 26) = _
  rw [a26, st36]
theorem a28 : orbit 17 28 = 9 := by
  show step (orbit 17 27) = _
  rw [a27, st18]
theorem b0 : orbit 29 0 = 29 := rfl
theorem b1 : orbit 29 1 = 668 := by
  show step (orbit 29 0) = _
  rw [b0, st29]
theorem b2 : orbit 29 2 = 334 := by
  show step (orbit 29 1) = _
  rw [b1, st668]
theorem b3 : orbit 29 3 = 167 := by
  show step (orbit 29 2) = _
  rw [b2, st334]
theorem b4 : orbit 29 4 = 27222 := by
  show step (orbit 29 3) = _
  rw [b3, st167]
theorem b5 : orbit 29 5 = 13611 := by
  show step (orbit 29 4) = _
  rw [b4, st27222]
theorem b6 : orbit 29 6 = 4537 := by
  show step (orbit 29 5) = _
  rw [b5, st13611]
theorem b7 : orbit 29 7 = 349 := by
  show step (orbit 29 6) = _
  rw [b6, st4537]
theorem b8 : orbit 29 8 = 121104 := by
  show step (orbit 29 7) = _
  rw [b7, st349]
theorem b9 : orbit 29 9 = 60552 := by
  show step (orbit 29 8) = _
  rw [b8, st121104]
theorem b10 : orbit 29 10 = 30276 := by
  show step (orbit 29 9) = _
  rw [b9, st60552]
theorem b11 : orbit 29 11 = 15138 := by
  show step (orbit 29 10) = _
  rw [b10, st30276]
theorem b12 : orbit 29 12 = 7569 := by
  show step (orbit 29 11) = _
  rw [b11, st15138]
theorem b13 : orbit 29 13 = 2523 := by
  show step (orbit 29 12) = _
  rw [b12, st7569]
theorem b14 : orbit 29 14 = 841 := by
  show step (orbit 29 13) = _
  rw [b13, st2523]
theorem b15 : orbit 29 15 = 29 := by
  show step (orbit 29 14) = _
  rw [b14, st841]
theorem c0 : orbit 3 0 = 3 := rfl
theorem c1 : orbit 3 1 = 7 := by
  show step (orbit 3 0) = _
  rw [c0, st3]
theorem c2 : orbit 3 2 = 36 := by
  show step (orbit 3 1) = _
  rw [c1, st7]
theorem c3 : orbit 3 3 = 18 := by
  show step (orbit 3 2) = _
  rw [c2, st36]
theorem c4 : orbit 3 4 = 9 := by
  show step (orbit 3 3) = _
  rw [c3, st18]
theorem c5 : orbit 3 5 = 3 := by
  show step (orbit 3 4) = _
  rw [c4, st9]

def L17 : List ℕ := [17, 222, 111, 37, 1148, 574, 287, 41, 1518, 759, 253, 23, 438, 219, 73, 5184, 2592, 1296, 648, 324, 162, 81, 27, 9, 3, 7, 36, 18]

theorem hL (i : Fin 28) : orbit 17 i = L17.getD i 0 := by
  fin_cases i <;> simp only [Fin.val_mk] <;> first | (rw [a0]; rfl) | (rw [a1]; rfl) | (rw [a2]; rfl) | (rw [a3]; rfl) | (rw [a4]; rfl) | (rw [a5]; rfl) | (rw [a6]; rfl) | (rw [a7]; rfl) | (rw [a8]; rfl) | (rw [a9]; rfl) | (rw [a10]; rfl) | (rw [a11]; rfl) | (rw [a12]; rfl) | (rw [a13]; rfl) | (rw [a14]; rfl) | (rw [a15]; rfl) | (rw [a16]; rfl) | (rw [a17]; rfl) | (rw [a18]; rfl) | (rw [a19]; rfl) | (rw [a20]; rfl) | (rw [a21]; rfl) | (rw [a22]; rfl) | (rw [a23]; rfl) | (rw [a24]; rfl) | (rw [a25]; rfl) | (rw [a26]; rfl) | (rw [a27]; rfl)

theorem nodupL : ∀ i j : Fin 28, L17.getD i 0 = L17.getD j 0 ↔ i = j := by decide

end P063043

theorem OMA.solution : type_of% @OMA.S_oeis_a063043.main := by
  refine ⟨⟨P063043.a23, P063043.a28⟩, ?_, ⟨?_, P063043.c5⟩, ?_⟩
  · intro i j
    rw [P063043.hL, P063043.hL]
    exact P063043.nodupL i j
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
      List.map_nil, P063043.c0, P063043.c1, P063043.c2, P063043.c3, P063043.c4]
    rfl
  · intro h
    have := h 29 (by norm_num) ⟨15, by norm_num, P063043.b15⟩
    simp [cycleOfThree] at this
