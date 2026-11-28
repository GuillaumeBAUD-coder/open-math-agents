import OMAStatements.S_oeis_a251271
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix over columns; the characteristic polynomial kills the state vector
-- (checked at j = 0 by decide +kernel, then by induction), giving the recurrence; closed form by
-- strong induction and the g.f. by comparing coefficients.

namespace OMA.P_oeis_a251271

open OMA.S_oeis_a251271 PowerSeries

abbrev R := Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- Compatibility of consecutive columns c, d (column sums of vertical windows do not drop). -/
def T (c d : R) : Prop :=
  c.2.1.val + c.1.val ≤ d.2.1.val + d.1.val ∧
  c.2.2.1.val + c.2.1.val ≤ d.2.2.1.val + d.2.1.val ∧
  c.2.2.2.1.val + c.2.2.1.val ≤ d.2.2.2.1.val + d.2.2.1.val ∧
  c.2.2.2.2.val + c.2.2.2.1.val ≤ d.2.2.2.2.val + d.2.2.2.1.val

instance (c d : R) : Decidable (T c d) := by unfold T; infer_instance

def enc (s : R) : ℕ := 1 * s.1.val + 2 * s.2.1.val + 4 * s.2.2.1.val + 8 * s.2.2.2.1.val + 16 * s.2.2.2.2.val

def Good (n : ℕ) (B : Fin n → R) : Prop :=
  ∀ j (h : j + 1 < n), T (B ⟨j, by omega⟩) (B ⟨j + 1, h⟩)

noncomputable instance (n : ℕ) : DecidablePred (Good n) := Classical.decPred _

def U : ℕ → R → ℕ
  | 0, _ => 1
  | j + 1, s => ∑ t, if T s t then U j t else 0

lemma Ustep (j : ℕ) (s : R) : U (j + 1) s = ∑ t, if T s t then U j t else 0 := rfl

noncomputable def cnt (m : ℕ) (s : R) : ℕ :=
  (Finset.univ.filter (fun B : Fin (m + 1) → R => Good (m + 1) B ∧ B 0 = s)).card

lemma cons0 {k : ℕ} (s : R) (C : Fin k → R) (h : 0 < k + 1) :
    (Fin.cons s C : Fin (k + 1) → R) ⟨0, h⟩ = s := Fin.cons_zero ..

lemma consS {k : ℕ} (s : R) (C : Fin k → R) (j : ℕ) (h : j + 1 < k + 1) :
    (Fin.cons s C : Fin (k + 1) → R) ⟨j + 1, h⟩ = C ⟨j, by omega⟩ := by
  show (Fin.cons s C : Fin (k + 1) → R) (Fin.succ ⟨j, by omega⟩) = _
  exact Fin.cons_succ ..

lemma good_cons (m : ℕ) (s : R) (C : Fin (m + 1) → R) :
    Good (m + 2) (Fin.cons s C : Fin (m + 2) → R) ↔ T s (C 0) ∧ Good (m + 1) C := by
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have := h 0 (by omega)
      rw [cons0, consS] at this
      exact this
    · have := h (j + 1) (by omega)
      rw [consS, consS] at this
      exact this
  · rintro ⟨h0, hg⟩ j hj
    cases j with
    | zero => rw [cons0, consS]; exact h0
    | succ j => rw [consS, consS]; exact hg j (by omega)

lemma cnt_zero (s : R) : cnt 0 s = 1 := by
  unfold cnt
  rw [Finset.card_eq_one]
  refine ⟨fun _ => s, ?_⟩
  ext B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h0⟩
    funext i
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact h0
  · rintro rfl
    exact ⟨fun j hj => by omega, rfl⟩

lemma cnt_succ (m : ℕ) (s : R) : cnt (m + 1) s = ∑ t, if T s t then cnt m t else 0 := by
  classical
  have e : cnt (m + 1) s = (Finset.univ.filter (fun C : Fin (m + 1) → R =>
      Good (m + 1) C ∧ T s (C 0))).card := by
    unfold cnt
    apply Finset.card_nbij' (fun B => Fin.tail B) (fun C => (Fin.cons s C : Fin (m + 2) → R))
    · intro B hB
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hB ⊢
      obtain ⟨hg, h0⟩ := hB
      have hc := Fin.cons_self_tail B
      rw [← hc, good_cons] at hg
      rw [h0] at hg
      exact ⟨hg.2, hg.1⟩
    · intro C hC
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hC ⊢
      exact ⟨(good_cons m s C).2 ⟨hC.2, hC.1⟩, Fin.cons_zero ..⟩
    · intro B hB
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hB
      rw [← hB.2]
      exact Fin.cons_self_tail B
    · intro C _
      exact Fin.tail_cons ..
  rw [e, Finset.card_eq_sum_card_fiberwise (f := fun C : Fin (m + 1) → R => C 0)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.filter_filter]
  split_ifs with h
  · unfold cnt
    congr 1
    apply Finset.filter_congr
    intro C _
    constructor
    · rintro ⟨⟨hg, -⟩, h0⟩; exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩; exact ⟨⟨hg, h0 ▸ h⟩, h0⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro C - ⟨⟨-, hq⟩, h0⟩
    exact h (h0 ▸ hq)

lemma cnt_eq_U (m : ℕ) (s : R) : cnt m s = U m s := by
  induction m generalizing s with
  | zero => rw [cnt_zero]; rfl
  | succ m ih => rw [cnt_succ, Ustep]; simp only [ih]

def S (m : ℕ) : ℕ := ∑ s, U m s

lemma card_good (m : ℕ) : (Finset.univ.filter (Good (m + 1))).card = S m := by
  classical
  unfold S
  simp only [← cnt_eq_U]
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := fun B : Fin (m + 1) → R => B 0)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.filter_filter]


def tr {n : ℕ} (x : Fin 5 → Fin n → Fin 2) : Fin n → R := fun j => (x 0 j, x 1 j, x 2 j, x 3 j, x 4 j)

lemma cond_iff (n : ℕ) (x : Fin 5 → Fin (n + 1) → Fin 2) :
    (∀ i i' : Fin 5, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
      ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val)) ↔
    Good (n + 1) (tr x) := by
  constructor
  · intro h j hj
    have h0 := h 0 1 rfl ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    have h1 := h 1 2 rfl ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    have h2 := h 2 3 rfl ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    have h3 := h 3 4 rfl ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (x 1 ⟨j, _⟩).val + (x 0 ⟨j, _⟩).val ≤ (x 1 ⟨j + 1, hj⟩).val + (x 0 ⟨j + 1, hj⟩).val
      omega
    · show (x 2 ⟨j, _⟩).val + (x 1 ⟨j, _⟩).val ≤ (x 2 ⟨j + 1, hj⟩).val + (x 1 ⟨j + 1, hj⟩).val
      omega
    · show (x 3 ⟨j, _⟩).val + (x 2 ⟨j, _⟩).val ≤ (x 3 ⟨j + 1, hj⟩).val + (x 2 ⟨j + 1, hj⟩).val
      omega
    · show (x 4 ⟨j, _⟩).val + (x 3 ⟨j, _⟩).val ≤ (x 4 ⟨j + 1, hj⟩).val + (x 3 ⟨j + 1, hj⟩).val
      omega
  · intro h i i' hi j j' hj
    have hlt : j.val + 1 < n + 1 := by have := j'.isLt; omega
    obtain rfl : j' = ⟨j.val + 1, hlt⟩ := Fin.ext hj
    obtain ⟨h0, h1, h2, h3⟩ := h j.val hlt
    have h0' : (x 1 j).val + (x 0 j).val ≤ (x 1 ⟨j.val + 1, hlt⟩).val + (x 0 ⟨j.val + 1, hlt⟩).val :=
      h0
    have h1' : (x 2 j).val + (x 1 j).val ≤ (x 2 ⟨j.val + 1, hlt⟩).val + (x 1 ⟨j.val + 1, hlt⟩).val :=
      h1
    have h2' : (x 3 j).val + (x 2 j).val ≤ (x 3 ⟨j.val + 1, hlt⟩).val + (x 2 ⟨j.val + 1, hlt⟩).val :=
      h2
    have h3' : (x 4 j).val + (x 3 j).val ≤ (x 4 ⟨j.val + 1, hlt⟩).val + (x 3 ⟨j.val + 1, hlt⟩).val :=
      h3
    have hi3 := i'.isLt
    rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 by omega) with e0 | e1 | e2 | e3
    · obtain rfl : i = 0 := Fin.ext (by rw [e0]; rfl)
      obtain rfl : i' = 1 := Fin.ext (by rw [hi]; rfl)
      omega
    · obtain rfl : i = 1 := Fin.ext (by rw [e1]; rfl)
      obtain rfl : i' = 2 := Fin.ext (by rw [hi]; rfl)
      omega
    · obtain rfl : i = 2 := Fin.ext (by rw [e2]; rfl)
      obtain rfl : i' = 3 := Fin.ext (by rw [hi]; rfl)
      omega
    · obtain rfl : i = 3 := Fin.ext (by rw [e3]; rfl)
      obtain rfl : i' = 4 := Fin.ext (by rw [hi]; rfl)
      omega

lemma a_eq (n : ℕ) : a n = S n := by
  classical
  rw [← card_good]
  unfold a
  apply Finset.card_nbij' (fun x => tr x) (fun B => fun i j => ![(B j).1, (B j).2.1, (B j).2.2.1, (B j).2.2.2.1, (B j).2.2.2.2] i)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    exact (cond_iff n x).1 hx
  · intro B hB
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hB ⊢
    rw [cond_iff]
    exact hB
  · intro x _
    funext i j
    fin_cases i <;> rfl
  · intro B _
    funext j
    rfl


def V0 (s : R) : ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD (enc s) 0

def V1 (s : R) : ℕ := [32, 24, 20, 8, 20, 16, 8, 4, 20, 15, 13, 5, 8, 6, 4, 2, 24, 18, 15, 6, 16, 13, 6, 3, 8, 6, 5, 2, 4, 3, 2, 1].getD (enc s) 0

def V2 (s : R) : ℕ := [337, 205, 142, 31, 141, 93, 30, 10, 142, 86, 65, 13, 30, 18, 9, 3, 205, 125, 86, 19, 93, 65, 18, 6, 31, 19, 13, 3, 10, 6, 3, 1].getD (enc s) 0

def V3 (s : R) : ℕ := [2058, 1069, 634, 86, 630, 356, 80, 20, 634, 328, 223, 26, 80, 40, 16, 4, 1069, 558, 328, 45, 356, 223, 40, 10, 86, 45, 26, 4, 20, 10, 4, 1].getD (enc s) 0

def V4 (s : R) : ℕ := [9109, 4176, 2176, 196, 2169, 1083, 175, 35, 2176, 1000, 627, 45, 175, 75, 25, 5, 4176, 1931, 1000, 90, 1083, 627, 75, 15, 196, 90, 45, 5, 35, 15, 5, 1].getD (enc s) 0

def V5 (s : R) : ℕ := [32636, 13517, 6320, 392, 6320, 2858, 336, 56, 6320, 2655, 1565, 71, 336, 126, 36, 6, 13517, 5676, 2655, 161, 2858, 1565, 126, 21, 392, 161, 71, 6, 56, 21, 6, 1].getD (enc s) 0

def V6 (s : R) : ℕ := [100843, 38408, 16399, 714, 16441, 6871, 588, 84, 16399, 6437, 3621, 105, 588, 196, 49, 7, 38408, 14929, 6437, 266, 6871, 3621, 196, 28, 714, 266, 105, 7, 84, 28, 7, 1].getD (enc s) 0

def V7 (s : R) : ℕ := [279718, 99370, 39330, 1212, 39498, 15514, 960, 120, 39330, 14674, 7971, 148, 960, 288, 64, 8, 99370, 36306, 14674, 414, 15514, 7971, 288, 36, 1212, 414, 148, 8, 120, 36, 8, 1].getD (enc s) 0

def V8 (s : R) : ℕ := [715685, 239963, 89199, 1947, 89661, 33569, 1485, 165, 89199, 32063, 16975, 201, 1485, 405, 81, 9, 239963, 83457, 32063, 615, 33569, 16975, 405, 45, 1947, 615, 201, 9, 165, 45, 9, 1].getD (enc s) 0

def V9 (s : R) : ℕ := [1722176, 550502, 194404, 2992, 195460, 70580, 2200, 220, 194404, 68039, 35361, 265, 2200, 550, 100, 10, 550502, 184174, 68039, 880, 70580, 35361, 550, 55, 2992, 880, 265, 10, 220, 55, 10, 1].getD (enc s) 0

def V10 (s : R) : ℕ := [3954037, 1215503, 411908, 4433, 414053, 145593, 3146, 286, 411908, 141512, 72593, 341, 3146, 726, 121, 11, 1215503, 394605, 141512, 1221, 145593, 72593, 726, 66, 4433, 1221, 341, 11, 286, 66, 11, 1].getD (enc s) 0

lemma U0 : U 0 = V0 := by
  funext s
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U1 : U 1 = V1 := by
  funext s
  rw [Ustep, U0]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U2 : U 2 = V2 := by
  funext s
  rw [Ustep, U1]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U3 : U 3 = V3 := by
  funext s
  rw [Ustep, U2]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U4 : U 4 = V4 := by
  funext s
  rw [Ustep, U3]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U5 : U 5 = V5 := by
  funext s
  rw [Ustep, U4]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U6 : U 6 = V6 := by
  funext s
  rw [Ustep, U5]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U7 : U 7 = V7 := by
  funext s
  rw [Ustep, U6]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U8 : U 8 = V8 := by
  funext s
  rw [Ustep, U7]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U9 : U 9 = V9 := by
  funext s
  rw [Ustep, U8]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma U10 : U 10 = V10 := by
  funext s
  rw [Ustep, U9]
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
lemma rel0 : ∀ s : R, U 10 s + 54 * U 8 s + 294 * U 6 s + 336 * U 4 s + 81 * U 2 s + 2 * U 0 s =
    11 * U 9 s + 156 * U 7 s + 378 * U 5 s + 204 * U 3 s + 19 * U 1 s := by
  intro s
  simp only [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10]
  revert s
  decide +kernel

lemma rel (j : ℕ) : ∀ s : R, U (j + 10) s + 54 * U (j + 8) s + 294 * U (j + 6) s + 336 * U (j + 4) s + 81 * U (j + 2) s + 2 * U j s =
    11 * U (j + 9) s + 156 * U (j + 7) s + 378 * U (j + 5) s + 204 * U (j + 3) s + 19 * U (j + 1) s := by
  induction j with
  | zero => exact rel0
  | succ j ih =>
    intro s
    rw [show j + 1 + 1 = (j + 1) + 1 by omega, show j + 1 + 2 = (j + 2) + 1 by omega, show j + 1 + 3 = (j + 3) + 1 by omega, show j + 1 + 4 = (j + 4) + 1 by omega, show j + 1 + 5 = (j + 5) + 1 by omega, show j + 1 + 6 = (j + 6) + 1 by omega, show j + 1 + 7 = (j + 7) + 1 by omega, show j + 1 + 8 = (j + 8) + 1 by omega, show j + 1 + 9 = (j + 9) + 1 by omega, show j + 1 + 10 = (j + 10) + 1 by omega]
    rw [Ustep (j + 10) s, Ustep (j + 9) s, Ustep (j + 8) s, Ustep (j + 7) s, Ustep (j + 6) s, Ustep (j + 5) s, Ustep (j + 4) s, Ustep (j + 3) s, Ustep (j + 2) s, Ustep (j + 1) s, Ustep j s]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs
    · exact ih t
    · simp

lemma Srec (m : ℕ) : S (m + 10) + 54 * S (m + 8) + 294 * S (m + 6) + 336 * S (m + 4) + 81 * S (m + 2) + 2 * S m =
    11 * S (m + 9) + 156 * S (m + 7) + 378 * S (m + 5) + 204 * S (m + 3) + 19 * S (m + 1) := by
  simp only [S, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => rel m s)

set_option maxRecDepth 100000 in
lemma S0 : S 0 = 32 := by
  rw [S, U0]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S1 : S 1 = 337 := by
  rw [S, U1]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S2 : S 2 = 2058 := by
  rw [S, U2]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S3 : S 3 = 9109 := by
  rw [S, U3]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S4 : S 4 = 32636 := by
  rw [S, U4]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S5 : S 5 = 100843 := by
  rw [S, U5]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S6 : S 6 = 279718 := by
  rw [S, U6]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S7 : S 7 = 715685 := by
  rw [S, U7]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S8 : S 8 = 1722176 := by
  rw [S, U8]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S9 : S 9 = 3954037 := by
  rw [S, U9]
  decide +kernel

lemma closed (m : ℕ) : (S m : ℚ) =
    (20160 * (1369 * 2 ^ m - 1365) - 18907464 * m - 6363848 * m ^ 2 - 1352064 * m ^ 3 -
            190036 * m ^ 4 - 16401 * m ^ 5 - 637 * m ^ 6 + 9 * m ^ 7 + m ^ 8) / 2520 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases (show m < 10 ∨ 10 ≤ m by omega) with h | h
    · interval_cases m <;> simp [S0, S1, S2, S3, S4, S5, S6, S7, S8, S9] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 10 := ⟨m - 10, by omega⟩
      have r' : (S (k + 10) : ℚ) + 54 * S (k + 8) + 294 * S (k + 6) + 336 * S (k + 4) + 81 * S (k + 2) + 2 * S k =
    11 * S (k + 9) + 156 * S (k + 7) + 378 * S (k + 5) + 204 * S (k + 3) + 19 * S (k + 1) := by exact_mod_cast Srec k
      rw [ih k (by omega), ih (k + 1) (by omega), ih (k + 2) (by omega), ih (k + 3) (by omega), ih (k + 4) (by omega), ih (k + 5) (by omega), ih (k + 6) (by omega), ih (k + 7) (by omega), ih (k + 8) (by omega), ih (k + 9) (by omega)] at r'
      push_cast at r' ⊢
      linear_combination r'

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]


end OMA.P_oeis_a251271

open OMA.S_oeis_a251271 OMA.P_oeis_a251271 PowerSeries

set_option maxRecDepth 100000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a251271.main := by
  have hcl : ∀ n : ℕ, (a n : ℚ) =
      (20160 * (1369 * 2 ^ n - 1365) - 18907464 * n - 6363848 * n ^ 2 - 1352064 * n ^ 3 -
            190036 * n ^ 4 - 16401 * n ^ 5 - 637 * n ^ 6 + 9 * n ^ 7 + n ^ 8) / 2520 := fun n => by
    rw [a_eq]; exact closed n
  have hrec : ∀ n : ℕ, 11 ≤ n → (a n : ℚ) = 11 * a (n - 1) - 54 * a (n - 2) + 156 * a (n - 3) - 294 * a (n - 4) + 378 * a (n - 5) - 336 * a (n - 6) + 204 * a (n - 7) - 81 * a (n - 8) + 19 * a (n - 9) - 2 * a (n - 10) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    rw [show k + 11 - 1 = k + 10 by omega, show k + 11 - 2 = k + 9 by omega, show k + 11 - 3 = k + 8 by omega, show k + 11 - 4 = k + 7 by omega, show k + 11 - 5 = k + 6 by omega, show k + 11 - 6 = k + 5 by omega, show k + 11 - 7 = k + 4 by omega, show k + 11 - 8 = k + 3 by omega, show k + 11 - 9 = k + 2 by omega, show k + 11 - 10 = k + 1 by omega, show k + 11 = k + 1 + 10 by omega]
    simp only [a_eq]
    have h' : (S (k + 1 + 10) : ℚ) + 54 * S (k + 1 + 8) + 294 * S (k + 1 + 6) + 336 * S (k + 1 + 4) + 81 * S (k + 1 + 2) + 2 * S (k + 1) =
    11 * S (k + 1 + 9) + 156 * S (k + 1 + 7) + 378 * S (k + 1 + 5) + 204 * S (k + 1 + 3) + 19 * S (k + 1 + 1) := by exact_mod_cast Srec (k + 1)
    simp only [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega, show k + 1 + 3 = k + 4 by omega, show k + 1 + 4 = k + 5 by omega, show k + 1 + 5 = k + 6 by omega, show k + 1 + 6 = k + 7 by omega, show k + 1 + 7 = k + 8 by omega, show k + 1 + 8 = k + 9 by omega, show k + 1 + 9 = k + 10 by omega] at h'
    linear_combination h'
  refine ⟨?_, fun n _ => hcl n⟩
  rw [show ((1 - X) ^ 9 * (1 - 2 * X) : PowerSeries ℚ) = 1 - C (11:ℚ) * X + C (54:ℚ) * X ^ 2 - C (156:ℚ) * X ^ 3 + C (294:ℚ) * X ^ 4 - C (378:ℚ) * X ^ 5 + C (336:ℚ) * X ^ 6 - C (204:ℚ) * X ^ 7 + C (81:ℚ) * X ^ 8 - C (19:ℚ) * X ^ 9 + C (2:ℚ) * X ^ 10 by
      simp only [map_ofNat]; ring,
    show (X * (337 - 1649 * X + 4669 * X ^ 2 - 9003 * X ^ 3 + 11763 * X ^ 4 - 10549 * X ^ 5 +
          6447 * X ^ 6 - 2573 * X ^ 7 + 606 * X ^ 8 - 64 * X ^ 9) : PowerSeries ℚ) =
      C (337:ℚ) * X - C (1649:ℚ) * X ^ 2 + C (4669:ℚ) * X ^ 3 - C (9003:ℚ) * X ^ 4 + C (11763:ℚ) * X ^ 5 - C (10549:ℚ) * X ^ 6 + C (6447:ℚ) * X ^ 7 - C (2573:ℚ) * X ^ 8 + C (606:ℚ) * X ^ 9 - C (64:ℚ) * X ^ 10 by
      simp only [map_ofNat]; ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
    PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  have v1 : (a 1 : ℚ) = 337 := by rw [hcl]; norm_num
  have v2 : (a 2 : ℚ) = 2058 := by rw [hcl]; norm_num
  have v3 : (a 3 : ℚ) = 9109 := by rw [hcl]; norm_num
  have v4 : (a 4 : ℚ) = 32636 := by rw [hcl]; norm_num
  have v5 : (a 5 : ℚ) = 100843 := by rw [hcl]; norm_num
  have v6 : (a 6 : ℚ) = 279718 := by rw [hcl]; norm_num
  have v7 : (a 7 : ℚ) = 715685 := by rw [hcl]; norm_num
  have v8 : (a 8 : ℚ) = 1722176 := by rw [hcl]; norm_num
  have v9 : (a 9 : ℚ) = 3954037 := by rw [hcl]; norm_num
  have v10 : (a 10 : ℚ) = 8757506 := by rw [hcl]; norm_num
  rcases (show n ≤ 10 ∨ 11 ≤ n by omega) with h | h
  · interval_cases n <;> simp only [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · have hq := hrec n h
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega, show n - 8 ≠ 0 by omega, show n - 9 ≠ 0 by omega, show n - 10 ≠ 0 by omega]
    rw [hq]; ring


