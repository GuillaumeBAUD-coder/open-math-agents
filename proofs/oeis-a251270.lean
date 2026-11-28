import OMAStatements.S_oeis_a251270
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix over columns; the characteristic polynomial kills the state vector
-- (checked at j = 0 by decide +kernel, then by induction), giving the recurrence; closed form by
-- strong induction and the g.f. by comparing coefficients.

namespace OMA.P_oeis_a251270

open OMA.S_oeis_a251270 PowerSeries

abbrev R := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- Compatibility of consecutive columns c, d (column sums of vertical windows do not drop). -/
def T (c d : R) : Prop :=
  c.2.1.val + c.1.val ≤ d.2.1.val + d.1.val ∧
  c.2.2.1.val + c.2.1.val ≤ d.2.2.1.val + d.2.1.val ∧
  c.2.2.2.val + c.2.2.1.val ≤ d.2.2.2.val + d.2.2.1.val

instance (c d : R) : Decidable (T c d) := by unfold T; infer_instance

def enc (s : R) : ℕ := 1 * s.1.val + 2 * s.2.1.val + 4 * s.2.2.1.val + 8 * s.2.2.2.val

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


def tr {n : ℕ} (x : Fin 4 → Fin n → Fin 2) : Fin n → R := fun j => (x 0 j, x 1 j, x 2 j, x 3 j)

lemma cond_iff (n : ℕ) (x : Fin 4 → Fin (n + 1) → Fin 2) :
    (∀ i i' : Fin 4, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
      ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val)) ↔
    Good (n + 1) (tr x) := by
  constructor
  · intro h j hj
    have h0 := h 0 1 rfl ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    have h1 := h 1 2 rfl ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    have h2 := h 2 3 rfl ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    refine ⟨?_, ?_, ?_⟩
    · show (x 1 ⟨j, _⟩).val + (x 0 ⟨j, _⟩).val ≤ (x 1 ⟨j + 1, hj⟩).val + (x 0 ⟨j + 1, hj⟩).val
      omega
    · show (x 2 ⟨j, _⟩).val + (x 1 ⟨j, _⟩).val ≤ (x 2 ⟨j + 1, hj⟩).val + (x 1 ⟨j + 1, hj⟩).val
      omega
    · show (x 3 ⟨j, _⟩).val + (x 2 ⟨j, _⟩).val ≤ (x 3 ⟨j + 1, hj⟩).val + (x 2 ⟨j + 1, hj⟩).val
      omega
  · intro h i i' hi j j' hj
    have hlt : j.val + 1 < n + 1 := by have := j'.isLt; omega
    obtain rfl : j' = ⟨j.val + 1, hlt⟩ := Fin.ext hj
    obtain ⟨h0, h1, h2⟩ := h j.val hlt
    have h0' : (x 1 j).val + (x 0 j).val ≤ (x 1 ⟨j.val + 1, hlt⟩).val + (x 0 ⟨j.val + 1, hlt⟩).val :=
      h0
    have h1' : (x 2 j).val + (x 1 j).val ≤ (x 2 ⟨j.val + 1, hlt⟩).val + (x 1 ⟨j.val + 1, hlt⟩).val :=
      h1
    have h2' : (x 3 j).val + (x 2 j).val ≤ (x 3 ⟨j.val + 1, hlt⟩).val + (x 2 ⟨j.val + 1, hlt⟩).val :=
      h2
    have hi3 := i'.isLt
    rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with e0 | e1 | e2
    · obtain rfl : i = 0 := Fin.ext (by rw [e0]; rfl)
      obtain rfl : i' = 1 := Fin.ext (by rw [hi]; rfl)
      omega
    · obtain rfl : i = 1 := Fin.ext (by rw [e1]; rfl)
      obtain rfl : i' = 2 := Fin.ext (by rw [hi]; rfl)
      omega
    · obtain rfl : i = 2 := Fin.ext (by rw [e2]; rfl)
      obtain rfl : i' = 3 := Fin.ext (by rw [hi]; rfl)
      omega

lemma a_eq (n : ℕ) : a n = S n := by
  classical
  rw [← card_good]
  unfold a
  apply Finset.card_nbij' (fun x => tr x) (fun B => fun i j => ![(B j).1, (B j).2.1, (B j).2.2.1, (B j).2.2.2] i)
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


def V0 (s : R) : ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD (enc s) 0

def V1 (s : R) : ℕ := [16, 12, 10, 4, 10, 8, 4, 2, 12, 9, 8, 3, 4, 3, 2, 1].getD (enc s) 0

def V2 (s : R) : ℕ := [108, 66, 45, 10, 45, 31, 9, 3, 66, 40, 31, 6, 10, 6, 3, 1].getD (enc s) 0

def V3 (s : R) : ℕ := [480, 251, 145, 20, 145, 90, 16, 4, 251, 130, 90, 10, 20, 10, 4, 1].getD (enc s) 0

def V4 (s : R) : ℕ := [1667, 771, 390, 35, 390, 225, 25, 5, 771, 355, 225, 15, 35, 15, 5, 1].getD (enc s) 0

def V5 (s : R) : ℕ := [4930, 2067, 941, 56, 941, 516, 36, 6, 2067, 871, 516, 21, 56, 21, 6, 1].getD (enc s) 0

def V6 (s : R) : ℕ := [13052, 5058, 2120, 84, 2120, 1123, 49, 7, 5058, 1994, 1123, 28, 84, 28, 7, 1].getD (enc s) 0

def V7 (s : R) : ℕ := [31936, 11622, 4570, 120, 4570, 2366, 64, 8, 11622, 4360, 2366, 36, 120, 36, 8, 1].getD (enc s) 0

def V8 (s : R) : ℕ := [73805, 25557, 9575, 165, 9575, 4885, 81, 9, 25557, 9245, 4885, 45, 165, 45, 9, 1].getD (enc s) 0

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
lemma rel0 : ∀ s : R, U 8 s + 35 * U 6 s + 105 * U 4 s + 49 * U 2 s + 2 * U 0 s =
    9 * U 7 s + 77 * U 5 s + 91 * U 3 s + 15 * U 1 s := by
  intro s
  simp only [U0, U1, U2, U3, U4, U5, U6, U7, U8]
  revert s
  decide +kernel

lemma rel (j : ℕ) : ∀ s : R, U (j + 8) s + 35 * U (j + 6) s + 105 * U (j + 4) s + 49 * U (j + 2) s + 2 * U j s =
    9 * U (j + 7) s + 77 * U (j + 5) s + 91 * U (j + 3) s + 15 * U (j + 1) s := by
  induction j with
  | zero => exact rel0
  | succ j ih =>
    intro s
    rw [show j + 1 + 1 = (j + 1) + 1 by omega, show j + 1 + 2 = (j + 2) + 1 by omega, show j + 1 + 3 = (j + 3) + 1 by omega, show j + 1 + 4 = (j + 4) + 1 by omega, show j + 1 + 5 = (j + 5) + 1 by omega, show j + 1 + 6 = (j + 6) + 1 by omega, show j + 1 + 7 = (j + 7) + 1 by omega, show j + 1 + 8 = (j + 8) + 1 by omega]
    rw [Ustep (j + 8) s, Ustep (j + 7) s, Ustep (j + 6) s, Ustep (j + 5) s, Ustep (j + 4) s, Ustep (j + 3) s, Ustep (j + 2) s, Ustep (j + 1) s, Ustep j s]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs
    · exact ih t
    · simp

lemma Srec (m : ℕ) : S (m + 8) + 35 * S (m + 6) + 105 * S (m + 4) + 49 * S (m + 2) + 2 * S m =
    9 * S (m + 7) + 77 * S (m + 5) + 91 * S (m + 3) + 15 * S (m + 1) := by
  simp only [S, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => rel m s)

set_option maxRecDepth 100000 in
lemma S0 : S 0 = 16 := by
  rw [S, U0]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S1 : S 1 = 108 := by
  rw [S, U1]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S2 : S 2 = 480 := by
  rw [S, U2]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S3 : S 3 = 1667 := by
  rw [S, U3]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S4 : S 4 = 4930 := by
  rw [S, U4]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S5 : S 5 = 13052 := by
  rw [S, U5]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S6 : S 6 = 31936 := by
  rw [S, U6]
  decide +kernel

set_option maxRecDepth 100000 in
lemma S7 : S 7 = 73805 := by
  rw [S, U7]
  decide +kernel

lemma closed (m : ℕ) : (S m : ℚ) =
    (5760 * (25 * 2 ^ (1 + m) - 49) - 186828 * m - 57236 * m ^ 2 - 9885 * m ^ 3 - 905 * m ^ 4 -
            27 * m ^ 5 + m ^ 6) / 360 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases (show m < 8 ∨ 8 ≤ m by omega) with h | h
    · interval_cases m <;> simp [S0, S1, S2, S3, S4, S5, S6, S7] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
      have r' : (S (k + 8) : ℚ) + 35 * S (k + 6) + 105 * S (k + 4) + 49 * S (k + 2) + 2 * S k =
    9 * S (k + 7) + 77 * S (k + 5) + 91 * S (k + 3) + 15 * S (k + 1) := by exact_mod_cast Srec k
      rw [ih k (by omega), ih (k + 1) (by omega), ih (k + 2) (by omega), ih (k + 3) (by omega), ih (k + 4) (by omega), ih (k + 5) (by omega), ih (k + 6) (by omega), ih (k + 7) (by omega)] at r'
      push_cast at r' ⊢
      linear_combination r'

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]


end OMA.P_oeis_a251270

open OMA.S_oeis_a251270 OMA.P_oeis_a251270 PowerSeries

set_option maxRecDepth 100000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a251270.main := by
  have hcl : ∀ n : ℕ, (a n : ℚ) =
      (5760 * (25 * 2 ^ (1 + n) - 49) - 186828 * n - 57236 * n ^ 2 - 9885 * n ^ 3 - 905 * n ^ 4 -
            27 * n ^ 5 + n ^ 6) / 360 := fun n => by
    rw [a_eq]; exact closed n
  have hrec : ∀ n : ℕ, 9 ≤ n → (a n : ℚ) = 9 * a (n - 1) - 35 * a (n - 2) + 77 * a (n - 3) - 105 * a (n - 4) + 91 * a (n - 5) - 49 * a (n - 6) + 15 * a (n - 7) - 2 * a (n - 8) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    rw [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega, show k + 9 = k + 1 + 8 by omega]
    simp only [a_eq]
    have h' : (S (k + 1 + 8) : ℚ) + 35 * S (k + 1 + 6) + 105 * S (k + 1 + 4) + 49 * S (k + 1 + 2) + 2 * S (k + 1) =
    9 * S (k + 1 + 7) + 77 * S (k + 1 + 5) + 91 * S (k + 1 + 3) + 15 * S (k + 1 + 1) := by exact_mod_cast Srec (k + 1)
    simp only [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega, show k + 1 + 3 = k + 4 by omega, show k + 1 + 4 = k + 5 by omega, show k + 1 + 5 = k + 6 by omega, show k + 1 + 6 = k + 7 by omega, show k + 1 + 7 = k + 8 by omega] at h'
    linear_combination h'
  refine ⟨?_, fun n _ => hcl n⟩
  rw [show ((1 - X) ^ 7 * (1 - 2 * X) : PowerSeries ℚ) = 1 - C (9:ℚ) * X + C (35:ℚ) * X ^ 2 - C (77:ℚ) * X ^ 3 + C (105:ℚ) * X ^ 4 - C (91:ℚ) * X ^ 5 + C (49:ℚ) * X ^ 6 - C (15:ℚ) * X ^ 7 + C (2:ℚ) * X ^ 8 by
      simp only [map_ofNat]; ring,
    show (X * (108 - 492 * X + 1127 * X ^ 2 - 1589 * X ^ 3 + 1407 * X ^ 4 - 769 * X ^ 5 + 238 * X ^ 6 -
          32 * X ^ 7) : PowerSeries ℚ) =
      C (108:ℚ) * X - C (492:ℚ) * X ^ 2 + C (1127:ℚ) * X ^ 3 - C (1589:ℚ) * X ^ 4 + C (1407:ℚ) * X ^ 5 - C (769:ℚ) * X ^ 6 + C (238:ℚ) * X ^ 7 - C (32:ℚ) * X ^ 8 by
      simp only [map_ofNat]; ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
    PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  have v1 : (a 1 : ℚ) = 108 := by rw [hcl]; norm_num
  have v2 : (a 2 : ℚ) = 480 := by rw [hcl]; norm_num
  have v3 : (a 3 : ℚ) = 1667 := by rw [hcl]; norm_num
  have v4 : (a 4 : ℚ) = 4930 := by rw [hcl]; norm_num
  have v5 : (a 5 : ℚ) = 13052 := by rw [hcl]; norm_num
  have v6 : (a 6 : ℚ) = 31936 := by rw [hcl]; norm_num
  have v7 : (a 7 : ℚ) = 73805 := by rw [hcl]; norm_num
  have v8 : (a 8 : ℚ) = 163604 := by rw [hcl]; norm_num
  rcases (show n ≤ 8 ∨ 9 ≤ n by omega) with h | h
  · interval_cases n <;> simp only [v1, v2, v3, v4, v5, v6, v7, v8] <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8]
  · have hq := hrec n h
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega, show n - 8 ≠ 0 by omega]
    rw [hq]; ring


