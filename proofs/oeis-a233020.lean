import OMAStatements.S_oeis_a233020
import Mathlib

-- The statement and two-type transfer proof are from @ivillar, PR #14842.
-- Idea: with two columns, every pair of cells in the same or consecutive rows is adjacent, so an array
-- is good iff each row has no complementary pair (sum 3) and no two consecutive rows contain one; the
-- count is then a walk count on rows (transfer matrix). The number of walks from a row depends only on
-- its type: constant rows (u,u) have 3 constant and 4 two-valued successors, two-valued rows {u,v} have
-- 2 and 2. So a(n+1) = α(n) + 2β(n) with (α, β) -> (3α + 4β, 2α + 2β); this 2 X 2 system has
-- characteristic polynomial t^2 - 5t - 2, which gives the recurrence and the rest.

namespace OMAA233020Helpers

open OMA.S_oeis_a233020

abbrev R := Fin 2 → Fin 4

/-- A row with no complementary horizontal pair. -/
abbrev ok (r : R) : Prop := (r 0 : ℕ) + r 1 ≠ 3

/-- Two consecutive rows: no complementary pair between them (all such cells are adjacent). -/
abbrev compat (r s : R) : Prop := ∀ j j' : Fin 2, (r j : ℕ) + s j' ≠ 3

/-- The array conditions, row by row. -/
abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem good_iff (n : ℕ) (x : Fin (n + 1) → R) : Good x ↔ Walk x ∧ x 0 0 = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i => ?_, fun i j j' => ?_⟩, ?_⟩
    · have h := h1 (i, 0) (i, 1) ⟨by simp, by simp, by simp, by simp, by simp⟩
      have b0 := (x i 0).isLt
      have b1 := (x i 1).isLt
      simp only at h
      omega
    · have hj := j.isLt
      have hj' := j'.isLt
      have h := h1 (i.castSucc, j) (i.succ, j')
        ⟨by simp [Prod.ext_iff, Fin.ext_iff], by simp only [Fin.val_castSucc, Fin.val_succ]; omega,
          by simp only [Fin.val_castSucc, Fin.val_succ]; omega, by omega, by omega⟩
      have b0 := (x i.castSucc j).isLt
      have b1 := (x i.succ j').isLt
      simp only at h
      omega
    · exact h2 (Nat.succ_pos n)
  · rintro ⟨⟨hok, hc⟩, h0⟩
    have near (i k : Fin (n + 1)) (h : i.val + 1 = k.val) : compat (x i) (x k) := by
      let j : Fin n := ⟨i.val, by have := k.isLt; omega⟩
      simpa only [show j.castSucc = i from Fin.ext rfl, show j.succ = k from Fin.ext h] using hc j
    refine ⟨?_, fun h => ?_⟩
    · rintro ⟨i, j⟩ ⟨k, l⟩ ⟨hne, h1, h2, -, -⟩
      change i.val ≤ k.val + 1 at h1
      change k.val ≤ i.val + 1 at h2
      change (x k l : ℕ) ≠ 3 - (x i j : ℕ)
      have bp := (x i j).isLt
      have bq := (x k l).isLt
      suffices h : (x i j : ℕ) + x k l ≠ 3 by omega
      rcases lt_trichotomy i.val k.val with hl | he | hg
      · exact near i k (by omega) j l
      · have hi : i = k := Fin.ext he
        subst k
        have hj : j ≠ l := fun e => hne (Prod.ext rfl e)
        have hr : (x i 0 : ℕ) + x i 1 ≠ 3 := hok i
        have columns : ∀ j l : Fin 2, j ≠ l → (j = 0 ∧ l = 1) ∨ (j = 1 ∧ l = 0) := by decide
        rcases columns j l hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simpa [add_comm] using hr
      · have h := near k i (by omega) l j
        omega
    · exact h0

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

/-- F(n, s): the number of row sequences of length n+1 satisfying the conditions, starting at s. -/
def F (n : ℕ) (s : R) : ℕ := ∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0

private lemma sum_fixed_row (s : R) (p : R → Prop) [DecidablePred p] :
    (∑ r : R, if p r ∧ r = s then (1 : ℕ) else 0) = if p s then 1 else 0 := by
  have h (r : R) : (if p r ∧ r = s then (1 : ℕ) else 0) =
      if r = s then (if p r then 1 else 0) else 0 := by
    by_cases hr : r = s <;> simp [hr]
  simp [h, Finset.sum_ite_eq']

theorem F_zero (s : R) : F 0 s = if ok s then 1 else 0 := by
  unfold F
  rw [← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  simpa [Equiv.funUnique_symm_apply, Walk] using sum_fixed_row s ok

private theorem sum_by_state {U S : Type*} [Fintype U] [Fintype S] [DecidableEq S]
    (state : U → S) (valid : U → Prop) [DecidablePred valid]
    (allowed : S → Prop) [DecidablePred allowed] :
    (∑ y : U, if allowed (state y) ∧ valid y then (1 : ℕ) else 0) =
      ∑ t : S, if allowed t then ∑ y : U, if valid y ∧ state y = t then 1 else 0 else 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := state) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) (fun y => if allowed (state y) ∧ valid y then (1 : ℕ) else 0)]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_filter]
  by_cases ht : allowed t
  · rw [if_pos ht]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : state y = t <;> simp [hy, ht]
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : state y = t <;> simp [hy, ht]

theorem F_succ (n : ℕ) (s : R) :
    F (n + 1) s = ∑ t : R, if ok s ∧ compat s t then F n t else 0 := by
  have lhs : F (n + 1) s = ∑ y : Fin (n + 1) → R, if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0 := by
    unfold F
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simpa only [Fin.consEquiv_apply, walk_cons, Fin.cons_zero] using
      sum_fixed_row s (fun r => ok r ∧ compat r (y 0) ∧ Walk y)
  rw [lhs]
  unfold F
  simpa only [and_assoc] using
    sum_by_state (fun y : Fin (n + 1) → R => y 0) Walk (fun t => ok s ∧ compat s t)

def α : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * α n + 4 * β n
where
  β : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * α n + 2 * β n

/-- The value of F by row type: constant rows give α, two-valued rows give β, bad rows 0. -/
def V (n : ℕ) (s : R) : ℕ := if ok s then (if s 0 = s 1 then α n else α.β n) else 0

theorem cA : ∀ s : R, (Finset.univ.filter (fun t : R => ok s ∧ compat s t ∧ ok t ∧ t 0 = t 1)).card =
    if ok s then (if s 0 = s 1 then 3 else 2) else 0 := by decide

theorem cB : ∀ s : R, (Finset.univ.filter (fun t : R => ok s ∧ compat s t ∧ ok t ∧ ¬ t 0 = t 1)).card =
    if ok s then (if s 0 = s 1 then 4 else 2) else 0 := by decide

theorem c0A : (Finset.univ.filter (fun t : R => t 0 = 0 ∧ ok t ∧ t 0 = t 1)).card = 1 := by decide

theorem c0B : (Finset.univ.filter (fun t : R => t 0 = 0 ∧ ok t ∧ ¬ t 0 = t 1)).card = 2 := by decide

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = (if P ∧ ok t ∧ t 0 = t 1 then α n else 0) +
      (if P ∧ ok t ∧ ¬ t 0 = t 1 then α.β n else 0) := by
  by_cases hp : P <;> by_cases ho : ok t <;> by_cases he : t 0 = t 1 <;> simp [V, hp, ho, he]

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n s := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    unfold V
    by_cases h : ok s
    · rw [if_pos h, if_pos h]; split_ifs <;> rfl
    · rw [if_neg h, if_neg h]
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    rw [Finset.sum_congr rfl (fun t _ => split_V n (ok s ∧ compat s t) t), Finset.sum_add_distrib,
      Finset.sum_ite, Finset.sum_ite]
    simp only [Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, add_zero]
    have hA := cA s
    have hB := cB s
    simp only [and_assoc] at hA hB ⊢
    rw [hA, hB]
    unfold V
    split_ifs <;> simp [α, α.β] <;> ring

theorem a_succ (n : ℕ) : a (n + 1) = α n + 2 * α.β n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good_iff n)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x ∧ x 0 0 = 0 then 1 else 0) =
      ∑ s : R, if s 0 = 0 then F n s else 0 := by
    simpa only [F, and_comm] using
      sum_by_state (fun x : Fin (n + 1) → R => x 0) Walk (fun s => s 0 = 0)
  rw [h1]
  simp only [F_eq]
  rw [Finset.sum_congr rfl (fun t _ => split_V n (t 0 = 0) t), Finset.sum_add_distrib,
    Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, add_zero]
  rw [c0A, c0B]
  ring

theorem a_rec (n : ℕ) : a (n + 3) = 5 * a (n + 2) + 2 * a (n + 1) := by
  rw [a_succ, a_succ, a_succ]
  simp only [α, α.β]
  ring

theorem a_one : a 1 = 3 := by rw [a_succ]; simp [α, α.β]

theorem a_two : a 2 = 15 := by rw [a_succ]; simp [α, α.β]

theorem ab (k : ℕ) : a (k + 1) = 3 * b (k + 1) ∧ a (k + 2) = 3 * b (k + 2) := by
  induction k with
  | zero => exact ⟨by rw [a_one]; rfl, by rw [a_two]; rfl⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [show k + 1 + 2 = k + 3 from rfl, a_rec, ih.1, ih.2]
    show 5 * (3 * b (k + 2)) + 2 * (3 * b (k + 1)) = 3 * (5 * b (k + 2) + 2 * b (k + 1))
    ring

theorem binet (n : ℕ) : (b n : ℝ) * Real.sqrt 33 =
    ((5 + Real.sqrt 33) / 2) ^ n - ((5 - Real.sqrt 33) / 2) ^ n := by
  have hs : Real.sqrt 33 * Real.sqrt 33 = 33 := Real.mul_self_sqrt (by norm_num)
  have h1 : ((5 + Real.sqrt 33) / 2) ^ 2 = 5 * ((5 + Real.sqrt 33) / 2) + 2 := by
    linear_combination (1 / 4) * hs
  have h2 : ((5 - Real.sqrt 33) / 2) ^ 2 = 5 * ((5 - Real.sqrt 33) / 2) + 2 := by
    linear_combination (1 / 4) * hs
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [b]
    | 1, _ => simp [b]; ring
    | k + 2, ih =>
      have e1 := ih (k + 1) (by omega)
      have e0 := ih k (by omega)
      show ((5 * b (k + 1) + 2 * b k : ℕ) : ℝ) * Real.sqrt 33 = _
      push_cast
      linear_combination 5 * e1 + 2 * e0 - ((5 + Real.sqrt 33) / 2) ^ k * h1 +
        ((5 - Real.sqrt 33) / 2) ^ k * h2

end OMAA233020Helpers

open OMA.S_oeis_a233020 OMAA233020Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a233020.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    exact a_rec k
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * (1 - 5 * PowerSeries.X - 2 * PowerSeries.X ^ 2) =
        F' - PowerSeries.C (5 : ℚ) * (PowerSeries.X ^ 1 * F') -
          PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 2 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (3 * PowerSeries.X : PowerSeries ℚ) = PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 1 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 2
    · interval_cases n <;> norm_num [a_one, a_two]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      have h := a_rec j
      have q : ((a (j + 3) : ℕ) : ℚ) = ((5 * a (j + 2) + 2 * a (j + 1) : ℕ) : ℚ) := by rw [h]
      push_cast at q
      simp
      linear_combination q
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h3 : (a (k + 1) : ℝ) = 3 * (b (k + 1) : ℝ) := by exact_mod_cast (ab k).1
    have hb := binet (k + 1)
    have hq : Real.sqrt (3 / 11) * Real.sqrt 33 = 3 := by
      rw [← Real.sqrt_mul (by norm_num)]
      rw [show (3 / 11 : ℝ) * 33 = 3 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h3, ← hb]
    linear_combination (-(b (k + 1) : ℝ)) * hq
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (ab k).1
