import OMAStatements.S_oeis_a208705
import Mathlib

-- Proof of the formulas of OEIS A208705 (statement by @ivillar).
-- Idea: the conditions only involve consecutive lines, so the count is a walk count on lines (transfer matrix).
-- The lines are grouped into 4 classes such that the number of successors in each class depends only on the class
-- (checked by decide); the class counts V n c then satisfy an explicit linear system, from which the recurrence
-- follows by linear algebra, and the g.f. and the closed form follow from the recurrence and initial values.

namespace OMAA208705Helpers

open OMA.S_oeis_a208705

/-- The lines of the array (the states of the transfer matrix). -/
abbrev R := Fin 4 → Fin 2

instance (u v : R) : Decidable (BlockOK u v) := by unfold BlockOK; infer_instance

abbrev ok (_r : R) : Prop := True

instance (u : R) : Decidable (Init u) := by unfold Init; infer_instance

abbrev ini (r : R) : Prop := Init r

abbrev compat (r s : R) : Prop := BlockOK r s

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

def F (n : ℕ) (s : R) : ℕ := ∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0

theorem F_zero (s : R) : F 0 s = if ok s then 1 else 0 := by
  unfold F
  rw [← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  have h : ∀ r : R, (if Walk ((Equiv.funUnique (Fin 1) R).symm r) ∧
      (Equiv.funUnique (Fin 1) R).symm r 0 = s then 1 else 0) = if r = s then (if ok s then 1 else 0) else 0 := by
    intro r
    simp only [Equiv.funUnique_symm_apply, Walk, IsEmpty.forall_iff, and_true]
    by_cases hr : r = s
    · subst hr; simp
    · simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
  simp

theorem F_succ (n : ℕ) (s : R) :
    F (n + 1) s = ∑ t : R, if ok s ∧ compat s t then F n t else 0 := by
  have lhs : F (n + 1) s = ∑ y : Fin (n + 1) → R, if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0 := by
    unfold F
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have h : ∀ r : R, (if Walk ((Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y)) ∧
        (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) 0 = s then 1 else 0) =
        if r = s then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
      intro r
      rw [show (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) = (Fin.cons r y : Fin (n + 2) → R)
        from rfl]
      simp only [walk_cons, Fin.cons_zero]
      by_cases hr : r = s
      · subst hr
        rw [if_pos rfl]
        exact if_congr ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩ rfl rfl
      · rw [if_neg hr, if_neg (show ¬((ok r ∧ compat r (y 0) ∧ Walk y) ∧ r = s) from fun h => hr h.2)]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [lhs]
  unfold F
  have h2 : ∀ t : R, (if ok s ∧ compat s t then
      ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = t then 1 else 0) else 0) =
      ∑ y : Fin (n + 1) → R, if y 0 = t then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
    intro t
    split_ifs with ht
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y 0 = t
      · subst hy
        rw [if_pos (rfl : y 0 = y 0)]
        exact if_congr ⟨fun h => ⟨ht.1, ht.2, h.1⟩, fun h => ⟨h.2.2, rfl⟩⟩ rfl rfl
      · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = t) from fun h => hy h.2)]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 0 = t
      · subst hy; rw [if_pos rfl, if_neg (fun h => ht ⟨h.1, h.2.1⟩)]
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

theorem good_iff (n : ℕ) (x : Fin (n + 1) → R) : Good x ↔ Walk x ∧ ini (x 0) := by
  unfold Good
  constructor
  · rintro ⟨h2, h3⟩
    exact ⟨⟨fun _ => trivial, fun i => h2 i.castSucc i.succ (by simp)⟩, h3 0 rfl⟩
  · rintro ⟨⟨-, h2⟩, h3⟩
    refine ⟨fun i j hij => ?_, fun i hi => ?_⟩
    · have hi : (i : ℕ) < n := by have := j.isLt; omega
      have e1 : (⟨i, hi⟩ : Fin n).castSucc = i := Fin.ext rfl
      have e2 : (⟨i, hi⟩ : Fin n).succ = j := Fin.ext (by simp [hij])
      have := h2 ⟨i, hi⟩
      rw [e1, e2] at this
      exact this
    · have e : i = 0 := Fin.ext hi
      rw [e]; exact h3

/-- Index of a line in the class table. -/
def code (r : R) : ℕ := (r 0 : ℕ) + 2 * ((r 1 : ℕ) + 2 * ((r 2 : ℕ) + 2 * ((r 3 : ℕ))))

/-- The class of a line: lines of the same class have the same number of successors in each class. -/
def cls (r : R) : ℕ := ([0, 0, 3, 3, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 0, 0] : List ℕ).getD (code r) 0

/-- Mt i j: the number of successors in class j of a line of class i. -/
def Mt (i j : ℕ) : ℕ :=
  (([[2, 2, 3, 3],
    [3, 3, 3, 3],
    [4, 4, 4, 4],
    [2, 2, 4, 4]] : List (List ℕ)).getD i []).getD j 0

/-- V n c: the number of walks of n + 1 lines starting at a given line of class c. -/
def V : ℕ → ℕ → ℕ
  | 0, c => ([1, 1, 1, 1] : List ℕ).getD c 0
  | n + 1, 0 => 2 * V n 0 + 2 * V n 1 + 3 * V n 2 + 3 * V n 3
  | n + 1, 1 => 3 * V n 0 + 3 * V n 1 + 3 * V n 2 + 3 * V n 3
  | n + 1, 2 => 4 * V n 0 + 4 * V n 1 + 4 * V n 2 + 4 * V n 3
  | n + 1, 3 => 2 * V n 0 + 2 * V n 1 + 4 * V n 2 + 4 * V n 3
  | _ + 1, _ => 0

theorem cls_lt : ∀ t : R, cls t < 4 := by decide +kernel

theorem sum_cls (g : ℕ → ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 4, (Finset.univ.filter (fun t : R => cls t = c ∧ P t)).card * g c := by
  have h1 : ∀ t : R, (if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 4, if cls t = c ∧ P t then g c else 0 := by
    intro t
    rw [Finset.sum_eq_single (cls t)]
    · by_cases hp : P t <;> simp [hp]
    · intro c _ hc
      rw [if_neg]
      exact fun h => hc h.1.symm
    · intro h
      exact absurd (Finset.mem_range.mpr (cls_lt t)) h
  rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

theorem cnt : ∀ s : R, ∀ c < 4,
    (Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t))).card = Mt (cls s) c := by
  decide +kernel

theorem cnt0 : ∀ s : R, (if ok s then 1 else 0) = V 0 (cls s) := by decide +kernel

theorem tcnt : ∀ c < 4, (Finset.univ.filter (fun t : R => cls t = c ∧ ini t)).card =
    ([2, 2, 2, 2] : List ℕ).getD c 0 := by decide +kernel

theorem step (n : ℕ) : ∀ i < 4, (∑ c ∈ Finset.range 4, Mt i c * V n c) = V (n + 1) i := by
  intro i hi
  interval_cases i <;> simp [Finset.sum_range_succ, Mt, V]

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n (cls s) := by
  induction n with
  | zero => intro s; rw [F_zero]; exact cnt0 s
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    rw [sum_cls (V n) (fun t => ok s ∧ compat s t), ← step n (cls s) (cls_lt s)]
    apply Finset.sum_congr rfl
    intro c hc
    rw [cnt s c (Finset.mem_range.mp hc)]

/-- U n: the number of arrays with n + 1 lines. -/
def U (n : ℕ) : ℕ := 2 * V n 0 + 2 * V n 1 + 2 * V n 2 + 2 * V n 3

theorem usum (n : ℕ) : (∑ c ∈ Finset.range 4, ([2, 2, 2, 2] : List ℕ).getD c 0 * V n c) = U n := by
  simp [Finset.sum_range_succ, U]

theorem a_eq (n : ℕ) : a (n + 1) = U n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good_iff n)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x ∧ ini (x 0) then 1 else 0) =
      ∑ s : R, if ini s then F n s else 0 := by
    unfold F
    have h2 : ∀ s : R, (if ini s then ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = s then 1 else 0)
        else 0) = ∑ y : Fin (n + 1) → R, if y 0 = s then (if Walk y ∧ ini (y 0) then 1 else 0)
          else 0 := by
      intro s
      split_ifs with hs
      · apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y 0 = s
        · subst hy; simp [hs]
        · simp [hy]
      · symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : y 0 = s
        · subst hy; rw [if_pos rfl, if_neg (fun h => hs h.2)]
        · rw [if_neg hy]
    rw [Finset.sum_congr rfl (fun s _ => h2 s), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_ite_eq]
    simp
  rw [h1]
  simp only [F_eq]
  rw [sum_cls (V n) (fun t => ini t), ← usum n]
  apply Finset.sum_congr rfl
  intro c hc
  rw [tcnt c (Finset.mem_range.mp hc)]

theorem up0 (n : ℕ) : U n = 2 * V n 0 + 2 * V n 1 + 2 * V n 2 + 2 * V n 3 := rfl

theorem up1 (n : ℕ) : U (n + 1) = 22 * V n 0 + 22 * V n 1 + 28 * V n 2 + 28 * V n 3 := by
  rw [up0 (n + 1)]
  simp only [V]
  ring

theorem up2 (n : ℕ) : U (n + 2) = 278 * V n 0 + 278 * V n 1 + 356 * V n 2 + 356 * V n 3 := by
  rw [show n + 2 = (n + 1) + 1 from rfl, up1 (n + 1)]
  simp only [V]
  ring

theorem a_rec : ∀ m : ℕ, 3 ≤ m → (a m : ℤ) = 13 * (a (m - 1) : ℤ) - 4 * (a (m - 2) : ℤ) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
  rw [show a (k + 3) = U (k + 2) from a_eq _, show a (k + 2) = U (k + 1) from a_eq _, show a (k + 1) = U (k) from a_eq _]
  rw [up2 k, up1 k, up0 k]
  push_cast
  ring

theorem a_v1 : a 1 = 8 := by
  rw [show a 1 = U 0 from a_eq _]; decide +kernel

theorem a_v2 : a 2 = 100 := by
  rw [show a 2 = U 1 from a_eq _]; decide +kernel

theorem gf_eq : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * (1 - 13 * PowerSeries.X + 4 * PowerSeries.X ^ 2) = F' - PowerSeries.C (13 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 2 * F') := by
    simp only [map_ofNat]
    ring
  have e2 : (4 * PowerSeries.X * (2 - PowerSeries.X) : PowerSeries ℚ) = PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 2
  · interval_cases n <;> norm_num [a_v1, a_v2]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    have h := a_rec (j + 3) (by omega)
    rw [show j + 3 - 1 = j + 2 by omega, show j + 3 - 2 = j + 1 by omega] at h
    have q : (a (j + 3) : ℚ) = 13 * (a (j + 2) : ℚ) - 4 * (a (j + 1) : ℚ) := by exact_mod_cast h
    simp
    linear_combination q

theorem hs0 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)

theorem char0_0 : ((13 : ℝ) + (-3 : ℝ) * Real.sqrt 17 ^ 1) ^ 2 = (26 : ℝ) * ((13 : ℝ) + (-3 : ℝ) * Real.sqrt 17 ^ 1) ^ 1 + (-16 : ℝ) * ((13 : ℝ) + (-3 : ℝ) * Real.sqrt 17 ^ 1) ^ 0 := by
  linear_combination ((9 : ℝ)) * hs0

theorem char0_1 : ((13 : ℝ) + (3 : ℝ) * Real.sqrt 17 ^ 1) ^ 2 = (26 : ℝ) * ((13 : ℝ) + (3 : ℝ) * Real.sqrt 17 ^ 1) ^ 1 + (-16 : ℝ) * ((13 : ℝ) + (3 : ℝ) * Real.sqrt 17 ^ 1) ^ 0 := by
  linear_combination ((9 : ℝ)) * hs0

theorem closedM0 : ∀ n : ℕ, 1 ≤ n → (2 : ℝ) ^ n * ((2 : ℝ) * Real.sqrt 17 ^ 1) * (a n : ℝ) = ((13 : ℝ) + (-3 : ℝ) * Real.sqrt 17 ^ 1) ^ n * ((-1 : ℝ) + (1 : ℝ) * Real.sqrt 17 ^ 1) + ((13 : ℝ) + (3 : ℝ) * Real.sqrt 17 ^ 1) ^ n * ((1 : ℝ) + (1 : ℝ) * Real.sqrt 17 ^ 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 3
    · interval_cases n
      · rw [a_v1]; push_cast; linear_combination (0 : ℝ) * hs0
      · rw [a_v2]; push_cast; linear_combination ((-18 : ℝ) * Real.sqrt 17 ^ 1) * hs0
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have h1 := ih (k + 2) (by omega) (by omega)
      have h2 := ih (k + 1) (by omega) (by omega)
      have hr := a_rec (k + 3) (by omega)
      rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega] at hr
      have q : (a (k + 3) : ℝ) = 13 * (a (k + 2) : ℝ) - 4 * (a (k + 1) : ℝ) := by exact_mod_cast hr
      linear_combination ((2 : ℝ) ^ (k + 3) * ((2 : ℝ) * Real.sqrt 17 ^ 1)) * q + (26 : ℝ) * h1 + (-16 : ℝ) * h2 - (((-1 : ℝ) + (1 : ℝ) * Real.sqrt 17 ^ 1) * ((13 : ℝ) + (-3 : ℝ) * Real.sqrt 17 ^ 1) ^ (k + 1)) * char0_0 - (((1 : ℝ) + (1 : ℝ) * Real.sqrt 17 ^ 1) * ((13 : ℝ) + (3 : ℝ) * Real.sqrt 17 ^ 1) ^ (k + 1)) * char0_1

theorem closedS0 : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((2 : ℝ) ^ (-1 - (n : ℤ)) * ((13 - 3 * Real.sqrt 17) ^ n * (-1 + Real.sqrt 17) + (1 + Real.sqrt 17) * (13 + 3 * Real.sqrt 17) ^ n)) / Real.sqrt 17 := by
  intro n hn
  have hM := closedM0 n hn
  have hpos : (0 : ℝ) < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [show (-1 - (n : ℤ)) = -((n : ℤ) + 1) by ring, zpow_neg, zpow_add_one₀ (by norm_num), zpow_natCast, eq_div_iff (by positivity)]
  field_simp
  linear_combination hM

end OMAA208705Helpers

open OMA.S_oeis_a208705 OMAA208705Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a208705.main :=
  ⟨a_rec, gf_eq, closedS0⟩
