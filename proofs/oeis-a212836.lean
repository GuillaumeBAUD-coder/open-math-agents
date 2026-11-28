import OMAStatements.S_oeis_a212836
import Mathlib

namespace OMA.A212836Proof

open OMA.S_oeis_a212836
open PowerSeries

def ind (n x y : ℕ) : ℕ := if adj n x y then 0 else 1

theorem count_eq (n : ℕ) : a n = ∑ y ∈ Finset.range (n+1),
    (∑ x ∈ Finset.range (n+1), ind n x y) * (∑ z ∈ Finset.range (n+1), ind n y z) := by
  unfold a
  rw [Finset.card_filter]
  let e : (Fin 3 → Fin (n+1)) ≃ Fin (n+1) × Fin (n+1) × Fin (n+1) :=
    { toFun := fun f => (f 0, f 1, f 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun f => by funext i; fin_cases i <;> rfl
      right_inv := fun p => rfl }
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have h1 : ∀ x y z : Fin (n+1), (if good n (e.symm (x, y, z)) then 1 else 0) = ind n x y * ind n y z := by
    intro x y z
    have hg : good n (e.symm (x, y, z)) ↔ (¬ adj n x y ∧ ¬ adj n y z) := Iff.rfl
    simp only [hg, ind]
    split_ifs <;> simp_all
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  have hin : ∀ y : ℕ, ∑ i : Fin (n+1), ind n (i : ℕ) y = ∑ x ∈ Finset.range (n+1), ind n x y :=
    fun y => Fin.sum_univ_eq_sum_range (fun x => ind n x y) (n+1)
  have hin2 : ∀ y : ℕ, ∑ i : Fin (n+1), ind n y (i : ℕ) = ∑ x ∈ Finset.range (n+1), ind n y x :=
    fun y => Fin.sum_univ_eq_sum_range (fun x => ind n y x) (n+1)
  simp only [hin, hin2]
  exact Fin.sum_univ_eq_sum_range (fun y => (∑ x ∈ Finset.range (n+1), ind n x y) * (∑ z ∈ Finset.range (n+1), ind n y z)) (n+1)

theorem ind_symm (n x y : ℕ) : ind n x y = ind n y x := by
  simp only [ind, show adj n x y ↔ adj n y x from by unfold adj; tauto]

theorem peel (m : ℕ) (g : ℕ → ℕ) : ∑ x ∈ Finset.range (m+2), g x
    = g 0 + ∑ i ∈ Finset.range m, g (i+1) + g (m+1) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  ring

theorem innerSum (m y : ℕ) : ∑ x ∈ Finset.range (m+2), ind (m+1) x y
    = if y = 0 ∨ y = m + 1 then m + 1 else m + 2 := by
  rw [peel]
  have hmid : ∑ i ∈ Finset.range m, ind (m+1) (i+1) y = m := by
    rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro i hi
      rw [Finset.mem_range] at hi
      simp only [ind]
      rw [if_neg (by unfold adj; omega)]
  rw [hmid]
  simp only [ind, adj]
  by_cases h0 : y = 0
  · subst h0; simp; omega
  · by_cases h1 : y = m + 1
    · subst h1; simp
    · simp [h0, h1]; omega

theorem closed (m : ℕ) : a (m+1) = 2 * (m+1)^2 + m * (m+2)^2 := by
  rw [count_eq]
  have h2 : ∀ y, ∑ z ∈ Finset.range (m+2), ind (m+1) y z
      = if y = 0 ∨ y = m + 1 then m + 1 else m + 2 := by
    intro y
    rw [← innerSum]
    exact Finset.sum_congr rfl (fun z _ => ind_symm _ _ _)
  simp only [show m + 1 + 1 = m + 2 from rfl, innerSum, h2]
  rw [peel]
  have hmid : ∑ i ∈ Finset.range m,
      (if i + 1 = 0 ∨ i + 1 = m + 1 then m + 1 else m + 2) *
      (if i + 1 = 0 ∨ i + 1 = m + 1 then m + 1 else m + 2) = m * (m+2)^2 := by
    rw [Finset.sum_congr rfl (g := fun _ => (m+2)^2)]
    · simp
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [if_neg (by omega)]
      ring
  rw [hmid]
  simp
  ring

theorem closedZ (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 3 + 3 * (n : ℤ) ^ 2 - n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [closed]
  push_cast
  ring

end OMA.A212836Proof

open OMA.S_oeis_a212836 OMA.A212836Proof PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a212836.main := by
  refine ⟨closedZ, ?_, ?_⟩
  · have hc : ∀ k : ℕ, (if k = 0 then (0 : ℚ) else (a k : ℚ)) =
        if k = 0 then 0 else (k : ℚ) ^ 3 + 3 * (k : ℚ) ^ 2 - k - 1 := by
      intro k
      split_ifs with hk
      · rfl
      · have := closedZ k (by omega)
        have h' : ((a k : ℤ) : ℚ) = (((k : ℤ) ^ 3 + 3 * (k : ℤ) ^ 2 - k - 1 : ℤ) : ℚ) := by rw [this]
        push_cast at h'
        exact h'
    simp only [hc]
    ext k
    have e1 : ∀ A : PowerSeries ℚ, A * (1 - X) ^ 4 = A - C (4 : ℚ) * (A * X ^ 1) + C (6 : ℚ) * (A * X ^ 2)
        - C (4 : ℚ) * (A * X ^ 3) + A * X ^ 4 := by
      intro A
      rw [show (C (4 : ℚ) : PowerSeries ℚ) = 4 from map_ofNat C 4,
        show (C (6 : ℚ) : PowerSeries ℚ) = 6 from map_ofNat C 6]
      ring
    have e2 : (X * (2 + 9 * X - 6 * X ^ 2 + X ^ 3) : PowerSeries ℚ) =
        C (2 : ℚ) * X ^ 1 + C (9 : ℚ) * X ^ 2 - C (6 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 := by
      rw [show (C (2 : ℚ) : PowerSeries ℚ) = 2 from map_ofNat C 2,
        show (C (9 : ℚ) : PowerSeries ℚ) = 9 from map_ofNat C 9,
        show (C (6 : ℚ) : PowerSeries ℚ) = 6 from map_ofNat C 6, map_one]
      ring
    rw [e1, e2]
    simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_C, coeff_mk]
    rcases (show k ≤ 4 ∨ 5 ≤ k by omega) with hk | hk
    · interval_cases k <;> norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
      simp only [show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega,
        show j + 5 - 3 = j + 2 by omega, show j + 5 - 4 = j + 1 by omega,
        if_pos (show 1 ≤ j + 5 by omega), if_pos (show 2 ≤ j + 5 by omega),
        if_pos (show 3 ≤ j + 5 by omega), if_pos (show 4 ≤ j + 5 by omega),
        if_neg (show j + 5 ≠ 0 by omega), if_neg (show j + 4 ≠ 0 by omega),
        if_neg (show j + 3 ≠ 0 by omega), if_neg (show j + 2 ≠ 0 by omega),
        if_neg (show j + 1 ≠ 0 by omega)]
      push_cast
      ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
    rw [closedZ (k+5) (by omega), closedZ (k+4) (by omega), closedZ (k+3) (by omega),
      closedZ (k+2) (by omega), closedZ (k+1) (by omega)]
    push_cast
    ring
