import OMAReductions.R_OeisA262781_conjecture_2_R1
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-! Restrict the finite sums to squares and totient weights that can fit in the target. -/

open Finset

namespace SmallTotientCounts

private lemma totient_sq (m : ℕ) (hm : 0 < m) : (m^2).totient = m*m.totient := by
  have hpr : (m^2).primeFactors = m.primeFactors := by
    rw [pow_two, Nat.primeFactors_mul hm.ne' hm.ne', Finset.union_idempotent]
  let P := ∏ p ∈ m.primeFactors, p
  let Q := ∏ p ∈ m.primeFactors, (p-1)
  have hP : 0 < P := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have h1 := Nat.totient_mul_prod_primeFactors (m^2)
  rw [hpr] at h1
  change (m^2).totient * P = m^2 * Q at h1
  have h2 : m.totient*P = m*Q := Nat.totient_mul_prod_primeFactors m
  apply Nat.eq_of_mul_eq_mul_right hP
  rw [h1, Nat.mul_assoc, h2, pow_two, Nat.mul_assoc]

private def weight (v : ℕ) : ℕ :=
  v * ((v / (∏ p ∈ v.primeFactors, p)) * ∏ p ∈ v.primeFactors, (p - 1))

private lemma weight_eq (v : ℕ) (hv : 0 < v) : (v ^ 2).totient = weight v := by
  rw [totient_sq v hv, weight, Nat.totient_eq_div_primeFactors_mul]

private def small (n : ℕ) : Finset ℕ :=
  (Ico 1 (n+1)).filter (fun v => weight v ≤ n)

private def term (n x y z : ℕ) : ℕ :=
  if (y.Prime ∨ z.Prime) ∧ x^2 + weight y + weight z = n then 1 else 0

private def fast (n : ℕ) : ℕ :=
  ∑ x ∈ range (n.sqrt+1), ∑ y ∈ small n,
    ∑ z ∈ (small n).filter (fun z => y ≤ z), term n x y z

private lemma same_count (n : ℕ) : OeisA262781.a n = fast n := by
  have hfull : OeisA262781.a n = ∑ x ∈ range (n+1), ∑ y ∈ Ico 1 (n+1),
        ∑ z ∈ Ico y (n+1), term n x y z := by
    unfold OeisA262781.a
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y hy
    apply sum_congr rfl
    intro z hz
    have hy' := (mem_Ico.mp hy).1
    have hz' := (mem_Ico.mp hz).1
    simp only [term, weight_eq y (by omega), weight_eq z (by omega)]
  rw [hfull]
  unfold fast
  calc
    _ = ∑ x ∈ range (n.sqrt+1), ∑ y ∈ Ico 1 (n+1), ∑ z ∈ Ico y (n+1), term n x y z := by
      symm
      apply sum_subset (range_mono (Nat.succ_le_succ (Nat.sqrt_le_self n)))
      intro x _ hx
      have hx' : n < x^2 := Nat.sqrt_lt'.mp (by simp at hx; omega)
      apply sum_eq_zero
      intro y _
      apply sum_eq_zero
      intro z _
      exact if_neg (fun h => by omega)
    _ = _ := by
      apply sum_congr rfl
      intro x _
      calc
        _ = ∑ y ∈ small n, ∑ z ∈ Ico y (n+1), term n x y z := by
          symm
          apply sum_subset (filter_subset _ _)
          intro y hy hny
          have hweight : n < weight y := by simpa [small, hy] using hny
          exact sum_eq_zero fun _ _ => if_neg (fun h => by omega)
        _ = _ := by
          apply sum_congr rfl
          intro y hy
          have hyl := (mem_Ico.mp (mem_filter.mp hy).1).1
          symm
          apply sum_subset
          · intro z hz
            obtain ⟨hz, hyz⟩ := mem_filter.mp hz
            exact mem_Ico.mpr ⟨hyz, (mem_Ico.mp (mem_filter.mp hz).1).2⟩
          · intro z hz hnz
            have hz' : z ∈ Ico 1 (n+1) :=
              mem_Ico.mpr ⟨hyl.trans (mem_Ico.mp hz).1, (mem_Ico.mp hz).2⟩
            have hweight : n < weight z := by
              simpa [small, hz', (mem_Ico.mp hz).1] using hnz
            exact if_neg (fun h => by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem listed_counts : ∀ n : ℕ,
    n ∈ ({3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649} : Finset ℕ) →
    OeisA262781.a n = 1 := by
  intro n hn
  simp only [mem_insert, mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [same_count]; decide +kernel

end SmallTotientCounts

theorem OMA.solution : OMA.R_OeisA262781_conjecture_2_R1.H1 := SmallTotientCounts.listed_counts