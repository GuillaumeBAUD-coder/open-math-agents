import OMAReductions.R_OeisA262813_conjecture_2_R1

open Finset

namespace OMA.SingletonCounts

def term (n x y z : ℕ) : ℕ :=
  if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0

def boundedCount (n : ℕ) : ℕ :=
  ∑ x ∈ range 7, ∑ y ∈ range 18, ∑ z ∈ Ico 1 26, term n x y z

lemma cut_off {n : ℕ} (lower : 25 ≤ n) (upper : n ≤ 306) :
    OeisA262813.a n = boundedCount n := by
  unfold OeisA262813.a boundedCount
  change (∑ x ∈ range (n+1), ∑ y ∈ range (n+1), ∑ z ∈ Ico 1 (n+1), term n x y z) = _
  symm
  calc
    _ = ∑ x ∈ range 7, ∑ y ∈ range 18, ∑ z ∈ Ico 1 (n+1), term n x y z := by
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      apply sum_subset (fun z hz => mem_Ico.mpr ⟨(mem_Ico.mp hz).1, by have := (mem_Ico.mp hz).2; omega⟩)
      intro z hz small
      have h : 26 ≤ z := by
        simp only [mem_Ico] at hz small
        omega
      have hzprod : 26 * 27 ≤ z * (z+1) := Nat.mul_le_mul h (Nat.succ_le_succ h)
      have big : n < x^3 + y^2 + Nat.triangular z := by
        unfold Nat.triangular
        omega
      simp [term, Nat.ne_of_gt big]
    _ = ∑ x ∈ range 7, ∑ y ∈ range (n+1), ∑ z ∈ Ico 1 (n+1), term n x y z := by
      apply sum_congr rfl
      intro x _
      apply sum_subset (range_mono (by omega))
      intro y _ small
      have h : 18 ≤ y := by simpa using small
      have bound := Nat.pow_le_pow_left h 2
      apply sum_eq_zero
      intro z _
      have big : n < x^3 + y^2 + Nat.triangular z := by omega
      simp [term, Nat.ne_of_gt big]
    _ = _ := by
      apply sum_subset (range_mono (by omega))
      intro x _ small
      have h : 7 ≤ x := by simpa using small
      have bound := Nat.pow_le_pow_left h 3
      apply sum_eq_zero
      intro y _
      apply sum_eq_zero
      intro z _
      have big : n < x^3 + y^2 + Nat.triangular z := by omega
      simp [term, Nat.ne_of_gt big]

end OMA.SingletonCounts

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : OMA.R_OeisA262813_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact OeisA262813.a_1
  · decide
  · decide
  all_goals rw [OMA.SingletonCounts.cut_off (by decide) (by decide)]
  all_goals decide
