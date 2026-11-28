import OMAStatements.S_mo_275621

open Finset

namespace Claude275621

/-- Mass of the subsets of `s` with fewer than `k` elements. -/
noncomputable def H {ι : Type} [DecidableEq ι] (s : Finset ι) (k : ℕ) (p : ι → ℝ) : ℝ :=
  ∑ S ∈ s.powerset, if S.card < k then (∏ i ∈ S, p i) * ∏ i ∈ s \ S, (1 - p i) else 0

variable {ι : Type} [DecidableEq ι]

lemma H_zero (s : Finset ι) (p : ι → ℝ) : H s 0 p = 0 := by simp [H]

lemma H_insert {a : ι} {s : Finset ι} (ha : a ∉ s) (k : ℕ) (p : ι → ℝ) :
    H (insert a s) (k + 1) p = (1 - p a) * H s (k + 1) p + p a * H s k p := by
  unfold H
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun S hS => ?_
    have hSs : S ⊆ s := Finset.mem_powerset.1 hS
    have haS : a ∉ S := fun h => ha (hSs h)
    rw [Finset.insert_sdiff_of_notMem _ haS,
      Finset.prod_insert (fun h => ha (Finset.mem_sdiff.1 h).1)]
    split_ifs <;> ring
  · refine Finset.sum_congr rfl fun S hS => ?_
    have hSs : S ⊆ s := Finset.mem_powerset.1 hS
    have haS : a ∉ S := fun h => ha (hSs h)
    rw [Finset.card_insert_of_notMem haS, Finset.prod_insert haS, Finset.insert_sdiff_insert,
      Finset.sdiff_insert_of_notMem ha]
    simp only [Nat.add_lt_add_iff_right]
    split_ifs <;> ring

lemma H_mono (s : Finset ι) (p : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1)
    (k : ℕ) : H s k p ≤ H s (k + 1) p := by
  unfold H
  refine Finset.sum_le_sum fun S hS => ?_
  have hSs : S ⊆ s := Finset.mem_powerset.1 hS
  have hnn : 0 ≤ (∏ i ∈ S, p i) * ∏ i ∈ s \ S, (1 - p i) :=
    mul_nonneg (Finset.prod_nonneg fun i hi => h0 i (hSs hi))
      (Finset.prod_nonneg fun i hi => sub_nonneg.2 (h1 i (Finset.mem_sdiff.1 hi).1))
  by_cases h : S.card < k
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h]; split_ifs
    · exact hnn
    · exact le_rfl

lemma H_shift (δ : ℝ) (hδ : 0 ≤ δ) (p : ι → ℝ) (s : Finset ι) :
    (∀ i ∈ s, 0 ≤ p i) → (∀ i ∈ s, p i + δ ≤ 1) →
      ∀ k, H s k (fun i => p i + δ) ≤ H s k p := by
  induction s using Finset.induction_on with
  | empty => intro _ _ k; simp [H]
  | insert a s ha ih =>
    intro h0 h1 k
    have h0s : ∀ i ∈ s, 0 ≤ p i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1s : ∀ i ∈ s, p i + δ ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih h0s h1s
    cases k with
    | zero => rw [H_zero, H_zero]
    | succ k =>
      rw [H_insert ha, H_insert ha]
      have ha0 := h0 a (Finset.mem_insert_self a s)
      have ha1 := h1 a (Finset.mem_insert_self a s)
      have hm := H_mono s p h0s (fun i hi => by have := h1s i hi; linarith) k
      have e1 := ih' (k + 1)
      have e2 := ih' k
      have w1 : 0 ≤ 1 - (p a + δ) := by linarith
      have w2 : 0 ≤ p a + δ := by linarith
      nlinarith [mul_le_mul_of_nonneg_left e1 w1, mul_le_mul_of_nonneg_left e2 w2,
        mul_nonneg hδ (sub_nonneg.2 hm)]

lemma cdf_eq {N : ℕ} (p : Fin N → ℝ) (k : ℕ) :
    OMA.S_mo_275621.cdf p k = H (Finset.univ : Finset (Fin N)) (k + 1) p := by
  unfold OMA.S_mo_275621.cdf H
  rw [Finset.sum_filter, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.compl_eq_univ_sdiff]
  simp only [Nat.lt_succ_iff]

end Claude275621

theorem OMA.solution : type_of% @OMA.S_mo_275621.main := by
  intro N p δ h0 hδ h1 k _
  rw [Claude275621.cdf_eq, Claude275621.cdf_eq]
  exact Claude275621.H_shift δ hδ p _ (fun i _ => h0 i) (fun i _ => h1 i) (k + 1)
