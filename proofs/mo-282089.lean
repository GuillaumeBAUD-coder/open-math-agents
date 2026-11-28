import OMAStatements.S_mo_282089

open OMA.S_mo_282089 Finset Polynomial

private theorem totalWeight (n : ℕ) :
    2 * weight (range n) = n * (n + 1) := by
  calc
    2 * weight (range n) = (∑ i ∈ range (n + 1), i) * 2 := by
      rw [Finset.sum_range_succ' (fun i : ℕ => i) n]
      simp [weight, mul_comm]
    _ = n * (n + 1) := by
      rw [Finset.sum_range_id_mul_two, Nat.add_sub_cancel]
      exact Nat.mul_comm _ _

private theorem coefficientCount (n k : ℕ) :
    (generating n).coeff k = ((range n).powerset.filter (fun s => k = weight s)).card := by
  unfold generating
  rw [Finset.prod_one_add]
  simp only [Finset.prod_pow_eq_pow_sum, weight, Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow, Finset.sum_boole, Nat.cast_id]
  congr 1

theorem OMA.solution : type_of% @OMA.S_mo_282089.main := by
  intro n
  have ht := totalWeight n
  have hsplit (s : Finset ℕ) (hs : s ⊆ range n) :
      weight (range n \ s) + weight s = weight (range n) := by
    unfold weight
    exact Finset.sum_sdiff hs
  by_cases hparity : n * (n + 1) / 2 % 2 = 0
  · rw [if_pos hparity, coefficientCount]
    unfold ways
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hs, hbalance⟩
      refine ⟨hs, ?_⟩
      have := hsplit s hs
      omega
    · rintro ⟨hs, htarget⟩
      refine ⟨hs, ?_⟩
      have := hsplit s hs
      omega
  · rw [if_neg hparity]
    unfold ways
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_powerset] at hs
    have := hsplit s hs.1
    omega