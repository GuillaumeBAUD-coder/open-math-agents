import OMAStatements.S_oeis_a264100
import Mathlib.Tactic

/-!
Proof of OEIS A264100: the first differences of totalLength reduce to endingWeight,
and by Nat.succ_div the jump endingWeight (n + 1) - endingWeight n sums (k + 1)
over all divisors k of n + 1, yielding sigma(n + 1) + tau(n + 1).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a264100.main := by
  intro n
  have hdiff (m : ℕ) : OMA.S_oeis_a264100.totalLength (m + 1) - OMA.S_oeis_a264100.totalLength m =
      OMA.S_oeis_a264100.endingWeight m := by
    unfold OMA.S_oeis_a264100.totalLength
    rw [Finset.sum_range_succ, Nat.add_sub_cancel_left]
  rw [hdiff (n + 1), hdiff n]
  have hew : OMA.S_oeis_a264100.endingWeight n =
      1 + ∑ k ∈ Finset.Icc 1 (n + 1), (k + 1) * (n / k) := by
    unfold OMA.S_oeis_a264100.endingWeight
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
      Nat.div_eq_of_lt (Nat.lt_succ_self n), mul_zero, add_zero]
  have hew1 : OMA.S_oeis_a264100.endingWeight (n + 1) =
      OMA.S_oeis_a264100.endingWeight n +
        ∑ k ∈ Finset.Icc 1 (n + 1), if k ∣ n + 1 then k + 1 else 0 := by
    rw [hew]
    unfold OMA.S_oeis_a264100.endingWeight
    have hsum : ∑ k ∈ Finset.Icc 1 (n + 1), (k + 1) * ((n + 1) / k) =
        (∑ k ∈ Finset.Icc 1 (n + 1), (k + 1) * (n / k)) +
          ∑ k ∈ Finset.Icc 1 (n + 1), if k ∣ n + 1 then k + 1 else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.succ_div]
      split_ifs <;> ring
    rw [hsum]
    omega
  rw [hew1, Nat.add_sub_cancel_left, ← Finset.sum_filter]
  have hfilt : (Finset.Icc 1 (n + 1)).filter (· ∣ n + 1) = (n + 1).divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, ne_eq,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, and_true]
    exact ⟨fun ⟨_, hdvd⟩ => hdvd, fun hdvd =>
      ⟨⟨Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos n), Nat.le_of_dvd (Nat.succ_pos n) hdvd⟩, hdvd⟩⟩
  rw [hfilt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
