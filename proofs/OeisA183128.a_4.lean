import FormalConjectures.OEIS.«183128»

-- Problem: Hanna's exponential series for $\binom{n+k-1}{k}^{k^2+1}$ — a 4
-- Upstream: formal-conjectures FormalConjectures/OEIS/183128.lean:68 (declaration OeisA183128.a_4)
-- Credit: @dk8827 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem OMA.solution : type_of% @OeisA183128.a_4 := by
  classical
  let g := OeisA183128.hannaLog fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + 1)
  change coeff 4 (subst g (exp ℚ)) = 131
  have hg : g.constantCoeff = 0 := by simp [g, OeisA183128.hannaLog]
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range 5)]
  · norm_num [Finset.sum_range_succ, coeff_exp, pow_succ, coeff_mul,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, g,
      OeisA183128.hannaLog, coeff_mk, Finset.sum_Icc_succ_top, Nat.factorial]
  · intro k hk
    by_contra h
    change k ∉ Finset.range 5 at h
    have hlt : (4 : ℕ∞) < k := by
      have : 4 < k := Nat.le_of_not_gt (fun hk' => h (Finset.mem_range.mpr hk'))
      exact_mod_cast this
    have hz := coeff_of_lt_order 4
      (hlt.trans_le (le_order_pow_of_constantCoeff_eq_zero k hg))
    exact hk (by simp [hz])
