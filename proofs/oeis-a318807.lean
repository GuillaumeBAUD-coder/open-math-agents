import OMAStatements.S_oeis_a318807

/-! A smaller counterexample to Michel Lagneau's A318807 conjecture.
The earlier disproof in #9203 uses the composite root 3107. Here the root
is 268. The squarefree-divisor product argument follows @anmolspace.
Source: https://oeis.org/A318807
Credit: @dwilfand-sys (smaller witness and proof)
-/

open Finset OMA.S_oeis_a318807

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a318807.main) := by
  intro h
  let w : ℕ := 4963023000
  let l : List ℕ := [2,2,2,3,3,5,5,5,13,13,13,251]
  have hw : w ≠ 0 := by decide
  have hf : w.primeFactorsList = l := by
    symm
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (by decide) (Nat.primeFactorsList_sorted w).pairwise
    apply Nat.primeFactorsList_unique (by decide)
    norm_num [l, List.forall_mem_cons]
  have hs : squarefreeSum w = 254016 := by
    rw [squarefreeSum, Nat.sum_divisors_filter_squarefree hw, Nat.factors_eq]
    change ∑ s ∈ w.primeFactors.powerset, s.val.prod = _
    calc
      _ = ∏ p ∈ w.primeFactors, (1+p) := by
        rw [Finset.prod_one_add]
        exact Finset.sum_congr rfl fun s _ ↦ Finset.prod_val s
      _ = _ := by rw [← Nat.toFinset_factors, hf]; decide
  have ht : ∑ d ∈ w.divisors, d = 18244699200 := by
    rw [Nat.sum_divisors hw]
    simp only [← Nat.primeFactorsList_count_eq, ← Nat.toFinset_factors, hf]
    decide
  have split : squarefreeSum w + nonsquarefreeSum w = ∑ d ∈ w.divisors, d :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hn : nonsquarefreeSum w = 18244445184 := by omega
  obtain ⟨p, hp, eq⟩ := h w (268^2) (by decide)
    ⟨504, by rw [hs]⟩ ⟨135072, by rw [hn]⟩ (by decide) (by rw [hs, hn]; decide)
  have : p = 268 := by nlinarith
  exact (show ¬ Nat.Prime 268 by norm_num) (this ▸ hp)
