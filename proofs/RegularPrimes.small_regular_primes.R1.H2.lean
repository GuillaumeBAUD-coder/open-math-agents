import OMAReductions.R_RegularPrimes_small_regular_primes_R1

-- Credit: @MrSeizy
-- The finite-table argument follows the Bernoulli certificate in open-math-agents PR 1075.
namespace OMA.SmallRegularPrimes

private def value (n : ℕ) : ℚ :=
  ([1, 1/2, 1/6, 0, -1/30, 0,
    1/42, 0, -1/30, 0, 5/66, 0,
    -691/2730, 0, 7/6, 0, -3617/510, 0,
    43867/798, 0, -174611/330, 0, 854513/138, 0,
    -236364091/2730, 0, 8553103/6, 0, -23749461029/870] : List ℚ)[n]?.getD 0

set_option maxRecDepth 10000 in
private theorem recurrence : ∀ n : Fin 29, value n = 1 -
    ∑ k ∈ Finset.range n.val, n.val.choose k / (n.val - k + 1) * value k := by
  decide +kernel

private theorem value_eq (n : ℕ) (hn : n < 29) : bernoulli' n = value n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [bernoulli'_def, recurrence ⟨n, hn⟩]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih k (Finset.mem_range.mp hk) ((Finset.mem_range.mp hk).trans hn)]

private def primes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31}

set_option maxRecDepth 10000 in
private theorem checkNumerators :
    ∀ p ∈ primes, ∀ k ∈ Finset.Icc 2 (p - 3), Even k →
      k < 29 ∧ ¬ (p : ℤ) ∣ (value k).num := by
  decide +kernel

end OMA.SmallRegularPrimes

open OMA.SmallRegularPrimes in
theorem OMA.solution : OMA.R_RegularPrimes_small_regular_primes_R1.H2 := by
  intro p hp k hk he
  obtain ⟨hlt, hnum⟩ := checkNumerators p hp k hk he
  rwa [value_eq k hlt]
