import OMAReductions.R_RegularPrimes_small_regular_primes_R1

-- Credit: @Halldon. The table certificate follows @VinnyMo's proof in open-math-agents #1075.

namespace OMA.SmallRegularPrimes

private def entry (n : ℕ) : ℚ :=
  ([1, 1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0,
    -691/2730, 0, 7/6, 0, -3617/510, 0, 43867/798, 0, -174611/330, 0,
    854513/138, 0, -236364091/2730, 0, 8553103/6, 0, -23749461029/870] : List ℚ)[n]?.getD 0

set_option maxRecDepth 10000 in
private theorem recurrence : ∀ i : Fin 29, entry i = 1 -
    ∑ k ∈ Finset.range i.val, i.val.choose k / (i.val - k + 1) * entry k := by
  decide +kernel

private theorem correct (n : ℕ) (hn : n < 29) : bernoulli' n = entry n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [bernoulli'_def, recurrence ⟨n, hn⟩]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih k (Finset.mem_range.mp hk) ((Finset.mem_range.mp hk).trans hn)]

set_option maxRecDepth 10000 in
private theorem checked :
    ∀ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ),
      p < 32 ∧ ∀ k ∈ Finset.Icc 2 (p - 3), k % 2 = 0 → ¬ (p : ℤ) ∣ (entry k).num := by
  decide +kernel

theorem arithmetic : OMA.R_RegularPrimes_small_regular_primes_R1.H2 := by
  intro p hp k hk heven
  obtain ⟨hpBound, hCompute⟩ := checked p hp
  have hkBound := (Finset.mem_Icc.mp hk).2
  rw [correct k (by omega)]
  exact hCompute k hk (Nat.even_iff.mp heven)

end OMA.SmallRegularPrimes

theorem OMA.solution : OMA.R_RegularPrimes_small_regular_primes_R1.H2 :=
  OMA.SmallRegularPrimes.arithmetic
