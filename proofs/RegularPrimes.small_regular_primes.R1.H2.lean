import OMAReductions.R_RegularPrimes_small_regular_primes_R1

/- The rational table uses the same recurrence certificate as the step for 37. -/
namespace OMA.BernoulliTable

def entry (n : ℕ) : ℚ :=
  ([1, 1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0, -691/2730, 0, 7/6, 0, -3617/510, 0, 43867/798, 0, -174611/330, 0, 854513/138, 0, -236364091/2730, 0, 8553103/6, 0, -23749461029/870] : List ℚ)[n]?.getD 0

set_option maxRecDepth 10000 in
private lemma recurrence : ∀ i : Fin 29, entry i = 1 -
    ∑ k ∈ Finset.range i.val, i.val.choose k / (i.val - k + 1) * entry k := by
  decide +kernel

lemma correct (n : ℕ) (hn : n < 29) : bernoulli' n = entry n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [bernoulli'_def, recurrence ⟨n, hn⟩]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih k (Finset.mem_range.mp hk) ((Finset.mem_range.mp hk).trans hn)]

private lemma nondivisibility :
    ∀ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ),
      ∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (entry k).num := by
  decide +kernel

end OMA.BernoulliTable

theorem OMA.solution : OMA.R_RegularPrimes_small_regular_primes_R1.H2 := by
  intro p hp k hk he
  have hp' : p ≤ 31 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  have hk' := (Finset.mem_Icc.mp hk).2
  rw [OMA.BernoulliTable.correct k (by omega)]
  exact OMA.BernoulliTable.nondivisibility p hp k hk he
