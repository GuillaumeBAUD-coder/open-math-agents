import OMAStatements.S_oeis_a327836

namespace OMA.S_oeis_a327836



/-- The entry's conjecture. -/
def Conjecture : Prop := ∀ n : ℕ, 1 ≤ n → a n ≤ 2 * (n + 1) ^ n

theorem good_bound (n : ℕ) : Good n (2 * (n + 1) ^ n) := by
  refine ⟨by positivity, ?_⟩
  have h : (((n + 1 : ℕ) : ℤ)) ∣ ((n : ℤ) ^ 2) - 1 :=
    ⟨(n : ℤ) - 1, by push_cast; ring⟩
  have h2 := dvd_sub_pow_of_dvd_sub h n
  rw [one_pow, ← pow_mul] at h2
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd]
  push_cast at h2 ⊢
  exact h2

/-- `a(n)` is an admissible exponent. -/
theorem a_good (n : ℕ) : Good n (a n) :=
  Nat.sInf_mem (s := {k | Good n k}) ⟨_, good_bound n⟩

theorem proof : Conjecture := fun n _ => Nat.sInf_le (good_bound n)

/-- Controls: the definition reproduces `a(1..4) = 1, 18, 64, 1250`. -/
theorem a_eq_of {n v : ℕ} (hv : Good n v) (hmin : ∀ k < v, ¬ Good n k) : a n = v :=
  le_antisymm (Nat.sInf_le hv) (le_csInf ⟨v, hv⟩ fun k hk => not_lt.mp fun h => hmin k h hk)

theorem a1 : a 1 = 1 := a_eq_of (by unfold Good; decide) (by unfold Good; decide)
theorem a2 : a 2 = 18 := a_eq_of (by unfold Good; decide) (by unfold Good; decide)
theorem a3 : a 3 = 64 := a_eq_of (by unfold Good; decide +kernel) (by unfold Good; decide +kernel)
theorem a4 : a 4 = 1250 :=
  a_eq_of (by unfold Good; decide +kernel) (by unfold Good; decide +kernel)

end OMA.S_oeis_a327836

theorem OMA.solution : type_of% @OMA.S_oeis_a327836.main :=
  OMA.S_oeis_a327836.proof
