import OMAStatements.S_oeis_a007618

-- Credit: @mfkrause

namespace OMA.R_oeis_a007618_R1

/-- At every fixed polynomial distance, some orbit reaches a power from farther back. -/
def H1 : Prop :=
  let f := fun n : ℕ => n + (Nat.digits 10 n).sum
  ∀ degree > 0, ∀ bound : ℕ, ∃ e > bound, ∃ start : ℕ,
    0 < start ∧ start % 3 ≠ 0 ∧ max 5 start + e^degree ≤ 10^e ∧
    ∃ k : ℕ, f^[k] start = 10^e

/-- For some polynomial distance, any two admissible paths from farther back meet by the power. -/
def H2 : Prop :=
  let f := fun n : ℕ => n + (Nat.digits 10 n).sum
  ∃ degree > 0, ∃ cutoff : ℕ, ∀ e > cutoff, ∀ a b : ℕ,
    0 < a → a % 3 ≠ 0 → 0 < b → b % 3 ≠ 0 → max a b + e^degree ≤ 10^e →
    ∃ i j : ℕ, f^[i] a = f^[j] b ∧ f^[j] b ≤ 10^e

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a007618.main := by
  intro surviving merging
  let f := fun n : ℕ => n + (Nat.digits 10 n).sum
  obtain ⟨degree, hdegree, cutoff, merge⟩ := merging
  apply Set.infinite_iff_exists_gt.mpr
  intro n
  obtain ⟨e, he, start, hp, hr, hgap, k, hk⟩ := surviving degree hdegree (max n cutoff)
  obtain ⟨i, j, hmeet, hbefore⟩ := merge e (by omega) 5 start (by decide) (by decide) hp hr hgap
  change f^[i] 5 = f^[j] start at hmeet
  change f^[j] start ≤ 10^e at hbefore
  change f^[k] start = 10^e at hk
  refine ⟨e, ?_, by omega⟩
  by_cases hj : j ≤ k
  · refine ⟨(k-j)+i, ?_⟩
    change f^[(k-j)+i] 5 = _
    rw [Function.iterate_add_apply, hmeet, ← Function.iterate_add_apply, Nat.sub_add_cancel hj, hk]
  · have hmono : Monotone (fun t : ℕ => f^[t] start) := by
      apply monotone_nat_of_le_succ
      intro t
      rw [Function.iterate_succ_apply']
      exact Nat.le_add_right _ _
    have hkj : f^[k] start ≤ f^[j] start := hmono (by omega)
    refine ⟨i, ?_⟩
    change f^[i] 5 = _
    omega

end OMA.R_oeis_a007618_R1
