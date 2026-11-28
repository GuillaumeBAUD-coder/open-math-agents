import OMAStatements.S_oeis_a243662

-- Problem: A243662: Triangle read by rows: the reversed x = 1+q Narayana triangle at m=2.
-- Upstream: formal-conjectures statements/oeis-a243662.lean:0 (declaration OMA.S_oeis_a243662.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: put k = j+1, n = j+l+1, write every binomial as a quotient of factorials, use
-- (3n+1)! = (3n+1)(3n)!, n! = n(n-1)!, (l+1)! = (l+1) l!, (2n+1)! = (2n+1)(2n)!, and close both
-- rational identities with the field tactic.

open OMA.S_oeis_a243662 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243662.main := by
  intro n k hk hkn
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, n = j + l + 1 := ⟨n - (j + 1), by omega⟩
  unfold T A001764 A001263
  rw [show 3 * (j + l + 1) + 1 - (j + 1) = 2 * j + 3 * l + 3 by omega,
    show j + l + 1 - (j + 1) = l by omega, show j + 1 - 1 = j by omega,
    show j + l + 1 - 1 = j + l by omega]
  have e1 : ((2 * j + 3 * l + 3).choose l : ℚ)
      = (Nat.factorial (2 * j + 3 * l + 3) : ℚ)
        / ((Nat.factorial l : ℚ) * (Nat.factorial (2 * j + 2 * l + 3) : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : l ≤ 2 * j + 3 * l + 3),
      show 2 * j + 3 * l + 3 - l = 2 * j + 2 * l + 3 by omega]
  have e2 : ((j + l + 1).choose j : ℚ)
      = (Nat.factorial (j + l + 1) : ℚ)
        / ((Nat.factorial j : ℚ) * (Nat.factorial (l + 1) : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : j ≤ j + l + 1), show j + l + 1 - j = l + 1 by omega]
  have e3 : ((3 * (j + l + 1) + 1).choose (j + l + 1) : ℚ)
      = (Nat.factorial (3 * (j + l + 1) + 1) : ℚ)
        / ((Nat.factorial (j + l + 1) : ℚ) * (Nat.factorial (2 * j + 2 * l + 3) : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : j + l + 1 ≤ 3 * (j + l + 1) + 1),
      show 3 * (j + l + 1) + 1 - (j + l + 1) = 2 * j + 2 * l + 3 by omega]
  have e4 : ((j + l).choose j : ℚ)
      = (Nat.factorial (j + l) : ℚ) / ((Nat.factorial j : ℚ) * (Nat.factorial l : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : j ≤ j + l), show j + l - j = l by omega]
  have e5 : ((3 * (j + l + 1)).choose j : ℚ)
      = (Nat.factorial (3 * (j + l + 1)) : ℚ)
        / ((Nat.factorial j : ℚ) * (Nat.factorial (2 * j + 3 * l + 3) : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : j ≤ 3 * (j + l + 1)),
      show 3 * (j + l + 1) - j = 2 * j + 3 * l + 3 by omega]
  have e6 : ((3 * (j + l + 1)).choose (j + l + 1) : ℚ)
      = (Nat.factorial (3 * (j + l + 1)) : ℚ)
        / ((Nat.factorial (j + l + 1) : ℚ) * (Nat.factorial (2 * j + 2 * l + 2) : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : j + l + 1 ≤ 3 * (j + l + 1)),
      show 3 * (j + l + 1) - (j + l + 1) = 2 * j + 2 * l + 2 by omega]
  have f1 : (Nat.factorial (3 * (j + l + 1) + 1) : ℚ)
      = ((3 * (j + l + 1) + 1 : ℕ) : ℚ) * (Nat.factorial (3 * (j + l + 1)) : ℚ) := by
    exact_mod_cast Nat.factorial_succ (3 * (j + l + 1))
  have f2 : (Nat.factorial (j + l + 1) : ℚ)
      = ((j + l + 1 : ℕ) : ℚ) * (Nat.factorial (j + l) : ℚ) := by
    exact_mod_cast Nat.factorial_succ (j + l)
  have f3 : (Nat.factorial (l + 1) : ℚ) = ((l + 1 : ℕ) : ℚ) * (Nat.factorial l : ℚ) := by
    exact_mod_cast Nat.factorial_succ l
  have f4 : (Nat.factorial (2 * j + 2 * l + 3) : ℚ)
      = ((2 * j + 2 * l + 3 : ℕ) : ℚ) * (Nat.factorial (2 * j + 2 * l + 2) : ℚ) := by
    have h := Nat.factorial_succ (2 * j + 2 * l + 2)
    rw [show 2 * j + 2 * l + 2 + 1 = 2 * j + 2 * l + 3 by omega] at h
    exact_mod_cast h
  rw [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4]
  push_cast
  constructor
  · field
  · field
