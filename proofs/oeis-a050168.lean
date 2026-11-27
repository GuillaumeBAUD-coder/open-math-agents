import OMAStatements.S_oeis_a050168

-- Problem: A050168: a(0) = 1; for n > 0, a(n) = binomial(n, floor(n/2)) + binomial(n-1, floor(n/2)).
-- Upstream: formal-conjectures statements/oeis-a050168.lean:0 (declaration OMA.S_oeis_a050168.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with c(k) = C(2k,k): 2 a(2k+2) = 3 c(k+1), (k+1) a(2k+1) = (3k+2) c(k), (k+1) c(k+1) = 2(2k+1) c(k); n = 3 by decide, n >= 4 by parity and linear_combination.

open OMA.S_oeis_a050168 in
theorem OMA.solution : type_of% @OMA.S_oeis_a050168.main := by
  have hA : ∀ k : ℕ, 2 * a (2 * k + 2) = 3 * (Nat.centralBinom (k + 1) : ℤ) := by
    intro k
    have h1 : (2 * k + 2).choose (k + 1) = (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) :=
      Nat.choose_succ_succ' (2 * k + 1) k
    have h2 : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k := Nat.choose_symm_half k
    have h3 : Nat.centralBinom (k + 1) = (2 * k + 2).choose (k + 1) := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (k + 1) = 2 * k + 2 by ring]
    unfold a
    rw [if_neg (show ¬(2 * k + 2 = 0) by omega), show (2 * k + 2) / 2 = k + 1 by omega,
      show 2 * k + 2 - 1 = 2 * k + 1 by omega, h3, h1, h2]
    push_cast
    ring
  have hB : ∀ k : ℕ,
      ((k : ℤ) + 1) * a (2 * k + 1) = (3 * (k : ℤ) + 2) * (Nat.centralBinom k : ℤ) := by
    intro k
    have h4 : (2 * k + 1) * (2 * k).choose k = (2 * k + 1).choose (k + 1) * (k + 1) :=
      Nat.add_one_mul_choose_eq (2 * k) k
    have h6 : (2 * k + 1).choose k * (k + 1) = (2 * k + 1) * (2 * k).choose k := by
      rw [← Nat.choose_symm_half k]
      exact h4.symm
    have h7 : ((2 * k + 1).choose k : ℤ) * ((k : ℤ) + 1)
        = (2 * (k : ℤ) + 1) * ((2 * k).choose k : ℤ) := by
      exact_mod_cast h6
    unfold a
    rw [if_neg (show ¬(2 * k + 1 = 0) by omega), show (2 * k + 1) / 2 = k by omega,
      show 2 * k + 1 - 1 = 2 * k by omega, Nat.centralBinom_eq_two_mul_choose]
    linear_combination h7
  have hC : ∀ k : ℕ, ((k : ℤ) + 1) * (Nat.centralBinom (k + 1) : ℤ)
      = 2 * (2 * (k : ℤ) + 1) * (Nat.centralBinom k : ℤ) := by
    intro k
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  intro n hn
  obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, n = 3 ∨ n = 2 * m + 4 ∨ n = 2 * m + 5 :=
    ⟨(n - 4) / 2, by omega⟩
  · decide
  · have A1 : 2 * a (2 * m + 4) = 3 * (Nat.centralBinom (m + 2) : ℤ) := by
      have h := hA (m + 1)
      rw [show 2 * (m + 1) + 2 = 2 * m + 4 by omega, show m + 1 + 1 = m + 2 by omega] at h
      exact h
    have B1 : ((m : ℤ) + 2) * a (2 * m + 3) = (3 * (m : ℤ) + 5) * (Nat.centralBinom (m + 1) : ℤ) := by
      have h := hB (m + 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega] at h
      push_cast at h
      linear_combination h
    have C1 : ((m : ℤ) + 2) * (Nat.centralBinom (m + 2) : ℤ)
        = 2 * (2 * (m : ℤ) + 3) * (Nat.centralBinom (m + 1) : ℤ) := by
      have h := hC (m + 1)
      rw [show m + 1 + 1 = m + 2 by omega] at h
      push_cast at h
      linear_combination h
    have A0 := hA m
    have B0 := hB m
    have C0 := hC m
    have hM : (2 * ((m : ℤ) + 1) * ((m : ℤ) + 2)) ≠ 0 := by positivity
    rw [show 2 * m + 4 - 1 = 2 * m + 3 by omega, show 2 * m + 4 - 2 = 2 * m + 2 by omega,
      show 2 * m + 4 - 3 = 2 * m + 1 by omega]
    refine (mul_eq_zero.mp ?_).resolve_left hM
    push_cast
    linear_combination ((m : ℤ) + 1) * ((m : ℤ) + 2) * (2 * (m : ℤ) + 5) * A1
      + 2 * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) * B1
      - 2 * ((m : ℤ) + 1) * ((m : ℤ) + 2) * (4 * (m : ℤ) + 7) * A0
      - 8 * ((m : ℤ) + 2) * (2 * (m : ℤ) + 1) * B0
      + 3 * ((m : ℤ) + 1) * (2 * (m : ℤ) + 5) * C1
      + 4 * ((m : ℤ) + 2) * (3 * (m : ℤ) + 2) * C0
  · have A1 : 2 * a (2 * m + 4) = 3 * (Nat.centralBinom (m + 2) : ℤ) := by
      have h := hA (m + 1)
      rw [show 2 * (m + 1) + 2 = 2 * m + 4 by omega, show m + 1 + 1 = m + 2 by omega] at h
      exact h
    have B1 : ((m : ℤ) + 2) * a (2 * m + 3) = (3 * (m : ℤ) + 5) * (Nat.centralBinom (m + 1) : ℤ) := by
      have h := hB (m + 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega] at h
      push_cast at h
      linear_combination h
    have B2 : ((m : ℤ) + 3) * a (2 * m + 5) = (3 * (m : ℤ) + 8) * (Nat.centralBinom (m + 2) : ℤ) := by
      have h := hB (m + 2)
      rw [show 2 * (m + 2) + 1 = 2 * m + 5 by omega] at h
      push_cast at h
      linear_combination h
    have C1 : ((m : ℤ) + 2) * (Nat.centralBinom (m + 2) : ℤ)
        = 2 * (2 * (m : ℤ) + 3) * (Nat.centralBinom (m + 1) : ℤ) := by
      have h := hC (m + 1)
      rw [show m + 1 + 1 = m + 2 by omega] at h
      push_cast at h
      linear_combination h
    have A0 := hA m
    have hM : ((m : ℤ) + 2) ≠ 0 := by positivity
    rw [show 2 * m + 5 - 1 = 2 * m + 4 by omega, show 2 * m + 5 - 2 = 2 * m + 3 by omega,
      show 2 * m + 5 - 3 = 2 * m + 2 by omega]
    refine (mul_eq_zero.mp ?_).resolve_left hM
    push_cast
    linear_combination 2 * ((m : ℤ) + 2) * B2 + ((m : ℤ) + 2) * ((m : ℤ) + 1) * A1
      - 2 * (4 * (m : ℤ) + 9) * B1 - 4 * ((m : ℤ) + 2) * ((m : ℤ) + 1) * A0
      + (9 * (m : ℤ) + 19) * C1
