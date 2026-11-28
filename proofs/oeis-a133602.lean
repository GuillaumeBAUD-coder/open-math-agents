import OMAStatements.S_oeis_a133602

-- Problem: A133602: The matrix-vector product A133080 * A000108.
-- Upstream: formal-conjectures statements/oeis-a133602.lean:0 (declaration OMA.S_oeis_a133602.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(m+1) = C(m+1) + [m odd] C(m) (only the last two columns of row m+2 of A133080
-- are nonzero), a(0) = C(0). Split n = 2i+3 and n = 2i+4; all three values are sums of Catalan
-- numbers C(2i), ..., C(2i+3), which are tied by (k+2) C(k+1) = 2 (2k+1) C(k). The identity is
-- then a linear combination of these relations with polynomial coefficients (linear_combination).

namespace P1A133602

open OMA.S_oeis_a133602

theorem ratN (k : ℕ) : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  rw [← h1, ← h2] at h3
  apply Nat.eq_of_mul_eq_mul_left (show 0 < k + 1 by omega)
  calc (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * ((k + 1 + 1) * catalan (k + 1)) := by ring
    _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := h3
    _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by ring

theorem ratZ (k : ℕ) :
    ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
  exact_mod_cast ratN k

theorem a0 : a 0 = catalan 0 := by
  unfold a
  simp [T]

theorem aF (m : ℕ) :
    a (m + 1) = catalan (m + 1) + (if (m + 2) % 2 = 0 then catalan m else 0) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : ∑ k ∈ Finset.range m, T (m + 1 + 1) (k + 1) * catalan k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have hT : T (m + 1 + 1) (k + 1) = 0 := by
      unfold T
      split_ifs <;> omega
    rw [hT, zero_mul]
  have h1 : T (m + 1 + 1) (m + 1 + 1) = 1 := by
    unfold T
    simp
  have h2 : T (m + 1 + 1) (m + 1) = if (m + 2) % 2 = 0 then 1 else 0 := by
    unfold T
    split_ifs <;> omega
  rw [h0, h1, h2]
  split_ifs <;> ring

theorem aEv (j : ℕ) : a (2 * j + 2) = catalan (2 * j + 2) := by
  have h := aF (2 * j + 1)
  rw [if_neg (show ¬((2 * j + 1 + 2) % 2 = 0) by omega), add_zero,
    show 2 * j + 1 + 1 = 2 * j + 2 by ring] at h
  exact h

theorem aOd (j : ℕ) : a (2 * j + 1) = catalan (2 * j + 1) + catalan (2 * j) := by
  have h := aF (2 * j)
  rw [if_pos (show (2 * j + 2) % 2 = 0 by omega)] at h
  exact h

theorem aOd3 (j : ℕ) : a (2 * j + 3) = catalan (2 * j + 3) + catalan (2 * j + 2) := by
  have h := aF (2 * j + 2)
  rw [if_pos (show (2 * j + 2 + 2) % 2 = 0 by omega),
    show 2 * j + 2 + 1 = 2 * j + 3 by ring] at h
  exact h

theorem aE (i : ℕ) : a (2 * i) = catalan (2 * i) := by
  rcases i with _ | j
  · exact a0
  · rw [show 2 * (j + 1) = 2 * j + 2 by ring]
    exact aEv j

end P1A133602

open OMA.S_oeis_a133602 P1A133602 in
theorem OMA.solution : type_of% @OMA.S_oeis_a133602.main := by
  intro n hn
  obtain ⟨i, rfl | rfl⟩ : ∃ i, n = 2 * i + 3 ∨ n = 2 * i + 4 := ⟨(n - 3) / 2, by omega⟩
  · rw [show 2 * i + 3 - 1 = 2 * i + 2 by omega, show 2 * i + 3 - 2 = 2 * i + 1 by omega,
      show 2 * i + 3 - 3 = 2 * i by omega, aEv i, aOd i, aE i]
    have r1 := ratZ (2 * i)
    have r2 := ratZ (2 * i + 1)
    rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring] at r2
    push_cast at r1 r2 ⊢
    linear_combination ((2 * (i : ℤ) + 2) * (2 * i) * (6 * i + 5)) * r2 +
      (-8 * (4 * (i : ℤ) + 1) + 2 * (4 * i + 3) * (2 * i) * (6 * i + 5)) * r1
  · rw [show 2 * i + 4 - 1 = 2 * i + 3 by omega, show 2 * i + 4 - 2 = 2 * i + 2 by omega,
      show 2 * i + 4 - 3 = 2 * i + 1 by omega, aOd3 i, aEv i, aOd i]
    have r1 := ratZ (2 * i)
    have r2 := ratZ (2 * i + 1)
    have r3 := ratZ (2 * i + 2)
    rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring] at r2
    rw [show 2 * i + 2 + 1 = 2 * i + 3 by ring] at r3
    push_cast at r1 r2 r3 ⊢
    linear_combination ((2 * (i : ℤ) + 3) * (2 * i + 1) * (6 * i + 8)) * r3 +
      (4 * ((i : ℤ) + 1) * (30 * i * i + 67 * i + 22)) * r2 +
      (-4 * (6 * (i : ℤ) + 11) * (4 * i + 3) * (4 * i + 1) +
        4 * (4 * i + 3) * (30 * i * i + 67 * i + 22)) * r1
