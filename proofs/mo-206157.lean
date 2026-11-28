import OMAStatements.S_mo_206157
import Mathlib

-- Problem mo-206157: for every prime p >= 13 and every k with 1 <= k <= 4, the number floor((p^2 - 1) / 2^k)
-- is not prime.
-- Upstream: statements/mo-206157.lean (declaration OMA.S_mo_206157.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: p is odd; write p = 8 u + r with r in {1, 3, 5, 7}.
--   r = 1: p^2 - 1 = 16 X with X = u (4u + 1);         r = 7: p^2 - 1 = 16 X with X = (u + 1)(4u + 3);
--   r = 3: p^2 - 1 = 16 X + 8 with X = u (4u + 3);     r = 5: p^2 - 1 = 16 X + 8 with X = (u + 1)(4u + 1).
-- If p^2 - 1 = 16 X, the quotients for k = 1, 2, 3, 4 are 8 X, 4 X, 2 X and X. If p^2 - 1 = 16 X + 8, they are
-- 4 (2X + 1), 2 (2X + 1), 2X + 1 and X, where 2X + 1 = (2u + 1)(4u + 1) for r = 3 and (2u + 1)(4u + 3) for
-- r = 5. Since p >= 13, all the factors shown are at least 2, so every quotient is composite.

private lemma case0 (X k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hX : 2 ≤ X) (h4 : ¬ X.Prime) :
    ¬ (16 * X / 2 ^ k).Prime := by
  have p1 : (2 : ℕ) ^ 1 = 2 := by norm_num
  have p2 : (2 : ℕ) ^ 2 = 4 := by norm_num
  have p3 : (2 : ℕ) ^ 3 = 8 := by norm_num
  have p4 : (2 : ℕ) ^ 4 = 16 := by norm_num
  interval_cases k
  · rw [p1, show 16 * X / 2 = 8 * X by omega]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [p2, show 16 * X / 4 = 4 * X by omega]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [p3, show 16 * X / 8 = 2 * X by omega]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [p4, show 16 * X / 16 = X by omega]
    exact h4

private lemma case8 (X k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hX : 1 ≤ X) (h3 : ¬ (2 * X + 1).Prime)
    (h4 : ¬ X.Prime) : ¬ ((16 * X + 8) / 2 ^ k).Prime := by
  have p1 : (2 : ℕ) ^ 1 = 2 := by norm_num
  have p2 : (2 : ℕ) ^ 2 = 4 := by norm_num
  have p3 : (2 : ℕ) ^ 3 = 8 := by norm_num
  have p4 : (2 : ℕ) ^ 4 = 16 := by norm_num
  interval_cases k
  · rw [p1, show (16 * X + 8) / 2 = 4 * (2 * X + 1) by omega]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [p2, show (16 * X + 8) / 4 = 2 * (2 * X + 1) by omega]
    exact Nat.not_prime_mul (by omega) (by omega)
  · rw [p3, show (16 * X + 8) / 8 = 2 * X + 1 by omega]
    exact h3
  · rw [p4, show (16 * X + 8) / 16 = X by omega]
    exact h4

private lemma np_mul {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : ¬ (a * b).Prime :=
  Nat.not_prime_mul (by omega) (by omega)

theorem OMA.solution : type_of% @OMA.S_mo_206157.main := by
  intro p hp h13 k hk1 hk4
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases hr with hr | hr | hr | hr
  · obtain ⟨u, hu⟩ : ∃ u, p = 8 * u + 1 := ⟨p / 8, by omega⟩
    have hu2 : 2 ≤ u := by omega
    have hX : 2 ≤ u * (4 * u + 1) := by
      have := Nat.mul_le_mul hu2 (show 1 ≤ 4 * u + 1 by omega)
      omega
    have e : p ^ 2 - 1 = 16 * (u * (4 * u + 1)) := by
      have h : p ^ 2 = 16 * (u * (4 * u + 1)) + 1 := by
        rw [hu]
        ring
      omega
    rw [e]
    exact case0 _ k hk1 hk4 hX (np_mul hu2 (by omega))
  · obtain ⟨u, hu⟩ : ∃ u, p = 8 * u + 3 := ⟨p / 8, by omega⟩
    have hu2 : 2 ≤ u := by omega
    have hX : 1 ≤ u * (4 * u + 3) := by
      have := Nat.mul_le_mul hu2 (show 1 ≤ 4 * u + 3 by omega)
      omega
    have e : p ^ 2 - 1 = 16 * (u * (4 * u + 3)) + 8 := by
      have h : p ^ 2 = 16 * (u * (4 * u + 3)) + 9 := by
        rw [hu]
        ring
      omega
    have e3 : 2 * (u * (4 * u + 3)) + 1 = (2 * u + 1) * (4 * u + 1) := by ring
    rw [e]
    refine case8 _ k hk1 hk4 hX ?_ (np_mul hu2 (by omega))
    rw [e3]
    exact np_mul (by omega) (by omega)
  · obtain ⟨u, hu⟩ : ∃ u, p = 8 * u + 5 := ⟨p / 8, by omega⟩
    have hu1 : 1 ≤ u := by omega
    have hX : 1 ≤ (u + 1) * (4 * u + 1) := by
      have := Nat.mul_le_mul (show 1 ≤ u + 1 by omega) (show 1 ≤ 4 * u + 1 by omega)
      omega
    have e : p ^ 2 - 1 = 16 * ((u + 1) * (4 * u + 1)) + 8 := by
      have h : p ^ 2 = 16 * ((u + 1) * (4 * u + 1)) + 9 := by
        rw [hu]
        ring
      omega
    have e3 : 2 * ((u + 1) * (4 * u + 1)) + 1 = (2 * u + 1) * (4 * u + 3) := by ring
    rw [e]
    refine case8 _ k hk1 hk4 hX ?_ (np_mul (by omega) (by omega))
    rw [e3]
    exact np_mul (by omega) (by omega)
  · obtain ⟨u, hu⟩ : ∃ u, p = 8 * u + 7 := ⟨p / 8, by omega⟩
    have hu1 : 1 ≤ u := by omega
    have hX : 2 ≤ (u + 1) * (4 * u + 3) := by
      have := Nat.mul_le_mul (show 2 ≤ u + 1 by omega) (show 1 ≤ 4 * u + 3 by omega)
      omega
    have e : p ^ 2 - 1 = 16 * ((u + 1) * (4 * u + 3)) := by
      have h : p ^ 2 = 16 * ((u + 1) * (4 * u + 3)) + 1 := by
        rw [hu]
        ring
      omega
    rw [e]
    exact case0 _ k hk1 hk4 hX (np_mul (by omega) (by omega))
