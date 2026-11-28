import OMAStatements.S_mo_201980
import Mathlib

-- Problem mo-201980: the statement claims that for some k in {4, 7, 8} and some n >= 4 there are positive
-- integers x, y, z with x^n + y^n + z^n = k x y z.
-- Upstream: statements/mo-201980.lean (declaration OMA.S_mo_201980.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: there are none. Let a be the largest of x, y, z. Then a^n <= x^n + y^n + z^n = k x y z <= 8 a^3.
-- Since n >= 4 this gives a^4 <= 8 a^3, so a <= 8; and if a >= 2 then 2^n <= a^n <= 8 * 8^3 = 2^12, so
-- n <= 12. If a = 1 then x = y = z = 1 and the equation reads 3 = k, which is not in {4, 7, 8}. Otherwise
-- 1 <= x, y, z <= 8 and 4 <= n <= 12, a finite range that is checked exhaustively.

private lemma bound (a n k : ℕ) (ha : 0 < a) (hk : k ≤ 8) (hn : 4 ≤ n) (h : a ^ n ≤ k * (a * a * a)) :
    a ≤ 8 ∧ (2 ≤ a → n ≤ 12) := by
  have h8 : a ^ n ≤ 8 * (a * a * a) := le_trans h (Nat.mul_le_mul_right _ hk)
  have h4 : a ^ 4 ≤ a ^ n := Nat.pow_le_pow_right ha hn
  have hpos : 0 < a * a * a := Nat.mul_pos (Nat.mul_pos ha ha) ha
  have ha8 : a ≤ 8 := by
    have e : a ^ 4 = a * (a * a * a) := by ring
    have h5 : a * (a * a * a) ≤ 8 * (a * a * a) := by
      rw [← e]
      exact le_trans h4 h8
    exact Nat.le_of_mul_le_mul_right h5 hpos
  refine ⟨ha8, fun h2 => ?_⟩
  have h6 : 2 ^ n ≤ a ^ n := Nat.pow_le_pow_left h2 n
  have h7 : a * a * a ≤ 8 * 8 * 8 := Nat.mul_le_mul (Nat.mul_le_mul ha8 ha8) ha8
  have h9 : 2 ^ n ≤ 2 ^ 12 := by
    calc 2 ^ n ≤ a ^ n := h6
      _ ≤ 8 * (a * a * a) := h8
      _ ≤ 8 * (8 * 8 * 8) := Nat.mul_le_mul_left 8 h7
      _ = 2 ^ 12 := by norm_num
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h9

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_201980.main) := by
  rintro ⟨k, hk, n, hn, x, y, z, hx, hy, hz, heq⟩
  have hk' : k = 4 ∨ k = 7 ∨ k = 8 := by simpa using hk
  have hk8 : k ≤ 8 := by omega
  have hfin : ∀ x ∈ Finset.Icc 1 8, ∀ y ∈ Finset.Icc 1 8, ∀ z ∈ Finset.Icc 1 8,
      ∀ n ∈ Finset.Icc 4 12, ∀ k ∈ ({4, 7, 8} : Finset ℕ),
      x ^ n + y ^ n + z ^ n ≠ k * x * y * z := by decide +kernel
  obtain ⟨a, ha, hxa, hya, hza, hpow⟩ :
      ∃ a, 0 < a ∧ x ≤ a ∧ y ≤ a ∧ z ≤ a ∧ a ^ n ≤ x ^ n + y ^ n + z ^ n := by
    rcases (by omega : (y ≤ x ∧ z ≤ x) ∨ (x ≤ y ∧ z ≤ y) ∨ (x ≤ z ∧ y ≤ z)) with h | h | h
    · exact ⟨x, hx, le_refl _, h.1, h.2, by omega⟩
    · exact ⟨y, hy, h.1, le_refl _, h.2, by omega⟩
    · exact ⟨z, hz, h.1, h.2, le_refl _, by omega⟩
  have hprod : k * x * y * z ≤ k * (a * a * a) := by
    have h1 : k * x * y * z ≤ k * a * a * a :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left k hxa) hya) hza
    have e : k * a * a * a = k * (a * a * a) := by ring
    rw [← e]
    exact h1
  have hle : a ^ n ≤ k * (a * a * a) := by
    rw [heq] at hpow
    exact le_trans hpow hprod
  obtain ⟨ha8, hn12⟩ := bound a n k ha hk8 hn hle
  by_cases h2 : 2 ≤ a
  · have hn' := hn12 h2
    exact hfin x (Finset.mem_Icc.mpr ⟨hx, by omega⟩) y (Finset.mem_Icc.mpr ⟨hy, by omega⟩)
      z (Finset.mem_Icc.mpr ⟨hz, by omega⟩) n (Finset.mem_Icc.mpr ⟨hn, hn'⟩) k hk heq
  · have hx1 : x = 1 := by omega
    have hy1 : y = 1 := by omega
    have hz1 : z = 1 := by omega
    rw [hx1, hy1, hz1] at heq
    simp only [one_pow, mul_one] at heq
    omega
