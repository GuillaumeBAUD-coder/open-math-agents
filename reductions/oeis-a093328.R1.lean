import OMAStatements.S_oeis_a093328

-- Reduction oeis-a093328.R1 of A093328: a(n) = 2*n^2 + 3 is never a perfect power.
-- Credit: @PieLord757
-- The square case is proved here (squares mod 9 avoid 2, 3, 5, 8). What remains is the cube case
-- and the case of a prime exponent at least 5. Each H becomes its own step once this file is accepted.

namespace OMA.R_oeis_a093328_R1

/-- The cube case: `2 n^2 + 3` is never a cube. -/
def H1 : Prop := ∀ n k : ℕ, k ^ 3 ≠ 2 * n ^ 2 + 3

/-- Prime exponents at least 5: `2 n^2 + 3` is never a `p`-th power. -/
def H2 : Prop := ∀ n k p : ℕ, p.Prime → 5 ≤ p → k ^ p ≠ 2 * n ^ 2 + 3

lemma sq_ne (n j : ℕ) : j ^ 2 ≠ 2 * n ^ 2 + 3 := by
  intro h
  have h9 : j ^ 2 % 9 = (2 * n ^ 2 + 3) % 9 := by rw [h]
  have hj : j % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hn : n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  rw [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Nat.pow_mod n] at h9
  interval_cases (j % 9) <;> interval_cases (n % 9) <;> norm_num at h9

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a093328.main := by
  intro h1 h2 n hpow
  obtain ⟨k, m, _hk, hm, he⟩ := hpow
  have he' : k ^ m = 2 * n ^ 2 + 3 := he
  have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨t, ht⟩ := Nat.minFac_dvd m
  have hkt : (k ^ t) ^ m.minFac = 2 * n ^ 2 + 3 := by
    rw [← pow_mul, mul_comm, ← ht]; exact he'
  have h2le := hp.two_le
  by_cases hp2 : m.minFac = 2
  · rw [hp2] at hkt; exact sq_ne n (k ^ t) hkt
  by_cases hp3 : m.minFac = 3
  · rw [hp3] at hkt; exact h1 n (k ^ t) hkt
  have hp4 : m.minFac ≠ 4 := by
    intro h4; rw [h4] at hp; exact absurd hp (by norm_num)
  exact h2 n (k ^ t) m.minFac hp (by omega) hkt

end OMA.R_oeis_a093328_R1
