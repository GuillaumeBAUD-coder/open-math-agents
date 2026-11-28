import OMAReductions.R_oeis_a058887_R1

/-! 271129 is prime (`norm_num`). Covering congruences: 2^24 ≡ 1 modulo each of 3, 5, 7, 13, 17, 241,
and for every residue r of n modulo 24 one of these primes q divides 271129 · 2^r + 1 (checked by
the kernel). So q divides 271129 · 2^n + 1, which is larger than q, hence not prime. -/

namespace OMA.Sierpinski271129

def cover : List ℕ := [3, 5, 7, 13, 17, 241]

theorem base : ∀ r < 24, ∃ q ∈ cover, (271129 * 2 ^ r + 1) % q = 0 ∧ 2 ^ 24 % q = 1 := by
  decide +kernel

theorem reduce (A q n : ℕ) (h : 2 ^ 24 % q = 1) : (A * 2 ^ n) % q = (A * 2 ^ (n % 24)) % q := by
  have hk : 2 ^ n = (2 ^ 24) ^ (n / 24) * 2 ^ (n % 24) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [hk, show A * ((2 ^ 24) ^ (n / 24) * 2 ^ (n % 24)) =
      (A * 2 ^ (n % 24)) * (2 ^ 24) ^ (n / 24) by ring,
    Nat.mul_mod, Nat.pow_mod, h, one_pow, ← Nat.mul_mod, mul_one]

end OMA.Sierpinski271129

theorem OMA.solution : OMA.R_oeis_a058887_R1.H1 := by
  unfold OMA.R_oeis_a058887_R1.H1 OMA.S_oeis_a058887.IsSierpinski
  refine ⟨by norm_num, ⟨135564, by norm_num⟩, fun n hn hp => ?_⟩
  obtain ⟨q, hq, h1, h2⟩ := OMA.Sierpinski271129.base (n % 24) (Nat.mod_lt _ (by norm_num))
  have hmod : (271129 * 2 ^ n + 1) % q = 0 := by
    rw [Nat.add_mod, OMA.Sierpinski271129.reduce _ _ _ h2, ← Nat.add_mod]
    exact h1
  have hq3 : 3 ≤ q ∧ q ≤ 241 := by
    simp only [OMA.Sierpinski271129.cover, List.mem_cons, List.not_mem_nil, or_false] at hq
    omega
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hge : 271129 * 2 ≤ 271129 * 2 ^ n := Nat.mul_le_mul_left _ h2n
  rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega
