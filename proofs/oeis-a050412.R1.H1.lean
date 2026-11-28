import OMAReductions.R_oeis_a050412_R1

/-! Covering congruences: 2^24 ≡ 1 modulo each of 3, 5, 7, 13, 17, 241, and for every residue
r of k modulo 24 one of these primes q satisfies 509203 · 2^r ≡ 1 (mod q) (checked by the kernel).
So q divides 509203 · 2^k - 1, which is larger than q, hence not prime. -/

namespace OMA.Riesel509203

def cover : List ℕ := [3, 5, 7, 13, 17, 241]

theorem base : ∀ r < 24, ∃ q ∈ cover, (509203 * 2 ^ r) % q = 1 ∧ 2 ^ 24 % q = 1 := by
  decide +kernel

theorem reduce (A q n : ℕ) (h : 2 ^ 24 % q = 1) : (A * 2 ^ n) % q = (A * 2 ^ (n % 24)) % q := by
  have hk : 2 ^ n = (2 ^ 24) ^ (n / 24) * 2 ^ (n % 24) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [hk, show A * ((2 ^ 24) ^ (n / 24) * 2 ^ (n % 24)) =
      (A * 2 ^ (n % 24)) * (2 ^ 24) ^ (n / 24) by ring,
    Nat.mul_mod, Nat.pow_mod, h, one_pow, ← Nat.mul_mod, mul_one]

end OMA.Riesel509203

theorem OMA.solution : OMA.R_oeis_a050412_R1.H1 := by
  unfold OMA.R_oeis_a050412_R1.H1 OMA.S_oeis_a050412.IsRiesel
  refine ⟨⟨254601, by norm_num⟩, fun k hk hp => ?_⟩
  obtain ⟨q, hq, h1, h2⟩ := OMA.Riesel509203.base (k % 24) (Nat.mod_lt _ (by norm_num))
  have hmod : (509203 * 2 ^ k) % q = 1 := by
    rw [OMA.Riesel509203.reduce _ _ _ h2]
    exact h1
  have hq3 : 3 ≤ q ∧ q ≤ 241 := by
    simp only [OMA.Riesel509203.cover, List.mem_cons, List.not_mem_nil, or_false] at hq
    omega
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hge : 509203 * 2 ≤ 509203 * 2 ^ k := Nat.mul_le_mul_left _ h2k
  have hdvd : q ∣ 509203 * 2 ^ k - 1 := by
    have h1q : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
    exact (Nat.modEq_iff_dvd' (by omega)).1 (by unfold Nat.ModEq; rw [h1q, hmod])
  rcases hp.eq_one_or_self_of_dvd q hdvd with h | h <;> omega
