import OMAStatements.S_oeis_a283107
import Mathlib

/-!
# OEIS A283107: if `σ(4(k-1))` is prime then `τ(4(k-1))` is prime

Write `m = 4(k - 1) = 2^e · u` with `u` odd; then `e ≥ 2`. Since `σ` is multiplicative,
`σ(m) = σ(2^e) σ(u)` with `σ(2^e) = 2^(e+1) - 1 ≥ 7`. If `σ(m)` is prime, then `σ(u) = 1`,
which forces `u = 1`, and `2^(e+1) - 1` is prime, which forces `e + 1` to be prime.
Hence `τ(m) = τ(2^e) = e + 1` is prime.
-/

open ArithmeticFunction

namespace OMA.A283107

/-- `σ(2^e) = 2^(e+1) - 1`. -/
lemma sigma_two_pow (e : ℕ) : sigma 1 (2 ^ e) = 2 ^ (e + 1) - 1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq (le_refl 2)]
  simp

/-- `σ(u) = 1` only for `u = 1` (for positive `u`). -/
lemma eq_one_of_sigma_eq_one {u : ℕ} (hu : u ≠ 0) (h : sigma 1 u = 1) : u = 1 := by
  by_contra hne
  rw [sigma_one_apply] at h
  have hmem : u ∈ u.divisors := Nat.mem_divisors_self u hu
  have h1 : (1 : ℕ) ∈ u.divisors.erase u :=
    Finset.mem_erase.mpr ⟨fun h => hne h.symm, Nat.one_mem_divisors.mpr hu⟩
  have hsum := Finset.add_sum_erase u.divisors (fun d => d) hmem
  have hge : 1 ≤ ∑ d ∈ u.divisors.erase u, d :=
    Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) h1
  have hupos : 0 < u := Nat.pos_of_ne_zero hu
  omega

end OMA.A283107

open OMA.A283107 in
theorem OMA.solution : type_of% @OMA.S_oeis_a283107.main := by
  intro k hk hprime
  -- `4 (k - 1) = 2^e · u` with `u` odd
  obtain ⟨e, u, hodd, hm⟩ := Nat.exists_eq_two_pow_mul_odd (n := 4 * (k - 1)) (by omega)
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact absurd hodd (by decide)
  -- `e ≥ 2`
  have he : 2 ≤ e := by
    obtain ⟨j, rfl⟩ := hodd
    by_contra hlt
    have : e = 0 ∨ e = 1 := by omega
    rcases this with rfl | rfl <;> omega
  have hcop : Nat.Coprime (2 ^ e) u := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
  rw [hm] at hprime ⊢
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_two_pow] at hprime
  -- the first factor is at least `7`, so the second is `1`
  have hbig : 2 ^ (e + 1) - 1 ≠ 1 := by
    have : 2 ^ 3 ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.prime_mul_iff.mp hprime with ⟨hp, hu1⟩ | ⟨-, h1⟩
  · have hu : u = 1 := eq_one_of_sigma_eq_one hu0 hu1
    subst hu
    rw [mul_one, sigma_zero_apply_prime_pow Nat.prime_two]
    exact (Nat.prime_of_pow_sub_one_prime (by omega) hp).2
  · exact absurd h1 hbig
