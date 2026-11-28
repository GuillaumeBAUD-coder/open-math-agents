import OMAStatements.S_oeis_a001917
import Mathlib.Tactic

namespace A001917

-- The three failed powers rule out all proper divisors of 364 as orders.
private lemma order_certificate (m : ℕ)
    (top : 2^364 % m = 1 % m)
    (h2 : 2^182 % m ≠ 1 % m)
    (h7 : 2^52 % m ≠ 1 % m)
    (h13 : 2^28 % m ≠ 1 % m) : orderOf (2 : ZMod m) = 364 := by
  have cast_pow (e : ℕ) :
      (2 : ZMod m)^e = 1 ↔ 2^e % m = 1 % m := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff' (2^e) 1 m)
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) ((cast_pow 364).2 top)
  intro p hp hdvd
  have hm := hp.mem_primeFactors hdvd (by decide : (364 : ℕ) ≠ 0)
  rw [show (364 : ℕ).primeFactors = ({2, 7, 13} : Finset ℕ) by decide +kernel] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with (rfl | rfl | rfl)
  · exact mt (cast_pow 182).1 h2
  · exact mt (cast_pow 52).1 h7
  · exact mt (cast_pow 28).1 h13

private lemma cosets_lower_bound (m : ℕ) (hm : 1 < m) :
    m.totient / orderOf (2 : ZMod m) ≤ OMA.S_oeis_a001917.cosets m := by
  unfold OMA.S_oeis_a001917.cosets
  exact Finset.single_le_sum (fun d _ => Nat.zero_le (d.totient / orderOf (2 : ZMod d)))
    (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩, hm⟩)


private lemma disproof_of_certificate {p v : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) (hv : 0 < v)
    (ord : orderOf (2 : ZMod p) = v)
    (ordSq : orderOf (2 : ZMod (p^2)) = v)
    (hsix : (p - 1) / v = 3)
    (hlarge : 7 * v ≤ p * (p - 1)) :
    ¬ (type_of% @OMA.S_oeis_a001917.main) := by
  open OMA.S_oeis_a001917 in
  intro h
  have hbound : 7 ≤ cosets (p^2) := by
    have hsmall : 7 ≤ (p^2).totient / orderOf (2 : ZMod (p^2)) := by
      rw [ordSq, Nat.totient_prime_pow_succ hp 1, pow_one, Nat.le_div_iff_mul_le hv]
      exact hlarge
    exact hsmall.trans (cosets_lower_bound _ (by exact one_lt_pow₀ (by omega) (by decide)))
  have he := h p 2 hp (by omega) (by decide)
  rw [primeTerm, ord, hsix] at he
  omega

end A001917

open OMA.S_oeis_a001917 A001917 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001917.main) := by
  have hp : Nat.Prime 1093 := by decide +kernel
  have h1 : orderOf (2 : ZMod 1093) = 364 :=
    order_certificate _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have h2 : orderOf (2 : ZMod (1093^2)) = 364 :=
    order_certificate _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  exact disproof_of_certificate hp (by decide) (by decide) h1 h2 (by norm_num) (by norm_num)
