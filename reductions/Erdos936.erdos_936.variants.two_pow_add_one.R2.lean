import FormalConjectures.ErdosProblems.«936»
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum.Prime

-- Credit: @thegeomain

/-!
Congruence reduction for Erdős Problem 936.
For each of three two-adic cases, require specific prime divisors of the exponent before testing
whether the corresponding value can be powerful. The remaining large two-adic valuations form
the fourth case.
-/

namespace OMA.R_Erdos936_erdos_936_variants_two_pow_add_one_R2


private lemma prime_pow_dvd_odd_power_add_one_iff {p x m : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hpd : p ∣ x + 1) (hmo : Odd m) (hpm : ¬p ∣ m)
    (j : ℕ) : p^j ∣ x^m + 1 ↔ p^j ∣ x + 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpx : ¬p ∣ x := by
    intro hd
    have h := Nat.dvd_sub hpd hd
    exact hp.not_dvd_one (by simpa using h)
  have hval : padicValNat p (x^m + 1) = padicValNat p (x + 1) := by
    simpa [padicValNat.eq_zero_of_not_dvd hpm] using
      padicValNat.pow_add_pow (p := p) (x := x) (y := 1) hpo hpd hpx hmo
  rw [Nat.pow_dvd_iff_le_padicValNat hp.ne_one (Nat.succ_ne_zero (x^m)),
      Nat.pow_dvd_iff_le_padicValNat hp.ne_one (Nat.succ_ne_zero x), hval]

private lemma prime_square_obstruction_for_odd_power {p d m : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hpd : p ∣ 2^d + 1) (hps : ¬p^2 ∣ 2^d + 1)
    (hmo : Odd m) (hpm : ¬p ∣ m) :
    p ∣ 2^(d*m) + 1 ∧ ¬p^2 ∣ 2^(d*m) + 1 := by
  rw [pow_mul]
  constructor
  · simpa using (prime_pow_dvd_odd_power_add_one_iff hp hpo hpd hmo hpm 1).mpr
      (by simpa using hpd)
  · exact fun hd => hps ((prime_pow_dvd_odd_power_add_one_iff hp hpo hpd hmo hpm 2).mp hd)

private lemma not_powerful_of_odd_power_prime_obstruction {p d m : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hpd : p ∣ 2^d + 1) (hps : ¬p^2 ∣ 2^d + 1)
    (hmo : Odd m) (hpm : ¬p ∣ m) : ¬(2^(d*m) + 1 : ℕ).Powerful := by
  obtain ⟨hd, hs⟩ := prime_square_obstruction_for_odd_power hp hpo hpd hps hmo hpm
  intro h
  exact hs (h p (hp.mem_primeFactors hd (Nat.succ_ne_zero _)))


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma seed_prime_174763 : Nat.Prime 174763 := by norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma seed_prime_10169 : Nat.Prime 10169 := by norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma seed_prime_354689 : Nat.Prime 354689 := by norm_num

private lemma forced_prime_from_seed {n d p : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hdn : d ∣ n) (hq : Odd (n / d))
    (hpd : p ∣ 2^d + 1) (hps : ¬ p^2 ∣ 2^d + 1)
    (hpower : (2^n + 1 : ℕ).Powerful) : p ∣ n := by
  have he : d * (n / d) = n := Nat.mul_div_cancel' hdn
  by_contra hnp
  have hqnp : ¬ p ∣ n / d := fun h => hnp (he ▸ dvd_mul_of_dvd_right h d)
  have hbad := not_powerful_of_odd_power_prime_obstruction hp hpo hpd hps hq hqnp
  rw [he] at hbad
  exact hbad hpower

private lemma odd_exponent_forces_three {n : ℕ} (hn : Odd n)
    (hpower : (2^n + 1 : ℕ).Powerful) : 3 ∣ n := by
  exact forced_prime_from_seed (d := 1) (by decide) (by decide) (one_dvd _) (by simpa using hn)
    (by decide) (by decide) hpower

private lemma odd_quotient_of_dvd {n d : ℕ} (hn : Odd n) (hd : d ∣ n) : Odd (n / d) := by
  have h : Odd (d * (n / d)) := (Nat.mul_div_cancel' hd).symm ▸ hn
  exact (Nat.odd_mul.mp h).2

private lemma odd_multiple_nine_forces_factors {n : ℕ} (hn : Odd n) (h9 : 9 ∣ n)
    (hpower : (2^n + 1 : ℕ).Powerful) : 19 ∣ n ∧ 174763 ∣ n := by
  have h19 : 19 ∣ n := forced_prime_from_seed (d := 9) (by decide) (by decide) h9
    (odd_quotient_of_dvd hn h9) (by decide) (by decide) hpower
  exact ⟨h19, forced_prime_from_seed (d := 19) seed_prime_174763 (by decide) h19
    (odd_quotient_of_dvd hn h19) (by decide) (by decide) hpower⟩

private lemma v2_one_forces_factors {n : ℕ} (hn : n % 4 = 2)
    (hpower : (2^n + 1 : ℕ).Powerful) : 5 ∣ n ∧ 41 ∣ n ∧ 10169 ∣ n := by
  have h2 : 2 ∣ n := by omega
  have hodd : Odd (n / 2) := Nat.odd_iff.mpr (by omega)
  have h5 : 5 ∣ n := forced_prime_from_seed (d := 2) (by decide) (by decide) h2 hodd
    (by decide) (by decide) hpower
  have h10 : 10 ∣ n := (show Nat.Coprime 2 5 by decide).mul_dvd_of_dvd_of_dvd h2 h5
  have hodd10 : Odd (n / 10) := by
    refine Nat.odd_iff.mpr ?_
    omega
  have h41 : 41 ∣ n := forced_prime_from_seed (d := 10) (by decide) (by decide)
    h10 hodd10 (by decide) (by decide) hpower
  have h82 : 82 ∣ n := (show Nat.Coprime 2 41 by decide).mul_dvd_of_dvd_of_dvd h2 h41
  have hodd82 : Odd (n / 82) := by
    refine Nat.odd_iff.mpr ?_
    omega
  exact ⟨h5, h41, forced_prime_from_seed (d := 82) seed_prime_10169 (by decide)
    h82 hodd82 (by decide) (by decide) hpower⟩

private lemma v2_two_forces_factors {n : ℕ} (hn : n % 8 = 4)
    (hpower : (2^n + 1 : ℕ).Powerful) : 17 ∣ n ∧ 354689 ∣ n := by
  have h4 : 4 ∣ n := by omega
  have hodd : Odd (n / 4) := Nat.odd_iff.mpr (by omega)
  have h17 : 17 ∣ n := forced_prime_from_seed (d := 4) (by decide) (by decide) h4 hodd
    (by decide) (by decide) hpower
  have h68 : 68 ∣ n := (show Nat.Coprime 4 17 by decide).mul_dvd_of_dvd_of_dvd h4 h17
  have hodd68 : Odd (n / 68) := Nat.odd_iff.mpr (by omega)
  exact ⟨h17, forced_prime_from_seed (d := 68) seed_prime_354689 (by decide) h68 hodd68
    (by decide) (by decide) hpower⟩



open Filter

/-- The remaining odd exponents are multiples of three, with two extra factors if nine divides. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop,
  Odd n → 3 ∣ n → (9 ∣ n → 19 ∣ n ∧ 174763 ∣ n) → ¬ (2^n + 1 : ℕ).Powerful

/-- The remaining exponents with two-adic valuation one have three prescribed odd factors. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop,
  n % 4 = 2 → (5 ∣ n ∧ 41 ∣ n ∧ 10169 ∣ n) → ¬ (2^n + 1 : ℕ).Powerful

/-- The remaining exponents with two-adic valuation two have two prescribed odd factors. -/
def H3 : Prop := ∀ᶠ n : ℕ in atTop,
  n % 8 = 4 → (17 ∣ n ∧ 354689 ∣ n) → ¬ (2^n + 1 : ℕ).Powerful

/-- The remaining case of exponents divisible by eight. -/
def H4 : Prop := ∀ᶠ n : ℕ in atTop, 8 ∣ n → ¬ (2^n + 1 : ℕ).Powerful

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos936.erdos_936.variants.two_pow_add_one := by
  intro h1 h2 h3 h4
  unfold H1 at h1
  unfold H2 at h2
  unfold H3 at h3
  unfold H4 at h4
  unfold Erdos936.EventuallyNotPowerful
  filter_upwards [h1, h2, h3, h4] with n hodd hsingle hdouble height
  intro hpower
  by_cases hn : Odd n
  · exact hodd hn (odd_exponent_forces_three hn hpower)
      (fun h9 => odd_multiple_nine_forces_factors hn h9 hpower) hpower
  by_cases hn4 : n % 4 = 2
  · exact hsingle hn4 (v2_one_forces_factors hn4 hpower) hpower
  by_cases hn8 : n % 8 = 4
  · exact hdouble hn8 (v2_two_forces_factors hn8 hpower) hpower
  have hn_even : n % 2 = 0 := by
    rw [Nat.odd_iff] at hn
    omega
  exact height (by omega) hpower

end OMA.R_Erdos936_erdos_936_variants_two_pow_add_one_R2
