import OMAReductions.R_BealConjecture_beal_conjecture_R2
import Mathlib.Data.Nat.Prime.Basic

-- Credit: @Hennyrick
-- Bennett and Skinner, Canadian Journal of Mathematics 56 (2004), Theorem 8.4.

namespace OMA.R_BealConjecture_beal_conjecture_R2_H3_R1

open OMA.R_BealConjecture_beal_conjecture_R2

/-- The square-plus-power case of Bennett and Skinner, Theorem 8.4.
Only the square root of the exception is needed here. -/
def H1 : Prop :=
  ∀ {u d m k : Nat}, u % 2 = 1 → d % 2 = 1 → 1 < d → 2 < m →
    2 < k → k % 2 = 1 → u ^ 2 + d ^ m = 2 ^ k → u = 13

/-- The cubic and fifth-power equation, restricted to the cubic bases whose
residue admits a common exponent modulo ten in both local tests. -/
def H2 : Prop :=
  ∀ {a b k : Nat}, 1 < a → 1 < b → a % 2 = 1 → b % 2 = 1 →
    Nat.gcd a b = 1 → a % 8 + b % 8 = 8 → 2 < k →
    (∃ t : Fin 10,
      (∃ u : Fin 11, ((a % 341) ^ 3 + u.val ^ 5) % 11 = 2 ^ t.val % 11) ∧
      (∃ v : Fin 31, ((a % 341) ^ 3 + v.val ^ 5) % 31 = 2 ^ t.val % 31)) →
    a ^ 3 + b ^ 5 ≠ 2 ^ k

/-- The remaining odd summands have ordered distinct odd prime exponents. -/
def H3 : Prop :=
  ∀ {a b p q k : Nat}, 1 < a → 1 < b → a % 2 = 1 → b % 2 = 1 →
    Nat.gcd a b = 1 → a % 8 + b % 8 = 8 →
    2 < p → p < q → Nat.Prime p → Nat.Prime q → 2 < k → (p ≠ 3 ∨ q ≠ 5) →
    a ^ p + b ^ q ≠ 2 ^ k

namespace BealFactors

theorem coprime_factor_is_power {a b c n : Nat} (hab : Nat.Coprime a b)
    (heq : a * b = c ^ n) : ∃ u : Nat, a = u ^ n := by
  cases n with
  | zero =>
    exact ⟨1, Nat.eq_one_of_mul_eq_one_right heq⟩
  | succ n =>
    let x := Nat.gcd c a
    let y := Nat.gcd c b
    have hd : c ∣ a * b := ⟨c ^ n, by rw [heq, Nat.pow_succ, Nat.mul_comm]⟩
    have hxy : c = x * y :=
      (Nat.gcd_eq_left_iff_dvd.mpr hd).symm.trans (hab.gcd_mul c)
    have hprod : a * b = x ^ (n+1) * y ^ (n+1) := by
      calc
        _ = c ^ (n+1) := heq
        _ = (x*y) ^ (n+1) := congrArg (· ^ (n+1)) hxy
        _ = _ := Nat.mul_pow _ _ _
    have hay : Nat.Coprime a (y ^ (n+1)) :=
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right c b) hab).pow_right _
    have hxb : Nat.Coprime (x ^ (n+1)) b :=
      (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right c a) hab).pow_left _
    exact ⟨x, Nat.dvd_antisymm
      (hay.dvd_of_dvd_mul_right ⟨b, hprod.symm⟩)
      (hxb.dvd_of_dvd_mul_right ⟨y ^ (n+1), hprod⟩)⟩

theorem coprime_factors_are_powers {s t b y : Nat} (hc : Nat.gcd s t = 1)
    (h : s * t = b ^ y) : ∃ u v : Nat, s = u ^ y ∧ t = v ^ y := by
  obtain ⟨u, hu⟩ := coprime_factor_is_power hc h
  obtain ⟨v, hv⟩ := coprime_factor_is_power (Nat.Coprime.symm hc) ((Nat.mul_comm _ _).trans h)
  exact ⟨u, v, hu, hv⟩

end BealFactors

namespace BealParity

theorem odd_base_of_odd_power {a n : Nat} (hn : 0 < n) (ha : a ^ n % 2 = 1) :
    a % 2 = 1 := by
  rw [Nat.pow_mod] at ha
  by_cases h : a % 2 = 0
  · rw [h, Nat.zero_pow hn] at ha
    contradiction
  · omega

/-- Factoring a difference of squares forces two odd powers with the same
exponent to sum to a power of two. -/
theorem square_summand_excluded {a b m y h : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hy : 1 < y) (hh : 0 < h) :
    (a ^ m) ^ 2 + b ^ y ≠ (2 ^ h) ^ 2 := by
  intro heq
  let c := 2 ^ h
  let d := a ^ m
  have hc : c % 2 = 0 := by
    dsimp [c]
    rw [Nat.pow_mod]
    simp [Nat.zero_pow hh]
  have hd : d % 2 = 1 := by dsimp [d]; rw [Nat.pow_mod, ha, Nat.one_pow]
  have hbpos : 0 < b ^ y := Nat.pow_pos (by omega)
  have hcd : d < c := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp
    change d ^ 2 + b ^ y = c ^ 2 at heq
    omega
  let s := c - d
  let t := c + d
  have hs : s % 2 = 1 := by dsimp [s]; omega
  have ht : t % 2 = 1 := by dsimp [t]; omega
  have hsum : s + t = 2 ^ (h + 1) := by
    change (c - d) + (c + d) = 2 ^ (h + 1)
    rw [Nat.pow_succ]
    change (c - d) + (c + d) = c * 2
    omega
  have hprod : s * t = b ^ y := by
    change d ^ 2 + b ^ y = c ^ 2 at heq
    have hc' : c = s + d := by dsimp [s]; omega
    change s * (c + d) = b ^ y
    rw [hc'] at heq ⊢
    grind
  let g := Nat.gcd s t
  have hgs : g ∣ s := Nat.gcd_dvd_left s t
  have hgt : g ∣ t := Nat.gcd_dvd_right s t
  obtain ⟨j, hj⟩ := (show g ∣ s from hgs)
  have hgodd : g % 2 = 1 := by
    rw [hj, Nat.mul_mod] at hs
    by_cases hg : g % 2 = 0
    · simp [hg] at hs
    · omega
  have hgSum : g ∣ 2 ^ (h + 1) := hsum ▸ Nat.dvd_add hgs hgt
  obtain ⟨i, hi⟩ := hgSum
  have hg : g = 1 :=
    BealPartial.odd_factor_of_two_pow g hgodd (h + 1) i ((Nat.mul_comm i g).trans hi.symm)
  obtain ⟨u, v, hu, hv⟩ := BealFactors.coprime_factors_are_powers hg hprod
  rw [hu] at hs
  rw [hv] at ht
  rw [hu, hv] at hsum
  exact BealSum.rhs_two_power (odd_base_of_odd_power (by omega) hs)
    (odd_base_of_odd_power (by omega) ht) (by omega) (by simpa using hy) hsum

/-- For an even exponent on the power of two, both odd-base summand exponents
must themselves be odd. -/
theorem odd_exponents_of_even_power_of_two {a b x y k : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hx : 1 < x) (hy : 1 < y)
    (hk : 0 < k) (hke : k % 2 = 0) (heq : a ^ x + b ^ y = 2 ^ k) :
    x % 2 = 1 ∧ y % 2 = 1 := by
  have hsplit : k = (k / 2) * 2 := by omega
  rw [hsplit, Nat.pow_mul] at heq
  constructor
  · by_cases he : x % 2 = 0
    · have hxsplit : x = (x / 2) * 2 := by omega
      rw [hxsplit, Nat.pow_mul] at heq
      exact False.elim (square_summand_excluded ha hb hy (by omega) heq)
    · omega
  · by_cases he : y % 2 = 0
    · have hysplit : y = (y / 2) * 2 := by omega
      rw [hysplit, Nat.pow_mul, Nat.add_comm] at heq
      exact False.elim (square_summand_excluded hb ha hx (by omega) heq)
    · omega

end BealParity

namespace BealSquare

/-- The square root in the exceptional positive solution of the generalized
Ramanujan-Nagell equation is not a nontrivial perfect power. -/
theorem power_ne_thirteen {a n : Nat} (ha : a % 2 = 1) (hn : 1 < n) : a ^ n ≠ 13 := by
  intro h
  have hs : a ^ 2 ≤ a ^ n := Nat.pow_le_pow_right (by omega) hn
  by_cases h4 : 4 ≤ a
  · have := Nat.pow_le_pow_left h4 2
    omega
  rcases (show a = 1 ∨ a = 3 by omega) with h1 | h3
  · rw [h1, Nat.one_pow] at h
    contradiction
  · subst a
    by_cases he : n = 2
    · subst n
      contradiction
    · have hge := Nat.pow_le_pow_right (n := 3) (by decide) (show 3 ≤ n by omega)
      omega

theorem unit_addend_impossible {u k : Nat} (hu : u % 2 = 1) (hk : 2 ≤ k) :
    u ^ 2 + 1 ≠ 2 ^ k := by
  intro h
  have hmod : u ^ 2 % 4 = 1 := by
    rw [Nat.pow_mod]
    rcases (show u % 4 = 1 ∨ u % 4 = 3 by omega) with h | h <;> rw [h] <;> decide
  have hdiv : 4 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
  have hz := Nat.mod_eq_zero_of_dvd hdiv
  rw [← h] at hz
  omega

/-- The square-plus-power classification of Bennett and Skinner, Theorem 8.4,
excludes an even exponent on the first summand of a Beal counterexample. -/
theorem no_even_left_of_classification
    (classification : ∀ {u d m k : Nat}, u % 2 = 1 → d % 2 = 1 →
      1 < d → 2 < m → 2 < k → k % 2 = 1 → u ^ 2 + d ^ m = 2 ^ k → u = 13)
    {a b x y k : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) (hx : 2 < x)
    (hy : 2 < y) (hk : 2 < k) (hko : k % 2 = 1) (hxe : x % 2 = 0) :
    a ^ x + b ^ y ≠ 2 ^ k := by
  intro heq
  have hx' : x = x / 2 * 2 := by omega
  rw [hx', Nat.pow_mul] at heq
  have hu : a ^ (x / 2) % 2 = 1 := by rw [Nat.pow_mod, ha, Nat.one_pow]
  by_cases hb1 : b = 1
  · rw [hb1, Nat.one_pow] at heq
    exact unit_addend_impossible hu (by omega) heq
  · exact power_ne_thirteen ha (by omega) (classification hu hb (by omega) hy hk hko heq)

end BealSquare

namespace BealH3Odd

theorem odd_prime_divisor {n : Nat} (hn : 2 < n) (ho : n % 2 = 1) :
    ∃ p : Nat, 2 < p ∧ Nat.Prime p ∧ p ∣ n := by
  obtain ⟨p, hpr, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hp := Nat.Prime.two_le hpr
  refine ⟨p, ?_, hpr, hpn⟩
  by_cases h : p = 2
  · subst p
    have := Nat.mod_eq_zero_of_dvd hpn
    omega
  · omega

theorem both_odd_of_sorted_primes
    (H : ∀ {a b p q k : Nat}, a % 2 = 1 → b % 2 = 1 → 2 < p → p < q →
      Nat.Prime p → Nat.Prime q → 2 < k → a ^ p + b ^ q ≠ 2 ^ k)
    {a b x y k : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hx : 2 < x) (hy : 2 < y) (hxo : x % 2 = 1) (hyo : y % 2 = 1)
    (hk : 2 < k) (hg : Nat.gcd x y = 1) : a ^ x + b ^ y ≠ 2 ^ k := by
  obtain ⟨p, hp, hpr, hpx⟩ := odd_prime_divisor hx hxo
  obtain ⟨q, hq, hqr, hqy⟩ := odd_prime_divisor hy hyo
  have hne : p ≠ q := by
    intro h
    subst q
    have hd := Nat.dvd_gcd hpx hqy
    rw [hg] at hd
    have := Nat.dvd_one.mp hd
    omega
  obtain ⟨i, hi⟩ := hpx
  obtain ⟨j, hj⟩ := hqy
  rw [hi, hj, Nat.mul_comm p i, Nat.mul_comm q j, Nat.pow_mul, Nat.pow_mul]
  have hao : a ^ i % 2 = 1 := by rw [Nat.pow_mod, ha, Nat.one_pow]
  have hbo : b ^ j % 2 = 1 := by rw [Nat.pow_mod, hb, Nat.one_pow]
  by_cases hlt : p < q
  · exact H hao hbo hp hlt hpr hqr hk
  · rw [Nat.add_comm]
    exact H hbo hao hq (by omega) hqr hpr hk

end BealH3Odd

theorem odd_exponent_mod_eight {a p : Nat} (ha : a % 2 = 1) (hp : p % 2 = 1) :
    a ^ p % 8 = a % 8 := by
  have hs : a ^ 2 % 8 = 1 := by
    rw [Nat.pow_mod]
    rcases (show a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 by omega) with h|h|h|h <;> rw [h] <;> decide
  have he : p = 2 * (p / 2) + 1 := by omega
  rw [he, Nat.pow_succ, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod (a ^ 2), hs, Nat.one_pow]
  simp

theorem large_base {a b p q k : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hq : 1 < q) (hk : 2 < k) (heq : a ^ p + b ^ q = 2 ^ k) : 1 < a := by
  apply Nat.lt_of_not_ge
  intro h
  have ha1 : a = 1 := by omega
  rw [ha1, Nat.one_pow, Nat.add_comm] at heq
  have hone := BealEven.eq_one_of_succ_pow_two hb hq heq
  have hlarge := Nat.pow_le_pow_right (n := 2) (by decide) (show 3 ≤ k by omega)
  omega

theorem bases_coprime {a b p q k : Nat} (ha : a % 2 = 1) (hp : 0 < p) (hq : 0 < q)
    (heq : a ^ p + b ^ q = 2 ^ k) : Nat.gcd a b = 1 := by
  let g := Nat.gcd a b
  have hg : g ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨j, hj⟩ := hg
  have hgo : g % 2 = 1 := by
    rw [hj, Nat.mul_mod] at ha
    by_cases h : g % 2 = 0
    · simp [h] at ha
    · omega
  have hd : g ∣ 2 ^ k := by
    rw [← heq]
    exact Nat.dvd_add (Nat.dvd_trans (Nat.gcd_dvd_left a b) (by simpa only [Nat.pow_one] using Nat.pow_dvd_pow a hp))
      (Nat.dvd_trans (Nat.gcd_dvd_right a b) (by simpa only [Nat.pow_one] using Nat.pow_dvd_pow b hq))
  obtain ⟨i, hi⟩ := hd
  exact BealPartial.odd_factor_of_two_pow g hgo k i ((Nat.mul_comm i g).trans hi.symm)

theorem reduce_two_exponent {m : Nat} (hm : 1 < m) (h : 2 ^ 10 % m = 1) (k : Nat) :
    2 ^ k % m = 2 ^ (k % 10) % m := by
  calc
    2 ^ k % m = 2 ^ (k % 10 + 10 * (k / 10)) % m := by rw [Nat.mod_add_div]
    _ = _ := by
      rw [Nat.pow_add, Nat.mul_mod, Nat.pow_mul, Nat.pow_mod (2 ^ 10), h, Nat.one_pow,
        Nat.mod_eq_of_lt hm, Nat.mul_one, Nat.mod_mod]

theorem fifth_residue {m a b k : Nat} (hm : 1 < m) (hd : m ∣ 341) (h : 2 ^ 10 % m = 1)
    (heq : a ^ 3 + b ^ 5 = 2 ^ k) :
    ∃ u : Fin m, ((a % 341) ^ 3 + u.val ^ 5) % m = 2 ^ (k % 10) % m := by
  refine ⟨⟨b % m, Nat.mod_lt _ (by omega)⟩, ?_⟩
  change ((a % 341) ^ 3 + (b % m) ^ 5) % m = 2 ^ (k % 10) % m
  rw [← reduce_two_exponent hm h k, ← heq, Nat.add_mod, Nat.add_mod (a ^ 3),
    Nat.pow_mod (a % 341), Nat.mod_mod_of_dvd a hd, ← Nat.pow_mod, ← Nat.pow_mod]

/- Exactly 176 of the 341 classes admit simultaneous witnesses modulo 11 and 31. -/
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem number_of_locally_possible_cubic_bases :
    (List.range 341).countP (fun a => decide (∃ t : Fin 10,
      (∃ u : Fin 11, (a ^ 3 + u.val ^ 5) % 11 = 2 ^ t.val % 11) ∧
      (∃ v : Fin 31, (a ^ 3 + v.val ^ 5) % 31 = 2 ^ t.val % 31))) = 176 := by
  decide

theorem excluded_cubic_class_three {a b k : Nat} (ha : a % 341 = 3) :
    a ^ 3 + b ^ 5 ≠ 2 ^ k := by
  intro heq
  have h11 := fifth_residue (m := 11) (by decide) (by decide) (by decide) heq
  have h31 := fifth_residue (m := 31) (by decide) (by decide) (by decide) heq
  rw [ha] at h11 h31
  have h : ¬ ∃ t : Fin 10,
      (∃ u : Fin 11, (3 ^ 3 + u.val ^ 5) % 11 = 2 ^ t.val % 11) ∧
      (∃ v : Fin 31, (3 ^ 3 + v.val ^ 5) % 31 = 2 ^ t.val % 31) := by decide
  exact h ⟨⟨k % 10, Nat.mod_lt _ (by decide)⟩, h11, h31⟩

theorem sorted_prime_case (h2 : H2) (h3 : H3) {a b p q k : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hp : 2 < p) (hpq : p < q) (hpr : Nat.Prime p) (hqr : Nat.Prime q) (hk : 2 < k) :
    a ^ p + b ^ q ≠ 2 ^ k := by
  intro heq
  have hm := congrArg (fun t : Nat => t % 8) heq
  change (a ^ p + b ^ q) % 8 = 2 ^ k % 8 at hm
  rw [Nat.add_mod, odd_exponent_mod_eight ha (hpr.eq_two_or_odd.resolve_left (by omega)),
    odd_exponent_mod_eight hb (hqr.eq_two_or_odd.resolve_left (by omega))] at hm
  have hd : 8 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
  have hz := Nat.mod_eq_zero_of_dvd hd
  have hla := large_base ha hb (by omega) hk heq
  have hlb := large_base hb ha (by omega) hk ((Nat.add_comm _ _).trans heq)
  have hab := bases_coprime ha (by omega) (by omega) heq
  have hr : a % 8 + b % 8 = 8 := by omega
  by_cases hpair : p = 3 ∧ q = 5
  · obtain ⟨rfl, rfl⟩ := hpair
    exact h2 hla hlb ha hb hab hr hk ⟨⟨k % 10, Nat.mod_lt _ (by decide)⟩,
      fifth_residue (by decide) (by decide) (by decide) heq,
      fifth_residue (by decide) (by decide) (by decide) heq⟩ heq
  · exact h3 hla hlb ha hb hab hr hp hpq hpr hqr hk (by omega) heq

theorem main : H1 → H2 → H3 → OMA.R_BealConjecture_beal_conjecture_R2.H3 := by
  intro h1 h2 h3 a b x y k ha hb hx hy hk hg heq
  by_cases hke : k % 2 = 0
  · obtain ⟨hxo, hyo⟩ := BealParity.odd_exponents_of_even_power_of_two ha hb
      (by omega) (by omega) (by omega) hke heq
    exact BealH3Odd.both_odd_of_sorted_primes (fun ha hb => sorted_prime_case h2 h3 ha hb)
      ha hb hx hy hxo hyo hk hg heq
  · have hko : k % 2 = 1 := by omega
    by_cases hxe : x % 2 = 0
    · exact BealSquare.no_even_left_of_classification (fun hu hd => h1 hu hd)
        ha hb hx hy hk hko hxe heq
    by_cases hye : y % 2 = 0
    · exact BealSquare.no_even_left_of_classification (fun hu hd => h1 hu hd)
        hb ha hy hx hk hko hye ((Nat.add_comm _ _).trans heq)
    exact BealH3Odd.both_odd_of_sorted_primes (fun ha hb => sorted_prime_case h2 h3 ha hb)
      ha hb hx hy (by omega) (by omega) hk hg heq

end OMA.R_BealConjecture_beal_conjecture_R2_H3_R1
