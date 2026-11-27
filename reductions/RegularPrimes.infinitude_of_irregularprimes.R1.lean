import FormalConjectures.Wikipedia.RegularPrimes
import Mathlib

-- Credit: @marcusbuffett
-- The auxiliary numerator lemma is adapted from Riccardo Brasca and contributors,
-- https://github.com/riccardobrasca/KummerCriterion, commit
-- d6f2d56131fb9a992bcfc97e46aa1dec7d8c7018, IrregularPrimes/RatNumerator.lean, Apache-2.0.

namespace OMA.R_RegularPrimes_infinitude_of_irregularprimes_R1

/-- Analytic growth of the divided Bernoulli numbers along even multiples. -/
def H1 : Prop := ∀ d : ℕ, 0 < d → ∃ n : ℕ, 0 < n ∧ Even n ∧ d ∣ n ∧
    1 < |(((bernoulli n / n : ℚ) : ℝ))|

/-- Von Staudt-Clausen excludes the zero residue, and the Kummer congruence
transfers a numerator divisor to the even representative in the fundamental range. -/
def H2 : Prop := ∀ p n : ℕ, p.Prime → 0 < n → Even n → (p : ℤ) ∣ (bernoulli n / n).num →
    ∃ k ∈ Finset.Icc 2 (p-3), Even k ∧ n ≡ k [MOD p-1] ∧ (p : ℤ) ∣ (bernoulli' k).num

/-- The class-number direction of Kummer's criterion. -/
def H3 : Prop := ∀ (p : ℕ) [Fact p.Prime], RegularPrimes.IsRegularPrime p →
    ∀ k ∈ Finset.Icc 2 (p-3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num

theorem exists_prime_dvd_num_of_one_lt_abs
    {q : ℚ} (hq : (1 : ℝ) < |(q : ℝ)|) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ q.num := by
  have hq_rat : (1 : ℚ) < |q| := by
    exact_mod_cast hq
  have hnum_gt_den_int : ((|q|).den : ℤ) < (|q|).num := by
    have hnot : ¬ (|q|).num ≤ ((|q|).den : ℤ) := fun hle =>
      (not_le_of_gt hq_rat) ((Rat.num_le_denom_iff).mp hle)
    exact lt_of_not_ge hnot
  have hden_lt_num : q.den < q.num.natAbs := by
    have hcast : (q.den : ℤ) < (q.num.natAbs : ℤ) := by
      simpa using hnum_gt_den_int
    exact_mod_cast hcast
  have hone_lt_num : 1 < q.num.natAbs :=
    lt_of_le_of_lt (Nat.succ_le_iff.mpr q.den_pos) hden_lt_num
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (show q.num.natAbs ≠ 1 by omega)
  exact ⟨p, hp, (Int.natCast_dvd (m := p) (n := q.num)).mpr hpdvd⟩

theorem main : H1 → H2 → H3 → type_of% @RegularPrimes.infinitude_of_irregularprimes := by
  intro growth descend regular
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, heven, hfac, hlarge⟩ := growth N.factorial (Nat.factorial_pos N)
  obtain ⟨p,hp,hdiv⟩ := exists_prime_dvd_num_of_one_lt_abs hlarge
  obtain ⟨k,hk,hke,hmod,hnum⟩ := descend p n hp hn heven hdiv
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, ⟨hp, fun hr => regular p hr k hk hke hnum⟩, ?_⟩
  by_contra! h
  have htwo := hp.two_le
  obtain ⟨hklo,hkhi⟩ := Finset.mem_Icc.mp hk
  have hpn : p-1 ∣ n := (Nat.dvd_factorial (by omega) (by omega : p-1 ≤ N)).trans hfac
  have hpk : p-1 ∣ k := (hmod.dvd_iff (dvd_refl _)).mp hpn
  have := Nat.le_of_dvd (by omega : 0 < k) hpk
  omega

end OMA.R_RegularPrimes_infinitude_of_irregularprimes_R1
