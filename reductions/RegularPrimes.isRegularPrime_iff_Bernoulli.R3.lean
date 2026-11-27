import FormalConjectures.Wikipedia.RegularPrimes
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

-- Credit: @Noctluxis
-- The product congruence is the denominator-cleared form of Diekmann's
-- relative class number congruence. Compare KummerCriterion.HMinus.PadicCorollaries,
-- hMinus_formula_bernoulli_mod_p, in riccardobrasca/KummerCriterion.

namespace OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3

open NumberField

/-- The residue of the relative class number after clearing Bernoulli denominators.
For the conductor two this includes the empty-product identity. -/
def H1 : Prop := ∀ (p : ℕ) [Fact p.Prime],
  let K := CyclotomicField p ℚ
  let hMinus := classNumber K / classNumber (maximalRealSubfield K)
  let S := (Finset.Icc 2 (p - 3)).filter Even
  (hMinus : ZMod p) * (∏ k ∈ S, (2 : ZMod p) * k * (bernoulli' k).den) =
    ∏ k ∈ S, -((bernoulli' k).num : ZMod p)

/-- Divisibility of the full class number is detected by its relative part. -/
def H2 : Prop := ∀ (p : ℕ) [Fact p.Prime],
  let K := CyclotomicField p ℚ
  p ∣ classNumber K ↔ p ∣ classNumber K / classNumber (maximalRealSubfield K)

lemma denominator_coprime : ∀ (p : ℕ) [Fact p.Prime],
    ∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ p ∣ (bernoulli' k).den := by
  intro p hp k hk he
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
  obtain ⟨j, hj⟩ := he
  have hkj : k = 2 * j := by omega
  clear hj
  subst k
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
  let S := (Finset.range (2 * j + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * j)
  let T := ∑ q ∈ S, (1 : ℚ) / q
  obtain ⟨a, ha⟩ := Bernoulli.vonStaudt_clausen j
  change (a : ℚ) = bernoulli (2 * j) + T at ha
  have hB : bernoulli (2 * j) = (a : ℚ) - T := by linarith
  have hprod : (∏ q ∈ S, ((1 : ℚ) / q).den).Coprime p := by
    refine Nat.Coprime.prod_left fun q hq => ?_
    obtain ⟨hbound, hprime, _⟩ := Finset.mem_filter.mp hq
    have hlt := Finset.mem_range.mp hbound
    rw [show ((1 : ℚ) / q).den = q by simp [hprime.ne_zero]]
    exact (Nat.coprime_primes hprime hp.out).mpr (by omega)
  have hT : T.den.Coprime p :=
    Nat.Coprime.of_dvd_left (Finset.Rat.den_sum_dvd_prod_den S _) hprod
  rw [hB]
  apply hp.out.coprime_iff_not_dvd.mp
  apply Nat.Coprime.symm
  apply Nat.Coprime.of_dvd_left (Rat.sub_den_dvd _ _)
  simpa using hT

lemma relative_criterion (hFormula : H1) (p : ℕ) [hp : Fact p.Prime] :
    let K := CyclotomicField p ℚ
    p ∣ classNumber K / classNumber (maximalRealSubfield K) ↔
      ∃ k ∈ Finset.Icc 2 (p - 3), Even k ∧ (p : ℤ) ∣ (bernoulli' k).num := by
  let K := CyclotomicField p ℚ
  let hMinus := classNumber K / classNumber (maximalRealSubfield K)
  let S := (Finset.Icc 2 (p - 3)).filter Even
  let D : ZMod p := ∏ k ∈ S, (2 : ZMod p) * k * (bernoulli' k).den
  have hD : D ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    obtain ⟨hkI, hkEven⟩ := Finset.mem_filter.mp hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hkI
    have htwo : ((2 : ℕ) : ZMod p) ≠ 0 :=
      (ZMod.natCast_eq_zero_iff 2 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
    have hk' : (k : ZMod p) ≠ 0 :=
      (ZMod.natCast_eq_zero_iff k p).not.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    exact mul_ne_zero (mul_ne_zero (by simpa only [Nat.cast_ofNat] using htwo) hk')
      ((ZMod.natCast_eq_zero_iff _ p).not.mpr (denominator_coprime p k hkI hkEven))
  have eqn : (hMinus : ZMod p) * D = ∏ k ∈ S, -((bernoulli' k).num : ZMod p) := hFormula p
  change p ∣ hMinus ↔ _
  rw [← ZMod.natCast_eq_zero_iff]
  constructor
  · intro hz
    obtain ⟨k, hk, hnum⟩ := Finset.prod_eq_zero_iff.mp (eqn.symm.trans (by rw [hz, zero_mul]))
    obtain ⟨hkI, hkEven⟩ := Finset.mem_filter.mp hk
    exact ⟨k, hkI, hkEven, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (neg_eq_zero.mp hnum)⟩
  · rintro ⟨k, hkI, hkEven, hnum⟩
    have hz : -((bernoulli' k).num : ZMod p) = 0 :=
      neg_eq_zero.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hnum)
    have hprod := Finset.prod_eq_zero_iff.mpr
      (show ∃ j ∈ S, -((bernoulli' j).num : ZMod p) = 0 from
        ⟨k, Finset.mem_filter.mpr ⟨hkI, hkEven⟩, hz⟩)
    exact (mul_eq_zero.mp (eqn.trans hprod)).resolve_right hD

theorem main : H1 → H2 → type_of% @RegularPrimes.isRegularPrime_iff_Bernoulli := by
  intro hFormula hReflect p hp
  let K := CyclotomicField p ℚ
  have hr : p ∣ classNumber K ↔ p ∣ classNumber K / classNumber (maximalRealSubfield K) :=
    hReflect p
  have hb : p ∣ classNumber K ↔
      ∃ k ∈ Finset.Icc 2 (p - 3), Even k ∧ (p : ℤ) ∣ (bernoulli' k).num :=
    hr.trans (relative_criterion hFormula p)
  change Nat.Coprime p (classNumber K) ↔ _
  rw [hp.out.coprime_iff_not_dvd, hb]
  constructor
  · intro h k hk he hd
    exact h ⟨k, hk, he, hd⟩
  · rintro h ⟨k, hk, he, hd⟩
    exact h k hk he hd

end OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3
