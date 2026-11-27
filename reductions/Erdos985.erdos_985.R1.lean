import FormalConjectures.ErdosProblems.«985»
import Mathlib

-- Reduction Erdos985.erdos_985.R1 of Erdős Problem 985
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
`main` follows McGown, Treviño and Trudgian, *Resolving Grosswald's conjecture on GRH*
(Funct. Approx. Comment. Math. 55 (2016)), Theorem 1 and its Lemma 1 (after Bach 1997).
For a prime `p ≥ 10^8` with no prime primitive root below `p`, the character expansion of the
primitive-root indicator bounds the principal weighted prime sum by `2^ω(p-1) - 1` times a bound
for the non-principal ones. Under GRH (H1) both sums are estimated through a weighted explicit
formula for the completed L-functions, whose zero sums come from the Hadamard product (H3,
applied to `Λ(s, χ)` and to `ξ(s)`); the resulting inequality fails for every `p ≥ 10^8`.
The primes below `10^8` are the finite check H2.

H1 is GRH for Dirichlet L-functions, H2 is a finite computation, and H3 is Hadamard's
factorisation theorem for entire functions of order at most one, in logarithmic-derivative form.
The constructions of the source proof are written inline as terms, since a reduction file may
declare no definitions besides H1, H2 and H3.
-/

namespace OMA.R_Erdos985_erdos_985_R1

/-- GRH for Dirichlet L-functions: no Dirichlet L-function vanishes for `Re s > 1/2`
(the pole of the trivial character at `s = 1` excepted). This is the hypothesis
`DirichletLNonvanishingRightOfHalf` of leanprover-community/riemann-hypothesis, written out. -/
def H1 : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- The finite check: every odd prime `p < 10^8` has a prime primitive root `q < p`. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p < 10 ^ 8 →
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

/-- Hadamard factorisation, logarithmic-derivative form, for an entire function of order at
most one: if `f` is entire, `f 0 ≠ 0` and `‖f z‖ ≤ C exp(C ‖z‖ log(‖z‖ + 2))`, then its zeros,
counted with multiplicity, satisfy `Σ m(ρ) / ‖ρ‖^(1+ε) < ∞` for every `ε > 0`, and
`f'/f (z) = b + Σ m(ρ) (1/(z - ρ) + 1/ρ)` away from the zeros. -/
def H3 : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → f 0 ≠ 0 →
    (∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2))) →
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + ε)) ∧
    ∃ b : ℂ, ∀ z : ℂ, f z ≠ 0 →
      Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)) ∧
      deriv f z / f z = b + ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)
open Complex in
theorem port_logDeriv_Gamma {g : ℂ → ℂ} {a s : ℂ} (hg : HasDerivAt g a s)
    (h : ∀ m : ℕ, g s ≠ -(m : ℂ)) :
    logDeriv (fun z ↦ Gamma (g z)) s = a * digamma (g s) := by
  rw [show (fun z ↦ Gamma (g z)) = Gamma ∘ g from rfl,
    logDeriv_comp (differentiableAt_Gamma _ h) hg.differentiableAt, hg.deriv, digamma_def]
  exact mul_comm _ _
open Complex in
theorem port_digamma_apply_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    digamma (s + n) = digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn (m : ℕ) : s + (n : ℂ) ≠ -(m : ℂ) := fun h ↦
      hs (m + n) (by push_cast at h ⊢; linear_combination h)
    rw [show s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 by push_cast; ring,
      digamma_apply_add_one _ hsn, ih, Finset.sum_range_succ]
    ring
open Complex in
open scoped Real in
theorem port_digamma_one_sub {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) :
    digamma (1 - s) = digamma s + π * cot (π * s) := by
  have h1 (m : ℕ) : s ≠ -m := by simpa using hs (-m)
  have h2 (m : ℕ) : 1 - s ≠ -m := fun h ↦ hs (1 + m) (by push_cast; linear_combination -h)
  have hG : (fun z => Gamma z * Gamma (1 - z)) = fun z => (π : ℂ) / sin (π * z) :=
    funext Gamma_mul_Gamma_one_sub
  have hsin : sin (π * s) ≠ 0 := by
    rw [Ne, sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    apply hs k
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp at hk
    exact hk
  have hL := congrArg (fun F => logDeriv F s) hG
  have hd1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  rw [
    logDeriv_mul (f := Gamma) (g := fun z => Gamma (1 - z)) s (Gamma_ne_zero h1) (Gamma_ne_zero h2) (differentiableAt_Gamma _ h1)
      ((differentiableAt_Gamma _ h2).comp s hd1.differentiableAt),
    port_logDeriv_Gamma hd1 h2] at hL
  have hd2 : HasDerivAt (fun z : ℂ => sin (π * z)) (cos (π * s) * π) s := by
    simpa [mul_comm] using ((hasDerivAt_id s).const_mul (π : ℂ)).csin
  have hR : logDeriv (fun z => (π : ℂ) / sin (π * z)) s = -(π * cos (π * s) / sin (π * s)) := by
    rw [logDeriv_apply, deriv_const_div (c := (π : ℂ)) hd2.differentiableAt hsin, hd2.deriv]
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  rw [hR, ← digamma_def] at hL
  rw [cot_eq_cos_div_sin]
  linear_combination -hL
open Complex in
open scoped Real in
theorem port_digamma_two_mul {s : ℂ} (hs : ∀ m : ℕ, 2 * s ≠ -(m : ℂ)) :
    digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2 := by
  have hs₀ (m : ℕ) : s ≠ -(m : ℂ) := fun h ↦
    hs (2 * m) (by push_cast; linear_combination 2 * h)
  have hs₁ (m : ℕ) : s + 1 / 2 ≠ -(m : ℂ) := fun h ↦
    hs (2 * m + 1) (by push_cast; linear_combination 2 * h)
  have hpow : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by simp [cpow_eq_zero_iff]
  have hd2 := hasDerivAt_id' s |>.const_mul 2 |>.const_sub 1 |>.const_cpow <|
    .inl (by norm_num : (2 : ℂ) ≠ 0)
  suffices key : digamma s + digamma (s + 1 / 2) = 2 * digamma (2 * s) - 2 * log 2 by
    linear_combination (-1 / 2 : ℂ) * key
  have hpi : (√π : ℂ) ≠ 0 := by
    rw [Ne, ofReal_eq_zero]; exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    digamma s + digamma (s + 1 / 2) = logDeriv (fun z ↦ Gamma z * Gamma (z + 1 / 2)) s := by
      rw [logDeriv_mul (f := Gamma) (g := fun z ↦ Gamma (z + 1 / 2)) s (Gamma_ne_zero hs₀)
        (Gamma_ne_zero hs₁) (differentiableAt_Gamma _ hs₀)
        ((differentiableAt_Gamma _ hs₁).comp s ((hasDerivAt_id' s).add_const (1 / 2)).differentiableAt),
        port_logDeriv_Gamma ((hasDerivAt_id' s).add_const (1 / 2)) hs₁, ← digamma_def]
      ring
    _ = logDeriv (fun z ↦ Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * (√π : ℂ)) s := by
      rw [funext Gamma_mul_Gamma_add_half]
    _ = 2 * digamma (2 * s) - 2 * log 2 := by
      rw [logDeriv_mul_const s (√π : ℂ) hpi,
        logDeriv_mul (f := fun z ↦ Gamma (2 * z)) (g := fun z => (2 : ℂ) ^ (1 - 2 * z)) s
          (Gamma_ne_zero hs) hpow
          ((differentiableAt_Gamma _ hs).comp s ((hasDerivAt_id' s).const_mul 2).differentiableAt)
          hd2.differentiableAt,
        port_logDeriv_Gamma ((hasDerivAt_id' s).const_mul 2) hs, mul_one, sub_eq_add_neg]
      congr! 1
      rw [logDeriv_apply, hd2.deriv, div_eq_iff hpow]
      ring
theorem port_completedLFunction_ne_zero_of_one_le_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) ⦃s : ℂ⦄ (hχs : χ ≠ 1 ∨ s ≠ 1)
    (hs : 1 ≤ s.re) : DirichletCharacter.completedLFunction χ s ≠ 0 := by
  intro h
  apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0), h, zero_div]
theorem port_rootNumber_mul_rootNumber_inv {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    DirichletCharacter.rootNumber χ * DirichletCharacter.rootNumber χ⁻¹ = 1 := by
  have h2 : DirichletCharacter.completedLFunction χ 2 ≠ 0 :=
    port_completedLFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by simp)
  have ha : DirichletCharacter.completedLFunction χ 2
      = (N : ℂ) ^ (-(3 / 2 : ℂ)) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ (-1) := by
    convert hχ.completedLFunction_one_sub (-1) using 2 <;> norm_num
  have hb : DirichletCharacter.completedLFunction χ⁻¹ (-1)
      = (N : ℂ) ^ (3 / 2 : ℂ) * DirichletCharacter.rootNumber χ⁻¹ *
        DirichletCharacter.completedLFunction χ 2 := by
    convert (show (χ⁻¹).IsPrimitive by
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]; exact hχ).completedLFunction_one_sub 2 using 2 <;> norm_num
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpow : (N : ℂ) ^ (-(3 / 2 : ℂ)) * (N : ℂ) ^ (3 / 2 : ℂ) = 1 := by
    rw [Complex.cpow_neg, inv_mul_cancel₀ (by simp [Complex.cpow_eq_zero_iff, hN])]
  rw [hb] at ha
  have : DirichletCharacter.completedLFunction χ 2 *
      (1 - DirichletCharacter.rootNumber χ * DirichletCharacter.rootNumber χ⁻¹) = 0 := by
    linear_combination ha + DirichletCharacter.rootNumber χ * DirichletCharacter.rootNumber χ⁻¹ *
      DirichletCharacter.completedLFunction χ 2 * hpow
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h2
  · linear_combination -h
theorem port_even_one : (1 : DirichletCharacter ℂ 1).Even := by
  show (1 : DirichletCharacter ℂ 1) (-1) = 1
  exact MulChar.one_apply (isUnit_of_subsingleton _)
theorem port_rootNumber_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : DirichletCharacter.rootNumber χ ≠ 0 := by
  intro h
  have := port_rootNumber_mul_rootNumber_inv hχ
  rw [h, zero_mul] at this
  exact zero_ne_one this

section Toolkit
namespace Erdos985.Analytic
theorem hadamard_logDeriv [Fact H3] {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2))) :
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + ε)) ∧
    ∃ b : ℂ, ∀ z : ℂ, f z ≠ 0 →
      Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)) ∧
      deriv f z / f z = b + ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ) :=
  (Fact.out : H3) f hf hf0 hgrowth
end Erdos985.Analytic
section
namespace Erdos985
end Erdos985
end
section
namespace Erdos985
open ArithmeticFunction Real
theorem ZdbachC_def (p x : ℝ) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)) :=
  Classical.choose_spec (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p))) p x
theorem ZdbachC_eq :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) = fun (p x : ℝ) => (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)) := by
  funext p x
  exact ZdbachC_def p x
theorem ZdbachSum_def (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ) :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)) :=
  Classical.choose_spec (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x))) N χ x
theorem ZdbachSum_eq :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) = fun (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ) => (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)) := by
  funext N χ x
  exact ZdbachSum_def N χ x
end Erdos985
end
section
open ArithmeticFunction
namespace Erdos985.Indicator
lemma exists_primeFactor_pow_eq_one (p : ℕ) [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0)
    (hord : orderOf a ≠ p - 1) : ∃ ℓ ∈ (p - 1).primeFactors, a ^ ((p - 1) / ℓ) = 1 := by
  have hd : orderOf a ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha
  have hN : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le; omega
  have hq : (p - 1) / orderOf a ≠ 1 := by
    intro h
    exact hord (Nat.eq_of_dvd_of_div_eq_one hd h)
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hq
  have hℓN : ℓ ∣ p - 1 := hℓd.trans (Nat.div_dvd_of_dvd hd)
  refine ⟨ℓ, Nat.mem_primeFactors.mpr ⟨hℓ, hℓN, hN⟩, ?_⟩
  rw [← orderOf_dvd_iff_pow_eq_one]
  apply Nat.dvd_div_of_mul_dvd
  rw [mul_comm]
  calc orderOf a * ℓ ∣ orderOf a * ((p - 1) / orderOf a) := Nat.mul_dvd_mul_left _ hℓd
    _ = p - 1 := Nat.mul_div_cancel' hd
lemma orderOf_ne_of_vonMangoldt_ne_zero (p : ℕ) [Fact p.Prime] (x : ℕ) (hxp : x ≤ p)
    (hno : ∀ q, q.Prime → q < x → orderOf (q : ZMod p) ≠ p - 1) {n : ℕ} (hn : n < x)
    (hΛ : Λ n ≠ 0) : (n : ZMod p) ≠ 0 ∧ orderOf (n : ZMod p) ≠ p - 1 := by
  obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  have hqn : q ≤ q ^ k := Nat.le_self_pow hk.ne' q
  have hqp : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd hq.pos h
    omega
  have hn0 : ((q ^ k : ℕ) : ZMod p) ≠ 0 := by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hqp
  refine ⟨hn0, fun h => hno q hq (by omega) ?_⟩
  rw [Nat.cast_pow] at h
  have h1 : orderOf ((q : ZMod p) ^ k) ∣ orderOf (q : ZMod p) := orderOf_pow_dvd k
  exact Nat.dvd_antisymm (ZMod.orderOf_dvd_card_sub_one hqp) (h ▸ h1)
lemma not_dvd_sum (N : ℕ) (T : Finset ℕ) (hT : T ⊆ N.primeFactors) (c : T → ℕ)
    (hc : ∀ ℓ, 0 < c ℓ ∧ c ℓ < (ℓ : ℕ)) (ℓ₀ : T) :
    ¬ N ∣ ∑ ℓ : T, c ℓ * (N / ℓ) := by
  classical
  intro hdiv
  have hmem : ∀ ℓ : T, (ℓ : ℕ).Prime ∧ (ℓ : ℕ) ∣ N ∧ N ≠ 0 :=
    fun ℓ => Nat.mem_primeFactors.mp (hT ℓ.2)
  set M := ∏ ℓ ∈ Finset.univ.erase ℓ₀, (ℓ : ℕ) with hM
  have h1 : N ∣ M * ∑ ℓ : T, c ℓ * (N / ℓ) := dvd_mul_of_dvd_right hdiv M
  rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ₀)] at h1
  have h2 : N ∣ ∑ ℓ ∈ Finset.univ.erase ℓ₀, M * (c ℓ * (N / ℓ)) := by
    apply Finset.dvd_sum
    intro ℓ hℓ
    obtain ⟨M', hM'⟩ := Finset.dvd_prod_of_mem (fun ℓ : T => (ℓ : ℕ)) hℓ
    rw [← hM] at hM'
    rw [hM']
    have : (ℓ : ℕ) * (N / ℓ) = N := Nat.mul_div_cancel' (hmem ℓ).2.1
    exact ⟨M' * c ℓ, by
      rw [show (ℓ : ℕ) * M' * (c ℓ * (N / ℓ)) = ((ℓ : ℕ) * (N / ℓ)) * (M' * c ℓ) by ring, this]⟩
  have h3 : N ∣ M * (c ℓ₀ * (N / ℓ₀)) := (Nat.dvd_add_left h2).mp h1
  obtain ⟨hp0, hd0, hN0⟩ := hmem ℓ₀
  have hpos : 0 < N / ℓ₀ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd0) hp0.pos
  have h4 : (ℓ₀ : ℕ) ∣ M * c ℓ₀ := by
    have : (ℓ₀ : ℕ) * (N / ℓ₀) ∣ (M * c ℓ₀) * (N / ℓ₀) := by
      rw [Nat.mul_div_cancel' hd0, mul_assoc]; exact h3
    exact Nat.dvd_of_mul_dvd_mul_right hpos this
  rcases (Nat.Prime.dvd_mul hp0).mp h4 with h | h
  · rw [hM] at h
    obtain ⟨ℓ, hℓ, hdl⟩ := (hp0.prime.dvd_finsetProd_iff _).mp h
    have := (Nat.prime_dvd_prime_iff_eq hp0 (hmem ℓ).1).mp hdl
    exact (Finset.mem_erase.mp hℓ).1 (Subtype.ext this).symm
  · have := Nat.le_of_dvd (hc ℓ₀).1 h
    have := (hc ℓ₀).2
    omega
end Erdos985.Indicator
namespace Erdos985.Indicator
open Finset
theorem ZdW_def (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ) :
    (Classical.choose (⟨_, fun _ _ _ _ => rfl⟩ : ∃ f : (p : ℕ) → DirichletCharacter ℂ p → ℕ → Finset ℕ → ℂ, ∀ (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ), f p ψ x T = (open ArithmeticFunction Finset in ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))))) p ψ x T = (open ArithmeticFunction Finset in ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))) :=
  Classical.choose_spec (⟨_, fun _ _ _ _ => rfl⟩ : ∃ f : (p : ℕ) → DirichletCharacter ℂ p → ℕ → Finset ℕ → ℂ, ∀ (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ), f p ψ x T = (open ArithmeticFunction Finset in ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ)))) p ψ x T
theorem ZdW_eq :
    (Classical.choose (⟨_, fun _ _ _ _ => rfl⟩ : ∃ f : (p : ℕ) → DirichletCharacter ℂ p → ℕ → Finset ℕ → ℂ, ∀ (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ), f p ψ x T = (open ArithmeticFunction Finset in ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))))) = fun (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ) => (open ArithmeticFunction Finset in ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))) := by
  funext p ψ x T
  exact ZdW_def p ψ x T
lemma norm_W_le (p : ℕ) [Fact p.Prime] (ψ : DirichletCharacter ℂ p) (hψ : orderOf ψ = p - 1)
    (x : ℕ) (B : ℝ) (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) χ x‖ ≤ B)
    (T : Finset ℕ) (hT : T ⊆ (p - 1).primeFactors) (hne : T.Nonempty) :
    ‖(Classical.choose (⟨_, fun _ _ _ _ => rfl⟩ : ∃ f : (p : ℕ) → DirichletCharacter ℂ p → ℕ → Finset ℕ → ℂ, ∀ (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ), f p ψ x T = (open ArithmeticFunction Finset in ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))))) p ψ x T‖ ≤ (∏ ℓ ∈ T, ((ℓ : ℝ) - 1)) * B := by
  classical
  obtain ⟨l, hl⟩ := hne
  set m : (T → ℕ) → ℕ := fun c => ∑ ℓ : T, c ℓ * ((p - 1) / ℓ) with hm
  have hndvd : ∀ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), ¬ (p - 1) ∣ m c := by
    intro c hc
    rw [Fintype.mem_piFinset] at hc
    refine not_dvd_sum (p - 1) T hT c (fun ℓ => ?_) ⟨l, hl⟩
    have := Finset.mem_Ico.mp (hc ℓ); omega
  have key : ∀ n : ℕ, ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ)) =
      ∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), ψ n ^ m c := by
    intro n
    rw [← Finset.prod_coe_sort, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_pow_eq_pow_sum]
  have hW : (Classical.choose (⟨_, fun _ _ _ _ => rfl⟩ : ∃ f : (p : ℕ) → DirichletCharacter ℂ p → ℕ → Finset ℕ → ℂ, ∀ (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ), f p ψ x T = (open ArithmeticFunction Finset in ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))))) p ψ x T = ∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)),
      ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) (ψ ^ m c) x := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Indicator.ZdW_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.ZdbachSum_eq]
    simp_rw [key, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun n _ => ?_
    have hm0 : m c ≠ 0 := fun h => hndvd c hc (h ▸ dvd_zero (p - 1))
    rw [MulChar.pow_apply' _ hm0]
    ring
  rw [hW]
  calc ‖∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) (ψ ^ m c) x‖
      ≤ ∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), ‖((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) (ψ ^ m c) x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), B := by
        refine Finset.sum_le_sum fun c hc => hB _ fun h => hndvd c hc ?_
        rw [← hψ]
        exact orderOf_dvd_of_pow_eq_one h
    _ = (∏ ℓ ∈ T, ((ℓ : ℝ) - 1)) * B := by
        rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset]
        congr 1
        rw [← Finset.prod_coe_sort T (fun ℓ => ((ℓ : ℝ) - 1))]
        push_cast
        refine Finset.prod_congr rfl fun ℓ _ => ?_
        have h1 : 1 ≤ (ℓ : ℕ) := (Nat.mem_primeFactors.mp (hT ℓ.2)).1.one_lt.le
        rw [Nat.card_Ico, Nat.cast_sub h1, Nat.cast_one]
end Erdos985.Indicator
end
section
namespace Erdos985
open ArithmeticFunction Finset Erdos985.Indicator
theorem principal_le_of_no_prime_primitive_root (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (x : ℕ) (hxp : x ≤ p) (B : ℝ)
    (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) χ x‖ ≤ B)
    (hno : ∀ q, q.Prime → q < x → orderOf (q : ZMod p) ≠ p - 1) :
    ∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x)
      ≤ ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * B := by
  classical
  have hN : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulChar (ZMod p) ℂ, orderOf ψ = p - 1 :=
    MulChar.exists_mulChar_orderOf (ZMod p) (by rw [ZMod.card])
      (Complex.isPrimitiveRoot_exp (p - 1) hN)
  set P := (p - 1).primeFactors with hP
  have hP2 : ∀ ℓ ∈ P, 2 ≤ ℓ := fun ℓ hℓ => (Nat.mem_primeFactors.mp hℓ).1.two_le
  set a : ℕ → ℝ := fun ℓ => 1 - 1 / (ℓ : ℝ) with ha
  set b : ℕ → ℝ := fun ℓ => -(1 / (ℓ : ℝ)) with hb
  set A : ℕ → ℕ → ℂ := fun ℓ n => ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ)) with hA
  set S₀ : ℝ := ∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) with hS₀
  have h0 : ∀ n ∈ range x,
      (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ P, ((b ℓ : ℂ) * A ℓ n + (a ℓ : ℂ)) = 0 := by
    intro n hn
    by_cases hΛ : Λ n = 0
    · simp [hΛ]
    obtain ⟨hn0, hord⟩ := orderOf_ne_of_vonMangoldt_ne_zero p x hxp hno (mem_range.mp hn) hΛ
    obtain ⟨ℓ, hℓ, hpow⟩ := exists_primeFactor_pow_eq_one p hn0 hord
    rw [Finset.prod_eq_zero hℓ, mul_zero]
    have hψ1 : ψ n ^ ((p - 1) / ℓ) = 1 := by rw [← map_pow, hpow, map_one]
    have hℓ1 : 1 ≤ ℓ := (hP2 ℓ hℓ).trans' (by norm_num)
    have hAℓ : A ℓ n = (ℓ : ℂ) - 1 := by
      simp only [hA]
      simp_rw [pow_mul', hψ1, one_pow]
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub hℓ1, Nat.cast_one]
    rw [hAℓ]
    have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
    simp only [ha, hb]
    push_cast
    field_simp
    ring
  have hsum : ∑ t ∈ P.powerset,
      (((∏ ℓ ∈ t, b ℓ) * ∏ ℓ ∈ P \ t, a ℓ : ℝ) : ℂ) * (Classical.choose (⟨_, fun _ _ _ _ => rfl⟩ : ∃ f : (p : ℕ) → DirichletCharacter ℂ p → ℕ → Finset ℕ → ℂ, ∀ (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ), f p ψ x T = (open ArithmeticFunction Finset in ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))))) p ψ x t = 0 := by
    rw [← Finset.sum_eq_zero h0]
    simp_rw [Finset.prod_add, Finset.mul_sum, OMA.R_Erdos985_erdos_985_R1.Erdos985.Indicator.ZdW_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.prod_mul_distrib]
    push_cast
    ring
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset P)] at hsum
  simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty] at hsum
  set θ : ℝ := ∏ ℓ ∈ P, a ℓ with hθ
  have ha_pos : ∀ ℓ ∈ P, 0 < a ℓ := by
    intro ℓ hℓ
    have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hP2 ℓ hℓ
    simp only [ha]
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hθpos : 0 < θ := Finset.prod_pos ha_pos
  have hW0 : (Classical.choose (⟨_, fun _ _ _ _ => rfl⟩ : ∃ f : (p : ℕ) → DirichletCharacter ℂ p → ℕ → Finset ℕ → ℂ, ∀ (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ), f p ψ x T = (open ArithmeticFunction Finset in ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))))) p ψ x ∅ = (S₀ : ℂ) := by
    simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Indicator.ZdW_eq, hS₀]
  rw [hW0] at hsum
  have hcoef : ∀ t ∈ P.powerset.erase ∅,
      |(∏ ℓ ∈ t, b ℓ) * ∏ ℓ ∈ P \ t, a ℓ| * (∏ ℓ ∈ t, ((ℓ : ℝ) - 1)) = θ := by
    intro t ht
    have htP : t ⊆ P := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    rw [abs_mul, Finset.abs_prod, abs_of_nonneg (Finset.prod_nonneg fun ℓ hℓ =>
      (ha_pos ℓ (Finset.sdiff_subset hℓ)).le), mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib,
      hθ, ← Finset.prod_sdiff htP, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hP2 ℓ (htP hℓ)
    simp only [ha, hb, abs_neg]
    rw [abs_of_pos (by positivity)]
    field_simp
  have hbound : ‖((θ : ℝ) : ℂ) * (S₀ : ℂ)‖ ≤ ((P.powerset.erase ∅).card : ℝ) * (θ * B) := by
    rw [eq_neg_of_add_eq_zero_left hsum, norm_neg]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    have htP : t ⊆ P := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hcoef t ht, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_W_le p ψ hψ x B hB t htP htne) (abs_nonneg _)
  have hcard : ((P.powerset.erase ∅).card : ℝ) = (2 : ℝ) ^ P.card - 1 := by
    rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset P), Finset.card_powerset,
      Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  rw [hcard] at hbound
  have hle : θ * S₀ ≤ θ * (((2 : ℝ) ^ P.card - 1) * B) := by
    calc θ * S₀ ≤ |θ * S₀| := le_abs_self _
      _ = ‖((θ : ℝ) : ℂ) * (S₀ : ℂ)‖ := by
          rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := hbound
      _ = θ * (((2 : ℝ) ^ P.card - 1) * B) := by ring
  exact le_of_mul_le_mul_left hle hθpos
end Erdos985
end
section
namespace Erdos985
open Real
lemma pow_card_primeFactors_mul_le (B n : ℕ) (hn : n ≠ 0) :
    B ^ n.primeFactors.card * ∏ r ∈ (Finset.range B).filter Nat.Prime, r
      ≤ n * B ^ ((Finset.range B).filter Nat.Prime).card := by
  set S := n.primeFactors
  set T := (Finset.range B).filter Nat.Prime
  have hS : ∏ r ∈ S, r ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  have hset : T.filter (· ∈ S) = S.filter (· < B) := by
    ext r
    simp only [T, S, Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    tauto
  have e1 := Finset.prod_filter_mul_prod_filter_not S (· < B) (fun r => r)
  have e2 := Finset.prod_filter_mul_prod_filter_not T (· ∈ S) (fun r => r)
  have c1 := Finset.card_filter_add_card_filter_not (s := S) (p := (· < B))
  have c2 := Finset.card_filter_add_card_filter_not (s := T) (p := (· ∈ S))
  rw [hset] at e2 c2
  have b1 : B ^ (S.filter (fun r => ¬ r < B)).card ≤ ∏ r ∈ S.filter (fun r => ¬ r < B), r :=
    Finset.pow_card_le_prod _ _ _ (fun x hx => by
      simp only [Finset.mem_filter] at hx; omega)
  have b2 : ∏ r ∈ T.filter (fun r => ¬ r ∈ S), r ≤ B ^ (T.filter (fun r => ¬ r ∈ S)).card :=
    Finset.prod_le_pow_card _ _ _ (fun x hx => by
      simp only [T, Finset.mem_filter, Finset.mem_range] at hx; omega)
  rw [← e2, ← c1, ← c2]
  set P := ∏ r ∈ S.filter (· < B), r
  set a := (S.filter (· < B)).card
  set b := (S.filter (fun r => ¬ r < B)).card
  set d := (T.filter (fun r => ¬ r ∈ S)).card
  calc B ^ (a + b) * (P * ∏ r ∈ T.filter (fun r => ¬ r ∈ S), r)
      ≤ B ^ (a + b) * (P * B ^ d) := by gcongr
    _ = (P * B ^ b) * B ^ (a + d) := by ring
    _ ≤ (P * ∏ r ∈ S.filter (fun r => ¬ r < B), r) * B ^ (a + d) := by gcongr
    _ ≤ n * B ^ (a + d) := by rw [e1]; gcongr
lemma bachC_le (p s0 L0 : ℝ) (hp : 1 ≤ p) (hs0 : 0 < s0) (hL0 : 0 < L0)
    (hs : s0 ≤ √p) (hL : L0 ≤ Real.log p) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p p ≤ (2/3) * (1 + 2 / s0 + 3 / p) * (1 + (5/3) / L0) + (1 / s0 + 2 / (s0 * L0)) := by
  have hpp : p ≤ p ^ (3/2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hp (by norm_num : (1:ℝ) ≤ 3/2)
  have hp0 : 0 < p := by linarith
  have hsp : 0 < √p := lt_of_lt_of_le hs0 hs
  have hLp : 0 < Real.log p := lt_of_lt_of_le hL0 hL
  have e : (Real.log p + 2) / (√p * Real.log p) = 1 / √p + 2 / (√p * Real.log p) := by
    field_simp
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.ZdbachC_eq]
  rw [e]
  gcongr
lemma log_le_tangent (x a : ℝ) (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ Real.log a + x / a - 1 := by
  have := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at this
  linarith
lemma bachC_pos (p : ℝ) (hp : 1 < p) : 0 < (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p p := by
  have := Real.log_pos hp
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.ZdbachC_eq]
  have : 0 < p := by linarith
  positivity
lemma finish_aux (A c s L Aa c0 U : ℝ) (hs : 0 < s) (hA0 : 0 ≤ A) (hA : A ≤ Aa)
    (hc0 : 0 ≤ c) (hc : c ≤ c0) (hL0 : 0 ≤ L) (hL : L ≤ U)
    (h : s * (Aa * c0 * U) < s ^ 2 / 2 - s / 20 - 3) :
    A * (c * s * L) < s ^ 2 / 2 - (s / 20 + 3) := by
  have h1 : A * c * L ≤ Aa * c0 * U := by
    have := hA0.trans hA
    have := hc0.trans hc
    gcongr
  have h2 : s * (A * c * L) ≤ s * (Aa * c0 * U) := mul_le_mul_of_nonneg_left h1 hs.le
  nlinarith
theorem bach_inequality_large (p : ℕ) (_hp : p.Prime) (hp0 : 10 ^ 8 ≤ p) :
    ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p p * √p * Real.log p)
      < p / 2 - (√p / 20 + 3) := by
  set k := (p - 1).primeFactors.card with hk
  have hpR : (10 ^ 8 : ℝ) ≤ p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0' : (0 : ℝ) < p := by linarith
  set s := √(p : ℝ) with hs_def
  have hs2 : s ^ 2 = p := Real.sq_sqrt hp0'.le
  have hspos : 0 < s := Real.sqrt_pos.2 hp0'
  have hsge : (10000 : ℝ) ≤ s := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
  have hLpos : 0 < Real.log p := Real.log_pos hp1
  have hc0 : 0 ≤ (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p p := (bachC_pos p hp1).le
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hlogs : Real.log p = 2 * Real.log s := by
    rw [hs_def, Real.log_sqrt hp0'.le]; ring
  have hX1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hA0 : (0 : ℝ) ≤ 2 ^ k - 1 := by linarith
  rw [show (p : ℝ) / 2 = s ^ 2 / 2 by rw [hs2]]
  have hU14 : Real.log p ≤ 2 * (14 * 0.6931471808 + s / 16384 - 1) := by
    have h := log_le_tangent s 16384 hspos (by norm_num)
    have : Real.log (16384 : ℝ) = 14 * Real.log 2 := by
      rw [show (16384 : ℝ) = 2 ^ 14 by norm_num, Real.log_pow]; norm_num
    rw [hlogs]; linarith
  have hpnz : p - 1 ≠ 0 := by omega
  rcases (show k ≤ 8 ∨ k = 9 ∨ 10 ≤ k by omega) with h8 | h9 | h10
  ·
    have hL : (18.02 : ℝ) ≤ Real.log p := by
      have : Real.log ((2 : ℝ) ^ 26) ≤ Real.log p := Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hc := bachC_le p 10000 18.02 hp1.le (by norm_num) (by norm_num) hsge hL
    have h3 : 3 / (p : ℝ) ≤ 3 / 10 ^ 8 := by gcongr
    have hc' : (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p p ≤ 0.7286 := by
      have : (2/3 : ℝ) * (1 + 2 / 10000 + 3 / p) * (1 + (5/3) / 18.02)
          ≤ (2/3) * (1 + 2 / 10000 + 3 / 10^8) * (1 + (5/3) / 18.02) := by gcongr
      norm_num at hc this ⊢; linarith
    have hA : (2 : ℝ) ^ k - 1 ≤ 255 := by
      have : (2 : ℝ) ^ k ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) h8
      norm_num at this; linarith
    refine finish_aux _ _ _ _ 255 0.7286 _ hspos hA0 hA hc0 hc' hLpos.le hU14 ?_
    nlinarith
  ·
    have hnat := pow_card_primeFactors_mul_le 23 (p - 1) hpnz
    rw [← hk, h9, show ∏ r ∈ (Finset.range 23).filter Nat.Prime, r = 9699690 by decide,
      show ((Finset.range 23).filter Nat.Prime).card = 8 by decide] at hnat
    norm_num at hnat
    have hp9 : 223092871 ≤ p := by omega
    have hpR9 : (223092871 : ℝ) ≤ p := by exact_mod_cast hp9
    have hsge' : (14936 : ℝ) ≤ s := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
    have hL : (18.71 : ℝ) ≤ Real.log p := by
      have : Real.log ((2 : ℝ) ^ 27) ≤ Real.log p := Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hc := bachC_le p 14936 18.71 hp1.le (by norm_num) (by norm_num) hsge' hL
    have hc' : (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p p ≤ 0.7265 := by
      have : (2/3 : ℝ) * (1 + 2 / 14936 + 3 / p) * (1 + (5/3) / 18.71)
          ≤ (2/3) * (1 + 2 / 14936 + 3 / 223092871) * (1 + (5/3) / 18.71) := by gcongr
      norm_num at hc this ⊢; linarith
    have hA : (2 : ℝ) ^ k - 1 ≤ 511 := by rw [h9]; norm_num
    refine finish_aux _ _ _ _ 511 0.7265 _ hspos hA0 hA hc0 hc' hLpos.le hU14 ?_
    nlinarith
  ·
    have hnat := pow_card_primeFactors_mul_le 16 (p - 1) hpnz
    rw [← hk, show ∏ r ∈ (Finset.range 16).filter Nat.Prime, r = 30030 by decide,
      show ((Finset.range 16).filter Nat.Prime).card = 6 by decide] at hnat
    have h16 : 16 ^ 10 ≤ 16 ^ k := Nat.pow_le_pow_right (by norm_num) h10
    have hp10 : 1600000000 ≤ p := by
      have := Nat.mul_le_mul_right 30030 h16
      norm_num at hnat this; omega
    have hpR10 : (1600000000 : ℝ) ≤ p := by exact_mod_cast hp10
    have hX4 : ((2 : ℝ) ^ k) ^ 4 * 30030 ≤ p * 16 ^ 6 := by
      have : 16 ^ k * 30030 ≤ p * 16 ^ 6 :=
        hnat.trans (Nat.mul_le_mul_right _ (Nat.sub_le p 1))
      rw [← pow_mul, mul_comm k 4, pow_mul]
      exact_mod_cast (by norm_num at this ⊢; exact this)
    have hsge2 : (40000 : ℝ) ≤ s := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
    set t := √s with ht_def
    have ht2 : t ^ 2 = s := Real.sq_sqrt hspos.le
    have htpos : 0 < t := Real.sqrt_pos.2 hspos
    have htge : (200 : ℝ) ≤ t := (Real.le_sqrt (by norm_num) hspos.le).2 (by linarith)
    have ht4 : (p : ℝ) = t ^ 4 := by rw [← hs2, ← ht2]; ring
    have hX : (2 : ℝ) ^ k - 1 ≤ 4.87 * t := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : 4.87 * t ≤ (2 : ℝ) ^ k := by linarith
      have h2 : (4.87 * t) ^ 4 ≤ ((2 : ℝ) ^ k) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
      rw [ht4] at hX4
      have : (0:ℝ) < t ^ 4 := by positivity
      nlinarith
    have hU : Real.log p ≤ 4 * (5.5451774464 + t / 256 - 1) := by
      have h := log_le_tangent t 256 htpos (by norm_num)
      have : Real.log (256 : ℝ) = 8 * Real.log 2 := by
        rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
      rw [ht4, Real.log_pow]; push_cast; linarith
    have hL : (18.02 : ℝ) ≤ Real.log p := by
      have : Real.log ((2 : ℝ) ^ 26) ≤ Real.log p := Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hc := bachC_le p 10000 18.02 hp1.le (by norm_num) (by norm_num) hsge hL
    have h3 : 3 / (p : ℝ) ≤ 3 / 10 ^ 8 := by gcongr
    have hc' : (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p p ≤ 0.7286 := by
      have : (2/3 : ℝ) * (1 + 2 / 10000 + 3 / p) * (1 + (5/3) / 18.02)
          ≤ (2/3) * (1 + 2 / 10000 + 3 / 10^8) * (1 + (5/3) / 18.02) := by gcongr
      norm_num at hc this ⊢; linarith
    refine finish_aux _ _ _ _ (4.87 * t) 0.7286 _ hspos hA0 hX hc0 hc' hLpos.le hU ?_
    rw [← ht2]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 htge) (sub_nonneg.2 htge)) (sub_nonneg.2 htge),
      mul_nonneg (sub_nonneg.2 htge) (sub_nonneg.2 htge)]
end Erdos985
end
section
open Complex MeasureTheory Set
namespace Erdos985.Analytic.PerronKernel
theorem Zdcesaro_def (t : ℝ) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)))) t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)) :=
  Classical.choose_spec (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ))) t
theorem Zdcesaro_eq :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)))) = fun (t : ℝ) => (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)) := by
  funext t
  exact Zdcesaro_def t
lemma continuous_cesaro : Continuous (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)))) := by
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.Zdcesaro_eq]; fun_prop
lemma cesaro_eq_on_Ioi {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)))) t = indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ) t
      - indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1 : ℂ) : ℝ → ℂ) t := by
  simp only [mem_Ioi] at ht
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.Zdcesaro_eq]
  by_cases h1 : t ≤ 1
  · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
    rw [indicator_of_mem hm, indicator_of_mem hm, cpow_one, max_eq_right (by linarith)]
    push_cast; ring
  · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
    rw [indicator_of_notMem hm, indicator_of_notMem hm, max_eq_left (by linarith)]
    simp
lemma hasMellin_cesaro {s : ℂ} (hs : 0 < s.re) : HasMellin (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)))) s (1 / (s * (s + 1))) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have h := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hval : 1 / s - 1 / (s + 1) = 1 / (s * (s + 1)) := by field_simp; ring
  rw [hval] at h
  refine ⟨?_, ?_⟩
  · have := h.1
    unfold MellinConvergent at this ⊢
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [cesaro_eq_on_Ioi ht]
  · rw [← h.2]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [cesaro_eq_on_Ioi ht]
lemma denom_ne_zero (c : ℝ) (hc : 0 < c) (t : ℝ) :
    ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) ≠ 0 := by
  have h0 : ((c : ℂ) + t * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : ((c : ℂ) + t * I + 1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  exact mul_ne_zero h0 h1
lemma norm_denom_ge (c : ℝ) (hc : 0 < c) (t : ℝ) :
    min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)‖ := by
  have hs : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hs1 : ‖(c : ℂ) + t * I‖ ^ 2 ≤ ‖(c : ℂ) + t * I + 1‖ ^ 2 := by
    rw [hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; nlinarith
  have hn1 : ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + 1‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hs1
  rw [norm_mul]
  calc min (c ^ 2) 1 * (1 + t ^ 2) ≤ c ^ 2 + t ^ 2 := by
        rcases le_total (c ^ 2) 1 with h | h
        · rw [min_eq_left h]; nlinarith [sq_nonneg t]
        · rw [min_eq_right h]; linarith
    _ = ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I‖ := by rw [← hs]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)
lemma continuous_inv_denom (c : ℝ) (hc : 0 < c) :
    Continuous fun t : ℝ => 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  by
  have h1 : Continuous fun t : ℝ => ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) := by
    have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    exact h0.mul (h0.add continuous_const)
  exact Continuous.div (f := fun _ => (1:ℂ)) continuous_const h1 (denom_ne_zero c hc)
lemma integrable_inv_denom (c : ℝ) (hc : 0 < c) :
    Integrable fun t : ℝ => 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (min (c ^ 2) 1)⁻¹)
    (continuous_inv_denom c hc).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_div, norm_one]
  have h := norm_denom_ge c hc t
  have hpos : 0 < min (c ^ 2) 1 * (1 + t ^ 2) := by positivity
  calc 1 / ‖((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)‖ ≤ 1 / (min (c ^ 2) 1 * (1 + t ^ 2)) :=
        one_div_le_one_div_of_le hpos h
    _ = (min (c ^ 2) 1)⁻¹ * (1 + t ^ 2)⁻¹ := by rw [one_div, mul_inv]
theorem perron_cesaro_aux (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (max 0 (1 - 1 / y) : ℝ) := by
  have hmel : ∀ t : ℝ, mellin (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)))) ((c : ℂ) + t * I)
      = 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := fun t =>
    (hasMellin_cesaro (s := (c : ℂ) + t * I) (by simpa using hc)).2
  have hconv : MellinConvergent (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)))) (c : ℂ) := (hasMellin_cesaro (by simpa using hc)).1
  have hvert : VerticalIntegrable (mellin (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ))))) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact integrable_inv_denom c hc
  have hinv := mellinInv_mellin_eq (E := ℂ) c (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)))) (x := 1 / y) (by positivity) hconv hvert
    continuous_cesaro.continuousAt
  have hint : (∫ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = ∫ t : ℝ, (((1 / y : ℝ)) : ℂ) ^ (-((c : ℂ) + t * I)) • mellin (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℂ, ∀ (t : ℝ), f t = (open Complex MeasureTheory Set in ((max 0 (1 - t) : ℝ) : ℂ)))) ((c : ℂ) + t * I) := by
    congr 1
    funext t
    rw [hmel t, smul_eq_mul, ofReal_div, ofReal_one, one_div (y : ℂ),
      inv_cpow_ofReal_nonneg hy.le, cpow_neg, inv_inv]
    ring
  rw [hint]
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  have h2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; ring
  rw [h2] at hinv
  rw [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.Zdcesaro_def] at hinv
  exact hinv
end Erdos985.Analytic.PerronKernel
end
section
open Complex MeasureTheory Set Filter
namespace Erdos985.Analytic.PerronKernel
theorem perron_kernel (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = 2 * Real.pi * (if 1 ≤ y then 1 - 1 / y else 0) := by
  have h := perron_cesaro_aux y c hy hc
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (ofReal_ne_zero.2 this.ne')
  have h' : (∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = 2 * Real.pi * ((max 0 (1 - 1 / y) : ℝ) : ℂ) := by
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  rw [h']
  congr 1
  split_ifs with h1
  · rw [max_eq_right (by rw [sub_nonneg, div_le_one hy]; exact h1)]
  · rw [max_eq_left (by
      rw [sub_nonpos, le_div_iff₀ hy]; linarith)]
theorem ZdK_def (c y t : ℝ) :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ → ℂ, ∀ (c y t : ℝ), f c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))))) c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) :=
  Classical.choose_spec (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ → ℂ, ∀ (c y t : ℝ), f c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))) c y t
theorem ZdK_eq :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ → ℂ, ∀ (c y t : ℝ), f c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))))) = fun (c y t : ℝ) => (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) := by
  funext c y t
  exact ZdK_def c y t
lemma norm_K (c y t : ℝ) (hy : 0 < y) :
    ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ → ℂ, ∀ (c y t : ℝ), f c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))))) c y t‖ = y ^ c * ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ := by
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdK_eq]
  rw [div_eq_mul_one_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
  simp
lemma integrable_K (c y : ℝ) (hc : 0 < c) (hy : 0 < y) : Integrable ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ → ℂ, ∀ (c y t : ℝ), f c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))))) c y) := by
  have hcont : Continuous ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ → ℂ, ∀ (c y t : ℝ), f c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))))) c y) := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdK_eq]
    have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    have h1 : Continuous fun t : ℝ => ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) :=
      h0.mul (h0.add continuous_const)
    exact (h0.const_cpow (Or.inl (ofReal_ne_zero.2 hy.ne'))).div h1 (denom_ne_zero c hc)
  refine Integrable.mono' ((integrable_inv_denom c hc).norm.const_mul (y ^ c))
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_K c y t hy]
lemma integral_norm_K (c y : ℝ) (hy : 0 < y) :
    ∫ t : ℝ, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ → ℂ, ∀ (c y t : ℝ), f c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))))) c y t‖ = y ^ c * ∫ t : ℝ, ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ := by
  simp_rw [norm_K c y _ hy]
  rw [integral_const_mul]
lemma term_mul_eq (a : ℕ → ℂ) (c t : ℝ) (N n : ℕ) (hN : 1 ≤ N) :
    LSeries.term a ((c : ℂ) + t * I) n * ((N : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = if n = 0 then 0 else a n * (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ → ℂ, ∀ (c y t : ℝ), f c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))))) c ((N : ℝ) / n) t := by
  rw [LSeries.term_def]
  split_ifs with hn
  · simp
  · simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdK_eq]
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have hnc : (n : ℂ) ^ ((c : ℂ) + t * I) ≠ 0 := by
      rw [cpow_ne_zero_iff]; left; exact_mod_cast hn
    rw [ofReal_div, div_eq_mul_inv ((N : ℝ) : ℂ), ← ofReal_inv, mul_cpow_ofReal_nonneg
      (by positivity) (by positivity), ofReal_inv, inv_cpow_ofReal_nonneg hn0.le, ofReal_natCast,
      ofReal_natCast]
    field_simp
theorem perron_weighted (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioo 0 N, a n * (1 - (n : ℂ) / N)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * (N : ℂ) ^ ((c : ℂ) + t * I)
          / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  set C := ∫ t : ℝ, ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < (N : ℝ) / n := fun n hn =>
    div_pos hN0 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  let G : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else a n * (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ → ℂ, ∀ (c y t : ℝ), f c y t = (open Complex MeasureTheory Set Filter in (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))))) c ((N : ℝ) / n) t
  have hG_int : ∀ n, Integrable (G n) := by
    intro n
    by_cases hn : n = 0
    · simp only [G, hn, ↓reduceIte]; exact integrable_zero _ _ _
    · simp only [G, hn, ↓reduceIte]; exact (integrable_K c _ hc (hpos n hn)).const_mul _
  have hG_norm : ∀ n, ∫ t, ‖G n t‖ = if n = 0 then 0 else ‖a n‖ * (((N : ℝ) / n) ^ c * C) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte, norm_mul]
      rw [integral_const_mul, integral_norm_K c _ (hpos n hn)]
  have hsum : Summable fun n => ∫ t, ‖G n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (ha.mul_left ((N : ℝ) ^ c * C))
    rw [hG_norm]
    split_ifs with hn
    · have : 0 ≤ ‖a n‖ / (n : ℝ) ^ c := div_nonneg (norm_nonneg _) (by positivity)
      positivity
    · rw [Real.div_rpow hN0.le (Nat.cast_nonneg n)]
      apply le_of_eq
      ring
  have hfun : (fun t : ℝ => LSeries a ((c : ℂ) + t * I) * (N : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) = fun t => ∑' n, G n t := by
    funext t
    rw [mul_div_assoc, LSeries, ← tsum_mul_right]
    congr 1
    funext n
    exact term_mul_eq a c t N n hN
  have hGint : ∀ n, ∫ t, G n t = if n = 0 then 0 else
      a n * (2 * Real.pi * ((if 1 ≤ (N : ℝ) / n then 1 - 1 / ((N : ℝ) / n) else 0 : ℝ) : ℂ)) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte]
      rw [integral_const_mul]
      simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdK_eq]
      rw [perron_kernel _ c (hpos n hn) hc]
  rw [hfun, ← integral_tsum_of_summable_integral_norm hG_int hsum]
  simp_rw [hGint]
  rw [tsum_eq_sum (s := Finset.Ioo 0 N), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioo] at hn
    have hn0 : n ≠ 0 := by omega
    have hle : 1 ≤ (N : ℝ) / n := by
      rw [one_le_div (Nat.cast_pos.2 (by omega))]; exact_mod_cast hn.2.le
    simp only [hn0, hle, ↓reduceIte]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    push_cast
    field_simp
  · intro n hn
    rw [Finset.mem_Ioo] at hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte]
      have hnN : N ≤ n := by omega
      rcases eq_or_lt_of_le hnN with h | h
      · subst h
        have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0
        simp [div_self (show (N : ℝ) ≠ 0 by exact_mod_cast hn0)]
      · have hlt : ¬ 1 ≤ (N : ℝ) / n := by
          rw [not_le, div_lt_one (Nat.cast_pos.2 (by omega))]; exact_mod_cast h
        simp [hlt]
end Erdos985.Analytic.PerronKernel
end
section
open Complex MeasureTheory Set Filter Topology
namespace Erdos985.Analytic.PerronKernel
theorem ZdresExpr_def (w : ℂ) (t : ℝ) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)) :=
  Classical.choose_spec (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w))) w t
theorem ZdresExpr_eq :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) = fun (w : ℂ) (t : ℝ) => (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)) := by
  funext w t
  exact ZdresExpr_def w t
theorem ZdresFun_def (w : ℂ) (t : ℝ) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0) :=
  Classical.choose_spec (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0)) w t
theorem ZdresFun_eq :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) = fun (w : ℂ) (t : ℝ) => (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0) := by
  funext w t
  exact ZdresFun_def w t
lemma resExpr_one (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) : (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w 1 = 0 := by
  have h1 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
  have h2 : 1 + w ≠ 0 := by rwa [add_comm]
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdresExpr_eq]
  simp only [ofReal_one, one_cpow]
  field_simp
  ring
lemma resFun_eq_on_Ioi (w : ℂ) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w t = (1 / (w * (w + 1))) • indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (-w) : ℝ → ℂ) t
      - (1 / w) • indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ) t
      + (1 / (1 + w)) • indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1 : ℂ) : ℝ → ℂ) t := by
  simp only [mem_Ioi] at ht
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdresFun_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdresExpr_eq]
  by_cases h1 : t ≤ 1
  · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
    simp only [h1, ↓reduceIte]
    rw [indicator_of_mem hm, indicator_of_mem hm, indicator_of_mem hm, cpow_one]
    simp only [smul_eq_mul]
    ring
  · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
    simp only [h1, ↓reduceIte]
    rw [indicator_of_notMem hm, indicator_of_notMem hm, indicator_of_notMem hm]
    simp
lemma hasMellin_resFun {s w : ℂ} (hs : 0 < s.re) (hsw : w.re < s.re) (hw0 : w ≠ 0)
    (hw1 : w ≠ -1) : HasMellin ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w) s (1 / ((s - w) * s * (s + 1))) := by
  have hA := hasMellin_cpow_Ioc (-w) (s := s) (by simp; linarith)
  have hB := hasMellin_one_Ioc hs
  have hC := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have hA' := hasMellin_const_smul hA.1 (1 / (w * (w + 1)))
  have hB' := hasMellin_const_smul hB.1 (1 / w)
  have hC' := hasMellin_const_smul hC.1 (1 / (1 + w))
  have hAB := hasMellin_sub hA'.1 hB'.1
  have h := hasMellin_add hAB.1 hC'.1
  rw [hAB.2, hA'.2, hB'.2, hC'.2, hA.2, hB.2, hC.2] at h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsw0 : s - w ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsw0' : s + -w ≠ 0 := by rwa [← sub_eq_add_neg]
  have h1 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
  have h2 : 1 + w ≠ 0 := by rwa [add_comm]
  have hval : (1 / (w * (w + 1))) • (1 / (s + -w)) - (1 / w) • (1 / s)
      + (1 / (1 + w)) • (1 / (s + 1)) = 1 / ((s - w) * s * (s + 1)) := by
    simp only [smul_eq_mul, ← sub_eq_add_neg]
    field_simp
    ring
  rw [hval] at h
  refine ⟨?_, ?_⟩
  · have := h.1
    unfold MellinConvergent at this ⊢
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [resFun_eq_on_Ioi w ht]
  · rw [← h.2]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [resFun_eq_on_Ioi w ht]
lemma continuousAt_resFun (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w) x₀ := by
  set a := min (x₀ / 2) (1 / 2) with ha
  have ha0 : 0 < a := lt_min (by positivity) (by norm_num)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hax : a < x₀ := (min_le_left _ _).trans_lt (by linarith)
  let g : ℝ → ℂ := fun t => if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w (max t a) else 0
  have hE : Continuous fun t : ℝ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w (max t a) := by
    have hm : Continuous fun t : ℝ => max t a := continuous_id.max continuous_const
    have hpow : Continuous fun t : ℝ => ((max t a : ℝ) : ℂ) ^ (-w) := by
      refine continuous_iff_continuousAt.2 fun t => ?_
      refine ContinuousAt.cpow (continuous_ofReal.comp hm).continuousAt continuousAt_const ?_
      exact ofReal_mem_slitPlane.2 (lt_of_lt_of_le ha0 (le_max_right _ _))
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdresExpr_eq]
    exact ((hpow.div_const _).sub continuous_const).add
      ((continuous_ofReal.comp hm).div_const _)
  have hg : Continuous g := by
    refine continuous_if_le continuous_id continuous_const hE.continuousOn
      continuous_const.continuousOn (fun t ht => ?_)
    rw [ht, max_eq_left ha1]
    exact resExpr_one w hw0 hw1
  have hev : g =ᶠ[𝓝 x₀] (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w := by
    filter_upwards [Ioi_mem_nhds hax] with t ht
    simp only [g, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdresFun_eq, max_eq_left (le_of_lt (mem_Ioi.1 ht))]
  exact hg.continuousAt.congr hev
lemma integrable_inv_denom_res (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : w.re < c) :
    Integrable fun t : ℝ =>
      1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hδ : 0 < c - w.re := by linarith
  have hne : ∀ t : ℝ, ((c : ℂ) + t * I - w) ≠ 0 := by
    intro t h; have := congrArg Complex.re h; simp at this; linarith
  have hcont : Continuous fun t : ℝ =>
      1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
    have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    have h1 : Continuous fun t : ℝ =>
        ((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) :=
      ((h0.sub continuous_const).mul h0).mul (h0.add continuous_const)
    refine Continuous.div (f := fun _ => (1:ℂ)) continuous_const h1 (fun t => ?_)
    rw [mul_assoc]
    exact mul_ne_zero (hne t) (denom_ne_zero c hc t)
  refine Integrable.mono' ((integrable_inv_denom c hc).norm.const_mul (c - w.re)⁻¹)
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hge : c - w.re ≤ ‖(c : ℂ) + t * I - w‖ := by
    have := re_le_norm ((c : ℂ) + t * I - w); simpa using this
  rw [mul_assoc, norm_div, norm_div, norm_one, norm_mul]
  rw [← one_div_mul_one_div, ← one_div (c - w.re)]
  exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hδ hge)
    (one_div_nonneg.2 (norm_nonneg _))
theorem perron_residue_aux (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w.re < c)
    (hw0 : w ≠ 0) (hw1 : w ≠ -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + (x : ℂ) ^ (-1 : ℂ) / (1 + w) := by
  have hx0 : 0 < x := by linarith
  have hmel : ∀ t : ℝ, mellin ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w) ((c : ℂ) + t * I)
      = 1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := fun t =>
    (hasMellin_resFun (s := (c : ℂ) + t * I) (by simpa using hc) (by simpa using hw) hw0 hw1).2
  have hconv : MellinConvergent ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w) (c : ℂ) :=
    (hasMellin_resFun (by simpa using hc) (by simpa using hw) hw0 hw1).1
  have hvert : VerticalIntegrable (mellin ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w)) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact integrable_inv_denom_res c hc w hw
  have hinv := mellinInv_mellin_eq (E := ℂ) c ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w) (x := 1 / x) (by positivity) hconv hvert
    (continuousAt_resFun w hw0 hw1 (by positivity))
  have hint : (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = ∫ t : ℝ, (((1 / x : ℝ)) : ℂ) ^ (-((c : ℂ) + t * I)) • mellin ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in if t ≤ 1 then (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (w : ℂ) (t : ℝ), f w t = (open Complex MeasureTheory Set Filter Topology in (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)))) w t else 0))) w) ((c : ℂ) + t * I) := by
    congr 1
    funext t
    rw [hmel t, smul_eq_mul, ofReal_div, ofReal_one, one_div (x : ℂ),
      inv_cpow_ofReal_nonneg hx0.le, cpow_neg, inv_inv]
    ring
  rw [hint]
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  have h2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; ring
  rw [h2] at hinv
  rw [hinv]
  have hle : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdresFun_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdresExpr_eq]
  simp only [hle, ↓reduceIte]
  rw [ofReal_div, ofReal_one, one_div (x : ℂ), inv_cpow_ofReal_nonneg hx0.le, cpow_neg, inv_inv,
    cpow_neg_one]
end Erdos985.Analytic.PerronKernel
end
section
open Complex MeasureTheory Set Filter Topology
namespace Erdos985.Analytic.PerronAux
lemma inv_ofReal_cpow_neg {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((y⁻¹ : ℝ) : ℂ) ^ (-s) = (y : ℂ) ^ s := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm),
    cpow_neg, inv_inv]
theorem perron_of_mellin {f : ℝ → ℂ} {F : ℂ → ℂ} {y c : ℝ} (hy : 0 < y)
    (hf : MellinConvergent f c) (hF : ∀ t : ℝ, mellin f (c + t * I) = F (c + t * I))
    (hFi : Integrable fun t : ℝ => F (c + t * I)) (hfc : ContinuousAt f y⁻¹) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) * F (c + t * I)
      = f y⁻¹ := by
  have hV : VerticalIntegrable (mellin f) c := by
    unfold VerticalIntegrable
    simp_rw [hF]; exact hFi
  have := mellinInv_mellin_eq c f (inv_pos.2 hy) hf hV hfc
  rw [← this, mellinInv]
  simp_rw [hF, inv_ofReal_cpow_neg hy, smul_eq_mul]
  rw [Complex.real_smul]
  push_cast; ring
lemma continuousAt_indicator_Ioc {h : ℝ → ℂ} {t : ℝ} (ht : 0 < t) (hh : ContinuousAt h t)
    (h1 : t = 1 → h 1 = 0) : ContinuousAt (indicator (Ioc 0 1) h) t := by
  rcases lt_trichotomy t 1 with h' | rfl | h'
  · refine hh.congr ?_
    filter_upwards [Ioo_mem_nhds ht h'] with u hu
    rw [indicator_of_mem (show u ∈ Ioc (0:ℝ) 1 from ⟨hu.1, hu.2.le⟩)]
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · refine (hh.continuousWithinAt).congr_of_eventuallyEq ?_ (by simp)
      filter_upwards [Ioc_mem_nhdsLE (show (0:ℝ) < 1 by norm_num)] with u hu
      rw [indicator_of_mem hu]
    · have : ContinuousWithinAt (fun _ : ℝ => (0 : ℂ)) (Ici 1) 1 := continuousWithinAt_const
      refine this.congr_of_eventuallyEq ?_ (by simp [h1 rfl])
      filter_upwards [self_mem_nhdsWithin] with u hu
      rcases eq_or_lt_of_le (show (1:ℝ) ≤ u from hu) with rfl | hu'
      · simp [h1 rfl]
      · rw [indicator_of_notMem (fun hm : u ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 hu'))]
  · refine continuousAt_const.congr (f := fun _ => (0:ℂ)) ?_
    filter_upwards [Ioi_mem_nhds h'] with u hu
    rw [indicator_of_notMem (fun hm : u ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 (show 1 < u from hu)))]
theorem ZdP_def (a : ℂ) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)) :=
  Classical.choose_spec (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a))) a
theorem ZdP_eq :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) = fun (a : ℂ) => (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)) := by
  funext a
  exact ZdP_def a
lemma hasMellin_P (a : ℂ) {s : ℂ} (hs : 0 < s.re + a.re) : HasMellin ((Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a) s (1 / (s + a)) := by
  rw [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronAux.ZdP_def]; exact hasMellin_cpow_Ioc a hs
lemma hasMellin_three (α β γ a b d : ℂ) {s : ℂ} (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re)
    (hd : 0 < s.re + d.re) :
    HasMellin (indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
      γ * (t : ℂ) ^ d)) s (α * (1 / (s + a)) + β * (1 / (s + b)) + γ * (1 / (s + d))) := by
  have e : indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
      γ * (t : ℂ) ^ d) = fun t => (α • (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a t + β • (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) b t) + γ • (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) d t := by
    funext t
    by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronAux.ZdP_eq, ht]
  rw [e]
  have h1 := hasMellin_P a ha
  have h2 := hasMellin_P b hb
  have h3 := hasMellin_P d hd
  have k1 := hasMellin_const_smul h1.1 α
  have k2 := hasMellin_const_smul h2.1 β
  have k3 := hasMellin_const_smul h3.1 γ
  have k12 := hasMellin_add k1.1 k2.1
  have k := hasMellin_add k12.1 k3.1
  refine ⟨k.1, ?_⟩
  rw [k.2, k12.2, k1.2, k2.2, k3.2, h1.2, h2.2, h3.2]
  simp [smul_eq_mul]
lemma integrableOn_P (a : ℂ) (ha : -1 < a.re) : IntegrableOn ((Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a) (Ioi 0) := by
  have := (hasMellin_P a (s := 1) (by simp; linarith)).1
  unfold MellinConvergent at this
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp
lemma hasMellin_log_P (a : ℂ) {s : ℂ} (ha : -1 < a.re) (hs : 0 < s.re + a.re) :
    HasMellin (fun t : ℝ => (Real.log t : ℂ) * (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a t) s (-1 / (s + a) ^ 2) := by
  have hloc : LocallyIntegrableOn ((Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a) (Ioi 0) := (integrableOn_P a ha).locallyIntegrableOn
  have htop : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a =O[atTop] (· ^ (-(s.re + 1))) := by
    refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronAux.ZdP_eq, indicator_of_notMem (fun hm : t ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 ht))]
  have hbot : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a =O[𝓝[>] 0] (· ^ (-(-a.re))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    rw [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronAux.ZdP_def, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht.1, ht.2.le⟩),
      norm_cpow_eq_rpow_re_of_pos ht.1, neg_neg, one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  obtain ⟨hconv, hder⟩ := mellin_hasDerivAt_of_isBigO_rpow hloc htop (by linarith) hbot
    (by linarith)
  have hne : s + a ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hev : mellin ((Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a) =ᶠ[𝓝 s] fun z => (z + a)⁻¹ := by
    have hopen : IsOpen {z : ℂ | 0 < z.re + a.re} :=
      isOpen_lt continuous_const (continuous_re.add continuous_const)
    filter_upwards [hopen.mem_nhds hs] with z hz
    rw [(hasMellin_P a hz).2, one_div]
  have h2 : HasDerivAt (fun z => (z + a)⁻¹) (-1 / (s + a) ^ 2) s := by
    have := ((hasDerivAt_id s).add_const a).inv hne
    simp only [id] at this
    convert this using 1 <;> try rfl
  have h3 := (h2.congr_of_eventuallyEq hev).unique hder
  refine ⟨?_, ?_⟩
  · refine (hconv).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Complex.real_smul]
  · rw [h3]; unfold mellin; congr 1
theorem Zdprof_def (κ a₀ α β γ a b d : ℂ) :
    (Classical.choose (⟨_, fun _ _ _ _ _ _ _ _ => rfl⟩ : ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℝ → ℂ, ∀ (κ a₀ α β γ a b d : ℂ), f κ a₀ α β γ a b d = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) + (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))))) κ a₀ α β γ a b d = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) + (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))) :=
  Classical.choose_spec (⟨_, fun _ _ _ _ _ _ _ _ => rfl⟩ : ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℝ → ℂ, ∀ (κ a₀ α β γ a b d : ℂ), f κ a₀ α β γ a b d = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) + (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d)))) κ a₀ α β γ a b d
theorem Zdprof_eq :
    (Classical.choose (⟨_, fun _ _ _ _ _ _ _ _ => rfl⟩ : ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℝ → ℂ, ∀ (κ a₀ α β γ a b d : ℂ), f κ a₀ α β γ a b d = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) + (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))))) = fun (κ a₀ α β γ a b d : ℂ) => (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) + (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))) := by
  funext κ a₀ α β γ a b d
  exact Zdprof_def κ a₀ α β γ a b d
lemma hasMellin_prof (κ a₀ α β γ a b d : ℂ) {s : ℂ} (ha₀ : -1 < a₀.re) (ha₀' : 0 < s.re + a₀.re)
    (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re) (hd : 0 < s.re + d.re) :
    HasMellin ((Classical.choose (⟨_, fun _ _ _ _ _ _ _ _ => rfl⟩ : ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℝ → ℂ, ∀ (κ a₀ α β γ a b d : ℂ), f κ a₀ α β γ a b d = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) + (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))))) κ a₀ α β γ a b d) s (κ * (-1 / (s + a₀) ^ 2) +
      (α * (1 / (s + a)) + β * (1 / (s + b)) + γ * (1 / (s + d)))) := by
  have e : (Classical.choose (⟨_, fun _ _ _ _ _ _ _ _ => rfl⟩ : ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℝ → ℂ, ∀ (κ a₀ α β γ a b d : ℂ), f κ a₀ α β γ a b d = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) + (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))))) κ a₀ α β γ a b d = fun t => κ • ((Real.log t : ℂ) * (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℝ → ℂ, ∀ (a : ℂ), f a = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)))) a₀ t) +
      indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
      γ * (t : ℂ) ^ d) t := by
    funext t
    by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronAux.Zdprof_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronAux.ZdP_eq, ht]
  rw [e]
  have h1 := hasMellin_log_P a₀ ha₀ ha₀'
  have k1 := hasMellin_const_smul h1.1 κ
  have h2 := hasMellin_three α β γ a b d ha hb hd
  have k := hasMellin_add k1.1 h2.1
  refine ⟨k.1, ?_⟩
  rw [k.2, k1.2, h1.2, h2.2, smul_eq_mul]
lemma continuousAt_prof (κ a₀ α β γ a b d : ℂ) {t : ℝ} (ht : 0 < t)
    (h1 : t = 1 → α + β + γ = 0) : ContinuousAt ((Classical.choose (⟨_, fun _ _ _ _ _ _ _ _ => rfl⟩ : ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℝ → ℂ, ∀ (κ a₀ α β γ a b d : ℂ), f κ a₀ α β γ a b d = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) + (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))))) κ a₀ α β γ a b d) t := by
  rw [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronAux.Zdprof_def]
  refine continuousAt_indicator_Ioc ht ?_ (fun h => by simp [h1 h])
  have hc : ∀ e : ℂ, ContinuousAt (fun u : ℝ => (u : ℂ) ^ e) t :=
    fun e => continuousAt_ofReal_cpow_const t e (Or.inr ht.ne')
  have hl : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) t :=
    continuous_ofReal.continuousAt.comp (Real.continuousAt_log ht.ne')
  exact (continuousAt_const.mul (hl.mul (hc a₀))).add
    (((continuousAt_const.mul (hc a)).add (continuousAt_const.mul (hc b))).add
      (continuousAt_const.mul (hc d)))
theorem perron_prof {y c : ℝ} (hy : 0 < y) (κ a₀ α β γ a b d : ℂ)
    (ha₀ : -1 < a₀.re) (ha₀' : 0 < c + a₀.re) (ha : 0 < c + a.re) (hb : 0 < c + b.re)
    (hd : 0 < c + d.re) (h1 : y⁻¹ = 1 → α + β + γ = 0) {F : ℂ → ℂ}
    (hF : ∀ t : ℝ, κ * (-1 / ((c : ℂ) + t * I + a₀) ^ 2) +
      (α * (1 / ((c : ℂ) + t * I + a)) + β * (1 / ((c : ℂ) + t * I + b)) +
        γ * (1 / ((c : ℂ) + t * I + d))) = F (c + t * I))
    (hFi : Integrable fun t : ℝ => F (c + t * I)) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) * F (c + t * I)
      = (Classical.choose (⟨_, fun _ _ _ _ _ _ _ _ => rfl⟩ : ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℂ → ℝ → ℂ, ∀ (κ a₀ α β γ a b d : ℂ), f κ a₀ α β γ a b d = (open Complex MeasureTheory Set Filter Topology in indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) + (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))))) κ a₀ α β γ a b d y⁻¹ := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := by intro t; simp
  refine perron_of_mellin hy ?_ ?_ hFi (continuousAt_prof _ _ _ _ _ _ _ _ (inv_pos.2 hy) h1)
  · exact (hasMellin_prof κ a₀ α β γ a b d (s := (c : ℂ)) ha₀ (by simpa using ha₀')
      (by simpa using ha) (by simpa using hb) (by simpa using hd)).1
  · intro t
    rw [(hasMellin_prof κ a₀ α β γ a b d (s := (c : ℂ) + t * I) ha₀ (by rw [hre]; exact ha₀')
      (by rw [hre]; exact ha) (by rw [hre]; exact hb) (by rw [hre]; exact hd)).2, hF]
end Erdos985.Analytic.PerronAux
end
section
open Complex MeasureTheory Set Filter Topology
namespace Erdos985.Analytic.PerronAux
lemma norm_line_sq (c t : ℝ) : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, normSq_add_mul_I]
lemma line_add_one (c t : ℝ) : (c : ℂ) + t * I + 1 = ((c + 1 : ℝ) : ℂ) + t * I := by
  push_cast; ring
lemma abs_im_le_norm_line (c t : ℝ) : |t| ≤ ‖(c : ℂ) + t * I‖ := by
  simpa using abs_im_le_norm ((c : ℂ) + t * I)
lemma re_le_norm_sub (c t : ℝ) (w : ℂ) : c - w.re ≤ ‖(c : ℂ) + t * I - w‖ := by
  have := re_le_norm ((c : ℂ) + t * I - w)
  simpa using this
lemma abs_sub_im_le_norm_sub (c t : ℝ) (w : ℂ) : |t - w.im| ≤ ‖(c : ℂ) + t * I - w‖ := by
  have := abs_im_le_norm ((c : ℂ) + t * I - w)
  simpa using this
lemma c_le_norm_line {c : ℝ} (_hc : 0 ≤ c) (t : ℝ) : c ≤ ‖(c : ℂ) + t * I‖ := by
  have := re_le_norm ((c : ℂ) + t * I)
  simpa using this
lemma norm_line_le_add_one {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + 1‖ := by
  rw [line_add_one]
  have h1 := norm_line_sq c t
  have h2 := norm_line_sq (c + 1) t
  have := norm_nonneg ((c : ℂ) + t * I)
  have := norm_nonneg (((c + 1 : ℝ) : ℂ) + t * I)
  nlinarith
lemma one_le_norm_line_add_one {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : 1 ≤ ‖(c : ℂ) + t * I + 1‖ := by
  rw [line_add_one]; have := c_le_norm_line (c := c + 1) (by linarith) t; linarith
lemma min_mul_le_norm_line_sq (c t : ℝ) :
    min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ ^ 2 := by
  rw [norm_line_sq]
  have h1 : min (c ^ 2) 1 ≤ c ^ 2 := min_le_left _ _
  have h2 : min (c ^ 2) 1 ≤ 1 := min_le_right _ _
  nlinarith [sq_nonneg t]
lemma line_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith
lemma line_add_one_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I + 1 ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith
lemma line_sub_ne_zero {c : ℝ} (t : ℝ) {w : ℂ} (hw : w.re < c) : (c : ℂ) + t * I - w ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith
lemma integrable_div_line_two {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hG : Continuous G) {B : ℝ}
    (hB : ∀ t, ‖G t‖ ≤ B) :
    Integrable fun t : ℝ => G t / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine (integrable_inv_one_add_sq.const_mul (B / min (c ^ 2) 1)).mono' ?_ (ae_of_all _ ?_)
  · refine (hG.div (by fun_prop) fun t => ?_).aestronglyMeasurable
    exact mul_ne_zero (line_ne_zero hc t) (line_add_one_ne_zero hc t)
  · intro t
    rw [norm_div, norm_mul]
    have hs := min_mul_le_norm_line_sq c t
    have h1 := norm_line_le_add_one hc.le t
    have hpos : 0 < ‖(c : ℂ) + t * I‖ := norm_pos_iff.2 (line_ne_zero hc t)
    have hpos1 : 0 < ‖(c : ℂ) + t * I + 1‖ := norm_pos_iff.2 (line_add_one_ne_zero hc t)
    have key : min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc ‖G t‖ ≤ B := hB t
      _ = B / min (c ^ 2) 1 * (1 + t ^ 2)⁻¹ * (min (c ^ 2) 1 * (1 + t ^ 2)) := by
          field_simp
      _ ≤ B / min (c ^ 2) 1 * (1 + t ^ 2)⁻¹ *
          (‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖) := by
          gcongr
lemma integrable_div_line_three {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hG : Continuous G) {B : ℝ}
    (hB : ∀ t, ‖G t‖ ≤ B) {w : ℂ} (hw : w.re < c) :
    Integrable fun t : ℝ =>
      G t / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hδ : 0 < c - w.re := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hG' : Continuous fun t : ℝ => G t / ((c : ℂ) + t * I - w) :=
    hG.div (by fun_prop) fun t => line_sub_ne_zero t hw
  have := integrable_div_line_two hc hG' (B := B / (c - w.re)) fun t => by
    rw [norm_div]
    exact div_le_div₀ hB0 (hB t) hδ (re_le_norm_sub c t w)
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only
  rw [div_div, mul_assoc]
lemma norm_cpow_line {x : ℝ} (hx : 0 < x) (c t : ℝ) :
    ‖(x : ℂ) ^ ((c : ℂ) + t * I)‖ = x ^ c := by
  rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
lemma continuous_cpow_line {x : ℝ} (hx : 0 < x) (c : ℝ) :
    Continuous fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) :=
  Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.2 hx.ne'))
lemma norm_perron_kernel {x : ℝ} (hx : 0 < x) (c t : ℝ) (w : ℂ) :
    ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖
      = x ^ c / (‖(c : ℂ) + t * I - w‖ * ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖) := by
  rw [norm_div, norm_cpow_line hx, norm_mul, norm_mul]
lemma integrable_perron_kernel {x c : ℝ} (hx : 0 < x) (hc : 0 < c) {w : ℂ} (hw : w.re < c) :
    Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  integrable_div_line_three hc (continuous_cpow_line hx c) (B := x ^ c)
    (fun t => (norm_cpow_line hx c t).le) hw
lemma integrable_cesaro_kernel {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  integrable_div_line_two hc (continuous_cpow_line hx c) (B := x ^ c)
    (fun t => (norm_cpow_line hx c t).le)
lemma one_div_mul_le_rpow {a b D θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hab : D ≤ a + b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 / (a * b) ≤ (D / 2) ^ (-θ) * (a ^ (-(2 - θ)) + b ^ (-(2 - θ))) := by
  have key : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b → D ≤ a + b →
      1 / (a * b) ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := by
    intro a b ha hb hle hab
    have hb2 : D / 2 ≤ b := by linarith
    have h1 : b ^ (-θ) ≤ (D / 2) ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb2 (by linarith)
    have hp : (0 : ℝ) ≤ 1 - θ := by linarith
    have hap : a ^ (1 - θ) ≤ b ^ (1 - θ) := Real.rpow_le_rpow ha.le hle hp
    have hA : a ^ (-(2 - θ)) = (a * a ^ (1 - θ))⁻¹ := by
      rw [Real.rpow_neg ha.le, show 2 - θ = 1 + (1 - θ) by ring, Real.rpow_add ha, Real.rpow_one]
    have hB : b ^ (-θ) = b ^ (1 - θ) / b := by
      rw [Real.rpow_neg hb.le, show θ = 1 - (1 - θ) by ring, Real.rpow_sub hb, Real.rpow_one]
      field_simp
      rw [show 1 - (1 - (1 - θ)) = 1 - θ by ring]
    have hapos : 0 < a ^ (1 - θ) := Real.rpow_pos_of_pos ha _
    have hbpos : 0 < b ^ (1 - θ) := Real.rpow_pos_of_pos hb _
    calc 1 / (a * b) ≤ b ^ (-θ) * a ^ (-(2 - θ)) := by
          rw [hA, hB, div_le_iff₀ (by positivity)]
          field_simp
          exact hap
      _ ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := by
          gcongr
  have hA0 : 0 ≤ a ^ (-(2 - θ)) := Real.rpow_nonneg ha.le _
  have hB0 : 0 ≤ b ^ (-(2 - θ)) := Real.rpow_nonneg hb.le _
  have hD0 : 0 ≤ (D / 2) ^ (-θ) := Real.rpow_nonneg (by positivity) _
  rcases le_total a b with h | h
  · calc 1 / (a * b) ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := key a b ha hb h hab
      _ ≤ _ := by gcongr; linarith
  · calc 1 / (a * b) = 1 / (b * a) := by rw [mul_comm]
      _ ≤ (D / 2) ^ (-θ) * b ^ (-(2 - θ)) := key b a hb ha h (by linarith)
      _ ≤ _ := by gcongr; linarith
lemma norm_sub_lb {c δ : ℝ} (t : ℝ) {w : ℂ} (hw : w.re ≤ c - δ) :
    min δ 1 / 2 * (1 + |t - w.im|) ≤ ‖(c : ℂ) + t * I - w‖ := by
  have h1 := re_le_norm_sub c t w
  have h2 := abs_sub_im_le_norm_sub c t w
  have h3 : min δ 1 ≤ δ := min_le_left _ _
  have h4 : min δ 1 ≤ 1 := min_le_right _ _
  have h5 := abs_nonneg (t - w.im)
  nlinarith
lemma norm_add_one_lb {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    1 / 2 * (1 + |t|) ≤ ‖(c : ℂ) + t * I + 1‖ := by
  have h1 := one_le_norm_line_add_one hc t
  have h2 : |t| ≤ ‖(c : ℂ) + t * I + 1‖ := by
    rw [line_add_one]; exact abs_im_le_norm_line _ t
  linarith
lemma integrable_one_add_abs_rpow {r : ℝ} (hr : 1 < r) (v : ℝ) :
    Integrable fun t : ℝ => (1 + |t - v|) ^ (-r) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  simpa [Real.norm_eq_abs] using h.comp_sub_right v
lemma integral_one_add_abs_rpow (r v : ℝ) :
    ∫ t : ℝ, (1 + |t - v|) ^ (-r) = ∫ t : ℝ, (1 + |t|) ^ (-r) :=
  integral_sub_right_eq_self (fun t : ℝ => (1 + |t|) ^ (-r)) v
theorem integral_norm_kernel_two_le {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      Integrable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) ∧
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖
        ≤ K * x ^ c * (1 + ‖w‖) ^ (-θ) := by
  set r : ℝ := 2 - θ with hr_def
  have hr : 1 < r := by rw [hr_def]; linarith
  set m : ℝ := min δ 1 / 2 with hm_def
  have hm : 0 < m := by rw [hm_def]; exact half_pos (lt_min hδ one_pos)
  set J : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  set A : ℝ := m ^ (-r) + (1 / 2 : ℝ) ^ (-r) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(6⁻¹ : ℝ) ^ (-θ) * A * J, by positivity, ?_⟩
  intro x c hx hc w hw
  have hwc : w.re < c := by linarith
  set D : ℝ := max 1 ‖w + 1‖ with hD_def
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  set C : ℝ := x ^ c * (D / 2) ^ (-θ) with hC
  have hC0 : 0 ≤ C := by positivity
  set h : ℝ → ℝ := fun t => C * (m ^ (-r) * (1 + |t - w.im|) ^ (-r) +
    (1 / 2 : ℝ) ^ (-r) * (1 + |t - 0|) ^ (-r)) with hh
  have hint : Integrable h :=
    (((integrable_one_add_abs_rpow hr w.im).const_mul _).add
      ((integrable_one_add_abs_rpow hr 0).const_mul _)).const_mul _
  have hpt : ∀ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ ≤ h t := by
    intro t
    set a := ‖(c : ℂ) + t * I - w‖
    set b := ‖(c : ℂ) + t * I + 1‖
    have ha : 0 < a := norm_pos_iff.2 (line_sub_ne_zero t hwc)
    have hb : 0 < b := norm_pos_iff.2 (line_add_one_ne_zero hc t)
    have hDab : D ≤ a + b := by
      refine max_le (by have := one_le_norm_line_add_one hc.le t; linarith) ?_
      have : w + 1 = ((c : ℂ) + t * I + 1) - ((c : ℂ) + t * I - w) := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    have hab := one_div_mul_le_rpow ha hb hD hDab hθ0 hθ1.le
    have hal : a ^ (-r) ≤ m ^ (-r) * (1 + |t - w.im|) ^ (-r) := by
      rw [← Real.mul_rpow hm.le (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (norm_sub_lb t hw) (by linarith)
    have hbl : b ^ (-r) ≤ (1 / 2 : ℝ) ^ (-r) * (1 + |t - 0|) ^ (-r) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity), sub_zero]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (norm_add_one_lb hc.le t) (by linarith)
    rw [norm_div, norm_cpow_line hx, norm_mul, div_eq_mul_one_div]
    simp only [hh, hC]
    rw [mul_assoc]
    gcongr
    refine hab.trans ?_
    rw [hr_def] at hal hbl
    gcongr
  refine ⟨?_, ?_⟩
  · refine hint.mono' ?_ (ae_of_all _ hpt)
    exact ((continuous_cpow_line hx c).div (by fun_prop) fun t =>
      mul_ne_zero (line_sub_ne_zero t hwc) (line_add_one_ne_zero hc t)).aestronglyMeasurable
  · calc _ ≤ ∫ t, h t := integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) hint
          (ae_of_all _ hpt)
      _ = C * A * J := by
          simp only [hh]
          rw [integral_const_mul, integral_add ((integrable_one_add_abs_rpow hr w.im).const_mul _)
            ((integrable_one_add_abs_rpow hr 0).const_mul _), integral_const_mul,
            integral_const_mul, integral_one_add_abs_rpow, integral_one_add_abs_rpow]
          rw [hA]; ring
      _ ≤ _ := by
          rw [hC]
          have hw1 : (1 + ‖w‖) / 6 ≤ D / 2 := by
            have : ‖w‖ ≤ ‖w + 1‖ + 1 := by
              have := norm_sub_le (w + 1) 1; simpa using this
            have h1 : ‖w + 1‖ ≤ D := le_max_right _ _
            have h2 : (1 : ℝ) ≤ D := le_max_left _ _
            linarith
          have hθ' : (D / 2) ^ (-θ) ≤ (6⁻¹ : ℝ) ^ (-θ) * (1 + ‖w‖) ^ (-θ) := by
            rw [← Real.mul_rpow (by norm_num) (by positivity)]
            exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          calc x ^ c * (D / 2) ^ (-θ) * A * J
              ≤ x ^ c * ((6⁻¹ : ℝ) ^ (-θ) * (1 + ‖w‖) ^ (-θ)) * A * J := by gcongr
            _ = _ := by ring
theorem integral_norm_perron_kernel_le {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖
        ≤ K / c * x ^ c * (1 + ‖w‖) ^ (-θ) := by
  obtain ⟨K, hK, hb⟩ := integral_norm_kernel_two_le hδ hθ0 hθ1
  refine ⟨K, hK, fun x c hx hc w hw => ?_⟩
  obtain ⟨hI, hle⟩ := hb x c hx hc w hw
  have hpt : ∀ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ ≤
      c⁻¹ * ‖(x : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ := by
    intro t
    have hs : c ≤ ‖(c : ℂ) + t * I‖ := c_le_norm_line hc.le t
    have e : (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) =
        ((c : ℂ) + t * I)⁻¹ * ((x : ℂ) ^ ((c : ℂ) + t * I) /
          (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) := by
      field_simp
    rw [e, norm_mul, norm_inv]
    gcongr
  calc _ ≤ ∫ t : ℝ, c⁻¹ * ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ :=
        integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (hI.norm.const_mul _)
          (ae_of_all _ hpt)
    _ = c⁻¹ * ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ := integral_const_mul _ _
    _ ≤ c⁻¹ * (K * x ^ c * (1 + ‖w‖) ^ (-θ)) := by gcongr
    _ = _ := by ring
end Erdos985.Analytic.PerronAux
end
section
open Complex MeasureTheory Set
namespace Erdos985.Analytic
open PerronAux
theorem perron_cesaro (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (max 0 (1 - 1 / y) : ℝ) :=
  PerronKernel.perron_cesaro_aux y c hy hc
theorem perron_residue (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w.re < c)
    (hw0 : w ≠ 0) (hw1 : w ≠ -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + (x : ℂ) ^ (-1 : ℂ) / (1 + w) :=
  PerronKernel.perron_residue_aux x c hx hc w hw hw0 hw1
theorem perron_residue_zero (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w = 0) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ) := by
  subst hw
  have hx0 : 0 < x := by linarith
  have key := perron_prof (c := c) hx0 (-1) 0 (-1) 0 1 0 0 1
    (by simp) (by simpa using hc) (by simpa using hc)
    (by simpa using hc) (by simpa using (show 0 < c + 1 by linarith))
    (fun _ => by ring) (F := fun s => 1 / ((s - 0) * s * (s + 1)))
    (fun t => by
      have h0 := line_ne_zero hc t
      have h1 := line_add_one_ne_zero hc t
      simp only [add_zero, sub_zero]
      field_simp
      ring)
    (integrable_div_line_three hc (G := fun _ => (1 : ℂ)) continuous_const (B := 1)
      (fun _ => by simp) (w := 0) (by simpa using hc))
  simp only [mul_one_div] at key
  rw [key, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronAux.Zdprof_def, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
    ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), cpow_neg_one, Real.log_inv]
  push_cast
  simp only [cpow_one, cpow_zero]
  ring
theorem perron_residue_neg_one (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w = -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = 1 - (x : ℂ) ^ (-1 : ℂ) - (x : ℂ) ^ (-1 : ℂ) * (Real.log x : ℂ) := by
  subst hw
  have hx0 : 0 < x := by linarith
  have key := perron_prof (c := c) hx0 1 1 1 (-1) 0 0 1 0
    (by simp) (by simpa using (show 0 < c + 1 by linarith)) (by simpa using hc)
    (by simpa using (show 0 < c + 1 by linarith)) (by simpa using hc)
    (fun _ => by ring) (F := fun s => 1 / ((s - -1) * s * (s + 1)))
    (fun t => by
      have h0 := line_ne_zero hc t
      have h1 := line_add_one_ne_zero hc t
      simp only [add_zero, sub_neg_eq_add]
      field_simp
      ring)
    (integrable_div_line_three hc (G := fun _ => (1 : ℂ)) continuous_const (B := 1)
      (fun _ => by simp) (w := -1) (by simp; linarith))
  simp only [mul_one_div] at key
  rw [key, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronAux.Zdprof_def, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
    ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), cpow_neg_one, Real.log_inv]
  push_cast
  simp only [cpow_one, cpow_zero]
  ring
theorem perron_residue_integrable (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (w : ℂ) (hw : w.re < c) :
    Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  integrable_perron_kernel hx hc hw
theorem perron_residue_norm (x c : ℝ) (hx : 0 < x) (t : ℝ) (w : ℂ) :
    ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖
      = x ^ c / (‖(c : ℂ) + t * I - w‖ * ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖) :=
  norm_perron_kernel hx c t w
theorem perron_pair_integral_norm_le {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      Integrable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) ∧
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖
        ≤ K * x ^ c * (1 + ‖w‖) ^ (-θ) :=
  integral_norm_kernel_two_le hδ hθ0 hθ1
theorem perron_residue_integral_norm_le {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖
        ≤ K / c * x ^ c * (1 + ‖w‖) ^ (-θ) :=
  integral_norm_perron_kernel_le hδ hθ0 hθ1
end Erdos985.Analytic
end
section
open Real Filter Topology
namespace Erdos985.Analytic.DigammaAux
lemma log_one_add_inv_le {a : ℝ} (ha : 0 < a) :
    log (1 + a⁻¹) ≤ 1 / (2 * a) + 1 / (2 * (a + 1)) := by
  set y : ℝ := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun k : ℕ => 2 * y * (y ^ 2) ^ k) (2 * y * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 * y)
  have hle := hasSum_le (fun k : ℕ => ?_) (hasSum_log_one_add_inv ha) hg
  · refine hle.trans (le_of_eq ?_)
    have h2a : (2 * a + 1) ≠ 0 := by positivity
    have e1 : 1 - y ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
      rw [hy]; field_simp; ring
    rw [e1, hy]
    field_simp
    ring
  · rw [← hy, pow_succ, ← pow_mul]
    have h1 : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    have h2 : 0 ≤ y ^ (2 * k) * y := by positivity
    nlinarith
theorem ZdemSeq_def (m : ℕ) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)))) m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)) :=
  Classical.choose_spec (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ))) m
theorem ZdemSeq_eq :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)))) = fun (m : ℕ) => (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)) := by
  funext m
  exact ZdemSeq_def m
lemma emSeq_mono : Monotone (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)))) := by
  refine monotone_nat_of_le_succ (fun m => ?_)
  have ha : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have key := log_one_add_inv_le ha
  have hlog : log (((m + 1 + 1 : ℕ) : ℝ)) = log ((m + 1 : ℕ) : ℝ) + log (1 + ((m + 1 : ℕ) : ℝ)⁻¹) := by
    rw [← log_mul ha.ne' (by positivity)]
    congr 1
    field_simp
    push_cast
    ring
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.DigammaAux.ZdemSeq_eq]
  rw [hlog, harmonic_succ (m + 1)]
  push_cast at key ⊢
  have : (1 : ℝ) / (2 * (m + 1)) + 1 / (2 * (m + 1 + 1)) =
      ((m : ℝ) + 1 + 1)⁻¹ + 1 / 2 / (m + 1) - 1 / 2 / (m + 1 + 1) := by
    field_simp; ring
  linarith
lemma tendsto_emSeq : Tendsto (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)))) atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ => (harmonic n : ℝ) - log n - (1 / 2) / n) atTop
      (𝓝 (eulerMascheroniConstant - 0)) :=
    tendsto_harmonic_sub_log.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [sub_zero] at h1
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.DigammaAux.ZdemSeq_eq]
  exact (tendsto_add_atTop_iff_nat 1).mpr h1
lemma emSeq_le (m : ℕ) : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)))) m ≤ eulerMascheroniConstant :=
  emSeq_mono.ge_of_tendsto tendsto_emSeq m
lemma eulerMascheroniConstant_gt : (0.57688 : ℝ) < eulerMascheroniConstant := by
  refine lt_of_lt_of_le ?_ (emSeq_le 15)
  have hH : (harmonic 16 : ℝ) = 2436559 / 720720 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : log ((16 : ℕ) : ℝ) = 4 * log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.DigammaAux.ZdemSeq_eq]
  norm_num only [Nat.reduceAdd] at hH hl ⊢
  rw [hH, hl]
  linarith [log_two_lt_d9]
end Erdos985.Analytic.DigammaAux
end
section
namespace Erdos985.Analytic
open Complex
private lemma cot_pi_div_four : Complex.cot (↑Real.pi * (1 / 4)) = 1 := by
  rw [show (↑Real.pi * (1 / 4) : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
    Complex.cot_eq_cos_div_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have : (Real.sqrt 2 / 2 : ℝ) ≠ 0 := by positivity
  rw [div_self (by exact_mod_cast this)]
private lemma digamma_three_quarters_eq :
    digamma (3 / 4 : ℂ) =
      ((Real.pi / 2 - 3 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
  have hs : ∀ n : ℤ, (1 / 4 : ℂ) ≠ n := by
    intro n h
    have : ((4 * n : ℤ) : ℂ) = 1 := by push_cast; rw [← h]; norm_num
    have : 4 * n = 1 := by exact_mod_cast this
    omega
  have hs2 : ∀ m : ℕ, 2 * (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have h1 := port_digamma_one_sub hs
  rw [show (1 : ℂ) - 1 / 4 = 3 / 4 by norm_num, cot_pi_div_four] at h1
  have h2 := port_digamma_two_mul hs2
  rw [show (2 : ℂ) * (1 / 4) = 1 / 2 by norm_num, show (1 / 4 : ℂ) + 1 / 2 = 3 / 4 by norm_num,
    digamma_one_half] at h2
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  rw [hlog] at h2
  push_cast
  linear_combination h1 / 2 - h2
theorem digamma_three_quarters_re_le : (digamma (3 / 4 : ℂ)).re ≤ -1.085 := by
  rw [digamma_three_quarters_eq, Complex.ofReal_re]
  linarith [Real.pi_lt_d6, Real.log_two_gt_d9, DigammaAux.eulerMascheroniConstant_gt]
theorem digamma_five_quarters_re_le : (digamma (5 / 4 : ℂ)).re ≤ -0.227 := by
  have hs : ∀ m : ℕ, (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hs' : ∀ n : ℤ, (1 / 4 : ℂ) ≠ n := by
    intro n h
    have : ((4 * n : ℤ) : ℂ) = 1 := by push_cast; rw [← h]; norm_num
    have : 4 * n = 1 := by exact_mod_cast this
    omega
  have h1 := port_digamma_one_sub hs'
  rw [show (1 : ℂ) - 1 / 4 = 3 / 4 by norm_num, cot_pi_div_four,
    digamma_three_quarters_eq] at h1
  have h3 := digamma_apply_add_one (1 / 4) hs
  rw [show (1 / 4 : ℂ) + 1 = 5 / 4 by norm_num] at h3
  have h5 : digamma (5 / 4 : ℂ) =
      ((4 - Real.pi / 2 - 3 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    rw [h3]
    push_cast at h1 ⊢
    linear_combination -h1
  rw [h5, Complex.ofReal_re]
  linarith [Real.pi_gt_d6, Real.log_two_gt_d9, DigammaAux.eulerMascheroniConstant_gt]
end Erdos985.Analytic
end
section
open Real ArithmeticFunction
namespace Erdos985.Analytic.ConstantsAux
lemma rpow32 {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * √x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]
lemma term_eq (f : ℕ → ℝ) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) (3 / 2) n = ((f n / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rfl
lemma lseries_eq (f : ℕ → ℝ) :
    LSeries (fun n => (f n : ℂ)) (3 / 2) = ((∑' n : ℕ, f n / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (term_eq f)
lemma summable_of_lseries (f : ℕ → ℝ) (h : LSeriesSummable (fun n => (f n : ℂ)) (3 / 2)) :
    Summable fun n : ℕ => f n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have : LSeries.term (fun n => (f n : ℂ)) (3 / 2) =
      fun n => ((f n / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := funext (term_eq f)
  rw [LSeriesSummable, this] at h
  exact Complex.summable_ofReal.mp h
lemma re32 : 1 < (3 / 2 : ℂ).re := by norm_num
lemma summable_Λ : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) :=
  summable_of_lseries _ (LSeriesSummable_vonMangoldt re32)
lemma summable_one : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
  refine summable_of_lseries (fun _ => 1) ?_
  have := LSeriesSummable_one_iff.mpr re32
  convert this using 2 <;> simp
lemma summable_log : Summable fun n : ℕ => Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  refine summable_of_lseries (fun n => Real.log n) ?_
  have := (LSeriesSummable_vonMangoldt re32).convolution (LSeriesSummable_one_iff.mpr re32)
  rw [convolution_vonMangoldt_const_one] at this
  convert this using 2 with n
  simp [Complex.natCast_log]
lemma mul_eq :
    (∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) =
      ∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have h := LSeries_convolution' (LSeriesSummable_vonMangoldt re32)
    (LSeriesSummable_one_iff.mpr re32)
  rw [convolution_vonMangoldt_const_one] at h
  have e1 := lseries_eq (fun n => (Λ n : ℝ))
  have e2 := lseries_eq (fun _ => (1 : ℝ))
  have e3 := lseries_eq (fun n : ℕ => Real.log n)
  have h1 : (1 : ℕ → ℂ) = fun _ => ((1 : ℝ) : ℂ) := by ext; simp
  have h3 : (fun n : ℕ => Complex.log n) = fun n : ℕ => ((Real.log n : ℝ) : ℂ) := by
    ext n; simp [Complex.natCast_log]
  rw [h1, h3, e1, e2, e3] at h
  exact_mod_cast h.symm
lemma z_step {x : ℝ} (hx : 1 ≤ x) : 2 / √x - 2 / √(x + 1) ≤ 1 / (x * √x) := by
  have ha : 0 < √x := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < √(x + 1) := Real.sqrt_pos.mpr (by linarith)
  have hab : √x ≤ √(x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hx2 : √x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hy2 : √(x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  set a := √x
  set b := √(x + 1)
  rw [← hx2, div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have : b - a = 1 / (a + b) := by
    field_simp; nlinarith
  nlinarith [mul_pos ha hb, mul_pos (mul_pos ha ha) ha]
lemma g_anti {c y : ℝ} (hc : 2 ≤ c) (hcy : c ≤ y) :
    Real.log y / (y * √y) ≤ Real.log c / (c * √c) := by
  have hc0 : 0 < c := by linarith
  have hy0 : 0 < y := by linarith
  have ha : 0 < √c := Real.sqrt_pos.mpr hc0
  have hb : 0 < √y := Real.sqrt_pos.mpr hy0
  have hab : √c ≤ √y := Real.sqrt_le_sqrt hcy
  have hx2 : √c ^ 2 = c := Real.sq_sqrt hc0.le
  have hy2 : √y ^ 2 = y := Real.sq_sqrt hy0.le
  have hL : 2 / 3 ≤ Real.log c := by
    have := Real.log_le_log (by norm_num) hc
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log y - Real.log c ≤ y / c - 1 := by
    rw [← Real.log_div hy0.ne' hc0.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  set a := √c
  set b := √y
  rw [← hx2, ← hy2] at hlog ⊢
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : b ^ 2 / a ^ 2 - 1 = (b ^ 2 - a ^ 2) / a ^ 2 := by field_simp
  rw [hq] at hlog
  have hlog' : (Real.log (b ^ 2) - Real.log (a ^ 2)) * a ^ 2 ≤ b ^ 2 - a ^ 2 := by
    rwa [le_div_iff₀ (by positivity)] at hlog
  have key : (b ^ 2 - a ^ 2) * a ≤ Real.log (a ^ 2) * (b ^ 3 - a ^ 3) := by
    have h1 : (b ^ 2 - a ^ 2) * a ≤ 2 / 3 * (b ^ 3 - a ^ 3) := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab))
        (by positivity : (0 : ℝ) ≤ 2 * b + a)]
    have h2 : 0 ≤ b ^ 3 - a ^ 3 := by
      have := pow_le_pow_left₀ ha.le hab 3
      linarith
    have hL' : 2 / 3 ≤ Real.log (a ^ 2) := by rw [hx2]; exact hL
    nlinarith
  nlinarith [mul_pos ha (mul_pos ha ha)]
theorem ZdGf_def (x : ℝ) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x) :=
  Classical.choose_spec (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x)) x
theorem ZdGf_eq :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) = fun (x : ℝ) => (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x) := by
  funext x
  exact ZdGf_def x
lemma hasDerivAt_Gf {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) (-(Real.log t / (t * √t))) t := by
  have hs : 0 < √t := Real.sqrt_pos.mpr ht
  have h1 : HasDerivAt (fun x => 2 * Real.log x + 4) (2 * t⁻¹) t :=
    ((Real.hasDerivAt_log ht.ne').const_mul 2).add_const 4
  have h2 := Real.hasDerivAt_sqrt ht.ne'
  have := h1.div h2 hs.ne'
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ConstantsAux.ZdGf_eq]
  convert this using 1 <;> try rfl
  have hst : √t ^ 2 = t := Real.sq_sqrt ht.le
  field_simp
  rw [hst]
  ring
lemma d_step {x : ℝ} (hx : 2 ≤ x) :
    Real.log (x + 1) / ((x + 1) * √(x + 1)) ≤ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) x - (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) (x + 1) := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) (fun t => -(Real.log t / (t * √t)))
    (by linarith : x < x + 1)
    (fun t ht => (hasDerivAt_Gf (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_Gf (by linarith [ht.1]))
  have : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) x - (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) (x + 1) = Real.log c / (c * √c) := by
    rw [show x + 1 - x = 1 by ring, div_one] at hcd
    linarith
  rw [this]
  exact g_anti (by linarith [hc.1]) hc.2.le
lemma Gf_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) x := by
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ConstantsAux.ZdGf_eq]
  have := Real.log_nonneg hx
  positivity
lemma z_tail (K M : ℕ) (hK : 1 ≤ K) :
    2 / √(K : ℝ) - 2 / √((K : ℝ) + M) ≤
      ∑' i : ℕ, (1 : ℝ) / (((i + K : ℕ) : ℝ)) ^ (3 / 2 : ℝ) := by
  have hs : Summable fun i : ℕ => (1 : ℝ) / (((i + K : ℕ) : ℝ)) ^ (3 / 2 : ℝ) :=
    (summable_nat_add_iff K).mpr summable_one
  refine le_trans ?_ (hs.sum_le_tsum (Finset.range M) (fun i _ => by positivity))
  have htel := Finset.sum_range_sub' (fun i : ℕ => 2 / √((K : ℝ) + i)) M
  simp only [Nat.cast_zero, add_zero] at htel
  rw [← htel]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hx : (1 : ℝ) ≤ (K : ℝ) + i := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
  have := z_step hx
  rw [rpow32 (by positivity)]
  push_cast
  rw [show (K : ℝ) + ((i : ℝ) + 1) = (K : ℝ) + i + 1 by ring, add_comm (i : ℝ) (K : ℝ)]
  exact this
lemma d_tail (K : ℕ) (hK : 3 ≤ K) :
    ∑' i : ℕ, Real.log ((i + K : ℕ) : ℝ) / (((i + K : ℕ) : ℝ)) ^ (3 / 2 : ℝ) ≤
      (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) ((K : ℝ) - 1) := by
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  refine Real.tsum_le_of_sum_range_le (fun i => ?_) (fun M => ?_)
  · have : (1 : ℝ) ≤ ((i + K : ℕ) : ℝ) := by push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := Real.log_nonneg this
    positivity
  · have htel := Finset.sum_range_sub' (fun i : ℕ => (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) ((K : ℝ) - 1 + i)) M
    simp only [Nat.cast_zero, add_zero] at htel
    have hG : 0 ≤ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (2 * Real.log x + 4) / √x))) ((K : ℝ) - 1 + M) :=
      Gf_nonneg (by linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)])
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (le_of_eq_of_le htel (by linarith))
    have hx : (2 : ℝ) ≤ (K : ℝ) - 1 + i := by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := d_step hx
    rw [rpow32 (by positivity)]
    push_cast
    rw [show (K : ℝ) - 1 + ((i : ℝ) + 1) = (K : ℝ) - 1 + i + 1 by ring,
      show (i : ℝ) + K = (K : ℝ) - 1 + i + 1 by ring]
    exact this
lemma log_succ_le' (m : ℝ) (hm : 0 < m) :
    Real.log (m + 1) ≤ Real.log m + (1 / (2 * m) + 1 / (2 * (m + 1))) := by
  have h := Erdos985.Analytic.DigammaAux.log_one_add_inv_le hm
  have e : Real.log (m + 1) = Real.log m + Real.log (1 + m⁻¹) := by
    rw [← Real.log_mul hm.ne' (by positivity)]
    congr 1
    field_simp
  linarith
lemma zb (n u : ℝ) (hn : 0 < n) (hu0 : 0 ≤ u) (hu : n ≤ u ^ 2) :
    1 / (n * u) ≤ 1 / (n * √n) := by
  have hs : √n ≤ u := by
    rw [show u = √(u ^ 2) from (Real.sqrt_sq hu0).symm]; exact Real.sqrt_le_sqrt hu
  have : 0 < √n := Real.sqrt_pos.mpr hn
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hs hn.le)
lemma db (n l : ℝ) (hn : 1 ≤ n) (hl0 : 0 < l) (hl : l ^ 2 ≤ n) :
    Real.log n / (n * √n) ≤ Real.log n / (n * l) := by
  have hs : l ≤ √n := Real.le_sqrt_of_sq_le hl
  exact div_le_div_of_nonneg_left (Real.log_nonneg hn) (by positivity)
    (mul_le_mul_of_nonneg_left hs (by linarith))
lemma log_primes_le :
    Real.log 2 ≤ 0.6931471808 ∧ Real.log 3 ≤ 1.098749 ∧ Real.log 5 ≤ 1.609512 ∧
    Real.log 7 ≤ 1.945980 ∧ Real.log 11 ≤ 2.398001 ∧ Real.log 13 ≤ 2.565052 ∧
    Real.log 17 ≤ 2.833350 ∧ Real.log 19 ≤ 2.944613 := by
  have p2 := Real.log_two_lt_d9.le
  have p3 : 2 * Real.log 3 ≤ 3 * Real.log 2 + (1 / (2 * 8) + 1 / (2 * (8 + 1))) := by
    have h := log_succ_le' 8 (by norm_num)
    have e1 : Real.log (8 + 1) = 2 * Real.log 3 := by
      rw [show (8 : ℝ) + 1 = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2^3 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p5 : 2 * Real.log 5 ≤ 3 * Real.log 2 + Real.log 3 + (1 / (2 * 24) + 1 / (2 * (24 + 1))) := by
    have h := log_succ_le' 24 (by norm_num)
    have e1 : Real.log (24 + 1) = 2 * Real.log 5 := by
      rw [show (24 : ℝ) + 1 = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
      rw [show (24 : ℝ) = 2^3 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p7 : 2 * Real.log 7 ≤ 4 * Real.log 2 + Real.log 3 + (1 / (2 * 48) + 1 / (2 * (48 + 1))) := by
    have h := log_succ_le' 48 (by norm_num)
    have e1 : Real.log (48 + 1) = 2 * Real.log 7 := by
      rw [show (48 : ℝ) + 1 = 7 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
      rw [show (48 : ℝ) = 2^4 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p11 : 2 * Real.log 11 ≤ 3 * Real.log 2 + Real.log 3 + Real.log 5 + (1 / (2 * 120) + 1 / (2 * (120 + 1))) := by
    have h := log_succ_le' 120 (by norm_num)
    have e1 : Real.log (120 + 1) = 2 * Real.log 11 := by
      rw [show (120 : ℝ) + 1 = 11 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 120 = 3 * Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (120 : ℝ) = 2^3 * 3 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p13 : 2 * Real.log 13 ≤ 3 * Real.log 2 + Real.log 3 + Real.log 7 + (1 / (2 * 168) + 1 / (2 * (168 + 1))) := by
    have h := log_succ_le' 168 (by norm_num)
    have e1 : Real.log (168 + 1) = 2 * Real.log 13 := by
      rw [show (168 : ℝ) + 1 = 13 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 168 = 3 * Real.log 2 + Real.log 3 + Real.log 7 := by
      rw [show (168 : ℝ) = 2^3 * 3 * 7 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p17 : 2 * Real.log 17 ≤ 5 * Real.log 2 + 2 * Real.log 3 + (1 / (2 * 288) + 1 / (2 * (288 + 1))) := by
    have h := log_succ_le' 288 (by norm_num)
    have e1 : Real.log (288 + 1) = 2 * Real.log 17 := by
      rw [show (288 : ℝ) + 1 = 17 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 288 = 5 * Real.log 2 + 2 * Real.log 3 := by
      rw [show (288 : ℝ) = 2^5 * 3^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p19 : 2 * Real.log 19 ≤ 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + (1 / (2 * 360) + 1 / (2 * (360 + 1))) := by
    have h := log_succ_le' 360 (by norm_num)
    have e1 : Real.log (360 + 1) = 2 * Real.log 19 := by
      rw [show (360 : ℝ) + 1 = 19 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 360 = 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
      rw [show (360 : ℝ) = 2^3 * 3^2 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  norm_num at *
  refine ⟨p2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
lemma finite_bounds :
    2.6069 ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ∧
    ∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 3.9490 := by
  obtain ⟨l2, l3, l5, l7, l11, l13, l17, l19⟩ := log_primes_le
  have hZ := (summable_one.sum_add_tsum_nat_add 21).symm
  have hD := (summable_log.sum_add_tsum_nat_add 21).symm
  have hzt := z_tail 21 399999979 (by norm_num)
  have hdt := d_tail 21 (by norm_num)
  have hsq : √((21 : ℕ) + (399999979 : ℕ) : ℝ) = 20000 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]; norm_num
  rw [hsq] at hzt
  have hrs (f : ℝ → ℝ) : ∑ i ∈ Finset.range 21, f (i : ℝ) / (i : ℝ) ^ (3 / 2 : ℝ) =
      ∑ i ∈ Finset.range 21, f (i : ℝ) / ((i : ℝ) * √(i : ℝ)) :=
    Finset.sum_congr rfl (fun i _ => by rw [rpow32 (Nat.cast_nonneg i)])
  rw [hrs (fun _ => 1)] at hZ
  rw [hrs Real.log] at hD
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hZ hD
  norm_num at hZ hD hzt hdt
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ConstantsAux.ZdGf_eq] at hdt
  have z21 : 2 / (45826 / 10000 : ℝ) ≤ 2 / √21 := by
    have hs : √21 ≤ (45826 / 10000 : ℝ) := by
      rw [show (45826 / 10000 : ℝ) = √((45826 / 10000) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hs
  have g20 : (2 * Real.log 20 + 4) / √20 ≤ (2 * Real.log 20 + 4) / (44721/10000) := by
    have : (0 : ℝ) ≤ 2 * Real.log 20 + 4 := by have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 20); linarith
    exact div_le_div_of_nonneg_left this (by norm_num)
      (Real.le_sqrt_of_sq_le (by norm_num))
  have z1 := zb 1 (10000/10000) (by norm_num) (by norm_num) (by norm_num)
  have z2 := zb 2 (14143/10000) (by norm_num) (by norm_num) (by norm_num)
  have d2 := db 2 (14142/10000) (by norm_num) (by norm_num) (by norm_num)
  have z3 := zb 3 (17321/10000) (by norm_num) (by norm_num) (by norm_num)
  have d3 := db 3 (17320/10000) (by norm_num) (by norm_num) (by norm_num)
  have z4 := zb 4 (20000/10000) (by norm_num) (by norm_num) (by norm_num)
  have d4 := db 4 (20000/10000) (by norm_num) (by norm_num) (by norm_num)
  have z5 := zb 5 (22361/10000) (by norm_num) (by norm_num) (by norm_num)
  have d5 := db 5 (22360/10000) (by norm_num) (by norm_num) (by norm_num)
  have z6 := zb 6 (24495/10000) (by norm_num) (by norm_num) (by norm_num)
  have d6 := db 6 (24494/10000) (by norm_num) (by norm_num) (by norm_num)
  have z7 := zb 7 (26458/10000) (by norm_num) (by norm_num) (by norm_num)
  have d7 := db 7 (26457/10000) (by norm_num) (by norm_num) (by norm_num)
  have z8 := zb 8 (28285/10000) (by norm_num) (by norm_num) (by norm_num)
  have d8 := db 8 (28284/10000) (by norm_num) (by norm_num) (by norm_num)
  have z9 := zb 9 (30000/10000) (by norm_num) (by norm_num) (by norm_num)
  have d9 := db 9 (30000/10000) (by norm_num) (by norm_num) (by norm_num)
  have z10 := zb 10 (31623/10000) (by norm_num) (by norm_num) (by norm_num)
  have d10 := db 10 (31622/10000) (by norm_num) (by norm_num) (by norm_num)
  have z11 := zb 11 (33167/10000) (by norm_num) (by norm_num) (by norm_num)
  have d11 := db 11 (33166/10000) (by norm_num) (by norm_num) (by norm_num)
  have z12 := zb 12 (34642/10000) (by norm_num) (by norm_num) (by norm_num)
  have d12 := db 12 (34641/10000) (by norm_num) (by norm_num) (by norm_num)
  have z13 := zb 13 (36056/10000) (by norm_num) (by norm_num) (by norm_num)
  have d13 := db 13 (36055/10000) (by norm_num) (by norm_num) (by norm_num)
  have z14 := zb 14 (37417/10000) (by norm_num) (by norm_num) (by norm_num)
  have d14 := db 14 (37416/10000) (by norm_num) (by norm_num) (by norm_num)
  have z15 := zb 15 (38730/10000) (by norm_num) (by norm_num) (by norm_num)
  have d15 := db 15 (38729/10000) (by norm_num) (by norm_num) (by norm_num)
  have z16 := zb 16 (40000/10000) (by norm_num) (by norm_num) (by norm_num)
  have d16 := db 16 (40000/10000) (by norm_num) (by norm_num) (by norm_num)
  have z17 := zb 17 (41232/10000) (by norm_num) (by norm_num) (by norm_num)
  have d17 := db 17 (41231/10000) (by norm_num) (by norm_num) (by norm_num)
  have z18 := zb 18 (42427/10000) (by norm_num) (by norm_num) (by norm_num)
  have d18 := db 18 (42426/10000) (by norm_num) (by norm_num) (by norm_num)
  have z19 := zb 19 (43589/10000) (by norm_num) (by norm_num) (by norm_num)
  have d19 := db 19 (43588/10000) (by norm_num) (by norm_num) (by norm_num)
  have z20 := zb 20 (44722/10000) (by norm_num) (by norm_num) (by norm_num)
  have d20 := db 20 (44721/10000) (by norm_num) (by norm_num) (by norm_num)
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2^2 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e14 : Real.log 14 = Real.log 2 + Real.log 7 := by
    rw [show (14 : ℝ) = 2 * 7 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2^4 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
    rw [show (18 : ℝ) = 2 * 3^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    rw [show (20 : ℝ) = 2^2 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
  norm_num at *
  constructor <;> linarith
end Erdos985.Analytic.ConstantsAux
end
section
open Complex ArithmeticFunction
namespace Erdos985.Analytic
private lemma deriv_div_Gamma_eq (s : ℂ) : deriv Gamma s / Gamma s = digamma s := by
  rw [digamma_def, logDeriv_apply]
theorem digamma_three_quarters_le :
    (deriv Gamma (3 / 4) / Gamma (3 / 4)).re ≤ -1.08 := by
  rw [deriv_div_Gamma_eq]
  linarith [digamma_three_quarters_re_le]
theorem digamma_five_quarters_le :
    (deriv Gamma (5 / 4) / Gamma (5 / 4)).re ≤ -0.22 := by
  rw [deriv_div_Gamma_eq]
  linarith [digamma_five_quarters_re_le]
theorem summable_vonMangoldt_rpow : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) :=
  ConstantsAux.summable_Λ
theorem tsum_vonMangoldt_rpow_le : ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 1.52 := by
  have hmul := ConstantsAux.mul_eq
  obtain ⟨hZ, hD⟩ := ConstantsAux.finite_bounds
  have hS : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  set S := ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
  set Z := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
  by_contra h
  have h' := (not_le.mp h).le
  nlinarith [mul_le_mul h' hZ (by norm_num) hS]
theorem tsum_vonMangoldt_rpow_le_sharp [Fact H3] :
    ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 1.515 := by
  have hmul := ConstantsAux.mul_eq
  obtain ⟨hZ, hD⟩ := ConstantsAux.finite_bounds
  have hS : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  set S := ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
  set Z := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
  by_contra h
  have h' := (not_le.mp h).le
  nlinarith [mul_le_mul h' hZ (by norm_num) hS]
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
theorem Zdparity_def (N : ℕ) (χ : DirichletCharacter ℂ N) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1) :=
  Classical.choose_spec (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1)) N χ
theorem Zdparity_eq :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) = fun (N : ℕ) (χ : DirichletCharacter ℂ N) => (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1) := by
  funext N χ
  exact Zdparity_def N χ
theorem ZdgammaLogDeriv_def (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ) :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)) :=
  Classical.choose_spec (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2))) N χ s
theorem ZdgammaLogDeriv_eq :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) = fun (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ) => (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)) := by
  funext N χ s
  exact ZdgammaLogDeriv_def N χ s
theorem ZdgammaPart_def (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ) :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))) :=
  Classical.choose_spec (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))) N χ x
theorem ZdgammaPart_eq :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) = fun (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ) => (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))) := by
  funext N χ x
  exact ZdgammaPart_def N χ x
theorem ZdzeroTerm_def (x : ℕ) (ρ : ℂ) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))) :=
  Classical.choose_spec (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ)))) x ρ
theorem ZdzeroTerm_eq :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) = fun (x : ℕ) (ρ : ℂ) => (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))) := by
  funext x ρ
  exact ZdzeroTerm_def x ρ
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.StepAAux
open Complex
theorem hasDerivAt_Gamma_digamma {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt Gamma (Gamma w * digamma w) w := by
  have hd : DifferentiableAt ℂ Gamma w := differentiableAt_Gamma w fun m h => by
    rw [h] at hw; simp at hw; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  convert hd.hasDerivAt using 1 <;> try rfl
  rw [digamma_def, logDeriv_apply, mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hw)]
theorem hasDerivAt_Gammaℝ {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt Gammaℝ (Gammaℝ w * (-(1 / 2) * (Real.log Real.pi : ℂ)
      + (1 / 2) * digamma (w / 2))) w := by
  have h1 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) w := by
    simpa using ((hasDerivAt_id w).neg.div_const 2)
  have h2 := h1.const_cpow (c := (Real.pi : ℂ)) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h3 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) w := by
    simpa using (hasDerivAt_id w).div_const 2
  have hw2 : 0 < (w / 2).re := by simp; linarith
  have h4 := (hasDerivAt_Gamma_digamma hw2).comp w h3
  have h5 := h2.mul h4
  have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (ofReal_log Real.pi_pos.le).symm
  convert h5 using 1 <;> try rfl
  · rw [hlog, Gammaℝ_def]; simp only [Function.comp_apply]; ring
variable {N : ℕ}
theorem hasDerivAt_gammaFactor (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (DirichletCharacter.gammaFactor χ)
      (DirichletCharacter.gammaFactor χ s * ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ s) s := by
  classical
  by_cases he : χ.Even
  · have hfun : DirichletCharacter.gammaFactor χ = Gammaℝ := funext he.gammaFactor_def
    rw [hfun]
    convert hasDerivAt_Gammaℝ hs using 2
    simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdgammaLogDeriv_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.Zdparity_eq, he]
  · have hfun : DirichletCharacter.gammaFactor χ = fun z => Gammaℝ (z + 1) := by
      funext z; simp [DirichletCharacter.gammaFactor, he]
    rw [hfun]
    have h := (hasDerivAt_Gammaℝ (w := s + 1) (by simp; linarith)).comp s
      ((hasDerivAt_id s).add_const 1)
    convert h using 1 <;> try rfl
    · simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdgammaLogDeriv_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.Zdparity_eq, he]
theorem gammaFactor_ne_zero (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  classical
  by_cases he : χ.Even
  · rw [he.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · simp only [DirichletCharacter.gammaFactor, he, ite_false]
    exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
end Erdos985.Analytic.StepAAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
theorem completedLFunction_inv_eq_zero {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive)
    {s : ℂ} (hs : DirichletCharacter.completedLFunction χ (1 - s) = 0) :
    DirichletCharacter.completedLFunction χ⁻¹ s = 0 := by
  rw [hprim.completedLFunction_one_sub] at hs
  rcases mul_eq_zero.mp hs with h | h
  · exfalso
    rcases mul_eq_zero.mp h with h | h
    · rw [cpow_eq_zero_iff] at h
      exact NeZero.ne N (by exact_mod_cast h.1)
    · exact port_rootNumber_ne_zero hprim h
  · exact h
theorem completedLFunction_zero_re_mem {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) {ρ : ℂ} (hρ : DirichletCharacter.completedLFunction χ ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    have h1 : DirichletCharacter.completedLFunction χ (1 - (1 - ρ)) = 0 := by simpa using hρ
    exact port_completedLFunction_ne_zero_of_one_le_re χ⁻¹
      (Or.inl (by simpa using hχ)) (by simp; linarith) (completedLFunction_inv_eq_zero hprim h1)
  · by_contra h
    push Not at h
    exact port_completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ
theorem LFunction_eq_zero_of_completed {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : s ≠ 0)
    (h : DirichletCharacter.completedLFunction χ s = 0) : DirichletCharacter.LFunction χ s = 0 := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs), h, zero_div]
theorem completedLFunction_zero_re (hGRH : H1)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.completedLFunction χ ρ = 0) : ρ.re = 1 / 2 := by
  rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
  · exfalso
    have h1 : DirichletCharacter.completedLFunction χ (1 - (1 - ρ)) = 0 := by simpa using hρ
    have h2 := completedLFunction_inv_eq_zero hprim h1
    have hne : (1 - ρ) ≠ 0 := fun h' => by
      have := congrArg Complex.re h'; simp at this; linarith
    exact hGRH N χ⁻¹ (1 - ρ) (by simp; linarith) (Or.inl (by simpa using hχ))
      (LFunction_eq_zero_of_completed hne h2)
  · exact h
  · exfalso
    have hne : ρ ≠ 0 := fun h' => by rw [h'] at h; simp at h; linarith
    exact hGRH N χ ρ h (Or.inl hχ) (LFunction_eq_zero_of_completed hne hρ)
theorem logDeriv_LFunction_eq {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
      = deriv (DirichletCharacter.completedLFunction χ) s
          / DirichletCharacter.completedLFunction χ s - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ s := by
  have hs0 : 0 < s.re := by linarith
  have hL : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  have hγ := StepAAux.gammaFactor_ne_zero χ hs0
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      fun w => DirichletCharacter.gammaFactor χ w * DirichletCharacter.LFunction χ w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show s ∈ {w : ℂ | 0 < w.re} from hs0)] with w hw
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ w
      (Or.inl fun h => by rw [h] at hw; simp at hw),
      mul_div_cancel₀ _ (StepAAux.gammaFactor_ne_zero χ hw)]
  have hd : HasDerivAt (fun w => DirichletCharacter.gammaFactor χ w * DirichletCharacter.LFunction χ w) _ s :=
    (StepAAux.hasDerivAt_gammaFactor χ hs0).mul
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hχ)).hasDerivAt
  rw [hev.deriv_eq, hd.deriv, hev.eq_of_nhds]
  field_simp
  ring
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real
lemma one_le_log_of_three_le {u : ℝ} (hu : 3 ≤ u) : 1 ≤ log u := by
  have h3 : exp 1 < 3 := lt_of_lt_of_le exp_one_lt_d9 (by norm_num)
  rw [le_log_iff_exp_le (by linarith)]
  linarith
lemma ulogu_mono {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : u * log u ≤ v * log v :=
  mul_le_mul huv (log_le_log (by linarith) huv) (log_nonneg hu) (by linarith)
lemma expo_mono {a a' b b' y y' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (hb : 3 ≤ b) (hy : 0 ≤ y)
    (hle : y + b ≤ y' + b') :
    a * ((y + b) * log (y + b)) ≤ a' * ((y' + b') * log (y' + b')) := by
  have h1 : 1 ≤ log (y + b) := one_le_log_of_three_le (by linarith)
  have h2 : (y + b) * log (y + b) ≤ (y' + b') * log (y' + b') :=
    ulogu_mono (by linarith) hle
  have h3 : 0 ≤ (y' + b') * log (y' + b') := by nlinarith
  exact mul_le_mul haa h2 (by nlinarith) (ha.trans haa)
lemma LogGrowth_nonneg_K {F : ℂ → ℂ} {K a b : ℝ}
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) : 0 ≤ K :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h 0)) (exp_pos _)
lemma LogGrowth_mono {F : ℂ → ℂ} {K a b : ℝ} (ha : 0 ≤ a) (hb : 3 ≤ b)
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) {a' b' : ℝ} (haa : a ≤ a')
    (hbb : b ≤ b') : ∀ s, ‖F s‖ ≤ K * exp (a' * ((‖s‖ + b') * log (‖s‖ + b'))) := by
  intro s
  refine (h s).trans (mul_le_mul_of_nonneg_left ?_ (LogGrowth_nonneg_K h))
  exact exp_le_exp.2 (expo_mono ha haa hb (norm_nonneg _) (by linarith))
lemma LogGrowth_congr {F G : ℂ → ℂ} (hF : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) F) (h : ∀ s, F s = G s) : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) G := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  exact ⟨K, a, b, ha, hb, fun s => h s ▸ hK s⟩
lemma LogGrowth_const (c : ℂ) : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (fun _ => c) :=
  ⟨‖c‖, 0, 3, le_rfl, le_rfl, fun s => by simp⟩
lemma LogGrowth_add {F G : ℂ → ℂ} (hF : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) F) (hG : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) G) :
    (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (fun s => F s + G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K + K', max a a', max b b', le_max_of_le_left ha, le_max_of_le_left hb, fun s => ?_⟩
  have h1 := LogGrowth_mono ha hb hK (le_max_left a a') (le_max_left b b') s
  have h2 := LogGrowth_mono ha' hb' hK' (le_max_right a a') (le_max_right b b') s
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2
lemma LogGrowth_mul {F G : ℂ → ℂ} (hF : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) F) (hG : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) G) :
    (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (fun s => F s * G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K * K', a + a', max b b', add_nonneg ha ha', le_max_of_le_left hb, fun s => ?_⟩
  have h1 := LogGrowth_mono ha hb hK le_rfl (le_max_left b b') s
  have h2 := LogGrowth_mono ha' hb' hK' le_rfl (le_max_right b b') s
  rw [norm_mul]
  calc ‖F s‖ * ‖G s‖ ≤ _ := mul_le_mul h1 h2 (norm_nonneg _)
        (mul_nonneg (LogGrowth_nonneg_K hK) (exp_pos _).le)
    _ = _ := by rw [add_mul a a', exp_add]; ring
lemma LogGrowth_sum {ι : Type*} (S : Finset ι) {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ S, (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (F i)) : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (fun s => ∑ i ∈ S, F i s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact LogGrowth_congr (LogGrowth_const 0) (fun s => by simp)
  | insert i S hi ih =>
    refine LogGrowth_congr (LogGrowth_add (hF i (Finset.mem_insert_self _ _))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))) (fun s => ?_)
    rw [Finset.sum_insert hi]
lemma LogGrowth_comp {F : ℂ → ℂ} (hF : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) F) {g : ℂ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hg : ∀ s, ‖g s‖ ≤ ‖s‖ + d) : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (fun s => F (g s)) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  refine ⟨K, a, b + d, ha, by linarith, fun s => (hK (g s)).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (LogGrowth_nonneg_K hK)
  exact expo_mono ha le_rfl hb (norm_nonneg _) (by linarith [hg s])
lemma LogGrowth_natCast_cpow_neg {N : ℕ} (hN : 0 < N) : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (fun s => (N : ℂ) ^ (-s)) := by
  refine ⟨1, log N, 3, log_natCast_nonneg N, le_rfl, fun s => ?_⟩
  rw [Complex.norm_natCast_cpow_of_pos hN, one_mul]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ log (N : ℝ) := log_nonneg hN1
  calc (N : ℝ) ^ (-s).re ≤ (N : ℝ) ^ ‖s‖ :=
        rpow_le_rpow_of_exponent_le hN1 (by
          rw [Complex.neg_re]; exact (neg_le_abs _).trans (Complex.abs_re_le_norm s))
    _ = exp (log N * ‖s‖) := by
        rw [rpow_def_of_pos (by exact_mod_cast hN)]
    _ ≤ _ := by
        refine exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hlog)
        have h1 : 1 ≤ log (‖s‖ + 3) := one_le_log_of_three_le (by linarith [norm_nonneg s])
        nlinarith [norm_nonneg s]
lemma LogGrowth_order {F : ℂ → ℂ} (hF : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) F) :
    ∀ ε : ℝ, ε > 0 → ∃ C, ∀ z, ‖F z‖ ≤ C * exp (‖z‖ ^ (1 + ε)) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  intro ε hε
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set A := a * 2 ^ (1 + δ) / δ with hA
  have hA0 : 0 ≤ A := by positivity
  set X := max b (A ^ δ⁻¹) with hX
  have hXb : b ≤ X := le_max_left _ _
  have key : ∀ x : ℝ, X ≤ x → a * ((x + b) * log (x + b)) ≤ x ^ (1 + ε) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hxb : 0 < x + b := by linarith
    have hlog : log (x + b) ≤ (x + b) ^ δ / δ := log_le_rpow_div hxb.le hδ0
    have e1 : (x + b) * log (x + b) ≤ (x + b) ^ (1 + δ) / δ := by
      rw [rpow_add hxb, rpow_one, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hlog hxb.le
    have e2 : (x + b) ^ (1 + δ) ≤ 2 ^ (1 + δ) * x ^ (1 + δ) := by
      rw [← mul_rpow (by norm_num) hx0.le]
      exact rpow_le_rpow hxb.le (by linarith) (by linarith)
    have e3 : A ≤ x ^ δ := by
      calc A = (A ^ δ⁻¹) ^ δ := (rpow_inv_rpow hA0 hδ0.ne').symm
        _ ≤ x ^ δ := rpow_le_rpow (by positivity) ((le_max_right _ _).trans hx) hδ0.le
    have e4 : x ^ (1 + ε) = x ^ (1 + δ) * x ^ δ := by
      rw [← rpow_add hx0]; congr 1; rw [hδ]; ring
    calc a * ((x + b) * log (x + b)) ≤ a * ((x + b) ^ (1 + δ) / δ) :=
          mul_le_mul_of_nonneg_left e1 ha
      _ ≤ a * (2 ^ (1 + δ) * x ^ (1 + δ) / δ) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e2 hδ0.le) ha
      _ = A * x ^ (1 + δ) := by rw [hA]; ring
      _ ≤ x ^ δ * x ^ (1 + δ) := mul_le_mul_of_nonneg_right e3 (by positivity)
      _ = x ^ (1 + ε) := by rw [e4, mul_comm]
  set M := a * ((X + b) * log (X + b)) with hM
  refine ⟨K * exp M, fun z => (hK z).trans ?_⟩
  have hK0 : 0 ≤ K := LogGrowth_nonneg_K hK
  rw [mul_assoc, ← exp_add]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) hK0
  have hpow : 0 ≤ ‖z‖ ^ (1 + ε) := by positivity
  rcases le_total X ‖z‖ with h | h
  · have hM0 : 0 ≤ M := by
      have : 1 ≤ log (X + b) := one_le_log_of_three_le (by linarith)
      have : 0 ≤ X + b := by linarith
      positivity
    linarith [key _ h]
  · have := expo_mono (y := ‖z‖) (y' := X) (b' := b) ha le_rfl hb (norm_nonneg _) (by linarith)
    linarith
lemma LogGrowth_order_nat {F : ℂ → ℂ} (hF : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) F) :
    ∀ ε : ℕ, ε > 0 → ∃ C, ∀ z, ‖F z‖ ≤ C * exp (‖z‖ ^ (1 + ε)) := by
  intro ε hε
  obtain ⟨C, hC⟩ := LogGrowth_order hF (ε : ℝ) (by exact_mod_cast hε)
  refine ⟨C, fun z => ?_⟩
  have h := hC z
  rwa [show (1 : ℝ) + ε = ((1 + ε : ℕ) : ℝ) by push_cast; ring, rpow_natCast] at h
end Erdos985.Analytic.XiOrderAux
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real Set MeasureTheory
open scoped Nat
lemma exp_neg_le_factorial_mul {y : ℝ} (hy : 0 < y) (m : ℕ) : exp (-y) ≤ m ! * y⁻¹ ^ m := by
  have h := pow_div_factorial_le_exp (x := y) (hx := hy.le) (n := m)
  have hpos : 0 < y ^ m / m ! := by positivity
  rw [exp_neg]
  calc (exp y)⁻¹ ≤ (y ^ m / m !)⁻¹ := inv_anti₀ hpos h
    _ = m ! * y⁻¹ ^ m := by rw [inv_div, inv_pow, div_eq_mul_inv]
theorem ZddomFun_eq :
    (Classical.choose (⟨_, rfl⟩ : ∃ f : ℝ → ℝ, f = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))))) = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))) :=
  Classical.choose_spec (⟨_, rfl⟩ : ∃ f : ℝ → ℝ, f = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))))
theorem ZddomFun_def : (Classical.choose (⟨_, rfl⟩ : ∃ f : ℝ → ℝ, f = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))))) = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))) := ZddomFun_eq
lemma integrableOn_domFun : IntegrableOn (Classical.choose (⟨_, rfl⟩ : ∃ f : ℝ → ℝ, f = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))))) (Ioi 0) := by
  have h1 : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have h2 : Integrable ((Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).integrable_indicator measurableSet_Ioi
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.XiOrderAux.ZddomFun_eq]
  exact (h1.add h2).integrableOn
lemma integrand_bound (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) (t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * (Classical.choose (⟨_, rfl⟩ : ∃ f : ℝ → ℝ, f = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))))) t := by
  have hsre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hk := P.hk
  have hA : 0 ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by positivity
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  rcases lt_trichotomy t 1 with h1 | rfl | h1
  ·
    have hdom : (Classical.choose (⟨_, rfl⟩ : ∃ f : ℝ → ℝ, f = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))))) t = 1 := by
      simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.XiOrderAux.ZddomFun_eq, indicator, ht, h1.le, not_lt.2 h1.le]
    rw [hdom, mul_one]
    have hfm : P.f_modif t = (P.ε * ((1 / t) ^ P.k : ℝ)) • (P.g (1 / t) - P.g₀) := by
      have hfe := P.h_feq (1 / t) (by simpa using ht)
      rw [one_div_one_div] at hfe
      simp only [WeakFEPair.f_modif, Pi.add_apply, indicator, mem_Ioi, mem_Ioo, ht, h1,
        and_self, ite_true, not_lt.2 h1.le, ite_false, zero_add, hfe, smul_sub]
      congr 2
      rw [one_div, inv_rpow ht.le, rpow_neg ht.le]
    have h1t : 1 < 1 / t := by rw [lt_one_div one_pos ht, div_one]; exact h1
    rw [hfm, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hgb := hg (1 / t) h1t
    have he := exp_neg_le_factorial_mul (show 0 < p * (1 / t) by positivity) m
    rw [neg_mul] at hgb
    have hcalc : t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m) ≤ 1 := by
      rw [one_div, inv_inv, inv_rpow ht.le, ← rpow_neg ht.le, ← rpow_natCast,
        ← rpow_add ht, ← rpow_add ht]
      apply rpow_le_one ht.le h1.le
      have := neg_abs_le s.re
      linarith
    calc t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * ‖P.g (1 / t) - P.g₀‖)
        ≤ t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * (C * (m ! * (p * (1 / t))⁻¹ ^ m))) := by
          gcongr
          exact hgb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * ‖P.ε‖ * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m)) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * ‖P.ε‖ * m ! * p⁻¹ ^ m * 1 := by gcongr
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by
          rw [mul_one]; gcongr; exact le_max_right _ _
  · have h0 : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hA (by simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.XiOrderAux.ZddomFun_eq])
  ·
    have hdom : (Classical.choose (⟨_, rfl⟩ : ∃ f : ℝ → ℝ, f = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))))) t = t ^ (-2 : ℝ) := by
      simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.XiOrderAux.ZddomFun_eq, indicator, h1, not_le.2 h1]
    rw [hdom]
    have hfm : P.f_modif t = P.f t - P.f₀ := by
      simp [WeakFEPair.f_modif, indicator, h1, not_lt.2 h1.le]
    rw [hfm]
    have he := exp_neg_le_factorial_mul (show 0 < p * t by positivity) m
    have hfb := hf t h1
    rw [neg_mul] at hfb
    have ht0 : 0 < t := ht
    have hcalc : t ^ (s.re - 1) * t⁻¹ ^ m ≤ t ^ (-2 : ℝ) := by
      rw [inv_pow, ← rpow_natCast, ← rpow_neg ht.le, ← rpow_add ht]
      apply rpow_le_rpow_of_exponent_le h1.le
      have := le_abs_self s.re
      linarith
    calc t ^ (s.re - 1) * ‖P.f t - P.f₀‖
        ≤ t ^ (s.re - 1) * (C * (m ! * (p * t)⁻¹ ^ m)) := by
          gcongr
          exact hfb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * 1 * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * t⁻¹ ^ m) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * t ^ (-2 : ℝ) := by
          gcongr
          exact le_max_left _ _
lemma Λ₀_bound (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) :
    ‖P.Λ₀ s‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * ∫ t in Ioi 0, (Classical.choose (⟨_, rfl⟩ : ∃ f : ℝ → ℝ, f = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))))) t := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (integrableOn_domFun.const_mul _) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun t ht => integrand_bound P hp hC hf hg s m hm t ht)
theorem Λ₀_logGrowth (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t)) : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) P.Λ₀ := by
  set I0 := ∫ t in Ioi 0, (Classical.choose (⟨_, rfl⟩ : ∃ f : ℝ → ℝ, f = (open Real Set MeasureTheory in (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))))) t
  set Q := max 1 p⁻¹
  have hQ : 1 ≤ Q := le_max_left _ _
  have hk := P.hk
  set b := P.k + 5
  refine ⟨C * max 1 ‖P.ε‖ * I0, 1 + log Q, b, by linarith [log_nonneg hQ], by linarith,
    fun s => ?_⟩
  set m := ⌈‖s‖ + P.k + 1⌉₊
  have hm : ‖s‖ + P.k + 1 ≤ m := Nat.le_ceil _
  have hm' : (m : ℝ) ≤ ‖s‖ + b := by
    have := Nat.ceil_lt_add_one (show 0 ≤ ‖s‖ + P.k + 1 by positivity)
    linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith [norm_nonneg s]
  have hI0 : 0 ≤ I0 := setIntegral_nonneg measurableSet_Ioi (fun t _ => by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.XiOrderAux.ZddomFun_eq, Pi.add_apply]
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun t ht => rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _) _))
  refine (Λ₀_bound P hp hC hf hg s m hm).trans ?_
  have hfac : (m ! : ℝ) * p⁻¹ ^ m ≤ exp ((1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b))) := by
    have h1 : (m ! : ℝ) * p⁻¹ ^ m ≤ ((m : ℝ) * Q) ^ m := by
      rw [mul_pow]
      gcongr
      · exact_mod_cast Nat.factorial_le_pow m
      · exact le_max_right _ _
    have h2 : ((m : ℝ) * Q) ^ m = exp (m * log (m * Q)) := by
      rw [← log_pow, exp_log (by positivity)]
    have hL : 1 ≤ log (‖s‖ + b) := one_le_log_of_three_le (by linarith [norm_nonneg s])
    have hlogQ : 0 ≤ log Q := log_nonneg hQ
    have h3 : (m : ℝ) * log (m * Q) ≤ (1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b)) := by
      rw [log_mul (by positivity) (by positivity)]
      have e1 : (m : ℝ) * log m ≤ (‖s‖ + b) * log (‖s‖ + b) := ulogu_mono hm1 hm'
      have e2 : (m : ℝ) * log Q ≤ (‖s‖ + b) * log (‖s‖ + b) * log Q := by
        have : (m : ℝ) ≤ (‖s‖ + b) * log (‖s‖ + b) := by nlinarith
        exact mul_le_mul_of_nonneg_right this hlogQ
      nlinarith
    rw [h2] at h1
    exact h1.trans (exp_le_exp.2 h3)
  have hE : 0 ≤ C * max 1 ‖P.ε‖ := by positivity
  calc C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * I0 = C * max 1 ‖P.ε‖ * I0 * (m ! * p⁻¹ ^ m) := by ring
    _ ≤ _ := by gcongr
end Erdos985.Analytic.XiOrderAux
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real Set Filter Asymptotics HurwitzZeta
lemma exp_bound_of_isBigO {F : ℝ → ℝ} (hc : ContinuousOn F (Ioi 0)) {p : ℝ} (hp : 0 ≤ p)
    (h : F =O[atTop] fun x => exp (-p * x)) :
    ∃ C, 0 ≤ C ∧ ∀ t, 1 < t → |F t| ≤ C * exp (-p * t) := by
  obtain ⟨c, hc'⟩ := h.bound
  obtain ⟨T, hT⟩ := eventually_atTop.1 hc'
  set T' := max T 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := T')).exists_bound_of_continuousOn
    (hc.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1))
  refine ⟨max (max c 0) (max M 0 * exp (p * T')), by positivity, fun t ht => ?_⟩
  rcases le_total T' t with h1 | h1
  · have := hT t ((le_max_left _ _).trans h1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have h2 := hM t ⟨ht.le, h1⟩
    rw [Real.norm_eq_abs] at h2
    calc |F t| ≤ max M 0 := h2.trans (le_max_left _ _)
      _ ≤ max M 0 * (exp (p * T') * exp (-p * t)) := by
          refine le_mul_of_one_le_right (le_max_right _ _) ?_
          rw [← exp_add, one_le_exp_iff]
          nlinarith
      _ = (max M 0 * exp (p * T')) * exp (-p * t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le
lemma combine_bounds {f g : ℝ → ℝ} {p₁ p₂ C₁ C₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hf : ∀ t, 1 < t → f t ≤ C₁ * exp (-p₁ * t)) (hg : ∀ t, 1 < t → g t ≤ C₂ * exp (-p₂ * t)) :
    ∃ p C, 0 < p ∧ 0 ≤ C ∧ (∀ t, 1 < t → f t ≤ C * exp (-p * t)) ∧
      (∀ t, 1 < t → g t ≤ C * exp (-p * t)) := by
  refine ⟨min p₁ p₂, max C₁ C₂, lt_min hp₁ hp₂, le_max_of_le_left hC₁, fun t ht => ?_,
    fun t ht => ?_⟩
  · refine (hf t ht).trans (mul_le_mul (le_max_left _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_left p₁ p₂]
  · refine (hg t ht).trans (mul_le_mul (le_max_right _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_right p₁ p₂]
lemma even_logGrowth (a : UnitAddCircle) : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (hurwitzEvenFEPair a).Λ₀ := by
  obtain ⟨p₁, hp₁, h₁⟩ := isBigO_atTop_evenKernel_sub a
  obtain ⟨p₂, hp₂, h₂⟩ := isBigO_atTop_cosKernel_sub a
  obtain ⟨C₁, hC₁, hb₁⟩ := exp_bound_of_isBigO
    ((continuousOn_evenKernel a).sub continuousOn_const) hp₁.le h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := exp_bound_of_isBigO
    ((continuousOn_cosKernel a).sub continuousOn_const) hp₂.le h₂
  obtain ⟨p, C, hp, hC, hf, hg⟩ := combine_bounds hp₁ hp₂ hC₁ hC₂ hb₁ hb₂
  refine Λ₀_logGrowth _ hp hC (fun t ht => ?_) (fun t ht => ?_)
  · have : (hurwitzEvenFEPair a).f t - (hurwitzEvenFEPair a).f₀ =
        ((evenKernel a t - if a = 0 then 1 else 0 : ℝ) : ℂ) := by
      simp only [hurwitzEvenFEPair, Function.comp_apply]
      split_ifs <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hf t ht
  · have : (hurwitzEvenFEPair a).g t - (hurwitzEvenFEPair a).g₀ =
        ((cosKernel a t - 1 : ℝ) : ℂ) := by
      simp [hurwitzEvenFEPair]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hg t ht
lemma odd_logGrowth (a : UnitAddCircle) : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (hurwitzOddFEPair a).Λ₀ := by
  obtain ⟨p₁, hp₁, h₁⟩ := isBigO_atTop_oddKernel a
  obtain ⟨p₂, hp₂, h₂⟩ := isBigO_atTop_sinKernel a
  obtain ⟨C₁, hC₁, hb₁⟩ := exp_bound_of_isBigO (continuousOn_oddKernel a) hp₁.le h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := exp_bound_of_isBigO (continuousOn_sinKernel a) hp₂.le h₂
  obtain ⟨p, C, hp, hC, hf, hg⟩ := combine_bounds hp₁ hp₂ hC₁ hC₂ hb₁ hb₂
  refine Λ₀_logGrowth _ hp hC (fun t ht => ?_) (fun t ht => ?_)
  · simpa [hurwitzOddFEPair, Complex.norm_real] using hf t ht
  · simpa [hurwitzOddFEPair, Complex.norm_real] using hg t ht
lemma completedHurwitzZetaEven₀_logGrowth (a : UnitAddCircle) :
    (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (completedHurwitzZetaEven₀ a) := by
  refine LogGrowth_congr (LogGrowth_mul
    (LogGrowth_comp (even_logGrowth a) (g := fun s => s / 2) le_rfl (fun s => ?_))
    (LogGrowth_const (1 / 2))) (fun s => ?_)
  · rw [norm_div, Complex.norm_two, add_zero]
    linarith [norm_nonneg s]
  · simp only [completedHurwitzZetaEven₀]; ring
lemma completedHurwitzZetaOdd_logGrowth (a : UnitAddCircle) :
    (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (completedHurwitzZetaOdd a) := by
  refine LogGrowth_congr (LogGrowth_mul
    (LogGrowth_comp (odd_logGrowth a) (g := fun s => (s + 1) / 2) zero_le_one (fun s => ?_))
    (LogGrowth_const (1 / 2))) (fun s => ?_)
  · rw [norm_div, Complex.norm_two]
    have := norm_add_le s 1
    rw [norm_one] at this
    linarith [norm_nonneg s]
  · simp only [completedHurwitzZetaOdd, WeakFEPair.Λ, hurwitzOddFEPair_f₀, hurwitzOddFEPair_g₀,
      smul_zero, sub_zero]
    ring
theorem completedLFunction_logGrowth {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (DirichletCharacter.completedLFunction χ) := by
  have hN : N ≠ 1 := fun h => hχ (χ.level_one' h)
  have h0 : χ 0 = 0 := χ.map_zero' hN
  have hsum : ∑ j, χ j = 0 := χ.sum_eq_zero_of_ne_one hχ
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hpow := LogGrowth_natCast_cpow_neg hNpos
  have hE : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (fun s => ∑ j : ZMod N, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s) :=
    LogGrowth_sum _ (fun j _ => LogGrowth_mul (LogGrowth_const (χ j))
      (completedHurwitzZetaEven₀_logGrowth _))
  have hO : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (fun s => ∑ j : ZMod N, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s) :=
    LogGrowth_sum _ (fun j _ => LogGrowth_mul (LogGrowth_const (χ j))
      (completedHurwitzZetaOdd_logGrowth _))
  refine LogGrowth_congr (LogGrowth_add (LogGrowth_mul hpow hE) (LogGrowth_mul hpow hO)) (fun s => ?_)
  rw [DirichletCharacter.completedLFunction, ZMod.completedLFunction_eq]
  simp only [h0, hsum, mul_zero, zero_div, sub_zero, ZMod.completedLFunction₀]
end Erdos985.Analytic.XiOrderAux
end
section
open Complex
namespace Erdos985.Analytic
theorem ZdxiZeta_def (s : ℂ) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1) :=
  Classical.choose_spec (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1)) s
theorem ZdxiZeta_eq :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) = fun (s : ℂ) => (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1) := by
  funext s
  exact ZdxiZeta_def s
theorem differentiable_xiZeta : Differentiable ℂ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) := by
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdxiZeta_eq]
  have := differentiable_completedZeta₀
  fun_prop
theorem xiZeta_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) s = s * (s - 1) * completedRiemannZeta s := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdxiZeta_def, completedRiemannZeta_eq]
  field_simp
  ring
theorem xiZeta_zero : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) 0 = 1 := by simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdxiZeta_eq]
open XiOrderAux in
theorem growth_of_logGrowth {F : ℂ → ℂ} (hF : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) F) :
    ∃ C : ℝ, ∀ s : ℂ, ‖F s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  obtain ⟨K, a, b, ha, hb, h⟩ := hF
  have hK : 0 ≤ K := LogGrowth_nonneg_K h
  set lb := Real.log b
  have hlb : 0 ≤ lb := Real.log_nonneg (by linarith)
  set C₀ := a * (2 * lb + 1 + 2 * b)
  set D := a * (b * (lb + 1))
  refine ⟨max (K * Real.exp D) C₀, fun s => (h s).trans ?_⟩
  set u := ‖s‖
  have hu : 0 ≤ u := norm_nonneg s
  set ℓ := Real.log (u + 2)
  have hℓ2 : (1 / 2 : ℝ) ≤ ℓ := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hℓu : ℓ ≤ u + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < u + 2 by linarith); linarith
  have hL : 0 ≤ u * ℓ := by positivity
  have h1 : Real.log (u + b) ≤ lb + ℓ := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have h2 : u ≤ 2 * (u * ℓ) := by nlinarith
  have key : a * ((u + b) * Real.log (u + b)) ≤ C₀ * (u * ℓ) + D := by
    have e : (u + b) * Real.log (u + b) ≤ (2 * lb + 1 + 2 * b) * (u * ℓ) + b * (lb + 1) := by
      calc (u + b) * Real.log (u + b) ≤ (u + b) * (lb + ℓ) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = lb * u + u * ℓ + b * lb + b * ℓ := by ring
        _ ≤ lb * (2 * (u * ℓ)) + u * ℓ + b * lb + b * (2 * (u * ℓ) + 1) := by
            gcongr; linarith
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left e ha
    simp only [C₀, D]; nlinarith
  calc K * Real.exp (a * ((u + b) * Real.log (u + b)))
      ≤ K * Real.exp (C₀ * (u * ℓ) + D) := by gcongr
    _ = K * Real.exp D * Real.exp (C₀ * (u * ℓ)) := by
        rw [Real.exp_add]; ring
    _ ≤ max (K * Real.exp D) C₀ * Real.exp (max (K * Real.exp D) C₀ * (u * ℓ)) :=
        mul_le_mul (le_max_left _ _)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hL))
          (Real.exp_pos _).le (le_max_of_le_left (by positivity))
    _ = _ := by ring_nf
theorem xiZeta_growth :
    ∃ C : ℝ, ∀ s : ℂ, ‖(Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  open XiOrderAux in
  have hid : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (fun s : ℂ => s) := by
    refine ⟨1, 1, 3, zero_le_one, le_rfl, fun s => ?_⟩
    have h3 : 1 ≤ Real.log (‖s‖ + 3) := one_le_log_of_three_le (by linarith [norm_nonneg s])
    have := Real.add_one_le_exp ‖s‖
    have : ‖s‖ ≤ (‖s‖ + 3) * Real.log (‖s‖ + 3) := by nlinarith [norm_nonneg s]
    have : Real.exp ‖s‖ ≤ Real.exp (1 * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  open XiOrderAux in
  have h : (fun F : ℂ → ℂ => ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * Real.exp (a * ((‖s‖ + b) * Real.log (‖s‖ + b)))) (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) :=
    LogGrowth_congr (LogGrowth_add (LogGrowth_mul (LogGrowth_mul hid
      (LogGrowth_add hid (LogGrowth_const (-1))))
      (completedHurwitzZetaEven₀_logGrowth 0)) (LogGrowth_const 1)) fun s => by
        rw [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdxiZeta_def]; simp only [completedRiemannZeta₀]; ring
  exact growth_of_logGrowth h
theorem completedLFunction_growth {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ s : ℂ, ‖DirichletCharacter.completedLFunction χ s‖
      ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) :=
  growth_of_logGrowth (XiOrderAux.completedLFunction_logGrowth hχ)
theorem completedLFunction_zero_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
  have h := hprim.completedLFunction_one_sub 1
  rw [sub_self] at h
  rw [h]
  refine mul_ne_zero (mul_ne_zero ?_ (port_rootNumber_ne_zero hprim)) ?_
  · exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr (by exact_mod_cast NeZero.ne N)
  · exact port_completedLFunction_ne_zero_of_one_le_re χ⁻¹
      (Or.inl (by simpa using hχ)) (by simp)
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.IdentityAux
open Complex MeasureTheory
theorem integrable_of_hasSum {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f) (hF_int : ∀ i, Integrable (F i))
    (hF_sum : Summable fun i => ∫ t, ‖F i t‖) (hsum : ∀ t, HasSum (fun i => F i t) (f t)) :
    Integrable f := by
  refine ⟨hf, ?_⟩
  have h1 : ∀ t, ‖f t‖ₑ ≤ ∑' i, ‖F i t‖ₑ := fun t => by
    rw [← (hsum t).tsum_eq]; exact enorm_tsum_le_tsum_enorm
  unfold HasFiniteIntegral
  calc ∫⁻ t, ‖f t‖ₑ ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ := lintegral_mono h1
    _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ := lintegral_tsum fun i => (hF_int i).aestronglyMeasurable.enorm
    _ = ∑' i, ENNReal.ofReal (∫ t, ‖F i t‖) := by
        congr 1; funext i; rw [ofReal_integral_norm_eq_lintegral_enorm (hF_int i)]
    _ = ENNReal.ofReal (∑' i, ∫ t, ‖F i t‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun _ => norm_nonneg _)
          hF_sum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top
variable {N : ℕ} [NeZero N]
theorem zero_re_mem {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.completedLFunction χ ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra h
    push Not at h
    have h1 : DirichletCharacter.completedLFunction χ (1 - (1 - ρ)) ≠ 0 := by
      rw [hprim.completedLFunction_one_sub]
      refine mul_ne_zero (mul_ne_zero ?_ (port_rootNumber_ne_zero hprim)) ?_
      · exact (cpow_ne_zero_iff_of_exponent_ne_zero (by
          intro h0; have := congrArg Complex.re h0; simp at this; linarith)).mpr
          (by exact_mod_cast NeZero.ne N)
      · exact port_completedLFunction_ne_zero_of_one_le_re χ⁻¹
          (Or.inl (by simpa using hχ)) (by simp; linarith)
    exact h1 (by simpa using hρ)
  · by_contra h
    push Not at h
    exact port_completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ
theorem order_ne_zero {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.completedLFunction χ ρ = 0) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 := by
  have hd := DirichletCharacter.differentiable_completedLFunction hχ
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    hd.differentiableOn.analyticOnNhd isOpen_univ
  have h0 : analyticOrderAt (DirichletCharacter.completedLFunction χ) 0 ≠ ⊤ := by
    rw [(analyticOrderAt_eq_zero.2 (Or.inr (completedLFunction_zero_ne_zero χ hχ hprim)))]
    exact ENat.zero_ne_top
  have htop := han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 0) (Set.mem_univ ρ) h0
  intro hm
  have := Nat.cast_analyticOrderNatAt htop
  rw [hm, Nat.cast_zero, eq_comm, analyticOrderAt_eq_zero] at this
  rcases this with h | h
  · exact h (han ρ (Set.mem_univ _))
  · exact h hρ
theorem countable_zeros [Fact H3] {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Countable {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} := by
  have hs := (hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)).1 1 one_pos
  rw [← Set.countable_univ_iff]
  convert hs.countable_support
  symm
  rw [Function.support_eq_univ]
  intro ρ
  have hm := order_ne_zero hprim hχ ρ.2
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (zero_re_mem hprim hχ ρ.2).1.ne' (by simp [h])
  have : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 hρ0
  positivity
end Erdos985.Analytic.IdentityAux
end
section
namespace Erdos985.Analytic.IdentityAux
open Complex MeasureTheory
theorem Zdkern_def (x t : ℝ) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))) :=
  Classical.choose_spec (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))) x t
theorem Zdkern_eq :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) = fun (x t : ℝ) => (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))) := by
  funext x t
  exact Zdkern_def x t
theorem ZdresKern_def (x : ℝ) (ρ : ℂ) (t : ℝ) :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))) :=
  Classical.choose_spec (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))) x ρ t
theorem ZdresKern_eq :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) = fun (x : ℝ) (ρ : ℂ) (t : ℝ) => (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))) := by
  funext x ρ t
  exact ZdresKern_def x ρ t
theorem ZdpairTerm_def (x : ℝ) (ρ : ℂ) (t : ℝ) :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t) :=
  Classical.choose_spec (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t)) x ρ t
theorem ZdpairTerm_eq :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) = fun (x : ℝ) (ρ : ℂ) (t : ℝ) => (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t) := by
  funext x ρ t
  exact ZdpairTerm_def x ρ t
lemma line_ne_zero' (t : ℝ) : (2 : ℂ) + t * I ≠ 0 := fun h => by
  have := congrArg re h; simp at this
lemma line_add_one_ne_zero' (t : ℝ) : (2 : ℂ) + t * I + 1 ≠ 0 := fun h => by
  have := congrArg re h; simp at this; norm_num at this
lemma line_sub_ne_zero' {ρ : ℂ} (hρ : ρ.re < 2) (t : ℝ) : (2 : ℂ) + t * I - ρ ≠ 0 := fun h => by
  have := congrArg re h; simp at this; linarith
lemma two_sub_ne_zero' {ρ : ℂ} (hρ : ρ.re < 2) : (2 : ℂ) - ρ ≠ 0 := fun h => by
  have := congrArg re h; simp at this; linarith
lemma pairTerm_eq (x : ℝ) (ρ : ℂ) (t : ℝ) :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t = (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x ρ t - (1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t := by
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.ZdpairTerm_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.ZdresKern_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.Zdkern_eq]
  simp only [div_eq_mul_inv, mul_inv]
  ring
lemma integrable_kern {x : ℝ} (hx : 0 < x) : Integrable ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x) := by
  have := PerronKernel.integrable_K 2 x two_pos hx
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PerronKernel.ZdK_eq] at this
  simp only [ofReal_ofNat] at this
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.Zdkern_eq]
  exact this
lemma integrable_resKern {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re < 2) :
    Integrable ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x ρ) := by
  have := perron_residue_integrable x 2 hx two_pos ρ (by simpa using hρ)
  simp only [ofReal_ofNat] at this
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.ZdresKern_eq]
  exact this
lemma integrable_pairTerm {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re < 2) :
    Integrable ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ) := by
  have : (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ = fun t => (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x ρ t - (1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t :=
    funext (pairTerm_eq x ρ)
  rw [this]
  exact (integrable_resKern hx hρ).sub ((integrable_kern hx).const_mul _)
lemma integral_kern {x : ℝ} (hx : 1 ≤ x) :
    ∫ t, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t = 2 * Real.pi * (1 - 1 / (x : ℂ)) := by
  have h := PerronKernel.perron_kernel x 2 (by linarith) two_pos
  simp only [ofReal_ofNat] at h
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.Zdkern_eq]
  rw [show (∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))) = _ from h,
    ite_eq_left_iff.2 (fun h => absurd hx h)]
  push_cast
  ring
lemma integral_pairTerm (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re < 2) (hρ0 : ρ ≠ 0)
    (hρ1 : ρ ≠ -1) :
    ∫ t, (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) (x : ℝ) ρ t = -(2 * Real.pi) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h := perron_residue (x : ℝ) 2 hx' two_pos ρ (by simpa using hρ) hρ0 hρ1
  simp only [ofReal_ofNat, ofReal_natCast] at h
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hR : ∫ t, (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) (x : ℝ) ρ t = 2 * Real.pi * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ
      + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ)) := by
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.ZdresKern_eq]
  have hK := integral_kern hx'
  simp_rw [pairTerm_eq]
  rw [integral_sub (integrable_resKern hx0 hρ) ((integrable_kern hx0).const_mul _),
    integral_const_mul, hR, hK]
  simp only [ofReal_natCast]
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdzeroTerm_eq]
  ring
lemma norm_pairTerm_le {x : ℝ} {ρ : ℂ} (hρ : ρ.re < 2) (t : ℝ) :
    ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t‖ ≤
      ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖
        / ‖(2 : ℂ) - ρ‖ := by
  have h0 := line_ne_zero' t
  have h1 := line_add_one_ne_zero' t
  have h2 := line_sub_ne_zero' hρ t
  have h3 := two_sub_ne_zero' hρ
  have heq : (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t = ((2 - ((2 : ℂ) + t * I)) / ((2 : ℂ) + t * I)) *
      ((x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1)))
        / (2 - ρ) := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.ZdpairTerm_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.Zdkern_eq]
    field_simp
    ring
  rw [heq, norm_div, norm_mul]
  gcongr
  calc ‖(2 - ((2 : ℂ) + t * I)) / ((2 : ℂ) + t * I)‖ * _ ≤ 1 * _ := by
        gcongr
        rw [norm_div, div_le_one (norm_pos_iff.2 h0)]
        have e : (2 : ℂ) - ((2 : ℂ) + t * I) = -(t * I) := by ring
        rw [e, norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
        have := abs_im_le_norm ((2 : ℂ) + t * I)
        simpa using this
    _ = _ := one_mul _
theorem integral_norm_pairTerm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ ρ : ℂ, ρ.re < 1 → ρ ≠ 0 →
      ∫ t, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t‖ ≤ C * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  refine ⟨3 * K, by positivity, fun x hx ρ hρ hρ0 => ?_⟩
  obtain ⟨hint, hbd⟩ := hK x 2 hx two_pos ρ (by norm_num; exact hρ.le)
  simp only [ofReal_ofNat] at hint hbd
  have hρ2 : ρ.re < 2 := by linarith
  have ha : 1 < ‖(2 : ℂ) - ρ‖ := by
    have := re_le_norm ((2 : ℂ) - ρ); simp at this; linarith
  have hr : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  calc ∫ t, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t‖
      ≤ ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖
          / ‖(2 : ℂ) - ρ‖ :=
        integral_mono (integrable_pairTerm hx hρ2).norm (hint.norm.div_const _)
          (norm_pairTerm_le hρ2)
    _ = (∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖)
          / ‖(2 : ℂ) - ρ‖ := integral_div _ _
    _ ≤ K * x ^ (2 : ℝ) * (1 + ‖ρ‖) ^ (-(1 / 2 : ℝ)) / ‖(2 : ℂ) - ρ‖ := by gcongr
    _ ≤ 3 * K * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ) := by
        have hle : ‖ρ‖ ≤ 3 * ‖(2 : ℂ) - ρ‖ := by
          have := norm_sub_le (2 : ℂ) ((2 : ℂ) - ρ)
          simp at this
          linarith
        have hsq : ‖ρ‖ ^ (1 / 2 : ℝ) ≤ (1 + ‖ρ‖) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hr.le (by linarith) (by norm_num)
        rw [Real.rpow_neg (by positivity), Real.rpow_add hr, Real.rpow_one]
        have hp1 : 0 < (1 + ‖ρ‖) ^ (1 / 2 : ℝ) := by positivity
        have hp2 : 0 < ‖ρ‖ ^ (1 / 2 : ℝ) := by positivity
        have hxk : 0 ≤ K * x ^ (2 : ℝ) := by positivity
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc K * x ^ (2 : ℝ) * ((1 + ‖ρ‖) ^ (1 / 2 : ℝ))⁻¹ * (‖ρ‖ * ‖ρ‖ ^ (1 / 2 : ℝ))
            ≤ K * x ^ (2 : ℝ) * ((1 + ‖ρ‖) ^ (1 / 2 : ℝ))⁻¹
                * (3 * ‖(2 : ℂ) - ρ‖ * (1 + ‖ρ‖) ^ (1 / 2 : ℝ)) := by
              gcongr
          _ = 3 * K * x ^ (2 : ℝ) * ‖(2 : ℂ) - ρ‖ := by
              field_simp
end Erdos985.Analytic.IdentityAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory IdentityAux
open scoped Classical
variable {N : ℕ} [NeZero N]
theorem explicit_formula [Fact H3] {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (x : ℕ) (hx : 1 ≤ x) :
    ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) χ x
      = (∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ)
        + ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) χ x
        - (1 - 1 / (x : ℂ)) * (deriv (DirichletCharacter.LFunction χ) 2
            / DirichletCharacter.LFunction χ 2) := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  set L := DirichletCharacter.LFunction χ with hL
  set G := ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ with hG
  set D : ℂ → ℂ := fun z => deriv Λf z / Λf z with hD
  set m : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt Λf ρ : ℂ) with hm
  set c2 : ℂ := deriv L 2 / L 2 with hc2
  have := countable_zeros hprim hχ
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hΛd : Differentiable ℂ Λf := DirichletCharacter.differentiable_completedLFunction hχ
  have hLd : Differentiable ℂ L := DirichletCharacter.differentiable_LFunction hχ
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → Λf z ≠ 0 := fun z hz =>
    port_completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  have hLne : ∀ z : ℂ, 1 ≤ z.re → L z ≠ 0 := fun z hz =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  obtain ⟨hsum_ε, b, hb⟩ := hadamard_logDeriv hΛd (completedLFunction_zero_ne_zero χ hχ hprim)
    (completedLFunction_growth χ hχ)
  have hzre : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => zero_re_mem hprim hχ ρ.2
  let F : {ρ : ℂ // Λf ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (integrable_pairTerm hx0 (by linarith [hzre ρ])).const_mul _
  obtain ⟨C, hC0, hC⟩ := integral_norm_pairTerm_le
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    calc (analyticOrderNatAt Λf ρ : ℝ) * ∫ t, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t‖
        ≤ (analyticOrderNatAt Λf ρ : ℝ) * (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC x hx0 ρ (hzre ρ).2 hρ0) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_hasSum : ∀ t : ℝ, HasSum (fun ρ => F ρ t) ((D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I) (hΛne _ (by rw [hsre]; norm_num))
    obtain ⟨h2s, h2e⟩ := hb 2 (hΛne _ (by norm_num))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t)
    convert this using 1 <;> try rfl
    · funext ρ
      simp only [F, m, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.ZdpairTerm_eq]
      ring
    · simp only [hD]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => D ((2 : ℂ) + t * I) := by
    have hcd : Continuous (deriv Λf) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs_cont).div (hΛd.continuous.comp hs_cont)
      (fun t => hΛne _ (by simp))
  have hF1_int : Integrable fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t :=
    integrable_of_hasSum
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (integrable_kern hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : ∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t
      = ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (-(2 * Real.pi) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ) := by
    rw [show (fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
    refine tsum_congr fun ρ => ?_
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    have hρ1 : (ρ : ℂ) ≠ -1 := fun h => by
      have := (hzre ρ).1; rw [h] at this; norm_num at this
    simp only [F]
    rw [integral_const_mul, integral_pairTerm x hx (by linarith [hzre ρ]) hρ0 hρ1]
  set a : ℕ → ℂ := fun n => (χ n : ℂ) * (Λ n : ℂ) with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := 2)
      (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, a]
  have hP := PerronKernel.perron_weighted a 2 two_pos ha_sum x hx
  simp only [ofReal_ofNat] at hP
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(D z - G z) := fun z hz => by
    have h1 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hz
    have h2 := logDeriv_LFunction_eq hχ hz
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hz,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hz] at h1
    change LSeries a z = _ at h1
    rw [h1, neg_div, h2]
  have hc2' : c2 = D 2 - G 2 := logDeriv_LFunction_eq hχ (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hH
  have hH_eq : ∀ t : ℝ, H t = LSeries a ((2 : ℂ) + t * I) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t := fun t => by
    simp only [hH, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.Zdkern_eq, ofReal_natCast]
    ring
  have hH_int : Integrable H := by
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) := by
      have hcd : Continuous (deriv L) := (hLd.contDiff (n := 1)).continuous_deriv le_rfl
      have : (fun t : ℝ => LSeries a ((2 : ℂ) + t * I))
          = fun t : ℝ => -(deriv L ((2 : ℂ) + t * I) / L ((2 : ℂ) + t * I)) := by
        funext t
        have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
        rw [hLS _ hz, ← logDeriv_LFunction_eq hχ hz]
      rw [this]
      exact ((hcd.comp hs_cont).div (hLd.continuous.comp hs_cont)
        (fun t => hLne _ (by simp))).neg
    set B := ∑' n, ‖LSeries.term a 2 n‖
    have hbd : ∀ t : ℝ, ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ B := fun t => by
      have hs2 := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := 2)
        (by norm_num)).norm
      have heq : (fun n => ‖LSeries.term a ((2 : ℂ) + t * I) n‖)
          = fun n => ‖LSeries.term a 2 n‖ := by
        funext n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre]; simp
      calc ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a ((2 : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (by rw [heq]; exact hs2)
        _ = B := by rw [heq]
    have : H = fun t : ℝ => LSeries a ((2 : ℂ) + t * I) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t := funext hH_eq
    rw [this]
    refine Integrable.mono' ((integrable_kern hx0).norm.const_mul B)
      (hcont.aestronglyMeasurable.mul (integrable_kern hx0).1)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t) (norm_nonneg _)
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t : ℝ => H t + (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t + c2 * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    rw [hH_eq, hLS _ hz, hc2']
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.Zdkern_eq, ofReal_natCast]
    ring
  have hgamma : ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) χ x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t)
        + c2 * ∫ t, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t) := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdgammaPart_eq]
    rw [← hG, hF2, integral_add _ ((integrable_kern hx0).const_mul _),
      integral_add hH_int hF1_int, integral_const_mul]
    exact hH_int.add hF1_int
  have hbach : ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) χ x = ∑ n ∈ Finset.Ioo 0 x, a n * (1 - (n : ℂ) / x) := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.ZdbachSum_eq]
    rw [show ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)
        = ∑ n ∈ Finset.range x, a n * (1 - (n : ℂ) / x) from
      Finset.sum_congr rfl fun n _ => by simp only [a]; ring]
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Ioo] at hn; rw [Finset.mem_range]; omega
    · have : n = 0 := by rw [Finset.mem_Ioo] at hn'; rw [Finset.mem_range] at hn; omega
      subst this
      simp [a]
  have hbach' : ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) χ x = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    rw [hbach, hP]
  have hK := integral_kern hx1
  have htsum : ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (-(2 * Real.pi) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ)
      = -(2 * Real.pi) * ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => by ring
  rw [hgamma, hbach', hF1_integral, htsum, hK]
  simp only [ofReal_natCast]
  field_simp
  ring
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.BoundsAux
open Complex
lemma zeroTerm_eq (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ = 2 / (ρ * (2 - ρ)) - (3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))
      - (x : ℂ) ^ ρ / (ρ * (ρ + 1)) := by
  have h0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  have h2 : (2 : ℂ) - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have h1 : (1 : ℂ) + ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have h1' : ρ + 1 ≠ 0 := by rwa [add_comm]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdzeroTerm_eq]
  rw [cpow_neg_one]
  field_simp
  ring
lemma norm_two_sub_eq {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖(2 : ℂ) - ρ‖ = ‖ρ + 1‖ := by
  rw [← Complex.norm_conj (ρ + 1)]
  congr 1
  apply Complex.ext <;> norm_num [hρ]
lemma norm_le_norm_add_one {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖ρ + 1‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp [Complex.normSq_apply, hρ]
  norm_num
end Erdos985.Analytic.BoundsAux
namespace Erdos985.Analytic
open Complex BoundsAux
theorem norm_zeroTerm_le' (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖(Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖ ≤ (√(x : ℝ) + 2 + 3 / x) / ‖ρ * (ρ + 1)‖ := by
  have h0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  have h1' : ρ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hP : 0 < ‖ρ * (ρ + 1)‖ := norm_pos_iff.mpr (mul_ne_zero h0 h1')
  have hn0 : 0 < ‖ρ‖ := norm_pos_iff.mpr h0
  have hn1 : 0 < ‖ρ + 1‖ := norm_pos_iff.mpr h1'
  have e2 := norm_two_sub_eq hρ
  have hle := norm_le_norm_add_one hρ
  rw [zeroTerm_eq x hx hρ]
  have t1 : ‖2 / (ρ * (2 - ρ))‖ = 2 / ‖ρ * (ρ + 1)‖ := by
    rw [norm_div, norm_mul, norm_mul, e2]; simp
  have t2 : ‖(3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))‖ ≤ (3 / x) / ‖ρ * (ρ + 1)‖ := by
    rw [norm_div, norm_mul, norm_mul, e2, add_comm 1 ρ, norm_div]
    simp only [Complex.norm_natCast, Complex.norm_ofNat]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hle hn1.le
  have t3 : ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ = √(x : ℝ) / ‖ρ * (ρ + 1)‖ := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega), hρ, Real.sqrt_eq_rpow]
  calc _ ≤ ‖2 / (ρ * (2 - ρ)) - (3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))‖
          + ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ := norm_sub_le _ _
    _ ≤ ‖2 / (ρ * (2 - ρ))‖ + ‖(3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))‖
          + ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 2 / ‖ρ * (ρ + 1)‖ + (3 / x) / ‖ρ * (ρ + 1)‖ + √(x : ℝ) / ‖ρ * (ρ + 1)‖ := by
          rw [t1, t3]; linarith
    _ = _ := by field_simp; ring
end Erdos985.Analytic
end
section
open Real ArithmeticFunction
namespace Erdos985.Analytic.BoundsAux
lemma term_eq2 (f : ℕ → ℝ) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) 2 n = ((f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat]
    push_cast
    rfl
lemma lseries_eq2 (f : ℕ → ℝ) :
    LSeries (fun n => (f n : ℂ)) 2 = ((∑' n : ℕ, f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (term_eq2 f)
lemma summable_of_lseries2 (f : ℕ → ℝ) (h : LSeriesSummable (fun n => (f n : ℂ)) 2) :
    Summable fun n : ℕ => f n / (n : ℝ) ^ 2 := by
  have : LSeries.term (fun n => (f n : ℂ)) 2 =
      fun n => ((f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := funext (term_eq2 f)
  rw [LSeriesSummable, this] at h
  exact Complex.summable_ofReal.mp h
lemma re2 : 1 < (2 : ℂ).re := by norm_num
lemma summable_Λ2 : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ 2 :=
  summable_of_lseries2 _ (LSeriesSummable_vonMangoldt re2)
lemma summable_log2 : Summable fun n : ℕ => Real.log n / (n : ℝ) ^ 2 := by
  refine summable_of_lseries2 (fun n => Real.log n) ?_
  have := (LSeriesSummable_vonMangoldt re2).convolution (LSeriesSummable_one_iff.mpr re2)
  rw [convolution_vonMangoldt_const_one] at this
  convert this using 2 with n
  simp [Complex.natCast_log]
lemma mul_eq2 :
    (∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) =
      ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
  have h := LSeries_convolution' (LSeriesSummable_vonMangoldt re2)
    (LSeriesSummable_one_iff.mpr re2)
  rw [convolution_vonMangoldt_const_one] at h
  have e1 := lseries_eq2 (fun n => (Λ n : ℝ))
  have e2 := lseries_eq2 (fun _ => (1 : ℝ))
  have e3 := lseries_eq2 (fun n : ℕ => Real.log n)
  have h1 : (1 : ℕ → ℂ) = fun _ => ((1 : ℝ) : ℂ) := by ext; simp
  have h3 : (fun n : ℕ => Complex.log n) = fun n : ℕ => ((Real.log n : ℝ) : ℂ) := by
    ext n; simp [Complex.natCast_log]
  rw [h1, h3, e1, e2, e3] at h
  exact_mod_cast h.symm
lemma g2_anti {c y : ℝ} (hc : 2 ≤ c) (hcy : c ≤ y) :
    Real.log y / y ^ 2 ≤ Real.log c / c ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hy0 : 0 < y := by linarith
  have hL : 2 / 3 ≤ Real.log c := by
    have := Real.log_le_log (by norm_num) hc
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log y - Real.log c ≤ y / c - 1 := by
    rw [← Real.log_div hy0.ne' hc0.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hlog' : (Real.log y - Real.log c) * c ≤ y - c := by
    have : y / c - 1 = (y - c) / c := by field_simp
    rw [this, le_div_iff₀ hc0] at hlog; exact hlog
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ y - c := by linarith
  have : (y - c) * c ≤ Real.log c * (y - c) * (y + c) := by
    have : c ≤ Real.log c * (y + c) := by nlinarith
    nlinarith
  nlinarith
theorem ZdG2_def (x : ℝ) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) x = (open Real ArithmeticFunction in (Real.log x + 1) / x) :=
  Classical.choose_spec (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x)) x
theorem ZdG2_eq :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) = fun (x : ℝ) => (open Real ArithmeticFunction in (Real.log x + 1) / x) := by
  funext x
  exact ZdG2_def x
lemma hasDerivAt_G2 {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) (-(Real.log t / t ^ 2)) t := by
  have h1 : HasDerivAt (fun x => Real.log x + 1) (t⁻¹) t :=
    (Real.hasDerivAt_log ht.ne').add_const 1
  have := h1.div (hasDerivAt_id' t) ht.ne'
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.ZdG2_eq]
  convert this using 1 <;> try rfl
  field_simp
  ring
lemma d2_step {x : ℝ} (hx : 2 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ 2 ≤ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) x - (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) (x + 1) := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) (fun t => -(Real.log t / t ^ 2))
    (by linarith : x < x + 1)
    (fun t ht => (hasDerivAt_G2 (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_G2 (by linarith [ht.1]))
  have : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) x - (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) (x + 1) = Real.log c / c ^ 2 := by
    rw [show x + 1 - x = 1 by ring, div_one] at hcd
    linarith
  rw [this]
  exact g2_anti (by linarith [hc.1]) hc.2.le
lemma G2_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) x := by
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.ZdG2_eq]
  have := Real.log_nonneg hx
  have : 0 < x := by linarith
  positivity
lemma d2_tail (K : ℕ) (hK : 3 ≤ K) :
    ∑' i : ℕ, Real.log ((i + K : ℕ) : ℝ) / (((i + K : ℕ) : ℝ)) ^ 2 ≤ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) ((K : ℝ) - 1) := by
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  refine Real.tsum_le_of_sum_range_le (fun i => ?_) (fun M => ?_)
  · have : (1 : ℝ) ≤ ((i + K : ℕ) : ℝ) := by push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := Real.log_nonneg this
    positivity
  · have htel := Finset.sum_range_sub' (fun i : ℕ => (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) ((K : ℝ) - 1 + i)) M
    simp only [Nat.cast_zero, add_zero] at htel
    have hG : 0 ≤ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Real ArithmeticFunction in (Real.log x + 1) / x))) ((K : ℝ) - 1 + M) :=
      G2_nonneg (by linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)])
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (le_of_eq_of_le htel (by linarith))
    have hx : (2 : ℝ) ≤ (K : ℝ) - 1 + i := by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := d2_step hx
    push_cast
    rw [show (K : ℝ) - 1 + ((i : ℝ) + 1) = (K : ℝ) - 1 + i + 1 by ring,
      show (i : ℝ) + K = (K : ℝ) - 1 + i + 1 by ring]
    exact this
lemma D2_le : ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 ≤ 0.962 := by
  obtain ⟨l2, l3, l5, -, -, -, -, -⟩ := ConstantsAux.log_primes_le
  have hD := (summable_log2.sum_add_tsum_nat_add 7).symm
  have hdt := d2_tail 7 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hD
  norm_num at hD hdt
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.ZdG2_eq] at hdt
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [hD]
  norm_num [e4, e6] at hdt ⊢
  linarith
lemma S2_le : ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 ≤ 0.6 := by
  have hmul := mul_eq2
  have hZ : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = π ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  have hD := D2_le
  have hS : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  rw [hZ] at hmul
  have hpi : (1.643 : ℝ) ≤ π ^ 2 / 6 := by
    nlinarith [Real.pi_gt_d2, mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 3.14) Real.pi_gt_d2.le]
  set S := ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2
  by_contra h
  have h' := (not_le.mp h).le
  nlinarith [mul_le_mul h' hpi (by norm_num) hS]
end Erdos985.Analytic.BoundsAux
namespace Erdos985.Analytic
open Complex BoundsAux
variable {N : ℕ} [NeZero N]
theorem norm_logDeriv_LFunction_two_le' (χ : DirichletCharacter ℂ N) :
    ‖deriv (DirichletCharacter.LFunction χ) 2 / DirichletCharacter.LFunction χ 2‖ ≤ 0.6 := by
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds 2] LSeries (fun n => χ n) := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s hs
    exact DirichletCharacter.LFunction_eq_LSeries χ hs
  rw [hev.deriv_eq, hev.eq_of_nhds]
  have key := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ re2
  rw [show deriv (LSeries fun n => χ n) 2 / LSeries (fun n => χ n) 2
      = -(-deriv (LSeries fun n => χ n) 2 / LSeries (fun n => χ n) 2) by ring, ← key, norm_neg]
  refine le_trans ?_ S2_le
  have hsum := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ re2
  rw [LSeries]
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) hsum.norm summable_Λ2
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat, norm_div, Pi.mul_apply, norm_mul, norm_pow,
    Complex.norm_natCast]
  rw [show ‖((Λ n : ℝ) : ℂ)‖ = Λ n from by
    rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]]
  gcongr
  calc ‖χ n‖ * Λ n ≤ 1 * Λ n :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ n) vonMangoldt_nonneg
    _ = Λ n := one_mul _
end Erdos985.Analytic
end
section
open Complex Filter Topology Set
namespace Erdos985.Analytic.BoundsAux
theorem ZdrD_def (x : ℝ) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x))) x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x) :=
  Classical.choose_spec (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x)) x
theorem ZdrD_eq :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x))) = fun (x : ℝ) => (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x) := by
  funext x
  exact ZdrD_def x
lemma digamma_ofReal {x : ℝ} (hx : 0 < x) : digamma (x : ℂ) = ((Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x))) x : ℂ) := by
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have hneR : ∀ m : ℕ, x ≠ -m := fun m h => by linarith [m.cast_nonneg (α := ℝ)]
  have h1 := ((Complex.differentiableAt_Gamma _ hne).hasDerivAt).comp_ofReal
  have h2 := ((Real.differentiableAt_Gamma hneR).hasDerivAt).ofReal_comp
  have heq : (fun t : ℝ => Complex.Gamma (t : ℂ)) = fun t => ((Real.Gamma t : ℝ) : ℂ) :=
    funext Complex.Gamma_ofReal
  rw [heq] at h1
  have hd := h1.unique h2
  rw [digamma_def, logDeriv_apply, hd, Complex.Gamma_ofReal, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.ZdrD_def, Function.comp_def,
    deriv.log (Real.differentiableAt_Gamma hneR) (Real.Gamma_pos_of_pos hx).ne']
  push_cast
  rfl
lemma rD_bounds {x : ℝ} (hx : 1 < x) : Real.log (x - 1) ≤ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x))) x ∧ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x))) x ≤ Real.log x := by
  let f := Real.log ∘ Real.Gamma
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec (y : ℝ) (hy : 0 < y) : f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hder {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ f y := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith [m.cast_nonneg (α := ℝ)])
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.ZdrD_eq]
  constructor
  · refine (le_of_eq ?_).trans (hc.slope_le_deriv (mem_Ioi.mpr (by linarith : (0:ℝ) < x - 1))
      (mem_Ioi.mpr (by linarith : (0:ℝ) < x)) (by linarith) (hder (by linarith)))
    rw [slope_def_field, show x - (x - 1) = (1:ℝ) by ring, div_one]
    have := h_rec (x - 1) (by linarith)
    rw [show x - 1 + 1 = x by ring] at this
    linarith
  · refine (hc.deriv_le_slope (mem_Ioi.mpr (by linarith : (0:ℝ) < x))
      (mem_Ioi.mpr (by linarith : (0:ℝ) < x + 1)) (by linarith) (hder (by linarith))).trans
      (le_of_eq ?_)
    rw [slope_def_field, show x + 1 - x = (1:ℝ) by ring, div_one, h_rec x (by linarith)]
    ring
lemma log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.log a - Real.log b ≤ a / b - 1 := by
  rw [← Real.log_div ha.ne' hb.ne']
  exact Real.log_le_sub_one_of_pos (by positivity)
lemma tendsto_rD_sub {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x))) (x + n) - (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x))) (1 + n)) atTop (𝓝 0) := by
  have hC := tendsto_const_div_atTop_nhds_zero_nat (x + 4)
  have hC' := hC.neg
  rw [neg_zero] at hC'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hC' hC ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨l1, -⟩ := rD_bounds (x := x + n) (by linarith)
    obtain ⟨-, u2⟩ := rD_bounds (x := 1 + n) (by linarith)
    have := log_sub_log_le (a := 1 + n) (b := x + n - 1) (by linarith) (by linarith)
    have hq : (1 + n) / (x + n - 1) - 1 ≤ (x + 4) / n := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨-, u1⟩ := rD_bounds (x := x + n) (by linarith)
    obtain ⟨l2, -⟩ := rD_bounds (x := 1 + n) (by linarith)
    rw [show 1 + (n : ℝ) - 1 = n by ring] at l2
    have := log_sub_log_le (a := x + n) (b := n) (by linarith) (by linarith)
    have hq : (x + n) / n - 1 ≤ (x + 4) / n := by
      rw [div_sub_one (by linarith)]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
lemma norm_term_le {w : ℂ} (hw : 1 / 2 < w.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)‖ ≤ 2 * (‖w‖ + 1) / ((k : ℝ) + 1) ^ 2 := by
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hre : ((k : ℝ) + 1) / 2 ≤ ‖(k : ℂ) + w‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp
    linarith [k.cast_nonneg (α := ℝ)]
  have hkw : ((k : ℂ) + w) ≠ 0 := by
    intro h; rw [h, norm_zero] at hre; linarith [k.cast_nonneg (α := ℝ)]
  rw [div_sub_div _ _ hk1 hkw, norm_div, norm_mul]
  have e1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (k + 1)
  rw [e1]
  have hnum : ‖1 * ((k : ℂ) + w) - (k + 1) * 1‖ ≤ ‖w‖ + 1 := by
    rw [show 1 * ((k : ℂ) + w) - (k + 1) * 1 = w - 1 by ring]
    exact (norm_sub_le _ _).trans (by simp)
  have hk0 : (0 : ℝ) < k + 1 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ ‖w‖ + 1 := by positivity
  calc ‖1 * ((k : ℂ) + w) - (k + 1) * 1‖ * ((k : ℝ) + 1) ^ 2
      ≤ (‖w‖ + 1) * ((k : ℝ) + 1) ^ 2 := by gcongr
    _ ≤ 2 * (‖w‖ + 1) * (((k : ℝ) + 1) * ‖(k : ℂ) + w‖) := by
      nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : 0 ≤ 2 * (‖w‖ + 1) * ((k : ℝ) + 1))]
lemma summable_inv_sq_succ : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this
lemma summable_term {w : ℂ} (hw : 1 / 2 < w.re) :
    Summable fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w) := by
  refine Summable.of_norm_bounded ?_ (norm_term_le hw)
  exact (summable_inv_sq_succ.mul_left (2 * (‖w‖ + 1))).congr (fun k => by ring)
lemma hasSum_digamma_real {x : ℝ} (hx : 1 / 2 < x) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)) (digamma x - digamma 1) := by
  have hx0 : 0 < x := by linarith
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have h1' : ∀ m : ℕ, (1 : ℂ) ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)) =
      (digamma x - digamma 1) - (digamma ((x + n : ℝ) : ℂ) - digamma ((1 + n : ℝ) : ℂ)) := by
    intro n
    push_cast
    rw [port_digamma_apply_add_nat hx' n, port_digamma_apply_add_nat h1' n, Finset.sum_sub_distrib]
    simp only [one_div, add_comm (1 : ℂ), add_comm (x : ℂ)]
    ring
  have hs := summable_term (w := (x : ℂ)) (by simpa using hx)
  rw [hs.hasSum_iff_tendsto_nat]
  simp_rw [hpart]
  rw [show nhds (digamma (x : ℂ) - digamma 1) = nhds (digamma (x : ℂ) - digamma 1 - 0) by simp]
  refine tendsto_const_nhds.sub ?_
  have : (fun n : ℕ => digamma ((x + n : ℝ) : ℂ) - digamma ((1 + n : ℝ) : ℂ)) =
      fun n : ℕ => (((Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x))) (x + n) - (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℝ → ℝ, ∀ (x : ℝ), f x = (open Complex Filter Topology Set in deriv (Real.log ∘ Real.Gamma) x))) (1 + n) : ℝ) : ℂ) := by
    funext n
    rw [digamma_ofReal (by positivity), digamma_ofReal (by positivity)]
    push_cast; ring
  rw [this, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp]
  exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_rD_sub hx0)
lemma differentiableOn_digamma :
    DifferentiableOn ℂ digamma {z : ℂ | 0 < z.re} := by
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hne : ∀ z ∈ {z : ℂ | 0 < z.re}, ∀ m : ℕ, z ≠ -m := fun z hz m h => by
    rw [h] at hz; simp at hz; linarith [m.cast_nonneg (α := ℝ)]
  have hG : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have : digamma = fun z => deriv Gamma z / Gamma z := by
    funext z; rw [digamma_def, logDeriv_apply]
  rw [this]
  exact (hG.deriv ho).div hG (fun z hz => Complex.Gamma_ne_zero_of_re_pos hz)
lemma differentiableOn_tsum_term (R : ℝ) :
    DifferentiableOn ℂ (fun z => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)))
      ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 R) := by
  refine differentiableOn_tsum_of_summable_norm (u := fun k : ℕ => 2 * (R + 1) / ((k : ℝ) + 1) ^ 2)
    (F := fun (k : ℕ) (z : ℂ) => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))
    ?_ (fun k => ?_) ((isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball)
    (fun k z hz => ?_)
  · exact (summable_inv_sq_succ.mul_left (2 * (R + 1))).congr (fun k => by ring)
  · intro z hz
    have hkz : (k : ℂ) + z ≠ 0 := by
      intro h
      have h1 := congrArg Complex.re h
      have h2 : 1 / 2 < z.re := hz.1
      simp only [add_re, natCast_re, zero_re] at h1
      linarith [k.cast_nonneg (α := ℝ)]
    have : DifferentiableAt ℂ (fun z : ℂ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) z := by
      fun_prop (disch := exact hkz)
    exact this.differentiableWithinAt
  · refine (norm_term_le hz.1 k).trans ?_
    have hz2 : ‖z‖ < R := by simpa using hz.2
    gcongr
lemma frequently_eq_one :
    ∃ᶠ z in 𝓝[≠] (1 : ℂ), (digamma z - digamma 1) =
      ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) := by
  let u : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hu : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall (fun n => ?_)⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ))
      rw [add_zero] at this
      have := (Complex.continuous_ofReal.tendsto _).comp this
      simpa [u, Function.comp_def] using this
    · simp only [mem_compl_iff, mem_singleton_iff, u]
      intro h
      have h1 := congrArg Complex.re h
      simp only [ofReal_re, one_re] at h1
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  refine hu.frequently (Frequently.of_forall (fun n => ?_))
  have hx : 1 / 2 < (1 + 1 / ((n : ℝ) + 1)) := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact (hasSum_digamma_real hx).tsum_eq.symm
theorem hasSum_digamma {w : ℂ} (hw : 1 / 2 < w.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)) (digamma w - digamma 1) := by
  have hUo : IsOpen ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
    (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
    ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hF : DifferentiableOn ℂ (fun z => digamma z - digamma 1)
      ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) := by
    refine (differentiableOn_digamma.mono (fun z hz => ?_)).sub_const _
    have h : 1 / 2 < z.re := hz.1
    show 0 < z.re
    linarith
  have h1U : (1 : ℂ) ∈ ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
    ⟨by norm_num, by rw [Metric.mem_ball, dist_zero_right, norm_one]; linarith [norm_nonneg w]⟩
  have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    ((differentiableOn_tsum_term _).analyticOnNhd hUo) hUc h1U frequently_eq_one
  have hwU : w ∈ ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) := ⟨hw, by simp⟩
  have := heq hwU
  simp only at this
  rw [this]
  exact (summable_term hw).hasSum
end Erdos985.Analytic.BoundsAux
end
section
open Filter Topology
namespace Erdos985.Analytic.BoundsAux
theorem Zdtau_def (x : ℝ) (m : ℕ) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))) :=
  Classical.choose_spec (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1)))) x m
theorem Zdtau_eq :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) = fun (x : ℝ) (m : ℕ) => (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))) := by
  funext x m
  exact Zdtau_def x m
lemma core_ge (y p M K : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ y) (hK : 0 ≤ K) (hM : 2 * (K + 1) ≤ M) :
    -(1 / 2) * (1 / ((K + 1) * (K + 2))) ≤
      (1 - y) / (2 + M) - (p / (M * (M - 1)) + 1 / M - y / (M - 1)) := by
  have h1 : M - 1 ≠ 0 := by intro h; linarith
  have h2 : M ≠ 0 := by intro h; linarith
  have h3 : 2 + M ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : (1 - y) / (2 + M) - (p / (M * (M - 1)) + 1 / M - y / (M - 1))
      - -(1 / 2) * (1 / ((K + 1) * (K + 2))) =
      ((M - 1) * (M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K) + (K + 1) * (K + 2) * (4 * M - 4) * y
        + 2 * (K + 1) * (K + 2) * (M + 2) * (y - p)) / (2 * M * (K + 1) * (K + 2) * (M - 1) * (2 + M)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  have hy : 0 ≤ y := hp0.trans hp
  apply div_nonneg
  · have : 0 ≤ M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K := by nlinarith
    have : 0 ≤ (M - 1) * (M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K) := mul_nonneg (by linarith) this
    have : 0 ≤ (K + 1) * (K + 2) * (4 * M - 4) * y :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) hy
    have : 0 ≤ 2 * (K + 1) * (K + 2) * (M + 2) * (y - p) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    linarith
  · have : 0 ≤ M - 1 := by linarith
    have : 0 ≤ M := by linarith
    positivity
lemma core_even (y p K : ℝ) (hp0 : 0 ≤ p) (hy : 0 ≤ y) (hK : 0 ≤ K) :
    (1 - y) / (2 + 2 * (K + 1)) - (p / (2 * (K + 1) * (2 * (K + 1) - 1)) + 1 / (2 * (K + 1))
      - y / (2 * (K + 1) - 1)) ≤ (3 * y - 1) / 2 * (1 / ((K + 1) * (K + 2))) := by
  have h1 : 2 * K + 1 ≠ 0 := by intro h; linarith
  have h1' : 2 * (K + 1) - 1 ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : (3 * y - 1) / 2 * (1 / ((K + 1) * (K + 2))) - ((1 - y) / (2 + 2 * (K + 1)) -
      (p / (2 * (K + 1) * (2 * (K + 1) - 1)) + 1 / (2 * (K + 1)) - y / (2 * (K + 1) - 1))) =
      (K * p + 3 * K * y + 2 * p) / (2 * (K + 1) * (K + 2) * (2 * K + 1)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  positivity
lemma core_odd (y p K : ℝ) (hp0 : 0 ≤ p) (hy : 0 ≤ y) (hK : 0 ≤ K) :
    (1 - y) / (2 + (2 * (K + 1) + 1)) - (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1))
      + 1 / (2 * (K + 1) + 1) - y / (2 * (K + 1) + 1 - 1))
      ≤ 3 * y / 4 * (1 / ((K + 1) * (K + 2))) := by
  have h1 : 2 * K + 3 ≠ 0 := by intro h; linarith
  have h2 : 2 * K + 5 ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : 3 * y / 4 * (1 / ((K + 1) * (K + 2))) - ((1 - y) / (2 + (2 * (K + 1) + 1)) -
      (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1)) + 1 / (2 * (K + 1) + 1)
        - y / (2 * (K + 1) + 1 - 1))) =
      (4 * K ^ 2 * p + 8 * K ^ 2 + 18 * K * p + 6 * K * y + 24 * K + 20 * p + 9 * y + 16) /
        (4 * (K + 1) * (K + 2) * (2 * K + 3) * (2 * K + 5)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  positivity
lemma tau_ge (x : ℝ) (hx : 1 ≤ x) (k : ℕ) (m : ℕ) (hm : 2 * (k + 1) ≤ m) :
    -(1 / 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x m := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.Zdtau_eq, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have hy1 : 1 / x ≤ 1 := by rw [div_le_one (by linarith)]; exact hx
  exact core_ge _ _ _ _ (by positivity) (pow_le_of_le_one hy0.le hy1 hm0) (Nat.cast_nonneg k)
    (by exact_mod_cast hm)
lemma tau_le_even (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1)) ≤ (3 * (1 / x) - 1) / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have hm0 : 2 * (k + 1) ≠ 0 := by omega
  have hm1 : 2 * (k + 1) ≠ 1 := by omega
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.Zdtau_eq, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have := core_even (1 / x) ((1 / x) ^ (2 * (k + 1))) k (by positivity) hy0.le (Nat.cast_nonneg k)
  push_cast
  exact this
lemma tau_le_odd (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1) + 1) ≤ 3 * (1 / x) / 4 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have hm0 : 2 * (k + 1) + 1 ≠ 0 := by omega
  have hm1 : 2 * (k + 1) + 1 ≠ 1 := by omega
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.Zdtau_eq, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have := core_odd (1 / x) ((1 / x) ^ (2 * (k + 1) + 1)) k (by positivity) hy0.le
    (Nat.cast_nonneg k)
  push_cast
  exact this
lemma hasSum_u : HasSum (fun k : ℕ => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
  have hps : ∀ n : ℕ, ∑ i ∈ Finset.range n, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) =
      1 - 1 / ((n : ℝ) + 1) := by
    intro n
    have := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + 1)) n
    simp only [Nat.cast_zero, zero_add, div_one, Nat.cast_add, Nat.cast_one] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
    ring
  simp_rw [hps]
  have := tendsto_one_div_add_atTop_nhds_zero_nat.const_sub (1 : ℝ)
  simpa using this
theorem tsum_tau_bound (x : ℝ) (hx : 1 ≤ x) (a : ℕ) (ha : a ≤ 1) :
    Summable (fun k : ℕ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * k + a)) ∧
      |∑' k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * k + a)| ≤ Real.log x + 1 := by
  set y := 1 / x with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one (by linarith)]; exact hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL1 : 1 - y ≤ Real.log x := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < x)
    rwa [hy, one_div]
  set u : ℕ → ℝ := fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k => by positivity
  set B : ℝ := if a = 0 then (3 * y - 1) / 2 else 3 * y / 4 with hB
  have hup : ∀ k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1) + a) ≤ B * u k := by
    intro k
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · simp only [hB, ↓reduceIte]; exact tau_le_even x hx k
    · simp only [hB, one_ne_zero, ite_false]; exact tau_le_odd x hx k
  have hlo : ∀ k : ℕ, -(1 / 2) * u k ≤ (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1) + a) :=
    fun k => tau_ge x hx k _ (by omega)
  have hB1 : |B| ≤ 1 := by
    rw [hB]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hg : Summable (fun k : ℕ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1) + a)) := by
    refine Summable.of_norm_bounded hasSum_u.summable (fun k => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hup k
    have h2 := hlo k
    have h3 : B * u k ≤ u k := by
      have := (abs_le.mp hB1).2
      nlinarith [hu0 k]
    constructor <;> nlinarith [hu0 k]
  have hS : Summable (fun k : ℕ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * k + a)) := by
    exact (summable_nat_add_iff 1).mp hg
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq_zero_add]
  have e1 : (fun k : ℕ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1) + a)) = fun k : ℕ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1) + a) := rfl
  have hle : ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1) + a) ≤ B := by
    have := Summable.tsum_le_tsum hup hg (hasSum_u.summable.mul_left B)
    rwa [tsum_mul_left, hasSum_u.tsum_eq, mul_one] at this
  have hge : -(1 / 2) ≤ ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1) + a) := by
    have := Summable.tsum_le_tsum hlo (hasSum_u.summable.mul_left _) hg
    rwa [tsum_mul_left, hasSum_u.tsum_eq, mul_one] at this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · simp only [hB, ite_true] at hle
    simp only [mul_zero, add_zero, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.Zdtau_eq, ite_true] at hle hge ⊢
    rw [← hy] at *
    rw [abs_le]; constructor <;> linarith
  · simp only [hB, one_ne_zero, ite_false] at hle
    simp only [mul_zero, zero_add, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.Zdtau_eq, ite_true, one_ne_zero, ite_false] at hle hge ⊢
    rw [← hy] at *
    have hyL : y * Real.log x ≤ Real.log x := by nlinarith
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hy0.le hL]
end Erdos985.Analytic.BoundsAux
end
section
open Complex MeasureTheory Filter Topology
namespace Erdos985.Analytic.BoundsAux
lemma parity_le_one {N : ℕ} (χ : DirichletCharacter ℂ N) : ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ ≤ 1 := by
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.Zdparity_eq]; split_ifs <;> norm_num
lemma hasSum_gammaLogDeriv {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => 1 / (2 + ((2 * k + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ : ℕ) : ℂ))
        - 1 / (s + ((2 * k + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ : ℕ) : ℂ)))
      (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ s - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) := by
  have ha0 : (0 : ℝ) ≤ (((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ : ℝ) := Nat.cast_nonneg _
  have hw : 1 / 2 < ((s + (((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have hw2 : 1 / 2 < ((2 + (((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have h := ((hasSum_digamma hw).sub (hasSum_digamma hw2)).mul_left (1 / 2)
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdgammaLogDeriv_eq]
  convert h using 1 <;> try rfl
  · funext k
    have hh (u z : ℂ) : 1 / 2 * (1 / (u + z / 2)) = 1 / (2 * u + z) := by
      rw [one_div_mul_one_div]; congr 1; ring
    rw [show (1 / 2 : ℂ) * (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (s + (((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ : ℂ)) / 2)
        - (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (2 + (((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ : ℂ)) / 2)))
        = 1 / 2 * (1 / ((k : ℂ) + (2 + (((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ : ℂ)) / 2))
          - 1 / 2 * (1 / ((k : ℂ) + (s + (((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ : ℂ)) / 2)) by ring, hh, hh]
    push_cast
    congr 1 <;> congr 1 <;> ring
  · ring
theorem ZdgTerm_def (x : ℕ) (m : ℕ) (t : ℝ) :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))) :=
  Classical.choose_spec (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))) x m t
theorem ZdgTerm_eq :
    (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) = fun (x : ℕ) (m : ℕ) (t : ℝ) => (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))) := by
  funext x m t
  exact ZdgTerm_def x m t
lemma gTerm_eq (x m : ℕ) (t : ℝ) : (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m t =
    1 / (2 + (m : ℂ)) * ((x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
    - (x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have h0 : (2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h1 : (2 : ℂ) + t * I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (2 : ℂ) + t * I + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (2 : ℂ) + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.ZdgTerm_eq]
  rw [sub_neg_eq_add]
  field_simp
lemma hw_m (m : ℕ) : (-(m : ℂ)).re < 2 := by
  simp only [neg_re, natCast_re]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
lemma integrable_gTerm (x : ℕ) (hx : 1 ≤ x) (m : ℕ) : Integrable ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hK := PerronAux.integrable_cesaro_kernel (x := (x : ℝ)) (c := 2) hx0 two_pos
  have hP := PerronAux.integrable_perron_kernel (x := (x : ℝ)) (c := 2) hx0 two_pos (hw_m m)
  simp only [ofReal_natCast, ofReal_ofNat] at hK hP
  rw [show (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m = _ from funext (gTerm_eq x m)]
  exact (hK.const_mul _).sub hP
lemma integral_gTerm (x : ℕ) (hx : 1 ≤ x) (m : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m t = ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x m : ℂ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hK := PerronAux.integrable_cesaro_kernel (x := (x : ℝ)) (c := 2) hx0 two_pos
  have hP := PerronAux.integrable_perron_kernel (x := (x : ℝ)) (c := 2) hx0 two_pos (hw_m m)
  have hC := perron_cesaro (x : ℝ) 2 hx0 two_pos
  simp only [ofReal_natCast, ofReal_ofNat] at hK hP hC
  rw [show (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m = _ from funext (gTerm_eq x m), integral_sub (hK.const_mul _) hP,
    integral_const_mul, mul_sub, mul_left_comm, hC,
    max_eq_right (show (0 : ℝ) ≤ 1 - 1 / (x : ℝ) by
      rw [sub_nonneg, div_le_one hx0]; exact hx1)]
  rcases m with _ | _ | m
  · have hR := perron_residue_zero (x : ℝ) 2 hx1 two_pos (-((0 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.Zdtau_eq, ↓reduceIte]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hR := perron_residue_neg_one (x : ℝ) 2 hx1 two_pos (-((0 + 1 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.Zdtau_eq, ↓reduceIte, zero_add, one_ne_zero]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hM : (2 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by push_cast; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hw0 : -((m + 1 + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hw1 : -((m + 1 + 1 : ℕ) : ℂ) ≠ -1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hR := perron_residue (x : ℝ) 2 hx1 two_pos _ (hw_m (m + 1 + 1)) hw0 hw1
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    have h0 : m + 1 + 1 ≠ 0 := by omega
    have h1 : m + 1 + 1 ≠ 1 := by omega
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.Zdtau_eq, h0, h1, ↓reduceIte]
    rw [cpow_neg, cpow_natCast, cpow_neg_one]
    push_cast
    have e1 : (m : ℂ) + 1 + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e2 : (m : ℂ) + 1 + 1 - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e3 : (2 : ℂ) + ((m : ℂ) + 1 + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e4 : -((m : ℂ) + 1 + 1) + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e5 : 1 + -((m : ℂ) + 1 + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e6 : (x : ℂ) ^ (m + 1 + 1) ≠ 0 := pow_ne_zero _ hxC
    simp only [one_div, inv_pow]
    field_simp
    ring
lemma norm_gTerm_le (x m : ℕ) (t : ℝ) :
    ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m t‖ ≤ 1 / (2 + m) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have h0 : (2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h1 : (2 : ℂ) + t * I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (2 : ℂ) + t * I + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (2 : ℂ) + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have e : (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m t = (((2 : ℂ) + t * I - 2) / ((2 : ℂ) + t * I)) * (1 / (2 + (m : ℂ))) *
      ((x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))) := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.ZdgTerm_eq]
    rw [sub_neg_eq_add]
    field_simp
    ring
  rw [e, norm_mul, norm_mul]
  have hq : ‖((2 : ℂ) + t * I - 2) / ((2 : ℂ) + t * I)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr h0)]
    have : (2 : ℂ) + t * I - 2 = t * I := by ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := Complex.abs_im_le_norm ((2 : ℂ) + t * I)
    simpa using this
  have hn : ‖1 / (2 + (m : ℂ))‖ = 1 / (2 + m) := by
    rw [norm_div, norm_one]
    congr 1
    exact_mod_cast Complex.norm_natCast (2 + m)
  rw [hn]
  have := norm_nonneg ((x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1)))
  have : 0 ≤ 1 / (2 + (m : ℝ)) := by positivity
  calc _ ≤ 1 * (1 / (2 + (m : ℝ))) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := by gcongr
    _ = _ := by ring
lemma rpow_bound (k m : ℕ) (hkm : k ≤ m) :
    (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m) ≤ ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
  have e : ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) = ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) / ((k : ℝ) + 1) := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + (-1) by norm_num, Real.rpow_add hk, Real.rpow_neg_one]
    ring
  rw [e]
  apply div_le_div₀ (by positivity) _ hk (by linarith)
  exact Real.rpow_le_rpow_of_nonpos hk (by linarith) (by norm_num)
lemma summable_rpow32 : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
  simpa using this
end Erdos985.Analytic.BoundsAux
namespace Erdos985.Analytic
open BoundsAux
theorem norm_gammaPart_le' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    ‖((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) χ x‖ ≤ Real.log x + 1 := by
  obtain ⟨C, hC0, hC⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hsum : ∀ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) =
      ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x (2 * k + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.ZdgTerm_eq]
    exact (((hasSum_gammaLogDeriv χ hs).mul_right _).div_const _).tsum_eq.symm
  have hnorm : ∀ m : ℕ, ∫ t, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m t‖ ≤
      C * (x : ℝ) ^ (2 : ℝ) * ((1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m)) := by
    intro m
    obtain ⟨hQi, hQb⟩ := hC x 2 hx0 two_pos (-(m : ℂ)) (by
      simp only [neg_re, natCast_re]; norm_num; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    simp only [ofReal_natCast, ofReal_ofNat, norm_neg, Complex.norm_natCast] at hQi hQb
    calc ∫ t : ℝ, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m t‖ ≤ ∫ t : ℝ, 1 / (2 + (m : ℝ)) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ :=
          integral_mono (integrable_gTerm x hx m).norm (hQi.norm.const_mul _)
            (fun t => norm_gTerm_le x m t)
      _ = 1 / (2 + (m : ℝ)) * ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := integral_const_mul _ _
      _ ≤ 1 / (2 + (m : ℝ)) * (C * (x : ℝ) ^ (2 : ℝ) * (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x (2 * k + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hnorm _).trans ?_) (summable_rpow32.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    gcongr
    exact rpow_bound k _ (by omega)
  have hgp : ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) χ x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x (2 * k + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) t := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdgammaPart_eq]
    congr 1
    congr 1
    funext t
    exact hsum t
  rw [hgp, ← integral_tsum_of_summable_integral_norm (fun k => integrable_gTerm x hx _) hsumm,
    ← tsum_mul_left]
  simp_rw [integral_gTerm x hx]
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs]
  exact (tsum_tau_bound x hx1 (((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) (parity_le_one χ)).2
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
theorem norm_zeroTerm_le (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖(Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖ ≤ (√(x : ℝ) + 2 + 3 / x) / ‖ρ * (ρ + 1)‖ :=
  norm_zeroTerm_le' x hx hρ
theorem norm_gammaPart_le (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    ‖((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) χ x‖ ≤ Real.log x + 1 :=
  norm_gammaPart_le' χ x hx
theorem norm_logDeriv_LFunction_two_le (χ : DirichletCharacter ℂ N) :
    ‖deriv (DirichletCharacter.LFunction χ) 2 / DirichletCharacter.LFunction χ 2‖ ≤ 0.6 :=
  norm_logDeriv_LFunction_two_le' χ
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.ZeroSumAux
open Complex ArithmeticFunction
open scoped Classical
theorem log_pi_gt : (1.1364 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have h1 : Real.exp 1.1364 = Real.exp 1 * Real.exp 0.1364 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_bound' (x := 0.1364) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h2
  rw [h1]
  have h3 := Real.exp_one_lt_d9
  have h4 := Real.pi_gt_d4
  have h5 : 0 < Real.exp 0.1364 := Real.exp_pos _
  nlinarith
variable {N : ℕ} [NeZero N]
theorem norm_logDeriv_LFunction_three_halves_le (χ : DirichletCharacter ℂ N) :
    ‖deriv (DirichletCharacter.LFunction χ) (3 / 2) / DirichletCharacter.LFunction χ (3 / 2)‖
      ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hs : 1 < (3 / 2 : ℂ).re := by norm_num
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have h' : deriv (LSeries fun n => χ n) (3 / 2) / LSeries (fun n => χ n) (3 / 2)
      = -LSeries (fun n => χ n * (Λ n : ℂ)) (3 / 2) := by
    simp only [Pi.mul_def] at h; rw [h, neg_div, neg_neg]
  rw [h', norm_neg, LSeries]
  refine tsum_of_norm_bounded summable_vonMangoldt_rpow.hasSum fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.norm_term_eq]; simp only [hn, ↓reduceIte, norm_mul]
    have : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have hΛ : ‖(Λ n : ℂ)‖ = Λ n := by
      rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    rw [hΛ]
    norm_num
    gcongr
    calc ‖χ n‖ * Λ n ≤ 1 * Λ n := by gcongr
      _ = Λ n := one_mul _
theorem re_gammaLogDeriv_three_halves_le {N : ℕ} (χ : DirichletCharacter ℂ N) :
    (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (3 / 2)).re ≤ -(1 / 2) * Real.log Real.pi - 0.1135 := by
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdgammaLogDeriv_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.Zdparity_eq]
  split_ifs
  · have h : ((3 / 2 : ℂ) + ((0 : ℕ) : ℂ)) / 2 = 3 / 4 := by norm_num
    rw [h]
    have := digamma_three_quarters_re_le
    simp only [add_re, mul_re, neg_re, ofReal_re, neg_im, ofReal_im]
    norm_num
    linarith
  · have h : ((3 / 2 : ℂ) + ((1 : ℕ) : ℂ)) / 2 = 5 / 4 := by norm_num
    rw [h]
    have := digamma_five_quarters_re_le
    simp only [add_re, mul_re, neg_re, ofReal_re, neg_im, ofReal_im]
    norm_num
    linarith
theorem re_logDeriv_completed_three_halves_le [Fact H3] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    (deriv (DirichletCharacter.completedLFunction χ) (3 / 2)
        / DirichletCharacter.completedLFunction χ (3 / 2)).re
      ≤ 1.515 - (1 / 2) * Real.log Real.pi - 0.1135 := by
  have h := logDeriv_LFunction_eq hχ (s := 3 / 2) (by norm_num)
  rw [eq_sub_iff_add_eq] at h
  rw [← h, add_re]
  have h1 := (re_le_norm _).trans ((norm_logDeriv_LFunction_three_halves_le χ).trans
    tsum_vonMangoldt_rpow_le_sharp)
  have h2 := re_gammaLogDeriv_three_halves_le χ
  linarith
end Erdos985.Analytic.ZeroSumAux
end
section
namespace Erdos985.Analytic.ZeroSumAux
open Complex
variable {N : ℕ} [NeZero N]
theorem logDeriv_functional_equation {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) {s : ℂ} (hs : DirichletCharacter.completedLFunction χ⁻¹ s ≠ 0) :
    -(deriv (DirichletCharacter.completedLFunction χ) (1 - s)
        / DirichletCharacter.completedLFunction χ (1 - s))
      = (Real.log N : ℂ) + deriv (DirichletCharacter.completedLFunction χ⁻¹) s
          / DirichletCharacter.completedLFunction χ⁻¹ s := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hF : HasDerivAt (fun w => DirichletCharacter.completedLFunction χ (1 - w))
      (deriv (DirichletCharacter.completedLFunction χ) (1 - s) * (-1)) s :=
    (DirichletCharacter.differentiable_completedLFunction hχ (1 - s)).hasDerivAt.comp s
      ((hasDerivAt_id s).const_sub 1)
  have hP : HasDerivAt (fun w : ℂ => (N : ℂ) ^ (w - 1 / 2))
      ((N : ℂ) ^ (s - 1 / 2) * Complex.log N * 1) s :=
    ((hasDerivAt_id s).sub_const (1 / 2)).const_cpow (Or.inl hN)
  have hG := (hP.mul_const (DirichletCharacter.rootNumber χ)).mul
    (DirichletCharacter.differentiable_completedLFunction hχi s).hasDerivAt
  have hfun : (fun w => DirichletCharacter.completedLFunction χ (1 - w))
      = fun w => (N : ℂ) ^ (w - 1 / 2) * DirichletCharacter.rootNumber χ
          * DirichletCharacter.completedLFunction χ⁻¹ w :=
    funext hprim.completedLFunction_one_sub
  rw [hfun] at hF
  have hd := hF.unique hG
  have hval := hprim.completedLFunction_one_sub s
  have hlog : Complex.log N = (Real.log N : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg N)]; simp
  have hPne : (N : ℂ) ^ (s - 1 / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hN h.1
  have hε := port_rootNumber_ne_zero hprim
  rw [hval, ← hlog]
  have : deriv (DirichletCharacter.completedLFunction χ) (1 - s)
      = -((N : ℂ) ^ (s - 1 / 2) * Complex.log N * 1 * DirichletCharacter.rootNumber χ
          * DirichletCharacter.completedLFunction χ⁻¹ s
        + (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ
          * deriv (DirichletCharacter.completedLFunction χ⁻¹) s) := by
    linear_combination (-1 : ℂ) * hd
  rw [this]
  generalize (N : ℂ) ^ (s - 1 / 2) = P at *
  field_simp
theorem re_inv_reflect {ρ : ℂ} (hρ : ρ.re = 1 / 2) (x : ℝ) :
    (1 / ((1 : ℂ) - x - ρ)).re = -(1 / ((x : ℂ) - ρ)).re := by
  obtain ⟨a, b⟩ := ρ
  simp only at hρ
  subst hρ
  simp [normSq_apply]
  ring_nf
theorem inv_norm_mul_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / ‖ρ * (ρ + 1)‖ ≤ (4 / 3) * (1 / ((3 / 2 : ℂ) - ρ)).re := by
  obtain ⟨a, γ⟩ := ρ
  simp only at hρ
  subst hρ
  have hre : (1 / ((3 / 2 : ℂ) - ⟨1 / 2, γ⟩)).re = 1 / (1 + γ ^ 2) := by
    simp [normSq_apply]
    norm_num
    ring
  rw [hre]
  set t := ‖(⟨1 / 2, γ⟩ : ℂ) * (⟨1 / 2, γ⟩ + 1)‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hsq : t ^ 2 = (1 / 4 + γ ^ 2) * (9 / 4 + γ ^ 2) := by
    rw [ht, ← normSq_eq_norm_sq, normSq_mul]
    simp [normSq_apply]
    ring
  have hlow : (3 / 4) * (1 + γ ^ 2) ≤ t := by
    have h1 : ((3 / 4) * (1 + γ ^ 2)) ^ 2 ≤ t ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg γ]
    nlinarith [sq_nonneg γ]
  have hpos : 0 < (3 / 4) * (1 + γ ^ 2) := by positivity
  calc 1 / t ≤ 1 / ((3 / 4) * (1 + γ ^ 2)) := one_div_le_one_div_of_le hpos hlow
    _ = 4 / 3 * (1 / (1 + γ ^ 2)) := by field_simp
end Erdos985.Analytic.ZeroSumAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
theorem zeroSum_le [Fact H3] (hGRH : H1) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) ∧
    ∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖
      ≤ (2 / 3) * (Real.log N + 5 / 3) := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  obtain ⟨-, b, H⟩ := hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)
  set f := DirichletCharacter.completedLFunction χ with hf
  set fi := DirichletCharacter.completedLFunction χ⁻¹ with hfi
  set x : ℝ := 3 / 2 with hx
  have hs0 : f x ≠ 0 :=
    port_completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp [hx]; norm_num)
  have hsi : fi x ≠ 0 :=
    port_completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi)
      (by simp [hx]; norm_num)
  have hs1 : f (1 - x) ≠ 0 := fun h => hsi (completedLFunction_inv_eq_zero hprim h)
  obtain ⟨sA, eA⟩ := H x hs0
  obtain ⟨sB, eB⟩ := H (1 - x) hs1
  set m : {ρ : ℂ // f ρ = 0} → ℕ := fun ρ => analyticOrderNatAt f ρ with hm
  set r : {ρ : ℂ // f ρ = 0} → ℝ := fun ρ => (m ρ : ℝ) * (1 / ((x : ℂ) - ρ)).re with hr
  have hd := sA.hasSum.sub sB.hasSum
  have hdre := Complex.reCLM.hasSum hd
  have hcrit : ∀ ρ : {ρ : ℂ // f ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => completedLFunction_zero_re hGRH hprim hχ ρ.2
  have hterm : ∀ ρ : {ρ : ℂ // f ρ = 0},
      Complex.reCLM ((analyticOrderNatAt f ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
        - (analyticOrderNatAt f ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ)) = 2 * r ρ := by
    intro ρ
    have := ZeroSumAux.re_inv_reflect (hcrit ρ) x
    simp only [Complex.reCLM_apply, sub_re, mul_re, add_re, natCast_re, natCast_im, zero_mul,
      sub_zero, hr, hm]
    rw [this]; ring
  simp only [hterm] at hdre
  have hrsum : HasSum r ((Complex.reCLM (∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
      - ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ))) / 2) := by
    have := hdre.div_const 2
    simpa using this
  have hval : Complex.reCLM (∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
      - ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ))
      = (deriv f x / f x).re + Real.log N + (deriv fi x / fi x).re := by
    have hFE := ZeroSumAux.logDeriv_functional_equation hprim hχ (s := x) hsi
    have e : ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
      - ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ)
        = deriv f x / f x + (Real.log N + deriv fi x / fi x) := by
      rw [← hFE, eA, eB]; ring
    rw [e]
    simp only [Complex.reCLM_apply, add_re, ofReal_re]
    ring
  rw [hval] at hrsum
  have hB := ZeroSumAux.re_logDeriv_completed_three_halves_le hχ
  have hBi := ZeroSumAux.re_logDeriv_completed_three_halves_le hχi
  have hx' : ((x : ℝ) : ℂ) = 3 / 2 := by simp [hx]
  rw [hx'] at hrsum
  have hcmp : ∀ ρ : {ρ : ℂ // f ρ = 0},
      (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ ≤ (4 / 3) * r ρ := by
    intro ρ
    have h := ZeroSumAux.inv_norm_mul_le (hcrit ρ)
    simp only [hr, hm, hx']
    rw [div_eq_mul_one_div]
    have : (0 : ℝ) ≤ analyticOrderNatAt f ρ := Nat.cast_nonneg _
    nlinarith
  have hnn : ∀ ρ : {ρ : ℂ // f ρ = 0},
      0 ≤ (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hsum4 := hrsum.mul_left (4 / 3)
  have hS : Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
      (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
    Summable.of_nonneg_of_le hnn hcmp hsum4.summable
  refine ⟨hS, ?_⟩
  have hle := hS.tsum_le_tsum hcmp hsum4.summable
  rw [hsum4.tsum_eq] at hle
  have hpi := ZeroSumAux.log_pi_gt
  linarith
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
theorem bach_nonprincipal_of_GRH [Fact H3] (hGRH : H1) (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) :
    ‖((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) χ x‖ ≤ (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p x * √x * Real.log p := by
  have hp := (Fact.out : p.Prime)
  have hprim : χ.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def]
    rcases (Nat.dvd_prime hp).1 (DirichletCharacter.conductor_dvd_level χ) with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) hχ
    · exact h
  set Λc := DirichletCharacter.completedLFunction χ
  set m : {ρ : ℂ // Λc ρ = 0} → ℝ := fun ρ => (analyticOrderNatAt Λc ρ : ℝ)
  set A : ℝ := √(x : ℝ) + 2 + 3 / x
  obtain ⟨hsum, hZ⟩ := zeroSum_le hGRH hprim hχ
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ ρ : {ρ : ℂ // Λc ρ = 0},
      ‖(analyticOrderNatAt Λc ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖ ≤ A * (m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by
    intro ρ
    rw [norm_mul, Complex.norm_natCast]
    have h := norm_zeroTerm_le x hx (completedLFunction_zero_re hGRH hprim hχ ρ.2)
    calc (analyticOrderNatAt Λc ρ : ℝ) * ‖(Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖
        ≤ (analyticOrderNatAt Λc ρ : ℝ) * (A / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = A * (m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by simp only [m]; ring
  have hsumA : Summable fun ρ : {ρ : ℂ // Λc ρ = 0} =>
      A * (m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := hsum.mul_left A
  have hZnorm : ‖∑' ρ : {ρ : ℂ // Λc ρ = 0}, (analyticOrderNatAt Λc ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖
      ≤ A * ((2 / 3) * (Real.log p + 5 / 3)) := by
    have hs : Summable fun ρ : {ρ : ℂ // Λc ρ = 0} =>
        ‖(analyticOrderNatAt Λc ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumA
    calc _ ≤ ∑' ρ : {ρ : ℂ // Λc ρ = 0}, ‖(analyticOrderNatAt Λc ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖ :=
          norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ : {ρ : ℂ // Λc ρ = 0}, A * (m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
          hs.tsum_le_tsum hterm hsumA
      _ = A * ∑' ρ : {ρ : ℂ // Λc ρ = 0}, m ρ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := tsum_mul_left
      _ ≤ A * ((2 / 3) * (Real.log p + 5 / 3)) := mul_le_mul_of_nonneg_left hZ hA0
  have hG := norm_gammaPart_le χ x hx
  have hL := norm_logDeriv_LFunction_two_le χ
  have hfac : ‖(1 - 1 / (x : ℂ))‖ ≤ 1 := by
    have : (1 - 1 / (x : ℂ)) = ((1 - 1 / (x : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 : 0 < 1 / (x : ℝ) := by positivity
    have h2 : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hxR
    constructor <;> linarith
  have hlast : ‖(1 - 1 / (x : ℂ)) * (deriv (DirichletCharacter.LFunction χ) 2
      / DirichletCharacter.LFunction χ 2)‖ ≤ 0.6 := by
    rw [norm_mul]
    calc _ ≤ 1 * 0.6 := mul_le_mul hfac hL (norm_nonneg _) zero_le_one
      _ = 0.6 := one_mul _
  have htotal : ‖((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open ArithmeticFunction Real in ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)))) _) χ x‖ ≤ A * ((2 / 3) * (Real.log p + 5 / 3)) + (Real.log x + 1) + 0.6 := by
    rw [explicit_formula hprim hχ x hx]
    calc _ ≤ ‖(∑' ρ : {ρ : ℂ // Λc ρ = 0}, (analyticOrderNatAt Λc ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ)
              + ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) χ x‖ + ‖(1 - 1 / (x : ℂ)) * (deriv (DirichletCharacter.LFunction χ) 2
                / DirichletCharacter.LFunction χ 2)‖ := norm_sub_le _ _
      _ ≤ (‖∑' ρ : {ρ : ℂ // Λc ρ = 0}, (analyticOrderNatAt Λc ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖
              + ‖((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) χ x‖) + 0.6 := add_le_add (norm_add_le _ _) hlast
      _ ≤ _ := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hsx : 0 < √(x : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hx32 : (x : ℝ) ^ (3 / 2 : ℝ) = x * √(x : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hRHS : (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p x * √x * Real.log p
      = A * ((2 / 3) * (Real.log p + 5 / 3)) + (Real.log x + 2) := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.ZdbachC_eq, A]
    rw [hx32]
    have hx0 : (x : ℝ) ≠ 0 := by positivity
    have hs0 : √(x : ℝ) ≠ 0 := hsx.ne'
    have hl0 : Real.log p ≠ 0 := hlogp.ne'
    field_simp
  rw [hRHS]
  linarith
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.PrincipalAux
open Complex
theorem completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  intro h
  apply riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
theorem xiZeta_one : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) 1 = 1 := by simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdxiZeta_eq]
theorem xiZeta_zero_re_mem {ρ : ℂ} (hρ : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, xiZeta_zero] at hρ; exact one_ne_zero hρ
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, xiZeta_one] at hρ; exact one_ne_zero hρ
  have hΛ : completedRiemannZeta ρ = 0 := by
    rw [xiZeta_eq hρ0 hρ1] at hρ
    rcases mul_eq_zero.mp hρ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hρ0
      · exact absurd (sub_eq_zero.mp h) hρ1
    · exact h
  constructor
  · by_contra h
    push Not at h
    apply completedRiemannZeta_ne_zero_of_one_le_re (s := 1 - ρ) (by simp; linarith)
    rw [completedRiemannZeta_one_sub, hΛ]
  · by_contra h
    push Not at h
    exact completedRiemannZeta_ne_zero_of_one_le_re h hΛ
theorem xiZeta_order_ne_zero {ρ : ℂ} (hρ : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0) : analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ ≠ 0 := by
  have han : AnalyticOnNhd ℂ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) Set.univ :=
    differentiable_xiZeta.differentiableOn.analyticOnNhd isOpen_univ
  have h0 : analyticOrderAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) 0 ≠ ⊤ := by
    rw [(analyticOrderAt_eq_zero.2 (Or.inr (by rw [xiZeta_zero]; exact one_ne_zero)))]
    exact ENat.zero_ne_top
  have htop := han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 0) (Set.mem_univ ρ) h0
  intro hm
  have := Nat.cast_analyticOrderNatAt htop
  rw [hm, Nat.cast_zero, eq_comm, analyticOrderAt_eq_zero] at this
  rcases this with h | h
  · exact h (han ρ (Set.mem_univ _))
  · exact h hρ
theorem countable_xiZeta_zeros [Fact H3] : Countable {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0} := by
  have hs := (hadamard_logDeriv differentiable_xiZeta (by rw [xiZeta_zero]; exact one_ne_zero)
    xiZeta_growth).1 1 one_pos
  rw [← Set.countable_univ_iff]
  convert hs.countable_support
  symm
  rw [Function.support_eq_univ]
  intro ρ
  have hm := xiZeta_order_ne_zero ρ.2
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (xiZeta_zero_re_mem ρ.2).1.ne' (by simp [h])
  have : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 hρ0
  positivity
theorem gammaLogDeriv_one (s : ℂ) :
    ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) (1 : DirichletCharacter ℂ 1) s
      = -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2) := by
  simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdgammaLogDeriv_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.Zdparity_eq, port_even_one]
theorem logDeriv_riemannZeta_eq [Fact H3] {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s
      = deriv (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) s / (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) s - 1 / s - 1 / (s - 1)
          - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) (1 : DirichletCharacter ℂ 1) s := by
  have hs0 : 0 < s.re := by linarith
  have hne0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hne1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hne1' : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hγ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hev : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) =ᶠ[nhds s] fun w => w * (w - 1) * (Gammaℝ w * riemannZeta w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show s ∈ {w : ℂ | 1 < w.re} from hs)] with w hw
    have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith
    have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
    rw [xiZeta_eq hw0 hw1, riemannZeta_def_of_ne_zero hw0,
      mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (by linarith))]
  have hp : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have hd := hp.fun_mul ((StepAAux.hasDerivAt_Gammaℝ hs0).fun_mul
    (differentiableAt_riemannZeta hne1).hasDerivAt)
  rw [hev.deriv_eq, hd.deriv, hev.eq_of_nhds, gammaLogDeriv_one]
  field_simp
  ring
end Erdos985.Analytic.PrincipalAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory IdentityAux
theorem xiZeta_zero_re_mem {ρ : ℂ} (hρ : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 :=
  PrincipalAux.xiZeta_zero_re_mem hρ
theorem explicit_formula_zeta [Fact H3] (x : ℕ) (hx : 1 ≤ x) :
    (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0}, (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ)
        + ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) (1 : DirichletCharacter ℂ 1) x
        + ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
        - (1 - 1 / (x : ℂ)) * (deriv riemannZeta 2 / riemannZeta 2) := by
  classical
  set G := ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) (1 : DirichletCharacter ℂ 1) with hG
  set D : ℂ → ℂ := fun z => deriv (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) z / (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) z with hD
  set m : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℂ) with hm
  set c2 : ℂ := deriv riemannZeta 2 / riemannZeta 2 with hc2
  have := PrincipalAux.countable_xiZeta_zeros
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hΛd : Differentiable ℂ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) := differentiable_xiZeta
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) z ≠ 0 := fun z hz h => by
    linarith [(xiZeta_zero_re_mem h).2]
  obtain ⟨hsum_ε, b, hb⟩ := hadamard_logDeriv hΛd (by rw [xiZeta_zero]; exact one_ne_zero)
    xiZeta_growth
  have hzre : ∀ ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => xiZeta_zero_re_mem ρ.2
  let F : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (integrable_pairTerm hx0 (by linarith [hzre ρ])).const_mul _
  obtain ⟨C, hC0, hC⟩ := integral_norm_pairTerm_le
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    calc (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) * ∫ t, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t))) x ρ t‖
        ≤ (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) *
            (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC x hx0 ρ (hzre ρ).2 hρ0) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_hasSum : ∀ t : ℝ, HasSum (fun ρ => F ρ t) ((D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I) (hΛne _ (by rw [hsre]; norm_num))
    obtain ⟨h2s, h2e⟩ := hb 2 (hΛne _ (by norm_num))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t)
    convert this using 1 <;> try rfl
    · funext ρ
      simp only [F, m, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.ZdpairTerm_eq]
      ring
    · simp only [hD]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => D ((2 : ℂ) + t * I) := by
    have hcd : Continuous (deriv (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1)))) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs_cont).div (hΛd.continuous.comp hs_cont)
      (fun t => hΛne _ (by simp))
  have hF1_int : Integrable fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t :=
    integrable_of_hasSum
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (integrable_kern hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : ∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t
      = ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0}, m ρ * (-(2 * Real.pi) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ) := by
    rw [show (fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
    refine tsum_congr fun ρ => ?_
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    have hρ1 : (ρ : ℂ) ≠ -1 := fun h => by
      have := (hzre ρ).1; rw [h] at this; norm_num at this
    simp only [F]
    rw [integral_const_mul, integral_pairTerm x hx (by linarith [hzre ρ]) hρ0 hρ1]
  set a : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, a]
  have hP := PerronKernel.perron_weighted a 2 two_pos ha_sum x hx
  simp only [ofReal_ofNat] at hP
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(D z - 1 / z - 1 / (z - 1) - G z) := fun z hz => by
    have h1 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
    change LSeries a z = _ at h1
    rw [h1, neg_div, PrincipalAux.logDeriv_riemannZeta_eq hz]
  have hc2' : c2 = D 2 - 1 / 2 - 1 / (2 - 1) - G 2 :=
    PrincipalAux.logDeriv_riemannZeta_eq (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hH
  have hH_eq : ∀ t : ℝ, H t = LSeries a ((2 : ℂ) + t * I) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t := fun t => by
    simp only [hH, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.Zdkern_eq, ofReal_natCast]
    ring
  have hH_int : Integrable H := by
    have hab : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) := by
      refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le
        (LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ)) (by norm_num))) ?_
      have : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
      rw [this]
      exact EReal.coe_lt_coe_iff.2 (by norm_num)
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) :=
      (LSeries_differentiableOn a).continuousOn.comp_continuous hs_cont
        (fun t => by simp only [Set.mem_ofPred_eq, hsre]; exact_mod_cast hab)
    set B := ∑' n, ‖LSeries.term a 2 n‖
    have hbd : ∀ t : ℝ, ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ B := fun t => by
      have hs2 := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
      have heq : (fun n => ‖LSeries.term a ((2 : ℂ) + t * I) n‖)
          = fun n => ‖LSeries.term a 2 n‖ := by
        funext n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre]; simp
      calc ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a ((2 : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (by rw [heq]; exact hs2)
        _ = B := by rw [heq]
    have : H = fun t : ℝ => LSeries a ((2 : ℂ) + t * I) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t := funext hH_eq
    rw [this]
    refine Integrable.mono' ((integrable_kern hx0).norm.const_mul B)
      (hcont.aestronglyMeasurable.mul (integrable_kern hx0).1)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t) (norm_nonneg _)
  set P0 : ℝ → ℂ := fun t => ((x : ℝ) : ℂ) ^ ((2 : ℂ) + t * I) /
    (((2 : ℂ) + t * I - 0) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hP0
  have hP0_int : Integrable P0 := by
    have := perron_residue_integrable (x : ℝ) 2 hx0 two_pos 0 (by simp)
    simp only [ofReal_ofNat] at this
    exact this
  have hP0_integral : ∫ t, P0 t = 2 * Real.pi * ((Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ)) := by
    have h := perron_residue_zero (x : ℝ) 2 hx1 two_pos 0 rfl
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [hP0]
  have hR1_int : Integrable ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x 1) := integrable_resKern hx0 (by norm_num)
  have hR1_integral : ∫ t, (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x 1 t
      = 2 * Real.pi * ((x : ℂ) ^ (1 : ℂ) / (1 * (1 + 1)) - 1 / 1 + (x : ℂ) ^ (-1 : ℂ) / (1 + 1)) := by
    have h := perron_residue (x : ℝ) 2 hx1 two_pos 1 (by norm_num) one_ne_zero (by norm_num)
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.ZdresKern_eq]
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t : ℝ => H t + (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t - P0 t - (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x 1 t
          + (c2 + 3 / 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    have h0 := line_ne_zero' t
    have h1 := line_add_one_ne_zero' t
    have h2 := line_sub_ne_zero' (ρ := 1) (by norm_num) t
    rw [hH_eq, hLS _ hz, hc2']
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.Zdkern_eq, OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.IdentityAux.ZdresKern_eq, hP0, ofReal_natCast, sub_zero]
    field_simp
    ring
  have hgamma : ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) (1 : DirichletCharacter ℂ 1) x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t)
        - (∫ t, P0 t) - (∫ t, (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℝ → ℂ → ℝ → ℂ, ∀ (x : ℝ) (ρ : ℂ) (t : ℝ), f x ρ t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x 1 t) + (c2 + 3 / 2) * ∫ t, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℂ, ∀ (x t : ℝ), f x t = (open Complex MeasureTheory in (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x t) := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdgammaPart_eq]
    rw [← hG, hF2, integral_add _ ((integrable_kern hx0).const_mul _),
      integral_sub _ hR1_int, integral_sub _ hP0_int, integral_add hH_int hF1_int,
      integral_const_mul]
    · exact hH_int.add hF1_int
    · exact (hH_int.add hF1_int).sub hP0_int
    · exact ((hH_int.add hF1_int).sub hP0_int).sub hR1_int
  have hbach : (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = ∑ n ∈ Finset.Ioo 0 x, a n * (1 - (n : ℂ) / x) := by
    push_cast
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Ioo] at hn; rw [Finset.mem_range]; omega
    · have : n = 0 := by rw [Finset.mem_Ioo] at hn'; rw [Finset.mem_range] at hn; omega
      subst this
      simp [a]
  have hbach' : (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    rw [hbach, hP]
  have hK := integral_kern hx1
  have htsum : ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0}, m ρ * (-(2 * Real.pi) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ)
      = -(2 * Real.pi) * ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0}, m ρ * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => by ring
  rw [hgamma, hbach', hF1_integral, htsum, hK, hP0_integral, hR1_integral]
  simp only [ofReal_natCast, cpow_one, cpow_neg_one]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  field_simp
  ring
end Erdos985.Analytic
end
section
open Complex MeasureTheory Filter Topology ArithmeticFunction
namespace Erdos985.Analytic.PrincipalAux
open BoundsAux
theorem tsum_tau_even_bound (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * k)) ∧
      1 - 3 / (2 * x) ≤ ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * k) + Real.log x ∧
      ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * k) + Real.log x ≤ 1 := by
  have hup : ∀ k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1)) ≤
      (3 * (1 / x) - 1) / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := fun k =>
    tau_le_even x hx k
  have hlo : ∀ k : ℕ, -(1 / 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1)) :=
    fun k => tau_ge x hx k (2 * (k + 1)) le_rfl
  have hS : Summable (fun k : ℕ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * k)) := by
    simpa using (tsum_tau_bound x hx 0 (by norm_num)).1
  have hg : Summable (fun k : ℕ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1))) :=
    (summable_nat_add_iff (f := fun k : ℕ => (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * k)) 1).mpr hS
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq_zero_add]
  have hle : ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1)) ≤ (3 * (1 / x) - 1) / 2 := by
    have := Summable.tsum_le_tsum hup hg (hasSum_u.summable.mul_left _)
    rwa [tsum_mul_left, hasSum_u.tsum_eq, mul_one] at this
  have hge : -(1 / 2) ≤ ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * (k + 1)) := by
    have := Summable.tsum_le_tsum hlo (hasSum_u.summable.mul_left _) hg
    rwa [tsum_mul_left, hasSum_u.tsum_eq, mul_one] at this
  have h0 : (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * 0) = (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) := by simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.Zdtau_eq]
  rw [h0]
  have e : 3 / (2 * x) = 3 / 2 * (1 / x) := by field_simp
  rw [e]
  constructor <;> linarith
theorem gammaPart_eq_tsum_tau {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ)
    (hx : 1 ≤ x) :
    ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) χ x = ((∑' k : ℕ, (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℕ → ℝ, ∀ (x : ℝ) (m : ℕ), f x m = (open Filter Topology in if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x) else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))))) x (2 * k + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hsum : ∀ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) =
      ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x (2 * k + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.BoundsAux.ZdgTerm_eq]
    exact (((hasSum_gammaLogDeriv χ hs).mul_right _).div_const _).tsum_eq.symm
  have hnorm : ∀ m : ℕ, ∫ t, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m t‖ ≤
      C * (x : ℝ) ^ (2 : ℝ) * ((1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m)) := by
    intro m
    obtain ⟨hQi, hQb⟩ := hC x 2 hx0 two_pos (-(m : ℂ)) (by
      simp only [neg_re, natCast_re]; norm_num; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    simp only [ofReal_natCast, ofReal_ofNat, norm_neg, Complex.norm_natCast] at hQi hQb
    calc ∫ t : ℝ, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x m t‖ ≤ ∫ t : ℝ, 1 / (2 + (m : ℝ)) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ :=
          integral_mono (integrable_gTerm x hx m).norm (hQi.norm.const_mul _)
            (fun t => norm_gTerm_le x m t)
      _ = 1 / (2 + (m : ℝ)) * ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := integral_const_mul _ _
      _ ≤ 1 / (2 + (m : ℝ)) * (C * (x : ℝ) ^ (2 : ℝ) * (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖(Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x (2 * k + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hnorm _).trans ?_) (summable_rpow32.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    gcongr
    exact rpow_bound k _ (by omega)
  have hgp : ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) χ x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, ∑' k : ℕ, (Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : ℕ → ℕ → ℝ → ℂ, ∀ (x : ℕ) (m : ℕ) (t : ℝ), f x m t = (open Complex MeasureTheory Filter Topology in (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) x (2 * k + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) t := by
    simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdgammaPart_eq]
    congr 1
    congr 1
    funext t
    exact hsum t
  rw [hgp, ← integral_tsum_of_summable_integral_norm (fun k => integrable_gTerm x hx _) hsumm,
    ← tsum_mul_left]
  simp_rw [integral_gTerm x hx]
  rw [← Complex.ofReal_tsum]
lemma parity_one : ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) (1 : DirichletCharacter ℂ 1) = 0 := by
  simp [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.Zdparity_eq, port_even_one]
theorem gammaPart_one_bound' (x : ℕ) (hx : 1 ≤ x) :
    (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) (1 : DirichletCharacter ℂ 1) x).im = 0 ∧
    1 - 3 / (2 * (x : ℝ)) ≤ (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) (1 : DirichletCharacter ℂ 1) x).re + Real.log x ∧
    (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) (1 : DirichletCharacter ℂ 1) x).re + Real.log x ≤ 1 := by
  rw [gammaPart_eq_tsum_tau _ x hx, parity_one]
  simp only [add_zero, Complex.ofReal_im, Complex.ofReal_re, true_and]
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  exact (tsum_tau_even_bound x hx1).2
theorem logDeriv_zeta_two_bound' :
    (deriv riemannZeta 2 / riemannZeta 2).im = 0 ∧
    -0.6 ≤ (deriv riemannZeta 2 / riemannZeta 2).re ∧
      (deriv riemannZeta 2 / riemannZeta 2).re ≤ 0 := by
  have key := LSeries_vonMangoldt_eq_deriv_riemannZeta_div re2
  have e : deriv riemannZeta 2 / riemannZeta 2
      = -((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [← lseries_eq2 (fun n => (Λ n : ℝ)), key]; ring
  rw [e]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.neg_re, Complex.ofReal_re,
    true_and]
  have hS := S2_le
  have h0 : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  constructor <;> linarith
end Erdos985.Analytic.PrincipalAux
end
section
open Real Filter Topology
namespace Erdos985.Analytic.PrincipalAux
lemma log_one_add_inv_ge {a : ℝ} (ha : 0 < a) :
    2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 ≤ log (1 + a⁻¹) := by
  have h := hasSum_log_one_add_inv ha
  have hle := sum_le_hasSum (Finset.range 2) (fun k _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  norm_num at hle
  simpa [one_div, inv_pow] using hle
lemma step_ineq {a : ℝ} (ha : 0 < a) :
    1 / (2 * a) + 1 / (2 * (a + 1)) + 1 / (8 * (a + 1) ^ 2) - 1 / (8 * a ^ 2)
      ≤ log (1 + a⁻¹) := by
  refine le_trans ?_ (log_one_add_inv_ge ha)
  rw [← sub_nonneg]
  have e : 2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 -
      (1 / (2 * a) + 1 / (2 * (a + 1)) + 1 / (8 * (a + 1) ^ 2) - 1 / (8 * a ^ 2))
      = (4 * a ^ 2 + 2 * a + 1) * (4 * a ^ 2 + 6 * a + 3) /
        (24 * a ^ 2 * (a + 1) ^ 2 * (2 * a + 1) ^ 3) := by
    field_simp
    ring
  rw [e]
  positivity
theorem ZdemSeqU_def (m : ℕ) :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ) + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2))) m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ) + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2) :=
  Classical.choose_spec (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ) + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2)) m
theorem ZdemSeqU_eq :
    (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ) + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2))) = fun (m : ℕ) => (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ) + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2) := by
  funext m
  exact ZdemSeqU_def m
lemma emSeqU_anti : Antitone (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ) + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2))) := by
  refine antitone_nat_of_succ_le (fun m => ?_)
  have ha : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have key := step_ineq ha
  have hlog : log (((m + 1 + 1 : ℕ) : ℝ)) =
      log ((m + 1 : ℕ) : ℝ) + log (1 + ((m + 1 : ℕ) : ℝ)⁻¹) := by
    rw [← log_mul ha.ne' (by positivity)]
    congr 1
    field_simp
    push_cast
    ring
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PrincipalAux.ZdemSeqU_eq]
  rw [hlog, harmonic_succ (m + 1)]
  push_cast at key ⊢
  have : (1 : ℝ) / (2 * (m + 1)) + 1 / (2 * (m + 1 + 1)) + 1 / (8 * (m + 1 + 1) ^ 2)
      - 1 / (8 * (m + 1) ^ 2) =
      ((m : ℝ) + 1 + 1)⁻¹ + 1 / 2 / (m + 1) - 1 / 2 / (m + 1 + 1)
        + 1 / 8 / (m + 1 + 1) ^ 2 - 1 / 8 / (m + 1) ^ 2 := by
    field_simp; ring
  linarith
lemma tendsto_emSeqU : Tendsto (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ) + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2))) atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ => (harmonic n : ℝ) - log n - (1 / 2) / n + (1 / 8) / (n : ℝ) ^ 2)
      atTop (𝓝 (eulerMascheroniConstant - 0 + 0)) := by
    refine (tendsto_harmonic_sub_log.sub (tendsto_const_div_atTop_nhds_zero_nat _)).add ?_
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 / 8 : ℝ)).comp
      (tendsto_pow_atTop (α := ℕ) (n := 2) (by norm_num))
    refine this.congr (fun n => ?_)
    simp
  rw [sub_zero, add_zero] at h1
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PrincipalAux.ZdemSeqU_eq]
  exact (tendsto_add_atTop_iff_nat 1).mpr h1
lemma le_emSeqU (m : ℕ) : eulerMascheroniConstant ≤ (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℕ → ℝ, ∀ (m : ℕ), f m = (open Real Filter Topology in (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ) + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2))) m :=
  emSeqU_anti.le_of_tendsto tendsto_emSeqU m
lemma eulerMascheroniConstant_lt' : eulerMascheroniConstant < 0.5774 := by
  refine lt_of_le_of_lt (le_emSeqU 15) ?_
  have hH : (harmonic 16 : ℝ) = 2436559 / 720720 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : log ((16 : ℕ) : ℝ) = 4 * log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.PrincipalAux.ZdemSeqU_eq]
  norm_num only [Nat.reduceAdd] at hH hl ⊢
  rw [hH, hl]
  linarith [log_two_gt_d9]
lemma log_pi_gt' : (1.144 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have h1 : Real.exp 1.144 = Real.exp 1 * Real.exp 0.144 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_bound' (x := 0.144) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h2
  rw [h1]
  have h3 := Real.exp_one_lt_d9
  have h4 := Real.pi_gt_d4
  have h5 : 0 < Real.exp 0.144 := Real.exp_pos _
  nlinarith
lemma two_add_gamma_sub_log_lt : 2 + eulerMascheroniConstant - Real.log (4 * Real.pi) < 1 / 20 := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have := eulerMascheroniConstant_lt'
  have := log_pi_gt'
  have := log_two_gt_d9
  push_cast
  linarith
end Erdos985.Analytic.PrincipalAux
end
section
open Complex
namespace Erdos985.Analytic.PrincipalAux
theorem xiZeta_one_sub (s : ℂ) : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) (1 - s) = (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) s := by
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdxiZeta_eq, completedRiemannZeta₀_one_sub]
  ring
theorem hasDerivAt_xiZeta (s : ℂ) :
    HasDerivAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ((1 * (s - 1) + s * 1) * completedRiemannZeta₀ s
      + s * (s - 1) * deriv completedRiemannZeta₀ s) s := by
  have h := (((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).mul
    (differentiable_completedZeta₀ s).hasDerivAt).add_const 1
  simp only [OMA.R_Erdos985_erdos_985_R1.Erdos985.Analytic.ZdxiZeta_eq]
  exact h
theorem deriv_xiZeta_zero : deriv (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) 0 = -completedRiemannZeta₀ 0 := by
  rw [(hasDerivAt_xiZeta 0).deriv]; ring
theorem deriv_xiZeta_one : deriv (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) 1 = completedRiemannZeta₀ 1 := by
  rw [(hasDerivAt_xiZeta 1).deriv]; ring
theorem xiZeta_ne_zero_of_half_lt (hGRH : H1) {s : ℂ}
    (hs : 1 / 2 < s.re) : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; rw [xiZeta_one] at h; norm_num at h
  rw [xiZeta_eq hs0 hs1] at h
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hs0
      · exact absurd h hs1'
    · exact h
  have hζ : riemannZeta s = 0 := by rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  have := hGRH 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
  rw [DirichletCharacter.LFunction_modOne_eq] at this
  exact this hζ
theorem xiZeta_zero_re' (hGRH : H1) {ρ : ℂ} (hρ : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0) :
    ρ.re = 1 / 2 := by
  have h1 : ¬ 1 / 2 < ρ.re := fun h => xiZeta_ne_zero_of_half_lt hGRH h hρ
  have h2 : ¬ 1 / 2 < (1 - ρ).re := fun h =>
    xiZeta_ne_zero_of_half_lt hGRH h (by rw [xiZeta_one_sub]; exact hρ)
  simp only [sub_re, one_re] at h2
  linarith
theorem inv_norm_mul_le_re {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / ‖ρ * (ρ + 1)‖ ≤ (1 / (1 - ρ) + 1 / ρ).re := by
  obtain ⟨a, γ⟩ := ρ
  simp only at hρ
  subst hρ
  have hre : (1 / (1 - (⟨1 / 2, γ⟩ : ℂ)) + 1 / ⟨1 / 2, γ⟩).re = 1 / (1 / 4 + γ ^ 2) := by
    simp [normSq_apply]
    field_simp
    ring
  rw [hre]
  set t := ‖(⟨1 / 2, γ⟩ : ℂ) * (⟨1 / 2, γ⟩ + 1)‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hsq : t ^ 2 = (1 / 4 + γ ^ 2) * (9 / 4 + γ ^ 2) := by
    rw [ht, ← normSq_eq_norm_sq, normSq_mul]
    simp [normSq_apply]
    ring
  have hpos : 0 < 1 / 4 + γ ^ 2 := by positivity
  have hlow : 1 / 4 + γ ^ 2 ≤ t := by
    have h1 : (1 / 4 + γ ^ 2) ^ 2 ≤ t ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg γ]
    nlinarith [sq_nonneg γ]
  exact one_div_le_one_div_of_le hpos hlow
theorem re_two_completedRiemannZeta₀_one :
    (2 * completedRiemannZeta₀ 1).re = 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  rw [completedRiemannZeta₀_one]
  have e : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [e]
  simp
  ring
theorem zeroSum_zeta_le' [Fact H3] (hGRH : H1) :
    Summable (fun ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0} =>
        (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) ∧
    ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0}, (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖
      ≤ 1 / 20 := by
  have hx0 : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) 0 ≠ 0 := by rw [xiZeta_zero]; norm_num
  have hx1 : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) 1 ≠ 0 := by rw [xiZeta_one]; norm_num
  obtain ⟨-, b, H⟩ := hadamard_logDeriv differentiable_xiZeta hx0 xiZeta_growth
  obtain ⟨-, e0⟩ := H 0 hx0
  obtain ⟨s1, e1⟩ := H 1 hx1
  have hz : ∀ ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0},
      (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℂ) * (1 / (0 - (ρ : ℂ)) + 1 / ρ) = 0 := by
    intro ρ; simp
  simp only [hz, tsum_zero, add_zero, deriv_xiZeta_zero, xiZeta_zero, div_one] at e0
  rw [deriv_xiZeta_one, xiZeta_one, div_one] at e1
  set T := ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0},
    (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / ρ) with hT
  have hTv : T = 2 * completedRiemannZeta₀ 1 := by
    have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
      rw [← completedRiemannZeta₀_one_sub]; norm_num
    rw [h01] at e0
    linear_combination e0 - e1
  have hre := Complex.reCLM.hasSum s1.hasSum
  rw [← hT, hTv] at hre
  simp only [Complex.reCLM_apply, re_two_completedRiemannZeta₀_one] at hre
  have hcmp : ∀ ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0},
      (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ ≤
        ((analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / ρ)).re := by
    intro ρ
    have h := inv_norm_mul_le_re (xiZeta_zero_re' hGRH ρ.2)
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  have hnn : ∀ ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0},
      0 ≤ (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hS := Summable.of_nonneg_of_le hnn hcmp hre.summable
  refine ⟨hS, ?_⟩
  have hle := hS.tsum_le_tsum hcmp hre.summable
  rw [hre.tsum_eq] at hle
  linarith [two_add_gamma_sub_log_lt]
end Erdos985.Analytic.PrincipalAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction
theorem xiZeta_zero_re (hGRH : H1) {ρ : ℂ} (hρ : (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0) :
    ρ.re = 1 / 2 := by
  exact PrincipalAux.xiZeta_zero_re' hGRH hρ
theorem zeroSum_zeta_le [Fact H3] (hGRH : H1) :
    Summable (fun ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0} =>
        (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) ∧
    ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0}, (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖
      ≤ 1 / 20 := by
  exact PrincipalAux.zeroSum_zeta_le' hGRH
theorem gammaPart_one_bound (x : ℕ) (hx : 1 ≤ x) :
    (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) (1 : DirichletCharacter ℂ 1) x).im = 0 ∧
    1 - 3 / (2 * (x : ℝ)) ≤ (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) (1 : DirichletCharacter ℂ 1) x).re + Real.log x ∧
    (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) (1 : DirichletCharacter ℂ 1) x).re + Real.log x ≤ 1 := by
  exact PrincipalAux.gammaPart_one_bound' x hx
theorem logDeriv_zeta_two_bound :
    (deriv riemannZeta 2 / riemannZeta 2).im = 0 ∧
    -0.6 ≤ (deriv riemannZeta 2 / riemannZeta 2).re ∧ (deriv riemannZeta 2 / riemannZeta 2).re ≤ 0 := by
  exact PrincipalAux.logDeriv_zeta_two_bound'
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction
theorem bach_principal_of_GRH [Fact H3] (hGRH : H1) (x : ℕ) (hx : 1 ≤ x) :
    |∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) - x / 2| ≤ √x / 20 + 3 := by
  set S : ℝ := ∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x)
  set Z : ℂ := ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0}, (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ
  set Γp := ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (x : ℕ), f N χ x = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ (2 + t * I) - ((Classical.choose (⟨_, fun _ _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℂ → ℂ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ), f N χ s = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : (N : ℕ) → DirichletCharacter ℂ N → ℕ, ∀ (N : ℕ) (χ : DirichletCharacter ℂ N), f N χ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in if χ.Even then 0 else 1))) _) χ) / 2)))) _) χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))))) _) (1 : DirichletCharacter ℂ 1) x
  set L2 := deriv riemannZeta 2 / riemannZeta 2
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hid := explicit_formula_zeta x hx
  have hre : S = Z.re + Γp.re + ((x : ℝ) / 2 + Real.log x - 7 / 2 + 3 / x)
      - (1 - 1 / (x : ℝ)) * L2.re := by
    have := congrArg Complex.re hid
    simp only [Complex.ofReal_re] at this
    refine this.trans ?_
    have hL2 : L2.im = 0 := (logDeriv_zeta_two_bound).1
    have e1 : (1 - 1 / (x : ℂ)) = ((1 - 1 / (x : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
        = (((x : ℝ) / 2 + Real.log x - 7 / 2 + 3 / x : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Complex.sub_re, Complex.add_re, Complex.add_re, Complex.ofReal_re,
      Complex.re_ofReal_mul]
  obtain ⟨hsum, hZ⟩ := zeroSum_zeta_le hGRH
  set A : ℝ := √(x : ℝ) + 2 + 3 / x
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0},
      ‖(analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖
        ≤ A * ((analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by
    intro ρ
    rw [norm_mul, Complex.norm_natCast]
    have h := norm_zeroTerm_le x hx (xiZeta_zero_re hGRH ρ.2)
    calc (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) * ‖(Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖
        ≤ (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) * (A / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  have hsumA := hsum.mul_left A
  have hs : Summable fun ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0} =>
      ‖(analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumA
  have hZn : ‖Z‖ ≤ A * (1 / 20) := by
    calc ‖Z‖ ≤ ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0}, ‖(analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℂ) * (Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℕ → ℂ → ℂ, ∀ (x : ℕ) (ρ : ℂ), f x ρ = (open Complex ArithmeticFunction MeasureTheory in open scoped Classical in (1 - 1 / (x : ℂ)) / (2 - ρ) - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))))) x ρ‖ :=
          norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0},
            A * ((analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
          hs.tsum_le_tsum hterm hsumA
      _ = A * ∑' ρ : {ρ : ℂ // (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ = 0},
            (analyticOrderNatAt (Classical.choose (⟨_, fun _ => rfl⟩ : ∃ f : ℂ → ℂ, ∀ (s : ℂ), f s = (open Complex in s * (s - 1) * completedRiemannZeta₀ s + 1))) ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := tsum_mul_left
      _ ≤ A * (1 / 20) := mul_le_mul_of_nonneg_left hZ hA0
  have hZre : |Z.re| ≤ A * (1 / 20) := (Complex.abs_re_le_norm Z).trans hZn
  obtain ⟨-, hg1, hg2⟩ := gammaPart_one_bound x hx
  obtain ⟨-, hl1, hl2⟩ := logDeriv_zeta_two_bound
  have hf0 : 0 ≤ 1 - 1 / (x : ℝ) := by
    have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one hx0]; exact hxR
    linarith
  have hf1 : 1 - 1 / (x : ℝ) ≤ 1 := by
    have : 0 < 1 / (x : ℝ) := by positivity
    linarith
  have h3x : 3 / (x : ℝ) ≤ 3 := by rw [div_le_iff₀ hx0]; linarith
  have h3x0 : 0 ≤ 3 / (x : ℝ) := by positivity
  have hfl1 : (1 - 1 / (x : ℝ)) * L2.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf0 hl2
  have hfl2 : -0.6 ≤ (1 - 1 / (x : ℝ)) * L2.re := by nlinarith
  have hT1 : -(5 / 2) ≤ Γp.re + Real.log x - 7 / 2 + 3 / x - (1 - 1 / (x : ℝ)) * L2.re := by
    have : 3 / (2 * (x : ℝ)) ≤ 3 / x := by
      rw [div_le_div_iff₀ (by positivity) hx0]; nlinarith
    linarith
  have hT2 : Γp.re + Real.log x - 7 / 2 + 3 / x - (1 - 1 / (x : ℝ)) * L2.re ≤ 5 / 2 := by
    linarith
  have hkey : S - x / 2 = Z.re + (Γp.re + Real.log x - 7 / 2 + 3 / x
      - (1 - 1 / (x : ℝ)) * L2.re) := by rw [hre]; ring
  rw [hkey]
  have hA : A * (1 / 20) ≤ √x / 20 + 1 / 4 := by simp only [A]; linarith
  calc |Z.re + _| ≤ |Z.re| + |Γp.re + Real.log x - 7 / 2 + 3 / x - (1 - 1 / (x : ℝ)) * L2.re| :=
        abs_add_le _ _
    _ ≤ (√x / 20 + 1 / 4) + 5 / 2 := add_le_add (hZre.trans hA) (abs_le.2 ⟨hT1, hT2⟩)
    _ ≤ √x / 20 + 3 := by linarith
end Erdos985.Analytic
end
section
namespace Erdos985
open ArithmeticFunction Real
theorem erdos_985_of_GRH [Fact H3] (hGRH : H1)
    (hsmall : H2) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  intro p hp hp2
  by_cases hlt : p < 10 ^ 8
  · exact hsmall p hp hp2 hlt
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  have hno : ∀ q, q.Prime → q < p → orderOf (q : ZMod p) ≠ p - 1 :=
    fun q hq hqp => hcon q hq hqp
  have hp1 : 1 ≤ p := hp.one_lt.le
  have key := principal_le_of_no_prime_primitive_root p hp2 p le_rfl
    ((Classical.choose (⟨_, fun _ _ => rfl⟩ : ∃ f : ℝ → ℝ → ℝ, ∀ (p x : ℝ), f p x = (open ArithmeticFunction Real in (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p) + (Real.log x + 2) / (√x * Real.log p)))) p p * √p * Real.log p) (fun χ hχ => Analytic.bach_nonprincipal_of_GRH hGRH p χ hχ p hp1) hno
  have hprin := Analytic.bach_principal_of_GRH hGRH p hp1
  have hbig := bach_inequality_large p hp (not_lt.mp hlt)
  have := (abs_le.mp hprin).1
  linarith
end Erdos985
end
end Toolkit

/-- Erdős Problem 985 from GRH, the finite check below `10^8`, and Hadamard factorisation. -/
theorem main : H1 → H2 → H3 → type_of% @Erdos985.erdos_985 := by
  intro h1 h2 h3
  haveI : Fact H3 := ⟨h3⟩
  exact Erdos985.erdos_985_of_GRH h1 h2
end OMA.R_Erdos985_erdos_985_R1
