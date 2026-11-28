import OMAStatements.S_mse_5112273

/-!
# Disproof of MSE 5112273 (Rational ratio of sines at distinct rational multiples of pi)

No distinct rationals `p, q ∈ (0, 1/2)` have rational `sin (p * π) / sin (q * π)`.
Embedding `ζ₁ = exp (2πi p)` and `ζ₂ = exp (2πi q)` in `ℚ(exp (2πi / (p.den * q.den))) ⊆ ℂ`
and taking `Algebra.norm ℚ` of `(ζ₁ - 1)(ζ₁⁻¹ - 1) = r² (ζ₂ - 1)(ζ₂⁻¹ - 1)` relates `r` to
`Φ_{p.den}(1)` and `Φ_{q.den}(1)`. Comparing prime factorizations forces `r = 1`, hence `p = q`.
-/

open Polynomial IntermediateField Algebra Nat
open Real (pi pi_pos)
open Complex (exp cos I)
open IsPrimitiveRoot (coe_submonoidClass_iff)
open scoped IntermediateField

private noncomputable def e (x : ℂ) : ℂ := exp (2 * pi * I * x)

private noncomputable def phi1 (d : ℕ) : ℤ := eval 1 (cyclotomic d ℤ)

private lemma fac_le (d : ℕ) (hd : 2 < d) (ℓ : ℕ) : (phi1 d).natAbs.factorization ℓ ≤ 1 := by
  by_cases h : ∃ p k : ℕ, p.Prime ∧ p ^ k = d
  · rcases h with ⟨p, k, hp, rfl⟩
    rcases exists_eq_succ_of_ne_zero (by rintro rfl; simp at hd : k ≠ 0) with ⟨m, rfl⟩
    have : Fact p.Prime := ⟨hp⟩
    rw [phi1, eval_one_cyclotomic_prime_pow m, Int.natAbs_natCast, hp.factorization]
    by_cases hℓ : ℓ = p <;> simp [hℓ]
  · rw [phi1, eval_one_cyclotomic_not_prime_pow fun hp k h' => h ⟨_, k, hp, h'⟩, Int.natAbs_one,
      factorization_one]; simp

private lemma npow (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {ζ : L} {d : ℕ} (hζ : IsPrimitiveRoot ζ d) (hd : 2 < d)
    (hi : Irreducible (cyclotomic d K)) :
    (norm K ((ζ - 1) * (ζ⁻¹ - 1))) ^ d.totient = (phi1 d : K) ^ (2 * Module.finrank K L) := by
  have : NeZero d := ⟨by omega⟩
  have one : ∀ {ξ : L}, IsPrimitiveRoot ξ d →
      (norm K (ξ - 1)) ^ d.totient = (phi1 d : K) ^ Module.finrank K L := fun {ξ} hξ => by
    set η := ξ - 1
    have heq : (K⟮η⟯ : IntermediateField K L) = K⟮ξ⟯ := by
      refine le_antisymm ?_ ?_ <;> rw [adjoin_simple_le_iff]
      · exact sub_mem (mem_adjoin_simple_self K ξ) (one_mem _)
      · have h : ξ = η + 1 := (sub_add_cancel ξ 1).symm
        rw [h]; exact add_mem (mem_adjoin_simple_self K η) (one_mem _)
    have : IsCyclotomicExtension {d} K K⟮η⟯ := by
      rw [heq]
      exact IsCyclotomicExtension.equiv _ _ _
        (h := adjoin_simple_toSubalgebra_of_isAlgebraic
          (IsIntegral.isIntegral (R := K) ξ).isAlgebraic ▸
          hξ.adjoin_isCyclotomicExtension K) (.refl : K⟮ξ⟯.toSubalgebra ≃ₐ[K] _)
    have hz : IsPrimitiveRoot (AdjoinSimple.gen K η + 1) d :=
      coe_submonoidClass_iff.mp (by simpa [η] using hξ)
    rw [norm_eq_norm_adjoin K η,
      show norm K (AdjoinSimple.gen K η) = (phi1 d : K) by
        simpa [add_sub_cancel_right, phi1] using hz.sub_one_norm_eq_eval_cyclotomic hd hi,
      ← pow_mul, mul_comm, ← IsCyclotomicExtension.finrank K⟮η⟯ hi, Module.finrank_mul_finrank]
  rw [map_mul, mul_pow, one hζ, one hζ.inv, ← pow_add, ← two_mul]

private lemma e_sq (x : ℝ) :
    (e x - 1) * ((e x)⁻¹ - 1) = (((2 * Real.sin (x * pi)) ^ 2 : ℝ) : ℂ) := by
  simp only [e, ← Complex.exp_neg]
  have h1 : exp (2 * pi * I * x) + exp (-(2 * pi * I * x)) = 2 * cos (2 * (x * pi)) := by
    rw [cos, show 2 * ((x : ℂ) * pi) * I = 2 * pi * I * x by ring]; ring
  have h2 : exp (2 * pi * I * x) * exp (-(2 * pi * I * x)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  push_cast
  linear_combination h2 - h1 - 2 * Complex.cos_two_mul' ((x : ℂ) * pi) -
    2 * Complex.cos_sq' ((x : ℂ) * pi)

private lemma den_gt_two {q : ℚ} (h0 : (0 : ℝ) < q) (h1 : (q : ℝ) < 1 / 2) : 2 < q.den := by
  have hn := Rat.num_pos.mpr (by exact_mod_cast h0 : (0 : ℚ) < q)
  have hq : (q.num : ℝ) / q.den < 1 / 2 := by simpa [Rat.cast_def] using h1
  have : 2 * q.num < (q.den : ℤ) := by
    exact_mod_cast (by linarith [(div_lt_div_iff₀ (cast_pos.mpr q.den_pos : (0 : ℝ) < q.den)
      (by norm_num : (0 : ℝ) < 2)).mp hq] : (2 : ℝ) * q.num < q.den)
  omega

private lemma e_mem {q : ℚ} (hq : 0 < q) {m : ℕ} (hm : 0 < m) :
    e q ∈ ℚ⟮e (1 / ((q.den * m : ℕ) : ℂ))⟯ := by
  have hp : e (1 / ((q.den * m : ℕ) : ℂ)) ^ (q.num.natAbs * m) = e q := by
    simp only [e, ← Complex.exp_nat_mul]; congr 1
    have hn : (q.num.natAbs : ℂ) = q.num := by
      simpa only [Int.cast_natCast] using congrArg (Int.cast : ℤ → ℂ)
        (Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le)
    rw [show (q : ℂ) = (q.num.natAbs : ℂ) / q.den by rw [hn, ← Rat.cast_def]]
    push_cast; field_simp [cast_ne_zero.mpr q.den_nz, cast_ne_zero.mpr hm.ne']
  rw [← hp]; exact pow_mem (mem_adjoin_simple_self ℚ _) _

private lemma eq_one {r : ℚ} (hr : 0 < r) {d1 d2 M : ℕ} (hd1 : 2 < d1) (hd2 : 2 < d2) (hM : 0 < M)
    (he : (phi1 d1 : ℚ) ^ (M * d2.totient) =
      r ^ (M * (d1.totient * d2.totient)) * (phi1 d2 : ℚ) ^ (M * d1.totient)) : r = 1 := by
  set a := d1.totient; set b := d2.totient
  have ht : ∀ d, 2 < d → 2 ≤ d.totient := fun d h => by
    rcases totient_even h with ⟨k, hk⟩; have := totient_pos.mpr (by omega : 0 < d); omega
  have ha := ht d1 hd1; have hb := ht d2 hd2
  set c1 := (phi1 d1).natAbs; set c2 := (phi1 d2).natAbs
  have hp : ∀ d, 2 < d → 0 < phi1 d := fun d h => cyclotomic_pos h (1 : ℤ)
  have hc : ∀ d, 2 < d → (phi1 d : ℚ) = ((phi1 d).natAbs : ℚ) := fun d h => by
    simpa only [Int.cast_natCast] using congrArg (Int.cast : ℤ → ℚ)
      (Int.natAbs_of_nonneg (hp d h).le).symm
  have hc10 : c1 ≠ 0 := by have := hp d1 hd1; omega
  have hc20 : c2 ≠ 0 := by have := hp d2 hd2; omega
  set u := r.num.natAbs; set v := r.den
  have hnp := Rat.num_pos.mpr hr; have hu0 : u ≠ 0 := by omega
  have hv0 : v ≠ 0 := r.den_nz
  have hrq : r = (u : ℚ) / v := by
    rw [show (u : ℚ) = r.num by
      simpa only [Int.cast_natCast] using congrArg (Int.cast : ℤ → ℚ) (Int.natAbs_of_nonneg hnp.le),
      Rat.num_div_den]
  rw [hc d1 hd1, hc d2 hd2, hrq, div_pow, div_mul_eq_mul_div,
    eq_div_iff (pow_ne_zero _ (cast_ne_zero.mpr hv0))] at he
  have hnat : c1 ^ (M * b) * v ^ (M * (a * b)) = u ^ (M * (a * b)) * c2 ^ (M * a) := by
    exact_mod_cast he
  have hvu : v = u := eq_of_factorization_eq hv0 hu0 fun ℓ => by
    have hℓ := congrArg (fun n => n.factorization ℓ) hnat
    simp only [Nat.factorization_mul (pow_ne_zero _ hc10) (pow_ne_zero _ hv0),
      Nat.factorization_mul (pow_ne_zero _ hu0) (pow_ne_zero _ hc20),
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hℓ
    have hf : a * b * v.factorization ℓ + b * c1.factorization ℓ =
        a * b * u.factorization ℓ + a * c2.factorization ℓ := mul_left_cancel₀ hM.ne' (by linarith)
    have q := congrArg (· / (a * b)) hf
    rwa [mul_add_div (by positivity), mul_add_div (by positivity),
      div_eq_of_lt (by nlinarith [fac_le d1 hd1 ℓ]),
      div_eq_of_lt (by nlinarith [fac_le d2 hd2 ℓ]), add_zero, add_zero] at q
  rw [hrq, hvu, div_self (cast_ne_zero.mpr hu0)]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_5112273.main) := by
  rintro ⟨p, q, hp0, hp12, hq0, hq12, hpq, r, hr⟩
  have hsin : ∀ x : ℚ, (0 : ℝ) < x → (x : ℝ) < 1 / 2 → 0 < Real.sin (x * pi) := fun x h0 h1 =>
    Real.sin_pos_of_pos_of_lt_pi (mul_pos h0 pi_pos) (by nlinarith [pi_pos])
  have hsq := hsin q hq0 hq12
  have hr0 : (0 : ℚ) < r := by
    exact_mod_cast (show (0 : ℝ) < r by rw [← hr]; exact div_pos (hsin p hp0 hp12) hsq)
  have hdp := den_gt_two hp0 hp12; have hdq := den_gt_two hq0 hq12
  set N := p.den * q.den; have hN : 0 < N := by positivity
  set ω : ℂ := e (1 / N)
  have hω : IsPrimitiveRoot ω N := by
    simpa [ω, e, div_eq_mul_inv] using Complex.isPrimitiveRoot_exp N hN.ne'
  set L : IntermediateField ℚ ℂ := ℚ⟮ω⟯
  have : FiniteDimensional ℚ L := adjoin.finiteDimensional
    ⟨X ^ N - 1, monic_X_pow_sub_C 1 hN.ne', by simp [hω.pow_eq_one]⟩
  have hmp : e p ∈ L := e_mem (by exact_mod_cast hp0) (by omega)
  have hmq : e q ∈ L := by
    rw [show L = ℚ⟮e (1 / ((q.den * p.den : ℕ) : ℂ))⟯ by simp only [L, ω, N, mul_comm p.den]]
    exact e_mem (by exact_mod_cast hq0) (by omega)
  let z1 : L := ⟨e p, hmp⟩; let z2 : L := ⟨e q, hmq⟩
  have hz1 : IsPrimitiveRoot z1 p.den := coe_submonoidClass_iff.mp (Complex.isPrimitiveRoot_exp_rat p)
  have hz2 : IsPrimitiveRoot z2 q.den := coe_submonoidClass_iff.mp (Complex.isPrimitiveRoot_exp_rat q)
  have hrel : (z1 - 1) * (z1⁻¹ - 1) = algebraMap ℚ L (r ^ 2) * ((z2 - 1) * (z2⁻¹ - 1)) := by
    apply Subtype.ext
    change (e p - 1) * ((e p)⁻¹ - 1) = ((r ^ 2 : ℚ) : ℂ) * ((e q - 1) * ((e q)⁻¹ - 1))
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp, show (q : ℂ) = ((q : ℝ) : ℂ) by simp, e_sq, e_sq,
      show (2 * Real.sin (p * pi)) ^ 2 = (r : ℝ) ^ 2 * (2 * Real.sin (q * pi)) ^ 2 by
        rw [(div_eq_iff hsq.ne').mp hr]; ring]
    push_cast; rfl
  have hn := congrArg (fun x => (norm ℚ x) ^ (p.den.totient * q.den.totient)) hrel
  rw [pow_mul, npow ℚ hz1 hdp (cyclotomic.irreducible_rat (by omega)), map_mul,
    Algebra.norm_algebraMap, mul_pow, mul_comm p.den.totient, pow_mul _ q.den.totient,
    pow_mul _ q.den.totient, npow ℚ hz2 hdq (cyclotomic.irreducible_rat (by omega))] at hn
  simp only [← pow_mul] at hn
  rw [mul_assoc (2 * _), mul_comm q.den.totient] at hn
  have hr1 := eq_one hr0 hdp hdq (mul_pos two_pos Module.finrank_pos) hn
  have hme : (p : ℝ) * pi = q * pi := Real.strictMonoOn_sin.injOn
    ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
    ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
    (by simpa [hr1] using (div_eq_iff hsq.ne').mp hr)
  exact hpq (by exact_mod_cast mul_right_cancel₀ pi_pos.ne' hme)
