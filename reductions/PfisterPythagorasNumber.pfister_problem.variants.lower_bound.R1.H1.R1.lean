import OMAReductions.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Reduction of Cassels–Ellison–Pfister (1971) to Cassels' theorem and the Motzkin elliptic curve

This reduction splits `PfisterPythagorasNumber.pfister_problem.variants.lower_bound.R1.H1`
(the Motzkin polynomial `1 + X₀² X₁⁴ + X₀⁴ X₁² - 3 X₀² X₁²` is not a sum of 3 squares in
`ℝ(X₀, X₁)`) into two clean, self-contained steps:

- `H1`: Cassels' theorem (1964) for sums of 3 squares in one variable over `ℝ(x)` — any
  polynomial in `ℝ(x)[y]` that is a sum of 3 squares in `ℝ(x)(y)` is already a sum of 3 squares
  in `ℝ(x)[y]`.
- `H2`: No non-trivial `ℝ(x)`-rational point on the factored Motzkin elliptic curve
  `S² = (T - 2x)(T + 2x)(T - (x⁴ - 3x²))` with `x⁴ - 3x² - T` a nonzero sum of 3 squares in `ℝ(x)`.

In `main`, we embed `MvRatFunc (Fin 2) ℝ` into `RatFunc (RatFunc ℝ)`, apply `H1`, use formal
reality of `ℝ(x)` to bound the `y`-degrees by 2, extract the five vector equations in `ℝ(x)³`,
rule out `b = 0` by evaluating at `t ≥ 3`, and apply Lagrange's identity to produce a point
`(T, S)` contradicting `H2`.
-/

-- Reduction PfisterPythagorasNumber.pfister_problem.variants.lower_bound.R1.H1.R1
-- Credit: @hackoria

open scoped Polynomial

namespace OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1_H1_R1

/-- Cassels (1964) for sums of 3 squares in one variable over `ℝ(x)`. -/
def H1 : Prop :=
  ∀ f : Polynomial (RatFunc ℝ),
    IsSumSqOfLength 3 (algebraMap (Polynomial (RatFunc ℝ)) (RatFunc (RatFunc ℝ)) f) →
    IsSumSqOfLength 3 f

/-- No non-trivial `ℝ(x)`-point on the Motzkin elliptic curve (Cassels–Ellison–Pfister 1971). -/
def H2 : Prop :=
  let x : RatFunc ℝ := algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X
  ¬ ∃ (T S : RatFunc ℝ),
    S ^ 2 = (T - 2 * x) * (T + 2 * x) * (T - (x ^ 4 - 3 * x ^ 2)) ∧
    IsSumSqOfLength 3 (x ^ 4 - 3 * x ^ 2 - T) ∧
    x ^ 4 - 3 * x ^ 2 - T ≠ 0

section Proof

private abbrev K : Type := RatFunc ℝ
private noncomputable def xK : K := algebraMap ℝ[X] K Polynomial.X

private lemma exists_real_ge_not_root (p : ℝ[X]) (hp : p ≠ 0) (M : ℝ) :
    ∃ t : ℝ, M ≤ t ∧ p.eval t ≠ 0 := by
  have hinf : (Set.Ici M).Infinite := Set.Ici_infinite M
  obtain ⟨t, htM, htnr⟩ := hinf.exists_notMem_finset p.roots.toFinset
  refine ⟨t, htM, fun h0 => htnr ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact h0

private lemma real_poly_sum_sq_eq_zero {p₁ p₂ p₃ : ℝ[X]}
    (h : p₁ * p₁ + p₂ * p₂ + p₃ * p₃ = 0) : p₁ = 0 ∧ p₂ = 0 ∧ p₃ = 0 := by
  have hev : ∀ t : ℝ, p₁.eval t = 0 ∧ p₂.eval t = 0 ∧ p₃.eval t = 0 := fun t => by
    have ht := congr_arg (Polynomial.eval t) h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_zero] at ht
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  have h0 : ∀ q : ℝ[X], (∀ t : ℝ, q.eval t = 0) → q = 0 := fun q hq => by
    by_contra hne
    obtain ⟨t, _, ht⟩ := exists_real_ge_not_root q hne 0
    exact ht (hq t)
  exact ⟨h0 p₁ fun t => (hev t).1, h0 p₂ fun t => (hev t).2.1, h0 p₃ fun t => (hev t).2.2⟩

private lemma ratFunc_sum_sq_eq_zero {a b c : K}
    (h : a * a + b * b + c * c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have had := RatFunc.denom_ne_zero a
  have hbd := RatFunc.denom_ne_zero b
  have hcd := RatFunc.denom_ne_zero c
  set D : ℝ[X] := a.denom * b.denom * c.denom
  have hD : D ≠ 0 := mul_ne_zero (mul_ne_zero had hbd) hcd
  set p₁ : ℝ[X] := a.num * b.denom * c.denom
  set p₂ : ℝ[X] := a.denom * b.num * c.denom
  set p₃ : ℝ[X] := a.denom * b.denom * c.num
  have hclear : ∀ (u : K) (q : ℝ[X]),
      algebraMap ℝ[X] K D * u = algebraMap ℝ[X] K q →
      (algebraMap ℝ[X] K D * u) * (algebraMap ℝ[X] K D * u) = algebraMap ℝ[X] K (q * q) := by
    intro u q hu; rw [hu, map_mul]
  have ha : algebraMap ℝ[X] K D * a = algebraMap ℝ[X] K p₁ := by
    rw [← RatFunc.num_div_denom a]
    simp only [D, p₁, map_mul]
    field_simp [RatFunc.algebraMap_ne_zero had]
  have hb : algebraMap ℝ[X] K D * b = algebraMap ℝ[X] K p₂ := by
    rw [← RatFunc.num_div_denom b]
    simp only [D, p₂, map_mul]
    field_simp [RatFunc.algebraMap_ne_zero hbd]
  have hc : algebraMap ℝ[X] K D * c = algebraMap ℝ[X] K p₃ := by
    rw [← RatFunc.num_div_denom c]
    simp only [D, p₃, map_mul]
    field_simp [RatFunc.algebraMap_ne_zero hcd]
  have hsum : p₁ * p₁ + p₂ * p₂ + p₃ * p₃ = 0 := by
    apply RatFunc.algebraMap_injective ℝ
    rw [map_add, map_add, map_zero, ← hclear a p₁ ha, ← hclear b p₂ hb, ← hclear c p₃ hc]
    calc (algebraMap ℝ[X] K D * a) * (algebraMap ℝ[X] K D * a) +
        (algebraMap ℝ[X] K D * b) * (algebraMap ℝ[X] K D * b) +
        (algebraMap ℝ[X] K D * c) * (algebraMap ℝ[X] K D * c)
        = (algebraMap ℝ[X] K D) ^ 2 * (a * a + b * b + c * c) := by ring
      _ = 0 := by rw [h, mul_zero]
  obtain ⟨hp1, hp2, hp3⟩ := real_poly_sum_sq_eq_zero hsum
  have hDK : algebraMap ℝ[X] K D ≠ 0 := RatFunc.algebraMap_ne_zero hD
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp (ha.trans (by rw [hp1, map_zero]))).resolve_left hDK
  · exact (mul_eq_zero.mp (hb.trans (by rw [hp2, map_zero]))).resolve_left hDK
  · exact (mul_eq_zero.mp (hc.trans (by rw [hp3, map_zero]))).resolve_left hDK

private lemma not_sum_sq_of_neg_eval {q : ℝ[X]} (t0 : ℝ)
    (hneg : ∀ t : ℝ, t0 ≤ t → q.eval t < 0) :
    ¬ IsSumSqOfLength 3 (algebraMap ℝ[X] K q) := by
  rintro ⟨f, hf⟩
  rw [Fin.sum_univ_three] at hf
  have hd0 := RatFunc.denom_ne_zero (f 0)
  have hd1 := RatFunc.denom_ne_zero (f 1)
  have hd2 := RatFunc.denom_ne_zero (f 2)
  set D : ℝ[X] := (f 0).denom * (f 1).denom * (f 2).denom
  have hD : D ≠ 0 := mul_ne_zero (mul_ne_zero hd0 hd1) hd2
  set p₀ : ℝ[X] := (f 0).num * (f 1).denom * (f 2).denom
  set p₁ : ℝ[X] := (f 0).denom * (f 1).num * (f 2).denom
  set p₂ : ℝ[X] := (f 0).denom * (f 1).denom * (f 2).num
  have h0 : algebraMap ℝ[X] K D * f 0 = algebraMap ℝ[X] K p₀ := by
    rw [← RatFunc.num_div_denom (f 0)]; simp only [D, p₀, map_mul]
    field_simp [RatFunc.algebraMap_ne_zero hd0]
  have h1 : algebraMap ℝ[X] K D * f 1 = algebraMap ℝ[X] K p₁ := by
    rw [← RatFunc.num_div_denom (f 1)]; simp only [D, p₁, map_mul]
    field_simp [RatFunc.algebraMap_ne_zero hd1]
  have h2 : algebraMap ℝ[X] K D * f 2 = algebraMap ℝ[X] K p₂ := by
    rw [← RatFunc.num_div_denom (f 2)]; simp only [D, p₂, map_mul]
    field_simp [RatFunc.algebraMap_ne_zero hd2]
  have heq : q * (D * D) = p₀ * p₀ + p₁ * p₁ + p₂ * p₂ := by
    apply RatFunc.algebraMap_injective ℝ
    simp only [map_add, map_mul]
    rw [← h0, ← h1, ← h2]
    linear_combination (algebraMap ℝ[X] K D * algebraMap ℝ[X] K D) * hf
  obtain ⟨t, ht, hDt⟩ := exists_real_ge_not_root D hD t0
  have hev := congr_arg (Polynomial.eval t) heq
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at hev
  have hqneg : q.eval t < 0 := hneg t ht
  have hDpos : 0 < D.eval t * D.eval t := mul_self_pos.mpr hDt
  nlinarith

private lemma natDegree_le_two_of_sum_sq {p₁ p₂ p₃ M : K[X]}
    (hM : M.natDegree ≤ 4) (heq : M = p₁ * p₁ + p₂ * p₂ + p₃ * p₃) :
    p₁.natDegree ≤ 2 ∧ p₂.natDegree ≤ 2 ∧ p₃.natDegree ≤ 2 := by
  set d := max p₁.natDegree (max p₂.natDegree p₃.natDegree)
  have hd : d ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have hcoeff : M.coeff (2 * d) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hterm : ∀ q : K[X], q.natDegree ≤ d → (q * q).coeff (2 * d) = q.coeff d * q.coeff d := by
      intro q hq
      rw [Polynomial.coeff_mul, Finset.sum_eq_single (d, d)]
      · intro ⟨i, j⟩ hij hne
        rw [Finset.mem_antidiagonal] at hij
        by_cases hi : d < i
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        · have hj : d < j := by
            by_contra hle; apply hne; ext <;> omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < j), mul_zero]
      · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by omega)) h
    have hsum : p₁.coeff d * p₁.coeff d + p₂.coeff d * p₂.coeff d + p₃.coeff d * p₃.coeff d = 0 := by
      have h := congr_arg (fun q : K[X] => q.coeff (2 * d)) heq
      rw [hcoeff, Polynomial.coeff_add, Polynomial.coeff_add,
        hterm p₁ (le_max_left _ _),
        hterm p₂ ((le_max_left _ _).trans (le_max_right _ _)),
        hterm p₃ ((le_max_right _ _).trans (le_max_right _ _))] at h
      exact h.symm
    obtain ⟨hc1, hc2, hc3⟩ := ratFunc_sum_sq_eq_zero hsum
    have h1 : d = p₁.natDegree ∨ d = p₂.natDegree ∨ d = p₃.natDegree := by
      dsimp only [d]; omega
    rcases h1 with h | h | h
    · have hp : p₁ ≠ 0 := fun h0 => by rw [h0, Polynomial.natDegree_zero] at h; omega
      exact Polynomial.leadingCoeff_ne_zero.mpr hp (by rw [Polynomial.leadingCoeff, ← h]; exact hc1)
    · have hp : p₂ ≠ 0 := fun h0 => by rw [h0, Polynomial.natDegree_zero] at h; omega
      exact Polynomial.leadingCoeff_ne_zero.mpr hp (by rw [Polynomial.leadingCoeff, ← h]; exact hc2)
    · have hp : p₃ ≠ 0 := fun h0 => by rw [h0, Polynomial.natDegree_zero] at h; omega
      exact Polynomial.leadingCoeff_ne_zero.mpr hp (by rw [Polynomial.leadingCoeff, ← h]; exact hc3)
  exact ⟨(le_max_left _ _).trans hd,
    ((le_max_left _ _).trans (le_max_right _ _)).trans hd,
    ((le_max_right _ _).trans (le_max_right _ _)).trans hd⟩

private lemma poly_eq_quad {p : K[X]} (hp : p.natDegree ≤ 2) :
    p = Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 +
        Polynomial.C (p.coeff 1) * Polynomial.X +
        Polynomial.C (p.coeff 0) := by
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | n + 3 =>
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

private noncomputable def gPoly : MvPolynomial (Fin 2) ℝ →+* K[X] :=
  (Polynomial.mapRingHom ((algebraMap ℝ[X] K).comp
    (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv.toRingHom)).comp
    (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv.toRingHom

private lemma gPoly_inj : Function.Injective gPoly := by
  have hinner : Function.Injective ((algebraMap ℝ[X] K).comp
      (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv.toRingHom) :=
    (RatFunc.algebraMap_injective ℝ).comp (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).injective
  exact (Polynomial.map_injective _ hinner).comp (MvPolynomial.finSuccEquiv ℝ 1).injective

private noncomputable def gRat : MvPolynomial (Fin 2) ℝ →+* RatFunc K :=
  (algebraMap K[X] (RatFunc K)).comp gPoly

private lemma gRat_inj : Function.Injective gRat :=
  (RatFunc.algebraMap_injective K).comp gPoly_inj

private noncomputable def embedMotzkin : MvRatFunc (Fin 2) ℝ →+* RatFunc K :=
  IsFractionRing.lift gRat_inj

theorem main : H1 → H2 →
    OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1.H1 := by
  intro hcassels hcurve ⟨f, hf⟩
  let M : K[X] :=
    Polynomial.C (xK ^ 2) * Polynomial.X ^ 4 +
    Polynomial.C (xK ^ 4 - 3 * xK ^ 2) * Polynomial.X ^ 2 + 1
  have hMmap : embedMotzkin (algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)
      (1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
        MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 -
        3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)) =
      algebraMap K[X] (RatFunc K) M := by
    have hlift : ∀ p : MvPolynomial (Fin 2) ℝ,
        embedMotzkin (algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ) p) =
        algebraMap K[X] (RatFunc K) (gPoly p) := fun p =>
      IsFractionRing.lift_algebraMap gRat_inj p
    rw [hlift]
    congr 1
    have hX0 : gPoly (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
      simp [gPoly, MvPolynomial.finSuccEquiv_X_zero]
    have hX1 : gPoly (MvPolynomial.X (1 : Fin 2)) = Polynomial.C xK := by
      change Polynomial.map ((algebraMap ℝ[X] K).comp
        (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv.toRingHom)
        (MvPolynomial.finSuccEquiv ℝ 1 (MvPolynomial.X (Fin.succ 0))) = Polynomial.C xK
      rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
      simp [xK]
    simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, hX0, hX1, M]
    ring
  have hsumK : IsSumSqOfLength 3 (algebraMap K[X] (RatFunc K) M) := by
    refine ⟨fun i => embedMotzkin (f i), ?_⟩
    rw [← hMmap, hf, map_sum]
    refine Finset.sum_congr rfl fun i _ => map_mul _ _ _
  obtain ⟨p, hp⟩ := hcassels M hsumK
  rw [Fin.sum_univ_three] at hp
  have hMdeg : M.natDegree ≤ 4 := by
    dsimp only [M]
    compute_degree!
  obtain ⟨hd0, hd1, hd2⟩ := natDegree_le_two_of_sum_sq hMdeg hp
  set a₁ := (p 0).coeff 2; set b₁ := (p 0).coeff 1; set c₁ := (p 0).coeff 0
  set a₂ := (p 1).coeff 2; set b₂ := (p 1).coeff 1; set c₂ := (p 1).coeff 0
  set a₃ := (p 2).coeff 2; set b₃ := (p 2).coeff 1; set c₃ := (p 2).coeff 0
  have hp0 := poly_eq_quad hd0
  have hp1 := poly_eq_quad hd1
  have hp2 := poly_eq_quad hd2
  have hpoly : M =
      Polynomial.C (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * Polynomial.X ^ 4 +
      Polynomial.C (2 * (a₁ * b₁ + a₂ * b₂ + a₃ * b₃)) * Polynomial.X ^ 3 +
      Polynomial.C (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 + 2 * (a₁ * c₁ + a₂ * c₂ + a₃ * c₃)) * Polynomial.X ^ 2 +
      Polynomial.C (2 * (b₁ * c₁ + b₂ * c₂ + b₃ * c₃)) * Polynomial.X +
      Polynomial.C (c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2) := by
    rw [hp, hp0, hp1, hp2]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  have hcoef : ∀ n, M.coeff n =
      (Polynomial.C (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * Polynomial.X ^ 4 +
       Polynomial.C (2 * (a₁ * b₁ + a₂ * b₂ + a₃ * b₃)) * Polynomial.X ^ 3 +
       Polynomial.C (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 + 2 * (a₁ * c₁ + a₂ * c₂ + a₃ * c₃)) * Polynomial.X ^ 2 +
       Polynomial.C (2 * (b₁ * c₁ + b₂ * c₂ + b₃ * c₃)) * Polynomial.X +
       Polynomial.C (c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2)).coeff n := fun n => congr_arg (fun q => q.coeff n) hpoly
  have e4 : a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 = xK ^ 2 := by
    have h := hcoef 4
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h.symm
  have e3 : a₁ * b₁ + a₂ * b₂ + a₃ * b₃ = 0 := by
    have h := hcoef 3
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h
  have e2 : b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 + 2 * (a₁ * c₁ + a₂ * c₂ + a₃ * c₃) = xK ^ 4 - 3 * xK ^ 2 := by
    have h := hcoef 2
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h.symm
  have e1 : b₁ * c₁ + b₂ * c₂ + b₃ * c₃ = 0 := by
    have h := hcoef 1
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h
  have e0 : c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 = 1 := by
    have h := hcoef 0
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h.symm
  set T : K := 2 * (a₁ * c₁ + a₂ * c₂ + a₃ * c₃)
  set S : K := 2 * (a₁ * (c₂ * b₃ - c₃ * b₂) + a₂ * (c₃ * b₁ - c₁ * b₃) + a₃ * (c₁ * b₂ - c₂ * b₁))
  have hb_eq : xK ^ 4 - 3 * xK ^ 2 - T = b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 := by
    dsimp only [T]; linear_combination -e2
  have hb_ne : xK ^ 4 - 3 * xK ^ 2 - T ≠ 0 := by
    intro h0
    have hT : T = xK ^ 4 - 3 * xK ^ 2 := by linear_combination -h0
    have hcs : 4 * xK ^ 2 - (xK ^ 4 - 3 * xK ^ 2) ^ 2 =
        (2 * (a₂ * c₃ - a₃ * c₂)) ^ 2 + (2 * (a₃ * c₁ - a₁ * c₃)) ^ 2 +
        (2 * (a₁ * c₂ - a₂ * c₁)) ^ 2 := by
      have hlag : 4 * ((a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * (c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2)) -
          (2 * (a₁ * c₁ + a₂ * c₂ + a₃ * c₃)) ^ 2 =
          (2 * (a₂ * c₃ - a₃ * c₂)) ^ 2 + (2 * (a₃ * c₁ - a₁ * c₃)) ^ 2 +
          (2 * (a₁ * c₂ - a₂ * c₁)) ^ 2 := by ring
      rw [e4, e0, mul_one] at hlag
      change 4 * xK ^ 2 - T ^ 2 = _ at hlag
      rw [hT] at hlag
      exact hlag
    have hsq : IsSumSqOfLength 3 (algebraMap ℝ[X] K (4 * Polynomial.X ^ 2 - (Polynomial.X ^ 4 - 3 * Polynomial.X ^ 2) ^ 2)) := by
      refine ⟨fun i => match i with
        | 0 => 2 * (a₂ * c₃ - a₃ * c₂)
        | 1 => 2 * (a₃ * c₁ - a₁ * c₃)
        | 2 => 2 * (a₁ * c₂ - a₂ * c₁), ?_⟩
      simp only [map_sub, map_mul, map_pow, map_ofNat, Fin.sum_univ_three]
      change 4 * xK ^ 2 - (xK ^ 4 - 3 * xK ^ 2) ^ 2 = _
      rw [hcs]; ring
    exact not_sum_sq_of_neg_eval 3 (fun t ht => by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      have ht2 : 9 ≤ t ^ 2 := by nlinarith
      have ht4 : 54 ≤ t ^ 4 - 3 * t ^ 2 := by nlinarith
      nlinarith) hsq
  have hcurve_eq : S ^ 2 = (T - 2 * xK) * (T + 2 * xK) * (T - (xK ^ 4 - 3 * xK ^ 2)) := by
    have hident :
        4 * (a₁ * (c₂ * b₃ - c₃ * b₂) + a₂ * (c₃ * b₁ - c₁ * b₃) + a₃ * (c₁ * b₂ - c₂ * b₁)) ^ 2 +
        4 * ((a₁ * b₁ + a₂ * b₂ + a₃ * b₃) * c₁ - (b₁ * c₁ + b₂ * c₂ + b₃ * c₃) * a₁) ^ 2 +
        4 * ((a₁ * b₁ + a₂ * b₂ + a₃ * b₃) * c₂ - (b₁ * c₁ + b₂ * c₂ + b₃ * c₃) * a₂) ^ 2 +
        4 * ((a₁ * b₁ + a₂ * b₂ + a₃ * b₃) * c₃ - (b₁ * c₁ + b₂ * c₂ + b₃ * c₃) * a₃) ^ 2 =
        (4 * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * (c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2) -
          (2 * (a₁ * c₁ + a₂ * c₂ + a₃ * c₃)) ^ 2) * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2) := by ring
    rw [e3, e1, e4, e0] at hident
    have hS : S ^ 2 = (4 * xK ^ 2 - T ^ 2) * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2) := by
      dsimp only [S, T]
      linear_combination hident
    rw [hS, ← hb_eq]
    ring
  have hb_sq : IsSumSqOfLength 3 (xK ^ 4 - 3 * xK ^ 2 - T) := by
    refine ⟨fun i => match i with | 0 => b₁ | 1 => b₂ | 2 => b₃, ?_⟩
    rw [hb_eq, Fin.sum_univ_three]
    ring
  exact hcurve ⟨T, S, hcurve_eq, hb_sq, hb_ne⟩

end Proof

end OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1_H1_R1
