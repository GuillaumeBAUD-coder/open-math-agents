import FormalConjectures.ErdosProblems.«90»

-- Reduction Erdos90.erdos_90.variants.sawin_explicit.R1 of Sawin's explicit exponent.
-- Credit: @green-notes
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Sawin's explicit unit distance exponent `1.014114`

Reduction of `Erdos90.erdos_90.variants.sawin_explicit` into four independent pillars
following Sawin (`arXiv:2605.20579`):

* `H1`: Sawin Lemma 2 (lattice geometry in `EuclideanSpace ℝ (Fin (2 * d))`).
* `H2`: Sawin Lemmas 11–12 (quantitative totally real / CM tower beating `0.014114`).
* `H3`: Sawin Lemmas 6 & 9 (relative class group pigeonhole and Louboutin bound).
* `H4`: Sawin Lemmas 4, 5, 7, 8 (ideal family and Euclidean lattice embedding).
-/

namespace OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1

open Filter EuclideanGeometry NumberField
open scoped EuclideanGeometry

/-- Sawin Lemma 2 (lattice geometry of unit distances): a lattice in `R^{2d}` with minimal
nonzero norm `ρ` and an injective additive map `π : Λ → R^2` containing `S` of norm `≤ 1` and
`|π v| = 1` yields a finite planar point set `U` of bounded size with many unit distances. -/
def H1 : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (R : ℝ), 1 < R →
    ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * d))))
      (ρ : ℝ), 0 < ρ → (∀ v : Λ, v ≠ 0 → ρ ≤ ‖(v : EuclideanSpace ℝ (Fin (2 * d)))‖) →
      ∀ (π : Λ →+ ℝ²), Function.Injective π →
        ∀ (S : Finset Λ),
          (∀ v ∈ S, ‖(v : EuclideanSpace ℝ (Fin (2 * d)))‖ ≤ 1) →
          (∀ v ∈ S, ‖π v‖ = 1) →
          ∃ U : Finset ℝ², 0 < U.card ∧ (U.card : ℝ) ≤ (2 * R / ρ + 1) ^ (2 * d) ∧
            ((1 : ℝ) - 1 / R) ^ (2 * d) * (S.card : ℝ) * (U.card : ℝ) ≤
              2 * (unitDistNum U : ℝ)

/-- Sawin Lemmas 11 and 12 (quantitative totally real and CM tower): there exist a finite prime
set `S_Q`, local parameters `e, f, k`, root discriminant bound `lam > 1`, and radius `R > 1`
satisfying the explicit exponent inequality beating `0.014114`, together with CM quadratic
extensions `K / F` of arbitrarily large degree `d` where every prime of `F` over `p ∈ S_Q`
splits in `K` with ramification index `e p` and inertia degree at most `f p`. -/
def H2 : Prop :=
  ∃ (S_Q : Finset ℕ) (e f k : ℕ → ℕ) (lam R : ℝ),
    1 < lam ∧ 1 < R ∧
    (∀ p ∈ S_Q, p.Prime ∧ 1 ≤ e p ∧ 1 ≤ f p ∧ 1 ≤ k p) ∧
    (2 * R * ∏ p ∈ S_Q, (p : ℝ) ^ ((k p : ℝ) / (2 * (e p : ℝ))) + 1) ^ (0.014114 : ℝ) <
      (1 - 1 / R) * Real.sqrt (2 * Real.pi / Real.exp 1) *
        (∏ p ∈ S_Q, ((k p : ℝ) + 1) ^ ((1 : ℝ) / (2 * (e p : ℝ) * (f p : ℝ)))) /
        (lam ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log lam)) ∧
    ∀ N : ℕ, ∃ (F K : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
      (_ : IsTotallyReal F) (_ : Field K) (_ : CharZero K) (_ : NumberField K)
      (_ : IsTotallyComplex K) (_ : Algebra F K) (_ : Algebra.IsQuadraticExtension F K),
      N ≤ Module.finrank ℚ F ∧
      |(NumberField.discr K : ℝ)| / |(NumberField.discr F : ℝ)| ≤ lam ^ (Module.finrank ℚ F) ∧
      ∀ p ∈ S_Q, ∀ 𝔭 ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F),
        𝔭.ramificationIdx ℤ = e p ∧ 𝔭.inertiaDeg ℤ ≤ f p ∧ Nat.card (𝔭.primesOver (𝓞 K)) = 2

/-- Sawin Lemmas 6 and 9 (relative class group pigeonhole and Louboutin bound): for any CM
quadratic extension `K / F` with `|disc K| / |disc F| ≤ lam^d`, any nonempty finite set `L` of
nonzero ideals of `O_K` sharing a common relative norm to `O_F` yields an ideal `J₀ ∈ L` and a
finite subset `B ⊆ J₀⁻¹` of elements of relative norm `1` whose size loses at most
`2^d * 8 * lam^2 * (sqrt(lam) * log(lam) * e / (4 * pi))^d`. -/
def H3 : Prop :=
  ∀ (F K : Type) [Field F] [CharZero F] [NumberField F] [IsTotallyReal F]
    [Field K] [CharZero K] [NumberField K] [IsTotallyComplex K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K] (lam : ℝ),
    1 < lam →
    |(NumberField.discr K : ℝ)| / |(NumberField.discr F : ℝ)| ≤ lam ^ (Module.finrank ℚ F) →
    ∀ (L : Finset (Ideal (𝓞 K))),
      L.Nonempty →
      (∀ J ∈ L, J ≠ ⊥) →
      (∀ J₁ ∈ L, ∀ J₂ ∈ L, Ideal.relNorm (𝓞 F) J₁ = Ideal.relNorm (𝓞 F) J₂) →
      ∃ J₀ ∈ L, ∃ B : Finset K,
        (∀ β ∈ B, (∀ a ∈ J₀, ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = β * algebraMap (𝓞 K) K a) ∧
          Algebra.norm F β = 1) ∧
        (L.card : ℝ) ≤ (B.card : ℝ) *
          (2 ^ (Module.finrank ℚ F) *
            (8 * lam ^ 2 * (Real.sqrt lam * Real.log lam * (Real.exp 1 / (4 * Real.pi))) ^
              (Module.finrank ℚ F)))

/-- Sawin Lemmas 4, 5, 7, 8 (ideal family and Euclidean lattice embedding): given a CM extension
`K / F` with primes `p ∈ S_Q` splitting in `K` with `e p, f p` and any relative class group
pigeonhole bound with loss factor `C_loss > 0`, one obtains lattice data `(Λ, ρ, π, S)`
satisfying the hypotheses of the lattice reduction lemma with explicit `ρ` and `S.card`. -/
def H4 : Prop :=
  ∀ (F K : Type) [Field F] [CharZero F] [NumberField F] [IsTotallyReal F]
    [Field K] [CharZero K] [NumberField K] [IsTotallyComplex K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K],
    1 ≤ Module.finrank ℚ F →
    ∀ (S_Q : Finset ℕ) (e f k : ℕ → ℕ) (C_loss : ℝ),
      0 < C_loss →
      (∀ p ∈ S_Q, p.Prime ∧ 1 ≤ e p ∧ 1 ≤ f p ∧ 1 ≤ k p) →
      (∀ p ∈ S_Q, ∀ 𝔭 ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F),
        𝔭.ramificationIdx ℤ = e p ∧ 𝔭.inertiaDeg ℤ ≤ f p ∧ Nat.card (𝔭.primesOver (𝓞 K)) = 2) →
      (∀ (L : Finset (Ideal (𝓞 K))),
        L.Nonempty → (∀ J ∈ L, J ≠ ⊥) →
        (∀ J₁ ∈ L, ∀ J₂ ∈ L, Ideal.relNorm (𝓞 F) J₁ = Ideal.relNorm (𝓞 F) J₂) →
        ∃ J₀ ∈ L, ∃ B : Finset K,
          (∀ β ∈ B, (∀ a ∈ J₀, ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = β * algebraMap (𝓞 K) K a) ∧
            Algebra.norm F β = 1) ∧
          (L.card : ℝ) ≤ (B.card : ℝ) * C_loss) →
      ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * Module.finrank ℚ F))))
        (ρ : ℝ) (π : Λ →+ ℝ²) (S : Finset Λ),
        0 < ρ ∧
        (∀ v : Λ, v ≠ 0 → ρ ≤ ‖(v : EuclideanSpace ℝ (Fin (2 * Module.finrank ℚ F)))‖) ∧
        Function.Injective π ∧
        (∀ v ∈ S, ‖(v : EuclideanSpace ℝ (Fin (2 * Module.finrank ℚ F)))‖ ≤ 1) ∧
        (∀ v ∈ S, ‖π v‖ = 1) ∧
        ρ⁻¹ ≤ ∏ p ∈ S_Q, (p : ℝ) ^ ((k p : ℝ) / (2 * (e p : ℝ))) ∧
        ∏ p ∈ S_Q, ((k p : ℝ) + 1) ^ ((Module.finrank ℚ F : ℝ) / ((e p : ℝ) * (f p : ℝ))) ≤
          (S.card : ℝ) * C_loss

lemma exp_algebra_helper {R lam B : ℝ} {d : ℕ} (hlam : 1 < lam) (hR : 1 < R)
    (hB : 0 < B) :
    ((1 - 1 / R) * Real.sqrt (2 * Real.pi / Real.exp 1) * B /
      (lam ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log lam))) ^ (2 * d) / (8 * lam ^ 2) =
    ((1 - 1 / R) ^ (2 * d) * (B ^ (2 * d))) /
      (2 ^ d * (8 * lam ^ 2 * (Real.sqrt lam * Real.log lam * (Real.exp 1 / (4 * Real.pi))) ^ d)) := by
  have hlog : 0 < Real.log lam := Real.log_pos hlam
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hlam0 : 0 < lam := by linarith
  have hsqrt_lam : (lam ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt lam := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam0.le, Real.sqrt_eq_rpow]
    norm_num
  have hsqrt_log : (Real.sqrt (Real.log lam)) ^ 2 = Real.log lam := Real.sq_sqrt hlog.le
  have hsqrt_pi : (Real.sqrt (2 * Real.pi / Real.exp 1)) ^ 2 = 2 * Real.pi / Real.exp 1 :=
    Real.sq_sqrt (by positivity)
  have hsq : ((1 - 1 / R) * Real.sqrt (2 * Real.pi / Real.exp 1) * B /
      (lam ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log lam))) ^ 2 =
      ((1 - 1 / R) ^ 2 * (B ^ 2)) /
        (2 * (Real.sqrt lam * Real.log lam * (Real.exp 1 / (4 * Real.pi)))) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, hsqrt_pi, hsqrt_lam, hsqrt_log]
    field_simp
    ring
  set C : ℝ := Real.sqrt lam * Real.log lam * (Real.exp 1 / (4 * Real.pi))
  have h1 : ((1 - 1 / R) * Real.sqrt (2 * Real.pi / Real.exp 1) * B /
      (lam ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log lam))) ^ (2 * d) =
      ((1 - 1 / R) ^ (2 * d) * B ^ (2 * d)) / (2 ^ d * C ^ d) := by
    calc ((1 - 1 / R) * Real.sqrt (2 * Real.pi / Real.exp 1) * B /
        (lam ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log lam))) ^ (2 * d)
        = (((1 - 1 / R) * Real.sqrt (2 * Real.pi / Real.exp 1) * B /
            (lam ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log lam))) ^ 2) ^ d := pow_mul _ 2 d
      _ = (((1 - 1 / R) ^ 2 * B ^ 2) / (2 * C)) ^ d := by rw [hsq]
      _ = ((1 - 1 / R) ^ 2 * B ^ 2) ^ d / (2 * C) ^ d := div_pow _ _ d
      _ = (((1 - 1 / R) ^ 2) ^ d * (B ^ 2) ^ d) / (2 ^ d * C ^ d) := by rw [mul_pow, mul_pow]
      _ = ((1 - 1 / R) ^ (2 * d) * B ^ (2 * d)) / (2 ^ d * C ^ d) := by rw [← pow_mul, ← pow_mul]
  rw [h1, div_div, mul_assoc (2 ^ d) (C ^ d) (8 * lam ^ 2), mul_comm (C ^ d) (8 * lam ^ 2)]

lemma sawin_asymptotic_step
    {d N S_card : ℕ} {U : Finset ℝ²} {S_Q : Finset ℕ} {e f k : ℕ → ℕ}
    {lam R ρ P1 P2 X Y C_loss : ℝ}
    (hlam : 1 < lam) (hR : 1 < R) (hρ : 0 < ρ) (hP2_pos : 0 < P2)
    (hX_pos : 0 < X) (hC_pos : 0 < C_loss)
    (hP2_eq : P2 = ∏ p ∈ S_Q, ((k p : ℝ) + 1) ^ ((1 : ℝ) / (2 * (e p : ℝ) * (f p : ℝ))))
    (hX_eq : X = 2 * R * P1 + 1)
    (hY_eq : Y = (1 - 1 / R) * Real.sqrt (2 * Real.pi / Real.exp 1) * P2 /
      (lam ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log lam)))
    (hC_eq : C_loss = 2 ^ d * (8 * lam ^ 2 *
      (Real.sqrt lam * Real.log lam * (Real.exp 1 / (4 * Real.pi))) ^ d))
    (hp_S : ∀ p ∈ S_Q, p.Prime ∧ 1 ≤ e p ∧ 1 ≤ f p ∧ 1 ≤ k p)
    (hr_bd : 16 * lam ^ 2 ≤ (Y / X ^ (0.014114 : ℝ)) ^ (2 * d))
    (hY_bd : 8 * lam ^ 2 * ((N : ℝ) + 1) ≤ Y ^ (2 * d))
    (hρ_inv : ρ⁻¹ ≤ P1)
    (hS_card : ∏ p ∈ S_Q, ((k p : ℝ) + 1) ^ ((d : ℝ) / ((e p : ℝ) * (f p : ℝ))) ≤
      (S_card : ℝ) * C_loss)
    (hU_pos : 0 < U.card)
    (hU_le : (U.card : ℝ) ≤ (2 * R / ρ + 1) ^ (2 * d))
    (hU_dens : ((1 : ℝ) - 1 / R) ^ (2 * d) * (S_card : ℝ) * (U.card : ℝ) ≤
      2 * (unitDistNum U : ℝ)) :
    N < U.card ∧ (U.card : ℝ) ^ (1.014114 : ℝ) ≤ (Erdos90.maxUnitDistances U.card : ℝ) := by
  have hP2_pow : P2 ^ (2 * d) =
      ∏ p ∈ S_Q, ((k p : ℝ) + 1) ^ ((d : ℝ) / ((e p : ℝ) * (f p : ℝ))) := by
    rw [hP2_eq, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨_, hep, hfp, _⟩ := hp_S p hp
    have h1 : (0 : ℝ) < (k p : ℝ) + 1 := by positivity
    rw [← Real.rpow_natCast, ← Real.rpow_mul h1.le]
    congr 1
    have he0 : (e p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hf0 : (f p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp
  have hS_lower : Y ^ (2 * d) / (8 * lam ^ 2) ≤ ((1 : ℝ) - 1 / R) ^ (2 * d) * (S_card : ℝ) := by
    have hexp : Y ^ (2 * d) / (8 * lam ^ 2) =
        ((1 - 1 / R) ^ (2 * d) * P2 ^ (2 * d)) / C_loss := by
      rw [hY_eq, hC_eq]
      exact exp_algebra_helper hlam hR hP2_pos
    rw [hexp, hP2_pow, div_le_iff₀ hC_pos]
    have h1R : 0 ≤ (1 : ℝ) - 1 / R := by
      rw [sub_nonneg, div_le_one (by linarith)]
      exact hR.le
    calc ((1 : ℝ) - 1 / R) ^ (2 * d) *
          ∏ p ∈ S_Q, ((k p : ℝ) + 1) ^ ((d : ℝ) / ((e p : ℝ) * (f p : ℝ)))
        ≤ ((1 : ℝ) - 1 / R) ^ (2 * d) * ((S_card : ℝ) * C_loss) :=
          mul_le_mul_of_nonneg_left hS_card (pow_nonneg h1R _)
      _ = ((1 : ℝ) - 1 / R) ^ (2 * d) * (S_card : ℝ) * C_loss := by ring
  refine ⟨?_, ?_⟩
  · have hU_sq : 2 * (unitDistNum U : ℝ) ≤ (U.card : ℝ) * (U.card : ℝ) := by
      have h1 : unitDistNum U ≤ U.card.choose 2 := unitDistNum_le_choose_two U
      have h2 : 2 * U.card.choose 2 ≤ U.card * U.card := by
        rw [Nat.choose_two_right]
        calc 2 * (U.card * (U.card - 1) / 2) ≤ U.card * (U.card - 1) := Nat.mul_div_le _ 2
          _ ≤ U.card * U.card := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact_mod_cast (Nat.mul_le_mul_left 2 h1).trans h2
    have hU_ge_S : ((1 : ℝ) - 1 / R) ^ (2 * d) * (S_card : ℝ) ≤ (U.card : ℝ) := by
      have hU_posR : (0 : ℝ) < (U.card : ℝ) := Nat.cast_pos.mpr hU_pos
      exact le_of_mul_le_mul_right (hU_dens.trans hU_sq) hU_posR
    have hN_lt_U : (N : ℝ) < (U.card : ℝ) := by
      have h1 : (N : ℝ) < (N : ℝ) + 1 := by linarith
      have h2 : (N : ℝ) + 1 ≤ Y ^ (2 * d) / (8 * lam ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      exact lt_of_lt_of_le h1 (h2.trans (hS_lower.trans hU_ge_S))
    exact Nat.cast_lt.mp hN_lt_U
  · have hU_le_X : (U.card : ℝ) ≤ X ^ (2 * d) := by
      refine hU_le.trans (pow_le_pow_left₀ (by positivity) ?_ _)
      rw [div_eq_mul_inv, hX_eq]
      linarith [mul_le_mul_of_nonneg_left hρ_inv (by linarith : (0 : ℝ) ≤ 2 * R)]
    have hX_pow_le_Y : (X ^ (0.014114 : ℝ)) ^ (2 * d) ≤ Y ^ (2 * d) / (16 * lam ^ 2) := by
      rw [div_pow] at hr_bd
      have hX_2d_pos : 0 < (X ^ (0.014114 : ℝ)) ^ (2 * d) := by positivity
      rw [le_div_iff₀ hX_2d_pos] at hr_bd
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hU_rpow : (U.card : ℝ) ^ (1.014114 : ℝ) ≤ (unitDistNum U : ℝ) := by
      have hU_nonneg : (0 : ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
      have hsplit_exp : (U.card : ℝ) ^ (1.014114 : ℝ) =
          (U.card : ℝ) ^ (0.014114 : ℝ) * (U.card : ℝ) := by
        rw [show (1.014114 : ℝ) = 0.014114 + 1 by norm_num,
          Real.rpow_add (Nat.cast_pos.mpr hU_pos), Real.rpow_one]
      have hU_eps : (U.card : ℝ) ^ (0.014114 : ℝ) ≤ (X ^ (0.014114 : ℝ)) ^ (2 * d) := by
        calc (U.card : ℝ) ^ (0.014114 : ℝ)
            ≤ (X ^ (2 * d)) ^ (0.014114 : ℝ) :=
              Real.rpow_le_rpow hU_nonneg hU_le_X (by norm_num)
          _ = (X ^ (0.014114 : ℝ)) ^ (2 * d) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hX_pos.le, mul_comm,
                Real.rpow_mul hX_pos.le, Real.rpow_natCast]
      have hU_eps2 : (U.card : ℝ) ^ (0.014114 : ℝ) ≤
          (1 / 2 : ℝ) * (((1 : ℝ) - 1 / R) ^ (2 * d) * (S_card : ℝ)) := by
        calc (U.card : ℝ) ^ (0.014114 : ℝ)
            ≤ (X ^ (0.014114 : ℝ)) ^ (2 * d) := hU_eps
          _ ≤ Y ^ (2 * d) / (16 * lam ^ 2) := hX_pow_le_Y
          _ = (1 / 2 : ℝ) * (Y ^ (2 * d) / (8 * lam ^ 2)) := by ring
          _ ≤ (1 / 2 : ℝ) * (((1 : ℝ) - 1 / R) ^ (2 * d) * (S_card : ℝ)) :=
              mul_le_mul_of_nonneg_left hS_lower (by norm_num)
      calc (U.card : ℝ) ^ (1.014114 : ℝ)
          = (U.card : ℝ) ^ (0.014114 : ℝ) * (U.card : ℝ) := hsplit_exp
        _ ≤ (1 / 2 : ℝ) * (((1 : ℝ) - 1 / R) ^ (2 * d) * (S_card : ℝ)) * (U.card : ℝ) :=
            mul_le_mul_of_nonneg_right hU_eps2 hU_nonneg
        _ = (1 / 2 : ℝ) * (((1 : ℝ) - 1 / R) ^ (2 * d) * (S_card : ℝ) * (U.card : ℝ)) := by ring
        _ ≤ (1 / 2 : ℝ) * (2 * (unitDistNum U : ℝ)) :=
            mul_le_mul_of_nonneg_left hU_dens (by norm_num)
        _ = (unitDistNum U : ℝ) := by ring
    have hmax : (unitDistNum U : ℝ) ≤ (Erdos90.maxUnitDistances U.card : ℝ) :=
      Nat.cast_le.mpr (le_csSup (Erdos90.unitDistanceCounts_BddAbove U.card) ⟨U, rfl, rfl⟩)
    exact hU_rpow.trans hmax

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos90.erdos_90.variants.sawin_explicit := by
  intro h1 h2 h3 h4
  obtain ⟨S_Q, e, f, k, lam, R, hlam, hR, hp_S, hXltY, htower⟩ := h2
  obtain ⟨P1, hP1_eq⟩ : ∃ x, x = ∏ p ∈ S_Q, (p : ℝ) ^ ((k p : ℝ) / (2 * (e p : ℝ))) := ⟨_, rfl⟩
  obtain ⟨P2, hP2_eq⟩ :
      ∃ x, x = ∏ p ∈ S_Q, ((k p : ℝ) + 1) ^ ((1 : ℝ) / (2 * (e p : ℝ) * (f p : ℝ))) := ⟨_, rfl⟩
  obtain ⟨X, hX_eq⟩ : ∃ x, x = 2 * R * P1 + 1 := ⟨_, rfl⟩
  obtain ⟨Y, hY_eq⟩ : ∃ x, x = (1 - 1 / R) * Real.sqrt (2 * Real.pi / Real.exp 1) * P2 /
      (lam ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log lam)) := ⟨_, rfl⟩
  have hP1_ge1 : 1 ≤ P1 := by
    rw [hP1_eq]
    refine Finset.prod_induction _ (fun x => (1 : ℝ) ≤ x) (fun _ _ ha hb => by nlinarith)
      le_rfl fun p hp => ?_
    obtain ⟨hp_prime, _, _, _⟩ := hp_S p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp_prime.one_le
    exact Real.one_le_rpow hp1 (by positivity)
  have hP2_pos : 0 < P2 := by
    rw [hP2_eq]
    exact Finset.prod_pos fun _ _ => Real.rpow_pos_of_pos (by positivity) _
  have hX_gt3 : 3 < X := by
    have h2R : 2 < 2 * R := by linarith
    have hmul : 2 * R ≤ 2 * R * P1 := le_mul_of_one_le_right (by linarith) hP1_ge1
    rw [hX_eq]
    linarith
  have hX_pos : 0 < X := by linarith
  have hXltY' : X ^ (0.014114 : ℝ) < Y := by
    rw [hX_eq, hY_eq, hP1_eq, hP2_eq]
    exact hXltY
  have hXpow_gt1 : 1 < X ^ (0.014114 : ℝ) := Real.one_lt_rpow (by linarith) (by norm_num)
  have hY_gt1 : 1 < Y := lt_trans hXpow_gt1 hXltY'
  have hr_gt1 : 1 < Y / X ^ (0.014114 : ℝ) := (one_lt_div (by positivity)).mpr hXltY'
  rw [Set.infinite_iff_exists_gt]
  intro N
  have htend_mul : Tendsto (fun d : ℕ => 2 * d) atTop atTop := by
    rw [tendsto_atTop_atTop]
    exact fun b => ⟨b, fun a ha => by omega⟩
  have htend1 : Tendsto (fun d : ℕ => (Y / X ^ (0.014114 : ℝ)) ^ (2 * d)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr_gt1).comp htend_mul
  have htend2 : Tendsto (fun d : ℕ => Y ^ (2 * d)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hY_gt1).comp htend_mul
  obtain ⟨D1, hD1⟩ := (htend1.eventually_ge_atTop (16 * lam ^ 2)).exists_forall_of_atTop
  obtain ⟨D2, hD2⟩ := (htend2.eventually_ge_atTop (8 * lam ^ 2 * ((N : ℝ) + 1))).exists_forall_of_atTop
  set D0 : ℕ := max 1 (max D1 D2)
  obtain ⟨F, K, _, _, _, _, _, _, _, _, _, _, hN_d, hdiscr, hsplit⟩ := htower D0
  have hd1 : 1 ≤ Module.finrank ℚ F := le_trans (le_max_left _ _) hN_d
  have hdD1 : D1 ≤ Module.finrank ℚ F :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN_d
  have hdD2 : D2 ≤ Module.finrank ℚ F :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN_d
  have hr_bd : 16 * lam ^ 2 ≤ (Y / X ^ (0.014114 : ℝ)) ^ (2 * Module.finrank ℚ F) :=
    hD1 (Module.finrank ℚ F) hdD1
  have hY_bd : 8 * lam ^ 2 * ((N : ℝ) + 1) ≤ Y ^ (2 * Module.finrank ℚ F) :=
    hD2 (Module.finrank ℚ F) hdD2
  have hlog_pos : 0 < Real.log lam := Real.log_pos hlam
  obtain ⟨C_loss, hC_eq⟩ : ∃ x, x = 2 ^ (Module.finrank ℚ F) * (8 * lam ^ 2 *
      (Real.sqrt lam * Real.log lam * (Real.exp 1 / (4 * Real.pi))) ^ (Module.finrank ℚ F)) :=
    ⟨_, rfl⟩
  have hC_pos : 0 < C_loss := by
    rw [hC_eq]
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  have hpigeon : ∀ (L : Finset (Ideal (𝓞 K))),
      L.Nonempty → (∀ J ∈ L, J ≠ ⊥) →
      (∀ J₁ ∈ L, ∀ J₂ ∈ L, Ideal.relNorm (𝓞 F) J₁ = Ideal.relNorm (𝓞 F) J₂) →
      ∃ J₀ ∈ L, ∃ B : Finset K,
        (∀ β ∈ B, (∀ a ∈ J₀, ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = β * algebraMap (𝓞 K) K a) ∧
          Algebra.norm F β = 1) ∧
        (L.card : ℝ) ≤ (B.card : ℝ) * C_loss := by
    rw [hC_eq]
    exact h3 F K lam hlam hdiscr
  obtain ⟨Λ, ρ, π, S, hρ, hΛ, hπ, hS_norm, hS_proj, hρ_inv, hS_card⟩ :=
    h4 F K hd1 S_Q e f k C_loss hC_pos hp_S hsplit hpigeon
  obtain ⟨U, hU_pos, hU_le, hU_dens⟩ :=
    h1 (Module.finrank ℚ F) hd1 R hR Λ ρ hρ hΛ π hπ S hS_norm hS_proj
  rw [← hP1_eq] at hρ_inv
  have hres := sawin_asymptotic_step hlam hR hρ hP2_pos hX_pos hC_pos hP2_eq hX_eq hY_eq hC_eq
    hp_S hr_bd hY_bd hρ_inv hS_card hU_pos hU_le hU_dens
  first | exact ⟨U.card, hres.2, hres.1⟩ | exact ⟨U.card, hres.1, hres.2⟩

end OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1
