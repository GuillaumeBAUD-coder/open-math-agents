import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R3 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1
-- Credit: @0xf905

/-!
# Iterative density increment at exponential thresholds for 4-term progressions

The target is step H1 of reduction R1.H2.R1.H1.R1 of Erdős 142: there exist A > 1 and c > 0
such that eventually r_4(N) ≤ N * exp(-c * (log log N)^A).

This reduction isolates the 4-term iterative density increment architecture from qualitative
Szemerédi for 4-term progressions:

  H1: Above a fixed density level J, every 4-AP-free subset of [1, N] of density at least
      exp(-(j+1)) with log-log budget C * (j+1)^β + B ≤ log log N admits an affine
      subprogression of length M ≥ 2 on which the density reaches exp(-j) while losing at
      most C * ((j+1)^β - j^β) in log log length (with 0 < β < 1).
  H2: Qualitative Szemerédi for 4-term progressions at each fixed exponential threshold exp(-J).

Inducting on the density level rules out all 4-AP-free sets above the budget threshold, and
inverting β < 1 yields the super-polylogarithmic exponent A = (1 + 1/β) / 2 > 1.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3

open Erdos142 Filter Real

/-- Above level J, a 4-AP-free set gains a factor e in density on an affine subprogression
while charging its log-log length loss to the discrete difference of C * j^β. -/
def H1 : Prop :=
  ∃ (β C B : ℝ) (J : ℕ), 0 < β ∧ β < 1 ∧ 0 < C ∧
    ∀ j : ℕ, J ≤ j → ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      (N : ℝ) * Real.exp (-((j + 1 : ℕ) : ℝ)) ≤ (S.card : ℝ) →
      C * ((j + 1 : ℕ) : ℝ) ^ β + B ≤ Real.log (Real.log (N : ℝ)) →
      ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        (M : ℝ) * Real.exp (-(j : ℝ)) ≤
          (((Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)).card : ℝ) ∧
        Real.log (Real.log (N : ℝ)) - Real.log (Real.log (M : ℝ)) ≤
          C * (((j + 1 : ℕ) : ℝ) ^ β - (j : ℝ) ^ β)

/-- Qualitative Szemerédi for 4-term progressions at each fixed exponential density threshold. -/
def H2 : Prop :=
  ∀ J : ℕ, ∃ Q : ℝ, ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
    (N : ℝ) * Real.exp (-(J : ℝ)) ≤ (S.card : ℝ) →
    Real.log (Real.log (N : ℝ)) < Q

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1.H1 := by
  intro h1 h2
  obtain ⟨β, C, B, J, hβ0, hβ1, hC, hstep⟩ := h1
  obtain ⟨Q, hterm⟩ := h2 J
  let B' : ℝ := max B Q
  have hBB' : B ≤ B' := le_max_left _ _
  have hQB' : Q ≤ B' := le_max_right _ _
  have no_dense : ∀ m : ℕ, ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      (N : ℝ) * Real.exp (-((J + m : ℕ) : ℝ)) ≤ (S.card : ℝ) →
      ¬ (C * ((J + m : ℕ) : ℝ) ^ β + B' ≤ Real.log (Real.log (N : ℝ))) := by
    intro m
    induction m with
    | zero =>
      intro N S hN hS hfree hdens hbud
      simp only [Nat.add_zero] at hdens hbud
      have hlt := hterm N S hN hS hfree hdens
      have hpow : 0 ≤ C * (J : ℝ) ^ β := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg J) β)
      linarith
    | succ m ih =>
      intro N S hN hS hfree hdens hbud
      have hidx : J + (m + 1) = (J + m) + 1 := by omega
      rw [hidx] at hdens hbud
      have hbudB : C * (((J + m) + 1 : ℕ) : ℝ) ^ β + B ≤ Real.log (Real.log (N : ℝ)) := by
        linarith
      obtain ⟨a, q, M, hq, hM2, -, hUcard, hloss⟩ :=
        hstep (J + m) (Nat.le_add_right J m) N S hN hS hfree hdens hbudB
      let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
      have hUfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < 4, b + i * d ∈ U :=
        OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.progression_preimage_free
          (le_refl 4) hq hfree
      have hMbud : C * ((J + m : ℕ) : ℝ) ^ β + B' ≤ Real.log (Real.log (M : ℝ)) := by
        linarith
      exact ih M U hM2 (Finset.filter_subset _ _) hUfree hUcard hMbud
  let A : ℝ := (1 + 1 / β) / 2
  have h1β : 1 < 1 / β := (one_lt_div hβ0).mpr hβ1
  have hA1 : 1 < A := by dsimp [A]; linarith
  have hA0 : 0 < A := by linarith
  have hAβ : A * β < 1 := by
    have heq : A * β = (β + 1) / 2 := by dsimp [A]; field_simp
    linarith
  have hgap : 0 < 1 - A * β := by linarith
  refine ⟨A, 1, hA1, zero_lt_one, ?_⟩
  have hloglog : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hpow_neg : Tendsto (fun t : ℝ ↦ t ^ (-(1 - A * β))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hgap
  have hKpos : 0 < 2 * C * (2 : ℝ) ^ β := by positivity
  have hsmall : ∀ᶠ t : ℝ in atTop, t ^ (-(1 - A * β)) ≤ (2 * C * (2 : ℝ) ^ β)⁻¹ :=
    (hpow_neg.eventually (Iio_mem_nhds (inv_pos.mpr hKpos))).mono fun _ h ↦ h.le
  have hpowA : Tendsto (fun t : ℝ ↦ t ^ A) atTop atTop := tendsto_rpow_atTop hA0
  filter_upwards [eventually_ge_atTop 2, hloglog.eventually_ge_atTop 1,
    hloglog.eventually_ge_atTop (2 * B'), hloglog.eventually hsmall,
    (hpowA.comp hloglog).eventually_ge_atTop (J : ℝ)] with N hN2 ht1 htB hts hJ
  set t : ℝ := Real.log (Real.log (N : ℝ))
  have ht0 : 0 < t := by linarith
  have htA1 : 1 ≤ t ^ A := Real.one_le_rpow ht1 hA0.le
  let n : ℕ := ⌈t ^ A⌉₊
  have hn_ge : t ^ A ≤ (n : ℝ) := Nat.le_ceil _
  have hJn : J ≤ n := by
    have : (J : ℝ) ≤ (n : ℝ) := le_trans hJ hn_ge
    exact_mod_cast this
  have hn_le : (n : ℝ) ≤ 2 * t ^ A := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ t ^ A by linarith)
    dsimp [n]
    linarith
  have hterm1 : C * (n : ℝ) ^ β ≤ t / 2 := by
    have h1' : (n : ℝ) ^ β ≤ (2 * t ^ A) ^ β :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le hβ0.le
    have h2' : (2 * t ^ A) ^ β = (2 : ℝ) ^ β * t ^ (A * β) := by
      rw [Real.mul_rpow (by norm_num) (by linarith), ← Real.rpow_mul ht0.le]
    have h3' : t ^ (A * β) = t * t ^ (-(1 - A * β)) := by
      conv_lhs => rw [show A * β = 1 + -(1 - A * β) by ring]
      rw [Real.rpow_add ht0, Real.rpow_one]
    have h4' : C * ((2 : ℝ) ^ β * (t * t ^ (-(1 - A * β)))) ≤
        C * ((2 : ℝ) ^ β * (t * (2 * C * (2 : ℝ) ^ β)⁻¹)) := by
      have h2β : (0 : ℝ) ≤ (2 : ℝ) ^ β := by positivity
      gcongr
    have h5' : C * ((2 : ℝ) ^ β * (t * (2 * C * (2 : ℝ) ^ β)⁻¹)) = t / 2 := by
      have h2β : (2 : ℝ) ^ β ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) β).ne'
      field_simp [hC.ne', h2β]
    calc C * (n : ℝ) ^ β ≤ C * (2 * t ^ A) ^ β := mul_le_mul_of_nonneg_left h1' hC.le
      _ = C * ((2 : ℝ) ^ β * (t * t ^ (-(1 - A * β)))) := by rw [h2', h3']
      _ ≤ C * ((2 : ℝ) ^ β * (t * (2 * C * (2 : ℝ) ^ β)⁻¹)) := h4'
      _ = t / 2 := h5'
  have hbud : C * ((J + (n - J) : ℕ) : ℝ) ^ β + B' ≤ t := by
    rw [Nat.add_sub_of_le hJn]
    linarith
  obtain ⟨S, hS, hfree, hcard⟩ :=
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.extremizer (by decide : 1 < 4) N
  have hfree' :=
    OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.no_positive_step (by decide : 1 < 4) hfree
  have hlt : (S.card : ℝ) < (N : ℝ) * Real.exp (-(n : ℝ)) := by
    by_contra! hge
    have hge' : (N : ℝ) * Real.exp (-((J + (n - J) : ℕ) : ℝ)) ≤ (S.card : ℝ) := by
      rwa [Nat.add_sub_of_le hJn]
    exact no_dense (n - J) N S hN2 hS hfree' hge' hbud
  have hexp : Real.exp (-(n : ℝ)) ≤ Real.exp (-(1 : ℝ) * t ^ A) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [← hcard]
  calc (S.card : ℝ) ≤ (N : ℝ) * Real.exp (-(n : ℝ)) := hlt.le
    _ ≤ (N : ℝ) * Real.exp (-(1 : ℝ) * t ^ A) :=
        mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg N)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3
