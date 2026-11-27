import OMAStatements.S_opg_inequality_for_square_summable_complex_series
import Mathlib

/-!
# Retkes’s inequality for square-summable complex series

The proof uses the partition of the positive integers into dyadic classes,
Cauchy–Schwarz on each class, and the Basel sum.
See https://doi.org/10.4171/EM/278.
-/

open scoped BigOperators

namespace Retkes

private def dyadicIndex (p : ℕ × ℕ) : ℕ :=
  2 ^ p.1 * (2 * p.2 + 1) - 1

private theorem dyadicIndex_succ (p : ℕ × ℕ) :
    dyadicIndex p + 1 = 2 ^ p.1 * (2 * p.2 + 1) := by
  have h : 0 < 2 ^ p.1 * (2 * p.2 + 1) := by positivity
  unfold dyadicIndex
  omega

private theorem dyadicIndex_bijective : Function.Bijective dyadicIndex := by
  constructor
  · intro p q he
    have hpq := (dyadicIndex_succ p).symm.trans
      ((congrArg (· + 1) he).trans (dyadicIndex_succ q))
    have hpadic (k l : ℕ) : padicValNat 2 (2 ^ k * (2 * l + 1)) = k := by
      rw [padicValNat_base_pow_mul (by decide : 1 < 2) (by omega : 2 * l + 1 ≠ 0),
        padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * l + 1), zero_add]
    have hfst : p.1 = q.1 := by
      simpa only [hpadic] using congrArg (padicValNat 2) hpq
    rw [hfst] at hpq
    have hsnd := Nat.eq_of_mul_eq_mul_left (by positivity) hpq
    exact Prod.ext hfst (by omega)
  · intro n
    let m := n + 1
    let k := padicValNat 2 m
    let r := m.divMaxPow 2
    have hn : ¬ 2 ∣ r := Nat.not_dvd_divMaxPow (by decide) (by omega : m ≠ 0)
    have hr : 2 * (r / 2) + 1 = r := by omega
    refine ⟨(k, r / 2), ?_⟩
    unfold dyadicIndex
    change 2 ^ k * (2 * (r / 2) + 1) - 1 = n
    rw [hr, Nat.pow_padicValNat_mul_divMaxPow]
    exact Nat.add_sub_cancel n 1

private noncomputable def dyadicEquiv : ℕ × ℕ ≃ ℕ :=
  Equiv.ofBijective dyadicIndex dyadicIndex_bijective

/-- Cauchy–Schwarz for a sum of complex products with square-summable factors. -/
private theorem norm_tsum_mul_sq_le (u : ℕ → ℝ) (v : ℕ → ℂ)
    (hu : Summable (fun i => u i ^ 2)) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ‖∑' i, (u i : ℂ) * v i‖ ^ 2 ≤ (∑' i, u i ^ 2) * (∑' i, ‖v i‖ ^ 2) := by
  have hnorm (i : ℕ) : ‖(u i : ℂ) * v i‖ = |u i| * ‖v i‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hmajor : Summable (fun i => (u i ^ 2 + ‖v i‖ ^ 2) * (1 / 2 : ℝ)) :=
    (hu.add hv).mul_right _
  have hprodNorm : Summable (fun i => ‖(u i : ℂ) * v i‖) := by
    apply hmajor.of_nonneg_of_le (fun i => norm_nonneg _)
    intro i
    rw [hnorm]
    nlinarith [sq_nonneg (|u i| - ‖v i‖), sq_abs (u i)]
  have hfinite (n : ℕ) :
      (∑ i ∈ Finset.range n, ‖(u i : ℂ) * v i‖) ^ 2 ≤
        (∑ i ∈ Finset.range n, u i ^ 2) * (∑ i ∈ Finset.range n, ‖v i‖ ^ 2) := by
    simp only [hnorm]
    simpa only [sq_abs] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) (fun i => |u i|) (fun i => ‖v i‖)
  have hlim := le_of_tendsto_of_tendsto
    (hprodNorm.hasSum.tendsto_sum_nat.pow 2)
    (hu.hasSum.tendsto_sum_nat.mul hv.hasSum.tendsto_sum_nat)
    (Filter.Eventually.of_forall hfinite)
  have hnormle := norm_tsum_le_tsum_norm hprodNorm
  exact (pow_le_pow_left₀ (norm_nonneg _) hnormle _).trans hlim

theorem main : ∀ a : ℕ → ℂ, Summable (fun n : ℕ => ‖a (n + 1)‖ ^ 2) →
    (6 / Real.pi ^ 2) *
        (∑' k : ℕ, ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2) ≤
      ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 := by
  intro a ha
  let f (n : ℕ) := ‖a (n + 1)‖ ^ 2
  let g (p : ℕ × ℕ) := ‖a (2 ^ p.1 * (2 * p.2 + 1))‖ ^ 2
  have hfg (p : ℕ × ℕ) : f (dyadicEquiv p) = g p := by
    simp only [f, g, dyadicEquiv, Equiv.ofBijective_apply, dyadicIndex_succ]
  have hg : Summable g := by
    have hc : Summable (fun p => f (dyadicEquiv p)) := ha.comp_injective dyadicEquiv.injective
    exact hc.congr hfg
  have hsumg : (∑' p, g p) = ∑' n, f n := by
    simpa only [hfg] using dyadicEquiv.tsum_eq f
  have hrow (k : ℕ) : Summable (fun l => g (k, l)) := hg.prod_factor k
  have hbasel : HasSum (fun l : ℕ => (((l : ℝ) + 1)⁻¹) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa [one_div, inv_pow] using h
  let w (k : ℕ) := ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2
  have hw (k : ℕ) : w k ≤ (Real.pi ^ 2 / 6) * ∑' l, g (k, l) := by
    have h := norm_tsum_mul_sq_le (fun l => ((l : ℝ) + 1)⁻¹)
      (fun l => a (2 ^ k * (2 * l + 1))) hbasel.summable (hrow k)
    rw [hbasel.tsum_eq] at h
    simpa [w, g] using h
  have hsf : Summable (fun k => ∑' l, g (k, l)) := hg.prod
  have hsm := hsf.mul_left (Real.pi ^ 2 / 6)
  have hsw : Summable w := hsm.of_nonneg_of_le (fun k => sq_nonneg _) hw
  have hwg : (∑' k, w k) ≤ (Real.pi ^ 2 / 6) * ∑' n, f n := by
    calc
      (∑' k, w k) ≤ ∑' k, (Real.pi ^ 2 / 6) * ∑' l, g (k, l) :=
        hsw.tsum_le_tsum hw hsm
      _ = (Real.pi ^ 2 / 6) * ∑' p, g p := by
        rw [tsum_mul_left, hg.tsum_prod]
      _ = (Real.pi ^ 2 / 6) * ∑' n, f n := by rw [hsumg]
  change (6 / Real.pi ^ 2) * (∑' k, w k) ≤ ∑' n, f n
  calc
    _ ≤ (6 / Real.pi ^ 2) * ((Real.pi ^ 2 / 6) * ∑' n, f n) :=
      mul_le_mul_of_nonneg_left hwg (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero]

end Retkes

theorem OMA.solution :
    type_of% @OMA.S_opg_inequality_for_square_summable_complex_series.main :=
  Retkes.main
