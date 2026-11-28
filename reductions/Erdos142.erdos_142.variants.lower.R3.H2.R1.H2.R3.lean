import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3_H2_R1
import Mathlib

/-!
# Affine subprogression density increment with power-potential concavity for k = 4 and k >= 5

This reduction splits `OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1.H2` into two
affine subprogression density-increment hypotheses with sublinear length loss:
- `H1`: length `k = 4` (quadratic / U^3 regime)
- `H2`: length `k >= 5` (higher-order / U^{k-1} nilsequence regime)

In `main`, we construct the sublinear potential `F(x) = K * x ^ β` with `β = 1 - (ν - α) / 2`,
prove `0 ≤ F(x) ≤ x / 2 + D` for all `x ≥ 2` via weighted AM-GM, prove that affine
subprogression pullbacks preserve `k`-AP-freeness, and show by concavity of `x ↦ x ^ β`
that the drop `F(p) - F(p')` pays the `L * p ^ α` log-log length loss while yielding a
unit drop `p' + 1 ≤ p`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1_H2_R3

open Filter Real

/-- Sparse affine subprogression density increment for 4-AP-free sets with polynomial gain
and strictly smaller power log-log length loss. -/
def H1 : Prop :=
  ∃ (α ν c L K₀ T₀ B₀ : ℝ), 0 ≤ α ∧ α < ν ∧ ν < 1 ∧ 0 < c ∧ 0 < L ∧ 0 < K₀ ∧
    ∀ (N : ℕ) (S : Finset ℕ), 1 < N → S.Nonempty → S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      let p := max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
      T₀ < p → K₀ * p ^ (1 - (ν - α) / 2) + B₀ ≤ log (log (N : ℝ)) →
      ∃ a q M : ℕ, 0 < q ∧ 1 < M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
        let p' := max 2 (log (2 * (M : ℝ) / (U.card : ℝ)))
        U.Nonempty ∧ p' + c * p ^ ν ≤ p ∧
        log (log (N : ℝ)) - log (log (M : ℝ)) ≤ L * p ^ α

/-- Sparse affine subprogression density increment for k-AP-free sets (k >= 5) with polynomial
gain and strictly smaller power log-log length loss. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k →
    ∃ (α ν c L K₀ T₀ B₀ : ℝ), 0 ≤ α ∧ α < ν ∧ ν < 1 ∧ 0 < c ∧ 0 < L ∧ 0 < K₀ ∧
      ∀ (N : ℕ) (S : Finset ℕ), 1 < N → S.Nonempty → S ⊆ Finset.Icc 1 N →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
        T₀ < p → K₀ * p ^ (1 - (ν - α) / 2) + B₀ ≤ log (log (N : ℝ)) →
        ∃ a q M : ℕ, 0 < q ∧ 1 < M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
          let p' := max 2 (log (2 * (M : ℝ) / (U.card : ℝ)))
          U.Nonempty ∧ p' + c * p ^ ν ≤ p ∧
          log (log (N : ℝ)) - log (log (M : ℝ)) ≤ L * p ^ α

/-- Pulling back a `k`-AP-free set along a nontrivial affine progression preserves `k`-AP-freeness. -/
lemma pullback_ap_free {k a q M : ℕ} {S : Finset ℕ} (hq : 0 < q)
    (hfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k, b + i * d ∈ S) :
    ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k,
      b + i * d ∈ (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S) := by
  rintro ⟨b, d, hd, hmem⟩
  by_cases hk : k = 0
  · subst hk
    exact hfree ⟨0, 1, Nat.one_pos, fun i hi ↦ (Nat.not_lt_zero i hi).elim⟩
  have hb1 : 1 ≤ b := by
    have h0 := Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 0 (Nat.pos_of_ne_zero hk))).1
    simpa using h0.1
  refine hfree ⟨a + (b - 1) * q, d * q, Nat.mul_pos hd hq, fun i hi ↦ ?_⟩
  have hbi := (Finset.mem_filter.mp (hmem i hi)).2
  have hEq : a + (b + i * d - 1) * q = a + (b - 1) * q + i * (d * q) := by
    have hsub : b + i * d - 1 = (b - 1) + i * d := by omega
    rw [hsub, add_mul, ← add_assoc, mul_assoc]
  rwa [hEq] at hbi

/-- Concavity drop of `x ↦ x ^ β` for `0 < β < 1` and `0 < y ≤ x`. -/
lemma rpow_sub_rpow_ge {x y β : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    β * x ^ (β - 1) * (x - y) ≤ x ^ β - y ^ β := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have h1β : 0 ≤ 1 - β := by linarith
  have hAM := Real.geom_mean_le_arith_mean2_weighted hβ0 h1β (div_nonneg hy.le hx.le) zero_le_one
    (by ring)
  rw [Real.one_rpow, mul_one, mul_one, Real.div_rpow hy.le hx.le] at hAM
  have hmul := mul_le_mul_of_nonneg_right hAM (Real.rpow_nonneg hx.le β)
  rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hx β).ne'] at hmul
  have hdiv : (y / x) * x ^ β = y * x ^ (β - 1) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp [hx.ne']
  have hxp : x * x ^ (β - 1) = x ^ β := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp [hx.ne']
  have hlin : (β * (y / x) + (1 - β)) * x ^ β = x ^ β - β * x ^ (β - 1) * (x - y) := by
    calc
      (β * (y / x) + (1 - β)) * x ^ β
          = β * ((y / x) * x ^ β) + (1 - β) * x ^ β := by ring
      _ = β * (y * x ^ (β - 1)) + x ^ β - β * (x * x ^ (β - 1)) := by rw [hdiv, hxp]; ring
      _ = x ^ β - β * x ^ (β - 1) * (x - y) := by ring
  rw [hlin] at hmul
  linarith

/-- Any sublinear power `K * x ^ β` (`0 < β < 1`) is dominated by `x / 2 + D` on `[0, ∞)`. -/
lemma sublinear_rpow_le_half_add {K β : ℝ} (hK : 0 < K) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ D : ℝ, ∀ x : ℝ, 0 ≤ x → K * x ^ β ≤ x / 2 + D := by
  have h1β : 0 < 1 - β := by linarith
  let t : ℝ := 1 / (2 * β)
  have ht : 0 < t := by positivity
  let a : ℝ := (K / t ^ β) ^ (1 / (1 - β))
  have ha : 0 ≤ a := by positivity
  refine ⟨(1 - β) * a, fun x hx ↦ ?_⟩
  have htx : 0 ≤ t * x := mul_nonneg ht.le hx
  have hAM := Real.geom_mean_le_arith_mean2_weighted h1β.le hβ0.le ha htx (by ring)
  have ha_pow : a ^ (1 - β) = K / t ^ β := by
    dsimp [a]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ K / t ^ β), one_div_mul_cancel h1β.ne',
      Real.rpow_one]
  have htx_pow : (t * x) ^ β = t ^ β * x ^ β := Real.mul_rpow ht.le hx
  have hlhs : a ^ (1 - β) * (t * x) ^ β = K * x ^ β := by
    rw [ha_pow, htx_pow]
    field_simp [(Real.rpow_pos_of_pos ht β).ne']
  have hrhs : (1 - β) * a + β * (t * x) = x / 2 + (1 - β) * a := by
    have hβt : β * (t * x) = x / 2 := by
      dsimp [t]
      field_simp [hβ0.ne']
    linarith
  linarith

/-- Assemble the potential-descent step for a fixed length `k` from its affine density increment. -/
lemma step_of_increment {k : ℕ}
    (hinc : ∃ (α ν c L K₀ T₀ B₀ : ℝ), 0 ≤ α ∧ α < ν ∧ ν < 1 ∧ 0 < c ∧ 0 < L ∧ 0 < K₀ ∧
      ∀ (N : ℕ) (S : Finset ℕ), 1 < N → S.Nonempty → S ⊆ Finset.Icc 1 N →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
        T₀ < p → K₀ * p ^ (1 - (ν - α) / 2) + B₀ ≤ log (log (N : ℝ)) →
        ∃ a q M : ℕ, 0 < q ∧ 1 < M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
          let p' := max 2 (log (2 * (M : ℝ) / (U.card : ℝ)))
          U.Nonempty ∧ p' + c * p ^ ν ≤ p ∧
          log (log (N : ℝ)) - log (log (M : ℝ)) ≤ L * p ^ α) :
    ∃ (F : ℝ → ℝ) (T D Cmin : ℝ),
      (∀ x ≥ 2, 0 ≤ F x ∧ F x ≤ x / 2 + D) ∧
      let p := fun (N : ℕ) (S : Finset ℕ) ↦ max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
      let valid := fun (N : ℕ) (S : Finset ℕ) ↦ 1 < N ∧ S.Nonempty ∧ S ⊆ Finset.Icc 1 N ∧
        ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S
      ∀ C ≥ Cmin, ∀ (N : ℕ) (S : Finset ℕ), valid N S → T < p N S →
        F (p N S) + C ≤ log (log (N : ℝ)) → ∃ (M : ℕ) (B : Finset ℕ),
          valid M B ∧ F (p M B) + C ≤ log (log (M : ℝ)) ∧ p M B + 1 ≤ p N S := by
  obtain ⟨α, ν, c, L, K₀, T₀, B₀, hα0, hαν, hν1, hc, hL, hK₀, hstep⟩ := hinc
  let β : ℝ := 1 - (ν - α) / 2
  have hβ0 : 0 < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hν0 : 0 < ν := lt_of_le_of_lt hα0 hαν
  let K : ℝ := max K₀ (L / (β * c))
  have hK_pos : 0 < K := lt_of_lt_of_le hK₀ (le_max_left _ _)
  have hK₀_le : K₀ ≤ K := le_max_left _ _
  have hKL_le : L / (β * c) ≤ K := le_max_right _ _
  obtain ⟨D, hD⟩ := sublinear_rpow_le_half_add hK_pos hβ0 hβ1
  let T : ℝ := max T₀ ((1 / c) ^ (1 / ν))
  refine ⟨fun x ↦ K * x ^ β, T, D, B₀, ?_, ?_⟩
  · intro x hx
    refine ⟨mul_nonneg hK_pos.le (Real.rpow_nonneg (by linarith) β), hD x (by linarith)⟩
  · dsimp only
    intro C hC N S ⟨hN1, hSne, hSsub, hSfree⟩ hTp hbud
    set pN : ℝ := max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
    have hp2 : (2 : ℝ) ≤ pN := le_max_left _ _
    have hp_pos : 0 < pN := by linarith
    have hT₀p : T₀ < pN := lt_of_le_of_lt (le_max_left _ _) hTp
    have h1cp : (1 / c) ^ (1 / ν) < pN := lt_of_le_of_lt (le_max_right _ _) hTp
    have hbud₀ : K₀ * pN ^ β + B₀ ≤ log (log (N : ℝ)) := by
      have hKmul : K₀ * pN ^ β ≤ K * pN ^ β :=
        mul_le_mul_of_nonneg_right hK₀_le (Real.rpow_nonneg hp_pos.le β)
      linarith
    obtain ⟨a, q, M, hq, hM1, -, hUne, hgain, hloss⟩ :=
      hstep N S hN1 hSne hSsub hSfree hT₀p hbud₀
    let U : Finset ℕ := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
    set pM : ℝ := max 2 (log (2 * (M : ℝ) / (U.card : ℝ)))
    have hpM2 : (2 : ℝ) ≤ pM := le_max_left _ _
    have hpM_pos : 0 < pM := by linarith
    have hc_pow : 1 ≤ c * pN ^ ν := by
      have hpow : ((1 / c) ^ (1 / ν)) ^ ν ≤ pN ^ ν :=
        Real.rpow_le_rpow (by positivity) h1cp.le hν0.le
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / c), one_div_mul_cancel hν0.ne',
        Real.rpow_one] at hpow
      have hmul := mul_le_mul_of_nonneg_left hpow hc.le
      rwa [mul_one_div_cancel hc.ne'] at hmul
    have hpM_le : pM ≤ pN := by linarith
    have hdrop : β * pN ^ (β - 1) * (pN - pM) ≤ pN ^ β - pM ^ β :=
      rpow_sub_rpow_ge hpM_pos hpM_le hβ0.le hβ1.le
    have hdiff_ge : c * pN ^ ν ≤ pN - pM := by linarith
    have hexp_ge : α ≤ β - 1 + ν := by dsimp [β]; linarith
    have hp_exp : pN ^ α ≤ pN ^ (β - 1 + ν) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ pN) hexp_ge
    have hprod_pow : pN ^ (β - 1) * pN ^ ν = pN ^ (β - 1 + ν) :=
      (Real.rpow_add hp_pos (β - 1) ν).symm
    have hKβc : L ≤ K * β * c := by
      have hβc : 0 < β * c := mul_pos hβ0 hc
      have h1 := (div_le_iff₀ hβc).mp hKL_le
      linarith
    have hFdrop : L * pN ^ α ≤ K * pN ^ β - K * pM ^ β := by
      calc
        L * pN ^ α ≤ (K * β * c) * pN ^ (β - 1 + ν) :=
          mul_le_mul hKβc hp_exp (Real.rpow_nonneg hp_pos.le α) (by positivity)
        _ = K * (β * pN ^ (β - 1) * (c * pN ^ ν)) := by
          rw [← hprod_pow]; ring
        _ ≤ K * (β * pN ^ (β - 1) * (pN - pM)) := by
          apply mul_le_mul_of_nonneg_left _ hK_pos.le
          exact mul_le_mul_of_nonneg_left hdiff_ge (by positivity)
        _ ≤ K * (pN ^ β - pM ^ β) :=
          mul_le_mul_of_nonneg_left hdrop hK_pos.le
        _ = K * pN ^ β - K * pM ^ β := by ring
    refine ⟨M, U, ⟨hM1, hUne, Finset.filter_subset _ _, pullback_ap_free hq hSfree⟩, ?_, ?_⟩
    · linarith
    · linarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1.H2 := by
  intro h1 h2 k hk
  rcases eq_or_lt_of_le hk with rfl | hk5
  · exact step_of_increment h1
  · exact step_of_increment (h2 k hk5)

end OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1_H2_R3
