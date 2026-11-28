import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2
import Mathlib

/-!
# Unit-step to halving density increment via affine composition and strong induction

This reduction reduces the halving square-root density increment for `k >= 6`
(`p' ≤ p / 2`, log-log loss `≤ D * √p`) to a single-step unit log-density increment
(`p' + 1 ≤ p`, log-log loss `≤ D₀ / √p`), split into `k = 6` (`H1`) and `k >= 7` (`H2`).

In `main`, we prove:
1. Composition of affine subprogressions (`i ↦ a + (i - 1) * q`) preserves interval
   containment, pullback filter sets, and `k`-AP-freeness.
2. Strong induction on `⌊p⌋₊` iterates the unit-step increment while `p_curr > p₀ / 2`,
   charging each step's loss `D₀ / √p_curr ≤ (√2 * D₀ / √p₀) * (p_curr - p_next)` to a
   telescoping upper bound `(√2 * D₀ / √p₀) * (p₀ - p_final) ≤ 2 * D₀ * √p₀`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2_H2_R1

open Filter Real

/-- Single-step unit density increment for 6-AP-free sets with inverse-square-root log-log loss. -/
def H1 : Prop :=
  ∃ D₀ L₀ T₀ : ℝ, 0 < D₀ ∧ ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 6, a + i * d ∈ S) →
    let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
    T₀ < p → L₀ * Real.sqrt p ≤ Real.log (Real.log (N : ℝ)) →
    ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
      (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
      let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
      let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
      0 < U.card ∧ p' + 1 ≤ p ∧
        Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + D₀ / Real.sqrt p

/-- Single-step unit density increment for k-AP-free sets (k >= 7) with inverse-square-root loss. -/
def H2 : Prop :=
  ∀ k : ℕ, 7 ≤ k → ∃ D₀ L₀ T₀ : ℝ, 0 < D₀ ∧ ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
    let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
    T₀ < p → L₀ * Real.sqrt p ≤ Real.log (Real.log (N : ℝ)) →
    ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
      (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
      let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
      let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
      0 < U.card ∧ p' + 1 ≤ p ∧
        Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + D₀ / Real.sqrt p

/-- Pulling back a `k`-AP-free set along a nontrivial affine progression preserves `k`-AP-freeness. -/
lemma pullback_free {k a q M : ℕ} {S : Finset ℕ} (hk : 0 < k) (hq : 0 < q)
    (hfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k, b + i * d ∈ S) :
    ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k,
      b + i * d ∈ (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S) := by
  rintro ⟨b, d, hd, hmem⟩
  have hb1 : 1 ≤ b := by
    have h0 := Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 0 hk)).1
    simpa using h0.1
  refine hfree ⟨a + (b - 1) * q, d * q, Nat.mul_pos hd hq, fun i hi ↦ ?_⟩
  have hbi := (Finset.mem_filter.mp (hmem i hi)).2
  have hEq : a + (b + i * d - 1) * q = a + (b - 1) * q + i * (d * q) := by
    have hsub : b + i * d - 1 = (b - 1) + i * d := by omega
    rw [hsub, add_mul, ← add_assoc, mul_assoc]
  rwa [hEq] at hbi

/-- Composition of two affine subprogressions on `[1, N]` and `[1, M]`. -/
lemma compose_affine {N M M' a q a' q' : ℕ}
    (h1 : ∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N)
    (h2 : ∀ j ∈ Finset.Icc 1 M', a' + (j - 1) * q' ∈ Finset.Icc 1 M)
    (hM' : 1 ≤ M') :
    (∀ j ∈ Finset.Icc 1 M', a + (a' - 1) * q + (j - 1) * (q * q') ∈ Finset.Icc 1 N) ∧
    ∀ S : Finset ℕ,
      (Finset.Icc 1 M').filter (fun j ↦ a + (a' - 1) * q + (j - 1) * (q * q') ∈ S) =
      (Finset.Icc 1 M').filter (fun j ↦
        a' + (j - 1) * q' ∈ (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)) := by
  have ha'1 : 1 ≤ a' := by
    have h0 := Finset.mem_Icc.mp (h2 1 (Finset.mem_Icc.mpr ⟨le_rfl, hM'⟩))
    simpa using h0.1
  have hformula : ∀ j : ℕ,
      a + (a' - 1) * q + (j - 1) * (q * q') = a + (a' + (j - 1) * q' - 1) * q := by
    intro j
    have hsub : a' + (j - 1) * q' - 1 = (a' - 1) + (j - 1) * q' := by omega
    rw [hsub, add_mul, ← add_assoc]
    ring
  constructor
  · intro j hj
    rw [hformula j]
    exact h1 (a' + (j - 1) * q') (h2 j hj)
  · intro S
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, hmem⟩
      rw [hformula j] at hmem
      exact ⟨hj, h2 j hj, hmem⟩
    · rintro ⟨hj, -, hmem⟩
      rw [hformula j]
      exact ⟨hj, hmem⟩

/-- Iterating a unit-step increment halves `p` while accumulating at most `2 * D₀ * √p` loss. -/
lemma halve_of_unit_step {k : ℕ} (hk : 0 < k)
    (hunit : ∃ D₀ L₀ T₀ : ℝ, 0 < D₀ ∧ ∀ (N : ℕ) (S : Finset ℕ),
      2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T₀ < p → L₀ * Real.sqrt p ≤ Real.log (Real.log (N : ℝ)) →
      ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
        let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
        0 < U.card ∧ p' + 1 ≤ p ∧
          Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + D₀ / Real.sqrt p) :
    ∃ D L T : ℝ, 0 < D ∧ ∀ (N : ℕ) (S : Finset ℕ),
      2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T < p → L * Real.sqrt p ≤ Real.log (Real.log (N : ℝ)) →
      ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
        let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
        0 < U.card ∧ p' ≤ p / 2 ∧
          Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + D * Real.sqrt p := by
  obtain ⟨D₀, L₀, T₀, hD₀, hstep⟩ := hunit
  refine ⟨2 * D₀, max L₀ 0 + 2 * D₀, max (2 * T₀) 4, by positivity, ?_⟩
  intro N S hN2 hSsub hScard hSfree
  dsimp only
  set p₀ : ℝ := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
  intro hTp hbud
  have hp₀_gt4 : 4 < p₀ := lt_of_le_of_lt (le_max_right _ _) hTp
  have hp₀_gt2T₀ : 2 * T₀ < p₀ := lt_of_le_of_lt (le_max_left _ _) hTp
  have hp₀_pos : 0 < p₀ := by linarith
  have hsqrt_half_pos : 0 < Real.sqrt (p₀ / 2) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt_p₀_pos : 0 < Real.sqrt p₀ := Real.sqrt_pos.mpr hp₀_pos
  let Cstep : ℝ := D₀ / Real.sqrt (p₀ / 2)
  have hCstep_pos : 0 < Cstep := div_pos hD₀ hsqrt_half_pos
  have hCstep_mul : Cstep * p₀ ≤ 2 * D₀ * Real.sqrt p₀ := by
    have hrt : Real.sqrt (p₀ / 2) = Real.sqrt p₀ / Real.sqrt 2 :=
      Real.sqrt_div hp₀_pos.le 2
    have hsq2_le : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hsq_sq : Real.sqrt p₀ * Real.sqrt p₀ = p₀ := Real.mul_self_sqrt hp₀_pos.le
    have hEq : Cstep * p₀ = D₀ * Real.sqrt 2 * Real.sqrt p₀ := by
      dsimp [Cstep]
      rw [hrt]
      have hsq2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      field_simp [hsqrt_p₀_pos.ne', hsq2_ne]
      nlinarith [hsq_sq]
    rw [hEq]
    calc
      D₀ * Real.sqrt 2 * Real.sqrt p₀ ≤ D₀ * 2 * Real.sqrt p₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq2_le hD₀.le) hsqrt_p₀_pos.le
      _ = 2 * D₀ * Real.sqrt p₀ := by ring
  have hIter : ∀ n : ℕ, ∀ (a q M : ℕ),
      0 < q → 2 ≤ M → (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) →
      let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
      let pU := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
      0 < U.card → pU ≤ p₀ → ⌊pU⌋₊ = n →
      Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + Cstep * (p₀ - pU) →
      ∃ a' q' M' : ℕ, 0 < q' ∧ 2 ≤ M' ∧
        (∀ i ∈ Finset.Icc 1 M', a' + (i - 1) * q' ∈ Finset.Icc 1 N) ∧
        let U' := (Finset.Icc 1 M').filter (fun i ↦ a' + (i - 1) * q' ∈ S)
        let pU' := max 2 (Real.log (2 * (M' : ℝ) / (U'.card : ℝ)))
        0 < U'.card ∧ pU' ≤ p₀ / 2 ∧
          Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M' : ℝ)) + 2 * D₀ * Real.sqrt p₀ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a q M hq hM2 hAff
      dsimp only
      set U : Finset ℕ := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
      set pU : ℝ := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
      intro hUcard hpU_le hfloor hloss
      by_cases hdone : pU ≤ p₀ / 2
      · refine ⟨a, q, M, hq, hM2, hAff, hUcard, hdone, ?_⟩
        have hpU_nonneg : 0 ≤ pU := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)
        have h1 : Cstep * (p₀ - pU) ≤ Cstep * p₀ := by nlinarith
        linarith
      · push Not at hdone
        have hT₀_lt : T₀ < pU := by linarith
        have hUfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k, b + i * d ∈ U :=
          pullback_free hk hq hSfree
        have hUsub : U ⊆ Finset.Icc 1 M := Finset.filter_subset _ _
        have hsqrtU_le : Real.sqrt pU ≤ Real.sqrt p₀ := Real.sqrt_le_sqrt hpU_le
        have hbudU : L₀ * Real.sqrt pU ≤ Real.log (Real.log (M : ℝ)) := by
          have hpU_nonneg : 0 ≤ pU := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)
          have hloss_tot : Cstep * (p₀ - pU) ≤ 2 * D₀ * Real.sqrt p₀ := by nlinarith
          have hL0 : L₀ * Real.sqrt pU ≤ max L₀ 0 * Real.sqrt p₀ := by
            calc
              L₀ * Real.sqrt pU ≤ max L₀ 0 * Real.sqrt pU :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
              _ ≤ max L₀ 0 * Real.sqrt p₀ :=
                mul_le_mul_of_nonneg_left hsqrtU_le (le_max_right _ _)
          linarith
        obtain ⟨a', q', M', hq', hM'2, hAff', hU'card, hpU'drop, hloss'⟩ :=
          hstep M U hM2 hUsub hUcard hUfree hT₀_lt hbudU
        obtain ⟨hCompAff, hCompFilt⟩ := compose_affine hAff hAff' (by omega)
        set U' : Finset ℕ := (Finset.Icc 1 M').filter
          (fun j ↦ a + (a' - 1) * q + (j - 1) * (q * q') ∈ S)
        have hU'eq : U' = (Finset.Icc 1 M').filter (fun j ↦ a' + (j - 1) * q' ∈ U) := hCompFilt S
        set pU' : ℝ := max 2 (Real.log (2 * (M' : ℝ) / (U'.card : ℝ)))
        have hpU'_drop' : pU' + 1 ≤ pU := by
          dsimp only [pU']; rw [hU'eq]; exact hpU'drop
        have hU'card' : 0 < U'.card := by rw [hU'eq]; exact hU'card
        have hpU'_nonneg : 0 ≤ pU' := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)
        have hfl_lt : ⌊pU'⌋₊ < n := by
          have hle := Nat.floor_mono hpU'_drop'
          rw [Nat.floor_add_one hpU'_nonneg, hfloor] at hle
          omega
        have hstep_loss : D₀ / Real.sqrt pU ≤ Cstep * (pU - pU') := by
          have h1 : D₀ / Real.sqrt pU ≤ Cstep := by
            dsimp [Cstep]
            exact div_le_div_of_nonneg_left hD₀.le hsqrt_half_pos (Real.sqrt_le_sqrt hdone.le)
          nlinarith
        have hnew_loss : Real.log (Real.log (N : ℝ)) ≤
            Real.log (Real.log (M' : ℝ)) + Cstep * (p₀ - pU') := by
          linarith
        exact ih ⌊pU'⌋₊ hfl_lt (a + (a' - 1) * q) (q * q') M' (Nat.mul_pos hq hq') hM'2 hCompAff
          hU'card' (by linarith) rfl hnew_loss
  have hInitFilt : (Finset.Icc 1 N).filter (fun i ↦ 1 + (i - 1) * 1 ∈ S) = S := by
    ext i
    simp only [Finset.mem_filter, mul_one]
    constructor
    · rintro ⟨hi, hmem⟩
      have hi1 := (Finset.mem_Icc.mp hi).1
      have : 1 + (i - 1) = i := by omega
      rwa [this] at hmem
    · intro hi
      have hiIcc := hSsub hi
      have hi1 := (Finset.mem_Icc.mp hiIcc).1
      have : 1 + (i - 1) = i := by omega
      exact ⟨hiIcc, by rwa [this]⟩
  have hInitAff : ∀ i ∈ Finset.Icc 1 N, 1 + (i - 1) * 1 ∈ Finset.Icc 1 N := by
    intro i hi
    have hi1 := (Finset.mem_Icc.mp hi).1
    have heq : 1 + (i - 1) * 1 = i := by omega
    rw [heq]
    exact hi
  exact hIter ⌊p₀⌋₊ 1 1 N Nat.one_pos hN2 hInitAff
    (by rw [hInitFilt]; exact hScard)
    (by rw [hInitFilt])
    (by rw [hInitFilt])
    (by rw [hInitFilt]; simp [p₀])

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2.H2 := by
  intro h6 h7 k hk
  rcases eq_or_lt_of_le hk with rfl | hk7
  · exact halve_of_unit_step (by decide : 0 < 6) h6
  · exact halve_of_unit_step (by omega) (h7 k hk7)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2_H2_R1
