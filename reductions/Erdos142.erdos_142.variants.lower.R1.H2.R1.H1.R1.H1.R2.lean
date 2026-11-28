import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1.R2 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1
-- Credit: @DPS0340

/-!
# Multicolor 4-AP van der Waerden + shift covering reduction for r_4(N)

We reduce the `k = 4` super-polylogarithmic bound
`r 4 N ≤ N * exp (-c * (log log N) ^ A)` (`A > 1`)
to two independent combinatorial statements:
- `H1`: a super-polylogarithmic multicolor van der Waerden bound for 4-term arithmetic
  progressions on `[1, N]` with `⌈exp (c * (log log N) ^ A)⌉` colors;
- `H2`: a finite shift-covering lemma showing that any `S ⊆ [1, N]` with
  `2 * N * log N < q * |S|` covers `[N + 1, 2 * N]` by `q` translates.

Coloring `x ∈ [1, N]` by the index of a translate covering `x + N` turns any monochromatic
4-term progression in `[1, N]` into a 4-term progression inside `S`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2

open Finset Filter Real Erdos142
open scoped Topology

/-- Every coloring of [1, N] with ⌈exp (c * (log log N) ^ A)⌉ colors eventually contains
a monochromatic nontrivial 4-term arithmetic progression. -/
def H1 : Prop :=
  ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    ∀ col : ℕ → Fin ⌈Real.exp (c * Real.log (Real.log (N : ℝ)) ^ A)⌉₊,
      ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ Finset.Icc 1 N ∧ col (a + i * d) = col a

/-- Any subset S of [1, N] with 2 * N * log N < q * |S| covers [N + 1, 2 * N]
using at most q translates. -/
def H2 : Prop :=
  ∀ (N q : ℕ) (S : Finset ℕ), 0 < N → 0 < q → S ⊆ Finset.Icc 1 N →
    2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ) →
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Finset.Icc 1 N,
      ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b

lemma exists_maximizer_4 (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree 4 ∧ r 4 N = S.card := by
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree 4, S.card = m}
  have hz : 0 ∈ C := ⟨∅, empty_subset _, fun T hT h => (Set.not_isAPOfLength_empty
    (by decide : (0 : ℕ∞) < 4)
    (Set.subset_empty_iff.mp (by simpa using hT) ▸ h)).elim, rfl⟩
  have hb : BddAbove C := ⟨N, by rintro _ ⟨U, hU, -, rfl⟩; simpa using card_le_card hU⟩
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  exact ⟨S, hS, hf, he.symm⟩

lemma not_free_4_of_ap {S : Finset ℕ} {b d : ℕ} (hd : 0 < d)
    (hmem : ∀ i < 4, b + i * d ∈ S) : ¬ (S : Set ℕ).IsAPOfLengthFree 4 := by
  intro hf
  let T := (range 4).image (fun i => b + i * d)
  have hcard : T.card = 4 := by
    rw [card_image_of_injective _ (fun i j e => Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel e)),
      card_range]
  have hsub : (T : Set ℕ) ⊆ (S : Set ℕ) := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    exact hmem i (mem_range.mp hi)
  have hle : (4 : ℕ∞) ≤ 1 := hf _ hsub ⟨b, d, by simp [hcard], by ext y; simp [T]⟩
  exact (by decide : ¬ (4 : ℕ∞) ≤ 1) hle

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1.H1 := by
  classical
  intro h1 h2
  obtain ⟨A, c, hA, hc, hvdw⟩ := h1
  refine ⟨A, c / 2, hA, half_pos hc, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlim : Tendsto (fun x : ℝ => Real.log 2 * x ^ (-A) + x ^ (-(A - 1))) atTop (𝓝 0) := by
    have ha := (tendsto_rpow_neg_atTop (by linarith : 0 < A)).const_mul (Real.log 2)
    have hb := tendsto_rpow_neg_atTop (by linarith : 0 < A - 1)
    simpa using ha.add hb
  filter_upwards [hvdw, eventually_ge_atTop (4 : ℕ),
    hlog.eventually (eventually_gt_atTop (1 : ℝ)),
    hll.eventually (eventually_gt_atTop (0 : ℝ)),
    (hlim.comp hll).eventually (gt_mem_nhds (half_pos hc))]
    with N hcol hN4 hlog1 hllpos hsmall
  by_contra hgt
  push Not at hgt
  obtain ⟨S, hS, hf, hcard⟩ := exists_maximizer_4 N
  set x : ℝ := Real.log (Real.log (N : ℝ))
  let q : ℕ := ⌈Real.exp (c * x ^ A)⌉₊
  have hqpos : 0 < q := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hlog_lt : Real.log 2 + x < (c / 2) * x ^ A := by
    change Real.log 2 * x ^ (-A) + x ^ (-(A - 1)) < c / 2 at hsmall
    have hxa : 0 < x ^ A := Real.rpow_pos_of_pos hllpos A
    have hmul := mul_lt_mul_of_pos_right hsmall hxa
    have hlhs : (Real.log 2 * x ^ (-A) + x ^ (-(A - 1))) * x ^ A = Real.log 2 + x := by
      rw [add_mul, mul_assoc, ← Real.rpow_add hllpos, ← Real.rpow_add hllpos]
      have e1 : -A + A = 0 := by ring
      have e2 : -(A - 1) + A = 1 := by ring
      rw [e1, e2, Real.rpow_zero, Real.rpow_one, mul_one]
    linarith
  have hcov_ineq : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ) := by
    have hq_ge : Real.exp (c * x ^ A) ≤ (q : ℝ) := Nat.le_ceil _
    have hS_gt : (N : ℝ) * Real.exp (-(c / 2) * x ^ A) < (S.card : ℝ) := by
      rwa [← hcard]
    have h2log : 2 * Real.log (N : ℝ) < Real.exp ((c / 2) * x ^ A) := by
      calc 2 * Real.log (N : ℝ)
          = Real.exp (Real.log 2) * Real.exp x := by
            rw [Real.exp_log (by norm_num), Real.exp_log (by linarith)]
        _ = Real.exp (Real.log 2 + x) := (Real.exp_add _ _).symm
        _ < Real.exp ((c / 2) * x ^ A) := Real.exp_lt_exp.mpr hlog_lt
    have hexp_mul : Real.exp (c * x ^ A) * Real.exp (-(c / 2) * x ^ A) =
        Real.exp ((c / 2) * x ^ A) := by
      rw [← Real.exp_add]; congr 1; ring
    calc 2 * (N : ℝ) * Real.log (N : ℝ)
        = (N : ℝ) * (2 * Real.log (N : ℝ)) := by ring
      _ < (N : ℝ) * Real.exp ((c / 2) * x ^ A) := mul_lt_mul_of_pos_left h2log hNR
      _ = Real.exp (c * x ^ A) * ((N : ℝ) * Real.exp (-(c / 2) * x ^ A)) := by
          rw [← hexp_mul]; ring
      _ < Real.exp (c * x ^ A) * (S.card : ℝ) := mul_lt_mul_of_pos_left hS_gt (Real.exp_pos _)
      _ ≤ (q : ℝ) * (S.card : ℝ) := mul_le_mul_of_nonneg_right hq_ge (Nat.cast_nonneg _)
  obtain ⟨shifts, hshifts⟩ := h2 N q S hNpos hqpos hS hcov_ineq
  let col : ℕ → Fin q := fun y =>
    if hy : y ∈ Icc 1 N then (hshifts y hy).choose else ⟨0, hqpos⟩
  have hcol_spec : ∀ y (hy : y ∈ Icc 1 N), ∃ b ∈ S, y + N = shifts (col y) + b := fun y hy => by
    simpa only [col, dif_pos hy] using (hshifts y hy).choose_spec
  obtain ⟨a, d, hd, hap⟩ := hcol col
  have ha : a ∈ Icc 1 N := by simpa using (hap 0 (by omega)).1
  obtain ⟨b₀, _, hb₀⟩ := hcol_spec a ha
  apply not_free_4_of_ap (b := b₀) hd _ hf
  intro i hi
  obtain ⟨bi, hbiS, hbiEq⟩ := hcol_spec (a + i * d) (hap i hi).1
  rw [(hap i hi).2] at hbiEq
  have hterm : b₀ + i * d = bi := by omega
  rwa [hterm]

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2
