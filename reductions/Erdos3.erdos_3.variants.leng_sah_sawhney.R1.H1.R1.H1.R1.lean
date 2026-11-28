import OMAReductions.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1

-- Reduction Erdos3.erdos_3.variants.leng_sah_sawhney.R1.H1.R1.H1.R1 of step
-- Erdos3.erdos_3.variants.leng_sah_sawhney.R1.H1.R1.H1
-- Credit: @arindale
--
-- H1 is the density-increment trichotomy of Leng, Sah and Sawhney
-- (arXiv:2402.17995, Lemma 3.7).  Its proof rests on the quasipolynomial
-- inverse theorem for the Gowers norms and on the nilsequence Schmidt
-- decomposition, neither of which is available in Mathlib.  We therefore
-- isolate the deep core: from a large interval and a count that deviates from
-- the constant-density model, produce a long arithmetic progression carrying a
-- fixed multiplicative density gain.  The elementary enlargement of the loss
-- polynomial (absorbing the paper's constants into ours) is H2.

namespace OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1_H1_R1

open Finset
open scoped Classical

/-- The deep core of the density-increment lemma: on a large interval, a
deviation of the `k`-term progression count from the constant-density model
forces a long arithmetic progression with a fixed multiplicative density gain. -/
def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k →
  ∃ c C0 : ℝ, ∃ D0 : ℕ, 0 < c ∧ 0 < C0 ∧
    ∀ (N : ℕ) (A : Finset ℕ), 3 ≤ N → 0 < A.card → A ⊆ Icc 1 N →
      let count (B : Finset ℕ) :=
        ((range (N + 1) ×ˢ range (N + 1)).filter
          (fun p => ∀ i < k, p.1 + i * p.2 ∈ B)).card
      let δ := (A.card : ℝ) / N
      let loss := C0 * (1 + Real.log ((N : ℝ) / A.card)) ^ D0
      let total := ((N : ℝ) + 1) ^ 2
      ¬ (N : ℝ) ≤ Real.exp (Real.exp loss) →
      ¬ |(count A : ℝ) / total - δ ^ k * count (Icc 1 N) / total| ≤ δ ^ k / (256 * k) →
      ∃ a d M : ℕ, 0 < d ∧
        (∀ i ∈ Icc 1 M, a + (i - 1) * d ∈ Icc 1 N) ∧
        (N : ℝ) ^ Real.exp (-loss) ≤ (M : ℝ) ∧
        (1 + c) * δ ≤ (((Icc 1 M).filter (fun i => a + (i - 1) * d ∈ A)).card : ℝ) / M

/-- Elementary enlargement of the loss polynomial: any constant and degree can
be dominated, uniformly on `[0, ∞)`, by a larger constant and degree. -/
def H2 : Prop :=
  ∀ c C0 : ℝ, ∀ D0 : ℕ, 0 < C0 →
    ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧
      ∀ g : ℝ, 0 ≤ g → C0 * (1 + g) ^ D0 ≤ C * (1 + g) ^ D

theorem main : H1 → H2 → OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1.H1 := by
  intro core enlarge k hk
  obtain ⟨c, C0, D0, hc, hC0, hcore⟩ := core k hk
  obtain ⟨C, D, hC, hbound⟩ := enlarge c C0 D0 hC0
  refine ⟨1 + c / 2, C, by linarith, hC, D, ?_⟩
  intro N A hN hApos hsub
  intro count δ loss total
  by_cases hsmall : (N : ℝ) ≤ Real.exp (Real.exp loss)
  · exact Or.inl hsmall
  by_cases hclose : |(count A : ℝ) / total - δ ^ k * count (Icc 1 N) / total| ≤
      δ ^ k / (256 * k)
  · exact Or.inr (Or.inl hclose)
  have hcard : A.card ≤ N := by simpa using card_le_card hsub
  have hAposR : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hApos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hg : 0 ≤ Real.log ((N : ℝ) / A.card) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hAposR]
    simpa using (show (A.card : ℝ) ≤ (N : ℝ) by exact_mod_cast hcard)
  have hlossle :
      C0 * (1 + Real.log ((N : ℝ) / A.card)) ^ D0 ≤
        C * (1 + Real.log ((N : ℝ) / A.card)) ^ D := hbound _ hg
  have hsmall0 :
      ¬ (N : ℝ) ≤
        Real.exp (Real.exp (C0 * (1 + Real.log ((N : ℝ) / A.card)) ^ D0)) := by
    intro h
    apply hsmall
    exact h.trans (Real.exp_le_exp_of_le (Real.exp_le_exp_of_le hlossle))
  have hcore' := hcore N A hN hApos hsub
  dsimp only at hcore'
  obtain ⟨a, d, M, hd, hAP, hlen, hdens⟩ := hcore' hsmall0 hclose
  refine Or.inr (Or.inr ⟨a, d, M, hd, hAP, ?_, ?_⟩)
  · have hexp :
        Real.exp (-(C * (1 + Real.log ((N : ℝ) / A.card)) ^ D)) ≤
          Real.exp (-(C0 * (1 + Real.log ((N : ℝ) / A.card)) ^ D0)) :=
      Real.exp_le_exp_of_le (by linarith)
    have hrpow :
        (N : ℝ) ^ Real.exp (-(C * (1 + Real.log ((N : ℝ) / A.card)) ^ D)) ≤
          (N : ℝ) ^ Real.exp (-(C0 * (1 + Real.log ((N : ℝ) / A.card)) ^ D0)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hexp
    exact hrpow.trans hlen
  · have hdpos : 0 < δ := div_pos hAposR hNpos
    exact (mul_le_mul_of_nonneg_right (by linarith : (1 + c / 2) ≤ 1 + c) hdpos.le).trans hdens

end OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1_H1_R1
