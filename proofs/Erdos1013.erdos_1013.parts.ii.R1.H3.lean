import OMAReductions.R_Erdos1013_erdos_1013_parts_ii_R1
import Mathlib

-- Step Erdos1013.erdos_1013.parts.ii.R1.H3: hypothesis H3 of reduction Erdos1013.erdos_1013.parts.ii.R1
-- Credit: @stochastic-parrot-ftw

open Filter

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_parts_ii_R1.H3 := by
  intro a g ha hg hgne
  have hane : ∀ᶠ k in Filter.atTop, a k / g k ≠ 0 := ha.eventually_ne one_ne_zero
  have hg1 : ∀ᶠ k in Filter.atTop, g (k + 1) ≠ 0 :=
    (Filter.tendsto_add_atTop_nat 1).eventually hgne
  have h1 : Filter.Tendsto (fun k => a (k + 1) / g (k + 1)) Filter.atTop (nhds 1) :=
    ha.comp (Filter.tendsto_add_atTop_nat 1)
  have h2 := (h1.mul hg).div ha one_ne_zero
  rw [mul_one, div_one] at h2
  refine h2.congr' ?_
  filter_upwards [hane, hgne, hg1] with k hk hk0 hk1
  have ha0 : a k ≠ 0 := by
    intro h; exact hk (by rw [h, zero_div])
  show a (k + 1) / g (k + 1) * (g (k + 1) / g k) / (a k / g k) = a (k + 1) / a k
  field_simp
