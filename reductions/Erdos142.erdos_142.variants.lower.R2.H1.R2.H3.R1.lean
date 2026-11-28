import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R2

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R2.H3.R1 of step Erdos142.erdos_142.variants.lower.R2.H1.R2.H3
-- Credit: @jktcv2kz4f-cyber

/-!
# Pigeonhole reduction of polylogarithmic van der Waerden progressions (k ≥ 4) to extremal density

We reduce monochromatic `k`-APs (`k ≥ 4`) in `[1, 4 ^ j]` with `(⌈log (4 ^ j)⌉₊ + 1) ^ 4`
colors (`R2.H1.R2.H3`) to the polylogarithmic extremal density bounds
`r k N < N / (⌈log N⌉₊ + 1) ^ 4`, split between `k = 4` (`H1`) and `k ≥ 5` (`H2`).

By the pigeonhole principle, whenever `q * r k N < N`, every `q`-coloring of `[1, N]` has
a color class of size strictly exceeding `r k N`, which therefore contains a `k`-term
arithmetic progression.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2_H3_R1

open Erdos142 Filter Real

/-- Polylogarithmic extremal density bound for 4-term arithmetic progressions. -/
def H1 : Prop :=
  ∀ᶠ N : ℕ in atTop,
    (r 4 N : ℝ) < (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)

/-- Polylogarithmic extremal density bound for k-term arithmetic progressions (k ≥ 5). -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∀ᶠ N : ℕ in atTop,
    (r k N : ℝ) < (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)

lemma mono_ap_of_density {k : ℕ} (hk : 2 ≤ k)
    (hdens : ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) < (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) :
    ∀ᶠ j : ℕ in atTop,
      ∀ c : ℕ → Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
        ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Finset.Icc 1 (4 ^ j) ∧ c (a + i * d) = c a := by
  have hT : Tendsto (fun j : ℕ => (4 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  filter_upwards [hT.eventually hdens] with j hj
  intro c
  let N : ℕ := 4 ^ j
  let q : ℕ := (⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4
  have hqpos : 0 < q := by positivity
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hmulR : (q : ℝ) * (r k N : ℝ) < (N : ℝ) := by
    have h1 := (lt_div_iff₀ hqR).mp hj
    linarith
  have hmulN : q * r k N < N := by exact_mod_cast hmulR
  have hcard : (Finset.univ : Finset (Fin q)).card * r k N < (Finset.Icc 1 N).card := by
    simpa [Nat.card_Icc] using hmulN
  obtain ⟨col, _, hcol⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := c) (fun n _ => Finset.mem_univ (c n)) hcard
  let S : Finset ℕ := (Finset.Icc 1 N).filter (fun n => c n = col)
  have hcolS : r k N < S.card := hcol
  have hSsub : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hnotfree : ¬ (S : Set ℕ).IsAPOfLengthFree k := by
    intro hfree
    have hle : S.card ≤ r k N :=
      OMA.R_Erdos142_erdos_142_variants_lower_R2.card_le_maxCard hSsub hfree
    omega
  have hex : ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
    by_contra hno
    exact hnotfree ((OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.isAPOfLengthFree_iff hk).mpr hno)
  obtain ⟨a, d, hd, hSAP⟩ := hex
  have haS : a ∈ (Finset.Icc 1 N).filter (fun n => c n = col) := by
    simpa [S] using hSAP 0 (by omega)
  have ha_col : c a = col := (Finset.mem_filter.mp haS).2
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have hmem := Finset.mem_filter.mp (show a + i * d ∈ (Finset.Icc 1 N).filter (fun n => c n = col) from hSAP i hi)
  exact ⟨hmem.1, hmem.2.trans ha_col.symm⟩

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.H3 := by
  intro h4 h5 k hk
  by_cases hk4 : k = 4
  · subst hk4
    exact mono_ap_of_density (by decide) h4
  · exact mono_ap_of_density (by omega) (h5 k (by omega))

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2_H3_R1
