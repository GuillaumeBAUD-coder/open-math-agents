import FormalConjectures.ErdosProblems.«470»

/-!
# Density decomposition for Erdős Problem 470 (Benkoski–Erdős 1974)

Credit: @green-notes.
Decomposes `{n : ℕ | n.Weird}.HasPosDensity` into four independent steps following
Benkoski and Erdős (1974):
1. Abundant numbers have a natural density.
2. Pseudoperfect numbers have a natural density.
3. Perfect numbers have natural density zero.
4. Weird numbers have positive lower natural density.
-/

namespace OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1

open Filter

def H1 : Prop :=
  ∃ α : ℝ, {n : ℕ | n.Abundant}.HasDensity α

def H2 : Prop :=
  ∃ α : ℝ, {n : ℕ | n.Pseudoperfect}.HasDensity α

def H3 : Prop :=
  ({n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n}).HasDensity 0

def H4 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ b : ℕ in Filter.atTop, c ≤ {n : ℕ | n.Weird}.partialDensity Set.univ b

lemma hasDensity_sdiff {S T : Set ℕ} {α β : ℝ} (hST : T ⊆ S)
    (hS : S.HasDensity α) (hT : T.HasDensity β) : (S \ T).HasDensity (α - β) := by
  rw [Set.HasDensity] at hS hT ⊢
  have heq : ∀ b : ℕ, (S \ T).partialDensity Set.univ b =
      S.partialDensity Set.univ b - T.partialDensity Set.univ b := by
    intro b
    simp only [Set.partialDensity, Set.inter_univ]
    have hfinS : (S ∩ Set.Iio b).Finite := (Set.finite_Iio b).inter_of_right S
    have hfinT : (T ∩ Set.Iio b).Finite := (Set.finite_Iio b).inter_of_right T
    have hsub : T ∩ Set.Iio b ⊆ S ∩ Set.Iio b := Set.inter_subset_inter_left _ hST
    have hdiff : (S \ T) ∩ Set.Iio b = (S ∩ Set.Iio b) \ (T ∩ Set.Iio b) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_sdiff]
      tauto
    rw [hdiff, Set.ncard_sdiff hsub hfinT]
    have hle : (T ∩ Set.Iio b).ncard ≤ (S ∩ Set.Iio b).ncard := Set.ncard_le_ncard hsub hfinS
    rw [Nat.cast_sub hle, sub_div]
  simp_rw [heq]
  exact hS.sub hT

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos470.erdos_470.variants.weird_pos_density := by
  rintro ⟨α₁, h1⟩ ⟨α₂, h2⟩ h3 ⟨c, hc_pos, hc_ev⟩
  have hPerf_sub_P :
      {n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} ⊆ {n : ℕ | n.Pseudoperfect} := by
    rintro n ⟨hn_pos, hsum⟩
    exact ⟨hn_pos, n.properDivisors, Finset.Subset.refl _, hsum⟩
  have hP_diff_Perf :
      ({n : ℕ | n.Pseudoperfect} \ {n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n}).HasDensity
        (α₂ - 0) :=
    hasDensity_sdiff hPerf_sub_P h2 h3
  have hAP_eq :
      {n : ℕ | n.Pseudoperfect} \ {n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} =
      {n : ℕ | n.Abundant ∧ n.Pseudoperfect} := by
    ext n
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Nat.Abundant, Nat.Pseudoperfect]
    constructor
    · rintro ⟨⟨hn_pos, s, hs_sub, hsum⟩, hnot_perf⟩
      have hle : n ≤ ∑ d ∈ n.properDivisors, d := by
        calc n = ∑ d ∈ s, d := hsum.symm
          _ ≤ ∑ d ∈ n.properDivisors, d := Finset.sum_le_sum_of_subset hs_sub
      have hne : ∑ d ∈ n.properDivisors, d ≠ n := fun heq => hnot_perf ⟨hn_pos, heq⟩
      exact ⟨lt_of_le_of_ne hle hne.symm, hn_pos, s, hs_sub, hsum⟩
    · rintro ⟨hab, hn_pos, s, hs_sub, hsum⟩
      refine ⟨⟨hn_pos, s, hs_sub, hsum⟩, fun ⟨_, heq⟩ => ?_⟩
      omega
  rw [hAP_eq] at hP_diff_Perf
  have hW_eq :
      {n : ℕ | n.Weird} =
      {n : ℕ | n.Abundant} \ {n : ℕ | n.Abundant ∧ n.Pseudoperfect} := by
    ext n
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Nat.Weird]
    tauto
  have hAP_sub_A : {n : ℕ | n.Abundant ∧ n.Pseudoperfect} ⊆ {n : ℕ | n.Abundant} :=
    fun _ h => h.1
  have hW_dens : {n : ℕ | n.Weird}.HasDensity (α₁ - (α₂ - 0)) := by
    rw [hW_eq]
    exact hasDensity_sdiff hAP_sub_A h1 hP_diff_Perf
  have hc_le : c ≤ α₁ - (α₂ - 0) := ge_of_tendsto hW_dens hc_ev
  exact ⟨α₁ - (α₂ - 0), lt_of_lt_of_le hc_pos hc_le, hW_dens⟩

end OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1
