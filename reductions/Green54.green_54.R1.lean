import FormalConjectures.GreensOpenProblems.«54»

/-!
# Green 54 via finite-dimensional Gaussian convexity

Hua–Song–Tudose (arXiv:2605.10908v2), Theorem 1.1 and Corollary 5.2, provide the
finite-dimensional input at $b=1/3$ and $c=1/4$. The second input is a compact
limit principle for coordinate restrictions of convex sets.

The finite-to-infinite route was discussed by @luciusacarr and @NullLabTests in
the Green54 desk notes. Credit: @justusklocke-cloud.
-/

namespace OMA.R_Green54_green_54_R1

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology Pointwise ENNReal NNReal

private theorem exists_convexBox (K : Set (ℕ → ℝ)) (hK : IsCompact K) :
    ∃ B : Set (ℕ → ℝ), IsCompact B ∧ Convex ℝ B ∧ K ⊆ B := by
  have hb (i : ℕ) : ∃ a b : ℝ, ∀ x ∈ K, x i ∈ Set.Icc a b := by
    obtain ⟨a, ha⟩ := hK.bddBelow_image (continuous_apply i).continuousOn
    obtain ⟨b, hb⟩ := hK.bddAbove_image (continuous_apply i).continuousOn
    exact ⟨a, b, fun x hx => ⟨ha (mem_image_of_mem _ hx), hb (mem_image_of_mem _ hx)⟩⟩
  choose a b hab using hb
  refine ⟨Set.pi univ (fun i => Set.Icc (a i) (b i)), ?_,
    convex_pi (fun _ _ => convex_Icc _ _), fun x hx i _ => hab i x hx⟩
  have hbox : Set.pi univ (fun i => Set.Icc (a i) (b i)) =
      {x | ∀ i, x i ∈ Set.Icc (a i) (b i)} := by
    ext x
    simp [Set.pi]
  rw [hbox]
  exact isCompact_pi_infinite (fun _ => isCompact_Icc)

private theorem prefix_image_nsmul (n m : ℕ) (K : Set (ℕ → ℝ)) :
    (Finset.range n).restrict '' (m • K) = m • ((Finset.range n).restrict '' K) := by
  let p : (ℕ → ℝ) →+ (↥(Finset.range n) → ℝ) := {
    toFun := (Finset.range n).restrict
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  exact Set.image_nsmul p K m

private theorem compact_nsmul {K : Set (ℕ → ℝ)} (hK : IsCompact K) (n : ℕ) :
    IsCompact (n • K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    exact ih.add hK

private theorem prefix_measure {n : ℕ} {A : Set (↥(Finset.range n) → ℝ)} (hA : IsCompact A) :
    Green54.gaussianMeasureInf ((Finset.range n).restrict ⁻¹' A) =
      (Measure.pi (fun _ : ↥(Finset.range n) => gaussianReal 0 1)) A := by
  rw [← Measure.map_apply (Finset.measurable_restrict _) hA.isClosed.measurableSet]
  exact congrArg (fun μ : Measure (↥(Finset.range n) → ℝ) => μ A)
    (Measure.infinitePi_map_restrict (fun _ : ℕ => gaussianReal 0 1))

private theorem intersection_large
    (μ : Measure (ℕ → ℝ)) [IsProbabilityMeasure μ]
    (A B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (ha : (0.25 : ℝ≥0∞) ≤ μ A) (hb : (0.99 : ℝ≥0∞) ≤ μ B) :
    (0.01 : ℝ≥0∞) ≤ μ (A ∩ B) := by
  by_contra! h
  have hu : μ (A ∪ B) ≤ 1 := by simpa using (measure_mono (subset_univ (A ∪ B)) :
    μ (A ∪ B) ≤ μ univ)
  have h1 := add_le_add ha hb
  rw [← measure_union_add_inter A hB] at h1
  have h2 := h1.trans (add_le_add hu h.le)
  have hnum : (1 + 0.01 : ℝ≥0∞) < 0.25 + 0.99 := by
    change 1 + ((0.01 : ℝ≥0) : ℝ≥0∞) < ((0.25 : ℝ≥0) : ℝ≥0∞) + ((0.99 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.coe_one, ← ENNReal.coe_add, ← ENNReal.coe_add, ENNReal.coe_lt_coe]
    norm_num
  exact hnum.not_ge h2

private theorem dilation_triple_subset_nine {ι : Type*} (A : Set (ι → ℝ)) :
    (3 : ℝ) • ((3 : ℕ) • A) ⊆ (9 : ℕ) • A := by
  rintro _ ⟨x, hx, rfl⟩
  have h : (3 : ℝ) • x = x + x + x := by
    funext i
    change 3 * x i = x i + x i + x i
    ring
  change (3 : ℝ) • x ∈ (9 : ℕ) • A
  rw [h, show (9 : ℕ) = 3 + 3 + 3 by rfl, add_nsmul, add_nsmul]
  exact Set.add_mem_add (Set.add_mem_add hx hx) hx

/-- The finite-dimensional Gaussian convexity theorem at $b=1/3$ and $c=1/4$. -/
def H1 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ A : Set (↥(Finset.range n) → ℝ), IsCompact A →
    (5 / 6 : ℝ≥0∞) < (Measure.pi (fun _ : ↥(Finset.range n) => gaussianReal 0 1)) A →
    ∃ C : Set (↥(Finset.range n) → ℝ), IsCompact C ∧ Convex ℝ C ∧
      C ⊆ (3 : ℝ) • ((3 : ℕ) • A) ∧
      (0.25 : ℝ≥0∞) ≤ (Measure.pi (fun _ : ↥(Finset.range n) => gaussianReal 0 1)) C

/-- Compact limit for large convex sets constrained by successively longer coordinate prefixes. -/
def H2 : Prop :=
  ∀ (μ : Measure (ℕ → ℝ)) [IsFiniteMeasure μ] (c : ℝ≥0∞) (B S : Set (ℕ → ℝ)),
    IsCompact B → IsCompact S → ∀ D : ℕ → Set (ℕ → ℝ),
    (∀ n, IsCompact (D n) ∧ Convex ℝ (D n) ∧ c ≤ μ (D n) ∧ D n ⊆ B ∧
      D n ⊆ (Finset.range (n + 1)).restrict ⁻¹' ((Finset.range (n + 1)).restrict '' S)) →
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ S ∧ c ≤ μ C

theorem main : H1 → H2 → type_of% @Green54.green_54 := by
  classical
  intro hfinite hcompact K hK hbalanced hKmass
  let μ := Green54.gaussianMeasureInf
  let _ : IsProbabilityMeasure μ := by unfold μ Green54.gaussianMeasureInf; infer_instance
  obtain ⟨B, hB, hBconv, hKB⟩ := exists_convexBox K hK
  have hBmass : (0.99 : ℝ≥0∞) ≤ μ B := hKmass.trans (measure_mono hKB)
  have hKne : K.Nonempty := by
    by_contra! he
    rw [he, measure_empty] at hKmass
    have hpos : (0 : ℝ≥0∞) < 0.99 := by
      change ((0 : ℝ≥0) : ℝ≥0∞) < ((0.99 : ℝ≥0) : ℝ≥0∞)
      exact ENNReal.coe_lt_coe.mpr (by norm_num)
    exact hpos.not_ge hKmass
  have hK0 : (0 : ℕ → ℝ) ∈ K := hbalanced.zero_mem hKne
  let S := (9 : ℕ) • K
  have hS : IsCompact S := compact_nsmul hK 9
  have hseq (n : ℕ) : ∃ D : Set (ℕ → ℝ),
      IsCompact D ∧ Convex ℝ D ∧ (0.01 : ℝ≥0∞) ≤ μ D ∧ D ⊆ B ∧
      D ⊆ (Finset.range (n + 1)).restrict ⁻¹'
        ((Finset.range (n + 1)).restrict '' S) := by
    let p := (Finset.range (n + 1)).restrict (π := fun _ => ℝ)
    have hp : Continuous p := Finset.continuous_restrict _
    let A := p '' K
    have hA : IsCompact A := hK.image hp
    have hAmass : (5 / 6 : ℝ≥0∞) <
        Measure.pi (fun _ : ↥(Finset.range (n + 1)) => gaussianReal 0 1) A := by
      rw [← prefix_measure hA]
      have hfive : (5 / 6 : ℝ≥0∞) < 0.99 := by
        change (5 / 6 : ℝ≥0∞) < ((0.99 : ℝ≥0) : ℝ≥0∞)
        rw [← ENNReal.coe_ofNat 5, ← ENNReal.coe_ofNat 6, ← ENNReal.coe_div (by norm_num),
          ENNReal.coe_lt_coe]
        norm_num
      exact hfive.trans_le (hKmass.trans (measure_mono (fun x hx => mem_image_of_mem p hx)))
    obtain ⟨T, hT, hTconv, hTA, hTmass⟩ := hfinite (n + 1) (Nat.succ_pos _) A hA hAmass
    let D := (p ⁻¹' T) ∩ B
    have hD : IsCompact D := hB.inter_left (hT.isClosed.preimage hp)
    have hDp : Convex ℝ (p ⁻¹' T) :=
      convex_iff_add_mem.mpr (fun x hx y hy a b ha hb hab =>
        convex_iff_add_mem.mp hTconv hx hy ha hb hab)
    refine ⟨D, hD, hDp.inter hBconv, ?_, inter_subset_right, ?_⟩
    · apply intersection_large μ _ _ hB.isClosed.measurableSet _ hBmass
      exact (prefix_measure hT).symm ▸ hTmass
    · have hTA' : T ⊆ p '' S := by
        rw [show p '' S = (9 : ℕ) • A from prefix_image_nsmul (n + 1) 9 K]
        exact hTA.trans (dilation_triple_subset_nine A)
      exact inter_subset_left.trans (preimage_mono hTA')
  choose D hDcompact hDconv hDmass hDB hDS using hseq
  obtain ⟨C, hC, hcconv, hcS, hcmass⟩ := hcompact μ 0.01 B S hB hS D
    (fun n => ⟨hDcompact n, hDconv n, hDmass n, hDB n, hDS n⟩)
  exact ⟨C, hC, hcconv,
    hcS.trans (Set.nsmul_subset_nsmul (subset_refl K) hK0 (by decide : 9 ≤ 10)), hcmass⟩

end OMA.R_Green54_green_54_R1
