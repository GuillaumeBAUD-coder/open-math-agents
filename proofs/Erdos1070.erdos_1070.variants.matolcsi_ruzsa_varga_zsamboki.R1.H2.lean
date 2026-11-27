import OMAReductions.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1
import Mathlib

/-! # Subadditivity of the unit-distance independence function `f`

`f n` is attained: some `n`-point set `X` has independence number at most `f n` (take the
least independence number over all `n`-point sets). Given such `X₁` (size `a`) and `X₂`
(size `b`), translate `X₂` by a vector longer than twice every norm in `X₁ ∪ X₂`, so the two
sets are disjoint and their union has `a + b` points. A largest independent set of the union
splits into a part inside `X₁` and a part that translates back into `X₂`; both stay
independent, so `f (a + b) ≤ α (X₁ ∪ X₂') ≤ α X₁ + α X₂ ≤ f a + f b`. -/

open Finset

namespace OMA.E1070

/-- Points of the plane. -/
abbrev P2 := EuclideanSpace ℝ (Fin 2)

/-- Independence number of the unit distance graph on a finite set. -/
noncomputable abbrev α (X : Finset P2) : ℕ := (SimpleGraph.UnitDistancePlaneGraph (X : Set P2)).indepNum

lemma card_le_alpha (X s : Finset P2) (hs : s ⊆ X)
    (hind : ∀ x ∈ s, ∀ y ∈ s, dist x y ≠ 1) : s.card ≤ α X := by
  classical
  have ht : (s.subtype (· ∈ (X : Set P2))).card = s.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun x hx => hs hx)
  rw [← ht]
  apply SimpleGraph.IsIndepSet.card_le_indepNum
  intro x hx y hy _ hadj
  have hx' : x.1 ∈ s := Finset.mem_subtype.1 (Finset.mem_coe.1 hx)
  have hy' : y.1 ∈ s := Finset.mem_subtype.1 (Finset.mem_coe.1 hy)
  apply hind x.1 hx' y.1 hy'
  have h : dist x y = 1 := hadj
  rwa [Subtype.dist_eq] at h

lemma exists_max (X : Finset P2) :
    ∃ s ⊆ X, (∀ x ∈ s, ∀ y ∈ s, dist x y ≠ 1) ∧ s.card = α X := by
  classical
  obtain ⟨t, ht⟩ := (SimpleGraph.UnitDistancePlaneGraph (X : Set P2)).exists_isNIndepSet_indepNum
  refine ⟨t.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  · intro x hx y hy hd
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    by_cases hxy : x' = y'
    · subst hxy
      simp at hd
    · apply ht.isIndepSet (Finset.mem_coe.2 hx') (Finset.mem_coe.2 hy') hxy
      show dist x' y' = 1
      rw [Subtype.dist_eq]
      exact hd
  · rw [Finset.card_map, ht.card_eq]

lemma exists_card (n : ℕ) : ∃ X : Finset P2, X.card = n := by
  let φ : ℕ → P2 := fun t => EuclideanSpace.single 0 (t : ℝ)
  have hφ : Function.Injective φ := by
    intro a b h
    have := congrArg (fun p : P2 => p 0) h
    simpa [φ] using this
  exact ⟨(range n).image φ, by rw [card_image_of_injective _ hφ, card_range]⟩

lemma attain (n : ℕ) : ∃ X : Finset P2, X.card = n ∧ α X ≤ Erdos1070.f n := by
  classical
  obtain ⟨X₀, hX₀⟩ := exists_card n
  have hne : {k | ∃ X : Finset P2, X.card = n ∧ α X = k}.Nonempty := ⟨_, X₀, hX₀, rfl⟩
  obtain ⟨X, hXc, hXk⟩ := Nat.sInf_mem hne
  refine ⟨X, hXc, ?_⟩
  rw [hXk]
  apply le_csSup
  · exact ⟨α X₀, fun m hm => hm X₀ hX₀⟩
  · intro Y hY
    exact Nat.sInf_le ⟨Y, hY, rfl⟩

end OMA.E1070

open OMA.E1070 in
theorem OMA.solution : OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1.H2 := by
  unfold OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1.H2
  intro a b
  classical
  obtain ⟨X₁, h1c, h1⟩ := attain a
  obtain ⟨X₂, h2c, h2⟩ := attain b
  set B : ℝ := ∑ x ∈ X₁ ∪ X₂, ‖x‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun x _ => norm_nonneg x)
  have hle : ∀ x ∈ X₁ ∪ X₂, ‖x‖ ≤ B := fun x hx =>
    Finset.single_le_sum (f := fun x : P2 => ‖x‖) (fun y _ => norm_nonneg y) hx
  set v : P2 := EuclideanSpace.single 0 (2 * B + 1) with hv
  have hvn : ‖v‖ = 2 * B + 1 := by
    rw [hv, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  set Y := X₂.image (· + v) with hY
  have hYc : Y.card = b := by rw [hY, card_image_of_injective _ (add_left_injective v), h2c]
  have hdisj : Disjoint X₁ Y := by
    rw [Finset.disjoint_left]
    intro x hx hxY
    rw [hY, Finset.mem_image] at hxY
    obtain ⟨y, hy, rfl⟩ := hxY
    have e1 := hle (y + v) (mem_union_left _ hx)
    have e2 := hle y (mem_union_right _ hy)
    have e3 : ‖v‖ ≤ ‖y + v‖ + ‖y‖ := by
      have := norm_sub_le (y + v) y
      simpa using this
    linarith
  have hcard : (X₁ ∪ Y).card = a + b := by rw [card_union_of_disjoint hdisj, h1c, hYc]
  have hf := Erdos1070.f_le (X₁ ∪ Y)
  rw [hcard] at hf
  obtain ⟨s, hsX, hsind, hscard⟩ := exists_max (X₁ ∪ Y)
  have hs1 : (s.filter (fun x => x ∈ X₁)).card ≤ α X₁ :=
    card_le_alpha X₁ _ (fun x hx => (mem_filter.1 hx).2)
      (fun x hx y hy => hsind x (mem_filter.1 hx).1 y (mem_filter.1 hy).1)
  have hs2 : ((s.filter (fun x => ¬ x ∈ X₁)).image (· - v)).card ≤ α X₂ := by
    apply card_le_alpha
    · intro z hz
      rw [mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      rw [mem_filter] at hx
      have hxu := hsX hx.1
      rw [mem_union] at hxu
      rcases hxu with h | h
      · exact absurd h hx.2
      · rw [hY, mem_image] at h
        obtain ⟨y, hy, rfl⟩ := h
        simpa using hy
    · intro z hz w hw
      rw [mem_image] at hz hw
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨y, hy, rfl⟩ := hw
      rw [dist_sub_right]
      exact hsind x (mem_filter.1 hx).1 y (mem_filter.1 hy).1
  rw [card_image_of_injective _ sub_left_injective] at hs2
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun x => x ∈ X₁)
  have hU : α (X₁ ∪ Y) ≤ α X₁ + α X₂ := by
    rw [← hscard, ← hsplit]
    exact add_le_add hs1 hs2
  calc Erdos1070.f (a + b) ≤ α (X₁ ∪ Y) := hf
    _ ≤ α X₁ + α X₂ := hU
    _ ≤ Erdos1070.f a + Erdos1070.f b := add_le_add h1 h2
