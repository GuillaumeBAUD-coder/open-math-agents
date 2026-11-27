import OMAReductions.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1
import Mathlib.Algebra.Module.Submodule.Union

/-!
The projection lemmas are adapted from @Genbox, merged open-math-agents PR 657.
The dimension inequality is Valtr's generic projection argument, as described by
Pohoata and Zakharov, Section 1 (https://arxiv.org/abs/2208.04878).
-/

open scoped EuclideanGeometry Finset

theorem OMA.finite_image_pullback {α β : Type*} [DecidableEq β] (L : α → β) (X : Finset α) (Z : Finset β)
    (hZ : Z ⊆ X.image L) (hL : Set.InjOn L (X : Set α)) :
    ∃ Y ⊆ X, Y.image L = Z ∧ Y.card = Z.card := by
  classical
  let Y := X.filter fun y => L y ∈ Z
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image L = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hy).2
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hZ hz)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hz⟩, rfl⟩
  refine ⟨Y, hYX, hYZ, ?_⟩
  rw [← hYZ, Finset.card_image_of_injOn (hL.mono hYX)]

open scoped Classical in
theorem OMA.convex_subset_lifts {k d n : ℕ} (L : (ℝ^d) →ₗ[ℝ] (ℝ^k)) (X : Finset (ℝ^d))
    (hL : Set.InjOn L (X : Set (ℝ^d))) (hX : Erdos651.HasConvexSubset n (X.image L)) :
    Erdos651.HasConvexSubset n X := by
  classical
  obtain ⟨Z, hZ, hZn, hconv⟩ := hX
  obtain ⟨Y, hYX, hYZ, hcard⟩ := OMA.finite_image_pullback L X Z hZ hL
  refine ⟨Y, hYX, hcard.trans hZn, ?_⟩
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hconv ⊢
  intro y hy h
  have hLy : L y ∈ (Z : Set (ℝ^k)) := by
    rw [← hYZ]
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  apply hconv (L y) hLy
  have himage : L '' ((Y : Set (ℝ^d)) \ {y}) ⊆ (Z : Set (ℝ^k)) \ {L y} := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hYZ]
      exact Finset.mem_image.mpr ⟨a, ha.1, rfl⟩
    · intro he
      exact ha.2 (hL (hYX ha.1) (hYX hy) he)
  apply convexHull_mono himage
  rw [← L.image_convexHull]
  exact ⟨y, h, rfl⟩

open scoped Classical in
theorem OMA.generic_projection {k : ℕ} (hk : 1 ≤ k) (X : Finset (ℝ^(k+1)))
    (hX : Erdos651.IsInGeneralPosition X) :
    ∃ L : (ℝ^(k+1)) →ₗ[ℝ] (ℝ^k),
      Set.InjOn L (X : Set (ℝ^(k+1))) ∧ Erdos651.IsInGeneralPosition (X.image L) := by
  classical
  let T := X.powerset.filter fun Y => Y.card ≤ k + 1
  let W (Y : T) : Submodule ℝ (ℝ^(k+1)) := vectorSpan ℝ (Y.val : Set (ℝ^(k+1)))
  have hW (Y : T) : W Y ≠ ⊤ := by
    have hsmall : Y.val.card ≤ k + 1 := (Finset.mem_filter.mp Y.prop).2
    have hdim : Module.finrank ℝ (W Y) ≤ k := by
      rcases Y.val.eq_empty_or_nonempty with hY | hY
      · change Module.finrank ℝ (vectorSpan ℝ (Y.val : Set (ℝ^(k+1)))) ≤ k
        rw [hY, Finset.coe_empty, vectorSpan_empty, finrank_bot]
        exact Nat.zero_le _
      · have hcard : Y.val.card = (Y.val.card - 1) + 1 := by
          have := Finset.card_pos.mpr hY
          omega
        have h := finrank_vectorSpan_image_finset_le ℝ id Y.val hcard
        rw [Finset.image_id] at h
        have h' : Module.finrank ℝ (W Y) ≤ Y.val.card - 1 := h
        omega
    intro htop
    rw [htop, finrank_top, finrank_euclideanSpace_fin] at hdim
    omega
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top W hW
  have hv₀ : v ≠ 0 := by
    let e : T := ⟨∅, by simp [T]⟩
    intro h
    exact hv e (h.symm ▸ (W e).zero_mem)
  let U := ℝ ∙ v
  have hdim : Module.finrank ℝ ((ℝ^(k+1)) ⧸ U) = Module.finrank ℝ (ℝ^k) := by
    have h := U.finrank_quotient_add_finrank
    rw [show Module.finrank ℝ U = 1 from finrank_span_singleton hv₀,
      finrank_euclideanSpace_fin] at h
    rw [finrank_euclideanSpace_fin]
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hdim
  let L : (ℝ^(k+1)) →ₗ[ℝ] (ℝ^k) := e.toLinearMap.comp U.mkQ
  have hker (Y : Finset (ℝ^(k+1))) (hYX : Y ⊆ X) (hY : Y.card ≤ k + 1) :
      Disjoint (vectorSpan ℝ (Y : Set (ℝ^(k+1)))) (LinearMap.ker L) := by
    let i : T := ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hYX, hY⟩⟩
    rw [Submodule.disjoint_def]
    intro u hu hlu
    have hU : u ∈ U := by
      rw [← Submodule.ker_mkQ U]
      apply LinearMap.mem_ker.mpr
      apply e.injective
      exact (LinearMap.mem_ker.mp hlu).trans e.map_zero.symm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hU
    by_cases ha₀ : a = 0
    · simpa [ha₀] using ha.symm
    · rw [← ha] at hu
      exact (hv i (((W i).smul_mem_iff ha₀).mp hu)).elim
  have hL : Set.InjOn L (X : Set (ℝ^(k+1))) := by
    intro a ha b hb hab
    let Y : Finset (ℝ^(k+1)) := {a, b}
    have hYX : Y ⊆ X := by
      intro x hx
      simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have hY : Y.card ≤ k + 1 := Finset.card_le_two.trans (by omega)
    have hm : a - b ∈ vectorSpan ℝ (Y : Set (ℝ^(k+1))) :=
      vsub_mem_vectorSpan ℝ (show a ∈ (Y : Set _) by simp [Y])
        (show b ∈ (Y : Set _) by simp [Y])
    have hd : a - b ∈ LinearMap.ker L := LinearMap.mem_ker.mpr (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp (hker Y hYX hY) _ hm hd)
  refine ⟨L, hL, fun Z hZ hcard => ?_⟩
  obtain ⟨Y, hYX, hYZ, hcardY⟩ := OMA.finite_image_pullback L X Z hZ hL
  have hYcard : Y.card ≤ k + 1 := hcardY.trans_le hcard
  let p : ↥(Y : Set (ℝ^(k+1))) → ℝ^(k+1) := Subtype.val
  have hrange : Set.range (L ∘ p) = (Z : Set (ℝ^k)) := by
    rw [Set.range_comp, Subtype.range_coe, ← Finset.coe_image, hYZ]
  suffices h : AffineIndependent ℝ (L ∘ p) by
    rw [← hrange]
    exact h.range
  rcases isEmpty_or_nonempty ↥(Y : Set (ℝ^(k+1))) with hEmpty | hNonempty
  · let _ := hEmpty
    exact affineIndependent_of_subsingleton _ (L ∘ p)
  · obtain ⟨y⟩ := hNonempty
    have hind : AffineIndependent ℝ p := hX Y hYX (by omega)
    have hd := (affineIndependent_iff_linearIndependent_vsub ℝ p y).mp hind
    apply (affineIndependent_iff_linearIndependent_vsub ℝ (L ∘ p) y).mpr
    have hs : Submodule.span ℝ (Set.range (fun i : {i // i ≠ y} => p i -ᵥ p y)) ≤
        vectorSpan ℝ (Y : Set (ℝ^(k+1))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact vsub_mem_vectorSpan ℝ i.val.prop y.prop
    have hm := hd.map ((hker Y hYX hYcard).mono_left hs)
    change LinearIndependent ℝ (fun i : {i // i ≠ y} => L (p i - p y)) at hm
    simpa only [Function.comp_apply, vsub_eq_sub, map_sub] using hm

theorem OMA.cardSet_projection {k n N : ℕ} (hk : 1 ≤ k) (hN : N ∈ Erdos651.cardSet k n) :
    N ∈ Erdos651.cardSet (k + 1) n := by
  classical
  intro X hX hcard
  obtain ⟨L, hL, hgp⟩ := OMA.generic_projection hk X hX
  apply OMA.convex_subset_lifts L X hL
  apply hN _ hgp
  rwa [Finset.card_image_of_injOn hL]


theorem OMA.solution : OMA.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1.H2 := by
  intro k n N hk hN
  exact OMA.cardSet_projection (by omega) hN
