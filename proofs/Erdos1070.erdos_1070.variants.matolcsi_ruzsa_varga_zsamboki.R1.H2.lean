import OMAReductions.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1

-- Step Erdos1070.erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki.R1.H2: hypothesis H2 of reduction
-- Erdos1070.erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki.R1
-- Credit: @iskan-ai

/-! Subadditivity of `f`. Take an `a`-point set `X` and a `b`-point set `Y` realising `f a` and
`f b`, translate `Y` far away so that the two sets are disjoint, and note that an independent set
of the union splits into an independent set of `X` and one of the translate of `Y`, while a
translation does not change distances. -/

open SimpleGraph

namespace OMA.E1070H2

abbrev P := EuclideanSpace ℝ (Fin 2)

/-- Independence number of the unit distance graph on a finite point set. -/
noncomputable def iota (A : Finset P) : ℕ := (UnitDistancePlaneGraph (A : Set P)).indepNum

/-- A point set without unit distances inside `A` has at most `iota A` points. -/
theorem le_iota {A S : Finset P} (hS : S ⊆ A)
    (hi : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y ≠ 1) : S.card ≤ iota A := by
  classical
  let t : Finset (A : Set P) := S.subtype (fun x => x ∈ (A : Set P))
  have hcard : t.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    apply Finset.filter_true_of_mem
    intro x hx
    exact Finset.mem_coe.mpr (hS hx)
  have hind : (UnitDistancePlaneGraph (A : Set P)).IsIndepSet (t : Set (A : Set P)) := by
    intro x hx y hy hxy hadj
    have hx' : (x : P) ∈ S := by simpa [t] using hx
    have hy' : (y : P) ∈ S := by simpa [t] using hy
    exact hi _ hx' _ hy' (fun h => hxy (Subtype.ext h)) hadj
  rw [← hcard]
  exact hind.card_le_indepNum

/-- `iota A` is attained by a point set without unit distances inside `A`. -/
theorem iota_attained (A : Finset P) :
    ∃ S ⊆ A, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y ≠ 1) ∧ S.card = iota A := by
  classical
  obtain ⟨s, hs⟩ := (UnitDistancePlaneGraph (A : Set P)).exists_isNIndepSet_indepNum
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_coe.mp y.2
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    have hne : x' ≠ y' := fun h => hxy (by rw [h])
    exact hs.isIndepSet (Finset.mem_coe.mpr hx') (Finset.mem_coe.mpr hy') hne
  · rw [Finset.card_map]
    exact hs.card_eq

theorem iota_union (X Y : Finset P) : iota (X ∪ Y) ≤ iota X + iota Y := by
  classical
  obtain ⟨S, hS, hi, hc⟩ := iota_attained (X ∪ Y)
  rw [← hc, ← Finset.card_filter_add_card_filter_not (s := S) (fun x => x ∈ X)]
  apply Nat.add_le_add
  · apply le_iota
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy hxy
      exact hi x (Finset.mem_of_mem_filter x hx) y (Finset.mem_of_mem_filter y hy) hxy
  · apply le_iota
    · intro x hx
      obtain ⟨hxS, hxX⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp (hS hxS) with h | h
      · exact absurd h hxX
      · exact h
    · intro x hx y hy hxy
      exact hi x (Finset.mem_of_mem_filter x hx) y (Finset.mem_of_mem_filter y hy) hxy

theorem iota_translate (Y : Finset P) (v : P) : iota (Y.image (· + v)) ≤ iota Y := by
  classical
  obtain ⟨S, hS, hi, hc⟩ := iota_attained (Y.image (· + v))
  rw [← hc]
  have hinj : Function.Injective (fun x : P => x - v) := fun a b h => by simpa using h
  rw [← Finset.card_image_of_injective S hinj]
  apply le_iota
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hS hz)
    simpa using hy
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    have hne : x' ≠ y' := fun h => hxy (by rw [h])
    have := hi x' hx' y' hy' hne
    simpa [dist_sub_right] using this

/-- `f n` is attained by some `n`-point set. -/
theorem attained (n : ℕ) : ∃ X : Finset P, X.card = n ∧ iota X ≤ Erdos1070.f n := by
  classical
  obtain ⟨X0, hX0⟩ := Infinite.exists_subset_card_eq P n
  have hex : ∃ m, ∃ X : Finset P, X.card = n ∧ iota X ≤ m := ⟨iota X0, X0, hX0, le_rfl⟩
  obtain ⟨X, hX, hXm⟩ := Nat.find_spec hex
  refine ⟨X, hX, hXm.trans ?_⟩
  unfold Erdos1070.f
  apply le_csSup
  · exact ⟨iota X, fun m hm => hm X hX⟩
  · intro Y hY
    exact Nat.find_min' hex ⟨Y, hY, le_rfl⟩

end OMA.E1070H2

open OMA.E1070H2 in
theorem OMA.solution : OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1.H2 := by
  classical
  intro a b
  obtain ⟨X, hX, hXf⟩ := attained a
  obtain ⟨Y, hY, hYf⟩ := attained b
  set R : ℝ := (∑ x ∈ X, ‖x‖) + (∑ y ∈ Y, ‖y‖) + 1 with hR
  have hRpos : 0 < R := by
    have h1 : 0 ≤ ∑ x ∈ X, ‖x‖ := Finset.sum_nonneg (fun x _ => norm_nonneg x)
    have h2 : 0 ≤ ∑ y ∈ Y, ‖y‖ := Finset.sum_nonneg (fun y _ => norm_nonneg y)
    linarith
  let v : P := EuclideanSpace.single 0 R
  have hv : ‖v‖ = R := by
    simp [v, PiLp.norm_single, abs_of_pos hRpos]
  have hdisj : Disjoint X (Y.image (· + v)) := by
    rw [Finset.disjoint_left]
    intro x hx hxY
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxY
    have hx1 : ‖x‖ ≤ ∑ x ∈ X, ‖x‖ := Finset.single_le_sum (fun x _ => norm_nonneg x) hx
    have hy1 : ‖y‖ ≤ ∑ y ∈ Y, ‖y‖ := Finset.single_le_sum (fun y _ => norm_nonneg y) hy
    have hvxy : v = x - y := by rw [← hxy]; abel
    have : ‖v‖ ≤ ‖x‖ + ‖y‖ := by rw [hvxy]; exact norm_sub_le x y
    linarith
  have hinj : Function.Injective (fun y : P => y + v) := fun p q h => by simpa using h
  have hcard : (X ∪ Y.image (· + v)).card = a + b := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective Y hinj, hX, hY]
  have h1 := Erdos1070.f_le (X ∪ Y.image (· + v))
  rw [hcard] at h1
  calc Erdos1070.f (a + b) ≤ iota (X ∪ Y.image (· + v)) := h1
    _ ≤ iota X + iota (Y.image (· + v)) := iota_union _ _
    _ ≤ iota X + iota Y := Nat.add_le_add_left (iota_translate Y v) _
    _ ≤ Erdos1070.f a + Erdos1070.f b := Nat.add_le_add hXf hYf
