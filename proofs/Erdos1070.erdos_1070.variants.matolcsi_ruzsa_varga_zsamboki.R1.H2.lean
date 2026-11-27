import OMAReductions.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1

-- Step Erdos1070.erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki.R1.H2: hypothesis H2 of reduction Erdos1070.erdos_1070.variants.matolcsi_ruzsa_varga_zsamboki.R1

/-!
Subadditivity of `f`. Take an `a`-point set `Xa` and a `b`-point set `Xb` whose unit distance graphs
have independence numbers at most `f a` and `f b` (they exist because `f` is a maximum). Translate
`Xb` by a vector `v` outside the finite set of differences, so that `Xa` and `Xb + v` are disjoint.
An independent set of the union splits into a part inside `Xa` and a part inside `Xb + v`, both
free of unit distances, so its size is at most `f a + f b`. No separation is needed: the bound
on the independence number of a union holds whatever edges run between the two parts.
-/

open scoped Classical
open SimpleGraph

namespace OMA

/-- A finite point set with no two points at distance one, inside `V`, has at most
`indepNum` points. -/
theorem card_le_indepNum (V T : Finset (EuclideanSpace ℝ (Fin 2))) (hTV : T ⊆ V)
    (hT : ∀ x ∈ T, ∀ y ∈ T, dist x y ≠ 1) :
    T.card ≤ (UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
  have hind : (UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2)))).IsIndepSet
      (↑(T.subtype (fun x => x ∈ (V : Set (EuclideanSpace ℝ (Fin 2))))) :
        Set (↥(V : Set (EuclideanSpace ℝ (Fin 2))))) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro p hp q hq _ hadj
    have hp' : (p : EuclideanSpace ℝ (Fin 2)) ∈ T := Finset.mem_subtype.mp (Finset.mem_coe.mp hp)
    have hq' : (q : EuclideanSpace ℝ (Fin 2)) ∈ T := Finset.mem_subtype.mp (Finset.mem_coe.mp hq)
    exact hT _ hp' _ hq' hadj
  have h := hind.card_le_indepNum
  rw [Finset.card_subtype] at h
  have e : T.filter (fun x => x ∈ (V : Set (EuclideanSpace ℝ (Fin 2)))) = T := by
    apply Finset.filter_true_of_mem
    intro x hx
    exact Finset.mem_coe.mpr (hTV hx)
  rw [e] at h
  exact h

/-- Some `n`-point set attains `f n`. -/
theorem exists_extremal (n : ℕ) : ∃ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n ∧
    (UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum ≤ Erdos1070.f n := by
  by_contra hcon
  have hall : ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n →
      Erdos1070.f n + 1 ≤
        (UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
    intro X hX
    by_contra h
    exact hcon ⟨X, hX, by omega⟩
  obtain ⟨X0, hX0⟩ := Infinite.exists_subset_card_eq (EuclideanSpace ℝ (Fin 2)) n
  have hbdd : BddAbove {m : ℕ | ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n →
      m ≤ (UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum} :=
    ⟨(UnitDistancePlaneGraph (X0 : Set (EuclideanSpace ℝ (Fin 2)))).indepNum,
      fun m hm => hm X0 hX0⟩
  have hle : Erdos1070.f n + 1 ≤ Erdos1070.f n := le_csSup hbdd hall
  omega

end OMA

theorem OMA.solution : OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1.H2 := by
  unfold OMA.R_Erdos1070_erdos_1070_variants_matolcsi_ruzsa_varga_zsamboki_R1.H2
  intro a b
  obtain ⟨Xa, hXa, hfa⟩ := OMA.exists_extremal a
  obtain ⟨Xb, hXb, hfb⟩ := OMA.exists_extremal b
  -- a translation vector outside the finite set of differences
  obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset
    ((Xa ×ˢ Xb).image fun pq : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => pq.1 - pq.2)
  have hinj : Function.Injective (fun y : EuclideanSpace ℝ (Fin 2) => y + v) :=
    fun y1 y2 h => add_right_cancel h
  have hdisj : Disjoint Xa (Xb.image fun y => y + v) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx2
    apply hv
    refine Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩
    show x - y = v
    rw [← hyx]
    abel
  have hcard : (Xa ∪ Xb.image fun y => y + v).card = a + b := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj, hXa, hXb]
  have hf := Erdos1070.f_le (Xa ∪ Xb.image fun y => y + v)
  rw [hcard] at hf
  refine hf.trans ?_
  obtain ⟨s, hs⟩ := (UnitDistancePlaneGraph
    ((Xa ∪ Xb.image fun y => y + v : Finset (EuclideanSpace ℝ (Fin 2))) :
      Set (EuclideanSpace ℝ (Fin 2)))).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  have hsind := hs.isIndepSet
  rw [SimpleGraph.isIndepSet_iff] at hsind
  -- the points of `s`, as a finite set of the plane
  have hTdist : ∀ x ∈ s.map (Function.Embedding.subtype _), ∀ y ∈ s.map (Function.Embedding.subtype _),
      dist x y ≠ 1 := by
    intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hy
    by_cases hpq : p = q
    · rw [hpq]
      simp
    · intro hd
      exact hsind (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) hpq hd
  have hTsub : ∀ x ∈ s.map (Function.Embedding.subtype _), x ∈ Xa ∨ x ∈ Xb.image fun y => y + v := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_union.mp (Finset.mem_coe.mp p.2)
  have hTcard : (s.map (Function.Embedding.subtype _)).card = s.card := Finset.card_map _
  generalize s.map (Function.Embedding.subtype _) = T at hTdist hTsub hTcard
  rw [← hTcard, ← Finset.card_filter_add_card_filter_not (s := T) (fun x => x ∈ Xa)]
  have h1 : (T.filter fun x => x ∈ Xa).card ≤
      (UnitDistancePlaneGraph (Xa : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
    apply OMA.card_le_indepNum
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy
      exact hTdist x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
  have h2 : (T.filter fun x => ¬ x ∈ Xa).card ≤
      (UnitDistancePlaneGraph (Xb : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
    have hinj2 : Function.Injective (fun y : EuclideanSpace ℝ (Fin 2) => y - v) :=
      fun y1 y2 h => sub_left_injective h
    rw [← Finset.card_image_of_injective _ hinj2]
    apply OMA.card_le_indepNum
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hxT, hxa⟩ := Finset.mem_filter.mp hx
      rcases hTsub x hxT with h | h
      · exact absurd h hxa
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
        show y + v - v ∈ Xb
        rw [add_sub_cancel_right]
        exact hy
    · intro z1 hz1 z2 hz2
      obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.mp hz1
      obtain ⟨x2, hx2, rfl⟩ := Finset.mem_image.mp hz2
      show dist (x1 - v) (x2 - v) ≠ 1
      rw [dist_sub_right]
      exact hTdist x1 (Finset.mem_filter.mp hx1).1 x2 (Finset.mem_filter.mp hx2).1
  omega
