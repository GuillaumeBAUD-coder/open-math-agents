import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1_H2_R1

open SimpleGraph
open scoped Classical

namespace Split713

/-- Deleting every edge at a set `I` of vertices costs at most `|I| · |B|` edges. -/
theorem strip {B : Type} [Fintype B] (D : SimpleGraph B) (I : Finset B) :
    ∃ D' : SimpleGraph B, D' ≤ D ∧ (∀ x ∈ I, ∀ y, ¬ D'.Adj x y) ∧
      Nat.card D.edgeSet ≤ Nat.card D'.edgeSet + I.card * Fintype.card B := by
  refine Finset.induction_on I ⟨D, le_rfl, by simp, by simp⟩ ?_
  intro a I ha ih
  obtain ⟨D₁, hle, hiso, hcard⟩ := ih
  refine ⟨D₁.deleteIncidenceSet a, (D₁.deleteIncidenceSet_le a).trans hle, ?_, ?_⟩
  · intro x hx y hxy
    rw [deleteIncidenceSet_adj] at hxy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hxy.2.1 rfl
    · exact hiso x hx y hxy.1
  · have he := card_edgeFinset_deleteIncidenceSet D₁ a
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at he
    have hdeg := D₁.degree_le_card_edgeFinset (v := a)
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at hdeg
    have hlt := D₁.degree_lt_card_verts a
    rw [Finset.card_insert_of_notMem ha, Nat.add_mul, Nat.one_mul]
    omega

/-- If `S` is a union of components of `G` and `G` has no isolated vertex, a `G`-free graph has
at most `ex(G[S]) + ex(G[Sᶜ]) + |A| · |B|` edges. -/
theorem combine {A B : Type} [Fintype A] [Fintype B] (G : SimpleGraph A) (S : Set A)
    (hS : ∀ x y, G.Adj x y → (x ∈ S ↔ y ∈ S)) (hpos : ∀ x, ∃ y, G.Adj x y)
    (D : SimpleGraph B) (hf : G.Free D) :
    Nat.card D.edgeSet ≤ extremalNumber (Fintype.card B) (G.induce S) +
      extremalNumber (Fintype.card B) (G.induce Sᶜ) + Fintype.card A * Fintype.card B := by
  by_contra hlt
  push Not at hlt
  have hE : D.edgeFinset.card = Nat.card D.edgeSet := by
    rw [edgeFinset_card, Nat.card_eq_fintype_card]
  have h1 : extremalNumber (Fintype.card B) (G.induce S) < D.edgeFinset.card := by
    omega
  obtain ⟨f⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset h1
  obtain ⟨D', hD'le, hiso, hcard⟩ := strip D (Finset.univ.image (fun a : S => f a))
  have hI : (Finset.univ.image (fun a : S => f a)).card ≤ Fintype.card A :=
    Finset.card_image_le.trans (Fintype.card_subtype_le _)
  have := Nat.mul_le_mul_right (Fintype.card B) hI
  have hE' : D'.edgeFinset.card = Nat.card D'.edgeSet := by
    rw [edgeFinset_card, Nat.card_eq_fintype_card]
  have h2 : extremalNumber (Fintype.card B) (G.induce Sᶜ) < D'.edgeFinset.card := by
    omega
  obtain ⟨g⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset h2
  have fI : ∀ s : S, f s ∈ Finset.univ.image (fun a : S => f a) :=
    fun s => Finset.mem_image_of_mem _ (Finset.mem_univ s)
  have gI : ∀ t : (Sᶜ : Set A), g t ∉ Finset.univ.image (fun a : S => f a) := by
    intro t ht
    obtain ⟨y, hy⟩ := hpos t
    have hyT : y ∈ Sᶜ := fun hyS => t.2 ((hS _ _ hy).2 hyS)
    exact hiso _ ht _ (g.toHom.map_adj (show (G.induce Sᶜ).Adj t ⟨y, hyT⟩ from hy))
  let h (x : A) : B := if hx : x ∈ S then f ⟨x, hx⟩ else g ⟨x, hx⟩
  have hSv (x : A) (hx : x ∈ S) : h x = f ⟨x, hx⟩ := by simp [h, hx]
  have hTv (x : A) (hx : x ∉ S) : h x = g ⟨x, hx⟩ := by simp [h, hx]
  apply hf
  refine ⟨⟨⟨h, ?_⟩, ?_⟩⟩
  · intro x y hxy
    by_cases hx : x ∈ S
    · have hy : y ∈ S := (hS _ _ hxy).1 hx
      rw [hSv x hx, hSv y hy]
      exact f.toHom.map_adj (show (G.induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
    · have hy : y ∉ S := fun hy => hx ((hS _ _ hxy).2 hy)
      rw [hTv x hx, hTv y hy]
      exact hD'le (g.toHom.map_adj (show (G.induce Sᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy))
  · intro x y hxy
    change h x = h y at hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · rw [hSv x hx, hSv y hy] at hxy
      exact congrArg Subtype.val (f.injective hxy)
    · rw [hSv x hx, hTv y hy] at hxy
      exact (gI ⟨y, hy⟩ (by rw [← hxy]; exact fI _)).elim
    · rw [hTv x hx, hSv y hy] at hxy
      exact (gI ⟨x, hx⟩ (by rw [hxy]; exact fI _)).elim
    · rw [hTv x hx, hTv y hy] at hxy
      exact congrArg Subtype.val (g.injective hxy)

theorem degree_induce_ge {q : ℕ} {G : SimpleGraph (Fin q)} (hd : ∀ v, 2 ≤ G.degree v)
    (T : Set (Fin q)) (hT : ∀ x y, G.Adj x y → (x ∈ T ↔ y ∈ T)) (v : T) :
    2 ≤ (G.induce T).degree v := by
  rw [degree_induce_of_neighborSet_subset (fun y hy => (hT _ _ hy).1 v.2)]
  exact hd v

theorem relabel {q : ℕ} {G : SimpleGraph (Fin q)} (hd : ∀ v, 2 ≤ G.degree v)
    (T : Set (Fin q)) (hT : ∀ x y, G.Adj x y → (x ∈ T ↔ y ∈ T))
    (a : Fin q) (ha : a ∈ T) (b : Fin q) (hb : b ∉ T) :
    ∃ (r : ℕ) (G' : SimpleGraph (Fin r)), 0 < r ∧ r < q ∧ G' ⊑ G ∧ (∀ v, 2 ≤ G'.degree v) ∧
      ∀ n, extremalNumber n G' = extremalNumber n (G.induce T) := by
  let e := Fintype.equivFin T
  let iso : G.induce T ≃g (G.induce T).map e.toEmbedding := Iso.map e (G.induce T)
  refine ⟨Fintype.card T, (G.induce T).map e.toEmbedding, Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩,
    ?_, ⟨(Copy.induce G T).comp iso.symm.toCopy⟩, ?_,
    fun n => extremalNumber_congr_right iso.symm⟩
  · have := Fintype.card_subtype_lt (p := (· ∈ T)) hb
    simp only [Fintype.card_fin] at this
    convert this
  intro v
  obtain ⟨x, rfl⟩ := iso.surjective v
  rw [iso.degree_eq]
  exact degree_induce_ge hd T hT x

end Split713

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1.H1 := by
  intro q G hq hd hc
  have hpos : ∀ x, ∃ y, G.Adj x y := by
    intro x
    obtain ⟨y, hy⟩ := Finset.card_pos.mp
      (show 0 < (G.neighborFinset x).card by rw [card_neighborFinset_eq_degree]; have := hd x; omega)
    exact ⟨y, (G.mem_neighborFinset _ _).mp hy⟩
  let u : Fin q := ⟨0, hq⟩
  obtain ⟨w, hw⟩ : ∃ w, ¬ G.Reachable u w := by
    by_contra h
    push Not at h
    exact hc ((connected_iff_exists_forall_reachable G).mpr ⟨u, h⟩)
  let S : Set (Fin q) := {x | G.Reachable u x}
  have hS : ∀ x y, G.Adj x y → (x ∈ S ↔ y ∈ S) := fun x y h =>
    ⟨fun hx => hx.trans h.reachable, fun hy => hy.trans h.symm.reachable⟩
  have hSc : ∀ x y, G.Adj x y → (x ∈ Sᶜ ↔ y ∈ Sᶜ) := fun x y h => not_congr (hS x y h)
  have huS : u ∈ S := Reachable.refl u
  have hwS : w ∉ S := hw
  obtain ⟨r₁, G₁, p₁, l₁, c₁, d₁, e₁⟩ := Split713.relabel hd S hS u huS w hwS
  obtain ⟨r₂, G₂, p₂, l₂, c₂, d₂, e₂⟩ :=
    Split713.relabel hd Sᶜ hSc w hwS u (show ¬ u ∈ Sᶜ from not_not.mpr huS)
  refine ⟨r₁, r₂, G₁, G₂, p₁, l₁, p₂, l₂, c₁, c₂, d₁, d₂, ?_⟩
  · intro n
    rw [e₁, e₂, ← Fintype.card_fin n, extremalNumber_le_iff]
    intro D dec hD
    have hE : D.edgeFinset.card = Nat.card D.edgeSet := by
      rw [edgeFinset_card, Nat.card_eq_fintype_card]
    rw [hE]
    have := Split713.combine G S hS hpos D hD
    simp only [Fintype.card_fin] at this ⊢
    exact this
