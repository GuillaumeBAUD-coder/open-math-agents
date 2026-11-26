import FormalConjectures.ErdosProblems.«934»

-- Problem: Erdős Problem 934 — h one
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open SimpleGraph

namespace OMA

theorem one_le_edist {V : Type} (G : SimpleGraph V) {a b : V} (h : a ≠ b) :
    ((1 : ℕ) : ℕ∞) ≤ G.edist a b := by
  rw [Nat.cast_one, ENat.one_le_iff_ne_zero]
  intro h0
  exact h (SimpleGraph.edist_eq_zero_iff.mp h0)

theorem not_one_le_edist_self {V : Type} (G : SimpleGraph V) (a : V) :
    ¬ ((1 : ℕ) : ℕ∞) ≤ G.edist a a := by
  rw [Nat.cast_one, ENat.one_le_iff_ne_zero]
  intro h0
  exact h0 (SimpleGraph.edist_eq_zero_iff.mpr rfl)

/-- If every edge contains `u`, there are at most `deg u` edges. -/
theorem star_bound {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n)
    (h : ∀ a b, G.Adj a b → a = u ∨ b = u) : G.edgeSet.ncard ≤ (G.neighborSet u).ncard := by
  have hsub : G.edgeSet ⊆ (fun x => s(u, x)) '' G.neighborSet u := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro hab
    rw [mem_edgeSet] at hab
    rcases h a b hab with rfl | rfl
    · exact ⟨b, hab, rfl⟩
    · exact ⟨a, hab.symm, Sym2.eq_swap⟩
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

theorem upper (d : ℕ) (hd : d ≠ 2) (n : ℕ) (G : SimpleGraph (Fin n))
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d) (hE : d + 1 ≤ G.edgeSet.ncard) :
    Erdos934.HasFarEdges G 1 := by
  by_contra hfar
  have H : ∀ u v w x, G.Adj u v → G.Adj w x → (u = w ∨ u = x ∨ v = w ∨ v = x) := by
    intro u v w x huv hwx
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2, h3, h4⟩ := hne
    refine hfar ⟨u, v, w, x, huv, hwx, ?_⟩
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact one_le_edist G (by assumption)
  have hstar : ∀ u, ∃ a b, G.Adj a b ∧ a ≠ u ∧ b ≠ u := by
    intro u
    by_contra hno
    push Not at hno
    have := star_bound G u (fun a b hab => by
      by_cases ha : a = u
      · exact Or.inl ha
      · exact Or.inr (hno a b hab ha))
    have := hdeg u
    omega
  have hne : G.edgeSet.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    omega
  obtain ⟨e, he⟩ := hne
  revert he
  refine Sym2.ind (fun u v => ?_) e
  intro huv
  rw [mem_edgeSet] at huv
  have huv_ne : u ≠ v := G.ne_of_adj huv
  -- an edge at v avoiding u
  have hw : ∃ w, G.Adj v w ∧ w ≠ u := by
    obtain ⟨a, b, hab, hau, hbu⟩ := hstar u
    rcases H u v a b huv hab with h | h | h | h
    · exact absurd h.symm hau
    · exact absurd h.symm hbu
    · exact ⟨b, h ▸ hab, hbu⟩
    · exact ⟨a, h ▸ hab.symm, hau⟩
  have hx : ∃ x, G.Adj u x ∧ x ≠ v := by
    obtain ⟨a, b, hab, hav, hbv⟩ := hstar v
    rcases H u v a b huv hab with h | h | h | h
    · exact ⟨b, h ▸ hab, hbv⟩
    · exact ⟨a, h ▸ hab.symm, hav⟩
    · exact absurd h.symm hav
    · exact absurd h.symm hbv
  obtain ⟨w, hvw, hwu⟩ := hw
  obtain ⟨x, hux, hxv⟩ := hx
  have hxw : x = w := by
    rcases H u x v w hux hvw with h | h | h | h
    · exact absurd h huv_ne
    · exact absurd h.symm hwu
    · exact absurd h hxv
    · exact h
  subst hxw
  have hvx_ne : v ≠ x := G.ne_of_adj hvw
  -- all edges are among the three triangle edges
  have hsub : G.edgeSet ⊆ ({s(u, v), s(v, x), s(u, x)} : Set (Sym2 (Fin n))) := by
    intro e'
    refine Sym2.ind (fun a b => ?_) e'
    intro hab
    rw [mem_edgeSet] at hab
    have hab_ne : a ≠ b := G.ne_of_adj hab
    have h1 := H u v a b huv hab
    have h2 := H v x a b hvw hab
    have h3 := H u x a b hux hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
    simp only [Fin.ext_iff, ne_eq] at *
    omega
  have hcard3 : ({s(u, v), s(v, x), s(u, x)} : Set (Sym2 (Fin n))).ncard ≤ 3 := by
    calc ({s(u, v), s(v, x), s(u, x)} : Set (Sym2 (Fin n))).ncard
        ≤ ({s(v, x), s(u, x)} : Set (Sym2 (Fin n))).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (({s(u, x)} : Set (Sym2 (Fin n))).ncard + 1) + 1 :=
          Nat.add_le_add_right (Set.ncard_insert_le _ _) 1
      _ = 3 := by rw [Set.ncard_singleton]
  have hE3 : G.edgeSet.ncard ≤ 3 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hcard3
  have hdeg2 : 2 ≤ (G.neighborSet u).ncard := by
    have hsub2 : ({v, x} : Set (Fin n)) ⊆ G.neighborSet u := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact huv
      · exact hux
    calc 2 = ({v, x} : Set (Fin n)).ncard := (Set.ncard_pair hvx_ne).symm
      _ ≤ _ := Set.ncard_le_ncard hsub2 (Set.toFinite _)
  have := hdeg u
  omega

/-- The star with centre `0` on `d + 1` vertices. -/
def star (d : ℕ) : SimpleGraph (Fin (d + 1)) where
  Adj a b := a ≠ b ∧ (a = 0 ∨ b = 0)
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

theorem star_adj (d : ℕ) (a b : Fin (d + 1)) :
    (star d).Adj a b ↔ a ≠ b ∧ (a = 0 ∨ b = 0) := Iff.rfl

theorem lower (d m : ℕ)
    (hm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → Erdos934.HasFarEdges G 1) :
    d + 1 ≤ m := by
  classical
  by_contra hlt
  have hmd : m ≤ d := by omega
  have hdeg : ∀ v, ((star d).neighborSet v).ncard ≤ d := by
    intro v
    have hsub : (star d).neighborSet v ⊆ ({v}ᶜ : Set (Fin (d + 1))) := by
      intro y hy
      have : v ≠ y ∧ (v = 0 ∨ y = 0) := (star_adj d v y).mp hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h => this.1 h.symm
    have hc : ({v}ᶜ : Set (Fin (d + 1))).ncard = d := by
      have := Set.ncard_add_ncard_compl ({v} : Set (Fin (d + 1)))
      rw [Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at this
      omega
    exact le_of_le_of_eq (Set.ncard_le_ncard hsub (Set.toFinite _)) hc
  have hedges : m ≤ (star d).edgeSet.ncard := by
    have hinj : Function.Injective (fun i : Fin d => s((0 : Fin (d + 1)), i.succ)) := by
      intro i j hij
      simp only [Sym2.eq_iff] at hij
      rcases hij with ⟨-, h⟩ | ⟨h, -⟩
      · exact Fin.succ_injective _ h
      · exact absurd h.symm (Fin.succ_ne_zero _)
    have hsub : Set.range (fun i : Fin d => s((0 : Fin (d + 1)), i.succ)) ⊆ (star d).edgeSet := by
      rintro e ⟨i, rfl⟩
      rw [mem_edgeSet]
      exact (star_adj d _ _).mpr ⟨(Fin.succ_ne_zero i).symm, Or.inl rfl⟩
    have hr : (Set.range (fun i : Fin d => s((0 : Fin (d + 1)), i.succ))).ncard = d := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    calc m ≤ d := hmd
      _ = _ := hr.symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  obtain ⟨u, v, w, x, huv, hwx, hfar⟩ := hm (d + 1) (star d) hdeg hedges
  have h0uv : (0 : Fin (d + 1)) ∈ ({u, v} : Set (Fin (d + 1))) := by
    rcases ((star_adj d u v).mp huv).2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have h0wx : (0 : Fin (d + 1)) ∈ ({w, x} : Set (Fin (d + 1))) := by
    rcases ((star_adj d w x).mp hwx).2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  exact not_one_le_edist_self _ _ (hfar 0 h0uv 0 h0wx)

end OMA

theorem OMA.solution : type_of% @Erdos934.erdos_934.variants.h_one := by
  intro d hd
  unfold Erdos934.h
  refine le_antisymm (Nat.sInf_le (OMA.upper d hd)) (le_csInf ⟨d + 1, OMA.upper d hd⟩ ?_)
  intro m hm
  exact OMA.lower d m hm
