import FormalConjectures.ErdosProblems.«150»

/-! The five-cycle has five minimal cuts (the pairs of non-adjacent vertices), so `c(5) ≥ 5`,
whereas the question at `m = 1` would give `c(5) = 3`. -/

open SimpleGraph

namespace OMA

/-- The cycle on five vertices. -/
def c5 : SimpleGraph (Fin 5) where
  Adj a b := b = a + 1 ∨ a = b + 1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun a h => by revert h; revert a; decide⟩

/-- The pair of non-adjacent vertices `i`, `i + 2`. -/
def cut (i : Fin 5) : Set (Fin 5) := {x | x = i ∨ x = i + 2}

lemma finj : ∀ i j : Fin 5, (i = j ∨ i = j + 2) → (j = i ∨ j = i + 2) → i = j := by decide

lemma cut_injective : Function.Injective cut := by
  intro i j h
  have h1 : i ∈ cut j := by
    rw [← h]
    exact Or.inl rfl
  have h2 : j ∈ cut i := by
    rw [h]
    exact Or.inl rfl
  have h1' : i = j ∨ i = j + 2 := h1
  have h2' : j = i ∨ j = i + 2 := h2
  exact finj i j h1' h2'

lemma f34 : ∀ i : Fin 5, i + 4 = i + 3 + 1 ∨ i + 3 = i + 4 + 1 := by decide
lemma f40 : ∀ i : Fin 5, i = i + 4 + 1 ∨ i + 4 = i + 1 := by decide
lemma f32 : ∀ i : Fin 5, i + 2 = i + 3 + 1 ∨ i + 3 = i + 2 + 1 := by decide
lemma f21 : ∀ i : Fin 5, i + 1 = i + 2 + 1 ∨ i + 2 = i + 1 + 1 := by decide
lemma fcases : ∀ i x : Fin 5, x = i ∨ x = i + 1 ∨ x = i + 2 ∨ x = i + 3 ∨ x = i + 4 := by decide
lemma fm1 : ∀ i : Fin 5, ¬ (i + 1 = i ∨ i + 1 = i + 2) := by decide
lemma fm3 : ∀ i : Fin 5, ¬ (i + 3 = i ∨ i + 3 = i + 2) := by decide
lemma fm4 : ∀ i : Fin 5, ¬ (i + 4 = i ∨ i + 4 = i + 2) := by decide
lemma fstep : ∀ i w : Fin 5, ¬ (w = i ∨ w = i + 2) → (w = i + 1 + 1 ∨ i + 1 = w + 1) → False := by
  decide
lemma f13 : ∀ i : Fin 5, i + 3 ≠ i + 1 := by decide

lemma radj (S : Set (Fin 5)) {x y : Fin 5} (hx : x ∉ S) (hy : y ∉ S) (h : c5.Adj x y) :
    (c5.induce Sᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  (show (c5.induce Sᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩ from h).reachable

lemma conn (i : Fin 5) (S : Set (Fin 5)) (h1 : i + 1 ∉ S) (h3 : i + 3 ∉ S) (h4 : i + 4 ∉ S)
    (h : i ∉ S ∨ i + 2 ∉ S) : (c5.induce Sᶜ).Preconnected := by
  have a34 : c5.Adj (i + 3) (i + 4) := f34 i
  have a40 : c5.Adj (i + 4) i := f40 i
  have a32 : c5.Adj (i + 3) (i + 2) := f32 i
  have a01 : c5.Adj i (i + 1) := Or.inl rfl
  have a21 : c5.Adj (i + 2) (i + 1) := f21 i
  have key : ∀ x (hx : x ∉ S), (c5.induce Sᶜ).Reachable ⟨i + 3, h3⟩ ⟨x, hx⟩ := by
    intro x hx
    have hcases : x = i ∨ x = i + 1 ∨ x = i + 2 ∨ x = i + 3 ∨ x = i + 4 := fcases i x
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact (radj S h3 h4 a34).trans (radj S h4 hx a40)
    · rcases h with h0 | h2
      · exact ((radj S h3 h4 a34).trans (radj S h4 h0 a40)).trans (radj S h0 hx a01)
      · exact (radj S h3 h2 a32).trans (radj S h2 hx a21)
    · exact radj S h3 hx a32
    · exact Reachable.refl _
    · exact radj S h3 hx a34
  intro u v
  exact (key u.1 u.2).symm.trans (key v.1 v.2)

lemma not_conn (i : Fin 5) : ¬ (c5.induce (cut i)ᶜ).Preconnected := by
  intro h
  have m1 : i + 1 ∉ cut i := fm1 i
  have m3 : i + 3 ∉ cut i := fm3 i
  have hwalk : ∀ (u v : ↥(cut i)ᶜ) (p : (c5.induce (cut i)ᶜ).Walk u v),
      u.1 = i + 1 → v.1 = i + 1 := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons a b _ hadj _ ih =>
      intro ha
      exfalso
      have hb : ¬ (b.1 = i ∨ b.1 = i + 2) := b.2
      have hab : b.1 = a.1 + 1 ∨ a.1 = b.1 + 1 := hadj
      rw [ha] at hab
      exact fstep i b.1 hb hab
  obtain ⟨p⟩ := h ⟨i + 1, m1⟩ ⟨i + 3, m3⟩
  have h13 : i + 3 = i + 1 := hwalk _ _ p rfl
  exact f13 i h13

lemma cut_isMinimalCut (i : Fin 5) : Erdos150.IsMinimalCut c5 (cut i) := by
  refine ⟨not_conn i, ?_⟩
  intro S hS
  obtain ⟨hsub, hnot⟩ := hS
  have m1 : i + 1 ∉ S := fun hm => fm1 i (hsub hm)
  have m3 : i + 3 ∉ S := fun hm => fm3 i (hsub hm)
  have m4 : i + 4 ∉ S := fun hm => fm4 i (hsub hm)
  have h02 : i ∉ S ∨ i + 2 ∉ S := by
    by_contra hcon
    apply hnot
    intro x hx
    have hx' : x = i ∨ x = i + 2 := hx
    rcases hx' with rfl | rfl
    · by_contra h0
      exact hcon (Or.inl h0)
    · by_contra h2
      exact hcon (Or.inr h2)
  exact conn i S m1 m3 m4 h02

lemma five_le : 5 ≤ {T : Set (Fin 5) | Erdos150.IsMinimalCut c5 T}.ncard := by
  have hsub : cut '' Set.univ ⊆ {T : Set (Fin 5) | Erdos150.IsMinimalCut c5 T} := by
    rintro T ⟨i, -, rfl⟩
    exact cut_isMinimalCut i
  have hcard : (cut '' Set.univ).ncard = 5 := by
    rw [Set.ncard_image_of_injective _ cut_injective, Set.ncard_univ]
    simp
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

end OMA

theorem OMA.solution : type_of% @Erdos150.erdos_150.variants.erdos_nesetril := by
  intro h
  have h1 : Erdos150.maxMinimalCuts 5 = 3 := h 1
  have hbdd : BddAbove {k | ∃ G : SimpleGraph (Fin 5),
      {T : Set (Fin 5) | Erdos150.IsMinimalCut G T}.ncard = k} := by
    refine ⟨Nat.card (Set (Fin 5)), ?_⟩
    rintro k ⟨G, rfl⟩
    exact Set.ncard_le_card _
  have hle : {T : Set (Fin 5) | Erdos150.IsMinimalCut OMA.c5 T}.ncard ≤
      Erdos150.maxMinimalCuts 5 := le_csSup hbdd ⟨OMA.c5, rfl⟩
  have h5 := OMA.five_le
  omega
