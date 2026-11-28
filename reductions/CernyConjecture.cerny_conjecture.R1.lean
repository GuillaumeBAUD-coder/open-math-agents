import FormalConjectures.Wikipedia.CernyConjecture

-- Reduction CernyConjecture.cerny_conjecture.R1 of the Cerny conjecture: commutative automata
-- versus the rest.
-- Credit: @marcusbuffett
--
-- H1 (commutative automata, Rystsov 1997): if the letters of a synchronizing DFA act by
-- commuting maps, it has a synchronizing word of length at most n - 1, which is at most
-- (n - 1)^2. With commuting letters the image of the state set only shrinks along a word, so a
-- letter that does not shrink it can be deleted.
-- H2 (open core): the conjecture for synchronizing automata with two non-commuting letters.
--
-- Both are stated for alphabets and state sets in Type. The lemma small_model below moves any
-- automaton to states Fin n and to the alphabet of its letter actions, which lies in Type, while
-- keeping commutativity and the lengths of synchronizing words.

namespace OMA.R_CernyConjecture_cerny_conjecture_R1

/-- Commutative synchronizing automata have a reset word of length at most `n - 1`. -/
def H1 : Prop :=
  ∀ {α : Type} {σ : Type} [Fintype σ] (M : DFA α σ),
    (∀ (q : σ) (a b : α), M.step (M.step q a) b = M.step (M.step q b) a) →
    M.IsSynchronizing →
    ∃ w : List α, M.IsSynchronizingWord w ∧ w.length ≤ Fintype.card σ - 1

/-- The Cerny bound for synchronizing automata that are not commutative. -/
def H2 : Prop :=
  ∀ {α : Type} {σ : Type} [Fintype σ] (M : DFA α σ),
    (¬ ∀ (q : σ) (a b : α), M.step (M.step q a) b = M.step (M.step q b) a) →
    M.IsSynchronizing →
    ∃ w : List α, M.IsSynchronizingWord w ∧ w.length ≤ (Fintype.card σ - 1) ^ 2

universe u v

lemma evalFrom_map {α : Type u} {σ : Type v} {β : Type} {n : ℕ} (M : DFA α σ)
    (N : DFA β (Fin n)) (e : σ ≃ Fin n) (f : α → β)
    (hN : ∀ q a, N.step (e q) (f a) = e (M.step q a)) :
    ∀ (w : List α) (q : σ), N.evalFrom (e q) (w.map f) = e (M.evalFrom q w) := by
  intro w
  induction w with
  | nil => intro q; simp [DFA.evalFrom_nil]
  | cons a w ih => intro q; rw [List.map_cons, DFA.evalFrom_cons, DFA.evalFrom_cons, hN, ih]

lemma small_model {α : Type u} {σ : Type v} [Fintype σ] (M : DFA α σ)
    (hM : M.IsSynchronizing) :
    ∃ (β : Type) (N : DFA β (Fin (Fintype.card σ))),
      ((∀ (q : σ) (a b : α), M.step (M.step q a) b = M.step (M.step q b) a) ↔
        (∀ (q : Fin (Fintype.card σ)) (a b : β), N.step (N.step q a) b = N.step (N.step q b) a)) ∧
      N.IsSynchronizing ∧
      ∀ u : List β, N.IsSynchronizingWord u →
        ∃ w : List α, M.IsSynchronizingWord w ∧ w.length = u.length := by
  classical
  obtain ⟨w0, p, hp⟩ := hM
  let e := Fintype.equivFin σ
  let f : α → (Fin (Fintype.card σ) → Fin (Fintype.card σ)) := fun a i => e (M.step (e.symm i) a)
  let N : DFA (Set.range f) (Fin (Fintype.card σ)) := ⟨fun i g => g.1 i, e p, ∅⟩
  let f' : α → Set.range f := fun a => ⟨f a, a, rfl⟩
  have hN : ∀ q a, N.step (e q) (f' a) = e (M.step q a) := by
    intro q a; simp [N, f', f]
  have hev := evalFrom_map M N e f' hN
  refine ⟨Set.range f, N, ⟨?_, ?_⟩, ⟨w0.map f', e p, ?_⟩, ?_⟩
  · intro hc i g h
    obtain ⟨_, a, rfl⟩ := g
    obtain ⟨_, b, rfl⟩ := h
    simp only [N, f, Equiv.symm_apply_apply, hc]
  · intro hc q a b
    have := hc (e q) (f' a) (f' b)
    simp only [N, f', f, Equiv.symm_apply_apply] at this
    exact e.injective this
  · intro i
    obtain ⟨q, rfl⟩ := e.surjective i
    rw [hev, hp]
  · rintro u ⟨r, hr⟩
    refine ⟨u.map (fun g => Classical.choose g.2), ⟨e.symm r, fun q => ?_⟩, by simp⟩
    have hmap : (u.map (fun g => Classical.choose g.2)).map f' = u := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id u]
      apply List.map_congr_left
      intro g _
      exact Subtype.ext (Classical.choose_spec g.2)
    have := hev (u.map (fun g => Classical.choose g.2)) q
    rw [hmap, hr] at this
    rw [this, Equiv.symm_apply_apply]

theorem main : H1 → H2 → type_of% @CernyConjecture.cerny_conjecture := by
  intro h1 h2 α σ _ M hM
  obtain ⟨β, N, hiff, hN, hlift⟩ := small_model M hM
  by_cases hc : ∀ (q : σ) (a b : α), M.step (M.step q a) b = M.step (M.step q b) a
  · obtain ⟨u, hu, hlen⟩ := h1 N (hiff.mp hc) hN
    obtain ⟨w, hw, hwl⟩ := hlift u hu
    refine ⟨w, hw, ?_⟩
    rw [hwl]
    rw [Fintype.card_fin] at hlen
    refine hlen.trans ?_
    rcases Nat.eq_zero_or_pos (Fintype.card σ - 1) with h | h
    · simp [h]
    · exact Nat.le_self_pow two_ne_zero _
  · obtain ⟨u, hu, hlen⟩ := h2 N (fun h => hc (hiff.mpr h)) hN
    obtain ⟨w, hw, hwl⟩ := hlift u hu
    refine ⟨w, hw, ?_⟩
    rw [hwl]
    simpa [Fintype.card_fin] using hlen

end OMA.R_CernyConjecture_cerny_conjecture_R1
