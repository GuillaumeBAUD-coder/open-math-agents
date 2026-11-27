import FormalConjectures.ErdosProblems.«64»

/-! Reduction of the Erdős–Gyárfás problem to blocks with at most one exceptional
vertex. The separation hypothesis states that after deleting any vertex, every
nontrivial partition has a crossing edge. For related cut-vertex structure of
minimal counterexamples, see Guillaume Ducoffe and Bogdan Dumitru, arXiv:2609.28594,
Theorem 2.3. Finite relabelling and cycle lifting follow the earlier reduction
Erdos64.erdos_64.R1 (project pull request 466). -/

namespace OMA.R_Erdos64_erdos_64_R3

open SimpleGraph

def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree →
    (∀ (a : V) (S : Set V), a ∈ S → (∃ x ∈ S, x ≠ a) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ ∃ y ∉ S, G.Adj x y) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.degree r = 2 → (∀ x, x ≠ r → 3 ≤ G.degree x) →
    (∀ (a : V) (S : Set V), a ∈ S → (∃ x ∈ S, x ≠ a) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ ∃ y ∉ S, G.Adj x y) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

theorem solve_rooted (solid : H1) (deficient : H2) (n : ℕ) :
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
      Fintype.card V = n → (∃ x : V, x ≠ r) → (∀ x, x ≠ r → 3 ≤ G.degree x) →
      ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G finite dec r size nontrivial high
    classical
    by_cases block : (∀ (a : V) (S : Set V), a ∈ S → (∃ x ∈ S, x ≠ a) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ ∃ y ∉ S, G.Adj x y)
    · by_cases low : G.degree r < 3
      · have another (a : V) (ha : a ≠ r) : ∃ y, G.Adj r y ∧ y ≠ a := by
          have enough : 1 < (G.neighborFinset a).card := by
            rw [card_neighborFinset_eq_degree]
            exact (by decide : 1 < 3).trans_le (high a ha)
          obtain ⟨z, hz, hzr⟩ := Finset.exists_mem_ne enough r
          have hza := ((G.mem_neighborFinset a z).mp hz).ne.symm
          have outside : z ∉ ({r, a} : Set V) := by simp [hzr, hza]
          obtain ⟨x, hx, hxa, y, hy, hxy⟩ :=
            block a {r, a} (by simp) ⟨r, by simp, ha.symm⟩ ⟨z, outside⟩
          have hxr : x = r := by simpa [hxa] using hx
          subst x
          exact ⟨y, hxy, fun eq => hy (by simp [eq])⟩
        obtain ⟨a, ha⟩ := nontrivial
        obtain ⟨b, hb, _⟩ := another a ha
        obtain ⟨c, hc, hcb⟩ := another b hb.ne.symm
        have two : 1 < (G.neighborFinset r).card := Finset.one_lt_card.mpr
          ⟨b, (G.mem_neighborFinset r b).mpr hb, c, (G.mem_neighborFinset r c).mpr hc, hcb.symm⟩
        rw [card_neighborFinset_eq_degree] at two
        exact deficient V G r (by omega) high block
      · have : Nonempty V := ⟨r⟩
        apply solid V G _ block
        apply G.le_minDegree_of_forall_le_degree 3
        intro x
        by_cases eq : x = r
        · subst x
          omega
        · exact high x eq
    push Not at block
    obtain ⟨a, S, ha, ⟨u, hu, hua⟩, ⟨v, hv⟩, separated⟩ := block
    have shrink (T : Set V) (atop : a ∈ T) (b : V) (hb : b ∈ T) (hba : b ≠ a)
        (miss : ∃ z : V, z ∉ T) (away : ∀ x ∈ T, x ≠ a → x ≠ r)
        (closedSide : ∀ x ∈ T, x ≠ a → G.neighborSet x ⊆ T) :
        ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
      let H := G.induce T
      let pivot : T := ⟨a, atop⟩
      obtain ⟨z, hz⟩ := miss
      have smaller : Fintype.card T < Fintype.card V :=
        Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
          (b := z) (fun ⟨x, eq⟩ => hz (eq ▸ x.property))
      have other : ∃ x : T, x ≠ pivot :=
        ⟨⟨b, hb⟩, fun h => hba (congrArg Subtype.val h)⟩
      have inherited (x : T) (hx : x ≠ pivot) : 3 ≤ H.degree x := by
        have ne : x.val ≠ a := fun h => hx (Subtype.ext h)
        change 3 ≤ (G.induce T).degree x
        rw [degree_induce_of_neighborSet_subset (closedSide x.val x.property ne)]
        exact high x.val (away x.val x.property ne)
      obtain ⟨k, x, c, hk, hc, hl⟩ := ih _ (size ▸ smaller) T H pivot rfl other inherited
      let lift : H →g G := ⟨Subtype.val, fun h => h⟩
      exact ⟨k, x.val, c.map lift, hk, hc.map Subtype.val_injective, by simpa using hl⟩
    by_cases rootHere : r ∈ S
    · let T : Set V := {x | x = a ∨ x ∉ S}
      refine shrink T (Or.inl rfl) v (Or.inr hv) (fun eq => hv (eq ▸ ha)) ⟨u, ?_⟩ ?_ ?_
      · intro h
        exact h.elim hua (fun hn => hn hu)
      · intro x hx hxa hxr
        exact (hx.resolve_left hxa) (hxr ▸ rootHere)
      · intro x hx hxa y hxy
        by_cases hya : y = a
        · exact Or.inl hya
        · right
          intro hy
          exact separated y hy hya x (hx.resolve_left hxa) (G.adj_symm hxy)
    · apply shrink S ha u hu hua ⟨v, hv⟩
      · intro x hx _ hxr
        exact rootHere (hxr ▸ hx)
      · intro x hx hxa y hxy
        by_contra hy
        exact separated x hx hxa y hy hxy

theorem main : H1 → H2 → type_of% @Erdos64.erdos_64 := by
  intro solid deficient V G finite dec minimum
  classical
  let e := (Fintype.equivFin V).symm
  let H := G.comap e
  let i : H ≃g G := SimpleGraph.Iso.comap e G
  have minimumH : 3 ≤ H.minDegree := i.minDegree_eq ▸ minimum
  have existsRoot : Nonempty (Fin (Fintype.card V)) := by
    rcases isEmpty_or_nonempty (Fin (Fintype.card V)) with empty | nonempty
    · have := empty
      have hz := H.minDegree_of_subsingleton
      omega
    · exact nonempty
  obtain ⟨r⟩ := existsRoot
  have high (x : Fin (Fintype.card V)) := minimumH.trans (H.minDegree_le_degree x)
  obtain ⟨w, hw⟩ := (H.degree_pos_iff_exists_adj r).mp (Nat.lt_of_lt_of_le (by decide : 0 < 3) (high r))
  obtain ⟨k, v, c, hk, hc, hl⟩ := solve_rooted solid deficient _ _ H r rfl ⟨w, hw.ne.symm⟩
    (fun x _ => high x)
  exact ⟨k, i v, c.map i.toHom, hk, hc.map i.injective, by simpa using hl⟩

end OMA.R_Erdos64_erdos_64_R3
