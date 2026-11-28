import FormalConjectures.Wikipedia.MeynielConjecture

-- Credit: @dimitrismoustakas

/-!
# Reducing Meyniel's conjecture to bipartite Hamiltonian graphs

H1 gives a closed tour of a connected graph G that visits all n vertices. For n ≥ 2,
the tour has 2(n − 1) entries. Doubling each entry produces a bipartite Hamiltonian
graph J on N = 4(n − 1) vertices. Mark one entry for each vertex of G. All additional
edges join marked entries, so at most 2n = N/2 + 2 vertices of J have degree above two.

Every cop move in J projects to a legal move in G, and every robber move in G lifts
between marked vertices in J. Thus c(G) ≤ c(J). H2 bounds c(J) by C√N on this class,
which yields c(G) ≤ 2C√n. For n = 1 the same construction uses two stationary
tour entries and a four-cycle.
-/

namespace OMA.R_MeynielConjecture_meyniel_conjecture_R2

open MeynielConjecture SimpleGraph

/-- A connected graph of order at least two has a spanning closed tour of length twice its
order minus two. A singleton has a tour of two stationary steps. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    ∃ w : Fin (2 * (Fintype.card V - 2) + 2) → V,
      Function.Surjective w ∧ ∀ i, Step G (w i) (w (i + 1))

/-- Meyniel's bound for bipartite Hamiltonian graphs in which at most half the vertices,
plus two, have more than two neighbors. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (W : Type) [Fintype W] [DecidableEq W] (J : SimpleGraph W),
    J.IsBipartite → J.IsHamiltonian →
    2 * ({x | 2 < (J.neighborSet x).ncard} : Set W).ncard ≤ Fintype.card W + 4 →
    (copNumber J : ℝ) ≤ C * Real.sqrt (Fintype.card W)

/-- Project a capture strategy through a map preserving cop moves. Robber replies need only
lift inside the designated set of robber positions. The remaining round budget is preserved. -/
lemma catch_project {V W : Type} {G : SimpleGraph V} {J : SimpleGraph W} (p : W → V)
    (S : Set W)
    (forward : ∀ {x y}, Step J x y → Step G (p x) (p y))
    (lift : ∀ x ∈ S, ∀ v, Step G (p x) v → ∃ y ∈ S, Step J x y ∧ p y = v)
    (k : ℕ) : ∀ (m : ℕ) (c : Fin k → W) (r : W), r ∈ S → CopsCatchWithin J k m c r →
      CopsCatchWithin G k m (fun i => p (c i)) (p r) := by
  intro m
  induction m with
  | zero =>
    rintro c r _ ⟨i, hi⟩
    exact ⟨i, congrArg p hi⟩
  | succ m ih =>
    rintro c r hr (⟨i, hi⟩ | ⟨c', hs, ⟨i, hi⟩ | hn⟩)
    · exact Or.inl ⟨i, congrArg p hi⟩
    · exact Or.inr ⟨fun i => p (c' i), fun i => forward (hs i),
        Or.inl ⟨i, congrArg p hi⟩⟩
    · refine Or.inr ⟨fun i => p (c' i), fun i => forward (hs i), Or.inr ?_⟩
      intro v hv
      obtain ⟨y, hyS, hy, rfl⟩ := lift r hr v hv
      exact ih c' y hyS (hn y hy)

lemma copNumber_project {V W : Type} [Fintype W] {G : SimpleGraph V} {J : SimpleGraph W}
    (p : W → V) (S : Set W) (onto : ∀ v, ∃ x ∈ S, p x = v)
    (forward : ∀ {x y}, Step J x y → Step G (p x) (p y))
    (lift : ∀ x ∈ S, ∀ v, Step G (p x) v → ∃ y ∈ S, Step J x y ∧ p y = v) :
    copNumber G ≤ copNumber J := by
  have hw : CopsWin J (copNumber J) :=
    Nat.sInf_mem (s := {k | CopsWin J k}) ⟨_, copsWin_card J⟩
  obtain ⟨c, hc⟩ := hw
  apply Nat.sInf_le (s := {k | CopsWin G k})
  refine ⟨fun i => p (c i), fun v => ?_⟩
  obtain ⟨r, hr, rfl⟩ := onto v
  obtain ⟨m, hm⟩ := hc r
  exact ⟨m, catch_project p S forward lift _ m c r hr hm⟩

/-- The pairs in cyclic order provide a spanning cycle in Mathlib's sense. -/
private lemma alternating_hamiltonian (m : ℕ) (J : SimpleGraph (Fin (m + 2) × Bool))
    (pair : ∀ i, J.Adj (i, false) (i, true))
    (next : ∀ i, J.Adj (i, true) (i + 1, false)) : J.IsHamiltonian := by
  let index (i : Fin (2 * m + 4)) : Fin (m + 2) := ⟨i.val / 2, by have := i.isLt; omega⟩
  let d (i : Fin (2 * m + 4)) := (index i, if i.val % 2 = 0 then false else true)
  have inj : Function.Injective d := by
    intro i j h
    have hq := congrArg (fun x : Fin (m + 2) × Bool => x.1.val) h
    have hc := congrArg Prod.snd h
    change i.val / 2 = j.val / 2 at hq
    change (if i.val % 2 = 0 then false else true) =
      (if j.val % 2 = 0 then false else true) at hc
    apply Fin.ext
    split_ifs at hc <;> first | contradiction | omega
  have along (i : Fin (2 * m + 4)) : J.Adj (d i) (d (i + 1)) := by
    have hi := i.isLt
    by_cases hn : i.val + 1 < 2 * m + 4
    · have hs := Fin.val_add_one_of_lt' hn
      by_cases he : i.val % 2 = 0
      · have ho : (i + 1).val % 2 ≠ 0 := by omega
        have hq : index (i + 1) = index i := by
          apply Fin.ext
          change (i + 1).val / 2 = i.val / 2
          omega
        simpa only [d, if_pos he, if_neg ho, hq] using pair (index i)
      · have he' : (i + 1).val % 2 = 0 := by omega
        have hb : (index i).val + 1 < m + 2 := by dsimp [index]; omega
        have hq : index (i + 1) = index i + 1 := by
          apply Fin.ext
          rw [Fin.val_add_one_of_lt' hb]
          change (i + 1).val / 2 = i.val / 2 + 1
          omega
        simpa only [d, if_neg he, if_pos he', hq] using next (index i)
    · have hi' : i = Fin.last (2 * m + 3) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst i
      have hl : index (Fin.last (2 * m + 3)) = Fin.last (m + 1) := by
        apply Fin.ext
        change (2 * m + 3) / 2 = m + 1
        omega
      have hz : index 0 = 0 := by apply Fin.ext; simp [index]
      have ho : (2 * m + 3) % 2 ≠ 0 := by omega
      simpa [d, hl, hz, ho] using next (Fin.last (m + 1))
  have copy : (cycleGraph (2 * m + 4)).IsContained J := by
    refine ⟨⟨⟨d, ?_⟩, inj⟩⟩
    intro i j hij
    rcases cycleGraph_adj.mp hij with h | h
    · have heq : i = j + 1 := sub_eq_iff_eq_add'.mp h
      simpa only [heq] using (along j).symm
    · have heq : j = i + 1 := sub_eq_iff_eq_add'.mp h
      simpa only [heq] using along i
  obtain ⟨x, p, hc, hl⟩ := (cycleGraph_isContained_iff (by omega : 2 < 2 * m + 4)).mp copy
  intro _
  refine ⟨x, p, Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hc, ?_⟩⟩
  rw [hl]
  simp [Fintype.card_prod]
  omega

/-- Duplicate every entry of the tour and mark one column per original vertex. Besides the
Hamiltonian cycle, the only edges join marked representatives with a legal projected move. -/
theorem lift_of_tour_with_moves {V : Type} (G : SimpleGraph V) (m : ℕ)
    (w : Fin (m + 2) → V) (hw : Function.Surjective w)
    (hnext : ∀ i, Step G (w i) (w (i + 1))) :
    ∃ J : SimpleGraph (Fin (m + 2) × Bool),
      J.IsBipartite ∧ J.IsHamiltonian ∧ copNumber G ≤ copNumber J ∧
      ∃ mark : V → Fin (m + 2), Function.LeftInverse w mark ∧
        (∀ x y, J.Adj x y → x.2 ≠ y.2 ∧ (x.1 = y.1 ∨ (x.2 = true ∧ y.1 = x.1 + 1) ∨
          (y.2 = true ∧ x.1 = y.1 + 1) ∨ (x.1 ∈ Set.range mark ∧ y.1 ∈ Set.range mark))) ∧
        (∀ {x y}, Step J x y → Step G (w x.1) (w y.1)) ∧
        (∀ i, J.Adj (i, false) (i, true)) ∧ ∀ i, J.Adj (i, true) (i + 1, false) := by
  classical
  let mark (v : V) := Classical.choose (hw v)
  have label (v : V) : w (mark v) = v := Classical.choose_spec (hw v)
  let p : Fin (m + 2) × Bool → V := fun x => w x.1
  let S : Set (Fin (m + 2) × Bool) := {x | x.1 ∈ Set.range mark}
  let rail (x y : Fin (m + 2) × Bool) := x.2 = true ∧ y.1 = x.1 + 1
  let J : SimpleGraph (Fin (m + 2) × Bool) :=
    { Adj := fun x y => x.2 ≠ y.2 ∧ Step G (p x) (p y) ∧
        (x.1 = y.1 ∨ rail x y ∨ rail y x ∨ (x ∈ S ∧ y ∈ S))
      symm := ⟨by
        intro x y h
        refine ⟨Ne.symm h.1, ?_, ?_⟩
        · rcases h.2.1 with e | e
          · exact Or.inl e.symm
          · exact Or.inr e.symm
        · rcases h.2.2 with e | e | e | e
          · exact Or.inl e.symm
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (Or.inr ⟨e.2, e.1⟩))⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  have marked (v : V) (b : Bool) : (mark v, b) ∈ S := ⟨v, rfl⟩
  have onto (v : V) : ∃ x ∈ S, p x = v := ⟨(mark v, false), marked v false, label v⟩
  have forward : ∀ {x y}, Step J x y → Step G (p x) (p y) := by
    rintro x y (rfl | h)
    · exact Or.inl rfl
    · exact h.2.1
  have lift : ∀ x ∈ S, ∀ v, Step G (p x) v → ∃ y ∈ S, Step J x y ∧ p y = v := by
    intro x hx v hv
    have hy := marked v (!x.2)
    refine ⟨(mark v, !x.2), hy, Or.inr ⟨?_, ?_, Or.inr (Or.inr (Or.inr ⟨hx, hy⟩))⟩, label v⟩
    · change x.2 ≠ !x.2
      cases x.2 <;> decide
    · change Step G (p x) (w (mark v))
      rw [label]
      exact hv
  have pair (i) : J.Adj (i, false) (i, true) := ⟨Bool.false_ne_true, Or.inl rfl, Or.inl rfl⟩
  have next (i) : J.Adj (i, true) (i + 1, false) :=
    ⟨Ne.symm Bool.false_ne_true, hnext i, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  refine ⟨J, ?_, alternating_hamiltonian m J pair next,
    copNumber_project (G := G) (J := J) p S onto forward lift, mark, label,
    (fun _ _ h => ⟨h.1, h.2.2⟩), (fun e => forward e), pair, next⟩
  refine ⟨Coloring.mk (fun x => if x.2 then (1 : Fin 2) else 0) ?_⟩
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hne : b ≠ c := h.1
  change (if b then (1 : Fin 2) else 0) ≠ (if c then (1 : Fin 2) else 0)
  cases b <;> cases c <;> first | exact (hne rfl).elim | decide

theorem lift_of_tour {V : Type} (G : SimpleGraph V) (m : ℕ)
    (w : Fin (m + 2) → V) (hw : Function.Surjective w)
    (hnext : ∀ i, Step G (w i) (w (i + 1))) :
    ∃ J : SimpleGraph (Fin (m + 2) × Bool),
      J.IsBipartite ∧ J.IsHamiltonian ∧ copNumber G ≤ copNumber J ∧
      ∃ mark : V → Fin (m + 2), Function.LeftInverse w mark ∧
        ∀ x y, J.Adj x y → x.2 ≠ y.2 ∧ (x.1 = y.1 ∨ (x.2 = true ∧ y.1 = x.1 + 1) ∨
          (y.2 = true ∧ x.1 = y.1 + 1) ∨ (x.1 ∈ Set.range mark ∧ y.1 ∈ Set.range mark)) := by
  obtain ⟨J, hb, hh, hk, mark, left, edges, _⟩ := lift_of_tour_with_moves G m w hw hnext
  exact ⟨J, hb, hh, hk, mark, left, edges⟩

/-- The cyclic order gives both possible neighbors of each unmarked vertex. -/
lemma unmarked_neighbors {V : Type} {m : ℕ} (J : SimpleGraph (Fin (m + 2) × Bool))
    (mark : V → Fin (m + 2))
    (edges : ∀ x y, J.Adj x y → x.2 ≠ y.2 ∧ (x.1 = y.1 ∨
      (x.2 = true ∧ y.1 = x.1 + 1) ∨ (y.2 = true ∧ x.1 = y.1 + 1) ∨
      (x.1 ∈ Set.range mark ∧ y.1 ∈ Set.range mark))) {i : Fin (m + 2)} (b : Bool)
    (unmarked : i ∉ Set.range mark) :
    J.neighborSet (i, b) ⊆ {(i, !b), ((if b then i + 1 else i - 1), !b)} := by
  let other : Fin (m + 2) := if b then i + 1 else i - 1
  rintro ⟨j, c⟩ h
  obtain ⟨hc, hr⟩ := edges (i, b) (j, c) h
  change b ≠ c at hc
  have hcolor : c = !b := by cases b <;> cases c <;> first | rfl | exact (hc rfl).elim
  change (j, c) = (i, !b) ∨ (j, c) = (other, !b)
  rcases hr with hsame | ⟨hb, hj⟩ | ⟨ht, hprev⟩ | hm
  · exact Or.inl (Prod.ext hsame.symm hcolor)
  · change b = true at hb
    exact Or.inr (Prod.ext (by simpa [other, hb] using hj) hcolor)
  · change c = true at ht
    have hb : b = false := by cases b <;> first | rfl | exact (hc ht.symm).elim
    have hj : j = i - 1 := eq_sub_iff_add_eq.mpr hprev.symm
    exact Or.inr (Prod.ext (by simpa [other, hb] using hj) hcolor)
  · exact (unmarked hm.1).elim

/-- Outside the marked columns there are only two possible neighbors: the other color in
the same column and the next or previous vertex of the alternating Hamiltonian cycle. -/
lemma branch_count {V : Type} [Fintype V] {m : ℕ} (J : SimpleGraph (Fin (m + 2) × Bool))
    (mark : V → Fin (m + 2)) (hinj : Function.Injective mark)
    (edges : ∀ x y, J.Adj x y → x.2 ≠ y.2 ∧ (x.1 = y.1 ∨
      (x.2 = true ∧ y.1 = x.1 + 1) ∨ (y.2 = true ∧ x.1 = y.1 + 1) ∨
      (x.1 ∈ Set.range mark ∧ y.1 ∈ Set.range mark))) :
    ({x | 2 < (J.neighborSet x).ncard} : Set _).ncard ≤ 2 * Fintype.card V := by
  let rep (z : V × Bool) := (mark z.1, z.2)
  have hi : Function.Injective rep := by
    rintro ⟨u, b⟩ ⟨v, c⟩ h
    change (mark u, b) = (mark v, c) at h
    exact Prod.ext (hinj (congrArg Prod.fst h)) (congrArg (fun z : Fin (m + 2) × Bool => z.2) h)
  have hsub : {x | 2 < (J.neighborSet x).ncard} ⊆ Set.range rep := by
    rintro ⟨i, b⟩ hbranch
    by_contra hout
    have unmarked : i ∉ Set.range mark := by
      rintro ⟨v, hv⟩
      exact hout ⟨(v, b), Prod.ext hv rfl⟩
    let other : Fin (m + 2) := if b then i + 1 else i - 1
    have two : J.neighborSet (i, b) ⊆ {(i, !b), (other, !b)} := unmarked_neighbors J mark edges b unmarked
    have hpair : ({(i, !b), (other, !b)} : Set _).ncard ≤ 2 := by
      simpa only [Set.ncard_singleton] using Set.ncard_insert_le (i, !b) {(other, !b)}
    exact (not_lt_of_ge ((Set.ncard_le_ncard two).trans hpair)) hbranch
  calc
    _ ≤ (Set.range rep).ncard := Set.ncard_le_ncard hsub
    _ = Nat.card (V × Bool) := Set.ncard_range_of_injective hi
    _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_prod, Nat.mul_comm]

theorem main : H1 → H2 → type_of% @MeynielConjecture.meyniel_conjecture := by
  rintro htour ⟨C, hC, hbound⟩
  refine ⟨2 * C, by positivity, fun V _ G hG => ?_⟩
  have : Nonempty V := hG.nonempty
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  let m := 2 * (Fintype.card V - 2)
  have hsize : m + 2 ≤ 2 * Fintype.card V := by dsimp [m]; omega
  obtain ⟨w, hw, hnext⟩ := htour V G hG
  obtain ⟨J, hb, hh, hcop, mark, hinv, edges⟩ := lift_of_tour G m w hw hnext
  have hbranch := branch_count J mark hinv.injective edges
  have hsparse : 2 * ({x | 2 < (J.neighborSet x).ncard} : Set _).ncard ≤
      Fintype.card (Fin (m + 2) × Bool) + 4 := by
    calc
      _ ≤ 2 * (2 * Fintype.card V) := Nat.mul_le_mul_left 2 hbranch
      _ ≤ _ := by
        simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        dsimp only [m]
        omega
  have hJ := hbound _ J hb hh hsparse
  have hcard : (Fintype.card (Fin (m + 2) × Bool) : ℝ) = 2 * ((m + 2 : ℕ) : ℝ) := by
    simp [Fintype.card_prod]
    ring
  rw [hcard] at hJ
  have hsizeR : ((m + 2 : ℕ) : ℝ) ≤ 2 * (Fintype.card V : ℝ) := by
    exact_mod_cast hsize
  have hfour : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt : Real.sqrt (2 * ((m + 2 : ℕ) : ℝ)) ≤ 2 * Real.sqrt (Fintype.card V) := by
    calc
      _ ≤ Real.sqrt (4 * (Fintype.card V : ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hfour]
  calc
    (copNumber G : ℝ) ≤ (copNumber J : ℝ) := by exact_mod_cast hcop
    _ ≤ _ := hJ
    _ ≤ C * (2 * Real.sqrt (Fintype.card V)) := mul_le_mul_of_nonneg_left hsqrt hC.le
    _ = _ := by ring

end OMA.R_MeynielConjecture_meyniel_conjecture_R2
