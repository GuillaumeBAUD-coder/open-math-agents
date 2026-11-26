import FormalConjectures.Wikipedia.RamseyNumbers

/-! Kalbfleisch's 101-vertex Paley graph. Adjacency is stored as a bit mask
of the nonzero quadratic residues. An exhaustive search only extends a clique
by larger vertices adjacent to all those already chosen. Credit: @Deldor14. -/
open SimpleGraph Finset
namespace OMA.Paley
private def linked (x y : Fin 101) : Bool :=
  Nat.testBit 1550432784880709368503235994226 ((101 + y.val - x.val) % 101)

private def P : SimpleGraph (Fin 101) where
  Adj x y := linked x y = true
  symm := by
    have h : ∀ x y : Fin 101, linked x y = linked y x := by decide +kernel
    constructor
    intro x y hx; rwa [← h]
  loopless := ⟨by
    intro x
    have h : ∀ y : Fin 101, linked y y = false := by decide +kernel
    simp [h]⟩

private def search {V : Type*} [LinearOrder V] (adj : V → V → Bool) :
    ℕ → List V → Bool
  | 0, _ => true
  | n+1, L => L.any fun u => search adj n (L.filter fun v => decide (u < v) && adj u v)

private lemma search_complete {V : Type*} [LinearOrder V] (G : SimpleGraph V)
    (adj : V → V → Bool) (hadj : ∀ ⦃u v⦄, G.Adj u v → adj u v = true)
    {n : ℕ} {s : Finset V} {L : List V} (hs : G.IsNClique n s) (hL : ∀ x ∈ s, x ∈ L) :
    search adj n L = true := by
  induction n generalizing s L with
  | zero => rfl
  | succ n ih =>
    have hne : s.Nonempty := card_pos.mp (hs.card_eq ▸ Nat.succ_pos _)
    let u := s.min' hne
    have hu : u ∈ s := s.min'_mem hne
    apply List.any_eq_true.mpr
    refine ⟨u, hL u hu, ih (s := s.erase u) (by simpa using hs.erase_of_mem hu) ?_⟩
    intro x hx
    obtain ⟨hxne,hxs⟩ := mem_erase.mp hx
    have hux : u < x := lt_of_le_of_ne (s.min'_le x hxs) hxne.symm
    exact List.mem_filter.mpr ⟨hL x hxs, by simp [hux,hadj (hs.isClique hu hxs hxne.symm)]⟩

private def vertices : List (Fin 101) := List.finRange 101

private def nonedge (u v : Fin 101) : Bool := decide (u ≠ v) && !(linked u v)
private def shift (v : Fin 101) : Fin 101 ↪ Fin 101 where
  toFun x := ⟨(x.val+101-v.val)%101, Nat.mod_lt _ (by decide)⟩
  inj' := by
    intro x y h
    have h' := congrArg Fin.val h
    change (x.val+101-v.val)%101 = (y.val+101-v.val)%101 at h'
    have := x.isLt
    have := y.isLt
    have := v.isLt
    apply Fin.ext
    omega

private lemma shift_self (v : Fin 101) : shift v v = 0 := by
  apply Fin.ext
  change (v.val+101-v.val)%101 = 0
  omega

private lemma shift_edge (a u v : Fin 101) : linked (shift a u) (shift a v) = linked u v := by
  unfold linked
  congr 1
  change (101 + (v.val+101-a.val)%101 - (u.val+101-a.val)%101)%101 = _
  have := a.isLt
  have := u.isLt
  have := v.isLt
  omega

private lemma no_six (G : SimpleGraph (Fin 101)) (adj : Fin 101 → Fin 101 → Bool)
    (hadj : ∀ ⦃u v⦄, G.Adj u v → adj u v = true)
    (hshift : ∀ a u v, G.Adj u v → G.Adj (shift a u) (shift a v))
    (test : search adj 5 (vertices.filter (adj 0)) = false) : G.CliqueFree 6 := by
  intro s hs
  have hne : s.Nonempty := card_pos.mp (hs.card_eq ▸ (by decide : 0 < 6))
  obtain ⟨v,hv⟩ := hne
  let t := s.map (shift v)
  have ht : G.IsNClique 6 t := by
    refine ⟨?_, (card_map _).trans hs.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hy
    exact hshift _ _ _ (hs.isClique hi hj (fun h => hxy (congrArg _ h)))
  have hz : (0 : Fin 101) ∈ t := mem_map.mpr ⟨v,hv,shift_self v⟩
  have hcheck := search_complete G adj hadj (n := 5) (s := t.erase 0)
    (L := vertices.filter (adj 0)) (ht.erase_of_mem hz) (by
      intro x hx
      obtain ⟨h0,htx⟩ := mem_erase.mp hx
      exact List.mem_filter.mpr ⟨by simp [vertices], hadj (ht.isClique hz htx h0.symm)⟩)
  rw [test] at hcheck
  contradiction

set_option maxRecDepth 4096 in
private lemma positive_test : search linked 5 (vertices.filter (linked 0)) = false := by decide +kernel
set_option maxRecDepth 4096 in
private lemma negative_test : search nonedge 5 (vertices.filter (nonedge 0)) = false := by decide +kernel

end OMA.Paley
open OMA.Paley in
theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_six_six_lower_bound := by
  refine ⟨P, no_six P linked (fun {_ _} h => h) ?_ positive_test,
    no_six Pᶜ nonedge ?_ ?_ negative_test⟩
  · intro a u v h
    change linked (shift a u) (shift a v) = true
    rwa [shift_edge]
  · intro u v h
    have hn : ¬ linked u v = true := h.2
    simp [nonedge, h.1, Bool.eq_false_iff.mpr hn]
  · intro a u v h
    refine ⟨fun e => h.1 ((shift a).injective e),?_⟩
    change ¬ linked (shift a u) (shift a v) = true
    rw [shift_edge]
    exact h.2
