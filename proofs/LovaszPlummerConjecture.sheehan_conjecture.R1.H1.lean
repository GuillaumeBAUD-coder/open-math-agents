import OMAReductions.R_LovaszPlummerConjecture_sheehan_conjecture_R1
import Mathlib

/-!
Thomason's parity argument for an edge whose endpoints may both have even degree.
Formalized for Left to Solve by @sobrien032 using Codex.
The path rotation follows Andrew Thomason, “Hamiltonian cycles and uniquely
edge colourable graphs” (1978).
-/

/- Vertex orders for spanning paths with a prescribed first oriented edge. -/

namespace Sheehan

variable {V : Type*}

structure Order (G : SimpleGraph V) (u v : V) where
  tail : List V
  nodup : (u :: v :: tail).Nodup
  covers : ∀ x, x ∈ u :: v :: tail
  chain : (u :: v :: tail).IsChain G.Adj

namespace Order

variable {G : SimpleGraph V} {u v : V}

def verts (p : Order G u v) : List V := u :: v :: p.tail

def last (p : Order G u v) : V := (v :: p.tail).getLast (by simp)

theorem ext_tail {p q : Order G u v} (h : p.tail = q.tail) : p = q := by
  cases p; cases q; simp_all

end Order
end Sheehan

/- Passing between fixed-start spanning orders and Hamiltonian closed walks. -/

namespace Sheehan

open SimpleGraph LovaszPlummerConjecture

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

theorem three_le_card_of_cycle [Fintype V] (c : G.Walk w w)
    (hc : IsHamiltonianCycle G c) : 3 ≤ Fintype.card V := by
  have h := hc.1.nodup_dropLast_support.length_le_card
  have hn := hc.1.three_le_length
  simp only [List.length_dropLast, Walk.length_support] at h
  omega

/-- With the first vertex and direction fixed, dropping the repeated final
vertex of a cycle gives the corresponding spanning order. -/
private theorem order_of_oriented_cycle (d : G.Walk u u)
    (hd : IsHamiltonianCycle G d) :
    ∃ p : Order G u d.snd, G.Adj p.last u ∧ d.support = p.verts ++ [u] := by
  have hn := hd.1.three_le_length
  have hs := d.support_dropLast_concat hd.1.not_nil
  have hlength : 3 ≤ d.dropLast.support.length := by
    rw [Walk.length_support, Walk.length_dropLast]
    omega
  obtain ⟨a, b, t, h⟩ : ∃ a b t, d.dropLast.support = a :: b :: t := by
    cases h : d.dropLast.support with
    | nil => simp [h] at hlength
    | cons a l =>
      cases l with
      | nil => simp [h] at hlength
      | cons b t => exact ⟨_, _, _, rfl⟩
  rw [h] at hs
  have ha : a = u := by simpa only [h, List.head_cons] using d.dropLast.head_support
  subst a
  have hb : b = d.snd := by
    have hindex := d.support_getElem_one (by simp [← hs])
    simpa only [← hs, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] using hindex
  subst b
  have hnodup := hd.1.isPath_dropLast.support_nodup
  rw [h] at hnodup
  have hchain := d.dropLast.isChain_adj_support
  rw [h] at hchain
  let p : Order G u d.snd :=
    { tail := t
      nodup := hnodup
      covers := fun x => by
        have hx := hd.2 x
        rw [← hs] at hx
        simpa [List.mem_cons, or_assoc, or_left_comm, or_comm] using hx
      chain := hchain }
  refine ⟨p, ?_, hs.symm⟩
  have hl : p.last = d.penultimate := by
    simpa only [h, List.getLast_cons_cons, Order.last, p] using d.dropLast.getLast_support
  exact hl ▸ d.adj_penultimate hd.1.not_nil

theorem cycle_to_order [DecidableEq V] (c : G.Walk w w) (hc : IsHamiltonianCycle G c)
    (e : Sym2 V) (he : e ∈ c.edges) :
    ∃ u v, e = s(u,v) ∧ ∃ (p : Order G u v) (d : G.Walk u u),
      G.Adj p.last u ∧ IsHamiltonianCycle G d ∧ d.support = p.verts ++ [u] ∧
        d.edges.toFinset = c.edges.toFinset := by
  obtain ⟨u,v⟩ := e
  let d := c.rotate u (hc.2 u)
  have hd : IsHamiltonianCycle G d :=
    ⟨hc.1.rotate _, fun x => (c.mem_support_rotate_iff _ _).mpr (hc.2 x)⟩
  have hed := (c.rotate_edges u (hc.2 u)).mem_iff.mpr he
  have hmem : v ∈ d.toSubgraph.neighborSet u := Walk.adj_toSubgraph_iff_mem_edges.mpr hed
  rw [hd.1.neighborSet_toSubgraph_endpoint] at hmem
  have hsets : d.edges.toFinset = c.edges.toFinset := by
    ext f
    simpa only [List.mem_toFinset] using (c.rotate_edges u (hc.2 u)).mem_iff (a := f)
  obtain h | h : v = d.snd ∨ v = d.penultimate := hmem
  · subst v
    obtain ⟨p, hp, hs⟩ := order_of_oriented_cycle d hd
    exact ⟨_, _, rfl, p, d, hp, hd, hs, hsets⟩
  · have hrev : IsHamiltonianCycle G d.reverse :=
      ⟨hd.1.reverse, fun x => by simpa using hd.2 x⟩
    have hstart : v = d.reverse.snd := h.trans d.snd_reverse.symm
    obtain ⟨p, hp, hs⟩ := order_of_oriented_cycle d.reverse hrev
    exact ⟨u, d.reverse.snd, hstart ▸ rfl, p, d.reverse, hp, hrev, hs, by simpa using hsets⟩

theorem order_to_cycle [Fintype V] (p : Order G u v) (hclose : G.Adj p.last u)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ c : G.Walk u u, IsHamiltonianCycle G c ∧ c.support = p.verts ++ [u] := by
  classical
  let a : G.Walk u p.last := Walk.ofSupport p.verts (by simp [Order.verts]) p.chain
  let c := a.concat hclose
  have ha : a.support = p.verts := Walk.support_ofSupport _ _
  have hs : c.support = p.verts ++ [u] := by rw [Walk.support_concat, ha]
  have hcard' : p.verts.length = Fintype.card V := by
    have hall : p.verts.toFinset = Finset.univ := Finset.eq_univ_of_forall fun x =>
      List.mem_toFinset.mpr (p.covers x)
    have hnodup : p.verts.Nodup := p.nodup
    rw [← List.toFinset_card_of_nodup hnodup, hall, Finset.card_univ]
  have hlen : 3 ≤ c.length := by
    have hh := c.length_support
    rw [hs, List.length_append, hcard'] at hh
    simp only [List.length_singleton] at hh
    omega
  refine ⟨c, ⟨Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨.mk' ?_, hlen⟩, ?_⟩, hs⟩
  · rw [Walk.support_tail_of_not_nil _ (Walk.not_nil_iff_lt_length.mpr (by omega)), hs]
    change ((v :: p.tail) ++ [u]).Nodup
    exact (List.perm_append_comm.nodup_iff).mpr p.nodup
  · intro x
    rw [hs]
    exact List.mem_append_left _ (p.covers x)

end Sheehan

/- Recover an anchored Hamiltonian order from its undirected cycle edges. -/

namespace Sheehan

open SimpleGraph
open scoped Sym2

variable {V : Type*}

/-- Successive undirected edges in an ordered list of vertices. -/
private def consecutive (x : V) : List V → List (Sym2 V)
  | [] => []
  | y :: ys => s(x,y) :: consecutive y ys

private theorem consecutive_zip (x : V) (xs : List V) :
    consecutive x xs = List.zipWith (s(·, ·)) (x :: xs) xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => simp [consecutive, ih y]

private theorem vertex_mem_of_edge {x z : V} {xs : List V} {e : Sym2 V}
    (he : e ∈ consecutive x xs) (hz : z ∈ e) : z ∈ x :: xs := by
  induction xs generalizing x with
  | nil => simp [consecutive] at he
  | cons y ys ih =>
    rcases List.mem_cons.mp he with rfl | ht
    · rcases Sym2.mem_iff.mp hz with rfl | rfl <;> simp
    · exact List.mem_cons_of_mem _ (ih ht)

variable [DecidableEq V]

/-- At the starting vertex of a simple path there is only one incident path
edge. Removing it recovers the same property for the remaining path. -/
private theorem order_of_path_edges (x : V) (xs ys : List V)
    (hx : (x :: xs).Nodup) (hy : (x :: ys).Nodup)
    (he : (consecutive x xs).toFinset = (consecutive x ys).toFinset) : xs = ys := by
  induction xs generalizing x ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b bs => have := he.symm; simp [consecutive] at this
  | cons a as ih =>
    cases ys with
    | nil => simp [consecutive] at he
    | cons b bs =>
      have hab : s(x,a) ∈ consecutive x (b :: bs) := by
        apply List.mem_toFinset.mp
        rw [← he]
        simp [consecutive]
      have hb : a = b := by
        rcases List.mem_cons.mp hab with h | h
        · rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h₁, h₂⟩
          · exact h
          · exact h₂.trans h₁
        · exact (hy.notMem (vertex_mem_of_edge h (Sym2.mem_mk_left _ _))).elim
      subst b
      have ha : s(x,a) ∉ consecutive a as := fun h =>
        hx.notMem (vertex_mem_of_edge h (Sym2.mem_mk_left _ _))
      have hb : s(x,a) ∉ consecutive a bs := fun h =>
        hy.notMem (vertex_mem_of_edge h (Sym2.mem_mk_left _ _))
      have htail := congrArg (fun t : Finset (Sym2 V) => t.erase s(x,a)) he
      simp [consecutive, ha, hb] at htail
      exact congrArg (a :: ·) (ih a bs hx.tail hy.tail htail)

theorem order_eq_of_cycle_edges {G : SimpleGraph V} {u v : V} {p q : Order G u v}
    {c d : G.Walk u u} (hc : c.support = (u :: v :: p.tail) ++ [u])
    (hd : d.support = (u :: v :: q.tail) ++ [u]) (hcc : c.IsCycle) (hdd : d.IsCycle)
    (he : c.edges.toFinset = d.edges.toFinset) : p = q := by
  have edges {r : Order G u v} {w : G.Walk u u}
      (hw : w.support = (u :: v :: r.tail) ++ [u]) :
      w.edges = s(u,v) :: consecutive v (r.tail ++ [u]) := by
    rw [Walk.edges_eq_zipWith_support, hw, consecutive_zip]
    rfl
  have hp := hcc.edges_nodup
  have hq := hdd.edges_nodup
  rw [edges hc, List.nodup_cons] at hp
  rw [edges hd, List.nodup_cons] at hq
  rw [edges hc, edges hd] at he
  have htail := congrArg (fun t : Finset (Sym2 V) => t.erase s(u,v)) he
  simp [hp.1, hq.1] at htail
  have hcp := hcc.support_nodup
  have hdq := hdd.support_nodup
  rw [hc] at hcp
  rw [hd] at hdq
  apply Order.ext_tail
  exact List.append_cancel_right (order_of_path_edges v _ _ hcp hdq htail)

end Sheehan

/- Rotate a spanning path by reversing the portion strictly after a marked neighbor
of its endpoint. The marked predecessor gives the unique fixed point above each path. -/

namespace Sheehan

variable {V : Type*} {G : SimpleGraph V} {u v : V}

abbrev Flag (G : SimpleGraph V) (u v : V) :=
  Σ p : Order G u v, {y : V // G.Adj p.last y ∧ y ≠ u}

private def revAfter [DecidableEq V] (y : V) : List V → List V
  | [] => []
  | x :: xs => x :: (if x = y then xs.reverse else revAfter y xs)

private theorem revAfter_split [DecidableEq V] (y : V) (a b : List V) (hn : y ∉ a) :
    revAfter y (a ++ y :: b) = a ++ y :: b.reverse := by
  induction a with
  | nil => simp [revAfter]
  | cons x a ih =>
    simp only [List.mem_cons, not_or] at hn
    simp [revAfter, Ne.symm hn.1, ih hn.2]

private theorem flag_split (f : Flag G u v) :
    ∃ a b : List V, v :: f.1.tail = a ++ f.2.val :: b ∧ f.2.val ∉ a ∧ b ≠ [] := by
  obtain ⟨hm, hu⟩ := f.2.property
  have hmem : f.2.val ∈ v :: f.1.tail := (List.mem_cons.mp (f.1.covers _)).resolve_left hu
  obtain ⟨a, b, hab⟩ := List.mem_iff_append.mp hmem
  have hd := f.1.nodup.of_cons
  rw [hab] at hd
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact fun hy => (List.nodup_append.mp hd).2.2 _ hy _ (by simp) rfl
  · rintro rfl
    have hh : (v :: f.1.tail).getLast? = some f.2.val := by simp [hab]
    have hz : f.1.last = f.2.val :=
      Option.some.inj ((List.getLast?_eq_some_getLast (by simp)).symm.trans hh)
    exact hm.ne hz

private theorem order_last? (p : Order G u v) : (v :: p.tail).getLast? = some p.last :=
  List.getLast?_eq_some_getLast (by simp)

private theorem revAfter_exists [DecidableEq V] (f : Flag G u v) :
    ∃ q : Flag G u v, v :: q.1.tail = revAfter f.2.val (v :: f.1.tail) ∧ q.2.val = f.2.val := by
  obtain ⟨a, b, hab, ha, hb⟩ := flag_split f
  let y := f.2.val
  have hsplit : revAfter y (v :: f.1.tail) = a ++ y :: b.reverse := by
    rw [hab]; exact revAfter_split y a b ha
  let t := if v = y then f.1.tail.reverse else revAfter y f.1.tail
  have ht : v :: t = a ++ y :: b.reverse := hsplit
  have hperm : (u :: v :: t).Perm (u :: v :: f.1.tail) := by
    rw [ht, hab]
    exact (((List.reverse_perm b).cons y).append_left a).cons u
  have hc := f.1.chain
  rw [hab] at hc
  obtain ⟨hpre, hsuf⟩ := List.isChain_cons_split.mp hc
  have hlast : b.getLast? = some f.1.last := by
    have he := order_last? f.1
    rwa [hab, List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_cons_of_ne_nil hb] at he
  have hr : (y :: b.reverse).IsChain G.Adj := by
    apply List.isChain_cons.mpr
    constructor
    · intro z hz
      rw [List.head?_reverse, hlast] at hz
      have : z = f.1.last := by simpa [eq_comm] using hz
      exact this ▸ f.2.property.1.symm
    · exact List.isChain_reverse.mpr (hsuf.tail.imp fun _ _ hadj => hadj.symm)
  let p : Order G u v := {
    tail := t
    covers := fun x => hperm.mem_iff.mpr (f.1.covers x)
    nodup := hperm.nodup_iff.mpr f.1.nodup
    chain := by rw [ht]; exact List.isChain_cons_split.mpr ⟨hpre, hr⟩ }
  have hp : v :: p.tail = a ++ y :: b.reverse := ht
  have hh := order_last? p
  rw [hp, List.getLast?_append_of_ne_nil _ (by simp),
    List.getLast?_cons_of_ne_nil (by simpa using hb), List.getLast?_reverse] at hh
  refine ⟨⟨p, y, (hsuf.rel_head? ?_).symm, f.2.property.2⟩, rfl, rfl⟩
  rw [hh]; simp

noncomputable def turn (f : Flag G u v) : Flag G u v := by
  classical
  exact (revAfter_exists f).choose

private theorem turn_spec (f : Flag G u v) :
    v :: (turn f).1.tail = @revAfter V (Classical.decEq V) f.2.val (v :: f.1.tail) ∧
      (turn f).2.val = f.2.val := by
  classical
  exact (revAfter_exists f).choose_spec

private theorem flag_ext {f g : Flag G u v} (hp : f.1.tail = g.1.tail)
    (hy : f.2.val = g.2.val) : f = g := by
  obtain ⟨p,y⟩ := f
  obtain ⟨q,z⟩ := g
  have he : p = q := Order.ext_tail hp
  subst q
  congr 1
  exact Subtype.ext hy

theorem turn_involutive : Function.Involutive (@turn V G u v) := by
  classical
  intro f
  obtain ⟨a, b, hab, ha, _⟩ := flag_split f
  obtain ⟨hc, hy⟩ := turn_spec f
  obtain ⟨hc', hy'⟩ := turn_spec (turn f)
  rw [hab, revAfter_split _ _ _ ha] at hc
  rw [hy, hc, revAfter_split _ _ _ ha, List.reverse_reverse, ← hab] at hc'
  exact flag_ext (List.cons.inj hc').2 (hy'.trans hy)

private theorem singleton_of_nodup_reverse {b : List V} (hd : b.Nodup)
    (hn : b ≠ []) (hr : b.reverse = b) : ∃ z, b = [z] := by
  obtain ⟨z, l, rfl⟩ := List.exists_cons_of_ne_nil hn
  refine ⟨z, ?_⟩
  by_contra h
  have hl : l ≠ [] := by rintro rfl; exact h rfl
  have hh := congrArg List.head? hr
  rw [List.head?_reverse, List.getLast?_cons_of_ne_nil hl,
    List.getLast?_eq_some_getLast hl, List.head?_cons] at hh
  exact hd.notMem (Option.some.inj hh ▸ List.getLast_mem hl)

private theorem fixed_iff (f : Flag G u v) :
    turn f = f ↔ ∃ a z, v :: f.1.tail = a ++ [f.2.val, z] := by
  classical
  constructor
  · intro hf
    obtain ⟨a, b, hab, ha, hb⟩ := flag_split f
    have hr := (turn_spec f).1
    rw [hf, hab, revAfter_split _ _ _ ha] at hr
    have hbr : b.reverse = b := (List.cons.inj (List.append_cancel_left hr)).2.symm
    have hd := f.1.nodup.of_cons
    rw [hab] at hd
    obtain ⟨z, rfl⟩ := singleton_of_nodup_reverse (List.nodup_append.mp hd).2.1.of_cons hb hbr
    exact ⟨a, z, hab⟩
  · rintro ⟨a, z, hab⟩
    obtain ⟨hr, hy⟩ := turn_spec f
    have hd := f.1.nodup.of_cons
    rw [hab] at hd
    have ha : f.2.val ∉ a := fun hm => (List.nodup_append.mp hd).2.2 _ hm _ (by simp) rfl
    rw [hab, revAfter_split _ _ _ ha] at hr
    apply flag_ext _ hy
    exact (List.cons.inj (hr.trans hab.symm)).2

private theorem fixed_mark {f : Flag G u v} (hf : turn f = f) :
    (v :: f.1.tail).dropLast.getLast? = some f.2.val := by
  obtain ⟨a, z, hab⟩ := (fixed_iff f).mp hf
  rw [hab, show a ++ [f.2.val, z] = (a ++ [f.2.val]) ++ [z] by simp,
    List.dropLast_concat, List.getLast?_concat]

noncomputable def fixedEquiv (hlt : ∀ p : Order G u v, p.tail ≠ []) :
    {f : Flag G u v // turn f = f} ≃ Order G u v := by
  apply Equiv.ofBijective (fun f => f.val.1)
  constructor
  · intro f g he
    change f.val.1 = g.val.1 at he
    apply Subtype.ext
    apply flag_ext (congrArg Order.tail he)
    apply Option.some.inj
    rw [← fixed_mark f.property, ← fixed_mark g.property, he]
  · intro p
    obtain ⟨c, z, hc⟩ := (List.eq_nil_or_concat p.tail).resolve_left (hlt p)
    have hne : v :: c ≠ [] := by simp
    let a := (v :: c).dropLast
    let y := (v :: c).getLast hne
    have ha : a ++ [y] = v :: c := List.dropLast_append_getLast hne
    have hab : v :: p.tail = a ++ [y, z] := calc
      v :: p.tail = (v :: c) ++ [z] := by rw [hc, List.concat_eq_append]; rfl
      _ = (a ++ [y]) ++ [z] := by rw [ha]
      _ = a ++ [y, z] := by simp
    have hh := order_last? p
    rw [hab, List.getLast?_append_of_ne_nil _ (by simp)] at hh
    have hlast : z = p.last := Option.some.inj hh
    have hch := p.chain
    rw [hab] at hch
    have hadj : G.Adj y z := (List.isChain_cons_split.mp hch).2.rel
    have hu : y ≠ u := by
      rintro rfl
      apply p.nodup.notMem
      rw [hab]; simp
    let f : Flag G u v := ⟨p, y, hlast ▸ hadj.symm, hu⟩
    exact ⟨⟨f, (fixed_iff f).mpr ⟨a, z, hab⟩⟩, rfl⟩

end Sheehan

/- Count marked spanning paths modulo two to obtain a second path that closes. -/

namespace Sheehan

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {u v : V}

private theorem perm_univ (p : Order G u v) :
    p.verts.Perm (Finset.univ : Finset V).toList := by
  apply (List.perm_ext_iff_of_nodup p.nodup (Finset.nodup_toList _)).mpr
  intro x
  exact ⟨fun _ => Finset.mem_toList.mpr (Finset.mem_univ _), fun _ => p.covers _⟩

private noncomputable instance orderFintype : Fintype (Order G u v) := by
  classical
  let S := (Finset.univ : Finset V).toList.permutations.toFinset
  let f (p : Order G u v) : ↥S :=
    ⟨p.verts, List.mem_toFinset.mpr (List.mem_permutations.mpr (perm_univ p))⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Order.ext_tail
    simpa [f, Order.verts] using congrArg Subtype.val h
  letI := Finite.of_injective f hf
  exact Fintype.ofFinite _

private theorem tail_nonempty (hcard : 3 ≤ Fintype.card V) (p : Order G u v) : p.tail ≠ [] := by
  intro h
  have := (perm_univ p).length_eq
  simp [Order.verts, h] at this
  omega

private theorem last_ne_anchors (hcard : 3 ≤ Fintype.card V) (p : Order G u v) :
    p.last ≠ u ∧ p.last ≠ v := by
  have hm : p.last ∈ v :: p.tail := List.getLast_mem _
  refine ⟨fun he => p.nodup.notMem (by simpa only [he] using hm), ?_⟩
  have ht := tail_nonempty hcard p
  have hm' : p.last ∈ p.tail := by
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil ht
    simpa only [Order.last, hx, List.getLast_cons_cons] using List.getLast_mem (l := x :: xs) (by simp)
  exact fun he => p.nodup.tail.notMem (by simpa only [he] using hm')

private theorem involution_parity {A : Type*} [Fintype A] (t : A → A)
    (ht : Function.Involutive t) {B : Type*} [Fintype B]
    (e : {a : A // t a = a} ≃ B) : Fintype.card A ≡ Fintype.card B [MOD 2] := by
  classical
  let f : Function.End A := t
  have hf : f ^ 2 ^ 1 = 1 := by
    funext a
    exact ht a
  have hm := Equiv.Perm.card_fixedPoints_modEq hf
  let e' : f.fixedPoints ≃ B := e
  rw [← Fintype.card_congr e']
  exact hm

private theorem marked_count [DecidableEq V] [DecidableRel G.Adj] (z u : V) :
    Fintype.card {y : V // G.Adj z y ∧ y ≠ u} + (if G.Adj z u then 1 else 0) =
      G.degree z := by
  classical
  have heq : Finset.univ.filter (fun y => G.Adj z y ∧ y ≠ u) = (G.neighborFinset z).erase u := by
    ext y
    simp [and_comm]
  rw [Fintype.card_subtype, heq, ← G.card_neighborFinset_eq_degree]
  by_cases h : G.Adj z u
  · simpa [h] using Finset.card_erase_add_one ((G.mem_neighborFinset z u).mpr h)
  · simp [h]

private theorem counting [DecidableEq V] [DecidableRel G.Adj] (hcard : 3 ≤ Fintype.card V)
    (hodd : ∀ x, x ≠ u → x ≠ v → G.degree x % 2 = 1)
    (t : (Σ p : Order G u v, {y : V // G.Adj p.last y ∧ y ≠ u}) →
         (Σ p : Order G u v, {y : V // G.Adj p.last y ∧ y ≠ u}))
    (ht : Function.Involutive t) (e : {a // t a = a} ≃ Order G u v)
    (p : Order G u v) (hp : G.Adj p.last u) :
    ∃ q : Order G u v, G.Adj q.last u ∧ q ≠ p := by
  classical
  by_contra! hu
  have hclose (q : Order G u v) : G.Adj q.last u ↔ q = p :=
    ⟨hu q, fun h => h ▸ hp⟩
  have hdeg : (∑ q : Order G u v, G.degree q.last) ≡ Fintype.card (Order G u v) [MOD 2] := by
    have hh : ∀ q : Order G u v, ∀ _ : q ∈ Finset.univ, G.degree q.last ≡ 1 [MOD 2] := by
      intro q _
      exact hodd _ (last_ne_anchors hcard q).1 (last_ne_anchors hcard q).2
    simpa using Nat.ModEq.sum hh
  have hm := involution_parity t ht e
  rw [Fintype.card_sigma] at hm
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Order G u v))) rfl
    (fun q _ => marked_count (G := G) q.last u)
  simp only [Finset.sum_add_distrib, hclose, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  unfold Nat.ModEq at hm hdeg
  omega

theorem other_closing_order [DecidableEq V] [DecidableRel G.Adj] (hcard : 3 ≤ Fintype.card V)
    (hodd : ∀ x, x ≠ u → x ≠ v → G.degree x % 2 = 1)
    (p : Order G u v) (hp : G.Adj p.last u) : ∃ q : Order G u v, G.Adj q.last u ∧ q ≠ p :=
  counting hcard hodd turn turn_involutive (fixedEquiv (tail_nonempty hcard)) p hp

end Sheehan

/- Thomason's parity argument produces a second Hamiltonian cycle. -/

namespace Sheehan

open SimpleGraph LovaszPlummerConjecture

theorem solve {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V) (c : G.Walk w w) (hc : IsHamiltonianCycle G c)
    (e : Sym2 V) (he : e ∈ c.edges) (hdeg : ∀ x, G.degree x % 2 ≠ 1 → x ∈ e) :
    ∃ (z : V) (c' : G.Walk z z), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset := by
  obtain ⟨u, v, rfl, p, d, hp, hd, hs, heq⟩ := cycle_to_order c hc e he
  have hcard := three_le_card_of_cycle c hc
  have hodd (x : V) (hxu : x ≠ u) (hxv : x ≠ v) : G.degree x % 2 = 1 := by
    by_contra hx
    exact (Sym2.mem_iff.mp (hdeg x hx)).elim hxu hxv
  obtain ⟨q, hq, hne⟩ := other_closing_order hcard hodd p hp
  obtain ⟨c', hc', hs'⟩ := order_to_cycle q hq hcard
  refine ⟨u, c', hc', fun h => hne ?_⟩
  exact order_eq_of_cycle_edges hs' hs hc'.1 hd.1 (h.trans heq.symm)

end Sheehan

theorem OMA.solution : OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1.H1 :=
  @Sheehan.solve
