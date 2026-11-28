import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1
import Mathlib.Data.List.Cycle
import Mathlib.Combinatorics.SimpleGraph.Operations

/-! Ore's crossing argument and saturation by degree sum. The crossing-chord counting
is adapted from the merged first reduction of Graph Conjecture 189. -/

open SimpleGraph

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1_H1_R1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma cycle_iff_wrap {l : List V} (hne : l ≠ []) :
    Cycle.Chain G.Adj (l : Cycle V) ↔
      l.IsChain G.Adj ∧ ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, G.Adj a b := by
  rw [Cycle.chain_ne_nil _ hne, List.isChain_cons]
  rw [and_comm]
  simp [List.getLast?_eq_some_getLast hne]

lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]


lemma close_spanning_path [DecidableRel G.Adj] (l : List V) (hl_ne : l ≠ [])
    (hlnd : l.Nodup) (hcover : ∀ v, v ∈ l) (hlch : l.IsChain G.Adj)
    (hsum : l.length ≤ G.degree (l.head hl_ne) + G.degree (l.getLast hl_ne)) :
    (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ Cycle.Chain G.Adj (l : Cycle V)) := by
  classical
  set m := l.length
  set q0 := l.head hl_ne
  set z := l.getLast hl_ne
  have hp : 0 < m := List.length_pos_iff.mpr hl_ne
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  -- The two index sets of possible crossing chords.
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hcover y)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hcover y)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, List.getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hbound : m ≤ G.degree q0 + G.degree z := hsum
  obtain ⟨j, hjS, hjT⟩ : ∃ j, j ∈ S ∧ j ∈ T := by
    by_contra hcon
    push Not at hcon
    have hdisj : Disjoint S T := Finset.disjoint_left.mpr hcon
    have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at this
    omega
  rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
  obtain ⟨hjm, hA⟩ := hjS
  obtain ⟨-, hB⟩ := hjT
  -- the cycle
  set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
  have hperm : c.Perm l := by
    have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
    rw [List.take_append_drop] at this
    exact this
  have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
  have hj1 : j < m := by omega
  have hj2 : j + 1 < m := by omega
  have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
    rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
    simp [List.getElem?_eq_getElem hj1]
  have e2 : (l.drop (j + 1)).reverse.head? = some z := by
    rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), List.getLast?_eq_some_getLast hl_ne]
  have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
    rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
      List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]
    rfl
  have e4 : c.head? = some q0 := by
    rw [hcdef, List.head?_append, List.head?_take]
    simp [List.head?_eq_some_head hl_ne, q0]
  have hcyc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b := by
    refine ⟨List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩, ?_⟩
    · rw [List.isChain_reverse]
      exact (hlch.drop _).imp (fun a b h => h.symm)
    · intro x hx y hy
      rw [e1] at hx
      rw [e2] at hy
      simp at hx hy
      subst hx hy
      exact hB
    · intro a ha b hb
      rw [e3] at ha
      rw [e4] at hb
      simp at ha hb
      subst ha hb
      exact (hA).symm
  exact ⟨c, hcnd, fun v => hperm.mem_iff.mpr (hcover v),
    (cycle_iff_wrap (by intro he; have := hperm.length_eq; simp [he] at this; omega)).mpr hcyc⟩


lemma spanning_length (l : List V) (hd : l.Nodup) (hall : ∀ v, v ∈ l) :
    l.length = Fintype.card V := by
  have hu : l.toFinset = Finset.univ := Finset.eq_univ_of_forall (fun v => by simpa using hall v)
  simpa [hu] using (List.toFinset_card_of_nodup hd).symm

lemma cycle_closure [DecidableRel G.Adj] (hn : 3 ≤ Fintype.card V) (x y : V) (hne : x ≠ y)
    (hdeg : Fintype.card V ≤ G.degree x + G.degree y)
    (hcycle : (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ Cycle.Chain (G ⊔ edge x y).Adj (l : Cycle V))) : (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ Cycle.Chain G.Adj (l : Cycle V)) := by
  classical
  let H := G ⊔ edge x y
  obtain ⟨l, hnd, hall, hcy⟩ := hcycle
  obtain ⟨a, b, hl⟩ := List.append_of_mem (hall x)
  let t := b ++ a
  have hr : l.IsRotated (x :: t) := by
    rw [hl]
    exact List.isRotated_append
  obtain ⟨hxout, htnd⟩ := List.nodup_cons.mp (hr.perm.nodup_iff.mp hnd)
  have hspan (v : V) : v ∈ x :: t := hr.perm.mem_iff.mp (hall v)
  have hlen := spanning_length (x :: t) (List.nodup_cons.mpr ⟨hxout, htnd⟩) hspan
  simp only [List.length_cons] at hlen
  have ht : t ≠ [] := List.length_pos_iff.mp (by omega)
  have hc : Cycle.Chain H.Adj ((x :: t) : Cycle V) := Cycle.coe_eq_coe.mpr hr ▸ hcy
  obtain ⟨hchain, hwrap⟩ := (cycle_iff_wrap (List.cons_ne_nil _ _)).mp hc
  obtain ⟨hfirst, htail⟩ := List.isChain_cons.mp hchain
  have hstart : H.Adj x (t.head ht) := hfirst _ (List.head?_eq_some_head ht)
  have hlast : H.Adj x (t.getLast ht) := by
    apply Adj.symm
    exact hwrap _ (by simp [List.getLast?_cons, List.getLast?_eq_some_getLast ht]) x rfl
  have hinside : t.IsChain G.Adj := by
    apply List.IsChain.imp_of_mem_imp _ htail
    intro i j hi hj hij
    rcases (sup_adj ..).mp hij with h | h
    · exact h
    · rcases ((edge_adj ..).mp h).1 with ⟨rfl, _⟩ | ⟨_, rfl⟩
      · exact (hxout hi).elim
      · exact (hxout hj).elim
  have hend {z : V} (haz : H.Adj x z) : G.Adj x z ∨ z = y := by
    simp [H, sup_adj, edge_adj, hne] at haz
    exact haz.imp_right And.left
  have ends_ne : t.head ht ≠ t.getLast ht := by
    intro h
    obtain ⟨i, hi⟩ := (htnd.head_eq_getLast_iff ht).mp h
    rw [hi] at hlen
    simp only [List.length_singleton] at hlen
    omega
  have finish (r : List V) (hp : r.Perm t) (hrc : r.IsChain G.Adj)
      (hrn : r ≠ []) (hxr : G.Adj x (r.head hrn)) (hry : r.getLast hrn = y) :
      (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ Cycle.Chain G.Adj (l : Cycle V)) := by
    have hperm := hp.cons x
    apply close_spanning_path (x :: r) (List.cons_ne_nil _ _)
      (hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hxout,htnd⟩))
      (fun v => hperm.mem_iff.mpr (hspan v))
    · exact hrc.cons_of_ne_nil hrn hxr
    · have hel : (x :: r).getLast (List.cons_ne_nil _ _) = y := by
        cases r with
        | nil => exact (hrn rfl).elim
        | cons a r => exact hry
      rw [hel]
      change r.length + 1 ≤ G.degree x + G.degree y
      rwa [hp.length_eq, hlen]
  rcases hend hstart with hs | hs
  · rcases hend hlast with he | he
    · refine ⟨x :: t, List.nodup_cons.mpr ⟨hxout,htnd⟩, hspan,
        (cycle_iff_wrap (List.cons_ne_nil _ _)).mpr ⟨hinside.cons_of_ne_nil ht hs, ?_⟩⟩
      simpa [List.getLast?_cons, List.getLast?_eq_some_getLast ht] using he.symm
    · exact finish t (List.Perm.refl t) hinside ht hs he
  · have hxr := (hend hlast).resolve_right (fun h => ends_ne (hs.trans h.symm))
    exact finish t.reverse (List.reverse_perm _) (List.isChain_reverse.mpr
      (hinside.imp (fun _ _ h => h.symm))) (by simpa using ht)
      (by simpa using hxr) (by simpa using hs)


lemma path_closure [Nontrivial V] [DecidableRel G.Adj] (x y : V) (hne : x ≠ y)
    (hdeg : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (hp : (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain (G ⊔ edge x y).Adj)) : (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain G.Adj) := by
  classical
  let cone (G : SimpleGraph V) : SimpleGraph (Option V) := {
    Adj := fun
      | none, none => False
      | some a, some b => G.Adj a b
      | _, _ => True
    symm := ⟨by rintro (_ | a) (_ | b) h <;> first | exact h.symm | trivial | exact h⟩
    loopless := ⟨by rintro (_ | a) <;> simp [irrefl]⟩ }
  have path_iff_cone {G : SimpleGraph V} : (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain G.Adj) ↔ (∃ l : List (Option V), l.Nodup ∧ (∀ v, v ∈ l) ∧ Cycle.Chain (cone G).Adj (l : Cycle (Option V))) := by
    constructor
    · rintro ⟨l, hnd, hall, hch⟩
      have hl : l ≠ [] := by rintro rfl; simpa using hall (Classical.arbitrary V)
      have hn : l.map some ≠ [] := by simpa using hl
      refine ⟨none :: l.map some, ?_, ?_, (cycle_iff_wrap (List.cons_ne_nil _ _)).mpr ⟨?_, ?_⟩⟩
      · simp [hnd, List.nodup_map_iff (Option.some_injective V)]
      · rintro (_ | v) <;> simp [hall]
      · apply List.IsChain.cons_of_ne_nil hn
        · exact (List.isChain_map some).mpr hch
        · simp [List.head_map, cone]
      · simp [List.getLast?_cons, List.getLast?_eq_some_getLast hn, List.getLast_map, cone]
    · rintro ⟨l,hnd,hall,hch⟩
      obtain ⟨a,b,hl⟩ := List.append_of_mem (hall none)
      let t := b ++ a
      have hr : l.IsRotated (none :: t) := by rw [hl]; exact List.isRotated_append
      obtain ⟨hout,htnd⟩ := List.nodup_cons.mp (hr.perm.nodup_iff.mp hnd)
      have he : ∀ (r : List (Option V)), none ∉ r → ∃ s : List V, r = s.map some := by
        intro r
        induction r with
        | nil => exact fun _ => ⟨[],rfl⟩
        | cons k r ih =>
          intro hh
          cases k with
          | none => simp at hh
          | some v =>
            obtain ⟨s,hs⟩ := ih (by simpa using hh)
            exact ⟨v :: s, by simp [hs]⟩
      obtain ⟨s,hs⟩ := he t hout
      have hc : Cycle.Chain (cone G).Adj ((none :: t) : Cycle (Option V)) :=
        Cycle.coe_eq_coe.mpr hr ▸ hch
      have hc' := ((cycle_iff_wrap (List.cons_ne_nil _ _)).mp hc).1.tail
      rw [hs] at htnd hc'
      refine ⟨s, (List.nodup_map_iff (Option.some_injective V)).mp htnd, ?_,
        (List.isChain_map some).mp hc'⟩
      intro v
      have hm := hr.perm.mem_iff.mp (hall (some v))
      simpa [hs] using hm
  have cone_degree {G : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel (cone G).Adj] (v : V) :
      (cone G).degree (some v) = G.degree v + 1 := by
    classical
    have he : (cone G).neighborFinset (some v) =
        insert none ((G.neighborFinset v).image some) := by
      ext x
      rw [mem_neighborFinset]
      cases x <;> simp [cone]
    have h := congrArg Finset.card he
    simpa [Finset.card_image_of_injective _ (Option.some_injective V)] using h
  have he : cone (G ⊔ edge x y) = cone G ⊔ edge (some x) (some y) := by
    ext i j
    cases i <;> cases j <;> simp [cone, sup_adj, edge_adj]
  have hc := path_iff_cone.mp hp
  rw [he] at hc
  apply path_iff_cone.mpr
  apply cycle_closure _ (some x) (some y) (by simpa using hne) _ hc
  · have := Fintype.one_lt_card (α := V)
    simp only [Fintype.card_option]
    omega
  · rw [Fintype.card_option, cone_degree, cone_degree]
    omega

open Classical in
lemma maximal_nontraceable [Nontrivial V] (h : ¬ (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain G.Adj)) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ¬ (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain H.Adj) ∧
      ∀ (x y : V), x ≠ y → ¬ H.Adj x y →
        H.degree x +
        H.degree y + 1 < Fintype.card V := by
  classical
  obtain ⟨H,hGH,hmax⟩ := Finite.exists_le_maximal (p := fun H : SimpleGraph V => ¬ (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain H.Adj)) h
  refine ⟨H,hGH,hmax.1,?_⟩
  intro x y hxy hn
  by_contra! hsum
  have hbad : ¬ (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain (H ⊔ edge x y).Adj) := fun hp => hmax.1 (path_closure x y hxy hsum hp)
  exact (H.lt_sup_edge x y hxy hn).not_ge (hmax.2 hbad le_sup_left)

lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq] 
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))
lemma alternating_chain [DecidableRel G.Adj] (L R : Finset V) (hsize : L.card = R.card)
    (hdis : Disjoint L R) (hc : ∀ x ∈ L, ∀ y ∈ R, G.Adj x y) (a : V) (ha : a ∈ L) :
    ∃ l : List V, l.head? = some a ∧ l.Nodup ∧ l.IsChain G.Adj ∧ l.toFinset = L ∪ R := by
  classical
  induction R using Finset.strongInductionOn generalizing L a with
  | _ R ih =>
    obtain ⟨b,hb⟩ : R.Nonempty := Finset.card_pos.mp
      (by rw [← hsize]; exact Finset.card_pos.mpr ⟨a,ha⟩)
    have hab := hc a ha b hb
    let L' := L.erase a
    let R' := R.erase b
    have hlr : L'.card = R'.card := by simp [L',R',Finset.card_erase_of_mem,ha,hb,hsize]
    have hsplit : insert a (insert b (L' ∪ R')) = L ∪ R := by
      ext x
      simp [L',R']
      grind
    by_cases hem : L' = ∅
    · have hr' : R' = ∅ := Finset.card_eq_zero.mp (by simp [← hlr,hem])
      refine ⟨[a,b],rfl,by simp [hab.ne],by simpa using hab,?_⟩
      simpa [hem,hr'] using hsplit
    · obtain ⟨c,hc'⟩ := Finset.nonempty_iff_ne_empty.mpr hem
      have hrec := ih R' (Finset.erase_ssubset hb) L' hlr
        (hdis.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))
        (fun x hx y hy => hc x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)) c hc'
      obtain ⟨l,hhead,hnd,hch,hset⟩ := hrec
      have habs : a ∉ l := by
        intro hh
        have : a ∈ L' ∪ R' := hset ▸ List.mem_toFinset.mpr hh
        rcases Finset.mem_union.mp this with hL | hR
        · exact Finset.notMem_erase a L hL
        · exact Finset.disjoint_left.mp hdis ha (Finset.mem_of_mem_erase hR)
      have hbbs : b ∉ l := by
        intro hh
        have : b ∈ L' ∪ R' := hset ▸ List.mem_toFinset.mpr hh
        rcases Finset.mem_union.mp this with hL | hR
        · exact Finset.disjoint_left.mp hdis (Finset.mem_of_mem_erase hL) hb
        · exact Finset.notMem_erase b R hR
      refine ⟨a::b::l,rfl, by simp [hab.ne,habs,hbbs,hnd], ?_,?_⟩
      · apply List.isChain_cons.mpr
        refine ⟨by simpa using hab, List.isChain_cons.mpr ⟨?_,hch⟩⟩
        intro y hy
        have he : y = c := by simpa [hhead,eq_comm] using hy
        subst y
        exact (hc c (Finset.mem_of_mem_erase hc') b hb).symm
      · simpa [hset] using hsplit

lemma hamiltonian_of_spanning_path [Nonempty V] (hp : (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain G.Adj)) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨l, hd, hfull, hchain⟩ := hp
  have hl : l ≠ [] := by rintro rfl; simpa using hfull (Classical.arbitrary V)
  let p := Walk.ofSupport l hl hchain
  have he : p.support = l := Walk.support_ofSupport hl hchain
  have hpath : p.IsPath := Walk.IsPath.mk' (by simpa [he] using hd)
  exact ⟨_,_,p,hpath.isHamiltonian_of_mem (by simpa [he] using hfull)⟩

lemma high_off_minimum [Nontrivial V] [DecidableRel G.Adj] {v : V}
    (hv : G.degree v = G.minDegree) {x : V} (hx : x ≠ v) : G.secondSmallestDegree ≤ G.degree x := by
  rcases degree_pair (G := G) x v hx with h | h
  · exact h
  · exact h.trans (hv ▸ G.minDegree_le_degree x)

lemma path_of_clique_off_vertex {v u : V} (hu : G.Adj v u)
    (hcl : ∀ x ≠ v, ∀ y ≠ v, x ≠ y → G.Adj x y) : (∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain G.Adj) := by
  classical
  let l := ((Finset.univ.erase v).erase u).toList
  have hmem (x : V) : x ∈ l ↔ x ≠ u ∧ x ≠ v := by simp [l]
  have hul : (u :: l).Nodup := List.nodup_cons.mpr ⟨by simp [hmem], Finset.nodup_toList _⟩
  have hnot : v ∉ u :: l := by simp [hmem, hu.ne]
  have hchain : (u :: l).IsChain G.Adj := by
    apply List.IsChain.imp_of_mem_imp _ (List.Pairwise.isChain hul)
    intro x y hx hy hxy
    exact hcl x (fun he => hnot (he ▸ hx)) y (fun he => hnot (he ▸ hy)) hxy
  refine ⟨v :: u :: l, List.nodup_cons.mpr ⟨hnot,hul⟩, ?_, ?_⟩
  · intro x
    simp only [List.mem_cons, hmem]
    tauto
  · exact List.isChain_cons.mpr ⟨by simpa using hu,hchain⟩

theorem trace_at_most_twice_second_add_one [Nontrivial V] [DecidableRel G.Adj]
    (hc : G.Connected) (hn : Fintype.card V ≤ 2 * G.secondSmallestDegree + 1) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  apply hamiltonian_of_spanning_path
  by_contra hnopath
  obtain ⟨H, hGH, hH, hs⟩ := maximal_nontraceable hnopath
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  obtain ⟨u, hu⟩ := hc.preconnected.exists_adj_of_nontrivial v
  apply hH (path_of_clique_off_vertex (hGH hu) ?_)
  intro x hx y hy hxy
  by_contra h
  have hbound := hs x y hxy h
  have hdx := (high_off_minimum hv.symm hx).trans (degree_le_of_le hGH)
  have hdy := (high_off_minimum hv.symm hy).trans (degree_le_of_le hGH)
  omega


section LeafCounts
variable [DecidableRel G.Adj]

theorem dist_from_leaf {v u : V} (hc : G.Connected) (hu : G.Adj v u)
    (huniq : ∀ w, G.Adj v w → w = u) {x : V} (hx : x ≠ v) :
    G.dist v x = G.dist u x + 1 := by
  have htri := hc.dist_triangle (u := v) (v := u) (w := x)
  rw [dist_eq_one_iff_adj.mpr hu] at htri
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v x
  cases p with
  | nil => exact (hx rfl).elim
  | cons h q =>
    obtain rfl := huniq _ h
    have hq := dist_le q
    simp only [Walk.length_cons] at hp
    omega

theorem even_count_at_leaf {v u : V} (hc : G.Connected) (hu : G.Adj v u)
    (huniq : ∀ w, G.Adj v w → w = u) (hd : G.diam ≤ 3) :
    distEven G v = G.degree u ∧ distEven G u + G.degree u = Fintype.card V := by
  classical
  letI : Nonempty V := ⟨v⟩
  have hub (x : V) : G.dist u x ≤ 2 := by
    by_cases hx : x = v
    · simpa [hx, dist_eq_one_iff_adj.mpr hu.symm]
    · have hh := G.dist_le_diam (u := v) (v := x) (G.connected_iff_ediam_ne_top.mp hc)
      rw [dist_from_leaf hc hu huniq hx] at hh
      omega
  have hleaf : (Finset.univ.filter fun x => Even (G.dist v x)) = G.neighborFinset u := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset]
    by_cases hx : x = v
    · simp [hx, hu.symm]
    · rw [dist_from_leaf hc hu huniq hx, ← dist_eq_one_iff_adj, Nat.even_iff]
      have := hub x
      omega
  have hcenter : (Finset.univ.filter fun x => Even (G.dist u x)) =
      Finset.univ.filter (fun x => ¬ G.Adj u x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← dist_eq_one_iff_adj, Nat.even_iff]
    have := hub x
    omega
  constructor
  · simpa [distEven, hleaf]
  · rw [distEven, hcenter, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (p := G.Adj u)
    simpa [Nat.add_comm] using h

theorem boundary_leaf {v : V} (hc : G.Connected) (hd : G.diam ≤ 3) (hv : G.degree v = 1)
    (s : ℕ) (hb : ∀ x, distEven G x ≤ 1 + s) (hn : Fintype.card V = 2*s+2) :
    ∃ u, G.Adj v u ∧ G.degree u = s+1 ∧ (Finset.univ.filter (fun x => ¬ G.Adj u x)).card = s+1 := by
  obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
  obtain ⟨he, hf⟩ := even_count_at_leaf hc hu huniq hd
  have hdeg : G.degree u = s+1 := by have := hb v; have := hb u; omega
  refine ⟨u,hu,hdeg,?_⟩
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (p := G.Adj u)
  rw [← neighborFinset_eq_filter, card_neighborFinset_eq_degree, Finset.card_univ] at h
  omega


end LeafCounts

lemma degree_grows_of_new_edge {H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) {b u : V} (hnew : H.Adj b u) (hold : ¬ G.Adj b u) : G.degree b < H.degree b := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    exact (H.mem_neighborFinset _ _).mpr (hGH ((G.mem_neighborFinset _ _).mp hx))
  · intro he
    have hm := (H.mem_neighborFinset _ _).mpr hnew
    rw [← he] at hm
    exact hold ((G.mem_neighborFinset _ _).mp hm)

theorem trace_of_boundary_neighbor [Nontrivial V] [DecidableRel G.Adj]
    {v u : V} (hv : G.minDegree = G.degree v) (hu : G.Adj v u)
    (hn : Fintype.card V = 2 * G.secondSmallestDegree + 2)
    (hdu : G.degree u = G.secondSmallestDegree + 1) (hspos : 0 < G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let s := G.secondSmallestDegree
  change Fintype.card V = 2*s+2 at hn
  change G.degree u = s+1 at hdu
  change 0 < s at hspos
  let A := (G.neighborFinset u).erase v
  let B := (Finset.univ.filter (fun x => ¬ G.Adj u x)).erase u
  have huvm := (G.mem_neighborFinset u v).mpr hu.symm
  have hA : A.card = s := by simp [A, Finset.card_erase_of_mem huvm, hdu]
  have hset := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (p := G.Adj u)
  rw [← neighborFinset_eq_filter, card_neighborFinset_eq_degree, Finset.card_univ] at hset
  have huB : u ∈ Finset.univ.filter (fun x => ¬ G.Adj u x) := by simp
  have hB : B.card = s := by
    change ((Finset.univ.filter _).erase u).card = s
    rw [Finset.card_erase_of_mem huB]
    omega
  have memA (x : V) : x ∈ A ↔ x ≠ v ∧ G.Adj u x := by simp [A]
  have memB (x : V) : x ∈ B ↔ x ≠ u ∧ ¬ G.Adj u x := by simp [B]
  apply hamiltonian_of_spanning_path
  by_contra hnopath
  obtain ⟨H,hGH,hH,hsat⟩ := maximal_nontraceable hnopath
  have hhigh {x : V} (hx : x ≠ v) : s ≤ H.degree x :=
    (high_off_minimum hv.symm hx).trans (degree_le_of_le hGH)
  have hucore {x : V} (hx : x ≠ v) (hxu : x ≠ u) : H.Adj u x := by
    by_contra h
    have hfail := hsat u x hxu.symm h
    have hdle : G.degree u ≤ H.degree u := degree_le_of_le hGH
    have := hhigh hx
    omega
  have hcross : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b := by
    intro a ha b hb'
    obtain ⟨hav,hua⟩ := (memA a).mp ha
    obtain ⟨hbu,hub⟩ := (memB b).mp hb'
    have hbv : b ≠ v := fun he => hub (he ▸ hu.symm)
    have hnew := degree_grows_of_new_edge hGH (hucore hbv hbu).symm (fun h => hub h.symm)
    have hbg : s ≤ G.degree b := high_off_minimum hv.symm hbv
    have hag := hhigh hav
    by_contra hnab
    have hne : a ≠ b := fun he => hub (he ▸ hua)
    have hfail := hsat a b hne hnab
    omega
  obtain ⟨a,ha⟩ : A.Nonempty := Finset.card_pos.mp (hA ▸ hspos)
  have hdis : Disjoint A B := Finset.disjoint_left.mpr fun x hx hy =>
    (memB x |>.mp hy).2 (memA x |>.mp hx).2
  obtain ⟨l,hh,hnd,hch,hl⟩ := alternating_chain A B (hA.trans hB.symm) hdis hcross a ha
  have hmemb (x : V) : x ∈ l ↔ (x ≠ v ∧ G.Adj u x) ∨ (x ≠ u ∧ ¬ G.Adj u x) := by
    rw [← List.mem_toFinset, hl, Finset.mem_union, memA, memB]
  apply hH
  refine ⟨v :: u :: l, ?_, ?_, ?_⟩
  · simp [hnd, hmemb, hu.ne, hu.symm]
  · intro x
    simp only [List.mem_cons, hmemb]
    tauto
  · refine List.isChain_cons.mpr ⟨by simpa using hGH hu, List.isChain_cons.mpr ⟨?_,hch⟩⟩
    intro y hy
    have hya : y = a := by simpa [hh, eq_comm] using hy
    exact hya ▸ hGH ((memA a).mp ha).2

theorem trace_of_leaf [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected) (hd : G.diam ≤ 3)
    (hm : G.minDegree = 1) (hlow : G.minDegree + G.secondSmallestDegree + 1 < Fintype.card V)
    (hb : ∀ x, distEven G x ≤ 1 + G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let s := G.secondSmallestDegree
  by_cases hsmall : Fintype.card V ≤ 2*s+1
  · exact trace_at_most_twice_second_add_one hc hsmall
  obtain ⟨v,hv⟩ := G.exists_minimal_degree_vertex
  have hv1 : G.degree v = 1 := hv.symm.trans hm
  obtain ⟨u,hu,huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv1
  obtain ⟨he,hcard⟩ := even_count_at_leaf hc hu huniq hd
  have hev : distEven G v ≤ 1+s := hb v
  have heu : distEven G u ≤ 1+s := hb u
  have hn : Fintype.card V = 2*s+2 := by omega
  have hdu : G.degree u = s+1 := by omega
  have hspos : 0 < s := by change G.minDegree + s + 1 < _ at hlow; omega
  exact trace_of_boundary_neighbor hv hu hn hdu hspos

section RadiusTwo
variable [DecidableRel G.Adj]

theorem near_twins {v u w : V} (hc : G.Connected) (hu : G.Adj v u)
    (hneigh : ∀ x, G.Adj v x → x = u ∨ x = w)
    (s : ℕ) (hev : distEven G v ≤ s+1) (hdu : s ≤ G.degree u) :
    let E := Finset.univ.filter fun x => Even (G.dist v x)
    (E \ G.neighborFinset u).card ≤ (if G.Adj u w then 2 else 1) ∧
    G.degree u ≤ s + (if G.Adj u w then 2 else 1) := by
  classical
  let E := Finset.univ.filter fun x => Even (G.dist v x)
  change (E \ G.neighborFinset u).card ≤ _ ∧ G.degree u ≤ _
  have hE : E.card ≤ s+1 := hev
  have hout {x : V} (hx : x ∈ G.neighborFinset u) (hnot : x ∉ E) : x = w := by
    have hadj : G.Adj u x := (G.mem_neighborFinset u x).mp hx
    have htri := hc.dist_triangle (u := v) (v := u) (w := x)
    rw [dist_eq_one_iff_adj.mpr hu, dist_eq_one_iff_adj.mpr hadj] at htri
    have hodd : ¬ Even (G.dist v x) := by simpa [E] using hnot
    rw [Nat.even_iff] at hodd
    have hvx : G.Adj v x := dist_eq_one_iff_adj.mp (by omega)
    exact (hneigh x hvx).resolve_left hadj.ne.symm
  have hcard := Finset.card_sdiff_add_card E (G.neighborFinset u)
  rw [card_neighborFinset_eq_degree] at hcard
  by_cases huw : G.Adj u w
  · simp only [if_pos huw]
    have hsub : E ∪ G.neighborFinset u ⊆ insert w E := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_insert_of_mem h
      · by_cases he : x ∈ E
        · exact Finset.mem_insert_of_mem he
        · exact Finset.mem_insert.mpr (Or.inl (hout h he))
    have hsize := Finset.card_le_card hsub
    have hlim := Finset.card_insert_le w E
    omega
  · simp only [if_neg huw]
    have hsub : E ∪ G.neighborFinset u ⊆ E := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact h
      · by_contra he
        exact huw (hout h he ▸ (G.mem_neighborFinset u x).mp h)
    have hsize := Finset.card_le_card hsub
    omega


theorem order_from_center {u : V} (hu : ∀ x, G.dist u x ≤ 2) :
    Fintype.card V = distEven G u + G.degree u := by
  classical
  have he : (Finset.univ.filter (fun x => Even (G.dist u x))) =
      Finset.univ.filter (fun x => ¬ G.Adj u x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← dist_eq_one_iff_adj, Nat.even_iff]
    have := hu x
    omega
  have hs := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (p := G.Adj u)
  rw [← neighborFinset_eq_filter, card_neighborFinset_eq_degree, Finset.card_univ] at hs
  rw [distEven,he, Nat.add_comm]
  exact hs.symm

theorem trace_of_boundary_triangle [Nontrivial V] {v u w : V} (hv : G.minDegree = G.degree v)
    (hu : G.Adj v u) (hw : G.Adj v w) (huw : G.Adj u w)
    (hn : Fintype.card V = 2 * G.secondSmallestDegree + 2)
    (hdu : G.degree u = G.secondSmallestDegree + 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let s := G.secondSmallestDegree
  let A := ((G.neighborFinset u).erase v).erase w
  let U := Finset.univ.filter (fun x => ¬ G.Adj u x)
  have memA (x : V) : x ∈ A ↔ x ≠ w ∧ x ≠ v ∧ G.Adj u x := by simp [A]
  have memU (x : V) : x ∈ U ↔ ¬ G.Adj u x := by simp [U]
  have huvm := (G.mem_neighborFinset u v).mpr hu.symm
  have hwA : w ∈ (G.neighborFinset u).erase v := by simp [hw.ne.symm, huw]
  have hA : A.card = s := by
    simp [A, Finset.card_erase_of_mem hwA, Finset.card_erase_of_mem huvm, hdu, s]
  have hset := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (p := G.Adj u)
  rw [← neighborFinset_eq_filter, card_neighborFinset_eq_degree, Finset.card_univ] at hset
  change G.degree u + U.card = Fintype.card V at hset
  have hU : U.card = s := by dsimp [s]; omega
  apply hamiltonian_of_spanning_path
  by_contra hno
  obtain ⟨H,hGH,hH,hsat⟩ := maximal_nontraceable hno
  have hhigh {x : V} (hx : x ≠ v) : G.secondSmallestDegree ≤ H.degree x :=
    (high_off_minimum hv.symm hx).trans (degree_le_of_le hGH)
  have hucore {x : V} (hx : x ≠ v) (hxu : x ≠ u) : H.Adj u x := by
    by_contra h
    have hfail := hsat u x hxu.symm h
    have : G.degree u ≤ H.degree u := degree_le_of_le hGH
    have := hhigh hx
    omega
  have hcross : ∀ b ∈ U, ∀ a ∈ A, H.Adj b a := by
    intro b hb a ha
    have hub := (memU b).mp hb
    obtain ⟨_,hav,hua⟩ := (memA a).mp ha
    by_cases he : b = u
    · exact he ▸ hGH hua
    have hbv : b ≠ v := fun h => hub (h ▸ hu.symm)
    have hnew := degree_grows_of_new_edge hGH (hucore hbv he).symm (fun h => hub h.symm)
    have hbg := high_off_minimum hv.symm hbv
    have hag := hhigh hav
    by_contra hnab
    have hne : b ≠ a := fun h => hub (h ▸ hua)
    have hfail := hsat b a hne hnab
    omega
  have hdis : Disjoint U A := Finset.disjoint_left.mpr fun x hx hy =>
    (memU x |>.mp hx) (memA x |>.mp hy).2.2
  obtain ⟨l,hh,hnd,hch,hl⟩ := alternating_chain U A (hU.trans hA.symm) hdis hcross u
    ((memU u).mpr (G.loopless.irrefl u))
  have hmemb (x : V) : x ∈ l ↔ ¬ G.Adj u x ∨ x ≠ w ∧ x ≠ v ∧ G.Adj u x := by
    rw [← List.mem_toFinset, hl, Finset.mem_union, memU, memA]
  apply hH
  refine ⟨v :: w :: l, ?_, ?_, ?_⟩
  · simp [hnd, hmemb, hw.ne, hu.symm, huw]
  · intro x
    simp only [List.mem_cons, hmemb]
    tauto
  · refine List.isChain_cons.mpr ⟨by simpa using hGH hw, List.isChain_cons.mpr ⟨?_,hch⟩⟩
    intro y hy
    have hyu : y = u := by simpa [hh,eq_comm] using hy
    exact hyu ▸ hGH huw.symm

end RadiusTwo


def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → G.diam = 3 → G.minDegree = 2 →
    (∀ x, distEven G x ≤ 1 + G.secondSmallestDegree) →
    (∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card) →
    ∀ v u w : V, u ≠ w → G.neighborFinset v = {u,w} → G.Adj u w →
      (∀ x, G.dist u x ≤ 2) → G.degree u = G.secondSmallestDegree + 2 →
      Fintype.card V = 2 * G.secondSmallestDegree + 3 →
      ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → G.diam = 3 → G.minDegree = 2 →
    (∀ x, distEven G x ≤ 1 + G.secondSmallestDegree) →
    (∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card) →
    (∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) →
    2 * G.secondSmallestDegree + 2 ≤ Fintype.card V →
    Fintype.card V ≤ 3 * (G.secondSmallestDegree + 1) →
    ∀ v u w : V, u ≠ w → G.neighborFinset v = {u,w} →
      (∃ x, G.dist u x = 3) → (∃ x, G.dist w x = 3) →
      ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1.H1 := by
  classical
  intro center_case far_case V _ _ _ G _ hc hd hlow hupper heven hhall htriangle hmin
  set s := G.secondSmallestDegree with hs
  by_cases hsmall : Fintype.card V ≤ 2*s+1
  · exact trace_at_most_twice_second_add_one hc hsmall
  by_cases hm1 : G.minDegree = 1
  · exact trace_of_leaf hc hd.le hm1 hlow heven
  obtain ⟨v,hv⟩ := G.exists_minimal_degree_vertex
  obtain ⟨q,hq⟩ := hc.preconnected.exists_adj_of_nontrivial v
  have hpos : 0 < G.degree v := hq.degree_pos_left
  have hm2 : G.minDegree = 2 := by omega
  have hcard : (G.neighborFinset v).card = 2 := by rw [card_neighborFinset_eq_degree, ← hv, hm2]
  obtain ⟨u,w,huw,hn⟩ := Finset.card_eq_two.mp hcard
  have center (u w : V) (huw : u ≠ w) (hn : G.neighborFinset v = {u,w})
      (hcen : ∀ x, G.dist u x ≤ 2) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
    have neigh (x : V) : G.Adj v x ↔ x = u ∨ x = w := by
      rw [← G.mem_neighborFinset, hn]
      simp
    have hu := (neigh u).mpr (Or.inl rfl)
    have hw := (neigh w).mpr (Or.inr rfl)
    have hdeg := high_off_minimum hv.symm hu.ne.symm
    have hlim := (near_twins hc hu (fun x => (neigh x).mp) s (by simpa [Nat.add_comm] using heven v) hdeg).2
    have hcount := order_from_center hcen
    have hbound := heven u
    have hspos : 0 < s := by
      have hn3 : Fintype.card V ≤ 3 * (s+1) := by simpa [hm2] using hupper
      omega
    by_cases hauw : G.Adj u w
    · simp [hauw] at hlim
      by_cases hdu : G.degree u = s+1
      · exact trace_of_boundary_neighbor hv hu (by omega) hdu hspos
      · have hdu2 : G.degree u = s+2 := by omega
        by_cases heq : Fintype.card V = 2*s+2
        · exact trace_of_boundary_triangle hv hu hw hauw heq hdu2
        · exact center_case G hc hd hm2 heven hhall v u w huw hn hauw hcen hdu2 (by omega)
    · simp [hauw] at hlim
      exact trace_of_boundary_neighbor hv hu (by omega) (by omega) hspos
  by_cases hcu : ∀ x, G.dist u x ≤ 2
  · exact center u w huw hn hcu
  by_cases hcw : ∀ x, G.dist w x ≤ 2
  · exact center w u huw.symm (by simpa [Finset.pair_comm] using hn) hcw
  have far (z : V) (h : ¬ ∀ x, G.dist z x ≤ 2) : ∃ x, G.dist z x = 3 := by
    push Not at h
    obtain ⟨x,hx⟩ := h
    have hub := G.dist_le_diam (u := z) (v := x) (G.connected_iff_ediam_ne_top.mp hc)
    exact ⟨x,by omega⟩
  apply far_case G hc hd hm2 heven hhall htriangle (by omega) _ v u w huw hn (far u hcu) (far w hcw)
  simpa [hm2] using hupper

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1_H1_R1
