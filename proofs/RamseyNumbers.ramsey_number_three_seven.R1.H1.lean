import OMAReductions.R_RamseyNumbers_ramsey_number_three_seven_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Every graph on 18 vertices has a triangle or an independent set of size six

This is the upper-bound argument from the accepted R(3,6) proof by @ysanatomic,
adapted to the exact Ramsey property used in the reduction of R(3,7).
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1699

The argument follows David Cariolaro, On the Ramsey number R(3,6), 2007.
An avoiding graph would be 5-regular. Counting common neighbors forces a
four-cycle and three matchings, whose adjacencies contradict the same bound.
-/

open Finset SimpleGraph

private theorem ramsey36_not_triangle {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (ht : G.CliqueFree 3) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) : ¬ G.Adj b c :=
  fun hbc ↦ ht _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

private theorem ramsey36_no_three_common {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hupper : ∀ x y, x ≠ y → ¬ G.Adj x y →
        (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    {a b c d e : V} (hab : a ≠ b) (hn : ¬ G.Adj a b)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hac : G.Adj a c) (had : G.Adj a d) (hae : G.Adj a e)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hbe : G.Adj b e) : False := by
  have hsub : ({c, d, e} : Finset V) ⊆ G.neighborFinset a ∩ G.neighborFinset b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have ht := (Finset.card_le_card hsub).trans (hupper a b hab hn)
  simp [card_insert_of_notMem, hcd, hce, hde] at ht

/-- A triangle-free graph on four vertices of degree two has two common
neighbors in that set for each nonadjacent pair. -/
private theorem ramsey36_no_external_common {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (ht : G.CliqueFree 3)
    (hupper : ∀ x y, x ≠ y → ¬ G.Adj x y →
        (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    (P : Finset V) (hP : P.card = 4)
    (hd : ∀ p ∈ P, (G.neighborFinset p ∩ P).card = 2)
    {p q x : V} (hp : p ∈ P) (hq : q ∈ P) (hx : x ∉ P)
    (hpx : G.Adj p x) (hqx : G.Adj q x) : p = q := by
  by_contra hpq
  have hn := ramsey36_not_triangle ht hpx.symm hqx.symm
  let R := (P.erase p).erase q
  have hqp : q ≠ p := fun he ↦ hpq he.symm
  have hpq' : q ∈ P.erase p := by simp [hqp, hq]
  have hR : R.card = 2 := by
    rw [Finset.card_erase_of_mem hpq', Finset.card_erase_of_mem hp, hP]
  have hnp : G.neighborFinset p ∩ P = R := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      have ⟨ha, hmem⟩ := Finset.mem_inter.mp hy
      have ha' := (G.mem_neighborFinset _ _).mp ha
      simp only [R, Finset.mem_erase]
      exact ⟨fun h ↦ hn (h ▸ ha'), ha'.ne.symm, hmem⟩
    · rw [hR, hd p hp]
  have hnq : G.neighborFinset q ∩ P = R := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      have ⟨ha, hmem⟩ := Finset.mem_inter.mp hy
      have ha' := (G.mem_neighborFinset _ _).mp ha
      simp only [R, Finset.mem_erase]
      exact ⟨ha'.ne.symm, fun h ↦ hn (h ▸ ha'.symm), hmem⟩
    · rw [hR, hd q hq]
  have hsub : insert x R ⊆ G.neighborFinset p ∩ G.neighborFinset q := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simp [hpx, hqx]
    · exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp (hnp ▸ hy)).1, (Finset.mem_inter.mp (hnq ▸ hy)).1⟩
  have hnX : x ∉ R := fun hm ↦ hx (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))
  have hbound := (Finset.card_le_card hsub).trans (hupper p q hpq hn)
  rw [Finset.card_insert_of_notMem hnX, hR] at hbound
  omega

private theorem ramsey36_matching {V : Type} {G : SimpleGraph V}
    {P Q : Finset V} (hcard : P.card = Q.card)
    (hex : ∀ p ∈ P, ∃ q ∈ Q, G.Adj p q)
    (huniq : ∀ {p p' q}, p ∈ P → p' ∈ P → q ∈ Q → G.Adj p q → G.Adj p' q → p = p') :
    ∃ e : ↥P ≃ ↥Q, ∀ p : ↥P, ∀ q : ↥Q, G.Adj p.1 q.1 ↔ e p = q := by
  choose f hf hfAdj using fun p : ↥P ↦ hex p.1 p.2
  let g (p : ↥P) : ↥Q := ⟨f p, hf p⟩
  have hi : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have hval : f x = f y := congrArg Subtype.val hxy
    refine huniq x.2 y.2 (hf x) (hfAdj x) ?_
    rw [hval]
    exact hfAdj y
  let e₀ : ↥P ≃ ↥Q := Fintype.equivOfCardEq (by simpa using hcard)
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp (e₀.symm.injective.comp hi)) (e₀.symm q)
    exact ⟨a, e₀.symm.injective ha⟩
  let e := Equiv.ofBijective g ⟨hi, hsurj⟩
  refine ⟨e, fun p q ↦ ⟨?_, ?_⟩⟩
  · intro h
    obtain ⟨r, hr⟩ := hsurj q
    have hp : p = r := Subtype.ext <| huniq p.2 r.2 q.2 h
      (congrArg Subtype.val hr ▸ hfAdj r)
    change g p = q
    rwa [hp]
  · rintro rfl
    exact hfAdj p

private theorem ramsey36_last_contradiction {V ι : Type}
    [Fintype V] [Fintype ι] [DecidableEq V] [DecidableEq ι]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (ht : G.CliqueFree 3)
    (hupper : ∀ x y, x ≠ y → ¬ G.Adj x y →
        (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    (p s t w : ι → V) (hc : Fintype.card ι = 4)
    (hps : ∀ i j, G.Adj (p i) (s j) ↔ i = j)
    (hpt : ∀ i j, G.Adj (p i) (t j) ↔ i = j)
    (hpw : ∀ i j, G.Adj (p i) (w j) ↔ i = j)
    (hps' : ∀ i j, p i ≠ s j) (hpt' : ∀ i j, p i ≠ t j)
    (hpw' : ∀ i j, p i ≠ w j) (hst' : ∀ i j, s i ≠ t j) (htw' : ∀ i j, t i ≠ w j)
    (hpd : ∀ i, (Finset.univ.filter fun j ↦ G.Adj (p i) (p j)).card = 2)
    (hws : ∀ i, (Finset.univ.filter fun j ↦ G.Adj (w i) (s j)).card = 2)
    (hwt : ∀ i, (Finset.univ.filter fun j ↦ G.Adj (w i) (t j)).card = 2)
    (hst : ∀ i, ∃ j, G.Adj (s i) (t j)) : False := by
  have := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  let i : ι := Classical.choice inferInstance
  let S := Finset.univ.filter fun j ↦ G.Adj (w i) (s j)
  let T := Finset.univ.filter fun j ↦ G.Adj (w i) (t j)
  have hcS : S.card = 2 := hws i
  have hcT : T.card = 2 := hwt i
  have hiS : i ∉ S := by
    intro h
    exact ramsey36_not_triangle ht ((hpw i i).mpr rfl) ((hps i i).mpr rfl)
      (Finset.mem_filter.mp h).2
  have hiT : i ∉ T := by
    intro h
    exact ramsey36_not_triangle ht ((hpw i i).mpr rfl) ((hpt i i).mpr rfl)
      (Finset.mem_filter.mp h).2
  have hST : (S ∩ T).Nonempty := by
    by_contra h
    have hempty : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hcard := Finset.card_union_add_card_inter S T
    rw [hempty, card_empty, add_zero, hcS, hcT] at hcard
    have hfin : S ∪ T ⊆ (Finset.univ : Finset ι).erase i := by
      intro x hx
      have hne : x ≠ i := fun hx' ↦ by
        subst x
        exact (Finset.mem_union.mp hx).elim hiS hiT
      simp [hne]
    have hle := Finset.card_le_card hfin
    rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hc] at hle
    omega
  obtain ⟨j, hj⟩ := hST
  have hjS := (Finset.mem_inter.mp hj).1
  have hjT := (Finset.mem_inter.mp hj).2
  have hji : j ≠ i := fun h ↦ hiS (h ▸ hjS)
  have hnot (k : ι) (hne : k ≠ i) (hS : k ∈ S) (hT : k ∈ T) :
      ¬ G.Adj (p i) (p k) := by
    intro h
    exact ramsey36_no_three_common hupper (hpw' k i).symm (fun h' ↦ hne ((hpw k i).mp h'.symm))
      (hps' i k) (hpt' i k) (hst' k k) ((hpw i i).mpr rfl).symm
      (Finset.mem_filter.mp hS).2 (Finset.mem_filter.mp hT).2 h.symm
      ((hps k k).mpr rfl) ((hpt k k).mpr rfl)
  obtain ⟨k, hk⟩ : (S.erase j).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hjS, hcS]
    decide
  obtain ⟨hkj, hkS⟩ := Finset.mem_erase.mp hk
  have hki : k ≠ i := fun e ↦ hiS (e ▸ hkS)
  let I := ((Finset.univ : Finset ι).erase i).erase j
  have hI : I.card = 2 := by
    have hj' : j ∈ (Finset.univ : Finset ι).erase i := by simp [hji]
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hc]
  have hP : (Finset.univ.filter fun a ↦ G.Adj (p i) (p a)) = I := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      have h := (Finset.mem_filter.mp ha).2
      simp only [I, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun e ↦ hnot j hji hjS hjT (e ▸ h), fun e ↦ G.loopless.irrefl (p i) (e ▸ h)⟩
    · rw [hI, hpd]
  have hik : G.Adj (p i) (p k) := by
    have hmem : k ∈ I := by simp [I, hki, hkj]
    rw [← hP] at hmem
    exact (Finset.mem_filter.mp hmem).2
  have hkT : k ∉ T := fun h ↦ hnot k hki hkS h hik
  let J := ((Finset.univ : Finset ι).erase i).erase k
  have hJ : J.card = 2 := by
    have hk' : k ∈ (Finset.univ : Finset ι).erase i := by simp [hki]
    rw [Finset.card_erase_of_mem hk', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hc]
  have hT : T = J := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      have h₁ : a ≠ i := fun e ↦ hiT (e ▸ ha)
      have h₂ : a ≠ k := fun e ↦ hkT (e ▸ ha)
      simp [J, h₁, h₂]
    · rw [hJ, hcT]
  obtain ⟨a, ha⟩ := hst k
  have hak : a ≠ k := fun e ↦ ramsey36_not_triangle ht ((hps k k).mpr rfl)
    ((hpt k k).mpr rfl) (e ▸ ha)
  have haT : a ∉ T := fun h ↦
    ramsey36_not_triangle ht (Finset.mem_filter.mp hkS).2 (Finset.mem_filter.mp h).2 ha
  have hai : a = i := by
    by_contra hn
    exact haT (hT.symm ▸ (show a ∈ J by simp [J, hn, hak]))
  exact ramsey36_no_three_common hupper (hps' i k) (fun h ↦ hki.symm ((hps i k).mp h))
    (hpw' k i) (hpt' k i) (htw' i i).symm hik ((hpw i i).mpr rfl) ((hpt i i).mpr rfl)
    ((hps k k).mpr rfl).symm (Finset.mem_filter.mp hkS).2.symm (hai ▸ ha)



namespace OMA

open Finset SimpleGraph

private lemma ramsey36_nclique_pair {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b : V} (hab : G.Adj a b) : G.IsNClique 2 {a,b} := by
  refine ⟨?_, Finset.card_pair hab.ne⟩
  simpa only [Finset.coe_insert, Finset.coe_singleton] using
    G.isClique_pair.mpr (fun _ ↦ hab)

private lemma ramsey36_map_clique {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (e : H ↪g G) {S : Finset U} {k : ℕ} (hS : H.IsNClique k S) :
    G.IsNClique k (S.map e.toEmbedding) := by
  refine ⟨?_, by rw [Finset.card_map, hS.card_eq]⟩
  intro a ha b hb hab
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
  exact e.toHom.map_adj (hS.isClique hi hj (fun h ↦ hab (congrArg e h)))

private lemma ramsey36_on_subset {V : Type*} [DecidableEq V] (G : SimpleGraph V) {n k : ℕ}
    (hR : RamseyNumbers.IsGraphRamsey n 3 k) (ht : G.CliqueFree 3)
    {S : Finset V} (hcard : n ≤ S.card) :
    ∃ I : Finset V, I ⊆ S ∧ Gᶜ.IsNClique k I := by
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin n ↪ V :=
    (Finset.equivFinOfCardEq hT).symm.toEmbedding.trans (Function.Embedding.subtype _)
  let H : SimpleGraph (Fin n) := G.comap e
  let f : H ↪g G := SimpleGraph.Embedding.comap e G
  let fc : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv f
  have htc : H.CliqueFree 3 := ht.comap f.isContained
  have hrc : ¬ Hᶜ.CliqueFree k := fun h ↦ hR H ⟨htc, h⟩
  unfold SimpleGraph.CliqueFree at hrc
  push Not at hrc
  obtain ⟨I, hI⟩ := hrc
  refine ⟨I.map fc.toEmbedding, ?_, ramsey36_map_clique fc hI⟩
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
  exact hTS ((Finset.equivFinOfCardEq hT).symm i).property

private lemma ramsey36_neighbors_clique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : V) :
    Gᶜ.IsClique (G.neighborFinset v : Set V) := by
  intro a ha b hb hab
  rw [SimpleGraph.compl_adj]
  refine ⟨hab, fun hadj ↦ ?_⟩
  apply ht (insert v {a,b})
  exact (ramsey36_nclique_pair hadj).insert (by
    intro w hw
    rcases (by simpa using hw : w = a ∨ w = b) with hwa | hwb
    · rw [hwa]
      exact (G.mem_neighborFinset v a).mp ha
    · rw [hwb]
      exact (G.mem_neighborFinset v b).mp hb)

private lemma ramsey36_degree_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree k) (v : V) :
    G.degree v < k := by
  by_contra! h
  exact (hi.mono h) _ ⟨ramsey36_neighbors_clique G ht v, rfl⟩

private lemma ramsey36_compl_degree_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k : ℕ}
    (hR : RamseyNumbers.IsGraphRamsey n 3 k) (ht : G.CliqueFree 3)
    (hi : Gᶜ.CliqueFree (k + 1)) (v : V) :
    Gᶜ.degree v < n := by
  by_contra! h
  obtain ⟨I, hI, hIc⟩ := ramsey36_on_subset G hR ht (S := Gᶜ.neighborFinset v) h
  exact hi _ (hIc.insert fun a ha ↦ (Gᶜ.mem_neighborFinset v a).mp (hI ha))

private lemma ramsey36_R32 : RamseyNumbers.IsGraphRamsey 3 3 2 := by
  classical
  intro G ⟨ht, hi⟩
  apply ht Finset.univ
  refine ⟨?_, by simp⟩
  intro a _ b _ hab
  by_contra hn
  exact hi _ (ramsey36_nclique_pair ((SimpleGraph.compl_adj G a b).mpr ⟨hab, hn⟩))

private lemma ramsey36_R33 : RamseyNumbers.IsGraphRamsey 6 3 3 := by
  classical
  intro G ⟨ht, hi⟩
  have hd := ramsey36_degree_lt G ht hi 0
  have hc := ramsey36_compl_degree_lt G ramsey36_R32 ht hi 0
  rw [G.degree_compl] at hc
  simp at hc
  omega

private lemma ramsey36_R34 : RamseyNumbers.IsGraphRamsey 9 3 4 := by
  classical
  intro G ⟨ht, hi⟩
  have hd (v : Fin 9) := ramsey36_degree_lt G ht hi v
  have hc (v : Fin 9) := ramsey36_compl_degree_lt G ramsey36_R33 ht hi v
  have heq (v : Fin 9) : G.degree v = 3 := by
    have h := hc v
    rw [G.degree_compl] at h
    simp at h
    have := hd v
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  omega

private lemma ramsey36_R35 : RamseyNumbers.IsGraphRamsey 14 3 5 := by
  classical
  intro G ⟨ht, hi⟩
  have hd := ramsey36_degree_lt G ht hi 0
  have hc := ramsey36_compl_degree_lt G ramsey36_R34 ht hi 0
  rw [G.degree_compl] at hc
  simp at hc
  omega

private lemma ramsey36_degree_four {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 13)
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 5) (v : V) :
    G.degree v = 4 := by
  have hd := ramsey36_degree_lt G ht hi v
  have hc := ramsey36_compl_degree_lt G ramsey36_R34 ht hi v
  rw [G.degree_compl, hV] at hc
  omega

private lemma ramsey36_degree_at_least_four
    (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6) (v : Fin 18) : 4 ≤ G.degree v := by
  have hc := ramsey36_compl_degree_lt G ramsey36_R35 ht hi v
  rw [G.degree_compl] at hc
  simp at hc
  omega

/-- An eighteen-vertex triangle-free graph without an independent set of size six is 5-regular. -/
lemma ramsey36_degree_eq_five (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6) (v : Fin 18) :
    G.degree v = 5 := by
  classical
  have hd (w : Fin 18) := ramsey36_degree_lt G ht hi w
  have hl (w : Fin 18) := ramsey36_degree_at_least_four G ht hi w
  by_contra hneq
  have h4 : G.degree v = 4 := by have := hd v; have := hl v; omega
  let S := Gᶜ.neighborFinset v
  let H := G.induce (S : Set (Fin 18))
  let e : H ↪g G := SimpleGraph.Embedding.induce (G := G) (S : Set (Fin 18))
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  have h13 : S.card = 13 := by
    rw [show S = Gᶜ.neighborFinset v from rfl, card_neighborFinset_eq_degree,
      G.degree_compl, h4]
    decide
  have hHV : Fintype.card ↥(S : Set (Fin 18)) = 13 := (Fintype.card_coe S).trans h13
  have hHt : H.CliqueFree 3 := ht.comap e.isContained
  have hHi : Hᶜ.CliqueFree 5 := by
    intro I hI
    apply hi _
    apply (ramsey36_map_clique ec hI).insert
    intro w hw
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hw
    exact (Gᶜ.mem_neighborFinset v z.val).mp z.property
  have h4S (u : Fin 18) (hu : u ∈ S) : (G.neighborFinset u ∩ S).card = 4 := by
    let w : (S : Set (Fin 18)) := ⟨u, hu⟩
    have hw := ramsey36_degree_four H hHV hHt hHi w
    have hmap := G.map_neighborFinset_induce (s := (S : Set (Fin 18))) w
    rw [Finset.toFinset_coe] at hmap
    rw [← hmap, Finset.card_map, card_neighborFinset_eq_degree]
    exact (congrArg (fun J : Fintype (H.neighborSet w) ↦ @SimpleGraph.degree _ H w J)
      (Subsingleton.elim _ _)).trans hw
  have hpos : (G.neighborFinset v).Nonempty := Finset.card_pos.mp (by
    simpa only [card_neighborFinset_eq_degree, h4] using (by decide : 0 < 4))
  obtain ⟨t, htA⟩ := hpos
  have hvt := (G.mem_neighborFinset v t).mp htA
  let A := (G.neighborFinset v).erase t
  let B := (G.neighborFinset t).erase v
  have hAcard : A.card = 3 := by
    simp [A, Finset.card_erase_of_mem htA, h4]
  have hBcard : 3 ≤ B.card := by
    have hvt' := (G.mem_neighborFinset t v).mpr hvt.symm
    have hlt := hl t
    simp only [B, Finset.card_erase_of_mem hvt', card_neighborFinset_eq_degree]
    omega
  obtain ⟨J, hJB, hJcard⟩ := Finset.exists_subset_card_eq hBcard
  have hJS : J ⊆ S := by
    intro u hu
    obtain ⟨huv, huA⟩ := Finset.mem_erase.mp (hJB hu)
    apply (Gᶜ.mem_neighborFinset v u).mpr
    rw [SimpleGraph.compl_adj]
    exact ⟨huv.symm, fun hadj ↦
      (ramsey36_neighbors_clique G ht v htA ((G.mem_neighborFinset v u).mpr hadj)
        ((G.mem_neighborFinset t u).mp huA).ne).2 ((G.mem_neighborFinset t u).mp huA)⟩
  have hSnot {u : Fin 18} (hu : u ∈ G.neighborFinset v) : u ∉ S := by
    intro h
    exact ((Gᶜ.mem_neighborFinset v u).mp h).2 ((G.mem_neighborFinset v u).mp hu)
  have hdis : Disjoint A J := Finset.disjoint_left.mpr fun _ ha hj ↦
    hSnot (Finset.mem_of_mem_erase ha) (hJS hj)
  have hcross (a : Fin 18) (ha : a ∈ A) (b : Fin 18) (hb : b ∈ J) :
      ¬ G.Adj a b := by
    intro hab
    let W := G.neighborFinset b ∩ S
    have hWcard : W.card = 4 := h4S b (hJS hb)
    have haW : a ∉ W := fun h ↦ hSnot (Finset.mem_of_mem_erase ha) (Finset.mem_inter.mp h).2
    have htW : t ∉ W := fun h ↦ hSnot htA (Finset.mem_inter.mp h).2
    have hat := (Finset.mem_erase.mp ha).1
    have hmem : insert t (insert a W) ⊆ G.neighborFinset b := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with hzt | hza | hz
      · rw [hzt]
        exact (G.mem_neighborFinset b t).mpr
          ((G.mem_neighborFinset t b).mp (Finset.mem_of_mem_erase (hJB hb))).symm
      · rw [hza]
        exact (G.mem_neighborFinset b a).mpr hab.symm
      · exact (Finset.mem_inter.mp hz).1
    have hcard := Finset.card_le_card hmem
    rw [Finset.card_insert_of_notMem (by simp [hat.symm, htW]),
      Finset.card_insert_of_notMem haW, hWcard, card_neighborFinset_eq_degree] at hcard
    have := hd b
    omega
  apply hi (A ∪ J)
  refine ⟨?_, by rw [Finset.card_union_of_disjoint hdis, hAcard, hJcard]⟩
  rw [Finset.coe_union]
  change ((↑A : Set (Fin 18)) ∪ ↑J).Pairwise Gᶜ.Adj
  rw [Set.pairwise_union]
  refine ⟨(ramsey36_neighbors_clique G ht v).subset ?_,
    (ramsey36_neighbors_clique G ht t).subset ?_, ?_⟩
  · exact fun _ ha ↦ Finset.mem_of_mem_erase ha
  · exact fun _ hb ↦ Finset.mem_of_mem_erase (hJB hb)
  · intro a ha b hb hab
    have h := (SimpleGraph.compl_adj G a b).mpr ⟨hab, hcross a ha b hb⟩
    exact ⟨h, h.symm⟩

/-- Distinct nonadjacent vertices have either one or two common neighbors. -/
lemma ramsey36_common_bounds (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6)
    {x y : Fin 18} (hne : x ≠ y) (hnadj : ¬ G.Adj x y) :
    1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card ∧
      (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2 := by
  classical
  have hx := ramsey36_degree_eq_five G ht hi x
  have hy := ramsey36_degree_eq_five G ht hi y
  have hcx : Gᶜ.IsNClique 5 (G.neighborFinset x) :=
    ⟨ramsey36_neighbors_clique G ht x, hx⟩
  constructor
  · by_contra! hz
    have hz' : G.neighborFinset x ∩ G.neighborFinset y = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    apply hi _
    apply hcx.insert (a := y)
    intro z hz
    rw [SimpleGraph.compl_adj]
    constructor
    · intro h
      apply hnadj
      rw [h]
      exact (G.mem_neighborFinset x z).mp hz
    · intro haz
      have him : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
        Finset.mem_inter.mpr ⟨hz, (G.mem_neighborFinset y z).mpr haz⟩
      simp [hz'] at him
  · by_contra! hlarge
    let U := G.neighborFinset x ∪ G.neighborFinset y
    let W := Finset.univ \ insert x (insert y U)
    have hUc : U.card + (G.neighborFinset x ∩ G.neighborFinset y).card = 10 := by
      simpa only [U, card_neighborFinset_eq_degree, hx, hy] using
        Finset.card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
    have hUc' := Finset.card_insert_le x (insert y U)
    have hUc'' := Finset.card_insert_le y U
    have hWc : W.card + (insert x (insert y U)).card = 18 := by
      simpa [W] using Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ (insert x (insert y U)))
    have hW9 : 9 ≤ W.card := by omega
    obtain ⟨I, hIW, hIc⟩ := ramsey36_on_subset G ramsey36_R34 ht hW9
    have hIx (z : Fin 18) (hz : z ∈ I) : Gᶜ.Adj x z := by
      have h := hIW hz
      simp only [W, U, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_union, G.mem_neighborFinset, not_or] at h
      exact (SimpleGraph.compl_adj G x z).mpr ⟨fun hxz ↦ h.1 hxz.symm, h.2.2.1⟩
    have hIy (z : Fin 18) (hz : z ∈ I) : Gᶜ.Adj y z := by
      have h := hIW hz
      simp only [W, U, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_union, G.mem_neighborFinset, not_or] at h
      exact (SimpleGraph.compl_adj G y z).mpr ⟨fun hyz ↦ h.2.1 hyz.symm, h.2.2.2⟩
    apply hi _
    apply (hIc.insert hIx).insert
    intro z hz
    rcases Finset.mem_insert.mp hz with hzx | hz
    · rw [hzx]
      exact (SimpleGraph.compl_adj G y x).mpr ⟨hne.symm, fun h ↦ hnadj h.symm⟩
    · exact hIy z hz

end OMA

namespace OMA.RamseyThreeSix

open Finset SimpleGraph

lemma has_neighbor_in_fourth_part {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p v t : V} {S P T W : Finset V}
    (cover : ∀ x, x = v ∨ x = t ∨ x ∈ S ∨ x ∈ P ∨ x ∈ T ∨ x ∈ W)
    (hpv : ¬ G.Adj p v) (hpt : ¬ G.Adj p t) (hdegree : G.degree p = 5)
    (hs : (G.neighborFinset p ∩ S).card = 1) (hp : (G.neighborFinset p ∩ P).card = 2)
    (ht : (G.neighborFinset p ∩ T).card = 1) : ∃ w ∈ W, G.Adj p w := by
  by_contra hnone
  let N := G.neighborFinset p
  have hcover : N ⊆ (N ∩ S) ∪ (N ∩ P) ∪ (N ∩ T) := by
    intro x hx
    have hAdj : G.Adj p x := by simpa [N] using hx
    rcases cover x with rfl | rfl | hS | hP | hT | hW
    · exact (hpv hAdj).elim
    · exact (hpt hAdj).elim
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hx, hS⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hx, hP⟩))
    · exact mem_union_right _ (mem_inter.mpr ⟨hx, hT⟩)
    · exact (hnone ⟨x, hW, hAdj⟩).elim
  have hcount : N.card ≤ 4 := calc
    N.card ≤ ((N ∩ S) ∪ (N ∩ P) ∪ (N ∩ T)).card := card_le_card hcover
    _ ≤ ((N ∩ S) ∪ (N ∩ P)).card + (N ∩ T).card := card_union_le _ _
    _ ≤ (N ∩ S).card + (N ∩ P).card + (N ∩ T).card :=
      Nat.add_le_add_right (card_union_le _ _) _
    _ = 4 := by simp [N, hs, hp, ht]
  have hcard : N.card = 5 := hdegree
  omega

lemma card_neighborFinset_inter_equiv {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) {S : Finset V} (f : ι ≃ ↥S) :
    (G.neighborFinset v ∩ S).card =
      ((Finset.univ : Finset ι).filter (fun i => G.Adj v (f i).val)).card := by
  symm
  refine Finset.card_bij (fun i _ => (f i).val) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_inter.mpr ⟨by simpa using (Finset.mem_filter.mp hi).2, (f i).property⟩
  · intro i _ j _ hij
    exact f.injective (Subtype.ext hij)
  · intro x hx
    let y : ↥S := ⟨x, (Finset.mem_inter.mp hx).2⟩
    have hadj : G.Adj v x := by simpa using (Finset.mem_inter.mp hx).1
    refine ⟨f.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa [y] using hadj
    · simp [y]

end OMA.RamseyThreeSix

namespace OMA.ER36

open Finset SimpleGraph

abbrev V := Fin 18

structure LocalConfiguration (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) where
  t : V
  P : Finset V
  S : Finset V
  T : Finset V
  W : Finset V
  t_adj : G.Adj v t
  P_eq : P = (univ.erase v \ G.neighborFinset v).filter
    (fun p ↦ ((G.neighborFinset v) ∩ (G.neighborFinset p)).card = 1)
  S_eq : S = (G.neighborFinset v).erase t
  T_eq : T = (G.neighborFinset t).erase v
  P_card : P.card = 4
  S_card : S.card = 4
  T_card : T.card = 4
  W_card : W.card = 4
  P_outside : P ⊆ univ.erase v \ G.neighborFinset v
  T_outside : T ⊆ univ.erase v \ G.neighborFinset v
  W_outside : W ⊆ univ.erase v \ G.neighborFinset v
  P_disj_T : Disjoint P T
  P_disj_W : Disjoint P W
  T_disj_W : Disjoint T W
  cover : ∀ x : V, x = v ∨ x = t ∨ x ∈ S ∨ x ∈ P ∨ x ∈ T ∨ x ∈ W
  P_one_S : ∀ p ∈ P, (G.neighborFinset p ∩ S).card = 1
  S_one_P : ∀ s ∈ S, (G.neighborFinset s ∩ P).card = 1
  T_one_S : ∀ u ∈ T, (G.neighborFinset u ∩ S).card = 1
  S_one_T : ∀ s ∈ S, (G.neighborFinset s ∩ T).card = 1
  W_two_S : ∀ w ∈ W, (G.neighborFinset w ∩ S).card = 2
  P_reg : ∀ p ∈ P, (G.neighborFinset p ∩ P).card = 2
  P_has_T : ∀ p ∈ P, (G.neighborFinset p ∩ T).Nonempty

variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem neighborhood_independent (htriangle : G.CliqueFree 3) (v : V)
    {x y : V} (hx : x ∈ G.neighborFinset v) (hy : y ∈ G.neighborFinset v) : ¬ G.Adj x y := by
  intro hxy
  exact htriangle {v, x, y}
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨(G.mem_neighborFinset _ _).mp hx, (G.mem_neighborFinset _ _).mp hy, hxy⟩)

omit [DecidableRel G.Adj] in
private theorem independent_card_le (hindep : Gᶜ.CliqueFree 6) {A : Finset V}
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) : A.card ≤ 5 := by
  by_contra! hn
  obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq (s := A) (n := 6) (by omega)
  refine hindep B ⟨?_, hBcard⟩
  intro x hx y hy hxy
  exact ⟨hxy, hA x (hBA hx) y (hBA hy)⟩

omit [DecidableRel G.Adj] in
private theorem independent_insert {A : Finset V} {a : V}
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) (ha : ∀ x ∈ A, ¬ G.Adj a x) :
    ∀ x ∈ insert a A, ∀ y ∈ insert a A, ¬ G.Adj x y := by
  intro x hx y hy
  rcases mem_insert.mp hx with hxa | hxA
  · subst x
    rcases mem_insert.mp hy with hya | hyA
    · subst y
      exact fun hadj ↦ (G.ne_of_adj hadj) rfl
    · exact ha y hyA
  · rcases mem_insert.mp hy with hya | hyA
    · subst y
      exact fun hadj ↦ ha x hxA hadj.symm
    · exact hA x hxA y hyA

private theorem incidence_count (A B : Finset V) :
    (∑ a ∈ A, (G.neighborFinset a ∩ B).card) = ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
  have hd (a : V) (S : Finset V) :
      (G.neighborFinset a ∩ S).card = ∑ x ∈ S, if G.Adj a x then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext x
    simp [and_comm]
  simp_rw [hd]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ by
    simp only [G.adj_comm a b]

private theorem reverse_matching {A B : Finset V}
    (hcard : A.card = B.card)
    (hA : ∀ a ∈ A, (G.neighborFinset a ∩ B).card = 1)
    (hB : ∀ b ∈ B, (G.neighborFinset b ∩ A).card ≤ 1) :
    ∀ b ∈ B, (G.neighborFinset b ∩ A).card = 1 := by
  have hsum : ∑ b ∈ B, (G.neighborFinset b ∩ A).card = B.card := by
    rw [incidence_count G B A]
    calc
      _ = ∑ _a ∈ A, 1 := Finset.sum_congr rfl hA
      _ = _ := by simpa using hcard
  intro b hb
  have hrest : ∑ z ∈ B.erase b, (G.neighborFinset z ∩ A).card ≤ (B.erase b).card := by
    calc
      _ ≤ ∑ _z ∈ B.erase b, 1 := Finset.sum_le_sum fun z hz ↦ hB z (Finset.mem_of_mem_erase hz)
      _ = _ := by simp
  rw [Finset.card_erase_of_mem hb] at hrest
  rw [← Finset.sum_erase_add B (fun z ↦ (G.neighborFinset z ∩ A).card) hb] at hsum
  have hb' := hB b hb
  have hBpos := Finset.card_pos.mpr ⟨b, hb⟩
  omega

private theorem inter_card_union {B C : Finset V} (A : Finset V) (h : Disjoint B C) :
    (A ∩ (B ∪ C)).card = (A ∩ B).card + (A ∩ C).card := by
  rw [inter_union_distrib_left, Finset.card_union_of_disjoint]
  exact h.mono Finset.inter_subset_right Finset.inter_subset_right

private theorem common_neighbor_unique_pair
    (hcommon : ∀ x y, x ≠ y → ¬ G.Adj x y → ((G.neighborFinset x) ∩ (G.neighborFinset y)).card ≤ 2)
    {v s t a b : V} (hst : s ≠ t) (hsnt : ¬ G.Adj s t)
    (hvs : G.Adj s v) (hvt : G.Adj t v)
    (hav : a ≠ v) (hbv : b ≠ v)
    (hsa : G.Adj s a) (hta : G.Adj t a)
    (hsb : G.Adj s b) (htb : G.Adj t b) : a = b := by
  by_contra hab
  have hsub : ({a, b, v} : Finset V) ⊆ G.neighborFinset s ∩ G.neighborFinset t := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hvs, hvt, hsa, hta, hsb, htb]
  have hcard := Finset.card_le_card hsub
  simp [hab, hav, hbv] at hcard
  have hbound := hcommon s t hst hsnt
  omega

theorem local_configuration (htriangle : G.CliqueFree 3) (hindep : Gᶜ.CliqueFree 6)
    (hdeg : ∀ x, (G.neighborFinset x).card = 5)
    (hcommon : ∀ x y, x ≠ y → ¬ G.Adj x y →
      1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card ∧ (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    (v : V) : Nonempty (LocalConfiguration G v) := by
  let U := G.neighborFinset v
  let H := (univ.erase v) \ U
  have hU : U.card = 5 := hdeg v
  have hHmem {x : V} : x ∈ H ↔ x ≠ v ∧ ¬ G.Adj v x := by simp [H, U]
  have hUind {x y : V} (hx : x ∈ U) (hy : y ∈ U) : ¬ G.Adj x y :=
    neighborhood_independent G htriangle v hx hy
  have hHcard : H.card = 12 := by
    have hsub : U ⊆ (univ : Finset V).erase v := by
      intro x hx
      exact mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset _ _).mp hx)).symm, mem_univ _⟩
    dsimp only [H]
    rw [card_sdiff_of_subset hsub, card_erase_of_mem (mem_univ _), hU]
    decide
  have hNoutside {x : V} (hx : x ∈ U) : G.neighborFinset x ∩ H = (G.neighborFinset x).erase v := by
    ext z
    simp only [mem_inter, hHmem, mem_erase, mem_neighborFinset]
    constructor
    · exact fun h ↦ ⟨h.2.1, h.1⟩
    · rintro ⟨hne, hadj⟩
      exact ⟨hadj, hne, fun hz ↦ hUind hx ((G.mem_neighborFinset _ _).mpr hz) hadj⟩
  have hNoutside_card {x : V} (hx : x ∈ U) : (G.neighborFinset x ∩ H).card = 4 := by
    rw [hNoutside hx, card_erase_of_mem, hdeg]
    exact (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hx).symm
  let P := H.filter fun x ↦ (U ∩ G.neighborFinset x).card = 1
  let Q := H.filter fun x ↦ (U ∩ G.neighborFinset x).card = 2
  have hPsub : P ⊆ H := filter_subset _ _
  have hQsub : Q ⊆ H := filter_subset _ _
  have hPdeg {x : V} (hx : x ∈ P) : (G.neighborFinset x ∩ U).card = 1 := by
    rw [inter_comm]
    exact (mem_filter.mp hx).2
  have hQdeg {x : V} (hx : x ∈ Q) : (G.neighborFinset x ∩ U).card = 2 := by
    rw [inter_comm]
    exact (mem_filter.mp hx).2
  have hPQ : P ∪ Q = H := by
    ext x
    constructor
    · exact fun hx ↦ (mem_union.mp hx).elim (fun hp ↦ hPsub hp) (fun hq ↦ hQsub hq)
    · intro hx
      obtain ⟨hne, hnadj⟩ := hHmem.mp hx
      have h := hcommon v x hne.symm hnadj
      have hc : (U ∩ G.neighborFinset x).card = 1 ∨ (U ∩ G.neighborFinset x).card = 2 := by
        change 1 ≤ (U ∩ G.neighborFinset x).card ∧ (U ∩ G.neighborFinset x).card ≤ 2 at h
        omega
      exact mem_union.mpr (hc.imp (fun hc ↦ mem_filter.mpr ⟨hx, hc⟩)
        (fun hc ↦ mem_filter.mpr ⟨hx, hc⟩))
  have hPQ_disj : Disjoint P Q := by
    refine Finset.disjoint_left.mpr fun x hp hq ↦ ?_
    exact (by decide : 1 ≠ 2) ((hPdeg hp).symm.trans (hQdeg hq))
  have hPcard : P.card = 4 := by
    have htot : (∑ x ∈ U, (G.neighborFinset x ∩ H).card) = 20 := by
      calc
        _ = ∑ _x ∈ U, 4 := sum_congr rfl fun _ hx ↦ hNoutside_card hx
        _ = _ := by simp [hU]
    rw [incidence_count G U H, ← hPQ, sum_union hPQ_disj,
      sum_congr rfl (fun _ hx ↦ hPdeg hx),
      sum_congr rfl (fun _ hx ↦ hQdeg hx)] at htot
    simp at htot
    have hcards := card_union_of_disjoint hPQ_disj
    rw [hPQ, hHcard] at hcards
    omega
  have hQcard : Q.card = 8 := by
    have h := card_union_of_disjoint hPQ_disj
    rw [hPQ, hHcard, hPcard] at h
    omega
  have hPunique {p x y : V} (hp : p ∈ P) (hx : x ∈ U) (hy : y ∈ U)
      (hpx : G.Adj p x) (hpy : G.Adj p y) : x = y :=
    Finset.card_le_one_iff.mp (hPdeg hp).le
      (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hpx, hx⟩)
      (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hpy, hy⟩)
  have hUPle {x : V} (hx : x ∈ U) : (G.neighborFinset x ∩ P).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro p q hp hq
    obtain ⟨hxp', hpP⟩ := mem_inter.mp hp
    obtain ⟨hxq', hqP⟩ := mem_inter.mp hq
    have hxp := (G.mem_neighborFinset _ _).mp hxp'
    have hxq := (G.mem_neighborFinset _ _).mp hxq'
    by_contra hpq
    have hp_out : p ∉ U := (mem_sdiff.mp (hPsub hpP)).2
    have hq_out : q ∉ U := (mem_sdiff.mp (hPsub hqP)).2
    have hn : ¬ G.Adj p q := neighborhood_independent G htriangle x hxp' hxq'
    have hpU (z : V) (hz : z ∈ U.erase x) : ¬ G.Adj p z := fun h ↦
      (mem_erase.mp hz).1 (hPunique hpP (mem_of_mem_erase hz) hx h hxp.symm)
    have hqU (z : V) (hz : z ∈ U.erase x) : ¬ G.Adj q z := fun h ↦
      (mem_erase.mp hz).1 (hPunique hqP (mem_of_mem_erase hz) hx h hxq.symm)
    have hi : ∀ a ∈ insert p (insert q (U.erase x)), ∀ b ∈ insert p (insert q (U.erase x)),
        ¬ G.Adj a b := by
      intro a ha b hb
      simp only [mem_insert] at ha hb
      rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
      · exact fun hadj ↦ (G.ne_of_adj hadj) rfl
      · exact hn
      · exact hpU _ hb
      · exact fun h ↦ hn h.symm
      · exact fun hadj ↦ (G.ne_of_adj hadj) rfl
      · exact hqU _ hb
      · exact fun h ↦ hpU _ ha h.symm
      · exact fun h ↦ hqU _ ha h.symm
      · exact hUind (mem_of_mem_erase ha) (mem_of_mem_erase hb)
    have hpc : p ∉ insert q (U.erase x) := by
      simp only [mem_insert]
      exact fun h ↦ h.elim hpq (fun hp ↦ hp_out (mem_of_mem_erase hp))
    have hqc : q ∉ U.erase x := fun hq ↦ hq_out (mem_of_mem_erase hq)
    have hbound := independent_card_le G hindep hi
    rw [card_insert_of_notMem hpc, card_insert_of_notMem hqc, card_erase_of_mem hx, hU] at hbound
    omega
  let S := U.filter fun x ↦ (G.neighborFinset x ∩ P).Nonempty
  have hSsub : S ⊆ U := filter_subset _ _
  have hSPdeg {s : V} (hs : s ∈ S) : (G.neighborFinset s ∩ P).card = 1 := by
    have hp := Finset.card_pos.mpr (mem_filter.mp hs).2
    have hle := hUPle (hSsub hs)
    omega
  have hPSdeg {p : V} (hp : p ∈ P) : (G.neighborFinset p ∩ S).card = 1 := by
    have heq : G.neighborFinset p ∩ S = G.neighborFinset p ∩ U := by
      ext s
      constructor
      · exact fun h ↦ mem_inter.mpr ⟨(mem_inter.mp h).1, hSsub (mem_inter.mp h).2⟩
      · rintro h
        obtain ⟨hps, hs⟩ := mem_inter.mp h
        exact mem_inter.mpr ⟨hps, mem_filter.mpr ⟨hs, ⟨p, mem_inter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hps).symm, hp⟩⟩⟩⟩
    rw [heq, hPdeg hp]
  have hScard : S.card = 4 := by
    have hs : (∑ s ∈ S, (G.neighborFinset s ∩ P).card) = S.card := by
      calc
        _ = ∑ _s ∈ S, 1 := Finset.sum_congr rfl fun _ hs ↦ hSPdeg hs
        _ = _ := by simp
    rw [incidence_count G S P, sum_congr rfl (fun _ hp ↦ hPSdeg hp)] at hs
    simpa [hPcard] using hs.symm
  obtain ⟨t, ht⟩ := card_eq_one.mp
    (show (U \ S).card = 1 by rw [card_sdiff_of_subset hSsub, hU, hScard])
  have htu : t ∈ U := (mem_sdiff.mp (show t ∈ U \ S by simp [ht])).1
  have htS : t ∉ S := (mem_sdiff.mp (show t ∈ U \ S by simp [ht])).2
  have htAdj : G.Adj v t := (G.mem_neighborFinset _ _).mp htu
  have hS_eq : S = U.erase t := by
    ext x
    have heq : (x ∈ U ∧ x ∉ S) ↔ x = t := by
      simpa only [mem_sdiff, mem_singleton] using Finset.ext_iff.mp ht x
    simp only [mem_erase]
    constructor
    · exact fun hx ↦ ⟨fun h ↦ htS (h ▸ hx), hSsub hx⟩
    · exact fun h ↦ by_contra fun hn ↦ h.1 (heq.mp ⟨h.2, hn⟩)
  let T := (G.neighborFinset t).erase v
  have hTH : T ⊆ H := by
    rw [show T = G.neighborFinset t ∩ H from (hNoutside htu).symm]
    exact inter_subset_right
  have hTcard : T.card = 4 := by
    simpa only [T, ← hNoutside htu] using hNoutside_card htu
  have hTP_disj : Disjoint T P := by
    refine Finset.disjoint_left.mpr fun x hxt hxp ↦ htS ?_
    have htx := (G.mem_neighborFinset _ _).mp (mem_of_mem_erase hxt)
    exact mem_filter.mpr ⟨htu, ⟨x, mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr htx, hxp⟩⟩⟩
  have hTQ : T ⊆ Q := by
    intro x hx
    have hh : x ∈ P ∪ Q := hPQ ▸ hTH hx
    exact (mem_union.mp hh).resolve_left fun hp ↦ Finset.disjoint_left.mp hTP_disj hx hp
  let W := Q \ T
  have hWQ : W ⊆ Q := sdiff_subset
  have hWcard : W.card = 4 := by
    dsimp only [W]
    rw [card_sdiff_of_subset hTQ, hQcard, hTcard]
  have hWnotT {x : V} (hx : x ∈ W) : x ∉ T := (mem_sdiff.mp hx).2
  have hSTdeg {u : V} (hu : u ∈ T) : (G.neighborFinset u ∩ S).card = 1 := by
    have htu' := (G.mem_neighborFinset _ _).mp (mem_of_mem_erase hu)
    have hmem : t ∈ G.neighborFinset u ∩ U := mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr htu'.symm, htu⟩
    rw [hS_eq, inter_erase, card_erase_of_mem hmem, hQdeg (hTQ hu)]
  have hTSle {s : V} (hs : s ∈ S) : (G.neighborFinset s ∩ T).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr fun hx hy ↦ ?_
    obtain ⟨hxs, hxT⟩ := mem_inter.mp hx
    obtain ⟨hys, hyT⟩ := mem_inter.mp hy
    have hsv := (G.mem_neighborFinset _ _).mp (hSsub hs)
    have hst : s ≠ t := (mem_erase.mp (hS_eq ▸ hs)).1
    exact common_neighbor_unique_pair G (fun x y hne hadj ↦ (hcommon x y hne hadj).2)
      hst (hUind (hSsub hs) htu) hsv.symm htAdj.symm
      (mem_erase.mp hxT).1 (mem_erase.mp hyT).1
      ((G.mem_neighborFinset _ _).mp hxs) ((G.mem_neighborFinset _ _).mp (mem_of_mem_erase hxT))
      ((G.mem_neighborFinset _ _).mp hys) ((G.mem_neighborFinset _ _).mp (mem_of_mem_erase hyT))
  have hTSdeg {s : V} (hs : s ∈ S) : (G.neighborFinset s ∩ T).card = 1 :=
    reverse_matching G (hTcard.trans hScard.symm) (fun _ ↦ hSTdeg) (fun _ ↦ hTSle) s hs
  have hWSdeg {w : V} (hw : w ∈ W) : (G.neighborFinset w ∩ S).card = 2 := by
    have hne := (hHmem.mp (hQsub (hWQ hw))).1
    have hnot : t ∉ G.neighborFinset w ∩ U := by
      intro ht
      have hadj := (G.mem_neighborFinset _ _).mp (mem_inter.mp ht).1
      exact hWnotT hw (mem_erase.mpr ⟨hne, (G.mem_neighborFinset _ _).mpr hadj.symm⟩)
    rw [hS_eq, inter_erase, erase_eq_of_notMem hnot, hQdeg (hWQ hw)]
  have hPW_disj : Disjoint P W := hPQ_disj.mono_right hWQ
  have hTW_disj : Disjoint T W := Finset.disjoint_left.mpr fun _ hx hy ↦ hWnotT hy hx
  have hQTW : T ∪ W = Q := by
    rw [union_comm]
    exact Finset.sdiff_union_of_subset hTQ
  have hcover (x : V) : x = v ∨ x = t ∨ x ∈ S ∨ x ∈ P ∨ x ∈ T ∨ x ∈ W := by
    by_cases hxv : x = v
    · exact Or.inl hxv
    by_cases hxu : x ∈ U
    · by_cases hxt : x = t
      · exact Or.inr (Or.inl hxt)
      · exact Or.inr (Or.inr (Or.inl (hS_eq.symm ▸ mem_erase.mpr ⟨hxt, hxu⟩)))
    · have hxH : x ∈ H := mem_sdiff.mpr ⟨mem_erase.mpr ⟨hxv, mem_univ _⟩, hxu⟩
      rcases mem_union.mp (hPQ.symm ▸ hxH) with hp | hq
      · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
      · rcases mem_union.mp (hQTW.symm ▸ hq) with ht | hw
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hw))))
  have hPTnonempty {p : V} (hp : p ∈ P) : (G.neighborFinset p ∩ T).Nonempty := by
    obtain ⟨hpv, hvp⟩ := hHmem.mp (hPsub hp)
    have hpt : ¬ G.Adj p t := by
      intro hadj
      exact htS (mem_filter.mpr ⟨htu, ⟨p,
        mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hp⟩⟩⟩)
    have hpne : p ≠ t := fun h ↦ (mem_sdiff.mp (hPsub hp)).2 (h.symm ▸ htu)
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (hcommon p t hpne hpt).1
    obtain ⟨hpu, htu⟩ := mem_inter.mp hu
    have hne : u ≠ v := fun h ↦ hvp (h ▸ ((G.mem_neighborFinset _ _).mp hpu).symm)
    exact ⟨u, mem_inter.mpr ⟨hpu, mem_erase.mpr ⟨hne, htu⟩⟩⟩
  have hSWdeg {s : V} (hs : s ∈ S) : (G.neighborFinset s ∩ W).card = 2 := by
    have h := hNoutside_card (hSsub hs)
    rw [← hPQ, inter_card_union _ hPQ_disj, hSPdeg hs, ← hQTW,
      inter_card_union _ hTW_disj, hTSdeg hs] at h
    omega
  have hforce {p q w s r : V} (hp : p ∈ P) (hq : q ∈ P) (hw : w ∈ W)
      (hpq : p ≠ q) (hs : s ∈ S) (hr : r ∈ S) (hsr : s ≠ r)
      (hps : G.Adj p s) (hqr : G.Adj q r) (hws : G.Adj w s) (hwr : G.Adj w r) :
      G.Adj p q := by
    by_contra hnadj
    let R := (U.erase s).erase r
    have hRU {x : V} (hx : x ∈ R) : x ∈ U :=
      mem_of_mem_erase (mem_of_mem_erase hx)
    have hmR {x : V} (hx : x ∈ R) : x ≠ s ∧ x ≠ r :=
      ⟨(mem_erase.mp (mem_of_mem_erase hx)).1, (mem_erase.mp hx).1⟩
    have hRcard : R.card = 3 := by
      dsimp only [R]
      rw [card_erase_of_mem (mem_erase.mpr ⟨hsr.symm, hSsub hr⟩),
        card_erase_of_mem (hSsub hs), hU]
    have hi_R : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y :=
      fun _ hx _ hy ↦ hUind (hRU hx) (hRU hy)
    have hpR {x : V} (hx : x ∈ R) : ¬ G.Adj p x := fun hadj ↦
      (hmR hx).1 (hPunique hp (hRU hx) (hSsub hs) hadj hps)
    have hqR {x : V} (hx : x ∈ R) : ¬ G.Adj q x := fun hadj ↦
      (hmR hx).2 (hPunique hq (hRU hx) (hSsub hr) hadj hqr)
    have hwsr : ({s, r} : Finset V) = G.neighborFinset w ∩ U := by
      apply Finset.eq_of_subset_of_card_le
      · exact insert_subset (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hws, hSsub hs⟩)
          (singleton_subset_iff.mpr (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hwr, hSsub hr⟩))
      · rw [card_pair hsr, hQdeg (hWQ hw)]
    have hwR {x : V} (hx : x ∈ R) : ¬ G.Adj w x := by
      intro hadj
      have hmem : x ∈ G.neighborFinset w ∩ U := mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hRU hx⟩
      rw [← hwsr] at hmem
      exact (mem_insert.mp hmem).elim (hmR hx).1 (fun h ↦ (hmR hx).2 (mem_singleton.mp h))
    have hpw : ¬ G.Adj p w := neighborhood_independent G htriangle s
      ((G.mem_neighborFinset _ _).mpr hps.symm) ((G.mem_neighborFinset _ _).mpr hws.symm)
    have hqw : ¬ G.Adj q w := neighborhood_independent G htriangle r
      ((G.mem_neighborFinset _ _).mpr hqr.symm) ((G.mem_neighborFinset _ _).mpr hwr.symm)
    have hiw := independent_insert G hi_R (fun _ ↦ hwR)
    have hiq := independent_insert G hiw (by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hqw
      · exact hqR hx)
    have hip := independent_insert G hiq (by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hnadj
      · rcases mem_insert.mp hx with rfl | hx
        · exact hpw
        · exact hpR hx)
    have hpU : p ∉ U := (mem_sdiff.mp (hPsub hp)).2
    have hqU : q ∉ U := (mem_sdiff.mp (hPsub hq)).2
    have hwU : w ∉ U := (mem_sdiff.mp (hQsub (hWQ hw))).2
    have hpw_ne : p ≠ w := fun h ↦ Finset.disjoint_left.mp hPW_disj hp (h.symm ▸ hw)
    have hqw_ne : q ≠ w := fun h ↦ Finset.disjoint_left.mp hPW_disj hq (h.symm ▸ hw)
    have hw_not : w ∉ R := fun h ↦ hwU (hRU h)
    have hq_not : q ∉ insert w R := by
      rw [mem_insert, not_or]
      exact ⟨hqw_ne, fun h ↦ hqU (hRU h)⟩
    have hp_not : p ∉ insert q (insert w R) := by
      simp only [mem_insert, not_or]
      exact ⟨hpq, hpw_ne, fun h ↦ hpU (hRU h)⟩
    have hsmall := independent_card_le G hindep hip
    rw [card_insert_of_notMem hp_not, card_insert_of_notMem hq_not,
      card_insert_of_notMem hw_not, hRcard] at hsmall
    omega
  have hWother {w s : V} (hw : w ∈ W) (hs : s ∈ S) (hws : G.Adj w s) :
      ∃ r ∈ S, r ≠ s ∧ G.Adj w r := by
    have hmem : s ∈ G.neighborFinset w ∩ S := mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hws, hs⟩
    have hcard : ((G.neighborFinset w ∩ S).erase s).card = 1 := by
      rw [card_erase_of_mem hmem, hWSdeg hw]
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (by rw [hcard]; decide)
    obtain ⟨hrs, hm⟩ := mem_erase.mp hr
    exact ⟨r, (mem_inter.mp hm).2, hrs, (G.mem_neighborFinset _ _).mp (mem_inter.mp hm).1⟩
  have hSchoose {s : V} (hs : s ∈ S) : ∃ p ∈ P, G.Adj p s := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset s ∩ P).card by rw [hSPdeg hs]; decide)
    exact ⟨p, (mem_inter.mp hp).2, ((G.mem_neighborFinset _ _).mp (mem_inter.mp hp).1).symm⟩
  have hPdeg_lower {p : V} (hp : p ∈ P) : 2 ≤ (G.neighborFinset p ∩ P).card := by
    obtain ⟨s, hps⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset p ∩ S).card by rw [hPSdeg hp]; decide)
    obtain ⟨hps, hs⟩ := mem_inter.mp hps
    have hpsA := (G.mem_neighborFinset _ _).mp hps
    obtain ⟨w₁, w₂, hne, heq⟩ := Finset.card_eq_two.mp (hSWdeg hs)
    obtain ⟨hsw₁, hw₁⟩ := mem_inter.mp (show w₁ ∈ G.neighborFinset s ∩ W by simp [heq])
    obtain ⟨hsw₂, hw₂⟩ := mem_inter.mp (show w₂ ∈ G.neighborFinset s ∩ W by simp [heq])
    have hw₁s := ((G.mem_neighborFinset _ _).mp hsw₁).symm
    have hw₂s := ((G.mem_neighborFinset _ _).mp hsw₂).symm
    obtain ⟨r₁, hr₁, hr₁s, hw₁r⟩ := hWother hw₁ hs hw₁s
    obtain ⟨r₂, hr₂, hr₂s, hw₂r⟩ := hWother hw₂ hs hw₂s
    have hrne : r₁ ≠ r₂ := by
      intro heq
      subst r₂
      exact hne (common_neighbor_unique_pair G (fun x y hne hadj ↦ (hcommon x y hne hadj).2)
        hr₁s.symm (hUind (hSsub hs) (hSsub hr₁)) (G.adj_symm ((G.mem_neighborFinset _ _).mp (hSsub hs)))
        (G.adj_symm ((G.mem_neighborFinset _ _).mp (hSsub hr₁)))
        (hHmem.mp (hQsub (hWQ hw₁))).1 (hHmem.mp (hQsub (hWQ hw₂))).1
        hw₁s.symm hw₁r.symm hw₂s.symm hw₂r.symm)
    obtain ⟨p₁, hp₁, hp₁r⟩ := hSchoose hr₁
    obtain ⟨p₂, hp₂, hp₂r⟩ := hSchoose hr₂
    have hp₁_ne : p ≠ p₁ := by
      intro heq
      subst p₁
      exact hr₁s (hPunique hp (hSsub hr₁) (hSsub hs) hp₁r hpsA)
    have hp₂_ne : p ≠ p₂ := by
      intro heq
      subst p₂
      exact hr₂s (hPunique hp (hSsub hr₂) (hSsub hs) hp₂r hpsA)
    have hpp_ne : p₁ ≠ p₂ := by
      intro heq
      subst p₂
      exact hrne (hPunique hp₁ (hSsub hr₁) (hSsub hr₂) hp₁r hp₂r)
    have h₁ := hforce hp hp₁ hw₁ hp₁_ne hs hr₁ hr₁s.symm hpsA hp₁r hw₁s hw₁r
    have h₂ := hforce hp hp₂ hw₂ hp₂_ne hs hr₂ hr₂s.symm hpsA hp₂r hw₂s hw₂r
    have hsub : ({p₁, p₂} : Finset V) ⊆ G.neighborFinset p ∩ P :=
      insert_subset (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h₁, hp₁⟩)
        (singleton_subset_iff.mpr (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h₂, hp₂⟩))
    simpa only [card_pair hpp_ne] using Finset.card_le_card hsub
  have hPreg {p : V} (hp : p ∈ P) : (G.neighborFinset p ∩ P).card = 2 := by
    have hlo := hPdeg_lower hp
    by_contra! hne
    have hbig : 3 ≤ (G.neighborFinset p ∩ P).card := by omega
    have hsub : G.neighborFinset p ∩ P ⊆ P.erase p := by
      intro q hq
      obtain ⟨hpq, hqP⟩ := mem_inter.mp hq
      exact mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset _ _).mp hpq)).symm, hqP⟩
    have hfull : G.neighborFinset p ∩ P = P.erase p :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [card_erase_of_mem hp, hPcard] using hbig)
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset p ∩ P).card)
    have hqP := (mem_inter.mp hq).2
    have hlow := hPdeg_lower hqP
    have hqsub : G.neighborFinset q ∩ P ⊆ {p} := by
      intro r hr
      apply mem_singleton.mpr
      by_contra hrp
      have hrp' : r ∈ G.neighborFinset p ∩ P := by
        rw [hfull]
        exact mem_erase.mpr ⟨hrp, (mem_inter.mp hr).2⟩
      exact neighborhood_independent G htriangle p (mem_inter.mp hq).1 (mem_inter.mp hrp').1
        ((G.mem_neighborFinset _ _).mp (mem_inter.mp hr).1)
    have hsmall := Finset.card_le_card hqsub
    rw [card_singleton] at hsmall
    omega
  exact ⟨{ t := t, P := P, S := S, T := T, W := W, t_adj := htAdj, P_eq := rfl, S_eq := hS_eq
           T_eq := rfl, P_card := hPcard, S_card := hScard, T_card := hTcard, W_card := hWcard
           P_outside := hPsub, T_outside := hTH, W_outside := hWQ.trans hQsub
           P_disj_T := hTP_disj.symm, P_disj_W := hPW_disj, T_disj_W := hTW_disj, cover := hcover
           P_one_S := fun _ ↦ hPSdeg, S_one_P := fun _ ↦ hSPdeg
           T_one_S := fun _ ↦ hSTdeg, S_one_T := fun _ ↦ hTSdeg
           W_two_S := fun _ ↦ hWSdeg, P_reg := fun _ ↦ hPreg, P_has_T := fun _ ↦ hPTnonempty }⟩

end OMA.ER36

private theorem ramsey36_use_configuration (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hdeg : ∀ x, G.degree x = 5)
    (hcommon : ∀ x y, x ≠ y → ¬ G.Adj x y →
      1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card ∧
      (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2)
    (v : Fin 18) (F : OMA.ER36.LocalConfiguration G v)
    (F' : OMA.ER36.LocalConfiguration G F.t) : False := by
  have hupper (x y) (hne : x ≠ y) (hn : ¬ G.Adj x y) := (hcommon x y hne hn).2
  have hexternal {p q x} (hp : p ∈ F.P) (hq : q ∈ F.P) (hx : x ∉ F.P)
      (hpx : G.Adj p x) (hqx : G.Adj q x) : p = q :=
    ramsey36_no_external_common ht hupper F.P F.P_card F.P_reg hp hq hx hpx hqx
  have outside {x} (hx : x ∈ Finset.univ.erase v \ G.neighborFinset v) :
      x ≠ v ∧ ¬ G.Adj v x := by
    obtain ⟨hm, hn⟩ := mem_sdiff.mp hx
    exact ⟨(mem_erase.mp hm).1, fun h ↦ hn ((G.mem_neighborFinset _ _).mpr h)⟩
  have not_t {x} (hv : ¬ G.Adj v x) : x ≠ F.t := fun h ↦ hv (h ▸ F.t_adj)
  have nt_adj {x} (hv : x ≠ v) (hx : x ∉ F.T) : ¬ G.Adj F.t x := by
    intro h
    apply hx
    rw [F.T_eq]
    exact mem_erase.mpr ⟨hv, (G.mem_neighborFinset _ _).mpr h⟩
  have s_not_outside {x} (hs : x ∈ F.S) :
      x ∉ Finset.univ.erase v \ G.neighborFinset v := by
    rw [F.S_eq] at hs
    exact fun h ↦ (mem_sdiff.mp h).2 (mem_of_mem_erase hs)
  have s_disj_p : Disjoint F.S F.P :=
    disjoint_left.mpr fun _ hS hP ↦ s_not_outside hS (F.P_outside hP)
  have s_disj_t : Disjoint F.S F.T :=
    disjoint_left.mpr fun _ hS hT ↦ s_not_outside hS (F.T_outside hT)
  obtain ⟨eS, heS⟩ := ramsey36_matching (G := G) (F.P_card.trans F.S_card.symm)
    (fun p hp ↦ by
      obtain ⟨x,hx⟩ := (Finset.card_pos.mp (by rw [F.P_one_S p hp]; decide))
      exact ⟨x, (mem_inter.mp hx).2, (G.mem_neighborFinset _ _).mp (mem_inter.mp hx).1⟩)
    (fun hp hq hx hpx hqx ↦ (Finset.card_le_one_iff.mp (by rw [F.S_one_P _ hx]))
      (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hpx.symm, hp⟩)
      (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hqx.symm, hq⟩))
  obtain ⟨eT, heT⟩ := ramsey36_matching (G := G) (F.P_card.trans F.T_card.symm)
    (fun p hp ↦ by
      obtain ⟨x,hx⟩ := F.P_has_T p hp
      exact ⟨x, (mem_inter.mp hx).2, (G.mem_neighborFinset _ _).mp (mem_inter.mp hx).1⟩)
    (fun hp hq hx hpx hqx ↦ hexternal hp hq
      (fun h ↦ Finset.disjoint_left.mp F.P_disj_T h hx) hpx hqx)
  have hPT (p : ↥F.P) : (G.neighborFinset p.val ∩ F.T).card = 1 := by
    have heq : G.neighborFinset p.val ∩ F.T = {(eT p).val} := by
      ext x
      constructor
      · intro hx
        obtain ⟨ha, hm⟩ := mem_inter.mp hx
        exact mem_singleton.mpr (congrArg Subtype.val ((heT p ⟨x, hm⟩).mp
          ((G.mem_neighborFinset _ _).mp ha))).symm
      · intro hx
        obtain rfl := mem_singleton.mp hx
        exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ((heT p (eT p)).mpr rfl), (eT p).property⟩
    rw [heq, card_singleton]
  have hpW (p : Fin 18) (hp : p ∈ F.P) : ∃ w ∈ F.W, G.Adj p w := by
    exact OMA.RamseyThreeSix.has_neighbor_in_fourth_part G F.cover
      (fun h ↦ (outside (F.P_outside hp)).2 h.symm)
      (fun h ↦ nt_adj (outside (F.P_outside hp)).1
        (Finset.disjoint_left.mp F.P_disj_T hp) h.symm)
      (hdeg p) (F.P_one_S _ hp) (F.P_reg _ hp) (hPT ⟨p, hp⟩)
  obtain ⟨eW, heW⟩ := ramsey36_matching (G := G) (F.P_card.trans F.W_card.symm) hpW
    (fun hp hq hx hpx hqx ↦ hexternal hp hq
      (fun h ↦ Finset.disjoint_left.mp F.P_disj_W h hx) hpx hqx)
  have hT_eq {x} (hx : ¬ G.Adj v x) :
      G.neighborFinset F.t ∩ G.neighborFinset x = G.neighborFinset x ∩ F.T := by
    ext y
    rw [F.T_eq]
    simp only [mem_inter, mem_erase, G.mem_neighborFinset]
    constructor
    · rintro ⟨ht, hx'⟩
      exact ⟨hx', fun he ↦ hx (he ▸ hx'.symm), ht⟩
    · rintro ⟨hx', _, ht⟩
      exact ⟨ht, hx'⟩
  have hP'_eq : F.P = F'.P := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have ⟨hnv, hnvAdj⟩ := outside (F.P_outside hx)
      have hntAdj : ¬ G.Adj F.t x := nt_adj hnv (Finset.disjoint_left.mp F.P_disj_T hx)
      rw [F'.P_eq]
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨not_t hnvAdj, mem_univ _⟩,
          fun h ↦ hntAdj ((G.mem_neighborFinset _ _).mp h)⟩,
        by rw [hT_eq hnvAdj]; exact hPT ⟨x, hx⟩⟩
    · rw [F.P_card, F'.P_card]
  have hWT (w : Fin 18) (hw : w ∈ F.W) : (G.neighborFinset w ∩ F.T).card = 2 := by
    have ⟨hnv, hnvAdj⟩ := outside (F.W_outside hw)
    have hntAdj : ¬ G.Adj F.t w := nt_adj hnv
      (fun h ↦ Finset.disjoint_left.mp F.T_disj_W h hw)
    have hne : w ≠ F.t := not_t hnvAdj
    have hb := hcommon F.t w hne.symm hntAdj
    rw [hT_eq hnvAdj] at hb
    have hone : (G.neighborFinset w ∩ F.T).card ≠ 1 := by
      intro h1
      have hP' : w ∈ F'.P := by
        rw [F'.P_eq]
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨hne, mem_univ _⟩,
          fun h ↦ hntAdj ((G.mem_neighborFinset _ _).mp h)⟩, by rw [hT_eq hnvAdj, h1]⟩
      exact Finset.disjoint_left.mp F.P_disj_W (hP'_eq.symm ▸ hP') hw
    omega
  have hmatched {Q : Finset (Fin 18)} (e : ↥F.P ≃ ↥Q)
      (he : ∀ p : ↥F.P, ∀ q : ↥Q, G.Adj p.1 q.1 ↔ e p = q) (i j : ↥F.P) :
      G.Adj i.1 (e j).1 ↔ i = j := (he i (e j)).trans e.injective.eq_iff
  refine ramsey36_last_contradiction ht hupper Subtype.val
    (fun i ↦ (eS i).val) (fun i ↦ (eT i).val) (fun i ↦ (eW i).val)
    (by simpa using F.P_card) (hmatched eS heS) (hmatched eT heT) (hmatched eW heW)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j he
    exact Finset.disjoint_left.mp s_disj_p (he ▸ (eS j).property) i.property
  · intro i j he
    exact Finset.disjoint_left.mp F.P_disj_T i.property (he ▸ (eT j).property)
  · intro i j he
    exact Finset.disjoint_left.mp F.P_disj_W i.property (he ▸ (eW j).property)
  · intro i j he
    exact Finset.disjoint_left.mp s_disj_t (eS i).property (he ▸ (eT j).property)
  · intro i j he
    exact Finset.disjoint_left.mp F.T_disj_W (eT i).property (he ▸ (eW j).property)
  · intro i
    exact (OMA.RamseyThreeSix.card_neighborFinset_inter_equiv G i.val
      (Equiv.refl ↥F.P)).symm.trans (F.P_reg _ i.property)
  · intro i
    rw [← OMA.RamseyThreeSix.card_neighborFinset_inter_equiv G (eW i).val eS]
    exact F.W_two_S _ (eW i).property
  · intro i
    rw [← OMA.RamseyThreeSix.card_neighborFinset_inter_equiv G (eW i).val eT]
    exact hWT _ (eW i).property
  · intro i
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [F.S_one_T _ (eS i).property]; decide)
    obtain ⟨ha, hm⟩ := mem_inter.mp hx
    refine ⟨eT.symm ⟨x, hm⟩, ?_⟩
    rw [eT.apply_symm_apply]
    exact (G.mem_neighborFinset _ _).mp ha

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_seven_R1.H1 := by
  intro G hbad
  classical
  obtain ⟨ht, hi⟩ := hbad
  have hdeg := OMA.ramsey36_degree_eq_five G ht hi
  have hcommon (x y : Fin 18) (hne : x ≠ y) (hn : ¬ G.Adj x y) :=
    OMA.ramsey36_common_bounds G ht hi hne hn
  let v : Fin 18 := 0
  obtain ⟨F⟩ := OMA.ER36.local_configuration G ht hi hdeg hcommon v
  obtain ⟨F'⟩ := OMA.ER36.local_configuration G ht hi hdeg hcommon F.t
  exact ramsey36_use_configuration G ht hdeg hcommon v F F'
