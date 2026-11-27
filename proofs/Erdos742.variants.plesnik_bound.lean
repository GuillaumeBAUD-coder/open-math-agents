import FormalConjectures.ErdosProblems.«742»

/-! # An edge bound from missing pairs in a diameter-two-critical graph -/
-- Credit: @steveDOTdigital
namespace OMA.DiameterTwoBound
open SimpleGraph Finset
open scoped Classical

private def Pays {V : Type*} (G : SimpleGraph V) (x y z : V) : Prop :=
  ¬ G.Adj x z ∧ G.Adj y z ∧ ∀ t, G.Adj x t → G.Adj z t → t = y

private lemma eq_ediam {V : Type*} (G : SimpleGraph V) : G.diam = 2 ↔ G.ediam = 2 := by
  rw [SimpleGraph.diam,ENat.toNat_eq_iff (by decide : (2:ℕ) ≠ 0)]
  rfl

private lemma witness {V : Type*} (G : SimpleGraph V) (crit : Erdos742.IsDiameter2Critical G)
    {v x y : V} (vx : G.Adj v x) (vy : G.Adj v y) (xy : G.Adj x y) :
    (∃ z, Pays G x y z) ∨ (∃ z, Pays G y x z) := by
  classical
  let D := G.deleteEdges {s(x,y)}
  have less := SimpleGraph.ediam_anti (G.deleteEdges_le {s(x,y)})
  have base := (eq_ediam G).mp crit.1
  change G.ediam ≤ D.ediam at less
  rw [base] at less
  have large : ¬ D.ediam ≤ 2 := by
    intro h
    exact crit.2 _ xy ((eq_ediam D).mpr (le_antisymm h less))
  rw [SimpleGraph.ediam_le_iff] at large
  push Not at large
  obtain ⟨a,b,far⟩ := large
  obtain ⟨ne,non,empty⟩ := D.two_lt_edist_iff.mp far
  have good (p q : V) : D.Adj p q ↔ G.Adj p q ∧ ¬((p=x ∧ q=y) ∨ (p=y ∧ q=x)) := by
    change (G.deleteEdges {s(x,y)}).Adj p q ↔ _
    simp only [SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
  have bad (t : V) (ha : D.Adj a t) (hb : D.Adj b t) : False := by
    have h := D.mem_commonNeighbors.mpr ⟨ha,hb⟩
    rw [empty] at h
    exact h
  have ax := vx.symm
  have ay := vy.symm
  have vn1 := vx.ne
  have vn2 := vy.ne
  have d1 : D.Adj x v := (good x v).mpr ⟨ax,by grind⟩
  have d2 : D.Adj y v := (good y v).mpr ⟨ay,by grind⟩
  have uncut (p q : V) (h : G.Adj p q) (no : ¬D.Adj p q) :
      (p=x ∧ q=y) ∨ (p=y ∧ q=x) := by
    by_contra miss
    exact no ((good _ _).mpr ⟨h,miss⟩)
  have ab : ¬G.Adj a b := by
    intro e
    rcases uncut a b e non with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact bad v d1 d2
    · exact bad v d2 d1
  have common : (G.commonNeighbors a b).Nonempty := by
    by_contra! e
    have gt := G.two_lt_edist_iff.mpr ⟨ne,ab,e⟩
    have le : G.edist a b ≤ 2 := G.edist_le_ediam.trans_eq base
    exact (not_lt_of_ge le) gt
  obtain ⟨t,ht⟩ := common
  obtain ⟨at',bt'⟩ := G.mem_commonNeighbors.mp ht
  have broken (q : V) (qa : G.Adj a q) (qb : G.Adj b q) :
      ((a=x ∧ q=y) ∨ (a=y ∧ q=x)) ∨ ((b=x ∧ q=y) ∨ (b=y ∧ q=x)) := by
    by_cases left : (a=x ∧ q=y) ∨ (a=y ∧ q=x)
    · exact Or.inl left
    · right
      by_contra right
      exact bad q ((good _ _).mpr ⟨qa,left⟩) ((good _ _).mpr ⟨qb,right⟩)
  have xy' := xy.symm
  have na : ¬G.Adj b a := fun h => ab h.symm
  rcases broken t at' bt' with (⟨a1,t1⟩ | ⟨a1,t1⟩) | (⟨b1,t1⟩ | ⟨b1,t1⟩)
  · subst a; subst t
    exact Or.inl ⟨b,ab,bt'.symm,fun w hx hb => by have := broken w hx hb; grind⟩
  · subst a; subst t
    exact Or.inr ⟨b,ab,bt'.symm,fun w hy hb => by have := broken w hy hb; grind⟩
  · subst b; subst t
    exact Or.inl ⟨a,na,at'.symm,fun w hx ha => by have := broken w ha hx; grind⟩
  · subst b; subst t
    exact Or.inr ⟨a,na,at'.symm,fun w hy ha => by have := broken w ha hy; grind⟩

-- A nonedge with a unique common neighbor recovers an edge of the triangle.
private noncomputable def decode {V : Type*} (G : SimpleGraph V) (p : V × V) : Sym2 V := by
  classical
  exact if G.Adj p.1 p.2 then s(p.1,p.2)
    else if h : ∃ y, G.Adj p.1 y ∧ G.Adj p.2 y then s(p.1,h.choose)
    else s(p.1,p.2)

private lemma paid {V : Type*} (G : SimpleGraph V) {v x y z : V}
    (vx : G.Adj v x) (vy : G.Adj v y) (xy : G.Adj x y) (p : Pays G x y z) :
    z ≠ v ∧ ¬G.Adj v z ∧ decode G (x,z) = s(x,y) := by
  classical
  have dist : z ≠ v := fun e => p.1 (e ▸ vx.symm)
  have outside : ¬G.Adj v z := fun vz => vy.ne (p.2.2 v vx.symm vz.symm)
  have ex : ∃ t, G.Adj x t ∧ G.Adj z t := ⟨y,xy,p.2.1.symm⟩
  have eq := p.2.2 ex.choose ex.choose_spec.1 ex.choose_spec.2
  refine ⟨dist,outside,?_⟩
  simp [decode,p.1,ex,eq]

private lemma edge_cover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (crit : Erdos742.IsDiameter2Critical G) (v : V) :
    G.edgeFinset.card ≤ G.degree v +
      (Fintype.card V - 1) * (Fintype.card V - 1 - G.degree v) := by
  classical
  let A := G.neighborFinset v
  let B := (Finset.univ : Finset V).erase v
  let C := B \ A
  let incident := A.image (fun x => s(v,x))
  let other := (B ×ˢ C).image (decode G)
  have memB {x : V} (h : x ≠ v) : x ∈ B := by simp [B,h]
  have memC {x : V} (h : x ≠ v) (hx : ¬G.Adj v x) : x ∈ C :=
    Finset.mem_sdiff.mpr ⟨memB h,fun a => hx ((G.mem_neighborFinset v x).mp a)⟩
  have ordinary {x y : V} (h : x ≠ v) (hy : y ∈ C) (xy : G.Adj x y) : s(x,y) ∈ other := by
    apply Finset.mem_image.mpr
    exact ⟨(x,y),Finset.mem_product.mpr ⟨memB h,hy⟩,by simp [decode,xy]⟩
  have internal {x y : V} (vx : G.Adj v x) (vy : G.Adj v y) (xy : G.Adj x y)
      (p : ∃ z, Pays G x y z) : s(x,y) ∈ other := by
    obtain ⟨z,hz⟩ := p
    obtain ⟨ne,h,e⟩ := paid G vx vy xy hz
    exact Finset.mem_image.mpr ⟨(x,z),Finset.mem_product.mpr ⟨memB vx.ne.symm,memC ne h⟩,e⟩
  have cover : G.edgeFinset ⊆ incident ∪ other := by
    intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      intro he
      have xy : G.Adj x y := G.mem_edgeFinset.mp he
      apply Finset.mem_union.mpr
      by_cases xx : x = v
      · subst x
        exact Or.inl (Finset.mem_image.mpr ⟨y,(G.mem_neighborFinset v y).mpr xy,rfl⟩)
      by_cases yy : y = v
      · subst y
        exact Or.inl (Finset.mem_image.mpr ⟨x,(G.mem_neighborFinset v x).mpr xy.symm,Sym2.eq_swap⟩)
      apply Or.inr
      by_cases hy : G.Adj v y
      · by_cases hx : G.Adj v x
        · rcases witness G crit hx hy xy with p|p
          · exact internal hx hy xy p
          · rw [Sym2.eq_swap (a := x) (b := y)]
            exact internal hy hx xy.symm p
        · rw [Sym2.eq_swap (a := x) (b := y)]
          exact ordinary yy (memC xx hx) xy.symm
      · exact ordinary xx (memC yy hy) xy
  have sub : A ⊆ B := by
    intro x hx
    exact memB ((G.mem_neighborFinset v x).mp hx).ne.symm
  have cb : B.card = Fintype.card V - 1 := by simp [B]
  have ca : A.card = G.degree v := rfl
  have cc : C.card = Fintype.card V - 1 - G.degree v := by
    rw [show C = B \ A from rfl, Finset.card_sdiff_of_subset sub,cb,ca]
  calc
    _ ≤ (incident ∪ other).card := Finset.card_le_card cover
    _ ≤ incident.card + other.card := Finset.card_union_le ..
    _ ≤ A.card + (B ×ˢ C).card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by rw [Finset.card_product,ca,cb,cc]

private lemma arithmetic (m d c : ℕ) (size : 3 ≤ d+c+1)
    (degrees : 2*m ≤ (d+c+1)*d) (cover : m ≤ d+(d+c)*c) :
    8*m < 3*(d+c+1)*(d+c) := by
  by_contra! contra
  have dc : 3*c ≤ d := by
    by_contra! small
    have gap : 4*d < 3*(d+c) := by omega
    have h := Nat.mul_lt_mul_of_pos_left gap (show 0 < d+c+1 by omega)
    nlinarith only [degrees,contra,h]
  obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le dc
  by_cases zero : c = 0
  · subst c
    simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] at *
    have hh : 2 ≤ h := by omega
    have sq := Nat.mul_le_mul_left h hh
    nlinarith only [cover,contra,sq,hh]
  · have cp : 1 ≤ c := by omega
    have cs := Nat.mul_le_mul_left c cp
    have ch := Nat.mul_le_mul_left h cp
    nlinarith only [cover,contra,cs,ch,cp, Nat.zero_le (h*h)]

end OMA.DiameterTwoBound

open SimpleGraph Finset OMA.DiameterTwoBound in
theorem OMA.solution : type_of% @Erdos742.variants.plesnik_bound := by
  intro V _ _ G _ crit
  classical
  have : Nontrivial V := G.nontrivial_of_diam_ne_zero (by rw [crit.1]; decide)
  have diam := (eq_ediam G).mp crit.1
  obtain ⟨x,y,dist⟩ := G.exists_edist_eq_ediam_of_finite
  obtain ⟨ne,_,z,hz⟩ := G.edist_eq_two_iff.mp (dist.trans diam)
  obtain ⟨xz,yz⟩ := G.mem_commonNeighbors.mp hz
  have n3 : 3 ≤ Fintype.card V := by
    simpa [ne,xz.ne,yz.ne] using (({x,y,z} : Finset V).card_le_univ)
  obtain ⟨v,_,maximum⟩ := Finset.exists_max_image Finset.univ (fun w : V => G.degree w) Finset.univ_nonempty
  have hand : 2 * G.edgeFinset.card ≤ Fintype.card V * G.degree v := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc
      _ ≤ ∑ _ : V, G.degree v := Finset.sum_le_sum maximum
      _ = _ := by simp
  have cap := edge_cover G crit v
  let c := Fintype.card V - 1 - G.degree v
  have vd : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  have eq : G.degree v + c + 1 = Fintype.card V := by dsimp [c]; omega
  have eq' : G.degree v + c = Fintype.card V - 1 := by omega
  have q := arithmetic G.edgeFinset.card (G.degree v) c (by rwa [eq]) (by rwa [eq]) (by rwa [eq'])
  rw [eq,eq'] at q
  have pos : 1 ≤ Fintype.card V := by omega
  have qr : (8:ℝ) * G.edgeFinset.card < 3*(Fintype.card V : ℝ)*((Fintype.card V:ℝ)-1) := by
    rw [show (Fintype.card V : ℝ) - 1 = ((Fintype.card V - 1 : ℕ) : ℝ) by rw [Nat.cast_sub pos, Nat.cast_one]]
    exact_mod_cast q
  linarith
