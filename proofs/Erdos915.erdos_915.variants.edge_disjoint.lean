import FormalConjectures.ErdosProblems.«915»
import Mathlib

/-! Unit-capacity flows and cuts in finite simple graphs. -/

open Finset SimpleGraph
open scoped Classical BigOperators

namespace OMA915

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private def row (f : V → V → ℤ) (x : V) := ∑ y, f x y

private def terminal (s t x : V) : ℤ := (if x=s then 1 else 0)-(if x=t then 1 else 0)

private def skew (f : V → V → ℤ) : Prop := ∀ x y, f x y = -f y x

private def unitFlow (G : SimpleGraph V) (s t : V) (v : ℕ) (f : V → V → ℤ) : Prop :=
  skew f ∧
  (∀ x y, -1 ≤ f x y ∧ f x y ≤ 1) ∧
  (∀ x y, ¬G.Adj x y → f x y = 0) ∧
  ∀ x, row f x = (v:ℤ)*terminal s t x

private def firstStep (u v x y : V) : ℤ :=
  (if x=u ∧ y=v then 1 else 0)-(if x=v ∧ y=u then 1 else 0)

private def along : {u v : V} → G.Walk u v → V → V → ℤ
  | _, _, .nil => fun _ _ => 0
  | u, _, .cons (v := v) _ p => fun x y => firstStep u v x y + along p x y

private def allowed (R : V → V → Prop) {u v : V} (p : G.Walk u v) : Prop :=
  ∀ d ∈ p.darts, R d.fst d.snd

omit [Fintype V] in
private lemma along_skew {s t : V} (p : G.Walk s t) : skew (along p) := by
  intro x y
  induction p with
  | nil => simp [along]
  | @cons u v w h p ih =>
    unfold along firstStep
    rw [ih]
    simp only [and_comm (a := y=u),and_comm (a := y=v)]
    ring

private lemma row_firstStep (u v x : V) : row (firstStep u v) x = terminal u v x := by
  unfold firstStep terminal row
  rw [sum_sub_distrib]
  have he (a b : V) : (∑ y : V, if x=a ∧ y=b then (1:ℤ) else 0) = (if x=a then 1 else 0) := by
    by_cases h : x=a
    · simp only [h,true_and,if_true]
      simp
    · simp [h]
  rw [he,he]

private lemma along_row {s t : V} (p : G.Walk s t) (x : V) :
    row (along p) x = terminal s t x := by
  induction p with
  | nil => simp [along,row,terminal]
  | @cons u v w h p ih =>
    change (∑ y, (firstStep u v x y + along p x y)) = _
    rw [sum_add_distrib]
    change row (firstStep u v) x + row (along p) x = _
    rw [row_firstStep,ih]
    unfold terminal
    ring

omit [Fintype V] in
private lemma along_zero {s t : V} (p : G.Walk s t) {x y : V}
    (he : s(x,y) ∉ p.edges) : along p x y = 0 := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    rw [Walk.edges_cons,List.mem_cons,not_or] at he
    have hne : ¬(x=u ∧ y=v) ∧ ¬(x=v ∧ y=u) := by simpa [Sym2.eq_iff,not_or] using he.1
    change firstStep u v x y + along p x y = _
    simp [firstStep,hne.1,hne.2,ih he.2]

omit [Fintype V] in
private lemma along_edge {s t : V} (p : G.Walk s t) (hp : p.IsTrail)
    (R : V → V → Prop) (hR : allowed R p) {x y : V} (hxy : s(x,y) ∈ p.edges) :
    (along p x y = 1 ∧ R x y) ∨ (along p x y = -1 ∧ R y x) := by
  induction p with
  | nil => simp at hxy
  | @cons u v w h p ih =>
    have htrail := (Walk.isTrail_cons h p).1 hp
    have hr : R u v := hR ⟨(u,v),h⟩ (by simp)
    have hpR : allowed R p := fun d hd => hR d (by simp [hd])
    rw [Walk.edges_cons,List.mem_cons] at hxy
    obtain hxy|hxy := hxy
    · have hz : along p x y = 0 := along_zero p (hxy ▸ htrail.2)
      rw [Sym2.eq_iff] at hxy
      obtain ⟨rfl,rfl⟩|⟨rfl,rfl⟩ := hxy
      · left
        exact ⟨by simp [along,firstStep,h.ne,h.ne.symm,hz],hr⟩
      · right
        exact ⟨by simp [along,firstStep,h.ne,h.ne.symm,hz],hr⟩
    · have hne : ¬(x=u ∧ y=v) ∧ ¬(x=v ∧ y=u) := by
        simpa [Sym2.eq_iff,not_or] using (show s(x,y) ≠ s(u,v) from fun he => htrail.2 (he ▸ hxy))
      simpa [along,firstStep,hne.1,hne.2] using ih htrail.1 hpR hxy

private def reached (G : SimpleGraph V) (R : V → V → Prop) (s : V) : Finset V :=
  univ.filter fun x => ∃ p : G.Walk s x, allowed R p

omit [DecidableEq V] in
private lemma reached_self (G : SimpleGraph V) (R : V → V → Prop) (s : V) :
    s ∈ reached G R s := mem_filter.2 ⟨mem_univ _,.nil,by simp [allowed]⟩

omit [DecidableEq V] in
private lemma reached_closed (G : SimpleGraph V) (R : V → V → Prop) (s : V)
    {x y : V} (hx : x ∈ reached G R s) (hxy : G.Adj x y) (hR : R x y) :
    y ∈ reached G R s := by
  obtain ⟨p,hp⟩ := (mem_filter.1 hx).2
  refine mem_filter.2 ⟨mem_univ _,p.concat hxy,fun d hd => ?_⟩
  rw [Walk.darts_concat] at hd
  rw [List.concat_eq_append,List.mem_append,List.mem_singleton] at hd
  obtain hd|rfl := hd
  · exact hp d hd
  · exact hR

private lemma reached_path {R : V → V → Prop} {s t : V} (ht : t ∈ reached G R s) :
    ∃ p : G.Walk s t, p.IsPath ∧ allowed R p := by
  obtain ⟨p,hp⟩ := (mem_filter.1 ht).2
  exact ⟨p.bypass,p.bypass_isPath,fun d hd => hp d (p.darts_bypass_subset_darts hd)⟩

private lemma row_across (f : V → V → ℤ) (hf : skew f) (S : Finset V) :
    (∑ x ∈ S, row f x) = ∑ x ∈ S, ∑ y ∈ univ \ S, f x y := by
  have hz : (∑ x ∈ S, ∑ y ∈ S, f x y) = 0 := by
    have he : (∑ x ∈ S, ∑ y ∈ S, f x y) = -(∑ x ∈ S, ∑ y ∈ S, f x y) := by
      conv_lhs => rw [sum_comm]
      conv_lhs =>
        enter [2,x,2,y]
        rw [hf y x]
      simp
    omega
  unfold row
  simp_rw [← sum_sdiff (subset_univ S)]
  rw [sum_add_distrib,hz,add_zero]

private def cut (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ∑ x ∈ S, ∑ y ∈ univ \ S, if G.Adj x y then 1 else 0

private lemma row_terminals {f : V → V → ℤ} {s t : V} {v : ℕ}
    (hf : unitFlow G s t v f) {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    (∑ x ∈ S, ∑ y ∈ univ \ S, f x y) = v := by
  rw [← row_across f hf.1 S]
  simp_rw [hf.2.2.2]
  rw [← mul_sum]
  simp [terminal,sum_sub_distrib,hs,ht]

private lemma path_augment {s t : V} {v : ℕ} {f : V → V → ℤ}
    (hf : unitFlow G s t v f) (p : G.Walk s t) (hp : p.IsPath)
    (hR : allowed (fun x y => f x y < 1) p) :
    unitFlow G s t (v+1) (fun x y => f x y + along p x y) := by
  refine ⟨fun x y => by dsimp; rw [hf.1 x y,along_skew p x y]; ring,?_,?_,?_⟩
  · intro x y
    dsimp
    by_cases h : s(x,y) ∈ p.edges
    · rcases along_edge p hp.isTrail _ hR h with ⟨hδ,hlt⟩|⟨hδ,hlt⟩
      · rw [hδ]; have := (hf.2.1 x y).1; omega
      · rw [hδ]; have := (hf.2.1 x y).2; have := hf.1 x y; omega
    · rw [along_zero p h,add_zero]
      exact hf.2.1 x y
  · intro x y hne
    have h : s(x,y) ∉ p.edges := fun he => hne (G.mem_edgeSet.1 (p.edges_subset_edgeSet he))
    simp [hf.2.2.1 x y hne,along_zero p h]
  · intro x
    unfold row
    rw [sum_add_distrib]
    change row f x + row (along p) x = _
    rw [hf.2.2.2 x,along_row]
    push_cast
    ring

private lemma path_remove {s t : V} {v : ℕ} {f : V → V → ℤ}
    (hf : unitFlow G s t (v+1) f) (p : G.Walk s t) (hp : p.IsPath)
    (hR : allowed (fun x y => 0 < f x y) p) :
    let f' := fun x y => f x y - along p x y
    unitFlow G s t v f' ∧
      (∀ x y, s(x,y) ∈ p.edges → f' x y = 0) ∧
      ∀ x y, f' x y ≠ 0 → f x y ≠ 0 := by
  dsimp
  have hz (x y : V) (h : s(x,y) ∈ p.edges) : f x y - along p x y = 0 := by
    rcases along_edge p hp.isTrail _ hR h with ⟨hδ,hlt⟩|⟨hδ,hlt⟩
    · have := (hf.2.1 x y).2
      omega
    · have := (hf.2.1 y x).2
      have := hf.1 x y
      omega
  refine ⟨⟨fun x y => by dsimp; rw [hf.1 x y,along_skew p x y]; ring,?_,?_,?_⟩,hz,?_⟩
  · intro x y
    by_cases h : s(x,y) ∈ p.edges
    · simp [hz x y h]
    · simpa [along_zero p h] using hf.2.1 x y
  · intro x y hne
    have h : s(x,y) ∉ p.edges := fun he => hne (G.mem_edgeSet.1 (p.edges_subset_edgeSet he))
    simp [hf.2.2.1 x y hne,along_zero p h]
  · intro x
    unfold row
    rw [sum_sub_distrib]
    change row f x - row (along p) x = _
    rw [hf.2.2.2 x,along_row]
    push_cast
    ring
  · intro x y h
    have hxy : s(x,y) ∉ p.edges := fun he => h (hz x y he)
    simpa [along_zero p hxy] using h


/-- A positive flow contains a source-to-sink path of positive-flow arcs. -/
private lemma positive_path {s t : V} {v : ℕ} {f : V → V → ℤ}
    (hv : 0 < v) (hf : unitFlow G s t v f) :
    ∃ p : G.Walk s t, p.IsPath ∧ allowed (fun x y => 0 < f x y) p := by
  let R : V → V → Prop := fun x y => 0 < f x y
  let S := reached G R s
  by_cases ht : t ∈ S
  · exact reached_path ht
  have hs : s ∈ S := reached_self G _ _
  have hcut := row_terminals hf hs ht
  have hnon : (∑ x ∈ S, ∑ y ∈ univ \ S, f x y) ≤ 0 := by
    refine sum_nonpos fun x hx => sum_nonpos fun y hy => ?_
    by_cases hxy : G.Adj x y
    · by_contra! h
      exact (mem_sdiff.1 hy).2 (reached_closed G R s hx hxy h)
    · simp [hf.2.2.1 x y hxy]
  have hv' : (v:ℤ) ≤ 0 := hcut ▸ hnon
  omega

/-- Integral unit flow decomposes into that many edge-disjoint paths.
Only edges on which the original flow is nonzero can occur. -/
private lemma flow_paths {s t : V} (hst : s ≠ t) :
    ∀ (v : ℕ) (f : V → V → ℤ), unitFlow G s t v f →
      ∃ P : Finset (G.Walk s t), P.card = v ∧ (∀ p ∈ P, p.IsPath) ∧
        ((P : Set (G.Walk s t)).Pairwise fun p q => List.Disjoint p.edges q.edges) ∧
        ∀ p ∈ P, ∀ x y, s(x,y) ∈ p.edges → f x y ≠ 0 := by
  intro v
  induction v with
  | zero => intro f hf; exact ⟨∅,by simp⟩
  | succ v ih =>
    intro f hf
    obtain ⟨p,hp,hRp⟩ := positive_path (by omega) hf
    obtain ⟨hf',hzero,hsupp⟩ := path_remove hf p hp hRp
    obtain ⟨P,hP,hPa,hPdis,hPsupp⟩ := ih _ hf'
    have hdis (q : G.Walk s t) (hq : q ∈ P) : List.Disjoint p.edges q.edges := by
      intro e he he'
      induction e using Sym2.inductionOn with
      | _ x y =>
        exact hPsupp q hq x y he' (hzero x y he)
    have hpnot : p ∉ P := by
      intro hpP
      have hne : p.edges ≠ [] := fun h => hst (Walk.edges_eq_nil.1 h).eq
      obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ hne
      exact hdis p hpP he he
    refine ⟨insert p P,by simp [hpnot,hP],?_,?_,?_⟩
    · intro q hq
      rcases mem_insert.1 hq with rfl|ha
      · exact hp
      · exact hPa q ha
    · intro x hx y hy hne
      rcases mem_insert.1 hx with hxp|hx <;> rcases mem_insert.1 hy with hyp|hy
      · exact (hne (hxp.trans hyp.symm)).elim
      · subst x
        exact hdis y hy
      · subst y
        exact (hdis x hx).symm
      · exact hPdis hx hy hne
    · intro q hq x y he
      rcases mem_insert.1 hq with hqp|ha
      · subst q
        rcases along_edge p hp.isTrail _ hRp he with ⟨_,hh⟩|⟨_,hh⟩
        · exact ne_of_gt hh
        · have h := hf.1 x y
          omega
      · exact hsupp x y (hPsupp q ha x y he)

/-- A maximal unit flow determines a separating cut of the same size. -/
private lemma optimal_cut {s t : V} (hst : s ≠ t) :
    ∃ (v : ℕ) (f : V → V → ℤ) (S : Finset V),
      unitFlow G s t v f ∧ s ∈ S ∧ t ∉ S ∧ cut G S = v ∧
      ∀ T : Finset V, s ∈ T → t ∉ T → cut G S ≤ cut G T := by
  let F : Set ℕ := {v | ∃ f, unitFlow G s t v f}
  have hF : F.Nonempty := ⟨0,fun _ _ => 0,by simp [unitFlow,skew,row]⟩
  have hB : BddAbove F := by
    refine ⟨Fintype.card V,?_⟩
    rintro v ⟨f,hf⟩
    have hv : row f s = v := by simpa [terminal,hst] using hf.2.2.2 s
    have hle : row f s ≤ (Fintype.card V:ℤ) := by
      unfold row
      simpa using sum_le_sum (s := (univ : Finset V)) (fun y _ => (hf.2.1 s y).2)
    exact_mod_cast hv ▸ hle
  let v := sSup F
  obtain ⟨f,hf⟩ := Nat.sSup_mem hF hB
  have hfv : unitFlow G s t v f := hf
  let R : V → V → Prop := fun x y => f x y < 1
  let S := reached G R s
  have hs : s ∈ S := reached_self G _ _
  have ht : t ∉ S := by
    intro ht
    obtain ⟨p,hp,hpR⟩ := reached_path ht
    have hv : v+1 ∈ F := ⟨_,path_augment hfv p hp hpR⟩
    have hh : v+1 ≤ v := le_csSup hB hv
    omega
  have hc : cut G S = v := by
    have hh := row_terminals hfv hs ht
    have he (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ univ \ S) :
        f x y = if G.Adj x y then 1 else 0 := by
      by_cases hxy : G.Adj x y
      · rw [if_pos hxy]
        have hnot : ¬ f x y < 1 := fun h =>
          (mem_sdiff.1 hy).2 (reached_closed G R s hx hxy h)
        have hle := (hfv.2.1 x y).2
        omega
      · simpa [hxy] using hfv.2.2.1 x y hxy
    have hEq : (∑ x ∈ S, ∑ y ∈ univ \ S, f x y) = (cut G S:ℤ) := by
      unfold cut
      push_cast
      exact sum_congr rfl fun x hx => sum_congr rfl fun y hy => by
        rw [he x hx y hy]
    exact_mod_cast hEq.symm.trans hh
  refine ⟨v,f,S,hfv,hs,ht,hc,?_⟩
  intro T hTs hTt
  have hh := row_terminals hfv hTs hTt
  have hle : (∑ x ∈ T, ∑ y ∈ univ \ T, f x y) ≤ (cut G T:ℤ) := by
    unfold cut
    push_cast
    refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
    by_cases h : G.Adj x y
    · simpa [h] using (hfv.2.1 x y).2
    · simp [h,hfv.2.2.1 x y h]
  rw [hc]
  exact_mod_cast hh ▸ hle


private def entry (G : SimpleGraph V) (S : Finset V) (x y : V) : ℕ :=
  if x ∈ S ∧ y ∉ S ∧ G.Adj x y then 1 else 0

private lemma cut_eq_entry (G : SimpleGraph V) (S : Finset V) :
    cut G S = ∑ x, ∑ y, entry G S x y := by
  calc
    _ = ∑ x, if x ∈ S then ∑ y ∈ univ \ S, if G.Adj x y then 1 else 0 else 0 := by
      rw [← sum_filter]
      simp [cut]
    _ = _ := by
      apply sum_congr rfl
      intro x hx
      by_cases h : x ∈ S
      · rw [if_pos h]
        rw [show (univ \ S) = univ.filter (fun y => y ∉ S) by ext; simp, sum_filter]
        apply sum_congr rfl
        intro y hy
        by_cases hh : y ∈ S <;> simp [entry,h,hh]
      · simp [entry,h]

private lemma cut_compl (G : SimpleGraph V) (S : Finset V) : cut G Sᶜ = cut G S := by
  simp only [cut,Finset.compl_eq_univ_sdiff]
  rw [show univ \ (univ \ S) = S by ext; simp, sum_comm]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  simp [G.adj_comm x y]

private lemma cut_submod (G : SimpleGraph V) (A B : Finset V) :
    cut G (A ∩ B) + cut G (A ∪ B) ≤ cut G A + cut G B := by
  simp only [cut_eq_entry,← sum_add_distrib]
  apply sum_le_sum
  intro x _
  apply sum_le_sum
  intro y _
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
    by_cases hyA : y ∈ A <;> by_cases hyB : y ∈ B <;>
      simp [entry,hxA,hxB,hyA,hyB]

private def Minimum (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∃ s ∈ A, ∃ t ∉ A, ∀ T : Finset V, s ∈ T → t ∉ T → cut G A ≤ cut G T

private lemma minimum_compl {G : SimpleGraph V} {A : Finset V} (h : Minimum G A) :
    Minimum G Aᶜ := by
  obtain ⟨s,hs,t,ht,hmin⟩ := h
  refine ⟨t,by simpa,s,by simpa,fun T htT hsT => ?_⟩
  rw [cut_compl]
  have hh := hmin Tᶜ (by simpa) (by simpa)
  rwa [cut_compl] at hh

private def uniform (A B : Finset V) : Prop := A ⊆ B ∨ Disjoint A B

private lemma adjust_cut {G : SimpleGraph V} {A : Finset V} (hA : Minimum G A)
    (B : Finset V) :
    ∃ C : Finset V, cut G C ≤ cut G B ∧ uniform A C ∧
      ∀ x ∉ A, x ∈ C ↔ x ∈ B := by
  obtain ⟨s,hs,t,ht,hmin⟩ := hA
  by_cases h : s ∈ B
  · refine ⟨A ∪ B,?_,Or.inl subset_union_left,fun x hx => by simp [hx]⟩
    have hh := hmin (A∩B) (mem_inter.2 ⟨hs,h⟩) (fun h => ht (mem_inter.1 h).1)
    have hm := cut_submod G A B
    omega
  · refine ⟨(A ∪ Bᶜ)ᶜ,?_,Or.inr ?_,fun x hx => by simp [hx]⟩
    · rw [cut_compl]
      have hh := hmin (A ∩ Bᶜ) (mem_inter.2 ⟨hs,by simpa⟩) (fun h => ht (mem_inter.1 h).1)
      have hm := cut_submod G A Bᶜ
      rw [cut_compl] at hm
      omega
    · rw [Finset.disjoint_left]
      intro x hx
      simp [hx]

private lemma adjust_many {G : SimpleGraph V} (𝒜 : Finset (Finset V))
    (hm : ∀ A ∈ 𝒜, Minimum G A) (hd : (𝒜 : Set (Finset V)).Pairwise Disjoint)
    (B : Finset V) :
    ∃ C : Finset V, cut G C ≤ cut G B ∧
      (∀ A ∈ 𝒜, uniform A C) ∧
      ∀ x, (∀ A ∈ 𝒜, x ∉ A) → (x ∈ C ↔ x ∈ B) := by
  induction 𝒜 using Finset.induction_on with
  | empty => exact ⟨B,le_rfl,by simp,fun _ _ => Iff.rfl⟩
  | @insert A 𝒜 hnot ih =>
    have hd' : (𝒜 : Set (Finset V)).Pairwise Disjoint := fun X hX Y hY hne =>
      hd (mem_insert_of_mem hX) (mem_insert_of_mem hY) hne
    obtain ⟨C,hC,hU,hout⟩ := ih (fun X hX => hm X (mem_insert_of_mem hX)) hd'
    obtain ⟨D,hD,hAu,hDo⟩ := adjust_cut (hm A (mem_insert_self _ _)) C
    refine ⟨D,hD.trans hC,?_,?_⟩
    · intro X hX
      rcases mem_insert.1 hX with h|hX
      · subst X
        exact hAu
      have hh (x : V) (hx : x ∈ X) : x ∈ D ↔ x ∈ C := hDo x (by
        have hh := hd (mem_insert_of_mem hX) (mem_insert_self A 𝒜) (by
          intro h
          exact hnot (h ▸ hX))
        exact Finset.disjoint_left.1 hh hx)
      obtain hs|hs := hU X hX
      · exact Or.inl fun x hx => (hh x hx).2 (hs hx)
      · exact Or.inr (Finset.disjoint_left.2 fun x hx hy =>
          Finset.disjoint_left.1 hs hx ((hh x hx).1 hy))
    · intro x hx
      exact (hDo x (hx A (mem_insert_self _ _))).trans
        (hout x fun X hX => hx X (mem_insert_of_mem hX))

private def compatible (A B : Finset V) : Prop :=
  ¬ ((∃ x, x∈A ∧ x∈B) ∧ (∃ x, x∈A ∧ x∉B) ∧
    (∃ x, x∉A ∧ x∈B) ∧ (∃ x, x∉A ∧ x∉B))

omit [Fintype V] [DecidableEq V] in
private lemma compatible_comm {A B : Finset V} : compatible A B ↔ compatible B A := by
  unfold compatible
  constructor
  · intro h ⟨⟨a,ha,hb⟩,⟨b,hb',hb''⟩,⟨c,hc,hc'⟩,⟨d,hd,hd'⟩⟩
    exact h ⟨⟨a,hb,ha⟩,⟨c,hc',hc⟩,⟨b,hb'',hb'⟩,⟨d,hd',hd⟩⟩
  · intro h ⟨⟨a,ha,hb⟩,⟨b,hb',hb''⟩,⟨c,hc,hc'⟩,⟨d,hd,hd'⟩⟩
    exact h ⟨⟨a,hb,ha⟩,⟨c,hc',hc⟩,⟨b,hb'',hb'⟩,⟨d,hd',hd⟩⟩

private lemma compatible_compl_left {A B : Finset V} : compatible Aᶜ B ↔ compatible A B := by
  simp only [compatible,Finset.mem_compl,not_not]
  constructor
  · exact fun h ⟨a,b,c,d⟩ => h ⟨c,d,a,b⟩
  · exact fun h ⟨a,b,c,d⟩ => h ⟨c,d,a,b⟩

private lemma compatible_compl_right {A B : Finset V} : compatible A Bᶜ ↔ compatible A B := by
  simp only [compatible,Finset.mem_compl,not_not]
  constructor
  · exact fun h ⟨a,b,c,d⟩ => h ⟨b,a,d,c⟩
  · exact fun h ⟨a,b,c,d⟩ => h ⟨b,a,d,c⟩

omit [Fintype V] [DecidableEq V] in
private lemma compatible_self (A : Finset V) : compatible A A := by
  simp [compatible]

omit [Fintype V] [DecidableEq V] in
private lemma compatible_of_uniform {A B : Finset V} (h : uniform A B) : compatible A B := by
  intro ⟨⟨x,hx,hx'⟩,⟨y,hy,hy'⟩,_,_⟩
  rcases h with h|h
  · exact hy' (h hy)
  · exact Finset.disjoint_left.1 h hx hx'

private def away (x : V) (A : Finset V) : Finset V := if x ∈ A then Aᶜ else A

private lemma away_not_mem (x : V) (A : Finset V) : x ∉ away x A := by
  unfold away
  split <;> simp_all

private lemma away_minimum {G : SimpleGraph V} {A : Finset V}
    (hA : Minimum G A) (x : V) : Minimum G (away x A) := by
  unfold away
  split
  · exact minimum_compl hA
  · exact hA

private lemma away_compatible {A B : Finset V}
    (h : compatible A B) (x : V) : compatible (away x A) (away x B) := by
  unfold away
  split <;> split <;> simpa [compatible_compl_left,compatible_compl_right]

omit [Fintype V] in
private lemma max_away {A : Finset V} {𝒜 : Finset (Finset V)} (hA : A ∈ 𝒜) :
    ∃ M ∈ 𝒜, A ⊆ M ∧ ∀ N ∈ 𝒜, M ⊆ N → N = M := by
  let R := 𝒜.filter (fun N => A ⊆ N)
  have hn : R.Nonempty := ⟨A,mem_filter.2 ⟨hA,Subset.rfl⟩⟩
  obtain ⟨M,hM,hle⟩ := exists_max_image R Finset.card hn
  refine ⟨M,(mem_filter.1 hM).1,(mem_filter.1 hM).2,?_⟩
  intro N hN hMN
  have hNM : N.card ≤ M.card := hle N (mem_filter.2 ⟨hN,(mem_filter.1 hM).2.trans hMN⟩)
  exact (eq_of_subset_of_card_le hMN hNM).symm

private def same (C : Finset (Finset V)) (x y : V) : Prop :=
  ∀ A ∈ C, x∈A ↔ y∈A

omit [Fintype V] in
private lemma same_add {C : Finset (Finset V)} {B : Finset V} {x y : V} :
    same (insert B C) x y ↔ same C x y ∧ (x∈B ↔ y∈B) := by
  constructor
  · intro h
    exact ⟨fun A hA => h A (mem_insert_of_mem hA),h B (mem_insert_self _ _)⟩
  · intro ⟨h,hB⟩ A hA
    rcases mem_insert.1 hA with rfl|hA
    · exact hB
    · exact h A hA

private lemma away_mem_same {C : Finset (Finset V)} {x y v : V} (hxy : same C x y)
    {A : Finset V} (hA : A ∈ C) : x ∈ away v A ↔ y ∈ away v A := by
  unfold away
  split
  · simpa using not_congr (hxy A hA)
  · exact hxy A hA

/-- Add a minimum cut separating two vertices in the same current atom.
Uncrossing lets the new cut leave every other atom intact. -/
private lemma extend_cut {G : SimpleGraph V} (C : Finset (Finset V))
    (hm : ∀ A ∈ C, Minimum G A) (hc : (C : Set (Finset V)).Pairwise compatible)
    {s t : V} (hst : s ≠ t) (hsame : same C s t) :
    ∃ B : Finset V, B ∉ C ∧ s ∈ B ∧ t ∉ B ∧ Minimum G B ∧
      (∀ A ∈ C, compatible A B) ∧
      ∀ x y, same C x y → ¬same C s x → (x∈B ↔ y∈B) := by
  let U := C.image (away s)
  let D := U.filter (fun A => ∀ X ∈ U, A ⊆ X → X = A)
  have hu (A : Finset V) (hA : A ∈ U) : s ∉ A ∧ t ∉ A := by
    obtain ⟨X,hX,rfl⟩ := mem_image.1 hA
    exact ⟨away_not_mem _ _,fun ht => away_not_mem s X ((away_mem_same hsame hX).2 ht)⟩
  have hmin (A : Finset V) (hA : A ∈ D) : Minimum G A := by
    obtain ⟨X,hX,rfl⟩ := mem_image.1 (mem_filter.1 hA).1
    exact away_minimum (hm X hX) s
  have hc' (A B : Finset V) (hA : A ∈ U) (hB : B ∈ U) : compatible A B := by
    obtain ⟨X,hX,rfl⟩ := mem_image.1 hA
    obtain ⟨Y,hY,rfl⟩ := mem_image.1 hB
    apply away_compatible
    by_cases h : X=Y
    · subst X
      exact compatible_self Y
    · exact hc hX hY h
  have hd : (D : Set (Finset V)).Pairwise Disjoint := by
    intro A hA B hB hne
    by_contra hdis
    obtain ⟨x,hx,hx'⟩ := not_disjoint_iff.1 hdis
    obtain ⟨ha₁,ha₂⟩ := mem_filter.1 hA
    obtain ⟨hb₁,hb₂⟩ := mem_filter.1 hB
    have hAB : ¬ A ⊆ B := fun h => hne (ha₂ B hb₁ h).symm
    have hBA : ¬ B ⊆ A := fun h => hne (hb₂ A ha₁ h)
    obtain ⟨a,ha,ha'⟩ := not_subset.1 hAB
    obtain ⟨b,hb,hb'⟩ := not_subset.1 hBA
    exact hc' A B ha₁ hb₁ ⟨⟨x,hx,hx'⟩,⟨a,ha,ha'⟩,⟨b,hb',hb⟩,
      ⟨s,(hu A ha₁).1,(hu B hb₁).1⟩⟩
  have hmax (A : Finset V) (hA : A ∈ U) : ∃ M ∈ D, A ⊆ M := by
    obtain ⟨M,hM,hAM,hMmax⟩ := max_away hA
    exact ⟨M,mem_filter.2 ⟨hM,hMmax⟩,hAM⟩
  obtain ⟨v,f,B,hf,hs,ht,he,hb⟩ := optimal_cut (G := G) hst
  obtain ⟨B',hle,huniform,hout⟩ := adjust_many D hmin hd B
  have hs' : s ∈ B' := (hout s (fun A hA => (hu A (mem_filter.1 hA).1).1)).2 hs
  have ht' : t ∉ B' := fun h => ht ((hout t (fun A hA => (hu A (mem_filter.1 hA).1).2)).1 h)
  refine ⟨B',fun h => ht' ((hsame B' h).1 hs'),hs',ht',
    ⟨s,hs',t,ht',fun T hT hT' => hle.trans (hb T hT hT')⟩,?_,?_⟩
  · intro A hA
    obtain ⟨M,hM,hm'⟩ := hmax (away s A) (mem_image.2 ⟨A,hA,rfl⟩)
    have h : uniform (away s A) B' := by
      obtain ha|ha := huniform M hM
      · exact Or.inl (hm'.trans ha)
      · exact Or.inr (ha.mono_left hm')
    have hh := compatible_of_uniform h
    unfold away at hh
    split at hh
    · exact compatible_compl_left.1 hh
    · exact hh
  · intro x y hxy hxs
    unfold same at hxs
    push Not at hxs
    obtain ⟨A,hA,hbad⟩ := hxs
    have hxA : x ∈ away s A := by
      unfold away
      by_cases hsA : s ∈ A <;> simp_all
    obtain ⟨M,hM,hle'⟩ := hmax (away s A) (mem_image.2 ⟨A,hA,rfl⟩)
    have hxM : x ∈ M := hle' hxA
    have hyM : y ∈ M := by
      obtain ⟨F,hF,heq⟩ := mem_image.1 (mem_filter.1 hM).1
      rw [← heq] at hxM ⊢
      exact (away_mem_same hxy hF).1 hxM
    obtain ha|ha := huniform M hM
    · exact iff_of_true (ha hxM) (ha hyM)
    · exact iff_of_false (Finset.disjoint_left.1 ha hxM) (Finset.disjoint_left.1 ha hyM)


omit [Fintype V] [DecidableEq V] in
private lemma same_refl (C : Finset (Finset V)) (x : V) : same C x x :=
  fun _ _ => Iff.rfl

omit [Fintype V] [DecidableEq V] in
private lemma same_symm {C : Finset (Finset V)} {x y : V} (h : same C x y) : same C y x :=
  fun A hA => (h A hA).symm

omit [Fintype V] [DecidableEq V] in
private lemma same_trans {C : Finset (Finset V)} {x y z : V}
    (h : same C x y) (h' : same C y z) : same C x z :=
  fun A hA => (h A hA).trans (h' A hA)

private structure CutSystem (G : SimpleGraph V) where
  cuts : Finset (Finset V)
  reps : Finset V
  minimum : ∀ A ∈ cuts, Minimum G A
  compatible : (cuts : Set (Finset V)).Pairwise compatible
  covers : ∀ x : V, ∃ y ∈ reps, same cuts x y
  no_duplicates : ∀ x ∈ reps, ∀ y ∈ reps, same cuts x y → x=y
  count : cuts.card+1 = reps.card

private lemma add_cut_system (G : SimpleGraph V) (S : CutSystem G)
    {s t : V} (hne : s≠t) (hst : same S.cuts s t) :
    ∃ T : CutSystem G, T.cuts.card = S.cuts.card+1 := by
  obtain ⟨B,hB,hs,ht,hmin,hcomp,hpreserve⟩ := extend_cut S.cuts S.minimum S.compatible hne hst
  obtain ⟨r,hr,hsr⟩ := S.covers s
  obtain ⟨u,hsu,hOpp⟩ : ∃ u, same S.cuts s u ∧ ¬(u∈B ↔ r∈B) := by
    by_cases h : r∈B
    · exact ⟨t,hst,fun eq => ht (eq.2 h)⟩
    · exact ⟨s,same_refl _ _,fun eq => h (eq.1 hs)⟩
  have hu : u ∉ S.reps := by
    intro hu
    have h := S.no_duplicates u hu r hr (same_trans (same_symm hsu) hsr)
    exact hOpp (h ▸ Iff.rfl)
  let T : CutSystem G :=
    { cuts := insert B S.cuts
      reps := insert u S.reps
      minimum := fun A hA => by
        rcases mem_insert.1 hA with rfl|hA
        · exact hmin
        · exact S.minimum A hA
      compatible := by
        intro A hA C hC hne
        rcases mem_insert.1 hA with hA'|hA' <;> rcases mem_insert.1 hC with hC'|hC'
        · exact (hne (hA'.trans hC'.symm)).elim
        · subst A
          exact compatible_comm.1 (hcomp C hC')
        · subst C
          exact hcomp A hA'
        · exact S.compatible hA' hC' hne
      covers := fun x => by
        by_cases hx : same S.cuts s x
        · by_cases hxr : x∈B ↔ r∈B
          · exact ⟨r,mem_insert_of_mem hr,same_add.2 ⟨same_trans (same_symm hx) hsr,hxr⟩⟩
          · have hxu : x∈B ↔ u∈B := by tauto
            exact ⟨u,mem_insert_self _ _,same_add.2 ⟨same_trans (same_symm hx) hsu,hxu⟩⟩
        · obtain ⟨v,hv,hxv⟩ := S.covers x
          exact ⟨v,mem_insert_of_mem hv,same_add.2 ⟨hxv,hpreserve x v hxv hx⟩⟩
      no_duplicates := fun x hx y hy hxy => by
        obtain ⟨he,hnew⟩ := same_add.1 hxy
        rcases mem_insert.1 hx with hxu|hxu <;> rcases mem_insert.1 hy with hyu|hyu
        · exact hxu.trans hyu.symm
        · subst x
          have h := S.no_duplicates y hyu r hr (same_trans (same_symm (same_trans hsu he)) hsr)
          exact (hOpp (h ▸ hnew)).elim
        · subst y
          have h := S.no_duplicates x hxu r hr (same_trans (same_symm (same_trans hsu (same_symm he))) hsr)
          exact (hOpp (h ▸ hnew.symm)).elim
        · exact S.no_duplicates x hxu y hyu he
      count := by simp [hB,hu, ← S.count] }
  exact ⟨T,by simp [T,hB]⟩

private lemma separating_cuts (G : SimpleGraph V) [Nonempty V] :
    ∃ C : Finset (Finset V), C.card ≤ Fintype.card V-1 ∧
      (∀ A ∈ C, Minimum G A) ∧ (C : Set (Finset V)).Pairwise compatible ∧
      ∀ x y, same C x y → x=y := by
  let F : Set ℕ := {k | ∃ S : CutSystem G, S.cuts.card=k}
  have hF : F.Nonempty := by
    obtain ⟨r⟩ := ‹Nonempty V›
    refine ⟨0,⟨⟨∅,{r},by simp,by simp,?_ ,?_ ,by simp⟩,rfl⟩⟩
    · intro x
      exact ⟨r,by simp,by simp [same]⟩
    · simp
  have hB : BddAbove F := by
    refine ⟨Fintype.card V,?_⟩
    rintro k ⟨S,rfl⟩
    have hh := card_le_univ S.reps
    have := S.count
    omega
  obtain ⟨S,hS⟩ := Nat.sSup_mem hF hB
  refine ⟨S.cuts,?_,S.minimum,S.compatible,?_⟩
  · have hh := card_le_univ S.reps
    have := S.count
    omega
  · intro x y hxy
    by_contra! hne
    obtain ⟨T,hT⟩ := add_cut_system G S hne hxy
    have hle := le_csSup hB (show T.cuts.card ∈ F from ⟨T,rfl⟩)
    omega

private def crosses (A : Finset V) (x y : V) : Prop := x∈A ↔ y∉A

private def crossSet (C : Finset (Finset V)) (x y : V) : Finset (Finset V) :=
  C.filter fun A => crosses A x y

omit [Fintype V] in
private lemma cross_iff {A : Finset V} {x y : V} :
    crosses A x y ↔ ¬(x∈A ↔ y∈A) := by
  unfold crosses
  tauto

omit [Fintype V] in
private lemma crossSet_ne_empty {C : Finset (Finset V)}
    (hsep : ∀ x y, same C x y → x=y) {x y : V} (hxy : x≠y) :
    (crossSet C x y).Nonempty := by
  by_contra! h
  apply hxy (hsep _ _ ?_)
  intro A hA
  by_contra hn
  have : A∈crossSet C x y := mem_filter.2 ⟨hA,cross_iff.2 hn⟩
  simp [h] at this

private lemma equal_endpoints {C : Finset (Finset V)}
    (hc : (C : Set (Finset V)).Pairwise compatible)
    (hsep : ∀ x y, same C x y → x=y)
    {A : Finset V} {x y x' y' : V}
    (hx : x∈A) (hy : y∉A) (hx' : x'∈A) (hy' : y'∉A)
    (hA : A∈C) (h : crossSet C x y = {A}) (h' : crossSet C x' y' = {A}) :
    x=x' ∧ y=y' := by
  have ho (B : Finset V) (hB : B∈C) (hne : B≠A) : (x∈B ↔ y∈B) := by
    by_contra hbad
    have hb : B∈crossSet C x y := mem_filter.2 ⟨hB,cross_iff.2 hbad⟩
    rw [h,mem_singleton] at hb
    exact hne hb
  have ho' (B : Finset V) (hB : B∈C) (hne : B≠A) : (x'∈B ↔ y'∈B) := by
    by_contra hbad
    have hb : B∈crossSet C x' y' := mem_filter.2 ⟨hB,cross_iff.2 hbad⟩
    rw [h',mem_singleton] at hb
    exact hne hb
  have hxx : same C x x' := by
    intro B hB
    by_cases hBA : B=A
    · subst B
      exact iff_of_true hx hx'
    have hb := ho B hB hBA
    have hb' := ho' B hB hBA
    by_contra hn
    by_cases hxB : x∈B
    · have hx'B : x'∉B := fun hz => hn (iff_of_true hxB hz)
      exact hc hA hB (Ne.symm hBA) ⟨⟨x,hx,hxB⟩,⟨x',hx',hx'B⟩,⟨y,hy,hb.1 hxB⟩,
        ⟨y',hy',fun hh => hx'B (hb'.2 hh)⟩⟩
    · have hx'B : x'∈B := by by_contra! hq; exact hn (iff_of_false hxB hq)
      exact hc hA hB (Ne.symm hBA) ⟨⟨x',hx',hx'B⟩,⟨x,hx,hxB⟩,⟨y',hy',hb'.1 hx'B⟩,
        ⟨y,hy,fun hh => hxB (hb.2 hh)⟩⟩
  refine ⟨hsep _ _ hxx,hsep _ _ ?_⟩
  intro B hB
  by_cases hBA : B=A
  · subst B
    exact iff_of_false hy hy'
  exact (ho B hB hBA).symm.trans ((hxx B hB).trans (ho' B hB hBA))

private lemma count_single_cross (E : Finset (V × V)) {C : Finset (Finset V)}
    (hc : (C : Set (Finset V)).Pairwise compatible)
    (hsep : ∀ x y, same C x y → x=y) :
    (E.filter fun p => (crossSet C p.1 p.2).card=1).card ≤ 2*C.card := by
  let U := E.filter fun p => (crossSet C p.1 p.2).card=1
  have hex (p : U) : ∃ a, crossSet C p.val.1 p.val.2 = {a} :=
    card_eq_one.1 (mem_filter.1 p.property).2
  choose A hA using hex
  have hAC (p : U) : A p ∈ C := by
    have hh : A p∈crossSet C p.val.1 p.val.2 := by simp [hA]
    exact (mem_filter.1 hh).1
  have hcross (p : U) : crosses (A p) p.val.1 p.val.2 := by
    have hh : A p∈crossSet C p.val.1 p.val.2 := by simp [hA]
    exact (mem_filter.1 hh).2
  let f (p : U) : C × Bool := (⟨A p,hAC p⟩,decide (p.val.1∈A p))
  have hf : Function.Injective f := by
    intro p q he
    have hAeq : A p=A q := congrArg (fun z : C × Bool => z.1.val) he
    have hbool := congrArg Prod.snd he
    have hmem : p.val.1∈A p ↔ q.val.1∈A p := by
      dsimp [f] at hbool
      rw [← hAeq] at hbool
      by_cases hp : p.val.1∈A p <;> by_cases hq : q.val.1∈A p <;> simp_all
    have hqA : crossSet C q.val.1 q.val.2={A p} := hAeq ▸ hA q
    have hqX : crosses (A p) q.val.1 q.val.2 := hAeq ▸ hcross q
    by_cases hp : p.val.1∈A p
    · have hq : q.val.1∈A p := hmem.1 hp
      have hp' : p.val.2∉A p := (hcross p).1 hp
      have hq' : q.val.2∉A p := hqX.1 hq
      obtain ⟨hx,hy⟩ := equal_endpoints hc hsep hp hp' hq hq' (hAC p) (hA p) hqA
      exact Subtype.ext (Prod.ext hx hy)
    · have hq : q.val.1∉A p := fun h => hp (hmem.2 h)
      have hp' : p.val.2∈A p := by by_contra! h; exact hp ((hcross p).2 h)
      have hq' : q.val.2∈A p := by by_contra! h; exact hq (hqX.2 h)
      have hflip (x y : V) : crossSet C y x = crossSet C x y := by
        ext a
        simp only [crossSet,mem_filter,cross_iff]
        tauto
      obtain ⟨hy,hx⟩ := equal_endpoints hc hsep hp' hp hq' hq (hAC p)
        ((hflip _ _).trans (hA p)) ((hflip _ _).trans hqA)
      exact Subtype.ext (Prod.ext hx hy)
  have h := Fintype.card_le_of_injective f hf
  simpa [mul_comm,Fintype.card_prod,Fintype.card_coe] using h


private lemma sum_crossings (G : SimpleGraph V) (A : Finset V) :
    (∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
      if crosses A p.1 p.2 then 1 else 0) = 2*cut G A := by
  rw [show 2*cut G A = cut G A + cut G Aᶜ by rw [cut_compl,two_mul],
    cut_eq_entry G A,cut_eq_entry G Aᶜ,← sum_add_distrib]
  simp_rw [← sum_add_distrib]
  rw [sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases hx : x∈A <;> by_cases hy : y∈A <;> by_cases hG : G.Adj x y <;>
    simp [entry,crosses,hx,hy,hG]

private lemma edges_bound (G : SimpleGraph V) [Nonempty V] (m : ℕ)
    (hC : ∀ A : Finset V, Minimum G A → cut G A ≤ m) :
    2*G.edgeSet.ncard ≤ (m+1)*(Fintype.card V-1) := by
  obtain ⟨C,hCcard,hCmin,hcompat,hsep⟩ := separating_cuts G
  let E := (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2)
  let d (p : V × V) := (crossSet C p.1 p.2).card
  let U := E.filter (fun p => d p = 1)
  have hU : U.card ≤ 2*C.card := count_single_cross E hcompat hsep
  have hS : (∑ p ∈ E, d p) = ∑ A ∈ C, 2*cut G A := by
    have hd (p : V × V) : d p = ∑ A ∈ C, if crosses A p.1 p.2 then 1 else 0 := by simp [d,crossSet]
    simp_rw [hd]
    rw [sum_comm]
    exact sum_congr rfl fun A _ => sum_crossings G A
  have hbound : (∑ A ∈ C, 2*cut G A) ≤ 2*m*C.card := by
    have hh : (∑ A ∈ C, 2*cut G A) ≤ ∑ _ ∈ C, 2*m :=
      sum_le_sum fun A hA => Nat.mul_le_mul_left _ (hC A (hCmin A hA))
    simpa [mul_assoc,mul_comm,mul_left_comm] using hh
  have hsum : 2*E.card ≤ (∑ p ∈ E,d p)+U.card := by
    have h : (∑ _ ∈ E, (2:ℕ)) ≤ ∑ p ∈ E, (d p + if d p = 1 then 1 else 0) := by
      refine sum_le_sum fun p hp => ?_
      have hne : p.1 ≠ p.2 := (show G.Adj p.1 p.2 from (mem_filter.1 hp).2).ne
      have hd : 0 < d p := card_pos.2 (crossSet_ne_empty hsep hne)
      split <;> omega
    simpa [sum_add_distrib,mul_comm,U] using h
  have hEc : E.card = 2*G.edgeSet.ncard := by
    rw [← G.coe_edgeFinset,Set.ncard_coe_finset]
    exact G.two_mul_card_edgeFinset.symm
  have htotal : 2*E.card ≤ 2*m*C.card+2*C.card :=
    hsum.trans (Nat.add_le_add (hS.trans_le hbound) hU)
  rw [hEc] at htotal
  have htotal' : 2*G.edgeSet.ncard ≤ (m+1)*C.card := by
    have ht : 2*m*C.card+2*C.card = 2*((m+1)*C.card) := by ring
    omega
  exact htotal'.trans (Nat.mul_le_mul_left _ hCcard)

private lemma choose_two (m : ℕ) (hm : 2 ≤ m) : 2*m.choose 2 = m*(m-1) := by
  rw [Nat.choose_two_right]
  have hmod : (m*(m-1))%2=0 := by
    rw [Nat.mul_mod]
    rcases (show m%2=0 ∨ m%2=1 by omega) with h|h
    · simp [h]
    · have h' : (m-1)%2=0 := by omega
      simp [h']
  have hdiv := Nat.mod_add_div (m*(m-1)) 2
  omega

end

/-- A family of compatible minimum cuts gives the edge bound after each cut
is charged for the edges it separates. The minimum-cut facts follow from
augmenting and decomposing unit flows on oriented edges. -/
theorem solution (m n : ℕ) (hm : 2 ≤ m) (_hn : 1 ≤ n)
    (V : Type) [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 1+n*(m-1)) (hE : G.edgeSet.ncard = 1+n*m.choose 2) :
    ∃ u v : V, u ≠ v ∧ ∃ P : Finset (G.Walk u v), P.card = m ∧
      (∀ p ∈ P, p.IsPath) ∧ ((P : Set (G.Walk u v)).Pairwise
        fun p q => List.Disjoint p.edges q.edges) := by
  classical
  let _ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  by_contra h
  have hcuts (A : Finset V) (hA : Minimum G A) : cut G A ≤ m-1 := by
    obtain ⟨s,hs,t,ht,hmin⟩ := hA
    have hst : s≠t := fun h => ht (h ▸ hs)
    obtain ⟨v,f,C,hflow,hcs,hct,hc,_⟩ := optimal_cut (G := G) hst
    apply (hmin C hcs hct).trans
    rw [hc]
    by_contra! hv
    obtain ⟨P,hP,hpath,hdis,_⟩ := flow_paths (G := G) hst v f hflow
    obtain ⟨Q,hQ,hQcard⟩ := exists_subset_card_eq (s := P)
      (show m ≤ P.card from hP ▸ by omega)
    exact h ⟨s,t,hst,Q,hQcard,fun p hp => hpath p (hQ hp),
      hdis.mono (show (Q : Set (G.Walk s t)) ⊆ P from hQ)⟩
  have hh := edges_bound G (m-1) hcuts
  rw [hE,hV,Nat.sub_add_cancel (show 1 ≤ m by omega)] at hh
  have hr : (1+n*(m-1)-1)*m = 2*(n*m.choose 2) := by
    rw [Nat.add_sub_cancel_left]
    calc
      _ = n*(m*(m-1)) := by ring
      _ = _ := by rw [← choose_two m hm]; ring
  rw [mul_comm m] at hh
  omega

end OMA915

theorem OMA.solution : type_of% @Erdos915.erdos_915.variants.edge_disjoint := by
  exact OMA915.solution