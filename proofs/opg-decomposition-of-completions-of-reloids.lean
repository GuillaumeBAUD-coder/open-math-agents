import OMAStatements.S_opg_decomposition_of_completions_of_reloids

/-!
# Counterexamples and surviving identities for completion of reloids

Victor Porton, Algebraic General Topology, volume 1, Conjecture 1057.
-/

namespace ReLoidProof

open OMA.S_opg_decomposition_of_completions_of_reloids
open Filter
open scoped Filter

private theorem fiberJoin_mem {X I : Type*} (c : X → I) {f : Filter X} {s : Set X}
    (hs : s ∈ f) : s ∈ fiberJoin c f :=
  fun _ => ⟨s,hs,fun _ hx _ => hx⟩

/-- This identifies the fiber definition with the join of restrictions in Porton's
Proposition 7.58. Taking c = Prod.snd gives the dual identity for columns. -/
theorem fiberJoin_eq {X I : Type*} (c : X → I) (f : Filter X) :
    fiberJoin c f = ⨆ i : I, f ⊓ 𝓟 {x | c x = i} := by
  apply Filter.ext
  intro s
  simp only [mem_iSup, mem_inf_principal]
  constructor
  · intro h i
    obtain ⟨r, hr, hh⟩ := h i
    exact f.sets_of_superset hr (fun x hx hi => hh x hx hi)
  · intro h i
    exact ⟨_,h i,fun _ hx hi => hx hi⟩

private theorem fiberJoin_subsingleton {X I : Type*} [Unique I] (c : X → I) (f : Filter X) :
    fiberJoin c f = f := by
  apply Filter.ext
  intro s
  refine ⟨?_,fiberJoin_mem c⟩
  intro h
  obtain ⟨r, hr, hh⟩ := h default
  exact f.sets_of_superset hr (fun x hx => hh x hx (Subsingleton.elim ..))

private theorem fiberJoin_top {X I : Type*} (c : X → I) :
    fiberJoin c (⊤ : Filter X) = ⊤ := by
  apply Filter.ext
  intro s
  refine ⟨?_,fiberJoin_mem c⟩
  intro h
  apply Filter.mem_top_iff_forall.mpr
  intro x
  obtain ⟨r, hr, hh⟩ := h (c x)
  exact hh x (Filter.mem_top_iff_forall.mp hr x) rfl

private theorem source_floor {A B C : Type*} [Infinite A] [Unique B] [Nonempty C] :
    let f : ReLoid A B := cofinite
    let g : ReLoid B C := ⊤
    coCompl f = f ∧ compl g = g ∧ compl (compose g f) = ⊥ ∧ compose g f ≠ ⊥ := by
  dsimp only
  refine ⟨fiberJoin_subsingleton _ _, fiberJoin_top _, Filter.empty_mem_iff_bot.mp ?_, ?_⟩
  · intro a
    let r : Set (A × B) := {(a,default)}ᶜ
    have hr : r ∈ cofinite := Filter.le_cofinite_iff_compl_singleton_mem.mp le_rfl _
    let s : Set (B × C) := Set.univ
    refine ⟨relComp s r, ⟨r,hr,s,Filter.univ_mem,Set.Subset.rfl⟩,?_⟩
    rintro ⟨a',c⟩ ⟨b,hab,_⟩ ha
    exact hab (Prod.ext ha (Subsingleton.elim ..))
  · intro eq_bot
    obtain ⟨r,hr,s,hs,h⟩ := Filter.empty_mem_iff_bot.mpr eq_bot
    obtain ⟨⟨a,b⟩,hab⟩ := Filter.nonempty_of_mem hr
    obtain ⟨c⟩ := ‹Nonempty C›
    exact h (a := (a,c)) ⟨b,hab,mem_top_iff_forall.mp hs (b,c)⟩

private theorem target_floor {A B C : Type*} [Nonempty A] [Unique B] [Infinite C] :
    let f : ReLoid A B := ⊤
    let g : ReLoid B C := cofinite
    coCompl f = f ∧ compl g = g ∧ coCompl (compose g f) = ⊥ ∧ compose g f ≠ ⊥ := by
  dsimp only
  refine ⟨fiberJoin_top _, fiberJoin_subsingleton _ _, Filter.empty_mem_iff_bot.mp ?_, ?_⟩
  · intro c
    let s : Set (B × C) := {(default,c)}ᶜ
    have hs : s ∈ cofinite := Filter.le_cofinite_iff_compl_singleton_mem.mp le_rfl _
    let r : Set (A × B) := Set.univ
    refine ⟨relComp s r, ⟨r,Filter.univ_mem,s,hs,Set.Subset.rfl⟩,?_⟩
    rintro ⟨a,c'⟩ ⟨b,_,hbc⟩ hc
    exact hbc (Prod.ext (Subsingleton.elim ..) hc)
  · intro eq_bot
    obtain ⟨r,hr,s,hs,h⟩ := Filter.empty_mem_iff_bot.mpr eq_bot
    obtain ⟨⟨b,c⟩,hbc⟩ := Filter.nonempty_of_mem hs
    obtain ⟨a⟩ := ‹Nonempty A›
    exact h (a := (a,c)) ⟨b,mem_top_iff_forall.mp hr (a,b),hbc⟩

theorem clause_four {A B C : Type*} (f : ReLoid A B) (g : ReLoid B C) :
    compl (compose g (compl f)) = compl (compose g f) := by
  apply Filter.ext
  intro t
  constructor
  · intro h a
    obtain ⟨u, ⟨r,hr,s,hs,hu⟩, ht⟩ := h a
    obtain ⟨r',hr',hh⟩ := hr a
    refine ⟨relComp s r', ⟨r',hr',s,hs,Set.Subset.rfl⟩,?_⟩
    rintro ⟨a',c⟩ ⟨b,hbr,hbs⟩ ha
    exact ht _ (hu ⟨b,hh _ hbr ha,hbs⟩) ha
  · intro h a
    obtain ⟨u, ⟨r,hr,s,hs,hu⟩, ht⟩ := h a
    exact ⟨u,⟨r,fiberJoin_mem _ hr,s,hs,hu⟩,ht⟩

theorem clause_five {A B C : Type*} (f : ReLoid A B) (g : ReLoid B C) :
    coCompl (compose (coCompl g) f) = coCompl (compose g f) := by
  apply Filter.ext
  intro t
  constructor
  · intro h c
    obtain ⟨u, ⟨r,hr,s,hs,hu⟩, ht⟩ := h c
    obtain ⟨s',hs',hh⟩ := hs c
    refine ⟨relComp s' r, ⟨r,hr,s',hs',Set.Subset.rfl⟩,?_⟩
    rintro ⟨a,c'⟩ ⟨b,hbr,hbs⟩ hc
    exact ht _ (hu ⟨b,hbr,hh _ hbs hc⟩) hc
  · intro h c
    obtain ⟨u, ⟨r,hr,s,hs,hu⟩, ht⟩ := h c
    exact ⟨u,⟨r,hr,s,fiberJoin_mem _ hs,hu⟩,ht⟩

universe u v w

theorem first_and_third_fail :
    ∃ (A : Type u) (B : Type v) (C : Type w) (f : ReLoid A B) (g : ReLoid B C),
      coCompl f = f ∧ compl (compose g f) ≠ compose (compl g) f ∧
      compl (compose g (coCompl f)) ≠ compose (compl g) (coCompl f) := by
  let A := ULift.{u} ℕ
  let B := PUnit.{v+1}
  let C := PUnit.{w+1}
  refine ⟨A,B,C,cofinite,⊤,?_⟩
  obtain ⟨hf,hg,dead,alive⟩ := source_floor (A:=A) (B:=B) (C:=C)
  rw [hf,hg,dead]
  exact ⟨rfl, Ne.symm alive, Ne.symm alive⟩

theorem second_fails :
    ∃ (A : Type u) (B : Type v) (C : Type w) (f : ReLoid A B) (g : ReLoid B C),
      compl g = g ∧ coCompl (compose g f) ≠ compose g (coCompl f) := by
  let A := PUnit.{u+1}
  let B := PUnit.{v+1}
  let C := ULift.{w} ℕ
  refine ⟨A,B,C,⊤,cofinite,?_⟩
  obtain ⟨hf,hg,dead,alive⟩ := target_floor (A:=A) (B:=B) (C:=C)
  rw [hf,hg,dead]
  exact ⟨rfl, Ne.symm alive⟩

end ReLoidProof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_decomposition_of_completions_of_reloids.main) := by
  obtain ⟨A,B,C,f,g,hf,bad,_⟩ := ReLoidProof.first_and_third_fail
  exact fun h => bad ((h A B C f g).1 hf)

