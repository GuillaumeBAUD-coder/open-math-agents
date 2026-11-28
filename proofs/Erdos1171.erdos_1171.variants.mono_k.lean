import FormalConjectures.ErdosProblems.«1171»

/-! # Monotonicity in the number of colors for Erdős 1171 -/
-- Credit: @steveDOTdigital

open Ordinal Cardinal

universe u v

lemma OMA.fewer {j k : ℕ} (hjk : j ≤ k)
    (hk : OrdinalMultiColorRamsey.{u} (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    OrdinalMultiColorRamsey.{u} (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  classical
  intro col
  let embed := Fin.castLE (n := j + 1) (m := k + 1) (by omega)
  obtain ⟨A, hmono, htype⟩ | ⟨i, A, hmono, hcard⟩ :=
    hk fun e => embed (col e)
  · refine Or.inl ⟨A, ?_, htype⟩
    intro x hx y hy hxy
    have he := congrArg Fin.val (hmono x hx y hy hxy)
    exact Fin.ext he
  · have hi : i.val < j := by
      by_contra hi
      -- An unused color cannot occur on an edge. Its clique has at most one vertex.
      have hs : A.Subsingleton := by
        intro x hx y hy
        by_contra hxy
        have he := congrArg Fin.val (hmono x hx y hy hxy)
        simp [embed] at he
        have hb := (col s(x, y)).isLt
        omega
      have hsmall := hcard ▸ hs.cardinalMk_le_one
      norm_num at hsmall
    refine Or.inr ⟨⟨i.val, hi⟩, A, ?_, hcard⟩
    intro x hx y hy hxy
    have he := congrArg Fin.val (hmono x hx y hy hxy)
    exact Fin.ext he

-- The two universe parameters in the upstream theorem are independent.
lemma OMA.transfer {j : ℕ} (h : OrdinalMultiColorRamsey.{u} (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) :
    OrdinalMultiColorRamsey.{v} (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  classical
  let X := ((ω_ 1 ^ 2 : Ordinal.{u})).ToType
  let Y := ((ω_ 1 ^ 2 : Ordinal.{v})).ToType
  have hXY : Ordinal.lift.{v} (typeLT X) = Ordinal.lift.{u} (typeLT Y) := by
    simp [X, Y, Ordinal.type_toType, pow_two]
  obtain ⟨r⟩ : Nonempty (((· < ·) : X → X → Prop) ≃r ((· < ·) : Y → Y → Prop)) :=
    Ordinal.lift_type_eq.{u,v,0}.mp hXY
  let e : X ≃o Y := OrderIso.ofRelIsoLT r
  let img (A : Set X) : A ≃o (e '' A) :=
    { toEquiv := Equiv.Set.imageOfInjOn e A e.injective.injOn
      map_rel_iff' := e.le_iff_le }
  intro col
  obtain ⟨A, hm, ht⟩ | ⟨i, A, hm, hc⟩ := h fun p => col (p.map e)
  · refine Or.inl ⟨e '' A, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hm x hx y hy fun h => hxy (congrArg e h)
    · have ht' := (img A).toRelIsoLT.ordinal_lift_type_eq
      change Ordinal.lift.{v} (typeLT A) = Ordinal.lift.{u} (typeLT (e '' A)) at ht'
      apply (Ordinal.lift_inj.{u}).mp
      simpa [ht] using ht'.symm
  · refine Or.inr ⟨i, e '' A, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hm x hx y hy fun h => hxy (congrArg e h)
    · have hc' : Cardinal.lift.{v} (#A) = Cardinal.lift.{u} (#(e '' A)) :=
        Cardinal.lift_mk_eq.{u,v,0}.mpr ⟨(img A).toEquiv⟩
      apply (Cardinal.lift_inj.{v,u}).mp
      simpa [hc] using hc'.symm

theorem OMA.solution : type_of% @Erdos1171.erdos_1171.variants.mono_k :=
  fun h k => transfer (fewer h k)
