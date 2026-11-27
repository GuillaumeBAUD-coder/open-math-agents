import FormalConjectures.Mathoverflow.«235893»

-- Problem: Mathoverflow 235893 — mathoverflow 260589
-- Upstream: formal-conjectures FormalConjectures/Mathoverflow/235893.lean:217 (declaration Mathoverflow235893.mathoverflow_260589)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.MO260589

open Mathoverflow235893
open scoped Classical Cardinal EuclideanGeometry

private abbrev E2 := ℝ^2
private abbrev Alpha := (𝔠 : Cardinal.{0}).ord.ToType
private abbrev Idx := Lex (Alpha × Fin 3)
private abbrev Req :=
  {p : ℚ × ℚ // p.1 < p.2} × {C : Set E2 // IsClosed C ∧ 𝔠 ≤ #C}

private lemma mk_E2 : #E2 = 𝔠 := by
  let h1 : E2 ≃ ℝ × ℝ :=
    { toFun := fun v => (v 0, v 1)
      invFun := fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1, p.2]
      left_inv := fun v => by
        ext i
        fin_cases i <;> rfl
      right_inv := fun p => by simp }
  rw [Cardinal.mk_congr h1, Cardinal.mk_prod, Cardinal.lift_id,
    Cardinal.mk_real, Cardinal.mul_eq_self Cardinal.aleph0_le_continuum]

private lemma mk_closed_le_continuum : #{C : Set E2 // IsClosed C} ≤ 𝔠 := by
  obtain ⟨b, hb_count, _, hb_basis⟩ := TopologicalSpace.exists_countable_basis E2
  let φ : {C : Set E2 // IsClosed C} → Set b := fun C => {U : b | (U : Set E2) ⊆ C.1ᶜ}
  have hφ : Function.Injective φ := by
    intro C₁ C₂ hEq
    have hcompl : C₁.1ᶜ = C₂.1ᶜ := by
      ext x
      have hx₁ : x ∈ C₁.1ᶜ ↔ ∃ U : b, x ∈ (U : Set E2) ∧ U ∈ φ C₁ := by
        constructor
        · intro hx
          obtain ⟨U, hUb, hxU, hUsub⟩ := hb_basis.isOpen_iff.mp C₁.2.isOpen_compl x hx
          exact ⟨⟨U, hUb⟩, hxU, hUsub⟩
        · rintro ⟨U, hxU, hUsub⟩
          exact hUsub hxU
      have hx₂ : x ∈ C₂.1ᶜ ↔ ∃ U : b, x ∈ (U : Set E2) ∧ U ∈ φ C₂ := by
        constructor
        · intro hx
          obtain ⟨U, hUb, hxU, hUsub⟩ := hb_basis.isOpen_iff.mp C₂.2.isOpen_compl x hx
          exact ⟨⟨U, hUb⟩, hxU, hUsub⟩
        · rintro ⟨U, hxU, hUsub⟩
          exact hUsub hxU
      rw [hx₁, hx₂, hEq]
    exact Subtype.ext (compl_injective hcompl)
  calc
    #{C : Set E2 // IsClosed C} ≤ #(Set b) := Cardinal.mk_le_of_injective hφ
    _ = 2 ^ #b := Cardinal.mk_set
    _ ≤ 2 ^ ℵ₀ := Cardinal.power_le_power_left (by norm_num) (Cardinal.mk_le_aleph0_iff.mpr hb_count)
    _ = 𝔠 := Cardinal.two_power_aleph0

private lemma mk_req_le_continuum : #Req ≤ 𝔠 := by
  have h1 : #{p : ℚ × ℚ // p.1 < p.2} ≤ 𝔠 := by
    calc
      #{p : ℚ × ℚ // p.1 < p.2} ≤ #(ℚ × ℚ) := Cardinal.mk_subtype_le _
      _ ≤ ℵ₀ := Cardinal.mk_le_aleph0
      _ ≤ 𝔠 := Cardinal.aleph0_le_continuum
  have h2 : #{C : Set E2 // IsClosed C ∧ 𝔠 ≤ #C} ≤ 𝔠 := by
    have hinj : Function.Injective
        (fun C : {C : Set E2 // IsClosed C ∧ 𝔠 ≤ #C} => (⟨C.1, C.2.1⟩ : {C : Set E2 // IsClosed C})) := by
      rintro ⟨C₁, h₁⟩ ⟨C₂, h₂⟩ hab
      have hC : C₁ = C₂ := congrArg Subtype.val hab
      subst hC
      rfl
    exact (Cardinal.mk_le_of_injective hinj).trans mk_closed_le_continuum
  calc
    #Req = #{p : ℚ × ℚ // p.1 < p.2} * #{C : Set E2 // IsClosed C ∧ 𝔠 ≤ #C} := by
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    _ ≤ 𝔠 * 𝔠 := mul_le_mul' h1 h2
    _ = 𝔠 := Cardinal.mul_eq_self Cardinal.aleph0_le_continuum

private lemma nonempty_req : Nonempty Req :=
  ⟨⟨⟨(0, 1), by norm_num⟩, ⟨Set.univ, isClosed_univ, by rw [Cardinal.mk_univ, mk_E2]⟩⟩⟩

private lemma mk_alpha : #Alpha = 𝔠 := by
  simp [Alpha]

private lemma card_Iio_alpha (a : Alpha) : #{b : Alpha // b < a} < 𝔠 := by
  have hlt : (Ordinal.typein (· < · : Alpha → Alpha → Prop) a).card < 𝔠 := by
    rw [← Cardinal.lt_ord]
    have h := Ordinal.typein_lt_type (· < · : Alpha → Alpha → Prop) a
    rwa [Ordinal.type_toType] at h
  have heq : (Ordinal.typein (· < · : Alpha → Alpha → Prop) a).card = #{b : Alpha // b < a} := by
    change (Ordinal.type (· < · : {b : Alpha // b < a} → {b : Alpha // b < a} → Prop)).card = _
    exact Ordinal.card_type _
  rwa [← heq]

private lemma card_Iio_idx (t : Idx) : #{s : Idx // s < t} < 𝔠 := by
  let a : Alpha := (ofLex t).1
  let f : {s : Idx // s < t} → ({b : Alpha // b < a} ⊕ Unit) × Fin 3 := fun s =>
    if h : (ofLex s.1).1 < a then
      (Sum.inl ⟨(ofLex s.1).1, h⟩, (ofLex s.1).2)
    else
      (Sum.inr (), (ofLex s.1).2)
  have hf : Function.Injective f := by
    intro s₁ s₂ hEq
    have hle₁ : (ofLex s₁.1).1 ≤ a := by
      rcases Prod.Lex.lt_iff.mp s₁.2 with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    have hle₂ : (ofLex s₂.1).1 ≤ a := by
      rcases Prod.Lex.lt_iff.mp s₂.2 with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    have h12 : (ofLex s₁.1).1 = (ofLex s₂.1).1 ∧ (ofLex s₁.1).2 = (ofLex s₂.1).2 := by
      by_cases h₁ : (ofLex s₁.1).1 < a <;> by_cases h₂ : (ofLex s₂.1).1 < a <;>
        simp [f, h₁, h₂] at hEq
      · exact ⟨hEq.1, hEq.2⟩
      · have e₁ : (ofLex s₁.1).1 = a := le_antisymm hle₁ (le_of_not_gt h₁)
        have e₂ : (ofLex s₂.1).1 = a := le_antisymm hle₂ (le_of_not_gt h₂)
        exact ⟨e₁.trans e₂.symm, hEq⟩
    exact Subtype.ext (ofLex.injective (Prod.ext h12.1 h12.2))
  have hcard : #(({b : Alpha // b < a} ⊕ Unit) × Fin 3) < 𝔠 := by
    have hfin3 : #(Fin 3) = 3 := by simp
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id,
      Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
      Cardinal.mk_punit, hfin3]
    have hadd : #{b : Alpha // b < a} + 1 < 𝔠 :=
      Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum (card_Iio_alpha a)
        (lt_of_lt_of_le (Cardinal.natCast_lt_aleph0 (n := 1)) Cardinal.aleph0_le_continuum)
    exact Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum hadd
      (lt_of_lt_of_le (Cardinal.natCast_lt_aleph0 (n := 3)) Cardinal.aleph0_le_continuum)
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hf) hcard

private lemma nonempty_diff_of_card_lt {α : Type*} {A B : Set α} (h : #B < #A) :
    (A \ B).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
  exact not_le_of_gt h (Cardinal.mk_le_mk_of_subset hne)

private lemma nonempty_compl_of_card_lt {α : Type*} {B : Set α} (h : #B < #α) :
    (Bᶜ).Nonempty := by
  have h' : #B < #(Set.univ : Set α) := by simpa [Cardinal.mk_univ] using h
  have hdiff : (Set.univ \ B).Nonempty := nonempty_diff_of_card_lt h'
  have heq : (Set.univ \ B : Set α) = Bᶜ := by ext x; simp
  rwa [heq] at hdiff

private noncomputable def buildStep (X : Alpha → ℝ) (Y : Alpha → E2) (P : Alpha → Req) :
    Idx → Option (ℝ × E2) :=
  WellFoundedLT.fix fun t rec =>
    let D : Set ℝ := {x | ∃ (s : Idx) (hs : s < t), ∃ y, rec s hs = some (x, y)}
    let R : Set E2 := {y | ∃ (s : Idx) (hs : s < t), ∃ x, rec s hs = some (x, y)}
    match (ofLex t).2 with
    | ⟨0, _⟩ =>
      let req := P (ofLex t).1
      let I : Set ℝ := Set.Ioo (req.1.1.1 : ℝ) (req.1.1.2 : ℝ)
      let C : Set E2 := req.2.1
      if h : (I \ D).Nonempty ∧ (C \ R).Nonempty then
        some (h.1.some, h.2.some)
      else none
    | ⟨1, _⟩ =>
      let x := X (ofLex t).1
      if h : x ∉ D ∧ (Rᶜ).Nonempty then
        some (x, h.2.some)
      else none
    | ⟨2, _⟩ =>
      let y := Y (ofLex t).1
      if h : y ∉ R ∧ (Dᶜ).Nonempty then
        some (h.2.some, y)
      else none

private def domBefore (step : Idx → Option (ℝ × E2)) (t : Idx) : Set ℝ :=
  {x | ∃ (s : Idx), ∃ (_ : s < t), ∃ y, step s = some (x, y)}

private def rngBefore (step : Idx → Option (ℝ × E2)) (t : Idx) : Set E2 :=
  {y | ∃ (s : Idx), ∃ (_ : s < t), ∃ x, step s = some (x, y)}

private lemma card_domBefore_lt (step : Idx → Option (ℝ × E2)) (t : Idx) :
    #(domBefore step t) < 𝔠 := by
  let g : domBefore step t → {s : Idx // s < t} := fun x =>
    ⟨x.2.choose, x.2.choose_spec.choose⟩
  have hg : Function.Injective g := by
    intro x₁ x₂ hEq
    have h₁ := x₁.2.choose_spec.choose_spec
    have h₂ := x₂.2.choose_spec.choose_spec
    rcases h₁ with ⟨y₁, hy₁⟩
    rcases h₂ with ⟨y₂, hy₂⟩
    have hs : x₁.2.choose = x₂.2.choose := congrArg Subtype.val hEq
    rw [hs] at hy₁
    have hpair := Option.some.inj (hy₁.symm.trans hy₂)
    exact Subtype.ext (congrArg Prod.fst hpair)
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hg) (card_Iio_idx t)

private lemma card_rngBefore_lt (step : Idx → Option (ℝ × E2)) (t : Idx) :
    #(rngBefore step t) < 𝔠 := by
  let g : rngBefore step t → {s : Idx // s < t} := fun y =>
    ⟨y.2.choose, y.2.choose_spec.choose⟩
  have hg : Function.Injective g := by
    intro y₁ y₂ hEq
    have h₁ := y₁.2.choose_spec.choose_spec
    have h₂ := y₂.2.choose_spec.choose_spec
    rcases h₁ with ⟨x₁, hx₁⟩
    rcases h₂ with ⟨x₂, hx₂⟩
    have hs : y₁.2.choose = y₂.2.choose := congrArg Subtype.val hEq
    rw [hs] at hx₁
    have hpair := Option.some.inj (hx₁.symm.trans hx₂)
    exact Subtype.ext (congrArg Prod.snd hpair)
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hg) (card_Iio_idx t)

private lemma buildStep_eq (X : Alpha → ℝ) (Y : Alpha → E2) (P : Alpha → Req) (t : Idx) :
    buildStep X Y P t =
      match (ofLex t).2 with
      | ⟨0, _⟩ =>
        let req := P (ofLex t).1
        let I : Set ℝ := Set.Ioo (req.1.1.1 : ℝ) (req.1.1.2 : ℝ)
        let C : Set E2 := req.2.1
        if h : (I \ domBefore (buildStep X Y P) t).Nonempty ∧
            (C \ rngBefore (buildStep X Y P) t).Nonempty then
          some (h.1.some, h.2.some)
        else none
      | ⟨1, _⟩ =>
        let x := X (ofLex t).1
        if h : x ∉ domBefore (buildStep X Y P) t ∧
            (rngBefore (buildStep X Y P) t)ᶜ.Nonempty then
          some (x, h.2.some)
        else none
      | ⟨2, _⟩ =>
        let y := Y (ofLex t).1
        if h : y ∉ rngBefore (buildStep X Y P) t ∧
            (domBefore (buildStep X Y P) t)ᶜ.Nonempty then
          some (h.2.some, y)
        else none := by
  conv_lhs => unfold buildStep
  rw [WellFoundedLT.fix_eq]
  rfl

private lemma buildStep_fresh (X : Alpha → ℝ) (Y : Alpha → E2) (P : Alpha → Req)
    {t : Idx} {x : ℝ} {y : E2} (h : buildStep X Y P t = some (x, y)) :
    x ∉ domBefore (buildStep X Y P) t ∧ y ∉ rngBefore (buildStep X Y P) t := by
  rw [buildStep_eq] at h
  rcases hidx : (ofLex t).2 with ⟨k, hk⟩
  rw [hidx] at h
  match k, hk with
  | 0, _ =>
    dsimp only at h
    split_ifs at h with h0
    have hpair := Option.some.inj h
    cases hpair
    exact ⟨h0.1.some_mem.2, h0.2.some_mem.2⟩
  | 1, _ =>
    dsimp only at h
    split_ifs at h with h1
    have hpair := Option.some.inj h
    cases hpair
    exact ⟨h1.1, h1.2.some_mem⟩
  | 2, _ =>
    dsimp only at h
    split_ifs at h with h2
    have hpair := Option.some.inj h
    cases hpair
    exact ⟨h2.2.some_mem, h2.1⟩

private lemma buildStep_unique_of_fst (X : Alpha → ℝ) (Y : Alpha → E2) (P : Alpha → Req)
    {s₁ s₂ : Idx} {x : ℝ} {y₁ y₂ : E2}
    (h₁ : buildStep X Y P s₁ = some (x, y₁))
    (h₂ : buildStep X Y P s₂ = some (x, y₂)) : y₁ = y₂ := by
  rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
  · exfalso
    exact (buildStep_fresh X Y P h₂).1 ⟨s₁, hlt, y₁, h₁⟩
  · exact congrArg Prod.snd (Option.some.inj (h₁.symm.trans h₂))
  · exfalso
    exact (buildStep_fresh X Y P h₁).1 ⟨s₂, hgt, y₂, h₂⟩

private lemma buildStep_unique_of_snd (X : Alpha → ℝ) (Y : Alpha → E2) (P : Alpha → Req)
    {s₁ s₂ : Idx} {x₁ x₂ : ℝ} {y : E2}
    (h₁ : buildStep X Y P s₁ = some (x₁, y))
    (h₂ : buildStep X Y P s₂ = some (x₂, y)) : x₁ = x₂ := by
  rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
  · exfalso
    exact (buildStep_fresh X Y P h₂).2 ⟨s₁, hlt, x₁, h₁⟩
  · exact congrArg Prod.fst (Option.some.inj (h₁.symm.trans h₂))
  · exfalso
    exact (buildStep_fresh X Y P h₁).2 ⟨s₂, hgt, x₂, h₂⟩

private lemma buildStep_hit_req (X : Alpha → ℝ) (Y : Alpha → E2) (P : Alpha → Req) (a : Alpha) :
    ∃ x ∈ Set.Ioo ((P a).1.1.1 : ℝ) ((P a).1.1.2 : ℝ),
      ∃ y ∈ (P a).2.1, buildStep X Y P (toLex (a, (0 : Fin 3))) = some (x, y) := by
  let t : Idx := toLex (a, (0 : Fin 3))
  have hI : ((Set.Ioo ((P a).1.1.1 : ℝ) ((P a).1.1.2 : ℝ)) \
      domBefore (buildStep X Y P) t).Nonempty := by
    apply nonempty_diff_of_card_lt
    have hlt : ((P a).1.1.1 : ℝ) < ((P a).1.1.2 : ℝ) := Rat.cast_lt.mpr (P a).1.2
    rw [Cardinal.mk_Ioo_real hlt]
    exact card_domBefore_lt (buildStep X Y P) t
  have hC : ((P a).2.1 \ rngBefore (buildStep X Y P) t).Nonempty := by
    apply nonempty_diff_of_card_lt
    exact lt_of_lt_of_le (card_rngBefore_lt (buildStep X Y P) t) (P a).2.2.2
  have hcond : ((Set.Ioo ((P a).1.1.1 : ℝ) ((P a).1.1.2 : ℝ)) \
      domBefore (buildStep X Y P) t).Nonempty ∧
      ((P a).2.1 \ rngBefore (buildStep X Y P) t).Nonempty := ⟨hI, hC⟩
  have heq : buildStep X Y P t = some (hcond.1.some, hcond.2.some) := by
    rw [buildStep_eq]
    dsimp only [t, ofLex_toLex]
    rw [dif_pos hcond]
  exact ⟨hcond.1.some, hcond.1.some_mem.1, hcond.2.some, hcond.2.some_mem.1, heq⟩

private lemma buildStep_hit_dom (X : Alpha → ℝ) (Y : Alpha → E2) (P : Alpha → Req) (a : Alpha) :
    ∃ s : Idx, ∃ y : E2, buildStep X Y P s = some (X a, y) := by
  let t : Idx := toLex (a, (1 : Fin 3))
  by_cases hmem : X a ∈ domBefore (buildStep X Y P) t
  · rcases hmem with ⟨s, _, y, hs⟩
    exact ⟨s, y, hs⟩
  · have hR : (rngBefore (buildStep X Y P) t)ᶜ.Nonempty := by
      apply nonempty_compl_of_card_lt
      rw [mk_E2]
      exact card_rngBefore_lt (buildStep X Y P) t
    have hcond : X a ∉ domBefore (buildStep X Y P) t ∧ (rngBefore (buildStep X Y P) t)ᶜ.Nonempty :=
      ⟨hmem, hR⟩
    have heq : buildStep X Y P t = some (X a, hcond.2.some) := by
      rw [buildStep_eq]
      dsimp only [t, ofLex_toLex]
      rw [dif_pos hcond]
    exact ⟨t, hcond.2.some, heq⟩

private lemma buildStep_hit_rng (X : Alpha → ℝ) (Y : Alpha → E2) (P : Alpha → Req) (a : Alpha) :
    ∃ s : Idx, ∃ x : ℝ, buildStep X Y P s = some (x, Y a) := by
  let t : Idx := toLex (a, (2 : Fin 3))
  by_cases hmem : Y a ∈ rngBefore (buildStep X Y P) t
  · rcases hmem with ⟨s, _, x, hs⟩
    exact ⟨s, x, hs⟩
  · have hD : (domBefore (buildStep X Y P) t)ᶜ.Nonempty := by
      apply nonempty_compl_of_card_lt
      rw [Cardinal.mk_real]
      exact card_domBefore_lt (buildStep X Y P) t
    have hcond : Y a ∉ rngBefore (buildStep X Y P) t ∧ (domBefore (buildStep X Y P) t)ᶜ.Nonempty :=
      ⟨hmem, hD⟩
    have heq : buildStep X Y P t = some (hcond.2.some, Y a) := by
      rw [buildStep_eq]
      dsimp only [t, ofLex_toLex]
      rw [dif_pos hcond]
    exact ⟨t, hcond.2.some, heq⟩

private lemma exists_bijection_hitting_all :
    ∃ f : ℝ ≃ E2, ∀ (p q : ℚ), p < q →
      ∀ (C : Set E2), IsClosed C → 𝔠 ≤ #C →
        ∃ x ∈ Set.Ioo (p : ℝ) (q : ℝ), f x ∈ C := by
  have hX_eq : #Alpha = #ℝ := by rw [mk_alpha, Cardinal.mk_real]
  have hY_eq : #Alpha = #E2 := by rw [mk_alpha, mk_E2]
  obtain ⟨eX⟩ := Cardinal.eq.mp hX_eq
  obtain ⟨eY⟩ := Cardinal.eq.mp hY_eq
  have hsum_eq : #(Req ⊕ Alpha) = #Alpha := by
    apply le_antisymm
    · rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, mk_alpha]
      calc
        #Req + 𝔠 ≤ 𝔠 + 𝔠 := add_le_add mk_req_le_continuum le_rfl
        _ = 𝔠 := Cardinal.add_eq_self Cardinal.aleph0_le_continuum
    · exact Cardinal.mk_le_of_injective Sum.inr_injective
  obtain ⟨eSum⟩ := Cardinal.eq.mp hsum_eq
  let r0 : Req := nonempty_req.some
  let P : Alpha → Req := fun a =>
    match eSum.symm a with
    | Sum.inl r => r
    | Sum.inr _ => r0
  have hP_surj : Function.Surjective P := fun r =>
    ⟨eSum (Sum.inl r), by simp [P]⟩
  let step := buildStep eX eY P
  have htot : ∀ x : ℝ, ∃ y : E2, ∃ s : Idx, step s = some (x, y) := by
    intro x
    obtain ⟨s, y, hs⟩ := buildStep_hit_dom eX eY P (eX.symm x)
    exact ⟨y, s, by simpa using hs⟩
  have hsurj : ∀ y : E2, ∃ x : ℝ, ∃ s : Idx, step s = some (x, y) := by
    intro y
    obtain ⟨s, x, hs⟩ := buildStep_hit_rng eX eY P (eY.symm y)
    exact ⟨x, s, by simpa using hs⟩
  let toFun : ℝ → E2 := fun x => (htot x).choose
  let invFun : E2 → ℝ := fun y => (hsurj y).choose
  have htoFun : ∀ x, ∃ s : Idx, step s = some (x, toFun x) := fun x => (htot x).choose_spec
  have hinvFun : ∀ y, ∃ s : Idx, step s = some (invFun y, y) := fun y => (hsurj y).choose_spec
  let f : ℝ ≃ E2 :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun x => by
        obtain ⟨s₁, h₁⟩ := hinvFun (toFun x)
        obtain ⟨s₂, h₂⟩ := htoFun x
        exact buildStep_unique_of_snd eX eY P h₁ h₂
      right_inv := fun y => by
        obtain ⟨s₁, h₁⟩ := htoFun (invFun y)
        obtain ⟨s₂, h₂⟩ := hinvFun y
        exact buildStep_unique_of_fst eX eY P h₁ h₂ }
  refine ⟨f, fun p q hpq C hC hcard => ?_⟩
  let req : Req := ⟨⟨(p, q), hpq⟩, ⟨C, hC, hcard⟩⟩
  obtain ⟨a, ha⟩ := hP_surj req
  obtain ⟨x, hxI, y, hyC, hstep⟩ := buildStep_hit_req eX eY P a
  rw [ha] at hxI hyC
  obtain ⟨s', hs'⟩ := htoFun x
  have hfxy : f x = y := buildStep_unique_of_fst eX eY P hs' hstep
  exact ⟨x, hxI, hfxy ▸ hyC⟩

private lemma continuum_le_mk_closedBall (z : E2) {r : ℝ} (hr : 0 < r) :
    𝔠 ≤ #(Metric.closedBall z r) := by
  let e0 : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0]
  have he0_norm : ‖e0‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [e0, Fin.sum_univ_two]
  let g : Set.Ioo (0 : ℝ) r → Metric.closedBall z r := fun t =>
    ⟨z + t.1 • e0, by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg t.2.1.le, he0_norm, mul_one]
      exact t.2.2.le⟩
  have hg : Function.Injective g := by
    intro t₁ t₂ hEq
    have hval : z + t₁.1 • e0 = z + t₂.1 • e0 := congrArg Subtype.val hEq
    have hsmul : t₁.1 • e0 = t₂.1 • e0 := add_left_cancel hval
    have h0 := congrArg (fun v : E2 => v 0) hsmul
    simp [e0] at h0
    exact Subtype.ext h0
  calc
    𝔠 = #(Set.Ioo (0 : ℝ) r) := (Cardinal.mk_Ioo_real hr).symm
    _ ≤ #(Metric.closedBall z r) := Cardinal.mk_le_of_injective hg

private lemma continuum_le_mk_compl_union {U V : Set E2} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) {y₁ y₂ : E2} (hy₁ : y₁ ∈ U) (hy₂ : y₂ ∈ V) :
    𝔠 ≤ #((U ∪ V)ᶜ : Set E2) := by
  have hne : y₁ ≠ y₂ := fun h => Set.disjoint_left.mp hUV hy₁ (h ▸ hy₂)
  let d : E2 := y₂ - y₁
  have hd_ne : d ≠ 0 := sub_ne_zero.mpr hne.symm
  let a : ℝ := d 0
  let b : ℝ := d 1
  have hab_pos : 0 < a ^ 2 + b ^ 2 := by
    by_contra hle
    push Not at hle
    have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    apply hd_ne
    ext i
    fin_cases i
    · exact ha0
    · exact hb0
  let w : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-b, a]
  have hw0 : w 0 = -b := rfl
  have hw1 : w 1 = a := rfl
  have hw_ne : w ≠ 0 := by
    intro hw
    have h0 : w 0 = 0 := by rw [hw]; rfl
    have h1 : w 1 = 0 := by rw [hw]; rfl
    rw [hw0] at h0
    rw [hw1] at h1
    nlinarith
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hV y₂ hy₂
  let δ : ℝ := r / ‖w‖
  have hδ_pos : 0 < δ := div_pos hr_pos hw_pos
  have hex : ∀ t : Set.Ioo (0 : ℝ) δ,
      ∃ u : ℝ, 0 < u ∧ y₁ + u • (d + t.1 • w) ∈ (U ∪ V)ᶜ := by
    intro t
    let p : E2 := y₂ + t.1 • w
    have hpV : p ∈ V := by
      apply hr_ball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg t.2.1.le]
      exact (lt_div_iff₀ hw_pos).mp t.2.2
    let γ : ℝ → E2 := fun u => y₁ + u • (d + t.1 • w)
    have hγ_cont : Continuous γ :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hconn : IsPreconnected (γ '' Set.Icc (0 : ℝ) 1) :=
      (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).isPreconnected.image γ hγ_cont.continuousOn
    have h0 : γ 0 = y₁ := by simp [γ]
    have h1 : γ 1 = p := by
      simp only [γ, one_smul, d, p]
      abel
    have hnot_sub : ¬ (γ '' Set.Icc (0 : ℝ) 1 ⊆ U ∪ V) := by
      intro hsub
      have hneU : (γ '' Set.Icc (0 : ℝ) 1 ∩ U).Nonempty :=
        ⟨y₁, ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩, hy₁⟩
      have hneV : (γ '' Set.Icc (0 : ℝ) 1 ∩ V).Nonempty :=
        ⟨p, ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩, hpV⟩
      obtain ⟨z, _, hzU, hzV⟩ := hconn U V hU hV hsub hneU hneV
      exact Set.disjoint_left.mp hUV hzU hzV
    rw [Set.not_subset] at hnot_sub
    obtain ⟨z, ⟨u, huIcc, rfl⟩, hz_not⟩ := hnot_sub
    have hu_pos : 0 < u := by
      rcases eq_or_lt_of_le huIcc.1 with rfl | hlt
      · exfalso
        exact hz_not (Or.inl (h0 ▸ hy₁))
      · exact hlt
    exact ⟨u, hu_pos, hz_not⟩
  let g : Set.Ioo (0 : ℝ) δ → ((U ∪ V)ᶜ : Set E2) := fun t =>
    ⟨y₁ + (hex t).choose • (d + t.1 • w), (hex t).choose_spec.2⟩
  have hg : Function.Injective g := by
    intro t₁ t₂ hEq
    set u₁ := (hex t₁).choose
    set u₂ := (hex t₂).choose
    have hu₁ : 0 < u₁ := (hex t₁).choose_spec.1
    have hval : y₁ + u₁ • (d + t₁.1 • w) = y₁ + u₂ • (d + t₂.1 • w) := congrArg Subtype.val hEq
    have hvec : u₁ • (d + t₁.1 • w) = u₂ • (d + t₂.1 • w) := add_left_cancel hval
    have hc0 : u₁ * (a + t₁.1 * (-b)) = u₂ * (a + t₂.1 * (-b)) := by
      have h := congrArg (fun v : E2 => v 0) hvec
      simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, hw0] at h
      linarith
    have hc1 : u₁ * (b + t₁.1 * a) = u₂ * (b + t₂.1 * a) := by
      have h := congrArg (fun v : E2 => v 1) hvec
      simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, hw1] at h
      linarith
    have hu_eq : u₁ = u₂ := by
      have h1 : a * (u₁ * (a + t₁.1 * (-b))) + b * (u₁ * (b + t₁.1 * a)) =
                a * (u₂ * (a + t₂.1 * (-b))) + b * (u₂ * (b + t₂.1 * a)) := by
        rw [hc0, hc1]
      have hcomb : (u₁ - u₂) * (a ^ 2 + b ^ 2) = 0 := by linarith
      rcases mul_eq_zero.mp hcomb with h | h
      · linarith
      · linarith
    have ht_eq : t₁.1 = t₂.1 := by
      rw [hu_eq] at hc0 hc1
      have h1 : (-b) * (u₂ * (a + t₁.1 * (-b))) + a * (u₂ * (b + t₁.1 * a)) =
                (-b) * (u₂ * (a + t₂.1 * (-b))) + a * (u₂ * (b + t₂.1 * a)) := by
        rw [hc0, hc1]
      have hcomb : u₂ * (t₁.1 - t₂.1) * (a ^ 2 + b ^ 2) = 0 := by linarith
      rcases mul_eq_zero.mp hcomb with h | h
      · rcases mul_eq_zero.mp h with hu2 | ht
        · linarith
        · linarith
      · linarith
    exact Subtype.ext ht_eq
  calc
    𝔠 = #(Set.Ioo (0 : ℝ) δ) := (Cardinal.mk_Ioo_real hδ_pos).symm
    _ ≤ #((U ∪ V)ᶜ : Set E2) := Cardinal.mk_le_of_injective hg

private lemma isConnectedMap_of_hitting {f : ℝ ≃ E2}
    (hHit : ∀ (p q : ℚ), p < q → ∀ (C : Set E2), IsClosed C → 𝔠 ≤ #C →
      ∃ x ∈ Set.Ioo (p : ℝ) (q : ℝ), f x ∈ C) :
    IsConnectedMap f := by
  intro s hs
  by_cases hsub : s.Subsingleton
  · rcases hs.1 with ⟨a, ha⟩
    have hseq : s = {a} := Set.Subset.antisymm (fun x hx => hsub hx ha) (Set.singleton_subset_iff.mpr ha)
    rw [hseq, Set.image_singleton]
    exact isConnected_singleton
  · rw [Set.not_subsingleton_iff] at hsub
    obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := hsub
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ s, ∃ b ∈ s, a < b := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨x₁, hx₁, x₂, hx₂, hlt⟩
      · exact ⟨x₂, hx₂, x₁, hx₁, hgt⟩
    obtain ⟨p, hap, hpb⟩ := exists_rat_btwn hab
    obtain ⟨q, hpq, hqb⟩ := exists_rat_btwn hpb
    have hpq_rat : p < q := Rat.cast_lt.mp hpq
    have hIoo_sub : Set.Ioo (p : ℝ) (q : ℝ) ⊆ s := by
      intro x hx
      exact (isConnected_iff_ordConnected_and_nonempty.mp hs).1.out ha hb
        ⟨(hap.trans hx.1).le, (hx.2.trans hqb).le⟩
    refine ⟨hs.1.image f, ?_⟩
    intro U V hU hV hsubUV hneU hneV
    by_cases hUV : (U ∩ V).Nonempty
    · obtain ⟨z, hz⟩ := hUV
      obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp (hU.inter hV) z hz
      have hcb_sub : Metric.closedBall z (r / 2) ⊆ U ∩ V :=
        (Metric.closedBall_subset_ball (half_lt_self hr_pos)).trans hr_ball
      obtain ⟨x, hxIoo, hfx⟩ :=
        hHit p q hpq_rat (Metric.closedBall z (r / 2)) Metric.isClosed_closedBall
          (continuum_le_mk_closedBall z (half_pos hr_pos))
      exact ⟨f x, ⟨x, hIoo_sub hxIoo, rfl⟩, hcb_sub hfx⟩
    · exfalso
      have hdisj : Disjoint U V :=
        Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hUV)
      obtain ⟨y₁, _, hy₁U⟩ := hneU
      obtain ⟨y₂, _, hy₂V⟩ := hneV
      obtain ⟨x, hxIoo, hfx⟩ :=
        hHit p q hpq_rat (U ∪ V)ᶜ (hU.union hV).isClosed_compl
          (continuum_le_mk_compl_union hU hV hdisj hy₁U hy₂V)
      exact hfx (hsubUV ⟨x, hIoo_sub hxIoo, rfl⟩)

private lemma not_isConnectedMap_symm (f : ℝ ≃ E2) : ¬ IsConnectedMap f.symm := by
  intro hf
  have hrank : 1 < Module.rank ℝ E2 := by
    have hfin : Module.finrank ℝ E2 = 2 := by simp [E2]
    rw [← Module.finrank_eq_rank, hfin]
    norm_num
  have hconn : IsConnected ({(0 : E2)}ᶜ : Set E2) :=
    isConnected_compl_singleton_of_one_lt_rank hrank 0
  have himg : IsConnected (f.symm '' {(0 : E2)}ᶜ) := hf hconn
  have heq : f.symm '' {(0 : E2)}ᶜ = {f.symm 0}ᶜ := by
    ext x
    simp only [Equiv.image_symm_eq_preimage, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    constructor
    · intro h hx
      apply h
      rw [hx, Equiv.apply_symm_apply]
    · intro h hx
      apply h
      rw [← hx, Equiv.symm_apply_apply]
  rw [heq, isConnected_iff_ordConnected_and_nonempty] at himg
  let x₀ : ℝ := f.symm 0
  have h1 : x₀ - 1 ∈ ({x₀}ᶜ : Set ℝ) := by simp
  have h2 : x₀ + 1 ∈ ({x₀}ᶜ : Set ℝ) := by simp
  have hmem : x₀ ∈ ({x₀}ᶜ : Set ℝ) :=
    himg.1.out h1 h2 ⟨by linarith, by linarith⟩
  exact hmem rfl

end OMA.MO260589

theorem OMA.solution : type_of% @Mathoverflow235893.mathoverflow_260589 := by
  obtain ⟨f, hHit⟩ := OMA.MO260589.exists_bijection_hitting_all
  exact ⟨f, OMA.MO260589.isConnectedMap_of_hitting hHit, OMA.MO260589.not_isConnectedMap_symm f⟩
