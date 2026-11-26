import FormalConjectures.ErdosProblems.«590»
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Proof of Specker's Theorem (`Erdos590.erdos_590.variants.ge_three_false`)

Proves `¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3` for all `n ≥ 3` following Specker (1957).
We realize `ω ^ n` as the nested lexicographic product `NatTuple n` of `n` copies of `ULift ℕ`,
define a triangle-free blue graph via the first three strictly increasing partial sums
`p₀ < p₁ < p₂` (`p₁ x < p₀ y < p₂ x < p₁ y`), and show via a fiber-order-type lemma that
every subset of order type `ω ^ n` contains a blue edge.
-/

namespace OMA.Erdos590GeThreeFalse

open Cardinal Ordinal

universe u

abbrev NatTuple : ℕ → Type u
  | 0 => PUnit.{u + 1}
  | n + 1 => ULift.{u} ℕ ×ₗ NatTuple n

instance instLinearOrderNatTuple : ∀ n, LinearOrder (NatTuple.{u} n)
  | 0 => inferInstanceAs (LinearOrder PUnit.{u + 1})
  | n + 1 =>
      letI := instLinearOrderNatTuple n
      inferInstanceAs (LinearOrder (ULift.{u} ℕ ×ₗ NatTuple.{u} n))

private lemma wellFoundedLT_natTuple (n : ℕ) : WellFoundedLT (NatTuple.{u} n) := by
  induction n with
  | zero => exact inferInstanceAs (WellFoundedLT PUnit.{u + 1})
  | succ n ih => exact inferInstanceAs (WellFoundedLT (ULift.{u} ℕ ×ₗ NatTuple.{u} n))

instance instWellFoundedLTNatTuple (n : ℕ) : WellFoundedLT (NatTuple.{u} n) :=
  wellFoundedLT_natTuple n

private lemma typeLT_prodLex {α β : Type u} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] :
    typeLT (α ×ₗ β) = (typeLT β) * (typeLT α) := by
  have e : ((· < ·) : (α ×ₗ β) → (α ×ₗ β) → Prop) ≃r
      Prod.Lex ((· < ·) : α → α → Prop) ((· < ·) : β → β → Prop) :=
    { toEquiv := ofLex
      map_rel_iff' := by
        intro x y
        rfl }
  rw [e.ordinalType_congr, Ordinal.type_prod_lex]

private lemma typeLT_ulift_nat : typeLT (ULift.{u} ℕ) = (ω : Ordinal.{u}) := by
  change Ordinal.type (ULift.down ⁻¹'o ((· < ·) : ℕ → ℕ → Prop)) = (ω : Ordinal.{u})
  rw [Ordinal.type_ulift, Ordinal.type_nat_lt, Ordinal.lift_omega0]

private lemma typeLT_ulift_fin (m : ℕ) : typeLT (ULift.{u} (Fin m)) = (m : Ordinal.{u}) := by
  change Ordinal.type (ULift.down ⁻¹'o ((· < ·) : Fin m → Fin m → Prop)) = (m : Ordinal.{u})
  rw [Ordinal.type_ulift, Ordinal.type_fin, Ordinal.lift_natCast]

private lemma typeLT_natTuple (n : ℕ) : typeLT (NatTuple.{u} n) = (ω : Ordinal.{u}) ^ n := by
  induction n with
  | zero =>
    change typeLT PUnit.{u + 1} = 1
    exact Ordinal.type_eq_one_of_unique _
  | succ n ih =>
    change typeLT (ULift.{u} ℕ ×ₗ NatTuple.{u} n) = (ω : Ordinal.{u}) ^ (n + 1)
    rw [typeLT_prodLex, ih, typeLT_ulift_nat, pow_succ]

private def relEmbedding_of_strictMono {α β : Type u} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : StrictMono f) :
    ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  ⟨⟨f, hf.injective⟩, hf.lt_iff_lt⟩

private lemma typeLT_le_of_strictMono {α β : Type u} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (f : α → β) (hf : StrictMono f) :
    typeLT α ≤ typeLT β :=
  Ordinal.type_le_iff'.2 ⟨relEmbedding_of_strictMono f hf⟩

private lemma natTuple_lt_iff {k : ℕ} {x y : NatTuple.{u} (k + 1)} :
    x < y ↔ (ofLex x).1.down < (ofLex y).1.down ∨
      ((ofLex x).1.down = (ofLex y).1.down ∧ (ofLex x).2 < (ofLex y).2) := by
  change Prod.Lex (· < ·) (· < ·) (ofLex x) (ofLex y) ↔ _
  rw [Prod.lex_def]
  constructor
  · rintro (h | ⟨heq, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨congrArg ULift.down heq, h⟩
  · rintro (h | ⟨heq, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ULift.ext _ _ heq, h⟩

private lemma split_typeLT_le {k : ℕ} (A : Set (NatTuple.{u} (k + 1))) (M : ℕ) :
    typeLT A ≤
      typeLT ({x : NatTuple.{u} (k + 1) | x ∈ A ∧ (ofLex x).1.down < M} : Set _) +
      typeLT ({x : NatTuple.{u} (k + 1) | x ∈ A ∧ M ≤ (ofLex x).1.down} : Set _) := by
  let Alo : Set (NatTuple.{u} (k + 1)) := {x | x ∈ A ∧ (ofLex x).1.down < M}
  let Ahi : Set (NatTuple.{u} (k + 1)) := {x | x ∈ A ∧ M ≤ (ofLex x).1.down}
  rw [← Ordinal.type_sum_lex]
  let f : A → Alo ⊕ Ahi := fun x =>
    if h : (ofLex x.1).1.down < M then
      Sum.inl ⟨x.1, x.2, h⟩
    else
      Sum.inr ⟨x.1, x.2, Nat.le_of_not_lt h⟩
  have hf_lt : ∀ {x y : A}, x < y →
      Sum.Lex ((· < ·) : Alo → Alo → Prop) ((· < ·) : Ahi → Ahi → Prop) (f x) (f y) := by
    intro x y hxy
    dsimp only [f]
    split_ifs with hx hy hy
    · exact Sum.Lex.inl hxy
    · exact Sum.Lex.sep _ _
    · exfalso
      have hle : (ofLex x.1).1.down ≤ (ofLex y.1).1.down := by
        rcases natTuple_lt_iff.1 hxy with h1 | ⟨h1, _⟩
        · exact Nat.le_of_lt h1
        · exact h1.le
      omega
    · exact Sum.Lex.inr hxy
  have hf_inj : Function.Injective f := by
    intro x y hxy
    dsimp only [f] at hxy
    split_ifs at hxy with hx hy hy
    · simp only [Sum.inl.injEq, Subtype.mk.injEq] at hxy
      exact Subtype.ext hxy
    · simp only [Sum.inr.injEq, Subtype.mk.injEq] at hxy
      exact Subtype.ext hxy
  refine Ordinal.type_le_iff'.2 ⟨⟨⟨f, hf_inj⟩, ?_⟩⟩
  intro x y
  constructor
  · intro h
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · exact hlt
    · exfalso
      exact irrefl (f x) h
    · exfalso
      exact asymm h (hf_lt hgt)
  · exact hf_lt

private lemma lo_typeLT_le {k : ℕ} (A : Set (NatTuple.{u} (k + 1))) (M : ℕ) :
    typeLT ({x : NatTuple.{u} (k + 1) | x ∈ A ∧ (ofLex x).1.down < M} : Set _) ≤
      (ω : Ordinal.{u}) ^ k * (M : Ordinal.{u}) := by
  have htype : typeLT (ULift.{u} (Fin M) ×ₗ NatTuple.{u} k) =
      (ω : Ordinal.{u}) ^ k * (M : Ordinal.{u}) := by
    rw [typeLT_prodLex, typeLT_natTuple, typeLT_ulift_fin]
  rw [← htype]
  let f : {x : NatTuple.{u} (k + 1) | x ∈ A ∧ (ofLex x).1.down < M} →
      ULift.{u} (Fin M) ×ₗ NatTuple.{u} k :=
    fun x => toLex (ULift.up ⟨(ofLex x.1).1.down, x.2.2⟩, (ofLex x.1).2)
  apply typeLT_le_of_strictMono f
  intro x y hxy
  change Prod.Lex (· < ·) (· < ·) (ofLex (f x)) (ofLex (f y))
  rw [Prod.lex_def]
  rcases natTuple_lt_iff.1 hxy with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨?_, h2⟩
    apply ULift.ext
    exact Fin.ext h1

private lemma fiber_large_exists {k : ℕ} (A : Set (NatTuple.{u} (k + 1)))
    (hA : (ω : Ordinal.{u}) ^ (k + 1) ≤ typeLT A) (M : ℕ) :
    ∃ a : ℕ, M ≤ a ∧
      (ω : Ordinal.{u}) ^ k ≤
        typeLT ({u : NatTuple.{u} k | toLex (ULift.up a, u) ∈ A} : Set _) := by
  by_contra h
  push Not at h
  let Ahi : Set (NatTuple.{u} (k + 1)) := {x | x ∈ A ∧ M ≤ (ofLex x).1.down}
  have hhi : typeLT Ahi ≤ (ω : Ordinal.{u}) ^ k := by
    cases k with
    | zero =>
      have hemp : IsEmpty Ahi := by
        refine ⟨fun x => ?_⟩
        have hlt := h (ofLex x.1).1.down x.2.2
        have hmem : (ofLex x.1).2 ∈
            ({u : NatTuple.{u} 0 | toLex (ULift.up (ofLex x.1).1.down, u) ∈ A} : Set _) :=
          x.2.1
        have hne : typeLT ({u : NatTuple.{u} 0 | toLex (ULift.up (ofLex x.1).1.down, u) ∈ A} : Set _) ≠ 0 :=
          Ordinal.type_ne_zero_iff_nonempty.2 ⟨⟨_, hmem⟩⟩
        rw [pow_zero] at hlt
        exact hne (Order.lt_one_iff.1 hlt)
      rw [Ordinal.type_eq_zero_of_empty]
      exact zero_le
    | succ j =>
      have hex : ∀ a : ℕ, ∃ c : ℕ, M ≤ a → Nonempty
            (((· < ·) :
                ({u : NatTuple.{u} (j + 1) | toLex (ULift.up a, u) ∈ A} : Set _) → _ → Prop) ↪r
              ((· < ·) : (ULift.{u} (Fin c) ×ₗ NatTuple.{u} j) → _ → Prop)) := by
        intro a
        by_cases ha : M ≤ a
        · have hlt : typeLT ({u : NatTuple.{u} (j + 1) | toLex (ULift.up a, u) ∈ A} : Set _) <
              (ω : Ordinal.{u}) ^ Order.succ (j : Ordinal.{u}) := by
            have h1 := h a ha
            rw [← Ordinal.opow_natCast, Nat.cast_succ] at h1
            rw [Order.succ_eq_add_one]
            exact h1
          obtain ⟨c, hc⟩ := Ordinal.lt_omega0_opow_succ.1 hlt
          refine ⟨c, fun _ => Ordinal.type_le_iff'.1 ?_⟩
          rw [typeLT_prodLex, typeLT_natTuple, typeLT_ulift_fin]
          rw [Ordinal.opow_natCast] at hc
          exact hc.le
        · exact ⟨0, fun h' => (ha h').elim⟩
      classical
      let c : ℕ → ℕ := fun a => (hex a).choose
      let emb : ∀ a (ha : M ≤ a),
          ((· < ·) :
              ({u : NatTuple.{u} (j + 1) | toLex (ULift.up a, u) ∈ A} : Set _) → _ → Prop) ↪r
            ((· < ·) : (ULift.{u} (Fin (c a)) ×ₗ NatTuple.{u} j) → _ → Prop) :=
        fun a ha => Classical.choice ((hex a).choose_spec ha)
      let S : ℕ → ℕ := fun a => ∑ i ∈ Finset.Ico M a, c i
      have hS_step : ∀ a, M ≤ a → S a + c a = S (a + 1) := by
        intro a ha
        dsimp only [S]
        rw [Finset.sum_Ico_succ_top ha]
      have hS_mono : ∀ {a b}, M ≤ a → a ≤ b → S a ≤ S b := by
        intro a b _ hab
        dsimp only [S]
        exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hab)
      have htype : typeLT (ULift.{u} ℕ ×ₗ NatTuple.{u} j) = (ω : Ordinal.{u}) ^ (j + 1) := by
        rw [typeLT_prodLex, typeLT_natTuple, typeLT_ulift_nat, pow_succ]
      rw [← htype]
      let g : Ahi → ULift.{u} ℕ ×ₗ NatTuple.{u} j := fun x =>
        let a := (ofLex x.1).1.down
        let ha : M ≤ a := x.2.2
        let u : {u : NatTuple.{u} (j + 1) | toLex (ULift.up a, u) ∈ A} :=
          ⟨(ofLex x.1).2, x.2.1⟩
        let p := ofLex (emb a ha u)
        toLex (ULift.up (S a + p.1.down.val), p.2)
      apply typeLT_le_of_strictMono g
      intro x y hxy
      apply natTuple_lt_iff.2
      rcases natTuple_lt_iff.1 hxy with h1 | ⟨h1, h2⟩
      · left
        change S (ofLex x.1).1.down + _ < S (ofLex y.1).1.down + _
        have hp : (ofLex (emb (ofLex x.1).1.down x.2.2
            ⟨(ofLex x.1).2, x.2.1⟩)).1.down.val < c (ofLex x.1).1.down :=
          (ofLex (emb (ofLex x.1).1.down x.2.2 ⟨(ofLex x.1).2, x.2.1⟩)).1.down.isLt
        have hxM : M ≤ (ofLex x.1).1.down := x.2.2
        have hstep := hS_step (ofLex x.1).1.down hxM
        have hmon := hS_mono (by omega : M ≤ (ofLex x.1).1.down + 1)
          (by omega : (ofLex x.1).1.down + 1 ≤ (ofLex y.1).1.down)
        omega
      · cases x with
        | mk xval hx =>
          cases y with
          | mk yval hy =>
            rcases xval with ⟨⟨a⟩, u₁⟩
            rcases yval with ⟨⟨b⟩, u₂⟩
            dsimp only at h1 h2
            subst h1
            have hemb : emb a hx.2 ⟨u₁, hx.1⟩ < emb a hx.2 ⟨u₂, hy.1⟩ :=
              (emb a hx.2).map_rel_iff.2 h2
            change Prod.Lex (· < ·) (· < ·)
              (ofLex (emb a hx.2 ⟨u₁, hx.1⟩)) (ofLex (emb a hx.2 ⟨u₂, hy.1⟩)) at hemb
            rw [Prod.lex_def] at hemb
            rcases hemb with he1 | ⟨he1, he2⟩
            · left
              change S a + _ < S a + _
              exact Nat.add_lt_add_left he1 (S a)
            · right
              refine ⟨?_, he2⟩
              change S a + _ = S a + _
              exact congrArg (fun z : ULift (Fin (c a)) => S a + z.down.val) he1
  have hsum : typeLT A ≤ (ω : Ordinal.{u}) ^ k * (M : Ordinal.{u}) + (ω : Ordinal.{u}) ^ k :=
    (split_typeLT_le A M).trans (add_le_add (lo_typeLT_le A M) hhi)
  have hlt : (ω : Ordinal.{u}) ^ k * (M : Ordinal.{u}) + (ω : Ordinal.{u}) ^ k <
      (ω : Ordinal.{u}) ^ (k + 1) := by
    calc
      (ω : Ordinal.{u}) ^ k * (M : Ordinal.{u}) + (ω : Ordinal.{u}) ^ k
          = (ω : Ordinal.{u}) ^ k * ((M : Ordinal.{u}) + 1) := by rw [mul_add, mul_one]
      _ = (ω : Ordinal.{u}) ^ k * ((M + 1 : ℕ) : Ordinal.{u}) := by simp
      _ < (ω : Ordinal.{u}) ^ k * (ω : Ordinal.{u}) :=
        mul_lt_mul_of_pos_left (Ordinal.natCast_lt_omega0 (M + 1)) (pow_pos Ordinal.omega0_pos k)
      _ = (ω : Ordinal.{u}) ^ (k + 1) := by rw [pow_succ]
  exact not_lt_of_ge hA (lt_of_le_of_lt hsum hlt)

private def coord0 {m : ℕ} (x : NatTuple.{u} (m + 3)) : ℕ :=
  (ofLex x).1.down

private def coord1 {m : ℕ} (x : NatTuple.{u} (m + 3)) : ℕ :=
  (ofLex (ofLex x).2).1.down

private def coord2 {m : ℕ} (x : NatTuple.{u} (m + 3)) : ℕ :=
  (ofLex (ofLex (ofLex x).2).2).1.down

private def p0 {m : ℕ} (x : NatTuple.{u} (m + 3)) : ℕ :=
  coord0 x

private def p1 {m : ℕ} (x : NatTuple.{u} (m + 3)) : ℕ :=
  coord0 x + 1 + coord1 x

private def p2 {m : ℕ} (x : NatTuple.{u} (m + 3)) : ℕ :=
  coord0 x + 1 + coord1 x + 1 + coord2 x

private def speckerRel {m : ℕ} (x y : NatTuple.{u} (m + 3)) : Prop :=
  p1 x < p0 y ∧ p0 y < p2 x ∧ p2 x < p1 y

private lemma speckerRel_lt {m : ℕ} {x y : NatTuple.{u} (m + 3)} (h : speckerRel x y) :
    x < y := by
  apply natTuple_lt_iff.2
  left
  have := h.1
  dsimp only [p0, p1, coord0] at this
  omega

private def speckerBlue (m : ℕ) : SimpleGraph (NatTuple.{u} (m + 3)) where
  Adj x y := speckerRel x y ∨ speckerRel y x
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun x h => by rcases h with h | h <;> exact lt_irrefl x (speckerRel_lt h)⟩

private lemma speckerBlue_no_triangle (m : ℕ) :
    ¬ ∃ s : Set (NatTuple.{u} (m + 3)), (speckerBlue m).IsClique s ∧ #s = 3 := by
  rintro ⟨s, hcl, hcard⟩
  have h3 : (3 : Cardinal.{u}) ≤ #s := hcard.ge
  have h1 : (1 : Cardinal.{u}) < #s := lt_of_lt_of_le (by norm_num) h3
  have h2 : (2 : Cardinal.{u}) < #s := lt_of_lt_of_le (by norm_num) h3
  have hs_ne : s.Nonempty := Set.nonempty_coe_sort.1 (Cardinal.mk_ne_zero_iff.1 (by
    intro h0
    rw [h0] at hcard
    norm_num at hcard))
  obtain ⟨u, hu⟩ := hs_ne
  have hsu : (s \ {u}).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
    have hle : #s ≤ #({u} : Set (NatTuple.{u} (m + 3))) := Cardinal.mk_le_mk_of_subset hemp
    rw [Cardinal.mk_singleton] at hle
    exact not_lt_of_ge hle h1
  obtain ⟨v, hv, hvu⟩ := hsu
  have hsuv : (s \ {u, v}).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
    have hle : #s ≤ #({u, v} : Set (NatTuple.{u} (m + 3))) := Cardinal.mk_le_mk_of_subset hemp
    have h2' : #({u, v} : Set (NatTuple.{u} (m + 3))) ≤ 2 := by
      let su : Set (NatTuple.{u} (m + 3)) := {u}
      let sv : Set (NatTuple.{u} (m + 3)) := {v}
      have hunion : ({u, v} : Set (NatTuple.{u} (m + 3))) = su ∪ sv := by
        ext x
        simp [su, sv, or_comm]
      rw [hunion]
      calc
        #(su ∪ sv : Set (NatTuple.{u} (m + 3))) ≤ #su + #sv := Cardinal.mk_union_le su sv
        _ = 1 + 1 := by simp [su, sv]
        _ = 2 := by norm_num
    exact not_lt_of_ge (hle.trans h2') h2
  obtain ⟨w, hw, hwuv⟩ := hsuv
  have hw_u : w ≠ u := fun h => hwuv (Or.inl h)
  have hw_v : w ≠ v := fun h => hwuv (Or.inr h)
  have htriple : ∀ x y z : NatTuple.{u} (m + 3),
      x ∈ s → y ∈ s → z ∈ s → x < y → y < z → False := by
    intro x y z hx hy hz hxy hyz
    have hxz : x < z := lt_trans hxy hyz
    have h1' : speckerRel x y := by
      rcases hcl hx hy (ne_of_lt hxy) with h | h
      · exact h
      · exact (lt_asymm hxy (speckerRel_lt h)).elim
    have h2' : speckerRel y z := by
      rcases hcl hy hz (ne_of_lt hyz) with h | h
      · exact h
      · exact (lt_asymm hyz (speckerRel_lt h)).elim
    have h3' : speckerRel x z := by
      rcases hcl hx hz (ne_of_lt hxz) with h | h
      · exact h
      · exact (lt_asymm hxz (speckerRel_lt h)).elim
    have := h1'.2.2
    have := h2'.1
    have := h3'.2.1
    omega
  rcases lt_or_gt_of_ne hvu with hvu' | huv'
  · rcases lt_or_gt_of_ne hw_v with hwv | hvw
    · exact htriple w v u hw hv hu hwv hvu'
    · rcases lt_or_gt_of_ne hw_u with hwu | huw
      · exact htriple v w u hv hw hu hvw hwu
      · exact htriple v u w hv hu hw hvu' huw
  · rcases lt_or_gt_of_ne hw_u with hwu | huw
    · exact htriple w u v hw hu hv hwu huv'
    · rcases lt_or_gt_of_ne hw_v with hwv | hvw
      · exact htriple u w v hu hw hv huw hwv
      · exact htriple u v w hu hv hw huv' hvw

private lemma speckerRed_no_omega_pow (m : ℕ) :
    ¬ ∃ s : Set (NatTuple.{u} (m + 3)),
      (speckerBlue m)ᶜ.IsClique s ∧ typeLT s = (ω : Ordinal.{u}) ^ (m + 3) := by
  rintro ⟨s, hcl, htype⟩
  obtain ⟨a0, _, ha0⟩ := fiber_large_exists (k := m + 2) s htype.ge 0
  let S0 : Set (NatTuple.{u} (m + 2)) := {u | toLex (ULift.up a0, u) ∈ s}
  obtain ⟨a1, _, ha1⟩ := fiber_large_exists (k := m + 1) S0 ha0 0
  let S01 : Set (NatTuple.{u} (m + 1)) := {u | toLex (ULift.up a1, u) ∈ S0}
  obtain ⟨b0, hb0_ge, hb0⟩ := fiber_large_exists (k := m + 2) s htype.ge (a0 + 1 + a1 + 1)
  let T0 : Set (NatTuple.{u} (m + 2)) := {u | toLex (ULift.up b0, u) ∈ s}
  obtain ⟨a2, ha2_ge, ha2⟩ := fiber_large_exists (k := m) S01 ha1 (b0 + 1)
  have hS012_ne : ({u : NatTuple.{u} m | toLex (ULift.up a2, u) ∈ S01} : Set _).Nonempty := by
    have hpos : (0 : Ordinal.{u}) <
        typeLT ({u : NatTuple.{u} m | toLex (ULift.up a2, u) ∈ S01} : Set _) :=
      lt_of_lt_of_le (pow_pos Ordinal.omega0_pos m) ha2
    obtain ⟨⟨t, ht⟩⟩ := Ordinal.type_ne_zero_iff_nonempty.1 hpos.ne'
    exact ⟨t, ht⟩
  obtain ⟨t1, ht1⟩ := hS012_ne
  let x : NatTuple.{u} (m + 3) :=
    toLex (ULift.up a0, toLex (ULift.up a1, toLex (ULift.up a2, t1)))
  have hx : x ∈ s := ht1
  obtain ⟨b1, hb1_ge, hb1⟩ := fiber_large_exists (k := m + 1) T0 hb0 (p2 x + 1)
  have hT01_ne : ({u : NatTuple.{u} (m + 1) | toLex (ULift.up b1, u) ∈ T0} : Set _).Nonempty := by
    have hpos : (0 : Ordinal.{u}) <
        typeLT ({u : NatTuple.{u} (m + 1) | toLex (ULift.up b1, u) ∈ T0} : Set _) :=
      lt_of_lt_of_le (pow_pos Ordinal.omega0_pos (m + 1)) hb1
    obtain ⟨⟨t, ht⟩⟩ := Ordinal.type_ne_zero_iff_nonempty.1 hpos.ne'
    exact ⟨t, ht⟩
  obtain ⟨t2, ht2⟩ := hT01_ne
  let y : NatTuple.{u} (m + 3) :=
    toLex (ULift.up b0, toLex (ULift.up b1, t2))
  have hy : y ∈ s := ht2
  have hrel : speckerRel x y := by
    refine ⟨?_, ?_, ?_⟩
    · change a0 + 1 + a1 < b0
      omega
    · change b0 < a0 + 1 + a1 + 1 + a2
      omega
    · change p2 x < b0 + 1 + b1
      omega
  have hne : x ≠ y := ne_of_lt (speckerRel_lt hrel)
  have hred : (speckerBlue m)ᶜ.Adj x y := hcl hx hy hne
  exact hred.2 (Or.inl hrel)

end OMA.Erdos590GeThreeFalse

open Cardinal Ordinal in
theorem OMA.solution : type_of% @Erdos590.erdos_590.variants.ge_three_false := by
  intro n hn hram
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have htype : typeLT (((Ordinal.omega0 : Ordinal.{_}) ^ (m + 3)).ToType) =
      typeLT (OMA.Erdos590GeThreeFalse.NatTuple (m + 3)) := by
    rw [Ordinal.type_toType, OMA.Erdos590GeThreeFalse.typeLT_natTuple]
  obtain ⟨e⟩ := Ordinal.type_eq.1 htype
  let blue := (OMA.Erdos590GeThreeFalse.speckerBlue m).comap e
  let red := blueᶜ
  rcases hram red blue isCompl_compl.symm with ⟨s, hcl, hst⟩ | ⟨s, hcl, hsc⟩
  · apply OMA.Erdos590GeThreeFalse.speckerRed_no_omega_pow m
    refine ⟨e '' s, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      have hne : a ≠ b := fun h => hab (congrArg e h)
      have hred : red.Adj a b := hcl ha hb hne
      exact ⟨hab, hred.2⟩
    · have es : ((· < ·) : s → s → Prop) ≃r ((· < ·) : (e '' s : Set _) → _ → Prop) :=
        { toEquiv := Equiv.Set.image e s e.injective
          map_rel_iff' := by
            intro a b
            exact e.map_rel_iff }
      rw [← es.ordinalType_congr, hst]
  · apply OMA.Erdos590GeThreeFalse.speckerBlue_no_triangle m
    refine ⟨e '' s, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      have hne : a ≠ b := fun h => hab (congrArg e h)
      exact hcl ha hb hne
    · rw [Cardinal.mk_image_eq e.injective, hsc]
