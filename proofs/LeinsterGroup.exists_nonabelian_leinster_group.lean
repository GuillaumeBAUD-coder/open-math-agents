import FormalConjectures.Wikipedia.LeinsterGroup

/-!
# Existence of a Non-Abelian Leinster Group

We prove `LeinsterGroup.exists_nonabelian_leinster_group` using the group
`G = DihedralGroup 3 × Multiplicative (ZMod 5)` of order `30`.
1. Since every element of `DihedralGroup 3` has order dividing `6` and every element of
   `Multiplicative (ZMod 5)` has order dividing `5`, every subgroup `H ≤ G` splits as
   `H₁.prod H₂` (using `(a, b) ^ 25 = (a, 1)` and `(a, b) ^ 6 = (1, b)`).
2. The normal subgroups of `DihedralGroup 3` are precisely `⊥` (order `1`), the rotation
   subgroup `rotSubgroup` (order `3`), and `⊤` (order `6`); the subgroups of
   `Multiplicative (ZMod 5)` are precisely `⊥` (order `1`) and `⊤` (order `5`).
3. Hence `G` has exactly `6` normal subgroups, with orders `1, 5, 3, 15, 6, 30`, whose sum is
   `60 = 2 * 30`, and `G` is non-abelian because `DihedralGroup 3` is non-abelian.
-/

-- Problem: Leinster Groups — exists nonabelian leinster group
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/LeinsterGroup.lean:98 (declaration LeinsterGroup.exists_nonabelian_leinster_group)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace LeinsterNonabelianProof

private abbrev D3 := DihedralGroup 3
private abbrev C5 := Multiplicative (ZMod 5)
private abbrev G30 := D3 × C5

private lemma zmod3_add_self_three (i : ZMod 3) : i + i + i = 0 := by
  revert i
  decide

private lemma zmod3_sub_two (k : ZMod 3) : k - 1 + -1 = k + 1 := by
  revert k
  decide

private lemma zmod3_three (i j : ZMod 3) : j = i ∨ j = i + 1 ∨ j = i + 1 + 1 := by
  revert i j
  decide

private lemma zmod3_cases (j : ZMod 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  revert j
  decide

private lemma zmod5_ne_zero (x : ZMod 5) (h : x ≠ 0) :
    x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  revert x h
  decide

private lemma d3_pow_six (a : D3) : a ^ 6 = 1 := by
  cases a with
  | r i =>
    have h3 : (DihedralGroup.r i : D3) ^ 3 = 1 := by
      rw [pow_succ, pow_succ, pow_one]
      change DihedralGroup.r (i + i + i) = DihedralGroup.r 0
      rw [zmod3_add_self_three]
    have h6 : (DihedralGroup.r i : D3) ^ 6 = ((DihedralGroup.r i : D3) ^ 3) ^ 2 := by
      rw [← pow_mul]
    rw [h6, h3, one_pow]
  | sr i =>
    have h2 : (DihedralGroup.sr i : D3) ^ 2 = 1 := by
      rw [sq]
      change DihedralGroup.r (i - i) = DihedralGroup.r 0
      simp
    have h6 : (DihedralGroup.sr i : D3) ^ 6 = ((DihedralGroup.sr i : D3) ^ 2) ^ 3 := by
      rw [← pow_mul]
    rw [h6, h2, one_pow]

private lemma c5_pow_five (b : C5) : b ^ 5 = 1 := by
  have hb : b = Multiplicative.ofAdd (Multiplicative.toAdd b) := rfl
  rw [hb, ← ofAdd_nsmul]
  have hz : 5 • Multiplicative.toAdd b = (0 : ZMod 5) := by
    generalize Multiplicative.toAdd b = x
    revert x
    decide
  rw [hz]
  rfl

private def rotSubgroup : Subgroup D3 where
  carrier := { g | ∃ i : ZMod 3, g = DihedralGroup.r i }
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, rfl⟩
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, rfl⟩

private lemma rotSubgroup_normal : rotSubgroup.Normal := by
  constructor
  intro n hn g
  rcases hn with ⟨i, rfl⟩
  cases g with
  | r j =>
    refine ⟨j + i - j, ?_⟩
    change DihedralGroup.r (j + i + -j) = DihedralGroup.r (j + i - j)
    rw [sub_eq_add_neg]
  | sr j =>
    refine ⟨-i, ?_⟩
    change DihedralGroup.r (j - (j + i)) = DihedralGroup.r (-i)
    congr 1
    ring

private lemma d3_normal_classification (N : Subgroup D3) (hN : N.Normal) :
    N = ⊥ ∨ N = rotSubgroup ∨ N = ⊤ := by
  by_cases hsr : ∃ i : ZMod 3, DihedralGroup.sr i ∈ N
  · right; right
    rcases hsr with ⟨i, hi⟩
    have hstep : ∀ k : ZMod 3, DihedralGroup.sr k ∈ N → DihedralGroup.sr (k + 1) ∈ N := by
      intro k hk
      have hconj : DihedralGroup.r 1 * DihedralGroup.sr k * (DihedralGroup.r 1)⁻¹ ∈ N :=
        hN.conj_mem _ hk _
      have heq : DihedralGroup.r 1 * DihedralGroup.sr k * (DihedralGroup.r 1)⁻¹ =
          (DihedralGroup.sr (k + 1) : D3) := by
        change DihedralGroup.sr (k - 1 + -1) = DihedralGroup.sr (k + 1)
        rw [zmod3_sub_two]
      rwa [heq] at hconj
    have hall_sr : ∀ j : ZMod 3, DihedralGroup.sr j ∈ N := by
      have h1 : DihedralGroup.sr (i + 1) ∈ N := hstep i hi
      have h2 : DihedralGroup.sr (i + 1 + 1) ∈ N := hstep (i + 1) h1
      intro j
      rcases zmod3_three i j with rfl | rfl | rfl
      · exact hi
      · exact h1
      · exact h2
    ext g
    simp only [Subgroup.mem_top, iff_true]
    cases g with
    | sr j => exact hall_sr j
    | r j =>
      have hmul : DihedralGroup.sr 0 * DihedralGroup.sr j ∈ N :=
        N.mul_mem (hall_sr 0) (hall_sr j)
      have heq : (DihedralGroup.sr 0 : D3) * DihedralGroup.sr j = DihedralGroup.r j := by
        change DihedralGroup.r (j - 0) = DihedralGroup.r j
        simp
      rwa [heq] at hmul
  · push Not at hsr
    by_cases hr1 : DihedralGroup.r 1 ∈ N
    · right; left
      ext g
      cases g with
      | sr j =>
        exact ⟨fun h => absurd h (hsr j), fun ⟨_, h⟩ => by cases h⟩
      | r j =>
        have hr0 : (DihedralGroup.r 0 : D3) ∈ N := N.one_mem
        have hr2 : (DihedralGroup.r 2 : D3) ∈ N := by
          have h := N.mul_mem hr1 hr1
          have heq : (DihedralGroup.r 1 : D3) * DihedralGroup.r 1 = DihedralGroup.r 2 := by
            change DihedralGroup.r (1 + 1) = DihedralGroup.r 2
            rfl
          rwa [heq] at h
        have hj : DihedralGroup.r j ∈ N := by
          rcases zmod3_cases j with rfl | rfl | rfl
          · exact hr0
          · exact hr1
          · exact hr2
        exact ⟨fun _ => ⟨j, rfl⟩, fun _ => hj⟩
    · by_cases hr2 : DihedralGroup.r 2 ∈ N
      · exfalso
        have hmul : (DihedralGroup.r 2 : D3) * DihedralGroup.r 2 ∈ N := N.mul_mem hr2 hr2
        have heq : (DihedralGroup.r 2 : D3) * DihedralGroup.r 2 = DihedralGroup.r 1 := by
          change DihedralGroup.r (2 + 2) = DihedralGroup.r 1
          rfl
        rw [heq] at hmul
        exact hr1 hmul
      · left
        ext g
        simp only [Subgroup.mem_bot]
        cases g with
        | sr j =>
          exact ⟨fun h => absurd h (hsr j), fun h => by cases h⟩
        | r j =>
          rcases zmod3_cases j with rfl | rfl | rfl
          · exact ⟨fun _ => rfl, fun _ => N.one_mem⟩
          · exact ⟨fun h => absurd h hr1, fun h => by
              have : (1 : ZMod 3) = 0 := DihedralGroup.r.inj h
              exact absurd this (by decide)⟩
          · exact ⟨fun h => absurd h hr2, fun h => by
              have : (2 : ZMod 3) = 0 := DihedralGroup.r.inj h
              exact absurd this (by decide)⟩

private lemma c5_subgroup_classification (K : Subgroup C5) : K = ⊥ ∨ K = ⊤ := by
  by_cases hbot : K = ⊥
  · exact Or.inl hbot
  · right
    have hex : ∃ b : C5, b ∈ K ∧ b ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hbot
      ext b
      simp only [Subgroup.mem_bot]
      exact ⟨hall b, fun h => h ▸ K.one_mem⟩
    rcases hex with ⟨b, hbK, hb1⟩
    let x : ZMod 5 := Multiplicative.toAdd b
    have hx0 : x ≠ 0 := fun h => hb1 h
    have hpow_one : ∃ k : ℕ, b ^ k = Multiplicative.ofAdd (1 : ZMod 5) := by
      rcases zmod5_ne_zero x hx0 with h | h | h | h
      · exact ⟨1, by rw [pow_one]; exact h⟩
      · refine ⟨3, ?_⟩
        change Multiplicative.ofAdd (3 • x) = Multiplicative.ofAdd 1
        rw [h]; rfl
      · refine ⟨2, ?_⟩
        change Multiplicative.ofAdd (2 • x) = Multiplicative.ofAdd 1
        rw [h]; rfl
      · refine ⟨4, ?_⟩
        change Multiplicative.ofAdd (4 • x) = Multiplicative.ofAdd 1
        rw [h]; rfl
    rcases hpow_one with ⟨k, hk⟩
    have hgen : Multiplicative.ofAdd (1 : ZMod 5) ∈ K := hk ▸ K.pow_mem hbK k
    ext c
    simp only [Subgroup.mem_top, iff_true]
    let y : ZMod 5 := Multiplicative.toAdd c
    have hy : (Multiplicative.ofAdd (1 : ZMod 5)) ^ y.val = c := by
      change Multiplicative.ofAdd (y.val • (1 : ZMod 5)) = Multiplicative.ofAdd y
      congr 1
      simp
    exact hy ▸ K.pow_mem hgen y.val

private lemma g30_normal_split (H : Subgroup G30) (hH : H.Normal) :
    ∃ (N₁ : Subgroup D3) (N₂ : Subgroup C5), N₁.Normal ∧ H = N₁.prod N₂ := by
  let N₁ : Subgroup D3 := H.comap (MonoidHom.inl D3 C5)
  let N₂ : Subgroup C5 := H.comap (MonoidHom.inr D3 C5)
  have hN₁ : N₁.Normal := by
    constructor
    intro a ha g
    have hconj : (g, (1 : C5)) * (a, (1 : C5)) * (g, (1 : C5))⁻¹ ∈ H :=
      hH.conj_mem (a, 1) ha (g, 1)
    simpa [N₁] using hconj
  refine ⟨N₁, N₂, hN₁, ?_⟩
  ext ⟨a, b⟩
  constructor
  · intro hab
    have ha : (a, (1 : C5)) ∈ H := by
      have h25 := H.pow_mem hab 25
      have heq : (a, b) ^ 25 = (a, (1 : C5)) := by
        ext
        · change a ^ 25 = a
          have h : a ^ 25 = (a ^ 6) ^ 4 * a := by rw [← pow_mul, ← pow_succ]
          rw [h, d3_pow_six, one_pow, one_mul]
        · change b ^ 25 = 1
          have h : b ^ 25 = (b ^ 5) ^ 5 := by rw [← pow_mul]
          rw [h, c5_pow_five]
      rwa [heq] at h25
    have hb : ((1 : D3), b) ∈ H := by
      have h6 := H.pow_mem hab 6
      have heq : (a, b) ^ 6 = ((1 : D3), b) := by
        ext
        · change a ^ 6 = 1
          exact d3_pow_six a
        · change b ^ 6 = b
          have h : b ^ 6 = b ^ 5 * b := by rw [← pow_succ]
          rw [h, c5_pow_five, one_mul]
      rwa [heq] at h6
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    have hmul := H.mul_mem ha hb
    simpa using hmul

private lemma subgroup_prod_normal {A B : Type*} [Group A] [Group B]
    (N₁ : Subgroup A) (N₂ : Subgroup B) [N₁.Normal] [N₂.Normal] :
    (N₁.prod N₂).Normal := by
  constructor
  rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨g₁, g₂⟩
  exact ⟨Subgroup.Normal.conj_mem ‹_› a ha g₁, Subgroup.Normal.conj_mem ‹_› b hb g₂⟩

private lemma card_subgroup_prod {A B : Type*} [Group A] [Group B]
    (N₁ : Subgroup A) (N₂ : Subgroup B) :
    Nat.card (N₁.prod N₂) = Nat.card N₁ * Nat.card N₂ := by
  let e : ↥(N₁.prod N₂) ≃ ↥N₁ × ↥N₂ :=
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2, p.2.2⟩⟩
      left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
  rw [Nat.card_congr e, Nat.card_prod]

private lemma card_bot_eq_one {A : Type*} [Group A] : Nat.card (⊥ : Subgroup A) = 1 := by
  let e : ↥(⊥ : Subgroup A) ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨1, Subgroup.one_mem _⟩
      left_inv := fun ⟨x, hx⟩ => by
        rw [Subgroup.mem_bot] at hx
        exact Subtype.ext hx.symm
      right_inv := fun ⟨⟩ => rfl }
  rw [Nat.card_congr e, Nat.card_unique]

private lemma card_top_eq {A : Type*} [Group A] [Fintype A] :
    Nat.card (⊤ : Subgroup A) = Fintype.card A := by
  let e : ↥(⊤ : Subgroup A) ≃ A :=
    { toFun := fun x => x.1
      invFun := fun x => ⟨x, trivial⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]

private lemma card_rotSubgroup : Nat.card rotSubgroup = 3 := by
  let e : ZMod 3 ≃ ↥rotSubgroup :=
    { toFun := fun i => ⟨DihedralGroup.r i, ⟨i, rfl⟩⟩
      invFun := fun x => x.2.choose
      left_inv := fun i => by
        have h := (⟨i, rfl⟩ : ∃ j : ZMod 3, DihedralGroup.r i = DihedralGroup.r j).choose_spec
        exact (DihedralGroup.r.inj h).symm
      right_inv := fun ⟨x, hx⟩ => Subtype.ext hx.choose_spec.symm }
  rw [← Nat.card_congr e, Nat.card_zmod]

private lemma card_d3 : Fintype.card D3 = 6 := by
  let e : D3 ≃ ZMod 3 ⊕ ZMod 3 :=
    { toFun := fun g => match g with
        | DihedralGroup.r i => Sum.inl i
        | DihedralGroup.sr i => Sum.inr i
      invFun := fun s => match s with
        | Sum.inl i => DihedralGroup.r i
        | Sum.inr i => DihedralGroup.sr i
      left_inv := fun g => by cases g <;> rfl
      right_inv := fun s => by cases s <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_sum, ZMod.card]

private lemma card_c5 : Fintype.card C5 = 5 := by
  have e : C5 ≃ ZMod 5 := Multiplicative.toAdd
  rw [Fintype.card_congr e, ZMod.card]

private def d3NormalList : Fin 3 → Subgroup D3
  | 0 => ⊥
  | 1 => rotSubgroup
  | 2 => ⊤

private lemma d3NormalList_normal : ∀ i : Fin 3, (d3NormalList i).Normal
  | 0 => by change (⊥ : Subgroup D3).Normal; infer_instance
  | 1 => rotSubgroup_normal
  | 2 => by change (⊤ : Subgroup D3).Normal; infer_instance

private lemma d3NormalList_card : ∀ i : Fin 3,
    Nat.card (d3NormalList i) = match i with | 0 => 1 | 1 => 3 | 2 => 6
  | 0 => card_bot_eq_one
  | 1 => card_rotSubgroup
  | 2 => by change Nat.card (⊤ : Subgroup D3) = 6; rw [card_top_eq, card_d3]

private def c5SubList : Fin 2 → Subgroup C5
  | 0 => ⊥
  | 1 => ⊤

private lemma c5SubList_card : ∀ j : Fin 2,
    Nat.card (c5SubList j) = match j with | 0 => 1 | 1 => 5
  | 0 => card_bot_eq_one
  | 1 => by change Nat.card (⊤ : Subgroup C5) = 5; rw [card_top_eq, card_c5]

private def normalSubOfPair (p : Fin 3 × Fin 2) : { H : Subgroup G30 // H.Normal } :=
  ⟨(d3NormalList p.1).prod (c5SubList p.2), by
    have : (d3NormalList p.1).Normal := d3NormalList_normal p.1
    have : (c5SubList p.2).Normal := Subgroup.normal_of_isMulCommutative _
    exact subgroup_prod_normal _ _⟩

private lemma normalSubOfPair_card (p : Fin 3 × Fin 2) :
    Nat.card (normalSubOfPair p).1 =
      (match p.1 with | 0 => 1 | 1 => 3 | 2 => 6) *
      (match p.2 with | 0 => 1 | 1 => 5) := by
  dsimp only [normalSubOfPair]
  rw [card_subgroup_prod, d3NormalList_card, c5SubList_card]

private lemma normalSubOfPair_bijective : Function.Bijective normalSubOfPair := by
  constructor
  · intro p₁ p₂ heq
    have hcard : Nat.card (normalSubOfPair p₁).1 = Nat.card (normalSubOfPair p₂).1 :=
      congrArg (fun x : { H : Subgroup G30 // H.Normal } => Nat.card x.1) heq
    rw [normalSubOfPair_card, normalSubOfPair_card] at hcard
    rcases p₁ with ⟨i₁, j₁⟩
    rcases p₂ with ⟨i₂, j₂⟩
    fin_cases i₁ <;> fin_cases j₁ <;> fin_cases i₂ <;> fin_cases j₂ <;>
      first | rfl | (simp at hcard)
  · rintro ⟨H, hH⟩
    obtain ⟨N₁, N₂, hN₁, rfl⟩ := g30_normal_split H hH
    have hi : ∃ i : Fin 3, d3NormalList i = N₁ := by
      rcases d3_normal_classification N₁ hN₁ with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    have hj : ∃ j : Fin 2, c5SubList j = N₂ := by
      rcases c5_subgroup_classification N₂ with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    rcases hi with ⟨i, rfl⟩
    rcases hj with ⟨j, rfl⟩
    exact ⟨(i, j), rfl⟩

open scoped Classical in
private lemma g30_isLeinster : LeinsterGroup.IsLeinster G30 := by
  unfold LeinsterGroup.IsLeinster
  let e : Fin 3 × Fin 2 ≃ { H : Subgroup G30 // H.Normal } :=
    Equiv.ofBijective normalSubOfPair normalSubOfPair_bijective
  rw [← Equiv.sum_comp e]
  have hsum :
      ∑ p : Fin 3 × Fin 2, Nat.card (e p).1 = 60 := by
    have hfn : ∀ p : Fin 3 × Fin 2,
        Nat.card (e p).1 =
          (match p.1 with | 0 => 1 | 1 => 3 | 2 => 6) *
          (match p.2 with | 0 => 1 | 1 => 5) :=
      fun p => normalSubOfPair_card p
    simp_rw [hfn]
    decide
  rw [hsum, Fintype.card_prod, card_d3, card_c5]

private lemma g30_nonabelian : ¬ ∀ a b : G30, a * b = b * a := by
  intro hall
  have h := hall (DihedralGroup.r 1, 1) (DihedralGroup.sr 0, 1)
  have h1 : (DihedralGroup.r 1 : D3) * DihedralGroup.sr 0 =
      DihedralGroup.sr 0 * DihedralGroup.r 1 := congrArg Prod.fst h
  have h2 : (0 - 1 : ZMod 3) = 0 + 1 := DihedralGroup.sr.inj h1
  exact absurd h2 (by decide)

end LeinsterNonabelianProof

theorem OMA.solution : type_of% @LeinsterGroup.exists_nonabelian_leinster_group := by
  exact ⟨LeinsterNonabelianProof.G30, inferInstance, inferInstance,
    LeinsterNonabelianProof.g30_isLeinster, LeinsterNonabelianProof.g30_nonabelian⟩
