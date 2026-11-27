import FormalConjectures.Wikipedia.LinearArboricityConjecture

-- Problem: Alon (1988): the linear arboricity conjecture holds asymptotically.
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/LinearArboricityConjecture.lean:118 (declaration LinearArboricityConjecture.linear_arboricity_conjecture.variants.alon)
-- Credit: @irwincollin (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Asymptotic proof of the Linear Arboricity Conjecture (Alon 1988):
For every `ε > 0`, there exists `Δ₀` such that every finite simple graph `G`
of maximum degree `Δ ≥ Δ₀` satisfies `linearArboricity G ≤ (1/2 + ε) * Δ`.
-/

namespace AlonLA

open Filter SimpleGraph
open scoped Real

noncomputable section

open scoped Classical

section LLL

private def good {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : I → Finset Ω) (T : Finset I) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ j ∈ T, ω ∉ A j)

private lemma good_empty {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] (A : I → Finset Ω) :
    good A ∅ = Finset.univ := by
  ext ω
  simp [good]

private lemma good_insert {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]
    (A : I → Finset Ω) (i : I) (T : Finset I) :
    good A (insert i T) = (good A T).filter (fun ω => ω ∉ A i) := by
  ext ω
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    forall_eq_or_imp]
  exact and_comm

private lemma good_card_split {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]
    (A : I → Finset Ω) (i : I) (T : Finset I) :
    (good A T).card = (good A (insert i T)).card + (A i ∩ good A T).card := by
  rw [good_insert]
  have hsub : A i ∩ good A T = (good A T).filter (fun ω => ω ∈ A i) := by
    ext ω
    simp [and_comm]
  rw [hsub]
  have h := Finset.card_filter_add_card_filter_not (s := good A T) (p := fun ω => ω ∈ A i)
  omega

private lemma good_antitone {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : I → Finset Ω) {T₁ T₂ : Finset I} (h : T₁ ⊆ T₂) :
    good A T₂ ⊆ good A T₁ := by
  intro ω hω
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  intro j hj
  exact hω j (h hj)

private lemma one_sub_mul_le_pow_aux (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ n : ℕ, 1 - (n : ℝ) * a ≤ (1 - a) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := one_sub_mul_le_pow_aux a ha0 ha1 n
    have hmul : (1 - (n : ℝ) * a) * (1 - a) ≤ (1 - a) ^ n * (1 - a) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have hsq : 0 ≤ (n : ℝ) * a ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg a)
    rw [pow_succ]
    push_cast
    nlinarith

private lemma lll_step_chain {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]
    (A : I → Finset Ω) (α : ℝ) (hα1 : α ≤ 1) (n : ℕ)
    (ih : ∀ U : Finset I, U.card < n → ∀ j ∉ U,
      ((good A U).card : ℝ) * (1 - α) ≤ ((good A (insert j U)).card : ℝ)) :
    ∀ S T₂ : Finset I, Disjoint S T₂ → (S ∪ T₂).card ≤ n →
      ((good A T₂).card : ℝ) * (1 - α) ^ S.card ≤ ((good A (S ∪ T₂)).card : ℝ) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro T₂ _ _
    simp
  | @insert x S₀ hx ihS =>
    intro T₂ hdisj hcard
    have hdisj₀ : Disjoint S₀ T₂ := hdisj.mono_left (Finset.subset_insert x S₀)
    have hxT₂ : x ∉ T₂ := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self x S₀)
    have hxU : x ∉ S₀ ∪ T₂ := by simp [hx, hxT₂]
    have hsub : S₀ ∪ T₂ ⊂ insert x S₀ ∪ T₂ := by
      rw [Finset.insert_union]
      exact Finset.ssubset_insert hxU
    have hcard₀_lt : (S₀ ∪ T₂).card < n :=
      lt_of_lt_of_le (Finset.card_lt_card hsub) hcard
    have h1 : ((good A T₂).card : ℝ) * (1 - α) ^ S₀.card ≤ ((good A (S₀ ∪ T₂)).card : ℝ) :=
      ihS T₂ hdisj₀ hcard₀_lt.le
    have h2 : ((good A (S₀ ∪ T₂)).card : ℝ) * (1 - α) ≤
        ((good A (insert x (S₀ ∪ T₂))).card : ℝ) :=
      ih (S₀ ∪ T₂) hcard₀_lt x hxU
    rw [Finset.insert_union, Finset.card_insert_of_notMem hx, pow_succ]
    calc
      ((good A T₂).card : ℝ) * ((1 - α) ^ S₀.card * (1 - α))
          = ((good A T₂).card : ℝ) * (1 - α) ^ S₀.card * (1 - α) := by ring
      _ ≤ ((good A (S₀ ∪ T₂)).card : ℝ) * (1 - α) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ ((good A (insert x (S₀ ∪ T₂))).card : ℝ) := h2

theorem lll_symmetric {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I] [DecidableEq I]
    [Nonempty Ω]
    (A : I → Finset Ω) (Γ : I → Finset I) (p : ℝ) (d : ℕ)
    (hp : 0 ≤ p) (hpd : 4 * p * ((d : ℝ) + 1) ≤ 1)
    (hΓ : ∀ i, (Γ i).card ≤ d)
    (hlop : ∀ i : I, ∀ T : Finset I, i ∉ T → (∀ j ∈ T, j ∉ Γ i) →
      ((A i ∩ good A T).card : ℝ) ≤ p * ((good A T).card : ℝ)) :
    ∃ ω : Ω, ∀ i : I, ω ∉ A i := by
  have hp4 : 4 * p ≤ 1 := by
    have hd0 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
    nlinarith
  have h2p0 : 0 ≤ 2 * p := by linarith
  have h2p1 : 2 * p ≤ 1 := by linarith
  have hmain : ∀ n : ℕ, ∀ T : Finset I, T.card ≤ n → ∀ i ∉ T,
      ((good A T).card : ℝ) * (1 - 2 * p) ≤ ((good A (insert i T)).card : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hTn i hiT
      let S₁ : Finset I := T ∩ Γ i
      let S₂ : Finset I := T \ Γ i
      have hT_eq : S₁ ∪ S₂ = T := by
        ext x
        simp only [S₁, S₂, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      have hdisj : Disjoint S₁ S₂ := disjoint_sdiff_self_right.mono_left Finset.inter_subset_right
      have hS₁_le : S₁.card ≤ d :=
        (Finset.card_le_card Finset.inter_subset_right).trans (hΓ i)
      have hiS₂ : i ∉ S₂ := fun h => hiT (Finset.sdiff_subset h)
      have hS₂_Γ : ∀ j ∈ S₂, j ∉ Γ i := fun j hj => (Finset.mem_sdiff.mp hj).2
      have hbad_le : ((A i ∩ good A T).card : ℝ) ≤ p * ((good A S₂).card : ℝ) := by
        have hsub : A i ∩ good A T ⊆ A i ∩ good A S₂ :=
          Finset.inter_subset_inter_left (good_antitone A Finset.sdiff_subset)
        have h1 : ((A i ∩ good A T).card : ℝ) ≤ ((A i ∩ good A S₂).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
        exact h1.trans (hlop i S₂ hiS₂ hS₂_Γ)
      have hgood_ge : (1 / 2 : ℝ) * ((good A S₂).card : ℝ) ≤ ((good A T).card : ℝ) := by
        have hih : ∀ U : Finset I, U.card < n → ∀ j ∉ U,
            ((good A U).card : ℝ) * (1 - 2 * p) ≤ ((good A (insert j U)).card : ℝ) :=
          fun U hU => ih U.card hU U le_rfl
        have hchain := lll_step_chain A (2 * p) h2p1 n hih S₁ S₂ hdisj
          (by rw [hT_eq]; exact hTn)
        rw [hT_eq] at hchain
        have hpow_ge : (1 / 2 : ℝ) ≤ (1 - 2 * p) ^ S₁.card := by
          rcases Nat.eq_zero_or_pos S₁.card with h0 | hpos
          · rw [h0, pow_zero]
            norm_num
          · have hpow_mono : (1 - 2 * p) ^ d ≤ (1 - 2 * p) ^ S₁.card :=
              pow_le_pow_of_le_one (by linarith) (by linarith) hS₁_le
            have hbern := one_sub_mul_le_pow_aux (2 * p) h2p0 h2p1 d
            have h4pd : 4 * p * (d : ℝ) ≤ 1 := by
              nlinarith [Nat.cast_nonneg (α := ℝ) d]
            linarith
        calc
          (1 / 2 : ℝ) * ((good A S₂).card : ℝ)
              ≤ (1 - 2 * p) ^ S₁.card * ((good A S₂).card : ℝ) :=
                mul_le_mul_of_nonneg_right hpow_ge (Nat.cast_nonneg _)
          _ = ((good A S₂).card : ℝ) * (1 - 2 * p) ^ S₁.card := mul_comm _ _
          _ ≤ ((good A T).card : ℝ) := hchain
      have hbad_T : ((A i ∩ good A T).card : ℝ) ≤ 2 * p * ((good A T).card : ℝ) := by
        linarith [mul_le_mul_of_nonneg_left hgood_ge (by linarith : 0 ≤ 2 * p)]
      have hsplit : ((good A T).card : ℝ) =
          ((good A (insert i T)).card : ℝ) + ((A i ∩ good A T).card : ℝ) := by
        exact_mod_cast good_card_split A i T
      linarith
  have hpos_all : ∀ S : Finset I, 0 < (good A S).card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [good_empty, Finset.card_univ]
      exact Fintype.card_pos
    | @insert i S hi ih =>
      have hstep := hmain S.card S le_rfl i hi
      have hS_pos : (0 : ℝ) < (good A S).card := Nat.cast_pos.mpr ih
      have h12p : (0 : ℝ) < 1 - 2 * p := by linarith
      have hins : (0 : ℝ) < (good A (insert i S)).card :=
        lt_of_lt_of_le (mul_pos hS_pos h12p) hstep
      exact Nat.cast_pos.mp hins
  obtain ⟨ω, hω⟩ := Finset.card_pos.mp (hpos_all Finset.univ)
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hω
  exact ⟨ω, fun i => hω i trivial⟩

def DependsOn {X α : Type*} (S : Finset X) (E : Finset (X → α)) : Prop :=
  ∀ f g : X → α, (∀ x ∈ S, f x = g x) → (f ∈ E ↔ g ∈ E)

lemma dependsOn_mono {X α : Type*} {S T : Finset X} {E : Finset (X → α)}
    (hST : S ⊆ T) (hE : DependsOn S E) : DependsOn T E :=
  fun f g hfg => hE f g fun x hx => hfg x (hST hx)

lemma dependsOn_compl {X α : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    {S : Finset X} {E : Finset (X → α)} (hE : DependsOn S E) :
    DependsOn S (Finset.univ \ E) := by
  intro f g hfg
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact not_congr (hE f g hfg)

lemma dependsOn_inter {X α : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    {S T : Finset X} {E F : Finset (X → α)}
    (hE : DependsOn S E) (hF : DependsOn T F) :
    DependsOn (S ∪ T) (E ∩ F) := by
  intro f g hfg
  simp only [Finset.mem_inter]
  have he : f ∈ E ↔ g ∈ E := hE f g fun x hx => hfg x (Finset.mem_union_left T hx)
  have hf : f ∈ F ↔ g ∈ F := hF f g fun x hx => hfg x (Finset.mem_union_right S hx)
  exact and_congr he hf

lemma dependsOn_good {X α I : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (A : I → Finset (X → α)) (S : I → Finset X)
    (hS : ∀ i, DependsOn (S i) (A i)) (T : Finset I) :
    DependsOn (T.biUnion S) (good A T) := by
  intro f g hfg
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf j hj hmem
    have hEq := hS j f g (fun x hx => hfg x (Finset.mem_biUnion.mpr ⟨j, hj, hx⟩))
    exact hf j hj (hEq.mpr hmem)
  · intro hg j hj hmem
    have hEq := hS j f g (fun x hx => hfg x (Finset.mem_biUnion.mpr ⟨j, hj, hx⟩))
    exact hg j hj (hEq.mp hmem)

def splitProdEquiv {X α : Type*} (S : Finset X) [DecidablePred (fun x => x ∈ S)] :
    (X → α) ≃ (({x : X // x ∈ S} → α) × ({x : X // x ∉ S} → α)) where
  toFun f := (fun x => f x.1, fun y => f y.1)
  invFun p x := if hx : x ∈ S then p.1 ⟨x, hx⟩ else p.2 ⟨x, hx⟩
  left_inv f := funext fun x => by
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx]
  right_inv p := by
    ext x
    · simp [x.2]
    · simp [x.2]

theorem card_inter_of_dependsOn_disjoint {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Nonempty α]
    {S T : Finset X} (hdisj : Disjoint S T) {E F : Finset (X → α)}
    (hE : DependsOn S E) (hF : DependsOn T F) :
    (E ∩ F).card * Fintype.card (X → α) = E.card * F.card := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty α›
  let e := splitProdEquiv (α := α) S
  let E₁ : Finset ({x : X // x ∈ S} → α) :=
    Finset.univ.filter (fun g => e.symm (g, fun _ => a₀) ∈ E)
  let F₂ : Finset ({x : X // x ∉ S} → α) :=
    Finset.univ.filter (fun h => e.symm (fun _ => a₀, h) ∈ F)
  have hEiff : ∀ f : X → α, f ∈ E ↔ (e f).1 ∈ E₁ := by
    intro f
    simp only [E₁, Finset.mem_filter, Finset.mem_univ, true_and]
    refine hE f (e.symm ((e f).1, fun _ => a₀)) fun x hx => ?_
    simp [e, splitProdEquiv, hx]
  have hFiff : ∀ f : X → α, f ∈ F ↔ (e f).2 ∈ F₂ := by
    intro f
    simp only [F₂, Finset.mem_filter, Finset.mem_univ, true_and]
    refine hF f (e.symm (fun _ => a₀, (e f).2)) fun x hx => ?_
    have hxS : x ∉ S := Finset.disjoint_right.mp hdisj hx
    simp [e, splitProdEquiv, hxS]
  have himE : E.image e = E₁ ×ˢ Finset.univ := by
    ext p
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (hEiff f).mp hf
    · intro hp
      refine ⟨e.symm p, (hEiff (e.symm p)).mpr ?_, e.apply_symm_apply p⟩
      simpa using hp
  have himF : F.image e = Finset.univ ×ˢ F₂ := by
    ext p
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (hFiff f).mp hf
    · intro hp
      refine ⟨e.symm p, (hFiff (e.symm p)).mpr ?_, e.apply_symm_apply p⟩
      simpa using hp
  have himEF : (E ∩ F).image e = E₁ ×ˢ F₂ := by
    ext p
    simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_product]
    constructor
    · rintro ⟨f, ⟨hfE, hfF⟩, rfl⟩
      exact ⟨(hEiff f).mp hfE, (hFiff f).mp hfF⟩
    · rintro ⟨hp1, hp2⟩
      refine ⟨e.symm p, ⟨(hEiff (e.symm p)).mpr ?_, (hFiff (e.symm p)).mpr ?_⟩,
        e.apply_symm_apply p⟩ <;> simpa using ‹_›
  have hcE : E.card = E₁.card * Fintype.card ({x : X // x ∉ S} → α) := by
    rw [← Finset.card_image_of_injective E e.injective, himE, Finset.card_product, Finset.card_univ]
  have hcF : F.card = Fintype.card ({x : X // x ∈ S} → α) * F₂.card := by
    rw [← Finset.card_image_of_injective F e.injective, himF, Finset.card_product, Finset.card_univ]
  have hcEF : (E ∩ F).card = E₁.card * F₂.card := by
    rw [← Finset.card_image_of_injective (E ∩ F) e.injective, himEF, Finset.card_product]
  have hcTot : Fintype.card (X → α) =
      Fintype.card ({x : X // x ∈ S} → α) * Fintype.card ({x : X // x ∉ S} → α) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [hcEF, hcTot, hcE, hcF]
  ring

end LLL

section Chernoff

lemma chernoff_const_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < (1 + δ) * Real.log (1 + δ) - δ := by
  have h1 : 0 < 1 + δ := by linarith
  have hinv_pos : 0 < (1 + δ)⁻¹ := inv_pos.mpr h1
  have hinv_ne : (1 + δ)⁻¹ ≠ 1 := by
    intro h
    have : 1 + δ = 1 := by
      have := congrArg Inv.inv h
      simpa using this
    linarith
  have hlog := Real.log_lt_sub_one_of_pos hinv_pos hinv_ne
  rw [Real.log_inv] at hlog
  have hmul := mul_lt_mul_of_pos_left hlog h1
  have h11 : (1 + δ) * ((1 + δ)⁻¹ - 1) = -δ := by
    field_simp
    ring
  rw [h11] at hmul
  linarith

theorem chernoff_prod_upper {S α : Type*} [Fintype S] [DecidableEq S]
    [Fintype α] [DecidableEq α]
    (hit : S → Finset α) (μ δ : ℝ) (hα : 0 < Fintype.card α) (hδ : 0 < δ)
    (hμ : ∑ s : S, ((hit s).card : ℝ) / (Fintype.card α : ℝ) ≤ μ) :
    ((Finset.univ.filter (fun ω : S → α =>
        (1 + δ) * μ ≤ ((Finset.univ.filter (fun s : S => ω s ∈ hit s)).card : ℝ))).card : ℝ)
      ≤ Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (Fintype.card (S → α) : ℝ) := by
  let X : (S → α) → ℕ := fun ω => (Finset.univ.filter (fun s : S => ω s ∈ hit s)).card
  have h1δ : 0 < 1 + δ := by linarith
  have hαpos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr hα
  have hexp_sum : ∑ ω : S → α, (1 + δ) ^ (X ω) =
      ∏ s : S, ((Fintype.card α : ℝ) + δ * ((hit s).card : ℝ)) := by
    have hterm : ∀ ω : S → α, (1 + δ) ^ (X ω) =
        ∏ s : S, if ω s ∈ hit s then (1 + δ) else 1 := by
      intro ω
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    simp_rw [hterm]
    have hpi : (Finset.univ : Finset (S → α)) = Fintype.piFinset (fun _ : S => (Finset.univ : Finset α)) := by
      ext ω
      simp
    rw [hpi, ← Finset.prod_univ_sum (fun _ : S => (Finset.univ : Finset α))
      (fun s a => if a ∈ hit s then (1 + δ) else (1 : ℝ))]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
    have hsplit : (Finset.univ.filter (fun x : α => x ∈ hit s)).card +
        (Finset.univ.filter (fun x : α => x ∉ hit s)).card = Fintype.card α := by
      simpa using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
        (p := fun x : α => x ∈ hit s)
    have hcard1 : (Finset.univ.filter (fun x : α => x ∈ hit s)).card = (hit s).card := by
      congr 1
      ext x
      simp
    rw [hcard1] at hsplit ⊢
    have hcast : ((Finset.univ.filter (fun x : α => x ∉ hit s)).card : ℝ) =
        (Fintype.card α : ℝ) - ((hit s).card : ℝ) := by
      have : (Finset.univ.filter (fun x : α => x ∉ hit s)).card = Fintype.card α - (hit s).card := by
        omega
      rw [this, Nat.cast_sub]
      calc (hit s).card ≤ (Finset.univ : Finset α).card := Finset.card_le_univ _
        _ = Fintype.card α := Finset.card_univ
    rw [hcast]
    ring
  have hprod_bound : (∏ s : S, ((Fintype.card α : ℝ) + δ * ((hit s).card : ℝ))) ≤
      Real.exp (δ * μ) * (Fintype.card (S → α) : ℝ) := by
    have hcardΩ : (Fintype.card (S → α) : ℝ) = ∏ _s : S, (Fintype.card α : ℝ) := by
      rw [Fintype.card_fun, Nat.cast_pow, Finset.prod_const, Finset.card_univ]
    have hfac : (∏ s : S, ((Fintype.card α : ℝ) + δ * ((hit s).card : ℝ))) =
        (∏ s : S, (1 + δ * (((hit s).card : ℝ) / (Fintype.card α : ℝ)))) *
          (∏ _s : S, (Fintype.card α : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      field_simp
    have hexp_prod : (∏ s : S, (1 + δ * (((hit s).card : ℝ) / (Fintype.card α : ℝ)))) ≤
        Real.exp (δ * μ) := by
      calc (∏ s : S, (1 + δ * (((hit s).card : ℝ) / (Fintype.card α : ℝ))))
          ≤ ∏ s : S, Real.exp (δ * (((hit s).card : ℝ) / (Fintype.card α : ℝ))) := by
            refine Finset.prod_le_prod (fun s _ => by positivity) fun s _ => ?_
            linarith [Real.add_one_le_exp (δ * (((hit s).card : ℝ) / (Fintype.card α : ℝ)))]
        _ = Real.exp (∑ s : S, δ * (((hit s).card : ℝ) / (Fintype.card α : ℝ))) := by
            rw [Real.exp_sum]
        _ = Real.exp (δ * ∑ s : S, (((hit s).card : ℝ) / (Fintype.card α : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ Real.exp (δ * μ) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hμ hδ.le)
    rw [hfac, hcardΩ]
    exact mul_le_mul_of_nonneg_right hexp_prod (Finset.prod_nonneg fun _ _ => hαpos.le)
  have hmarkov : (1 + δ) ^ ((1 + δ) * μ) *
      (((Finset.univ : Finset (S → α)).filter (fun ω => (1 + δ) * μ ≤ (X ω : ℝ))).card : ℝ) ≤
      ∑ ω : S → α, (1 + δ) ^ (X ω) := by
    calc (1 + δ) ^ ((1 + δ) * μ) *
          (((Finset.univ : Finset (S → α)).filter (fun ω => (1 + δ) * μ ≤ (X ω : ℝ))).card : ℝ)
        = ∑ _ω ∈ (Finset.univ : Finset (S → α)).filter (fun ω => (1 + δ) * μ ≤ (X ω : ℝ)),
            (1 + δ) ^ ((1 + δ) * μ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ ω ∈ (Finset.univ : Finset (S → α)).filter (fun ω => (1 + δ) * μ ≤ (X ω : ℝ)),
            (1 + δ) ^ (X ω) := by
          refine Finset.sum_le_sum fun ω hω => ?_
          have hle : (1 + δ) * μ ≤ (X ω : ℝ) := (Finset.mem_filter.mp hω).2
          rw [← Real.rpow_natCast (1 + δ) (X ω)]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) hle
      _ ≤ ∑ ω : S → α, (1 + δ) ^ (X ω) := by
          refine Finset.sum_le_univ_sum_of_nonneg fun ω => by positivity
  have hcomb : (1 + δ) ^ ((1 + δ) * μ) *
      (((Finset.univ : Finset (S → α)).filter (fun ω => (1 + δ) * μ ≤ (X ω : ℝ))).card : ℝ) ≤
      Real.exp (δ * μ) * (Fintype.card (S → α) : ℝ) :=
    hmarkov.trans (hexp_sum ▸ hprod_bound)
  have hrpow : (1 + δ) ^ ((1 + δ) * μ) = Real.exp ((1 + δ) * Real.log (1 + δ) * μ) := by
    rw [Real.rpow_def_of_pos h1δ]
    ring_nf
  have hpos_pow : 0 < (1 + δ) ^ ((1 + δ) * μ) := Real.rpow_pos_of_pos h1δ _
  rw [← le_div_iff₀' hpos_pow] at hcomb
  refine hcomb.trans_eq ?_
  rw [hrpow, mul_div_right_comm, ← Real.exp_sub]
  congr 2
  ring

theorem chernoff_prod_upper_sub {X α : Type*} [Fintype X] [DecidableEq X]
    [Fintype α] [DecidableEq α]
    (S : Finset X) (hit : X → Finset α) (μ δ : ℝ) (hα : 0 < Fintype.card α) (hδ : 0 < δ)
    (hμ : ∑ x ∈ S, ((hit x).card : ℝ) / (Fintype.card α : ℝ) ≤ μ) :
    ((Finset.univ.filter (fun ω : X → α =>
        (1 + δ) * μ ≤ ((S.filter (fun x => ω x ∈ hit x)).card : ℝ))).card : ℝ)
      ≤ Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (Fintype.card (X → α) : ℝ) := by
  classical
  let e := splitProdEquiv (α := α) S
  have hμ' : ∑ s : {x : X // x ∈ S}, ((hit s.1).card : ℝ) / (Fintype.card α : ℝ) ≤ μ := by
    calc ∑ s : {x : X // x ∈ S}, ((hit s.1).card : ℝ) / (Fintype.card α : ℝ)
        = ∑ x ∈ S, ((hit x).card : ℝ) / (Fintype.card α : ℝ) := by
          rw [← Finset.sum_coe_sort S]
      _ ≤ μ := hμ
  have hbase := chernoff_prod_upper (fun s : {x : X // x ∈ S} => hit s.1) μ δ hα hδ hμ'
  let E : Finset (X → α) := Finset.univ.filter (fun ω : X → α =>
    (1 + δ) * μ ≤ ((S.filter (fun x => ω x ∈ hit x)).card : ℝ))
  let E₁ : Finset ({x : X // x ∈ S} → α) := Finset.univ.filter (fun g : {x : X // x ∈ S} → α =>
    (1 + δ) * μ ≤ ((Finset.univ.filter (fun s : {x : X // x ∈ S} => g s ∈ hit s.1)).card : ℝ))
  have him : E.image e = E₁ ×ˢ Finset.univ := by
    ext p
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true, E, E₁,
      Finset.mem_filter]
    have hcard_eq : ∀ f : X → α,
        (S.filter (fun x => f x ∈ hit x)).card =
          (Finset.univ.filter (fun s : {x : X // x ∈ S} => (e f).1 s ∈ hit s.1)).card := by
      intro f
      refine Finset.card_bij (fun x hx => ⟨x, (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, splitProdEquiv]
        exact (Finset.mem_filter.mp hx).2
      · intro x₁ _ x₂ _ h
        exact congrArg Subtype.val h
      · intro s hs
        refine ⟨s.1, Finset.mem_filter.mpr ⟨s.2, ?_⟩, rfl⟩
        simpa [e, splitProdEquiv] using (Finset.mem_filter.mp hs).2
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [← hcard_eq f]
      exact hf
    · intro hp
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      rw [hcard_eq (e.symm p)]
      simpa using hp
  have hcE : (E.card : ℝ) = (E₁.card : ℝ) * (Fintype.card ({x : X // x ∉ S} → α) : ℝ) := by
    have : E.card = E₁.card * Fintype.card ({x : X // x ∉ S} → α) := by
      rw [← Finset.card_image_of_injective E e.injective, him, Finset.card_product, Finset.card_univ]
    exact_mod_cast this
  have hcTot : (Fintype.card (X → α) : ℝ) =
      (Fintype.card ({x : X // x ∈ S} → α) : ℝ) * (Fintype.card ({x : X // x ∉ S} → α) : ℝ) := by
    have : Fintype.card (X → α) =
        Fintype.card ({x : X // x ∈ S} → α) * Fintype.card ({x : X // x ∉ S} → α) := by
      rw [Fintype.card_congr e, Fintype.card_prod]
    exact_mod_cast this
  change (E.card : ℝ) ≤ _
  rw [hcE, hcTot]
  calc (E₁.card : ℝ) * (Fintype.card ({x : X // x ∉ S} → α) : ℝ)
      ≤ (Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) *
          (Fintype.card ({x : X // x ∈ S} → α) : ℝ)) *
            (Fintype.card ({x : X // x ∉ S} → α) : ℝ) :=
        mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg _)
    _ = Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) *
          ((Fintype.card ({x : X // x ∈ S} → α) : ℝ) *
            (Fintype.card ({x : X // x ∉ S} → α) : ℝ)) := by ring

end Chernoff

section Orientation

def outDeg {V : Type*} (D : V → V → Prop) (v : V) : ℕ :=
  ({w : V | D v w} : Set V).ncard

def inDeg {V : Type*} (D : V → V → Prop) (v : V) : ℕ :=
  ({u : V | D u v} : Set V).ncard

lemma outDeg_eq_filter_card {V : Type*} [Fintype V] (D : V → V → Prop) (v : V)
    [DecidablePred (D v)] :
    outDeg D v = (Finset.univ.filter (fun w => D v w)).card := by
  rw [outDeg, ← Set.ncard_coe_finset]
  congr 1; ext w; simp

lemma ncard_neighborSet_eq_degree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (G.neighborSet v).ncard = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset]
  congr 1; ext w; simp

def walkDir {V : Type*} {G : SimpleGraph V} : ∀ {a b : V}, G.Walk a b → V → V → Prop
  | _, _, .nil => fun _ _ => False
  | _, _, @SimpleGraph.Walk.cons _ _ u v _ _ p => fun x y => (x = u ∧ y = v) ∨ walkDir p x y

lemma walkDir_adj {V : Type*} {G : SimpleGraph V} {a b : V} {W : G.Walk a b} {x y : V}
    (h : walkDir W x y) : G.Adj x y := by
  induction W with
  | nil => exact False.elim h
  | @cons u v w hadj p ih =>
    rcases h with ⟨rfl, rfl⟩ | hp
    · exact hadj
    · exact ih hp

lemma walkDir_mem_edges {V : Type*} {G : SimpleGraph V} {a b : V} {W : G.Walk a b} {x y : V}
    (h : walkDir W x y) : s(x, y) ∈ W.edges := by
  induction W with
  | nil => exact False.elim h
  | @cons u v w hadj p ih =>
    rcases h with ⟨rfl, rfl⟩ | hp
    · simp
    · exact List.mem_cons_of_mem _ (ih hp)

lemma mem_edges_walkDir {V : Type*} {G : SimpleGraph V} {a b : V} {W : G.Walk a b} {x y : V}
    (h : s(x, y) ∈ W.edges) : walkDir W x y ∨ walkDir W y x := by
  induction W with
  | nil => simp at h
  | @cons u v w hadj p ih =>
    rw [Walk.edges_cons, List.mem_cons] at h
    rcases h with hhead | htail
    · rw [Sym2.eq_iff] at hhead
      rcases hhead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; left; exact ⟨rfl, rfl⟩
      · right; left; exact ⟨rfl, rfl⟩
    · rcases ih htail with h1 | h2
      · left; right; exact h1
      · right; right; exact h2

lemma walkDir_iff_mem_edges {V : Type*} {G : SimpleGraph V} {a b : V} {W : G.Walk a b} {x y : V} :
    walkDir W x y ∨ walkDir W y x ↔ s(x, y) ∈ W.edges :=
  ⟨fun h => h.elim walkDir_mem_edges fun h' => by simpa [Sym2.eq_swap] using walkDir_mem_edges h',
   mem_edges_walkDir⟩

lemma walkDir_asym {V : Type*} {G : SimpleGraph V} {a b : V} {W : G.Walk a b}
    (hW : W.IsTrail) {x y : V} (h : walkDir W x y) : ¬ walkDir W y x := by
  induction W with
  | nil => exact False.elim h
  | @cons u v w hadj p ih =>
    rw [Walk.isTrail_cons] at hW
    rcases h with ⟨rfl, rfl⟩ | hp1
    · rintro (⟨hvu, huv⟩ | hp2)
      · exact hadj.ne hvu.symm
      · exact hW.2 (by simpa [Sym2.eq_swap] using walkDir_mem_edges hp2)
    · rintro (⟨hyu, hxv⟩ | hp2)
      · subst hyu hxv
        exact hW.2 (by simpa [Sym2.eq_swap] using walkDir_mem_edges hp1)
      · exact ih hW.1 hp1 hp2

lemma walkDir_balance {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (W : G.Walk a b) (hW : W.IsTrail) (z : V) :
    (outDeg (walkDir W) z : ℤ) - (inDeg (walkDir W) z : ℤ) =
    (if z = a then 1 else 0) - (if z = b then 1 else 0) := by
  induction W with
  | nil =>
    dsimp only [outDeg, inDeg, walkDir]
    have h01 : ({w : V | False} : Set V) = ∅ := rfl
    rw [h01, Set.ncard_empty, sub_self, sub_self]
  | @cons u v w hadj p ih =>
    rw [Walk.isTrail_cons] at hW
    have hp := ih hW.1
    have huv : ¬ walkDir p u v := fun h => hW.2 (walkDir_mem_edges h)
    have hout : outDeg (walkDir (Walk.cons hadj p)) z =
        outDeg (walkDir p) z + (if z = u then 1 else 0) := by
      dsimp only [outDeg]
      by_cases hzu : z = u
      · subst hzu
        have heq : ({y : V | walkDir (Walk.cons hadj p) z y} : Set V) =
            insert v {y : V | walkDir p z y} := by
          ext y
          simp only [Set.mem_ofPred_eq, walkDir, Set.mem_insert_iff, true_and]
        rw [heq, Set.ncard_insert_of_notMem (by simp [huv]) (Set.toFinite _), if_pos rfl]
      · have heq : ({y : V | walkDir (Walk.cons hadj p) z y} : Set V) =
            {y : V | walkDir p z y} := by
          ext y
          simp only [Set.mem_ofPred_eq, walkDir, hzu, false_and, false_or]
        rw [heq, if_neg hzu, add_zero]
    have hin : inDeg (walkDir (Walk.cons hadj p)) z =
        inDeg (walkDir p) z + (if z = v then 1 else 0) := by
      dsimp only [inDeg]
      by_cases hzv : z = v
      · subst hzv
        have heq : ({x : V | walkDir (Walk.cons hadj p) x z} : Set V) =
            insert u {x : V | walkDir p x z} := by
          ext x
          simp only [Set.mem_ofPred_eq, walkDir, Set.mem_insert_iff, and_true]
        rw [heq, Set.ncard_insert_of_notMem (by simp [huv]) (Set.toFinite _), if_pos rfl]
      · have heq : ({x : V | walkDir (Walk.cons hadj p) x z} : Set V) =
            {x : V | walkDir p x z} := by
          ext x
          simp only [Set.mem_ofPred_eq, walkDir, hzv, and_false, false_or]
        rw [heq, if_neg hzv, add_zero]
    rw [hout, hin]
    push_cast
    split_ifs at hp ⊢ <;> linarith

lemma degree_deleteEdges_trail {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V} (W : G.Walk a b) (hW : W.IsTrail)
    (z : V) :
    (G.deleteEdges {e | e ∈ W.edges}).degree z +
      (outDeg (walkDir W) z + inDeg (walkDir W) z) = G.degree z := by
  let s1 : Set V := (G.deleteEdges {e | e ∈ W.edges}).neighborSet z
  let s2 : Set V := {y : V | walkDir W z y}
  let s3 : Set V := {x : V | walkDir W x z}
  have h12 : Disjoint s1 s2 := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    simp only [s1, mem_neighborSet, deleteEdges_adj, Set.mem_ofPred_eq] at hy1
    exact hy1.2 (walkDir_mem_edges hy2)
  have h13 : Disjoint s1 s3 := by
    rw [Set.disjoint_left]
    intro x hx1 hx3
    simp only [s1, mem_neighborSet, deleteEdges_adj, Set.mem_ofPred_eq] at hx1
    exact hx1.2 (by simpa [Sym2.eq_swap] using walkDir_mem_edges hx3)
  have h23 : Disjoint s2 s3 := by
    rw [Set.disjoint_left]
    intro y hy2 hy3
    exact walkDir_asym hW hy2 hy3
  have hunion : G.neighborSet z = s1 ∪ (s2 ∪ s3) := by
    ext y
    simp only [mem_neighborSet, Set.mem_union, deleteEdges_adj, Set.mem_ofPred_eq, s1, s2, s3]
    constructor
    · intro hG
      by_cases hed : s(z, y) ∈ W.edges
      · right; exact walkDir_iff_mem_edges.mpr hed
      · left; exact ⟨hG, hed⟩
    · rintro (⟨hG, _⟩ | hW1 | hW2)
      · exact hG
      · exact walkDir_adj hW1
      · exact (walkDir_adj hW2).symm
  rw [← ncard_neighborSet_eq_degree G z, ← ncard_neighborSet_eq_degree _ z]
  change s1.ncard + (s2.ncard + s3.ncard) = (G.neighborSet z).ncard
  rw [hunion, Set.ncard_union_eq (Set.disjoint_union_right.mpr ⟨h12, h13⟩)
      (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq h23 (Set.toFinite _) (Set.toFinite _)]

lemma exists_maximal_trail {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    ∃ (w : V) (W : G.Walk u w), W.IsTrail ∧
      (G.deleteEdges {e | e ∈ W.edges}).degree w = 0 := by
  let L : Set ℕ := {n | ∃ (w : V) (W : G.Walk u w), W.IsTrail ∧ W.length = n}
  have h0 : 0 ∈ L := ⟨u, Walk.nil, Walk.IsTrail.nil, rfl⟩
  have hbdd : BddAbove L := by
    refine ⟨G.edgeFinset.card, ?_⟩
    rintro n ⟨w, W, hW, rfl⟩
    exact hW.length_le_card_edgeFinset
  let m := sSup L
  have hm : m ∈ L := Nat.sSup_mem ⟨0, h0⟩ hbdd
  obtain ⟨w, W, hW, hlen⟩ := hm
  refine ⟨w, W, hW, ?_⟩
  by_contra hpos
  have hne : (G.deleteEdges {e | e ∈ W.edges}).neighborFinset w |>.Nonempty := by
    rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree]
    exact Nat.pos_of_ne_zero hpos
  obtain ⟨x, hx⟩ := hne
  rw [mem_neighborFinset, deleteEdges_adj, Set.mem_ofPred_eq] at hx
  let W' : G.Walk u x := W.append (Walk.cons hx.1 Walk.nil)
  have hW' : W'.IsTrail := by
    rw [Walk.isTrail_append]
    refine ⟨hW, ?_, ?_⟩
    · simp [Walk.isTrail_cons]
    · simp only [Walk.edges_cons, Walk.edges_nil, List.disjoint_cons_right, List.disjoint_nil_right]
      exact ⟨hx.2, True.intro⟩
  have hlen' : W'.length = m + 1 := by
    simp [W', Walk.length_append, hlen]
  have hm1 : m + 1 ∈ L := ⟨x, W', hW', hlen'⟩
  have hle := le_csSup hbdd hm1
  omega

private lemma orientation_combine_step {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} (W : G.Walk u w) (hW : W.IsTrail)
    (D' : V → V → Prop) (hD'asym : ∀ x y, D' x y → ¬ D' y x)
    (hD'adj : ∀ x y, (G.deleteEdges {e | e ∈ W.edges}).Adj x y ↔ D' x y ∨ D' y x)
    (hD'bal : ∀ v, (outDeg D' v : ℤ) - (inDeg D' v : ℤ) ∈ ({-1, 0, 1} : Set ℤ))
    (hcompat : ∀ v, (outDeg (walkDir W) v : ℤ) - (inDeg (walkDir W) v : ℤ) ≠ 0 →
      Even ((G.deleteEdges {e | e ∈ W.edges}).degree v)) :
    ∃ D : V → V → Prop,
      (∀ x y, D x y → ¬ D y x) ∧
      (∀ x y, G.Adj x y ↔ D x y ∨ D y x) ∧
      (∀ v, (outDeg D v : ℤ) - (inDeg D v : ℤ) ∈ ({-1, 0, 1} : Set ℤ)) := by
  let G' := G.deleteEdges {e | e ∈ W.edges}
  let D : V → V → Prop := fun x y => D' x y ∨ walkDir W x y
  refine ⟨D, ?_, ?_, ?_⟩
  · intro x y hDxy hDyx
    have hdisjW : ∀ a b, D' a b → ¬ walkDir W a b := by
      intro a b hD' hWab
      have hadj := (hD'adj a b).mpr (Or.inl hD')
      rw [deleteEdges_adj, Set.mem_ofPred_eq] at hadj
      exact hadj.2 (walkDir_mem_edges hWab)
    have hdisjW' : ∀ a b, D' a b → ¬ walkDir W b a := by
      intro a b hD' hWba
      have hadj := (hD'adj a b).mpr (Or.inl hD')
      rw [deleteEdges_adj, Set.mem_ofPred_eq] at hadj
      exact hadj.2 (by simpa [Sym2.eq_swap] using walkDir_mem_edges hWba)
    rcases hDxy with h1 | h1 <;> rcases hDyx with h2 | h2
    · exact hD'asym x y h1 h2
    · exact hdisjW' x y h1 h2
    · exact hdisjW' y x h2 h1
    · exact walkDir_asym hW h1 h2
  · intro x y
    simp only [D]
    constructor
    · intro hG
      by_cases hed : s(x, y) ∈ W.edges
      · rcases walkDir_iff_mem_edges.mpr hed with h1 | h2
        · left; right; exact h1
        · right; right; exact h2
      · have hG' : G'.Adj x y := deleteEdges_adj.mpr ⟨hG, hed⟩
        rcases (hD'adj x y).mp hG' with h1 | h2
        · left; left; exact h1
        · right; left; exact h2
    · rintro ((h1 | h1) | (h2 | h2))
      · exact deleteEdges_le _ ((hD'adj x y).mpr (Or.inl h1))
      · exact walkDir_adj h1
      · exact deleteEdges_le _ ((hD'adj x y).mpr (Or.inr h2))
      · exact (walkDir_adj h2).symm
  · intro z
    have hD'sum : outDeg D' z + inDeg D' z = G'.degree z := by
      have hdisj : Disjoint ({y : V | D' z y} : Set V) {x : V | D' x z} := by
        rw [Set.disjoint_left]
        intro y hy1 hy2
        exact hD'asym z y hy1 hy2
      have hunion : G'.neighborSet z = {y : V | D' z y} ∪ {x : V | D' x z} := by
        ext y
        simp only [mem_neighborSet, Set.mem_union, Set.mem_ofPred_eq]
        exact hD'adj z y
      rw [← ncard_neighborSet_eq_degree G' z, hunion,
        Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      rfl
    have houtD : outDeg D z = outDeg D' z + outDeg (walkDir W) z := by
      have hdisj : Disjoint ({y : V | D' z y} : Set V) {y : V | walkDir W z y} := by
        rw [Set.disjoint_left]
        intro y hy1 hy2
        have hadj := (hD'adj z y).mpr (Or.inl hy1)
        rw [deleteEdges_adj, Set.mem_ofPred_eq] at hadj
        exact hadj.2 (walkDir_mem_edges hy2)
      have hunion : ({y : V | D z y} : Set V) = {y : V | D' z y} ∪ {y : V | walkDir W z y} := by
        ext y; simp [D]
      rw [outDeg, hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      rfl
    have hinD : inDeg D z = inDeg D' z + inDeg (walkDir W) z := by
      have hdisj : Disjoint ({x : V | D' x z} : Set V) {x : V | walkDir W x z} := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        have hadj := (hD'adj x z).mpr (Or.inl hx1)
        rw [deleteEdges_adj, Set.mem_ofPred_eq] at hadj
        exact hadj.2 (by simpa [Sym2.eq_swap] using walkDir_mem_edges hx2)
      have hunion : ({x : V | D x z} : Set V) = {x : V | D' x z} ∪ {x : V | walkDir W x z} := by
        ext x; simp [D]
      rw [inDeg, hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      rfl
    have hWbal := walkDir_balance W hW z
    have hWset : (outDeg (walkDir W) z : ℤ) - (inDeg (walkDir W) z : ℤ) ∈
        ({-1, 0, 1} : Set ℤ) := by
      rw [hWbal]
      split_ifs <;> simp
    have hbal_eq : (outDeg D z : ℤ) - (inDeg D z : ℤ) =
        ((outDeg D' z : ℤ) - (inDeg D' z : ℤ)) +
          ((outDeg (walkDir W) z : ℤ) - (inDeg (walkDir W) z : ℤ)) := by
      rw [houtD, hinD]
      push_cast
      ring
    rw [hbal_eq]
    by_cases hW0 : (outDeg (walkDir W) z : ℤ) - (inDeg (walkDir W) z : ℤ) = 0
    · rw [hW0, add_zero]
      exact hD'bal z
    · have hev : Even (G'.degree z) := hcompat z hW0
      have hbal0 : (outDeg D' z : ℤ) - (inDeg D' z : ℤ) = 0 := by
        rcases hev with ⟨k, hk⟩
        have hsum : (outDeg D' z : ℤ) + (inDeg D' z : ℤ) = 2 * k := by
          exact_mod_cast (hD'sum.trans (by omega : G'.degree z = 2 * k))
        have hb := hD'bal z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        rcases hb with h1 | h1 | h1 <;> omega
      rw [hbal0, zero_add]
      exact hWset

lemma exists_balanced_orientation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ D : V → V → Prop,
      (∀ u v, D u v → ¬ D v u) ∧
      (∀ u v, G.Adj u v ↔ D u v ∨ D v u) ∧
      (∀ v, (outDeg D v : ℤ) - (inDeg D v : ℤ) ∈ ({-1, 0, 1} : Set ℤ)) := by
  have hmain : ∀ m : ℕ, ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
      G.edgeFinset.card ≤ m →
      ∃ D : V → V → Prop,
        (∀ u v, D u v → ¬ D v u) ∧
        (∀ u v, G.Adj u v ↔ D u v ∨ D v u) ∧
        (∀ v, (outDeg D v : ℤ) - (inDeg D v : ℤ) ∈ ({-1, 0, 1} : Set ℤ)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro G _ hGm
      by_cases hEmpty : G.edgeFinset = ∅
      · refine ⟨fun _ _ => False, by simp, fun u v => ?_, fun v => ?_⟩
        · have hGbot : ¬ G.Adj u v := by
            intro hadj
            have hmem : s(u, v) ∈ G.edgeFinset := mem_edgeFinset.mpr hadj
            rw [hEmpty] at hmem
            simp at hmem
          simp [hGbot]
        · have h01 : ({w : V | False} : Set V) = ∅ := rfl
          simp [outDeg, inDeg, h01]
      · have hNonempty : G.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
        have htrail_step : ∀ {u w : V} (W : G.Walk u w), W.IsTrail → 0 < W.length →
            (∀ z, (outDeg (walkDir W) z : ℤ) - (inDeg (walkDir W) z : ℤ) ≠ 0 →
              Even ((G.deleteEdges {e | e ∈ W.edges}).degree z)) →
            ∃ D : V → V → Prop,
              (∀ x y, D x y → ¬ D y x) ∧
              (∀ x y, G.Adj x y ↔ D x y ∨ D y x) ∧
              (∀ v, (outDeg D v : ℤ) - (inDeg D v : ℤ) ∈ ({-1, 0, 1} : Set ℤ)) := by
          intro u w W hW hWpos hcompat
          let G' := G.deleteEdges {e | e ∈ W.edges}
          have hcardG' : G'.edgeFinset.card < G.edgeFinset.card := by
            obtain ⟨e, he⟩ : ∃ e, e ∈ W.edges := by
              cases W with
              | nil => simp at hWpos
              | cons h p => exact ⟨_, List.Mem.head _⟩
            have heG : e ∈ G.edgeFinset := mem_edgeFinset.mpr (W.edges_subset_edgeSet he)
            have hsub : G'.edgeFinset ⊂ G.edgeFinset := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨fun x hx => ?_, fun hEq => ?_⟩
              · rw [mem_edgeFinset] at hx ⊢
                exact (edgeSet_deleteEdges _ ▸ hx).1
              · have heG' : e ∈ G'.edgeFinset := by rw [hEq]; exact heG
                rw [mem_edgeFinset] at heG'
                exact (edgeSet_deleteEdges _ ▸ heG').2 he
            exact Finset.card_lt_card hsub
          have hltm : G'.edgeFinset.card < m := lt_of_lt_of_le hcardG' hGm
          obtain ⟨D', hD'asym, hD'adj, hD'bal⟩ := ih G'.edgeFinset.card hltm G' le_rfl
          exact orientation_combine_step G W hW D' hD'asym hD'adj hD'bal hcompat
        by_cases hOdd : ∃ u : V, Odd (G.degree u)
        · obtain ⟨u, huOdd⟩ := hOdd
          obtain ⟨w, W, hW, hw0⟩ := exists_maximal_trail G u
          have hWpos : 0 < W.length := by
            by_contra h0
            have hlen0 : W.length = 0 := by omega
            cases W with
            | nil =>
              have hdeg_eq := degree_deleteEdges_trail (Walk.nil : G.Walk u u) hW u
              have h0out : outDeg (walkDir (Walk.nil : G.Walk u u)) u = 0 := by
                have he : ({w : V | walkDir (Walk.nil : G.Walk u u) u w} : Set V) = ∅ := rfl
                rw [outDeg, he, Set.ncard_empty]
              have h0in : inDeg (walkDir (Walk.nil : G.Walk u u)) u = 0 := by
                have he : ({w : V | walkDir (Walk.nil : G.Walk u u) w u} : Set V) = ∅ := rfl
                rw [inDeg, he, Set.ncard_empty]
              have hdeg0 : G.degree u = 0 := by
                rw [← hdeg_eq, hw0, h0out, h0in]
              rw [hdeg0] at huOdd
              exact Nat.not_odd_zero huOdd
            | cons _ _ => simp at hlen0
          refine htrail_step W hW hWpos fun z hz => ?_
          have hbal := walkDir_balance W hW z
          have hbal_ne : (if z = u then (1 : ℤ) else 0) - (if z = w then 1 else 0) ≠ 0 := by
            rwa [← hbal]
          have huw : u ≠ w := by
            rintro rfl
            simp at hbal_ne
          have hzw : z = u ∨ z = w := by
            by_contra hnot
            push Not at hnot
            simp [hnot.1, hnot.2] at hbal_ne
          rcases hzw with rfl | rfl
          · have hdeg := degree_deleteEdges_trail W hW z
            rw [if_pos rfl, if_neg huw] at hbal
            have hoi : Odd (outDeg (walkDir W) z + inDeg (walkDir W) z) :=
              ⟨(outDeg (walkDir W) z + inDeg (walkDir W) z - 1) / 2, by omega⟩
            rcases huOdd with ⟨a, ha⟩
            rcases hoi with ⟨b, hb⟩
            exact ⟨a - b, by omega⟩
          · rw [hw0]
            exact Even.zero
        · push Not at hOdd
          have hEv : ∀ v : V, Even (G.degree v) := fun v => Nat.not_odd_iff_even.mp (hOdd v)
          obtain ⟨e, he⟩ := hNonempty
          induction e using Sym2.ind with
          | _ u y =>
            have hadj : G.Adj u y := mem_edgeFinset.mp he
            have huPos : 0 < G.degree u := by
              rw [← SimpleGraph.card_neighborFinset_eq_degree]
              exact Finset.card_pos.mpr ⟨y, by simp only [mem_neighborFinset]; exact hadj⟩
            obtain ⟨w, W, hW, hw0⟩ := exists_maximal_trail G u
            have hWpos : 0 < W.length := by
              by_contra h0
              have hlen0 : W.length = 0 := by omega
              cases W with
              | nil =>
                have hdeg_eq := degree_deleteEdges_trail (Walk.nil : G.Walk u u) hW u
                have h0out : outDeg (walkDir (Walk.nil : G.Walk u u)) u = 0 := by
                  have he' : ({w : V | walkDir (Walk.nil : G.Walk u u) u w} : Set V) = ∅ := rfl
                  rw [outDeg, he', Set.ncard_empty]
                have h0in : inDeg (walkDir (Walk.nil : G.Walk u u)) u = 0 := by
                  have he' : ({w : V | walkDir (Walk.nil : G.Walk u u) w u} : Set V) = ∅ := rfl
                  rw [inDeg, he', Set.ncard_empty]
                have hdeg0 : G.degree u = 0 := by
                  rw [← hdeg_eq, hw0, h0out, h0in]
                omega
              | cons _ _ => simp at hlen0
            refine htrail_step W hW hWpos fun z hz => ?_
            exfalso
            have hbal := walkDir_balance W hW z
            have hbal_ne : (if z = u then (1 : ℤ) else 0) - (if z = w then 1 else 0) ≠ 0 := by
              rwa [← hbal]
            have huw : u ≠ w := by
              rintro rfl
              simp at hbal_ne
            have hbalw := walkDir_balance W hW w
            rw [if_neg huw.symm, if_pos rfl] at hbalw
            have hdegw := degree_deleteEdges_trail W hW w
            rw [hw0, zero_add] at hdegw
            rcases hEv w with ⟨k, hk⟩
            omega
  exact hmain G.edgeFinset.card G le_rfl

lemma balanced_orientation_deg_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ} (hΔ : G.maxDegree ≤ Δ) :
    ∃ D : V → V → Prop,
      (∀ u v, D u v → ¬ D v u) ∧
      (∀ u v, G.Adj u v ↔ D u v ∨ D v u) ∧
      (∀ v, outDeg D v ≤ (Δ + 1) / 2 ∧ inDeg D v ≤ (Δ + 1) / 2) := by
  obtain ⟨D, hDasym, hDadj, hDbal⟩ := exists_balanced_orientation G
  refine ⟨D, hDasym, hDadj, fun v => ?_⟩
  have hsum : outDeg D v + inDeg D v = G.degree v := by
    have hdisj : Disjoint ({w : V | D v w} : Set V) {u : V | D u v} := by
      rw [Set.disjoint_left]
      intro w hw1 hw2
      exact hDasym v w hw1 hw2
    have hunion : G.neighborSet v = {w : V | D v w} ∪ {u : V | D u v} := by
      ext w
      simp only [mem_neighborSet, Set.mem_union, Set.mem_ofPred_eq]
      exact hDadj v w
    rw [← ncard_neighborSet_eq_degree G v, hunion,
      Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    rfl
  have hdeg : G.degree v ≤ Δ := (G.degree_le_maxDegree v).trans hΔ
  have hb := hDbal v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with h | h | h <;> omega

end Orientation

section Konig

private def uniqueNext {V : Type*} (M : V → V → Prop) (v : V) : Option V :=
  open scoped Classical in
  if h : ∃ w, M v w then some h.choose else none

private def uniquePrev {V : Type*} (M : V → V → Prop) (v : V) : Option V :=
  open scoped Classical in
  if h : ∃ u, M u v then some h.choose else none

lemma uniqueNext_eq_some_iff {V : Type*} [Fintype V] (M : V → V → Prop)
    (hOut : ∀ u, outDeg M u ≤ 1) {v w : V} :
    uniqueNext M v = some w ↔ M v w := by
  dsimp only [uniqueNext]
  constructor
  · intro h
    split_ifs at h with hex
    · cases h
      exact hex.choose_spec
  · intro hM
    have hex : ∃ w', M v w' := ⟨w, hM⟩
    rw [dif_pos hex]
    congr 1
    exact (Set.ncard_le_one_iff (Set.toFinite ({y : V | M v y} : Set V))).mp (hOut v)
      hex.choose_spec hM

lemma uniquePrev_eq_some_iff {V : Type*} [Fintype V] (M : V → V → Prop)
    (hIn : ∀ v, inDeg M v ≤ 1) {u v : V} :
    uniquePrev M v = some u ↔ M u v := by
  dsimp only [uniquePrev]
  constructor
  · intro h
    split_ifs at h with hex
    · cases h
      exact hex.choose_spec
  · intro hM
    have hex : ∃ u', M u' v := ⟨u, hM⟩
    rw [dif_pos hex]
    congr 1
    exact (Set.ncard_le_one_iff (Set.toFinite ({x : V | M x v} : Set V))).mp (hIn v)
      hex.choose_spec hM

private lemma exists_free_out_color {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (R : V → V → Prop)
    (M : Fin k → V → V → Prop)
    (hSub : ∀ j u v, M j u v → R u v)
    (hPart : ∀ u v, R u v → ∃! j, M j u v)
    (u₀ : V) (hu₀ : outDeg R u₀ < k) :
    ∃ α : Fin k, ∀ v, ¬ M α u₀ v := by
  let used : Finset (Fin k) := Finset.univ.filter (fun j => ∃ v, M j u₀ v)
  let pick : Fin k → V := fun j => if hj : ∃ v, M j u₀ v then hj.choose else u₀
  have hcard : used.card ≤ outDeg R u₀ := by
    rw [outDeg, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn pick ?_ ?_ (Set.toFinite _)
    · intro j hj
      simp only [Finset.mem_coe, used, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [pick, dif_pos hj, Set.mem_ofPred_eq]
      exact hSub j u₀ _ hj.choose_spec
    · intro j₁ hj₁ j₂ hj₂ hEq
      simp only [Finset.mem_coe, used, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
      simp only [pick, dif_pos hj₁, dif_pos hj₂] at hEq
      have hM1 : M j₁ u₀ hj₁.choose := hj₁.choose_spec
      have hM2 : M j₂ u₀ hj₁.choose := hEq ▸ hj₂.choose_spec
      obtain ⟨j, -, hjU⟩ := hPart _ _ (hSub _ _ _ hM1)
      exact (hjU j₁ hM1).trans (hjU j₂ hM2).symm
  have hlt : used.card < (Finset.univ : Finset (Fin k)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt hcard hu₀
  obtain ⟨α, -, hα⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨α, fun v hM => hα ?_⟩
  simp only [used, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, hM⟩

private lemma exists_free_in_color {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (R : V → V → Prop)
    (M : Fin k → V → V → Prop)
    (hSub : ∀ j u v, M j u v → R u v)
    (hPart : ∀ u v, R u v → ∃! j, M j u v)
    (v₀ : V) (hv₀ : inDeg R v₀ < k) :
    ∃ β : Fin k, ∀ u, ¬ M β u v₀ := by
  let used : Finset (Fin k) := Finset.univ.filter (fun j => ∃ u, M j u v₀)
  let pick : Fin k → V := fun j => if hj : ∃ u, M j u v₀ then hj.choose else v₀
  have hcard : used.card ≤ inDeg R v₀ := by
    rw [inDeg, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn pick ?_ ?_ (Set.toFinite _)
    · intro j hj
      simp only [Finset.mem_coe, used, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [pick, dif_pos hj, Set.mem_ofPred_eq]
      exact hSub j _ v₀ hj.choose_spec
    · intro j₁ hj₁ j₂ hj₂ hEq
      simp only [Finset.mem_coe, used, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
      simp only [pick, dif_pos hj₁, dif_pos hj₂] at hEq
      have hM1 : M j₁ hj₁.choose v₀ := hj₁.choose_spec
      have hM2 : M j₂ hj₁.choose v₀ := hEq ▸ hj₂.choose_spec
      obtain ⟨j, -, hjU⟩ := hPart _ _ (hSub _ _ _ hM1)
      exact (hjU j₁ hM1).trans (hjU j₂ hM2).symm
  have hlt : used.card < (Finset.univ : Finset (Fin k)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt hcard hv₀
  obtain ⟨β, -, hβ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨β, fun u hM => hβ ?_⟩
  simp only [used, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨u, hM⟩

private def chainStep {V : Type*} (Mα Mβ : V → V → Prop) (v₀ : V) : ℕ → Option (V ⊕ V)
  | 0 => some (Sum.inr v₀)
  | t + 1 =>
    match chainStep Mα Mβ v₀ t with
    | none => none
    | some (Sum.inr v) => (uniquePrev Mα v).map Sum.inl
    | some (Sum.inl u) => (uniqueNext Mβ u).map Sum.inr

private lemma chainStep_succ {V : Type*} (Mα Mβ : V → V → Prop) (v₀ : V) (t : ℕ) :
    chainStep Mα Mβ v₀ (t + 1) =
      match chainStep Mα Mβ v₀ t with
      | none => none
      | some (Sum.inr v) => (uniquePrev Mα v).map Sum.inl
      | some (Sum.inl u) => (uniqueNext Mβ u).map Sum.inr := rfl

private lemma chainStep_parity {V : Type*} (Mα Mβ : V → V → Prop) (v₀ : V) :
    ∀ t, (Even t → chainStep Mα Mβ v₀ t = none ∨ ∃ v, chainStep Mα Mβ v₀ t = some (Sum.inr v)) ∧
      (Odd t → chainStep Mα Mβ v₀ t = none ∨ ∃ u, chainStep Mα Mβ v₀ t = some (Sum.inl u))
  | 0 => ⟨fun _ => Or.inr ⟨v₀, rfl⟩, fun h => absurd h (by decide)⟩
  | t + 1 => by
    have ih := chainStep_parity Mα Mβ v₀ t
    constructor
    · intro ht1
      have ht : Odd t := by obtain ⟨k, hk⟩ := ht1; exact ⟨k - 1, by omega⟩
      rw [chainStep_succ]
      rcases ih.2 ht with hnone | ⟨u, hu⟩
      · left; simp [hnone]
      · rw [hu]
        cases hnx : uniqueNext Mβ u with
        | none => left; simp [hnx]
        | some v => right; exact ⟨v, by simp [hnx]⟩
    · intro ht1
      have ht : Even t := by obtain ⟨k, hk⟩ := ht1; exact ⟨k, by omega⟩
      rw [chainStep_succ]
      rcases ih.1 ht with hnone | ⟨v, hv⟩
      · left; simp [hnone]
      · rw [hv]
        cases hpr : uniquePrev Mα v with
        | none => left; simp [hpr]
        | some u => right; exact ⟨u, by simp [hpr]⟩

private lemma konig_kempe_swap {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (R R' : V → V → Prop) (u₀ v₀ : V)
    (hR₀ : R u₀ v₀) (hR'def : ∀ u v, R' u v ↔ R u v ∧ ¬ (u = u₀ ∧ v = v₀))
    (M : Fin k → V → V → Prop)
    (hMsub : ∀ j u v, M j u v → R' u v)
    (hMpart : ∀ u v, R' u v → ∃! j, M j u v)
    (hMout : ∀ j u, outDeg (M j) u ≤ 1)
    (hMin : ∀ j v, inDeg (M j) v ≤ 1)
    (α β : Fin k) (hαFree : ∀ v, ¬ M α u₀ v) (hβFree : ∀ u, ¬ M β u v₀) (hαβ : α ≠ β) :
    ∃ M' : Fin k → V → V → Prop,
      (∀ j u v, M' j u v → R u v) ∧
      (∀ u v, R u v → ∃! j : Fin k, M' j u v) ∧
      (∀ j u, outDeg (M' j) u ≤ 1) ∧
      (∀ j v, inDeg (M' j) v ≤ 1) := by
  classical
  let ch := chainStep (M α) (M β) v₀
  have hparEven : ∀ s, ch (2 * s) = none ∨ ∃ v, ch (2 * s) = some (Sum.inr v) :=
    fun s => (chainStep_parity (M α) (M β) v₀ (2 * s)).1 ⟨s, by ring⟩
  have hparOdd : ∀ s, ch (2 * s + 1) = none ∨ ∃ u, ch (2 * s + 1) = some (Sum.inl u) :=
    fun s => (chainStep_parity (M α) (M β) v₀ (2 * s + 1)).2 ⟨s, rfl⟩
  have hstep_α : ∀ s u v, ch (2 * s) = some (Sum.inr v) →
      ch (2 * s + 1) = some (Sum.inl u) → M α u v := by
    intro s u v hs1 hs2
    change chainStep (M α) (M β) v₀ (2 * s + 1) = some (Sum.inl u) at hs2
    rw [chainStep_succ] at hs2
    change chainStep (M α) (M β) v₀ (2 * s) = some (Sum.inr v) at hs1
    rw [hs1, Option.map_eq_some_iff] at hs2
    obtain ⟨u', hu', hEq⟩ := hs2
    cases hEq
    exact (uniquePrev_eq_some_iff (M α) (hMin α)).mp hu'
  have hstep_β : ∀ s u v, ch (2 * s + 1) = some (Sum.inl u) →
      ch (2 * s + 2) = some (Sum.inr v) → M β u v := by
    intro s u v hs1 hs2
    change chainStep (M α) (M β) v₀ ((2 * s + 1) + 1) = some (Sum.inr v) at hs2
    rw [chainStep_succ] at hs2
    change chainStep (M α) (M β) v₀ (2 * s + 1) = some (Sum.inl u) at hs1
    rw [hs1, Option.map_eq_some_iff] at hs2
    obtain ⟨v', hv', hEq⟩ := hs2
    cases hEq
    exact (uniqueNext_eq_some_iff (M β) (hMout β)).mp hv'
  have hprev_some : ∀ t z, ch (t + 1) = some z → (ch t).isSome := by
    intro t z hz
    cases ht : ch t with
    | none =>
      change chainStep (M α) (M β) v₀ (t + 1) = some z at hz
      rw [chainStep_succ] at hz
      change chainStep (M α) (M β) v₀ t = none at ht
      rw [ht] at hz
      simp at hz
    | some _ => rfl
  have hinj : ∀ m n z, ch m = some z → ch n = some z → m = n := by
    let P : ℕ → Prop := fun m => ∃ n, m < n ∧ ∃ z, ch m = some z ∧ ch n = some z
    suffices h : ¬ ∃ m, P m by
      intro m n z hm hn
      rcases lt_trichotomy m n with hlt | rfl | hgt
      · exact False.elim (h ⟨m, n, hlt, z, hm, hn⟩)
      · rfl
      · exact False.elim (h ⟨n, m, hgt, z, hn, hm⟩)
    intro hm
    have hmin := Nat.find_spec hm
    obtain ⟨n, hlt, z, hm0, hn0⟩ := hmin
    have hmin_le : ∀ m', P m' → Nat.find hm ≤ m' := fun m' hm' => Nat.find_min' hm hm'
    set m₀ := Nat.find hm
    rcases Nat.eq_zero_or_pos m₀ with h0 | hm₀pos
    · have hm_eq0 : m₀ = 0 := h0
      have hm0' : ch 0 = some z := hm_eq0 ▸ hm0
      have hch0 : ch 0 = some (Sum.inr v₀) := rfl
      have hz0 : z = Sum.inr v₀ := Option.some.inj (hm0'.symm.trans hch0)
      subst hz0
      have hnEven : ∃ s, n = 2 * s := by
        rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
        · exact ⟨s, by omega⟩
        · rw [hs] at hn0
          rcases hparOdd s with hnone | ⟨u, hu⟩
          · rw [hnone] at hn0; simp at hn0
          · rw [hu] at hn0; simp at hn0
      obtain ⟨s, rfl⟩ := hnEven
      have hspos : 1 ≤ s := by omega
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have hn_prev : (ch (2 * s' + 1)).isSome :=
        hprev_some (2 * s' + 1) (Sum.inr v₀) (by simpa [Nat.mul_add] using hn0)
      rcases hparOdd s' with hnone | ⟨u, hu⟩
      · simp [hnone] at hn_prev
      · exact hβFree u (hstep_β s' u v₀ hu hn0)
    · have hmPrev : (ch (m₀ - 1)).isSome :=
        hprev_some (m₀ - 1) z (by rwa [Nat.sub_add_cancel hm₀pos])
      have hnPrev : (ch (n - 1)).isSome :=
        hprev_some (n - 1) z (by rwa [Nat.sub_add_cancel (by omega : 0 < n)])
      rcases Nat.even_or_odd m₀ with ⟨sm, hsm⟩ | ⟨sm, hsm⟩
      · obtain ⟨sm', rfl⟩ : ∃ sm', sm = sm' + 1 := ⟨sm - 1, by omega⟩
        have hm_eq : m₀ = 2 * sm' + 2 := by omega
        have hzInr : ∃ v, z = Sum.inr v := by
          rcases hparEven (sm' + 1) with hnone | ⟨v, hv⟩
          · rw [show 2 * (sm' + 1) = 2 * sm' + 2 by ring, ← hm_eq, hm0] at hnone
            simp at hnone
          · rw [show 2 * (sm' + 1) = 2 * sm' + 2 by ring, ← hm_eq, hm0] at hv
            exact ⟨v, Option.some.inj hv⟩
        obtain ⟨v, rfl⟩ := hzInr
        have hnEven : ∃ sn, n = 2 * sn + 2 := by
          rcases Nat.even_or_odd n with ⟨sn, hsn⟩ | ⟨sn, hsn⟩
          · have hn1 : 1 ≤ sn := by omega
            exact ⟨sn - 1, by omega⟩
          · rw [hsn] at hn0
            rcases hparOdd sn with hnone | ⟨u, hu⟩
            · rw [hnone] at hn0; simp at hn0
            · rw [hu] at hn0; simp at hn0
        obtain ⟨sn, hsn⟩ := hnEven
        rcases hparOdd sm' with hmNone | ⟨um, hum⟩
        · have : m₀ - 1 = 2 * sm' + 1 := by omega
          rw [this, hmNone] at hmPrev; simp at hmPrev
        rcases hparOdd sn with hnNone | ⟨un, hun⟩
        · have : n - 1 = 2 * sn + 1 := by omega
          rw [this, hnNone] at hnPrev; simp at hnPrev
        have hM1 : M β um v := hstep_β sm' um v hum (by rw [← hm_eq]; exact hm0)
        have hM2 : M β un v := hstep_β sn un v hun (by rw [← hsn]; exact hn0)
        have hum_eq : um = un :=
          (Set.ncard_le_one_iff (Set.toFinite ({u : V | M β u v} : Set V))).mp (hMin β v) hM1 hM2
        subst hum_eq
        have hP' : P (m₀ - 1) := ⟨n - 1, by omega, Sum.inl um,
          by rw [show m₀ - 1 = 2 * sm' + 1 by omega]; exact hum,
          by rw [show n - 1 = 2 * sn + 1 by omega]; exact hun⟩
        have hcontra := hmin_le (m₀ - 1) hP'
        omega
      · have hm_eq : m₀ = 2 * sm + 1 := by omega
        have hzInl : ∃ u, z = Sum.inl u := by
          rcases hparOdd sm with hnone | ⟨u, hu⟩
          · rw [← hm_eq, hm0] at hnone; simp at hnone
          · rw [← hm_eq, hm0] at hu
            exact ⟨u, Option.some.inj hu⟩
        obtain ⟨u, rfl⟩ := hzInl
        have hnOdd : ∃ sn, n = 2 * sn + 1 := by
          rcases Nat.even_or_odd n with ⟨sn, hsn⟩ | ⟨sn, hsn⟩
          · rw [show n = 2 * sn by omega] at hn0
            rcases hparEven sn with hnone | ⟨v, hv⟩
            · rw [hnone] at hn0; simp at hn0
            · rw [hv] at hn0; simp at hn0
          · exact ⟨sn, by omega⟩
        obtain ⟨sn, hsn⟩ := hnOdd
        rcases hparEven sm with hmNone | ⟨vm, hvm⟩
        · have : m₀ - 1 = 2 * sm := by omega
          rw [this, hmNone] at hmPrev; simp at hmPrev
        rcases hparEven sn with hnNone | ⟨vn, hvn⟩
        · have : n - 1 = 2 * sn := by omega
          rw [this, hnNone] at hnPrev; simp at hnPrev
        have hM1 : M α u vm := hstep_α sm u vm hvm (by rw [← hm_eq]; exact hm0)
        have hM2 : M α u vn := hstep_α sn u vn hvn (by rw [← hsn]; exact hn0)
        have hvm_eq : vm = vn :=
          (Set.ncard_le_one_iff (Set.toFinite ({v : V | M α u v} : Set V))).mp (hMout α u) hM1 hM2
        subst hvm_eq
        have hP' : P (m₀ - 1) := ⟨n - 1, by omega, Sum.inr vm,
          by rw [show m₀ - 1 = 2 * sm by omega]; exact hvm,
          by rw [show n - 1 = 2 * sn by omega]; exact hvn⟩
        have hcontra := hmin_le (m₀ - 1) hP'
        omega
  have hno_u0 : ∀ s, ch (2 * s + 1) ≠ some (Sum.inl u₀) := by
    intro s hEq
    rcases hparEven s with hnone | ⟨v, hv⟩
    · change chainStep (M α) (M β) v₀ (2 * s + 1) = some (Sum.inl u₀) at hEq
      rw [chainStep_succ] at hEq
      change chainStep (M α) (M β) v₀ (2 * s) = none at hnone
      rw [hnone] at hEq
      simp at hEq
    · exact hαFree v (hstep_α s u₀ v hv hEq)
  let onChainA : V → V → Prop := fun u v =>
    ∃ s, ch (2 * s) = some (Sum.inr v) ∧ ch (2 * s + 1) = some (Sum.inl u)
  let onChainB : V → V → Prop := fun u v =>
    ∃ s, ch (2 * s + 1) = some (Sum.inl u) ∧ ch (2 * s + 2) = some (Sum.inr v)
  let M' : Fin k → V → V → Prop := fun j u v =>
    if j = α then (M α u v ∧ ¬ onChainA u v) ∨ onChainB u v ∨ (u = u₀ ∧ v = v₀)
    else if j = β then (M β u v ∧ ¬ onChainB u v) ∨ onChainA u v
    else M j u v
  refine ⟨M', ?_, ?_, ?_, ?_⟩
  · intro j u v hMj
    by_cases hjα : j = α
    · rw [hjα] at hMj
      simp only [M', ↓reduceIte] at hMj
      rcases hMj with ⟨h1, _⟩ | ⟨s, h1, h2⟩ | ⟨rfl, rfl⟩
      · exact ((hR'def u v).mp (hMsub α u v h1)).1
      · exact ((hR'def u v).mp (hMsub β u v (hstep_β s u v h1 h2))).1
      · exact hR₀
    · by_cases hjβ : j = β
      · rw [hjβ] at hMj
        simp only [M', if_neg (hjβ ▸ hjα), ↓reduceIte] at hMj
        rcases hMj with ⟨h1, _⟩ | ⟨s, h1, h2⟩
        · exact ((hR'def u v).mp (hMsub β u v h1)).1
        · exact ((hR'def u v).mp (hMsub α u v (hstep_α s u v h1 h2))).1
      · simp only [M', if_neg hjα, if_neg hjβ] at hMj
        exact ((hR'def u v).mp (hMsub j u v hMj)).1
  · intro u v hRuv
    by_cases huv : u = u₀ ∧ v = v₀
    · rcases huv with ⟨rfl, rfl⟩
      refine ⟨α, ?_, ?_⟩
      · simp [M']
      · intro j hj
        by_cases hjα : j = α
        · exact hjα
        · by_cases hjβ : j = β
          · rw [hjβ] at hj
            simp only [M', if_neg (hjβ ▸ hjα), ↓reduceIte] at hj
            rcases hj with ⟨h1, _⟩ | ⟨s, h1, h2⟩
            · exact absurd ((hR'def u v).mp (hMsub β u v h1)).2 (fun h => h ⟨rfl, rfl⟩)
            · exact absurd ((hR'def u v).mp (hMsub α u v (hstep_α s u v h1 h2))).2
                (fun h => h ⟨rfl, rfl⟩)
          · simp only [M', if_neg hjα, if_neg hjβ] at hj
            exact absurd ((hR'def u v).mp (hMsub j u v hj)).2 (fun h => h ⟨rfl, rfl⟩)
    · have hR'uv : R' u v := (hR'def u v).mpr ⟨hRuv, huv⟩
      obtain ⟨j, hjM, hjU⟩ := hMpart u v hR'uv
      have hdisj_AB : ¬ (M α u v ∧ M β u v) := fun ⟨ha, hb⟩ =>
        hαβ ((hjU α ha).trans (hjU β hb).symm)
      by_cases hjα : j = α
      · rw [hjα] at hjM
        by_cases hA : onChainA u v
        · refine ⟨β, ?_, ?_⟩
          · simp [M', hαβ.symm, hA]
          · intro j' hj'
            by_cases hj'α : j' = α
            · rw [hj'α] at hj'
              simp only [M', ↓reduceIte] at hj'
              rcases hj' with ⟨_, hnotA⟩ | ⟨s, h1, h2⟩ | h0
              · exact absurd hA hnotA
              · exact absurd ⟨hjM, hstep_β s u v h1 h2⟩ hdisj_AB
              · exact absurd h0 huv
            · by_cases hj'β : j' = β
              · exact hj'β
              · simp only [M', if_neg hj'α, if_neg hj'β] at hj'
                exact absurd ((hjU j' hj').trans hjα) hj'α
        · refine ⟨α, ?_, ?_⟩
          · simp [M', hjM, hA]
          · intro j' hj'
            by_cases hj'α : j' = α
            · exact hj'α
            · by_cases hj'β : j' = β
              · rw [hj'β] at hj'
                simp only [M', if_neg (hj'β ▸ hj'α), ↓reduceIte] at hj'
                rcases hj' with ⟨h1, _⟩ | h1
                · exact absurd ⟨hjM, h1⟩ hdisj_AB
                · exact absurd h1 hA
              · simp only [M', if_neg hj'α, if_neg hj'β] at hj'
                exact absurd ((hjU j' hj').trans hjα) hj'α
      · by_cases hjβ : j = β
        · rw [hjβ] at hjM
          by_cases hB : onChainB u v
          · refine ⟨α, ?_, ?_⟩
            · simp [M', hB]
            · intro j' hj'
              by_cases hj'α : j' = α
              · exact hj'α
              · by_cases hj'β : j' = β
                · rw [hj'β] at hj'
                  simp only [M', if_neg (hj'β ▸ hj'α), ↓reduceIte] at hj'
                  rcases hj' with ⟨_, hnotB⟩ | ⟨s, h1, h2⟩
                  · exact absurd hB hnotB
                  · exact absurd ⟨hstep_α s u v h1 h2, hjM⟩ hdisj_AB
                · simp only [M', if_neg hj'α, if_neg hj'β] at hj'
                  exact absurd ((hjU j' hj').trans hjβ) hj'β
          · refine ⟨β, ?_, ?_⟩
            · simp [M', hαβ.symm, hjM, hB]
            · intro j' hj'
              by_cases hj'α : j' = α
              · rw [hj'α] at hj'
                simp only [M', ↓reduceIte] at hj'
                rcases hj' with ⟨h1, _⟩ | h1 | h0
                · exact absurd ⟨h1, hjM⟩ hdisj_AB
                · exact absurd h1 hB
                · exact absurd h0 huv
              · by_cases hj'β : j' = β
                · exact hj'β
                · simp only [M', if_neg hj'α, if_neg hj'β] at hj'
                  exact absurd ((hjU j' hj').trans hjβ) hj'β
        · refine ⟨j, ?_, ?_⟩
          · simp [M', hjα, hjβ, hjM]
          · intro j' hj'
            by_cases hj'α : j' = α
            · rw [hj'α] at hj'
              simp only [M', ↓reduceIte] at hj'
              rcases hj' with ⟨h1, _⟩ | ⟨s, h1, h2⟩ | h0
              · exact absurd (hjU α h1) (Ne.symm hjα)
              · exact absurd (hjU β (hstep_β s u v h1 h2)) (Ne.symm hjβ)
              · exact absurd h0 huv
            · by_cases hj'β : j' = β
              · rw [hj'β] at hj'
                simp only [M', if_neg (hj'β ▸ hj'α), ↓reduceIte] at hj'
                rcases hj' with ⟨h1, _⟩ | ⟨s, h1, h2⟩
                · exact absurd (hjU β h1) (Ne.symm hjβ)
                · exact absurd (hjU α (hstep_α s u v h1 h2)) (Ne.symm hjα)
              · simp only [M', if_neg hj'α, if_neg hj'β] at hj'
                exact hjU j' hj'
  · intro j u
    rw [outDeg, Set.ncard_le_one_iff (Set.toFinite _)]
    intro v₁ v₂ hv₁ hv₂
    simp only [Set.mem_ofPred_eq] at hv₁ hv₂
    by_cases hjα : j = α
    · rw [hjα] at hv₁ hv₂
      simp only [M', ↓reduceIte] at hv₁ hv₂
      have hc1 : ∀ v₁ v₂, onChainB u v₁ → (M α u v₂ ∧ ¬ onChainA u v₂) → False := by
        intro v₁ v₂ ⟨s, hs1, hs2⟩ ⟨hM2, hnotA⟩
        rcases hparEven s with hnone | ⟨v', hv'⟩
        · change chainStep (M α) (M β) v₀ (2 * s + 1) = some (Sum.inl u) at hs1
          rw [chainStep_succ] at hs1
          change chainStep (M α) (M β) v₀ (2 * s) = none at hnone
          rw [hnone] at hs1; simp at hs1
        · have hM' : M α u v' := hstep_α s u v' hv' hs1
          have hv'eq : v' = v₂ :=
            (Set.ncard_le_one_iff (Set.toFinite ({v : V | M α u v} : Set V))).mp (hMout α u)
              hM' hM2
          subst hv'eq
          exact hnotA ⟨s, hv', hs1⟩
      rcases hv₁ with ⟨h1, hn1⟩ | ⟨s1, hs1a, hs1b⟩ | ⟨rfl, rfl⟩ <;>
        rcases hv₂ with ⟨h2, hn2⟩ | ⟨s2, hs2a, hs2b⟩ | ⟨hu2, hv2⟩
      · exact (Set.ncard_le_one_iff (Set.toFinite ({v : V | M α u v} : Set V))).mp (hMout α u)
          h1 h2
      · exact False.elim (hc1 v₂ v₁ ⟨s2, hs2a, hs2b⟩ ⟨h1, hn1⟩)
      · subst hu2; exact absurd h1 (hαFree v₁)
      · exact False.elim (hc1 v₁ v₂ ⟨s1, hs1a, hs1b⟩ ⟨h2, hn2⟩)
      · have hseq : 2 * s1 + 1 = 2 * s2 + 1 := hinj _ _ _ hs1a hs2a
        have hs : s1 = s2 := by omega
        subst hs
        rw [hs1b] at hs2b
        exact Sum.inr.inj (Option.some.inj hs2b)
      · subst hu2; exact absurd hs1a (hno_u0 s1)
      · exact absurd h2 (hαFree v₂)
      · exact absurd hs2a (hno_u0 s2)
      · exact hv2.symm
    · by_cases hjβ : j = β
      · rw [hjβ] at hv₁ hv₂
        simp only [M', if_neg (hjβ ▸ hjα), ↓reduceIte] at hv₁ hv₂
        have hc1 : ∀ v₁ v₂, onChainA u v₁ → (M β u v₂ ∧ ¬ onChainB u v₂) → False := by
          intro v₁ v₂ ⟨s, hs1, hs2⟩ ⟨hM2, hnotB⟩
          have hsucc : ch (2 * s + 2) = some (Sum.inr v₂) := by
            change chainStep (M α) (M β) v₀ ((2 * s + 1) + 1) = some (Sum.inr v₂)
            rw [chainStep_succ]
            change chainStep (M α) (M β) v₀ (2 * s + 1) = some (Sum.inl u) at hs2
            rw [hs2, Option.map_eq_some_iff]
            exact ⟨v₂, (uniqueNext_eq_some_iff (M β) (hMout β)).mpr hM2, rfl⟩
          exact hnotB ⟨s, hs2, hsucc⟩
        rcases hv₁ with ⟨h1, hn1⟩ | ⟨s1, hs1a, hs1b⟩ <;>
          rcases hv₂ with ⟨h2, hn2⟩ | ⟨s2, hs2a, hs2b⟩
        · exact (Set.ncard_le_one_iff (Set.toFinite ({v : V | M β u v} : Set V))).mp (hMout β u)
            h1 h2
        · exact False.elim (hc1 v₂ v₁ ⟨s2, hs2a, hs2b⟩ ⟨h1, hn1⟩)
        · exact False.elim (hc1 v₁ v₂ ⟨s1, hs1a, hs1b⟩ ⟨h2, hn2⟩)
        · have hseq : 2 * s1 + 1 = 2 * s2 + 1 := hinj _ _ _ hs1b hs2b
          have hs : s1 = s2 := by omega
          subst hs
          rw [hs1a] at hs2a
          exact Sum.inr.inj (Option.some.inj hs2a)
      · simp only [M', if_neg hjα, if_neg hjβ] at hv₁ hv₂
        exact (Set.ncard_le_one_iff (Set.toFinite ({v : V | M j u v} : Set V))).mp (hMout j u)
          hv₁ hv₂
  · intro j v
    rw [inDeg, Set.ncard_le_one_iff (Set.toFinite _)]
    intro u₁ u₂ hu₁ hu₂
    simp only [Set.mem_ofPred_eq] at hu₁ hu₂
    by_cases hjα : j = α
    · rw [hjα] at hu₁ hu₂
      simp only [M', ↓reduceIte] at hu₁ hu₂
      have hc1 : ∀ u₁ u₂, onChainB u₁ v → (M α u₂ v ∧ ¬ onChainA u₂ v) → False := by
        intro u₁ u₂ ⟨s, hs1, hs2⟩ ⟨hM2, hnotA⟩
        have hsucc : ch (2 * (s + 1) + 1) = some (Sum.inl u₂) := by
          change chainStep (M α) (M β) v₀ (2 * (s + 1) + 1) = some (Sum.inl u₂)
          rw [chainStep_succ]
          change chainStep (M α) (M β) v₀ (2 * s + 2) = some (Sum.inr v) at hs2
          rw [show 2 * (s + 1) = 2 * s + 2 by ring, hs2, Option.map_eq_some_iff]
          exact ⟨u₂, (uniquePrev_eq_some_iff (M α) (hMin α)).mpr hM2, rfl⟩
        exact hnotA ⟨s + 1, by rw [show 2 * (s + 1) = 2 * s + 2 by ring]; exact hs2, hsucc⟩
      rcases hu₁ with ⟨h1, hn1⟩ | ⟨s1, hs1a, hs1b⟩ | ⟨hu1, hv1⟩ <;>
        rcases hu₂ with ⟨h2, hn2⟩ | ⟨s2, hs2a, hs2b⟩ | ⟨hu2, hv2⟩
      · exact (Set.ncard_le_one_iff (Set.toFinite ({u : V | M α u v} : Set V))).mp (hMin α v)
          h1 h2
      · exact False.elim (hc1 u₂ u₁ ⟨s2, hs2a, hs2b⟩ ⟨h1, hn1⟩)
      · refine False.elim (hn1 ⟨0, ?_, ?_⟩)
        · rw [hv2]; rfl
        · rw [hv2] at h1
          change chainStep (M α) (M β) v₀ 1 = some (Sum.inl u₁)
          rw [chainStep_succ]
          change Option.map Sum.inl (uniquePrev (M α) v₀) = some (Sum.inl u₁)
          simp only [Option.map_eq_some_iff]
          exact ⟨u₁, (uniquePrev_eq_some_iff (M α) (hMin α)).mpr h1, rfl⟩
      · exact False.elim (hc1 u₁ u₂ ⟨s1, hs1a, hs1b⟩ ⟨h2, hn2⟩)
      · have hseq : 2 * s1 + 2 = 2 * s2 + 2 := hinj _ _ _ hs1b hs2b
        have hs : s1 = s2 := by omega
        subst hs
        rw [hs1a] at hs2a
        exact Sum.inl.inj (Option.some.inj hs2a)
      · rw [hv2] at hs1b
        have h0 : ch 0 = some (Sum.inr v₀) := rfl
        have hcontra := hinj 0 (2 * s1 + 2) _ h0 hs1b
        omega
      · refine False.elim (hn2 ⟨0, ?_, ?_⟩)
        · rw [hv1]; rfl
        · rw [hv1] at h2
          change chainStep (M α) (M β) v₀ 1 = some (Sum.inl u₂)
          rw [chainStep_succ]
          change Option.map Sum.inl (uniquePrev (M α) v₀) = some (Sum.inl u₂)
          simp only [Option.map_eq_some_iff]
          exact ⟨u₂, (uniquePrev_eq_some_iff (M α) (hMin α)).mpr h2, rfl⟩
      · rw [hv1] at hs2b
        have h0 : ch 0 = some (Sum.inr v₀) := rfl
        have hcontra := hinj 0 (2 * s2 + 2) _ h0 hs2b
        omega
      · exact hu1.trans hu2.symm
    · by_cases hjβ : j = β
      · rw [hjβ] at hu₁ hu₂
        simp only [M', if_neg (hjβ ▸ hjα), ↓reduceIte] at hu₁ hu₂
        have hc1 : ∀ u₁ u₂, onChainA u₁ v → (M β u₂ v ∧ ¬ onChainB u₂ v) → False := by
          intro u₁ u₂ ⟨s, hs1, hs2⟩ ⟨hM2, hnotB⟩
          rcases s with _ | s
          · have h0 : ch 0 = some (Sum.inr v₀) := rfl
            rw [Nat.mul_zero, h0] at hs1
            have hv_eq : v = v₀ := Sum.inr.inj (Option.some.inj hs1.symm)
            subst hv_eq
            exact hβFree u₂ hM2
          · rcases hparOdd s with hnone | ⟨u', hu'⟩
            · have h2 : ch (2 * (s + 1)) = none := by
                change chainStep (M α) (M β) v₀ ((2 * s + 1) + 1) = none
                rw [chainStep_succ]
                change chainStep (M α) (M β) v₀ (2 * s + 1) = none at hnone
                rw [hnone]
              rw [h2] at hs1; simp at hs1
            · have hMb' : M β u' v := hstep_β s u' v hu' hs1
              have hu'eq : u' = u₂ :=
                (Set.ncard_le_one_iff (Set.toFinite ({u : V | M β u v} : Set V))).mp (hMin β v)
                  hMb' hM2
              subst hu'eq
              exact hnotB ⟨s, hu', hs1⟩
        rcases hu₁ with ⟨h1, hn1⟩ | ⟨s1, hs1a, hs1b⟩ <;>
          rcases hu₂ with ⟨h2, hn2⟩ | ⟨s2, hs2a, hs2b⟩
        · exact (Set.ncard_le_one_iff (Set.toFinite ({u : V | M β u v} : Set V))).mp (hMin β v)
            h1 h2
        · exact False.elim (hc1 u₂ u₁ ⟨s2, hs2a, hs2b⟩ ⟨h1, hn1⟩)
        · exact False.elim (hc1 u₁ u₂ ⟨s1, hs1a, hs1b⟩ ⟨h2, hn2⟩)
        · have hseq : 2 * s1 = 2 * s2 := hinj _ _ _ hs1a hs2a
          have hs : s1 = s2 := by omega
          subst hs
          rw [hs1b] at hs2b
          exact Sum.inl.inj (Option.some.inj hs2b)
      · simp only [M', if_neg hjα, if_neg hjβ] at hu₁ hu₂
        exact (Set.ncard_le_one_iff (Set.toFinite ({u : V | M j u v} : Set V))).mp (hMin j v)
          hu₁ hu₂

private def relCard {V : Type*} (R : V → V → Prop) : ℕ :=
  ({e : V × V | R e.1 e.2} : Set (V × V)).ncard

theorem konig_digraph_decomp {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (R : V → V → Prop)
    (hOut : ∀ u, outDeg R u ≤ k) (hIn : ∀ v, inDeg R v ≤ k) :
    ∃ M : Fin k → V → V → Prop,
      (∀ j u v, M j u v → R u v) ∧
      (∀ u v, R u v → ∃! j : Fin k, M j u v) ∧
      (∀ j u, outDeg (M j) u ≤ 1) ∧
      (∀ j v, inDeg (M j) v ≤ 1) := by
  have hmain : ∀ m : ℕ, ∀ R : V → V → Prop,
      relCard R ≤ m →
      (∀ u, outDeg R u ≤ k) → (∀ v, inDeg R v ≤ k) →
      ∃ M : Fin k → V → V → Prop,
        (∀ j u v, M j u v → R u v) ∧
        (∀ u v, R u v → ∃! j : Fin k, M j u v) ∧
        (∀ j u, outDeg (M j) u ≤ 1) ∧
        (∀ j v, inDeg (M j) v ≤ 1) := by
    intro m
    induction m with
    | zero =>
      intro R hm _ _
      have h0 : ∀ u v, ¬ R u v := by
        intro u v hR
        have hpos : 0 < relCard R :=
          (Set.ncard_pos (Set.toFinite _)).mpr ⟨(u, v), hR⟩
        omega
      refine ⟨fun _ _ _ => False, by simp, fun u v hR => absurd hR (h0 u v), ?_, ?_⟩
      · intro j u
        have he : ({w : V | False} : Set V) = ∅ := rfl
        simp [outDeg, he]
      · intro j v
        have he : ({u : V | False} : Set V) = ∅ := rfl
        simp [inDeg, he]
    | succ m ih =>
      intro R hm hOut hIn
      by_cases hEmp : ∀ u v, ¬ R u v
      · refine ⟨fun _ _ _ => False, by simp, fun u v hR => absurd hR (hEmp u v), ?_, ?_⟩
        · intro j u
          have he : ({w : V | False} : Set V) = ∅ := rfl
          simp [outDeg, he]
        · intro j v
          have he : ({u : V | False} : Set V) = ∅ := rfl
          simp [inDeg, he]
      · push Not at hEmp
        obtain ⟨u₀, v₀, hR₀⟩ := hEmp
        let R' : V → V → Prop := fun u v => R u v ∧ ¬ (u = u₀ ∧ v = v₀)
        have hm' : relCard R' ≤ m := by
          have hss : ({e : V × V | R' e.1 e.2} : Set (V × V)) ⊂ {e : V × V | R e.1 e.2} := by
            rw [Set.ssubset_iff_subset_ne]
            refine ⟨fun e he => he.1, fun hEq => ?_⟩
            have hmem : (u₀, v₀) ∈ ({e : V × V | R' e.1 e.2} : Set (V × V)) := by
              rw [hEq]; exact hR₀
            exact hmem.2 ⟨rfl, rfl⟩
          have hlt := Set.ncard_lt_ncard hss (Set.toFinite _)
          change relCard R' < relCard R at hlt
          omega
        have hOut' : ∀ u, outDeg R' u ≤ k := fun u => by
          have hsub : ({v : V | R' u v} : Set V) ⊆ {v : V | R u v} := fun v hv => hv.1
          exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (hOut u)
        have hIn' : ∀ v, inDeg R' v ≤ k := fun v => by
          have hsub : ({u : V | R' u v} : Set V) ⊆ {u : V | R u v} := fun u hu => hu.1
          exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (hIn v)
        obtain ⟨M, hMsub, hMpart, hMout, hMin⟩ := ih R' hm' hOut' hIn'
        have hOut0 : outDeg R' u₀ < k := by
          have hss : ({v : V | R' u₀ v} : Set V) ⊂ {v : V | R u₀ v} := by
            rw [Set.ssubset_iff_subset_ne]
            refine ⟨fun v hv => hv.1, fun hEq => ?_⟩
            have hmem : v₀ ∈ ({v : V | R' u₀ v} : Set V) := by rw [hEq]; exact hR₀
            exact hmem.2 ⟨rfl, rfl⟩
          exact lt_of_lt_of_le (Set.ncard_lt_ncard hss (Set.toFinite _)) (hOut u₀)
        have hIn0 : inDeg R' v₀ < k := by
          have hss : ({u : V | R' u v₀} : Set V) ⊂ {u : V | R u v₀} := by
            rw [Set.ssubset_iff_subset_ne]
            refine ⟨fun u hu => hu.1, fun hEq => ?_⟩
            have hmem : u₀ ∈ ({u : V | R' u v₀} : Set V) := by rw [hEq]; exact hR₀
            exact hmem.2 ⟨rfl, rfl⟩
          exact lt_of_lt_of_le (Set.ncard_lt_ncard hss (Set.toFinite _)) (hIn v₀)
        obtain ⟨α, hαFree⟩ := exists_free_out_color R' M hMsub hMpart u₀ hOut0
        obtain ⟨β, hβFree⟩ := exists_free_in_color R' M hMsub hMpart v₀ hIn0
        by_cases hαβ : α = β
        · let M' : Fin k → V → V → Prop := fun j u v =>
            if j = α then M α u v ∨ (u = u₀ ∧ v = v₀) else M j u v
          have hβFree' : ∀ u, ¬ M α u v₀ := hαβ ▸ hβFree
          refine ⟨M', ?_, ?_, ?_, ?_⟩
          · intro j u v hMj
            by_cases hj : j = α
            · rw [hj] at hMj
              simp only [M', ↓reduceIte] at hMj
              rcases hMj with hM | ⟨rfl, rfl⟩
              · exact (hMsub α u v hM).1
              · exact hR₀
            · simp only [M', if_neg hj] at hMj
              exact (hMsub j u v hMj).1
          · intro u v hRuv
            by_cases huv : u = u₀ ∧ v = v₀
            · rcases huv with ⟨rfl, rfl⟩
              refine ⟨α, ?_, ?_⟩
              · simp [M']
              · intro j hj
                by_cases hjα : j = α
                · exact hjα
                · simp only [M', if_neg hjα] at hj
                  exact absurd (hMsub j u v hj).2 (fun h => h ⟨rfl, rfl⟩)
            · have hR'uv : R' u v := ⟨hRuv, huv⟩
              obtain ⟨j, hjM, hjU⟩ := hMpart u v hR'uv
              refine ⟨j, ?_, ?_⟩
              · by_cases hjα : j = α
                · rw [hjα] at hjM; simp [M', hjα, hjM]
                · simp [M', hjα, hjM]
              · intro j' hj'
                by_cases hj'α : j' = α
                · rw [hj'α] at hj'
                  simp only [M', ↓reduceIte] at hj'
                  rcases hj' with h | h
                  · exact hj'α.trans (hjU α h)
                  · exact absurd h huv
                · simp only [M', if_neg hj'α] at hj'
                  exact hjU j' hj'
          · intro j u
            rw [outDeg, Set.ncard_le_one_iff (Set.toFinite _)]
            intro v₁ v₂ hv₁ hv₂
            simp only [Set.mem_ofPred_eq] at hv₁ hv₂
            by_cases hj : j = α
            · rw [hj] at hv₁ hv₂
              simp only [M', ↓reduceIte] at hv₁ hv₂
              rcases hv₁ with h1 | ⟨hu1, rfl⟩ <;> rcases hv₂ with h2 | ⟨hu2, rfl⟩
              · exact (Set.ncard_le_one_iff (Set.toFinite ({v : V | M α u v} : Set V))).mp
                  (hMout α u) h1 h2
              · subst hu2; exact absurd h1 (hαFree v₁)
              · subst hu1; exact absurd h2 (hαFree v₂)
              · rfl
            · simp only [M', if_neg hj] at hv₁ hv₂
              exact (Set.ncard_le_one_iff (Set.toFinite ({v : V | M j u v} : Set V))).mp
                (hMout j u) hv₁ hv₂
          · intro j v
            rw [inDeg, Set.ncard_le_one_iff (Set.toFinite _)]
            intro u₁ u₂ hu₁ hu₂
            simp only [Set.mem_ofPred_eq] at hu₁ hu₂
            by_cases hj : j = α
            · rw [hj] at hu₁ hu₂
              simp only [M', ↓reduceIte] at hu₁ hu₂
              rcases hu₁ with h1 | ⟨rfl, hv1⟩ <;> rcases hu₂ with h2 | ⟨rfl, hv2⟩
              · exact (Set.ncard_le_one_iff (Set.toFinite ({u : V | M α u v} : Set V))).mp
                  (hMin α v) h1 h2
              · subst hv2; exact absurd h1 (hβFree' u₁)
              · subst hv1; exact absurd h2 (hβFree' u₂)
              · rfl
            · simp only [M', if_neg hj] at hu₁ hu₂
              exact (Set.ncard_le_one_iff (Set.toFinite ({u : V | M j u v} : Set V))).mp
                (hMin j v) hu₁ hu₂
        · exact konig_kempe_swap R R' u₀ v₀ hR₀ (fun _ _ => Iff.rfl) M hMsub hMpart hMout hMin
            α β hαFree hβFree hαβ
  exact hmain (relCard R) R le_rfl hOut hIn

lemma isLinearForest_of_deg_le_one {V : Type*} [Fintype V] (F : SimpleGraph V)
    (hdeg : ∀ v, (F.neighborSet v).ncard ≤ 1) :
    LinearArboricityConjecture.IsLinearForest F := by
  refine ⟨fun v p hp => ?_, fun v => (hdeg v).trans (by omega)⟩
  have hlen := hp.three_le_length
  cases p with
  | nil => exact absurd hp Walk.not_isCycle_nil
  | @cons _ v₁ _ hadj1 q =>
    have hq_path : q.IsPath := by simpa [Walk.tail_cons] using hp.isPath_tail
    have hq_len : 2 ≤ q.length := by
      simp only [Walk.length_cons] at hlen
      omega
    have hqrev_len : 2 ≤ q.reverse.length := by
      simpa [Walk.length_reverse] using hq_len
    have hqrev_nodup : q.reverse.support.Nodup := by
      rw [Walk.support_reverse]
      exact List.nodup_reverse.mpr hq_path.support_nodup
    cases hqr : q.reverse with
    | nil => simp [hqr] at hqrev_len
    | @cons _ w _ hadj_last s =>
      rw [hqr] at hqrev_len hqrev_nodup
      have hs_len : 1 ≤ s.length := by
        simp only [Walk.length_cons] at hqrev_len
        omega
      cases s with
      | nil => simp at hs_len
      | @cons _ z _ hadj_s t =>
        simp only [Walk.support_cons, List.nodup_cons] at hqrev_nodup
        have hw_notin : w ∉ t.support := hqrev_nodup.2.1
        have hv₁_in : v₁ ∈ t.support := Walk.end_mem_support t
        have hne : w ≠ v₁ := fun h => hw_notin (h ▸ hv₁_in)
        exact hne ((Set.ncard_le_one_iff (Set.toFinite (F.neighborSet v))).mp (hdeg v) hadj_last hadj1)

theorem greedy_matching_decomp {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj] (hΔ : H.maxDegree ≤ k) :
    ∃ F : Fin (2 * k) → SimpleGraph V,
      (∀ c, (∀ v, ((F c).neighborSet v).ncard ≤ 1) ∧ (F c) ≤ H) ∧
      (∀ u v, H.Adj u v ↔ ∃! c, (F c).Adj u v) := by
  have hmain : ∀ m : ℕ, ∀ H : SimpleGraph V, [DecidableRel H.Adj] →
      H.edgeFinset.card ≤ m → H.maxDegree ≤ k →
      ∃ F : Fin (2 * k) → SimpleGraph V,
        (∀ c, (∀ v, ((F c).neighborSet v).ncard ≤ 1) ∧ (F c) ≤ H) ∧
        (∀ u v, H.Adj u v ↔ ∃! c, (F c).Adj u v) := by
    intro m
    induction m with
    | zero =>
      intro H _ hm _
      have hHbot : ∀ u v, ¬ H.Adj u v := by
        intro u v h
        have hpos : 0 < H.edgeFinset.card := Finset.card_pos.mpr ⟨s(u, v), mem_edgeFinset.mpr h⟩
        omega
      refine ⟨fun _ => ⊥, fun _ => ⟨fun v => by simp, bot_le⟩, fun u v => ?_⟩
      simp [hHbot u v]
    | succ m ih =>
      intro H _ hm hΔ
      by_cases hEmp : H.edgeFinset = ∅
      · have hHbot : ∀ u v, ¬ H.Adj u v := by
          intro u v h
          have : s(u, v) ∈ H.edgeFinset := mem_edgeFinset.mpr h
          rw [hEmp] at this
          simp at this
        refine ⟨fun _ => ⊥, fun _ => ⟨fun v => by simp, bot_le⟩, fun u v => ?_⟩
        simp [hHbot u v]
      · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hEmp
        induction e using Sym2.ind with
        | _ u₀ v₀ =>
          have hadj₀ : H.Adj u₀ v₀ := mem_edgeFinset.mp he
          have hkpos : 1 ≤ k := by
            have hd : 1 ≤ H.degree u₀ := by
              rw [← SimpleGraph.card_neighborFinset_eq_degree]
              exact Finset.card_pos.mpr ⟨v₀, by simp only [mem_neighborFinset]; exact hadj₀⟩
            exact hd.trans ((H.degree_le_maxDegree u₀).trans hΔ)
          let H' := H.deleteEdges {s(u₀, v₀)}
          have hm' : H'.edgeFinset.card ≤ m := by
            have hss : H'.edgeFinset ⊂ H.edgeFinset := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨fun x hx => ?_, fun hEq => ?_⟩
              · rw [mem_edgeFinset] at hx ⊢
                exact (edgeSet_deleteEdges _ ▸ hx).1
              · have he' : s(u₀, v₀) ∈ H'.edgeFinset := by rw [hEq]; exact he
                rw [mem_edgeFinset] at he'
                exact (edgeSet_deleteEdges _ ▸ he').2 rfl
            have := Finset.card_lt_card hss
            omega
          have hΔ' : H'.maxDegree ≤ k := by
            refine H'.maxDegree_le_of_forall_degree_le k fun v => ?_
            exact (SimpleGraph.degree_le_of_le (deleteEdges_le _) : H'.degree v ≤ H.degree v).trans
              ((H.degree_le_maxDegree v).trans hΔ)
          obtain ⟨F, hFprop, hFpart⟩ := ih H' hm' hΔ'
          have hdeg_u₀ : H'.degree u₀ ≤ k - 1 := by
            have hss : H'.neighborFinset u₀ ⊂ H.neighborFinset u₀ := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨fun x hx => ?_, fun hEq => ?_⟩
              · rw [mem_neighborFinset] at hx ⊢
                exact deleteEdges_le _ hx
              · have hv' : v₀ ∈ H'.neighborFinset u₀ := by
                  rw [hEq, mem_neighborFinset]; exact hadj₀
                rw [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff] at hv'
                exact hv'.2 rfl
            have := Finset.card_lt_card hss
            simp only [SimpleGraph.card_neighborFinset_eq_degree] at this
            have := (H.degree_le_maxDegree u₀).trans hΔ
            omega
          have hdeg_v₀ : H'.degree v₀ ≤ k - 1 := by
            have hss : H'.neighborFinset v₀ ⊂ H.neighborFinset v₀ := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨fun x hx => ?_, fun hEq => ?_⟩
              · rw [mem_neighborFinset] at hx ⊢
                exact deleteEdges_le _ hx
              · have hu' : u₀ ∈ H'.neighborFinset v₀ := by
                  rw [hEq, mem_neighborFinset]; exact hadj₀.symm
                rw [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_swap] at hu'
                exact hu'.2 rfl
            have := Finset.card_lt_card hss
            simp only [SimpleGraph.card_neighborFinset_eq_degree] at this
            have := (H.degree_le_maxDegree v₀).trans hΔ
            omega
          let usedU : Finset (Fin (2 * k)) := Finset.univ.filter (fun c => ∃ w, (F c).Adj u₀ w)
          let usedV : Finset (Fin (2 * k)) := Finset.univ.filter (fun c => ∃ w, (F c).Adj v₀ w)
          let pickU : Fin (2 * k) → V := fun c => if hc : ∃ w, (F c).Adj u₀ w then hc.choose else u₀
          let pickV : Fin (2 * k) → V := fun c => if hc : ∃ w, (F c).Adj v₀ w then hc.choose else v₀
          have husedU : usedU.card ≤ H'.degree u₀ := by
            refine Finset.card_le_card_of_injOn pickU ?_ ?_
            · intro c hc
              simp only [Finset.mem_coe, usedU, Finset.mem_filter, Finset.mem_univ, true_and] at hc
              simp only [Finset.mem_coe, pickU, dif_pos hc, mem_neighborFinset]
              exact (hFprop c).2 hc.choose_spec
            · intro c₁ hc₁ c₂ hc₂ hEq
              simp only [Finset.mem_coe, usedU, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
              simp only [pickU, dif_pos hc₁, dif_pos hc₂] at hEq
              have ha₁ : (F c₁).Adj u₀ hc₁.choose := hc₁.choose_spec
              have ha₂ : (F c₂).Adj u₀ hc₁.choose := hEq ▸ hc₂.choose_spec
              obtain ⟨c, -, hcU⟩ := (hFpart _ _).mp ((hFprop c₁).2 ha₁)
              exact (hcU c₁ ha₁).trans (hcU c₂ ha₂).symm
          have husedV : usedV.card ≤ H'.degree v₀ := by
            refine Finset.card_le_card_of_injOn pickV ?_ ?_
            · intro c hc
              simp only [Finset.mem_coe, usedV, Finset.mem_filter, Finset.mem_univ, true_and] at hc
              simp only [Finset.mem_coe, pickV, dif_pos hc, mem_neighborFinset]
              exact (hFprop c).2 hc.choose_spec
            · intro c₁ hc₁ c₂ hc₂ hEq
              simp only [Finset.mem_coe, usedV, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
              simp only [pickV, dif_pos hc₁, dif_pos hc₂] at hEq
              have ha₁ : (F c₁).Adj v₀ hc₁.choose := hc₁.choose_spec
              have ha₂ : (F c₂).Adj v₀ hc₁.choose := hEq ▸ hc₂.choose_spec
              obtain ⟨c, -, hcU⟩ := (hFpart _ _).mp ((hFprop c₁).2 ha₁)
              exact (hcU c₁ ha₁).trans (hcU c₂ ha₂).symm
          have hlt : (usedU ∪ usedV).card < (Finset.univ : Finset (Fin (2 * k))).card := by
            have h1 : (usedU ∪ usedV).card ≤ usedU.card + usedV.card := Finset.card_union_le _ _
            rw [Finset.card_univ, Fintype.card_fin]
            omega
          obtain ⟨c₀, -, hc₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
          have hc₀U : ∀ w, ¬ (F c₀).Adj u₀ w := fun w hw =>
            hc₀ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨w, hw⟩⟩))
          have hc₀V : ∀ w, ¬ (F c₀).Adj v₀ w := fun w hw =>
            hc₀ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨w, hw⟩⟩))
          let edgeG : SimpleGraph V := SimpleGraph.fromEdgeSet {s(u₀, v₀)}
          let F' : Fin (2 * k) → SimpleGraph V := fun c =>
            if c = c₀ then F c₀ ⊔ edgeG else F c
          refine ⟨F', ?_, ?_⟩
          · intro c
            by_cases hc : c = c₀
            · rw [hc]
              refine ⟨fun v => ?_, fun u v h => ?_⟩
              · simp only [F', ↓reduceIte]
                by_cases hvu : v = u₀
                · subst hvu
                  have hnb : (F c₀ ⊔ edgeG).neighborSet v = {v₀} := by
                    ext w
                    simp only [mem_neighborSet, sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
                      edgeG, hc₀U w, false_or]
                    constructor
                    · rintro ⟨hed, hne⟩
                      rw [Sym2.eq_iff] at hed
                      rcases hed with ⟨_, rfl⟩ | ⟨h1, _⟩
                      · rfl
                      · exact absurd h1 hadj₀.ne
                    · rintro rfl
                      exact ⟨rfl, hadj₀.ne⟩
                  rw [hnb, Set.ncard_singleton]
                · by_cases hvv : v = v₀
                  · subst hvv
                    have hnb : (F c₀ ⊔ edgeG).neighborSet v = {u₀} := by
                      ext w
                      simp only [mem_neighborSet, sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
                        edgeG, hc₀V w, false_or]
                      constructor
                      · rintro ⟨hed, hne⟩
                        rw [Sym2.eq_iff] at hed
                        rcases hed with ⟨h1, _⟩ | ⟨_, rfl⟩
                        · exact absurd h1 hadj₀.ne.symm
                        · rfl
                      · rintro rfl
                        exact ⟨Sym2.eq_swap, hadj₀.ne.symm⟩
                    rw [hnb, Set.ncard_singleton]
                  · have hnb : (F c₀ ⊔ edgeG).neighborSet v = (F c₀).neighborSet v := by
                      ext w
                      simp [mem_neighborSet, edgeG, hvu, hvv]
                    rw [hnb]
                    exact (hFprop c₀).1 v
              · simp only [F', ↓reduceIte, sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
                  Sym2.eq_iff, edgeG] at h
                rcases h with hF | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
                · exact deleteEdges_le _ ((hFprop c₀).2 hF)
                · exact hadj₀
                · exact hadj₀.symm
            · simp only [F', if_neg hc]
              exact ⟨(hFprop c).1, (hFprop c).2.trans (deleteEdges_le _)⟩
          · intro u v
            constructor
            · intro hH
              by_cases hed : s(u, v) = s(u₀, v₀)
              · refine ⟨c₀, ?_, ?_⟩
                · simp only [F', ↓reduceIte, sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff, edgeG]
                  right
                  exact ⟨hed, hH.ne⟩
                · intro c hc
                  by_cases hcc : c = c₀
                  · exact hcc
                  · simp only [F', if_neg hcc] at hc
                    have hH' := (hFprop c).2 hc
                    rw [deleteEdges_adj, Set.mem_singleton_iff] at hH'
                    exact absurd hed hH'.2
              · have hH' : H'.Adj u v := deleteEdges_adj.mpr ⟨hH, hed⟩
                obtain ⟨c, hcF, hcU⟩ := (hFpart u v).mp hH'
                refine ⟨c, ?_, ?_⟩
                · by_cases hcc : c = c₀
                  · rw [hcc] at hcF; simp [F', hcc, hcF]
                  · simp [F', hcc, hcF]
                · intro c' hc'
                  by_cases hc'c₀ : c' = c₀
                  · rw [hc'c₀] at hc'
                    simp only [F', ↓reduceIte, sup_adj, fromEdgeSet_adj,
                      Set.mem_singleton_iff, edgeG] at hc'
                    rcases hc' with hFc₀ | ⟨hed', _⟩
                    · exact hc'c₀.trans (hcU c₀ hFc₀)
                    · exact absurd hed' hed
                  · simp only [F', if_neg hc'c₀] at hc'
                    exact hcU c' hc'
            · rintro ⟨c, hc, -⟩
              by_cases hcc : c = c₀
              · rw [hcc] at hc
                simp only [F', ↓reduceIte, sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
                  edgeG] at hc
                rcases hc with hF | ⟨hed, _⟩
                · exact deleteEdges_le _ ((hFprop c₀).2 hF)
                · rw [Sym2.eq_iff] at hed
                  rcases hed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact hadj₀
                  · exact hadj₀.symm
              · simp only [F', if_neg hcc] at hc
                exact deleteEdges_le _ ((hFprop c).2 hc)
  exact hmain H.edgeFinset.card H le_rfl hΔ

end Konig

section Step2Coloring

def fixVEquiv {V α : Type*} [DecidableEq V] (v : V) :
    (V → α) ≃ α × ({x : V // x ≠ v} → α) where
  toFun c := (c v, fun x => c x.1)
  invFun p x := if h : x = v then p.1 else p.2 ⟨x, h⟩
  left_inv c := by
    ext x
    by_cases h : x = v <;> simp [h]
  right_inv p := by
    rcases p with ⟨a, f⟩
    apply Prod.ext
    · simp
    · ext x
      simp [x.2]

theorem step2_vertex_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : V → V → Prop) (hDsub : ∀ u v, D u v → G.Adj u v)
    (Δ r p : ℕ) [Fact p.Prime]
    (hΔ : G.maxDegree ≤ Δ) (hr : ∀ v, outDeg D v ≤ r ∧ inDeg D v ≤ r)
    (δ : ℝ) (hδ : 0 < δ)
    (hLLL : 4 * (2 * (p : ℝ) *
      Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * ((r : ℝ) / (p : ℝ))))) *
      (((Δ ^ 2 + Δ + 1 : ℕ) : ℝ) + 1) ≤ 1) :
    ∃ c : V → ZMod p, ∀ v (j : ZMod p),
      outDeg (fun x y => D x y ∧ c y = c x + j) v ≤ Nat.floor ((1 + δ) * ((r : ℝ) / (p : ℝ))) ∧
      inDeg (fun x y => D x y ∧ c y = c x + j) v ≤ Nat.floor ((1 + δ) * ((r : ℝ) / (p : ℝ))) := by
  let d_max : ℕ := Nat.floor ((1 + δ) * ((r : ℝ) / (p : ℝ)))
  let μ : ℝ := (r : ℝ) / (p : ℝ)
  let p_bad : ℝ := 2 * (p : ℝ) * Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ))
  let S : V → Finset V := fun v => insert v (G.neighborFinset v)
  let Γ : V → Finset V := fun v => (S v).biUnion S
  let A : V → Finset (V → ZMod p) := fun v =>
    Finset.univ.filter (fun c => ∃ j : ZMod p,
      d_max < outDeg (fun x y => D x y ∧ c y = c x + j) v ∨
      d_max < inDeg (fun x y => D x y ∧ c y = c x + j) v)
  have hp_pos : 0 < p := Nat.Prime.pos Fact.out
  have hp_real : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_pos
  have hS_symm : ∀ a b : V, a ∈ S b ↔ b ∈ S a := by
    intro a b
    simp only [S, Finset.mem_insert, mem_neighborFinset]
    constructor <;> rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h.symm
    · exact Or.inl rfl
    · exact Or.inr h.symm
  have hAS : ∀ v, DependsOn (S v) (A v) := by
    intro v c₁ c₂ hagree
    have hc_v : c₁ v = c₂ v := hagree v (Finset.mem_insert_self v _)
    have hout_eq : ∀ j,
        outDeg (fun x y => D x y ∧ c₁ y = c₁ x + j) v =
        outDeg (fun x y => D x y ∧ c₂ y = c₂ x + j) v := by
      intro j
      dsimp only [outDeg]
      congr 1
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor <;> rintro ⟨hD, hc⟩ <;> refine ⟨hD, ?_⟩
      · have hy : y ∈ S v := Finset.mem_insert_of_mem (by simp only [mem_neighborFinset]; exact hDsub v y hD)
        rw [← hagree y hy, ← hc_v]; exact hc
      · have hy : y ∈ S v := Finset.mem_insert_of_mem (by simp only [mem_neighborFinset]; exact hDsub v y hD)
        rw [hagree y hy, hc_v]; exact hc
    have hin_eq : ∀ j,
        inDeg (fun x y => D x y ∧ c₁ y = c₁ x + j) v =
        inDeg (fun x y => D x y ∧ c₂ y = c₂ x + j) v := by
      intro j
      dsimp only [inDeg]
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor <;> rintro ⟨hD, hc⟩ <;> refine ⟨hD, ?_⟩
      · have hx : x ∈ S v := Finset.mem_insert_of_mem (by simp only [mem_neighborFinset]; exact (hDsub x v hD).symm)
        rw [← hagree x hx, ← hc_v]; exact hc
      · have hx : x ∈ S v := Finset.mem_insert_of_mem (by simp only [mem_neighborFinset]; exact (hDsub x v hD).symm)
        rw [hagree x hx, hc_v]; exact hc
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨j, h | h⟩
    · exact ⟨j, Or.inl (by rw [← hout_eq j]; exact h)⟩
    · exact ⟨j, Or.inr (by rw [← hin_eq j]; exact h)⟩
    · exact ⟨j, Or.inl (by rw [hout_eq j]; exact h)⟩
    · exact ⟨j, Or.inr (by rw [hin_eq j]; exact h)⟩
  have hΓ_card : ∀ v, (Γ v).card ≤ Δ ^ 2 + Δ + 1 := by
    intro v
    have hsub : Γ v ⊆ S v ∪ (G.neighborFinset v).biUnion (fun u => G.neighborFinset u) := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      rcases hx with ⟨u, hu, hxu⟩
      rcases Finset.mem_insert.mp hu with rfl | huN
      · exact Finset.mem_union_left _ hxu
      · rcases Finset.mem_insert.mp hxu with rfl | hxuN
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem huN)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, huN, hxuN⟩)
    have hS : (S v).card ≤ Δ + 1 := by
      calc (S v).card ≤ (G.neighborFinset v).card + 1 := Finset.card_insert_le _ _
        _ = G.degree v + 1 := by rw [G.card_neighborFinset_eq_degree]
        _ ≤ Δ + 1 := Nat.add_le_add_right (le_trans (G.degree_le_maxDegree v) hΔ) 1
    have hbi : ((G.neighborFinset v).biUnion (fun u => G.neighborFinset u)).card ≤ Δ ^ 2 := by
      calc ((G.neighborFinset v).biUnion (fun u => G.neighborFinset u)).card
          ≤ ∑ u ∈ G.neighborFinset v, (G.neighborFinset u).card := Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ G.neighborFinset v, Δ := by
            refine Finset.sum_le_sum fun u _ => ?_
            rw [G.card_neighborFinset_eq_degree]
            exact le_trans (G.degree_le_maxDegree u) hΔ
        _ = (G.neighborFinset v).card * Δ := Finset.sum_const _
        _ ≤ Δ * Δ := Nat.mul_le_mul_right Δ (by rw [G.card_neighborFinset_eq_degree]; exact le_trans (G.degree_le_maxDegree v) hΔ)
        _ = Δ ^ 2 := (sq Δ).symm
    calc (Γ v).card ≤ (S v ∪ (G.neighborFinset v).biUnion (fun u => G.neighborFinset u)).card := Finset.card_le_card hsub
      _ ≤ (S v).card + ((G.neighborFinset v).biUnion (fun u => G.neighborFinset u)).card := Finset.card_union_le _ _
      _ ≤ (Δ + 1) + Δ ^ 2 := Nat.add_le_add hS hbi
      _ = Δ ^ 2 + Δ + 1 := by omega
  have hp_nonneg : 0 ≤ p_bad := by
    positivity
  have hlop : ∀ v : V, ∀ T : Finset V, v ∉ T → (∀ u ∈ T, u ∉ Γ v) →
      ((A v ∩ good A T).card : ℝ) ≤ p_bad * ((good A T).card : ℝ) := by
    intro v T hvT hTΓ
    let X' := {x : V // x ≠ v}
    have hgood_dep : DependsOn (T.biUnion S) (good A T) := dependsOn_good A S hAS T
    have hv_not_mem : v ∉ T.biUnion S := by
      intro hv
      rw [Finset.mem_biUnion] at hv
      rcases hv with ⟨u, huT, hvu⟩
      have huΓ : u ∈ Γ v := Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self v _, (hS_symm v u).mp hvu⟩
      exact hTΓ u huT huΓ
    let G_sub : Finset (X' → ZMod p) :=
      Finset.univ.filter (fun c' => (fixVEquiv v).symm (0, c') ∈ good A T)
    have hgood_iff : ∀ c : V → ZMod p, c ∈ good A T ↔ (fixVEquiv v c).2 ∈ G_sub := by
      intro c
      simp only [G_sub, Finset.mem_filter, Finset.mem_univ, true_and]
      apply hgood_dep
      intro y hy
      have hyv : y ≠ v := fun h => hv_not_mem (h ▸ hy)
      simp [fixVEquiv, hyv]
    have hgood_card : (good A T).card = p * G_sub.card := by
      have hbi : (good A T).card = ((Finset.univ : Finset (ZMod p)) ×ˢ G_sub).card := by
        refine Finset.card_bij (fun c _ => fixVEquiv v c) ?_ ?_ ?_
        · intro c hc
          simp only [Finset.mem_product, Finset.mem_univ, true_and]
          exact (hgood_iff c).mp hc
        · intro c₁ _ c₂ _ h
          exact (fixVEquiv v).injective h
        · rintro ⟨c₀, c'⟩ hmem
          simp only [Finset.mem_product, Finset.mem_univ, true_and] at hmem
          refine ⟨(fixVEquiv v).symm (c₀, c'), ?_, (fixVEquiv v).apply_symm_apply _⟩
          rw [hgood_iff, (fixVEquiv v).apply_symm_apply]
          exact hmem
      rw [hbi, Finset.card_product, Finset.card_univ, ZMod.card]
    let T' : Finset X' := Finset.univ.filter (fun x => x.1 ∈ T.biUnion S)
    let N' : Finset X' := Finset.univ.filter (fun x => x.1 ∈ G.neighborFinset v)
    let outN' : Finset X' := Finset.univ.filter (fun x => D v x.1)
    let inN' : Finset X' := Finset.univ.filter (fun x => D x.1 v)
    have hGsub_dep : DependsOn T' G_sub := by
      intro c₁' c₂' hagree
      simp only [G_sub, Finset.mem_filter, Finset.mem_univ, true_and]
      apply hgood_dep
      intro y hy
      have hyv : y ≠ v := fun h => hv_not_mem (h ▸ hy)
      have hyT' : (⟨y, hyv⟩ : X') ∈ T' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
      simpa [fixVEquiv, hyv] using hagree ⟨y, hyv⟩ hyT'
    have hdisj : Disjoint N' T' := by
      rw [Finset.disjoint_left]
      intro x hxN hxT
      simp only [N', Finset.mem_filter, Finset.mem_univ, true_and] at hxN
      simp only [T', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hxT
      rcases hxT with ⟨u, huT, hxu⟩
      have hxSv : x.1 ∈ S v := Finset.mem_insert_of_mem hxN
      have huΓ : u ∈ Γ v := Finset.mem_biUnion.mpr ⟨x.1, hxSv, (hS_symm x.1 u).mp hxu⟩
      exact hTΓ u huT huΓ
    have hout_sub : outN' ⊆ N' := by
      intro x hx
      simp only [outN', Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [N', Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset]
      exact hDsub v x.1 hx
    have hin_sub : inN' ⊆ N' := by
      intro x hx
      simp only [inN', Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [N', Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset]
      exact (hDsub x.1 v hx).symm
    let E_out : ZMod p → ZMod p → Finset (X' → ZMod p) := fun c₀ j =>
      Finset.univ.filter (fun c' => (1 + δ) * μ ≤ ((outN'.filter (fun x => c' x ∈ ({c₀ + j} : Finset (ZMod p)))).card : ℝ))
    let E_in : ZMod p → ZMod p → Finset (X' → ZMod p) := fun c₀ j =>
      Finset.univ.filter (fun c' => (1 + δ) * μ ≤ ((inN'.filter (fun x => c' x ∈ ({c₀ - j} : Finset (ZMod p)))).card : ℝ))
    have hEout_dep : ∀ c₀ j, DependsOn N' (E_out c₀ j) := by
      intro c₀ j c₁' c₂' hagree
      have hfc : outN'.filter (fun x => c₁' x ∈ ({c₀ + j} : Finset (ZMod p))) =
                 outN'.filter (fun x => c₂' x ∈ ({c₀ + j} : Finset (ZMod p))) := by
        ext x
        simp only [Finset.mem_filter]
        constructor <;> rintro ⟨hx, hmem⟩ <;> refine ⟨hx, ?_⟩
        · rw [← hagree x (hout_sub hx)]; exact hmem
        · rw [hagree x (hout_sub hx)]; exact hmem
      simp only [E_out, Finset.mem_filter, Finset.mem_univ, true_and, hfc]
    have hEin_dep : ∀ c₀ j, DependsOn N' (E_in c₀ j) := by
      intro c₀ j c₁' c₂' hagree
      have hfc : inN'.filter (fun x => c₁' x ∈ ({c₀ - j} : Finset (ZMod p))) =
                 inN'.filter (fun x => c₂' x ∈ ({c₀ - j} : Finset (ZMod p))) := by
        ext x
        simp only [Finset.mem_filter]
        constructor <;> rintro ⟨hx, hmem⟩ <;> refine ⟨hx, ?_⟩
        · rw [← hagree x (hin_sub hx)]; exact hmem
        · rw [hagree x (hin_sub hx)]; exact hmem
      simp only [E_in, Finset.mem_filter, Finset.mem_univ, true_and, hfc]
    have hEout_bound : ∀ c₀ j, ((E_out c₀ j ∩ G_sub).card : ℝ) ≤
        Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (G_sub.card : ℝ) := by
      intro c₀ j
      have hdisj_card := card_inter_of_dependsOn_disjoint hdisj (hEout_dep c₀ j) hGsub_dep
      have hμ_out : ∑ _x ∈ outN', (({c₀ + j} : Finset (ZMod p)).card : ℝ) / (Fintype.card (ZMod p) : ℝ) ≤ μ := by
        simp only [Finset.card_singleton, Nat.cast_one, ZMod.card, Finset.sum_const, nsmul_eq_mul, mul_one_div]
        have hout_card : outN'.card ≤ r := by
          have heq : outN'.card = outDeg D v := by
            rw [outDeg_eq_filter_card]
            refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
            · intro x hx
              simp only [outN', Finset.mem_filter, Finset.mem_univ, true_and] at hx
              simp [hx]
            · intro x₁ _ x₂ _ h; exact Subtype.ext h
            · intro y hy
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
              exact ⟨⟨y, (hDsub v y hy).ne.symm⟩, by simp [outN', hy], rfl⟩
          rw [heq]; exact (hr v).1
        rw [div_le_div_iff_of_pos_right hp_real]
        exact Nat.cast_le.mpr hout_card
      have hch := chernoff_prod_upper_sub outN' (fun _ => {c₀ + j}) μ δ (by rw [ZMod.card]; exact hp_pos) hδ hμ_out
      have hpos : (0 : ℝ) < (Fintype.card (X' → ZMod p) : ℝ) := by
        rw [Fintype.card_pi]; positivity
      have hmul : ((E_out c₀ j ∩ G_sub).card : ℝ) * (Fintype.card (X' → ZMod p) : ℝ) ≤
          (Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (G_sub.card : ℝ)) *
          (Fintype.card (X' → ZMod p) : ℝ) := by
        calc ((E_out c₀ j ∩ G_sub).card : ℝ) * (Fintype.card (X' → ZMod p) : ℝ)
            = ((E_out c₀ j).card : ℝ) * (G_sub.card : ℝ) := by exact_mod_cast hdisj_card
          _ ≤ (Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (Fintype.card (X' → ZMod p) : ℝ)) * (G_sub.card : ℝ) := by
              exact mul_le_mul_of_nonneg_right hch (Nat.cast_nonneg _)
          _ = _ := by ring
      exact le_of_mul_le_mul_right hmul hpos
    have hEin_bound : ∀ c₀ j, ((E_in c₀ j ∩ G_sub).card : ℝ) ≤
        Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (G_sub.card : ℝ) := by
      intro c₀ j
      have hdisj_card := card_inter_of_dependsOn_disjoint hdisj (hEin_dep c₀ j) hGsub_dep
      have hμ_in : ∑ _x ∈ inN', (({c₀ - j} : Finset (ZMod p)).card : ℝ) / (Fintype.card (ZMod p) : ℝ) ≤ μ := by
        simp only [Finset.card_singleton, Nat.cast_one, ZMod.card, Finset.sum_const, nsmul_eq_mul, mul_one_div]
        have hin_card : inN'.card ≤ r := by
          have heq : inN'.card = inDeg D v := by
            rw [show inDeg D v = outDeg (fun x y => D y x) v from rfl, outDeg_eq_filter_card]
            refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
            · intro x hx
              simp only [inN', Finset.mem_filter, Finset.mem_univ, true_and] at hx
              simp [hx]
            · intro x₁ _ x₂ _ h; exact Subtype.ext h
            · intro y hy
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
              exact ⟨⟨y, (hDsub y v hy).ne⟩, by simp [inN', hy], rfl⟩
          rw [heq]; exact (hr v).2
        rw [div_le_div_iff_of_pos_right hp_real]
        exact Nat.cast_le.mpr hin_card
      have hch := chernoff_prod_upper_sub inN' (fun _ => {c₀ - j}) μ δ (by rw [ZMod.card]; exact hp_pos) hδ hμ_in
      have hpos : (0 : ℝ) < (Fintype.card (X' → ZMod p) : ℝ) := by
        rw [Fintype.card_pi]; positivity
      have hmul : ((E_in c₀ j ∩ G_sub).card : ℝ) * (Fintype.card (X' → ZMod p) : ℝ) ≤
          (Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (G_sub.card : ℝ)) *
          (Fintype.card (X' → ZMod p) : ℝ) := by
        calc ((E_in c₀ j ∩ G_sub).card : ℝ) * (Fintype.card (X' → ZMod p) : ℝ)
            = ((E_in c₀ j).card : ℝ) * (G_sub.card : ℝ) := by exact_mod_cast hdisj_card
          _ ≤ (Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (Fintype.card (X' → ZMod p) : ℝ)) * (G_sub.card : ℝ) := by
              exact mul_le_mul_of_nonneg_right hch (Nat.cast_nonneg _)
          _ = _ := by ring
      exact le_of_mul_le_mul_right hmul hpos
    have hfiber : ∀ c₀ : ZMod p,
        (((A v ∩ good A T).filter (fun c => c v = c₀)).card : ℝ) ≤
        2 * (p : ℝ) * Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (G_sub.card : ℝ) := by
      intro c₀
      let UnionBad : Finset (X' → ZMod p) :=
        Finset.univ.biUnion (fun j : ZMod p => (E_out c₀ j ∩ G_sub) ∪ (E_in c₀ j ∩ G_sub))
      have hcard_le : ((A v ∩ good A T).filter (fun c => c v = c₀)).card ≤ UnionBad.card := by
        refine Finset.card_le_card_of_injOn (fun c => (fixVEquiv v c).2) ?_ ?_
        · intro c hc
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_inter] at hc
          rcases hc with ⟨⟨hcA, hcG⟩, hcv⟩
          have hcG' : (fixVEquiv v c).2 ∈ G_sub := (hgood_iff c).mp hcG
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hcA
          rcases hcA with ⟨j, hdeg | hdeg⟩
          · refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨?_, hcG'⟩)⟩
            simp only [E_out, Finset.mem_filter, Finset.mem_univ, true_and]
            have hdeg_eq : outDeg (fun x y => D x y ∧ c y = c x + j) v =
                (outN'.filter (fun x => c x.1 ∈ ({c₀ + j} : Finset (ZMod p)))).card := by
              rw [outDeg_eq_filter_card]
              refine Finset.card_bij (fun y hy => ⟨y, by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
                exact (hDsub v y hy.1).ne.symm⟩) ?_ ?_ ?_
              · intro y hy
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
                simp [outN', hy.1, hy.2, hcv]
              · intro y₁ _ y₂ _ h; exact congrArg Subtype.val h
              · intro x hx
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, outN', Finset.mem_singleton] at hx
                exact ⟨x.1, by simp [hx.1, hx.2, hcv], rfl⟩
            have hlt : (1 + δ) * μ < (d_max : ℝ) + 1 := Nat.lt_floor_add_one _
            have hle : d_max + 1 ≤ (outN'.filter (fun x => c x.1 ∈ ({c₀ + j} : Finset (ZMod p)))).card := by
              rw [← hdeg_eq]; exact hdeg
            exact le_trans hlt.le (by exact_mod_cast hle)
          · refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨?_, hcG'⟩)⟩
            simp only [E_in, Finset.mem_filter, Finset.mem_univ, true_and]
            have hdeg_eq : inDeg (fun x y => D x y ∧ c y = c x + j) v =
                (inN'.filter (fun x => c x.1 ∈ ({c₀ - j} : Finset (ZMod p)))).card := by
              rw [show inDeg (fun x y => D x y ∧ c y = c x + j) v =
                outDeg (fun y x => D x y ∧ c y = c x + j) v from rfl, outDeg_eq_filter_card]
              refine Finset.card_bij (fun x hx => ⟨x, by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
                exact (hDsub x v hx.1).ne⟩) ?_ ?_ ?_
              · intro x hx
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
                simp only [inN', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                refine ⟨hx.1, ?_⟩
                rw [eq_sub_iff_add_eq, ← hcv, eq_comm]
                exact hx.2
              · intro x₁ _ x₂ _ h; exact congrArg Subtype.val h
              · intro x hx
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, inN', Finset.mem_singleton] at hx
                refine ⟨x.1, ?_, rfl⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                refine ⟨hx.1, ?_⟩
                rw [hcv, hx.2, sub_add_cancel]
            have hlt : (1 + δ) * μ < (d_max : ℝ) + 1 := Nat.lt_floor_add_one _
            have hle : d_max + 1 ≤ (inN'.filter (fun x => c x.1 ∈ ({c₀ - j} : Finset (ZMod p)))).card := by
              rw [← hdeg_eq]; exact hdeg
            exact le_trans hlt.le (by exact_mod_cast hle)
        · intro c₁ hc₁ c₂ hc₂ heq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_inter] at hc₁ hc₂
          apply (fixVEquiv v).injective
          exact Prod.ext (hc₁.2.trans hc₂.2.symm) heq
      have hUnion_bound : (UnionBad.card : ℝ) ≤
          2 * (p : ℝ) * Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (G_sub.card : ℝ) := by
        have h1 : UnionBad.card ≤ ∑ j : ZMod p, ((E_out c₀ j ∩ G_sub).card + (E_in c₀ j ∩ G_sub).card) := by
          calc UnionBad.card
              ≤ ∑ j : ZMod p, ((E_out c₀ j ∩ G_sub) ∪ (E_in c₀ j ∩ G_sub)).card := Finset.card_biUnion_le
            _ ≤ ∑ j : ZMod p, ((E_out c₀ j ∩ G_sub).card + (E_in c₀ j ∩ G_sub).card) :=
                Finset.sum_le_sum fun _ _ => Finset.card_union_le _ _
        calc (UnionBad.card : ℝ)
            ≤ ∑ j : ZMod p, (((E_out c₀ j ∩ G_sub).card : ℝ) + ((E_in c₀ j ∩ G_sub).card : ℝ)) := by exact_mod_cast h1
          _ ≤ ∑ _j : ZMod p, (2 * Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (G_sub.card : ℝ)) := by
              refine Finset.sum_le_sum fun j _ => ?_
              have ho := hEout_bound c₀ j
              have hi := hEin_bound c₀ j
              linarith
          _ = (p : ℝ) * (2 * Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) * (G_sub.card : ℝ)) := by
              rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          _ = _ := by ring
      exact le_trans (by exact_mod_cast hcard_le) hUnion_bound
    have hsplit : (A v ∩ good A T).card =
        ∑ c₀ : ZMod p, ((A v ∩ good A T).filter (fun c => c v = c₀)).card :=
      Finset.card_eq_sum_card_fiberwise (f := fun c : V → ZMod p => c v)
        (t := (Finset.univ : Finset (ZMod p))) (fun c _ => Finset.mem_univ _)
    calc ((A v ∩ good A T).card : ℝ)
        = ∑ c₀ : ZMod p, (((A v ∩ good A T).filter (fun c => c v = c₀)).card : ℝ) := by exact_mod_cast hsplit
      _ ≤ ∑ _c₀ : ZMod p, (p_bad * (G_sub.card : ℝ)) := by
          refine Finset.sum_le_sum fun c₀ _ => ?_
          exact hfiber c₀
      _ = (p : ℝ) * (p_bad * (G_sub.card : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      _ = p_bad * ((p * G_sub.card : ℕ) : ℝ) := by push_cast; ring
      _ = p_bad * ((good A T).card : ℝ) := by rw [hgood_card]
  obtain ⟨c, hc⟩ := lll_symmetric A Γ p_bad (Δ ^ 2 + Δ + 1) hp_nonneg hLLL hΓ_card hlop
  refine ⟨c, fun v j => ?_⟩
  have hnot := hc v
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
  have h1 : ¬ d_max < outDeg (fun x y => D x y ∧ c y = c x + j) v :=
    fun h => hnot ⟨j, Or.inl h⟩
  have h2 : ¬ d_max < inDeg (fun x y => D x y ∧ c y = c x + j) v :=
    fun h => hnot ⟨j, Or.inr h⟩
  exact ⟨Nat.le_of_not_lt h1, Nat.le_of_not_lt h2⟩

end Step2Coloring

section Cycles

def iterNext {V : Type*} [Fintype V] (M : V → V → Prop) : ℕ → V → Option V
  | 0, v => some v
  | k + 1, v => (iterNext M k v).bind (uniqueNext M)

lemma iterNext_add {V : Type*} [Fintype V] (M : V → V → Prop) (a b : ℕ) (v : V) :
    iterNext M (a + b) v = (iterNext M a v).bind (iterNext M b) := by
  induction b generalizing a with
  | zero =>
    simp only [Nat.add_zero, iterNext]
    cases iterNext M a v <;> rfl
  | succ b ih =>
    rw [← Nat.add_assoc, iterNext, ih a]
    cases iterNext M a v with
    | none => rfl
    | some u => simp only [Option.bind_some, iterNext]

lemma iterNext_comm {V : Type*} [Fintype V] (M : V → V → Prop) (a b : ℕ) (v : V) :
    (iterNext M a v).bind (iterNext M b) = (iterNext M b v).bind (iterNext M a) := by
  rw [← iterNext_add, Nat.add_comm, iterNext_add]

lemma iterNext_one_eq_uniqueNext {V : Type*} [Fintype V] (M : V → V → Prop) (v : V) :
    iterNext M 1 v = uniqueNext M v := by
  simp [iterNext]

lemma iterNext_isSome_mono {V : Type*} [Fintype V] (M : V → V → Prop)
    {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {v : V} (h : (iterNext M k₂ v).isSome) :
    (iterNext M k₁ v).isSome := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [iterNext_add] at h
  cases hk1 : iterNext M k₁ v with
  | none => rw [hk1] at h; simp at h
  | some _ => rfl

def onCycle {V : Type*} [Fintype V] (M : V → V → Prop) (v : V) : Prop :=
  ∃ k : ℕ, 0 < k ∧ iterNext M k v = some v

def isCycleRoot {V : Type*} [Fintype V] (M : V → V → Prop) (r : V) : Prop :=
  onCycle M r ∧ ∀ u, (∃ k, iterNext M k r = some u) →
    (Fintype.equivFin V) r ≤ (Fintype.equivFin V) u

abbrev Cyc {V : Type*} [Fintype V] (M : V → V → Prop) : Type _ :=
  {r : V // isCycleRoot M r}

noncomputable def cycLen {V : Type*} [Fintype V] (M : V → V → Prop) (r : Cyc M) : ℕ :=
  Nat.find r.2.1

lemma cycLen_pos {V : Type*} [Fintype V] (M : V → V → Prop) (r : Cyc M) :
    0 < cycLen M r :=
  (Nat.find_spec r.2.1).1

lemma iterNext_cycLen {V : Type*} [Fintype V] (M : V → V → Prop) (r : Cyc M) :
    iterNext M (cycLen M r) r.1 = some r.1 :=
  (Nat.find_spec r.2.1).2

lemma cycLen_min {V : Type*} [Fintype V] (M : V → V → Prop) (r : Cyc M)
    {k : ℕ} (hk0 : 0 < k) (hk : iterNext M k r.1 = some r.1) :
    cycLen M r ≤ k :=
  Nat.find_min' r.2.1 ⟨hk0, hk⟩

lemma iterNext_zmod {V : Type*} [Fintype V] (M : V → V → Prop) (hOut : ∀ u, outDeg M u ≤ 1)
    {p : ℕ} (c : V → ZMod p) (j : ZMod p)
    (hc : ∀ u w, M u w → c w = c u + j)
    (k : ℕ) {v w : V} (hk : iterNext M k v = some w) :
    c w = c v + (k : ZMod p) * j := by
  induction k generalizing w with
  | zero =>
    simp only [iterNext, Option.some.injEq] at hk
    subst hk
    simp
  | succ k ih =>
    simp only [iterNext] at hk
    cases hprev : iterNext M k v with
    | none => rw [hprev] at hk; simp at hk
    | some u =>
      rw [hprev, Option.bind_some, uniqueNext_eq_some_iff M hOut] at hk
      rw [hc u w hk, ih hprev]
      push_cast
      ring

lemma cycle_len_ge_p {V : Type*} [Fintype V] (M : V → V → Prop) (hOut : ∀ u, outDeg M u ≤ 1)
    {p : ℕ} [Fact p.Prime] (c : V → ZMod p) {j : ZMod p} (hj : j ≠ 0)
    (hc : ∀ u w, M u w → c w = c u + j) (r : Cyc M) :
    p ≤ cycLen M r := by
  have heq := iterNext_zmod M hOut c j hc (cycLen M r) (iterNext_cycLen M r)
  have hzero : ((cycLen M r : ℕ) : ZMod p) * j = 0 := by
    have : c r.1 + ((cycLen M r : ℕ) : ZMod p) * j = c r.1 + 0 := by
      rw [add_zero]; exact heq.symm
    exact add_left_cancel this
  have hcast : ((cycLen M r : ℕ) : ZMod p) = 0 := (mul_eq_zero.mp hzero).resolve_right hj
  have hdvd : p ∣ cycLen M r := (ZMod.natCast_eq_zero_iff (cycLen M r) p).mp hcast
  exact Nat.le_of_dvd (cycLen_pos M r) hdvd

noncomputable def cycStart {V : Type*} [Fintype V] (M : V → V → Prop) (p : ℕ)
    (r : Cyc M) (i : Fin p) : V :=
  (iterNext M i.1 r.1).getD r.1

noncomputable def cycEnd {V : Type*} [Fintype V] (M : V → V → Prop) (p : ℕ)
    (r : Cyc M) (i : Fin p) : V :=
  (iterNext M (i.1 + 1) r.1).getD r.1

noncomputable def cycEdge {V : Type*} [Fintype V] (M : V → V → Prop) (p : ℕ)
    (r : Cyc M) (i : Fin p) : Sym2 V :=
  s(cycStart M p r i, cycEnd M p r i)

lemma iterNext_some_of_le_cycLen {V : Type*} [Fintype V] (M : V → V → Prop)
    (r : Cyc M) {t : ℕ} (ht : t ≤ cycLen M r) :
    (iterNext M t r.1).isSome := by
  refine iterNext_isSome_mono M ht ?_
  rw [iterNext_cycLen]
  rfl

lemma cycStart_spec {V : Type*} [Fintype V] (M : V → V → Prop) {p : ℕ}
    (r : Cyc M) (hp : p ≤ cycLen M r) (i : Fin p) :
    iterNext M i.1 r.1 = some (cycStart M p r i) := by
  have hs := iterNext_some_of_le_cycLen M r (le_trans i.2.le hp)
  cases h : iterNext M i.1 r.1 with
  | none => rw [h] at hs; simp at hs
  | some u => simp [cycStart, h]

lemma cycEnd_spec {V : Type*} [Fintype V] (M : V → V → Prop) {p : ℕ}
    (r : Cyc M) (hp : p ≤ cycLen M r) (i : Fin p) :
    iterNext M (i.1 + 1) r.1 = some (cycEnd M p r i) := by
  have hs := iterNext_some_of_le_cycLen M r (le_trans (Nat.succ_le_of_lt i.2) hp)
  cases h : iterNext M (i.1 + 1) r.1 with
  | none => rw [h] at hs; simp at hs
  | some w => simp [cycEnd, h]

lemma cycEdge_mem_M {V : Type*} [Fintype V] (M : V → V → Prop) (hOut : ∀ u, outDeg M u ≤ 1)
    {p : ℕ} (r : Cyc M) (hp : p ≤ cycLen M r) (i : Fin p) :
    M (cycStart M p r i) (cycEnd M p r i) := by
  have h1 := cycStart_spec M r hp i
  have h2 := cycEnd_spec M r hp i
  simp only [iterNext, h1, Option.bind_some, uniqueNext_eq_some_iff M hOut] at h2
  exact h2

lemma iterNext_cyc_eq_inj {V : Type*} [Fintype V] (M : V → V → Prop)
    (r : Cyc M) {a b : ℕ} (hab : a < b) (hb : b ≤ cycLen M r)
    (hstrict : 0 < a ∨ b < cycLen M r)
    {u : V} (ha : iterNext M a r.1 = some u) (hbu : iterNext M b r.1 = some u) : False := by
  let d := b - a
  have hd_pos : 0 < d := Nat.sub_pos_of_lt hab
  have hd_lt : d < cycLen M r := by omega
  have hbe : b = a + d := (Nat.add_sub_cancel' hab.le).symm
  rw [hbe, iterNext_add, ha, Option.bind_some] at hbu
  have hshift : iterNext M d r.1 = some r.1 := by
    have ha_le : a ≤ cycLen M r := by omega
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le ha_le
    have hfull := iterNext_cycLen M r
    rw [ht, iterNext_add, ha, Option.bind_some] at hfull
    have hc := iterNext_comm M t d u
    rw [hfull, hbu, Option.bind_some, Option.bind_some] at hc
    exact hc.trans hfull
  exact absurd (cycLen_min M r hd_pos hshift) (not_le_of_gt hd_lt)

lemma cycStart_inj {V : Type*} [Fintype V] (M : V → V → Prop) {p : ℕ}
    (r : Cyc M) (hp : p ≤ cycLen M r) :
    Function.Injective (cycStart M p r) := by
  intro i₁ i₂ heq
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have h1 := cycStart_spec M r hp i₁
    have h2 := cycStart_spec M r hp i₂
    rw [heq] at h1
    exact iterNext_cyc_eq_inj M r hlt (le_trans i₂.2.le hp)
      (Or.inr (lt_of_lt_of_le i₂.2 hp)) h1 h2
  · have h1 := cycStart_spec M r hp i₁
    have h2 := cycStart_spec M r hp i₂
    rw [heq] at h1
    exact iterNext_cyc_eq_inj M r hlt (le_trans i₁.2.le hp)
      (Or.inr (lt_of_lt_of_le i₁.2 hp)) h2 h1

lemma cycEnd_inj {V : Type*} [Fintype V] (M : V → V → Prop) {p : ℕ}
    (r : Cyc M) (hp : p ≤ cycLen M r) :
    Function.Injective (cycEnd M p r) := by
  intro i₁ i₂ heq
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have h1 := cycEnd_spec M r hp i₁
    have h2 := cycEnd_spec M r hp i₂
    rw [heq] at h1
    exact iterNext_cyc_eq_inj M r (Nat.add_lt_add_right hlt 1)
      (le_trans (Nat.succ_le_of_lt i₂.2) hp) (Or.inl (Nat.succ_pos _)) h1 h2
  · have h1 := cycEnd_spec M r hp i₁
    have h2 := cycEnd_spec M r hp i₂
    rw [heq] at h1
    exact iterNext_cyc_eq_inj M r (Nat.add_lt_add_right hlt 1)
      (le_trans (Nat.succ_le_of_lt i₁.2) hp) (Or.inl (Nat.succ_pos _)) h2 h1

lemma cycEdge_hit_card_le_two {V : Type*} [Fintype V] (M : V → V → Prop) {p : ℕ}
    (r : Cyc M) (hp : p ≤ cycLen M r) (v : V) :
    (Finset.univ.filter (fun i : Fin p => v ∈ cycEdge M p r i)).card ≤ 2 := by
  have hsub : Finset.univ.filter (fun i : Fin p => v ∈ cycEdge M p r i) ⊆
      Finset.univ.filter (fun i : Fin p => cycStart M p r i = v) ∪
      Finset.univ.filter (fun i : Fin p => cycEnd M p r i = v) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cycEdge, Sym2.mem_iff] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_right _ (by simp)
  have h1 : (Finset.univ.filter (fun i : Fin p => cycStart M p r i = v)).card ≤ 1 :=
    Finset.card_le_one.mpr fun i₁ hi₁ i₂ hi₂ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hi₂
      exact cycStart_inj M r hp (hi₁.trans hi₂.symm)
  have h2 : (Finset.univ.filter (fun i : Fin p => cycEnd M p r i = v)).card ≤ 1 :=
    Finset.card_le_one.mpr fun i₁ hi₁ i₂ hi₂ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hi₂
      exact cycEnd_inj M r hp (hi₁.trans hi₂.symm)
  calc (Finset.univ.filter (fun i : Fin p => v ∈ cycEdge M p r i)).card
      ≤ (Finset.univ.filter (fun i : Fin p => cycStart M p r i = v) ∪
          Finset.univ.filter (fun i : Fin p => cycEnd M p r i = v)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun i : Fin p => cycStart M p r i = v)).card +
          (Finset.univ.filter (fun i : Fin p => cycEnd M p r i = v)).card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add h1 h2

lemma exists_cycleRoot_of_onCycle {V : Type*} [Fintype V] (M : V → V → Prop)
    {v : V} (hv : onCycle M v) :
    ∃ r : Cyc M, ∃ k, iterNext M k v = some r.1 ∧ ∃ m, iterNext M m r.1 = some v := by
  let R : Finset V := Finset.univ.filter (fun u => ∃ k, iterNext M k v = some u)
  have hRv : v ∈ R := by simp [R]; exact ⟨0, rfl⟩
  have hRne : R.Nonempty := ⟨v, hRv⟩
  obtain ⟨r, hrR, hrmin⟩ := Finset.exists_min_image R (fun u => ((Fintype.equivFin V u : ℕ))) hRne
  simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hrR
  rcases hrR with ⟨k₀, hk₀⟩
  rcases hv with ⟨L, hLpos, hLv⟩
  have hreach_back : ∀ u, (∃ k, iterNext M k v = some u) →
      (∃ m, iterNext M m u = some v) ∧ onCycle M u := by
    intro u ⟨k, hk⟩
    let q := L * (k / L + 1)
    have hkq : k ≤ q := (Nat.lt_mul_div_succ k hLpos).le
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hkq
    have hq_iter : iterNext M q v = some v := by
      clear hm
      have : ∀ n : ℕ, iterNext M (L * n) v = some v := by
        intro n
        induction n with
        | zero => simp [iterNext]
        | succ n ih =>
          rw [Nat.mul_succ, iterNext_add, ih, Option.bind_some, hLv]
      exact this (k / L + 1)
    rw [hm, iterNext_add, hk, Option.bind_some] at hq_iter
    refine ⟨⟨m, hq_iter⟩, ?_⟩
    have hmL : 0 < m + k := by
      have hqpos : 0 < q := Nat.mul_pos hLpos (Nat.succ_pos _)
      omega
    refine ⟨m + k, hmL, ?_⟩
    rw [iterNext_add, hq_iter, Option.bind_some, hk]
  have hr_back := hreach_back r ⟨k₀, hk₀⟩
  have hr_root : isCycleRoot M r := by
    refine ⟨hr_back.2, fun u ⟨k₁, hk₁⟩ => ?_⟩
    have huR : u ∈ R := by
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨k₀ + k₁, ?_⟩
      rw [iterNext_add, hk₀, Option.bind_some, hk₁]
    exact Fin.mk_le_mk.mp (hrmin u huR)
  exact ⟨⟨r, hr_root⟩, k₀, hk₀, hr_back.1⟩

def IsForwardWalk {V : Type*} (M : V → V → Prop) {G : SimpleGraph V} :
    ∀ {a b : V}, G.Walk a b → Prop
  | _, _, Walk.nil => True
  | a, _, @Walk.cons _ _ _ v _ _ rest => M a v ∧ IsForwardWalk M rest

def IsBackwardWalk {V : Type*} (M : V → V → Prop) {G : SimpleGraph V} :
    ∀ {a b : V}, G.Walk a b → Prop
  | _, _, Walk.nil => True
  | a, _, @Walk.cons _ _ _ v _ _ rest => M v a ∧ IsBackwardWalk M rest

lemma isForwardWalk_append {V : Type*} (M : V → V → Prop) {G : SimpleGraph V}
    {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : IsForwardWalk M p) (hq : IsForwardWalk M q) :
    IsForwardWalk M (p.append q) := by
  induction p with
  | nil => exact hq
  | cons _ rest ih => exact ⟨hp.1, ih hp.2 hq⟩

lemma isForwardWalk_reverse_of_backward {V : Type*} (M : V → V → Prop) {G : SimpleGraph V}
    {a b : V} {W : G.Walk a b} (hW : IsBackwardWalk M W) :
    IsForwardWalk M W.reverse := by
  induction W with
  | nil => trivial
  | @cons u v w hadj rest ih =>
    rw [Walk.reverse_cons]
    exact isForwardWalk_append M (ih hW.2) ⟨hW.1, trivial⟩

lemma trail_forward_aux {V : Type*} [Fintype V] (M : V → V → Prop)
    (hIn : ∀ x, inDeg M x ≤ 1)
    {G : SimpleGraph V} (hG : ∀ x y, G.Adj x y ↔ M x y ∨ M y x) :
    ∀ {a b : V} (W : G.Walk a b), W.IsTrail →
      ∀ prev : V, M prev a → s(prev, a) ∉ W.edges → IsForwardWalk M W := by
  intro a b W hW
  induction W with
  | nil => intro _ _ _; trivial
  | @cons u v w hadj rest ih =>
    intro prev hprev hnot
    rw [Walk.isTrail_cons] at hW
    rcases (hG u v).mp hadj with huv | hvu
    · refine ⟨huv, ih hW.1 u huv ?_⟩
      exact hW.2
    · have hin : prev = v := by
        have hle : inDeg M u ≤ 1 := hIn u
        dsimp only [inDeg] at hle
        rw [Set.ncard_le_one_iff] at hle
        exact hle hprev hvu
      subst hin
      exfalso
      apply hnot
      simp [Walk.edges_cons, Sym2.eq_swap]

lemma trail_backward_aux {V : Type*} [Fintype V] (M : V → V → Prop)
    (hOut : ∀ x, outDeg M x ≤ 1)
    {G : SimpleGraph V} (hG : ∀ x y, G.Adj x y ↔ M x y ∨ M y x) :
    ∀ {a b : V} (W : G.Walk a b), W.IsTrail →
      ∀ prev : V, M a prev → s(prev, a) ∉ W.edges → IsBackwardWalk M W := by
  intro a b W hW
  induction W with
  | nil => intro _ _ _; trivial
  | @cons u v w hadj rest ih =>
    intro prev hprev hnot
    rw [Walk.isTrail_cons] at hW
    rcases (hG u v).mp hadj with huv | hvu
    · have hout : prev = v := by
        have hle : outDeg M u ≤ 1 := hOut u
        dsimp only [outDeg] at hle
        rw [Set.ncard_le_one_iff] at hle
        exact hle hprev huv
      subst hout
      exfalso
      apply hnot
      simp [Walk.edges_cons, Sym2.eq_swap]
    · refine ⟨hvu, ih hW.1 u hvu ?_⟩
      exact hW.2

lemma isForwardWalk_length_iterNext {V : Type*} [Fintype V] (M : V → V → Prop)
    (hOut : ∀ x, outDeg M x ≤ 1) {G : SimpleGraph V} :
    ∀ {a b : V} (W : G.Walk a b), IsForwardWalk M W →
      iterNext M W.length a = some b := by
  intro a b W hW
  induction W with
  | nil => rfl
  | @cons u v w hadj rest ih =>
    rw [Walk.length_cons, Nat.add_comm rest.length 1, iterNext_add]
    have h1 : iterNext M 1 u = some v := by
      simp only [iterNext, Option.bind_some, uniqueNext_eq_some_iff M hOut]
      exact hW.1
    rw [h1, Option.bind_some]
    exact ih hW.2

lemma endpoints_mem_support_of_mem_edges {V : Type*} {G : SimpleGraph V} :
    ∀ {a b x y : V} (W : G.Walk a b), s(x, y) ∈ W.edges →
      x ∈ W.support ∧ y ∈ W.support := by
  intro a b x y W hmem
  induction W with
  | nil => simp at hmem
  | @cons u v w hadj rest ih =>
    simp only [Walk.edges_cons, List.mem_cons, Sym2.eq_iff] at hmem
    rcases hmem with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hrest
    · exact ⟨Walk.start_mem_support _, by simp [Walk.support_cons]⟩
    · exact ⟨by simp [Walk.support_cons], Walk.start_mem_support _⟩
    · obtain ⟨hx, hy⟩ := ih hrest
      exact ⟨by simp [Walk.support_cons, hx], by simp [Walk.support_cons, hy]⟩

lemma isForwardWalk_cycle_step {V : Type*} [Fintype V] (M : V → V → Prop)
    (hOut : ∀ x, outDeg M x ≤ 1) {G : SimpleGraph V}
    {a : V} {C : G.Walk a a} (hne : C ≠ Walk.nil) (hC : IsForwardWalk M C) :
    ∀ u ∈ C.support, ∃ w ∈ C.support, uniqueNext M u = some w ∧ s(u, w) ∈ C.edges := by
  have aux : ∀ {x y : V} (W : G.Walk x y), IsForwardWalk M W →
      ∀ u ∈ W.support, u = y ∨ ∃ w ∈ W.support, uniqueNext M u = some w ∧ s(u, w) ∈ W.edges := by
    intro x y W hW u hu
    induction W with
    | nil =>
      simp only [Walk.support_nil, List.mem_singleton] at hu
      exact Or.inl hu
    | @cons p q r hadj rest ih =>
      simp only [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | hu'
      · refine Or.inr ⟨q, by simp [Walk.support_cons], ?_, by simp [Walk.edges_cons]⟩
        exact (uniqueNext_eq_some_iff M hOut).mpr hW.1
      · rcases ih hW.2 hu' with rfl | ⟨w, hw, hun, hed⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨w, by simp [Walk.support_cons, hw], hun, by simp [Walk.edges_cons, hed]⟩
  intro u hu
  rcases aux C hC u hu with rfl | hw
  · cases C with
    | nil => exact absurd rfl hne
    | @cons _ v _ hadj rest =>
      refine ⟨v, by simp [Walk.support_cons], ?_, by simp [Walk.edges_cons]⟩
      exact (uniqueNext_eq_some_iff M hOut).mpr hC.1
  · exact hw

lemma iterNext_on_forward_cycle {V : Type*} [Fintype V] (M : V → V → Prop)
    (hOut : ∀ x, outDeg M x ≤ 1) {G : SimpleGraph V}
    {a : V} {C : G.Walk a a} (hne : C ≠ Walk.nil) (hC : IsForwardWalk M C) :
    ∀ t : ℕ, ∃ u ∈ C.support, ∃ w ∈ C.support,
      iterNext M t a = some u ∧ iterNext M (t + 1) a = some w ∧ s(u, w) ∈ C.edges := by
  intro t
  have hstep := isForwardWalk_cycle_step M hOut hne hC
  induction t with
  | zero =>
    obtain ⟨w, hw, hun, hed⟩ := hstep a (Walk.start_mem_support C)
    exact ⟨a, Walk.start_mem_support C, w, hw, rfl, by simpa [iterNext], hed⟩
  | succ t ih =>
    rcases ih with ⟨_, _, w, hw, _, ht1, _⟩
    obtain ⟨z, hz, hun, hed⟩ := hstep w hw
    refine ⟨w, hw, z, hz, ht1, ?_, hed⟩
    change (iterNext M (t + 1) a).bind (uniqueNext M) = some z
    rw [ht1, Option.bind_some, hun]

lemma iterNext_back_of_cyc {V : Type*} [Fintype V] (M : V → V → Prop)
    (r : Cyc M) {v : V} {k : ℕ} (hk : iterNext M k r.1 = some v) :
    ∃ m : ℕ, iterNext M m v = some r.1 := by
  have hLpos := cycLen_pos M r
  have hLv := iterNext_cycLen M r
  let q := cycLen M r * (k / cycLen M r + 1)
  have hkq : k ≤ q := (Nat.lt_mul_div_succ k hLpos).le
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hkq
  have hq_iter : iterNext M q r.1 = some r.1 := by
    clear hm
    have : ∀ n : ℕ, iterNext M (cycLen M r * n) r.1 = some r.1 := by
      intro n
      induction n with
      | zero => simp [iterNext]
      | succ n ih => rw [Nat.mul_succ, iterNext_add, ih, Option.bind_some, hLv]
    exact this (k / cycLen M r + 1)
  rw [hm, iterNext_add, hk, Option.bind_some] at hq_iter
  exact ⟨m, hq_iter⟩

lemma cycleRoot_unique_of_touch {V : Type*} [Fintype V] (M : V → V → Prop)
    {v : V} {r₁ r₂ : Cyc M}
    (h₁ : ∃ k₁, iterNext M k₁ r₁.1 = some v)
    (h₂ : ∃ k₂, iterNext M k₂ r₂.1 = some v) :
    r₁ = r₂ := by
  rcases h₁ with ⟨k₁, hk₁⟩
  rcases h₂ with ⟨k₂, hk₂⟩
  obtain ⟨m₁, hm₁⟩ := iterNext_back_of_cyc M r₁ hk₁
  obtain ⟨m₂, hm₂⟩ := iterNext_back_of_cyc M r₂ hk₂
  have h12 : (Fintype.equivFin V) r₁.1 ≤ (Fintype.equivFin V) r₂.1 := by
    refine r₁.2.2 r₂.1 ⟨k₁ + m₂, ?_⟩
    rw [iterNext_add, hk₁, Option.bind_some, hm₂]
  have h21 : (Fintype.equivFin V) r₂.1 ≤ (Fintype.equivFin V) r₁.1 := by
    refine r₂.2.2 r₁.1 ⟨k₂ + m₁, ?_⟩
    rw [iterNext_add, hk₂, Option.bind_some, hm₁]
  exact Subtype.ext ((Fintype.equivFin V).injective (le_antisymm h12 h21))

lemma acyclic_after_breaking {V : Type*} [Fintype V] (M : V → V → Prop)
    (hOut : ∀ x, outDeg M x ≤ 1) (hIn : ∀ x, inDeg M x ≤ 1)
    {G : SimpleGraph V} (hG : ∀ x y, G.Adj x y ↔ M x y ∨ M y x)
    (p : ℕ) (hp : ∀ r : Cyc M, p ≤ cycLen M r) (ω : Cyc M → Fin p) :
    (G.deleteEdges {e | ∃ r : Cyc M, e = cycEdge M p r (ω r)}).IsAcyclic := by
  intro v c hc
  have hle : G.deleteEdges {e | ∃ r : Cyc M, e = cycEdge M p r (ω r)} ≤ G :=
    fun _ _ h => deleteEdges_le _ h
  let q : G.Walk v v := c.mapLe hle
  have hq_trail : q.IsTrail := hc.isTrail.mapLe hle
  have hq_ne : q ≠ Walk.nil := by
    intro hnil
    cases c with
    | nil => exact hc.ne_nil rfl
    | cons _ _ => simp [q] at hnil
  have hq_edges_not_del : ∀ r : Cyc M, cycEdge M p r (ω r) ∉ q.edges := by
    intro r hmem
    rw [Walk.edges_mapLe_eq_edges] at hmem
    have h := Walk.edges_subset_edgeSet c hmem
    have hadj : (G.deleteEdges {e | ∃ r : Cyc M, e = cycEdge M p r (ω r)}).edgeSet (cycEdge M p r (ω r)) := h
    rw [edgeSet_deleteEdges] at hadj
    exact hadj.2 ⟨r, rfl⟩
  have hexists_fwd : ∃ C : G.Walk v v, C ≠ Walk.nil ∧ IsForwardWalk M C ∧
      (∀ e, e ∈ C.edges → e ∈ q.edges) := by
    cases hq_cases : q with
    | nil => exact absurd hq_cases hq_ne
    | @cons _ u _ hadj rest =>
      rw [hq_cases] at hq_trail
      rw [Walk.isTrail_cons] at hq_trail
      rcases (hG v u).mp hadj with hvu | huv
      · refine ⟨Walk.cons hadj rest, by simp, ?_, ?_⟩
        · exact ⟨hvu, trail_forward_aux M hIn hG rest hq_trail.1 v hvu hq_trail.2⟩
        · intro e he; exact he
      · have hbw : IsBackwardWalk M (Walk.cons hadj rest) :=
          ⟨huv, trail_backward_aux M hOut hG rest hq_trail.1 v huv hq_trail.2⟩
        refine ⟨(Walk.cons hadj rest).reverse, ?_, isForwardWalk_reverse_of_backward M hbw, ?_⟩
        · intro hrev
          have : (Walk.cons hadj rest).reverse.length = 0 := by rw [hrev]; rfl
          rw [Walk.length_reverse, Walk.length_cons] at this
          omega
        · intro e he
          rw [Walk.edges_reverse, List.mem_reverse] at he
          exact he
  rcases hexists_fwd with ⟨C, hCne, hCfwd, hCsub⟩
  have hClen_pos : 0 < C.length := by
    cases C with
    | nil => exact absurd rfl hCne
    | cons _ _ => simp
  have hv_onCyc : onCycle M v := ⟨C.length, hClen_pos, isForwardWalk_length_iterNext M hOut C hCfwd⟩
  obtain ⟨r, k₀, hk₀, _⟩ := exists_cycleRoot_of_onCycle M hv_onCyc
  obtain ⟨u, _, w, _, hu_eq, hw_eq, hed⟩ := iterNext_on_forward_cycle M hOut hCne hCfwd (k₀ + (ω r).1)
  have hu_start : u = cycStart M p r (ω r) := by
    have h1 : iterNext M (k₀ + (ω r).1) v = some (cycStart M p r (ω r)) := by
      rw [iterNext_add, hk₀, Option.bind_some, cycStart_spec M r (hp r) (ω r)]
    exact Option.some.inj (hu_eq.symm.trans h1)
  have hw_end : w = cycEnd M p r (ω r) := by
    have h2 : iterNext M (k₀ + (ω r).1 + 1) v = some (cycEnd M p r (ω r)) := by
      rw [Nat.add_assoc, iterNext_add, hk₀, Option.bind_some, cycEnd_spec M r (hp r) (ω r)]
    exact Option.some.inj (hw_eq.symm.trans h2)
  rw [hu_start, hw_end] at hed
  exact hq_edges_not_del r (hCsub _ hed)

end Cycles

section Step4CycleBreak

def breakRemGraph {V ι : Type*} [Fintype V] (M : ι → V → V → Prop) (p : ℕ)
    (ω : (Σ idx : ι, Cyc (M idx)) → Fin p) : SimpleGraph V where
  Adj u w := u ≠ w ∧ ∃ γ : Σ idx : ι, Cyc (M idx), s(u, w) = cycEdge (M γ.1) p γ.2 (ω γ)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem step4_cycle_breaking
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (M : ι → V → V → Prop)
    (p d_max : ℕ) [NeZero p]
    (hLen : ∀ idx (r : Cyc (M idx)), p ≤ cycLen (M idx) r)
    (hcard_ι : Fintype.card ι ≤ p * d_max)
    (hLLL : 4 * Real.exp (-(((1 + 1 : ℝ) * Real.log (1 + 1) - 1) * (2 * (d_max : ℝ)))) *
      (((2 * p ^ 2 * d_max : ℕ) : ℝ) + 1) ≤ 1) :
    ∃ ω : (Σ idx : ι, Cyc (M idx)) → Fin p,
      ∀ v : V, (breakRemGraph M p ω).degree v ≤ 4 * d_max := by
  have hp_pos : 0 < p := NeZero.pos p
  let AllCyc := Σ idx : ι, Cyc (M idx)
  let touchedVerts : AllCyc → Finset V := fun γ =>
    Finset.univ.biUnion (fun i : Fin p => {cycStart (M γ.1) p γ.2 i, cycEnd (M γ.1) p γ.2 i})
  let S₂ : V → Finset AllCyc := fun v => Finset.univ.filter (fun γ => v ∈ touchedVerts γ)
  let Γ₂ : V → Finset V := fun v => (S₂ v).biUnion touchedVerts
  let q_bad : ℝ := Real.exp (-(((1 + 1 : ℝ) * Real.log (1 + 1) - 1) * (2 * (d_max : ℝ))))
  let B : V → Finset (AllCyc → Fin p) := fun v =>
    Finset.univ.filter (fun ω =>
      4 * d_max < ((S₂ v).filter (fun γ => v ∈ cycEdge (M γ.1) p γ.2 (ω γ))).card)
  have htouched_card : ∀ γ : AllCyc, (touchedVerts γ).card ≤ 2 * p := by
    intro γ
    calc (touchedVerts γ).card
        ≤ ∑ i : Fin p, ({cycStart (M γ.1) p γ.2 i, cycEnd (M γ.1) p γ.2 i} : Finset V).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin p, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
      _ = p * 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ = 2 * p := Nat.mul_comm p 2
  have hS₂_card : ∀ v : V, (S₂ v).card ≤ Fintype.card ι := by
    intro v
    have hinj : Set.InjOn Sigma.fst (S₂ v : Set AllCyc) := by
      rintro ⟨idx₁, r₁⟩ h₁ ⟨idx₂, r₂⟩ h₂ hidx
      dsimp at hidx
      subst hidx
      simp only [Finset.mem_coe, S₂, Finset.mem_filter, Finset.mem_univ, true_and,
        touchedVerts, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
      have hreach : ∀ r : Cyc (M idx₁),
          (∃ i : Fin p, v = cycStart (M idx₁) p r i ∨ v = cycEnd (M idx₁) p r i) →
          ∃ k, iterNext (M idx₁) k r.1 = some v := by
        intro r ⟨i, hi⟩
        rcases hi with rfl | rfl
        · exact ⟨i.1, cycStart_spec (M idx₁) r (hLen idx₁ r) i⟩
        · exact ⟨i.1 + 1, cycEnd_spec (M idx₁) r (hLen idx₁ r) i⟩
      have hr : r₁ = r₂ := cycleRoot_unique_of_touch (M idx₁) (hreach r₁ h₁) (hreach r₂ h₂)
      subst hr
      rfl
    have hle := Finset.card_le_card_of_injOn Sigma.fst (fun _ _ => Finset.mem_univ _) hinj
    simpa [Finset.card_univ] using hle
  have hΓ₂_card : ∀ v : V, (Γ₂ v).card ≤ 2 * p ^ 2 * d_max := by
    intro v
    calc (Γ₂ v).card
        ≤ ∑ γ ∈ S₂ v, (touchedVerts γ).card := Finset.card_biUnion_le
      _ ≤ ∑ _γ ∈ S₂ v, (2 * p) := Finset.sum_le_sum fun γ _ => htouched_card γ
      _ = (S₂ v).card * (2 * p) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (p * d_max) * (2 * p) := Nat.mul_le_mul_right (2 * p) (le_trans (hS₂_card v) hcard_ι)
      _ = 2 * p ^ 2 * d_max := by ring
  have hBS : ∀ v : V, DependsOn (S₂ v) (B v) := by
    intro v ω₁ ω₂ hagree
    have hfc : (S₂ v).filter (fun γ => v ∈ cycEdge (M γ.1) p γ.2 (ω₁ γ)) =
               (S₂ v).filter (fun γ => v ∈ cycEdge (M γ.1) p γ.2 (ω₂ γ)) := by
      ext γ
      simp only [Finset.mem_filter]
      constructor <;> rintro ⟨hγ, hm⟩ <;> refine ⟨hγ, ?_⟩
      · rw [← hagree γ hγ]; exact hm
      · rw [hagree γ hγ]; exact hm
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, hfc]
  have hq_nonneg : 0 ≤ q_bad := by positivity
  have hlop : ∀ v : V, ∀ T : Finset V, v ∉ T → (∀ u ∈ T, u ∉ Γ₂ v) →
      ((B v ∩ good B T).card : ℝ) ≤ q_bad * ((good B T).card : ℝ) := by
    intro v T hvT hTΓ
    have hgood_dep : DependsOn (T.biUnion S₂) (good B T) := dependsOn_good B S₂ hBS T
    have hdisj : Disjoint (S₂ v) (T.biUnion S₂) := by
      rw [Finset.disjoint_left]
      intro γ hγv hγT
      rw [Finset.mem_biUnion] at hγT
      rcases hγT with ⟨u, huT, hγu⟩
      simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hγv hγu
      have huΓ : u ∈ Γ₂ v := Finset.mem_biUnion.mpr ⟨γ, by simp [S₂, hγv], hγu⟩
      exact hTΓ u huT huΓ
    have hdisj_card := card_inter_of_dependsOn_disjoint hdisj (hBS v) hgood_dep
    let hit : AllCyc → Finset (Fin p) := fun γ =>
      Finset.univ.filter (fun i : Fin p => v ∈ cycEdge (M γ.1) p γ.2 i)
    have hμ : ∑ γ ∈ S₂ v, ((hit γ).card : ℝ) / (Fintype.card (Fin p) : ℝ) ≤ 2 * (d_max : ℝ) := by
      have hp_real : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_pos
      calc ∑ γ ∈ S₂ v, ((hit γ).card : ℝ) / (Fintype.card (Fin p) : ℝ)
          ≤ ∑ _γ ∈ S₂ v, (2 : ℝ) / (p : ℝ) := by
            refine Finset.sum_le_sum fun γ _ => ?_
            rw [Fintype.card_fin]
            have hhc : (hit γ).card ≤ 2 := by
              dsimp only [hit]
              convert cycEdge_hit_card_le_two (M γ.1) γ.2 (hLen γ.1 γ.2) v
            exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hhc) (Nat.cast_nonneg _)
        _ = ((S₂ v).card : ℝ) * ((2 : ℝ) / (p : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((p * d_max : ℕ) : ℝ) * ((2 : ℝ) / (p : ℝ)) := by
            gcongr
            exact_mod_cast le_trans (hS₂_card v) hcard_ι
        _ = 2 * (d_max : ℝ) := by
            push_cast
            field_simp [hp_real.ne']
    have hch := chernoff_prod_upper_sub (S₂ v) hit (2 * (d_max : ℝ)) 1
      (by rw [Fintype.card_fin]; exact hp_pos) one_pos hμ
    have hB_sub : (B v).card ≤
        (Finset.univ.filter (fun ω : AllCyc → Fin p =>
          (1 + 1 : ℝ) * (2 * (d_max : ℝ)) ≤ (((S₂ v).filter (fun γ => ω γ ∈ hit γ)).card : ℝ))).card := by
      refine Finset.card_le_card ?_
      intro ω hω
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      have hfc : (S₂ v).filter (fun γ => ω γ ∈ hit γ) =
                 (S₂ v).filter (fun γ => v ∈ cycEdge (M γ.1) p γ.2 (ω γ)) := by
        ext γ; simp [hit]
      rw [hfc]
      have hle : 4 * d_max + 1 ≤ ((S₂ v).filter (fun γ => v ∈ cycEdge (M γ.1) p γ.2 (ω γ))).card := hω
      have hreal : (1 + 1 : ℝ) * (2 * (d_max : ℝ)) ≤ ((4 * d_max + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      exact le_trans hreal (by exact_mod_cast hle)
    have hpos : (0 : ℝ) < (Fintype.card (AllCyc → Fin p) : ℝ) := by
      have hp_fintype : 0 < Fintype.card (Fin p) := by rw [Fintype.card_fin]; exact hp_pos
      rw [Fintype.card_pi]
      exact Nat.cast_pos.mpr (Finset.prod_pos fun _ _ => hp_fintype)
    have hmul : ((B v ∩ good B T).card : ℝ) * (Fintype.card (AllCyc → Fin p) : ℝ) ≤
        (q_bad * ((good B T).card : ℝ)) * (Fintype.card (AllCyc → Fin p) : ℝ) := by
      calc ((B v ∩ good B T).card : ℝ) * (Fintype.card (AllCyc → Fin p) : ℝ)
          = ((B v).card : ℝ) * ((good B T).card : ℝ) := by exact_mod_cast hdisj_card
        _ ≤ ((Finset.univ.filter (fun ω : AllCyc → Fin p =>
              (1 + 1 : ℝ) * (2 * (d_max : ℝ)) ≤
              (((S₂ v).filter (fun γ => ω γ ∈ hit γ)).card : ℝ))).card : ℝ) * ((good B T).card : ℝ) := by
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hB_sub) (Nat.cast_nonneg _)
        _ ≤ (q_bad * (Fintype.card (AllCyc → Fin p) : ℝ)) * ((good B T).card : ℝ) := by
              exact mul_le_mul_of_nonneg_right hch (Nat.cast_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_right hmul hpos
  obtain ⟨ω, hω⟩ := @lll_symmetric (AllCyc → Fin p) V _ _ _ _ ⟨fun _ => ⟨0, hp_pos⟩⟩
    B Γ₂ q_bad (2 * p ^ 2 * d_max) hq_nonneg hLLL hΓ₂_card hlop
  refine ⟨ω, fun v => ?_⟩
  have hnot := hω v
  simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
  have hdeg_le : (breakRemGraph M p ω).degree v ≤
      ((S₂ v).filter (fun γ => v ∈ cycEdge (M γ.1) p γ.2 (ω γ))).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    let f : AllCyc → Finset V := fun γ =>
      Finset.univ.filter (fun w => w ≠ v ∧ s(v, w) = cycEdge (M γ.1) p γ.2 (ω γ))
    let G_v : Finset AllCyc := (S₂ v).filter (fun γ => v ∈ cycEdge (M γ.1) p γ.2 (ω γ))
    have hsub : (breakRemGraph M p ω).neighborFinset v ⊆ G_v.biUnion f := by
      intro w hw
      rw [mem_neighborFinset] at hw
      dsimp only [breakRemGraph] at hw
      rcases hw with ⟨hne, γ, hs⟩
      refine Finset.mem_biUnion.mpr ⟨γ, ?_, ?_⟩
      · have hv_mem : v ∈ cycEdge (M γ.1) p γ.2 (ω γ) := by
          rw [← hs]; exact Sym2.mem_mk_left v w
        have hv_touched : v ∈ touchedVerts γ := Finset.mem_biUnion.mpr ⟨ω γ, Finset.mem_univ _, by
          simpa [cycEdge, Sym2.mem_iff] using hv_mem⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_touched⟩, hv_mem⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne.symm, hs⟩
    have hf_le : ∀ γ, (f γ).card ≤ 1 := by
      intro γ
      refine Finset.card_le_one.mpr fun w₁ hw₁ w₂ hw₂ => ?_
      simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
      have heq : s(v, w₁) = s(v, w₂) := hw₁.2.trans hw₂.2.symm
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h.symm hw₂.1
    calc ((breakRemGraph M p ω).neighborFinset v).card
        ≤ (G_v.biUnion f).card := Finset.card_le_card hsub
      _ ≤ ∑ γ ∈ G_v, (f γ).card := Finset.card_biUnion_le
      _ ≤ ∑ _γ ∈ G_v, 1 := Finset.sum_le_sum fun γ _ => hf_le γ
      _ = G_v.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  exact le_trans hdeg_le hnot

end Step4CycleBreak

section Assembly

lemma alon_step2_lll_cond {p Δ r : ℕ} {δ : ℝ} (hp : 0 < p) (hδ : 0 < δ) (hΔ2 : 2 ≤ Δ)
    (hr_ge : (Δ : ℝ) / 2 ≤ (r : ℝ))
    (hB1 : 144 * (p : ℝ) / (((1 + δ) * Real.log (1 + δ) - δ) / (2 * (p : ℝ))) ^ 3 ≤ (Δ : ℝ)) :
    4 * (2 * (p : ℝ) *
      Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * ((r : ℝ) / (p : ℝ))))) *
      (((Δ ^ 2 + Δ + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
  let c₁ : ℝ := (1 + δ) * Real.log (1 + δ) - δ
  have hc₁ : 0 < c₁ := chernoff_const_pos hδ
  let α₁ : ℝ := c₁ / (2 * (p : ℝ))
  have hp_real_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hα₁ : 0 < α₁ := by positivity
  have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hexp_arg : α₁ * (Δ : ℝ) ≤ c₁ * ((r : ℝ) / (p : ℝ)) := by
    calc α₁ * (Δ : ℝ) = c₁ * (((Δ : ℝ) / 2) / (p : ℝ)) := by dsimp [α₁]; ring
      _ ≤ c₁ * ((r : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr_ge hp_real_pos.le) hc₁.le
  have hexp_pow := Real.pow_div_factorial_le_exp (α₁ * (Δ : ℝ)) (by positivity) 3
  have hfact3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num
  rw [hfact3] at hexp_pow
  have hexp_bound : Real.exp (-(c₁ * ((r : ℝ) / (p : ℝ)))) ≤ 6 / (α₁ ^ 3 * (Δ : ℝ) ^ 3) := by
    have h1 : Real.exp (-(c₁ * ((r : ℝ) / (p : ℝ)))) ≤ Real.exp (-(α₁ * (Δ : ℝ))) :=
      Real.exp_le_exp.mpr (neg_le_neg hexp_arg)
    have h2 : Real.exp (-(α₁ * (Δ : ℝ))) = (Real.exp (α₁ * (Δ : ℝ)))⁻¹ := Real.exp_neg _
    have hpos_pow : 0 < (α₁ * (Δ : ℝ)) ^ 3 / 6 := by positivity
    have h3 : (Real.exp (α₁ * (Δ : ℝ)))⁻¹ ≤ ((α₁ * (Δ : ℝ)) ^ 3 / 6)⁻¹ :=
      inv_anti₀ hpos_pow hexp_pow
    have h4 : ((α₁ * (Δ : ℝ)) ^ 3 / 6)⁻¹ = 6 / (α₁ ^ 3 * (Δ : ℝ) ^ 3) := by ring
    linarith
  have hdeg_bound : (((Δ ^ 2 + Δ + 1 : ℕ) : ℝ) + 1) ≤ 3 * (Δ : ℝ) ^ 2 := by
    push_cast
    have h2Δ : (2 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ2
    nlinarith
  calc 4 * (2 * (p : ℝ) * Real.exp (-(c₁ * ((r : ℝ) / (p : ℝ))))) *
        (((Δ ^ 2 + Δ + 1 : ℕ) : ℝ) + 1)
      ≤ 4 * (2 * (p : ℝ) * (6 / (α₁ ^ 3 * (Δ : ℝ) ^ 3))) * (3 * (Δ : ℝ) ^ 2) := by
          refine mul_le_mul ?_ hdeg_bound (by positivity) (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hexp_bound (by positivity)
    _ = (144 * (p : ℝ) / α₁ ^ 3) / (Δ : ℝ) := by field_simp [hΔ_pos_real.ne']; norm_num
    _ ≤ 1 := (div_le_one hΔ_pos_real).mpr hB1

lemma alon_step4_lll_cond {p Δ r : ℕ} {δ : ℝ} (hp : 0 < p) (hδ : 0 < δ)
    (hr_ge : (Δ : ℝ) / 2 ≤ (r : ℝ))
    (hB2 : 2 * (p : ℝ) * (6 * (p : ℝ) ^ 2 / (((1 + 1 : ℝ) * Real.log (1 + 1) - 1) ^ 2) + 2) ≤ (Δ : ℝ)) :
    4 * Real.exp (-(((1 + 1 : ℝ) * Real.log (1 + 1) - 1) *
        (2 * (Nat.floor ((1 + δ) * ((r : ℝ) / (p : ℝ))) : ℝ)))) *
      (((2 * p ^ 2 * Nat.floor ((1 + δ) * ((r : ℝ) / (p : ℝ))) : ℕ) : ℝ) + 1) ≤ 1 := by
  let c₂ : ℝ := (1 + 1 : ℝ) * Real.log (1 + 1) - 1
  have hc₂ : 0 < c₂ := chernoff_const_pos one_pos
  have hp_real_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  let d_max : ℕ := Nat.floor ((1 + δ) * ((r : ℝ) / (p : ℝ)))
  have hd_max_ge_real : 6 * (p : ℝ) ^ 2 / c₂ ^ 2 + 1 ≤ (d_max : ℝ) := by
    have hlt : (1 + δ) * ((r : ℝ) / (p : ℝ)) - 1 < (d_max : ℝ) := by
      linarith [Nat.lt_floor_add_one ((1 + δ) * ((r : ℝ) / (p : ℝ)))]
    have h1 : (Δ : ℝ) / (2 * (p : ℝ)) ≤ (1 + δ) * ((r : ℝ) / (p : ℝ)) := by
      have h2 : (Δ : ℝ) / (2 * (p : ℝ)) ≤ (r : ℝ) / (p : ℝ) := by
        rw [← div_div]
        exact div_le_div_of_nonneg_right hr_ge hp_real_pos.le
      have h3 : (r : ℝ) / (p : ℝ) ≤ (1 + δ) * ((r : ℝ) / (p : ℝ)) :=
        le_mul_of_one_le_left (by positivity) (by linarith)
      exact le_trans h2 h3
    have h4 : 6 * (p : ℝ) ^ 2 / c₂ ^ 2 + 2 ≤ (Δ : ℝ) / (2 * (p : ℝ)) := by
      have hB2' : 2 * (p : ℝ) * (6 * (p : ℝ) ^ 2 / c₂ ^ 2 + 2) ≤ (Δ : ℝ) := hB2
      rw [le_div_iff₀ (by positivity)]
      linarith [hB2']
    linarith
  have hd_max_pos : 0 < d_max := by
    have : (1 : ℝ) ≤ (d_max : ℝ) := by
      have hnn : 0 ≤ 6 * (p : ℝ) ^ 2 / c₂ ^ 2 := by positivity
      linarith
    exact_mod_cast (by linarith : (0 : ℝ) < (d_max : ℝ))
  have hd_max_pos_real : (0 : ℝ) < (d_max : ℝ) := Nat.cast_pos.mpr hd_max_pos
  have hd_max_ge_B : 6 * (p : ℝ) ^ 2 / c₂ ^ 2 ≤ (d_max : ℝ) := by linarith
  have hexp_pow := Real.pow_div_factorial_le_exp (2 * c₂ * (d_max : ℝ)) (by positivity) 2
  have hfact2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hfact2] at hexp_pow
  have hexp_bound : Real.exp (-(c₂ * (2 * (d_max : ℝ)))) ≤
      1 / (2 * c₂ ^ 2 * (d_max : ℝ) ^ 2) := by
    have h1 : -(c₂ * (2 * (d_max : ℝ))) = -(2 * c₂ * (d_max : ℝ)) := by ring
    rw [h1, Real.exp_neg]
    have hpos_pow : 0 < (2 * c₂ * (d_max : ℝ)) ^ 2 / 2 := by positivity
    have h2 := inv_anti₀ hpos_pow hexp_pow
    have h3 : ((2 * c₂ * (d_max : ℝ)) ^ 2 / 2)⁻¹ = 1 / (2 * c₂ ^ 2 * (d_max : ℝ) ^ 2) := by ring
    linarith
  have hdeg_bound : (((2 * p ^ 2 * d_max : ℕ) : ℝ) + 1) ≤ 3 * (p : ℝ) ^ 2 * (d_max : ℝ) := by
    push_cast
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hd1 : (1 : ℝ) ≤ (d_max : ℝ) := by exact_mod_cast hd_max_pos
    nlinarith
  calc 4 * Real.exp (-(c₂ * (2 * (d_max : ℝ)))) * (((2 * p ^ 2 * d_max : ℕ) : ℝ) + 1)
      ≤ 4 * (1 / (2 * c₂ ^ 2 * (d_max : ℝ) ^ 2)) * (3 * (p : ℝ) ^ 2 * (d_max : ℝ)) := by
          refine mul_le_mul ?_ hdeg_bound (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hexp_bound (by norm_num)
    _ = (6 * (p : ℝ) ^ 2 / c₂ ^ 2) / (d_max : ℝ) := by field_simp [hc₂.ne', hd_max_pos_real.ne']; norm_num
    _ ≤ 1 := (div_le_one hd_max_pos_real).mpr hd_max_ge_B

lemma alon_final_arith {p Δ r : ℕ} {ε : ℝ} (hp : 0 < p) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp48 : 48 / ε ≤ (p : ℝ)) (hΔ8 : 8 / ε ≤ (Δ : ℝ)) (hr_le : (r : ℝ) ≤ ((Δ : ℝ) + 1) / 2) :
    (((p + 11) * Nat.floor ((1 + ε / 4) * ((r : ℝ) / (p : ℝ))) : ℕ) : ℝ) ≤ (1 / 2 + ε) * (Δ : ℝ) := by
  have hp_real_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hd_le : (Nat.floor ((1 + ε / 4) * ((r : ℝ) / (p : ℝ))) : ℝ) ≤ (1 + ε / 4) * ((r : ℝ) / (p : ℝ)) :=
    Nat.floor_le (by positivity)
  have hp11_le : ((p : ℝ) + 11) / (p : ℝ) ≤ 1 + ε / 4 := by
    have h1 : (11 : ℝ) ≤ (p : ℝ) * (ε / 4) := by
      have : 48 ≤ (p : ℝ) * ε := (div_le_iff₀ hε).mp hp48
      linarith
    rw [div_le_iff₀ hp_real_pos]
    linarith
  have hstep1 : (((p + 11) * Nat.floor ((1 + ε / 4) * ((r : ℝ) / (p : ℝ))) : ℕ) : ℝ) ≤
      (1 + ε / 4) * (1 + ε / 4) * (r : ℝ) := by
    push_cast
    calc ((p : ℝ) + 11) * (Nat.floor ((1 + ε / 4) * ((r : ℝ) / (p : ℝ))) : ℝ)
        ≤ ((p : ℝ) + 11) * ((1 + ε / 4) * ((r : ℝ) / (p : ℝ))) :=
            mul_le_mul_of_nonneg_left hd_le (by positivity)
      _ = (((p : ℝ) + 11) / (p : ℝ)) * (1 + ε / 4) * (r : ℝ) := by ring
      _ ≤ (1 + ε / 4) * (1 + ε / 4) * (r : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right hp11_le (by positivity)
  have hsq_le : (1 + ε / 4) * (1 + ε / 4) ≤ 1 + ε := by nlinarith [sq_nonneg ε]
  have hstep2 : (1 + ε / 4) * (1 + ε / 4) * (r : ℝ) ≤ (1 + ε) * (((Δ : ℝ) + 1) / 2) :=
    mul_le_mul hsq_le hr_le (Nat.cast_nonneg _) (by positivity)
  have hstep3 : (1 + ε) * (((Δ : ℝ) + 1) / 2) ≤ (1 / 2 + ε) * (Δ : ℝ) := by
    have hΔε : 8 ≤ (Δ : ℝ) * ε := (div_le_iff₀ hε).mp hΔ8
    nlinarith
  exact le_trans hstep1 (le_trans hstep2 hstep3)

lemma alon_graph_decomp {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ p : ℕ) [Fact p.Prime] (δ : ℝ) (hδ : 0 < δ) (hΔ_max : G.maxDegree ≤ Δ)
    (hLLL2 : 4 * (2 * (p : ℝ) *
      Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * ((((Δ + 1) / 2 : ℕ) : ℝ) / (p : ℝ))))) *
      (((Δ ^ 2 + Δ + 1 : ℕ) : ℝ) + 1) ≤ 1)
    (hLLL4 : 4 * Real.exp (-(((1 + 1 : ℝ) * Real.log (1 + 1) - 1) *
        (2 * (Nat.floor ((1 + δ) * ((((Δ + 1) / 2 : ℕ) : ℝ) / (p : ℝ))) : ℝ)))) *
      (((2 * p ^ 2 * Nat.floor ((1 + δ) * ((((Δ + 1) / 2 : ℕ) : ℝ) / (p : ℝ))) : ℕ) : ℝ) + 1) ≤ 1) :
    LinearArboricityConjecture.linearArboricity G ≤
      (p + 11) * Nat.floor ((1 + δ) * ((((Δ + 1) / 2 : ℕ) : ℝ) / (p : ℝ))) := by
  classical
  let r : ℕ := (Δ + 1) / 2
  let d_max : ℕ := Nat.floor ((1 + δ) * ((r : ℝ) / (p : ℝ)))
  have hp_pos : 0 < p := Nat.Prime.pos Fact.out
  obtain ⟨D, hD_asym, hD_cov, hD_deg⟩ := balanced_orientation_deg_bound G hΔ_max
  have hD_sub : ∀ u v, D u v → G.Adj u v := fun u v h => (hD_cov u v).mpr (Or.inl h)
  obtain ⟨c, hc⟩ := step2_vertex_coloring G D hD_sub Δ r p hΔ_max hD_deg δ hδ hLLL2
  let J := {j : ZMod p // j ≠ 0}
  have hJ_card : Fintype.card J = p - 1 := by
    let eJ : J ≃ {y : ZMod p // y ∈ (Finset.univ : Finset (ZMod p)).erase 0} :=
      { toFun := fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩
        invFun := fun y => ⟨y.1, (Finset.mem_erase.mp y.2).1⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
    rw [Fintype.card_congr eJ, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  have hkonig : ∀ j : J, ∃ M_j : Fin d_max → V → V → Prop,
      (∀ a u v, M_j a u v → D u v ∧ c v = c u + j.1) ∧
      (∀ u v, D u v ∧ c v = c u + j.1 → ∃! a : Fin d_max, M_j a u v) ∧
      (∀ a u, outDeg (M_j a) u ≤ 1) ∧ (∀ a v, inDeg (M_j a) v ≤ 1) :=
    fun j => konig_digraph_decomp d_max (fun u v => D u v ∧ c v = c u + j.1)
      (fun v => (hc v j.1).1) (fun v => (hc v j.1).2)
  let M : J × Fin d_max → V → V → Prop := fun ⟨j, a⟩ => (Classical.choose (hkonig j)) a
  have hM_sub : ∀ idx u v, M idx u v → D u v ∧ c v = c u + idx.1.1 :=
    fun ⟨j, a⟩ u v h => (Classical.choose_spec (hkonig j)).1 a u v h
  have hM_uniq : ∀ (j : J) u v, D u v ∧ c v = c u + j.1 → ∃! a : Fin d_max, M (j, a) u v :=
    fun j u v h => (Classical.choose_spec (hkonig j)).2.1 u v h
  have hM_out : ∀ idx u, outDeg (M idx) u ≤ 1 :=
    fun ⟨j, a⟩ u => (Classical.choose_spec (hkonig j)).2.2.1 a u
  have hM_in : ∀ idx v, inDeg (M idx) v ≤ 1 :=
    fun ⟨j, a⟩ v => (Classical.choose_spec (hkonig j)).2.2.2 a v
  have hM_asym : ∀ idx u v, M idx u v → ¬ M idx v u := by
    intro idx u v huv hvu
    exact hD_asym u v (hM_sub idx u v huv).1 (hM_sub idx v u hvu).1
  have hM_len : ∀ idx (r : Cyc (M idx)), p ≤ cycLen (M idx) r := by
    intro idx r
    exact cycle_len_ge_p (M idx) (hM_out idx) c idx.1.2
      (fun u w h => (hM_sub idx u w h).2) r
  have hcard_ι : Fintype.card (J × Fin d_max) ≤ p * d_max := by
    rw [Fintype.card_prod, hJ_card, Fintype.card_fin]
    exact Nat.mul_le_mul_right d_max (Nat.sub_le p 1)
  obtain ⟨ω, hω⟩ := step4_cycle_breaking M p d_max hM_len hcard_ι hLLL4
  let G_rem : SimpleGraph V := breakRemGraph M p ω
  have hG_rem_deg : G_rem.maxDegree ≤ 4 * d_max :=
    SimpleGraph.maxDegree_le_of_forall_degree_le _ (4 * d_max) hω
  obtain ⟨F_rem, hF_rem_prop, hF_rem_uniq⟩ := greedy_matching_decomp (4 * d_max) G_rem hG_rem_deg
  let G₀ : SimpleGraph V :=
    { Adj := fun u v => (D u v ∧ c v = c u) ∨ (D v u ∧ c u = c v)
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun u h => by
        rcases h with ⟨hD, _⟩ | ⟨hD, _⟩ <;> exact G.ne_of_adj (hD_sub u u hD) rfl⟩ }
  have hG₀_deg : G₀.maxDegree ≤ 2 * d_max := by
    refine SimpleGraph.maxDegree_le_of_forall_degree_le _ (2 * d_max) fun v => ?_
    rw [← ncard_neighborSet_eq_degree]
    have hsub : G₀.neighborSet v ⊆
        {w : V | D v w ∧ c w = c v + 0} ∪ {u : V | D u v ∧ c v = c u + 0} := by
      intro w hw
      rw [mem_neighborSet] at hw
      rcases hw with ⟨hD, hc0⟩ | ⟨hD, hc0⟩
      · exact Or.inl ⟨hD, by simpa using hc0⟩
      · exact Or.inr ⟨hD, by simpa using hc0⟩
    calc (G₀.neighborSet v).ncard
        ≤ ({w : V | D v w ∧ c w = c v + 0} ∪ {u : V | D u v ∧ c v = c u + 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({w : V | D v w ∧ c w = c v + 0} : Set V).ncard +
          ({u : V | D u v ∧ c v = c u + 0} : Set V).ncard :=
            Set.ncard_union_le _ _
      _ ≤ d_max + d_max := Nat.add_le_add (hc v 0).1 (hc v 0).2
      _ = 2 * d_max := (Nat.two_mul d_max).symm
  obtain ⟨F₀, hF₀_prop, hF₀_uniq⟩ := greedy_matching_decomp (2 * d_max) G₀ hG₀_deg
  let H_idx : J × Fin d_max → SimpleGraph V := fun idx =>
    { Adj := fun u v => M idx u v ∨ M idx v u
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun u h => by rcases h with h1 | h1 <;> exact hM_asym idx u u h1 h1⟩ }
  let delSet : J × Fin d_max → Set (Sym2 V) := fun idx =>
    {e | ∃ r : Cyc (M idx), e = cycEdge (M idx) p r (ω ⟨idx, r⟩)}
  let F_cyc : J × Fin d_max → SimpleGraph V := fun idx =>
    (H_idx idx).deleteEdges (delSet idx)
  have hF_cyc_lf : ∀ idx, LinearArboricityConjecture.IsLinearForest (F_cyc idx) ∧ F_cyc idx ≤ G := by
    intro idx
    refine ⟨⟨acyclic_after_breaking (M idx) (hM_out idx) (hM_in idx)
      (fun _ _ => Iff.rfl) p (hM_len idx) (fun r => ω ⟨idx, r⟩), ?_⟩, ?_⟩
    · intro v
      have hsub : (F_cyc idx).neighborSet v ⊆ {w : V | M idx v w} ∪ {u : V | M idx u v} := by
        intro w hw
        rw [mem_neighborSet] at hw
        exact deleteEdges_le _ hw
      calc ((F_cyc idx).neighborSet v).ncard
          ≤ ({w : V | M idx v w} ∪ {u : V | M idx u v}).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({w : V | M idx v w} : Set V).ncard + ({u : V | M idx u v} : Set V).ncard :=
              Set.ncard_union_le _ _
        _ ≤ 1 + 1 := Nat.add_le_add (hM_out idx v) (hM_in idx v)
    · intro u v h
      have hadj : (H_idx idx).Adj u v := deleteEdges_le _ h
      rcases hadj with h1 | h1
      · exact hD_sub u v (hM_sub idx u v h1).1
      · exact (hD_sub v u (hM_sub idx v u h1).1).symm
  have hG_rem_le : G_rem ≤ G := by
    intro u v ⟨_, γ, hs⟩
    have hm : M γ.1 (cycStart (M γ.1) p γ.2 (ω γ)) (cycEnd (M γ.1) p γ.2 (ω γ)) :=
      cycEdge_mem_M (M γ.1) (hM_out γ.1) γ.2 (hM_len γ.1 γ.2) (ω γ)
    have hadj : G.Adj (cycStart (M γ.1) p γ.2 (ω γ)) (cycEnd (M γ.1) p γ.2 (ω γ)) :=
      hD_sub _ _ (hM_sub γ.1 _ _ hm).1
    have hmem : s(u, v) = s(cycStart (M γ.1) p γ.2 (ω γ), cycEnd (M γ.1) p γ.2 (ω γ)) := hs
    rw [Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  have hG₀_le : G₀ ≤ G := by
    intro u v h
    rcases h with ⟨hD, _⟩ | ⟨hD, _⟩
    · exact hD_sub u v hD
    · exact (hD_sub v u hD).symm
  let SumIdx := Fin (2 * (2 * d_max)) ⊕ (J × Fin d_max) ⊕ Fin (2 * (4 * d_max))
  let F_sum : SumIdx → SimpleGraph V
    | Sum.inl i => F₀ i
    | Sum.inr (Sum.inl idx) => F_cyc idx
    | Sum.inr (Sum.inr k) => F_rem k
  have hF_sum_prop : ∀ s : SumIdx, LinearArboricityConjecture.IsLinearForest (F_sum s) ∧ F_sum s ≤ G := by
    rintro (i | idx | k)
    · exact ⟨isLinearForest_of_deg_le_one (F₀ i) (hF₀_prop i).1, le_trans (hF₀_prop i).2 hG₀_le⟩
    · exact hF_cyc_lf idx
    · exact ⟨isLinearForest_of_deg_le_one (F_rem k) (hF_rem_prop k).1, le_trans (hF_rem_prop k).2 hG_rem_le⟩
  have hF_sum_cov : ∀ u v, G.Adj u v ↔ ∃! s : SumIdx, (F_sum s).Adj u v := by
    intro u v
    constructor
    · intro huv
      have hGrem_or : ∀ (j : J), D u v ∧ c v = c u + j.1 →
          ∃! idx : J × Fin d_max, (H_idx idx).Adj u v := by
        intro j hj
        obtain ⟨a, ha, ha_uniq⟩ := hM_uniq j u v hj
        refine ⟨(j, a), Or.inl ha, ?_⟩
        rintro ⟨j', a'⟩ (h1 | h1)
        · have hj'_eq : j' = j := by
            have hcj := (hM_sub (j', a') u v h1).2
            have : c u + j'.1 = c u + j.1 := hcj.symm.trans hj.2
            exact Subtype.ext (add_left_cancel this)
          subst hj'_eq
          exact Prod.ext rfl (ha_uniq a' h1)
        · exact absurd (hM_sub (j', a') v u h1).1 (hD_asym u v hj.1)
      have hGrem_or_sym : ∀ (j : J), D v u ∧ c u = c v + j.1 →
          ∃! idx : J × Fin d_max, (H_idx idx).Adj u v := by
        intro j hj
        obtain ⟨a, ha, ha_uniq⟩ := hM_uniq j v u hj
        refine ⟨(j, a), Or.inr ha, ?_⟩
        rintro ⟨j', a'⟩ (h1 | h1)
        · exact absurd (hM_sub (j', a') u v h1).1 (hD_asym v u hj.1)
        · have hj'_eq : j' = j := by
            have hcj := (hM_sub (j', a') v u h1).2
            have : c v + j'.1 = c v + j.1 := hcj.symm.trans hj.2
            exact Subtype.ext (add_left_cancel this)
          subst hj'_eq
          exact Prod.ext rfl (ha_uniq a' h1)
      have hGrem_none_of_zero : c v = c u →
          (∀ idx, ¬ (H_idx idx).Adj u v) ∧ ¬ G_rem.Adj u v := by
        intro hcv
        have hH : ∀ idx, ¬ (H_idx idx).Adj u v := by
          intro idx hadj
          rcases hadj with h1 | h1
          · have h2 := (hM_sub idx u v h1).2
            rw [hcv] at h2
            exact idx.1.2 (add_left_cancel (by rw [add_zero]; exact h2.symm))
          · have h2 := (hM_sub idx v u h1).2
            rw [hcv] at h2
            exact idx.1.2 (add_left_cancel (by rw [add_zero]; exact h2.symm))
        refine ⟨hH, fun ⟨_, γ, hs⟩ => ?_⟩
        have hm := cycEdge_mem_M (M γ.1) (hM_out γ.1) γ.2 (hM_len γ.1 γ.2) (ω γ)
        have hhadj : (H_idx γ.1).Adj u v := by
          have hmem : s(u, v) = s(cycStart (M γ.1) p γ.2 (ω γ), cycEnd (M γ.1) p γ.2 (ω γ)) := hs
          rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl hm
          · exact Or.inr hm
        exact hH γ.1 hhadj
      rcases (hD_cov u v).mp huv with hDu | hDv
      · by_cases hc0 : c v = c u
        · obtain ⟨hH0, hRem0⟩ := hGrem_none_of_zero hc0
          obtain ⟨i, hi, hi_uniq⟩ := (hF₀_uniq u v).mp (Or.inl ⟨hDu, hc0⟩)
          refine ⟨Sum.inl i, hi, ?_⟩
          rintro (i' | idx' | k') hsf
          · exact congrArg Sum.inl (hi_uniq i' hsf)
          · exact absurd (deleteEdges_le _ hsf) (hH0 idx')
          · exact absurd ((hF_rem_prop k').2 hsf) hRem0
        · let j : J := ⟨c v - c u, sub_ne_zero.mpr hc0⟩
          have hj : D u v ∧ c v = c u + j.1 := ⟨hDu, by dsimp [j]; ring⟩
          obtain ⟨idx, hHidx, hHuniq⟩ := hGrem_or j hj
          have hother : ∀ idx', idx' ≠ idx → ¬ (F_cyc idx').Adj u v := fun idx' hne h =>
            hne (hHuniq idx' (deleteEdges_le _ h))
          have hnotG₀ : ¬ G₀.Adj u v := by
            rintro (⟨_, h⟩ | ⟨hD', _⟩)
            · exact hc0 h
            · exact hD_asym u v hDu hD'
          by_cases hdel : s(u, v) ∈ delSet idx
          · have hGrem : G_rem.Adj u v := by
              rcases hdel with ⟨r, hr⟩
              exact ⟨huv.ne, ⟨idx, r⟩, hr⟩
            obtain ⟨k, hk, hk_uniq⟩ := (hF_rem_uniq u v).mp hGrem
            refine ⟨Sum.inr (Sum.inr k), hk, ?_⟩
            rintro (i | idx' | k') hsf
            · exact absurd ((hF₀_prop i).2 hsf) hnotG₀
            · by_cases heq : idx' = idx
              · subst heq
                rw [deleteEdges_adj] at hsf
                exact absurd hdel hsf.2
              · exact absurd hsf (hother idx' heq)
            · exact congrArg (Sum.inr ∘ Sum.inr) (hk_uniq k' hsf)
          · have hFc : (F_cyc idx).Adj u v := deleteEdges_adj.mpr ⟨hHidx, hdel⟩
            have hnotGrem : ¬ G_rem.Adj u v := by
              rintro ⟨_, ⟨idx', r'⟩, hr'⟩
              have hHidx' : (H_idx idx').Adj u v := by
                have hm := cycEdge_mem_M (M idx') (hM_out idx') r' (hM_len idx' r') (ω ⟨idx', r'⟩)
                have hmem : s(u, v) = s(cycStart (M idx') p r' (ω ⟨idx', r'⟩),
                    cycEnd (M idx') p r' (ω ⟨idx', r'⟩)) := hr'
                rw [Sym2.eq_iff] at hmem
                rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inl hm
                · exact Or.inr hm
              have heq : idx' = idx := hHuniq idx' hHidx'
              subst heq
              exact hdel ⟨r', hr'⟩
            refine ⟨Sum.inr (Sum.inl idx), hFc, ?_⟩
            rintro (i | idx' | k') hsf
            · exact absurd ((hF₀_prop i).2 hsf) hnotG₀
            · exact congrArg (Sum.inr ∘ Sum.inl) (hHuniq idx' (deleteEdges_le _ hsf))
            · exact absurd ((hF_rem_prop k').2 hsf) hnotGrem
      · by_cases hc0 : c u = c v
        · obtain ⟨hH0, hRem0⟩ := hGrem_none_of_zero hc0.symm
          obtain ⟨i, hi, hi_uniq⟩ := (hF₀_uniq u v).mp (Or.inr ⟨hDv, hc0⟩)
          refine ⟨Sum.inl i, hi, ?_⟩
          rintro (i' | idx' | k') hsf
          · exact congrArg Sum.inl (hi_uniq i' hsf)
          · exact absurd (deleteEdges_le _ hsf) (hH0 idx')
          · exact absurd ((hF_rem_prop k').2 hsf) hRem0
        · let j : J := ⟨c u - c v, sub_ne_zero.mpr hc0⟩
          have hj : D v u ∧ c u = c v + j.1 := ⟨hDv, by dsimp [j]; ring⟩
          obtain ⟨idx, hHidx, hHuniq⟩ := hGrem_or_sym j hj
          have hother : ∀ idx', idx' ≠ idx → ¬ (F_cyc idx').Adj u v := fun idx' hne h =>
            hne (hHuniq idx' (deleteEdges_le _ h))
          have hnotG₀ : ¬ G₀.Adj u v := by
            rintro (⟨hD', _⟩ | ⟨_, h⟩)
            · exact hD_asym v u hDv hD'
            · exact hc0 h
          by_cases hdel : s(u, v) ∈ delSet idx
          · have hGrem : G_rem.Adj u v := by
              rcases hdel with ⟨r, hr⟩
              exact ⟨huv.ne, ⟨idx, r⟩, hr⟩
            obtain ⟨k, hk, hk_uniq⟩ := (hF_rem_uniq u v).mp hGrem
            refine ⟨Sum.inr (Sum.inr k), hk, ?_⟩
            rintro (i | idx' | k') hsf
            · exact absurd ((hF₀_prop i).2 hsf) hnotG₀
            · by_cases heq : idx' = idx
              · subst heq
                rw [deleteEdges_adj] at hsf
                exact absurd hdel hsf.2
              · exact absurd hsf (hother idx' heq)
            · exact congrArg (Sum.inr ∘ Sum.inr) (hk_uniq k' hsf)
          · have hFc : (F_cyc idx).Adj u v := deleteEdges_adj.mpr ⟨hHidx, hdel⟩
            have hnotGrem : ¬ G_rem.Adj u v := by
              rintro ⟨_, ⟨idx', r'⟩, hr'⟩
              have hHidx' : (H_idx idx').Adj u v := by
                have hm := cycEdge_mem_M (M idx') (hM_out idx') r' (hM_len idx' r') (ω ⟨idx', r'⟩)
                have hmem : s(u, v) = s(cycStart (M idx') p r' (ω ⟨idx', r'⟩),
                    cycEnd (M idx') p r' (ω ⟨idx', r'⟩)) := hr'
                rw [Sym2.eq_iff] at hmem
                rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inl hm
                · exact Or.inr hm
              have heq : idx' = idx := hHuniq idx' hHidx'
              subst heq
              exact hdel ⟨r', hr'⟩
            refine ⟨Sum.inr (Sum.inl idx), hFc, ?_⟩
            rintro (i | idx' | k') hsf
            · exact absurd ((hF₀_prop i).2 hsf) hnotG₀
            · exact congrArg (Sum.inr ∘ Sum.inl) (hHuniq idx' (deleteEdges_le _ hsf))
            · exact absurd ((hF_rem_prop k').2 hsf) hnotGrem
    · rintro ⟨s, hs, _⟩
      exact (hF_sum_prop s).2 hs
  have hcard_eq : Fintype.card SumIdx = (p + 11) * d_max := by
    simp only [SumIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hJ_card]
    have h1 : 2 * (2 * d_max) + ((p - 1) * d_max + 2 * (4 * d_max)) = (p - 1 + 12) * d_max := by ring
    rw [h1]
    congr 1
    omega
  let e : SumIdx ≃ Fin ((p + 11) * d_max) := Fintype.equivFinOfCardEq hcard_eq
  refine Nat.sInf_le ⟨fun i => F_sum (e.symm i), fun i => hF_sum_prop (e.symm i), fun u v => ?_⟩
  rw [hF_sum_cov u v]
  constructor
  · rintro ⟨s, hs, huniq⟩
    refine ⟨e s, by simpa using hs, fun i hi => ?_⟩
    rw [← huniq (e.symm i) hi]
    simp
  · rintro ⟨i, hi, huniq⟩
    refine ⟨e.symm i, hi, fun s hs => ?_⟩
    have := huniq (e s) (by simpa using hs)
    simpa using congrArg e.symm this

lemma alon_linear_arboricity_given_p (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (p : ℕ) [Fact p.Prime] (hp48 : 48 / ε ≤ (p : ℝ)) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (LinearArboricityConjecture.linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ := by
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hp_pos : 0 < p := Nat.Prime.pos Fact.out
  let c₁ : ℝ := (1 + δ) * Real.log (1 + δ) - δ
  let α₁ : ℝ := c₁ / (2 * (p : ℝ))
  let c₂ : ℝ := (1 + 1 : ℝ) * Real.log (1 + 1) - 1
  let Δ₀ : ℕ := max (Nat.ceil (8 / ε))
    (max (Nat.ceil (144 * (p : ℝ) / α₁ ^ 3) + 2)
      (Nat.ceil (2 * (p : ℝ) * (6 * (p : ℝ) ^ 2 / c₂ ^ 2 + 2)) + 2))
  refine ⟨Δ₀, fun Δ hΔ_ge V _ G _ hΔ_max => ?_⟩
  have hΔ8 : 8 / ε ≤ (Δ : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_trans (le_max_left _ _) hΔ_ge))
  have hB1 : 144 * (p : ℝ) / α₁ ^ 3 ≤ (Δ : ℝ) := by
    have h1 : Nat.ceil (144 * (p : ℝ) / α₁ ^ 3) + 2 ≤ Δ :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΔ_ge
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (by omega))
  have hΔ2 : 2 ≤ Δ := by
    have h1 : Nat.ceil (144 * (p : ℝ) / α₁ ^ 3) + 2 ≤ Δ :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΔ_ge
    omega
  have hB2 : 2 * (p : ℝ) * (6 * (p : ℝ) ^ 2 / c₂ ^ 2 + 2) ≤ (Δ : ℝ) := by
    have h1 : Nat.ceil (2 * (p : ℝ) * (6 * (p : ℝ) ^ 2 / c₂ ^ 2 + 2)) + 2 ≤ Δ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΔ_ge
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (by omega))
  let r : ℕ := (Δ + 1) / 2
  have hr_ge : (Δ : ℝ) / 2 ≤ (r : ℝ) := by
    have hnat : Δ ≤ 2 * r := by dsimp [r]; omega
    have hreal : (Δ : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hnat
    linarith
  have hr_le : (r : ℝ) ≤ ((Δ : ℝ) + 1) / 2 := by
    have hnat : 2 * r ≤ Δ + 1 := by dsimp [r]; omega
    have hreal : 2 * (r : ℝ) ≤ (Δ : ℝ) + 1 := by exact_mod_cast hnat
    linarith
  have hLLL2 := alon_step2_lll_cond hp_pos hδ hΔ2 hr_ge hB1
  have hLLL4 := alon_step4_lll_cond hp_pos hδ hr_ge hB2
  have hla := alon_graph_decomp G Δ p δ hδ hΔ_max hLLL2 hLLL4
  have hbound := alon_final_arith hp_pos hε hε1 hp48 hΔ8 hr_le
  exact le_trans (Nat.cast_le.mpr hla) hbound

lemma alon_linear_arboricity_asymp_le_one (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (LinearArboricityConjecture.linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ := by
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (Nat.ceil (48 / ε) + 3)
  have hp48 : 48 / ε ≤ (p : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (Nat.le_add_right _ 3) hp_ge)
  exact @alon_linear_arboricity_given_p ε hε hε1 p ⟨hp_prime⟩ hp48

theorem alon_linear_arboricity_asymp (ε : ℝ) (hε : 0 < ε) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (LinearArboricityConjecture.linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ := by
  by_cases hε1 : ε ≤ 1
  · exact alon_linear_arboricity_asymp_le_one ε hε hε1
  · obtain ⟨Δ₀, hΔ₀⟩ := alon_linear_arboricity_asymp_le_one 1 one_pos le_rfl
    refine ⟨Δ₀, fun Δ hΔ V _ G _ hG => ?_⟩
    have hle := hΔ₀ Δ hΔ V G hG
    have hge : 1 ≤ ε := le_of_not_ge hε1
    have hΔnn : (0 : ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _
    nlinarith

end Assembly

end

end AlonLA

theorem OMA.solution : type_of% @LinearArboricityConjecture.linear_arboricity_conjecture.variants.alon :=
  AlonLA.alon_linear_arboricity_asymp
