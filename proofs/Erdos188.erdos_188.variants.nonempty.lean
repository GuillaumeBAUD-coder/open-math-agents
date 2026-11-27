import FormalConjectures.ErdosProblems.«188»
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Data.Int.Interval

-- Problem: Erdős Problem 188 — nonempty
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/188.lean:61 (declaration Erdos188.erdos_188.variants.nonempty)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Proof of Erdős Problem 188 (nonempty variant)

We prove `Erdos188.erdos_188.variants.nonempty` via a finite Bernoulli product measure,
the symmetric Lovász Local Lemma, an $L_\infty$-grid construction, and Tychonoff compactness.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos188Solution

/- ### Part 1: Finite Bernoulli Product Probability -/

section BernoulliProb

variable {α : Type*} [DecidableEq α]

noncomputable def weight (V : Finset α) (p₀ : ℝ) (f : V → Bool) : ℝ :=
  ∏ x : V, if f x then p₀ else 1 - p₀

noncomputable def prob (V : Finset α) (p₀ : ℝ) (P : (V → Bool) → Prop) : ℝ :=
  letI := Classical.decPred P
  ∑ f : V → Bool, if P f then weight V p₀ f else 0

def DependsOn (V S : Finset α) (P : (V → Bool) → Prop) : Prop :=
  ∀ f g : V → Bool, (∀ x : V, x.1 ∈ S → f x = g x) → (P f ↔ P g)

omit [DecidableEq α] in
lemma weight_nonneg (V : Finset α) {p₀ : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : p₀ ≤ 1) (f : V → Bool) :
    0 ≤ weight V p₀ f := by
  unfold weight
  apply Finset.prod_nonneg
  intro x _
  split_ifs <;> linarith

lemma prob_nonneg (V : Finset α) {p₀ : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : p₀ ≤ 1)
    (P : (V → Bool) → Prop) : 0 ≤ prob V p₀ P := by
  unfold prob
  apply Finset.sum_nonneg
  intro f _
  split_ifs
  · exact weight_nonneg V hp₀ hp₁ f
  · exact le_rfl

lemma prob_congr (V : Finset α) (p₀ : ℝ) {P Q : (V → Bool) → Prop} (h : ∀ f, P f ↔ Q f) :
    prob V p₀ P = prob V p₀ Q := by
  unfold prob
  apply Finset.sum_congr rfl
  intro f _
  by_cases hP : P f
  · have hQ : Q f := (h f).1 hP
    simp only [if_pos hP, if_pos hQ]
  · have hQ : ¬ Q f := mt (h f).2 hP
    simp only [if_neg hP, if_neg hQ]

lemma prob_mono (V : Finset α) {p₀ : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : p₀ ≤ 1)
    {P Q : (V → Bool) → Prop} (h : ∀ f, P f → Q f) :
    prob V p₀ P ≤ prob V p₀ Q := by
  unfold prob
  apply Finset.sum_le_sum
  intro f _
  split_ifs with hP hQ
  · exact le_rfl
  · exact absurd (h f hP) hQ
  · exact weight_nonneg V hp₀ hp₁ f
  · exact le_rfl

lemma prob_true (V : Finset α) (p₀ : ℝ) : prob V p₀ (fun _ => True) = 1 := by
  unfold prob weight
  simp only [if_true]
  rw [← Fintype.prod_sum (fun (_ : V) (b : Bool) => if b then p₀ else 1 - p₀)]
  simp

lemma prob_and_not (V : Finset α) (p₀ : ℝ) (P Q : (V → Bool) → Prop) :
    prob V p₀ (fun f => P f ∧ ¬ Q f) = prob V p₀ P - prob V p₀ (fun f => P f ∧ Q f) := by
  unfold prob
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hP : P f <;> by_cases hQ : Q f <;> simp [hP, hQ]

lemma prob_not (V : Finset α) (p₀ : ℝ) (Q : (V → Bool) → Prop) :
    prob V p₀ (fun f => ¬ Q f) = 1 - prob V p₀ Q := by
  have h := prob_and_not V p₀ (fun _ => True) Q
  simpa [prob_true] using h

lemma exists_of_prob_pos (V : Finset α) (p₀ : ℝ) {P : (V → Bool) → Prop}
    (h : 0 < prob V p₀ P) : ∃ f : V → Bool, P f := by
  by_contra hne
  push Not at hne
  have hzero : prob V p₀ P = 0 := by
    unfold prob
    apply Finset.sum_eq_zero
    intro f _
    simp [hne f]
  linarith

omit [DecidableEq α] in
lemma dependsOn_mono {V S₁ S₂ : Finset α} {P : (V → Bool) → Prop}
    (h : DependsOn V S₁ P) (hsub : S₁ ⊆ S₂) : DependsOn V S₂ P :=
  fun f g hfg => h f g (fun x hx => hfg x (hsub hx))

omit [DecidableEq α] in
lemma dependsOn_not {V S : Finset α} {P : (V → Bool) → Prop}
    (h : DependsOn V S P) : DependsOn V S (fun f => ¬ P f) :=
  fun f g hfg => not_congr (h f g hfg)

lemma dependsOn_biAll {ι : Type*} {V : Finset α} {I : Finset ι}
    {S : ι → Finset α} {P : ι → (V → Bool) → Prop}
    (h : ∀ i ∈ I, DependsOn V (S i) (P i)) :
    DependsOn V (I.biUnion S) (fun f => ∀ i ∈ I, P i f) := by
  intro f g hfg
  constructor <;> intro hf i hi
  · exact (h i hi f g (fun x hx => hfg x (Finset.mem_biUnion.2 ⟨i, hi, hx⟩))).1 (hf i hi)
  · exact (h i hi f g (fun x hx => hfg x (Finset.mem_biUnion.2 ⟨i, hi, hx⟩))).2 (hf i hi)

/-- Equivalence splitting `V → Bool` along `A ⊆ V` into `(A → Bool) × ((V \ A) → Bool)`. -/
def piSplitEquiv (V A : Finset α) (hA : A ⊆ V) :
    (V → Bool) ≃ (A → Bool) × ((V \ A : Finset α) → Bool) where
  toFun f := (fun x => f ⟨x.1, hA x.2⟩, fun y => f ⟨y.1, (Finset.mem_sdiff.1 y.2).1⟩)
  invFun fg x :=
    if hx : x.1 ∈ A then fg.1 ⟨x.1, hx⟩
    else fg.2 ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hx⟩⟩
  left_inv f := by
    funext x
    by_cases hx : x.1 ∈ A <;> simp [hx]
  right_inv fg := by
    ext x
    · simp [x.2]
    · have hx : x.1 ∉ A := (Finset.mem_sdiff.1 x.2).2
      simp [hx]

lemma weight_split (V A : Finset α) (hA : A ⊆ V) (p₀ : ℝ) (f : V → Bool) :
    weight V p₀ f =
      weight A p₀ (piSplitEquiv V A hA f).1 *
      weight (V \ A) p₀ (piSplitEquiv V A hA f).2 := by
  unfold weight
  have hV : V = A ∪ (V \ A) := (Finset.union_sdiff_of_subset hA).symm
  have hdisj : Disjoint A (V \ A) := Finset.disjoint_sdiff
  let g : α → ℝ := fun x =>
    if hx : x ∈ V then (if f ⟨x, hx⟩ then p₀ else 1 - p₀) else 1
  have h1 : (∏ x : V, if f x then p₀ else 1 - p₀) = ∏ x ∈ V, g x := by
    rw [← Finset.prod_attach V g]
    apply Finset.prod_congr rfl
    intro x _
    simp [g, x.2]
  have h2 : (∏ x : A, if (piSplitEquiv V A hA f).1 x then p₀ else 1 - p₀) = ∏ x ∈ A, g x := by
    rw [← Finset.prod_attach A g]
    apply Finset.prod_congr rfl
    intro x _
    simp only [g, piSplitEquiv, Equiv.coe_fn_mk, dif_pos (hA x.2)]
    rfl
  have h3 : (∏ x : (V \ A : Finset α), if (piSplitEquiv V A hA f).2 x then p₀ else 1 - p₀) =
      ∏ x ∈ V \ A, g x := by
    rw [← Finset.prod_attach (V \ A) g]
    apply Finset.prod_congr rfl
    intro x _
    simp only [g, piSplitEquiv, Equiv.coe_fn_mk, dif_pos (Finset.mem_sdiff.1 x.2).1]
    rfl
  rw [h1, h2, h3]
  conv_lhs => rw [hV]
  rw [Finset.prod_union hdisj]

lemma prob_split (V A : Finset α) (hA : A ⊆ V) (p₀ : ℝ)
    (P₁ : (A → Bool) → Prop) (P₂ : ((V \ A : Finset α) → Bool) → Prop) :
    prob V p₀ (fun f => P₁ (piSplitEquiv V A hA f).1 ∧ P₂ (piSplitEquiv V A hA f).2) =
      prob A p₀ P₁ * prob (V \ A) p₀ P₂ := by
  classical
  unfold prob
  rw [Fintype.sum_equiv (piSplitEquiv V A hA) _
    (fun fg => if P₁ fg.1 ∧ P₂ fg.2 then weight A p₀ fg.1 * weight (V \ A) p₀ fg.2 else 0)]
  · rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f₂ _
    by_cases h1 : P₁ f₁ <;> by_cases h2 : P₂ f₂ <;> simp [h1, h2]
  · intro f
    simp only [weight_split V A hA p₀ f]

lemma prob_and_of_disjoint (V S₁ S₂ : Finset α) (hS₁ : S₁ ⊆ V) (_hS₂ : S₂ ⊆ V)
    (hdisj : Disjoint S₁ S₂) (p₀ : ℝ)
    {P₁ P₂ : (V → Bool) → Prop}
    (hP₁ : DependsOn V S₁ P₁) (hP₂ : DependsOn V S₂ P₂) :
    prob V p₀ (fun f => P₁ f ∧ P₂ f) = prob V p₀ P₁ * prob V p₀ P₂ := by
  let ext₁ : (S₁ → Bool) → (V → Bool) := fun f₁ x =>
    if hx : x.1 ∈ S₁ then f₁ ⟨x.1, hx⟩ else false
  let ext₂ : ((V \ S₁ : Finset α) → Bool) → (V → Bool) := fun f₂ x =>
    if hx : x.1 ∈ V \ S₁ then f₂ ⟨x.1, hx⟩ else false
  let Q₁ : (S₁ → Bool) → Prop := fun f₁ => P₁ (ext₁ f₁)
  let Q₂ : ((V \ S₁ : Finset α) → Bool) → Prop := fun f₂ => P₂ (ext₂ f₂)
  have hQ₁ : ∀ f : V → Bool, P₁ f ↔ Q₁ (piSplitEquiv V S₁ hS₁ f).1 := by
    intro f
    apply hP₁
    intro x hx
    simp [ext₁, piSplitEquiv, hx]
  have hQ₂ : ∀ f : V → Bool, P₂ f ↔ Q₂ (piSplitEquiv V S₁ hS₁ f).2 := by
    intro f
    apply hP₂
    intro x hx
    have hx' : x.1 ∈ V \ S₁ := Finset.mem_sdiff.2 ⟨x.2, Finset.disjoint_right.1 hdisj hx⟩
    simp only [ext₂, piSplitEquiv, Equiv.coe_fn_mk, dif_pos hx']
  have h12 : prob V p₀ (fun f => P₁ f ∧ P₂ f) = prob S₁ p₀ Q₁ * prob (V \ S₁) p₀ Q₂ := by
    rw [prob_congr V p₀ (fun f => and_congr (hQ₁ f) (hQ₂ f))]
    exact prob_split V S₁ hS₁ p₀ Q₁ Q₂
  have h1 : prob V p₀ P₁ = prob S₁ p₀ Q₁ := by
    have := prob_split V S₁ hS₁ p₀ Q₁ (fun _ => True)
    rw [prob_true, mul_one] at this
    rw [← this]
    exact prob_congr V p₀ (fun f => by simpa using hQ₁ f)
  have h2 : prob V p₀ P₂ = prob (V \ S₁) p₀ Q₂ := by
    have := prob_split V S₁ hS₁ p₀ (fun _ => True) Q₂
    rw [prob_true, one_mul] at this
    rw [← this]
    exact prob_congr V p₀ (fun f => by simpa using hQ₂ f)
  rw [h12, h1, h2]

lemma prob_biAll_of_pairwiseDisjoint {ι : Type*} [DecidableEq ι]
    (V : Finset α) (p₀ : ℝ) (I : Finset ι)
    (S : ι → Finset α) (P : ι → (V → Bool) → Prop)
    (hsub : ∀ i ∈ I, S i ⊆ V)
    (hdep : ∀ i ∈ I, DependsOn V (S i) (P i))
    (hdisj : (I : Set ι).PairwiseDisjoint S) :
    prob V p₀ (fun f => ∀ i ∈ I, P i f) = ∏ i ∈ I, prob V p₀ (P i) := by
  induction I using Finset.induction_on with
  | empty =>
    simp [prob_true]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_sub : S a ⊆ V := hsub a (Finset.mem_insert_self a s)
    have hs_sub : ∀ i ∈ s, S i ⊆ V := fun i hi => hsub i (Finset.mem_insert_of_mem hi)
    have ha_dep : DependsOn V (S a) (P a) := hdep a (Finset.mem_insert_self a s)
    have hs_dep : ∀ i ∈ s, DependsOn V (S i) (P i) := fun i hi => hdep i (Finset.mem_insert_of_mem hi)
    have hdisj_as : Disjoint (S a) (s.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdisj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    have hs_union_sub : s.biUnion S ⊆ V := Finset.biUnion_subset.2 hs_sub
    have heq : prob V p₀ (fun f => ∀ i ∈ insert a s, P i f) =
        prob V p₀ (fun f => P a f ∧ ∀ i ∈ s, P i f) :=
      prob_congr V p₀ (fun f => by simp)
    rw [heq, prob_and_of_disjoint V (S a) (s.biUnion S) ha_sub hs_union_sub hdisj_as p₀
      ha_dep (dependsOn_biAll hs_dep)]
    rw [ih hs_sub hs_dep (hdisj.subset (Finset.subset_insert a s))]

lemma prob_single_pattern (V S : Finset α) (hS : S ⊆ V) (p₀ : ℝ) (g : S → Bool) :
    prob V p₀ (fun f => ∀ x : S, f ⟨x.1, hS x.2⟩ = g x) = weight S p₀ g := by
  have h1 : prob V p₀ (fun f => ∀ x : S, f ⟨x.1, hS x.2⟩ = g x) =
      prob V p₀ (fun f => (piSplitEquiv V S hS f).1 = g ∧ True) := by
    apply prob_congr
    intro f
    simp [piSplitEquiv, funext_iff]
  rw [h1, prob_split V S hS p₀ (fun f₁ => f₁ = g) (fun _ => True), prob_true, mul_one]
  unfold prob
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hbg
    simp [hbg]
  · intro hg
    exact absurd (Finset.mem_univ g) hg

end BernoulliProb

/- ### Part 2: Symmetric Lovász Local Lemma -/

section LLL

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-- Symmetric Lovász Local Lemma on a finite Bernoulli product space (condition `4 * p * D ≤ 1`). -/
theorem symmetric_lll (V : Finset α) {p₀ : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : p₀ ≤ 1)
    (F : Finset ι) (W : ι → Finset α) (E : ι → (V → Bool) → Prop)
    (hWsub : ∀ i ∈ F, W i ⊆ V)
    (hEdep : ∀ i ∈ F, DependsOn V (W i) (E i))
    {p : ℝ} (hp_nonneg : 0 ≤ p)
    {D : ℕ} (hD : 1 ≤ D)
    (hcond : 4 * p * (D : ℝ) ≤ 1)
    (hprob : ∀ i ∈ F, prob V p₀ (E i) ≤ p)
    (hdeg : ∀ i ∈ F, (F.filter (fun j => ¬ Disjoint (W i) (W j))).card ≤ D) :
    0 < prob V p₀ (fun f => ∀ i ∈ F, ¬ E i f) := by
  have hp_half : 2 * p ≤ 1 / 2 := by
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    nlinarith
  have h1_sub_2p_pos : 0 < 1 - 2 * p := by linarith
  -- Strong induction on n = S.card
  have main : ∀ n : ℕ, ∀ S : Finset ι, S ⊆ F → S.card ≤ n →
      (0 < prob V p₀ (fun f => ∀ j ∈ S, ¬ E j f)) ∧
      (∀ i ∈ F, i ∉ S →
        prob V p₀ (fun f => E i f ∧ ∀ j ∈ S, ¬ E j f) ≤
          2 * p * prob V p₀ (fun f => ∀ j ∈ S, ¬ E j f)) := by
    intro n
    induction n with
    | zero =>
      intro S _ hScard
      have hS : S = ∅ := Finset.card_eq_zero.1 (Nat.eq_zero_of_le_zero hScard)
      subst hS
      refine ⟨by simp [prob_true], ?_⟩
      intro i hi _
      have h1 : prob V p₀ (fun f => E i f ∧ ∀ j ∈ (∅ : Finset ι), ¬ E j f) = prob V p₀ (E i) :=
        prob_congr V p₀ (fun f => by simp)
      have h2 : prob V p₀ (fun f => ∀ j ∈ (∅ : Finset ι), ¬ E j f) = 1 := by
        simp [prob_true]
      rw [h1, h2, mul_one]
      linarith [hprob i hi]
    | succ n ih =>
      intro S hSF hScard
      by_cases hSlen : S.card ≤ n
      · exact ih S hSF hSlen
      have hS_eq : S.card = n + 1 := by omega
      -- Part (a): prob (∀ j ∈ S, ¬ E j) > 0
      have hpos : 0 < prob V p₀ (fun f => ∀ j ∈ S, ¬ E j f) := by
        have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
        rcases hSne with ⟨a, ha⟩
        let S' := S.erase a
        have hS'sub : S' ⊆ F := (Finset.erase_subset a S).trans hSF
        have hS'card : S'.card ≤ n := by
          rw [Finset.card_erase_of_mem ha]
          omega
        have hih := ih S' hS'sub hS'card
        have haS' : a ∉ S' := Finset.notMem_erase a S
        have hstep := hih.2 a (hSF ha) haS'
        have hsplit : prob V p₀ (fun f => ∀ j ∈ S, ¬ E j f) =
            prob V p₀ (fun f => ∀ j ∈ S', ¬ E j f) -
            prob V p₀ (fun f => E a f ∧ ∀ j ∈ S', ¬ E j f) := by
          have h1 : prob V p₀ (fun f => ∀ j ∈ S, ¬ E j f) =
              prob V p₀ (fun f => (∀ j ∈ S', ¬ E j f) ∧ ¬ E a f) := by
            apply prob_congr
            intro f
            rw [← Finset.insert_erase ha]
            simp only [Finset.mem_insert, forall_eq_or_imp, S']
            tauto
          rw [h1, prob_and_not]
          congr 1
          exact prob_congr V p₀ (fun f => by tauto)
        rw [hsplit]
        nlinarith [hih.1]
      refine ⟨hpos, ?_⟩
      -- Part (b): conditional bound for i ∈ F \ S
      intro i hi hiS
      let S₁ := S.filter (fun j => ¬ Disjoint (W i) (W j))
      let S₂ := S.filter (fun j => Disjoint (W i) (W j))
      have hS₁₂ : S₁ ∪ S₂ = S := by
        ext x
        simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter]
        tauto
      have hSdisj : Disjoint S₁ S₂ := Finset.disjoint_filter.2 (fun _ _ h1 h2 => h1 h2)
      have hS₁_card : S₁.card ≤ D := by
        have hsub : S₁ ⊆ F.filter (fun j => ¬ Disjoint (W i) (W j)) :=
          Finset.filter_subset_filter _ hSF
        exact (Finset.card_le_card hsub).trans (hdeg i hi)
      -- Independence of E i from S₂
      have hS₂_sub_V : S₂.biUnion W ⊆ V :=
        Finset.biUnion_subset.2 (fun j hj => hWsub j (hSF (Finset.mem_filter.1 hj).1))
      have hdisj_i_S₂ : Disjoint (W i) (S₂.biUnion W) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact (Finset.mem_filter.1 hj).2
      have hdep_S₂ : DependsOn V (S₂.biUnion W) (fun f => ∀ j ∈ S₂, ¬ E j f) :=
        dependsOn_biAll (fun j hj => dependsOn_not (hEdep j (hSF (Finset.mem_filter.1 hj).1)))
      have hindep : prob V p₀ (fun f => E i f ∧ ∀ j ∈ S₂, ¬ E j f) =
          prob V p₀ (E i) * prob V p₀ (fun f => ∀ j ∈ S₂, ¬ E j f) :=
        prob_and_of_disjoint V (W i) (S₂.biUnion W) (hWsub i hi) hS₂_sub_V hdisj_i_S₂ p₀
          (hEdep i hi) hdep_S₂
      have hnum : prob V p₀ (fun f => E i f ∧ ∀ j ∈ S, ¬ E j f) ≤
          p * prob V p₀ (fun f => ∀ j ∈ S₂, ¬ E j f) := by
        have hle : prob V p₀ (fun f => E i f ∧ ∀ j ∈ S, ¬ E j f) ≤
            prob V p₀ (fun f => E i f ∧ ∀ j ∈ S₂, ¬ E j f) :=
          prob_mono V hp₀ hp₁ (fun f ⟨h1, h2⟩ => ⟨h1, fun j hj => h2 j (Finset.mem_filter.1 hj).1⟩)
        rw [hindep] at hle
        have hnn : 0 ≤ prob V p₀ (fun f => ∀ j ∈ S₂, ¬ E j f) := prob_nonneg V hp₀ hp₁ _
        exact hle.trans (mul_le_mul_of_nonneg_right (hprob i hi) hnn)
      -- Lower bound prob(S) ≥ (1 - 2p)^|S₁| * prob(S₂)
      have hdenom : (1 - 2 * p) ^ S₁.card * prob V p₀ (fun f => ∀ j ∈ S₂, ¬ E j f) ≤
          prob V p₀ (fun f => ∀ j ∈ S, ¬ E j f) := by
        suffices hT : ∀ T : Finset ι, T ⊆ S₁ →
            (1 - 2 * p) ^ T.card * prob V p₀ (fun f => ∀ j ∈ S₂, ¬ E j f) ≤
              prob V p₀ (fun f => ∀ j ∈ S₂ ∪ T, ¬ E j f) by
          have := hT S₁ Finset.Subset.rfl
          have heq : S₂ ∪ S₁ = S := by rw [Finset.union_comm, hS₁₂]
          rwa [heq] at this
        intro T
        induction T using Finset.induction_on with
        | empty =>
          intro _
          simp
        | @insert u T' hu ihT =>
          intro hTsub
          have hT'sub : T' ⊆ S₁ := (Finset.subset_insert u T').trans hTsub
          have huS₁ : u ∈ S₁ := hTsub (Finset.mem_insert_self u T')
          have huS : u ∈ S := (Finset.mem_filter.1 huS₁).1
          have huS₂ : u ∉ S₂ := Finset.disjoint_left.1 hSdisj huS₁
          have hu_not_mem : u ∉ S₂ ∪ T' := by
            simp [huS₂, hu]
          have hsub_S : S₂ ∪ T' ⊆ S := by
            intro x hx
            rcases Finset.mem_union.1 hx with h | h
            · exact (Finset.mem_filter.1 h).1
            · exact (Finset.mem_filter.1 (hT'sub h)).1
          have hssub : S₂ ∪ T' ⊂ S :=
            Finset.ssubset_iff_subset_ne.2 ⟨hsub_S, fun h => hu_not_mem (h.symm ▸ huS)⟩
          have hcard_lt : (S₂ ∪ T').card ≤ n := by
            have := Finset.card_lt_card hssub
            omega
          have hstep := (ih (S₂ ∪ T') (hsub_S.trans hSF) hcard_lt).2 u (hSF huS) hu_not_mem
          have hsplit : prob V p₀ (fun f => ∀ j ∈ S₂ ∪ insert u T', ¬ E j f) =
              prob V p₀ (fun f => ∀ j ∈ S₂ ∪ T', ¬ E j f) -
              prob V p₀ (fun f => E u f ∧ ∀ j ∈ S₂ ∪ T', ¬ E j f) := by
            have h1 : prob V p₀ (fun f => ∀ j ∈ S₂ ∪ insert u T', ¬ E j f) =
                prob V p₀ (fun f => (∀ j ∈ S₂ ∪ T', ¬ E j f) ∧ ¬ E u f) := by
              apply prob_congr
              intro f
              rw [Finset.union_insert]
              simp only [Finset.mem_insert, forall_eq_or_imp]
              tauto
            rw [h1, prob_and_not]
            congr 1
            exact prob_congr V p₀ (fun f => by tauto)
          rw [Finset.card_insert_of_notMem hu, pow_succ', hsplit]
          have hihT := ihT hT'sub
          nlinarith
      -- Bernoulli's inequality: (1 - 2p)^|S₁| ≥ 1 - 2p * |S₁| ≥ 1/2
      have hbern : (1 / 2 : ℝ) ≤ (1 - 2 * p) ^ S₁.card := by
        have h1 : 1 + (S₁.card : ℝ) * (-(2 * p)) ≤ (1 + -(2 * p)) ^ S₁.card :=
          one_add_mul_le_pow (by linarith) S₁.card
        rw [← sub_eq_add_neg] at h1
        have h2 : (S₁.card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hS₁_card
        have h3 : 2 * p * (S₁.card : ℝ) ≤ 1 / 2 := by nlinarith
        linarith
      have hnn : 0 ≤ prob V p₀ (fun f => ∀ j ∈ S₂, ¬ E j f) := prob_nonneg V hp₀ hp₁ _
      have hhalf : (1 / 2 : ℝ) * prob V p₀ (fun f => ∀ j ∈ S₂, ¬ E j f) ≤
          prob V p₀ (fun f => ∀ j ∈ S, ¬ E j f) :=
        (mul_le_mul_of_nonneg_right hbern hnn).trans hdenom
      nlinarith
  exact (main F.card F Finset.Subset.rfl le_rfl).1

end LLL

/- ### Part 3: Grid Geometry, Red/Blue Coloring, and Discretized APs -/

abbrev Grid := ℤ × ℤ

noncomputable def center (x : Grid) : ℂ :=
  ⟨(x.1 : ℝ) / 4 + 1 / 8, (x.2 : ℝ) / 4 + 1 / 8⟩

def inBox (x : Grid) (z : ℂ) : Prop :=
  |z.re - (center x).re| ≤ 1 / 3 ∧ |z.im - (center x).im| ≤ 1 / 3

def nbr (x : Grid) : Finset Grid :=
  Finset.Icc (x.1 - 6) (x.1 + 6) ×ˢ Finset.Icc (x.2 - 6) (x.2 + 6)

lemma mem_nbr {x y : Grid} :
    y ∈ nbr x ↔ (x.1 - 6 ≤ y.1 ∧ y.1 ≤ x.1 + 6) ∧ (x.2 - 6 ≤ y.2 ∧ y.2 ≤ x.2 + 6) := by
  simp [nbr, Finset.mem_product, Finset.mem_Icc]

lemma self_mem_nbr (x : Grid) : x ∈ nbr x := by
  rw [mem_nbr]
  omega

lemma card_nbr (x : Grid) : (nbr x).card = 169 := by
  simp only [nbr, Finset.card_product, Int.card_Icc]
  have h1 : x.1 + 6 + 1 - (x.1 - 6) = 13 := by omega
  have h2 : x.2 + 6 + 1 - (x.2 - 6) = 13 := by omega
  rw [h1, h2]
  rfl

lemma disjoint_nbr_of_far {x y : Grid}
    (h : 13 ≤ |x.1 - y.1| ∨ 13 ≤ |x.2 - y.2|) : Disjoint (nbr x) (nbr y) := by
  rw [Finset.disjoint_left]
  intro z hzx hzy
  rw [mem_nbr] at hzx hzy
  rcases h with h1 | h2
  · rcases le_or_gt 0 (x.1 - y.1) with hpos | hneg
    · rw [abs_of_nonneg hpos] at h1; omega
    · rw [abs_of_neg hneg] at h1; omega
  · rcases le_or_gt 0 (x.2 - y.2) with hpos | hneg
    · rw [abs_of_nonneg hpos] at h2; omega
    · rw [abs_of_neg hneg] at h2; omega

def isSelected (a : Grid → Bool) (x : Grid) : Prop :=
  a x = true ∧ ∀ y ∈ nbr x, y ≠ x → a y = false

def redSet (a : Grid → Bool) : Set ℂ :=
  {z : ℂ | ∃ x : Grid, isSelected a x ∧ inBox x z}

lemma dist_sq_eq_re_im (z w : ℂ) :
    dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

lemma redSet_pairwise_dist_ne_one (a : Grid → Bool) :
    (redSet a).Pairwise (fun z w => dist z w ≠ 1) := by
  rintro z ⟨x, hx, hzx⟩ w ⟨y, hy, hwy⟩ _
  intro hdist
  have hsq : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = 1 := by
    rw [← dist_sq_eq_re_im, hdist, one_pow]
  by_cases hxy : x = y
  · subst hxy
    have hre : |z.re - w.re| ≤ 2 / 3 := by
      have h1 := hzx.1
      have h2 := hwy.1
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    have him : |z.im - w.im| ≤ 2 / 3 := by
      have h1 := hzx.2
      have h2 := hwy.2
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    have hre2 : (z.re - w.re) ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (z.re - w.re)]
    have him2 : (z.im - w.im) ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (z.im - w.im)]
    linarith
  · have hnotnbr : y ∉ nbr x := by
      intro hmem
      have hfalse := hx.2 y hmem (Ne.symm hxy)
      rw [hy.1] at hfalse
      exact Bool.noConfusion hfalse
    rw [mem_nbr] at hnotnbr
    have hfar : (7 : ℤ) ≤ |x.1 - y.1| ∨ (7 : ℤ) ≤ |x.2 - y.2| := by
      by_contra h
      push Not at h
      apply hnotnbr
      rcases h with ⟨h1, h2⟩
      rw [abs_lt] at h1 h2
      omega
    rcases hfar with hfar1 | hfar2
    · have hfarR : (7 : ℝ) ≤ |(x.1 : ℝ) - (y.1 : ℝ)| := by
        have : (7 : ℝ) ≤ ((|x.1 - y.1| : ℤ) : ℝ) := by exact_mod_cast hfar1
        simpa [Int.cast_abs, Int.cast_sub] using this
      have hre : (13 / 12 : ℝ) ≤ |z.re - w.re| := by
        have h1 := hzx.1
        have h2 := hwy.1
        simp only [center] at h1 h2
        rw [abs_le] at h1 h2
        rcases le_or_gt 0 ((x.1 : ℝ) - (y.1 : ℝ)) with hpos | hneg
        · rw [abs_of_nonneg hpos] at hfarR
          have : 13 / 12 ≤ z.re - w.re := by linarith
          exact this.trans (le_abs_self _)
        · rw [abs_of_neg hneg] at hfarR
          have : 13 / 12 ≤ w.re - z.re := by linarith
          exact this.trans (by rw [abs_sub_comm]; exact le_abs_self _)
      have hre2 : (13 / 12 : ℝ) ^ 2 ≤ (z.re - w.re) ^ 2 := by
        rw [← sq_abs (z.re - w.re)]
        nlinarith [abs_nonneg (z.re - w.re)]
      nlinarith [sq_nonneg (z.im - w.im)]
    · have hfarR : (7 : ℝ) ≤ |(x.2 : ℝ) - (y.2 : ℝ)| := by
        have : (7 : ℝ) ≤ ((|x.2 - y.2| : ℤ) : ℝ) := by exact_mod_cast hfar2
        simpa [Int.cast_abs, Int.cast_sub] using this
      have him : (13 / 12 : ℝ) ≤ |z.im - w.im| := by
        have h1 := hzx.2
        have h2 := hwy.2
        simp only [center] at h1 h2
        rw [abs_le] at h1 h2
        rcases le_or_gt 0 ((x.2 : ℝ) - (y.2 : ℝ)) with hpos | hneg
        · rw [abs_of_nonneg hpos] at hfarR
          have : 13 / 12 ≤ z.im - w.im := by linarith
          exact this.trans (le_abs_self _)
        · rw [abs_of_neg hneg] at hfarR
          have : 13 / 12 ≤ w.im - z.im := by linarith
          exact this.trans (by rw [abs_sub_comm]; exact le_abs_self _)
      have him2 : (13 / 12 : ℝ) ^ 2 ≤ (z.im - w.im) ^ 2 := by
        rw [← sq_abs (z.im - w.im)]
        nlinarith [abs_nonneg (z.im - w.im)]
      nlinarith [sq_nonneg (z.re - w.re)]

/-- Parameters of a discretized `(10 * m)`-AP of step ~1. -/
structure APParam (m : ℕ) where
  a₁ : ℤ
  a₂ : ℤ
  b₁ : ℤ
  b₂ : ℤ
  hb₁ : |b₁| ≤ 100 * (m : ℤ)
  hb₂ : |b₂| ≤ 100 * (m : ℤ)
  hdir : 70 * (m : ℤ) ≤ |b₁| ∨ 70 * (m : ℤ) ≤ |b₂|
  deriving DecidableEq

noncomputable def apPtRe (m : ℕ) (γ : APParam m) (j : Fin m) : ℝ :=
  (γ.a₁ : ℝ) / 10 + (j.1 : ℝ) * (γ.b₁ : ℝ) / (10 * (m : ℝ))

noncomputable def apPtIm (m : ℕ) (γ : APParam m) (j : Fin m) : ℝ :=
  (γ.a₂ : ℝ) / 10 + (j.1 : ℝ) * (γ.b₂ : ℝ) / (10 * (m : ℝ))

noncomputable def apGridPt (m : ℕ) (γ : APParam m) (j : Fin m) : Grid :=
  (⌊4 * apPtRe m γ j⌋, ⌊4 * apPtIm m γ j⌋)

noncomputable def apSupport (m : ℕ) (γ : APParam m) : Finset Grid :=
  Finset.univ.biUnion (fun j : Fin m => nbr (apGridPt m γ j))

lemma apGridPt_pairwiseDisjoint_nbr {m : ℕ} (hm : 1 ≤ m) (γ : APParam m) :
    (Set.univ : Set (Fin m)).PairwiseDisjoint (fun j => nbr (apGridPt m γ j)) := by
  intro j₁ _ j₂ _ hne
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hjdiff : (1 : ℝ) ≤ |(j₁.1 : ℝ) - (j₂.1 : ℝ)| := by
    have : (j₁.1 : ℤ) ≠ (j₂.1 : ℤ) := by
      intro h
      apply hne
      ext
      exact_mod_cast h
    have h1 : (1 : ℤ) ≤ |(j₁.1 : ℤ) - (j₂.1 : ℤ)| := by rw [le_abs]; omega
    have h2 : (1 : ℝ) ≤ ((|(j₁.1 : ℤ) - (j₂.1 : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [Int.cast_abs, Int.cast_sub] using h2
  apply disjoint_nbr_of_far
  rcases γ.hdir with hdir1 | hdir2
  · left
    have hb : (70 : ℝ) * (m : ℝ) ≤ |(γ.b₁ : ℝ)| := by
      have : ((70 * (m : ℤ) : ℤ) : ℝ) ≤ ((|γ.b₁| : ℤ) : ℝ) := by exact_mod_cast hdir1
      simpa [Int.cast_abs] using this
    have hdiff : (28 : ℝ) ≤ |4 * apPtRe m γ j₁ - 4 * apPtRe m γ j₂| := by
      have heq : 4 * apPtRe m γ j₁ - 4 * apPtRe m γ j₂ =
          4 * (((j₁.1 : ℝ) - (j₂.1 : ℝ)) * (γ.b₁ : ℝ) / (10 * (m : ℝ))) := by
        unfold apPtRe; ring
      rw [heq, abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_pos (by positivity : (0 : ℝ) < 10 * (m : ℝ))]
      rw [← mul_div_assoc, le_div_iff₀ (by positivity : (0 : ℝ) < 10 * (m : ℝ))]
      have hmul : (70 : ℝ) * (m : ℝ) ≤ |(j₁.1 : ℝ) - (j₂.1 : ℝ)| * |(γ.b₁ : ℝ)| :=
        le_trans (by linarith) (mul_le_mul hjdiff hb (by positivity) (by positivity))
      linarith
    have hf1 := Int.floor_le (4 * apPtRe m γ j₁)
    have hf2 := Int.lt_floor_add_one (4 * apPtRe m γ j₁)
    have hg1 := Int.floor_le (4 * apPtRe m γ j₂)
    have hg2 := Int.lt_floor_add_one (4 * apPtRe m γ j₂)
    have hR : (13 : ℝ) ≤ |(⌊4 * apPtRe m γ j₁⌋ : ℝ) - (⌊4 * apPtRe m γ j₂⌋ : ℝ)| := by
      rcases le_or_gt 0 (4 * apPtRe m γ j₁ - 4 * apPtRe m γ j₂) with hpos | hneg
      · rw [abs_of_nonneg hpos] at hdiff
        have : 13 ≤ (⌊4 * apPtRe m γ j₁⌋ : ℝ) - (⌊4 * apPtRe m γ j₂⌋ : ℝ) := by linarith
        exact this.trans (le_abs_self _)
      · rw [abs_of_neg hneg] at hdiff
        have : 13 ≤ (⌊4 * apPtRe m γ j₂⌋ : ℝ) - (⌊4 * apPtRe m γ j₁⌋ : ℝ) := by linarith
        exact this.trans (by rw [abs_sub_comm]; exact le_abs_self _)
    have hcast : ((13 : ℤ) : ℝ) ≤ ((|⌊4 * apPtRe m γ j₁⌋ - ⌊4 * apPtRe m γ j₂⌋| : ℤ) : ℝ) := by
      simpa [Int.cast_abs, Int.cast_sub] using hR
    exact_mod_cast hcast
  · right
    have hb : (70 : ℝ) * (m : ℝ) ≤ |(γ.b₂ : ℝ)| := by
      have : ((70 * (m : ℤ) : ℤ) : ℝ) ≤ ((|γ.b₂| : ℤ) : ℝ) := by exact_mod_cast hdir2
      simpa [Int.cast_abs] using this
    have hdiff : (28 : ℝ) ≤ |4 * apPtIm m γ j₁ - 4 * apPtIm m γ j₂| := by
      have heq : 4 * apPtIm m γ j₁ - 4 * apPtIm m γ j₂ =
          4 * (((j₁.1 : ℝ) - (j₂.1 : ℝ)) * (γ.b₂ : ℝ) / (10 * (m : ℝ))) := by
        unfold apPtIm; ring
      rw [heq, abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_pos (by positivity : (0 : ℝ) < 10 * (m : ℝ))]
      rw [← mul_div_assoc, le_div_iff₀ (by positivity : (0 : ℝ) < 10 * (m : ℝ))]
      have hmul : (70 : ℝ) * (m : ℝ) ≤ |(j₁.1 : ℝ) - (j₂.1 : ℝ)| * |(γ.b₂ : ℝ)| :=
        le_trans (by linarith) (mul_le_mul hjdiff hb (by positivity) (by positivity))
      linarith
    have hf1 := Int.floor_le (4 * apPtIm m γ j₁)
    have hf2 := Int.lt_floor_add_one (4 * apPtIm m γ j₁)
    have hg1 := Int.floor_le (4 * apPtIm m γ j₂)
    have hg2 := Int.lt_floor_add_one (4 * apPtIm m γ j₂)
    have hR : (13 : ℝ) ≤ |(⌊4 * apPtIm m γ j₁⌋ : ℝ) - (⌊4 * apPtIm m γ j₂⌋ : ℝ)| := by
      rcases le_or_gt 0 (4 * apPtIm m γ j₁ - 4 * apPtIm m γ j₂) with hpos | hneg
      · rw [abs_of_nonneg hpos] at hdiff
        have : 13 ≤ (⌊4 * apPtIm m γ j₁⌋ : ℝ) - (⌊4 * apPtIm m γ j₂⌋ : ℝ) := by linarith
        exact this.trans (le_abs_self _)
      · rw [abs_of_neg hneg] at hdiff
        have : 13 ≤ (⌊4 * apPtIm m γ j₂⌋ : ℝ) - (⌊4 * apPtIm m γ j₁⌋ : ℝ) := by linarith
        exact this.trans (by rw [abs_sub_comm]; exact le_abs_self _)
    have hcast : ((13 : ℤ) : ℝ) ≤ ((|⌊4 * apPtIm m γ j₁⌋ - ⌊4 * apPtIm m γ j₂⌋| : ℤ) : ℝ) := by
      simpa [Int.cast_abs, Int.cast_sub] using hR
    exact_mod_cast hcast

lemma apSupport_coord_bound {m : ℕ} (hm : 1 ≤ m) (γ : APParam m) {w : Grid}
    (hw : w ∈ apSupport m γ) :
    |(w.1 : ℝ) - 4 * (γ.a₁ : ℝ) / 10| ≤ 40 * (m : ℝ) + 7 ∧
    |(w.2 : ℝ) - 4 * (γ.a₂ : ℝ) / 10| ≤ 40 * (m : ℝ) + 7 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  rcases Finset.mem_biUnion.1 hw with ⟨j, _, hwj⟩
  rw [mem_nbr] at hwj
  have hjle : (j.1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt j.2
  have hjnn : (0 : ℝ) ≤ (j.1 : ℝ) := by positivity
  have hb₁ : |(γ.b₁ : ℝ)| ≤ 100 * (m : ℝ) := by
    have : ((|γ.b₁| : ℤ) : ℝ) ≤ ((100 * (m : ℤ) : ℤ) : ℝ) := by exact_mod_cast γ.hb₁
    simpa [Int.cast_abs] using this
  have hb₂ : |(γ.b₂ : ℝ)| ≤ 100 * (m : ℝ) := by
    have : ((|γ.b₂| : ℤ) : ℝ) ≤ ((100 * (m : ℤ) : ℤ) : ℝ) := by exact_mod_cast γ.hb₂
    simpa [Int.cast_abs] using this
  constructor
  · have hterm : |4 * ((j.1 : ℝ) * (γ.b₁ : ℝ) / (10 * (m : ℝ)))| ≤ 40 * (m : ℝ) := by
      rw [abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_nonneg hjnn, abs_of_pos (by positivity : (0 : ℝ) < 10 * (m : ℝ))]
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 10 * (m : ℝ))]
      have : (j.1 : ℝ) * |(γ.b₁ : ℝ)| ≤ (m : ℝ) * (100 * (m : ℝ)) :=
        mul_le_mul hjle hb₁ (abs_nonneg _) (by positivity)
      linarith
    have hfl1 := Int.floor_le (4 * apPtRe m γ j)
    have hfl2 := Int.lt_floor_add_one (4 * apPtRe m γ j)
    have hw1l : ((⌊4 * apPtRe m γ j⌋ : ℤ) : ℝ) - 6 ≤ (w.1 : ℝ) := by
      have : ⌊4 * apPtRe m γ j⌋ - 6 ≤ w.1 := hwj.1.1
      exact_mod_cast this
    have hw1u : (w.1 : ℝ) ≤ ((⌊4 * apPtRe m γ j⌋ : ℤ) : ℝ) + 6 := by
      have : w.1 ≤ ⌊4 * apPtRe m γ j⌋ + 6 := hwj.1.2
      exact_mod_cast this
    have hpt : 4 * apPtRe m γ j = 4 * (γ.a₁ : ℝ) / 10 + 4 * ((j.1 : ℝ) * (γ.b₁ : ℝ) / (10 * (m : ℝ))) := by
      unfold apPtRe; ring
    rw [abs_le] at hterm ⊢
    constructor <;> linarith
  · have hterm : |4 * ((j.1 : ℝ) * (γ.b₂ : ℝ) / (10 * (m : ℝ)))| ≤ 40 * (m : ℝ) := by
      rw [abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_nonneg hjnn, abs_of_pos (by positivity : (0 : ℝ) < 10 * (m : ℝ))]
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 10 * (m : ℝ))]
      have : (j.1 : ℝ) * |(γ.b₂ : ℝ)| ≤ (m : ℝ) * (100 * (m : ℝ)) :=
        mul_le_mul hjle hb₂ (abs_nonneg _) (by positivity)
      linarith
    have hfl1 := Int.floor_le (4 * apPtIm m γ j)
    have hfl2 := Int.lt_floor_add_one (4 * apPtIm m γ j)
    have hw2l : ((⌊4 * apPtIm m γ j⌋ : ℤ) : ℝ) - 6 ≤ (w.2 : ℝ) := by
      have : ⌊4 * apPtIm m γ j⌋ - 6 ≤ w.2 := hwj.2.1
      exact_mod_cast this
    have hw2u : (w.2 : ℝ) ≤ ((⌊4 * apPtIm m γ j⌋ : ℤ) : ℝ) + 6 := by
      have : w.2 ≤ ⌊4 * apPtIm m γ j⌋ + 6 := hwj.2.2
      exact_mod_cast this
    have hpt : 4 * apPtIm m γ j = 4 * (γ.a₂ : ℝ) / 10 + 4 * ((j.1 : ℝ) * (γ.b₂ : ℝ) / (10 * (m : ℝ))) := by
      unfold apPtIm; ring
    rw [abs_le] at hterm ⊢
    constructor <;> linarith

/-- Dependency degree bound: at most `10^12 * m^4` discretized APs share a grid support vertex. -/
lemma apSupport_deg_bound {m : ℕ} (hm : 1 ≤ m) (F : Finset (APParam m)) (γ : APParam m) :
    (F.filter (fun γ' => ¬ Disjoint (apSupport m γ) (apSupport m γ'))).card ≤ 10 ^ 12 * m ^ 4 := by
  let R : ℤ := 235 * (m : ℤ)
  let B : ℤ := 100 * (m : ℤ)
  let box : Finset (ℤ × ℤ × ℤ × ℤ) :=
    Finset.Icc (γ.a₁ - R) (γ.a₁ + R) ×ˢ
    Finset.Icc (γ.a₂ - R) (γ.a₂ + R) ×ˢ
    Finset.Icc (-B) B ×ˢ
    Finset.Icc (-B) B
  let embed : APParam m → ℤ × ℤ × ℤ × ℤ := fun γ' => (γ'.a₁, γ'.a₂, γ'.b₁, γ'.b₂)
  have hinj : Function.Injective embed := by
    intro x y h
    simp only [embed, Prod.mk.injEq] at h
    cases x; cases y
    simp_all
  have hsub : (F.filter (fun γ' => ¬ Disjoint (apSupport m γ) (apSupport m γ'))).image embed ⊆ box := by
    intro t ht
    rcases Finset.mem_image.1 ht with ⟨γ', hγ', rfl⟩
    have hnd : ¬ Disjoint (apSupport m γ) (apSupport m γ') := (Finset.mem_filter.1 hγ').2
    rw [Finset.not_disjoint_iff] at hnd
    rcases hnd with ⟨w, hw1, hw2⟩
    have hb1 := apSupport_coord_bound hm γ hw1
    have hb2 := apSupport_coord_bound hm γ' hw2
    have ha₁ : |(γ'.a₁ : ℝ) - (γ.a₁ : ℝ)| ≤ (R : ℝ) := by
      have h1 := hb1.1; have h2 := hb2.1
      rw [abs_le] at h1 h2 ⊢
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hR : (R : ℝ) = 235 * (m : ℝ) := by simp [R]
      rw [hR]
      constructor <;> linarith
    have ha₂ : |(γ'.a₂ : ℝ) - (γ.a₂ : ℝ)| ≤ (R : ℝ) := by
      have h1 := hb1.2; have h2 := hb2.2
      rw [abs_le] at h1 h2 ⊢
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hR : (R : ℝ) = 235 * (m : ℝ) := by simp [R]
      rw [hR]
      constructor <;> linarith
    have ha₁Z : |γ'.a₁ - γ.a₁| ≤ R := by
      have : ((|γ'.a₁ - γ.a₁| : ℤ) : ℝ) ≤ (R : ℝ) := by
        simpa [Int.cast_abs, Int.cast_sub] using ha₁
      exact_mod_cast this
    have ha₂Z : |γ'.a₂ - γ.a₂| ≤ R := by
      have : ((|γ'.a₂ - γ.a₂| : ℤ) : ℝ) ≤ (R : ℝ) := by
        simpa [Int.cast_abs, Int.cast_sub] using ha₂
      exact_mod_cast this
    have hb₁Z : |γ'.b₁| ≤ B := γ'.hb₁
    have hb₂Z : |γ'.b₂| ≤ B := γ'.hb₂
    rw [abs_le] at ha₁Z ha₂Z hb₁Z hb₂Z
    simp only [box, embed, Finset.mem_product, Finset.mem_Icc]
    omega
  have hcard1 : (F.filter (fun γ' => ¬ Disjoint (apSupport m γ) (apSupport m γ'))).card ≤ box.card := by
    rw [← Finset.card_image_of_injective _ hinj]
    exact Finset.card_le_card hsub
  have hbox : box.card ≤ 10 ^ 12 * m ^ 4 := by
    simp only [box, Finset.card_product, Int.card_Icc]
    have h1 : (γ.a₁ + R + 1 - (γ.a₁ - R)).toNat = 470 * m + 1 := by
      have : γ.a₁ + R + 1 - (γ.a₁ - R) = (470 * m + 1 : ℕ) := by push_cast [R]; ring
      rw [this, Int.toNat_natCast]
    have h2 : (γ.a₂ + R + 1 - (γ.a₂ - R)).toNat = 470 * m + 1 := by
      have : γ.a₂ + R + 1 - (γ.a₂ - R) = (470 * m + 1 : ℕ) := by push_cast [R]; ring
      rw [this, Int.toNat_natCast]
    have h3 : (B + 1 - -B).toNat = 200 * m + 1 := by
      have : B + 1 - -B = (200 * m + 1 : ℕ) := by push_cast [B]; ring
      rw [this, Int.toNat_natCast]
    rw [h1, h2, h3]
    have h471 : 470 * m + 1 ≤ 500 * m := by omega
    have h201 : 200 * m + 1 ≤ 300 * m := by omega
    calc (470 * m + 1) * ((470 * m + 1) * ((200 * m + 1) * (200 * m + 1)))
        ≤ (500 * m) * ((500 * m) * ((300 * m) * (300 * m))) := by gcongr
      _ = 22500000000 * m ^ 4 := by ring
      _ ≤ 10 ^ 12 * m ^ 4 := by gcongr; norm_num
  exact hcard1.trans hbox

/- ### Part 4: Finite Existence via LLL & Global Existence via Compactness -/

noncomputable def p0Val : ℝ := 1 / 169
noncomputable def qVal : ℝ := p0Val * (1 - p0Val) ^ 168

lemma qVal_pos : 0 < qVal := by
  unfold qVal p0Val
  positivity

lemma qVal_le_one : qVal ≤ 1 := by
  unfold qVal p0Val
  have h1 : (1 - (1 / 169 : ℝ)) ^ 168 ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  linarith

def isSelectedOn (V : Finset Grid) (f : V → Bool) (x : Grid) : Prop :=
  ∃ hx : x ∈ V, f ⟨x, hx⟩ = true ∧
    ∀ y ∈ nbr x, y ≠ x → ∃ hy : y ∈ V, f ⟨y, hy⟩ = false

lemma isSelectedOn_dependsOn (V : Finset Grid) (x : Grid) (hsub : nbr x ⊆ V) :
    DependsOn V (nbr x) (fun f => isSelectedOn V f x) := by
  intro f g hfg
  have hfx : f ⟨x, hsub (self_mem_nbr x)⟩ = g ⟨x, hsub (self_mem_nbr x)⟩ :=
    hfg ⟨x, hsub (self_mem_nbr x)⟩ (self_mem_nbr x)
  constructor
  · rintro ⟨hx, hft, hrest⟩
    refine ⟨hx, hfx ▸ hft, fun y hy hne => ?_⟩
    rcases hrest y hy hne with ⟨hyV, hfy⟩
    exact ⟨hyV, (hfg ⟨y, hyV⟩ hy) ▸ hfy⟩
  · rintro ⟨hx, hgt, hrest⟩
    refine ⟨hx, hfx.symm ▸ hgt, fun y hy hne => ?_⟩
    rcases hrest y hy hne with ⟨hyV, hgy⟩
    exact ⟨hyV, (hfg ⟨y, hyV⟩ hy).symm ▸ hgy⟩

lemma prob_isSelectedOn (V : Finset Grid) (x : Grid) (hsub : nbr x ⊆ V) :
    prob V p0Val (fun f => isSelectedOn V f x) = qVal := by
  let g : nbr x → Bool := fun y => decide (y.1 = x)
  have heq : prob V p0Val (fun f => isSelectedOn V f x) =
      prob V p0Val (fun f => ∀ y : nbr x, f ⟨y.1, hsub y.2⟩ = g y) := by
    apply prob_congr
    intro f
    constructor
    · rintro ⟨hx, hft, hrest⟩ y
      by_cases hyx : y.1 = x
      · have hyeq : (⟨y.1, hsub y.2⟩ : V) = ⟨x, hx⟩ := Subtype.ext hyx
        rw [hyeq]
        simpa [g, hyx] using hft
      · rcases hrest y.1 y.2 hyx with ⟨hyV, hfy⟩
        simpa [g, hyx] using hfy
    · intro hall
      refine ⟨hsub (self_mem_nbr x), ?_, fun y hy hne => ⟨hsub hy, ?_⟩⟩
      · simpa [g] using hall ⟨x, self_mem_nbr x⟩
      · simpa [g, hne] using hall ⟨y, hy⟩
  rw [heq, prob_single_pattern V (nbr x) hsub p0Val g]
  unfold weight qVal
  have hxmem : (⟨x, self_mem_nbr x⟩ : nbr x) ∈ (Finset.univ : Finset (nbr x)) := Finset.mem_univ _
  rw [← Finset.mul_prod_erase _ _ hxmem]
  have h1 : (if g ⟨x, self_mem_nbr x⟩ then p0Val else 1 - p0Val) = p0Val := by
    simp [g]
  rw [h1]
  congr 1
  have h2 : ∀ y ∈ Finset.univ.erase (⟨x, self_mem_nbr x⟩ : nbr x),
      (if g y then p0Val else 1 - p0Val) = 1 - p0Val := by
    intro y hy
    have hne : y.1 ≠ x := by
      intro heq
      apply (Finset.mem_erase.1 hy).1
      exact Subtype.ext heq
    simp [g, hne]
  rw [Finset.prod_congr rfl h2, Finset.prod_const]
  congr 1
  rw [Finset.card_erase_of_mem hxmem, Finset.card_univ, Fintype.card_coe, card_nbr]

lemma exists_good_m :
    ∃ m : ℕ, 1 ≤ m ∧ 4 * (1 - qVal) ^ m * ((10 ^ 12 * m ^ 4 : ℕ) : ℝ) ≤ 1 := by
  have h0 : 0 ≤ 1 - qVal := by linarith [qVal_le_one]
  have h1 : 1 - qVal < 1 := by linarith [qVal_pos]
  have htend : Tendsto (fun m : ℕ => (m : ℝ) ^ 4 * (1 - qVal) ^ m) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 4 h0 h1
  have hball := Metric.tendsto_atTop.1 htend (1 / (4 * (10 : ℝ) ^ 12)) (by positivity)
  rcases hball with ⟨N, hN⟩
  refine ⟨max N 1, le_max_right N 1, ?_⟩
  have h := hN (max N 1) (le_max_left N 1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
  have hlt : 4 * (10 : ℝ) ^ 12 * ((max N 1 : ℕ) : ℝ) ^ 4 * (1 - qVal) ^ max N 1 < 1 := by
    have : ((max N 1 : ℕ) : ℝ) ^ 4 * (1 - qVal) ^ max N 1 < 1 / (4 * (10 : ℝ) ^ 12) := h
    nlinarith
  have heq : 4 * (1 - qVal) ^ max N 1 * ((10 ^ 12 * (max N 1) ^ 4 : ℕ) : ℝ) =
      4 * (10 : ℝ) ^ 12 * ((max N 1 : ℕ) : ℝ) ^ 4 * (1 - qVal) ^ max N 1 := by
    push_cast
    ring
  linarith

lemma exists_global_coloring :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ a : Grid → Bool,
      ∀ γ : APParam m, ∃ j : Fin m, isSelected a (apGridPt m γ j) := by
  rcases exists_good_m with ⟨m, hm, hcond⟩
  refine ⟨m, hm, ?_⟩
  let G : APParam m → Set (Grid → Bool) :=
    fun γ => {a | ∃ j : Fin m, isSelected a (apGridPt m γ j)}
  have hclosed : ∀ γ : APParam m, IsClosed (G γ) := by
    intro γ
    have heq : G γ = ⋃ j : Fin m,
        ({a : Grid → Bool | a (apGridPt m γ j) = true} ∩
          ⋂ y ∈ (nbr (apGridPt m γ j)).erase (apGridPt m γ j),
            {a : Grid → Bool | a y = false}) := by
      ext a
      simp only [G, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
        Finset.mem_erase, isSelected]
      constructor
      · rintro ⟨j, h1, h2⟩
        exact ⟨j, h1, fun y ⟨hne, hmem⟩ => h2 y hmem hne⟩
      · rintro ⟨j, h1, h2⟩
        exact ⟨j, h1, fun y hmem hne => h2 y ⟨hne, hmem⟩⟩
    rw [heq]
    apply isClosed_iUnion_of_finite
    intro j
    apply IsClosed.inter
    · exact isClosed_eq (continuous_apply _) continuous_const
    · apply isClosed_biInter
      intro y _
      exact isClosed_eq (continuous_apply _) continuous_const
  have hfin : ∀ F : Finset (APParam m), (Set.univ ∩ ⋂ γ ∈ F, G γ).Nonempty := by
    intro F
    let V : Finset Grid := F.biUnion (apSupport m)
    let E : APParam m → (V → Bool) → Prop :=
      fun γ f => ∀ j ∈ (Finset.univ : Finset (Fin m)), ¬ isSelectedOn V f (apGridPt m γ j)
    have hWsub : ∀ γ ∈ F, apSupport m γ ⊆ V := fun γ hγ =>
      Finset.subset_biUnion_of_mem (apSupport m) hγ
    have hEdep : ∀ γ ∈ F, DependsOn V (apSupport m γ) (E γ) := by
      intro γ hγ
      unfold E apSupport
      apply dependsOn_biAll
      intro j _
      apply dependsOn_not
      apply isSelectedOn_dependsOn
      exact (Finset.subset_biUnion_of_mem (fun j => nbr (apGridPt m γ j)) (Finset.mem_univ j)).trans
        (hWsub γ hγ)
    have hprob : ∀ γ ∈ F, prob V p0Val (E γ) ≤ (1 - qVal) ^ m := by
      intro γ hγ
      have hsub_j : ∀ j ∈ (Finset.univ : Finset (Fin m)), nbr (apGridPt m γ j) ⊆ V := by
        intro j _
        exact (Finset.subset_biUnion_of_mem (fun j => nbr (apGridPt m γ j)) (Finset.mem_univ j)).trans
          (hWsub γ hγ)
      have hdep_j : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          DependsOn V (nbr (apGridPt m γ j)) (fun f => ¬ isSelectedOn V f (apGridPt m γ j)) :=
        fun j hj => dependsOn_not (isSelectedOn_dependsOn V _ (hsub_j j hj))
      have hdisj_j : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
          (fun j => nbr (apGridPt m γ j)) := by
        simpa using apGridPt_pairwiseDisjoint_nbr hm γ
      rw [prob_biAll_of_pairwiseDisjoint V p0Val Finset.univ
        (fun j => nbr (apGridPt m γ j))
        (fun j f => ¬ isSelectedOn V f (apGridPt m γ j)) hsub_j hdep_j hdisj_j]
      have hprod : ∏ j : Fin m, prob V p0Val (fun f => ¬ isSelectedOn V f (apGridPt m γ j)) =
          (1 - qVal) ^ m := by
        have hterm : ∀ j ∈ (Finset.univ : Finset (Fin m)),
            prob V p0Val (fun f => ¬ isSelectedOn V f (apGridPt m γ j)) = 1 - qVal := by
          intro j hj
          rw [prob_not, prob_isSelectedOn V (apGridPt m γ j) (hsub_j j hj)]
        rw [Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hprod]
    have hD1 : 1 ≤ 10 ^ 12 * m ^ 4 := by
      have : 1 ≤ m ^ 4 := one_le_pow₀ hm
      omega
    have hpos := symmetric_lll V (by unfold p0Val; norm_num) (by unfold p0Val; norm_num)
      F (apSupport m) E hWsub hEdep
      (pow_nonneg (by linarith [qVal_le_one]) m) hD1 hcond hprob
      (fun γ _ => apSupport_deg_bound hm F γ)
    rcases exists_of_prob_pos V p0Val hpos with ⟨f, hf⟩
    let a : Grid → Bool := fun x => if hx : x ∈ V then f ⟨x, hx⟩ else false
    refine ⟨a, Set.mem_univ _, ?_⟩
    simp only [Set.mem_iInter, G, Set.mem_ofPred_eq]
    intro γ hγ
    have hnotE := hf γ hγ
    simp only [E, Finset.mem_univ, forall_true_left, not_forall, not_not] at hnotE
    rcases hnotE with ⟨j, hxV, hft, hrest⟩
    refine ⟨j, ?_, ?_⟩
    · simp [a, hxV, hft]
    · intro y hy hne
      rcases hrest y hy hne with ⟨hyV, hfy⟩
      simp [a, hyV, hfy]
  rcases isCompact_univ.inter_iInter_nonempty G hclosed hfin with ⟨a, _, ha⟩
  simp only [Set.mem_iInter, G, Set.mem_ofPred_eq] at ha
  exact ⟨a, ha⟩

/- ### Part 5: Connecting Discretized APs to Arbitrary Unit-Step APs in `ℂ` -/

lemma norm_eq_one_imp_coord_ge {d : ℂ} (hd : ‖d‖ = 1) :
    (7 / 10 : ℝ) ≤ |d.re| ∨ (7 / 10 : ℝ) ≤ |d.im| := by
  have hsq : d.re ^ 2 + d.im ^ 2 = 1 := by
    have := Complex.sq_norm d
    rw [hd, one_pow, Complex.normSq_apply] at this
    linarith
  by_contra h
  push Not at h
  have h1 : d.re ^ 2 < (7 / 10 : ℝ) ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg d.re, h.1]
  have h2 : d.im ^ 2 < (7 / 10 : ℝ) ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg d.im, h.2]
  linarith

lemma ap_hits_redSet {m : ℕ} (hm : 1 ≤ m) {a : Grid → Bool}
    (ha : ∀ γ : APParam m, ∃ j : Fin m, isSelected a (apGridPt m γ j))
    (z d : ℂ) (hd : ‖d‖ = 1) :
    ∃ n : ℕ, n < 10 * m ∧ z + n • d ∈ redSet a := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hd_re_le : |d.re| ≤ 1 := by
    have := Complex.abs_re_le_norm d
    linarith
  have hd_im_le : |d.im| ≤ 1 := by
    have := Complex.abs_im_le_norm d
    linarith
  let a₁ : ℤ := ⌊10 * z.re⌋
  let a₂ : ℤ := ⌊10 * z.im⌋
  let b₁ : ℤ := ⌊100 * (m : ℝ) * d.re⌋
  let b₂ : ℤ := ⌊100 * (m : ℝ) * d.im⌋
  have hb₁ : |b₁| ≤ 100 * (m : ℤ) := by
    rw [abs_le] at hd_re_le ⊢
    constructor
    · have : ((-(100 * (m : ℤ)) : ℤ) : ℝ) ≤ 100 * (m : ℝ) * d.re := by
        push_cast; nlinarith
      exact Int.le_floor.2 this
    · have hfl := Int.floor_le (100 * (m : ℝ) * d.re)
      have : (b₁ : ℝ) ≤ ((100 * (m : ℤ) : ℤ) : ℝ) := by
        push_cast; nlinarith
      exact_mod_cast this
  have hb₂ : |b₂| ≤ 100 * (m : ℤ) := by
    rw [abs_le] at hd_im_le ⊢
    constructor
    · have : ((-(100 * (m : ℤ)) : ℤ) : ℝ) ≤ 100 * (m : ℝ) * d.im := by
        push_cast; nlinarith
      exact Int.le_floor.2 this
    · have hfl := Int.floor_le (100 * (m : ℝ) * d.im)
      have : (b₂ : ℝ) ≤ ((100 * (m : ℤ) : ℤ) : ℝ) := by
        push_cast; nlinarith
      exact_mod_cast this
  have hdir : 70 * (m : ℤ) ≤ |b₁| ∨ 70 * (m : ℤ) ≤ |b₂| := by
    rcases norm_eq_one_imp_coord_ge hd with hre | him
    · left
      rcases le_or_gt 0 d.re with hpos | hneg
      · rw [abs_of_nonneg hpos] at hre
        have hle : ((70 * (m : ℤ) : ℤ) : ℝ) ≤ 100 * (m : ℝ) * d.re := by push_cast; nlinarith
        have hge : 70 * (m : ℤ) ≤ b₁ := Int.le_floor.2 hle
        exact hge.trans (le_abs_self b₁)
      · rw [abs_of_neg hneg] at hre
        have hfl := Int.floor_le (100 * (m : ℝ) * d.re)
        have : (b₁ : ℝ) ≤ ((-(70 * (m : ℤ)) : ℤ) : ℝ) := by push_cast; nlinarith
        have hle : b₁ ≤ -(70 * (m : ℤ)) := by exact_mod_cast this
        have : 70 * (m : ℤ) ≤ -b₁ := by omega
        exact this.trans (neg_le_abs b₁)
    · right
      rcases le_or_gt 0 d.im with hpos | hneg
      · rw [abs_of_nonneg hpos] at him
        have hle : ((70 * (m : ℤ) : ℤ) : ℝ) ≤ 100 * (m : ℝ) * d.im := by push_cast; nlinarith
        have hge : 70 * (m : ℤ) ≤ b₂ := Int.le_floor.2 hle
        exact hge.trans (le_abs_self b₂)
      · rw [abs_of_neg hneg] at him
        have hfl := Int.floor_le (100 * (m : ℝ) * d.im)
        have : (b₂ : ℝ) ≤ ((-(70 * (m : ℤ)) : ℤ) : ℝ) := by push_cast; nlinarith
        have hle : b₂ ≤ -(70 * (m : ℤ)) := by exact_mod_cast this
        have : 70 * (m : ℤ) ≤ -b₂ := by omega
        exact this.trans (neg_le_abs b₂)
  let γ : APParam m := ⟨a₁, a₂, b₁, b₂, hb₁, hb₂, hdir⟩
  rcases ha γ with ⟨j, hsel⟩
  refine ⟨10 * j.1, by omega, apGridPt m γ j, hsel, ?_⟩
  have hjle : (j.1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt j.2
  have hjnn : (0 : ℝ) ≤ (j.1 : ℝ) := by positivity
  have hre_pt : (z + (10 * j.1) • d).re = z.re + (10 * (j.1 : ℝ)) * d.re := by
    rw [nsmul_eq_mul]
    simp [Complex.add_re, Complex.mul_re]
  have him_pt : (z + (10 * j.1) • d).im = z.im + (10 * (j.1 : ℝ)) * d.im := by
    rw [nsmul_eq_mul]
    simp [Complex.add_im, Complex.mul_im]
  constructor
  · rw [hre_pt]
    have ha1l := Int.floor_le (10 * z.re)
    have ha1u := Int.lt_floor_add_one (10 * z.re)
    have hb1l := Int.floor_le (100 * (m : ℝ) * d.re)
    have hb1u := Int.lt_floor_add_one (100 * (m : ℝ) * d.re)
    have hfl1 := Int.floor_le (4 * apPtRe m γ j)
    have hfl2 := Int.lt_floor_add_one (4 * apPtRe m γ j)
    have hdiff_z : 0 ≤ z.re - (a₁ : ℝ) / 10 ∧ z.re - (a₁ : ℝ) / 10 ≤ 1 / 10 := by
      constructor <;> linarith
    have hdiff_d : 0 ≤ d.re - (b₁ : ℝ) / (100 * (m : ℝ)) ∧
        d.re - (b₁ : ℝ) / (100 * (m : ℝ)) ≤ 1 / (100 * (m : ℝ)) := by
      constructor
      · rw [sub_nonneg, div_le_iff₀ (by positivity : (0 : ℝ) < 100 * (m : ℝ))]
        linarith
      · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ (by positivity : (0 : ℝ) < 100 * (m : ℝ))]
        linarith
    have hmul_d : 0 ≤ (10 * (j.1 : ℝ)) * (d.re - (b₁ : ℝ) / (100 * (m : ℝ))) ∧
        (10 * (j.1 : ℝ)) * (d.re - (b₁ : ℝ) / (100 * (m : ℝ))) ≤ 1 / 10 := by
      constructor
      · exact mul_nonneg (by positivity) hdiff_d.1
      · calc (10 * (j.1 : ℝ)) * (d.re - (b₁ : ℝ) / (100 * (m : ℝ)))
            ≤ (10 * (m : ℝ)) * (1 / (100 * (m : ℝ))) :=
              mul_le_mul (by linarith) hdiff_d.2 hdiff_d.1 (by positivity)
          _ = 1 / 10 := by field_simp; norm_num
    have hcomb : (z.re + 10 * (j.1 : ℝ) * d.re) - apPtRe m γ j =
        (z.re - (a₁ : ℝ) / 10) + (10 * (j.1 : ℝ)) * (d.re - (b₁ : ℝ) / (100 * (m : ℝ))) := by
      simp only [apPtRe, γ]
      field_simp
      ring
    simp only [center, apGridPt]
    rw [abs_le]
    constructor <;> linarith
  · rw [him_pt]
    have ha2l := Int.floor_le (10 * z.im)
    have ha2u := Int.lt_floor_add_one (10 * z.im)
    have hb2l := Int.floor_le (100 * (m : ℝ) * d.im)
    have hb2u := Int.lt_floor_add_one (100 * (m : ℝ) * d.im)
    have hfl1 := Int.floor_le (4 * apPtIm m γ j)
    have hfl2 := Int.lt_floor_add_one (4 * apPtIm m γ j)
    have hdiff_z : 0 ≤ z.im - (a₂ : ℝ) / 10 ∧ z.im - (a₂ : ℝ) / 10 ≤ 1 / 10 := by
      constructor <;> linarith
    have hdiff_d : 0 ≤ d.im - (b₂ : ℝ) / (100 * (m : ℝ)) ∧
        d.im - (b₂ : ℝ) / (100 * (m : ℝ)) ≤ 1 / (100 * (m : ℝ)) := by
      constructor
      · rw [sub_nonneg, div_le_iff₀ (by positivity : (0 : ℝ) < 100 * (m : ℝ))]
        linarith
      · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ (by positivity : (0 : ℝ) < 100 * (m : ℝ))]
        linarith
    have hmul_d : 0 ≤ (10 * (j.1 : ℝ)) * (d.im - (b₂ : ℝ) / (100 * (m : ℝ))) ∧
        (10 * (j.1 : ℝ)) * (d.im - (b₂ : ℝ) / (100 * (m : ℝ))) ≤ 1 / 10 := by
      constructor
      · exact mul_nonneg (by positivity) hdiff_d.1
      · calc (10 * (j.1 : ℝ)) * (d.im - (b₂ : ℝ) / (100 * (m : ℝ)))
            ≤ (10 * (m : ℝ)) * (1 / (100 * (m : ℝ))) :=
              mul_le_mul (by linarith) hdiff_d.2 hdiff_d.1 (by positivity)
          _ = 1 / 10 := by field_simp; norm_num
    have hcomb : (z.im + 10 * (j.1 : ℝ) * d.im) - apPtIm m γ j =
        (z.im - (a₂ : ℝ) / 10) + (10 * (j.1 : ℝ)) * (d.im - (b₂ : ℝ) / (100 * (m : ℝ))) := by
      simp only [apPtIm, γ]
      field_simp
      ring
    simp only [center, apGridPt]
    rw [abs_le]
    constructor <;> linarith

end Erdos188Solution

theorem OMA.solution : type_of% @Erdos188.erdos_188.variants.nonempty := by
  rcases Erdos188Solution.exists_global_coloring with ⟨m, hm, a, ha⟩
  refine ⟨10 * m, Set.univ \ Erdos188Solution.redSet a, ?_, ?_⟩
  · have hcompl : Set.univ \ (Set.univ \ Erdos188Solution.redSet a) = Erdos188Solution.redSet a := by
      ext z
      simp
    rw [hcompl]
    exact Erdos188Solution.redSet_pairwise_dist_ne_one a
  · rintro ⟨bs, hbs, z, d, hd, hap⟩
    rcases Erdos188Solution.ap_hits_redSet hm ha z d hd with ⟨n, hn, hred⟩
    have hmem_bs : z + n • d ∈ bs := by
      rw [hap.eq]
      exact ⟨n, by exact_mod_cast hn, rfl⟩
    exact (hbs hmem_bs).2 hred
