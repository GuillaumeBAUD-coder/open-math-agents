import FormalConjectures.ErdosProblems.«627»

/-!
# Erdős Problem 627 (1961 bound)

Formalizes Erdős's 1961 result that for all sufficiently large `n`, there exists a
triangle-free graph on `n` vertices with clique number 2 and chromatic number
at least `c * √n / log n`, via the asymmetric Lovász Local Lemma on `G(n, p)`.
-/

-- Problem: Erdős Problem 627 — erdos 1961
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/627.lean:161 (declaration Erdos627.erdos_627.variants.erdos_1961)
-- Credit: @shreyas-makes (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter SimpleGraph Finset

namespace OMA_Erdos627_1961

section FiniteProb

variable {E : Type*} [Fintype E]

def bitWeight (p : ℝ) (b : Bool) : ℝ :=
  if b then p else 1 - p

def prodWeight (p : ℝ) (ω : E → Bool) : ℝ :=
  ∏ e : E, bitWeight p (ω e)

noncomputable def prob [DecidableEq E] (p : ℝ) (A : Set (E → Bool)) : ℝ :=
  ∑ ω : E → Bool, @ite _ (ω ∈ A) (Classical.propDecidable _) (prodWeight p ω) 0

def DependsOn (S : Finset E) (A : Set (E → Bool)) : Prop :=
  ∀ ω₁ ω₂ : E → Bool, (∀ e ∈ S, ω₁ e = ω₂ e) → (ω₁ ∈ A ↔ ω₂ ∈ A)

lemma bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b <;> simp [bitWeight] <;> linarith

lemma sum_bitWeight (p : ℝ) : ∑ b : Bool, bitWeight p b = 1 := by
  simp [bitWeight]

lemma prodWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : E → Bool) :
    0 ≤ prodWeight p ω :=
  Finset.prod_nonneg fun _ _ => bitWeight_nonneg hp0 hp1 _

lemma prob_nonneg [DecidableEq E] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (E → Bool)) :
    0 ≤ prob p A := by
  unfold prob
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact prodWeight_nonneg hp0 hp1 ω
  · exact le_rfl

lemma prob_mono [DecidableEq E] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : Set (E → Bool)} (h : A ⊆ B) :
    prob p A ≤ prob p B := by
  unfold prob
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : ω ∈ A
  · simp [hA, h hA]
  · by_cases hB : ω ∈ B
    · simp [hA, hB, prodWeight_nonneg hp0 hp1 ω]
    · simp [hA, hB]

lemma sum_prod_bitWeight {F : Type*} [Fintype F] [DecidableEq F] (p : ℝ) :
    (∑ ω : F → Bool, ∏ e : F, bitWeight p (ω e)) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : F) (b : Bool) => bitWeight p b)]
  simp only [sum_bitWeight, Finset.prod_const_one]

lemma prob_univ [DecidableEq E] (p : ℝ) : prob p (Set.univ : Set (E → Bool)) = 1 := by
  unfold prob prodWeight
  simp only [Set.mem_univ, ↓reduceIte]
  exact sum_prod_bitWeight p

lemma prob_inter_compl [DecidableEq E] (p : ℝ) (A B : Set (E → Bool)) :
    prob p (B ∩ Aᶜ) = prob p B - prob p (A ∩ B) := by
  have hsum : prob p (A ∩ B) + prob p (B ∩ Aᶜ) = prob p B := by
    unfold prob
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]
  linarith

lemma prob_all_eq [DecidableEq E] (p : ℝ) (S : Finset E) (b : Bool) :
    prob p {ω : E → Bool | ∀ e ∈ S, ω e = b} = (bitWeight p b) ^ S.card := by
  let g : E → Bool → ℝ := fun e c =>
    if e ∈ S then (if c = b then bitWeight p c else 0) else bitWeight p c
  have hpoint : ∀ ω : E → Bool,
      @ite _ (ω ∈ ({ω : E → Bool | ∀ e ∈ S, ω e = b} : Set (E → Bool)))
        (Classical.propDecidable _) (prodWeight p ω) 0 = ∏ e : E, g e (ω e) := by
    intro ω
    by_cases h : ∀ e ∈ S, ω e = b
    · have hmem : ω ∈ ({ω : E → Bool | ∀ e ∈ S, ω e = b} : Set (E → Bool)) := h
      rw [if_pos hmem]
      unfold prodWeight
      refine Finset.prod_congr rfl fun e _ => ?_
      by_cases he : e ∈ S
      · simp [g, he, h e he]
      · simp [g, he]
    · have hmem : ω ∉ ({ω : E → Bool | ∀ e ∈ S, ω e = b} : Set (E → Bool)) := h
      rw [if_neg hmem]
      push Not at h
      obtain ⟨e₀, he₀S, he₀ne⟩ := h
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ e₀) ?_
      dsimp [g]
      rw [if_pos he₀S, if_neg he₀ne]
  unfold prob
  simp_rw [hpoint]
  have hps := Fintype.prod_sum g
  rw [← hps]
  have hfac : ∀ e : E, (∑ c : Bool, g e c) = if e ∈ S then bitWeight p b else 1 := by
    intro e
    by_cases he : e ∈ S
    · cases b <;> simp [g, he]
    · simp [g, he, bitWeight]
  simp_rw [hfac]
  simp

lemma prob_inter_of_dependsOn [DecidableEq E] (p : ℝ) (S : Finset E) {A B : Set (E → Bool)}
    (hA : DependsOn S A) (hB : DependsOn Sᶜ B) :
    prob p (A ∩ B) = prob p A * prob p B := by
  let eSplit : (E → Bool) ≃ ({e : E // e ∈ S} → Bool) × ({e : E // e ∉ S} → Bool) :=
    { toFun := fun ω => (fun x => ω x.1, fun x => ω x.1)
      invFun := fun q e => if h : e ∈ S then q.1 ⟨e, h⟩ else q.2 ⟨e, h⟩
      left_inv := fun ω => by funext e; by_cases h : e ∈ S <;> simp [h]
      right_inv := fun ⟨ω₁, ω₂⟩ => by
        ext x
        · simp [x.2]
        · simp [x.2] }
  have hprod : ∀ ω₁ ω₂,
      prodWeight p (eSplit.symm (ω₁, ω₂)) =
        (∏ x : {e : E // e ∈ S}, bitWeight p (ω₁ x)) *
        (∏ x : {e : E // e ∉ S}, bitWeight p (ω₂ x)) := by
    intro ω₁ ω₂
    unfold prodWeight
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : E => e ∈ S)]
    congr 1
    · symm
      refine Finset.prod_nbij Subtype.val ?_ ?_ ?_ ?_
      · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x.1, x.2⟩
      · intro a _ b _ hab; exact Subtype.ext hab
      · intro e he; exact ⟨⟨e, (Finset.mem_filter.mp he).2⟩, Finset.mem_univ _, rfl⟩
      · intro x _; simp [eSplit, x.2]
    · symm
      refine Finset.prod_nbij Subtype.val ?_ ?_ ?_ ?_
      · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x.1, x.2⟩
      · intro a _ b _ hab; exact Subtype.ext hab
      · intro e he; exact ⟨⟨e, (Finset.mem_filter.mp he).2⟩, Finset.mem_univ _, rfl⟩
      · intro x _; simp [eSplit, x.2]
  have hfact : ∀ (U V : Set (E → Bool)), DependsOn S U → DependsOn Sᶜ V →
      prob p (U ∩ V) =
        (∑ ω₁ : {e : E // e ∈ S} → Bool,
          @ite _ (eSplit.symm (ω₁, fun _ => false) ∈ U) (Classical.propDecidable _)
            (∏ x : {e : E // e ∈ S}, bitWeight p (ω₁ x)) 0) *
        (∑ ω₂ : {e : E // e ∉ S} → Bool,
          @ite _ (eSplit.symm (fun _ => false, ω₂) ∈ V) (Classical.propDecidable _)
            (∏ x : {e : E // e ∉ S}, bitWeight p (ω₂ x)) 0) := by
    intro U V hU hV
    unfold prob
    rw [← Equiv.sum_comp eSplit.symm
      (fun ω => @ite _ (ω ∈ U ∩ V) (Classical.propDecidable _) (prodWeight p ω) 0)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ω₁ _ => Finset.sum_congr rfl fun ω₂ _ => ?_
    have h1 : eSplit.symm (ω₁, ω₂) ∈ U ↔ eSplit.symm (ω₁, fun _ => false) ∈ U :=
      hU _ _ (fun e he => by simp [eSplit, he])
    have h2 : eSplit.symm (ω₁, ω₂) ∈ V ↔ eSplit.symm (fun _ => false, ω₂) ∈ V :=
      hV _ _ (fun e he => by
        have heS : e ∉ S := by simpa using he
        simp [eSplit, heS])
    by_cases hU' : eSplit.symm (ω₁, fun _ => false) ∈ U <;>
      by_cases hV' : eSplit.symm (fun _ => false, ω₂) ∈ V
    · have hUV : eSplit.symm (ω₁, ω₂) ∈ U ∩ V := ⟨h1.mpr hU', h2.mpr hV'⟩
      rw [if_pos hUV, if_pos hU', if_pos hV', hprod]
    · have hUV : eSplit.symm (ω₁, ω₂) ∉ U ∩ V := fun h => hV' (h2.mp h.2)
      rw [if_neg hUV, if_neg hV', mul_zero]
    · have hUV : eSplit.symm (ω₁, ω₂) ∉ U ∩ V := fun h => hU' (h1.mp h.1)
      rw [if_neg hUV, if_neg hU', zero_mul]
    · have hUV : eSplit.symm (ω₁, ω₂) ∉ U ∩ V := fun h => hU' (h1.mp h.1)
      rw [if_neg hUV, if_neg hU', zero_mul]
  have hU1 : DependsOn S (Set.univ : Set (E → Bool)) := fun _ _ _ => Iff.rfl
  have hV1 : DependsOn Sᶜ (Set.univ : Set (E → Bool)) := fun _ _ _ => Iff.rfl
  have hsum1 :
      (∑ ω₁ : {e : E // e ∈ S} → Bool, ∏ x : {e : E // e ∈ S}, bitWeight p (ω₁ x)) = 1 :=
    sum_prod_bitWeight p
  have hsum2 :
      (∑ ω₂ : {e : E // e ∉ S} → Bool, ∏ x : {e : E // e ∉ S}, bitWeight p (ω₂ x)) = 1 :=
    sum_prod_bitWeight p
  have hAeq : prob p A =
      ∑ ω₁ : {e : E // e ∈ S} → Bool,
        @ite _ (eSplit.symm (ω₁, fun _ => false) ∈ A) (Classical.propDecidable _)
          (∏ x : {e : E // e ∈ S}, bitWeight p (ω₁ x)) 0 := by
    have h := hfact A Set.univ hA hV1
    simp only [Set.inter_univ, Set.mem_univ, ↓reduceIte] at h
    rw [hsum2, mul_one] at h
    exact h
  have hBeq : prob p B =
      ∑ ω₂ : {e : E // e ∉ S} → Bool,
        @ite _ (eSplit.symm (fun _ => false, ω₂) ∈ B) (Classical.propDecidable _)
          (∏ x : {e : E // e ∉ S}, bitWeight p (ω₂ x)) 0 := by
    have h := hfact Set.univ B hU1 hB
    simp only [Set.univ_inter, Set.mem_univ, ↓reduceIte] at h
    rw [hsum1, one_mul] at h
    exact h
  rw [hfact A B hA hB, hAeq, hBeq]

omit [Fintype E] in
lemma dependsOn_all_eq (S : Finset E) (b : Bool) :
    DependsOn S {ω : E → Bool | ∀ e ∈ S, ω e = b} := by
  intro ω₁ ω₂ h
  change (∀ e ∈ S, ω₁ e = b) ↔ (∀ e ∈ S, ω₂ e = b)
  constructor <;> intro hω e he
  · rw [← h e he]; exact hω e he
  · rw [h e he]; exact hω e he

lemma dependsOn_biInter_compl [DecidableEq E] {I : Type*} (S : Finset E) (Q : Finset I)
    (A : I → Set (E → Bool)) (supp : I → Finset E)
    (hdep : ∀ i, DependsOn (supp i) (A i))
    (hdisj : ∀ j ∈ Q, Disjoint S (supp j)) :
    DependsOn Sᶜ (⋂ j ∈ Q, (A j)ᶜ) := by
  intro ω₁ ω₂ h
  simp only [Set.mem_iInter, Set.mem_compl_iff]
  refine forall₂_congr fun j hj => not_congr ?_
  refine hdep j ω₁ ω₂ fun e he => h e ?_
  simp only [Finset.mem_compl]
  exact Finset.disjoint_right.mp (hdisj j hj) he

end FiniteProb

section AsymmetricLLL

variable {E I : Type*}

def nbhd [DecidableEq E] [Fintype I] [DecidableEq I] (supp : I → Finset E) (i : I) : Finset I :=
  Finset.univ.filter (fun j => j ≠ i ∧ ¬ Disjoint (supp i) (supp j))

def avoid (A : I → Set (E → Bool)) (Q : Finset I) : Set (E → Bool) :=
  ⋂ j ∈ Q, (A j)ᶜ

lemma avoid_empty (A : I → Set (E → Bool)) : avoid A ∅ = Set.univ := by
  ext ω; simp [avoid]

lemma avoid_insert [DecidableEq I] (A : I → Set (E → Bool)) (q : I) (Q : Finset I) :
    avoid A (insert q Q) = avoid A Q ∩ (A q)ᶜ := by
  ext ω
  simp only [avoid, Set.mem_iInter, Finset.mem_insert, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Or.inr hj), h q (Or.inl rfl)⟩
  · rintro ⟨hQ, hq⟩ j (rfl | hj)
    · exact hq
    · exact hQ j hj

lemma avoid_anti (A : I → Set (E → Bool)) {Q₁ Q₂ : Finset I} (h : Q₁ ⊆ Q₂) :
    avoid A Q₂ ⊆ avoid A Q₁ := by
  intro ω hω
  simp only [avoid, Set.mem_iInter] at hω ⊢
  intro j hj
  exact hω j (h hj)

lemma lll_cond_bound [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : I → Set (E → Bool)) (supp : I → Finset E) (x : I → ℝ)
    (hdep : ∀ i, DependsOn (supp i) (A i))
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hLLL : ∀ i, prob p (A i) ≤ x i * ∏ j ∈ nbhd supp i, (1 - x j)) :
    ∀ n : ℕ, ∀ Q : Finset I, Q.card = n → ∀ i ∉ Q,
      prob p (A i ∩ avoid A Q) ≤ x i * prob p (avoid A Q) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Q hQ i hiQ
    let Q₁ := Q.filter (fun j => j ∈ nbhd supp i)
    let Q₂ := Q.filter (fun j => j ∉ nbhd supp i)
    have hQ_eq : Q₁ ∪ Q₂ = Q := by
      ext j
      simp only [Q₁, Q₂, Finset.mem_union, Finset.mem_filter]
      by_cases hj : j ∈ nbhd supp i <;> simp [hj]
    have hdisj12 : Disjoint Q₁ Q₂ := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      exact (Finset.mem_filter.mp hj2).2 (Finset.mem_filter.mp hj1).2
    have hQ1_sub : Q₁ ⊆ nbhd supp i := fun j hj => (Finset.mem_filter.mp hj).2
    have hQ2_sub : Q₂ ⊆ Q := Finset.filter_subset _ Q
    have hchain : ∀ R : Finset I, R ⊆ Q₁ →
        (∏ j ∈ R, (1 - x j)) * prob p (avoid A Q₂) ≤ prob p (avoid A (R ∪ Q₂)) := by
      intro R
      induction R using Finset.induction_on with
      | empty =>
        intro _
        simp
      | @insert r R hrR ihR =>
        intro hsub
        have hrQ1 : r ∈ Q₁ := hsub (Finset.mem_insert_self r R)
        have hRsub : R ⊆ Q₁ := fun j hj => hsub (Finset.mem_insert_of_mem hj)
        have hr_not_mem : r ∉ R ∪ Q₂ := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hrR, Finset.disjoint_left.mp hdisj12 hrQ1⟩
        have hcard_lt : (R ∪ Q₂).card < n := by
          have hsubQ : insert r (R ∪ Q₂) ⊆ Q := by
            rw [← hQ_eq]
            intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact Finset.mem_union_left _ hrQ1
            · rcases Finset.mem_union.mp hj' with hjR | hj2
              · exact Finset.mem_union_left _ (hRsub hjR)
              · exact Finset.mem_union_right _ hj2
          have hle := Finset.card_le_card hsubQ
          rw [Finset.card_insert_of_notMem hr_not_mem, hQ] at hle
          omega
        have hstep := ih (R ∪ Q₂).card hcard_lt (R ∪ Q₂) rfl r hr_not_mem
        have h1mr : 0 ≤ 1 - x r := by linarith [hx1 r]
        have heq : prob p (avoid A (insert r (R ∪ Q₂))) =
            prob p (avoid A (R ∪ Q₂)) - prob p (A r ∩ avoid A (R ∪ Q₂)) := by
          rw [avoid_insert, prob_inter_compl]
        have hge : (1 - x r) * prob p (avoid A (R ∪ Q₂)) ≤
            prob p (avoid A (insert r (R ∪ Q₂))) := by
          rw [heq]; linarith
        rw [Finset.insert_union, Finset.prod_insert hrR, mul_assoc]
        exact le_trans (mul_le_mul_of_nonneg_left (ihR hRsub) h1mr) hge
    have hQ1_chain : (∏ j ∈ Q₁, (1 - x j)) * prob p (avoid A Q₂) ≤ prob p (avoid A Q) := by
      have h := hchain Q₁ Subset.rfl
      rwa [hQ_eq] at h
    have hprod_le : ∏ j ∈ nbhd supp i, (1 - x j) ≤ ∏ j ∈ Q₁, (1 - x j) := by
      rw [← Finset.prod_sdiff hQ1_sub]
      have hdiff_le : ∏ j ∈ nbhd supp i \ Q₁, (1 - x j) ≤ 1 :=
        Finset.prod_le_one (fun j _ => by linarith [hx1 j]) (fun j _ => by linarith [hx0 j])
      have hQ1_nonneg : 0 ≤ ∏ j ∈ Q₁, (1 - x j) :=
        Finset.prod_nonneg fun j _ => by linarith [hx1 j]
      nlinarith
    have hQ2_disj : ∀ j ∈ Q₂, Disjoint (supp i) (supp j) := by
      intro j hj
      have hjQ : j ∈ Q := (Finset.mem_filter.mp hj).1
      have hjnot : j ∉ nbhd supp i := (Finset.mem_filter.mp hj).2
      have hne : j ≠ i := fun h => hiQ (h ▸ hjQ)
      by_contra hnd
      exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne, hnd⟩)
    have hind : prob p (A i ∩ avoid A Q₂) = prob p (A i) * prob p (avoid A Q₂) :=
      prob_inter_of_dependsOn p (supp i) (hdep i)
        (dependsOn_biInter_compl (supp i) Q₂ A supp hdep hQ2_disj)
    have hmono : prob p (A i ∩ avoid A Q) ≤ prob p (A i ∩ avoid A Q₂) :=
      prob_mono hp0 hp1 (Set.inter_subset_inter_right _ (avoid_anti A hQ2_sub))
    have hQ2_nonneg : 0 ≤ prob p (avoid A Q₂) := prob_nonneg hp0 hp1 _
    calc prob p (A i ∩ avoid A Q)
        ≤ prob p (A i ∩ avoid A Q₂) := hmono
      _ = prob p (A i) * prob p (avoid A Q₂) := hind
      _ ≤ (x i * ∏ j ∈ nbhd supp i, (1 - x j)) * prob p (avoid A Q₂) :=
          mul_le_mul_of_nonneg_right (hLLL i) hQ2_nonneg
      _ = x i * ((∏ j ∈ nbhd supp i, (1 - x j)) * prob p (avoid A Q₂)) := by ring
      _ ≤ x i * ((∏ j ∈ Q₁, (1 - x j)) * prob p (avoid A Q₂)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod_le hQ2_nonneg) (hx0 i)
      _ ≤ x i * prob p (avoid A Q) :=
          mul_le_mul_of_nonneg_left hQ1_chain (hx0 i)

lemma exists_avoid_all [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : I → Set (E → Bool)) (supp : I → Finset E) (x : I → ℝ)
    (hdep : ∀ i, DependsOn (supp i) (A i))
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hLLL : ∀ i, prob p (A i) ≤ x i * ∏ j ∈ nbhd supp i, (1 - x j)) :
    ∃ ω : E → Bool, ∀ i : I, ω ∉ A i := by
  have hcond := lll_cond_bound hp0 hp1 A supp x hdep hx0 hx1 hLLL
  have hlow : ∀ Q : Finset I, ∏ j ∈ Q, (1 - x j) ≤ prob p (avoid A Q) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
      simp [avoid_empty, prob_univ]
    | @insert q Q hqQ ihQ =>
      have hstep := hcond Q.card Q rfl q hqQ
      have h1mq : 0 ≤ 1 - x q := by linarith [hx1 q]
      have heq : prob p (avoid A (insert q Q)) = prob p (avoid A Q) - prob p (A q ∩ avoid A Q) := by
        rw [avoid_insert, prob_inter_compl]
      have hge : (1 - x q) * prob p (avoid A Q) ≤ prob p (avoid A (insert q Q)) := by
        rw [heq]; linarith
      rw [Finset.prod_insert hqQ]
      exact le_trans (mul_le_mul_of_nonneg_left ihQ h1mq) hge
  have hpos : 0 < prob p (avoid A Finset.univ) := by
    refine lt_of_lt_of_le ?_ (hlow Finset.univ)
    exact Finset.prod_pos fun j _ => by linarith [hx1 j]
  by_contra hall
  push Not at hall
  have hempty : avoid A Finset.univ = ∅ := by
    ext ω
    simp only [avoid, Set.mem_iInter, Finset.mem_univ, forall_const, Set.mem_compl_iff,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    exact hall ω
  have hzero : prob p (avoid A Finset.univ) = 0 := by
    rw [hempty]
    classical
    simp [prob]
  linarith

end AsymmetricLLL

section ElementaryBounds

lemma bernoulli_sub {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * x ≤ (1 - x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [pow_succ]
    have h1 : 0 ≤ 1 - x := by linarith
    have h2 : (1 - (m : ℝ) * x) * (1 - x) ≤ (1 - x) ^ m * (1 - x) :=
      mul_le_mul_of_nonneg_right ih h1
    have h3 : 0 ≤ (m : ℝ) * x ^ 2 := by positivity
    nlinarith

lemma exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by
    linarith [Real.add_one_le_exp (2 * x)]
  have hpos : 0 < 1 + 2 * x := by linarith
  have h2 : Real.exp (-2 * x) ≤ (1 + 2 * x)⁻¹ := by
    rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
    exact inv_anti₀ hpos h1
  have h3 : (1 + 2 * x)⁻¹ ≤ 1 - x := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  exact le_trans h2 h3

lemma choose_le_pow_nat (n k : ℕ) : n.choose k ≤ n ^ k := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.choose_succ_succ]
      change n.choose k + n.choose (k + 1) ≤ (n + 1) ^ (k + 1)
      have h1 := ih k
      have h2 := ih (k + 1)
      have h3 : n ^ k + n ^ (k + 1) = (n + 1) * n ^ k := by ring
      have h4 : (n + 1) * n ^ k ≤ (n + 1) * (n + 1) ^ k :=
        Nat.mul_le_mul_left (n + 1) (Nat.pow_le_pow_left (Nat.le_succ n) k)
      have h5 : (n + 1) * (n + 1) ^ k = (n + 1) ^ (k + 1) := by rw [pow_succ']
      omega

lemma log_le_div_250_sqrt {n : ℕ} (hn : 1000 ^ 4 ≤ n) :
    Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) / 250 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  let y : ℝ := Real.sqrt (Real.sqrt (n : ℝ))
  have hy_nonneg : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = Real.sqrt (n : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hy4 : y ^ 4 = (n : ℝ) := by
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (n : ℝ)) ^ 2 := by rw [hy2]
      _ = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
  have hy_ge : (1000 : ℝ) ≤ y := by
    have h1 : (1000 : ℝ) ^ 4 ≤ y ^ 4 := by
      rw [hy4]
      exact_mod_cast hn
    by_contra hlt
    push Not at hlt
    have h2 : y ^ 4 < (1000 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hy_nonneg (by norm_num)
    linarith
  have hy_pos : 0 < y := by linarith
  have hlog : Real.log (n : ℝ) = 4 * Real.log y := by
    rw [← hy4, Real.log_pow]
    norm_num
  have hlog_y : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy_pos
  have h4y : 4 * y ≤ y ^ 2 / 250 := by nlinarith
  rw [hlog, ← hy2]
  linarith

lemma choose_two_ge_sq_div_four {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) ^ 2 / 4 ≤ (k.choose 2 : ℝ) := by
  have hnat : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
  have hreal : (2 : ℝ) * (k.choose 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
    have hk1 : 1 ≤ k := by omega
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast [hk1] at hcast
    exact hcast
  have hk2_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith

lemma lll_indep_numeric {n k M : ℕ} (hn : 1000 ^ 4 ≤ n) (hk2 : 2 ≤ k)
    (hM_pos : 1 ≤ M) (hM_le : M ≤ n ^ k)
    (hk_ge : 100 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ (k : ℝ)) :
    let p : ℝ := 1 / (10 * Real.sqrt (n : ℝ))
    let xT : ℝ := 4 * p ^ 3
    (1 - p) ^ (k.choose 2) ≤ (1 / (4 * (M : ℝ))) * (1 - xT) ^ (k.choose 2 * n) := by
  intro p xT
  have hn_real : (1000 : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrt_ge : (1000 : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (le_of_lt hn_pos)]
    linarith
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have hexp1 : Real.exp 1 ≤ (n : ℝ) := by
      have : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 1) hexp1
  have hM_pos_real : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hM_pos)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 / 10 := by
    dsimp [p]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hxT0 : 0 ≤ xT := by positivity
  have hxT_half : xT ≤ 1 / 2 := by
    dsimp [xT]
    have h1 : p ^ 3 ≤ (1 / 10 : ℝ) ^ 3 := pow_le_pow_left₀ hp0 hp1 3
    linarith
  have hlhs : (1 - p) ^ (k.choose 2) ≤ Real.exp (-p * (k.choose 2 : ℝ)) := by
    have h1 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    calc (1 - p) ^ (k.choose 2)
        ≤ (Real.exp (-p)) ^ (k.choose 2) := pow_le_pow_left₀ (by linarith) h1 _
      _ = Real.exp ((k.choose 2 : ℝ) * (-p)) := (Real.exp_nat_mul (-p) (k.choose 2)).symm
      _ = Real.exp (-p * (k.choose 2 : ℝ)) := by ring_nf
  have hrhs_exp : Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ)) ≤
      (1 - xT) ^ (k.choose 2 * n) := by
    have h1 : Real.exp (-2 * xT) ≤ 1 - xT := exp_neg_two_mul_le_one_sub hxT0 hxT_half
    calc Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ))
        = Real.exp (((k.choose 2 * n : ℕ) : ℝ) * (-2 * xT)) := by ring_nf
      _ = (Real.exp (-2 * xT)) ^ (k.choose 2 * n) := Real.exp_nat_mul (-2 * xT) _
      _ ≤ (1 - xT) ^ (k.choose 2 * n) :=
          pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h1 _
  have h2xTn : 2 * xT * (n : ℝ) = (2 / 25 : ℝ) * p := by
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hn_pos)
    dsimp [xT, p]
    have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
    field_simp [hne]
    nlinarith [hsq]
  have hlog4M : Real.log (4 * (M : ℝ)) ≤ (p - 2 * xT * (n : ℝ)) * (k.choose 2 : ℝ) := by
    have h4M_le : 4 * (M : ℝ) ≤ (n : ℝ) ^ (k + 1) := by
      have h4n : (4 : ℝ) ≤ (n : ℝ) := by linarith
      have hM_le_r : (M : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast hM_le
      calc 4 * (M : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ k :=
            mul_le_mul h4n hM_le_r (by positivity) (by positivity)
        _ = (n : ℝ) ^ (k + 1) := by rw [pow_succ']
    have hlog1 : Real.log (4 * (M : ℝ)) ≤ 2 * (k : ℝ) * Real.log (n : ℝ) := by
      calc Real.log (4 * (M : ℝ))
          ≤ Real.log ((n : ℝ) ^ (k + 1)) := Real.log_le_log (by positivity) h4M_le
        _ = ((k + 1 : ℕ) : ℝ) * Real.log (n : ℝ) := Real.log_pow (n : ℝ) (k + 1)
        _ ≤ 2 * (k : ℝ) * Real.log (n : ℝ) := by
            have hk1_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
            push_cast
            nlinarith
    have hlog2 : 2 * (k : ℝ) * Real.log (n : ℝ) ≤
        (k : ℝ) ^ 2 / (50 * Real.sqrt (n : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hlog3 : (k : ℝ) ^ 2 / (50 * Real.sqrt (n : ℝ)) ≤
        (p - 2 * xT * (n : ℝ)) * (k.choose 2 : ℝ) := by
      rw [h2xTn, show p - (2 / 25 : ℝ) * p = (23 / 25 : ℝ) * p by ring]
      have h1 : (23 / 25 : ℝ) * p * ((k : ℝ) ^ 2 / 4) ≤
          (23 / 25 : ℝ) * p * (k.choose 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (choose_two_ge_sq_div_four hk2) (by positivity)
      have h2 : (k : ℝ) ^ 2 / (50 * Real.sqrt (n : ℝ)) ≤
          (23 / 25 : ℝ) * p * ((k : ℝ) ^ 2 / 4) := by
        dsimp [p]
        have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
        have hdiff : (23 / 25 : ℝ) * (1 / (10 * Real.sqrt (n : ℝ))) * ((k : ℝ) ^ 2 / 4) -
            (k : ℝ) ^ 2 / (50 * Real.sqrt (n : ℝ)) =
            (3 / 1000 : ℝ) * ((k : ℝ) ^ 2 / Real.sqrt (n : ℝ)) := by
          field_simp [hne]
          ring
        have hnn : 0 ≤ (3 / 1000 : ℝ) * ((k : ℝ) ^ 2 / Real.sqrt (n : ℝ)) := by positivity
        linarith
      exact le_trans h2 h1
    exact le_trans hlog1 (le_trans hlog2 hlog3)
  have hexp_cmp : Real.exp (-p * (k.choose 2 : ℝ)) ≤
      (1 / (4 * (M : ℝ))) * Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ)) := by
    have h4M_eq : 4 * (M : ℝ) = Real.exp (Real.log (4 * (M : ℝ))) :=
      (Real.exp_log (by positivity)).symm
    have h4M_exp : 4 * (M : ℝ) ≤ Real.exp ((p - 2 * xT * (n : ℝ)) * (k.choose 2 : ℝ)) := by
      rw [h4M_eq]
      exact Real.exp_le_exp.mpr hlog4M
    have hsplit : Real.exp ((p - 2 * xT * (n : ℝ)) * (k.choose 2 : ℝ)) =
        Real.exp (p * (k.choose 2 : ℝ)) * Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit] at h4M_exp
    have h1 : (1 : ℝ) ≤ Real.exp (p * (k.choose 2 : ℝ)) *
        ((1 / (4 * (M : ℝ))) * Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ))) := by
      have hne : (4 * (M : ℝ)) ≠ 0 := by positivity
      calc (1 : ℝ) = (4 * (M : ℝ)) * (1 / (4 * (M : ℝ))) := by field_simp [hne]
        _ ≤ (Real.exp (p * (k.choose 2 : ℝ)) * Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ))) *
            (1 / (4 * (M : ℝ))) :=
            mul_le_mul_of_nonneg_right h4M_exp (by positivity)
        _ = Real.exp (p * (k.choose 2 : ℝ)) *
            ((1 / (4 * (M : ℝ))) * Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ))) := by ring
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos (-p * (k.choose 2 : ℝ))))
    calc Real.exp (-p * (k.choose 2 : ℝ))
        = Real.exp (-p * (k.choose 2 : ℝ)) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-p * (k.choose 2 : ℝ)) * (Real.exp (p * (k.choose 2 : ℝ)) *
          ((1 / (4 * (M : ℝ))) * Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ)))) := h2
      _ = (Real.exp (-p * (k.choose 2 : ℝ)) * Real.exp (p * (k.choose 2 : ℝ))) *
          ((1 / (4 * (M : ℝ))) * Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ))) := by ring
      _ = (1 / (4 * (M : ℝ))) * Real.exp (-2 * xT * ((k.choose 2 * n : ℕ) : ℝ)) := by
          rw [← Real.exp_add, show -p * (k.choose 2 : ℝ) + p * (k.choose 2 : ℝ) = 0 by ring,
            Real.exp_zero, one_mul]
  exact le_trans hlhs (le_trans hexp_cmp (mul_le_mul_of_nonneg_left hrhs_exp (by positivity)))

end ElementaryBounds

section GraphApplication

abbrev Edge (n : ℕ) := { e : Finset (Fin n) // e.card = 2 }

def edgesOf {n : ℕ} (U : Finset (Fin n)) : Finset (Edge n) :=
  Finset.univ.filter (fun e : Edge n => e.1 ⊆ U)

lemma card_edgesOf {n : ℕ} (U : Finset (Fin n)) :
    (edgesOf U).card = U.card.choose 2 := by
  rw [← Finset.card_powersetCard 2 U]
  refine Finset.card_nbij Subtype.val ?_ ?_ ?_
  · intro e he
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp he).2, e.2⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro s hs
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
    exact ⟨⟨s, hcard⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩, rfl⟩

lemma card_triangles_sharing_edge {n : ℕ} (U : Finset (Fin n)) :
    (Finset.univ.filter (fun T : {T : Finset (Fin n) // T.card = 3} =>
      ¬ Disjoint (edgesOf U) (edgesOf T.1))).card ≤ U.card.choose 2 * n := by
  let cover : Finset (Finset (Fin n)) :=
    (U.powersetCard 2).biUnion (fun e => Finset.univ.image (fun v : Fin n => insert v e))
  have hcard_cover : cover.card ≤ U.card.choose 2 * n := by
    calc cover.card
        ≤ ∑ e ∈ U.powersetCard 2, (Finset.univ.image (fun v : Fin n => insert v e)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ U.powersetCard 2, (Finset.univ : Finset (Fin n)).card :=
          Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ = (U.powersetCard 2).card * n := by simp
      _ = U.card.choose 2 * n := by rw [Finset.card_powersetCard]
  refine le_trans ?_ hcard_cover
  refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
  · intro T hT
    have hnd : ¬ Disjoint (edgesOf U) (edgesOf T.1) := (Finset.mem_filter.mp hT).2
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨e, heU, heT⟩ := hnd
    have heU_sub : e.1 ⊆ U := (Finset.mem_filter.mp heU).2
    have heT_sub : e.1 ⊆ T.1 := (Finset.mem_filter.mp heT).2
    have hsdiff_card : (T.1 \ e.1).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr heT_sub, T.2, e.2]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hsdiff_card
    have hTeq : T.1 = insert v e.1 := by
      ext x
      constructor
      · intro hx
        by_cases hxe : x ∈ e.1
        · exact Finset.mem_insert_of_mem hxe
        · have hx_diff : x ∈ T.1 \ e.1 := Finset.mem_sdiff.mpr ⟨hx, hxe⟩
          rw [hv, Finset.mem_singleton] at hx_diff
          exact hx_diff ▸ Finset.mem_insert_self v e.1
      · intro hx
        rcases Finset.mem_insert.mp hx with rfl | hxe
        · have hx_mem : x ∈ T.1 \ e.1 := by rw [hv]; exact Finset.mem_singleton_self x
          exact (Finset.mem_sdiff.mp hx_mem).1
        · exact heT_sub hxe
    refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_powersetCard.mpr ⟨heU_sub, e.2⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hTeq.symm⟩
  · intro a _ b _ hab
    exact Subtype.ext hab

lemma exists_good_edges (n k : ℕ) (hn : 1000 ^ 4 ≤ n) (hk2 : 2 ≤ k) (hk_le : k ≤ n)
    (hk_ge : 100 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ (k : ℝ)) :
    ∃ ω : Edge n → Bool,
      (∀ T : Finset (Fin n), T.card = 3 → ¬ ∀ e ∈ edgesOf T, ω e = true) ∧
      (∀ S : Finset (Fin n), S.card = k → ¬ ∀ e ∈ edgesOf S, ω e = false) := by
  have hn_real : (1000 : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrt_ge : (1000 : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (le_of_lt hn_pos)]
    linarith
  let p : ℝ := 1 / (10 * Real.sqrt (n : ℝ))
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    rw [div_le_one (by positivity)]
    linarith
  let I := { T : Finset (Fin n) // T.card = 3 } ⊕ { S : Finset (Fin n) // S.card = k }
  let M : ℕ := Fintype.card { S : Finset (Fin n) // S.card = k }
  have hM_eq : M = n.choose k := by
    dsimp [M]
    rw [Fintype.card_subtype]
    have hfilt : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = k)) =
        (Finset.univ : Finset (Fin n)).powersetCard k := by
      ext S
      simp [Finset.mem_powersetCard]
    rw [hfilt, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hM_pos : 1 ≤ M := by
    rw [hM_eq]
    exact Nat.choose_pos hk_le
  have hM_pos_real : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hM_pos)
  let xT : ℝ := 4 * p ^ 3
  let xS : ℝ := 1 / (2 * (M : ℝ))
  have hxT0 : 0 ≤ xT := by positivity
  have hxT_half : xT ≤ 1 / 2 := by
    have hp_le : p ≤ 1 / 10 := by
      dsimp [p]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    dsimp [xT]
    have h1 : p ^ 3 ≤ (1 / 10 : ℝ) ^ 3 := pow_le_pow_left₀ hp0 hp_le 3
    linarith
  have hxT1 : xT < 1 := by linarith
  have hxS0 : 0 ≤ xS := by positivity
  have hxS1 : xS < 1 := by
    dsimp [xS]
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_pos
    linarith
  let supp : I → Finset (Edge n) := Sum.elim (fun T => edgesOf T.1) (fun S => edgesOf S.1)
  let A : I → Set (Edge n → Bool) :=
    Sum.elim
      (fun T => {ω | ∀ e ∈ edgesOf T.1, ω e = true})
      (fun S => {ω | ∀ e ∈ edgesOf S.1, ω e = false})
  let x : I → ℝ := Sum.elim (fun _ => xT) (fun _ => xS)
  have hdep : ∀ i : I, DependsOn (supp i) (A i) := by
    rintro (T | S)
    · exact dependsOn_all_eq (edgesOf T.1) true
    · exact dependsOn_all_eq (edgesOf S.1) false
  have hx0 : ∀ i : I, 0 ≤ x i := by rintro (_ | _) <;> assumption
  have hx1 : ∀ i : I, x i < 1 := by rintro (_ | _) <;> assumption
  have hbernoulli_S : (1 / 2 : ℝ) ≤ (1 - xS) ^ M := by
    have h := bernoulli_sub hxS0 (le_of_lt hxS1) M
    have hmul : (M : ℝ) * xS = 1 / 2 := by dsimp [xS]; field_simp
    linarith
  have hprod_nbhd : ∀ (i : I) (d : ℕ),
      (Finset.univ.filter (fun T : {T : Finset (Fin n) // T.card = 3} =>
        ¬ Disjoint (supp i) (edgesOf T.1))).card ≤ d →
      (1 - xT) ^ d * (1 - xS) ^ M ≤ ∏ j ∈ nbhd supp i, (1 - x j) := by
    intro i d hd
    let L := (nbhd supp i).filter (fun j : I => Sum.isLeft j)
    let R := (nbhd supp i).filter (fun j : I => !Sum.isLeft j)
    have hLR_union : L ∪ R = nbhd supp i := by
      ext j
      simp only [L, R, Finset.mem_union, Finset.mem_filter]
      cases j <;> simp
    have hLR_disj : Disjoint L R := by
      rw [Finset.disjoint_left]
      intro j hjL hjR
      have h1 := (Finset.mem_filter.mp hjL).2
      have h2 := (Finset.mem_filter.mp hjR).2
      cases j <;> simp at h1 h2
    rw [← hLR_union, Finset.prod_union hLR_disj]
    have hL_prod : ∏ j ∈ L, (1 - x j) = (1 - xT) ^ L.card := by
      calc ∏ j ∈ L, (1 - x j)
          = ∏ _j ∈ L, (1 - xT) := by
            refine Finset.prod_congr rfl fun j hj => ?_
            have h1 := (Finset.mem_filter.mp hj).2
            cases j with
            | inl _ => rfl
            | inr _ => simp at h1
        _ = (1 - xT) ^ L.card := Finset.prod_const _
    have hR_prod : ∏ j ∈ R, (1 - x j) = (1 - xS) ^ R.card := by
      calc ∏ j ∈ R, (1 - x j)
          = ∏ _j ∈ R, (1 - xS) := by
            refine Finset.prod_congr rfl fun j hj => ?_
            have h1 := (Finset.mem_filter.mp hj).2
            cases j with
            | inl _ => simp at h1
            | inr _ => rfl
        _ = (1 - xS) ^ R.card := Finset.prod_const _
    rw [hL_prod, hR_prod]
    have hL_card : L.card ≤ d := by
      let Tset := Finset.univ.filter (fun T : {T : Finset (Fin n) // T.card = 3} =>
        ¬ Disjoint (supp i) (edgesOf T.1))
      have hLsub : L ⊆ Tset.image Sum.inl := by
        intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjnb, hjL⟩
        cases j with
        | inl T =>
          have hnd := (Finset.mem_filter.mp hjnb).2.2
          exact Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ T, hnd⟩, rfl⟩
        | inr _ => simp at hjL
      exact le_trans (Finset.card_le_card hLsub) (le_trans Finset.card_image_le hd)
    have hR_card : R.card ≤ M := by
      have hRsub : R ⊆ (Finset.univ : Finset {S : Finset (Fin n) // S.card = k}).image Sum.inr := by
        intro j hj
        have hjR := (Finset.mem_filter.mp hj).2
        cases j with
        | inl _ => simp at hjR
        | inr S => exact Finset.mem_image.mpr ⟨S, Finset.mem_univ S, rfl⟩
      calc R.card ≤ ((Finset.univ : Finset {S : Finset (Fin n) // S.card = k}).image Sum.inr).card :=
            Finset.card_le_card hRsub
        _ ≤ (Finset.univ : Finset {S : Finset (Fin n) // S.card = k}).card := Finset.card_image_le
        _ = M := Finset.card_univ
    have h1 : (1 - xT) ^ d ≤ (1 - xT) ^ L.card :=
      pow_le_pow_of_le_one (by linarith) (by linarith) hL_card
    have h2 : (1 - xS) ^ M ≤ (1 - xS) ^ R.card :=
      pow_le_pow_of_le_one (by linarith) (by linarith) hR_card
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hLLL : ∀ i : I, prob p (A i) ≤ x i * ∏ j ∈ nbhd supp i, (1 - x j) := by
    rintro (T | S)
    · have hprob : prob p (A (Sum.inl T)) = p ^ 3 := by
        dsimp [A]
        rw [prob_all_eq, card_edgesOf, T.2]
        simp [bitWeight]
      rw [hprob]
      have hdL : (Finset.univ.filter (fun T' : {T : Finset (Fin n) // T.card = 3} =>
          ¬ Disjoint (supp (Sum.inl T)) (edgesOf T'.1))).card ≤ 3 * n := by
        have h := card_triangles_sharing_edge T.1
        rw [T.2] at h
        exact h
      have hT_pow : (1 / 2 : ℝ) ≤ (1 - xT) ^ (3 * n) := by
        have h := bernoulli_sub hxT0 (le_of_lt hxT1) (3 * n)
        have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
          Real.mul_self_sqrt (le_of_lt hn_pos)
        have h3nx : ((3 * n : ℕ) : ℝ) * xT ≤ 1 / 2 := by
          push_cast
          dsimp [xT, p]
          have hcalc : (3 : ℝ) * (n : ℝ) * (4 * (1 / (10 * Real.sqrt (n : ℝ))) ^ 3) =
              12 / (1000 * Real.sqrt (n : ℝ)) := by
            have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
            field_simp [hne]
            nlinarith [hsq]
          rw [hcalc, div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        linarith
      have hnb := hprod_nbhd (Sum.inl T) (3 * n) hdL
      dsimp [x]
      have hprod_ge : (1 / 4 : ℝ) ≤ ∏ j ∈ nbhd supp (Sum.inl T), (1 - x j) := by
        calc (1 / 4 : ℝ) = (1 / 2) * (1 / 2) := by norm_num
          _ ≤ (1 - xT) ^ (3 * n) * (1 - xS) ^ M :=
              mul_le_mul hT_pow hbernoulli_S (by norm_num) (by positivity)
          _ ≤ ∏ j ∈ nbhd supp (Sum.inl T), (1 - x j) := hnb
      dsimp [xT]
      nlinarith [pow_nonneg hp0 3]
    · have hprob : prob p (A (Sum.inr S)) = (1 - p) ^ (k.choose 2) := by
        dsimp [A]
        rw [prob_all_eq, card_edgesOf, S.2]
        simp [bitWeight]
      rw [hprob]
      have hdL : (Finset.univ.filter (fun T' : {T : Finset (Fin n) // T.card = 3} =>
          ¬ Disjoint (supp (Sum.inr S)) (edgesOf T'.1))).card ≤ k.choose 2 * n := by
        have h := card_triangles_sharing_edge S.1
        rw [S.2] at h
        exact h
      have hnb := hprod_nbhd (Sum.inr S) (k.choose 2 * n) hdL
      have hM_le : M ≤ n ^ k := by rw [hM_eq]; exact choose_le_pow_nat n k
      have hnum := lll_indep_numeric hn hk2 hM_pos hM_le hk_ge
      dsimp [x]
      calc (1 - p) ^ (k.choose 2)
          ≤ (1 / (4 * (M : ℝ))) * (1 - xT) ^ (k.choose 2 * n) := hnum
        _ = xS * ((1 - xT) ^ (k.choose 2 * n) * (1 / 2)) := by dsimp [xS]; ring
        _ ≤ xS * ((1 - xT) ^ (k.choose 2 * n) * (1 - xS) ^ M) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hbernoulli_S (by positivity)) hxS0
        _ ≤ xS * ∏ j ∈ nbhd supp (Sum.inr S), (1 - x j) :=
            mul_le_mul_of_nonneg_left hnb hxS0
  obtain ⟨ω, hω⟩ := exists_avoid_all hp0 hp1 A supp x hdep hx0 hx1 hLLL
  refine ⟨ω, ?_, ?_⟩
  · intro T hT
    exact hω (Sum.inl ⟨T, hT⟩)
  · intro S hS
    exact hω (Sum.inr ⟨S, hS⟩)

lemma graph_from_good_edges (n k : ℕ) (hk_pos : 0 < k) (hkn : k < n)
    (ω : Edge n → Bool)
    (htri_ω : ∀ T : Finset (Fin n), T.card = 3 → ¬ ∀ e ∈ edgesOf T, ω e = true)
    (hind_ω : ∀ S : Finset (Fin n), S.card = k → ¬ ∀ e ∈ edgesOf S, ω e = false) :
    ∃ G : SimpleGraph (Fin n), G.cliqueNum = 2 ∧
      (n : ℝ) / (k : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  classical
  let G : SimpleGraph (Fin n) :=
    { Adj := fun u v => ∃ h : u ≠ v, ω ⟨{u, v}, Finset.card_pair h⟩ = true
      symm := ⟨fun u v ⟨huv, hω⟩ => ⟨huv.symm, by
        have heq : (⟨{v, u}, Finset.card_pair huv.symm⟩ : Edge n) =
            ⟨{u, v}, Finset.card_pair huv⟩ := Subtype.ext (Finset.pair_comm v u)
        rwa [heq]⟩⟩
      loopless := ⟨fun u ⟨h, _⟩ => h rfl⟩ }
  have htri : G.CliqueFree 3 := by
    intro T hT
    obtain ⟨hTclique, hTcard⟩ := hT
    apply htri_ω T hTcard
    intro e he
    have hesub : e.1 ⊆ T := (Finset.mem_filter.mp he).2
    obtain ⟨u, v, huv, heuv⟩ := Finset.card_eq_two.mp e.2
    have huT : u ∈ T := hesub (heuv ▸ Finset.mem_insert_self u {v})
    have hvT : v ∈ T := hesub (heuv ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
    obtain ⟨_, htrue⟩ := hTclique huT hvT huv
    have heq : e = ⟨{u, v}, Finset.card_pair huv⟩ := Subtype.ext heuv
    rwa [heq]
  have hindep : ∀ S : Finset (Fin n), S.card = k → ∃ u ∈ S, ∃ v ∈ S, G.Adj u v := by
    intro S hScard
    have hnot := hind_ω S hScard
    push Not at hnot
    obtain ⟨e, heS, hne⟩ := hnot
    have htrue : ω e = true := by
      cases hval : ω e with
      | true => rfl
      | false => exact False.elim (hne hval)
    have hesub : e.1 ⊆ S := (Finset.mem_filter.mp heS).2
    obtain ⟨u, v, huv, heuv⟩ := Finset.card_eq_two.mp e.2
    have huS : u ∈ S := hesub (heuv ▸ Finset.mem_insert_self u {v})
    have hvS : v ∈ S := hesub (heuv ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
    refine ⟨u, huS, v, hvS, huv, ?_⟩
    have heq : (⟨{u, v}, Finset.card_pair huv⟩ : Edge n) = e := Subtype.ext heuv.symm
    rw [heq]
    exact htrue
  let m : ℕ := G.chromaticNumber.toNat
  have hχ_ne_top : G.chromaticNumber ≠ ⊤ := by
    have hle : G.chromaticNumber ≤ n :=
      SimpleGraph.chromaticNumber_le_iff_colorable.mpr (by simpa using SimpleGraph.colorable_of_fintype G)
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top n) hle
  have hcol : G.Colorable m :=
    SimpleGraph.chromaticNumber_le_iff_colorable.mp (by rw [ENat.natCast_toNat hχ_ne_top])
  obtain ⟨C⟩ := hcol
  have hfiber_lt : ∀ c : Fin m, (Finset.univ.filter (fun v : Fin n => C v = c)).card < k := by
    intro c
    by_contra hge
    push Not at hge
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hge
    obtain ⟨u, huS, v, hvS, hadj⟩ := hindep S hScard
    have hCu : C u = c := (Finset.mem_filter.mp (hSsub huS)).2
    have hCv : C v = c := (Finset.mem_filter.mp (hSsub hvS)).2
    exact C.valid hadj (hCu.trans hCv.symm)
  have hn_le_mk : n ≤ m * k := by
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ = ∑ c : Fin m, (Finset.univ.filter (fun v : Fin n => C v = c)).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := fun v : Fin n => C v)
            (t := (Finset.univ : Finset (Fin m))) (fun _ _ => Finset.mem_univ _)]
      _ ≤ ∑ _c : Fin m, k := Finset.sum_le_sum fun c _ => le_of_lt (hfiber_lt c)
      _ = m * k := by simp
  have hχ_bound : (n : ℝ) / (k : ℝ) ≤ (m : ℝ) := by
    have hk_pos_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
    rw [div_le_iff₀ hk_pos_real]
    exact_mod_cast hn_le_mk
  have hm_ge2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m ≤ 1 := by omega
    have hle_k : n ≤ k := by
      calc n ≤ m * k := hn_le_mk
        _ ≤ 1 * k := Nat.mul_le_mul_right k hm1
        _ = k := one_mul k
    omega
  have hω_eq : G.cliqueNum = 2 := by
    apply Nat.le_antisymm htri.cliqueNum_le_two
    have hex_edge : ∃ u v : Fin n, G.Adj u v := by
      by_contra hno
      push Not at hno
      have hcol1 : G.Colorable 1 :=
        ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 1)) (fun h => False.elim (hno _ _ h))⟩
      have hle1 : G.chromaticNumber ≤ 1 :=
        SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcol1
      rw [← ENat.natCast_toNat hχ_ne_top] at hle1
      have : m ≤ 1 := by exact_mod_cast hle1
      omega
    obtain ⟨u, v, huv⟩ := hex_edge
    have hne : u ≠ v := G.ne_of_adj huv
    have hpair : G.IsClique ({u, v} : Finset (Fin n)) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact huv
      · exact huv.symm
      · exact False.elim (hab rfl)
    have hle := hpair.card_le_cliqueNum
    rwa [Finset.card_pair hne] at hle
  exact ⟨G, hω_eq, hχ_bound⟩

lemma graphOf_exists (n : ℕ) (hn : 1000 ^ 4 ≤ n) :
    ∃ G : SimpleGraph (Fin n), G.cliqueNum = 2 ∧
      (1 / 101 : ℝ) * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  have hn_real : (1000 : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrt_ge : (1000 : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (le_of_lt hn_pos)]
    linarith
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have hexp1 : Real.exp 1 ≤ (n : ℝ) := by
      have : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 1) hexp1
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlog_ub : Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) / 250 := log_le_div_250_sqrt hn
  let k : ℕ := Nat.ceil (100 * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
  have hk_ge_real : 100 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hk_le_real : (k : ℝ) ≤ 101 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    have hlt : (k : ℝ) < 100 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hprod_ge : (1 : ℝ) ≤ Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by nlinarith
    linarith
  have hk_ge2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ (k : ℝ) := by nlinarith
    exact_mod_cast this
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hn_pos)
  have hk_lt_n : k < n := by
    have hkn : (k : ℝ) < (n : ℝ) := by
      calc (k : ℝ) ≤ 101 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := hk_le_real
        _ ≤ 101 * Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) / 250) := by gcongr
        _ = (101 / 250 : ℝ) * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        _ = (101 / 250 : ℝ) * (n : ℝ) := by rw [hsq]
        _ < (n : ℝ) := by linarith
    exact_mod_cast hkn
  obtain ⟨ω, htri_ω, hind_ω⟩ := exists_good_edges n k hn hk_ge2 (le_of_lt hk_lt_n) hk_ge_real
  obtain ⟨G, hω_eq, hχ_div⟩ := graph_from_good_edges n k (by omega) hk_lt_n ω htri_ω hind_ω
  refine ⟨G, hω_eq, le_trans ?_ hχ_div⟩
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := by positivity
  rw [div_le_div_iff₀ hlog_pos hk_pos_real]
  calc (1 / 101 : ℝ) * Real.sqrt (n : ℝ) * (k : ℝ)
      ≤ (1 / 101 : ℝ) * Real.sqrt (n : ℝ) * (101 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hk_le_real (by positivity)
    _ = (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) * Real.log (n : ℝ) := by ring
    _ = (n : ℝ) * Real.log (n : ℝ) := by rw [hsq]

end GraphApplication

end OMA_Erdos627_1961

theorem OMA.solution : type_of% @Erdos627.erdos_627.variants.erdos_1961 := by
  refine ⟨1 / 101, by norm_num, ?_⟩
  rw [Filter.eventually_atTop]
  exact ⟨1000 ^ 4, fun n hn => OMA_Erdos627_1961.graphOf_exists n hn⟩
