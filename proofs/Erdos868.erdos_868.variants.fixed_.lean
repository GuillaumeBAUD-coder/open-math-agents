import FormalConjectures.ErdosProblems.«868»
import Mathlib

/-! A minimal subbasis obtained by staged deletions. -/

open Finset Filter
open scoped BigOperators Classical Topology

namespace OMA868

noncomputable section

private def avg (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ a, f a) / 2^n

private lemma avg_nonneg {f : (Fin n → Bool) → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ avg f :=
  div_nonneg (sum_nonneg fun a _ => h a) (by positivity)

private lemma avg_mono {f g : (Fin n → Bool) → ℝ} (h : ∀ a, f a ≤ g a) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (by positivity)

private lemma avg_const (n : ℕ) (c : ℝ) : avg (fun _ : Fin n → Bool => c) = c := by
  unfold avg
  have h : (2:ℝ)^n ≠ 0 := by positivity
  simp [Fintype.card_fin, Fintype.card_bool, h]

private lemma avg_sub {f g : (Fin n → Bool) → ℝ} :
    avg (fun a => f a-g a) = avg f-avg g := by simp [avg,sum_sub_distrib,sub_div]

private lemma avg_succ (f : (Fin (n+1) → Bool) → ℝ) :
    avg f = (avg (fun a => f (Fin.cons false a))+avg (fun a => f (Fin.cons true a)))/2 := by
  unfold avg
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  change ((∑ a, f (Fin.cons true a)) + ∑ a, f (Fin.cons false a)) / 2^(n+1) = _
  rw [pow_succ]
  ring

private lemma prod_avg_single {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, f i ≠ g i → f j ≠ g j → i = j) :
    (∏ i ∈ s, (f i + g i)/2) = ((∏ i ∈ s, f i)+(∏ i ∈ s, g i))/2 := by
  by_cases he : ∃ i ∈ s, f i ≠ g i
  · obtain ⟨i, hi, hfg⟩ := he
    have hh (j : ι) (hj : j ∈ s.erase i) : f j = g j := by
      by_contra! hne
      exact (mem_erase.1 hj).1 (h j (mem_erase.1 hj).2 i hi hne hfg)
    rw [← prod_erase_mul _ _ hi, ← prod_erase_mul s f hi, ← prod_erase_mul s g hi]
    have h₁ : (∏ j ∈ s.erase i, (f j+g j)/2) = ∏ j ∈ s.erase i, f j := by
      apply prod_congr rfl
      intro j hj
      rw [← hh j hj]
      ring
    rw [h₁, show (∏ j ∈ s.erase i, g j) = ∏ j ∈ s.erase i, f j from
      prod_congr rfl fun j hj => (hh j hj).symm]
    ring
  · push Not at he
    rw [show (∏ j ∈ s, g j) = ∏ j ∈ s, f j from prod_congr rfl fun j hj => (he j hj).symm]
    rw [show (∏ j ∈ s, (f j+g j)/2) = ∏ j ∈ s, f j from prod_congr rfl fun j hj => by
      rw [← he j hj]
      ring]
    ring

private lemma prod_avg_opposite {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hp : ∀ i j, f i < g i → f j < g j → i = j)
    (hm : ∀ i j, g i < f i → g j < f j → i = j) :
    ((∏ i, f i)+(∏ i, g i))/2 ≤ ∏ i, (f i+g i)/2 := by
  let s := univ.filter fun i => f i ≤ g i
  let t := univ.filter fun i => ¬ f i ≤ g i
  have hs := prod_avg_single s f g (fun i hi j hj hi' hj' =>
    hp i j (lt_of_le_of_ne (mem_filter.1 hi).2 hi') (lt_of_le_of_ne (mem_filter.1 hj).2 hj'))
  have ht := prod_avg_single t f g (fun i hi j hj _ _ =>
    hm i j (lt_of_not_ge (mem_filter.1 hi).2) (lt_of_not_ge (mem_filter.1 hj).2))
  have hfg : (∏ i ∈ s, f i) ≤ ∏ i ∈ s, g i :=
    prod_le_prod (fun i _ => hf i) fun i hi => (mem_filter.1 hi).2
  have hgf : (∏ i ∈ t, g i) ≤ ∏ i ∈ t, f i :=
    prod_le_prod (fun i _ => hg i) fun i hi => (lt_of_not_ge (mem_filter.1 hi).2).le
  rw [← prod_filter_mul_prod_filter_not univ (fun i => f i ≤ g i) f,
    ← prod_filter_mul_prod_filter_not univ (fun i => f i ≤ g i) g,
    ← prod_filter_mul_prod_filter_not univ (fun i => f i ≤ g i) (fun i => (f i+g i)/2)]
  change ((∏ i ∈ s, f i)*(∏ i ∈ t, f i) + (∏ i ∈ s, g i)*(∏ i ∈ t, g i))/2 ≤
    (∏ i ∈ s, (f i+g i)/2)*(∏ i ∈ t, (f i+g i)/2)
  rw [hs,ht]
  nlinarith only [mul_nonneg (sub_nonneg.2 hfg) (sub_nonneg.2 hgf)]

private def choices {V : Type*} [DecidableEq V] (f : Fin n → Bool → V)
    (a : Fin n → Bool) : Finset V := univ.image fun i => f i (a i)

private def hit {V : Type*} [DecidableEq V] (E D : Finset V) : ℝ :=
  if Disjoint E D then 0 else 1

private lemma hit_nonneg {V : Type*} [DecidableEq V] (E D : Finset V) : 0 ≤ hit E D := by
  unfold hit
  split <;> norm_num

private lemma hit_insert_eq_of_notMem {V : Type*} [DecidableEq V]
    {E D : Finset V} {x : V} (hx : x ∉ E) : hit E (insert x D) = hit E D := by
  have hh : Disjoint E (insert x D) ↔ Disjoint E D := by
    simp [disjoint_insert_right,hx]
  simp [hit,hh]

private lemma hit_ge_insert {V : Type*} [DecidableEq V]
    (E D : Finset V) (x : V) : hit E D ≤ hit E (insert x D) := by
  by_cases hd : Disjoint E (insert x D)
  · simp [hit, hd, hd.mono_right (subset_insert _ _)]
  · simpa [hit,hd] using (show hit E D ≤ 1 by unfold hit; split <;> norm_num)

private lemma choices_cons {V : Type*} [DecidableEq V] (f : Fin (n+1) → Bool → V)
    (b : Bool) (a : Fin n → Bool) :
    choices f (Fin.cons b a) = insert (f 0 b) (choices (fun i => f i.succ) a) := by
  ext x
  simp only [choices,mem_image,mem_univ,true_and,mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    induction i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ i => exact Or.inr ⟨i,rfl⟩
  · rintro (rfl|⟨i,rfl⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨i.succ,rfl⟩

/-- When each choice selects one of two points, disjoint sets have
nonpositively correlated events of being hit by the selected points. -/
private lemma paired_hits {V ι : Type*} [DecidableEq V] [Fintype ι]
    (E : ι → Finset V) (hE : Pairwise fun i j => Disjoint (E i) (E j)) :
    ∀ n (f : Fin n → Bool → V) (D : Finset V),
      avg (fun a => ∏ i, hit (E i) (D ∪ choices f a)) ≤
        ∏ i, avg (fun a => hit (E i) (D ∪ choices f a)) := by
  intro n
  induction n with
  | zero =>
    intro f D
    have hc (a : Fin 0 → Bool) : choices f a = ∅ := by simp [choices]
    simp [hc,avg_const]
  | succ n ih =>
    intro f D
    let F (i : Fin n) := f i.succ
    let A (b : Bool) (i : ι) := avg (fun a => hit (E i) (insert (f 0 b) D ∪ choices F a))
    have he (b : Bool) (a : Fin n → Bool) :
        D ∪ choices f (Fin.cons b a) = insert (f 0 b) D ∪ choices F a := by
      rw [choices_cons]
      ext x
      simp [F,or_left_comm]
    have hn (b : Bool) (i : ι) : 0 ≤ A b i := avg_nonneg fun _ => hit_nonneg _ _
    have href (b d : Bool) (i : ι) (h : f 0 b ∉ E i) : A b i ≤ A d i := by
      apply avg_mono
      intro a
      rw [insert_union,insert_union,hit_insert_eq_of_notMem h]
      exact hit_ge_insert _ _ _
    have huniq (b : Bool) (i j : ι) (hi : f 0 b ∈ E i) (hj : f 0 b ∈ E j) : i=j := by
      by_contra! hn
      exact disjoint_left.1 (hE hn) hi hj
    have he' (i : ι) : avg (fun a => hit (E i) (D ∪ choices f a)) =
        (A false i + A true i)/2 := by rw [avg_succ]; simp only [he,A]
    simp_rw [he']
    rw [avg_succ]
    simp_rw [he]
    refine (div_le_div_of_nonneg_right (add_le_add (ih F _) (ih F _)) (by norm_num)).trans ?_
    apply prod_avg_opposite (A false) (A true) (hn false) (hn true)
    · intro i j hi hj
      exact huniq true i j (by contrapose! hi; exact href true false i hi)
        (by contrapose! hj; exact href true false j hj)
    · intro i j hi hj
      exact huniq false i j (by contrapose! hi; exact href false true i hi)
        (by contrapose! hj; exact href false true j hj)


private lemma avg_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin n → Bool) → ℝ) :
    avg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avg (f i) := by
  unfold avg
  rw [← sum_div, sum_comm]

private lemma avg_mul_left (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    avg (fun a => c*f a) = c*avg f := by
  unfold avg
  rw [← mul_sum,mul_div_assoc]

private lemma avg_prod_coords (n : ℕ) (w : Fin n → Bool → ℝ) :
    avg (fun a => ∏ i, w i (a i)) = ∏ i, (w i false+w i true)/2 := by
  induction n with
  | zero => simp [avg_const]
  | succ n ih =>
    rw [avg_succ,Fin.prod_univ_succ]
    simp_rw [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,avg_mul_left]
    rw [ih]
    ring

private lemma avg_hit_le {V : Type*} [DecidableEq V]
    (f : Fin n → Bool → V) (hf : Function.Injective (fun p : Fin n × Bool => f p.1 p.2))
    (E : Finset V) (hE : E.card ≤ 2)
    (hno : ∀ i, ¬ (f i false ∈ E ∧ f i true ∈ E)) :
    avg (fun a => hit E (choices f a)) ≤ 3/4 := by
  let w (i : Fin n) (b : Bool) : ℝ := if f i b ∈ E then 0 else 1
  have hpro (a : Fin n → Bool) : 1-hit E (choices f a) = ∏ i, w i (a i) := by
    by_cases hh : Disjoint E (choices f a)
    · rw [hit,if_pos hh,sub_zero]
      symm
      apply prod_eq_one
      intro i hi
      have hnot : f i (a i) ∉ E := fun he => disjoint_left.1 hh he
        (mem_image.2 ⟨i,mem_univ _,rfl⟩)
      simp [w,hnot]
    · rw [hit,if_neg hh,sub_self]
      symm
      rw [Finset.not_disjoint_iff] at hh
      obtain ⟨x,hx,hx'⟩ := hh
      obtain ⟨i,_,rfl⟩ := mem_image.1 hx'
      exact prod_eq_zero (mem_univ i) (by simp [w,hx])
  let s := (univ : Finset (Fin n)).filter fun i => ∃ b, f i b ∈ E
  have hs : s.card ≤ E.card := by
    have hex : ∀ i : s, ∃ b, f i b ∈ E := fun i => (mem_filter.1 i.property).2
    choose b hb using hex
    simpa using Fintype.card_le_of_injective (fun i : s => (⟨f i (b i),hb i⟩ : E))
      (fun i j h => Subtype.ext (congrArg Prod.fst (hf (a₁ := (i.val,b i)) (a₂ := (j.val,b j))
        (congrArg Subtype.val h))))
  have hterm (i : Fin n) : (w i false+w i true)/2 = if i ∈ s then 1/2 else 1 := by
    by_cases h₁ : f i false ∈ E <;> by_cases h₂ : f i true ∈ E
    · exact (hno i ⟨h₁,h₂⟩).elim
    · have hi : i ∈ s := mem_filter.2 ⟨mem_univ _,false,h₁⟩
      norm_num [w,h₁,h₂,hi]
    · have hi : i ∈ s := mem_filter.2 ⟨mem_univ _,true,h₂⟩
      norm_num [w,h₁,h₂,hi]
    · have hi : i ∉ s := by simp [s,Bool.exists_bool,h₁,h₂]
      norm_num [w,h₁,h₂,hi]
  have hp : avg (fun a => ∏ i, w i (a i)) = (1/2)^s.card := by
    rw [avg_prod_coords]
    simp_rw [hterm]
    rw [Finset.prod_ite]
    simp [s]
  have hav : 1-avg (fun a => hit E (choices f a)) = (1/2)^s.card := by
    nth_rw 1 [← avg_const n 1]
    rw [← avg_sub, ← hp]
    congr 1
    funext a
    exact hpro a
  have hlow : (1:ℝ)/4 ≤ (1/2)^s.card := by
    have hh : (1/2 : ℝ)^2 ≤ (1/2)^s.card := pow_le_pow_of_le_one (by norm_num)
      (by norm_num) (hs.trans hE)
    norm_num at hh ⊢
    exact hh
  linarith

private lemma no_failure {n w : ℕ} (bad : ℕ → (Fin n → Bool) → Prop) [∀ m a, Decidable (bad m a)]
    (hw : ∀ m a, bad m a → w ≤ m) (g : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m)
    (hgs : Summable g) (hgt : (∑' m, g (m+w)) < 1)
    (havg : ∀ m ≥ w, avg (fun a => if bad m a then 1 else 0) ≤ g m) :
    ∃ a, ∀ m, ¬bad m a := by
  by_contra! h
  choose b hb using h
  let S := univ.image fun a => b a - w
  have heq (a : Fin n → Bool) : b a-w+w = b a := Nat.sub_add_cancel (hw _ _ (hb a))
  have hl (a : Fin n → Bool) :
      (1:ℝ) ≤ ∑ m ∈ S, if bad (m+w) a then 1 else 0 := by
    have hm : b a - w ∈ S := mem_image.2 ⟨a,mem_univ _,rfl⟩
    calc
      _ = (if bad ((b a-w)+w) a then (1:ℝ) else 0) := by simp [heq,hb]
      _ ≤ _ := single_le_sum (f := fun m => if bad (m+w) a then (1:ℝ) else 0)
        (fun i _ => by split <;> norm_num) hm
  have hs : Summable (fun m => g (m+w)) := hgs.comp_injective fun i j hij => Nat.add_right_cancel hij
  have hc := avg_mono hl
  rw [avg_const,avg_sum] at hc
  exact (hc.trans ((sum_le_sum fun m _ => havg _ (by omega)).trans
    (hs.sum_le_tsum S (fun m _ => hg _)))).not_gt hgt


open scoped Pointwise

private def reps (B : Set ℕ) (m : ℕ) : Finset ℕ :=
  (range (m/2+1)).filter fun a => a ∈ B ∧ m-a ∈ B

private def ends (m a : ℕ) : Finset ℕ := {a,m-a}

private lemma mem_reps {B : Set ℕ} {m a : ℕ} :
    a ∈ reps B m ↔ a ≤ m/2 ∧ a ∈ B ∧ m-a ∈ B := by
  simp [reps]

private lemma ends_bound {B : Set ℕ} {m a x : ℕ}
    (ha : a ∈ reps B m) (hx : x ∈ ends m a) : x ≤ m := by
  have h := (mem_reps.1 ha).1
  simp [ends] at hx
  rcases hx with rfl|rfl <;> omega

private lemma ends_subset {B : Set ℕ} {m a : ℕ} (ha : a ∈ reps B m) :
    (ends m a : Set ℕ) ⊆ B := by
  have h := (mem_reps.1 ha).2
  intro x hx
  simp [ends] at hx
  rcases hx with rfl|rfl <;> tauto

private lemma reps_mono {B C : Set ℕ} (h : B ⊆ C) (m : ℕ) : reps B m ⊆ reps C m := by
  intro a ha
  obtain ⟨ha,h₁,h₂⟩ := mem_reps.1 ha
  exact mem_reps.2 ⟨ha,h h₁,h h₂⟩

private lemma ends_disjoint {m a b : ℕ}
    (ha : a ≤ m/2) (hb : b ≤ m/2) (hne : a ≠ b) :
    Disjoint (ends m a) (ends m b) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp [ends] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with h|h <;> omega

private lemma reps_nonempty_iff {B : Set ℕ} {m : ℕ} : (reps B m).Nonempty ↔ m ∈ B+B := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨ha,h₁,h₂⟩ := mem_reps.1 ha
    exact ⟨a,h₁,m-a,h₂,by change a+(m-a)=m; omega⟩
  · rintro ⟨a,ha,b,hb,rfl⟩
    change (reps B (a+b)).Nonempty
    obtain h|h := le_total a b
    · exact ⟨a,mem_reps.2 ⟨by omega,ha,by simpa using hb⟩⟩
    · refine ⟨b,mem_reps.2 ⟨by omega,hb,?_⟩⟩
      simpa [add_comm a b] using ha

private lemma reps_count (B : Set ℕ) (m : ℕ) :
    (reps B m).card = Erdos868.ncard_add_repr B 2 m := by
  unfold Erdos868.ncard_add_repr
  rw [← Nat.card_coe_set_eq, ← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  refine
    { toFun := fun a => ⟨![a.val,m-a.val],?_⟩
      invFun := fun f => ⟨f.val 0,?_⟩
      left_inv := fun a => Subtype.ext (by rfl)
      right_inv := fun f => Subtype.ext (by
        funext i
        fin_cases i
        · rfl
        · have h := f.property.2.2
          rw [Fin.sum_univ_two] at h
          change m-f.val 0 = f.val 1
          omega) }
  · obtain ⟨ha,h₁,h₂⟩ := mem_reps.1 a.property
    refine ⟨?_,?_,?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all; omega
    · rintro _ ⟨i,rfl⟩
      fin_cases i <;> assumption
    · rw [Fin.sum_univ_two]
      change a.val+(m-a.val)=m
      omega
  · have hf := f.property.2.2
    rw [Fin.sum_univ_two] at hf
    have hmono := f.property.1 (show (0:Fin 2) ≤ 1 by decide)
    have hmem (i : Fin 2) : f.val i ∈ B := f.property.2.1 ⟨i,rfl⟩
    exact mem_reps.2 ⟨by omega,hmem 0,by
      convert hmem 1 using 1
      omega⟩

private lemma reps_delete {B : Set ℕ} {D : Finset ℕ} {m a : ℕ}
    (hm : a ∈ reps B m) :
    a ∈ reps (B \ (D : Set ℕ)) m ↔ Disjoint (ends m a) D := by
  obtain ⟨ha,h₁,h₂⟩ := mem_reps.1 hm
  simp [mem_reps,ha,h₁,h₂,ends,disjoint_insert_left]

private lemma reps_delete_loss (B : Set ℕ) (D : Finset ℕ) (m : ℕ) :
    (reps B m).card ≤ (reps (B \ (D : Set ℕ)) m).card + D.card := by
  let R := reps B m
  let S := reps (B \ (D : Set ℕ)) m
  have hsub : S ⊆ R := reps_mono Set.sdiff_subset _
  have hf (a : ↥(R \ S)) : ∃ x, x ∈ ends m a.val ∧ x ∈ D := by
    obtain ⟨ha,ha'⟩ := mem_sdiff.1 a.property
    exact not_disjoint_iff.1 (fun h => ha' ((reps_delete ha).2 h))
  choose f hf using hf
  have hc : (R \ S).card ≤ D.card := by
    simpa using Fintype.card_le_of_injective (fun a : ↥(R \ S) => (⟨f a,(hf a).2⟩ : D))
      (fun a b he => by
        apply Subtype.ext
        by_contra! hne
        have hdis := ends_disjoint (mem_reps.1 (mem_sdiff.1 a.property).1).1
          (mem_reps.1 (mem_sdiff.1 b.property).1).1 hne
        have hh : f a = f b := congrArg Subtype.val he
        exact disjoint_left.1 hdis (hf a).1 (hh ▸ (hf b).1))
  have heq := card_sdiff_add_card_eq_card hsub
  change R.card ≤ S.card+D.card
  omega

private lemma no_both_of_sum_ne {m q u a : ℕ} (hm : u ≤ m/2) (ha : a < q/2+1)
    (hne : a ≠ q-a) (hqm : m ≠ q) :
    ¬ (a ∈ ends m u ∧ q-a ∈ ends m u) := by
  intro ⟨h₁,h₂⟩
  simp [ends] at h₁ h₂
  rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;> omega

private lemma select_deletions (B : Set ℕ) (q w : ℕ) (P : Finset ℕ)
    (hP : P ⊆ reps B q) (hnd : ∀ a ∈ P, a ≠ q-a)
    (g : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m) (hgs : Summable g)
    (hgt : (∑' m, g (m+w)) < 1)
    (hr : ∀ m ≥ w, m ≠ q → (3/4 : ℝ)^(reps B m).card ≤ g m) :
    ∃ D : Finset ℕ, (∀ x ∈ D, ∃ a ∈ P, x ∈ ends q a) ∧
      (∀ a ∈ P, ¬ Disjoint (ends q a) D) ∧
      ∀ m ≥ w, m ≠ q → (reps (B \ (D : Set ℕ)) m).Nonempty := by
  let e := (Fintype.equivFinOfCardEq (Fintype.card_coe P)).symm
  let f (i : Fin P.card) (b : Bool) := if b then q-(e i).val else (e i).val
  have hf (i : Fin P.card) (b : Bool) : f i b ∈ ends q (e i).val := by
    cases b <;> simp [f,ends]
  have hp (i : Fin P.card) : (e i).val ≤ q/2 := (mem_reps.1 (hP (e i).property)).1
  have hfi : Function.Injective (fun p : Fin P.card × Bool => f p.1 p.2) := by
    rintro ⟨i,b⟩ ⟨j,d⟩ hh
    change f i b = f j d at hh
    have hij : i=j := by
      by_contra! hne
      have hne' : (e i).val ≠ (e j).val := fun eq => hne (e.injective (Subtype.ext eq))
      exact disjoint_left.1 (ends_disjoint (hp i) (hp j) hne') (hf i b) (hh ▸ hf j d)
    subst j
    have hne := hnd (e i).val (e i).property
    cases b <;> cases d <;> simp [f] at hh ⊢
    · exact (hne hh).elim
    · exact (hne hh.symm).elim
  let bad (m : ℕ) (c : Fin P.card → Bool) := w ≤ m ∧ m ≠ q ∧
    ¬ (reps (B \ (choices f c : Set ℕ)) m).Nonempty
  have hb (m : ℕ) (hm : w ≤ m) : avg (fun a => if bad m a then 1 else 0) ≤ g m := by
    by_cases hmq : m=q
    · simpa [bad,hmq,avg_const] using hg m
    let E (a : ↥(reps B m)) := ends m a.val
    have hEm (a : ↥(reps B m)) := (mem_reps.1 a.property).1
    have hE : Pairwise fun i j => Disjoint (E i) (E j) :=
      fun i j hne => ends_disjoint (hEm i) (hEm j) (fun h => hne (Subtype.ext h))
    have hform (c : Fin P.card → Bool) :
        (if bad m c then (1:ℝ) else 0) = ∏ i, hit (E i) (choices f c) := by
      by_cases hh : (reps (B \ (choices f c : Set ℕ)) m).Nonempty
      · rw [if_neg (fun h : bad m c => h.2.2 hh)]
        obtain ⟨a,ha⟩ := hh
        have ha' := reps_mono Set.sdiff_subset m ha
        symm
        apply prod_eq_zero (mem_univ (⟨a,ha'⟩ : ↥(reps B m)))
        change hit (ends m a) (choices f c) = 0
        simp [hit,(reps_delete ha').1 ha]
      · rw [if_pos ⟨hm,hmq,hh⟩]
        symm
        apply prod_eq_one
        intro i hi
        have hnot : ¬ Disjoint (E i) (choices f c) := fun hd =>
          hh ⟨i.val,(reps_delete i.property).2 hd⟩
        simp [hit,hnot]
    simp_rw [hform]
    calc
      _ ≤ ∏ i, avg (fun a => hit (E i) (choices f a)) := by
        simpa using paired_hits E hE P.card f ∅
      _ ≤ ∏ _ : ↥(reps B m), (3/4:ℝ) := by
        apply prod_le_prod (fun i _ => avg_nonneg fun _ => hit_nonneg _ _)
        intro i hi
        refine avg_hit_le f hfi _ ((card_insert_le _ _).trans (by simp)) ?_
        intro j
        simpa [f,E] using no_both_of_sum_ne (hEm i) (Nat.lt_succ_of_le (hp j))
          (hnd (e j).val (e j).property) hmq
      _ ≤ g m := by
        simpa only [prod_const,Fintype.card_coe,card_univ] using hr m hm hmq
  obtain ⟨c,hc⟩ := no_failure bad (fun _ _ h => h.1) g hg hgs hgt hb
  refine ⟨choices f c,?_,?_,?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.1 hx
    exact ⟨(e i).val,(e i).property,hf i (c i)⟩
  · intro a ha hd
    let i := e.symm ⟨a,ha⟩
    have hi : (e i).val = a := by simp [i]
    have hmem : f i (c i) ∈ ends q a := hi ▸ hf i (c i)
    exact disjoint_left.1 hd hmem (mem_image.2 ⟨i,mem_univ _,rfl⟩)
  · intro m hm hmq
    by_contra h
    exact hc m ⟨hm,hmq,h⟩


private lemma reps_congr_below {A B : Set ℕ} {m : ℕ}
    (h : ∀ x ≤ m, x ∈ A ↔ x ∈ B) : reps A m = reps B m := by
  ext x
  simp only [mem_reps]
  constructor <;> rintro ⟨hx,hx',hy'⟩
  · exact ⟨hx,(h x (by omega)).1 hx',(h _ (Nat.sub_le _ _)).1 hy'⟩
  · exact ⟨hx,(h x (by omega)).2 hx',(h _ (Nat.sub_le _ _)).2 hy'⟩

private lemma power_decay {c : ℝ} {m r : ℕ} (hm : 0 < m)
    (hr : c*Real.log m ≤ (r:ℝ)) :
    (3/4:ℝ)^r ≤ (m:ℝ)^(-(c*Real.log (4/3))) := by
  have hl : Real.log (3/4:ℝ) = -Real.log (4/3:ℝ) := by
    rw [← Real.log_inv]
    congr 1
    norm_num
  have hp : 0 ≤ Real.log (4/3:ℝ) := Real.log_nonneg (by norm_num)
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3/4),
    Real.rpow_def_of_pos (by exact_mod_cast hm),hl]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hr hp
  linarith only [hh]

private lemma eventually_small_tail (g : ℕ → ℝ) (hg : Summable g) :
    ∀ᶠ w in atTop, (∑' m, g (m+w)) < 1 := by
  have hs : Tendsto (fun w => ∑' m, g (m+w)) atTop (𝓝 0) := by
    have he (w : ℕ) : (∑' m,g (m+w)) = (∑' m,g m) - ∑ i ∈ range w,g i := by
      linarith [hg.sum_add_tsum_nat_add w]
    simp_rw [he]
    have hconst : Tendsto (fun _ : ℕ => ∑' m,g m) atTop (𝓝 (∑' m,g m)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hg.hasSum.tendsto_sum_nat
  exact hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))

private lemma enough_reps {A B : Set ℕ} {K : ℕ} {c e : ℝ}
    (hc : e < c) (hB : ∀ x > K, x ∈ A → x ∈ B)
    (hA : ∀ᶠ m : ℕ in atTop, c*Real.log m < ((reps A m).card:ℝ)) :
    ∀ C : ℝ, ∀ᶠ m : ℕ in atTop, e*Real.log m+C ≤ ((reps B m).card:ℝ) := by
  intro C
  have hneg := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    ((C+(K+1))/(c-e))
  have hsub : A \ (Iic K : Finset ℕ) ⊆ B := by
    intro x hx
    apply hB x _ hx.1
    simpa using hx.2
  filter_upwards [hA,hneg] with m hm hm'
  have hl := reps_delete_loss A (Iic K) m
  have hb := (card_le_card (reps_mono hsub m))
  have hcount : ((reps A m).card:ℝ) ≤ ((reps B m).card:ℝ)+((K+1:ℕ):ℝ) := by
    exact_mod_cast (hl.trans (by simpa using Nat.add_le_add_right hb (K+1)))
  have hp : C+(K+1:ℕ) ≤ (c-e)*Real.log m := by
    push_cast
    exact ((div_le_iff₀ (sub_pos.mpr hc)).1 hm').trans_eq (mul_comm _ _)
  linarith

/-- One stage protects the initial interval up to K and fixes a new large
integer with exactly one representation, using the designated summand. -/
private lemma sparse_stage {A B : Set ℕ} {K N d : ℕ} {c e : ℝ}
    (hc : e < c) (he : 1 < e*Real.log (4/3))
    (hA : ∀ᶠ m : ℕ in atTop, c*Real.log m < ((reps A m).card:ℝ))
    (hTail : ∀ x > K, x ∈ A → x ∈ B)
    (hBasis : ∀ m ≥ N, (reps B m).Nonempty) (hd : d ∈ B) (hdK : d ≤ K) :
    ∃ q > K, ∃ B' ⊆ B,
      (∀ x ≤ K, x∈B' ↔ x∈B) ∧ (∀ x > q, x∈A → x∈B') ∧
      (∀ m ≥ N, (reps B' m).Nonempty) ∧ reps B' q = {d} := by
  let g (m : ℕ) : ℝ := (m:ℝ)^(-(e*Real.log (4/3)))
  have hg (m : ℕ) : 0 ≤ g m := Real.rpow_nonneg (by positivity) _
  have hsum : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  obtain ⟨w,hw⟩ := eventually_atTop.1 <|
    (eventually_ge_atTop K).and <| (eventually_ge_atTop (1:ℕ)).and <|
      (eventually_small_tail g hsum).and <| enough_reps hc hTail hA 0
  -- Keep the same threshold for the bounded interval and the probability tail.
  obtain ⟨hwK',hw1,htw,_⟩ := hw w le_rfl
  have hB₁ : ∀ m ≥ w, e*Real.log m ≤ ((reps B m).card:ℝ) := by
    intro m hm
    simpa using (hw m hm).2.2.2
  obtain ⟨R,hR⟩ := eventually_atTop.1 (enough_reps hc hTail hA (w+2))
  let T := 2*(R+w+K+N+1)
  have ht₀ : N ≤ 2*T+1 := by dsimp [T]; omega
  obtain ⟨a,ha⟩ := hBasis (2*T+1) ht₀
  let b := (2*T+1)-a
  have hbd : b ∈ B := (mem_reps.1 ha).2.2
  have hbT : T < b := by
    have hh := (mem_reps.1 ha).1
    dsimp [b]
    omega
  let q := d+b
  have hbT' : 2*(R+w+K+N+1) < b := hbT
  have hqK : K < q := by dsimp [q]; omega
  have hq2 : 2*w < q := by dsimp [q]; omega
  have hqR : R ≤ q/2 := by dsimp [q]; omega
  have hqN : N ≤ q := by dsimp [q]; omega
  have hqb : q-d = b := by simp [q]
  have hdouble : q/2 ≠ b := by dsimp [q]; omega
  let F := insert (q/2) (((Iic w).image (fun a => q-a)).erase b)
  have hFcard : F.card ≤ w+2 := by
    calc
      _ ≤ (((Iic w).image (fun a => q-a)).erase b).card + 1 := card_insert_le _ _
      _ ≤ (Iic w).card + 1 :=
        Nat.add_le_add_right ((card_le_card (erase_subset _ _)).trans card_image_le) _
      _ = _ := by simp
  have hF (x : ℕ) (hx : x ∈ F) : w < x ∧ R ≤ x ∧ x ≤ q ∧ x ≠ b := by
    rcases mem_insert.1 hx with rfl|hx
    · exact ⟨by omega,hqR,by omega,hdouble⟩
    · obtain ⟨hne,hm⟩ := mem_erase.1 hx
      obtain ⟨a,ha,rfl⟩ := mem_image.1 hm
      have ha' := mem_Iic.1 ha
      exact ⟨by omega,by omega,Nat.sub_le _ _,hne⟩
  let C := B \ (F : Set ℕ)
  have hcB : C ⊆ B := Set.sdiff_subset
  have hdC : d ∈ C := ⟨hd,fun hf => by have := (hF _ hf).1; omega⟩
  have hbC : b ∈ C := ⟨hbd,fun hf => (hF _ hf).2.2.2 rfl⟩
  have hdq : d ∈ reps C q := mem_reps.2 ⟨by omega,hdC,hqb ▸ hbC⟩
  let P := (reps C q).erase d
  have hP : P ⊆ reps C q := erase_subset _ _
  have hPwide (a : ℕ) (ha : a ∈ P) : w < a := by
    obtain ⟨ha₀,ha₁⟩ := mem_erase.1 ha
    obtain ⟨h,qA,qB⟩ := mem_reps.1 ha₁
    by_contra! hw
    have hh : q-a ≠ b := by omega
    exact qB.2 (mem_insert_of_mem (mem_erase.2 ⟨hh,mem_image.2 ⟨a,mem_Iic.2 hw,rfl⟩⟩))
  have hPnot (a : ℕ) (ha : a ∈ P) : a ≠ q-a := by
    intro h
    have hhalf : a = q/2 := by have := (mem_reps.1 (hP ha)).1; omega
    exact ((mem_reps.1 (hP ha)).2.1).2 (hhalf ▸ mem_insert_self _ _)
  have hClarge (m : ℕ) (hm : w ≤ m) : e*Real.log m ≤ ((reps C m).card:ℝ) := by
    by_cases hr : R ≤ m
    · have hl := reps_delete_loss B F m
      have hh : ((reps B m).card:ℝ) ≤ ((reps C m).card:ℝ)+(F.card:ℝ) := by exact_mod_cast hl
      have hh' : (F.card:ℝ) ≤ w+2 := by exact_mod_cast hFcard
      linarith [hR m hr]
    · have hsame : reps C m = reps B m := reps_congr_below fun x hx =>
        ⟨fun h => h.1,fun h => ⟨h,fun hf => hr ((hF x hf).2.1.trans hx)⟩⟩
      rw [hsame]
      exact hB₁ m hm
  obtain ⟨D,hD,hDhit,hDkeep⟩ := select_deletions C q w P hP hPnot g hg hsum htw
    (fun m hm _ => power_decay (by omega) (hClarge m hm))
  let B' := C \ (D : Set ℕ)
  have hDB (x : ℕ) (hx : x ∈ D) : w < x ∧ x ≤ q := by
    obtain ⟨a,ha,hxA⟩ := hD x hx
    have ha' := (mem_reps.1 (hP ha)).1
    have ha'' := hPwide a ha
    simp [ends] at hxA
    rcases hxA with rfl|rfl <;> omega
  have hearly (x : ℕ) (hx : x ≤ w) : x ∈ B' ↔ x ∈ B :=
    ⟨fun h => h.1.1,fun h => ⟨⟨h,fun hf => (not_lt_of_ge hx) (hF x hf).1⟩,
      fun hf => (not_lt_of_ge hx) (hDB x hf).1⟩⟩
  have hkeepd : d ∈ reps B' q := by
    apply (reps_delete hdq).2
    rw [disjoint_left]
    intro x hx hd'
    obtain ⟨a,ha,hxa⟩ := hD x hd'
    have hne : d ≠ a := Ne.symm (mem_erase.1 ha).1
    exact disjoint_left.1 (ends_disjoint (mem_reps.1 hdq).1 (mem_reps.1 (hP ha)).1 hne) hx hxa
  have huniq : reps B' q = {d} := by
    ext a
    simp only [mem_singleton]
    refine ⟨fun ha => ?_,fun h => h.symm ▸ hkeepd⟩
    have hc := reps_mono (Set.sdiff_subset : B' ⊆ C) _ ha
    by_contra! hne
    exact hDhit a (mem_erase.2 ⟨hne,hc⟩) ((reps_delete hc).1 ha)
  refine ⟨q,hqK,B',Set.sdiff_subset.trans hcB,fun x hx => hearly x (hx.trans hwK'),
    ?_,?_,huniq⟩
  · intro x hx hxA
    exact ⟨⟨hTail x (hqK.trans hx) hxA,fun hf => (not_le_of_gt hx) (hF x hf).2.2.1⟩,
      fun hf => (not_le_of_gt hx) (hDB x hf).2⟩
  · intro m hm
    by_cases hmq : m=q
    · exact ⟨d, hmq ▸ hkeepd⟩
    by_cases hm' : w ≤ m
    · exact hDkeep m hm' hmq
    rw [reps_congr_below (B := B) (fun x hx => hearly x (by omega))]
    exact hBasis m hm


private structure State (A : Set ℕ) (N t : ℕ) where
  carrier : Set ℕ
  cutoff : ℕ
  cutoff_ge : t ≤ cutoff
  subset : carrier ⊆ A
  tail : ∀ x > cutoff, x∈A → x∈carrier
  basis : ∀ m ≥ N, (reps carrier m).Nonempty

private structure Transition {A : Set ℕ} {N t : ℕ} (B : State A N t) where
  next : State A N (t+1)
  advance : B.cutoff < next.cutoff
  subset : next.carrier ⊆ B.carrier
  frozen : ∀ x ≤ B.cutoff, x∈next.carrier ↔ x∈B.carrier
  unique : (Nat.unpair t).1 ∈ B.carrier → reps next.carrier next.cutoff = {(Nat.unpair t).1}

private lemma transition_exists {A : Set ℕ} {N t : ℕ} {c e : ℝ}
    (hc : e < c) (he : 1 < e*Real.log (4/3))
    (hA : ∀ᶠ m : ℕ in atTop, c*Real.log m < ((reps A m).card:ℝ)) (B : State A N t) :
    Nonempty (Transition B) := by
  by_cases h : (Nat.unpair t).1 ∈ B.carrier
  · obtain ⟨q,hq,C,hCB,hfreeze,htail,hbasis,huniq⟩ :=
      sparse_stage hc he hA B.tail B.basis h
        ((Nat.unpair_left_le t).trans B.cutoff_ge)
    exact ⟨⟨⟨C,q,by have := B.cutoff_ge; omega,hCB.trans B.subset,htail,hbasis⟩,
      hq,hCB,hfreeze,fun _ => huniq⟩⟩
  · exact ⟨⟨⟨B.carrier,B.cutoff+1,by have := B.cutoff_ge; omega,B.subset,
      fun x hx => B.tail x (by omega),B.basis⟩,Nat.lt_succ_self _,Set.Subset.rfl,fun _ _ => Iff.rfl,
      fun hh => (h hh).elim⟩⟩

private def run {A : Set ℕ} {N : ℕ}
    (step : ∀ {t : ℕ} (B : State A N t), Transition B)
    (B₀ : State A N 0) : (t : ℕ) → State A N t
  | 0 => B₀
  | t+1 => (step (run step B₀ t)).next

private lemma finish {A : Set ℕ} {N : ℕ}
    (step : ∀ {t : ℕ} (B : State A N t), Transition B)
    (B₀ : State A N 0) :
    ∃ B ⊆ A, B.IsAsymptoticAddBasisOfOrder 2 ∧
      ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  let T := run step B₀
  let B := ⋂ t, (T t).carrier
  have hsub (t : ℕ) : (T (t+1)).carrier ⊆ (T t).carrier := (step (T t)).subset
  have hanti : Antitone (fun t => (T t).carrier) := antitone_nat_of_succ_le hsub
  have hmono : Monotone (fun t => (T t).cutoff) :=
    monotone_nat_of_le_succ fun t => (step (T t)).advance.le
  have hfwd (i : ℕ) {j : ℕ} (hij : i ≤ j) (x : ℕ) (hx : x ≤ (T i).cutoff) :
      x ∈ (T j).carrier ↔ x ∈ (T i).carrier := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j hij ih => exact ((step (T j)).frozen x (hx.trans (hmono hij))).trans ih
  have hfreeze (i x : ℕ) (hx : x ≤ (T i).cutoff) :
      x ∈ B ↔ x ∈ (T i).carrier := by
    refine ⟨fun h => Set.mem_iInter.1 h i,fun h => Set.mem_iInter.2 ?_⟩
    intro j
    obtain hji | hij := le_total j i
    · exact hanti hji h
    · exact (hfwd i hij x hx).2 h
  refine ⟨B,fun x hx => (T 0).subset (Set.mem_iInter.1 hx 0),?_,?_⟩
  · rw [Set.isAsymptoticAddBasisOfOrder_two_iff,Nat.cofinite_eq_atTop]
    refine eventually_atTop.2 ⟨N,fun m hm => reps_nonempty_iff.1 ?_⟩
    rw [reps_congr_below (A := B) (B := (T m).carrier)
      (fun x hx => hfreeze m x (hx.trans (T m).cutoff_ge))]
    exact (T m).basis m hm
  · intro b hb hdel
    rw [Set.isAsymptoticAddBasisOfOrder_two_iff,Nat.cofinite_eq_atTop] at hdel
    obtain ⟨M,hM⟩ := eventually_atTop.1 hdel
    let t := Nat.pair b M
    have ht : (Nat.unpair t).1 = b := by simp [t]
    let q := (T (t+1)).cutoff
    have hq : M ≤ q := (Nat.right_le_pair b M).trans (by
      have := (T (t+1)).cutoff_ge
      exact (Nat.le_succ _).trans this)
    have huniq : reps (T (t+1)).carrier q = {b} := by
      have htag : (Nat.unpair t).1 ∈ (T t).carrier := by
        rw [ht]
        exact Set.mem_iInter.1 hb t
      change reps (step (T t)).next.carrier (step (T t)).next.cutoff = {b}
      simpa only [ht] using (step (T t)).unique htag
    obtain ⟨a,ha⟩ := reps_nonempty_iff.2 (hM q hq)
    have hsub' : B \ {b} ⊆ (T (t+1)).carrier := fun x hx => Set.mem_iInter.1 hx.1 (t+1)
    have ha' : a ∈ reps (T (t+1)).carrier q := reps_mono hsub' q ha
    rw [huniq,mem_singleton] at ha'
    exact (mem_reps.1 ha).2.1.2 (by simp [ha'])

end

/-- Erdős and Nathanson's minimal-basis construction, with the finite
random deletion estimate proved by conditioning on one pair at a time.
Source: [Systems of distinct representatives and minimal bases in additive number theory](https://www.renyi.hu/~p_erdos/1979-25.pdf). -/
theorem solution (A : Set ℕ) (c : ℝ) (hc : (Real.log (4/3))⁻¹ < c)
    (hA : A.IsAsymptoticAddBasisOfOrder 2)
    (h : ∀ᶠ m : ℕ in atTop, c*Real.log m < Erdos868.ncard_add_repr A 2 m) :
    ∃ B ⊆ A, B.IsAsymptoticAddBasisOfOrder 2 ∧
      ∀ b ∈ B, ¬(B \ {b}).IsAsymptoticAddBasisOfOrder 2 := by
  have hlog : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  let e := ((Real.log (4/3))⁻¹+c)/2
  have hce : e < c := by dsimp [e]; linarith
  have he : 1 < e*Real.log (4/3) := by
    have he' : (Real.log (4/3))⁻¹ < e := by dsimp [e]; linarith
    have hm := mul_lt_mul_of_pos_right he' hlog
    rwa [inv_mul_cancel₀ hlog.ne'] at hm
  rw [Set.isAsymptoticAddBasisOfOrder_two_iff,Nat.cofinite_eq_atTop] at hA
  obtain ⟨N,hN⟩ := eventually_atTop.1 hA
  have hh : ∀ᶠ m : ℕ in atTop, c*Real.log m < ((reps A m).card:ℝ) := by
    simpa only [reps_count] using h
  exact finish (fun B => Classical.choice (transition_exists hce he hh B))
    ⟨A,0,le_rfl,Set.Subset.rfl,fun _ _ hx => hx,fun m hm => reps_nonempty_iff.2 (hN m hm)⟩

end OMA868

theorem OMA.solution : type_of% @Erdos868.erdos_868.variants.fixed_ε := by
  exact OMA868.solution