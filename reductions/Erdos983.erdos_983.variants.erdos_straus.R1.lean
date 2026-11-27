import FormalConjectures.ErdosProblems.«983»
import Mathlib.Tactic
/-! # The asymptotic of Erdős and Straus

The upper bound counts the fibers belonging to primes above the square root.
For the lower bound we order paired primes along a path and separate its
extremal-set certificate from the prime distribution estimate.
Reference: P. Erdős, Some applications of graph theory to number theory,
1970, pages 138–140. -/

namespace OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1

open Finset Filter Asymptotics
open Erdos983

-- Select s+1 large-prime fibers, keeping more than 2s+1 elements.
private lemma select_fibers (B : Finset ℕ) (w : ℕ → ℕ) (s c : ℕ)
    (size : s+1 ≤ B.card) (total : s+B.card < c+∑ b ∈ B,w b) :
    ∃ T ⊆ B, T.card=s+1 ∧ 2*s+1 < c+∑ b ∈ T,w b := by
  classical
  let R := B.filter (fun b => 2 ≤ w b)
  have sub : R ⊆ B := filter_subset _ _
  by_cases many : s+1 ≤ R.card
  · obtain ⟨T,hT,ht⟩ := exists_subset_card_eq many
    refine ⟨T,hT.trans sub,ht,?_⟩
    have bound : ∑ b ∈ T,2 ≤ ∑ b ∈ T,w b := sum_le_sum fun b hb => (mem_filter.mp (hT hb)).2
    simp [ht] at bound
    omega
  · obtain ⟨T,rt,tb,ht⟩ := exists_subsuperset_card_eq sub (by omega) size
    refine ⟨T,tb,ht,?_⟩
    have bound : ∑ b ∈ B \ T,w b ≤ ∑ b ∈ B \ T,1 := by
      apply sum_le_sum
      intro b hb
      obtain ⟨hB,hT⟩ := mem_sdiff.mp hb
      by_contra! h
      exact hT (rt (mem_filter.mpr ⟨hB,by omega⟩))
    have part := sum_sdiff tb (f:=w)
    have cards := card_sdiff_add_card_eq_card tb
    simp at bound
    omega

-- An integer at most n has at most one distinct prime factor above √n.
private lemma big_factor_unique {n a p q : ℕ} (ha : 0<a) (an : a≤n)
    (hp : p ∈ a.primeFactors) (hq : q ∈ a.primeFactors)
    (bp : n.sqrt < p) (bq : n.sqrt < q) : p=q := by
  by_contra ne
  obtain ⟨pp,pd,_⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨qp,qd,_⟩ := Nat.mem_primeFactors.mp hq
  have cop := (Nat.coprime_primes pp qp).mpr ne
  have pq := Nat.le_of_dvd ha (cop.mul_dvd_of_dvd_of_dvd pd qd)
  have high := Nat.lt_succ_sqrt n
  have bound := Nat.mul_le_mul bp bq
  omega
private lemma upper_all (n : ℕ) :
    f (Nat.primeCounting n + 1) n ≤ 2 * Nat.primeCounting n.sqrt + 1 := by
  classical
  let primes (x:ℕ) := (range (x+1)).filter Nat.Prime
  have cardP (x:ℕ) : (primes x).card=x.primeCounting := by
    simp [primes,Nat.primeCounting,Nat.primeCounting',Nat.count_eq_card_filter_range]
  let D := primes n.sqrt
  let P := primes n
  let B := P \ D
  have sub : D ⊆ P := by
    intro p hp
    obtain ⟨h,pr⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp h; have := Nat.sqrt_le_self n; omega),pr⟩
  have totalP : B.card+D.card=P.card := card_sdiff_add_card_eq_card sub
  have cd : D.card=n.sqrt.primeCounting := cardP _
  have cp : P.card=n.primeCounting := cardP _
  by_cases small : B.card < D.card+1
  · have bound := Erdos983.erdos_983.variants.le_primeCounting (n:=n) (k:=n.primeCounting+1) (by omega)
    omega
  apply f_le
  intro A hA count
  let tag (a:ℕ) : ℕ := if h : ∃ p ∈ a.primeFactors, n.sqrt < p then h.choose else 0
  have tag_eq {a p:ℕ} (ha : a ∈ A) (hp : p ∈ a.primeFactors) (hbig : n.sqrt < p) : tag a = p := by
    have ex : ∃ q ∈ a.primeFactors, n.sqrt < q := ⟨p,hp,hbig⟩
    obtain ⟨lo,hi⟩ := mem_Icc.mp (hA ha)
    simp only [tag,dif_pos ex]
    exact big_factor_unique lo hi ex.choose_spec.1 hp ex.choose_spec.2 hbig
  have tag_mem {a:ℕ} (ha : a∈A) : tag a ∈ insert 0 B := by
    by_cases h : ∃ p ∈ a.primeFactors, n.sqrt < p
    · obtain ⟨p,hp,hg⟩ := h
      rw [tag_eq ha hp hg]
      apply mem_insert_of_mem
      obtain ⟨pr,dv,_⟩ := Nat.mem_primeFactors.mp hp
      obtain ⟨lo,hi⟩ := mem_Icc.mp (hA ha)
      have pn := (Nat.le_of_dvd lo dv).trans hi
      apply Finset.mem_sdiff.mpr
      exact ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),pr⟩,
        fun h => (by have := mem_range.mp (mem_filter.mp h).1; omega)⟩
    · exact mem_insert.mpr (Or.inl (dif_neg h))
  have zeroB : 0 ∉ B := fun h => Nat.not_prime_zero (mem_filter.mp (Finset.mem_sdiff.mp h).1).2
  let w (p : ℕ) := (A.filter (fun a => tag a=p)).card
  have count' := card_eq_sum_card_fiberwise (t:=insert 0 B) (s:=A) (f:=tag) (fun a ha => tag_mem ha)
  change A.card = ∑ b ∈ insert 0 B, w b at count'
  rw [sum_insert (by exact zeroB)] at count'
  obtain ⟨T,tb,ct,enough⟩ := select_fibers B w D.card (w 0) (by omega) (by omega)
  have dis : Disjoint D T := disjoint_left.mpr fun p hd ht => (Finset.mem_sdiff.mp (tb ht)).2 hd
  have cardU : (D∪T).card=2*n.sqrt.primeCounting+1 := by rw [card_union_of_disjoint dis,ct,cd]; omega
  refine ⟨D∪T,cardU,?_,?_⟩
  · intro p h
    rcases mem_union.mp h with hd|ht
    · exact (mem_filter.mp hd).2
    · exact (mem_filter.mp (Finset.mem_sdiff.mp (tb ht)).1).2
  have bound : A.filter (fun a => tag a ∈ insert 0 T) ⊆
      A.filter (fun a => ∀ p ∈ a.primeFactors,p ∈ D∪T) := by
    intro a ha
    obtain ⟨ha,hTag⟩ := mem_filter.mp ha
    apply mem_filter.mpr
    refine ⟨ha,fun p hp => ?_⟩
    by_cases h : p ≤ n.sqrt
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr (by omega),(Nat.mem_primeFactors.mp hp).1⟩)
    · rw [tag_eq ha hp (by omega)] at hTag
      rcases mem_insert.mp hTag with hzero|ht
      · exact ((Nat.mem_primeFactors.mp hp).1.ne_zero hzero).elim
      · exact mem_union_right _ ht
  have counting := sum_card_fiberwise_eq_card_filter A (insert 0 T) tag
  change (∑ b ∈ insert 0 T,w b)=_ at counting
  rw [sum_insert (fun h => zeroB (tb h))] at counting
  change 2*n.sqrt.primeCounting+1 < (A.filter _).card
  rw [←cd]
  exact enough.trans_le (counting ▸ card_le_card bound)

-- Read the primes alternately from the high and low ends.
private lemma paired_path {n t : ℕ} (pair : ∀ i<t,
    Nat.nth Nat.Prime i*Nat.nth Nat.Prime (t-1-i)≤n) :
    ∃ q : Fin t → ℕ, Function.Injective q ∧ (∀ i, (q i).Prime) ∧
      ∀ i j : Fin t, j.val=i.val+1 → q i*q j≤n := by
  let pos (i:Fin t) := if i.val%2=0 then t-1-i.val/2 else i.val/2
  let p := Nat.nth Nat.Prime
  have mono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  refine ⟨fun i => p (pos i),?_,fun i => Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _,?_⟩
  · intro i j eq
    apply Fin.ext
    have h := mono.injective eq
    have hi := i.isLt
    have hj := j.isLt
    dsimp only [pos] at h
    split_ifs at h <;> omega
  · intro i j edge
    have hi := i.isLt
    have hj := j.isLt
    have base := pair (i.val/2) (by omega)
    change p (i.val/2)*p (t-1-i.val/2)≤n at base
    by_cases h : i.val%2=0
    · have h' : j.val%2≠0 := by omega
      have e : j.val/2=i.val/2 := by omega
      simp only [pos,if_pos h,if_neg h',e,mul_comm]
      exact base
    · have h' : j.val%2=0 := by omega
      simp only [pos,if_neg h,if_pos h']
      exact (Nat.mul_le_mul_left _ (mono.monotone (by omega : t-1-j.val/2≤t-1-i.val/2))).trans base

/-- A path of distinct primes whose consecutive products are at most n
gives an extremal set by adjoining its endpoint primes and the unused primes. -/
def H1 : Prop := ∀ (n t : ℕ), 2 ≤ t → ∀ q : Fin t → ℕ,
  Function.Injective q → (∀ i, (q i).Prime) →
  (∀ i j : Fin t, j.val=i.val+1 → q i*q j≤n) →
  t ≤ f (n.primeCounting+1) n

/-- All complementary pairs among the first t primes fit below n, where t
falls short of twice the count up to √n by a superlogarithmically small
error on the √n scale. This is the prime distribution input. -/
def H2 : Prop := ∃ e : ℕ → ℕ,
  (∀ A : ℝ, 0<A → (fun n : ℕ => (e n:ℝ)) =o[atTop]
    (fun n : ℕ => Real.sqrt n / Real.log n ^ A)) ∧
  ∀ᶠ n : ℕ in atTop, 1 ≤ e n ∧ ∃ t : ℕ, 2 ≤ t ∧
    2*n.sqrt.primeCounting ≤ t+e n ∧
    ∀ i<t, Nat.nth Nat.Prime i * Nat.nth Nat.Prime (t-1-i) ≤ n

theorem main : H1 → H2 → type_of% @Erdos983.erdos_983.variants.erdos_straus := by
  rintro path ⟨e,loss,hpair⟩ A hA
  apply (IsBigO.of_bound' ?_).trans_isLittleO (loss A hA)
  filter_upwards [hpair] with n hn
  obtain ⟨one,t,ht,size,pair⟩ := hn
  obtain ⟨q,inj,pr,edges⟩ := paired_path pair
  have lower := path n t ht q inj pr edges
  have upper := upper_all n
  simp only [Real.norm_eq_abs,abs_of_nonneg (show (0 : ℝ) ≤ (e n : ℝ) by positivity)]
  apply abs_le.mpr
  constructor
  · have le : 2*n.sqrt.primeCounting ≤ f (n.primeCounting+1) n+e n := by omega
    have le' : 2*(n.sqrt.primeCounting:ℝ) ≤ (f (n.primeCounting+1) n:ℝ)+(e n:ℝ) := by exact_mod_cast le
    linarith
  · have le : f (n.primeCounting+1) n ≤ 2*n.sqrt.primeCounting+e n := by omega
    have le' : (f (n.primeCounting+1) n:ℝ) ≤ 2*(n.sqrt.primeCounting:ℝ)+(e n:ℝ) := by exact_mod_cast le
    linarith

end OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1
