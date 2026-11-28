import OMAStatements.S_oeis_a253288

/-!
In each prime-support class, the greedy rule either fixes its first unused member
or exchanges the first two. Two inputs requesting the second choice cannot be
neighbors in this class: their geometric mean is an integer strictly between them.
-/

open OMA.S_oeis_a253288

namespace PrimeSupportSwaps

private theorem class_infinite {n : ℕ} (hn : 2 ≤ n) : (Set.ofPred (SameFactors n)).Infinite := by
  have hmono : StrictMono (fun i : ℕ => n^(i+1)) :=
    strictMono_nat_of_lt_succ fun i => by
      rw [pow_succ n (i+1)]
      simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left (show 1 < n by omega) (by positivity : 0 < n^(i+1))
  apply Set.infinite_of_injective_forall_mem hmono.injective
  intro i
  exact ⟨fun p _ hp => hp.trans (dvd_pow_self n (by omega : i+1 ≠ 0)),
    fun p pp hp => pp.dvd_of_dvd_pow hp⟩

private theorem class_two {n k : ℕ} (hn : 2 ≤ n) (h : SameFactors n k) : 2 ≤ k := by
  by_contra! hk
  interval_cases k
  · obtain ⟨p, hp, pp⟩ := Nat.exists_infinite_primes (n+1)
    have := Nat.le_of_dvd (by omega : 0 < n) (h.2 p pp (dvd_zero _))
    omega
  · have hp := Nat.minFac_prime (by omega : n ≠ 1)
    exact hp.not_dvd_one (h.1 _ hp (Nat.minFac_dvd _))

/-- For two marked numbers with the same prime support, the geometric mean is an
integer strictly between them and has the same prime support. -/
private theorem between {x y : ℕ} (hx : 2 ≤ x) (hxy : x < y) (hc : SameFactors x y)
    (hmx : ¬ Even (a005361 x)) (hmy : ¬ Even (a005361 y)) :
    ∃ z, x < z ∧ z < y ∧ SameFactors x z := by
  have odd_exp {n p : ℕ} (hm : ¬ Even (a005361 n)) (hp : p ∈ n.primeFactors) :
      Odd (n.factorization p) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact hm (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp he).trans
      (Finset.dvd_prod_of_mem (fun q => n.factorization q) hp)))
  have hn : x*y ≠ 0 := mul_ne_zero (by omega) (by omega)
  have even_exp (p : ℕ) (hp : p ∈ (x*y).primeFactors) : Even ((x*y).factorization p) := by
    obtain ⟨hprime,hdvd,_⟩ := Nat.mem_primeFactors.mp hp
    have hd : p ∣ x := (hprime.dvd_mul.mp hdvd).elim id (hc.2 p hprime)
    rw [Nat.factorization_mul (by omega : x≠0) (by omega : y≠0), Finsupp.add_apply]
    exact (odd_exp hmx (Nat.mem_primeFactors.mpr ⟨hprime,hd,by omega⟩)).add_odd
      (odd_exp hmy (Nat.mem_primeFactors.mpr ⟨hprime,hc.1 p hprime hd,by omega⟩))
  let z := ∏ p ∈ (x*y).primeFactors, p ^ ((x*y).factorization p / 2)
  have hsq : x*y = z*z := by
    unfold z
    rw [← Finset.prod_mul_distrib]
    refine (Nat.prod_primeFactors_pow_factorization hn).trans (Finset.prod_congr rfl ?_)
    intro p hp
    rw [← pow_add]
    congr 1
    obtain ⟨k,hk⟩ := even_exp p hp
    omega
  refine ⟨z, ?_, ?_, ?_⟩
  · by_contra! h
    nlinarith [Nat.mul_self_le_mul_self h, Nat.mul_lt_mul_of_pos_left hxy (by omega : 0<x)]
  · by_contra! h
    nlinarith [Nat.mul_self_le_mul_self h, Nat.mul_lt_mul_of_pos_right hxy (by omega : 0<y)]
  · constructor
    · intro p hp hd
      have hd' : p ∣ z*z := hsq ▸ dvd_mul_of_dvd_left hd y
      exact (hp.dvd_mul.mp hd').elim id id
    · intro p hp hd
      have hd' : p ∣ x*y := hsq ▸ dvd_mul_of_dvd_left hd z
      exact (hp.dvd_mul.mp hd').elim id (hc.2 p hp)

private theorem reflFactors (n : ℕ) : SameFactors n n := ⟨fun _ _ h => h, fun _ _ h => h⟩

private theorem symmFactors {m n : ℕ} (h : SameFactors m n) : SameFactors n m := ⟨h.2,h.1⟩

private theorem transFactors {a b c : ℕ} (h : SameFactors a b) (g : SameFactors b c) :
    SameFactors a c := ⟨fun p hp d => g.1 p hp (h.1 p hp d), fun p hp d => h.2 p hp (g.2 p hp d)⟩

private def available (n x : ℕ) : Prop :=
  SameFactors n x ∧ ∀ m, m < n → 1 ≤ m → a m ≠ x

private theorem greedy {n : ℕ} (h : 2 ≤ n) :
    a n = Nat.nth (available n) (if Even (a005361 n) then 0 else 1) := by
  obtain ⟨t,rfl⟩ : ∃ t, n = t+2 := ⟨n-2,by omega⟩
  rw [a]; rfl

private theorem keeps_factors {n : ℕ} (hn : 1 ≤ n) : SameFactors n (a n) := by
  classical
  by_cases h : n=1
  · subst n; rw [a]; exact reflFactors 1
  have hh : 2 ≤ n := by omega
  have inf := (class_infinite hh).sdiff ((Finset.range n).image a).finite_toSet
  have ia : (Set.ofPred (available n)).Infinite := inf.mono (by
    intro x hx
    refine ⟨hx.1,fun m hm _ he => hx.2 ?_⟩
    exact Finset.mem_image.mpr ⟨m,Finset.mem_range.mpr hm,he⟩)
  rw [greedy hh]
  exact (Nat.nth_mem_of_infinite ia _).1

private def used (f : ℕ → ℕ) (i : ℕ) : Finset ℕ := (Finset.range i).image f

private theorem mem_used {f : ℕ → ℕ} {i x : ℕ} : x ∈ used f i ↔ ∃ j < i, f j = x := by
  simp [used]

private theorem used_succ (f : ℕ → ℕ) (i : ℕ) :
    used f (i+1) = insert (f i) (used f i) := by simp [used,Finset.range_add_one]

private theorem nth_tail {P : ℕ → Prop} {s : ℕ → ℕ} (mono : StrictMono s) (i b : ℕ)
    (tail : ∀ x, P x ↔ ∃ j, s (i+j) = x) : Nat.nth P b = s (i+b) := by
  let f (j : ℕ) := s (i+j)
  have mon : StrictMono f := fun _ _ h => mono (by omega)
  have im : Set.range f = Set.ofPred P := Set.ext (fun x => (tail x).symm)
  have inf := (Set.infinite_range_of_injective mon.injective)
  rw [im] at inf
  symm
  apply Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f
  · intro x hx
    obtain ⟨j,hj⟩ := (tail x).mp hx
    exact ⟨j,fun h => (inf h).elim,hj⟩
  · intro j _; exact (tail _).mpr ⟨j,rfl⟩
  · exact mon.strictMonoOn _
  · exact fun h => (inf h).elim

private theorem on_class {n : ℕ} (hn : 2 ≤ n) :
    ∀ j, let x := Nat.nth (SameFactors n) j; a (a x) = x := by
  classical
  let s := Nat.nth (SameFactors n)
  have inf := class_infinite hn
  have mono : StrictMono s := Nat.nth_strictMono inf
  have mem (j : ℕ) : SameFactors n (s j) := Nat.nth_mem_of_infinite inf j
  have onto {x : ℕ} (h : SameFactors n x) : ∃ j, s j = x := Nat.subset_range_nth h
  have two (j : ℕ) : 2 ≤ s j := class_two hn (mem j)
  have legal (i j : ℕ) : available (s i) (s j) ↔ s j ∉ used (a ∘ s) i := by
    constructor
    · rintro ⟨_,h⟩ H
      obtain ⟨k,hk,he⟩ := mem_used.mp H
      exact h (s k) (mono hk) (by have := two k; omega) he
    · intro h
      refine ⟨transFactors (symmFactors (mem i)) (mem j), ?_⟩
      intro m hm hm1 eq
      have mm := keeps_factors hm1
      rw [eq] at mm
      obtain ⟨k,rfl⟩ := onto (transFactors (mem j) (symmFactors mm))
      exact h (mem_used.mpr ⟨k,mono.lt_iff_lt.mp hm,eq⟩)
  have possible {i x : ℕ} (h : available (s i) x) : ∃ j, s j = x :=
    onto (transFactors (mem i) h.1)
  have present (i j : ℕ) : s j ∈ used s i ↔ j < i := by
    rw [mem_used]
    constructor
    · rintro ⟨z,hz,eq⟩
      rwa [←mono.injective eq]
    · intro h; exact ⟨j,h,rfl⟩
  have pick {i : ℕ} (h : used (a ∘ s) i = used s i) :
      a (s i) = s (i + if Even (a005361 (s i)) then 0 else 1) := by
    rw [greedy (two i)]
    apply nth_tail mono
    intro x
    constructor
    · intro hx
      obtain ⟨j,rfl⟩ := possible hx
      have free := (legal i j).mp hx
      rw [h,present] at free
      exact ⟨j-i,by congr 1; omega⟩
    · rintro ⟨j,rfl⟩
      rw [legal,h,present]
      omega
  have next_even {i : ℕ} (h : ¬Even (a005361 (s i))) : Even (a005361 (s (i+1))) := by
    by_contra hnext
    obtain ⟨z,hiz,hzi,hz⟩ := between (two i) (mono (Nat.lt_succ_self i))
      (transFactors (symmFactors (mem i)) (mem (i+1))) h hnext
    obtain ⟨j,rfl⟩ := onto (transFactors (mem i) hz)
    have := mono.lt_iff_lt.mp hiz
    have := mono.lt_iff_lt.mp hzi
    omega
  have back {i : ℕ} (clean : used (a ∘ s) i = used s i) (mark : ¬Even (a005361 (s i)))
      (first : a (s i) = s (i+1)) : a (s (i+1)) = s i := by
    rw [greedy (two _), if_pos (next_even mark),Nat.nth_zero]
    apply IsLeast.csInf_eq
    constructor
    · apply (legal (i+1) i).mpr
      rw [used_succ,clean]
      simp only [Function.comp_apply,first,Finset.mem_insert,present]
      exact fun hh => hh.elim (mono (show i < i+1 by omega)).ne (Nat.lt_irrefl _)
    · intro x hx
      obtain ⟨j,rfl⟩ := possible hx
      have free := (legal (i+1) j).mp hx
      rw [used_succ,clean] at free
      have old : s j ∉ used s i := fun H => free (Finset.mem_insert_of_mem H)
      exact mono.monotone (by have := (present i j).not.mp old; omega)
  have from_clean (d : ℕ) : ∀ i, used (a ∘ s) i = used s i →
      a (a (s (i+d))) = s (i+d) := by
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hc
      have eq := pick hc
      by_cases e : Even (a005361 (s i))
      · rw [if_pos e,Nat.add_zero] at eq
        cases d with
        | zero => simp only [Nat.add_zero,eq]
        | succ d =>
          have c : used (a ∘ s) (i+1) = used s (i+1) := by simp only [used_succ,hc,Function.comp_apply,eq]
          simpa only [Nat.add_right_comm, Nat.add_assoc, Nat.add_comm 1 d] using ih d (by omega) (i+1) c
      · rw [if_neg e] at eq
        have ret := back hc e eq
        cases d with
        | zero => simp only [Nat.add_zero,eq,ret]
        | succ d =>
          cases d with
          | zero => simp only [Nat.zero_add,ret,eq]
          | succ d =>
            have c : used (a ∘ s) (i+2) = used s (i+2) := by
              rw [show i+2=i+1+1 by omega,used_succ,used_succ,used_succ,used_succ,hc]
              simp only [Function.comp_apply,eq,ret,Finset.insert_comm]
            rw [show i+(d+1+1)=(i+2)+d by omega]
            exact ih d (by omega) (i+2) c
  intro j
  simpa only [Nat.zero_add] using from_clean j 0 (by simp [used])

end PrimeSupportSwaps

theorem OMA.solution : type_of% @OMA.S_oeis_a253288.main := by
  intro n hn
  by_cases eq : n=1
  · subst n; simp [a]
  · have h : 2 ≤ n := by omega
    obtain ⟨i,hi⟩ := Nat.subset_range_nth (p := SameFactors n) (a := n) (PrimeSupportSwaps.reflFactors n)
    have hh := PrimeSupportSwaps.on_class h i
    dsimp only at hh
    rwa [hi] at hh
