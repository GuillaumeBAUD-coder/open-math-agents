import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1

/-!
For the exponent-eleven branch, the two remaining questions involve the exponent
alone. The roots are the prime factors greater than three of 2^a+1. Repeatedly
adjoin prime factors greater than three of p+1 for each prime already present.
After removing the six fixed primes forced by 3^11+1, this procedure recovers
the entire remaining support in at most a+1 rounds. An empty root set is
impossible. With a single root, cancellation lowers the exponent by one or two
and preserves the balance. At most five units of descent suffice to reach a
bounded exponent or a case with at least two roots.

The balance-equation API is due to adammcarter and Dugongue. The six-prime
cancellation also appears in studer's PR 35627. The earlier R2 of the original
problem proves uniqueness of squarefree completions. Here both branches use
an explicit closure, and separate exactly two roots from at least three roots.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R3

open Finset Function

/-- If every non-root has a predecessor at least twice as far from 1,
    D + 1 rounds suffice when all roots are at most 2^D + 1. -/
lemma reach_all (roots support : Finset ℕ) (children : ℕ → Finset ℕ) (D : ℕ)
    (roots_mem : roots ⊆ support)
    (closed : ∀ p ∈ support, children p ⊆ support)
    (source : ∀ q ∈ support, q ∈ roots ∨ ∃ p ∈ support, q ∈ children p)
    (large : ∀ q ∈ support, 2 ≤ q)
    (shrinks : ∀ p ∈ support, ∀ q ∈ children p, 2 * (q - 1) ≤ p - 1)
    (root_bound : ∀ q ∈ roots, q - 1 ≤ 2^D) :
    (fun s : Finset ℕ => s ∪ s.biUnion children)^[D + 1] roots = support := by
  let step := fun s : Finset ℕ => s ∪ s.biUnion children
  change step^[D+1] roots = support
  have inside (i : ℕ) : step^[i] roots ⊆ support := by
    induction i with
    | zero => exact roots_mem
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact Finset.union_subset ih (Finset.biUnion_subset.mpr fun p hp => closed p (ih hp))
  have starts (i : ℕ) : roots ⊆ step^[i] roots := by
    induction i with
    | zero => exact fun _ h => h
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans Finset.subset_union_left
  have bound (p : ℕ) (hp : p ∈ support) : p - 1 ≤ 2^D := by
    let t := support.max' ⟨p, hp⟩
    have ht : t ∈ support := Finset.max'_mem _ _
    have hr : t ∈ roots := by
      rcases source t ht with hr | ⟨u, hu, htu⟩
      · exact hr
      · have := shrinks u hu t htu
        have : u ≤ t := Finset.le_max' _ _ hu
        have := large t ht
        omega
    have : p ≤ t := Finset.le_max' _ _ hp
    exact (Nat.sub_le_sub_right this 1).trans (root_bound t hr)
  have ancestor (i q : ℕ) (hq : q ∈ support) (miss : q ∉ step^[i] roots) :
      ∃ p ∈ support, 2^i * (q-1) ≤ p-1 := by
    induction i generalizing q with
    | zero => exact ⟨q, hq, by simp⟩
    | succ i ih =>
      have hr : q ∉ roots := fun h => miss (starts _ h)
      obtain ⟨u, hu, hqu⟩ := (source q hq).resolve_left hr
      have hmiss : u ∉ step^[i] roots := by
        intro h
        apply miss
        rw [Function.iterate_succ_apply']
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, h, hqu⟩)
      obtain ⟨p, hp, hsize⟩ := ih u hu hmiss
      refine ⟨p, hp, ?_⟩
      rw [pow_succ, Nat.mul_assoc]
      exact (Nat.mul_le_mul_left _ (shrinks u hu q hqu)).trans hsize
  apply Finset.Subset.antisymm (inside _)
  intro q hq
  by_contra miss
  obtain ⟨p, hp, hsize⟩ := ancestor _ q hq miss
  have hq' := large q hq
  have hone : 1 ≤ q-1 := by omega
  have hpow := Nat.mul_le_mul_left (2^(D+1)) hone
  rw [Nat.mul_one] at hpow
  have h := (hpow.trans hsize).trans (bound p hp)
  rw [pow_succ] at h
  have : 0 < 2^D := by positivity
  omega

lemma reconstruct (a : ℕ) (Q : Finset ℕ)
    (primes : ∀ p ∈ Q, Nat.Prime p ∧ 3 < p)
    (balance : (2^a + 1) * 8192 * (∏ p ∈ Q, (p+1)) =
      2^(a+1) * 6561 * (∏ p ∈ Q, p)) :
    (fun s : Finset ℕ => s ∪ s.biUnion (fun p => (p+1).primeFactors.filter (3 < ·)))^[a+1]
      ((2^a+1).primeFactors.filter (3 < ·)) = Q := by
  let roots := (2^a+1).primeFactors.filter (3 < ·)
  let next := fun p : ℕ => (p+1).primeFactors.filter (3 < ·)
  have sources (q : ℕ) (hq : q.Prime) (hq3 : 3 < q) :
      q ∈ Q ↔ q ∣ 2^a + 1 ∨ ∃ p ∈ Q, q ∣ p+1 := by
    have n2 : ¬q ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide : 0 < 2) h; omega
    have n3 : ¬q ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide : 0 < 3) h; omega
    have n8192 : ¬q ∣ 8192 := fun h => n2 (hq.dvd_of_dvd_pow (n := 13) h)
    have n6561 : ¬q ∣ 6561 := fun h => n3 (hq.dvd_of_dvd_pow (n := 8) h)
    have n2pow : ¬q ∣ 2^(a+1) := fun h => n2 (hq.dvd_of_dvd_pow h)
    have left : q ∣ (2^a + 1) * 8192 * (∏ p ∈ Q, (p+1)) ↔
        q ∣ 2^a+1 ∨ ∃ p ∈ Q, q ∣ p+1 := by
      simp only [hq.dvd_mul, n8192, or_false, Prime.dvd_finsetProd_iff hq.prime]
    rw [← left, balance, hq.dvd_mul, hq.dvd_mul]
    simp only [n2pow, n6561, false_or, Prime.dvd_finsetProd_iff hq.prime]
    constructor
    · exact fun h => ⟨q, h, dvd_refl q⟩
    · rintro ⟨p, hp, hqp⟩
      exact ((Nat.prime_dvd_prime_iff_eq hq (primes p hp).1).mp hqp) ▸ hp
  apply reach_all roots Q next a
  · intro q h
    obtain ⟨hp, hq⟩ := Finset.mem_filter.mp h
    exact (sources q (Nat.prime_of_mem_primeFactors hp) hq).mpr
      (Or.inl (Nat.dvd_of_mem_primeFactors hp))
  · intro p hp q h
    obtain ⟨hprime, hq⟩ := Finset.mem_filter.mp h
    exact (sources q (Nat.prime_of_mem_primeFactors hprime) hq).mpr
      (Or.inr ⟨p, hp, Nat.dvd_of_mem_primeFactors hprime⟩)
  · intro q hq
    obtain ⟨pr, big⟩ := primes q hq
    rcases (sources q pr big).mp hq with h | ⟨p, hp, hd⟩
    · exact Or.inl (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pr, h, by positivity⟩, big⟩)
    · exact Or.inr ⟨p, hp, Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨pr, hd, by omega⟩, big⟩⟩
  · intro p hp
    exact (by decide : 2 ≤ 3).trans (primes p hp).2.le
  · intro p hp q hq
    obtain ⟨pprime, pbig⟩ := primes p hp
    obtain ⟨hfac, qbig⟩ := Finset.mem_filter.mp hq
    have qprime := Nat.prime_of_mem_primeFactors hfac
    obtain ⟨u, hu⟩ := Nat.dvd_of_mem_primeFactors hfac
    have hpodd := pprime.eq_two_or_odd.resolve_left (by omega)
    have hqodd := qprime.eq_two_or_odd.resolve_left (by omega)
    have hge : 2 ≤ u := by
      by_contra! h
      interval_cases u <;> simp_all
      omega
    have := Nat.mul_le_mul_left q hge
    omega
  · intro q hq
    have hd := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    have hupper : q ≤ (2 : ℕ)^a+1 := Nat.le_of_dvd (Nat.succ_pos _) hd
    exact Nat.sub_le_of_le_add hupper

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

/-- Remove the six prime factors forced by 3^11 + 1 and their successors.
    The same cancellation occurs in studer's reduction in PR 35627. -/
lemma remove_fixed {a : ℕ} {P : Finset ℕ}
    (primeP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (bal : (2^a+1)*(1+3^11)*(∏ p ∈ P, (p+1)) =
        2^(a+1)*3^11*(∏ p ∈ P, p)) :
    let Q := P \ {7,17,67,83,331,661}
    (2^a+1)*8192*(∏ p ∈ Q, (p+1)) = 2^(a+1)*6561*(∏ p ∈ Q, p) := by
  obtain ⟨follow, _, _, _, _, _, start, _⟩ :=
    facts primeP (prime_dvd_prime_pow (e := 11) Nat.prime_three) bal
  have h67 := start 67 (by norm_num) (by decide) (by decide) (by decide)
  have h661 := start 661 (by norm_num) (by decide) (by decide) (by decide)
  have h17 := follow 17 (by norm_num) (by decide) (by decide) 67 h67 (by decide)
  have h331 := follow 331 (by norm_num) (by decide) (by decide) 661 h661 (by decide)
  have h83 := follow 83 (by norm_num) (by decide) (by decide) 331 h331 (by decide)
  have h7 := follow 7 (by norm_num) (by decide) (by decide) 83 h83 (by decide)
  let K : Finset ℕ := {7,17,67,83,331,661}
  have sub : K ⊆ P := by simp [K, Finset.insert_subset_iff, h7, h17, h67, h83, h331, h661]
  rw [← Finset.prod_sdiff (f := fun p : ℕ => p+1) sub,
      ← Finset.prod_sdiff (f := fun p : ℕ => p) sub] at bal
  have num : (∏ p ∈ K, (p+1)) = 180778493952 := by decide
  have den : (∏ p ∈ K, p) = 144786913369 := by decide
  rw [num, den] at bal
  change (2^a+1)*8192*(∏ p ∈ P \ K, (p+1)) = 2^(a+1)*6561*(∏ p ∈ P \ K, p)
  nlinarith only [bal]

lemma unitary_support {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hrepeated : ∀ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p = 3)
    (e : n.factorization 3 = 11) :
    let a := padicValNat 2 n
    let roots := (2^a+1).primeFactors.filter (3 < ·)
    let Q := (fun s : Finset ℕ => s ∪ s.biUnion (fun p => (p+1).primeFactors.filter (3 < ·)))^[a+1] roots
    (∀ p ∈ Q, p.Prime ∧ 3 < p) ∧ Disjoint Q {7,17,67,83,331,661} ∧
    (2^a+1)*8192*(∏ p ∈ Q, (p+1)) = 2^(a+1)*6561*(∏ p ∈ Q, p) := by
  let P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ))
  let K : Finset ℕ := {7,17,67,83,331,661}
  let Q := P \ K
  have hn := h.2.ne'
  have three : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), hn⟩
  have simple (p : ℕ) (hp : p ∈ n.primeFactors) (h2 : p ≠ 2) (h3 : p ≠ 3) :
      n.factorization p = 1 := by
    have pr := Nat.prime_of_mem_primeFactors hp
    have hpos := pr.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
    have hlt : ¬2 ≤ n.factorization p := fun hle =>
      h3 ((hrepeated p).mp ⟨pr, h2, (pr.pow_dvd_iff_le_factorization hn).mpr hle⟩)
    omega
  obtain ⟨hP, hbal⟩ := kernel_balance_one h three (by decide) simple
  rw [e, Nat.factorization_def n Nat.prime_two] at hbal
  have hQbal := remove_fixed hP hbal
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime ∧ 3 < p := by
    have hmem : p ∈ P := Finset.sdiff_subset hp
    obtain ⟨pr, h2⟩ := hP p hmem
    have h3 : p ≠ 3 := by simpa using (Finset.mem_filter.mp hmem).2
    exact ⟨pr, by have := pr.two_le; omega⟩
  have heq := reconstruct (padicValNat 2 n) Q hQ hQbal
  dsimp only
  rw [heq]
  exact ⟨hQ, Finset.sdiff_disjoint, hQbal⟩

lemma seed_singleton_form {x q : ℕ} (hx : Odd x)
    (roots : x.primeFactors.filter (3 < ·) = {q}) (sq : ¬ q^2 ∣ x) :
    x = 3^(padicValNat 3 x)*q := by
  have root : q ∈ x.primeFactors.filter (3 < ·) := by simp [roots]
  obtain ⟨qm, qbig⟩ := Finset.mem_filter.mp root
  have prime := Nat.prime_of_mem_primeFactors qm
  have xpos := hx.pos
  have qone : x.factorization q = 1 := by
    have pos := prime.factorization_pos_of_dvd xpos.ne' (Nat.dvd_of_mem_primeFactors qm)
    have lt : ¬ 2 ≤ x.factorization q := fun h => sq ((prime.pow_dvd_iff_le_factorization xpos.ne').mpr h)
    omega
  have sub : x.primeFactors ⊆ ({3,q} : Finset ℕ) := by
    intro r hr
    by_cases h : 3 < r
    · have mem := Finset.mem_filter.mpr ⟨hr, h⟩
      rw [roots, Finset.mem_singleton] at mem
      simp [mem]
    · have := (Nat.prime_of_mem_primeFactors hr).two_le
      have hn2 : r ≠ 2 := fun e => hx.not_two_dvd_nat (e ▸ Nat.dvd_of_mem_primeFactors hr)
      have : r = 3 := by omega
      simp [this]
  calc
    x = ∏ r ∈ x.primeFactors, r^x.factorization r := Nat.prod_primeFactors_pow_factorization xpos.ne'
    _ = ∏ r ∈ ({3,q} : Finset ℕ), r^x.factorization r := by
      apply Finset.prod_subset sub
      intro r _ h
      have hz : x.factorization r = 0 := Finsupp.notMem_support_iff.mp (by simpa using h)
      simp [hz]
    _ = 3^(padicValNat 3 x)*q := by
      rw [Finset.prod_pair (by omega : 3 ≠ q), Nat.factorization_def x Nat.prime_three, qone, pow_one]

lemma other_prime {x : ℕ} (hx : Odd x) (small : 3^(padicValNat 3 x) < x) :
    ∃ q, q.Prime ∧ 3 < q ∧ q ∣ x := by
  by_contra missing
  have uniq {q : ℕ} (hp : q.Prime) (hd : q ∣ x) : q = 3 := by
    have h2 : q ≠ 2 := fun e => hx.not_two_dvd_nat (e ▸ hd)
    have := hp.two_le
    by_contra h3
    exact missing ⟨q, hp, by omega, hd⟩
  have pure := Nat.eq_prime_pow_of_unique_prime_dvd hx.pos.ne' uniq
  have val := congrArg (padicValNat 3) pure
  rw [padicValNat.prime_pow] at val
  rw [val, ← pure] at small
  exact (lt_irrefl _ small)

/-- With a = 3u and u odd and at least 5, both factors of
    (2^u)^3 + 1 contain a prime greater than three. A sole root would
    divide both factors, contradicting the squarefree condition. -/
lemma two_or_more_at_three {a q : ℕ} (large : 9 < a) (res : a % 6 = 3)
    (roots : (2^a+1).primeFactors.filter (3 < ·) = {q}) (sq : ¬ q^2 ∣ 2^a+1) : False := by
  let u := a/3
  have eq : a = u*3 := by dsimp [u]; omega
  have hu : 5 ≤ u := by dsimp [u]; omega
  have uodd : Odd u := Nat.odd_iff.mpr (by dsimp [u]; omega)
  let x : ℕ := 2^u
  have xeven : Even x := Even.pow_of_ne_zero (by decide : Even 2) (by omega : u ≠ 0)
  have three_lt (j : ℕ) (hj : 4 ≤ j) : 3*j < 2^j := by
    induction j, hj using Nat.le_induction with
    | base => decide
    | succ j hj ih => rw [pow_succ]; omega
  have xlarge := three_lt u (by omega)
  have val : padicValNat 3 (x+1) = 1 + padicValNat 3 u := by
    simpa [x, padicValNat.self (by decide : 1 < 3)] using
      (padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) (by decide : Odd 3)
        (by decide) (by decide) uodd)
  have part : 3^padicValNat 3 u ≤ u := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have narrow : 3^padicValNat 3 (x+1) < x+1 := by
    rw [val, pow_add, pow_one]
    change 3 * 3^padicValNat 3 u < 2^u + 1
    omega
  obtain ⟨p, pp, pb, pd⟩ := other_prime xeven.add_one narrow
  let y := (x^3+1)/(x+1)
  have divides : x+1 ∣ x^3+1 := by simpa using
    (Odd.nat_add_dvd_pow_add_pow x 1 (by decide : Odd 3))
  have mult : (x+1)*y = x^3+1 := Nat.mul_div_cancel' divides
  have xn : 3 ∣ x+1 := (dvd_iff_padicValNat_ne_zero (by omega : x+1 ≠ 0)).mpr (by rw [val]; omega)
  have three_not_x : ¬3 ∣ x := by intro hd; have := Nat.dvd_sub xn hd; simp at this
  have valy : padicValNat 3 y = 1 := by
    have lift := padicValNat.pow_add_pow (p := 3) (x := x) (y := 1) (by decide : Odd 3)
      xn three_not_x (by decide : Odd 3)
    rw [one_pow, padicValNat.self (by decide : 1 < 3)] at lift
    change padicValNat 3 ((x^3+1)/(x+1)) = 1
    rw [padicValNat.div_of_dvd divides, lift]
    omega
  have ylarge : 3 < y := by
    by_contra! h
    have hh := Nat.mul_le_mul_left (x+1) h
    have hx : 4 ≤ x := by change 4 ≤ 2^u; omega
    nlinarith only [hh, mult, hx, Nat.mul_self_le_mul_self hx, Nat.pow_le_pow_left hx 3,
      Nat.zero_le ((x-2)^2)]
  have yodd : Odd y := Odd.of_dvd_nat ((xeven.pow_of_ne_zero (by decide : 3 ≠ 0)).add_one)
    (by rw [← mult]; exact dvd_mul_left _ _)
  obtain ⟨r, rp, rb, rd⟩ := other_prime yodd (by simpa [valy] using ylarge)
  have seed : 2^a+1 = (x+1)*y := by rw [eq, pow_mul]; exact mult.symm
  have identify (t : ℕ) (pt : t.Prime) (big : 3 < t) (d : t ∣ 2^a+1) : t = q := by
    have hm : t ∈ (2^a+1).primeFactors.filter (3 < ·) := Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨pt,d,by positivity⟩, big⟩
    simpa [roots] using hm
  have ep := identify p pp pb (seed ▸ pd.mul_right y)
  have er := identify r rp rb (seed ▸ rd.mul_left (x+1))
  subst p
  subst r
  apply sq
  rw [seed, pow_two]
  exact Nat.mul_dvd_mul pd rd

lemma cancel_root {a b c d q : ℕ} {Q : Finset ℕ} (hq : q ∈ Q) (hqpos : 0 < q)
    (ab : a = b+d) (seed : 2^a+1 = c*q) (shift : c*(q+1) = 2^d*(2^b+1))
    (bal : (2^a+1)*8192*(∏ p ∈ Q, (p+1)) = 2^(a+1)*6561*(∏ p ∈ Q, p)) :
    (2^b+1)*8192*(∏ p ∈ Q.erase q, (p+1)) = 2^(b+1)*6561*(∏ p ∈ Q.erase q, p) := by
  have exp : (2:ℕ)^(a+1) = 2^d * 2^(b+1) := by rw [← pow_add]; congr 1; omega
  rw [seed, ← Finset.mul_prod_erase Q (fun p : ℕ => p+1) hq,
    ← Finset.mul_prod_erase Q (fun p : ℕ => p) hq, exp] at bal
  apply Nat.eq_of_mul_eq_mul_left (show 0 < q * 2^d by positivity)
  calc
    _ = q * (2^d * (2^b+1)) * 8192 * (∏ p ∈ Q.erase q, (p+1)) := by ring
    _ = _ := by rw [← shift]; nlinarith only [bal]

/-- A single root q contributes the whole seed q at even a, or the seed
    3q at odd a. Deleting q from the support changes the numerator to
    2^a+2 or 2^a+4, respectively, before cancelling a power of two. -/
lemma single_step {a : ℕ} {Q : Finset ℕ} (big : 9 < a)
    (primes : ∀ p ∈ Q, p.Prime ∧ 3 < p)
    (bal : (2^a+1)*8192*(∏ p ∈ Q, (p+1)) = 2^(a+1)*6561*(∏ p ∈ Q, p))
    (one : ((2^a+1).primeFactors.filter (3 < ·)).card = 1) :
    ∃ b q, q ∈ Q ∧
      ((a % 2 = 0 ∧ a = b+1) ∨ (a % 2 = 1 ∧ a % 6 ≠ 3 ∧ a = b+2)) ∧
      (2^b+1)*8192*(∏ p ∈ Q.erase q, (p+1)) = 2^(b+1)*6561*(∏ p ∈ Q.erase q, p) := by
  obtain ⟨q, roots⟩ := Finset.card_eq_one.mp one
  have mem : q ∈ (2^a+1).primeFactors.filter (3 < ·) := by simp [roots]
  obtain ⟨qm, qbig⟩ := Finset.mem_filter.mp mem
  have qp := Nat.prime_of_mem_primeFactors qm
  have hP : ∀ p ∈ Q, p.Prime ∧ p ≠ 2 := fun p hp => ⟨(primes p hp).1, by have := (primes p hp).2; omega⟩
  obtain ⟨_, root_mem, _, _, no_square, _⟩ := facts hP (prime_dvd_prime_pow (e := 8) Nat.prime_three) bal
  have qQ := root_mem q qp (by omega) (by simp; omega) (Nat.dvd_of_mem_primeFactors qm)
  have sq : ¬ q^2 ∣ 2^a+1 := by simpa [pow_two] using no_square q qp (by omega) (by simp; omega)
  have oddseed : Odd (2^a+1) := (Even.pow_of_ne_zero (by decide : Even 2) (by omega : a ≠ 0)).add_one
  have form := seed_singleton_form oddseed roots sq
  by_cases even : a % 2 = 0
  · have ee : a = 2*(a/2) := by omega
    have cong := (show Nat.ModEq 3 (2^2) 1 by decide).pow (a/2)
    rw [one_pow, ← pow_mul, ← ee] at cong
    have no3 : ¬3 ∣ 2^a+1 := by change 2^a%3 = 1 at cong; omega
    rw [padicValNat.eq_zero_of_not_dvd no3, pow_zero, one_mul] at form
    have split : a = a-1+1 := by omega
    refine ⟨a-1, q, qQ, Or.inl ⟨even,split⟩, cancel_root qQ qp.pos split (c:=1) (by simpa) ?_ bal⟩
    rw [← form, show (2:ℕ)^a = 2^(a-1)*2 by conv_lhs => rw [split, pow_succ]]
    ring
  · have odd : Odd a := Nat.odd_iff.mpr (by omega)
    have avoid : a%6 ≠ 3 := fun h => two_or_more_at_three big h roots sq
    have n3 : ¬3 ∣ a := by omega
    have v : padicValNat 3 (2^a+1) = 1 := by
      simpa [padicValNat.self (by decide : 1 < 3), padicValNat.eq_zero_of_not_dvd n3] using
        (padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) (by decide : Odd 3)
          (by decide) (by decide) odd)
    rw [v, pow_one] at form
    have split : a = a-2+2 := by omega
    refine ⟨a-2, q, qQ, Or.inr ⟨by omega,avoid,split⟩, cancel_root qQ qp.pos split form ?_ bal⟩
    have exp : (2:ℕ)^a = 2^(a-2)*4 := by
      calc (2:ℕ)^a = 2^(a-2) * 2^2 := by conv_lhs => rw [split, pow_add]
           _ = _ := by norm_num
    omega

lemma bound_after_descent (M : ℕ)
    (branch : ∀ a (Q : Finset ℕ), (∀ p ∈ Q, p.Prime ∧ 3 < p) →
      Disjoint Q {7,17,67,83,331,661} →
      (2^a+1)*8192*(∏ p ∈ Q, (p+1)) = 2^(a+1)*6561*(∏ p ∈ Q, p) →
      2 ≤ ((2^a+1).primeFactors.filter (3 < ·)).card → a ≤ M)
    (a : ℕ) (Q : Finset ℕ) (primes : ∀ p ∈ Q, p.Prime ∧ 3 < p)
    (disj : Disjoint Q {7,17,67,83,331,661})
    (bal : (2^a+1)*8192*(∏ p ∈ Q, (p+1)) = 2^(a+1)*6561*(∏ p ∈ Q, p)) :
    a ≤ max 9 M + 5 := by
  -- An even exponent drops by one. The odd residue classes modulo six
  -- can then move from 1 to 5 to 3, losing two at each step.
  let slack := fun a : ℕ => if a%2 = 0 then 5 else if a%6 = 1 then 4 else if a%6 = 5 then 2 else 0
  suffices aux : a ≤ max 9 M + slack a by
    have : slack a ≤ 5 := by dsimp [slack]; split_ifs <;> decide
    omega
  induction a using Nat.strong_induction_on generalizing Q with
  | h a ih =>
    by_cases small : a ≤ 9
    · have := le_max_left 9 M
      omega
    let roots := (2^a+1).primeFactors.filter (3 < ·)
    have nonempty : 0 < roots.card := by
      by_contra! hz
      have empty : roots = ∅ := Finset.card_eq_zero.mp (by omega)
      let step := fun s : Finset ℕ => s ∪ s.biUnion (fun p => (p+1).primeFactors.filter (3 < ·))
      have eq : step^[a+1] roots = Q := reconstruct a Q primes bal
      have fixed : step ∅ = ∅ := by simp [step]
      rw [empty, Function.iterate_fixed fixed] at eq
      rw [← eq, Finset.prod_empty, Finset.prod_empty, Nat.mul_one, Nat.mul_one, pow_succ] at bal
      omega
    by_cases one : roots.card = 1
    · obtain ⟨b,q,hq,shift,newbal⟩ := single_step (by omega) primes bal one
      have earlier : b < a := by rcases shift with h | h <;> omega
      have smaller := ih b earlier (Q.erase q) (fun p hp => primes p (Finset.mem_of_mem_erase hp))
        (disj.mono_left (Finset.erase_subset ..)) newbal
      have credit : b + slack a ≥ a + slack b := by
        dsimp [slack]
        rcases shift with h | h <;> split_ifs <;> omega
      omega
    · have limit := branch a Q primes disj bal (by change 2 ≤ roots.card; omega)
      have := le_max_right 9 M
      omega

def H1 : Prop :=
  ∃ A : ℕ, ∀ a : ℕ,
    let roots := (2^a+1).primeFactors.filter (3 < ·)
    roots.card = 2 →
    let Q := (fun s : Finset ℕ => s ∪ s.biUnion
      (fun p => (p+1).primeFactors.filter (3 < ·)))^[a+1] roots
    Disjoint Q {7,17,67,83,331,661} →
    (2^a+1)*8192*(∏ p ∈ Q, (p+1)) = 2^(a+1)*6561*(∏ p ∈ Q, p) →
    a ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ a : ℕ,
    let roots := (2^a+1).primeFactors.filter (3 < ·)
    3 ≤ roots.card →
    let Q := (fun s : Finset ℕ => s ∪ s.biUnion
      (fun p => (p+1).primeFactors.filter (3 < ·)))^[a+1] roots
    Disjoint Q {7,17,67,83,331,661} →
    (2^a+1)*8192*(∏ p ∈ Q, (p+1)) = 2^(a+1)*6561*(∏ p ∈ Q, p) →
    a ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1.H1 := by
  rintro ⟨A, two⟩ ⟨B, many⟩
  refine ⟨max 9 (max A B) + 5, ?_⟩
  intro n hn hrepeated he _ _ _
  let a := padicValNat 2 n
  let roots := (2^a+1).primeFactors.filter (3 < ·)
  let step := fun s : Finset ℕ => s ∪ s.biUnion (fun p => (p+1).primeFactors.filter (3 < ·))
  obtain ⟨primes,disj,balance⟩ := unitary_support hn hrepeated he
  apply bound_after_descent (max A B) _ a (step^[a+1] roots) primes disj balance
  intro b Q hp hdis hbal count
  have eq := reconstruct b Q hp hbal
  rw [← eq] at hdis hbal
  by_cases h : ((2^b+1).primeFactors.filter (3 < ·)).card = 2
  · exact (two b h hdis hbal).trans (le_max_left A B)
  · exact (many b (by omega) hdis hbal).trans (le_max_right A B)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R3
