import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1

/-!
# Counting two residue classes in the exponent-five branch

Let P be the simple odd prime factors other than 3. At most five members of P
are 2 modulo 3, since each successor consumes a factor of 3. Each member p
that is 19 modulo 24 uses a distinct prime from this same set as a divisor
of (p+1)/4. Apart from these ten exceptions, every member is 1 modulo 12 or
7 modulo 24.

To pass from a bound on cardinality to one on the exponent, include the
2-component among the denominators of the unitary abundancy product.
For a nonempty set of k denominators with product of (1+1/y) equal to b/a,
the minimum is at most k*b. Removing it bounds the next numerator and
denominator, so induction bounds every component. This gives an elementary
quantitative form of the fixed-number-of-primes finiteness principle of
Subbarao and Warren, “Unitary perfect numbers,” Theorem 4 (doi:10.4153/CMB-1966-018-4).
-/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R2


private theorem gap (s : Finset ℕ) (x : ℕ) (hx : ∀ y ∈ s, x ≤ y) :
    x * (∏ y ∈ s, (y+1)) ≤ x * (∏ y ∈ s, y) + s.card * (∏ y ∈ s, (y+1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert y s hy ih =>
    have hi := ih (fun z hz => hx z (Finset.mem_insert_of_mem hz))
    have hxy := hx y (Finset.mem_insert_self ..)
    simp only [Finset.prod_insert hy, Finset.card_insert_of_notMem hy]
    nlinarith only [Nat.mul_le_mul_right y hi,
      Nat.mul_le_mul_right (∏ z ∈ s, (z+1)) (show x ≤ y+1 by omega),
      Nat.zero_le (s.card * ∏ z ∈ s, (z+1))]

/-- The denominators in an exact product of bounded length are uniformly
bounded when the numerator and denominator of its value are bounded. -/
private theorem component_bound (k M : ℕ) : ∃ B : ℕ, ∀ (s : Finset ℕ) (a b : ℕ),
    s.card ≤ k → 0 < a → a ≤ M → b ≤ M → (∀ y ∈ s, 0 < y) →
    a * (∏ y ∈ s, (y+1)) = b * (∏ y ∈ s, y) → ∀ y ∈ s, y ≤ B := by
  induction k generalizing M with
  | zero =>
    refine ⟨0, fun s a b hk _ _ _ _ _ => ?_⟩
    simp_all
  | succ k ih =>
    let T := (k+1)*M
    obtain ⟨B, hB⟩ := ih (M*(T+1))
    refine ⟨max T B, fun s a b hk ha haM hbM hpos E y hy => ?_⟩
    have hne : s.Nonempty := ⟨y, hy⟩
    let x := s.min' hne
    have hx : x ∈ s := s.min'_mem hne
    let U := ∏ z ∈ s, (z+1)
    let V := ∏ z ∈ s, z
    have hVU : V < U := Finset.prod_lt_prod_of_nonempty hpos (fun z _ => Nat.lt_succ_self z) hne
    have hU : 0 < U := by omega
    change a * U = b * V at E
    have hab : a < b := by
      by_contra! hle
      have h1 := Nat.mul_lt_mul_of_pos_left hVU ha
      have h2 := Nat.mul_le_mul_right V hle
      omega
    have hg := gap s x (fun z hz => s.min'_le z hz)
    change x*U ≤ x*V+s.card*U at hg
    have haux : (b*x)*U ≤ (a*x+b*s.card)*U := by
      calc (b*x)*U ≤ b*(x*V+s.card*U) := by simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left b hg
           _ = x*(b*V)+b*s.card*U := by ring
           _ = (a*x+b*s.card)*U := by rw [← E]; ring
    have hcancel := Nat.le_of_mul_le_mul_right haux hU
    have hstep := Nat.mul_le_mul_right x (show a+1 ≤ b from hab)
    have hsmall := Nat.mul_le_mul hk hbM
    have hxT : x ≤ T := by dsimp [T]; nlinarith only [hcancel,hstep,hsmall]
    by_cases heq : y = x
    · exact heq ▸ hxT.trans (le_max_left _ _)
    · dsimp only [U,V] at E
      rw [← Finset.mul_prod_erase s (fun z => z+1) hx,
          ← Finset.mul_prod_erase s (fun z => z) hx] at E
      have hrem := hB (s.erase x) (a*(x+1)) (b*x)
        (by rw [Finset.card_erase_of_mem hx]; omega) (by positivity)
        (Nat.mul_le_mul haM (by omega)) (Nat.mul_le_mul hbM (by omega))
        (fun z hz => hpos z (Finset.mem_of_mem_erase hz)) (by simpa [mul_assoc] using E)
        y (Finset.mem_erase.mpr ⟨heq, hy⟩)
      exact hrem.trans (le_max_right _ _)


open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (kernel_balance_one facts prime_dvd_prime_pow exists_prime_mod3)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 (budget_kernel3)

private theorem count_classes {P : Finset ℕ} {m : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3 : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    P.card ≤ (P.filter (fun p => p % 12 = 1)).card + (P.filter (fun p => p % 24 = 7)).card + 10 := by
  classical
  let S := P.filter (fun p => p % 3 = 2)
  let T := P.filter (fun p => p % 24 = 19)
  have hS : S.card ≤ 5 := by
    by_contra! hlo
    apply budget_kernel3 hP h3 E (Finset.filter_subset _ _ : S ⊆ P)
    have hdiv : 3^S.card ∣ ∏ p ∈ S, (p+1) := by
      rw [← Finset.prod_const]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => by have := (Finset.mem_filter.mp hp).2; omega)
    exact ((pow_dvd_pow 3 (show 5+1 ≤ S.card by omega)).trans hdiv).trans (dvd_mul_left _ _)
  obtain ⟨source, _, unique, _⟩ := facts hP (prime_dvd_prime_pow (z := 3) (by norm_num)) E
  have hw : ∀ p ∈ T, ∃ q, q ∈ S ∧ q ∣ p+1 := by
    intro p hp
    obtain ⟨hpP, hr⟩ := Finset.mem_filter.mp hp
    obtain ⟨q,hq,hd,hrq⟩ := exists_prime_mod3 ((p+1)/4) (by omega)
    have hodd : q ≠ 2 := by rintro rfl; omega
    have hn3 : q ∉ ({3} : Finset ℕ) := by simpa using (show q ≠ 3 by omega)
    have hd' : q ∣ p+1 := hd.trans ⟨4, by omega⟩
    exact ⟨q, Finset.mem_filter.mpr ⟨source q hq hodd hn3 p hpP hd', hrq⟩, hd'⟩
  choose! f hf using hw
  have hT : T.card ≤ S.card := Finset.card_le_card_of_injOn f (fun p hp => (hf p hp).1) (by
    intro p hp r hr heq
    have hfP := Finset.mem_filter.mp (hf p hp).1
    obtain ⟨hq,hq2⟩ := hP _ hfP.1
    apply unique (f p) hq hq2 (by simp only [Finset.mem_singleton]; intro he; exact h3 (he ▸ hfP.1))
      p (Finset.mem_filter.mp hp).1 r (Finset.mem_filter.mp hr).1 (hf p hp).2
    rw [heq]
    exact (hf r hr).2)
  let A := P.filter (fun p => p % 12 = 1)
  let B := P.filter (fun p => p % 24 = 7)
  have hcover : P ⊆ (A ∪ B) ∪ (S ∪ T) := by
    intro p hp
    have hodd := (hP p hp).1.odd_of_ne_two (hP p hp).2
    have hnd : ¬3 ∣ p := fun hd => h3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three (hP p hp).1).mp hd) ▸ hp)
    have hmod := Nat.odd_iff.mp hodd
    simp only [Finset.mem_union, A, B, S, T, Finset.mem_filter, hp, true_and]
    omega
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le (A ∪ B) (S ∪ T)
  have hv := Finset.card_union_le A B
  have hw' := Finset.card_union_le S T
  change P.card ≤ A.card+B.card+10
  omega

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    262 ≤ padicValNat 2 n →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144,
        524288} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (padicValNat 2 n % 2 = 1 →
      ((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 4) →
    (n.primeFactors.filter (fun p => p % 12 = 1)).card ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    262 ≤ padicValNat 2 n →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144,
        524288} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (padicValNat 2 n % 2 = 1 →
      ((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 4) →
    (n.primeFactors.filter (fun p => p % 24 = 7)).card ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩
  obtain ⟨C,hC⟩ := component_bound (A+B+11) 486
  refine ⟨C, fun n h hiff he hlo hsieve hfermat hodd => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  let P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ))
  let m := padicValNat 2 n
  rw [ha, he] at E
  change (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m+1) * 3^5 * ∏ p ∈ P, p at E
  have hpSub : P ⊆ n.primeFactors := fun _ hp => Finset.mem_of_mem_erase (Finset.mem_filter.mp hp).1
  have h1 := (Finset.card_le_card (Finset.filter_subset_filter (fun p => p % 12 = 1) hpSub)).trans
    (hA n h hiff he hlo hsieve hfermat hodd)
  have h2 := (Finset.card_le_card (Finset.filter_subset_filter (fun p => p % 24 = 7) hpSub)).trans
    (hB n h hiff he hlo hsieve hfermat hodd)
  have hc := count_classes (P := P) hP h3P E
  have hm0 : m ≠ 0 := by dsimp [m]; omega
  have hx : 2^m ∉ P := by
    intro hp
    have hEq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hP _ hp).1).mp (dvd_pow_self 2 hm0)
    exact (hP _ hp).2 hEq.symm
  have hcomp := hC (insert (2^m) P) 244 486
    (by rw [Finset.card_insert_of_notMem hx]; omega) (by decide) (by decide) (by decide)
    (by intro y hy; rcases Finset.mem_insert.mp hy with rfl | hmem
        · positivity
        · exact (hP y hmem).1.pos)
    (by simp only [Finset.prod_insert hx]; rw [pow_succ 2 m] at E; linear_combination E)
    (2^m) (Finset.mem_insert_self ..)
  exact m.lt_two_pow_self.le.trans hcomp

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R2
