import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1

/-!
The fixed 5⁴ kernel excludes every configuration with 5 dividing the exponent of 2.
For the remaining exponents the two questions concern the size of prime divisors and the
number of prime factors with multiplicity when all of them come from a fixed finite set.
Their combination bounds the exponent itself by a product bound.

If 5 divides the exponent, 41 divides the binary seed, while 313 divides the 5⁴ kernel.
Uniqueness of odd prime sources forces the chains through 41, 157 and 79. Below 1999 a
finite divisibility certificate leaves at most 32 possible simple primes. The disjoint-path
estimate from PR #35099 bounds the contribution above that cutoff. The resulting rational
upper bound is less than two, contradicting the unitary-perfect balance.
-/

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H2.R1.H1.R2 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H2.R1.H1
-- Credit: @AlfredMelson

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1_H1_R2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

theorem source_rules {P : Finset ℕ} {m : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+5^4)*∏ p ∈ P,(p+1) = 2^(m+1)*5^4*∏ p ∈ P,p)
    (h4 : m%4=2) (h5 : 5 ∣ m) :
    ∀ p ∈ P, ∀ q : ℕ, q.Prime → q≠2 → q≠5 → q ∣ p+1 →
      q ∈ P ∧ ((q = 3 → p = 41) ∧ (q = 7 → p = 41) ∧ q ≠ 41 ∧ (q = 79 → p = 157) ∧ (q = 157 → p = 313) ∧ q ≠ 313) ∧ ¬q*q ∣ p+1 := by
  have hns : ∀ {q : ℕ}, q ≠ 5 → q ∉ ({5} : Finset ℕ) := fun h x => h (Finset.mem_singleton.mp x)
  obtain ⟨s1,s2,s3,s4,_,s6,s7,s8⟩ := facts hP (prime_dvd_prime_pow (z:=5) (e:=4) (by norm_num)) E
  have h20 : m % (2*10) = 10 := by omega
  have hpow := one_add_pow_dvd_of_odd_mul (z:=2) h20
  have h41 : 41 ∣ 2^m+1 :=
    (show 41 ∣ 1+2^10 by decide).trans (by simpa only [add_comm 1] using hpow)
  have a41 := s2 41 (by norm_num) (by decide) (by decide) h41
  have a313 := s7 313 (by norm_num) (by decide) (by decide) (by decide)
  have a157 := s1 157 (by norm_num) (by decide) (by decide) 313 a313 (by decide)
  intro p hp q hq hq2 hq5 hd
  refine ⟨s1 q hq hq2 (hns hq5) p hp hd, ?_, s6 q hq hq2 (hns hq5) p hp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl; exact s3 _ hq hq2 (hns hq5) p hp 41 a41 hd (by decide)
  · rintro rfl; exact s3 _ hq hq2 (hns hq5) p hp 41 a41 hd (by decide)
  · rintro rfl; exact s4 41 hq hq2 (hns hq5) h41 p hp hd
  · rintro rfl; exact s3 _ hq hq2 (hns hq5) p hp 157 a157 hd (by decide)
  · rintro rfl; exact s3 _ hq hq2 (hns hq5) p hp 313 a313 hd (by decide)
  · rintro rfl; exact s8 313 hq hq2 (hns hq5) (by decide) p hp hd

theorem witnessed_prefix {P : Finset ℕ} (U W : List ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (no5 : 5 ∉ P)
    (rules : ∀ p ∈ P, ∀ q : ℕ, q.Prime → q≠2 → q≠5 → q ∣ p+1 →
      q ∈ P ∧ ((q = 3 → p = 41) ∧ (q = 7 → p = 41) ∧ q ≠ 41 ∧ (q = 79 → p = 157) ∧ (q = 157 → p = 313) ∧ q ≠ 313) ∧ ¬q*q ∣ p+1)
    (cert : W.zipIdx.all (fun t : ℕ × ℕ => let q := t.1; let p := t.2; decide ((1 < q ∧ q < p ∧ q ∣ p) ∨ (p ≤ 2 ∨ p = 5 ∨ p ∈ U) ∨
        (q.Prime ∧ q ≠ 2 ∧ q ≠ 5 ∧ q < p ∧ q ∣ p+1 ∧ (q ∉ U ∨ ¬ ((q = 3 → p = 41) ∧ (q = 7 → p = 41) ∧ q ≠ 41 ∧ (q = 79 → p = 157) ∧ (q = 157 → p = 313) ∧ q ≠ 313) ∨ q*q ∣ p+1)))) = true) :
    ∀ p : ℕ, p ∈ P → p < W.length → p ∈ U := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hp hlt
    have hlen : p < (W.zipIdx).length := by simpa using hlt
    have row := List.all_eq_true.mp cert _ (List.getElem_mem (l:=W.zipIdx) (n:=p) hlen)
    rw [List.getElem_zipIdx] at row
    simp only [Nat.zero_add, decide_eq_true_eq] at row
    obtain ⟨hpp,hp2⟩ := hP p hp
    rcases row with ⟨hlo,hhi,hd⟩ | (hlow | h5 | hr) | ⟨hq,h2,h5,hltq,hd,fail⟩
    · rcases (Nat.dvd_prime hpp).mp hd with he | he <;> omega
    · have := hpp.two_le; omega
    · exact (no5 (h5 ▸ hp)).elim
    · exact hr
    · obtain ⟨hqP,ho,hsq⟩ := rules p hp _ hq h2 h5 hd
      rcases fail with hu | bad | sq
      · exact (hu (ih _ hltq hqP (by omega))).elim
      · exact (bad ho).elim
      · exact (hsq sq).elim

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem small_candidates {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (no5 : 5 ∉ P)
    (rules : ∀ p ∈ P, ∀ q : ℕ, q.Prime → q≠2 → q≠5 → q ∣ p+1 →
      q ∈ P ∧ ((q = 3 → p = 41) ∧ (q = 7 → p = 41) ∧ q ≠ 41 ∧ (q = 79 → p = 157) ∧ (q = 157 → p = 313) ∧ q ≠ 313) ∧ ¬q*q ∣ p+1) :
    ∀ p : ℕ, p ∈ P → p < 1999 → p ∈ ([3, 7, 19, 31, 37, 41, 61, 73, 79, 127, 151, 157, 199, 313, 379, 397, 487, 499, 607, 619, 739, 757, 991, 997, 1213, 1237, 1249, 1279, 1459, 1549, 1951, 1993] : List ℕ) := by
  let U : List ℕ := [3, 7, 19, 31, 37, 41, 61, 73, 79, 127, 151, 157, 199, 313, 379, 397, 487, 499, 607, 619, 739, 757, 991, 997, 1213, 1237, 1249, 1279, 1459, 1549, 1951, 1993]
  let W : List ℕ := [
  [0, 0, 0, 0, 2, 0, 2, 0, 2, 3, 2, 3, 2, 7, 2, 3, 2, 3, 2, 0, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 3, 2, 7],
  [2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 3, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 7, 2, 3],
  [2, 3, 2, 13, 2, 3, 2, 3, 2, 11, 2, 3, 2, 3, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 3, 2, 7, 2, 3, 2, 3, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 3],
  [2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 41, 2, 3, 2, 3, 2, 13, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 3, 2, 97, 2, 3, 2, 3, 2, 0],
  [2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 7, 2, 3, 2, 3, 2, 23, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3],
  [2, 3, 2, 11, 2, 3, 2, 3, 2, 7, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 17, 2, 3, 2, 5, 2, 139, 2, 3, 2, 3, 2, 71, 2, 3, 2, 7, 2, 17, 2, 3, 2, 3, 2, 5, 2, 3, 2, 13],
  [2, 7, 2, 3, 2, 5, 2, 7, 2, 3, 2, 3, 2, 0, 2, 3, 2, 3, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 83, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 3, 2, 7],
  [2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 19, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 11, 2, 3, 2, 13, 2, 0, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3],
  [2, 3, 2, 13, 2, 3, 2, 11, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 3, 2, 211, 2, 3, 2, 5, 2, 7, 2, 3, 2, 3, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3],
  [2, 11, 2, 3, 2, 5, 2, 229, 2, 3, 2, 3, 2, 29, 2, 3, 2, 3, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 3, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 3, 2, 17, 2, 3, 2, 7, 2, 0],
  [2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 3, 2, 131, 2, 3, 2, 17, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 271, 2, 3, 2, 5, 2, 137, 2, 3],
  [2, 19, 2, 7, 2, 3, 2, 3, 2, 13, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2, 3, 2, 19, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3],
  [2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 307, 2, 3, 2, 3, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 79, 2, 3, 2, 5, 2, 7, 2, 3, 2, 3, 2, 7, 2, 3, 2, 3, 2, 11],
  [2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 331, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 337, 2, 3, 2, 3, 2, 7, 2, 3, 2, 3, 2, 5, 2, 3, 2, 13, 2, 173, 2, 3, 2, 5, 2, 17, 2, 3],
  [2, 3, 2, 19, 2, 3, 2, 7, 2, 71, 2, 3, 2, 23, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 367, 2, 3, 2, 11, 2, 0, 2, 3, 2, 3, 2, 5, 2, 3, 2, 7],
  [2, 47, 2, 3, 2, 5, 2, 0, 2, 3, 2, 3, 2, 7, 2, 3, 2, 13, 2, 7, 2, 3, 2, 3, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 197, 2, 3, 2, 7, 2, 13, 2, 3, 2, 3, 2, 17],
  [2, 3, 2, 11, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 3, 2, 103, 2, 3, 2, 3, 2, 83, 2, 3, 2, 7, 2, 5, 2, 3, 2, 3, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3],
  [2, 23, 2, 7, 2, 3, 2, 3, 2, 43, 2, 3, 2, 3, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 439, 2, 3, 2, 3, 2, 13, 2, 3, 2, 3, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 29],
  [2, 17, 2, 3, 2, 5, 2, 227, 2, 3, 2, 3, 2, 11, 2, 3, 2, 7, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 7, 2, 3, 2, 3, 2, 23, 2, 3, 2, 3, 2, 13],
  [2, 3, 2, 3, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 11, 2, 3, 2, 3, 2, 7, 2, 3, 2, 3, 2, 11, 2, 3, 2, 3, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3],
  [2, 7, 2, 17, 2, 3, 2, 19, 2, 101, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 3, 2, 11, 2, 3, 2, 17, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 3],
  [2, 263, 2, 3, 2, 5, 2, 7, 2, 3, 2, 3, 2, 7, 2, 3, 2, 11, 2, 107, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 17, 2, 3, 2, 3, 2, 547, 2, 3, 2, 3, 2, 7],
  [2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 281, 2, 3, 2, 7, 2, 113, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3],
  [2, 3, 2, 577, 2, 3, 2, 13, 2, 19, 2, 3, 2, 3, 2, 5, 2, 3, 2, 7, 2, 293, 2, 3, 2, 5, 2, 11, 2, 3, 2, 3, 2, 7, 2, 3, 2, 3, 2, 29, 2, 3, 2, 3, 2, 5, 2, 3, 2, 11],
  [2, 601, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 3, 2, 23, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 29, 2, 0],
  [2, 3, 2, 7, 2, 5, 2, 3, 2, 3, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 19, 2, 3, 2, 3, 2, 0, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3],
  [2, 3, 2, 163, 2, 3, 2, 3, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 3, 2, 661, 2, 3, 2, 5, 2, 83, 2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19],
  [2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 3, 2, 29, 2, 3, 2, 3, 2, 37, 2, 3, 2, 3, 2, 5, 2, 3, 2, 7, 2, 691, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 7],
  [2, 3, 2, 23, 2, 5, 2, 3, 2, 3, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 89, 2, 3, 2, 3, 2, 11, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 11, 2, 3, 2, 5, 2, 181, 2, 3],
  [2, 3, 2, 727, 2, 3, 2, 31, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 3, 2, 7, 2, 3, 2, 3, 2, 149, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3],
  [2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 3, 2, 17, 2, 3, 2, 37, 2, 7, 2, 3, 2, 3, 2, 5, 2, 3, 2, 11, 2, 383, 2, 3, 2, 5, 2, 29, 2, 3, 2, 23, 2, 193, 2, 3, 2, 7, 2, 0],
  [2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 7, 2, 3, 2, 3, 2, 11, 2, 3, 2, 19, 2, 79, 2, 3, 2, 3, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 17, 2, 3],
  [2, 3, 2, 7, 2, 3, 2, 3, 2, 7, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 811, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 23, 2, 3, 2, 3, 2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17],
  [2, 13, 2, 3, 2, 5, 2, 829, 2, 3, 2, 11, 2, 13, 2, 3, 2, 3, 2, 167, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 7, 2, 3, 2, 3, 2, 17],
  [2, 3, 2, 13, 2, 5, 2, 3, 2, 3, 2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2, 3, 2, 431, 2, 3, 2, 11, 2, 7, 2, 3, 2, 3, 2, 5, 2, 3, 2, 37, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3],
  [2, 17, 2, 877, 2, 3, 2, 7, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 223, 2, 3, 2, 3, 2, 179, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7],
  [2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 3, 2, 7, 2, 3, 2, 23, 2, 17, 2, 3, 2, 3, 2, 5, 2, 3, 2, 31, 2, 229, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 19, 2, 3, 2, 3, 2, 43],
  [2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 467, 2, 3, 2, 3, 2, 937, 2, 3, 2, 3, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 3, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3],
  [2, 3, 2, 11, 2, 3, 2, 3, 2, 23, 2, 3, 2, 3, 2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 41, 2, 3, 2, 3, 2, 967, 2, 3, 2, 13, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 3],
  [2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 37, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 3, 2, 5, 2, 3, 2, 3, 2, 7, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 3, 2]
].flatten
  have hn : W.length = 1999 := by decide +kernel
  have cert : W.zipIdx.all (fun t : ℕ × ℕ => let q := t.1; let p := t.2; decide ((1 < q ∧ q < p ∧ q ∣ p) ∨ (p ≤ 2 ∨ p = 5 ∨ p ∈ U) ∨
        (q.Prime ∧ q ≠ 2 ∧ q ≠ 5 ∧ q < p ∧ q ∣ p+1 ∧ (q ∉ U ∨ ¬ ((q = 3 → p = 41) ∧ (q = 7 → p = 41) ∧ q ≠ 41 ∧ (q = 79 → p = 157) ∧ (q = 157 → p = 313) ∧ q ≠ 313) ∨ q*q ∣ p+1)))) = true := by decide +kernel
  simpa only [hn] using witnessed_prefix U W hP no5 rules cert
-- Disjoint-path estimates adapted from aroth01's proof in PR #35099.
theorem balance_q {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*626*∏ p ∈ P,(p+1) = 2^(m+1)*625*∏ p ∈ P,p) :
    (1 + 1 / (2 : ℚ) ^ m) * (626 / 625) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) := Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
  have hcast : ((2 : ℚ) ^ m + 1) * 626 * ∏ p ∈ P, ((p : ℚ) + 1) = 2 ^ (m + 1) * 625 * ∏ p ∈ P, (p : ℚ) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) E
    push_cast at h
    exact h
  have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
    field_simp
  have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
  rw [e]
  field_simp
  rw [pow_succ] at hcast
  linarith


theorem upper_tail {P : Finset ℕ} {X : List ℕ} {N : ℕ} (hN5 : 5 ≤ N)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (s1 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, c ∣ p + 1 → c ∈ P)
    (s3 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p')
    (led : ¬ 5^5 ∣ ∏ p ∈ P, (p+1))
    (hcl : ∀ p ∈ P, p < N → p ∈ X) :
    ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1/(p:ℚ)) ≤
    (((N : ℚ)+1) / ((N:ℚ)-1)) ^ (X.length+4) * (((N:ℚ)+1)/((N:ℚ)-3)) := by
  classical
  obtain ⟨g, hg⟩ := exists_child ({5} : Finset ℕ)
  have hnz : ∀ {c : ℕ}, c ∉ ({5} : Finset ℕ) → c ≠ 5 := fun h h' => h (Finset.mem_singleton.mpr h')
  have hQP : ∀ q ∈ P.filter (fun p => p ∉ X), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hQX : ∀ q ∈ P.filter (fun p => p ∉ X), q ∉ X := fun q hq => (Finset.mem_filter.mp hq).2
  have hQN : ∀ q ∈ P.filter (fun p => p ∉ X), N ≤ q := fun q hq => by
    by_contra hlt
    exact hQX q hq (hcl q (hQP q hq) (by omega))
  have hgp : ∀ p ∈ P, g p ≠ 1 → (g p).Prime ∧ g p ≠ 2 ∧ g p ≠ 5 ∧ g p ∈ P ∧ 2 * g p ≤ p + 1 :=
    fun p hp h1 => by
      obtain ⟨hc, hc2, hcN⟩ := (hg p).2.2.1 h1
      exact ⟨hc, hc2, hnz hcN, s1 _ hc hc2 (hnz hcN) p hp (hg p).1,
        two_mul_le hc hc2 (hP p hp).1 (hP p hp).2 (hg p).1⟩
  have hg1 : ∀ q ∈ P.filter (fun p => p ∉ X), g q ∈ P.filter (fun p => p ∉ X) → g q ≠ 1 :=
    fun q _ hgq h1 => by
      have := (hP _ (hQP _ hgq)).1
      rw [h1] at this
      exact Nat.not_prime_one this
  have hpath := path_bound g (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1)) (P.filter (fun p => p ∉ X)).card
    (P.filter (fun p => p ∉ X)) rfl
    (fun q hq => (hP q (hQP q hq)).1.pos)
    (fun q hq hgq => by
      obtain ⟨hc, -, -, -, h2⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      have := hc.two_le
      omega)
    (fun q hq q' hq' hgq he => by
      obtain ⟨hc, hc2, hcz, -, -⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact s3 _ hc hc2 hcz q (hQP q hq) q' (hQP q' hq') (hg q).1 (he ▸ (hg q').1))
    (fun q hq => one_add_le_B (hP q (hQP q hq)).1.two_le)
    (fun q hq hgq => by
      obtain ⟨hc, -, -, -, h2⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact B_step hc.two_le h2)
  generalize hRdef : (P.filter (fun p => p ∉ X)).filter (fun q => g q ∉ P.filter (fun p => p ∉ X)) = R at hpath
  have hRQ : ∀ q ∈ R, q ∈ P.filter (fun p => p ∉ X) := fun q hq => by
    rw [← hRdef] at hq
    exact (Finset.mem_filter.mp hq).1
  have hRg : ∀ q ∈ R, g q ∉ P.filter (fun p => p ∉ X) := fun q hq => by
    rw [← hRdef] at hq
    exact (Finset.mem_filter.mp hq).2
  have hRP : ∀ q ∈ R, q ∈ P := fun q hq => hQP q (hRQ q hq)
  have hA : ∀ q ∈ R, g q ≠ 1 → g q ∈ X := fun q hq h1 => by
    have hqP := hRP q hq
    obtain ⟨hc, hc2, hcz, hcP, -⟩ := hgp q hqP h1
    have hcX : g q ∈ X := by
      by_contra hcX
      exact hRg q hq (Finset.mem_filter.mpr ⟨hcP, hcX⟩)
    exact hcX
  have hN2 : (2 : ℚ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hβN : ∀ q ∈ R, ((q : ℚ) + 1) / ((q : ℚ) - 1) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := fun q hq =>
    B_anti (by omega) (hQN q (hRQ q hq))
  have hβ0 : ∀ q ∈ R, (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq =>
    B_nonneg (hP q (hRP q hq)).1.pos
  have hBN1 : (1 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hcardA : (R.filter (fun q => g q ≠ 1)).card ≤ X.length := by
    refine (Finset.card_le_card_of_injOn g (t := X.toFinset) ?_ ?_).trans (List.toFinset_card_le _)
    · intro q hq
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      exact Finset.mem_coe.mpr (List.mem_toFinset.mpr (hA q hqR h1))
    · intro q hq q' hq' he
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      obtain ⟨hqR', -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq')
      obtain ⟨hc, hc2, hcz, -, -⟩ := hgp q (hRP q hqR) h1
      exact s3 _ hc hc2 hcz q (hRP q hqR) q' (hRP q' hqR') (hg q).1 (he ▸ (hg q').1)

  have hcardB : ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card ≤ 4 := by
    by_contra h
    apply led
    let T := (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q+1)
    have hT : T ⊆ P := fun q hq => hRP q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have h1 : 5^T.card ∣ ∏ q ∈ T,(q+1) := by
      rw [← Finset.prod_const]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun q hq => (Finset.mem_filter.mp hq).2
    exact (pow_dvd_pow 5 (show 5 ≤ T.card by change ¬ T.card ≤ 4 at h; omega)).trans (h1.trans (Finset.prod_dvd_prod_of_subset _ _ _ hT))
  have hpow : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 5 ∣ q + 1), ∃ k, q + 1 = 2 ^ k :=
    fun q hq => by
      obtain ⟨hq1, hzq⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hg1'⟩ := Finset.mem_filter.mp hq1
      refine two_pow_of_no_odd_prime fun c hc hc2 hcd => ?_
      have := (hg q).2.1 (not_not.mp hg1') c hc hc2 hcd
      rw [Finset.mem_singleton] at this
      exact hzq (this ▸ hcd)
  have hprodC : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 5 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 3) := by
    refine tail_bound _ _ N rfl (by omega)
      (fun q hq => hQN q (hRQ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1))
      (fun q hq q' hq' hlt => ?_)
    obtain ⟨k, hk⟩ := hpow q hq
    obtain ⟨k', hk'⟩ := hpow q' hq'
    have hkk : k < k' := by
      by_contra hge
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hge)
      omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt hkk)
    rw [pow_succ] at this
    omega
  have hprodA : ∏ q ∈ R.filter (fun q => g q ≠ 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (R.filter (fun q => g q ≠ 1)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp hq).1)
      (fun q hq => hβN q (Finset.mem_filter.mp hq).1)
  have hprodB : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
      (fun q hq => hβN q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
  have hsplit1 := Finset.prod_filter_mul_prod_filter_not R (fun q => g q ≠ 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hsplit2 := Finset.prod_filter_mul_prod_filter_not (R.filter (fun q => ¬ g q ≠ 1)) (fun q => 5 ∣ q + 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hpowle : (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (R.filter (fun q => g q ≠ 1)).card *
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (X.length + 4) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hBN1 (Nat.add_le_add hcardA hcardB)
  have hT0 : (0 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 3) := by
    have : (5 : ℚ) ≤ N := by exact_mod_cast hN5
    exact div_nonneg (by linarith) (by linarith)
  have hB0 : (0 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := le_trans zero_le_one hBN1
  have hRbound : ∏ q ∈ R, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (X.length + 4) * (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    rw [← hsplit1, ← hsplit2, ← mul_assoc]
    refine mul_le_mul (le_trans (mul_le_mul hprodA hprodB ?_ (pow_nonneg hB0 _)) hpowle) hprodC ?_
      (pow_nonneg hB0 _)
    · exact Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    · exact Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  exact hpath.trans hRbound

theorem five_ledger {m : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (no5 : 5 ∉ P)
    (E : (2^m+1)*626*∏ p ∈ P,(p+1) = 2^(m+1)*625*∏ p ∈ P,p) :
    ¬5^5 ∣ ∏ p ∈ P,(p+1) := by
  intro hd
  have h1 := hd.trans (dvd_mul_left (∏ p ∈ P,(p+1)) ((2^m+1)*626))
  rw [E] at h1
  have h2 : 625 * 5 ∣ 625 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
    simpa only [mul_left_comm, mul_assoc] using (show 625*5 ∣ 2^(m+1)*625*∏ p ∈ P,p from h1)
  have h3 : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp h3 with h4 | h4
  · have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h4)
    omega
  · obtain ⟨p, hp, hpd⟩ := (Prime.dvd_finsetProd_iff (Nat.Prime.prime (by norm_num)) _).mp h4
    have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) (hP p hp).1).mp hpd
    exact no5 (h5 ▸ hp)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem numeric :
    (1+1/(2:ℚ)^64)*(626/625) * (∏ p ∈ ([3, 7, 19, 31, 37, 41, 61, 73, 79, 127, 151, 157, 199, 313, 379, 397, 487, 499, 607, 619, 739, 757, 991, 997, 1213, 1237, 1249, 1279, 1459, 1549, 1951, 1993] : List ℕ).toFinset, (1+1/(p:ℚ))) *
      ((2000:ℚ)/1998)^(([3, 7, 19, 31, 37, 41, 61, 73, 79, 127, 151, 157, 199, 313, 379, 397, 487, 499, 607, 619, 739, 757, 991, 997, 1213, 1237, 1249, 1279, 1459, 1549, 1951, 1993] : List ℕ).length+4) * (2000/1996) < 2 := by
  decide +kernel

theorem exclusion {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p=5) (he : n.factorization 5=4)
    (h4 : padicValNat 2 n % 4=2) (hm : 64 ≤ padicValNat 2 n) : ¬5 ∣ padicValNat 2 n := by
  classical
  intro h5
  let possible : List ℕ := [3, 7, 19, 31, 37, 41, 61, 73, 79, 127, 151, 157, 199, 313, 379, 397, 487, 499, 607, 619, 739, 757, 991, 997, 1213, 1237, 1249, 1279, 1459, 1549, 1951, 1993]
  let m := padicValNat 2 n
  let P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5}:Finset ℕ))
  have hzn : 5 ∣ n := (dvd_pow_self 5 two_ne_zero).trans ((hS 5).mpr rfl).2.2
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 5 → n.factorization r = 1 := by
    intro r hr hr2 hr5
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd h.2.ne' (Nat.dvd_of_mem_primeFactors hr)
    by_contra hne
    have hsq : r^2 ∣ n := (hrp.pow_dvd_iff_le_factorization h.2.ne').mpr (by omega)
    exact hr5 ((hS r).mp ⟨hrp,hr2,hsq⟩)
  have hzpf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num,hzn,h.2.ne'⟩
  obtain ⟨hP,E⟩ := kernel_balance_one h hzpf (by decide) hs
  rw [Nat.factorization_def n Nat.prime_two,he] at E
  change (2^m+1)*(1+5^4)*∏ p ∈ P,(p+1) = 2^(m+1)*5^4*∏ p ∈ P,p at E
  change ∀ p ∈ P, p.Prime ∧ p ≠ 2 at hP
  have no5 : 5 ∉ P := fun h => (Finset.mem_filter.mp h).2 (Finset.mem_singleton_self _)
  have hcl := small_candidates hP no5 (source_rules hP E h4 h5)
  obtain ⟨s1,_,s3,_⟩ := facts hP (prime_dvd_prime_pow (z:=5) (e:=4) (by norm_num)) E
  have hns : ∀ {q : ℕ}, q ≠ 5 → q ∉ ({5} : Finset ℕ) := fun h x => h (Finset.mem_singleton.mp x)
  have htail := upper_tail (X:=possible) (N:=1999) (by decide) hP
    (fun c hc hc2 hc5 => s1 c hc hc2 (hns hc5))
    (fun c hc hc2 hc5 => s3 c hc hc2 (hns hc5)) (five_ledger hP no5 E) hcl
  let W := fun p : ℕ => 1+1/(p:ℚ)
  have hsmall : ∏ p ∈ P.filter (fun p => p ∈ possible), W p ≤ ∏ p ∈ possible.toFinset, W p :=
    Finset.prod_le_prod_of_subset_of_one_le
      (fun p hp => List.mem_toFinset.mpr (Finset.mem_filter.mp hp).2)
      (fun p _ => by dsimp [W]; positivity)
      (fun p _ _ => by dsimp [W]; exact le_add_of_nonneg_right (by positivity))
  have hbal := balance_q hP E
  change (1+1/(2:ℚ)^m)*(626/625)*(∏ p ∈ P, W p)=2 at hbal
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p ∈ possible) W] at hbal
  have hm64 : (1:ℚ)/2^m ≤ 1/2^64 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hm)
  have ht : ∏ p ∈ P.filter (fun p => p ∉ possible), W p ≤
      ((2000:ℚ)/1998)^(possible.length+4) * (2000/1996) := by
    convert htail using 1 <;> norm_num
  have hlow : (1+1/(2:ℚ)^m)*(626/625) ≤ (1+1/(2:ℚ)^64)*(626/625) :=
    mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
  have hnonneg : ∀ p : ℕ, 0 ≤ W p := fun p => by dsimp [W]; positivity
  have hle := mul_le_mul hlow (mul_le_mul hsmall ht (Finset.prod_nonneg fun p _ => hnonneg p)
      (Finset.prod_nonneg fun p _ => hnonneg p))
      (mul_nonneg (Finset.prod_nonneg fun p _ => hnonneg p) (Finset.prod_nonneg fun p _ => hnonneg p))
      (by norm_num)
  rw [hbal] at hle
  exact (not_lt_of_ge hle) (by simpa only [W,possible,mul_assoc] using numeric)


/-- All prime divisors of the remaining binary exponents lie below a uniform bound. -/
def H1 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    padicValNat 2 n % 4 = 2 → 128 ≤ padicValNat 2 n →
    (∀ q, q.Prime → 7 ≤ q → q ≤ 420 → ¬ q ∣ padicValNat 2 n) →
    ¬ 5 ∣ padicValNat 2 n → ¬ 27 ∣ padicValNat 2 n →
    ∀ q : ℕ, q.Prime → q ∣ padicValNat 2 n → q ≤ B

/-- With a fixed set of allowed primes, bound the number of factors, counted with multiplicity. -/
def H2 : Prop :=
  ∀ B : ℕ, ∃ L : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    padicValNat 2 n % 4 = 2 → 128 ≤ padicValNat 2 n →
    (∀ q, q.Prime → 7 ≤ q → q ≤ 420 → ¬ q ∣ padicValNat 2 n) →
    ¬ 5 ∣ padicValNat 2 n → ¬ 27 ∣ padicValNat 2 n →
    (∀ q : ℕ, q.Prime → q ∣ padicValNat 2 n → q ≤ B) →
    (padicValNat 2 n).primeFactorsList.length ≤ L

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1.H1 := by
  intro hs hl
  obtain ⟨B, hB⟩ := hs
  obtain ⟨L, hL⟩ := hl B
  refine ⟨(B+1)^L, ?_⟩
  intro n hn hS he h4 ha hsmall _ _ h27
  have h5 := exclusion hn hS he h4 (by omega)
  have hb := hB n hn hS he h4 ha hsmall h5 h27
  have hl := hL n hn hS he h4 ha hsmall h5 h27 hb
  let a := padicValNat 2 n
  have h0 : a ≠ 0 := by dsimp [a]; omega
  calc
    a = a.primeFactorsList.prod := (Nat.prod_primeFactorsList h0).symm
    _ ≤ (B+1)^a.primeFactorsList.length := List.prod_le_pow_card _ _ fun q hq => by
      obtain ⟨hp, hd, -⟩ := Nat.mem_primeFactors.mp (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hq)
      exact (hb q hp hd).trans (Nat.le_succ B)
    _ ≤ (B+1)^L := Nat.pow_le_pow_right (Nat.succ_pos _) hl

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1_H1_R2
