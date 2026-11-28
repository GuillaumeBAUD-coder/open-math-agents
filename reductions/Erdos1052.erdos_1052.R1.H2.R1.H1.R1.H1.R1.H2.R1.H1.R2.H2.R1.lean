import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R2

/-! For exponent eleven at the unique repeated odd prime, split off the
arithmetic obstruction when the component of 2 supplies the prime 5.
For remaining even exponents the earlier sieve leaves either valuation
three (with a forced chain 257, 43, 11) or valuation at least seven.
The stripped balance and earlier sieve are from studer's PR 35627. -/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R2_H2_R1

open Finset
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 (facts)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (kernel_balance_one prime_dvd_prime_pow one_add_pow_dvd_of_odd_mul)

/-- Leaf-weight obstruction when the base-two component contains 5. -/
def H1 : Prop :=
  ∀ {a : ℕ} {Q : Finset ℕ}, 12 ≤ a →
    (∀ q ∈ Q, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 7 ∧ q ≠ 17) →
    (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p →
    5 ∣ 2^a+1 → False

/-- The branch with three further forced simple primes. -/
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({6, 15, 17, 19, 21, 41, 107, 113, 159, 166, 173, 178, 194, 200, 202, 206, 213, 214,
        218, 226, 227, 232, 233, 237, 239, 241, 248, 253, 254, 263, 267, 274, 278, 279, 283, 293,
        296, 298, 299, 301, 305, 309, 326, 327, 329, 331, 337, 341, 344, 365, 367, 373, 381, 382,
        386, 394, 395, 397, 398} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    5 ∣ n → 1000^6 < padicValNat 2 n →
    (∀ d ∈ ({419, 421, 446, 454, 458, 461, 466, 499, 502, 509, 526, 536, 538, 541, 542, 554, 557, 562, 569, 577, 586, 607, 614, 617, 622, 626, 641, 659, 661, 662, 674, 683, 698, 712, 718, 727, 746, 751, 758, 766, 769, 773, 776, 778, 787, 794, 797, 807, 808, 809, 813, 818, 821, 823, 824, 838, 856, 862, 866, 877, 878, 881, 883, 887, 898, 904, 911, 914, 922, 933, 934, 937, 941, 947, 967, 971, 974, 977, 997, 998} : Finset ℕ), padicValNat 2 n % (2*d) ≠ d) →

    padicValNat 2 n % 16 = 8 → 257 ∣ n → 43 ∣ n → 11 ∣ n → padicValNat 2 n ≤ A

/-- All other surviving even exponents are divisible by 128. -/
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({6, 15, 17, 19, 21, 41, 107, 113, 159, 166, 173, 178, 194, 200, 202, 206, 213, 214,
        218, 226, 227, 232, 233, 237, 239, 241, 248, 253, 254, 263, 267, 274, 278, 279, 283, 293,
        296, 298, 299, 301, 305, 309, 326, 327, 329, 331, 337, 341, 344, 365, 367, 373, 381, 382,
        386, 394, 395, 397, 398} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    5 ∣ n → 1000^6 < padicValNat 2 n →
    (∀ d ∈ ({419, 421, 446, 454, 458, 461, 466, 499, 502, 509, 526, 536, 538, 541, 542, 554, 557, 562, 569, 577, 586, 607, 614, 617, 622, 626, 641, 659, 661, 662, 674, 683, 698, 712, 718, 727, 746, 751, 758, 766, 769, 773, 776, 778, 787, 794, 797, 807, 808, 809, 813, 818, 821, 823, 824, 838, 856, 862, 866, 877, 878, 881, 883, 887, 898, 904, 911, 914, 922, 933, 934, 937, 941, 947, 967, 971, 974, 977, 997, 998} : Finset ℕ), padicValNat 2 n % (2*d) ≠ d) →

    128 ∣ padicValNat 2 n → padicValNat 2 n ≤ A

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R2.H2 := by
  rintro obstruction ⟨A,hA⟩ ⟨B,hB⟩
  refine ⟨max A B, ?_⟩
  intro n hperfect unique he old₁ old₂ old₃ hfive lower sieve even
  let a := padicValNat 2 n
  have hn0 := hperfect.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hp := Nat.prime_of_mem_primeFactors hr
    have pos := hp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have upper : ¬2 ≤ n.factorization r := fun h =>
      hr3 ((unique r).mp ⟨hp,hr2,(hp.pow_dvd_iff_le_factorization hn0).mpr h⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three,h3n,hn0⟩
  obtain ⟨hP,E⟩ := kernel_balance_one hperfect h3pf (by decide) hs
  rw [he, Nat.factorization_def n Nat.prime_two] at E
  let P := (n.primeFactors.erase 2).filter (fun r => ¬r ∈ ({3} : Finset ℕ))
  have h3P : 3 ∉ P := by simp [P]
  obtain ⟨advance,seed,_,_,_,_,from3,_⟩ := facts hP
    (prime_dvd_prime_pow (e:=11) (by decide : Nat.Prime 3)) E
  have fixed := E1052Strip.forced_fixed advance from3
  have stripped := E1052Strip.strip_eleven fixed E
  have no2 : a%4 ≠ 2 := by
    intro bad
    have hd := one_add_pow_dvd_of_odd_mul (z:=2) (e0:=2) bad
    have hQ : ∀ q ∈ P \ {7,17,67,83,331,661}, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 7 ∧ q ≠ 17 := by
      intro q hq
      obtain ⟨hq,hn⟩ := mem_sdiff.mp hq
      exact ⟨(hP q hq).1,(hP q hq).2,fun e => h3P (e ▸ hq),
        fun e => hn (by simp [e]),fun e => hn (by simp [e])⟩
    norm_num [Nat.add_comm 1] at hd
    exact obstruction (a := a) (by dsimp [a]; omega) hQ stripped hd
  by_cases eight : a%16 = 8
  · have hd := one_add_pow_dvd_of_odd_mul (z:=2) (e0:=8) eight
    norm_num [Nat.add_comm 1] at hd
    have h257 : 257 ∈ P := seed 257 (by norm_num) (by decide) (by decide) hd
    have h43 := advance 43 (by norm_num) (by decide) (by decide) 257 h257 (by decide)
    have h11 := advance 11 (by norm_num) (by decide) (by decide) 43 h43 (by decide)
    have dvdn : ∀ q ∈ P, q ∣ n := fun q h =>
      Nat.dvd_of_mem_primeFactors (mem_of_mem_erase (mem_filter.mp h).1)
    exact (hA n hperfect unique he old₁ old₂ old₃ hfive lower sieve eight
      (dvdn _ h257) (dvdn _ h43) (dvdn _ h11)).trans (le_max_left A B)
  · have d4 := old₂ 4 (by decide)
    have d16 := old₂ 16 (by decide)
    have d32 := old₁ 32 (by decide)
    have d64 := old₁ 64 (by decide)
    have divisible : 128 ∣ a := by
      change a%2=0 at even
      change a%8≠4 at d4
      change a%32≠16 at d16
      change a%64≠32 at d32
      change a%128≠64 at d64
      omega
    exact (hB n hperfect unique he old₁ old₂ old₃ hfive lower sieve divisible).trans (le_max_right A B)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R2_H2_R1
