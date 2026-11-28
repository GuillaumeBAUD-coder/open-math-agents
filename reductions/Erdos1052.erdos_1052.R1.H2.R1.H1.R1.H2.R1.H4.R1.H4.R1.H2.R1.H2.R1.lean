import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1
import Mathlib

/-! For a = v₂(n) in this branch of Erdős 1052, the odd part a/2 is
not divisible by 9 or by any prime from 5 to 127. Hence if a > 6,
removing its possible factor 3 leaves an integer with least prime ≥ 131.
We separate boundedness of that least prime (H1) from control of the
exponents containing each individual large prime (H2). -/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts kernel_balance_one)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1 (setup5)

/-- Bounded least prime factor after removing the at-most-single factor of 3.
This is a question about roughness of exponents, not their size. -/
def H1 : Prop := ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (z ∈ ({23, 37, 41, 53} : Finset ℕ) ∨ (61 ≤ z ∧ z < 823 ∧
      z ∉ ({67, 73, 89, 101, 103, 107, 109, 113, 127, 131, 149, 151, 163, 167, 179, 181, 191, 193, 197,
      211, 223, 227, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
      317, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
      439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
      563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
      661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
      797, 809, 811, 821} : Finset ℕ))) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 →
    (if 3 ∣ padicValNat 2 n / 2 then padicValNat 2 n / 2 / 3 else padicValNat 2 n / 2).minFac ≤ B

/-- For each fixed large prime index, bound the exponents whose odd halves
are multiples of that index. No uniformity in p is assumed. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 127 < p → ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (z ∈ ({23, 37, 41, 53} : Finset ℕ) ∨ (61 ≤ z ∧ z < 823 ∧
      z ∉ ({67, 73, 89, 101, 103, 107, 109, 113, 127, 131, 149, 151, 163, 167, 179, 181, 191, 193, 197,
      211, 223, 227, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
      317, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
      439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
      563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
      661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
      797, 809, 811, 821} : Finset ℕ))) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 →
    p ∣ padicValNat 2 n / 2 → padicValNat 2 n ≤ A

theorem odd_half_divisor {m d : ℕ} (hm : m % 4 = 2) (hd : d ∣ m / 2) :
    4 ^ d + 1 ∣ 2 ^ m + 1 := by
  obtain ⟨k, hk⟩ := hd
  have ho : Odd (d * k) := Nat.odd_iff.mpr (by omega)
  have h := Odd.nat_add_dvd_pow_add_pow (4 ^ d) 1 (Nat.Odd.of_mul_right ho)
  rw [one_pow] at h
  have hmk : m = 2 * (d * k) := by omega
  rw [hmk, pow_mul, pow_mul]
  exact h

/- A prime q dividing 4^d+1 must be the exceptional base or occur simply.
Every odd nonexceptional prime divisor of q+1 in turn occurs simply. The
chains below terminate at a second supplier of 3, or a supplier of 5. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem odd_index_sieve {m e z : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hl : (z ∈ ({23, 37, 41, 53} : Finset ℕ) ∨ (61 ≤ z ∧ z < 823 ∧
      z ∉ ({67, 73, 89, 101, 103, 107, 109, 113, 127, 131, 149, 151, 163, 167, 179, 181, 191, 193, 197,
      211, 223, 227, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
      317, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
      439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
      563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
      661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
      797, 809, 811, 821} : Finset ℕ))))
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) (hm : m % 4 = 2)
    {d : ℕ} (hd : d ∈ ({9, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127} : Finset ℕ)) : ¬ d ∣ m / 2 := by
  intro hdm
  have hz7 : 7 ≤ z := by
    rcases hl with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      omega
    · omega
  have hz823 : z < 823 := by
    rcases hl with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      omega
    · exact h.2.1
  obtain ⟨_, _, h5, h3⟩ := setup5 hP hz hz7 E hm
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) :=
    fun c hc h => Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  obtain ⟨hnxt, hroot, _⟩ := facts hP hK E
  have hroot' (q : ℕ) (hp : q.Prime) (h2 : q ≠ 2) (hne : q ≠ z) (h : q ∣ 4 ^ d + 1) : q ∈ P :=
    hroot q hp h2 (by simpa using hne) (h.trans (odd_half_divisor hm hdm))
  have hnxt' (q p : ℕ) (hp : q.Prime) (h2 : q ≠ 2) (hne : q ≠ z) (h : q ∣ p + 1) (hmem : p ∈ P) : q ∈ P :=
    hnxt q hp h2 (by simpa using hne) p hmem h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h109 := hroot' 109 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide)
    exact h5 109 h109 (by decide)
  · by_cases h : z = 199
    · have h2113 := hroot' 2113 (by norm_num) (by decide) (by omega) (by decide)
      have h151 := hnxt' 151 2113 (by norm_num) (by decide) (by omega) (by decide) h2113
      have h19 := hnxt' 19 151 (by norm_num) (by decide) (by omega) (by decide) h151
      exact h5 19 h19 (by decide)
    · have h397 := hroot' 397 (by norm_num) (by decide) (by first | omega | (intro heq; subst z; norm_num at hl)) (by decide)
      have h199 := hnxt' 199 397 (by norm_num) (by decide) (by first | omega | (intro heq; subst z; norm_num at hl)) (by decide) h397
      exact h5 199 h199 (by decide)
  · by_cases h : z = 53
    · have h1613 := hroot' 1613 (by norm_num) (by decide) (by omega) (by decide)
      have := h3 1613 h1613 (by decide)
      omega
    · have h53 := hroot' 53 (by norm_num) (by decide) (by first | omega | (intro heq; subst z; norm_num at hl)) (by decide)
      have := h3 53 h53 (by decide)
      omega
  · by_cases h : z = 137
    · have h953 := hroot' 953 (by norm_num) (by decide) (by omega) (by decide)
      have := h3 953 h953 (by decide)
      omega
    · have h137 := hroot' 137 (by norm_num) (by decide) (by first | omega | (intro heq; subst z; norm_num at hl)) (by decide)
      have := h3 137 h137 (by decide)
      omega
  · by_cases h : z = 229
    · have h525313 := hroot' 525313 (by norm_num) (by decide) (by omega) (by decide)
      have h262657 := hnxt' 262657 525313 (by norm_num) (by decide) (by omega) (by decide) h525313
      have h11 := hnxt' 11 262657 (by norm_num) (by decide) (by omega) (by decide) h262657
      have := h3 11 h11 (by decide)
      omega
    · have h229 := hroot' 229 (by norm_num) (by decide) (by first | omega | (intro heq; subst z; norm_num at hl)) (by decide)
      exact h5 229 h229 (by decide)
  · have h1013 := hroot' 1013 (by norm_num) (by decide) (by omega) (by decide)
    have := h3 1013 h1013 (by decide)
    omega
  · have h107367629 := hroot' 107367629 (by norm_num) (by decide) (by omega) (by decide)
    exact h5 107367629 h107367629 (by decide)
  · have h8681 := hroot' 8681 (by norm_num) (by decide) (by omega) (by decide)
    have := h3 8681 h8681 (by decide)
    omega
  · have h149 := hroot' 149 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide)
    exact h5 149 h149 (by decide)
  · have h10169 := hroot' 10169 (by norm_num) (by decide) (by omega) (by decide)
    exact h5 10169 h10169 (by decide)
  · by_cases h : z = 173
    · have h500177 := hroot' 500177 (by norm_num) (by decide) (by omega) (by decide)
      have := h3 500177 h500177 (by decide)
      omega
    · have h173 := hroot' 173 (by norm_num) (by decide) (by first | omega | (intro heq; subst z; norm_num at hl)) (by decide)
      have := h3 173 h173 (by decide)
      omega
  · have h3761 := hroot' 3761 (by norm_num) (by decide) (by omega) (by decide)
    have := h3 3761 h3761 (by decide)
    omega
  · have h15358129 := hroot' 15358129 (by norm_num) (by decide) (by omega) (by decide)
    exact h5 15358129 h15358129 (by decide)
  · have h1181 := hroot' 1181 (by norm_num) (by decide) (by omega) (by decide)
    have := h3 1181 h1181 (by decide)
    omega
  · have h1709 := hroot' 1709 (by norm_num) (by decide) (by omega) (by decide)
    exact h5 1709 h1709 (by decide)
  · have h269 := hroot' 269 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide)
    exact h5 269 h269 (by decide)
  · have h569 := hroot' 569 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide)
    exact h5 569 h569 (by decide)
  · have h293 := hroot' 293 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide)
    have := h3 293 h293 (by decide)
    omega
  · have h317 := hroot' 317 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide)
    have := h3 317 h317 (by decide)
    omega
  · have h997 := hroot' 997 (by norm_num) (by decide) (by omega) (by decide)
    have h499 := hnxt' 499 997 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide) h997
    exact h5 499 h499 (by decide)
  · have h1069 := hroot' 1069 (by norm_num) (by decide) (by omega) (by decide)
    exact h5 1069 h1069 (by decide)
  · have h389 := hroot' 389 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide)
    exact h5 389 h389 (by decide)
  · have h809 := hroot' 809 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide)
    exact h5 809 h809 (by decide)
  · have h41201 := hroot' 41201 (by norm_num) (by decide) (by omega) (by decide)
    have := h3 41201 h41201 (by decide)
    omega
  · have h857 := hroot' 857 (by norm_num) (by decide) (by omega) (by decide)
    have := h3 857 h857 (by decide)
    omega
  · have h5669 := hroot' 5669 (by norm_num) (by decide) (by omega) (by decide)
    exact h5 5669 h5669 (by decide)
  · have h58309 := hroot' 58309 (by norm_num) (by decide) (by omega) (by decide)
    exact h5 58309 h58309 (by decide)
  · have h509 := hroot' 509 (by norm_num) (by decide) (by intro h; subst z; norm_num at hl) (by decide)
    exact h5 509 h509 (by decide)

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1.H2 := by
  classical
  rintro ⟨B, hB⟩ hlocal
  let bound (p : ℕ) := if hp : p.Prime ∧ 127 < p then Classical.choose (hlocal p hp.1 hp.2) else 0
  refine ⟨max 6 ((Finset.range (B + 1)).sup bound), ?_⟩
  intro n h z hz hl hS he h20 h28 hm
  by_cases hsmall : padicValNat 2 n ≤ 6
  · exact hsmall.trans (le_max_left _ _)
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  obtain ⟨hP, E⟩ := kernel_balance_one h
    (Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩) ((hS z).mpr rfl).2.1 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have h9 := odd_index_sieve hP hz hl E hm (d := 9) (by decide)
  let t := padicValNat 2 n / 2
  let u := if 3 ∣ t then t / 3 else t
  have hut : u ∣ t := by
    dsimp [u]
    split
    · exact Nat.div_dvd_of_dvd ‹3 ∣ t›
    · exact dvd_refl _
  have hu : u ≠ 1 ∧ ¬ 2 ∣ u ∧ ¬ 3 ∣ u := by
    dsimp [u, t]
    split <;> omega
  let p := u.minFac
  have hp : p.Prime := Nat.minFac_prime hu.1
  have hpu : p ∣ u := Nat.minFac_dvd _
  have hpd : p ∣ padicValNat 2 n / 2 := hpu.trans hut
  have hpB : p ≤ B := hB n h z hz hl hS he h20 h28 hm
  have hp3 : 3 < p := by
    have := hp.two_le
    by_contra hn
    have : p = 2 ∨ p = 3 := by omega
    rcases this with h2 | h3
    · exact hu.2.1 (h2 ▸ hpu)
    · exact hu.2.2 (h3 ▸ hpu)
  have hp127 : 127 < p := by
    by_contra hn
    by_cases h5 : p = 5
    · rw [h5] at hpd
      omega
    by_cases h7 : p = 7
    · rw [h7] at hpd
      omega
    refine odd_index_sieve hP hz hl E hm ?_ hpd
    have hle : p ≤ 127 := by omega
    interval_cases p <;> first | decide | (norm_num at hp; done) | omega
  have hcase : p.Prime ∧ 127 < p := ⟨hp, hp127⟩
  have hbound : padicValNat 2 n ≤ bound p := by
    rw [show bound p = _ from dif_pos hcase]
    exact Classical.choose_spec (hlocal p hp hp127) n h z hz hl hS he h20 h28 hm hpd
  exact hbound.trans
    ((Finset.le_sup (f := bound) (Finset.mem_range.mpr (by omega : p < B + 1))).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H2_R1
