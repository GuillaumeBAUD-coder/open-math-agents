import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1

/-!
# Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.H2.R1.H2.R2

Credit: @aroth01.

The step is: for unitary perfect numbers `n = 2 ^ a * z ^ e * (simple odd primes)` with `32 ∣ e`, `a = 2 mod 4`
and `z` one of the 16 primes 23, 37, 41, 53, 61, 71, 79, 83, 97, 137, 139, 157, 173, 199, 229, 331, `a` is bounded.

This is a second reduction of the step (R1, by another contributor, splits on the prime factors of `a`). It
separates the 13 primes for which an exact search closes from the three for which it does not:
* `H1`: `z = 37` or `z` one of the 12 primes of `[61, 823)` (stated as in the parent, by the list of the other
  primes); only `a = 2 mod 4` is kept of the conditions on `a`. A "frontier" search without a bound on the
  exponent of `z` (the leaves `2 ^ k * z ^ j - 1` are bounded fiber by fiber) closes each of these primes in at
  most 1400 steps; it is the proof of this hypothesis.
* `H2`: `z = 23`,  `H3`: `z = 41`,  `H4`: `z = 53`, with all the conditions of the step. For these three the same
  search does not close quickly.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H2_R2

-- H1: z = 37 or one of the 12 primes 61, 71, 79, 83, 97, 137, 139, 157, 173, 199, 229, 331.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (z = 37 ∨ (61 ≤ z ∧ z < 823 ∧
      z ∉ ({67, 73, 89, 101, 103, 107, 109, 113, 127, 131, 149, 151, 163, 167, 179, 181, 191, 193, 197, 211, 223,
      227, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 337, 347, 349,
      353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
      467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601,
      607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733,
      739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821} : Finset ℕ))) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H2: z = 23.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 23) →
    n.factorization 23 % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H3: z = 41.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 41) →
    n.factorization 41 % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H4: z = 53.
def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 53) →
    n.factorization 53 % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨max (max A1 A2) (max A3 A4), fun n h z hz hzmem hS he h20 h28 h4a => ?_⟩
  rcases hzmem with hl | hr
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact (h2 n h hS he h20 h28 h4a).trans (le_max_of_le_left (le_max_right _ _))
    · exact (h1 n h 37 hz (Or.inl rfl) hS he h4a).trans (le_max_of_le_left (le_max_left _ _))
    · exact (h3 n h hS he h20 h28 h4a).trans (le_max_of_le_right (le_max_left _ _))
    · exact (h4 n h hS he h20 h28 h4a).trans (le_max_of_le_right (le_max_right _ _))
  · exact (h1 n h z hz (Or.inr hr) hS he h4a).trans (le_max_of_le_left (le_max_left _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H2_R2
