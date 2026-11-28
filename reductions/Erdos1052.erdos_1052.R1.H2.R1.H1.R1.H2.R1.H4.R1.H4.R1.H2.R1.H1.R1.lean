import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1

/-!
# Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.H2.R1.H1.R1

Credit: @aroth01.

The step is: for unitary perfect numbers `n = 2 ^ a * z ^ e * (simple odd primes)` with `32 ∣ e` and `z` one of
`11, 13, 17, 19` (and conditions on `a`), `a` is bounded. This reduction splits on the class of `a`:
* `H1`: `a` odd (no other condition on `a`),
* `H2`: `z = 13` and `a = 2 mod 4` (no other condition on `a`),
* `H3`: `z` one of `11, 17, 19` and `a = 2 mod 4`, with the conditions of the step,
* `H4`: `4 ∣ a`, with the conditions of the step.

`H1` and `H2` are within reach of a "frontier" search that needs no bound on the exponent of `z` (the proof of
step `...H2.R1.H2.R2.H1`): for `a` odd, `3 ∣ 2 ^ a + 1` is a simple prime dividing no `p + 1`, and the search
closes in at most 150 steps for each of the four primes; for `z = 13` and `a = 2 mod 4` it closes in about 1100
steps. For `H3` and `H4` the same search does not close quickly.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H1_R1

-- H1: a is odd.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    z ∈ ({11, 13, 17, 19} : Finset ℕ) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 2 = 1 →
    padicValNat 2 n ≤ A

-- H2: z = 13 and a = 2 mod 4.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 13) →
    n.factorization 13 % 32 = 0 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H3: z is one of 11, 17, 19 and a = 2 mod 4; the conditions of the step are kept.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    z ∈ ({11, 17, 19} : Finset ℕ) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H4: 4 divides a; the conditions of the step are kept.
def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    z ∈ ({11, 13, 17, 19} : Finset ℕ) →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 0 →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n % 4 = 0 →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨max (max A1 A2) (max A3 A4), fun n h z hz hzmem hS he c6 c10 c14 c20 c28 c8 c16 c4096 codd cr => ?_⟩
  have hmod : padicValNat 2 n % 2 = 1 ∨ padicValNat 2 n % 4 = 2 ∨ padicValNat 2 n % 4 = 0 := by omega
  rcases hmod with ha | ha | ha
  · exact (h1 n h z hz hzmem hS he ha).trans (le_max_of_le_left (le_max_left _ _))
  · have hz' := hzmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
    rcases hz' with rfl | rfl | rfl | rfl
    · exact (h3 n h 11 hz (by decide) hS he c6 c10 c14 c20 c28 c8 c16 c4096 codd cr ha).trans
        (le_max_of_le_right (le_max_left _ _))
    · exact (h2 n h hS he ha).trans (le_max_of_le_left (le_max_right _ _))
    · exact (h3 n h 17 hz (by decide) hS he c6 c10 c14 c20 c28 c8 c16 c4096 codd cr ha).trans
        (le_max_of_le_right (le_max_left _ _))
    · exact (h3 n h 19 hz (by decide) hS he c6 c10 c14 c20 c28 c8 c16 c4096 codd cr ha).trans
        (le_max_of_le_right (le_max_left _ _))
  · exact (h4 n h z hz hzmem hS he c6 c10 c14 c20 c28 c8 c16 c4096 codd cr ha).trans
      (le_max_of_le_right (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H1_R1
