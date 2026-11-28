import FormalConjectures.OEIS.«63880»

-- Reduction OeisA63880.unique_primitive_108.R1 of problem OeisA63880.unique_primitive_108
-- Credit: @Ciphore
-- The primitive term is forced to be a multiple of `108`: since `108` is itself in the
-- sequence, primitivity then collapses to equality. The divisibility separates into
-- independent 2-adic and 3-adic cores.

/-!
## Reduction of `OeisA63880.unique_primitive_108`

If every term of the sequence is divisible by `4` and by `27`, then every term is a
multiple of `108`. A primitive multiple of `108` cannot be larger than `108`, because
`108` itself is in the sequence, so the primitive term is unique.
-/

namespace OMA.R_OeisA63880_unique_primitive_108_R1

open OeisA63880
open scoped ArithmeticFunction.sigma

/-- The 2-adic component of the congruence: every term of the sequence is divisible by `4`. -/
def H1 : Prop := ∀ n : ℕ, A n → 4 ∣ n

/-- The 3-adic component of the congruence: every term of the sequence is divisible by `27`. -/
def H2 : Prop := ∀ n : ℕ, A n → 27 ∣ n

theorem main : H1 → H2 → type_of% @OeisA63880.unique_primitive_108 := by
  intro h4 h27 n hn
  rw [IsPrimitiveTerm, Set.isPrimitive_iff] at hn
  obtain ⟨hnA, hnmin⟩ := hn
  have h4dvd : 4 ∣ n := h4 n hnA
  have h27dvd : 27 ∣ n := h27 n hnA
  have h108dvd : 108 ∣ n := by
    obtain ⟨b, hb⟩ := h27dvd
    have h4div : 4 ∣ 27 * b := hb ▸ h4dvd
    have hcop : Nat.Coprime 4 27 := by decide
    have h4b : 4 ∣ b := (Nat.Coprime.dvd_of_dvd_mul_left hcop h4div)
    obtain ⟨c, hc⟩ := h4b
    exact ⟨c, by rw [hb, hc]; ring⟩
  by_cases heq : n = 108
  · exact heq
  · exfalso
    have hnpos : 0 < n := hnA.1
    have hlt : 108 < n := by
      obtain ⟨c, hc⟩ := h108dvd
      have hc0 : 0 < c := by
        by_contra hz
        push Not at hz
        have : c = 0 := by omega
        subst this
        rw [mul_zero] at hc
        omega
      have hc1 : c ≠ 1 := by
        intro h1
        subst h1
        rw [mul_one] at hc
        exact heq hc
      have hc2 : 2 ≤ c := by omega
      calc 108 < 108 * 2 := by norm_num
        _ ≤ 108 * c := by exact Nat.mul_le_mul_left 108 hc2
        _ = n := hc.symm
    have hproper : 108 ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨h108dvd, hlt⟩
    exact hnmin 108 hproper a_108

end OMA.R_OeisA63880_unique_primitive_108_R1
