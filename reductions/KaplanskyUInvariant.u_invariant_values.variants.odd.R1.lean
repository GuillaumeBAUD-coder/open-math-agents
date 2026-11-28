import FormalConjectures.Paper.KaplanskyUInvariant

/-!
Reduction of Kaplansky's odd `u`-invariant expectation: every odd `n ≥ 9` is a `u`-invariant.

`H1` is Karpenko's theorem (2026 preprint): every `n` with `n + 1` and `n + 3` not powers of two
is a `u`-invariant. `H2` is the statement for the two exceptional families `2 ^ r - 1` and
`2 ^ r - 3`, `r ≥ 4`, which is exactly the part left open by Karpenko's theorem (the smallest
cases are `13` and `15`). `main` is the elementary number theory that combines the two.
-/

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_odd_R1

open KaplanskyUInvariant

/-- Karpenko's theorem: if neither `n + 1` nor `n + 3` is a power of two, then `n` is the
`u`-invariant of some field. -/
def H1 : Prop :=
  ∀ n : ℕ, (∀ r, 2 ^ r ≠ n + 1) → (∀ r, 2 ^ r ≠ n + 3) → IsUInvariant n

/-- The two exceptional families of Karpenko's theorem are `u`-invariants: `2 ^ r - 1` and
`2 ^ r - 3` for every `r ≥ 4`. -/
def H2 : Prop :=
  ∀ r : ℕ, 4 ≤ r → IsUInvariant (2 ^ r - 1) ∧ IsUInvariant (2 ^ r - 3)

/-- Every odd `n ≥ 9` is either covered by Karpenko's theorem, or of the form `2 ^ r - 1` or
`2 ^ r - 3` with `r ≥ 4`. -/
theorem main : H1 → H2 →
    type_of% @KaplanskyUInvariant.u_invariant_values.variants.odd := by
  intro h1 h2 n _hn hn9
  by_cases hp1 : ∃ r, 2 ^ r = n + 1
  · obtain ⟨r, hr⟩ := hp1
    have hr4 : 4 ≤ r := by
      rcases Nat.lt_or_ge r 4 with h | h
      · exfalso
        have hle : 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
        omega
      · exact h
    have hn : n = 2 ^ r - 1 := by omega
    rw [hn]
    exact (h2 r hr4).1
  · push Not at hp1
    by_cases hp3 : ∃ r, 2 ^ r = n + 3
    · obtain ⟨r, hr⟩ := hp3
      have hr4 : 4 ≤ r := by
        rcases Nat.lt_or_ge r 4 with h | h
        · exfalso
          have hle : 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
          omega
        · exact h
      have hn : n = 2 ^ r - 3 := by omega
      rw [hn]
      exact (h2 r hr4).2
    · push Not at hp3
      exact h1 n hp1 hp3

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_odd_R1
