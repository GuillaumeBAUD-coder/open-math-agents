import OMAStatements.S_oeis_a174525
import Mathlib

/-!
# OEIS A174525: every odd square `N > 1` is a base in which `ab` and `ba` are different squares

Write `N = (2u + 1)²` with `u ≥ 1` and take the digits

  `a = u²`,   `b = 4u² + 2u + 1 = N - 2u`.

Then `a N + b = (u (2u + 1) + 1)²` and `b N + a = (N - u)² = (4u² + 3u + 1)²`, both digits lie in
`[1, N)`, and the two numbers differ because `a < b`.
-/

open OMA.S_oeis_a174525

theorem OMA.solution : type_of% @OMA.S_oeis_a174525.main := by
  rintro N ⟨r, rfl⟩ hodd hne
  -- `r` is odd and at least `3`
  have hr : r % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one r with h | h
    · exfalso
      obtain ⟨j, hj⟩ := hodd
      have : (r * r) % 2 = 0 := by rw [Nat.mul_mod, h]
      omega
    · exact h
  obtain ⟨u, rfl⟩ : ∃ u, r = 2 * u + 1 := ⟨r / 2, by omega⟩
  have hu : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with rfl | h
    · exact absurd rfl hne
    · exact h
  have huu : 1 ≤ u * u := Nat.mul_pos hu hu
  refine ⟨u * u, 4 * (u * u) + 2 * u + 1, huu, by nlinarith, by omega, by nlinarith,
    ⟨u * (2 * u + 1) + 1, by ring⟩, ⟨4 * (u * u) + 3 * u + 1, by ring⟩, ?_⟩
  -- the two numbers differ: `a < b` and `N > 1`
  have h1 : u * u < 4 * (u * u) + 2 * u + 1 := by omega
  have h2 : 1 < (2 * u + 1) * (2 * u + 1) := by nlinarith
  intro h
  nlinarith
