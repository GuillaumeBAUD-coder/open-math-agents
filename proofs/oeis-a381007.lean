import OMAStatements.S_oeis_a381007
import Mathlib

/-!
# A381007: the Pythagorean triangles are primitive

With `t = 2 ^ (2n - 1)` (so `x = 2t = 2 ^ (2n)` and `y = t + 1 = 2 ^ (2n-1) + 1` in Euclid's
formula, as noted on the OEIS page by Chai Wah Wu, Feb 13 2025) the leg is
`a = 4t(t+1)` and the hypotenuse is `c = 5t^2 + 2t + 1`. Since `t` is even, `c` is odd,
`c ≡ 1 (mod t)` and `c + 3(t+1) ≡ 4 (mod t+1)` with `t + 1` odd, so `a` and `c` are coprime,
and hence so are `gcd(a, b)` and `c`.
-/

namespace OMA.A381007Proof

theorem cop_aux (k : ℕ) :
    Nat.Coprime (4 * (2 * k) * (2 * k + 1)) (5 * (2 * k) ^ 2 + 2 * (2 * k) + 1) := by
  have hodd : Odd (5 * (2 * k) ^ 2 + 2 * (2 * k) + 1) := ⟨10 * k ^ 2 + 2 * k, by ring⟩
  apply Nat.Coprime.mul_left
  · apply Nat.Coprime.mul_left
    · have h2 : Nat.Coprime 2 (5 * (2 * k) ^ 2 + 2 * (2 * k) + 1) :=
        Nat.coprime_two_left.mpr hodd
      have := Nat.Coprime.pow_left 2 h2
      simpa using this
    · have e : 5 * (2 * k) ^ 2 + 2 * (2 * k) + 1 = 1 + (5 * (2 * k) + 2) * (2 * k) := by ring
      rw [e, Nat.coprime_add_mul_right_right]
      exact Nat.coprime_one_right _
  · have key : Nat.Coprime (2 * k + 1) 4 := by
      have h2 : Nat.Coprime (2 * k + 1) 2 := Nat.coprime_two_right.mpr ⟨k, rfl⟩
      have := Nat.Coprime.pow_right 2 h2
      simpa using this
    have e : 5 * (2 * k) ^ 2 + 2 * (2 * k) + 1 + 3 * (2 * k + 1) =
        4 + (5 * (2 * k)) * (2 * k + 1) := by ring
    have h1 : Nat.Coprime (2 * k + 1) (5 * (2 * k) ^ 2 + 2 * (2 * k) + 1 + 3 * (2 * k + 1)) := by
      rw [e, Nat.coprime_add_mul_right_right]; exact key
    rwa [Nat.coprime_add_mul_right_right] at h1

end OMA.A381007Proof

open OMA.S_oeis_a381007 in
theorem OMA.solution : type_of% @OMA.S_oeis_a381007.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ht : 2 ^ (2 * m + 1) = 2 * 2 ^ (2 * m) := by ring
  set k := 2 ^ (2 * m) with hk
  have hA : legA (m + 1) = 4 * (2 * k) * (2 * k + 1) := by
    unfold legA
    rw [show 4 * (m + 1) = 2 * (2 * m + 1) + 2 by ring,
      show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, pow_add, pow_add, pow_mul', ht]
    ring
  have hC : hyp (m + 1) = 5 * (2 * k) ^ 2 + 2 * (2 * k) + 1 := by
    unfold hyp
    rw [show 4 * (m + 1) - 2 = 2 * (2 * m + 1) by omega,
      show 4 * (m + 1) = 2 * (2 * m + 1) + 2 by ring, show 2 * (m + 1) = (2 * m + 1) + 1 by ring,
      pow_add, pow_add, pow_mul', ht]
    ring
  have hcop : Nat.Coprime (legA (m + 1)) (hyp (m + 1)) := by
    rw [hA, hC]; exact OMA.A381007Proof.cop_aux k
  exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop
