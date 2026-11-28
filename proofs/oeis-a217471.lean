import OMAStatements.S_oeis_a217471
import Mathlib

/-
A217471: the sum of Fib(2k)^5 for k <= n equals (F - 1)^2 (4 F^3 + 8 F^2 - 3 F - 14) / 44 with
F = Fib(2n+1).

Write x = Fib(2n+1), y = Fib(2n+2) and P(t) = (t - 1)^2 (4 t^3 + 8 t^2 - 3 t - 14).
- cassini: y^2 - x y - x^2 = -1, by induction (the left side is invariant under
  (x, y) -> (x + y, x + 2y)).
- Then P(x + y) - P(x) - 44 y^5 = (-40 y^3 - 20 x y^2 - 20 x^2 y + 25 y) (y^2 - x y - x^2 + 1),
  so 44 a(n) = P(Fib(2n+1)) follows by induction with Fib(2n+3) = x + y.
-/

namespace OMA.P217471

lemma cassini (n : ℕ) :
    (Nat.fib (2 * n + 2) : ℤ) ^ 2 - (Nat.fib (2 * n + 2) : ℤ) * (Nat.fib (2 * n + 1) : ℤ) -
      (Nat.fib (2 * n + 1) : ℤ) ^ 2 = -1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h3 : Nat.fib (2 * (n + 1) + 1) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Nat.fib_add_two]
    have h4 : Nat.fib (2 * (n + 1) + 2) = Nat.fib (2 * n + 2) + Nat.fib (2 * (n + 1) + 1) := by
      rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by ring, Nat.fib_add_two,
        show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring]
    rw [h4, h3]
    push_cast
    linear_combination ih

lemma main' (a : ℕ → ℕ) (ha : ∀ n, a n = ∑ k ∈ Finset.range (n + 1), (Nat.fib (2 * k)) ^ 5) :
    ∀ n : ℕ, (a n : ℚ) =
      ((Nat.fib (2 * n + 1) : ℚ) - 1) ^ 2 *
        (4 * (Nat.fib (2 * n + 1) : ℚ) ^ 3 + 8 * (Nat.fib (2 * n + 1) : ℚ) ^ 2
          - 3 * (Nat.fib (2 * n + 1) : ℚ) - 14) / 44 := by
  have key : ∀ n : ℕ, 44 * (a n : ℤ) =
      ((Nat.fib (2 * n + 1) : ℤ) - 1) ^ 2 *
        (4 * (Nat.fib (2 * n + 1) : ℤ) ^ 3 + 8 * (Nat.fib (2 * n + 1) : ℤ) ^ 2
          - 3 * (Nat.fib (2 * n + 1) : ℤ) - 14) := by
    intro n
    induction n with
    | zero =>
      rw [ha]
      simp
    | succ n ih =>
      have e2 : Nat.fib (2 * (n + 1)) = Nat.fib (2 * n + 2) := by
        rw [show 2 * (n + 1) = 2 * n + 2 by ring]
      have hs : (a (n + 1) : ℤ) = a n + (Nat.fib (2 * n + 2) : ℤ) ^ 5 := by
        rw [ha (n + 1), Finset.sum_range_succ, ← ha n, e2]
        push_cast
        ring
      have h3 : (Nat.fib (2 * (n + 1) + 1) : ℤ) =
          (Nat.fib (2 * n + 1) : ℤ) + (Nat.fib (2 * n + 2) : ℤ) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Nat.fib_add_two]
        push_cast
        ring
      have hc := cassini n
      rw [hs, h3]
      linear_combination ih + (40 * (Nat.fib (2 * n + 2) : ℤ) ^ 3 +
        20 * (Nat.fib (2 * n + 1) : ℤ) * (Nat.fib (2 * n + 2) : ℤ) ^ 2 +
        20 * (Nat.fib (2 * n + 1) : ℤ) ^ 2 * (Nat.fib (2 * n + 2) : ℤ) -
        25 * (Nat.fib (2 * n + 2) : ℤ)) * hc
  intro n
  have h := key n
  have hq : (44 : ℚ) * (a n : ℚ) =
      ((Nat.fib (2 * n + 1) : ℚ) - 1) ^ 2 *
        (4 * (Nat.fib (2 * n + 1) : ℚ) ^ 3 + 8 * (Nat.fib (2 * n + 1) : ℚ) ^ 2
          - 3 * (Nat.fib (2 * n + 1) : ℚ) - 14) := by exact_mod_cast h
  rw [← hq]
  ring

end OMA.P217471

theorem OMA.solution : type_of% @OMA.S_oeis_a217471.main := OMA.P217471.main' OMA.S_oeis_a217471.a (fun _ => rfl)
