import OMAStatements.S_oeis_a214555
import Mathlib

/-
A214555: the numbers 5..5 4 9..9 4..4 5 (n fives, n+1 nines, n fours) satisfy the linear
recurrence with characteristic polynomial (x - 1)(x - 10)(x - 100)(x - 1000).

rep: 9 times the number with n digits d is d (10^n - 1).
key: 9 a(n) = 5000 * 1000^n - 500 * 100^n - 50 * 10^n + 5, by splitting the digit list.
The recurrence then holds for each of the four geometric sequences.
-/

namespace OMA.P214555

lemma rep (d n : ℕ) : 9 * ((Nat.ofDigits 10 (List.replicate n d) : ℕ) : ℤ) = d * (10 ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons]
    push_cast at ih ⊢
    linear_combination 10 * ih

lemma key (n : ℕ) :
    9 * ((Nat.ofDigits 10 (List.replicate n 5 ++ [4] ++ List.replicate (n + 1) 9 ++
      List.replicate n 4 ++ [5]).reverse : ℕ) : ℤ) =
      5000 * 1000 ^ n - 500 * 100 ^ n - 50 * 10 ^ n + 5 := by
  have e : (List.replicate n 5 ++ [4] ++ List.replicate (n + 1) 9 ++
      List.replicate n 4 ++ [5]).reverse =
      5 :: (List.replicate n 4 ++ (List.replicate (n + 1) 9 ++ 4 :: List.replicate n 5)) := by
    simp [List.reverse_append]
  rw [e, Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_cons]
  have h4 := rep 4 n
  have h9 := rep 9 (n + 1)
  have h5 := rep 5 n
  simp only [List.length_replicate]
  push_cast at h4 h9 h5 ⊢
  have e1 : (1000 : ℤ) ^ n = (10 ^ n) ^ 3 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e2 : (100 : ℤ) ^ n = (10 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e1, e2]
  linear_combination (10 : ℤ) * h4 + 10 * 10 ^ n * h9 + 100 * 10 ^ n * 10 ^ (n + 1) * h5

lemma main' (a : ℕ → ℕ) (ha : ∀ n, a n = Nat.ofDigits 10 (List.replicate n 5 ++ [4] ++
    List.replicate (n + 1) 9 ++ List.replicate n 4 ++ [5]).reverse) : ∀ n : ℕ,
    (a (n + 4) : ℤ) = 1111 * a (n + 3) - 112110 * a (n + 2) + 1111000 * a (n + 1)
      - 1000000 * a n := by
  intro n
  have h0 := key n
  have h1 := key (n + 1)
  have h2 := key (n + 2)
  have h3 := key (n + 3)
  have h4 := key (n + 4)
  rw [← ha] at h0 h1 h2 h3 h4
  have : 9 * (a (n + 4) : ℤ) = 9 * (1111 * a (n + 3) - 112110 * a (n + 2) + 1111000 * a (n + 1)
      - 1000000 * a n) := by
    linear_combination h4 - 1111 * h3 + 112110 * h2 - 1111000 * h1 + 1000000 * h0
  linarith

end OMA.P214555

theorem OMA.solution : type_of% @OMA.S_oeis_a214555.main := OMA.P214555.main' OMA.S_oeis_a214555.a (fun _ => rfl)
