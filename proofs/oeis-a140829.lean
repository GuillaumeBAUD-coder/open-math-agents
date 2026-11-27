import OMAStatements.S_oeis_a140829
import Mathlib

/-!
Write F = Fibonacci. For every i: a(2i+8) = F(i+2) + F(i+4) + 1 and a(2i+9) = F(i+6) - 1.
Induction on i: with A = F(i+2), B = F(i+3) and the Cassini value e = B^2 - AB - A^2 = +-1,
F(2i+10) = 3A^2 + 10AB + 8B^2 and (A+3B+1)(2A+3B-1) - F(2i+10) = e + A - 1 lies in
[0, 2A+3B-1), so the ceiling gives a(2i+10) = A + 3B + 1; similarly
(3A+5B-1)(A+3B+1) - F(2i+11) = 2e + 2A + 2B - 1 lies in [0, A+3B+1), so a(2i+11) = 3A + 5B - 1.
The first terms a(0..9) are computed directly. The recurrence then follows from the Fibonacci
recurrence on each parity class.
-/

namespace R140829
open OMA.S_oeis_a140829

theorem ceil_step (N D Q : ℕ) (hD : 0 < D) (hQ : 0 < Q) (h1 : N ≤ Q * D) (h2 : Q * D < N + D) :
    ⌈(N : ℚ) / (D : ℚ)⌉₊ = Q := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  rw [Nat.ceil_eq_iff (by omega)]
  constructor
  · rw [lt_div_iff₀ hDq, Nat.cast_pred hQ]
    have h2' : ((Q * D : ℕ) : ℚ) < ((N + D : ℕ) : ℚ) := by exact_mod_cast h2
    push_cast at h2'
    linarith
  · rw [div_le_iff₀ hDq]
    exact_mod_cast h1

theorem a_succ (n D Q : ℕ) (hn : a n = D) (hD : 0 < D) (hQ : 0 < Q)
    (h1 : Nat.fib (n + 1) ≤ Q * D) (h2 : Q * D < Nat.fib (n + 1) + D) : a (n + 1) = Q := by
  show ⌈(Nat.fib (n + 1) : ℚ) / (a n : ℚ)⌉₊ = Q
  rw [hn]
  exact ceil_step _ _ _ hD hQ h1 h2

theorem cas (j : ℕ) :
    (Nat.fib (j + 1) : ℤ) ^ 2 - Nat.fib j * Nat.fib (j + 1) - Nat.fib j ^ 2 = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show j + 1 + 1 = j + 2 by ring, Nat.fib_add_two]
    push_cast
    linear_combination (-1 : ℤ) * ih

theorem arith1 (A B D N Q : ℕ) (hA : 1 ≤ A)
    (hN : N = (A + B) * (A + 2 * B) + (A + 2 * B) * (2 * A + 3 * B))
    (hQ : Q = A + 3 * B + 1) (hD : D + 1 = 2 * A + 3 * B)
    (hc : (B : ℤ) ^ 2 - A * B - A ^ 2 = 1 ∨ ((B : ℤ) ^ 2 - A * B - A ^ 2 = -1 ∧ 2 ≤ A)) :
    N ≤ Q * D ∧ Q * D < N + D := by
  subst hN hQ
  have hDz : (D : ℤ) = 2 * (A : ℤ) + 3 * B - 1 := by omega
  have hAz : (1 : ℤ) ≤ A := by exact_mod_cast hA
  constructor
  · zify
    rw [hDz]
    rcases hc with h | ⟨h, h2⟩
    · nlinarith [h]
    · have h2z : (2 : ℤ) ≤ A := by exact_mod_cast h2
      nlinarith [h]
  · zify
    rw [hDz]
    rcases hc with h | ⟨h, h2⟩
    · nlinarith [h]
    · nlinarith [h]

theorem arith2 (A B N Q : ℕ) (hA : 1 ≤ A) (hAB : A < B)
    (hN : N = (A + 2 * B) * (A + 2 * B) + (2 * A + 3 * B) * (2 * A + 3 * B))
    (hQ : Q + 1 = 3 * A + 5 * B)
    (hc : (B : ℤ) ^ 2 - A * B - A ^ 2 = 1 ∨ (B : ℤ) ^ 2 - A * B - A ^ 2 = -1) :
    N ≤ Q * (A + 3 * B + 1) ∧ Q * (A + 3 * B + 1) < N + (A + 3 * B + 1) := by
  subst hN
  have hQz : (Q : ℤ) = 3 * (A : ℤ) + 5 * B - 1 := by omega
  have hAz : (1 : ℤ) ≤ A := by exact_mod_cast hA
  have hABz : (A : ℤ) + 1 ≤ B := by exact_mod_cast hAB
  constructor
  · zify
    rw [hQz]
    rcases hc with h | h
    · nlinarith [h]
    · nlinarith [h]
  · zify
    rw [hQz]
    rcases hc with h | h
    · nlinarith [h]
    · nlinarith [h]

theorem key (i : ℕ) :
    a (2 * i + 8) = Nat.fib (i + 2) + Nat.fib (i + 4) + 1 ∧ a (2 * i + 9) + 1 = Nat.fib (i + 6) := by
  induction i with
  | zero =>
    have h0 : a 0 = 1 := rfl
    have h1 : a 1 = 1 := a_succ 0 1 1 h0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h2 : a 2 = 1 := a_succ 1 1 1 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h3 : a 3 = 2 := a_succ 2 1 2 h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h4 : a 4 = 2 := a_succ 3 2 2 h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h5 : a 5 = 3 := a_succ 4 2 3 h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h6 : a 6 = 3 := a_succ 5 3 3 h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h7 : a 7 = 5 := a_succ 6 3 5 h6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h8 : a 8 = 5 := a_succ 7 5 5 h7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h9 : a 9 = 7 := a_succ 8 5 7 h8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_⟩
    · show a 8 = Nat.fib 2 + Nat.fib 4 + 1
      rw [h8]
      norm_num
    · show a 9 + 1 = Nat.fib 6
      rw [h9]
      norm_num
  | succ i ih =>
    obtain ⟨_, hO⟩ := ih
    have f4 : Nat.fib (i + 4) = Nat.fib (i + 2) + Nat.fib (i + 3) := Nat.fib_add_two
    have f5 : Nat.fib (i + 5) = Nat.fib (i + 3) + Nat.fib (i + 4) := Nat.fib_add_two
    have f6 : Nat.fib (i + 6) = Nat.fib (i + 4) + Nat.fib (i + 5) := Nat.fib_add_two
    have f7 : Nat.fib (i + 7) = Nat.fib (i + 5) + Nat.fib (i + 6) := Nat.fib_add_two
    have g5 : Nat.fib (i + 5) = Nat.fib (i + 2) + 2 * Nat.fib (i + 3) := by omega
    have g6 : Nat.fib (i + 6) = 2 * Nat.fib (i + 2) + 3 * Nat.fib (i + 3) := by omega
    have fN : Nat.fib (2 * i + 9 + 1) =
        Nat.fib (i + 4) * Nat.fib (i + 5) + Nat.fib (i + 5) * Nat.fib (i + 6) := by
      have := Nat.fib_add (i + 4) (i + 5)
      rw [show i + 4 + (i + 5) + 1 = 2 * i + 9 + 1 by ring] at this
      exact this
    have fN' : Nat.fib (2 * i + 10 + 1) =
        Nat.fib (i + 5) * Nat.fib (i + 5) + Nat.fib (i + 6) * Nat.fib (i + 6) := by
      have := Nat.fib_add (i + 5) (i + 5)
      rw [show i + 5 + (i + 5) + 1 = 2 * i + 10 + 1 by ring] at this
      exact this
    rw [f4, g5, g6] at fN
    rw [g5, g6] at fN'
    have hA1 : 1 ≤ Nat.fib (i + 2) := Nat.fib_pos.mpr (by omega)
    have hAB : Nat.fib (i + 2) < Nat.fib (i + 3) := Nat.fib_lt_fib_succ (by omega)
    have hc : (Nat.fib (i + 3) : ℤ) ^ 2 - Nat.fib (i + 2) * Nat.fib (i + 3) -
        Nat.fib (i + 2) ^ 2 = (-1) ^ (i + 2) := cas (i + 2)
    have hsgn : 2 ≤ Nat.fib (i + 2) ∨ ((-1 : ℤ) ^ (i + 2) = 1) := by
      rcases Nat.eq_zero_or_pos i with h | h
      · right
        subst h
        norm_num
      · left
        have h3 : Nat.fib 3 ≤ Nat.fib (i + 2) := Nat.fib_mono (by omega)
        have h3' : Nat.fib 3 = 2 := by norm_num
        omega
    have hc1 : ((Nat.fib (i + 3) : ℤ) ^ 2 - Nat.fib (i + 2) * Nat.fib (i + 3) -
        Nat.fib (i + 2) ^ 2 = 1) ∨ (((Nat.fib (i + 3) : ℤ) ^ 2 - Nat.fib (i + 2) * Nat.fib (i + 3) -
        Nat.fib (i + 2) ^ 2 = -1) ∧ 2 ≤ Nat.fib (i + 2)) := by
      rcases neg_one_pow_eq_or ℤ (i + 2) with h | h
      · left
        rw [hc, h]
      · right
        refine ⟨by rw [hc, h], ?_⟩
        rcases hsgn with h' | h'
        · exact h'
        · rw [h] at h'
          norm_num at h'
    have hc2 : ((Nat.fib (i + 3) : ℤ) ^ 2 - Nat.fib (i + 2) * Nat.fib (i + 3) -
        Nat.fib (i + 2) ^ 2 = 1) ∨ ((Nat.fib (i + 3) : ℤ) ^ 2 - Nat.fib (i + 2) * Nat.fib (i + 3) -
        Nat.fib (i + 2) ^ 2 = -1) := by
      rcases hc1 with h | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    have hD : a (2 * i + 9) + 1 = 2 * Nat.fib (i + 2) + 3 * Nat.fib (i + 3) := by omega
    obtain ⟨k1, k2⟩ := arith1 (Nat.fib (i + 2)) (Nat.fib (i + 3)) (a (2 * i + 9))
      (Nat.fib (2 * i + 9 + 1)) (Nat.fib (i + 2) + 3 * Nat.fib (i + 3) + 1) hA1 fN rfl hD hc1
    have e1 : a (2 * i + 10) = Nat.fib (i + 2) + 3 * Nat.fib (i + 3) + 1 :=
      a_succ (2 * i + 9) (a (2 * i + 9)) _ rfl (by omega) (by omega) k1 k2
    obtain ⟨k3, k4⟩ := arith2 (Nat.fib (i + 2)) (Nat.fib (i + 3)) (Nat.fib (2 * i + 10 + 1))
      (3 * Nat.fib (i + 2) + 5 * Nat.fib (i + 3) - 1) hA1 hAB fN' (by omega) hc2
    have e2 : a (2 * i + 11) = 3 * Nat.fib (i + 2) + 5 * Nat.fib (i + 3) - 1 :=
      a_succ (2 * i + 10) _ _ e1 (by omega) (by omega) k3 k4
    refine ⟨?_, ?_⟩
    · rw [show 2 * (i + 1) + 8 = 2 * i + 10 by ring, show i + 1 + 2 = i + 3 by ring,
        show i + 1 + 4 = i + 5 by ring, e1]
      omega
    · rw [show 2 * (i + 1) + 9 = 2 * i + 11 by ring, show i + 1 + 6 = i + 7 by ring, e2]
      omega

theorem solve : ∀ n : ℕ, 13 ≤ n →
    (a n : ℤ) = -a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨i, rfl | rfl⟩ : ∃ i, n = 2 * i + 13 ∨ n = 2 * i + 14 := ⟨(n - 13) / 2, by omega⟩
  · have e0 := (key (i + 2)).2
    have e1 := (key (i + 2)).1
    have e2 := (key (i + 1)).2
    have e3 := (key (i + 1)).1
    have e4 := (key i).2
    have e5 := (key i).1
    rw [show 2 * (i + 2) + 9 = 2 * i + 13 by ring, show i + 2 + 6 = i + 8 by ring] at e0
    rw [show 2 * (i + 2) + 8 = 2 * i + 12 by ring, show i + 2 + 2 = i + 4 by ring,
      show i + 2 + 4 = i + 6 by ring] at e1
    rw [show 2 * (i + 1) + 9 = 2 * i + 11 by ring, show i + 1 + 6 = i + 7 by ring] at e2
    rw [show 2 * (i + 1) + 8 = 2 * i + 10 by ring, show i + 1 + 2 = i + 3 by ring,
      show i + 1 + 4 = i + 5 by ring] at e3
    have f4 : Nat.fib (i + 4) = Nat.fib (i + 2) + Nat.fib (i + 3) := Nat.fib_add_two
    have f5 : Nat.fib (i + 5) = Nat.fib (i + 3) + Nat.fib (i + 4) := Nat.fib_add_two
    have f6 : Nat.fib (i + 6) = Nat.fib (i + 4) + Nat.fib (i + 5) := Nat.fib_add_two
    have f7 : Nat.fib (i + 7) = Nat.fib (i + 5) + Nat.fib (i + 6) := Nat.fib_add_two
    have f8 : Nat.fib (i + 8) = Nat.fib (i + 6) + Nat.fib (i + 7) := Nat.fib_add_two
    rw [show 2 * i + 13 - 1 = 2 * i + 12 by omega, show 2 * i + 13 - 2 = 2 * i + 11 by omega,
      show 2 * i + 13 - 3 = 2 * i + 10 by omega, show 2 * i + 13 - 4 = 2 * i + 9 by omega,
      show 2 * i + 13 - 5 = 2 * i + 8 by omega]
    omega
  · have e0 := (key (i + 3)).1
    have e1 := (key (i + 2)).2
    have e2 := (key (i + 2)).1
    have e3 := (key (i + 1)).2
    have e4 := (key (i + 1)).1
    have e5 := (key i).2
    rw [show 2 * (i + 3) + 8 = 2 * i + 14 by ring, show i + 3 + 2 = i + 5 by ring,
      show i + 3 + 4 = i + 7 by ring] at e0
    rw [show 2 * (i + 2) + 9 = 2 * i + 13 by ring, show i + 2 + 6 = i + 8 by ring] at e1
    rw [show 2 * (i + 2) + 8 = 2 * i + 12 by ring, show i + 2 + 2 = i + 4 by ring,
      show i + 2 + 4 = i + 6 by ring] at e2
    rw [show 2 * (i + 1) + 9 = 2 * i + 11 by ring, show i + 1 + 6 = i + 7 by ring] at e3
    rw [show 2 * (i + 1) + 8 = 2 * i + 10 by ring, show i + 1 + 2 = i + 3 by ring,
      show i + 1 + 4 = i + 5 by ring] at e4
    have f4 : Nat.fib (i + 4) = Nat.fib (i + 2) + Nat.fib (i + 3) := Nat.fib_add_two
    have f5 : Nat.fib (i + 5) = Nat.fib (i + 3) + Nat.fib (i + 4) := Nat.fib_add_two
    have f6 : Nat.fib (i + 6) = Nat.fib (i + 4) + Nat.fib (i + 5) := Nat.fib_add_two
    have f7 : Nat.fib (i + 7) = Nat.fib (i + 5) + Nat.fib (i + 6) := Nat.fib_add_two
    have f8 : Nat.fib (i + 8) = Nat.fib (i + 6) + Nat.fib (i + 7) := Nat.fib_add_two
    rw [show 2 * i + 14 - 1 = 2 * i + 13 by omega, show 2 * i + 14 - 2 = 2 * i + 12 by omega,
      show 2 * i + 14 - 3 = 2 * i + 11 by omega, show 2 * i + 14 - 4 = 2 * i + 10 by omega,
      show 2 * i + 14 - 5 = 2 * i + 9 by omega]
    omega

end R140829

theorem OMA.solution : type_of% @OMA.S_oeis_a140829.main := R140829.solve
