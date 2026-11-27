import OMAStatements.S_oeis_a090079
import Mathlib

/-!
For n >= 2 the binary digits of n are n % 2 followed by those of n / 2, so the reduced list of n
is the reduced list of n / 2 when n % 2 = (n / 2) % 2, and n % 2 prepended to it otherwise.
By strong induction this gives 3 * a(n) + 2 = 2^(runs n + 1) + n % 2 (in the second case the two
last bits sum to 1), and (1 - (-1)^n) / 2 = n % 2, so the division by 3 is exact.
-/

namespace R090079
open OMA.S_oeis_a090079

theorem reduced_rec (n : ℕ) (hn : 2 ≤ n) :
    reduced n = if n % 2 = n / 2 % 2 then reduced (n / 2) else n % 2 :: reduced (n / 2) := by
  have h1 : Nat.digits 2 n = n % 2 :: Nat.digits 2 (n / 2) :=
    Nat.digits_def' (by norm_num) (by omega)
  have h2 : Nat.digits 2 (n / 2) = n / 2 % 2 :: Nat.digits 2 (n / 2 / 2) :=
    Nat.digits_def' (by norm_num) (by omega)
  unfold reduced
  rw [h1, h2, List.destutter_cons_cons, List.destutter_cons']
  by_cases h : n % 2 = n / 2 % 2 <;> simp [h]

theorem key (n : ℕ) : 3 * a n + 2 = 2 ^ (runs n + 1) + n % 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp [a, runs, reduced]
      · simp [a, runs, reduced, Nat.ofDigits_cons]
    · have ih' := ih (n / 2) (by omega)
      have hr := reduced_rec n h
      by_cases hc : n % 2 = n / 2 % 2
      · have ha : a n = a (n / 2) := by simp only [a, hr, if_pos hc]
        have hl : runs n = runs (n / 2) := by simp only [runs, hr, if_pos hc]
        rw [ha, hl]
        omega
      · have ha : a n = n % 2 + 2 * a (n / 2) := by
          simp only [a, hr, if_neg hc, Nat.ofDigits_cons, Nat.cast_id]
        have hl : runs n = runs (n / 2) + 1 := by
          simp only [runs, hr, if_neg hc, List.length_cons]
        rw [ha, hl, pow_succ]
        have h2 : n % 2 + n / 2 % 2 = 1 := by omega
        omega

end R090079

theorem OMA.solution : type_of% @OMA.S_oeis_a090079.main := by
  intro n
  have hk := R090079.key n
  have hpar : ((1 : ℤ) - (-1) ^ n) / 2 = ((n % 2 : ℕ) : ℤ) := by
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow, Nat.even_iff.mp he]
      norm_num
    · rw [ho.neg_one_pow, Nat.odd_iff.mp ho]
      norm_num
  rw [hpar]
  have hk' : (3 : ℤ) * (OMA.S_oeis_a090079.a n : ℤ) + 2 =
      2 ^ (OMA.S_oeis_a090079.runs n + 1) + ((n % 2 : ℕ) : ℤ) := by
    exact_mod_cast hk
  omega
