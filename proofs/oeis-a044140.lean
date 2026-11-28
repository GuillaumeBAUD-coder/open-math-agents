import OMAStatements.S_oeis_a044140
import Mathlib

/-!
# A044140: the conjectured recurrence a(n) = a(n-1) + a(n-8) - a(n-9) fails at n = 58

The statement is false, so this file proves its negation with an explicit counterexample.

The digits are computed by a function d7 with a fixed number of steps, which agrees with
Nat.digits 7 below 7^5. Through it, being a term becomes a computable test T below 7^5, and
the number of terms below x is a finite count checked by the kernel. Then Nat.nth_count
turns each count into a value of the enumeration.

The values found are a(49) = 2109, a(50) = 2158, a(57) = 2452 and a(58) = 2499.
The recurrence at n = 58 would give a(58) = 2452 + 2158 - 2109 = 2501, but 2501 is not a
term: in base 7, 2499 is 10200 while 2498 is 10166, so 2499 is the next term after 2452.
-/

namespace OMA.P044140

open OMA.S_oeis_a044140

def d7 : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else n % 7 :: d7 f (n / 7)

theorem d7_eq : ∀ f n, n < 7 ^ f → d7 f n = Nat.digits 7 n := by
  intro f
  induction f with
  | zero => intro n hn; simp at hn; subst hn; simp [d7]
  | succ f ih =>
    intro n hn
    by_cases h0 : n = 0
    · subst h0; simp [d7]
    · rw [d7, if_neg h0, Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero h0), ih]
      rw [pow_succ] at hn
      omega

def H (m : ℕ) : Bool := decide (([0, 2] : List ℕ).IsInfix (d7 5 m).reverse)

def T (k : ℕ) : Bool := H k && !H (k - 1)

theorem isTerm_iff (k : ℕ) (hk : k < 7 ^ 5) : IsTerm k ↔ T k = true := by
  have h1 : d7 5 k = Nat.digits 7 k := d7_eq 5 k hk
  have h2 : d7 5 (k - 1) = Nat.digits 7 (k - 1) := d7_eq 5 (k - 1) (by omega)
  simp [IsTerm, Has02, T, H, h1, h2]

open Classical in
theorem count_eq : ∀ n, n ≤ 7 ^ 5 →
    Nat.count IsTerm n = Nat.count (fun k => T k = true) n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Nat.count_succ, Nat.count_succ, ih (by omega)]
    have := isTerm_iff n (by omega)
    by_cases h : T n = true
    · simp [h, this]
    · simp [h, this]

open Classical in
theorem nth_of (x m : ℕ) (hx : x < 7 ^ 5) (hT : T x = true)
    (hc : Nat.count (fun k => T k = true) x = m) : Nat.nth IsTerm m = x := by
  have hp : IsTerm x := (isTerm_iff x hx).2 hT
  rw [← hc, ← count_eq x hx.le]
  exact Nat.nth_count hp

theorem v58 : a 58 = 2499 :=
  nth_of 2499 57 (by norm_num) (by decide +kernel) (by decide +kernel)

theorem v57 : a 57 = 2452 :=
  nth_of 2452 56 (by norm_num) (by decide +kernel) (by decide +kernel)

theorem v50 : a 50 = 2158 :=
  nth_of 2158 49 (by norm_num) (by decide +kernel) (by decide +kernel)

theorem v49 : a 49 = 2109 :=
  nth_of 2109 48 (by norm_num) (by decide +kernel) (by decide +kernel)

end OMA.P044140

/-- The recurrence fails at n = 58: a(58) = 2499, while a(57) + a(50) - a(49) = 2501. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a044140.main) := by
  intro h
  have h58 := h 58 (by norm_num)
  norm_num [OMA.P044140.v58, OMA.P044140.v57, OMA.P044140.v50, OMA.P044140.v49] at h58
