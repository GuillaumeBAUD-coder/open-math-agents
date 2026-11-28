import OMAStatements.S_oeis_a065105
import Mathlib

/-!
# A065105 (numbers that are not products of Fibonacci numbers): the gap bound `≤ 3` is false

`62` and `66` are consecutive terms: `63 = 21 · 3`, `64 = 8 · 8`, `65 = 13 · 5` are products of
Fibonacci numbers, while `62 = 2 · 31` and `66 = 2 · 3 · 11` are not (`31` and `11` are not
Fibonacci numbers and cannot be split off).  The gap `4` occurs at an index `n ≥ 8`, because
at least the seven non-Fibonacci primes `7, 11, 17, 19, 23, 29, 31` come before `62`.
-/

namespace OMA.S_oeis_a065105

/-- Membership predicate of the sequence. -/
def P (m : ℕ) : Prop := 0 < m ∧ ¬ IsFibProd m

noncomputable instance : DecidablePred P := Classical.decPred _

lemma a_eq (n : ℕ) : a n = Nat.nth P (n - 1) := rfl

/-- A number below `89` that is none of `F(0), …, F(10)` is not a Fibonacci number. -/
lemma fib_ne {m : ℕ} (hm : m < 89) (h : ∀ k < 11, Nat.fib k ≠ m) (k : ℕ) : Nat.fib k ≠ m := by
  rcases lt_or_ge k 11 with hk | hk
  · exact h k hk
  · have h1 : Nat.fib 11 ≤ Nat.fib k := Nat.fib_mono hk
    have h2 : Nat.fib 11 = 89 := by decide
    omega

/-- A prime product of Fibonacci numbers is itself a Fibonacci number. -/
lemma prime_fib {m : ℕ} (h : IsFibProd m) (hp : m.Prime) : ∃ k, Nat.fib k = m := by
  induction h with
  | one => exact absurd hp Nat.not_prime_one
  | @mul a k _ ih =>
    rcases Nat.prime_mul_iff.mp hp with ⟨hpa, hk⟩ | ⟨-, ha1⟩
    · obtain ⟨j, hj⟩ := ih hpa
      exact ⟨j, by rw [hj, hk, mul_one]⟩
    · exact ⟨k, by rw [ha1, one_mul]⟩

/-- Non-Fibonacci primes below `89` belong to the sequence. -/
lemma P_prime {p : ℕ} (hp : p.Prime) (hp89 : p < 89) (h : ∀ k < 11, Nat.fib k ≠ p) : P p :=
  ⟨hp.pos, fun hf => by
    obtain ⟨k, hk⟩ := prime_fib hf hp
    exact fib_ne hp89 h k hk⟩

/-- `31` and `62` are not products of Fibonacci numbers. -/
lemma not_31_62 {m : ℕ} (h : IsFibProd m) : m ≠ 31 ∧ m ≠ 62 := by
  induction h with
  | one => exact ⟨by norm_num, by norm_num⟩
  | @mul a k _ ih =>
    obtain ⟨h1, h2⟩ := ih
    have f31 := fib_ne (m := 31) (by norm_num) (by decide) k
    have f62 := fib_ne (m := 62) (by norm_num) (by decide) k
    generalize Nat.fib k = F at *
    constructor
    · intro he
      have hle : F ≤ 31 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left a he)
      interval_cases F <;> omega
    · intro he
      have hle : F ≤ 62 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left a he)
      interval_cases F <;> omega

/-- `11`, `22`, `33` and `66` are not products of Fibonacci numbers. -/
lemma not_11_66 {m : ℕ} (h : IsFibProd m) : m ≠ 11 ∧ m ≠ 22 ∧ m ≠ 33 ∧ m ≠ 66 := by
  induction h with
  | one => exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  | @mul a k _ ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have f6 := fib_ne (m := 6) (by norm_num) (by decide) k
    have f11 := fib_ne (m := 11) (by norm_num) (by decide) k
    have f22 := fib_ne (m := 22) (by norm_num) (by decide) k
    have f33 := fib_ne (m := 33) (by norm_num) (by decide) k
    have f66 := fib_ne (m := 66) (by norm_num) (by decide) k
    generalize Nat.fib k = F at *
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro he
      have hle : F ≤ 11 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left a he)
      interval_cases F <;> omega
    · intro he
      have hle : F ≤ 22 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left a he)
      interval_cases F <;> omega
    · intro he
      have hle : F ≤ 33 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left a he)
      interval_cases F <;> omega
    · intro he
      have hle : F ≤ 66 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left a he)
      interval_cases F <;> omega

lemma P_62 : P 62 := ⟨by norm_num, fun h => (not_31_62 h).2 rfl⟩
lemma P_66 : P 66 := ⟨by norm_num, fun h => (not_11_66 h).2.2.2 rfl⟩

/-- `63 = 21 · 3`, `64 = 8 · 8`, `65 = 13 · 5` are products of Fibonacci numbers. -/
lemma not_P_63 : ¬ P 63 := fun h =>
  h.2 ((by decide : 1 * Nat.fib 8 * Nat.fib 4 = 63) ▸ (IsFibProd.one.mul (k := 8)).mul (k := 4))
lemma not_P_64 : ¬ P 64 := fun h =>
  h.2 ((by decide : 1 * Nat.fib 6 * Nat.fib 6 = 64) ▸ (IsFibProd.one.mul (k := 6)).mul (k := 6))
lemma not_P_65 : ¬ P 65 := fun h =>
  h.2 ((by decide : 1 * Nat.fib 7 * Nat.fib 5 = 65) ▸ (IsFibProd.one.mul (k := 7)).mul (k := 5))

/-- One more term below `n` once a term `m < n` is known. -/
lemma count_step {m n c : ℕ} (hc : c ≤ Nat.count P m) (hP : P m) (hmn : m < n) :
    c + 1 ≤ Nat.count P n := by
  have h := Nat.count_monotone P (Nat.succ_le_of_lt hmn)
  rw [Nat.count_succ, if_pos hP] at h
  omega

/-- At least seven terms precede `62`. -/
lemma seven_le : 7 ≤ Nat.count P 62 := by
  have h0 : 0 ≤ Nat.count P 7 := Nat.zero_le _
  have h1 := count_step h0 (P_prime (by norm_num) (by norm_num) (by decide)) (show 7 < 11 by norm_num)
  have h2 := count_step h1 (P_prime (by norm_num) (by norm_num) (by decide)) (show 11 < 17 by norm_num)
  have h3 := count_step h2 (P_prime (by norm_num) (by norm_num) (by decide)) (show 17 < 19 by norm_num)
  have h4 := count_step h3 (P_prime (by norm_num) (by norm_num) (by decide)) (show 19 < 23 by norm_num)
  have h5 := count_step h4 (P_prime (by norm_num) (by norm_num) (by decide)) (show 23 < 29 by norm_num)
  have h6 := count_step h5 (P_prime (by norm_num) (by norm_num) (by decide)) (show 29 < 31 by norm_num)
  exact count_step h6 (P_prime (by norm_num) (by norm_num) (by decide)) (show 31 < 62 by norm_num)

/-- Exactly one term (`62`) lies in `[62, 66)`. -/
lemma count_66 : Nat.count P 66 = Nat.count P 62 + 1 := by
  rw [Nat.count_succ, if_neg not_P_65, Nat.count_succ, if_neg not_P_64, Nat.count_succ,
    if_neg not_P_63, Nat.count_succ, if_pos P_62]

end OMA.S_oeis_a065105

open OMA.S_oeis_a065105 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a065105.main) := by
  rintro ⟨-, h⟩
  have hgap := h (Nat.count P 62 + 1) (by have := seven_le; omega)
  have e1 : a (Nat.count P 62 + 1) = 62 := by
    rw [a_eq, Nat.add_sub_cancel]
    exact Nat.nth_count P_62
  have e2 : a (Nat.count P 62 + 1 + 1) = 66 := by
    rw [a_eq, Nat.add_sub_cancel, ← count_66]
    exact Nat.nth_count P_66
  rw [e1, e2] at hgap
  omega
