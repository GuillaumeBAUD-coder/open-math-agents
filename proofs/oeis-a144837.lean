import OMAStatements.S_oeis_a144837
import Mathlib

/-!
# Proof of the conjecture of OEIS A144837 (Peter Bala, Nov 14 2022)

`a(n) = L(5^n)`, `L` the Lucas numbers. Claim: `a(n+1) == a(n) (mod 5^(n+r+1))` for `r <= n`.
The strongest case is `r = n`: `5^(2n+1)` divides `a(n+1) - a(n)`.

1. Binet: `L(n) = phi^n + psi^n` in the reals, by induction from `phi^2 = phi + 1`, `psi^2 = psi + 1`.
2. For odd `m`, with `u = phi^m`, `v = psi^m`, `u v = (-1)^m = -1`:
   `L(5m) = u^5 + v^5 = (u+v)^5 + 5 (u+v)^3 + 5 (u+v) = L(m)^5 + 5 L(m)^3 + 5 L(m)`.
   Since `5^n` is odd, `a(n+1) = a(n)^5 + 5 a(n)^3 + 5 a(n)` for all `n >= 0`.
3. Put `d(n) = a(n)^2 + 4`. Then `d(n+1) = d(n) (d(n)^2 - 5 d(n) + 5)^2` (a polynomial identity) and
   `d(0) = 5`, so `5^(2n+1)` divides `d(n)` by induction: `5 | d(n)` gives `5 | d(n)^2 - 5 d(n) + 5`.
4. `a(n+1) - a(n) = a(n) (a(n)^2 + 1) (a(n)^2 + 4)`, hence `5^(2n+1)` divides `a(n+1) - a(n)`,
   and `5^(n+r+1)` divides `5^(2n+1)` when `r <= n`.
-/

namespace A144837Proof

open OMA.S_oeis_a144837

/-- A root of `x^2 = x + 1` has powers obeying the Fibonacci recurrence. -/
private lemma pow_step (x : ℝ) (n : ℕ) (hx : x ^ 2 = x + 1) :
    x ^ (n + 2) = x ^ (n + 1) + x ^ n := by
  linear_combination x ^ n * hx

/-- Binet's formula for the Lucas numbers. -/
private lemma lucas_binet : ∀ n : ℕ,
    (lucas n : ℝ) = Real.goldenRatio ^ n + Real.goldenConj ^ n
  | 0 => by
    have h : lucas 0 = 2 := rfl
    rw [h]
    norm_num
  | 1 => by
    have h : lucas 1 = 1 := rfl
    rw [h, pow_one, pow_one, Real.goldenRatio_add_goldenConj]
    norm_num
  | n + 2 => by
    have h : lucas (n + 2) = lucas (n + 1) + lucas n := rfl
    have h1 := lucas_binet (n + 1)
    have h0 := lucas_binet n
    have hφ : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
    have hψ : Real.goldenConj ^ 2 = Real.goldenConj + 1 := Real.goldenConj_sq
    rw [h, Int.cast_add, h1, h0, pow_step _ n hφ, pow_step _ n hψ]
    exact add_add_add_comm _ _ _ _

/-- `L(5m) = L(m)^5 + 5 L(m)^3 + 5 L(m)` for odd `m`. -/
private lemma lucas_five_mul (m : ℕ) (hm : Odd m) :
    (lucas (5 * m) : ℤ) = (lucas m : ℤ) ^ 5 + 5 * (lucas m : ℤ) ^ 3 + 5 * (lucas m : ℤ) := by
  have key : ∀ u v : ℝ, u * v = -1 →
      u ^ 5 + v ^ 5 = (u + v) ^ 5 + 5 * (u + v) ^ 3 + 5 * (u + v) := by
    intro u v huv
    linear_combination (5 * (u * v - 1) * (u + v) - 5 * (u + v) ^ 3) * huv
  have huv : Real.goldenRatio ^ m * Real.goldenConj ^ m = -1 := by
    rw [← mul_pow, Real.goldenRatio_mul_goldenConj, hm.neg_one_pow]
  have h : ((lucas (5 * m) : ℤ) : ℝ) =
      (((lucas m : ℤ) ^ 5 + 5 * (lucas m : ℤ) ^ 3 + 5 * (lucas m : ℤ) : ℤ) : ℝ) := by
    push_cast
    rw [lucas_binet (5 * m), lucas_binet m, mul_comm 5 m, pow_mul, pow_mul]
    exact key _ _ huv
  exact Int.cast_injective h

/-- The recurrence of the entry, valid from `n = 0`. -/
private lemma a_succ (n : ℕ) : a (n + 1) = a n ^ 5 + 5 * a n ^ 3 + 5 * a n := by
  have hodd : Odd (5 ^ n) := (by decide : Odd 5).pow
  have h5 : 5 ^ (n + 1) = 5 * 5 ^ n := pow_succ' 5 n
  have h := lucas_five_mul (5 ^ n) hodd
  unfold a
  rw [h5]
  exact h

/-- `5^(2n+1)` divides `a(n)^2 + 4`. -/
private lemma five_pow_dvd (n : ℕ) : (5 : ℤ) ^ (2 * n + 1) ∣ a n ^ 2 + 4 := by
  induction n with
  | zero =>
    have h : a 0 = 1 := rfl
    rw [h]
    norm_num
  | succ n ih =>
    have hid : a (n + 1) ^ 2 + 4 =
        (a n ^ 2 + 4) * ((a n ^ 2 + 4) ^ 2 - 5 * (a n ^ 2 + 4) + 5) ^ 2 := by
      rw [a_succ]
      ring
    have h5 : (5 : ℤ) ∣ a n ^ 2 + 4 := dvd_trans (dvd_pow_self 5 (by omega)) ih
    have h5' : (5 : ℤ) ∣ (a n ^ 2 + 4) ^ 2 - 5 * (a n ^ 2 + 4) + 5 := by
      obtain ⟨c, hc⟩ := h5
      exact ⟨5 * c ^ 2 - 5 * c + 1, by rw [hc]; ring⟩
    have h25 : (5 : ℤ) ^ 2 ∣ ((a n ^ 2 + 4) ^ 2 - 5 * (a n ^ 2 + 4) + 5) ^ 2 :=
      pow_dvd_pow_of_dvd h5' 2
    have hpow : (5 : ℤ) ^ (2 * (n + 1) + 1) = 5 ^ (2 * n + 1) * 5 ^ 2 := by ring
    rw [hid, hpow]
    exact mul_dvd_mul ih h25

/-- `5^(2n+1)` divides `a(n+1) - a(n)`. -/
private lemma diff_dvd (n : ℕ) : (5 : ℤ) ^ (2 * n + 1) ∣ a (n + 1) - a n := by
  have hid : a (n + 1) - a n = (a n ^ 2 + 4) * (a n * (a n ^ 2 + 1)) := by
    rw [a_succ]
    ring
  rw [hid]
  exact Dvd.dvd.mul_right (five_pow_dvd n) _

/-- The conjecture: `a(n+1) == a(n) (mod 5^(n+r+1))` whenever `r <= n`. -/
private lemma conjecture (n r : ℕ) (hr : r ≤ n) :
    a (n + 1) ≡ a n [ZMOD (5 : ℤ) ^ (n + r + 1)] := by
  have h1 : (5 : ℤ) ^ (n + r + 1) ∣ (5 : ℤ) ^ (2 * n + 1) := pow_dvd_pow 5 (by omega)
  have h2 : (5 : ℤ) ^ (n + r + 1) ∣ a (n + 1) - a n := dvd_trans h1 (diff_dvd n)
  exact (Int.modEq_iff_dvd.mpr h2).symm

end A144837Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a144837.main := by
  intro n r _ hr
  exact A144837Proof.conjecture n r hr
