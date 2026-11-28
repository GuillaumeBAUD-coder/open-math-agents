import OMAStatements.S_oeis_a368634
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.ZMod.Basic

/-! OEIS A368634: `a(n)` is odd iff `n = 2 ^ k - 1`.

Write `c n` for the coefficient of `x ^ n` in `A ^ 2`. Since `A(-x) ^ 2` is `A ^ 2` rescaled by
`-1`, comparing coefficients gives `a 0 = 1` and `2 a (n + 1) = 3 c n - (-1) ^ n c n`, so
`a (n + 1) = c n` for even `n` and `a (n + 1) = 2 c n` for odd `n`. Modulo `2`, the symmetric sum
`c n = ∑_{i ≤ n} a i a (n - i)` keeps only the middle term, so `c n ≡ a (n / 2)` for even `n`
and `c n ≡ 0` otherwise. Hence `a (n + 1) ≡ a (n / 2)` or `0`, and strong induction gives the
claim, since `n + 1 = 2 ^ (k + 1) - 1` iff `n / 2 = 2 ^ k - 1` for even `n`. -/

namespace OpenMath.A368634

open Finset OMA.S_oeis_a368634

private theorem hx : ∀ x : ZMod 2, x + x = 0 := by decide

private theorem hsq : ∀ x : ZMod 2, x * x = x := by decide

/-- A sum over `0, …, n` that is symmetric under `i ↦ n - i` keeps only its middle term mod 2. -/
private theorem sym_sum : ∀ (n : ℕ) (g : ℕ → ZMod 2), (∀ i ≤ n, g i = g (n - i)) →
    ∑ i ∈ range (n + 1), g i = if n % 2 = 0 then g (n / 2) else 0
  | 0, g, _ => by simp
  | 1, g, hg => by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hg 1 le_rfl, Nat.sub_self, hx,
      if_neg (by norm_num)]
  | n + 2, g, hg => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ', hg (n + 2) le_rfl, Nat.sub_self]
    have ih := sym_sum n (fun i => g (i + 1)) (fun i hi => by
      show g (i + 1) = g (n - i + 1)
      rw [hg (i + 1) (by omega)]
      congr 1
      omega)
    rw [ih, show (n + 2) % 2 = n % 2 by omega, show (n + 2) / 2 = n / 2 + 1 by omega, add_assoc,
      hx, add_zero]

theorem main :
    ∀ A : PowerSeries ℤ, IsA368634 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  intro A hA
  have h' : PowerSeries.C (2 : ℤ) * A =
      PowerSeries.C 2 + PowerSeries.X * (PowerSeries.C 3 * A ^ 2 - negArg A ^ 2) := by
    rw [map_ofNat, map_ofNat]
    exact hA
  have hr : negArg A = PowerSeries.rescale (-1) A := by
    ext m
    simp [negArg, PowerSeries.coeff_rescale]
  have h0 : PowerSeries.coeff 0 A = 1 := by
    have h1 := congrArg (PowerSeries.coeff 0) h'
    rw [PowerSeries.coeff_C_mul, map_add, PowerSeries.coeff_C, if_pos rfl,
      PowerSeries.coeff_zero_X_mul, add_zero] at h1
    omega
  have hs : ∀ n, 2 * PowerSeries.coeff (n + 1) A =
      3 * PowerSeries.coeff n (A ^ 2) - (-1) ^ n * PowerSeries.coeff n (A ^ 2) := by
    intro n
    have h1 := congrArg (PowerSeries.coeff (n + 1)) h'
    rw [PowerSeries.coeff_C_mul, map_add, PowerSeries.coeff_C, if_neg (by omega), zero_add,
      PowerSeries.coeff_succ_X_mul, map_sub, PowerSeries.coeff_C_mul, hr, ← map_pow,
      PowerSeries.coeff_rescale] at h1
    exact h1
  have hc : ∀ n, ((PowerSeries.coeff n (A ^ 2) : ℤ) : ZMod 2) =
      if n % 2 = 0 then ((PowerSeries.coeff (n / 2) A : ℤ) : ZMod 2) else 0 := by
    intro n
    have hsym := sym_sum n (fun i => ((PowerSeries.coeff i A : ℤ) : ZMod 2) *
        ((PowerSeries.coeff (n - i) A : ℤ) : ZMod 2)) (fun i hi => by
      show _ * _ = _ * _
      rw [Nat.sub_sub_self hi, mul_comm])
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i A * PowerSeries.coeff j A) n, Int.cast_sum]
    simp only [Int.cast_mul]
    refine hsym.trans ?_
    split_ifs with h
    · show _ * _ = _
      rw [show n - n / 2 = n / 2 by omega]
      exact hsq _
    · rfl
  have hbs : ∀ n, ((PowerSeries.coeff (n + 1) A : ℤ) : ZMod 2) =
      if n % 2 = 0 then ((PowerSeries.coeff (n / 2) A : ℤ) : ZMod 2) else 0 := by
    intro n
    have h1 := hs n
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow, one_mul] at h1
      have h2 : PowerSeries.coeff (n + 1) A = PowerSeries.coeff n (A ^ 2) := by omega
      rw [h2, hc n]
    · rw [ho.neg_one_pow] at h1
      have h2 : PowerSeries.coeff (n + 1) A = 2 * PowerSeries.coeff n (A ^ 2) := by omega
      obtain ⟨r, hr'⟩ := ho
      rw [h2, if_neg (by omega)]
      push_cast
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  have key : ∀ m, (((PowerSeries.coeff m A : ℤ) : ZMod 2) = 1 ↔ ∃ k : ℕ, m = 2 ^ k - 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases m with _ | n
      · rw [h0]
        exact ⟨fun _ => ⟨0, rfl⟩, fun _ => by simp⟩
      · rw [hbs n]
        rcases Nat.even_or_odd n with ⟨r, hr'⟩ | ⟨r, hr'⟩
        · rw [if_pos (by omega), ih (n / 2) (by omega)]
          constructor
          · rintro ⟨k, hk⟩
            refine ⟨k + 1, ?_⟩
            have := Nat.one_le_two_pow (n := k)
            rw [pow_succ]
            omega
          · rintro ⟨k, hk⟩
            rcases k with _ | k
            · simp at hk
            · refine ⟨k, ?_⟩
              rw [pow_succ] at hk
              omega
        · rw [if_neg (by omega)]
          constructor
          · intro h
            exact absurd h (by decide)
          · rintro ⟨k, hk⟩
            rcases k with _ | k
            · simp at hk
            · rw [pow_succ] at hk
              omega
  intro n
  rw [← key n]
  have e : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = 1 ↔
      ((PowerSeries.coeff n A : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) := by
    rw [Int.cast_one]
  rw [e, ZMod.intCast_eq_intCast_iff']
  norm_num

end OpenMath.A368634

theorem OMA.solution : type_of% @OMA.S_oeis_a368634.main := OpenMath.A368634.main
