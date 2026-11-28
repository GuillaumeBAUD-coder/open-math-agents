import OMAStatements.S_oeis_a067016
import Mathlib

/-!
# A067016: Barker's closed form and generating function

With c(0..3) = 1, 4, 3, 2 and c(m) = 2m − 1 − (m mod 2) for m ≥ 4, every pair i + j = N (N ≥ 3)
satisfies c(i) + c(j) ≤ c(N+1): if i, j ≥ 2 the sum is at most 2N − 2, and the pairs using c(0) = 1 or
c(1) = 4 give at most c(N+1), with equality at i = 0 (N even) or i = 1 (N odd). By strong induction
a = c, which gives 2a(n) = −3 + (−1)^n + 4n for n ≥ 4. Multiplying the series by
(1 − x)²(1 + x) = 1 − x − x² + x³ kills every coefficient from x⁷ on; the first seven come from
a(0..6) = 1, 4, 3, 2, 7, 8, 11.
-/

namespace PA067016
open OMA.S_oeis_a067016

/-- The closed form. -/
def c (n : ℕ) : ℕ :=
  if n = 0 then 1 else if n = 1 then 4 else if n = 2 then 3 else if n = 3 then 2
  else 2 * n - 1 - n % 2

theorem c_fact (m : ℕ) :
    (m = 0 ∧ c m = 1) ∨ (m = 1 ∧ c m = 4) ∨ (2 ≤ m ∧ c m ≤ 2 * m - 1 - m % 2) := by
  unfold c
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m) with h | h | h | h | h
  · subst h; simp
  · subst h; simp
  · subst h; simp
  · subst h; simp
  · right; right
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    omega

theorem c_big (m : ℕ) (hm : 4 ≤ m) : c m = 2 * m - 1 - m % 2 := by
  unfold c
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem bound (N i : ℕ) (hN : 3 ≤ N) (hi : i ≤ N) : c i + c (N - i) ≤ c (N + 1) := by
  have h1 := c_fact i
  have h2 := c_fact (N - i)
  have h3 := c_big (N + 1) (by omega)
  omega

theorem attained (N : ℕ) (hN : 3 ≤ N) :
    c (if N % 2 = 1 then 1 else 0) + c (N - (if N % 2 = 1 then 1 else 0)) = c (N + 1) := by
  have h3 := c_big (N + 1) (by omega)
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · rw [if_neg (by omega), Nat.sub_zero, c_big N (by omega), h3]
    simp [c]
    omega
  · rw [if_pos h, h3]
    have hc1 : c 1 = 4 := by simp [c]
    rw [hc1]
    rcases (by omega : N - 1 = 2 ∨ 4 ≤ N - 1) with h' | h'
    · rw [h']; simp [c]; omega
    · rw [c_big (N - 1) h']; omega

theorem a_eq_c : ∀ n, a n = c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [a, c]
    | 1, _ => simp [a, c]
    | 2, _ => simp [a, c]
    | 3, _ => simp [a, c]
    | k + 4, ih =>
      rw [a]
      apply le_antisymm
      · apply Finset.sup_le
        intro i _
        rw [ih i (by omega), ih (k + 3 - i) (by omega)]
        exact bound (k + 3) i (by omega) (by omega)
      · have hi0lt : (if (k + 3) % 2 = 1 then 1 else 0) < k + 4 := by split_ifs <;> omega
        have hmem := Finset.le_sup (f := fun i : Fin (k + 4) => a i + a (k + 3 - i))
          (Finset.mem_univ (⟨_, hi0lt⟩ : Fin (k + 4)))
        simp only at hmem
        rw [ih _ (by omega), ih (k + 3 - _) (by omega), attained (k + 3) (by omega)] at hmem
        exact hmem

end PA067016

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a067016.main := by
  have hc : ∀ n, 4 ≤ n → (OMA.S_oeis_a067016.a n : ℤ) =
      if n % 2 = 0 then 2 * (n : ℤ) - 1 else 2 * (n : ℤ) - 2 := by
    intro n hn
    rw [PA067016.a_eq_c, PA067016.c_big n hn]
    split_ifs <;> omega
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [hc n hn]
    rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [if_pos (by omega), show (-1 : ℤ) ^ (t + t) = 1 by rw [← two_mul, pow_mul]; norm_num]
      push_cast; ring
    · rw [if_neg (by omega), show (-1 : ℤ) ^ (2 * t + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
      push_cast; ring
  · have hexp : ((1 - X) ^ 2 * (1 + X) : ℤ⟦X⟧) * PowerSeries.mk (fun n => (OMA.S_oeis_a067016.a n : ℤ)) =
        PowerSeries.mk (fun n => (OMA.S_oeis_a067016.a n : ℤ)) -
          X ^ 1 * PowerSeries.mk (fun n => (OMA.S_oeis_a067016.a n : ℤ)) -
          X ^ 2 * PowerSeries.mk (fun n => (OMA.S_oeis_a067016.a n : ℤ)) +
          X ^ 3 * PowerSeries.mk (fun n => (OMA.S_oeis_a067016.a n : ℤ)) := by ring
    have hR : (1 + 3 * X - 2 * X ^ 2 - 4 * X ^ 3 + 6 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6 : ℤ⟦X⟧) =
        C 1 * X ^ 0 + C 3 * X ^ 1 - C 2 * X ^ 2 - C 4 * X ^ 3 + C 6 * X ^ 4 + C 2 * X ^ 5 -
          C 2 * X ^ 6 := by
      rw [show (C 3 : ℤ⟦X⟧) = 3 from map_ofNat C 3, show (C 2 : ℤ⟦X⟧) = 2 from map_ofNat C 2,
        show (C 4 : ℤ⟦X⟧) = 4 from map_ofNat C 4, show (C 6 : ℤ⟦X⟧) = 6 from map_ofNat C 6, map_one]
      ring
    rw [hexp, hR]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · have v : ∀ m, (OMA.S_oeis_a067016.a m : ℤ) = (PA067016.c m : ℤ) := by
        intro m; rw [PA067016.a_eq_c]
      interval_cases n <;> simp [v, PA067016.c]
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
        hc n (by omega), hc (n - 1) (by omega), hc (n - 2) (by omega), hc (n - 3) (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
        show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, if_false]
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [if_pos h, if_neg (by omega), if_pos (by omega), if_neg (by omega)]
        push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
          Nat.cast_sub (show 3 ≤ n by omega)]
        ring
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
          Nat.cast_sub (show 3 ≤ n by omega)]
        ring
