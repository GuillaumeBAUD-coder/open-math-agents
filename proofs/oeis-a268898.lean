import OMAStatements.S_oeis_a268898

/-!
# A268898: closed form, recurrence and generating function

`count k x j` counts the words of length `k` over three colours that start after the colour `x`
and have exactly `j` complementary transitions (a transition `x → y` with `x + y = 2`).
For every colour `x` exactly one of the three colours is complementary and the other two are not,
so the recursion is colour-blind: `count k x 0 = 2 ^ k` and `count k x 1 * 2 = k * 2 ^ k`.
Hence `a (n + 1) = 4 ^ n * (6 n + 3)`, and the recurrence and the generating function follow.
-/

open PowerSeries
open OMA.S_oeis_a268898

namespace OMA

@[simp] lemma cs_0_0 (k : ℕ) : count (k + 1) 0 0 = count k 0 0 + (count k 1 0 + 0) := by
  simp [count, colors]

@[simp] lemma cs_1_0 (k : ℕ) : count (k + 1) 1 0 = count k 0 0 + (0 + (count k 2 0 + 0)) := by
  simp [count, colors]

@[simp] lemma cs_2_0 (k : ℕ) : count (k + 1) 2 0 = 0 + (count k 1 0 + (count k 2 0 + 0)) := by
  simp [count, colors]

@[simp] lemma cs_0_1 (k : ℕ) : count (k + 1) 0 1 = count k 0 1 + (count k 1 1 + (count k 2 0 + 0)) := by
  simp [count, colors]

@[simp] lemma cs_1_1 (k : ℕ) : count (k + 1) 1 1 = count k 0 1 + (count k 1 0 + (count k 2 1 + 0)) := by
  simp [count, colors]

@[simp] lemma cs_2_1 (k : ℕ) : count (k + 1) 2 1 = count k 0 0 + (count k 1 1 + (count k 2 1 + 0)) := by
  simp [count, colors]

lemma two_distrib (p q r : ℕ) : (p + (q + (r + 0))) * 2 = p * 2 + (q * 2 + r * 2) := by ring

@[simp] lemma count_zero (k : ℕ) (x : Color) : count k x 0 = 2 ^ k := by
  induction k generalizing x with
  | zero => simp [count]
  | succ k ih =>
      obtain rfl | rfl | rfl : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> simp
      · simp [ih, pow_succ]; ring
      · simp [ih, pow_succ]; ring
      · simp [ih, pow_succ]; ring

lemma count_one (k : ℕ) (x : Color) : count k x 1 * 2 = k * 2 ^ k := by
  induction k generalizing x with
  | zero => simp [count]
  | succ k ih =>
      obtain rfl | rfl | rfl : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> simp
      · rw [cs_0_1, two_distrib]
        simp [ih, pow_succ]; ring
      · rw [cs_1_1, two_distrib]
        simp [ih, pow_succ]; ring
      · rw [cs_2_1, two_distrib]
        simp [ih, pow_succ]; ring

lemma a_closed (n : ℕ) : a (n + 1) = 4 ^ n * (6 * n + 3) := by
  have hstep : a (n + 1) = count (2 * n + 1) 0 1 +
      (count (2 * n + 1) 1 1 + (count (2 * n + 1) 2 1 + 0)) := by
    simp [a, colors]
  have hd : count (2 * n + 1) 0 1 + (count (2 * n + 1) 1 1 + (count (2 * n + 1) 2 1 + 0)) =
      count (2 * n + 1) 0 1 + (count (2 * n + 1) 1 1 + count (2 * n + 1) 2 1) := by ring
  rw [hstep, hd]
  have h2n : (2 : ℕ) ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]
    norm_num
  have hb : (2 : ℕ) ^ (2 * n + 1) = 2 * 4 ^ n := by
    rw [pow_succ, h2n]
    ring
  have key : ∀ x : Color, count (2 * n + 1) x 1 = (2 * n + 1) * 4 ^ n := by
    intro x
    have h := count_one (2 * n + 1) x
    rw [hb] at h
    have h2 : (2 * n + 1) * (2 * 4 ^ n) = ((2 * n + 1) * 4 ^ n) * 2 := by ring
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) h
  rw [key 0, key 1, key 2]
  ring

lemma recurrence (n : ℕ) : a (n + 3) + 16 * a (n + 1) = 8 * a (n + 2) := by
  have e0 : a (n + 1) = 4 ^ n * (6 * n + 3) := a_closed n
  have e1 : a (n + 2) = 4 ^ (n + 1) * (6 * (n + 1) + 3) := a_closed (n + 1)
  have e2 : a (n + 3) = 4 ^ (n + 2) * (6 * (n + 2) + 3) := a_closed (n + 2)
  have h1 : (4 : ℕ) ^ (n + 1) = 4 ^ n * 4 := by rw [pow_succ]
  have h2 : (4 : ℕ) ^ (n + 2) = 4 ^ n * 16 := by
    rw [show n + 2 = n + 1 + 1 from rfl, pow_succ, h1]
    ring
  rw [e0, e1, e2, h1, h2]
  ring

lemma coeff_eight_mul (φ : ℚ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (8 * φ) = 8 * PowerSeries.coeff n φ := by
  rw [show (8 : ℚ⟦X⟧) = PowerSeries.C 8 from rfl, PowerSeries.coeff_C_mul]

lemma coeff_sixteen_mul (φ : ℚ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (16 * φ) = 16 * PowerSeries.coeff n φ := by
  rw [show (16 : ℚ⟦X⟧) = PowerSeries.C 16 from rfl, PowerSeries.coeff_C_mul]

lemma coeff_zero_X_mul (φ : ℚ⟦X⟧) : PowerSeries.coeff 0 (PowerSeries.X * φ) = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_X, zero_mul]

lemma coeff_rhs_zero : PowerSeries.coeff 0 (3 + 12 * PowerSeries.X : ℚ⟦X⟧) = 3 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [map_add, map_mul, PowerSeries.constantCoeff_X, mul_zero, add_zero, map_ofNat]

lemma coeff_rhs_one : PowerSeries.coeff 1 (3 + 12 * PowerSeries.X : ℚ⟦X⟧) = 12 := by
  have h : (3 + 12 * PowerSeries.X : ℚ⟦X⟧) = 3 + PowerSeries.X * 12 := by ring
  rw [h, map_add, PowerSeries.coeff_succ_X_mul 0,
    show (12 : ℚ⟦X⟧) = PowerSeries.C 12 from rfl, PowerSeries.coeff_C,
    show (3 : ℚ⟦X⟧) = PowerSeries.C 3 from rfl, PowerSeries.coeff_C]
  norm_num

lemma coeff_rhs_succ (m : ℕ) :
    PowerSeries.coeff (m + 2) (3 + 12 * PowerSeries.X : ℚ⟦X⟧) = 0 := by
  have h : (3 + 12 * PowerSeries.X : ℚ⟦X⟧) = 3 + PowerSeries.X * 12 := by ring
  rw [h, map_add, PowerSeries.coeff_succ_X_mul (m + 1)]
  rw [show (12 : ℚ⟦X⟧) = PowerSeries.C 12 from rfl, show (3 : ℚ⟦X⟧) = PowerSeries.C 3 from rfl,
    PowerSeries.coeff_C, PowerSeries.coeff_C]
  simp

lemma gf : (1 - 4 * PowerSeries.X : ℚ⟦X⟧) ^ 2 * PowerSeries.mk (fun n => (a n : ℚ)) =
    3 * PowerSeries.X * (1 + 4 * PowerSeries.X) := by
  have hshift : PowerSeries.mk (fun n => (a n : ℚ)) =
      PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) := by
    ext n
    rcases n with _ | n
    · rw [coeff_zero_X_mul, PowerSeries.coeff_mk]
      simp [a]
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rw [hshift]
  have hB : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) =
      PowerSeries.mk (fun n => ((6 * n + 3 : ℕ) : ℚ) * (4 : ℚ) ^ n) := by
    congr 1
    funext n
    rw [a_closed]
    push_cast
    ring
  rw [hB]
  set b : ℕ → ℚ := fun n => ((6 * n + 3 : ℕ) : ℚ) * (4 : ℚ) ^ n with hbdef
  set B : ℚ⟦X⟧ := PowerSeries.mk b with hBdef
  have hbc : ∀ n, PowerSeries.coeff n B = b n := fun n => PowerSeries.coeff_mk n b
  have hdist : (1 - 4 * PowerSeries.X : ℚ⟦X⟧) ^ 2 * B =
      B - 8 * (PowerSeries.X * B) + 16 * (PowerSeries.X * (PowerSeries.X * B)) := by
    rw [show (1 - 4 * PowerSeries.X : ℚ⟦X⟧) ^ 2 = 1 - 8 * PowerSeries.X + 16 * PowerSeries.X ^ 2
      from by ring]
    ring
  have hmain : (1 - 4 * PowerSeries.X : ℚ⟦X⟧) ^ 2 * B = 3 + 12 * PowerSeries.X := by
    have hy0 : PowerSeries.coeff 0 ((1 - 4 * PowerSeries.X : ℚ⟦X⟧) ^ 2 * B) = 3 := by
      rw [hdist, map_add, map_sub, coeff_eight_mul, coeff_sixteen_mul, coeff_zero_X_mul,
        coeff_zero_X_mul, hbc, hbdef]
      norm_num
    have hy1 : PowerSeries.coeff 1 ((1 - 4 * PowerSeries.X : ℚ⟦X⟧) ^ 2 * B) = 12 := by
      rw [hdist, map_add, map_sub, coeff_eight_mul, coeff_sixteen_mul,
        PowerSeries.coeff_succ_X_mul 0 B, PowerSeries.coeff_succ_X_mul 0 (PowerSeries.X * B),
        coeff_zero_X_mul, hbc, hbc, hbdef]
      norm_num
    have hy : ∀ m : ℕ, PowerSeries.coeff (m + 2) ((1 - 4 * PowerSeries.X : ℚ⟦X⟧) ^ 2 * B) = 0 := by
      intro m
      rw [hdist, map_add, map_sub, coeff_eight_mul, coeff_sixteen_mul,
        PowerSeries.coeff_succ_X_mul (m + 1) B,
        PowerSeries.coeff_succ_X_mul (m + 1) (PowerSeries.X * B),
        PowerSeries.coeff_succ_X_mul m B, hbc, hbc, hbc, hbdef]
      push_cast
      have hp : (4 : ℚ) ^ (m + 2) = 4 ^ m * 16 := by
        rw [show m + 2 = m + 1 + 1 from rfl, pow_succ, pow_succ]
        ring
      have hp1 : (4 : ℚ) ^ (m + 1) = 4 ^ m * 4 := by rw [pow_succ]
      rw [hp, hp1]
      ring
    ext n
    rcases n with _ | _ | m
    · rw [hy0, coeff_rhs_zero]
    · rw [hy1, coeff_rhs_one]
    · rw [hy m, coeff_rhs_succ]
  rw [show (1 - 4 * PowerSeries.X : ℚ⟦X⟧) ^ 2 * (PowerSeries.X * B) =
    PowerSeries.X * ((1 - 4 * PowerSeries.X : ℚ⟦X⟧) ^ 2 * B) from by ring, hmain]
  ring

end OMA

theorem OMA.solution : type_of% @OMA.S_oeis_a268898.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact OMA.recurrence n
  · exact OMA.gf
  · intro n
    exact OMA.a_closed n
