import OMAStatements.S_oeis_a001951
import Mathlib

/-!
The square with root (n) gives the required witness. Squaring the two floor
inequalities bounds the distance to the triangular number in both directions.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a001951.main := by
  intro n
  let m := OMA.S_oeis_a001951.a n
  let x := (n : ℝ) * Real.sqrt 2
  have xNonneg : 0 ≤ x := by dsimp [x]; positivity
  have mNonneg : (0 : ℝ) ≤ m := by positivity
  have floorLo : (m : ℝ) ≤ x :=
    Nat.floor_le xNonneg
  have floorHi : x < (m : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have square : x^2 = 2 * (n : ℝ)^2 := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have lo : (m : ℝ)^2 ≤ 2 * (n : ℝ)^2 := by
    have h := mul_nonneg (sub_nonneg.mpr floorLo) (add_nonneg xNonneg mNonneg)
    nlinarith only [h, square]
  have hi : 2 * (n : ℝ)^2 < ((m : ℝ)+1)^2 := by
    have pos : 0 < (m : ℝ)+1+x := by linarith only [mNonneg, xNonneg]
    have h := mul_pos (sub_pos.mpr floorHi) pos
    nlinarith only [h, square]
  have loN : m^2 ≤ 2 * n^2 := by exact_mod_cast lo
  have hiN : 2 * n^2 < (m+1)^2 := by exact_mod_cast hi
  have loZ : (m : ℤ)^2 ≤ 2 * (n : ℤ)^2 := by exact_mod_cast loN
  have hiZ : 2 * (n : ℤ)^2 < ((m : ℤ)+1)^2 := by exact_mod_cast hiN
  have evenProduct : 2 ∣ m*(m+1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self m)
  let t : ℤ := ((m*(m+1)/2 : ℕ) : ℤ)
  have twice : t*2 = (m : ℤ)*((m : ℤ)+1) := by
    dsimp [t]
    exact_mod_cast Nat.div_mul_cancel evenProduct
  have upper : 2 * (t - (n : ℤ)^2) ≤ (m : ℤ) := by
    nlinarith only [twice, loZ]
  have lower : 2 * ((n : ℤ)^2 - t) < (m : ℤ)+1 := by
    nlinarith only [twice, hiZ]
  have division : (m : ℤ) < 2 * ((m/2 : ℕ) : ℤ) + 2 := by
    exact_mod_cast (by omega : m < 2*(m/2)+2)
  refine ⟨n, ?_⟩
  change |t - (n : ℤ)^2| ≤ ((m/2 : ℕ) : ℤ)
  rw [abs_le]
  omega