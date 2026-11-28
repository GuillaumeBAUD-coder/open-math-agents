import OMAStatements.S_oeis_a228931

-- Problem: A228931: Optimal ascending continued fraction expansion of sqrt(2)-1.
-- Upstream: formal-conjectures statements/oeis-a228931.lean:0 (declaration OMA.S_oeis_a228931.main)
-- Credit: @datdzrgb (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A228931Aux

open OMA.S_oeis_a228931

/-- The integer traces `u + 1/u` of the residuals from index `1` on. -/
def Q : ℕ → ℤ
  | 0 => 6
  | k + 1 => Q k ^ 2 - 2

theorem Q_ge (k : ℕ) : 3 ≤ Q k := by
  induction k with
  | zero => simp [Q]
  | succ k ih => simp only [Q]; nlinarith

theorem magnitude_eq (z : ℝ) (q : ℤ) (h0 : 0 < |z|) (h1 : |z| < 1 / 2)
    (he : |z| ^ 2 - q * |z| + 1 = 0) : magnitude z = q := by
  have hu : 1 / |z| = q - |z| := by
    field_simp
    nlinarith
  unfold magnitude
  rw [round_eq_iff, hu]
  constructor <;> linarith

theorem step_eq (z : ℝ) (q : ℤ) (h0 : 0 < |z|) (h1 : |z| < 1 / 2)
    (he : |z| ^ 2 - q * |z| + 1 = 0) : step z = |z| ^ 2 := by
  unfold step
  rw [magnitude_eq z q h0 h1 he]
  linarith

theorem sqrt_two_bounds : (1.41 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.42 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem residual_one : residual 1 = 2 * Real.sqrt 2 - 3 := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have habs : |Real.sqrt 2 - 1| = Real.sqrt 2 - 1 := abs_of_pos (by linarith)
  have hm : magnitude (Real.sqrt 2 - 1) = 2 := by
    unfold magnitude
    have hu : 1 / |Real.sqrt 2 - 1| = Real.sqrt 2 + 1 := by
      rw [habs, div_eq_iff (by linarith)]
      linear_combination -hs
    rw [round_eq_iff, hu]
    constructor <;> push_cast <;> linarith
  show step (Real.sqrt 2 - 1) = _
  unfold step
  rw [hm, habs]
  push_cast
  ring

theorem inv (k : ℕ) :
    0 < |residual (k + 1)| ∧ |residual (k + 1)| < 1 / 2 ∧
      |residual (k + 1)| ^ 2 - Q k * |residual (k + 1)| + 1 = 0 ∧
      (1 ≤ k → 0 < residual (k + 1)) := by
  induction k with
  | zero =>
    obtain ⟨h1, h2⟩ := sqrt_two_bounds
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have habs : |residual 1| = 3 - 2 * Real.sqrt 2 := by
      rw [residual_one, abs_of_neg (by linarith)]; ring
    rw [habs]
    refine ⟨by linarith, by linarith, ?_, by omega⟩
    simp only [Q]
    push_cast
    nlinarith
  | succ k ih =>
    obtain ⟨h0, h1, he, -⟩ := ih
    have hr : residual (k + 1 + 1) = |residual (k + 1)| ^ 2 :=
      step_eq _ _ h0 h1 he
    have hpos : 0 < residual (k + 1 + 1) := by rw [hr]; positivity
    rw [abs_of_pos hpos, hr]
    refine ⟨by positivity, by nlinarith, ?_, fun _ => by positivity⟩
    simp only [Q]
    push_cast
    have : |residual (k + 1)| ^ 2 + 1 = Q k * |residual (k + 1)| := by linarith
    have h2 : (|residual (k + 1)| ^ 2 + 1) ^ 2 = (Q k * |residual (k + 1)|) ^ 2 := by rw [this]
    nlinarith

theorem a_eq (k : ℕ) (hk : 1 ≤ k) : a (k + 2) = Q k := by
  obtain ⟨h0, h1, he, hp⟩ := inv k
  show digit (residual (k + 1)) = _
  unfold digit
  rw [if_neg (not_lt.mpr (hp hk).le)]
  exact magnitude_eq _ _ h0 h1 he

theorem a_two : a 2 = -6 := by
  obtain ⟨h0, h1, he, -⟩ := inv 0
  obtain ⟨b1, b2⟩ := sqrt_two_bounds
  show digit (residual 1) = _
  unfold digit
  rw [if_pos (by rw [residual_one]; linarith), magnitude_eq _ _ h0 h1 he]
  rfl

theorem a_one : a 1 = 2 := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have habs : |Real.sqrt 2 - 1| = Real.sqrt 2 - 1 := abs_of_pos (by linarith)
  show digit (Real.sqrt 2 - 1) = _
  unfold digit
  rw [if_neg (by linarith)]
  unfold magnitude
  have hu : 1 / |Real.sqrt 2 - 1| = Real.sqrt 2 + 1 := by
    rw [habs, div_eq_iff (by linarith)]
    linear_combination -hs
  rw [round_eq_iff, hu]
  constructor <;> push_cast <;> linarith

end OMA.A228931Aux

open OMA.A228931Aux OMA.S_oeis_a228931 in
theorem OMA.solution : type_of% @OMA.S_oeis_a228931.main := by
  refine ⟨a_one, a_two, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [a_eq k (by omega)]
    have := Q_ge k
    omega
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 + 1 = (k + 1) + 2 from rfl, a_eq (k + 1) (by omega)]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [a_two]; rfl
    · rw [a_eq k hk]; rfl
