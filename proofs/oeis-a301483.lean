import OMAStatements.S_oeis_a301483
import Mathlib

-- Problem: oeis-a301483 (Barker's g.f. and recurrence for a(n) = floor(a(n-1) / (2^(1/3) - 1)))
-- Credit: @Aijy0264561
-- theta = 1/(2^(1/3) - 1) = alpha^2 + alpha + 1 is a root of x^3 - 3x^2 - 3x - 1. Let b satisfy Barker's
-- recurrence; b(n+3) - 3b(n+2) - 3b(n+1) - b(n) = -1, so g(n) = theta b(n) - b(n+1) - (theta - 1)/6
-- satisfies g(n+2) = (3 - theta) g(n+1) - g(n)/theta (using (theta - 1)^3 = 6 theta). The quadratic
-- form y^2 - (3 - theta) x y + x^2/theta is positive definite and shrinks by 1/theta each step, which
-- keeps |g| < 0.4477 < (theta - 1)/6, so floor(theta b(n)) = b(n+1) for all n >= 1 and a = b.

namespace OMA.A301483proof

open OMA.S_oeis_a301483 PowerSeries

/-- The linear recurrence sequence. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 11
  | n + 4 => 4 * b (n + 3) - 2 * b (n + 1) - b n

lemma b_rec (n : ℕ) : b (n + 4) = 4 * b (n + 3) - 2 * b (n + 1) - b n := rfl

lemma s_const (n : ℕ) : b (n + 3) - 3 * b (n + 2) - 3 * b (n + 1) - b n = -1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [b_rec]; linarith

noncomputable def α : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)

lemma α_cube : α ^ 3 = 2 := by
  unfold α
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma α_pos : 0 < α := by unfold α; positivity

lemma α_lo : (1.259921 : ℝ) < α := by
  by_contra h; push Not at h
  have := pow_le_pow_left₀ α_pos.le h 3
  rw [α_cube] at this; norm_num at this

lemma α_hi : α < 1.259922 := by
  by_contra h; push Not at h
  have := pow_le_pow_left₀ (by norm_num) h 3
  rw [α_cube] at this; norm_num at this

noncomputable def θ : ℝ := 1 / (α - 1)

lemma θ_eq : θ = α ^ 2 + α + 1 := by
  unfold θ
  have h : α - 1 ≠ 0 := by linarith [α_lo]
  field_simp
  linear_combination (-1 : ℝ) * α_cube

lemma θ_cubic : θ ^ 3 = 3 * θ ^ 2 + 3 * θ + 1 := by
  rw [θ_eq]; linear_combination (α ^ 3 + 3 * α ^ 2 + 3 * α + 3) * α_cube

lemma θ_lo : (3.847321 : ℝ) < θ := by rw [θ_eq]; nlinarith [α_lo, α_hi]
lemma θ_hi : θ < 3.847326 := by rw [θ_eq]; nlinarith [α_lo, α_hi]

/-- The centred error. -/
noncomputable def g (n : ℕ) : ℝ := θ * b n - b (n + 1) - (θ - 1) / 6

lemma g_rec (n : ℕ) : g (n + 2) = (3 - θ) * g (n + 1) - g n / θ := by
  have hs := s_const n
  have hθ : θ ≠ 0 := by linarith [θ_lo]
  have hc := θ_cubic
  unfold g
  have hs' : (b (n + 3) : ℝ) - 3 * b (n + 2) - 3 * b (n + 1) - b n = -1 := by exact_mod_cast hs
  rw [show (b (n + 2 + 1) : ℝ) = b (n + 3) from rfl, show (b (n + 1 + 1) : ℝ) = b (n + 2) from rfl]
  field_simp
  linear_combination (-6 * θ) * hs' + (6 * (b (n + 1) : ℝ) - 1) * hc

/-- The decaying quadratic form. -/
noncomputable def F (x y : ℝ) : ℝ := y ^ 2 - (3 - θ) * x * y + x ^ 2 / θ

lemma F_step (n : ℕ) : F (g (n + 1)) (g (n + 2)) = F (g n) (g (n + 1)) / θ := by
  have hθ : θ ≠ 0 := by linarith [θ_lo]
  unfold F; rw [g_rec]; field_simp; ring

lemma c_pos : (0.3094 : ℝ) < 1 - θ * (3 - θ) ^ 2 / 4 := by nlinarith [θ_lo, θ_hi]

lemma F_split (x y : ℝ) :
    θ * F x y = (x - θ * (3 - θ) / 2 * y) ^ 2 + θ * (1 - θ * (3 - θ) ^ 2 / 4) * y ^ 2 := by
  have hθ : θ ≠ 0 := by linarith [θ_lo]
  unfold F; field_simp; ring

lemma F_nonneg (x y : ℝ) : 0 ≤ F x y := by
  have hθ : 0 < θ := by linarith [θ_lo]
  have h := F_split x y
  have : 0 ≤ θ * F x y := by rw [h]; have := c_pos; positivity
  exact (mul_nonneg_iff_of_pos_left hθ).mp this

lemma F_decr (n : ℕ) : F (g (n + 1)) (g (n + 2)) ≤ F (g 1) (g 2) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [F_step]; exact le_trans (div_le_self (F_nonneg _ _) (by linarith [θ_lo])) ih

lemma F12 : F (g 1) (g 2) < 0.062 := by
  have h1 := θ_lo; have h2 := θ_hi
  have hθ : 0 < θ := by linarith
  have e : F (g 1) (g 2) = (42 * θ ^ 2 - 150 * θ - 36) / (36 * θ) := by
    unfold F g; simp only [b]; push_cast
    rw [eq_div_iff (by positivity)]
    field_simp
    linear_combination 36 * (85 * θ - 325) * θ_cubic
  rw [e, div_lt_iff₀ (by positivity)]
  nlinarith

lemma g_bound (n : ℕ) : |g (n + 2)| < 0.4477 := by
  have h1 := θ_lo; have h2 := θ_hi
  have hθ : 0 < θ := by linarith
  have hF := lt_of_le_of_lt (F_decr n) F12
  have hs := F_split (g (n + 1)) (g (n + 2))
  have hc := c_pos
  have hsq := sq_nonneg (g (n + 1) - θ * (3 - θ) / 2 * g (n + 2))
  have hy : (1 - θ * (3 - θ) ^ 2 / 4) * g (n + 2) ^ 2 ≤ F (g (n + 1)) (g (n + 2)) := by
    have : θ * ((1 - θ * (3 - θ) ^ 2 / 4) * g (n + 2) ^ 2) ≤ θ * F (g (n + 1)) (g (n + 2)) := by
      rw [hs]; nlinarith
    exact le_of_mul_le_mul_left this hθ
  have hy2 : g (n + 2) ^ 2 < 0.2004 := by nlinarith [sq_nonneg (g (n + 2))]
  rw [abs_lt]; constructor <;> nlinarith [sq_nonneg (g (n + 2) + 0.4477), sq_nonneg (g (n + 2) - 0.4477)]

lemma e_mem (n : ℕ) (hn : 1 ≤ n) : 0 ≤ θ * b n - b (n + 1) ∧ θ * b n - b (n + 1) < 1 := by
  have h1 := θ_lo; have h2 := θ_hi
  have hE : θ * b n - b (n + 1) = g n + (θ - 1) / 6 := by unfold g; ring
  rw [hE]
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    unfold g; simp only [b]; push_cast; constructor <;> nlinarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have := g_bound k
    rw [abs_lt] at this
    constructor <;> linarith

lemma a_eq_b (n : ℕ) : a n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | k + 2, ih =>
      have hk := ih (k + 1) (by omega)
      have hdiv : ((a (k + 1) : ℤ) : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) = θ * b (k + 1) := by
        rw [hk]; unfold θ α; ring
      show ⌊((a (k + 1) : ℤ) : ℝ) / ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1)⌋ = b (k + 2)
      rw [hdiv, Int.floor_eq_iff]
      obtain ⟨l, u⟩ := e_mem (k + 1) (by omega)
      constructor <;> linarith

lemma coeff_mul_X1 (φ : PowerSeries ℤ) (n : ℕ) :
    coeff n (φ * X) = if 1 ≤ n then coeff (n - 1) φ else 0 := by
  simpa using coeff_mul_X_pow' φ 1 n

lemma coeff_X1 (n : ℕ) : coeff n (X : PowerSeries ℤ) = if n = 1 then 1 else 0 := by
  rw [coeff_X]

theorem a301483 : type_of% @OMA.S_oeis_a301483.main := by
  have ha : a = b := funext a_eq_b
  refine ⟨?_, ?_⟩
  · rw [ha, mul_comm,
      show ((1 - X) * (1 - 3 * X - 3 * X ^ 2 - X ^ 3) : PowerSeries ℤ) =
        1 - C 4 * X + C 2 * X ^ 3 + X ^ 4 by simp only [map_ofNat]; ring,
      show (X * (1 - X - X ^ 2) : PowerSeries ℤ) = X - X ^ 2 - X ^ 3 by ring]
    ext n
    simp only [mul_sub, mul_add, mul_one, map_sub, map_add, mul_left_comm (mk _) (C _),
      coeff_C_mul, coeff_mul_X_pow', coeff_mul_X1, coeff_mk, coeff_X_pow, coeff_X1]
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp [b]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hr := b_rec m
      have c1 : 1 ≤ m + 4 := by omega
      have c3 : 3 ≤ m + 4 := by omega
      have c4 : 4 ≤ m + 4 := by omega
      have d1 : m + 4 ≠ 1 := by omega
      have d2 : m + 4 ≠ 2 := by omega
      have d3 : m + 4 ≠ 3 := by omega
      rw [if_pos c1, if_pos c3, if_pos c4, if_neg d1, if_neg d2, if_neg d3,
        show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega,
        show m + 4 - 4 = m by omega]
      linarith
  · intro n hn
    rw [ha]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have := b_rec (m + 1)
    simp only [show m + 5 - 1 = m + 1 + 3 by omega, show m + 5 - 3 = m + 1 + 1 by omega,
      show m + 5 - 4 = m + 1 by omega, show m + 5 = m + 1 + 4 by omega]
    linarith

end OMA.A301483proof

theorem OMA.solution : type_of% @OMA.S_oeis_a301483.main := OMA.A301483proof.a301483
