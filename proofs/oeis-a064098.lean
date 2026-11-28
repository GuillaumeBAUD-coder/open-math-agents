import OMAStatements.S_oeis_a064098
import Mathlib

namespace OMA.A064098Proof

open OMA.S_oeis_a064098 Filter Topology

/-- The Markov-triple form of the recurrence. -/
def m : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | n + 4 => 3 * m (n + 3) * m (n + 2) - m (n + 1)

theorem m_succ4 (n : ℕ) : m (n + 4) = 3 * m (n + 3) * m (n + 2) - m (n + 1) := rfl

theorem inv (n : ℕ) :
    m (n + 1) ^ 2 + m (n + 2) ^ 2 + m (n + 3) ^ 2 = 3 * m (n + 1) * m (n + 2) * m (n + 3) := by
  induction n with
  | zero => simp [m]
  | succ n ih =>
    rw [show n + 1 + 3 = n + 4 from rfl, m_succ4]
    linear_combination ih

theorem mono (n : ℕ) :
    1 ≤ m n ∧ m n ≤ m (n + 1) ∧ m (n + 1) ≤ m (n + 2) ∧ m (n + 2) ≤ m (n + 3) := by
  induction n with
  | zero => simp [m]
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨by linarith, h2, h3, ?_⟩
    rw [show n + 1 + 3 = n + 4 from rfl, m_succ4]
    nlinarith

theorem mul_eq (n : ℕ) : m (n + 4) * m (n + 1) = m (n + 3) ^ 2 + m (n + 2) ^ 2 := by
  rw [m_succ4]
  linear_combination -(inv n)

theorem a_eq : ∀ n, (a n : ℤ) = m n
  | 0 => by simp [a, m]
  | 1 => by simp [a, m]
  | 2 => by simp [a, m]
  | 3 => by simp [a, m]
  | n + 4 => by
    have h1 := a_eq (n + 1)
    have h2 := a_eq (n + 2)
    have h3 := a_eq (n + 3)
    show (((a (n + 3) ^ 2 + a (n + 2) ^ 2) / a (n + 1) : ℕ) : ℤ) = m (n + 4)
    rw [Int.natCast_div]
    push_cast
    rw [h1, h2, h3]
    have hpos : m (n + 1) ≠ 0 := by have := (mono (n + 1)).1; omega
    exact Int.ediv_eq_of_eq_mul_left hpos (mul_eq n).symm

theorem r_ge (n : ℕ) : (1 : ℝ) ≤ a n := by
  have h := (mono n).1
  rw [← a_eq] at h
  exact_mod_cast h

theorem r_up (n : ℕ) : (a (n + 4) : ℝ) ≤ 3 * a (n + 3) * a (n + 2) := by
  have h : (a (n + 4) : ℤ) ≤ 3 * a (n + 3) * a (n + 2) := by
    rw [a_eq, a_eq, a_eq, m_succ4]
    have := (mono (n + 1)).1
    linarith
  exact_mod_cast h

theorem r_lo (n : ℕ) : (a (n + 3) : ℝ) * a (n + 2) ≤ a (n + 4) := by
  have h : (a (n + 3) : ℤ) * a (n + 2) ≤ a (n + 4) := by
    rw [a_eq, a_eq, a_eq, m_succ4]
    obtain ⟨h0, h1, h2, h3⟩ := mono (n + 1)
    nlinarith
  exact_mod_cast h

noncomputable def x (n : ℕ) : ℝ := Real.log (a n)

theorem x_up (n : ℕ) : x (n + 4) ≤ Real.log 3 + x (n + 3) + x (n + 2) := by
  unfold x
  have h3 := r_ge (n + 3)
  have h2 := r_ge (n + 2)
  rw [← Real.log_mul (by norm_num) (by linarith), ← Real.log_mul (by positivity) (by linarith)]
  exact Real.log_le_log (by linarith [r_ge (n + 4)]) (by linarith [r_up n])

theorem x_lo (n : ℕ) : x (n + 3) + x (n + 2) ≤ x (n + 4) := by
  unfold x
  have h3 := r_ge (n + 3)
  have h2 := r_ge (n + 2)
  rw [← Real.log_mul (by linarith) (by linarith)]
  exact Real.log_le_log (by nlinarith) (r_lo n)

noncomputable def φ : ℝ := (Real.sqrt 5 + 1) / 2

theorem φ_sq : φ ^ 2 = φ + 1 := by
  unfold φ
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  linear_combination this / 4

theorem one_lt_φ : 1 < φ := by
  unfold φ
  have : (1 : ℝ) < Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem x_four : x 4 = Real.log 2 := by
  unfold x; rw [show a 4 = 2 from rfl]; norm_num

theorem x_five : x 5 = Real.log 5 := by
  unfold x; rw [show a 5 = 5 from rfl]; norm_num

theorem lower (n : ℕ) : Real.log 2 / φ * φ ^ n ≤ x (n + 4) ∧
    Real.log 2 / φ * φ ^ (n + 1) ≤ x (n + 5) := by
  have hφ := one_lt_φ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  induction n with
  | zero =>
    constructor
    · rw [pow_zero, mul_one, x_four]
      rw [div_le_iff₀ (by linarith)]; nlinarith
    · rw [zero_add, pow_one, div_mul_cancel₀ _ (by linarith), x_five]
      exact Real.log_le_log (by norm_num) (by norm_num)
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h := x_lo (n + 2)
    rw [show n + 2 + 3 = n + 5 from rfl, show n + 2 + 2 = n + 4 from rfl,
      show n + 2 + 4 = n + 1 + 5 from rfl] at h
    have e : Real.log 2 / φ * φ ^ (n + 1 + 1) =
        Real.log 2 / φ * φ ^ n + Real.log 2 / φ * φ ^ (n + 1) := by
      rw [pow_succ, pow_succ]; linear_combination (Real.log 2 / φ * φ ^ n) * φ_sq
    rw [e]
    linarith [ih.1, ih.2]

theorem upper (n : ℕ) : x (n + 2) + Real.log 3 ≤ 2 * Real.log 3 * φ ^ n ∧
    x (n + 3) + Real.log 3 ≤ 2 * Real.log 3 * φ ^ (n + 1) := by
  have hφ := one_lt_φ
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have x2 : x 2 = 0 := by unfold x; rw [show a 2 = 1 from rfl]; simp
  have x3 : x 3 = 0 := by unfold x; rw [show a 3 = 1 from rfl]; simp
  induction n with
  | zero =>
    constructor
    · rw [x2]; simp; linarith
    · rw [zero_add, pow_one, x3]; nlinarith
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h := x_up n
    rw [show n + 1 + 3 = n + 4 from rfl]
    have e : 2 * Real.log 3 * φ ^ (n + 1 + 1) =
        2 * Real.log 3 * φ ^ n + 2 * Real.log 3 * φ ^ (n + 1) := by
      rw [pow_succ, pow_succ]; linear_combination (2 * Real.log 3 * φ ^ n) * φ_sq
    rw [e]
    linarith [ih.1, ih.2]

theorem lim_aux (A B : ℝ) :
    Tendsto (fun k : ℕ => (A + k * B) / ((k : ℝ) + 4)) atTop (𝓝 B) := by
  have h : Tendsto (fun k : ℕ => (A - 4 * B) / ((k + 4 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (A - 4 * B)).comp (tendsto_add_atTop_nat 4)
  have h2 := h.const_add B
  rw [add_zero] at h2
  refine h2.congr (fun k => ?_)
  have : (0 : ℝ) < (k : ℝ) + 4 := by positivity
  push_cast
  field_simp
  ring

end OMA.A064098Proof

open OMA.A064098Proof Filter Topology in
theorem OMA.solution : type_of% @OMA.S_oeis_a064098.main := by
  have hφ := one_lt_φ
  have hφ0 : 0 < φ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / φ := by positivity
  rw [← tendsto_add_atTop_iff_nat 4]
  change Tendsto (fun k : ℕ => Real.log (x (k + 4)) / ((k + 4 : ℕ) : ℝ)) atTop (𝓝 (Real.log φ))
  have hlo := lim_aux (Real.log (Real.log 2 / φ)) (Real.log φ)
  have hhi := lim_aux (Real.log (2 * Real.log 3) + 2 * Real.log φ) (Real.log φ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro k
    have h := (lower k).1
    have hk : (0 : ℝ) < (k : ℝ) + 4 := by positivity
    simp only
    push_cast
    apply div_le_div_of_nonneg_right _ hk.le
    have := Real.log_le_log (by positivity) h
    rwa [Real.log_mul hc.ne' (by positivity), Real.log_pow] at this
  · intro k
    have h := (upper (k + 2)).1
    have hk : (0 : ℝ) < (k : ℝ) + 4 := by positivity
    have hpos : 0 < x (k + 4) := lt_of_lt_of_le (by positivity) (lower k).1
    simp only
    push_cast
    apply div_le_div_of_nonneg_right _ hk.le
    have h' : x (k + 4) ≤ 2 * Real.log 3 * φ ^ (k + 2) := by
      rw [show k + 2 + 2 = k + 4 from rfl] at h; linarith
    have := Real.log_le_log hpos h'
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
