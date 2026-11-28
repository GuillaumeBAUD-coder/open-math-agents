import FormalConjectures.Wikipedia.Hall

-- Problem: Hall's conjecture — danilov
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Hall.lean:77 (declaration Hall.danilov)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Danilov: the identity `(z²+6z+4)³ - (z²+1)(z²+9z+19)² = -27(2z+11)` evaluated along the
solutions of `z² + 1 = 5w²` gives `|y² - x³| = O(√x)` infinitely often. -/

namespace OMA.HallDanilov

/-- Arbitrarily large solutions of the negative Pell equation `z ^ 2 + 1 = 5 * w ^ 2`. -/
lemma pell_large (N : ℕ) : ∃ z w : ℕ, N ≤ z ∧ 1 ≤ w ∧ z ^ 2 + 1 = 5 * w ^ 2 := by
  induction N with
  | zero => exact ⟨2, 1, by norm_num, le_rfl, by norm_num⟩
  | succ n ih =>
    obtain ⟨z, w, hz, hw, hzw⟩ := ih
    exact ⟨9 * z + 20 * w, 4 * z + 9 * w, by omega, by omega, by nlinarith [hzw]⟩

/-- Danilov-type identity, specialised to the Pell solutions. -/
lemma key (z w : ℤ) (h : z ^ 2 + 1 = 5 * w ^ 2) :
    (25 * w * (z ^ 2 + 9 * z + 19)) ^ 2 - (5 * (z ^ 2 + 6 * z + 4)) ^ 3
      = 3375 * (2 * z + 11) := by
  linear_combination (-125 * (z ^ 2 + 9 * z + 19) ^ 2) * h

end OMA.HallDanilov

open OMA.HallDanilov in
theorem OMA.solution : type_of% @Hall.danilov := by
  intro δ hδ ⟨C, hC, hH⟩
  -- choose a large threshold
  set M : ℝ := 3375 * 13 / C with hM
  have hev : ∀ᶠ n : ℕ in Filter.atTop, M ≤ ((n : ℝ)) ^ (2 * δ) :=
    ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M
  obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
  obtain ⟨z, w, hz, -, hzw⟩ := pell_large (N + 1)
  have hz1 : 1 ≤ z := by omega
  have hzN : N ≤ z := by omega
  set x : ℤ := 5 * ((z : ℤ) ^ 2 + 6 * z + 4) with hx
  set y : ℤ := 25 * (w : ℤ) * ((z : ℤ) ^ 2 + 9 * z + 19) with hy
  have hkey : y ^ 2 - x ^ 3 = 3375 * (2 * (z : ℤ) + 11) :=
    key z w (by exact_mod_cast hzw)
  have hne : y ^ 2 ≠ x ^ 3 := by
    intro h; rw [h, sub_self] at hkey; omega
  have hlt := hH x y hne
  rw [hkey] at hlt
  have hxpos : (0 : ℤ) ≤ x := by positivity
  rw [abs_of_nonneg (by exact_mod_cast hxpos : (0 : ℝ) ≤ (x : ℝ))] at hlt
  rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ 3375 * (2 * (z : ℤ) + 11))] at hlt
  rw [hx] at hlt
  push_cast at hlt
  -- lower bound on x ^ (1/2 + δ)
  have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  have hxz : (z : ℝ) ^ 2 ≤ 5 * ((z : ℝ) ^ 2 + 6 * z + 4) := by nlinarith
  have hpow : ((z : ℝ) ^ 2) ^ (2⁻¹ + δ) ≤ (5 * ((z : ℝ) ^ 2 + 6 * z + 4)) ^ (2⁻¹ + δ) :=
    Real.rpow_le_rpow (by positivity) hxz (by positivity)
  have hz2 : ((z : ℝ) ^ 2) ^ (2⁻¹ + δ) = (z : ℝ) * (z : ℝ) ^ (2 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [show ((2 : ℕ) : ℝ) * (2⁻¹ + δ) = 1 + 2 * δ by push_cast; ring]
    rw [Real.rpow_add (by positivity), Real.rpow_one]
  have hMz := hN z hzN
  have hCM : C * M = 3375 * 13 := by rw [hM]; field_simp
  have : 3375 * (2 * (z : ℝ) + 11) ≤ C * (z * (z : ℝ) ^ (2 * δ)) := by
    have h1 : 3375 * (2 * (z : ℝ) + 11) ≤ C * M * z := by rw [hCM]; nlinarith
    have h2 : C * M * z ≤ C * (z * (z : ℝ) ^ (2 * δ)) := by
      have := mul_le_mul_of_nonneg_left hMz (le_of_lt hC)
      nlinarith
    linarith
  have h3 : C * (z * (z : ℝ) ^ (2 * δ))
      ≤ C * (5 * ((z : ℝ) ^ 2 + 6 * z + 4)) ^ (2⁻¹ + δ) := by
    rw [← hz2]; exact mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
  linarith
