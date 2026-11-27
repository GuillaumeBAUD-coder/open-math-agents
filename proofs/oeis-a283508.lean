import OMAStatements.S_oeis_a283508

namespace CAgrid
open OMA.S_oeis_a283508

/-- Stage one is on away from the four axial neighbors of the origin. -/
private def cross : Grid := fun x y =>
  decide (¬ ((x = -1 ∨ x = 1) ∧ y = 0 ∨ x = 0 ∧ (y = -1 ∨ y = 1)))

/-- At stage two exactly the eight neighbors in the surrounding square are off. -/
private def ringGrid : Grid := fun x y =>
  decide ((x = 0 ∧ y = 0) ∨ x < -1 ∨ 1 < x ∨ y < -1 ∨ 1 < y)

private def outside (x y : ℤ) : Prop := x < -1 ∨ 1 < x ∨ y < -1 ∨ 1 < y

private lemma initial_far {x y : ℤ} (h : outside x y) : initial x y = false := by
  simp only [initial, decide_eq_false_iff_not]
  unfold outside at h
  omega

private lemma cross_far {x y : ℤ} (h : outside x y) : cross x y = true := by
  simp only [cross, decide_eq_true_eq]
  unfold outside at h
  omega

private lemma ring_far {x y : ℤ} (h : outside x y) : ringGrid x y = true := by
  exact decide_eq_true (Or.inr h)

/-- Outside the radius-two square all five inputs are background cells. Inside it,
the local identities reduce to the twenty-five possible sites. -/
private lemma local_grid {f g : Grid} {b c : Bool}
    (hf : ∀ {x y}, outside x y → f x y = b) (hg : ∀ {x y}, outside x y → g x y = c)
    (hbg : rule b (bit b + bit b + bit b + bit b) = c)
    (hsmall : ∀ x y : ℤ, -2 ≤ x → x ≤ 2 → -2 ≤ y → y ≤ 2 → step f x y = g x y) :
    step f = g := by
  funext x y
  by_cases h : x < -2 ∨ 2 < x ∨ y < -2 ∨ 2 < y
  · simpa (disch := unfold outside; omega) only [step, neighbors, hf, hg] using hbg
  · push Not at h
    exact hsmall x y h.1 h.2.1 h.2.2.1 h.2.2.2

private theorem initial_step : step initial = cross := by
  apply local_grid initial_far cross_far (by decide)
  intro x y hxl hxr hyl hyr
  interval_cases x <;> interval_cases y <;> decide

private theorem cross_step : step cross = ringGrid := by
  apply local_grid cross_far ring_far (by decide)
  intro x y hxl hxr hyl hyr
  interval_cases x <;> interval_cases y <;> decide

private theorem ring_step : step ringGrid = ringGrid := by
  apply local_grid ring_far ring_far (by decide)
  intro x y hxl hxr hyl hyr
  interval_cases x <;> interval_cases y <;> decide

private theorem stable (n : ℕ) : state (n+2) = ringGrid := by
  induction n with
  | zero => exact (congrArg step initial_step).trans cross_step
  | succ n ih => exact (congrArg step ih).trans ring_step

theorem zero_term : a 0 = 1 := by decide
theorem one_term : a 1 = 10 := by decide

theorem succ_term : ∀ n : ℕ, a (n+2) = 10 * a (n+1) + 1
  | 0 => by decide
  | n+1 => by
    change encode (state ((n+1)+2)) ((n+2)+1) = 10 * encode (state (n+2)) (n+2) + 1
    rw [stable, stable, encode]
    simp [ringGrid, bit]
    omega

private lemma rule187 (l c r : Bool) : A267623.rule l c r = (!c || r) := by
  cases l <;> cases c <;> cases r <;> decide

/-- The sole off cell of the one-dimensional rule moves left by one at each step. -/
private theorem row (n : ℕ) : A267623.state (n+1) = fun x => decide (x ≠ -(n:ℤ)) := by
  induction n with
  | zero =>
    funext x
    change A267623.rule _ _ _ = _
    rw [rule187]
    simp only [A267623.state, A267623.initial, Int.ofNat_zero, neg_zero]
    by_cases h : x = 0 <;> simp [h]
  | succ n ih =>
    funext x
    change A267623.rule _ _ _ = _
    rw [rule187, ih]
    by_cases h : x = -(n:ℤ) <;> simp [h]
    omega

theorem comp_term : ∀ n : ℕ, a n = A267623.a n
  | 0 => by decide
  | 1 => by decide
  | n+2 => by
    rw [succ_term, A267623.a, comp_term (n+1), row (n+1)]
    simp [bit]
    omega

end CAgrid

namespace CAseries
open PowerSeries

lemma finish (a : ℕ → ℕ) (h0 : a 0 = 1) (h1 : a 1 = 10)
    (hs : ∀ n : ℕ, a (n+2) = 10 * a (n+1) + 1) :
    (PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X)) =
      1 - PowerSeries.X + PowerSeries.X^2) ∧
    (∀ n : ℕ, 0<n → a n = (91 * 10^n - 10)/90) ∧
    (∀ n : ℕ, 2<n → (a n : ℤ) = 11*(a (n-1):ℤ) - 10*(a (n-2):ℤ)) := by
  have hz (n : ℕ) : (a (n+2) : ℤ) = 10 * (a (n+1) : ℤ) + 1 := by exact_mod_cast hs n
  have hh (n : ℕ) : (a (n+3) : ℤ) = 11*(a (n+2):ℤ) - 10*(a (n+1):ℤ) := by
    linarith [hz n, hz (n+1)]
  refine ⟨?_, ?_, ?_⟩
  · let F := PowerSeries.mk (fun n => (a n : ℤ))
    change F * _ = _
    have poly : F * ((1 - X) * (1 - 10 * X)) =
        F - (11:ℕ) • (F * X) + (10:ℕ) • ((F * X) * X) := by
      simp only [nsmul_eq_mul, Nat.cast_ofNat]; ring
    rw [poly]
    ext n
    simp only [map_add, map_sub, map_nsmul, coeff_one, coeff_X, coeff_X_pow]
    rcases n with _ | _ | _ | n
    · simp [F,h0, coeff_zero_mul_X]
    · norm_num [F,h0,h1, coeff_succ_mul_X, coeff_zero_mul_X]
    · norm_num [F,h0,h1, hs 0, coeff_succ_mul_X, coeff_zero_mul_X]
    · simp only [coeff_succ_mul_X, F, coeff_mk, nsmul_eq_mul, Nat.cast_ofNat]
      simp only [show n+3 ≠ 0 by omega, show n+3 ≠ 1 by omega, show n+3 ≠ 2 by omega, if_false]
      linarith [hh n]
  · intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hnum (k : ℕ) : 90 * a (k+1) + 10 = 91 * 10^(k+1) := by
      induction k with
      | zero => norm_num [h1]
      | succ k ih =>
        rw [show k.succ+1 = k+2 by omega, hs k, pow_succ (10:ℕ) (k+1)]
        omega
    change a (k+1) = (91*10^(k+1)-10)/90
    rw [← hnum k, Nat.add_sub_cancel]
    simp
  · intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
    simpa [Nat.add_comm 3 k, Nat.add_sub_assoc] using hh k

end CAseries

open OMA.S_oeis_a283508 in
theorem OMA.solution : type_of% @OMA.S_oeis_a283508.main := by
  obtain ⟨hseries, hformula, hrec⟩ := CAseries.finish a CAgrid.zero_term
    CAgrid.one_term CAgrid.succ_term
  exact ⟨hseries, hformula, hrec, CAgrid.comp_term⟩
