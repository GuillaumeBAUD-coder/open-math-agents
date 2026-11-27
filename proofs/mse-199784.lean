import OMAStatements.S_mse_199784
import Mathlib

-- Problem: mse-199784. Is there a totally asymmetric 2P 0-sum game with all payoffs ±1, with a unique
-- Nash equilibrium which assigns positive probability to each strategy? Answer: yes, a 6 × 6 game.
-- Credit: @tatashbar

open OMA.S_mse_199784

namespace OMA.ZS199784

def A : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-1, 1, 1, -1, 1, -1;
     -1, 1, -1, -1, 1, 1;
     -1, -1, 1, 1, 1, -1;
     -1, 1, 1, 1, -1, 1;
     1, -1, -1, -1, -1, 1;
     1, 1, -1, 1, -1, -1]

noncomputable def x : Fin 6 → ℝ := ![2/13, 1/13, 3/13, 1/13, 4/13, 2/13]
noncomputable def y : Fin 6 → ℝ := ![4/13, 1/13, 2/13, 1/13, 3/13, 2/13]

theorem entries : ∀ i j, A i j = 1 ∨ A i j = -1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [A]

theorem asym : IsTotallyAsymmetric A := by
  intro σ τ h
  have hr : ∀ i, ∑ k, A (σ i) k = ∑ k, A i k := by
    intro i
    rw [← Equiv.sum_comp τ (fun k => A (σ i) k)]
    exact Finset.sum_congr rfl (fun k _ => h i k)
  have hw : ∀ j, ∑ i, A i (τ j) * (∑ k, A i k - 1) = ∑ i, A i j * (∑ k, A i k - 1) := by
    intro j
    rw [← Equiv.sum_comp σ (fun i => A i (τ j) * (∑ k, A i k - 1))]
    exact Finset.sum_congr rfl (fun i _ => by rw [h i j, hr i])
  have hf : ∀ i, ∑ j, A (σ i) j * (∑ l, A l j * (∑ k, A l k - 1))
      = ∑ j, A i j * (∑ l, A l j * (∑ k, A l k - 1)) := by
    intro i
    rw [← Equiv.sum_comp τ (fun j => A (σ i) j * (∑ l, A l j * (∑ k, A l k - 1)))]
    exact Finset.sum_congr rfl (fun j _ => by rw [h i j, hw j])
  have hF : ∀ i, ∑ j, A i j * (∑ l, A l j * (∑ k, A l k - 1))
      = (![4, -4, 8, 12, -12, 0] : Fin 6 → ℝ) i := by
    intro i
    fin_cases i <;> simp [A, Fin.sum_univ_six] <;> norm_num
  have hσ : ∀ i, σ i = i := by
    intro i
    have h1 := hf i
    rw [hF, hF] at h1
    generalize σ i = a at h1
    fin_cases a <;> fin_cases i <;> first | rfl | (exfalso; norm_num at h1)
  have hσ1 : σ = 1 := Equiv.ext hσ
  refine ⟨hσ1, Equiv.ext fun j => ?_⟩
  have hcol : ∀ i, A i (τ j) = A i j := by
    intro i
    have := h i j
    rwa [hσ i] at this
  have c0 := hcol 0
  have c1 := hcol 1
  have c2 := hcol 2
  have c3 := hcol 3
  have c4 := hcol 4
  have c5 := hcol 5
  generalize τ j = b at c0 c1 c2 c3 c4 c5
  show b = j
  fin_cases b <;> fin_cases j <;> first | rfl | (exfalso; simp [A] at c0 c1 c2 c3 c4 c5 <;> linarith)

theorem x_mem : x ∈ stdSimplex ℝ (Fin 6) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [x]
  · simp [x, Fin.sum_univ_six] <;> norm_num

theorem y_mem : y ∈ stdSimplex ℝ (Fin 6) := by
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases j <;> norm_num [y]
  · simp [y, Fin.sum_univ_six] <;> norm_num

/-- Against `y`, every strategy of player 1 earns `-1/13`. -/
theorem payoff_y (x' : Fin 6 → ℝ) (h : ∑ i, x' i = 1) : payoff A x' y = -1 / 13 := by
  rw [Fin.sum_univ_six] at h
  simp [payoff, Fin.sum_univ_six, A, y]
  linarith

/-- Against `x`, every strategy of player 2 concedes `-1/13`. -/
theorem payoff_x (y' : Fin 6 → ℝ) (h : ∑ j, y' j = 1) : payoff A x y' = -1 / 13 := by
  rw [Fin.sum_univ_six] at h
  simp [payoff, Fin.sum_univ_six, A, x]
  linarith

theorem nash : IsNashEquilibrium A x y := by
  refine ⟨x_mem, y_mem, fun x' hx' => ?_, fun y' hy' => ?_⟩
  · rw [payoff_y x' hx'.2, payoff_y x x_mem.2]
  · rw [payoff_x y' hy'.2, payoff_x y y_mem.2]

theorem unique (x' y' : Fin 6 → ℝ) (h : IsNashEquilibrium A x' y') : x' = x ∧ y' = y := by
  obtain ⟨hx', hy', h1, h2⟩ := h
  have sx := hx'.2
  have sy := hy'.2
  -- the value of the equilibrium `(x', y')` is `-1/13`
  have hP : payoff A x' y' = -1 / 13 := by
    have a := h1 x x_mem
    have b := h2 y y_mem
    rw [payoff_x y' sy] at a
    rw [payoff_y x' sx] at b
    linarith
  rw [hP] at h1 h2
  -- pure-strategy deviations
  have r0 := h1 _ (single_mem_stdSimplex ℝ (0 : Fin 6))
  have r1 := h1 _ (single_mem_stdSimplex ℝ (1 : Fin 6))
  have r2 := h1 _ (single_mem_stdSimplex ℝ (2 : Fin 6))
  have r3 := h1 _ (single_mem_stdSimplex ℝ (3 : Fin 6))
  have r4 := h1 _ (single_mem_stdSimplex ℝ (4 : Fin 6))
  have r5 := h1 _ (single_mem_stdSimplex ℝ (5 : Fin 6))
  have c0 := h2 _ (single_mem_stdSimplex ℝ (0 : Fin 6))
  have c1 := h2 _ (single_mem_stdSimplex ℝ (1 : Fin 6))
  have c2 := h2 _ (single_mem_stdSimplex ℝ (2 : Fin 6))
  have c3 := h2 _ (single_mem_stdSimplex ℝ (3 : Fin 6))
  have c4 := h2 _ (single_mem_stdSimplex ℝ (4 : Fin 6))
  have c5 := h2 _ (single_mem_stdSimplex ℝ (5 : Fin 6))
  rw [Fin.sum_univ_six] at sx sy
  simp [payoff, Fin.sum_univ_six, A, Pi.single_apply] at r0 r1 r2 r3 r4 r5 c0 c1 c2 c3 c4 c5
  constructor
  · funext i
    fin_cases i <;> simp [x] <;> linarith
  · funext j
    fin_cases j <;> simp [y] <;> linarith

theorem target :
    ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), 1 < m ∧ 1 < n ∧
      (∀ i j, A i j = 1 ∨ A i j = -1) ∧
      IsTotallyAsymmetric A ∧
      ∃ (x : Fin m → ℝ) (y : Fin n → ℝ), IsNashEquilibrium A x y ∧
        (∀ i, 0 < x i) ∧ (∀ j, 0 < y j) ∧
        ∀ (x' : Fin m → ℝ) (y' : Fin n → ℝ), IsNashEquilibrium A x' y' → x' = x ∧ y' = y :=
  ⟨6, 6, A, by norm_num, by norm_num, entries, asym, x, y, nash,
    fun i => by fin_cases i <;> norm_num [x], fun j => by fin_cases j <;> norm_num [y], unique⟩

end OMA.ZS199784

theorem OMA.solution : type_of% @OMA.S_mse_199784.main := OMA.ZS199784.target
