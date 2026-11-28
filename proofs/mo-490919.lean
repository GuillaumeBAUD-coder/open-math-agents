import OMAStatements.S_mo_490919

open OMA.S_mo_490919

lemma OMA.aux490919_entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (M : ℝ) (hM : ∀ i, p i ≤ M) :
    -Real.log M ≤ entropy p := by
  unfold entropy
  have key : ∀ i, p i * (-Real.log M) ≤ Real.negMulLog (p i) := by
    intro i
    rw [Real.negMulLog]
    rcases (hp i).lt_or_eq with h | h
    · have := Real.log_le_log h (hM i)
      nlinarith
    · rw [← h]; simp
  calc -Real.log M = ∑ i, p i * (-Real.log M) := by rw [← Finset.sum_mul, hs, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => key i)

theorem OMA.solution : type_of% @OMA.S_mo_490919.main := by
  intro G _ _ μ hμ hsum
  classical
  set S : ℝ := ∑ χ : AddChar G ℂ, ‖fourierHat μ χ‖ with hS
  -- each Fourier coefficient has norm at most 1
  have hle1 : ∀ ψ : AddChar G ℂ, ‖fourierHat μ ψ‖ ≤ 1 := by
    intro ψ
    unfold fourierHat
    calc ‖∑ x, (μ x : ℂ) * ψ x‖ ≤ ∑ x, ‖(μ x : ℂ) * ψ x‖ := norm_sum_le _ _
      _ = ∑ x, μ x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [norm_mul, AddChar.norm_apply, mul_one, Complex.norm_real, Real.norm_of_nonneg (hμ x)]
      _ = 1 := hsum
  have hS1 : 1 ≤ S := by
    have h0 : ‖fourierHat μ 0‖ = 1 := by
      unfold fourierHat
      simp only [AddChar.zero_apply, mul_one]
      rw [← Complex.ofReal_sum, hsum]; simp
    rw [← h0]
    exact Finset.single_le_sum (f := fun χ : AddChar G ℂ => ‖fourierHat μ χ‖)
      (fun χ _ => norm_nonneg _) (Finset.mem_univ _)
  have hSpos : 0 < S := lt_of_lt_of_le one_pos hS1
  -- maximum of μ
  obtain ⟨x0, hx0⟩ := Finite.exists_max μ
  have hx0pos : 0 < μ x0 := by
    by_contra h
    push Not at h
    have : ∑ x, μ x ≤ ∑ _x : G, (0:ℝ) := Finset.sum_le_sum (fun x _ => (hx0 x).trans h)
    simp at this; linarith
  -- Fourier inversion bound
  have hinv : (Fintype.card G : ℝ) * μ x0 ≤ S := by
    have hid : ∑ ψ : AddChar G ℂ, fourierHat μ ψ * ψ (-x0) = (Fintype.card G : ℂ) * μ x0 := by
      unfold fourierHat
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ x : G, ∑ ψ : AddChar G ℂ, (μ x : ℂ) * ψ x * ψ (-x0)
          = (μ x : ℂ) * (if x - x0 = 0 then (Fintype.card G : ℂ) else 0) := by
        intro x
        rw [← AddChar.sum_apply_eq_ite, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ψ _ => ?_)
        rw [sub_eq_add_neg, AddChar.map_add_eq_mul, mul_assoc]
      simp_rw [this, sub_eq_zero, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ x0]
      simp [mul_comm]
    have := norm_sum_le (Finset.univ : Finset (AddChar G ℂ)) (fun ψ => fourierHat μ ψ * ψ (-x0))
    rw [hid] at this
    simp only [norm_mul, AddChar.norm_apply, mul_one] at this
    rw [← hS] at this
    rw [Complex.norm_real, Real.norm_of_nonneg hx0pos.le, Complex.norm_natCast] at this
    exact this
  -- entropy bounds
  have h1 : -Real.log (μ x0) ≤ entropy μ := OMA.aux490919_entropy μ hμ hsum _ hx0
  have h2 : -Real.log (1 / S) ≤ entropy (fun ψ : AddChar G ℂ => ‖fourierHat μ ψ‖ / S) := by
    apply OMA.aux490919_entropy
    · intro ψ; exact div_nonneg (norm_nonneg _) hSpos.le
    · rw [← Finset.sum_div, ← hS, div_self hSpos.ne']
    · intro ψ; exact div_le_div_of_nonneg_right (hle1 ψ) hSpos.le
  have hn : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h3 : Real.log (Fintype.card G) ≤ Real.log S - Real.log (μ x0) := by
    rw [← Real.log_div hSpos.ne' hx0pos.ne']
    apply Real.log_le_log hn
    rw [le_div_iff₀ hx0pos]; exact hinv
  have h4 : -Real.log (1 / S) = Real.log S := by
    rw [one_div, Real.log_inv, neg_neg]
  linarith
