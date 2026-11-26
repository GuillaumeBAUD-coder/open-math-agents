import FormalConjectures.HilbertProblems.«17»

-- Problem: Hilbert's 17th problem — f not sum of squares
-- Upstream: formal-conjectures FormalConjectures/HilbertProblems/17.lean:73 (declaration Hilbert17.f_not_sum_of_squares)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.H17

open MvPolynomial

/-- The exponent vector `x^a y^b`. -/
noncomputable def e (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] lemma e_zero (a b : ℕ) : e a b 0 = a := by simp [e]

@[simp] lemma e_one (a b : ℕ) : e a b 1 = b := by simp [e]

lemma ext2 {β γ : Fin 2 →₀ ℕ} (h0 : β 0 = γ 0) (h1 : β 1 = γ 1) : β = γ := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma eq_e (β : Fin 2 →₀ ℕ) : β = e (β 0) (β 1) := ext2 (by simp) (by simp)

lemma e_inj (a b c d : ℕ) : e a b = e c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) h
    have h1 := congrArg (fun x : Fin 2 →₀ ℕ => x 1) h
    simp only [e_zero, e_one] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma e_eq_zero (a b : ℕ) : (0 : Fin 2 →₀ ℕ) = e a b ↔ 0 = a ∧ 0 = b := by
  rw [show (0 : Fin 2 →₀ ℕ) = e 0 0 from ext2 (by simp) (by simp), e_inj]

lemma f_coeff (a b : ℕ) : coeff (e a b) Hilbert17.f
    = (if 4 = a ∧ 2 = b then (1 : ℝ) else 0) + (if 2 = a ∧ 4 = b then 1 else 0)
      - (if 2 = a ∧ 2 = b then 3 else 0) + (if 0 = a ∧ 0 = b then 1 else 0) := by
  have h1 : (X 0 ^ 4 * X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) = monomial (e 4 2) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]; rfl
  have h2 : (X 0 ^ 2 * X 1 ^ 4 : MvPolynomial (Fin 2) ℝ) = monomial (e 2 4) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]; rfl
  have h3 : (3 * X 0 ^ 2 * X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) = monomial (e 2 2) 3 := by
    rw [mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul,
      show (3 : MvPolynomial (Fin 2) ℝ) = C 3 from (map_ofNat C 3).symm, C_mul_monomial, mul_one]
    rfl
  unfold Hilbert17.f
  rw [h1, h2, h3, coeff_add, coeff_sub, coeff_add, coeff_monomial, coeff_monomial, coeff_monomial,
    coeff_one]
  simp only [e_inj, e_eq_zero]

/-- The linear weight `p * a + q * b` of an exponent vector. -/
def ell (p q : ℤ) (β : Fin 2 →₀ ℕ) : ℤ := p * (β 0 : ℤ) + q * (β 1 : ℤ)

lemma ell_add (p q : ℤ) (β γ : Fin 2 →₀ ℕ) : ell p q (β + γ) = ell p q β + ell p q γ := by
  simp only [ell, Finsupp.add_apply]
  push_cast
  ring

lemma vertex {n : ℕ} (S : Fin n → MvPolynomial (Fin 2) ℝ) (p q : ℤ) (hq : q ≠ 0)
    (μ : Fin 2 →₀ ℕ)
    (h1 : ∀ i, ∀ β ∈ (S i).support, ell p q β ≤ ell p q μ)
    (h2 : ∀ i, ∀ β ∈ (S i).support, ell p q β = ell p q μ → β 0 ≤ μ 0) :
    coeff (μ + μ) (∑ i, S i ^ 2) = ∑ i, (coeff μ (S i)) ^ 2 := by
  rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_two, coeff_mul, pow_two]
  apply Finset.sum_eq_single (μ, μ)
  · rintro ⟨β, γ⟩ hbg hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hbg
    by_contra hprod
    have hβ : β ∈ (S i).support := by
      rw [mem_support_iff]; intro h; exact hprod (by simp [h])
    have hγ : γ ∈ (S i).support := by
      rw [mem_support_iff]; intro h; exact hprod (by simp [h])
    have he := congrArg (ell p q) hbg
    rw [ell_add, ell_add] at he
    have b1 := h1 i β hβ
    have g1 := h1 i γ hγ
    have eβ : ell p q β = ell p q μ := by linarith
    have eγ : ell p q γ = ell p q μ := by linarith
    have b2 := h2 i β hβ eβ
    have g2 := h2 i γ hγ eγ
    have e0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) hbg
    simp only [Finsupp.add_apply] at e0
    have β0 : β 0 = μ 0 := by omega
    have γ0 : γ 0 = μ 0 := by omega
    have β1 : β 1 = μ 1 := by
      simp only [ell] at eβ
      rw [β0] at eβ
      have h3 : q * ((β 1 : ℤ) - μ 1) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hq
      · exact_mod_cast (by linarith : (β 1 : ℤ) = μ 1)
    have γ1 : γ 1 = μ 1 := by
      simp only [ell] at eγ
      rw [γ0] at eγ
      have h3 : q * ((γ 1 : ℤ) - μ 1) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hq
      · exact_mod_cast (by linarith : (γ 1 : ℤ) = μ 1)
    exact hne (by rw [ext2 β0 β1, ext2 γ0 γ1])
  · intro h
    refine absurd ?_ h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]

/-- The exponents `μ` with `2 μ` in the support of the Motzkin polynomial. -/
lemma half_support {μ : Fin 2 →₀ ℕ} (h : coeff (μ + μ) Hilbert17.f ≠ 0) :
    (μ 0 = 2 ∧ μ 1 = 1) ∨ (μ 0 = 1 ∧ μ 1 = 2) ∨ (μ 0 = 1 ∧ μ 1 = 1) ∨ (μ 0 = 0 ∧ μ 1 = 0) := by
  rw [eq_e (μ + μ), f_coeff] at h
  by_contra hc
  apply h
  have a0 : (μ + μ) 0 = μ 0 + μ 0 := Finsupp.add_apply _ _ _
  have a1 : (μ + μ) 1 = μ 1 + μ 1 := Finsupp.add_apply _ _ _
  rw [if_neg (by rw [a0, a1]; omega), if_neg (by rw [a0, a1]; omega),
    if_neg (by rw [a0, a1]; omega), if_neg (by rw [a0, a1]; omega)]
  norm_num

lemma top {n : ℕ} (S : Fin n → MvPolynomial (Fin 2) ℝ) (hS : Hilbert17.f = ∑ i, S i ^ 2)
    (p q : ℤ) (hq : q ≠ 0) :
    ∃ a b : ℕ, ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 0)) ∧
      ∀ i, ∀ β ∈ (S i).support, ell p q β ≤ p * a + q * b := by
  classical
  by_cases hU : ∃ i, ((S i).support).Nonempty
  · have hUne : (Finset.univ.biUnion fun i => (S i).support).Nonempty := by
      obtain ⟨i, β, hβ⟩ := hU
      exact ⟨β, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hβ⟩⟩
    obtain ⟨μ0, hμ0, hmax0⟩ := Finset.exists_max_image _ (ell p q) hUne
    have hU'ne : ((Finset.univ.biUnion fun i => (S i).support).filter
        fun β => ell p q β = ell p q μ0).Nonempty :=
      ⟨μ0, Finset.mem_filter.mpr ⟨hμ0, rfl⟩⟩
    obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image _ (fun β : Fin 2 →₀ ℕ => β 0) hU'ne
    rw [Finset.mem_filter] at hμ
    have h1 : ∀ i, ∀ β ∈ (S i).support, ell p q β ≤ ell p q μ := by
      intro i β hβ
      rw [hμ.2]
      exact hmax0 β (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hβ⟩)
    have h2 : ∀ i, ∀ β ∈ (S i).support, ell p q β = ell p q μ → β 0 ≤ μ 0 := by
      intro i β hβ he
      exact hmax β (Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hβ⟩, he.trans hμ.2⟩)
    have hv := vertex S p q hq μ h1 h2
    rw [← hS] at hv
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hμ.1
    have hpos : 0 < ∑ i, (coeff μ (S i)) ^ 2 := by
      apply Finset.sum_pos'
      · intro i _
        positivity
      · have hj' := mem_support_iff.mp hj
        exact ⟨j, Finset.mem_univ _, by positivity⟩
    have hne : coeff (μ + μ) Hilbert17.f ≠ 0 := by
      rw [hv]
      exact hpos.ne'
    refine ⟨μ 0, μ 1, half_support hne, ?_⟩
    intro i β hβ
    exact h1 i β hβ
  · refine ⟨0, 0, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
    intro i β hβ
    exact absurd ⟨i, β, hβ⟩ hU

end OMA.H17

open MvPolynomial OMA.H17 in
theorem OMA.solution : type_of% @Hilbert17.f_not_sum_of_squares := by
  rintro ⟨n, -, S, hS⟩
  have key : ∀ i, ∀ β ∈ (S i).support,
      β 0 + β 1 ≤ 3 ∧ β 0 ≤ 2 * β 1 ∧ β 1 ≤ 2 * β 0 := by
    intro i β hβ
    obtain ⟨a1, b1, hab1, h1⟩ := top S hS 1 1 (by norm_num)
    obtain ⟨a2, b2, hab2, h2⟩ := top S hS 1 (-2) (by norm_num)
    obtain ⟨a3, b3, hab3, h3⟩ := top S hS (-2) 1 (by norm_num)
    have k1 := h1 i β hβ
    have k2 := h2 i β hβ
    have k3 := h3 i β hβ
    simp only [ell] at k1 k2 k3
    omega
  have hc : coeff (e 1 1 + e 1 1) (∑ i, S i ^ 2) = ∑ i, (coeff (e 1 1) (S i)) ^ 2 := by
    rw [coeff_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_two, coeff_mul, pow_two]
    apply Finset.sum_eq_single (e 1 1, e 1 1)
    · rintro ⟨β, γ⟩ hbg hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hbg
      by_contra hprod
      have hβ : β ∈ (S i).support := by
        rw [mem_support_iff]; intro h; exact hprod (by simp [h])
      have hγ : γ ∈ (S i).support := by
        rw [mem_support_iff]; intro h; exact hprod (by simp [h])
      have kβ := key i β hβ
      have kγ := key i γ hγ
      have e0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) hbg
      have e1 := congrArg (fun x : Fin 2 →₀ ℕ => x 1) hbg
      simp only [Finsupp.add_apply, e_zero, e_one] at e0 e1
      have hβe : β = e 1 1 := ext2 (by rw [e_zero]; omega) (by rw [e_one]; omega)
      have hγe : γ = e 1 1 := ext2 (by rw [e_zero]; omega) (by rw [e_one]; omega)
      exact hne (by rw [hβe, hγe])
    · intro h
      refine absurd ?_ h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
  rw [← hS, eq_e (e 1 1 + e 1 1), f_coeff] at hc
  simp only [Finsupp.add_apply, e_zero, e_one] at hc
  norm_num at hc
  have hnn : 0 ≤ ∑ i, (coeff (e 1 1) (S i)) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  linarith
