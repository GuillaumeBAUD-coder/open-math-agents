import FormalConjectures.HilbertProblems.«17»

/-!
# The Motzkin Polynomial Is Not a Sum of Squares

We prove `Hilbert17.f_not_sum_of_squares`: the Motzkin polynomial
`f(x, y) = x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1` cannot be expressed as a sum of squares of real
polynomials. Using extremal monomials under three additive lexicographic orders, every summand's
support is bounded by `deg_x ≤ 2`, `deg_y ≤ 2`, `deg_x + deg_y ≤ 3`. Vanishing of the `(4, 0)`,
`(0, 4)`, `(2, 0)`, and `(0, 2)` coefficients of `f` successively eliminates `(2, 0)`, `(0, 2)`,
`(1, 0)`, and `(0, 1)` from all summands, leaving `(1, 1) + (1, 1)` as the sole contribution to
the `(2, 2)` coefficient `-3 ≥ 0`, a contradiction.
-/

-- Problem: Hilbert's 17th problem — f not sum of squares
-- Upstream: formal-conjectures FormalConjectures/HilbertProblems/17.lean:73 (declaration Hilbert17.f_not_sum_of_squares)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Hilbert17MotzkinProof

open MvPolynomial

private noncomputable def mono (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

private lemma mono_apply_zero (a b : ℕ) : mono a b 0 = a := by
  simp [mono]

private lemma mono_apply_one (a b : ℕ) : mono a b 1 = b := by
  simp [mono]

private lemma eq_mono_iff (d : Fin 2 →₀ ℕ) (a b : ℕ) :
    d = mono a b ↔ d 0 = a ∧ d 1 = b := by
  constructor
  · rintro rfl
    exact ⟨mono_apply_zero a b, mono_apply_one a b⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · simpa [mono] using h0
    · simpa [mono] using h1

private lemma mono_add (a₁ b₁ a₂ b₂ : ℕ) :
    mono a₁ b₁ + mono a₂ b₂ = mono (a₁ + a₂) (b₁ + b₂) := by
  rw [eq_mono_iff]
  simp [mono]

private lemma f_eq_monomials :
    Hilbert17.f =
      monomial (mono 4 2) (1 : ℝ) +
      monomial (mono 2 4) 1 -
      monomial (mono 2 2) 3 +
      monomial (mono 0 0) 1 := by
  unfold Hilbert17.f
  have h1 : (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ^ 4 * X 1 ^ 2 =
      monomial (mono 4 2) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]
    rfl
  have h2 : (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ^ 2 * X 1 ^ 4 =
      monomial (mono 2 4) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]
    rfl
  have h3 : (3 : MvPolynomial (Fin 2) ℝ) * X 0 ^ 2 * X 1 ^ 2 =
      monomial (mono 2 2) 3 := by
    rw [mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]
    have hC : (3 : MvPolynomial (Fin 2) ℝ) = C 3 := (map_ofNat C 3).symm
    rw [hC, C_mul_monomial, mul_one]
    rfl
  have h4 : (1 : MvPolynomial (Fin 2) ℝ) = monomial (mono 0 0) 1 := by
    simp [mono, monomial_zero']
  rw [h1, h2, h3, h4]

private lemma coeff_f (d : Fin 2 →₀ ℕ) :
    coeff d Hilbert17.f =
      (if mono 4 2 = d then (1 : ℝ) else 0) +
      (if mono 2 4 = d then 1 else 0) -
      (if mono 2 2 = d then 3 else 0) +
      (if mono 0 0 = d then 1 else 0) := by
  rw [f_eq_monomials, coeff_add, coeff_sub, coeff_add,
    coeff_monomial, coeff_monomial, coeff_monomial, coeff_monomial]

private lemma coeff_f_eval (a b : ℕ) :
    coeff (mono a b) Hilbert17.f =
      (if a = 4 ∧ b = 2 then (1 : ℝ) else 0) +
      (if a = 2 ∧ b = 4 then 1 else 0) -
      (if a = 2 ∧ b = 2 then 3 else 0) +
      (if a = 0 ∧ b = 0 then 1 else 0) := by
  rw [coeff_f]
  have hiff : ∀ p q : ℕ, (mono p q = mono a b) ↔ (a = p ∧ b = q) := by
    intro p q
    rw [eq_comm, eq_mono_iff, mono_apply_zero, mono_apply_one]
  simp only [hiff]

private lemma pos_coeff_f_imp {d : Fin 2 →₀ ℕ} (h : 0 < coeff d Hilbert17.f) :
    (d 0 = 4 ∧ d 1 = 2) ∨ (d 0 = 2 ∧ d 1 = 4) ∨ (d 0 = 0 ∧ d 1 = 0) := by
  have hd : d = mono (d 0) (d 1) := (eq_mono_iff d (d 0) (d 1)).mpr ⟨rfl, rfl⟩
  rw [hd, coeff_f_eval] at h
  by_cases h42 : d 0 = 4 ∧ d 1 = 2
  · exact Or.inl h42
  by_cases h24 : d 0 = 2 ∧ d 1 = 4
  · exact Or.inr (Or.inl h24)
  by_cases h00 : d 0 = 0 ∧ d 1 = 0
  · exact Or.inr (Or.inr h00)
  exfalso
  by_cases h22 : d 0 = 2 ∧ d 1 = 2
  · simp [h22] at h
    linarith
  · simp [h42, h24, h22, h00] at h

private lemma sum_sq_coeff_eq {n : ℕ} (S : Fin n → MvPolynomial (Fin 2) ℝ)
    (m t : Fin 2 →₀ ℕ) (hm : m + m = t)
    (huniq : ∀ i (a b : Fin 2 →₀ ℕ), a + b = t →
      coeff a (S i) ≠ 0 → coeff b (S i) ≠ 0 → a = m ∧ b = m) :
    coeff t (∑ i, S i ^ 2) = ∑ i, coeff m (S i) ^ 2 := by
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq, coeff_mul, Finset.sum_eq_single (m, m)]
  · rw [sq]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    by_contra hnz
    have ha : coeff a (S i) ≠ 0 := left_ne_zero_of_mul hnz
    have hb : coeff b (S i) ≠ 0 := right_ne_zero_of_mul hnz
    obtain ⟨rfl, rfl⟩ := huniq i a b hab ha hb
    exact hne rfl
  · intro hnot
    exfalso
    exact hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr hm)

private lemma eq_zero_of_sum_sq_eq_zero {n : ℕ} {c : Fin n → ℝ}
    (h : ∑ i, c i ^ 2 = 0) (i : Fin n) : c i = 0 := by
  have hi : c i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp h i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

private lemma max_lex_bound {n : ℕ} (S : Fin n → MvPolynomial (Fin 2) ℝ)
    (hS : Hilbert17.f = ∑ i, S i ^ 2)
    (φ₁ φ₂ : (Fin 2 →₀ ℕ) → ℕ)
    (hφ₁ : ∀ a b, φ₁ (a + b) = φ₁ a + φ₁ b)
    (hφ₂ : ∀ a b, φ₂ (a + b) = φ₂ a + φ₂ b)
    (hinj : ∀ a b, φ₁ a = φ₁ b → φ₂ a = φ₂ b → a = b)
    {i₀ : Fin n} {d₀ : Fin 2 →₀ ℕ} (hd₀ : coeff d₀ (S i₀) ≠ 0) :
    ∃ m : Fin 2 →₀ ℕ,
      φ₁ d₀ ≤ φ₁ m ∧
      ((m 0 = 2 ∧ m 1 = 1) ∨ (m 0 = 1 ∧ m 1 = 2) ∨ (m 0 = 0 ∧ m 1 = 0)) := by
  let T : Finset (Fin 2 →₀ ℕ) := Finset.univ.biUnion (fun i => (S i).support)
  have hd₀T : d₀ ∈ T :=
    Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ i₀, mem_support_iff.mpr hd₀⟩
  let k : (Fin 2 →₀ ℕ) → ℕ ×ₗ ℕ := fun d => toLex (φ₁ d, φ₂ d)
  obtain ⟨m, hmT, hm_max⟩ := Finset.exists_max_image T k ⟨d₀, hd₀T⟩
  have hle_φ₁ : ∀ d ∈ T, φ₁ d ≤ φ₁ m := by
    intro d hd
    have hkd := hm_max d hd
    rw [Prod.Lex.le_iff] at hkd
    rcases hkd with hlt | ⟨heq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq heq
  have huniq : ∀ i (a b : Fin 2 →₀ ℕ), a + b = m + m →
      coeff a (S i) ≠ 0 → coeff b (S i) ≠ 0 → a = m ∧ b = m := by
    intro i a b hab ha hb
    have haT : a ∈ T := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, mem_support_iff.mpr ha⟩
    have hbT : b ∈ T := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, mem_support_iff.mpr hb⟩
    have hka := hm_max a haT
    have hkb := hm_max b hbT
    rw [Prod.Lex.le_iff] at hka hkb
    dsimp only [k, ofLex_toLex] at hka hkb
    have h1 : φ₁ a + φ₁ b = φ₁ m + φ₁ m := by
      rw [← hφ₁, ← hφ₁, hab]
    have h2 : φ₂ a + φ₂ b = φ₂ m + φ₂ m := by
      rw [← hφ₂, ← hφ₂, hab]
    have ha1 : φ₁ a = φ₁ m := by omega
    have hb1 : φ₁ b = φ₁ m := by omega
    have ha2 : φ₂ a = φ₂ m := by omega
    have hb2 : φ₂ b = φ₂ m := by omega
    exact ⟨hinj a m ha1 ha2, hinj b m hb1 hb2⟩
  have hcoeff : coeff (m + m) Hilbert17.f = ∑ i, coeff m (S i) ^ 2 := by
    rw [hS]
    exact sum_sq_coeff_eq S m (m + m) rfl huniq
  obtain ⟨i₁, _, hm1⟩ := Finset.mem_biUnion.mp hmT
  have hm1_ne : coeff m (S i₁) ≠ 0 := mem_support_iff.mp hm1
  have hpos : 0 < coeff (m + m) Hilbert17.f := by
    rw [hcoeff]
    exact Finset.sum_pos' (fun i _ => sq_nonneg (coeff m (S i)))
      ⟨i₁, Finset.mem_univ i₁, sq_pos_of_ne_zero hm1_ne⟩
  have hcases := pos_coeff_f_imp hpos
  have hadd0 : (m + m) 0 = m 0 + m 0 := rfl
  have hadd1 : (m + m) 1 = m 1 + m 1 := rfl
  rw [hadd0, hadd1] at hcases
  refine ⟨m, hle_φ₁ d₀ hd₀T, ?_⟩
  omega

end Hilbert17MotzkinProof

theorem OMA.solution : type_of% @Hilbert17.f_not_sum_of_squares := by
  rintro ⟨n, _, S, hS⟩
  have hdeg0 : ∀ i (d : Fin 2 →₀ ℕ), MvPolynomial.coeff d (S i) ≠ 0 → d 0 ≤ 2 := by
    intro i d hd
    obtain ⟨m, hle, hm⟩ := Hilbert17MotzkinProof.max_lex_bound S hS
      (fun x => x 0) (fun x => x 1)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun a b h0 h1 => by ext j; fin_cases j <;> assumption) hd
    omega
  have hdeg1 : ∀ i (d : Fin 2 →₀ ℕ), MvPolynomial.coeff d (S i) ≠ 0 → d 1 ≤ 2 := by
    intro i d hd
    obtain ⟨m, hle, hm⟩ := Hilbert17MotzkinProof.max_lex_bound S hS
      (fun x => x 1) (fun x => x 0)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun a b h1 h0 => by ext j; fin_cases j <;> assumption) hd
    omega
  have htot : ∀ i (d : Fin 2 →₀ ℕ), MvPolynomial.coeff d (S i) ≠ 0 → d 0 + d 1 ≤ 3 := by
    intro i d hd
    obtain ⟨m, hle, hm⟩ := Hilbert17MotzkinProof.max_lex_bound S hS
      (fun x => x 0 + x 1) (fun x => x 0)
      (fun a b => by show (a 0 + b 0) + (a 1 + b 1) = (a 0 + a 1) + (b 0 + b 1); omega)
      (fun _ _ => rfl)
      (fun a b hs h0 => by ext j; fin_cases j <;> dsimp <;> omega) hd
    omega
  have h20 : ∀ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 2 0) (S i) = 0 := by
    have hsum : ∑ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 2 0) (S i) ^ 2 = 0 := by
      have h1 : MvPolynomial.coeff (Hilbert17MotzkinProof.mono 4 0) Hilbert17.f = 0 := by
        rw [Hilbert17MotzkinProof.coeff_f_eval]; norm_num
      rw [← h1, hS]
      symm
      refine Hilbert17MotzkinProof.sum_sq_coeff_eq S
        (Hilbert17MotzkinProof.mono 2 0) (Hilbert17MotzkinProof.mono 4 0)
        (Hilbert17MotzkinProof.mono_add 2 0 2 0) ?_
      intro i a b hab ha hb
      have ha0 := hdeg0 i a ha
      have hb0 := hdeg0 i b hb
      have h0 : a 0 + b 0 = 4 := by
        have := congrArg (fun x : Fin 2 →₀ ℕ => x 0) hab
        simpa [Hilbert17MotzkinProof.mono_apply_zero] using this
      have h1' : a 1 + b 1 = 0 := by
        have := congrArg (fun x : Fin 2 →₀ ℕ => x 1) hab
        simpa [Hilbert17MotzkinProof.mono_apply_one] using this
      rw [Hilbert17MotzkinProof.eq_mono_iff, Hilbert17MotzkinProof.eq_mono_iff]
      omega
    exact Hilbert17MotzkinProof.eq_zero_of_sum_sq_eq_zero hsum
  have h02 : ∀ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 0 2) (S i) = 0 := by
    have hsum : ∑ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 0 2) (S i) ^ 2 = 0 := by
      have h1 : MvPolynomial.coeff (Hilbert17MotzkinProof.mono 0 4) Hilbert17.f = 0 := by
        rw [Hilbert17MotzkinProof.coeff_f_eval]; norm_num
      rw [← h1, hS]
      symm
      refine Hilbert17MotzkinProof.sum_sq_coeff_eq S
        (Hilbert17MotzkinProof.mono 0 2) (Hilbert17MotzkinProof.mono 0 4)
        (Hilbert17MotzkinProof.mono_add 0 2 0 2) ?_
      intro i a b hab ha hb
      have ha1 := hdeg1 i a ha
      have hb1 := hdeg1 i b hb
      have h0 : a 0 + b 0 = 0 := by
        have := congrArg (fun x : Fin 2 →₀ ℕ => x 0) hab
        simpa [Hilbert17MotzkinProof.mono_apply_zero] using this
      have h1' : a 1 + b 1 = 4 := by
        have := congrArg (fun x : Fin 2 →₀ ℕ => x 1) hab
        simpa [Hilbert17MotzkinProof.mono_apply_one] using this
      rw [Hilbert17MotzkinProof.eq_mono_iff, Hilbert17MotzkinProof.eq_mono_iff]
      omega
    exact Hilbert17MotzkinProof.eq_zero_of_sum_sq_eq_zero hsum
  have h10 : ∀ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 1 0) (S i) = 0 := by
    have hsum : ∑ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 1 0) (S i) ^ 2 = 0 := by
      have h1 : MvPolynomial.coeff (Hilbert17MotzkinProof.mono 2 0) Hilbert17.f = 0 := by
        rw [Hilbert17MotzkinProof.coeff_f_eval]; norm_num
      rw [← h1, hS]
      symm
      refine Hilbert17MotzkinProof.sum_sq_coeff_eq S
        (Hilbert17MotzkinProof.mono 1 0) (Hilbert17MotzkinProof.mono 2 0)
        (Hilbert17MotzkinProof.mono_add 1 0 1 0) ?_
      intro i a b hab ha hb
      have h0 : a 0 + b 0 = 2 := by
        have := congrArg (fun x : Fin 2 →₀ ℕ => x 0) hab
        simpa [Hilbert17MotzkinProof.mono_apply_zero] using this
      have h1' : a 1 + b 1 = 0 := by
        have := congrArg (fun x : Fin 2 →₀ ℕ => x 1) hab
        simpa [Hilbert17MotzkinProof.mono_apply_one] using this
      have ha_ne : ¬ (a 0 = 2 ∧ a 1 = 0) := by
        intro h
        exact ha ((Hilbert17MotzkinProof.eq_mono_iff a 2 0).mpr h ▸ h20 i)
      have hb_ne : ¬ (b 0 = 2 ∧ b 1 = 0) := by
        intro h
        exact hb ((Hilbert17MotzkinProof.eq_mono_iff b 2 0).mpr h ▸ h20 i)
      rw [Hilbert17MotzkinProof.eq_mono_iff, Hilbert17MotzkinProof.eq_mono_iff]
      omega
    exact Hilbert17MotzkinProof.eq_zero_of_sum_sq_eq_zero hsum
  have h01 : ∀ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 0 1) (S i) = 0 := by
    have hsum : ∑ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 0 1) (S i) ^ 2 = 0 := by
      have h1 : MvPolynomial.coeff (Hilbert17MotzkinProof.mono 0 2) Hilbert17.f = 0 := by
        rw [Hilbert17MotzkinProof.coeff_f_eval]; norm_num
      rw [← h1, hS]
      symm
      refine Hilbert17MotzkinProof.sum_sq_coeff_eq S
        (Hilbert17MotzkinProof.mono 0 1) (Hilbert17MotzkinProof.mono 0 2)
        (Hilbert17MotzkinProof.mono_add 0 1 0 1) ?_
      intro i a b hab ha hb
      have h0 : a 0 + b 0 = 0 := by
        have := congrArg (fun x : Fin 2 →₀ ℕ => x 0) hab
        simpa [Hilbert17MotzkinProof.mono_apply_zero] using this
      have h1' : a 1 + b 1 = 2 := by
        have := congrArg (fun x : Fin 2 →₀ ℕ => x 1) hab
        simpa [Hilbert17MotzkinProof.mono_apply_one] using this
      have ha_ne : ¬ (a 0 = 0 ∧ a 1 = 2) := by
        intro h
        exact ha ((Hilbert17MotzkinProof.eq_mono_iff a 0 2).mpr h ▸ h02 i)
      have hb_ne : ¬ (b 0 = 0 ∧ b 1 = 2) := by
        intro h
        exact hb ((Hilbert17MotzkinProof.eq_mono_iff b 0 2).mpr h ▸ h02 i)
      rw [Hilbert17MotzkinProof.eq_mono_iff, Hilbert17MotzkinProof.eq_mono_iff]
      omega
    exact Hilbert17MotzkinProof.eq_zero_of_sum_sq_eq_zero hsum
  have h22_lhs : MvPolynomial.coeff (Hilbert17MotzkinProof.mono 2 2) Hilbert17.f = -3 := by
    rw [Hilbert17MotzkinProof.coeff_f_eval]
    norm_num
  have h22_rhs : MvPolynomial.coeff (Hilbert17MotzkinProof.mono 2 2) Hilbert17.f =
      ∑ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 1 1) (S i) ^ 2 := by
    rw [hS]
    refine Hilbert17MotzkinProof.sum_sq_coeff_eq S
      (Hilbert17MotzkinProof.mono 1 1) (Hilbert17MotzkinProof.mono 2 2)
      (Hilbert17MotzkinProof.mono_add 1 1 1 1) ?_
    intro i a b hab ha hb
    have ha_tot := htot i a ha
    have hb_tot := htot i b hb
    have h0 : a 0 + b 0 = 2 := by
      have := congrArg (fun x : Fin 2 →₀ ℕ => x 0) hab
      simpa [Hilbert17MotzkinProof.mono_apply_zero] using this
    have h1' : a 1 + b 1 = 2 := by
      have := congrArg (fun x : Fin 2 →₀ ℕ => x 1) hab
      simpa [Hilbert17MotzkinProof.mono_apply_one] using this
    have ha20 : ¬ (a 0 = 2 ∧ a 1 = 0) := fun h =>
      ha ((Hilbert17MotzkinProof.eq_mono_iff a 2 0).mpr h ▸ h20 i)
    have ha02 : ¬ (a 0 = 0 ∧ a 1 = 2) := fun h =>
      ha ((Hilbert17MotzkinProof.eq_mono_iff a 0 2).mpr h ▸ h02 i)
    have ha10 : ¬ (a 0 = 1 ∧ a 1 = 0) := fun h =>
      ha ((Hilbert17MotzkinProof.eq_mono_iff a 1 0).mpr h ▸ h10 i)
    have ha01 : ¬ (a 0 = 0 ∧ a 1 = 1) := fun h =>
      ha ((Hilbert17MotzkinProof.eq_mono_iff a 0 1).mpr h ▸ h01 i)
    have hb20 : ¬ (b 0 = 2 ∧ b 1 = 0) := fun h =>
      hb ((Hilbert17MotzkinProof.eq_mono_iff b 2 0).mpr h ▸ h20 i)
    have hb02 : ¬ (b 0 = 0 ∧ b 1 = 2) := fun h =>
      hb ((Hilbert17MotzkinProof.eq_mono_iff b 0 2).mpr h ▸ h02 i)
    have hb10 : ¬ (b 0 = 1 ∧ b 1 = 0) := fun h =>
      hb ((Hilbert17MotzkinProof.eq_mono_iff b 1 0).mpr h ▸ h10 i)
    have hb01 : ¬ (b 0 = 0 ∧ b 1 = 1) := fun h =>
      hb ((Hilbert17MotzkinProof.eq_mono_iff b 0 1).mpr h ▸ h01 i)
    rw [Hilbert17MotzkinProof.eq_mono_iff, Hilbert17MotzkinProof.eq_mono_iff]
    omega
  have hnonneg : 0 ≤ ∑ i, MvPolynomial.coeff (Hilbert17MotzkinProof.mono 1 1) (S i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith
