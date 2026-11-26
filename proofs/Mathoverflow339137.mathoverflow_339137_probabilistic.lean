import FormalConjectures.Mathoverflow.«339137»

-- Problem: Mathoverflow 339137 — mathoverflow 339137 probabilistic
-- Upstream: formal-conjectures FormalConjectures/Mathoverflow/339137.lean:70 (declaration Mathoverflow339137.mathoverflow_339137_probabilistic)
-- Credit: @koolkao (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped Polynomial ENNReal

namespace OMA.MO339137

open Polynomial Mathoverflow339137 Green28

theorem unif_apply {s : Finset ℤ} (hs : s.Nonempty) (a : ℤ) :
    PMF.uniformOfFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  convert PMF.uniformOfFinset_apply hs a

theorem isZeroOne_iff (P : ℝ[X]) : IsZeroOne P ↔ ∀ n, P.coeff n ≠ 0 → P.coeff n = 1 := by
  constructor
  · intro h n hn
    have : P.coeff n ∈ P.coeffs := Polynomial.coeff_mem_coeffs hn
    simpa using h this
  · intro h c hc
    obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    simpa using h n (Polynomial.mem_support_iff.mp hn)

theorem nonneg_iff (P : ℝ[X]) : (∀ c ∈ P.coeffs, 0 ≤ c) ↔ ∀ n, 0 ≤ P.coeff n := by
  constructor
  · intro h n
    by_cases hn : P.coeff n = 0
    · simp [hn]
    · exact h _ (Polynomial.coeff_mem_coeffs hn)
  · intro h c hc
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    exact h n

theorem uniform_eq {U : PMF ℤ} (h : IsUniformOnSupport U) {z w : ℤ} (hz : U z ≠ 0)
    (hw : U w ≠ 0) : U z = U w := by
  classical
  obtain ⟨s, hs, rfl⟩ := h
  rw [unif_apply] at hz hw ⊢
  rw [unif_apply]
  split_ifs at hz hw ⊢ <;> simp_all

theorem uniform_of_const {U : PMF ℤ} (hfin : U.support.Finite) (κ : ℝ≥0∞)
    (h : ∀ z, U z ≠ 0 → U z = κ) : IsUniformOnSupport U := by
  classical
  set S := hfin.toFinset with hS
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := U.support_nonempty
    exact ⟨x, by simpa [hS] using hx⟩
  have hmem : ∀ z, z ∈ S ↔ U z ≠ 0 := fun z => by simp [hS]
  have hsum : (S.card : ℝ≥0∞) * κ = 1 := by
    rw [← U.tsum_coe, tsum_eq_sum (s := S) (fun z hz => by
      by_contra h'; exact hz ((hmem z).2 h'))]
    rw [Finset.sum_congr rfl (fun z hz => h z ((hmem z).1 hz))]
    simp
  have hκ : κ = (S.card : ℝ≥0∞)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)
  refine ⟨S, hSne, PMF.ext fun z => ?_⟩
  rw [unif_apply]
  split_ifs with hz
  · rw [h z ((hmem z).1 hz), hκ]
  · by_contra h'; exact hz ((hmem z).2 h')

theorem indepSum_apply (X Y : PMF ℤ) (z : ℤ) :
    indepSum X Y z = ∑' x, X x * Y (z - x) := by
  simp only [indepSum]
  show (X.bind fun x => Y.bind fun y => PMF.pure (x + y)) z = _
  rw [PMF.bind_apply]
  refine tsum_congr fun x => ?_
  rw [PMF.bind_apply, tsum_eq_single (z - x)]
  · simp
  · intro y hy
    rw [PMF.pure_apply, if_neg (by omega), mul_zero]

theorem indepSum_nat (X Y : PMF ℤ) (a b : ℤ) (hX : ∀ x < a, X x = 0) (hY : ∀ y < b, Y y = 0)
    (n : ℕ) : indepSum X Y (a + b + n) =
      ∑ i ∈ Finset.range (n + 1), X (a + i) * Y (b + ((n - i : ℕ) : ℤ)) := by
  rw [indepSum_apply]
  rw [tsum_eq_sum (s := (Finset.range (n + 1)).image (fun i : ℕ => a + (i : ℤ)))]
  · rw [Finset.sum_image (fun i _ j _ h => by simpa using h)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    congr 2
    push_cast [this]
    ring
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hx
    by_cases hxa : x < a
    · simp [hX x hxa]
    · have : a + n < x := by
        by_contra h'
        exact hx (x - a).toNat (by omega) (by omega)
      have hy := hY (a + b + n - x) (by omega)
      simp [hy]

theorem indepSum_neg (X Y : PMF ℤ) (hX : ∀ x < 0, X x = 0) (hY : ∀ y < 0, Y y = 0) (z : ℤ)
    (hz : z < 0) : indepSum X Y z = 0 := by
  rw [indepSum_apply, ENNReal.tsum_eq_zero]
  intro x
  by_cases hx : x < 0
  · simp [hX x hx]
  · have hy := hY (z - x) (by omega)
    simp [hy]

/-- polynomial with prescribed coefficients -/
theorem coeff_sum (f : ℕ → ℝ) (N : ℕ) (hf : ∀ i, N ≤ i → f i = 0) (n : ℕ) :
    (∑ i ∈ Finset.range N, C (f i) * X ^ i).coeff n = f n := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · exact (hf n (by omega)).symm

theorem shift_poly (X : PMF ℤ) (hfin : X.support.Finite) :
    ∃ a : ℤ, ∃ p : ℝ[X], (∀ x < a, X x = 0) ∧ (∀ n : ℕ, p.coeff n = (X (a + n)).toReal) ∧
      p ≠ 0 := by
  obtain ⟨a, ha⟩ := hfin.bddBelow
  obtain ⟨B, hB⟩ := hfin.bddAbove
  have hlo : ∀ x < a, X x = 0 := fun x hx => by
    by_contra h
    have := ha ((PMF.mem_support_iff X x).2 h); omega
  have hhi : ∀ x, B < x → X x = 0 := fun x hx => by
    by_contra h
    have := hB ((PMF.mem_support_iff X x).2 h); omega
  set N := (B - a + 1).toNat
  refine ⟨a, ∑ i ∈ Finset.range N, C (X (a + i)).toReal * Polynomial.X ^ i, hlo, ?_, ?_⟩
  · intro n
    refine coeff_sum _ N (fun i hi => ?_) n
    rw [hhi _ (by omega)]; rfl
  · intro hp
    obtain ⟨x, hx⟩ := X.support_nonempty
    have hxa : a ≤ x := ha hx
    have hc := coeff_sum (fun i => (X (a + i)).toReal) N (fun i hi => by
      rw [hhi _ (by omega)]; rfl) (x - a).toNat
    rw [hp, Polynomial.coeff_zero] at hc
    have hx' : a + ((x - a).toNat : ℤ) = x := by omega
    simp only [hx'] at hc
    have := (ENNReal.toReal_eq_zero_iff _).1 hc.symm
    rcases this with h | h
    · exact (PMF.mem_support_iff X x).1 hx h
    · exact PMF.apply_ne_top X x h

/-- From a zero-one normalized shift polynomial, the PMF is uniform. -/
theorem uniform_of_zeroOne (X : PMF ℤ) (hfin : X.support.Finite) (a : ℤ) (p : ℝ[X])
    (hlo : ∀ x < a, X x = 0) (hp : ∀ n : ℕ, p.coeff n = (X (a + n)).toReal) (α : ℝ)
    (hα : 0 < α) (h01 : IsZeroOne (p * C α⁻¹)) : IsUniformOnSupport X := by
  rw [isZeroOne_iff] at h01
  refine uniform_of_const hfin (ENNReal.ofReal α) fun z hz => ?_
  have hza : a ≤ z := by by_contra h; exact hz (hlo z (by omega))
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, z = a + n := ⟨(z - a).toNat, by omega⟩
  have hreal : (X (a + n)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨hz, PMF.apply_ne_top _ _⟩
  have hc : (p * C α⁻¹).coeff n = (X (a + n)).toReal * α⁻¹ := by
    rw [Polynomial.coeff_mul_C, hp]
  have h1 := h01 n (by rw [hc]; exact mul_ne_zero hreal (inv_ne_zero hα.ne'))
  rw [hc] at h1
  have : (X (a + n)).toReal = α := by
    field_simp at h1; linarith
  rw [← this, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

theorem forward (hMO : ∀ (P Q R : ℝ[X]), P.Monic → Q.Monic → (∀ c ∈ P.coeffs, 0 ≤ c) →
      (∀ c ∈ Q.coeffs, 0 ≤ c) → R = P * Q → IsZeroOne R → IsZeroOne P ∧ IsZeroOne Q) :
    ∀ (X Y : PMF ℤ), X.support.Finite ∧ Y.support.Finite ∧ IsUniformOnSupport (indepSum X Y) →
      IsUniformOnSupport X ∧ IsUniformOnSupport Y := by
  rintro X Y ⟨hX, hY, hU⟩
  obtain ⟨a, p, hpa, hpc, hp0⟩ := shift_poly X hX
  obtain ⟨b, q, hqb, hqc, hq0⟩ := shift_poly Y hY
  have hpnn : ∀ n, 0 ≤ p.coeff n := fun n => by rw [hpc]; exact ENNReal.toReal_nonneg
  have hqnn : ∀ n, 0 ≤ q.coeff n := fun n => by rw [hqc]; exact ENNReal.toReal_nonneg
  set α := p.leadingCoeff
  set β := q.leadingCoeff
  have hα : 0 < α := lt_of_le_of_ne (hpnn _) (Ne.symm (leadingCoeff_ne_zero.2 hp0))
  have hβ : 0 < β := lt_of_le_of_ne (hqnn _) (Ne.symm (leadingCoeff_ne_zero.2 hq0))
  have hPm : (p * C α⁻¹).Monic := Polynomial.monic_mul_leadingCoeff_inv hp0
  have hQm : (q * C β⁻¹).Monic := Polynomial.monic_mul_leadingCoeff_inv hq0
  have hPnn : ∀ n, 0 ≤ (p * C α⁻¹).coeff n := fun n => by
    rw [Polynomial.coeff_mul_C]; exact mul_nonneg (hpnn n) (inv_nonneg.2 hα.le)
  have hQnn : ∀ n, 0 ≤ (q * C β⁻¹).coeff n := fun n => by
    rw [Polynomial.coeff_mul_C]; exact mul_nonneg (hqnn n) (inv_nonneg.2 hβ.le)
  -- coefficients of the product
  have hpq : ∀ n : ℕ, (p * q).coeff n = (indepSum X Y (a + b + n)).toReal := by
    intro n
    rw [indepSum_nat X Y a b hpa hqb n, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ENNReal.toReal_sum
        (fun i _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpc, hqc, ENNReal.toReal_mul]
  have hR : (p * C α⁻¹) * (q * C β⁻¹) = (p * q) * C (α⁻¹ * β⁻¹) := by
    rw [C_mul]; ring
  have hRm : ((p * C α⁻¹) * (q * C β⁻¹)).Monic := hPm.mul hQm
  have hR01 : IsZeroOne ((p * C α⁻¹) * (q * C β⁻¹)) := by
    rw [isZeroOne_iff]
    intro n hn
    have key : ∀ m, ((p * C α⁻¹) * (q * C β⁻¹)).coeff m ≠ 0 →
        ((p * C α⁻¹) * (q * C β⁻¹)).coeff m =
          (indepSum X Y (a + b + n)).toReal * (α⁻¹ * β⁻¹) := by
      intro m hm
      rw [hR, Polynomial.coeff_mul_C, hpq] at hm ⊢
      have hm' : (indepSum X Y (a + b + m)).toReal ≠ 0 := left_ne_zero_of_mul hm
      have hn' : (indepSum X Y (a + b + n)) ≠ 0 := by
        rw [hR, Polynomial.coeff_mul_C, hpq] at hn
        exact fun h => left_ne_zero_of_mul hn (by rw [h]; rfl)
      rw [uniform_eq hU (fun h => hm' (by rw [h]; rfl)) hn']
    have h1 := key _ (by rw [hRm.coeff_natDegree]; exact one_ne_zero)
    rw [hRm.coeff_natDegree] at h1
    rw [key n hn, ← h1]
  obtain ⟨h1, h2⟩ := hMO _ _ _ hPm hQm ((nonneg_iff _).2 hPnn) ((nonneg_iff _).2 hQnn) rfl hR01
  exact ⟨uniform_of_zeroOne X hX a p hpa hpc α hα h1,
    uniform_of_zeroOne Y hY b q hqb hqc β hβ h2⟩

/-- the PMF attached to a monic nonnegative polynomial -/
theorem eval_one_eq (P : ℝ[X]) : P.eval 1 = ∑ k ∈ P.support, P.coeff k := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]; simp

theorem eval_one_pos (P : ℝ[X]) (hm : P.Monic) (hnn : ∀ n, 0 ≤ P.coeff n) : 0 < P.eval 1 := by
  rw [eval_one_eq]
  have hmem : P.natDegree ∈ P.support := by
    rw [Polynomial.mem_support_iff, hm.coeff_natDegree]; exact one_ne_zero
  calc (0 : ℝ) < P.coeff P.natDegree := by rw [hm.coeff_natDegree]; exact one_pos
    _ ≤ _ := Finset.single_le_sum (fun i _ => hnn i) hmem

theorem pmf_of_poly (P : ℝ[X]) (hm : P.Monic) (hnn : ∀ n, 0 ≤ P.coeff n) :
    ∃ X : PMF ℤ, X.support.Finite ∧
      ∀ z, X z = if 0 ≤ z then ENNReal.ofReal (P.coeff z.toNat / P.eval 1) else 0 := by
  classical
  have he := eval_one_pos P hm hnn
  set f : ℤ → ℝ≥0∞ := fun z => if 0 ≤ z then ENNReal.ofReal (P.coeff z.toNat / P.eval 1) else 0
  set s : Finset ℤ := P.support.image (fun k : ℕ => (k : ℤ))
  have h0 : ∀ z ∉ s, f z = 0 := by
    intro z hz
    simp only [f]
    split_ifs with h
    · have : z.toNat ∉ P.support := fun hk => hz (Finset.mem_image.2 ⟨_, hk, by omega⟩)
      rw [Polynomial.notMem_support_iff.1 this]; simp
    · rfl
  have h1 : ∑ z ∈ s, f z = 1 := by
    rw [Finset.sum_image (fun i _ j _ h => by simpa using h)]
    simp only [f, Nat.cast_nonneg, if_true, Int.toNat_natCast]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (hnn i) he.le),
      ← Finset.sum_div, ← eval_one_eq, div_self he.ne', ENNReal.ofReal_one]
  refine ⟨PMF.ofFinset f s h1 h0, ?_, fun z => rfl⟩
  refine (s.finite_toSet).subset fun z hz => ?_
  by_contra h
  exact (PMF.mem_support_iff _ z).1 hz (h0 z h)

theorem zeroOne_of_uniform (P : ℝ[X]) (hm : P.Monic) (hnn : ∀ n, 0 ≤ P.coeff n) (X : PMF ℤ)
    (hX : ∀ z, X z = if 0 ≤ z then ENNReal.ofReal (P.coeff z.toNat / P.eval 1) else 0)
    (hU : IsUniformOnSupport X) : IsZeroOne P := by
  have he := eval_one_pos P hm hnn
  rw [isZeroOne_iff]
  intro n hn
  have hXn : X n = ENNReal.ofReal (P.coeff n / P.eval 1) := by simp [hX]
  have hXd : X P.natDegree = ENNReal.ofReal (1 / P.eval 1) := by
    simp [hX, hm.coeff_natDegree]
  have hpos : 0 < P.coeff n := lt_of_le_of_ne (hnn n) (Ne.symm hn)
  have h1 : X n ≠ 0 := by rw [hXn]; exact (ENNReal.ofReal_pos.2 (div_pos hpos he)).ne'
  have h2 : X P.natDegree ≠ 0 := by
    rw [hXd]; exact (ENNReal.ofReal_pos.2 (div_pos one_pos he)).ne'
  have := uniform_eq hU h1 h2
  rw [hXn, hXd, ENNReal.ofReal_eq_ofReal_iff (div_nonneg (hnn n) he.le)
    (div_nonneg zero_le_one he.le)] at this
  field_simp at this
  linarith

theorem backward (hG : ∀ (X Y : PMF ℤ), X.support.Finite ∧ Y.support.Finite ∧
      IsUniformOnSupport (indepSum X Y) → IsUniformOnSupport X ∧ IsUniformOnSupport Y) :
    ∀ (P Q R : ℝ[X]), P.Monic → Q.Monic → (∀ c ∈ P.coeffs, 0 ≤ c) →
      (∀ c ∈ Q.coeffs, 0 ≤ c) → R = P * Q → IsZeroOne R → IsZeroOne P ∧ IsZeroOne Q := by
  intro P Q R hPm hQm hPnn hQnn hR hR01
  rw [nonneg_iff] at hPnn hQnn
  rw [isZeroOne_iff] at hR01
  obtain ⟨X, hXf, hX⟩ := pmf_of_poly P hPm hPnn
  obtain ⟨Y, hYf, hY⟩ := pmf_of_poly Q hQm hQnn
  have heP := eval_one_pos P hPm hPnn
  have heQ := eval_one_pos Q hQm hQnn
  have hXneg : ∀ x < 0, X x = 0 := fun x hx => by rw [hX, if_neg (by omega)]
  have hYneg : ∀ y < 0, Y y = 0 := fun y hy => by rw [hY, if_neg (by omega)]
  have hUn : ∀ n : ℕ, indepSum X Y n =
      ENNReal.ofReal (R.coeff n / (P.eval 1 * Q.eval 1)) := by
    intro n
    have := indepSum_nat X Y 0 0 hXneg hYneg n
    simp only [zero_add] at this
    rw [this, hR, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_div, ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        div_nonneg (mul_nonneg (hPnn _) (hQnn _)) (mul_pos heP heQ).le)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hX, hY, Nat.cast_nonneg, if_true, Int.toNat_natCast]
    rw [← ENNReal.ofReal_mul (div_nonneg (hPnn _) heP.le)]
    congr 1
    field_simp
  have hUfin : (indepSum X Y).support.Finite := by
    refine ((R.support.image (fun k : ℕ => (k : ℤ))).finite_toSet).subset fun z hz => ?_
    have hz' := (PMF.mem_support_iff _ z).1 hz
    have hz0 : 0 ≤ z := by
      by_contra h; exact hz' (indepSum_neg X Y hXneg hYneg z (by omega))
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, z = n := ⟨z.toNat, by omega⟩
    rw [hUn] at hz'
    have : R.coeff n ≠ 0 := fun h => hz' (by simp [h])
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Polynomial.mem_support_iff.2 this, rfl⟩)
  have hU : IsUniformOnSupport (indepSum X Y) := by
    refine uniform_of_const hUfin (ENNReal.ofReal (1 / (P.eval 1 * Q.eval 1))) fun z hz => ?_
    have hz0 : 0 ≤ z := by
      by_contra h; exact hz (indepSum_neg X Y hXneg hYneg z (by omega))
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, z = n := ⟨z.toNat, by omega⟩
    rw [hUn] at hz ⊢
    have : R.coeff n ≠ 0 := fun h => hz (by simp [h])
    rw [hR01 n this]
  obtain ⟨h1, h2⟩ := hG X Y ⟨hXf, hYf, hU⟩
  exact ⟨zeroOne_of_uniform P hPm hPnn X hX h1, zeroOne_of_uniform Q hQm hQnn Y hY h2⟩

end OMA.MO339137

theorem OMA.solution : type_of% @Mathoverflow339137.mathoverflow_339137_probabilistic :=
  ⟨OMA.MO339137.forward, OMA.MO339137.backward⟩
