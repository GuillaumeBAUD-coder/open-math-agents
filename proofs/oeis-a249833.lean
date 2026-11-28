import OMAStatements.S_oeis_a249833

open Finset PowerSeries

namespace OMA.S_oeis_a249833

-- Exponential power series E(t) = ∑ t^k / k!
private noncomputable def E : PowerSeries ℚ :=
  PowerSeries.mk fun k => ((k.factorial : ℚ)⁻¹)

private lemma coeff_E (k : ℕ) : PowerSeries.coeff k E = (k.factorial : ℚ)⁻¹ := by
  simp [E]

private lemma constantCoeff_E : PowerSeries.constantCoeff E = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_E]
  simp

private lemma deriv_E : PowerSeries.derivative (R := ℚ) E = E := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_E, coeff_E, Nat.factorial_succ]
  have h1 : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  push_cast
  field_simp

-- Derivation δ(f) = (1 + X * E) * f'
private noncomputable def delta (f : PowerSeries ℚ) : PowerSeries ℚ :=
  (1 + PowerSeries.X * E) * PowerSeries.derivative (R := ℚ) f

private lemma delta_add (f g : PowerSeries ℚ) : delta (f + g) = delta f + delta g := by
  simp [delta, map_add, mul_add]

private lemma delta_smul (c : ℚ) (f : PowerSeries ℚ) : delta (c • f) = c • delta f := by
  simp [delta]

private lemma delta_mul (f g : PowerSeries ℚ) :
    delta (f * g) = delta f * g + f * delta g := by
  simp only [delta, Derivation.leibniz, smul_eq_mul]
  ring

private lemma delta_one : delta 1 = 0 := by
  simp [delta]

private lemma delta_zero : delta 0 = 0 := by
  simp [delta]

private lemma delta_X : delta PowerSeries.X = 1 + PowerSeries.X * E := by
  simp [delta]

private lemma delta_E : delta E = E + E ^ 2 * PowerSeries.X := by
  simp only [delta, deriv_E]
  ring

private lemma delta_iter_add :
    ∀ n : ℕ, ∀ f g : PowerSeries ℚ, delta^[n] (f + g) = delta^[n] f + delta^[n] g
  | 0, f, g => rfl
  | n + 1, f, g => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', delta_iter_add n f g, delta_add]

private lemma delta_iter_smul :
    ∀ n : ℕ, ∀ (c : ℚ) (f : PowerSeries ℚ), delta^[n] (c • f) = c • delta^[n] f
  | 0, _, _ => rfl
  | n + 1, c, f => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        delta_iter_smul n c f, delta_smul]

private lemma delta_iter_zero : ∀ n : ℕ, delta^[n] 0 = 0
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', delta_iter_zero n, delta_zero]

private lemma delta_iter_one : ∀ n : ℕ, delta^[n] 1 = if n = 0 then 1 else 0
  | 0 => rfl
  | 1 => by simp [delta_one]
  | n + 2 => by
      rw [Function.iterate_succ_apply', delta_iter_one (n + 1)]
      simp [delta_zero]

-- Leibniz rule for iterates of δ
private lemma delta_iter_mul :
    ∀ n : ℕ, ∀ f g : PowerSeries ℚ,
      delta^[n] (f * g) =
        ∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℚ) • (delta^[k] f * delta^[n - k] g))
  | 0, f, g => by simp
  | n + 1, f, g => by
      rw [Function.iterate_succ_apply', delta_iter_mul n f g]
      have hdelta_sum : ∀ (s : Finset ℕ) (h : ℕ → PowerSeries ℚ),
          delta (∑ k ∈ s, h k) = ∑ k ∈ s, delta (h k) := by
        intro s h
        classical
        induction s using Finset.induction_on with
        | empty => simp [delta_zero]
        | insert a s ha ih => rw [Finset.sum_insert ha, delta_add, ih, Finset.sum_insert ha]
      rw [hdelta_sum]
      have hstep : ∀ k ∈ range (n + 1),
          delta ((n.choose k : ℚ) • (delta^[k] f * delta^[n - k] g)) =
            (n.choose k : ℚ) • (delta^[k + 1] f * delta^[n - k] g) +
            (n.choose k : ℚ) • (delta^[k] f * delta^[n - k + 1] g) := by
        intro k _
        rw [delta_smul, delta_mul, smul_add, Function.iterate_succ_apply',
          Function.iterate_succ_apply']
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
      -- Shift first sum by k ↦ k + 1 and combine via Pascal's rule
      conv_rhs => rw [sum_range_succ, sum_range_succ']
      have hshift : ∑ k ∈ range (n + 1), (n.choose k : ℚ) • (delta^[k + 1] f * delta^[n - k] g) =
          (∑ k ∈ range n, (n.choose k : ℚ) • (delta^[k + 1] f * delta^[n - k] g)) +
          ((n.choose n : ℚ) • (delta^[n + 1] f * delta^[0] g)) := by
        rw [sum_range_succ, Nat.sub_self]
      have hsecond : ∑ k ∈ range (n + 1), (n.choose k : ℚ) • (delta^[k] f * delta^[n - k + 1] g) =
          (∑ k ∈ range n, (n.choose (k + 1) : ℚ) • (delta^[k + 1] f * delta^[n - (k + 1) + 1] g)) +
          ((n.choose 0 : ℚ) • (delta^[0] f * delta^[n + 1] g)) := by
        rw [sum_range_succ', Nat.sub_zero]
      rw [hshift, hsecond]
      have hmid : (∑ k ∈ range n, (n.choose k : ℚ) • (delta^[k + 1] f * delta^[n - k] g)) +
          (∑ k ∈ range n, (n.choose (k + 1) : ℚ) • (delta^[k + 1] f * delta^[n - (k + 1) + 1] g)) =
          ∑ k ∈ range n, ((n + 1).choose (k + 1) : ℚ) • (delta^[k + 1] f * delta^[n + 1 - (k + 1)] g) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkn : k < n := mem_range.mp hk
        have hsub1 : n - (k + 1) + 1 = n - k := by omega
        have hsub2 : n + 1 - (k + 1) = n - k := by omega
        rw [hsub1, hsub2, Nat.choose_succ_succ, Nat.cast_add, add_smul]
      simp only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero, Nat.cast_one,
        one_smul]
      rw [← hmid]
      abel

-- Sequence A n = derivative (delta^[n] E)
private noncomputable def A (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.derivative (R := ℚ) (delta^[n] E)

private lemma A_zero : A 0 = E := by
  simp [A, deriv_E]

private lemma A_succ (n : ℕ) : A (n + 1) = PowerSeries.derivative (R := ℚ) ((1 + PowerSeries.X * E) * A n) := by
  simp only [A, Function.iterate_succ_apply', delta]

private lemma fact_coeff_A :
    ∀ n q : ℕ, (q.factorial : ℚ) * PowerSeries.coeff q (A n) = (R n q : ℚ)
  | 0, q => by
      rw [A_zero, coeff_E, R]
      have hne : (q.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
      simp [mul_inv_cancel₀ hne]
  | n + 1, q => by
      rw [A_succ, PowerSeries.coeff_derivative]
      have hmul_expand : PowerSeries.coeff (q + 1) ((1 + PowerSeries.X * E) * A n) =
          PowerSeries.coeff (q + 1) (A n) + PowerSeries.coeff q (E * A n) := by
        rw [add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_succ_X_mul]
      rw [hmul_expand]
      have h1 : (q.factorial : ℚ) * (((q + 1 : ℕ) : ℚ) * PowerSeries.coeff (q + 1) (A n)) =
          (R n (q + 1) : ℚ) := by
        have hfac : (q.factorial : ℚ) * ((q + 1 : ℕ) : ℚ) = ((q + 1).factorial : ℚ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        rw [← mul_assoc, hfac, fact_coeff_A n (q + 1)]
      have h2 : (q.factorial : ℚ) * (((q + 1 : ℕ) : ℚ) * PowerSeries.coeff q (E * A n)) =
          ((q + 1 : ℕ) : ℚ) * ∑ j ∈ Finset.range (q + 1), (q.choose j : ℚ) * (R n j : ℚ) := by
        rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i E * PowerSeries.coeff j (A n)) q]
        have hswap : ∑ i ∈ range (q + 1), PowerSeries.coeff i E * PowerSeries.coeff (q - i) (A n) =
            ∑ j ∈ range (q + 1), PowerSeries.coeff (q - j) E * PowerSeries.coeff j (A n) := by
          refine Finset.sum_nbij (fun i => q - i) ?_ ?_ ?_ ?_
          · intro i hi; simp only [mem_range] at hi ⊢; omega
          · intro i₁ hi₁ i₂ hi₂ heq
            simp only [Finset.mem_coe, mem_range] at hi₁ hi₂
            dsimp only at heq; omega
          · intro j hj
            simp only [Finset.mem_coe, mem_range] at hj
            exact ⟨q - j, by simp only [Finset.mem_coe, mem_range]; omega, by dsimp only; omega⟩
          · intro i hi
            have hiq : i ≤ q := Nat.lt_succ_iff.mp (mem_range.mp hi)
            simp [Nat.sub_sub_self hiq]
        rw [hswap]
        have hlhs : (q.factorial : ℚ) * (((q + 1 : ℕ) : ℚ) *
            ∑ j ∈ range (q + 1), PowerSeries.coeff (q - j) E * PowerSeries.coeff j (A n)) =
            ((q + 1 : ℕ) : ℚ) * ∑ j ∈ range (q + 1),
              (q.factorial : ℚ) * (PowerSeries.coeff (q - j) E * PowerSeries.coeff j (A n)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hlhs]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjq : j ≤ q := Nat.lt_succ_iff.mp (mem_range.mp hj)
        rw [coeff_E]
        have hchoose : (q.choose j : ℚ) * (j.factorial : ℚ) * ((q - j).factorial : ℚ) =
            (q.factorial : ℚ) := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjq
        have hjne : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
        have hqjne : ((q - j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (q - j))
        have hR := fact_coeff_A n j
        rw [← hR]
        have : (q.choose j : ℚ) = (q.factorial : ℚ) / ((j.factorial : ℚ) * ((q - j).factorial : ℚ)) := by
          field_simp [hjne, hqjne]; linarith
        rw [this]
        field_simp [hjne, hqjne]
      have hsplit : (q.factorial : ℚ) * ((PowerSeries.coeff (q + 1) (A n) + PowerSeries.coeff q (E * A n)) *
            ((q : ℚ) + 1)) =
          (q.factorial : ℚ) * (((q + 1 : ℕ) : ℚ) * PowerSeries.coeff (q + 1) (A n)) +
          (q.factorial : ℚ) * (((q + 1 : ℕ) : ℚ) * PowerSeries.coeff q (E * A n)) := by
        push_cast; ring
      rw [hsplit, h1, h2]
      simp only [R]
      push_cast
      ring

-- Homomorphism Φ : f ↦ ∑ (δ^n f)(0) / n! * X^n
private noncomputable def Phi (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (n.factorial : ℚ)⁻¹ * PowerSeries.constantCoeff (delta^[n] f)

private lemma coeff_Phi (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff n (Phi f) = (n.factorial : ℚ)⁻¹ * PowerSeries.constantCoeff (delta^[n] f) := by
  simp [Phi]

private lemma Phi_one : Phi 1 = 1 := by
  ext n
  rw [coeff_Phi, delta_iter_one, PowerSeries.coeff_one]
  split_ifs with hn
  · subst hn; simp
  · simp

private lemma Phi_add (f g : PowerSeries ℚ) : Phi (f + g) = Phi f + Phi g := by
  ext n
  rw [map_add, coeff_Phi, coeff_Phi, coeff_Phi, delta_iter_add, map_add, mul_add]

private lemma Phi_mul (f g : PowerSeries ℚ) : Phi (f * g) = Phi f * Phi g := by
  ext n
  rw [coeff_Phi, delta_iter_mul, map_sum, Finset.mul_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i (Phi f) * PowerSeries.coeff j (Phi g)) n]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [coeff_Phi, coeff_Phi, ← PowerSeries.coeff_zero_eq_constantCoeff, map_smul,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul, smul_eq_mul]
  have hchoose : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) =
      (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hkne : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hnkne : ((n - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hnne : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have : (n.factorial : ℚ)⁻¹ * (n.choose k : ℚ) = (k.factorial : ℚ)⁻¹ * ((n - k).factorial : ℚ)⁻¹ := by
    field_simp [hkne, hnkne, hnne]; linarith
  calc (n.factorial : ℚ)⁻¹ * ((n.choose k : ℚ) * (PowerSeries.constantCoeff (delta^[k] f) *
        PowerSeries.constantCoeff (delta^[n - k] g)))
      = ((n.factorial : ℚ)⁻¹ * (n.choose k : ℚ)) * (PowerSeries.constantCoeff (delta^[k] f) *
        PowerSeries.constantCoeff (delta^[n - k] g)) := by ring
    _ = ((k.factorial : ℚ)⁻¹ * ((n - k).factorial : ℚ)⁻¹) * (PowerSeries.constantCoeff (delta^[k] f) *
        PowerSeries.constantCoeff (delta^[n - k] g)) := by rw [this]
    _ = ((k.factorial : ℚ)⁻¹ * PowerSeries.constantCoeff (delta^[k] f)) *
        (((n - k).factorial : ℚ)⁻¹ * PowerSeries.constantCoeff (delta^[n - k] g)) := by ring

private lemma deriv_Phi (f : PowerSeries ℚ) :
    PowerSeries.derivative (R := ℚ) (Phi f) = Phi (delta f) := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_Phi, coeff_Phi, Function.iterate_succ_apply,
    Nat.factorial_succ]
  have h1 : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  push_cast
  field_simp

-- Fundamental identity: B * derivative (logOf B) = derivative B when constantCoeff B = 1
private lemma mul_deriv_logOf {B : PowerSeries ℚ} (hB0 : PowerSeries.constantCoeff B = 1) :
    B * PowerSeries.derivative (R := ℚ) (PowerSeries.logOf B) = PowerSeries.derivative (R := ℚ) B := by
  have hsubst : PowerSeries.HasSubst (B - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hB0])
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst hsubst]
  have h1X : (1 + PowerSeries.X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (PowerSeries.log ℚ) = 1 := by
    rw [PowerSeries.deriv_log]
    ext n
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_one]
    cases n with
    | zero => simp
    | succ n =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
        simp [pow_succ]
  have hone : (1 : PowerSeries ℚ).subst (B - 1) = 1 := by
    simpa [PowerSeries.coe_substAlgHom] using map_one (PowerSeries.substAlgHom hsubst)
  have hB_eq : (1 + PowerSeries.X : PowerSeries ℚ).subst (B - 1) = B := by
    rw [PowerSeries.subst_add hsubst, hone, PowerSeries.subst_X hsubst]
    ring
  have hprod : B * (PowerSeries.derivative (R := ℚ) (PowerSeries.log ℚ)).subst (B - 1) = 1 := by
    calc B * (PowerSeries.derivative (R := ℚ) (PowerSeries.log ℚ)).subst (B - 1)
        = (1 + PowerSeries.X : PowerSeries ℚ).subst (B - 1) *
            (PowerSeries.derivative (R := ℚ) (PowerSeries.log ℚ)).subst (B - 1) := by rw [hB_eq]
      _ = ((1 + PowerSeries.X : PowerSeries ℚ) *
            PowerSeries.derivative (R := ℚ) (PowerSeries.log ℚ)).subst (B - 1) := by
          rw [PowerSeries.subst_mul hsubst]
      _ = (1 : PowerSeries ℚ).subst (B - 1) := by rw [h1X]
      _ = 1 := hone
  have hderiv_sub : PowerSeries.derivative (R := ℚ) (B - 1) = PowerSeries.derivative (R := ℚ) B := by
    simp
  rw [hderiv_sub, ← mul_assoc, hprod, one_mul]

-- Uniqueness of solutions to B' = B + B^2 * logOf B with B(0) = 1
private lemma coeff_eq_of_ode {B₁ B₂ : PowerSeries ℚ}
    (h10 : PowerSeries.constantCoeff B₁ = 1)
    (h20 : PowerSeries.constantCoeff B₂ = 1)
    (h1 : PowerSeries.derivative (R := ℚ) B₁ = B₁ + B₁ ^ 2 * PowerSeries.logOf B₁)
    (h2 : PowerSeries.derivative (R := ℚ) B₂ = B₂ + B₂ ^ 2 * PowerSeries.logOf B₂) :
    ∀ k : ℕ, PowerSeries.coeff k B₁ = PowerSeries.coeff k B₂ ∧
      PowerSeries.coeff k (PowerSeries.logOf B₁) = PowerSeries.coeff k (PowerSeries.logOf B₂) := by
  have hlog1 := mul_deriv_logOf h10
  have hlog2 := mul_deriv_logOf h20
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | m
      · exact ⟨by rw [PowerSeries.coeff_zero_eq_constantCoeff, h10, h20],
          by rw [PowerSeries.coeff_zero_eq_constantCoeff,
            PowerSeries.constantCoeff_logOf h10, PowerSeries.constantCoeff_logOf h20]⟩
      · have hm1 : ((m : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        -- Step 1: coeff (m + 1) B₁ = coeff (m + 1) B₂
        have hB_eq : PowerSeries.coeff (m + 1) B₁ = PowerSeries.coeff (m + 1) B₂ := by
          have hd1 := congr_arg (PowerSeries.coeff m) h1
          have hd2 := congr_arg (PowerSeries.coeff m) h2
          rw [PowerSeries.coeff_derivative] at hd1 hd2
          have hrhs : PowerSeries.coeff m (B₁ + B₁ ^ 2 * PowerSeries.logOf B₁) =
              PowerSeries.coeff m (B₂ + B₂ ^ 2 * PowerSeries.logOf B₂) := by
            simp only [map_add, sq, PowerSeries.coeff_mul]
            congr 1
            · exact (ih m (by omega)).1
            · refine Finset.sum_congr rfl fun p hp => ?_
              have hpm : p.1 ≤ m ∧ p.2 ≤ m := by
                have := Finset.mem_antidiagonal.mp hp; omega
              rw [(ih p.2 (by omega)).2]
              congr 1
              refine Finset.sum_congr rfl fun q hq => ?_
              have hqm : q.1 ≤ p.1 ∧ q.2 ≤ p.1 := by
                have := Finset.mem_antidiagonal.mp hq; omega
              rw [(ih q.1 (by omega)).1, (ih q.2 (by omega)).1]
          have hmul_eq : PowerSeries.coeff (m + 1) B₁ * ((m : ℚ) + 1) =
              PowerSeries.coeff (m + 1) B₂ * ((m : ℚ) + 1) := by
            rw [hd1, hd2, hrhs]
          exact mul_right_cancel₀ hm1 hmul_eq
        -- Step 2: coeff (m + 1) (logOf B₁) = coeff (m + 1) (logOf B₂)
        have hL_eq : PowerSeries.coeff (m + 1) (PowerSeries.logOf B₁) =
            PowerSeries.coeff (m + 1) (PowerSeries.logOf B₂) := by
          have hl1 := congr_arg (PowerSeries.coeff m) hlog1
          have hl2 := congr_arg (PowerSeries.coeff m) hlog2
          rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i B₁ * PowerSeries.coeff j (PowerSeries.derivative (R := ℚ) (PowerSeries.logOf B₁))) m,
            Finset.sum_range_succ', Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff, h10,
            one_mul, PowerSeries.coeff_derivative] at hl1
          rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i B₂ * PowerSeries.coeff j (PowerSeries.derivative (R := ℚ) (PowerSeries.logOf B₂))) m,
            Finset.sum_range_succ', Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff, h20,
            one_mul, PowerSeries.coeff_derivative] at hl2
          have hrest : ∑ i ∈ range m, PowerSeries.coeff (i + 1) B₁ *
                PowerSeries.coeff (m - (i + 1)) (PowerSeries.derivative (R := ℚ) (PowerSeries.logOf B₁)) =
              ∑ i ∈ range m, PowerSeries.coeff (i + 1) B₂ *
                PowerSeries.coeff (m - (i + 1)) (PowerSeries.derivative (R := ℚ) (PowerSeries.logOf B₂)) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have him : i < m := mem_range.mp hi
            rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative]
            rw [(ih (i + 1) (by omega)).1, (ih (m - (i + 1) + 1) (by omega)).2]
          have hmul_eq : PowerSeries.coeff (m + 1) (PowerSeries.logOf B₁) * ((m : ℚ) + 1) =
              PowerSeries.coeff (m + 1) (PowerSeries.logOf B₂) * ((m : ℚ) + 1) := by
            rw [hB_eq, hrest] at hl1
            linarith
          exact mul_right_cancel₀ hm1 hmul_eq
        exact ⟨hB_eq, hL_eq⟩

private lemma main_proof :
    ∀ B : PowerSeries ℚ, B.constantCoeff = 1 →
      PowerSeries.derivative (R := ℚ) B = B + B ^ 2 * PowerSeries.logOf B →
      ∀ n : ℕ, (R n 0 : ℚ) = ((n + 1).factorial : ℚ) * PowerSeries.coeff (n + 1) B := by
  intro B hB0 hBode n
  set Btilde : PowerSeries ℚ := Phi E
  set Ltilde : PowerSeries ℚ := Phi PowerSeries.X
  have hBt0 : PowerSeries.constantCoeff Btilde = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_Phi]
    simp [constantCoeff_E]
  have hLt0 : PowerSeries.constantCoeff Ltilde = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_Phi]
    simp
  have hBt_deriv : PowerSeries.derivative (R := ℚ) Btilde = Btilde + Btilde ^ 2 * Ltilde := by
    rw [deriv_Phi, delta_E, Phi_add, Phi_mul, sq, Phi_mul]
    simp only [Btilde, Ltilde, sq]
  have hLt_deriv : PowerSeries.derivative (R := ℚ) Ltilde = 1 + Ltilde * Btilde := by
    rw [deriv_Phi, delta_X, Phi_add, Phi_one, Phi_mul]
  -- Show Ltilde = logOf Btilde via Btilde * (Ltilde' - (logOf Btilde)') = 0
  have hL_eq_log : Ltilde = PowerSeries.logOf Btilde := by
    have hmul_eq : Btilde * PowerSeries.derivative (R := ℚ) Ltilde =
        Btilde * PowerSeries.derivative (R := ℚ) (PowerSeries.logOf Btilde) := by
      rw [mul_deriv_logOf hBt0, hLt_deriv, hBt_deriv]
      ring
    have hB_unit : IsUnit Btilde := by
      rw [PowerSeries.isUnit_iff_constantCoeff, hBt0]
      exact isUnit_one
    have hderiv_eq : PowerSeries.derivative (R := ℚ) Ltilde =
        PowerSeries.derivative (R := ℚ) (PowerSeries.logOf Btilde) :=
      hB_unit.mul_left_cancel hmul_eq
    ext k
    cases k with
    | zero =>
        rw [PowerSeries.coeff_zero_eq_constantCoeff, hLt0, PowerSeries.constantCoeff_logOf hBt0]
    | succ m =>
        have hm := congr_arg (PowerSeries.coeff m) hderiv_eq
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at hm
        exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m : ((m : ℚ) + 1) ≠ 0) hm
  have hBt_ode : PowerSeries.derivative (R := ℚ) Btilde =
      Btilde + Btilde ^ 2 * PowerSeries.logOf Btilde := by
    rw [← hL_eq_log]
    exact hBt_deriv
  have hcoeff_eq := (coeff_eq_of_ode hB0 hBt0 hBode hBt_ode (n + 1)).1
  rw [hcoeff_eq, coeff_Phi]
  have hne : ((n + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [Function.iterate_succ_apply', delta, map_mul, map_add, map_one, map_mul,
    PowerSeries.constantCoeff_X, zero_mul, add_zero, one_mul]
  have hA := fact_coeff_A n 0
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul, PowerSeries.coeff_zero_eq_constantCoeff] at hA
  exact hA.symm

end OMA.S_oeis_a249833

theorem OMA.solution : type_of% @OMA.S_oeis_a249833.main :=
  OMA.S_oeis_a249833.main_proof
