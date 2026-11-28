import OMAStatements.S_oeis_a122648

namespace OMA.P_oeis_a122648

open PowerSeries OMA.S_oeis_a122648

private noncomputable def D (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f

@[simp]
private lemma coeff_D (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (D f) = ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f := by
  simp [D]

private lemma D_add (f g : PowerSeries ℚ) : D (f + g) = D f + D g := by
  ext n
  simp [map_add]
  ring

private lemma D_C_mul (c : ℚ) (f : PowerSeries ℚ) : D (C c * f) = C c * D f := by
  ext n
  simp [coeff_C_mul]
  ring

private lemma D_one : D 1 = 0 := by
  ext n
  simp [coeff_one]

private lemma D_mul (f g : PowerSeries ℚ) : D (f * g) = D f * g + f * D g := by
  ext n
  simp only [coeff_D, map_add, coeff_mul]
  rw [Finset.mul_sum]
  have hL :
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
          ((n + 1 : ℕ) : ℚ) * (coeff p.1 f * coeff p.2 g) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
          ((p.1 : ℚ) * coeff p.1 f * coeff p.2 g + coeff p.1 f * ((p.2 : ℚ) * coeff p.2 g)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hsum : p.1 + p.2 = n + 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hsumQ : (p.1 : ℚ) + (p.2 : ℚ) = ((n + 1 : ℕ) : ℚ) := by exact_mod_cast hsum
    rw [← hsumQ]
    ring
  rw [hL, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (i : ℚ) * coeff i f * coeff j g)]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => ((i + 1 : ℕ) : ℚ) * coeff (i + 1) f * coeff j g)]
    apply Finset.sum_congr rfl
    intro i _
    have hsub : n + 1 - (i + 1) = n - i := by omega
    rw [hsub]
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * ((j : ℚ) * coeff j g))]
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i f * (((j + 1 : ℕ) : ℚ) * coeff (j + 1) g))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hsub : n + 1 - i = (n - i) + 1 := by omega
    rw [hsub]

private lemma coeff_X_mul_zero' (f : PowerSeries ℚ) : coeff 0 (X * f) = 0 := by
  simp [coeff_mul]

private lemma coeff_X_mul_succ' (f : PowerSeries ℚ) (n : ℕ) :
    coeff (n + 1) (X * f) = coeff n f := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i X * coeff j f)]
  rw [Finset.sum_eq_single 1]
  · simp [coeff_X]
  · intro b _ hb
    simp [coeff_X, hb]
  · intro h
    exfalso
    exact h (Finset.mem_range.mpr (by omega))

private lemma coeff_E (n : ℕ) :
    coeff n E = if n % 2 = 0 then ((Nat.factorial (n / 2) : ℚ)⁻¹) else 0 := by
  unfold E
  have hsub : HasSubst (X ^ 2 : PowerSeries ℚ) :=
    ⟨1, by rw [pow_one]; change PowerSeries.constantCoeff (X ^ 2 : PowerSeries ℚ) = 0; simp⟩
  change MvPowerSeries.coeff (Finsupp.single () n) (subst (X ^ 2) (exp ℚ)) = _
  rw [PowerSeries.coeff_subst hsub]
  have hterm : ∀ d : ℕ,
      coeff d (exp ℚ) • MvPowerSeries.coeff (Finsupp.single () n) ((X ^ 2 : PowerSeries ℚ) ^ d) =
        if n = 2 * d then ((Nat.factorial d : ℚ)⁻¹) else 0 := by
    intro d
    change coeff d (exp ℚ) * coeff n ((X ^ 2 : PowerSeries ℚ) ^ d) = _
    rw [← pow_mul, coeff_X_pow, coeff_exp]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, one_div]
    split_ifs <;> simp
  simp_rw [hterm]
  by_cases he : n % 2 = 0
  · simp only [he, ↓reduceIte]
    refine (finsum_eq_single (fun d => if n = 2 * d then (Nat.factorial d : ℚ)⁻¹ else 0) (n / 2)
      (fun d hd => if_neg (by omega))).trans ?_
    exact if_pos (by omega)
  · simp only [he, ↓reduceIte]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    have hne : n ≠ 2 * d := by omega
    simp [hne]

private lemma coeff_H (n : ℕ) :
    coeff n H = (2 : ℚ) ^ n * (Nat.factorial n : ℚ)⁻¹ := by
  unfold H
  have hsub : HasSubst (C 2 * X : PowerSeries ℚ) :=
    ⟨1, by rw [pow_one]; change PowerSeries.constantCoeff (C 2 * X : PowerSeries ℚ) = 0; simp⟩
  change MvPowerSeries.coeff (Finsupp.single () n) (subst (C 2 * X) (exp ℚ)) = _
  rw [PowerSeries.coeff_subst hsub]
  have hterm : ∀ d : ℕ,
      coeff d (exp ℚ) • MvPowerSeries.coeff (Finsupp.single () n) ((C 2 * X : PowerSeries ℚ) ^ d) =
        if n = d then (2 : ℚ) ^ d * (Nat.factorial d : ℚ)⁻¹ else 0 := by
    intro d
    change coeff d (exp ℚ) * coeff n ((C 2 * X : PowerSeries ℚ) ^ d) = _
    rw [mul_pow, ← map_pow, coeff_C_mul, coeff_X_pow, coeff_exp]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, one_div]
    split_ifs <;> ring
  simp_rw [hterm]
  refine (finsum_eq_single (fun d => if n = d then (2 : ℚ) ^ d * (Nat.factorial d : ℚ)⁻¹ else 0) n
    (fun d hd => by simp [hd.symm])).trans ?_
  simp

private lemma D_E : D E = C 2 * X * E := by
  ext n
  rw [coeff_D, coeff_E, mul_assoc, coeff_C_mul]
  cases n with
  | zero =>
    rw [coeff_X_mul_zero']
    simp
  | succ m =>
    rw [coeff_X_mul_succ', coeff_E]
    by_cases hm : m % 2 = 0
    · have hm2 : (m + 1 + 1) % 2 = 0 := by omega
      simp only [hm, hm2, ↓reduceIte]
      have hdiv : (m + 1 + 1) / 2 = m / 2 + 1 := by omega
      rw [hdiv, Nat.factorial_succ]
      have h2 : ((m + 1 + 1 : ℕ) : ℚ) = 2 * ((m / 2 + 1 : ℕ) : ℚ) := by
        have : m + 1 + 1 = 2 * (m / 2 + 1) := by omega
        exact_mod_cast this
      rw [h2]
      push_cast
      have hnz1 : ((m / 2 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
      have hnz2 : (Nat.factorial (m / 2) : ℚ) ≠ 0 := by positivity
      field_simp [hnz1, hnz2]
    · have hm2 : (m + 1 + 1) % 2 ≠ 0 := by omega
      simp [hm, hm2]

private lemma D_H : D H = C 2 * H := by
  ext n
  rw [coeff_D, coeff_C_mul, coeff_H, coeff_H, pow_succ, Nat.factorial_succ]
  push_cast
  have hnz1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hnz2 : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  field_simp [hnz1, hnz2]

private lemma D_egf : D egf = (C 2 * X + C 2) * egf - E := by
  unfold egf
  rw [D_C_mul, D_mul, D_E, D_add, D_H, D_one]
  have hhalf : C (1 / 2 : ℚ) * C 2 = 1 := by
    rw [← map_mul]
    norm_num
  calc C (1 / 2 : ℚ) * (C 2 * X * E * (H + 1) + E * (C 2 * H + 0))
      = (C 2 * X + C 2) * (C (1 / 2 : ℚ) * (E * (H + 1))) -
          (C (1 / 2 : ℚ) * C 2) * E := by ring
    _ = (C 2 * X + C 2) * (C (1 / 2 : ℚ) * (E * (H + 1))) - E := by rw [hhalf, one_mul]

private lemma D_X : D X = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [coeff_X]

private lemma DD_egf :
    D (D egf) = (C 4 * X + C 2) * D egf + (C 2 - C 4 * X - C 4 * X ^ 2) * egf := by
  rw [D_egf]
  have hsub : D ((C 2 * X + C 2) * egf - E) =
      D ((C 2 * X + C 2) * egf) - D E := by
    have h1 := D_add ((C 2 * X + C 2) * egf - E) E
    rw [sub_add_cancel] at h1
    exact eq_sub_of_add_eq h1.symm
  rw [hsub, D_mul, D_add, D_C_mul, D_X, D_E]
  have hC2 : D (C 2) = 0 := by
    ext n
    simp
  rw [hC2]
  have hE : E = (C 2 * X + C 2) * egf - D egf := by
    rw [D_egf]
    ring
  rw [hE]
  have h2 : C (2 : ℚ) = 2 := map_ofNat C 2
  have h4 : C (4 : ℚ) = 4 := map_ofNat C 4
  rw [h2, h4]
  ring

end OMA.P_oeis_a122648

theorem OMA.solution : type_of% @OMA.S_oeis_a122648.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hode := congr_arg (PowerSeries.coeff (k + 2)) OMA.P_oeis_a122648.DD_egf
  simp only [OMA.P_oeis_a122648.coeff_D, map_add] at hode
  have hX : ∀ (f : PowerSeries ℚ) (m : ℕ),
      PowerSeries.coeff (m + 1) (PowerSeries.X * f) = PowerSeries.coeff m f :=
    fun f m => OMA.P_oeis_a122648.coeff_X_mul_succ' f m
  have hX2 : ∀ (f : PowerSeries ℚ) (m : ℕ),
      PowerSeries.coeff (m + 2) (PowerSeries.X ^ 2 * f) = PowerSeries.coeff m f := by
    intro f m
    rw [sq, mul_assoc, OMA.P_oeis_a122648.coeff_X_mul_succ', OMA.P_oeis_a122648.coeff_X_mul_succ']
  have hrew :
      PowerSeries.coeff (k + 2) ((PowerSeries.C 4 * PowerSeries.X + PowerSeries.C 2) *
          OMA.P_oeis_a122648.D OMA.S_oeis_a122648.egf) =
        4 * ((k + 2 : ℕ) : ℚ) * PowerSeries.coeff (k + 2) OMA.S_oeis_a122648.egf +
          2 * ((k + 3 : ℕ) : ℚ) * PowerSeries.coeff (k + 3) OMA.S_oeis_a122648.egf := by
    rw [add_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      hX, OMA.P_oeis_a122648.coeff_D, OMA.P_oeis_a122648.coeff_D]
    ring
  have hrew2 :
      PowerSeries.coeff (k + 2) ((PowerSeries.C 2 - PowerSeries.C 4 * PowerSeries.X -
          PowerSeries.C 4 * PowerSeries.X ^ 2) * OMA.S_oeis_a122648.egf) =
        2 * PowerSeries.coeff (k + 2) OMA.S_oeis_a122648.egf -
          4 * PowerSeries.coeff (k + 1) OMA.S_oeis_a122648.egf -
          4 * PowerSeries.coeff k OMA.S_oeis_a122648.egf := by
    rw [sub_mul, sub_mul, map_sub, map_sub, PowerSeries.coeff_C_mul,
      mul_assoc, PowerSeries.coeff_C_mul, mul_assoc, PowerSeries.coeff_C_mul, hX, hX2]
  rw [hrew, hrew2] at hode
  have hs1 : k + 4 - 1 = k + 3 := by omega
  have hs2 : k + 4 - 2 = k + 2 := by omega
  have hs3 : k + 4 - 3 = k + 1 := by omega
  have hs4 : k + 4 - 4 = k := by omega
  rw [hs1, hs2, hs3, hs4]
  unfold OMA.S_oeis_a122648.a
  have hf4 : (Nat.factorial (k + 4) : ℚ) =
      ((k + 4 : ℕ) : ℚ) * ((k + 3 : ℕ) : ℚ) * (Nat.factorial (k + 2) : ℚ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hf3 : (Nat.factorial (k + 3) : ℚ) =
      ((k + 3 : ℕ) : ℚ) * (Nat.factorial (k + 2) : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hf2 : (Nat.factorial (k + 2) : ℚ) =
      ((k + 2 : ℕ) : ℚ) * (Nat.factorial (k + 1) : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hf1 : (Nat.factorial (k + 1) : ℚ) =
      ((k + 1 : ℕ) : ℚ) * (Nat.factorial k : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hmul := congr_arg (fun t : ℚ => (Nat.factorial (k + 2) : ℚ) * t) hode
  rw [hf4, hf3]
  have hmul2 :
      (Nat.factorial (k + 2) : ℚ) *
        (4 * ((k + 2 : ℕ) : ℚ) * PowerSeries.coeff (k + 2) OMA.S_oeis_a122648.egf +
          2 * ((k + 3 : ℕ) : ℚ) * PowerSeries.coeff (k + 3) OMA.S_oeis_a122648.egf +
          (2 * PowerSeries.coeff (k + 2) OMA.S_oeis_a122648.egf -
            4 * PowerSeries.coeff (k + 1) OMA.S_oeis_a122648.egf -
            4 * PowerSeries.coeff k OMA.S_oeis_a122648.egf)) =
      (Nat.factorial (k + 2) : ℚ) *
        (((k + 3 : ℕ) : ℚ) * (((k + 4 : ℕ) : ℚ) *
          PowerSeries.coeff (k + 4) OMA.S_oeis_a122648.egf)) := hmul.symm
  rw [hf2, hf1] at hmul2 ⊢
  push_cast at hmul2 ⊢
  linarith
