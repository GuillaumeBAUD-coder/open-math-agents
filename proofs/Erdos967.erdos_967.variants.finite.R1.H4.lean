import OMAReductions.R_Erdos967_erdos_967_variants_finite_R1

-- Step Erdos967.erdos_967.variants.finite.R1.H4
-- Credit: @LordMike
-- For distinct primes p_i the polynomial P1 = sum over f in E of x^f / p^f (with 0 in E) is
-- coprime to its reciprocal P2 = sum over f in E of x^(D - f) / p^f.
-- Order the monomials by the weight W f = p^f (injective by unique factorisation, and
-- multiplicative). For a product A * B the coefficient at the sum of the W-maximal exponents is
-- the product of the two extremal coefficients; the same holds for W-minimal exponents.
-- Gauss's lemma (by reduction modulo primes): if A * B over the rationals is a polynomial with
-- coefficients 0 and 1, then A = c * A0 with A0 * B0 integral, so every extremal coefficient of
-- A has absolute value |c|. Let Q divide P1 and P2. The substitution x_i -> p_i x_i turns P1
-- into a 0/1 polynomial, and x_i -> x_i / p_i turns P2 into a constant times a 0/1 polynomial.
-- With fa the W-maximal and ga the W-minimal exponent of Q this gives
-- |q_fa| W fa = |q_ga| W ga and |q_fa| / W fa = |q_ga| / W ga, so W fa = W ga, Q is a monomial,
-- and since P1 has constant term 1 it is a nonzero constant.

namespace OMA.E967FH4

open MvPolynomial

/-- The coefficient of a product at the sum of two weight-maximal exponents. -/
lemma coeff_mul_ext {σ R : Type} [CommRing R] (w : (σ →₀ ℕ) → ℚ)
    (hmul : ∀ f g, w (f + g) = w f * w g) (hpos : ∀ f, 0 < w f) (hinj : Function.Injective w)
    (A B : MvPolynomial σ R) (fa fb : σ →₀ ℕ)
    (ha : ∀ f ∈ A.support, w f ≤ w fa) (hb : ∀ f ∈ B.support, w f ≤ w fb) :
    coeff (fa + fb) (A * B) = coeff fa A * coeff fb B := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_single (fa, fb) ?_ ?_
  · rintro ⟨x, y⟩ hxy hne
    by_contra h0
    have hx : coeff x A ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hy : coeff y B ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    have h1 := ha x (mem_support_iff.mpr hx)
    have h2 := hb y (mem_support_iff.mpr hy)
    have h3 : w x * w y = w fa * w fb := by
      rw [← hmul, ← hmul, Finset.HasAntidiagonal.mem_antidiagonal.mp hxy]
    have e1 : w x = w fa := by
      rcases h1.lt_or_eq with h | h
      · have c1 : w x * w y < w fa * w y := mul_lt_mul_of_pos_right h (hpos y)
        have c2 : w fa * w y ≤ w fa * w fb := mul_le_mul_of_nonneg_left h2 (hpos fa).le
        linarith
      · exact h
    have e2 : w y = w fb := by
      rcases h2.lt_or_eq with h | h
      · have c1 : w x * w y < w x * w fb := mul_lt_mul_of_pos_left h (hpos x)
        have c2 : w x * w fb ≤ w fa * w fb := mul_le_mul_of_nonneg_right h1 (hpos fb).le
        linarith
      · exact h
    exact hne (by rw [hinj e1, hinj e2])
  · intro h
    simp at h

/-- A weight-maximal coefficient of an integer divisor of a 0/1 polynomial is `±1`. -/
lemma ext_unit {σ : Type} (w : (σ →₀ ℕ) → ℚ)
    (hmul : ∀ f g, w (f + g) = w f * w g) (hpos : ∀ f, 0 < w f) (hinj : Function.Injective w)
    (A0 B0 F0 : MvPolynomial σ ℤ) (hAB : A0 * B0 = F0)
    (hF : ∀ g, coeff g F0 = 0 ∨ coeff g F0 = 1) (hB : B0 ≠ 0) (fa : σ →₀ ℕ)
    (hfa : fa ∈ A0.support) (ha : ∀ f ∈ A0.support, w f ≤ w fa) : |coeff fa A0| = 1 := by
  obtain ⟨fb, hfb, hb⟩ := Finset.exists_max_image B0.support w
    (Finset.nonempty_iff_ne_empty.mpr (fun h => hB (support_eq_empty.mp h)))
  have h := coeff_mul_ext w hmul hpos hinj A0 B0 fa fb ha hb
  rw [hAB] at h
  have hne : coeff fa A0 * coeff fb B0 ≠ 0 :=
    mul_ne_zero (mem_support_iff.mp hfa) (mem_support_iff.mp hfb)
  rcases hF (fa + fb) with h0 | h1
  · rw [h0] at h
    exact absurd h.symm hne
  · have h2 : coeff fa A0 * coeff fb B0 = 1 := by rw [← h, h1]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with h | h <;> simp [h]

/-- Gauss's lemma over the integers, by reduction modulo primes. -/
lemma gaussZ {σ : Type} (F0 : MvPolynomial σ ℤ) :
    ∀ n : ℕ, 0 < n → ∀ A1 B1 : MvPolynomial σ ℤ, A1 * B1 = C (n : ℤ) * F0 →
      ∃ (a : ℤ) (A0 B0 : MvPolynomial σ ℤ), a ≠ 0 ∧ A1 = C a * A0 ∧ A0 * B0 = F0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn A1 B1 h
    by_cases h1 : n = 1
    · subst h1
      exact ⟨1, A1, B1, one_ne_zero, by simp, by simpa using h⟩
    · have hl := Nat.minFac_prime h1
      have : Fact (n.minFac).Prime := ⟨hl⟩
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hm
          omega
        · exact h0
      have hmn : m < n := by
        have := hl.one_lt
        nlinarith
      have hz : map (Int.castRingHom (ZMod n.minFac)) A1 *
          map (Int.castRingHom (ZMod n.minFac)) B1 = 0 := by
        rw [← map_mul, h, map_mul, map_C]
        have h0 : (Int.castRingHom (ZMod n.minFac)) (n : ℤ) = 0 := by
          rw [eq_intCast, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
          exact Nat.minFac_dvd n
        rw [h0, map_zero, zero_mul]
      have hC : (C (n : ℤ) : MvPolynomial σ ℤ) = C ((n.minFac : ℕ) : ℤ) * C ((m : ℕ) : ℤ) := by
        rw [← C_mul]
        congr 1
        exact_mod_cast hm
      have hCne : (C ((n.minFac : ℕ) : ℤ) : MvPolynomial σ ℤ) ≠ 0 := by
        rw [Ne, C_eq_zero]
        exact_mod_cast hl.ne_zero
      rcases mul_eq_zero.mp hz with hA | hB
      · obtain ⟨A2, hA2⟩ := (C_dvd_iff_zmod _ _).mpr hA
        have h' : A2 * B1 = C ((m : ℕ) : ℤ) * F0 := by
          apply mul_left_cancel₀ hCne
          rw [← mul_assoc, ← hA2, h, hC, mul_assoc]
        obtain ⟨a, A0, B0, ha, e1, e2⟩ := ih m hmn hm0 A2 B1 h'
        refine ⟨(n.minFac : ℤ) * a, A0, B0,
          mul_ne_zero (by exact_mod_cast hl.ne_zero) ha, ?_, e2⟩
        rw [hA2, e1, C_mul, mul_assoc]
      · obtain ⟨B2, hB2⟩ := (C_dvd_iff_zmod _ _).mpr hB
        have h' : A1 * B2 = C ((m : ℕ) : ℤ) * F0 := by
          apply mul_left_cancel₀ hCne
          rw [mul_left_comm, ← hB2, h, hC, mul_assoc]
        exact ih m hmn hm0 A1 B2 h'

/-- Clearing denominators. -/
lemma clear_den {σ : Type} (A : MvPolynomial σ ℚ) :
    ∃ (d : ℕ) (A1 : MvPolynomial σ ℤ), 0 < d ∧
      C (d : ℚ) * A = map (Int.castRingHom ℚ) A1 := by
  induction A using MvPolynomial.induction_on' with
  | monomial f a =>
    refine ⟨a.den, monomial f a.num, a.den_pos, ?_⟩
    rw [C_mul_monomial, map_monomial, eq_intCast, Rat.den_mul_eq_num]
  | add p q hp hq =>
    obtain ⟨d1, P1, h1, e1⟩ := hp
    obtain ⟨d2, P2, h2, e2⟩ := hq
    refine ⟨d1 * d2, C (d2 : ℤ) * P1 + C (d1 : ℤ) * P2, Nat.mul_pos h1 h2, ?_⟩
    rw [map_add, map_mul, map_mul, map_C, map_C, ← e1, ← e2]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, C_mul]
    ring

/-- Gauss's lemma for a rational factorisation of a 0/1 polynomial. -/
lemma gaussQ {σ : Type} (A B : MvPolynomial σ ℚ) (F0 : MvPolynomial σ ℤ)
    (h : A * B = map (Int.castRingHom ℚ) F0) :
    ∃ (c : ℚ) (A0 B0 : MvPolynomial σ ℤ), c ≠ 0 ∧
      A = C c * map (Int.castRingHom ℚ) A0 ∧ A0 * B0 = F0 := by
  obtain ⟨dA, A1, hdA, eA⟩ := clear_den A
  obtain ⟨dB, B1, hdB, eB⟩ := clear_den B
  have hinj : Function.Injective (map (σ := σ) (Int.castRingHom ℚ)) :=
    map_injective _ Int.cast_injective
  have h1 : A1 * B1 = C ((dA * dB : ℕ) : ℤ) * F0 := by
    apply hinj
    rw [map_mul, map_mul, map_C, ← eA, ← eB, ← h]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, Int.cast_mul, C_mul]
    ring
  obtain ⟨a, A0, B0, ha, e1, e2⟩ := gaussZ F0 (dA * dB) (Nat.mul_pos hdA hdB) A1 B1 h1
  have hd : (dA : ℚ) ≠ 0 := by exact_mod_cast hdA.ne'
  refine ⟨a / dA, A0, B0, div_ne_zero (by exact_mod_cast ha) hd, ?_, e2⟩
  have h3 : C (dA : ℚ) * A = C (dA : ℚ) * (C (a / dA : ℚ) * map (Int.castRingHom ℚ) A0) := by
    rw [eA, e1, map_mul, map_C, ← mul_assoc, ← C_mul, eq_intCast, mul_div_cancel₀ _ hd]
  exact mul_left_cancel₀ (by rwa [Ne, C_eq_zero]) h3

/-- All weight-extremal coefficients of a rational divisor of a 0/1 polynomial have the same
absolute value. -/
lemma ext_abs {σ : Type} (A B : MvPolynomial σ ℚ) (F0 : MvPolynomial σ ℤ)
    (hF : ∀ g, coeff g F0 = 0 ∨ coeff g F0 = 1) (hF0 : F0 ≠ 0)
    (h : A * B = map (Int.castRingHom ℚ) F0) :
    ∃ c : ℚ, ∀ w : (σ →₀ ℕ) → ℚ, (∀ f g, w (f + g) = w f * w g) → (∀ f, 0 < w f) →
      Function.Injective w → ∀ fa ∈ A.support, (∀ f ∈ A.support, w f ≤ w fa) →
        |coeff fa A| = c := by
  obtain ⟨c, A0, B0, hc, eA, eAB⟩ := gaussQ A B F0 h
  have hB0 : B0 ≠ 0 := by
    rintro rfl
    exact hF0 (by rw [← eAB, mul_zero])
  have hco : ∀ f, coeff f A = c * ((coeff f A0 : ℤ) : ℚ) := by
    intro f
    rw [eA, coeff_C_mul, coeff_map, eq_intCast]
  have hsup : ∀ f, f ∈ A.support ↔ f ∈ A0.support := by
    intro f
    rw [mem_support_iff, mem_support_iff, hco]
    simp [hc]
  refine ⟨|c|, fun w hmul hpos hinj fa hfa hmax => ?_⟩
  have h1 := ext_unit w hmul hpos hinj A0 B0 F0 eAB hF hB0 fa ((hsup fa).mp hfa)
    (fun f hf => hmax f ((hsup f).mpr hf))
  have h2 : |((coeff fa A0 : ℤ) : ℚ)| = 1 := by exact_mod_cast h1
  rw [hco, abs_mul, h2, mul_one]

/-- Coefficients after the substitution `x_i ↦ c_i x_i`. -/
lemma scale_coeff {k : ℕ} (c : Fin k → ℚ) (A : MvPolynomial (Fin k) ℚ) (g : Fin k →₀ ℕ) :
    coeff g (aeval (fun i => C (c i) * X i : Fin k → MvPolynomial (Fin k) ℚ) A) =
      (∏ i, c i ^ g i) * coeff g A := by
  classical
  induction A using MvPolynomial.induction_on' with
  | monomial f a =>
    have h : aeval (fun i => C (c i) * X i : Fin k → MvPolynomial (Fin k) ℚ) (monomial f a) =
        monomial f (a * ∏ i, c i ^ f i) := by
      rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
        Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
      simp only [mul_pow, Finset.prod_mul_distrib, algebraMap_eq, C_mul, map_prod, map_pow]
      ring
    rw [h, coeff_monomial, coeff_monomial]
    split_ifs with h'
    · subst h'
      ring
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/-- Coefficients of a sum of monomials with distinct exponents. -/
lemma coeff_sum_monomial {σ R : Type} [CommSemiring R] (S : Finset (σ →₀ ℕ))
    (c : (σ →₀ ℕ) → R) (g : σ →₀ ℕ) [Decidable (g ∈ S)] :
    coeff g (∑ f ∈ S, monomial f (c f)) = if g ∈ S then c g else 0 := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs <;> rfl

/-- The weight is multiplicative. -/
lemma W_mul {k : ℕ} (c : Fin k → ℚ) (f g : Fin k →₀ ℕ) :
    ∏ i, c i ^ (f + g) i = (∏ i, c i ^ f i) * ∏ i, c i ^ g i := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.add_apply, pow_add]

/-- The weight is injective (unique factorisation). -/
lemma W_inj {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Function.Injective (fun f : Fin k →₀ ℕ => ∏ i, (p i : ℚ) ^ f i) := by
  intro f g h
  have h' : ∏ i, p i ^ f i = ∏ i, p i ^ g i := by
    have h2 : ∏ i, (p i : ℚ) ^ f i = ∏ i, (p i : ℚ) ^ g i := h
    exact_mod_cast h2
  have key : ∀ (f : Fin k →₀ ℕ) (j : Fin k), (∏ i, p i ^ f i).factorization (p j) = f j := by
    intro f j
    rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hp i).ne_zero),
      Finsupp.finsetSum_apply, Finset.sum_eq_single j]
    · rw [Nat.factorization_pow, Finsupp.smul_apply, (hp j).factorization,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    · intro i _ hij
      rw [Nat.factorization_pow, Finsupp.smul_apply, (hp i).factorization,
        Finsupp.single_apply, if_neg (fun h => hij (hinj h)), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  ext j
  rw [← key f j, ← key g j, h']

/-- The weight is positive. -/
lemma W_pos {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (g : Fin k →₀ ℕ) :
    0 < ∏ i, (p i : ℚ) ^ g i :=
  Finset.prod_pos fun i _ => pow_pos (by exact_mod_cast (hp i).pos) _

/-- The indicator polynomial of a finite set of exponents has coefficients 0 and 1. -/
lemma ind01 {σ : Type} (S : Finset (σ →₀ ℕ)) (g : σ →₀ ℕ) :
    coeff g (∑ f ∈ S, monomial f (1 : ℤ)) = 0 ∨ coeff g (∑ f ∈ S, monomial f (1 : ℤ)) = 1 := by
  classical
  rw [coeff_sum_monomial S (fun _ => (1 : ℤ)) g]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The indicator polynomial of a nonempty set is not zero. -/
lemma ind_ne {σ : Type} (S : Finset (σ →₀ ℕ)) (f : σ →₀ ℕ) (hf : f ∈ S) :
    (∑ f ∈ S, monomial f (1 : ℤ)) ≠ 0 := by
  classical
  rw [ne_zero_iff]
  refine ⟨f, ?_⟩
  rw [coeff_sum_monomial S (fun _ => (1 : ℤ)) f, if_pos hf]
  exact one_ne_zero

/-- Extremal coefficients of `Q` when a scaled copy of `Q` divides a 0/1 polynomial. -/
lemma abs_scale {k : ℕ} (c : Fin k → ℚ) (hc : ∀ i, 0 < c i) (Q B : MvPolynomial (Fin k) ℚ)
    (F0 : MvPolynomial (Fin k) ℤ) (hF : ∀ g, coeff g F0 = 0 ∨ coeff g F0 = 1) (hF0 : F0 ≠ 0)
    (h : aeval (fun i => C (c i) * X i : Fin k → MvPolynomial (Fin k) ℚ) Q * B =
      map (Int.castRingHom ℚ) F0) :
    ∃ r : ℚ, ∀ w : ((Fin k) →₀ ℕ) → ℚ, (∀ f g, w (f + g) = w f * w g) → (∀ f, 0 < w f) →
      Function.Injective w → ∀ fa ∈ Q.support, (∀ f ∈ Q.support, w f ≤ w fa) →
        (∏ i, c i ^ fa i) * |coeff fa Q| = r := by
  obtain ⟨r, hr⟩ := ext_abs _ B F0 hF hF0 h
  have hpos : ∀ g : Fin k →₀ ℕ, 0 < ∏ i, c i ^ g i :=
    fun g => Finset.prod_pos fun i _ => pow_pos (hc i) _
  have hsup : ∀ f, f ∈ (aeval (fun i => C (c i) * X i : Fin k → MvPolynomial (Fin k) ℚ)
      Q).support ↔ f ∈ Q.support := by
    intro f
    rw [mem_support_iff, mem_support_iff, scale_coeff]
    simp [(hpos f).ne']
  refine ⟨r, fun w h1 h2 h3 fa hfa hmax => ?_⟩
  have h4 := hr w h1 h2 h3 fa ((hsup fa).mpr hfa) (fun f hf => hmax f ((hsup f).mp hf))
  rw [scale_coeff, abs_mul, abs_of_pos (hpos fa)] at h4
  exact h4

/-- The substitution `x_i ↦ p_i x_i` turns the polynomial into a 0/1 polynomial. -/
lemma phi_eq {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (E : Finset (Fin k →₀ ℕ)) :
    aeval (fun i => C (p i : ℚ) * X i : Fin k → MvPolynomial (Fin k) ℚ)
      (∑ f ∈ E, monomial f (1 / ∏ i, (p i : ℚ) ^ f i)) =
    map (Int.castRingHom ℚ) (∑ f ∈ E, monomial f (1 : ℤ)) := by
  classical
  ext g
  rw [scale_coeff, coeff_sum_monomial E (fun f => 1 / ∏ i, (p i : ℚ) ^ f i) g, coeff_map,
    coeff_sum_monomial E (fun _ => (1 : ℤ)) g]
  split_ifs with h
  · rw [eq_intCast, Int.cast_one]
    exact mul_one_div_cancel (W_pos p hp g).ne'
  · simp

/-- The reciprocal polynomial as a sum over the reflected exponents. -/
lemma recip_eq {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (E : Finset (Fin k →₀ ℕ))
    (D : Fin k →₀ ℕ) (hle : ∀ f ∈ E, f ≤ D) :
    (∑ f ∈ E, monomial (D - f) (1 / ∏ i, (p i : ℚ) ^ f i) : MvPolynomial (Fin k) ℚ) =
    ∑ g ∈ E.image (fun f => D - f),
      monomial g ((∏ i, (p i : ℚ) ^ g i) / ∏ i, (p i : ℚ) ^ D i) := by
  classical
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun f hf => ?_
    congr 1
    have h1 := W_mul (fun i => (p i : ℚ)) f (D - f)
    rw [add_tsub_cancel_of_le (hle f hf)] at h1
    rw [h1]
    have h2 := (W_pos p hp f).ne'
    have h3 := (W_pos p hp (D - f)).ne'
    field_simp
  · intro a ha b hb hab
    have h1 : D - (D - a) = D - (D - b) := congrArg (fun x => D - x) hab
    rwa [tsub_tsub_cancel_of_le (hle a ha), tsub_tsub_cancel_of_le (hle b hb)] at h1

/-- The substitution `x_i ↦ x_i / p_i` turns the reciprocal polynomial into a constant times a
0/1 polynomial. -/
lemma psi_eq {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (E : Finset (Fin k →₀ ℕ))
    (D : Fin k →₀ ℕ) (hle : ∀ f ∈ E, f ≤ D) :
    C (∏ i, (p i : ℚ) ^ D i) *
      aeval (fun i => C ((p i : ℚ)⁻¹) * X i : Fin k → MvPolynomial (Fin k) ℚ)
        (∑ f ∈ E, monomial (D - f) (1 / ∏ i, (p i : ℚ) ^ f i)) =
    map (Int.castRingHom ℚ) (∑ g ∈ E.image (fun f => D - f), monomial g (1 : ℤ)) := by
  classical
  rw [recip_eq p hp E D hle]
  ext g
  rw [coeff_C_mul, scale_coeff,
    coeff_sum_monomial (E.image (fun f => D - f))
      (fun g => (∏ i, (p i : ℚ) ^ g i) / ∏ i, (p i : ℚ) ^ D i) g, coeff_map,
    coeff_sum_monomial (E.image (fun f => D - f)) (fun _ => (1 : ℤ)) g]
  split_ifs with h
  · rw [eq_intCast, Int.cast_one]
    have h1 : ∏ i, ((p i : ℚ)⁻¹) ^ g i = (∏ i, (p i : ℚ) ^ g i)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [inv_pow]
    rw [h1]
    have h2 := (W_pos p hp g).ne'
    have h3 := (W_pos p hp D).ne'
    field_simp
  · simp

/-- Two positive weights with `a x = b y` and `x / a = y / b` are equal. -/
lemma arith (a b x y : ℚ) (ha : 0 < a) (hb : 0 < b) (hy : 0 < y)
    (e1 : a * x = b * y) (e2 : a⁻¹ * x = b⁻¹ * y) : a = b := by
  have e3 : x * b = y * a := by
    calc x * b = (a⁻¹ * x) * (a * b) := by field_simp
      _ = (b⁻¹ * y) * (a * b) := by rw [e2]
      _ = y * a := by field_simp
  have e4 : a ^ 2 * y = b ^ 2 * y := by linear_combination (-a) * e3 + b * e1
  have e5 : a ^ 2 = b ^ 2 := mul_right_cancel₀ hy.ne' e4
  exact (pow_left_inj₀ ha.le hb.le two_ne_zero).mp e5

/-- The two relations between the extremal coefficients force `Q` to be a unit. -/
lemma final {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (Q H1 P1 : MvPolynomial (Fin k) ℚ) (hP1 : P1 = Q * H1) (h0 : coeff 0 P1 ≠ 0) (c1 c2 : ℚ)
    (hc1 : ∀ w : ((Fin k) →₀ ℕ) → ℚ, (∀ f g, w (f + g) = w f * w g) → (∀ f, 0 < w f) →
      Function.Injective w → ∀ fa ∈ Q.support, (∀ f ∈ Q.support, w f ≤ w fa) →
        (∏ i, (p i : ℚ) ^ fa i) * |coeff fa Q| = c1)
    (hc2 : ∀ w : ((Fin k) →₀ ℕ) → ℚ, (∀ f g, w (f + g) = w f * w g) → (∀ f, 0 < w f) →
      Function.Injective w → ∀ fa ∈ Q.support, (∀ f ∈ Q.support, w f ≤ w fa) →
        (∏ i, ((p i : ℚ)⁻¹) ^ fa i) * |coeff fa Q| = c2) : IsUnit Q := by
  classical
  have Wpos := W_pos p hp
  have Wmul := W_mul (fun i => (p i : ℚ))
  have Winj := W_inj p hp hinj
  have hQ : Q ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hP1
    rw [hP1] at h0
    simp at h0
  have hne : Q.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hQ (support_eq_empty.mp h))
  obtain ⟨fa, hfa, hmaxa⟩ := Finset.exists_max_image Q.support
    (fun f : Fin k →₀ ℕ => ∏ i, (p i : ℚ) ^ f i) hne
  obtain ⟨ga, hga, hming⟩ := Finset.exists_min_image Q.support
    (fun f : Fin k →₀ ℕ => ∏ i, (p i : ℚ) ^ f i) hne
  have hinv : ∀ g : Fin k →₀ ℕ, ∏ i, ((p i : ℚ)⁻¹) ^ g i = (∏ i, (p i : ℚ) ^ g i)⁻¹ := by
    intro g
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [inv_pow]
  have n1 : ∀ f g : Fin k →₀ ℕ, (∏ i, (p i : ℚ) ^ (f + g) i)⁻¹ =
      (∏ i, (p i : ℚ) ^ f i)⁻¹ * (∏ i, (p i : ℚ) ^ g i)⁻¹ := by
    intro f g
    rw [Wmul, mul_inv]
  have n2 : ∀ f : Fin k →₀ ℕ, 0 < (∏ i, (p i : ℚ) ^ f i)⁻¹ := fun f => inv_pos.mpr (Wpos f)
  have n3 : Function.Injective (fun f : Fin k →₀ ℕ => (∏ i, (p i : ℚ) ^ f i)⁻¹) :=
    fun f g h => Winj (inv_injective h)
  have n4 : ∀ f ∈ Q.support, (∏ i, (p i : ℚ) ^ f i)⁻¹ ≤ (∏ i, (p i : ℚ) ^ ga i)⁻¹ :=
    fun f hf => inv_anti₀ (Wpos ga) (hming f hf)
  have a1 := hc1 _ Wmul Wpos Winj fa hfa hmaxa
  have a2 := hc1 _ n1 n2 n3 ga hga n4
  have b1 := hc2 _ Wmul Wpos Winj fa hfa hmaxa
  have b2 := hc2 _ n1 n2 n3 ga hga n4
  rw [hinv] at b1 b2
  have hy : 0 < |coeff ga Q| := abs_pos.mpr (mem_support_iff.mp hga)
  have e4 : ∏ i, (p i : ℚ) ^ fa i = ∏ i, (p i : ℚ) ^ ga i :=
    arith _ _ _ _ (Wpos fa) (Wpos ga) hy (a1.trans a2.symm) (b1.trans b2.symm)
  have hall : ∀ f ∈ Q.support, f = fa := by
    intro f hf
    apply Winj
    refine le_antisymm (hmaxa f hf) ?_
    have h1 := hming f hf
    simp only at h1 ⊢
    rw [e4]
    exact h1
  have hQm : Q = monomial fa (coeff fa Q) := by
    ext g
    rw [coeff_monomial]
    split_ifs with h
    · rw [h]
    · by_contra h2
      exact h (hall g (mem_support_iff.mpr h2)).symm
  have hfa0 : fa = 0 := by
    rw [hP1, hQm, coeff_monomial_mul'] at h0
    by_contra h
    apply h0
    rw [if_neg]
    intro hle
    exact h (le_zero_iff.mp hle)
  subst hfa0
  rw [hQm]
  exact (isUnit_iff_ne_zero.mpr (mem_support_iff.mp hfa)).map C

/-- The polynomial and its reciprocal have only unit common divisors. -/
lemma rel {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (E : Finset (Fin k →₀ ℕ)) (D : Fin k →₀ ℕ) (h0 : 0 ∈ E) (hle : ∀ f ∈ E, f ≤ D)
    (Q : MvPolynomial (Fin k) ℚ)
    (hQ1 : Q ∣ ∑ f ∈ E, monomial f (1 / ∏ i, (p i : ℚ) ^ f i))
    (hQ2 : Q ∣ ∑ f ∈ E, monomial (D - f) (1 / ∏ i, (p i : ℚ) ^ f i)) : IsUnit Q := by
  classical
  obtain ⟨H1, e1⟩ := hQ1
  obtain ⟨H2, e2⟩ := hQ2
  have hphi := phi_eq p hp E
  rw [e1, map_mul] at hphi
  have hpsi := psi_eq p hp E D hle
  rw [e2, map_mul, mul_left_comm] at hpsi
  obtain ⟨c1, hc1⟩ := abs_scale (fun i => (p i : ℚ)) (fun i => by exact_mod_cast (hp i).pos)
    Q _ _ (ind01 E) (ind_ne E 0 h0) hphi
  obtain ⟨c2, hc2⟩ := abs_scale (fun i => (p i : ℚ)⁻¹)
    (fun i => inv_pos.mpr (by exact_mod_cast (hp i).pos))
    Q _ _ (ind01 _) (ind_ne _ (D - 0) (Finset.mem_image_of_mem _ h0)) hpsi
  refine final p hp hinj Q H1 _ e1 ?_ c1 c2 hc1 hc2
  rw [coeff_sum_monomial E (fun f => 1 / ∏ i, (p i : ℚ) ^ f i) 0, if_pos h0]
  simp

end OMA.E967FH4

theorem OMA.solution : OMA.R_Erdos967_erdos_967_variants_finite_R1.H4 := by
  intro k p hp hinj E D h0 hle Q hQ1 hQ2
  exact OMA.E967FH4.rel p hp hinj E D h0 hle Q hQ1 hQ2
