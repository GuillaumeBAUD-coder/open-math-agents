import OMAReductions.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1

-- Problem: Pfister's problem on the Pythagoras number of R(X_1, ..., X_n) (step R1.H2, Cassels 1964)
-- Credit: @luciusacarr

section

open Polynomial

private lemma formally_real_mvpoly {k n : ℕ} (p : Fin n → MvPolynomial (Fin k) ℝ)
    (hp : ∑ i, p i * p i = 0) : ∀ i, p i = 0 := by
  have hev : ∀ (x : Fin k → ℝ) (i : Fin n), MvPolynomial.eval x (p i) = 0 := by
    intro x
    have hsum : ∑ i : Fin n, MvPolynomial.eval x (p i) ^ 2 = 0 := by
      have h0 := congrArg (MvPolynomial.eval x) hp
      simpa [map_sum, map_mul, pow_two] using h0
    have hsq := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 hsum
    exact fun i => sq_eq_zero_iff.1 (hsq i (Finset.mem_univ i))
  intro i
  exact MvPolynomial.funext fun x => by simpa using hev x i

private lemma formally_real_mvratfunc {k n : ℕ} (c : Fin n → MvRatFunc (Fin k) ℝ)
    (hc : ∑ i, c i * c i = 0) : ∀ i, c i = 0 := by
  choose num den hden hfrac using fun i => IsFractionRing.div_surjective (MvPolynomial (Fin k) ℝ) (c i)
  let B : MvPolynomial (Fin k) ℝ := ∏ j : Fin n, den j
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => mem_nonZeroDivisors_iff_ne_zero.1 (hden j)
  let p : Fin n → MvPolynomial (Fin k) ℝ := fun i => num i * ∏ j ∈ Finset.univ.erase i, den j
  have hp_eq : ∀ i, algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) (p i) =
      algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) B * c i := by
    intro i
    have hBi : B = den i * ∏ j ∈ Finset.univ.erase i, den j := by
      dsimp only [B]
      rw [← Finset.mul_prod_erase Finset.univ den (Finset.mem_univ i)]
    have hdi0 : algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) (den i) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
        (mem_nonZeroDivisors_iff_ne_zero.1 (hden i))
    rw [← hfrac i]
    simp only [p, map_mul, map_prod, hBi]
    field_simp [hdi0]
  have hp_sum : ∑ i, p i * p i = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ)
    simp only [map_sum, map_mul, map_zero]
    have hmul : ∑ i : Fin n, algebraMap _ (MvRatFunc (Fin k) ℝ) (p i) *
          algebraMap _ (MvRatFunc (Fin k) ℝ) (p i) =
        algebraMap _ (MvRatFunc (Fin k) ℝ) B * algebraMap _ (MvRatFunc (Fin k) ℝ) B *
          ∑ i : Fin n, c i * c i := by
      simp only [hp_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hc, mul_zero] at hmul
    exact hmul
  have hp0 := formally_real_mvpoly p hp_sum
  have hBK : algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) B ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hB
  intro i
  have hmul := hp_eq i
  rw [hp0 i, map_zero] at hmul
  exact (mul_eq_zero.1 hmul.symm).resolve_left hBK

private lemma coeff_two_mul_sq {K : Type*} [CommRing K] {D : ℕ} {f : Polynomial K}
    (hf : f.natDegree ≤ D) : (f * f).coeff (2 * D) = f.coeff D * f.coeff D := by
  rw [Polynomial.coeff_mul]
  rw [Finset.sum_eq_single (D, D)]
  · rintro ⟨a, b⟩ hab hne
    have hab' : a + b = 2 * D := by simpa using hab
    have hne' : a ≠ D ∨ b ≠ D := by
      by_contra h
      push Not at h
      exact hne (Prod.ext h.1 h.2)
    have hcases : D < a ∨ D < b := by omega
    rcases hcases with ha | hb
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf ha), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf hb), mul_zero]
  · intro h
    exfalso
    apply h
    simp [Nat.two_mul]

private lemma formally_real_poly {k n : ℕ} (s : Fin n → Polynomial (MvRatFunc (Fin k) ℝ))
    (hs : ∑ i, s i * s i = 0) : ∀ i, s i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i0, hi0⟩ := hne
  let D : ℕ := Finset.univ.sup fun i => (s i).natDegree
  have hle : ∀ i, (s i).natDegree ≤ D := fun i =>
    Finset.le_sup (f := fun i => (s i).natDegree) (Finset.mem_univ i)
  have hsum : ∑ i : Fin n, (s i).coeff D * (s i).coeff D = 0 := by
    have hcoeff := congrArg (fun p => Polynomial.coeff p (2 * D)) hs
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hcoeff
    have hsq : ∑ i : Fin n, (s i * s i).coeff (2 * D) =
        ∑ i : Fin n, (s i).coeff D * (s i).coeff D :=
      Finset.sum_congr rfl fun i _ => coeff_two_mul_sq (hle i)
    rwa [hsq] at hcoeff
  have hc0 := formally_real_mvratfunc (fun i => (s i).coeff D) hsum
  have hD_mem : ∃ i, (s i).natDegree = D := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i0, Finset.mem_univ i0⟩
      (fun i => (s i).natDegree)
    exact ⟨j, hj.symm⟩
  obtain ⟨j, hj⟩ := hD_mem
  have hj0 : s j ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hj
    have hle0 := hle i0
    rw [← hj] at hle0
    have hdeg0 : (s i0).natDegree = 0 := Nat.eq_zero_of_le_zero hle0
    have hs0 := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hc_i0 := hc0 i0
    rw [← hj] at hc_i0
    exact hi0 (by rw [hs0, hc_i0, map_zero])
  have hlead := hc0 j
  rw [← hj] at hlead
  exact hj0 (Polynomial.leadingCoeff_eq_zero.1 hlead)

private lemma cassels_deg_zero {k m : ℕ} (fK : MvRatFunc (Fin k) ℝ)
    (q : Polynomial (MvRatFunc (Fin k) ℝ)) (hq0 : q ≠ 0) (hq_deg : q.natDegree = 0)
    (p : Fin (m + 1) → Polynomial (MvRatFunc (Fin k) ℝ))
    (heq : q * q * (Polynomial.C fK + Polynomial.X ^ 2) = ∑ i, p i * p i) :
    IsSumSqOfLength m fK := by
  obtain ⟨c, rfl⟩ : ∃ c : MvRatFunc (Fin k) ℝ, q = Polynomial.C c :=
    ⟨q.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hq_deg⟩
  have hc0 : c ≠ 0 := by simpa using hq0
  have hp_deg : ∀ i : Fin (m + 1), (p i).natDegree ≤ 1 := by
    by_contra hgt
    push Not at hgt
    let D : ℕ := Finset.univ.sup fun i => (p i).natDegree
    have hD2 : 2 ≤ D := by
      obtain ⟨i1, hi1⟩ := hgt
      exact le_trans hi1 (Finset.le_sup (f := fun i => (p i).natDegree) (Finset.mem_univ i1))
    have hle : ∀ i, (p i).natDegree ≤ D := fun i =>
      Finset.le_sup (f := fun i => (p i).natDegree) (Finset.mem_univ i)
    have hA_deg : (Polynomial.C c * Polynomial.C c * (Polynomial.C fK + Polynomial.X ^ 2)).natDegree ≤ 2 := by
      calc
        (Polynomial.C c * Polynomial.C c * (Polynomial.C fK + Polynomial.X ^ 2)).natDegree
            ≤ (Polynomial.C c * Polynomial.C c).natDegree + (Polynomial.C fK + Polynomial.X ^ 2).natDegree :=
              Polynomial.natDegree_mul_le
        _ ≤ 0 + max (Polynomial.C fK).natDegree (Polynomial.X ^ 2).natDegree := by
              gcongr
              · rw [← Polynomial.C_mul, Polynomial.natDegree_C]
              · exact Polynomial.natDegree_add_le _ _
        _ ≤ 2 := by simp [Polynomial.natDegree_C]
    have hcoeff0 : (Polynomial.C c * Polynomial.C c * (Polynomial.C fK + Polynomial.X ^ 2)).coeff (2 * D) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hsum : ∑ i : Fin (m + 1), (p i).coeff D * (p i).coeff D = 0 := by
      have hc := congrArg (fun r => Polynomial.coeff r (2 * D)) heq
      rw [hcoeff0, Polynomial.finsetSum_coeff] at hc
      have hsq : ∑ i : Fin (m + 1), (p i * p i).coeff (2 * D) =
          ∑ i : Fin (m + 1), (p i).coeff D * (p i).coeff D :=
        Finset.sum_congr rfl fun i _ => coeff_two_mul_sq (hle i)
      exact hsq.symm.trans hc.symm
    have hc_zero := formally_real_mvratfunc (fun i => (p i).coeff D) hsum
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i => (p i).natDegree)
    have hj0 : p j ≠ 0 := by
      intro hz
      rw [hz, Polynomial.natDegree_zero] at hj
      omega
    have hlead := hc_zero j
    dsimp only [D] at hlead
    rw [hj] at hlead
    exact hj0 (Polynomial.leadingCoeff_eq_zero.1 hlead)
  let a0 : Fin (m + 1) → MvRatFunc (Fin k) ℝ := fun i => (p i).coeff 1
  let b : Fin (m + 1) → MvRatFunc (Fin k) ℝ := fun i => (p i).coeff 0
  have hp_form : ∀ i, p i = Polynomial.C (a0 i) * Polynomial.X + Polynomial.C (b i) := by
    intro i
    ext n
    rcases n with _ | _ | n
    · simp [b]
    · simp [a0]
    · have := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hp_deg i) (by omega : 1 < n + 2))
      simp [this]
  have hL_eq : Polynomial.C c * Polynomial.C c * (Polynomial.C fK + Polynomial.X ^ 2) =
      Polynomial.C (c * c * fK) + Polynomial.C (c * c) * Polynomial.X ^ 2 := by
    rw [← Polynomial.C_mul, mul_add, ← Polynomial.C_mul]
  have hp_sq : ∀ i, p i * p i =
      Polynomial.C (a0 i * a0 i) * Polynomial.X ^ 2 +
      Polynomial.C (2 * (a0 i * b i)) * Polynomial.X +
      Polynomial.C (b i * b i) := by
    intro i
    rw [hp_form i]
    have h1 : (Polynomial.C (a0 i) * Polynomial.X + Polynomial.C (b i)) *
        (Polynomial.C (a0 i) * Polynomial.X + Polynomial.C (b i)) =
        (Polynomial.C (a0 i) * Polynomial.C (a0 i)) * Polynomial.X ^ 2 +
        (2 * (Polynomial.C (a0 i) * Polynomial.C (b i))) * Polynomial.X +
        Polynomial.C (b i) * Polynomial.C (b i) := by ring
    rw [h1, ← Polynomial.C_mul, ← Polynomial.C_mul, ← Polynomial.C_mul]
    have h2 : (2 : Polynomial (MvRatFunc (Fin k) ℝ)) = Polynomial.C 2 :=
      (Polynomial.C_ofNat (R := MvRatFunc (Fin k) ℝ) 2).symm
    rw [h2, ← Polynomial.C_mul]
  have coeff_C_X_pow (r : MvRatFunc (Fin k) ℝ) (n : ℕ) :
      (Polynomial.C r * Polynomial.X ^ 2).coeff n = if n = 2 then r else 0 :=
    Polynomial.coeff_C_mul_X_pow r 2 n
  have coeff_C_X (r : MvRatFunc (Fin k) ℝ) (n : ℕ) :
      (Polynomial.C r * Polynomial.X).coeff n = if n = 1 then r else 0 :=
    Polynomial.coeff_C_mul_X r n
  have ha_sq : c * c = ∑ i : Fin (m + 1), a0 i * a0 i := by
    have h2 := congrArg (fun r => Polynomial.coeff r 2) heq
    have hlhs : (Polynomial.C c * Polynomial.C c * (Polynomial.C fK + Polynomial.X ^ 2)).coeff 2 = c * c := by
      rw [hL_eq]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C, coeff_C_X_pow, ↓reduceIte,
        OfNat.ofNat_ne_zero, zero_add]
    have hrhs : (∑ i : Fin (m + 1), p i * p i).coeff 2 = ∑ i : Fin (m + 1), a0 i * a0 i := by
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp_sq i]
      simp only [Polynomial.coeff_add, coeff_C_X_pow, coeff_C_X, Polynomial.coeff_C, ↓reduceIte,
        OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, add_zero]
    rw [← hlhs, ← hrhs, h2]
  have hab : ∑ i : Fin (m + 1), a0 i * b i = 0 := by
    have h1 := congrArg (fun r => Polynomial.coeff r 1) heq
    have hlhs : (Polynomial.C c * Polynomial.C c * (Polynomial.C fK + Polynomial.X ^ 2)).coeff 1 = 0 := by
      rw [hL_eq]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C, coeff_C_X_pow, one_ne_zero,
        OfNat.one_ne_ofNat, ↓reduceIte, add_zero]
    have hrhs : (∑ i : Fin (m + 1), p i * p i).coeff 1 = 2 * ∑ i : Fin (m + 1), a0 i * b i := by
      rw [Polynomial.finsetSum_coeff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp_sq i]
      simp only [Polynomial.coeff_add, coeff_C_X_pow, coeff_C_X, Polynomial.coeff_C,
        OfNat.one_ne_ofNat, ↓reduceIte, one_ne_zero, zero_add, add_zero]
    rw [hlhs, hrhs] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (by norm_num)
  have hb_sq : c * c * fK = ∑ i : Fin (m + 1), b i * b i := by
    have h0 := congrArg (fun r => Polynomial.coeff r 0) heq
    have hlhs : (Polynomial.C c * Polynomial.C c * (Polynomial.C fK + Polynomial.X ^ 2)).coeff 0 = c * c * fK := by
      rw [hL_eq]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C, coeff_C_X_pow, ↓reduceIte,
        OfNat.zero_ne_ofNat, add_zero]
    have hrhs : (∑ i : Fin (m + 1), p i * p i).coeff 0 = ∑ i : Fin (m + 1), b i * b i := by
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp_sq i]
      simp only [Polynomial.coeff_add, coeff_C_X_pow, coeff_C_X, Polynomial.coeff_C,
        OfNat.zero_ne_ofNat, zero_ne_one, ↓reduceIte, zero_add]
    rw [← hlhs, ← hrhs, h0]
  have hsign : ∃ a : Fin (m + 1) → MvRatFunc (Fin k) ℝ,
      c * c = ∑ i, a i * a i ∧ ∑ i, a i * b i = 0 ∧ a 0 + c ≠ 0 := by
    by_cases hpos : a0 0 + c ≠ 0
    · exact ⟨a0, ha_sq, hab, hpos⟩
    · refine ⟨fun i => -a0 i, ?_, ?_, ?_⟩
      · simp only [neg_mul_neg]; exact ha_sq
      · simp only [neg_mul, Finset.sum_neg_distrib, neg_eq_zero]; exact hab
      · push Not at hpos
        intro hneg
        have h2c : (2 : MvRatFunc (Fin k) ℝ) * c = 0 := by linear_combination hpos + hneg
        exact hc0 ((mul_eq_zero.1 h2c).resolve_left (by norm_num))
  obtain ⟨a, ha_sq', hab', hh⟩ := hsign
  set h : MvRatFunc (Fin k) ℝ := a 0 + c
  let v : Fin (m + 1) → MvRatFunc (Fin k) ℝ := fun i => a i + if i = 0 then c else 0
  let t : MvRatFunc (Fin k) ℝ := b 0 / h
  let w : Fin (m + 1) → MvRatFunc (Fin k) ℝ := fun i => b i - t * v i
  have hv_sq : ∑ i : Fin (m + 1), v i * v i = 2 * c * h := by
    have hexp : ∑ i : Fin (m + 1), v i * v i =
        (∑ i : Fin (m + 1), a i * a i) + 2 * c * a 0 + c * c := by
      have hsub : ∀ i : Fin (m + 1), v i * v i =
          a i * a i + (if i = 0 then 2 * c * a 0 + c * c else 0) := by
        intro i
        by_cases hi : i = 0
        · subst hi; simp [v]; ring
        · simp [v, hi]
      simp_rw [hsub]
      simp [Finset.sum_add_distrib]
      ring
    rw [hexp, ← ha_sq']
    dsimp [h]
    ring
  have hvb : ∑ i : Fin (m + 1), v i * b i = c * b 0 := by
    have hsub : ∀ i : Fin (m + 1), v i * b i = a i * b i + (if i = 0 then c * b 0 else 0) := by
      intro i
      by_cases hi : i = 0
      · subst hi; simp [v]; ring
      · simp [v, hi]
    simp_rw [hsub]
    simp [Finset.sum_add_distrib, hab']
  have hw_sq : ∑ i : Fin (m + 1), w i * w i = c * c * fK := by
    have hexp : ∑ i : Fin (m + 1), w i * w i =
        (∑ i : Fin (m + 1), b i * b i) - 2 * t * (∑ i : Fin (m + 1), v i * b i) +
          t * t * (∑ i : Fin (m + 1), v i * v i) := by
      have hsub : ∀ i : Fin (m + 1), w i * w i =
          b i * b i - 2 * t * (v i * b i) + t * t * (v i * v i) := by
        intro i; dsimp [w]; ring
      simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hexp, ← hb_sq, hvb, hv_sq]
    dsimp [t, h]
    have hh' : a 0 + c ≠ 0 := hh
    change (c * c * fK - 2 * (b 0 / (a 0 + c)) * (c * b 0) +
      (b 0 / (a 0 + c)) * (b 0 / (a 0 + c)) * (2 * c * (a 0 + c))) = c * c * fK
    field_simp [hh']
    ring
  have hw0 : w 0 = 0 := by
    dsimp [w, v, t, h]
    have hh' : a 0 + c ≠ 0 := hh
    change b 0 - b 0 / (a 0 + c) * (a 0 + c) = 0
    rw [div_mul_cancel₀ _ hh', sub_self]
  refine ⟨fun j => w j.succ / c, ?_⟩
  rw [Fin.sum_univ_succ, hw0, zero_mul, zero_add] at hw_sq
  have hc0' : c ≠ 0 := hc0
  have hrhs_eq : ∑ j : Fin m, (w j.succ / c) * (w j.succ / c) =
      (∑ j : Fin m, w j.succ * w j.succ) / (c * c) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrhs_eq, hw_sq, mul_div_cancel_left₀ _ (mul_ne_zero hc0' hc0')]

private lemma cassels_descent {k m : ℕ} (fK : MvRatFunc (Fin k) ℝ)
    (q : Polynomial (MvRatFunc (Fin k) ℝ)) (hq0 : q ≠ 0) (hq1 : 1 ≤ q.natDegree)
    (p : Fin (m + 1) → Polynomial (MvRatFunc (Fin k) ℝ))
    (heq : q * q * (Polynomial.C fK + Polynomial.X ^ 2) = ∑ i, p i * p i) :
    ∃ q' : Polynomial (MvRatFunc (Fin k) ℝ), q' ≠ 0 ∧ q'.natDegree < q.natDegree ∧
      ∃ p' : Fin (m + 1) → Polynomial (MvRatFunc (Fin k) ℝ),
        q' * q' * (Polynomial.C fK + Polynomial.X ^ 2) = ∑ i, p' i * p' i := by
  let K := MvRatFunc (Fin k) ℝ
  let A : Polynomial K := Polynomial.C fK + Polynomial.X ^ 2
  let r : Fin (m + 1) → Polynomial K := fun i => p i / q
  let s : Fin (m + 1) → Polynomial K := fun i => p i % q
  have hdiv : ∀ i, p i = q * r i + s i := fun i => (EuclideanDomain.div_add_mod (p i) q).symm
  by_cases hs0 : ∀ i, s i = 0
  · refine ⟨1, one_ne_zero, by simpa using (by omega : 0 < q.natDegree), r, ?_⟩
    have hmul : q * q * A = q * q * ∑ i : Fin (m + 1), r i * r i := by
      rw [heq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hp_eq : p i = q * r i := by simpa [hs0 i] using hdiv i
      rw [hp_eq]; ring
    simpa using mul_left_cancel₀ (mul_ne_zero hq0 hq0) hmul
  · have hs_ne : ∃ i, s i ≠ 0 := by push Not at hs0; exact hs0
    let S : Polynomial K := ∑ i, s i * s i
    have hS0 : S ≠ 0 := by
      intro hS
      obtain ⟨i0, hi0⟩ := hs_ne
      exact hi0 (formally_real_poly s hS i0)
    have hS_deg : S.natDegree < 2 * q.natDegree := by
      have hs_deg : ∀ i : Fin (m + 1), (s i * s i).natDegree ≤ 2 * (q.natDegree - 1) := by
        intro i
        by_cases hsi : s i = 0
        · simp [hsi]
        · have hlt : (s i).natDegree < q.natDegree :=
            Polynomial.natDegree_mod_lt (p i) (by omega : q.natDegree ≠ 0)
          rw [Polynomial.natDegree_mul hsi hsi]
          omega
      calc
        S.natDegree ≤ Finset.fold max 0 (Polynomial.natDegree ∘ fun i => s i * s i) Finset.univ :=
          Polynomial.natDegree_sum_le Finset.univ _
        _ ≤ 2 * (q.natDegree - 1) := by
          rw [Finset.fold_max_le]
          refine ⟨by omega, fun i _ => hs_deg i⟩
        _ < 2 * q.natDegree := by omega
    let QV : Polynomial K := A - ∑ i, r i * r i
    let BUV : Polynomial K := 2 * (A * q - ∑ i, p i * r i)
    let q' : Polynomial K := QV * q - BUV
    let p' : Fin (m + 1) → Polynomial K := fun i => QV * p i - BUV * r i
    have hQ_new : q' * q' * A = ∑ i, p' i * p' i := by
      have hid : q' * q' * A - ∑ i, p' i * p' i =
          QV * QV * (q * q * A - ∑ i, p i * p i) -
          QV * BUV * (2 * (A * q - ∑ i, p i * r i) - BUV) +
          BUV * BUV * ((A - ∑ i, r i * r i) - QV) := by
        have hsub : ∀ i, p' i * p' i =
            QV * QV * (p i * p i) - 2 * QV * BUV * (p i * r i) + BUV * BUV * (r i * r i) := by
          intro i; dsimp [p']; ring
        simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        dsimp [q']
        ring
      have hzero : q' * q' * A - ∑ i, p' i * p' i = 0 := by
        rw [hid, heq]
        dsimp [QV, BUV]
        ring
      exact sub_eq_zero.1 hzero
    have hprod : -q' * q = S := by
      have hid : -q' * q = (q * q * A - ∑ i, p i * p i) + ∑ i, (p i - q * r i) * (p i - q * r i) := by
        have hsub : ∀ i, (p i - q * r i) * (p i - q * r i) =
            p i * p i - 2 * q * (p i * r i) + q * q * (r i * r i) := by
          intro i; ring
        simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        dsimp [q', QV, BUV]
        ring
      rw [hid, heq, sub_self, zero_add]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsi : p i - q * r i = s i := by
        have := hdiv i
        linear_combination this
      rw [hsi]
    have hq'0 : q' ≠ 0 := by
      intro hz
      rw [hz, neg_zero, zero_mul] at hprod
      exact hS0 hprod.symm
    have hdeg_lt : q'.natDegree < q.natDegree := by
      have hm := Polynomial.natDegree_mul (neg_ne_zero.2 hq'0) hq0
      rw [Polynomial.natDegree_neg, hprod] at hm
      omega
    exact ⟨q', hq'0, hdeg_lt, p', hQ_new⟩

private lemma finRotate_castSucc {k : ℕ} (j : Fin k) :
    finRotate (k + 1) (Fin.castSucc j) = j.succ := by
  ext
  simp

private lemma eval_G_eq (k : ℕ) (f : MvPolynomial (Fin k) ℝ) :
    let α : MvPolynomial (Fin (k + 1)) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin k) ℝ) :=
      (MvPolynomial.renameEquiv ℝ (finRotate (k + 1))).trans (MvPolynomial.finSuccEquiv ℝ k)
    let Φ : MvPolynomial (Fin (k + 1)) ℝ →+* Polynomial (MvRatFunc (Fin k) ℝ) :=
      (Polynomial.mapRingHom (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ))).comp
        α.toRingHom
    Φ (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2) =
      Polynomial.C (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) f) + Polynomial.X ^ 2 := by
  intro α Φ
  have hXlast : α (MvPolynomial.X (Fin.last k)) = Polynomial.X := by
    change MvPolynomial.finSuccEquiv ℝ k
      (MvPolynomial.rename (finRotate (k + 1)) (MvPolynomial.X (Fin.last k))) = Polynomial.X
    rw [MvPolynomial.rename_X, finRotate_last, MvPolynomial.finSuccEquiv_X_zero]
  have hren : α (MvPolynomial.rename Fin.castSucc f) = Polynomial.C f := by
    induction f using MvPolynomial.induction_on with
    | C a =>
        rw [MvPolynomial.rename_C]
        change α (algebraMap ℝ (MvPolynomial (Fin (k + 1)) ℝ) a) = Polynomial.C (algebraMap ℝ _ a)
        rw [AlgEquiv.commutes]
        rfl
    | add u v hu hv =>
        rw [map_add, map_add, hu, hv, Polynomial.C_add]
    | mul_X u j hu =>
        rw [map_mul, map_mul, hu, MvPolynomial.rename_X]
        have hXj : α (MvPolynomial.X (Fin.castSucc j)) = Polynomial.C (MvPolynomial.X j) := by
          change MvPolynomial.finSuccEquiv ℝ k
            (MvPolynomial.rename (finRotate (k + 1)) (MvPolynomial.X (Fin.castSucc j))) =
            Polynomial.C (MvPolynomial.X j)
          rw [MvPolynomial.rename_X, finRotate_castSucc, MvPolynomial.finSuccEquiv_X_succ]
        rw [hXj, ← Polynomial.C_mul]
  have hG : α (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2) =
      Polynomial.C f + Polynomial.X ^ 2 := by
    rw [map_add, map_pow, hren, hXlast]
  change Polynomial.map (algebraMap _ _)
    (α (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2)) = _
  rw [hG, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]

end

theorem OMA.solution : OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1.H2 := by
  intro k m f hnot hsq
  obtain ⟨g, hg⟩ := hsq
  choose num den hden hfrac using fun i =>
    IsFractionRing.div_surjective (MvPolynomial (Fin (k + 1)) ℝ) (g i)
  let Q : MvPolynomial (Fin (k + 1)) ℝ := ∏ j : Fin (m + 1), den j
  have hQ0 : Q ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => mem_nonZeroDivisors_iff_ne_zero.1 (hden j)
  let P : Fin (m + 1) → MvPolynomial (Fin (k + 1)) ℝ :=
    fun i => num i * ∏ j ∈ Finset.univ.erase i, den j
  let G : MvPolynomial (Fin (k + 1)) ℝ :=
    MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2
  have hP_eq : ∀ i, algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ) (P i) =
      algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ) Q * g i := by
    intro i
    have hQi : Q = den i * ∏ j ∈ Finset.univ.erase i, den j := by
      dsimp only [Q]
      rw [← Finset.mul_prod_erase Finset.univ den (Finset.mem_univ i)]
    have hdi0 : algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ) (den i) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
        (mem_nonZeroDivisors_iff_ne_zero.1 (hden i))
    rw [← hfrac i]
    simp only [P, map_mul, map_prod, hQi]
    field_simp [hdi0]
  have hpoly_eq : Q * Q * G = ∑ i : Fin (m + 1), P i * P i := by
    apply IsFractionRing.injective (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)
    simp only [map_sum, map_mul]
    calc
      algebraMap _ _ Q * algebraMap _ _ Q * algebraMap _ _ G
          = algebraMap _ _ Q * algebraMap _ _ Q * ∑ i : Fin (m + 1), g i * g i := by
              rw [hg]
      _ = ∑ i : Fin (m + 1), algebraMap _ _ (P i) * algebraMap _ _ (P i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hP_eq i]
          ring
  let α : MvPolynomial (Fin (k + 1)) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin k) ℝ) :=
    (MvPolynomial.renameEquiv ℝ (finRotate (k + 1))).trans (MvPolynomial.finSuccEquiv ℝ k)
  let Φ : MvPolynomial (Fin (k + 1)) ℝ →+* Polynomial (MvRatFunc (Fin k) ℝ) :=
    (Polynomial.mapRingHom (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ))).comp
      α.toRingHom
  have hΦ_inj : Function.Injective Φ :=
    (Polynomial.map_injective _
      (IsFractionRing.injective (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ))).comp α.injective
  have hΦ_G : Φ G = Polynomial.C (algebraMap _ _ f) + Polynomial.X ^ 2 := eval_G_eq k f
  have hsol : ∃ q : Polynomial (MvRatFunc (Fin k) ℝ), q ≠ 0 ∧
      ∃ p : Fin (m + 1) → Polynomial (MvRatFunc (Fin k) ℝ),
        q * q * (Polynomial.C (algebraMap _ _ f) + Polynomial.X ^ 2) = ∑ i, p i * p i := by
    refine ⟨Φ Q, fun h => hQ0 (hΦ_inj (by simpa using h)), fun i => Φ (P i), ?_⟩
    have hmap := congrArg Φ hpoly_eq
    simpa only [map_mul, map_sum, hΦ_G] using hmap
  have hex_deg : ∃ d : ℕ, ∃ q : Polynomial (MvRatFunc (Fin k) ℝ), q ≠ 0 ∧ q.natDegree = d ∧
      ∃ p : Fin (m + 1) → Polynomial (MvRatFunc (Fin k) ℝ),
        q * q * (Polynomial.C (algebraMap _ _ f) + Polynomial.X ^ 2) = ∑ i, p i * p i := by
    obtain ⟨q, hq0, p, hp⟩ := hsol
    exact ⟨q.natDegree, q, hq0, rfl, p, hp⟩
  classical
  let d := Nat.find hex_deg
  obtain ⟨q, hq0, hq_deg, p, heq⟩ := Nat.find_spec hex_deg
  rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
  · exact hnot (cassels_deg_zero (algebraMap _ _ f) q hq0 (by omega) p heq)
  · obtain ⟨q', hq'0, hlt, p', heq'⟩ := cassels_descent (algebraMap _ _ f) q hq0 (by omega) p heq
    exact Nat.find_min hex_deg (hq_deg ▸ hlt) ⟨q', hq'0, rfl, p', heq'⟩
