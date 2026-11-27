import OMAReductions.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1
import Mathlib.Data.Nat.GCD.BigOperators
-- Step Erdos1099.erdos_1099.variants.lcm.R1.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos1099.erdos_1099.variants.lcm.R1.H1.R1.H2.R1
-- Credit: @<your GitHub handle>

open Real Finset

private lemma norm_one_add_exp_mul_I (θ : ℝ) :
    ‖(1 : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)‖ = 2 * |Real.cos (θ / 2)| := by
  have h1 : (1 : ℂ) + Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
        (Complex.exp ((-(θ / 2) : ℝ) * Complex.I) + Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) := by
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · have : (((θ / 2 : ℝ) : ℂ) * Complex.I + (-(θ / 2) : ℝ) * Complex.I) = 0 := by
        push_cast; ring
      rw [this, Complex.exp_zero]
    · congr 1; push_cast; ring
  have h2 : Complex.exp ((-(θ / 2) : ℝ) * Complex.I) + Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.cos (θ / 2) : ℝ) : ℂ) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

private lemma divisors_prime_mul {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hcop : p.Coprime m) :
    (p * m).divisors = m.divisors ∪ m.divisors.image (p * ·) := by
  ext d
  simp only [Nat.mem_divisors, mem_union, mem_image]
  constructor
  · rintro ⟨hd, hne⟩
    by_cases hpd : p ∣ d
    · right
      obtain ⟨q, rfl⟩ := hpd
      refine ⟨q, ⟨?_, hm⟩, rfl⟩
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp hd
    · left
      refine ⟨?_, hm⟩
      exact (hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_left hd
  · rintro (⟨hd, _⟩ | ⟨q, ⟨hq, _⟩, rfl⟩)
    · exact ⟨hd.trans (dvd_mul_left m p), mul_ne_zero hp.ne_zero hm⟩
    · exact ⟨mul_dvd_mul_left p hq, mul_ne_zero hp.ne_zero hm⟩

private lemma disjoint_divisors_image {p m : ℕ} (hp : p.Prime) (hcop : p.Coprime m) :
    Disjoint m.divisors (m.divisors.image (p * ·)) := by
  rw [Finset.disjoint_left]
  intro d hd1 hd2
  obtain ⟨q, _, rfl⟩ := mem_image.mp hd2
  have hpm : p ∣ m := (dvd_mul_right p q).trans (Nat.dvd_of_mem_divisors hd1)
  exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hpm)

private lemma prime_sq_not_dvd_lcm_Icc {k p : ℕ} (hp : p.Prime) (hgt : k.sqrt < p) :
    ¬ p ^ 2 ∣ (Icc 1 k).lcm id := by
  have hklt : k < p ^ 2 := by
    have := Nat.lt_succ_sqrt k
    have hp1 : k.sqrt + 1 ≤ p := hgt
    nlinarith [Nat.sqrt_le k]
  have haux : ∀ S : Finset ℕ, (∀ i ∈ S, 1 ≤ i ∧ i ≤ k) → ¬ p ^ 2 ∣ S.lcm id := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ h
      rw [Finset.lcm_empty] at h
      have : p ^ 2 ≤ 1 := Nat.le_of_dvd one_pos h
      nlinarith [hp.two_le]
    | @insert a s has ih =>
      intro hS h
      rw [Finset.lcm_insert] at h
      have ha := hS a (mem_insert_self a s)
      have hs : ¬ p ^ 2 ∣ s.lcm id := ih (fun i hi => hS i (mem_insert_of_mem hi))
      have ha2 : ¬ p ^ 2 ∣ a := fun hdvd =>
        absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
      have hlcm : p ^ 2 ∣ Nat.lcm a (s.lcm id) := h
      have hne1 : a ≠ 0 := by omega
      have hne2 : s.lcm id ≠ 0 :=
        lcm_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt ((hS i (mem_insert_of_mem hi)).1)
      have hfac := (hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hne1 hne2)).mp hlcm
      rw [Nat.factorization_lcm hne1 hne2, Finsupp.sup_apply] at hfac
      rcases le_max_iff.mp hfac with h1 | h2
      · exact ha2 ((hp.pow_dvd_iff_le_factorization hne1).mpr h1)
      · exact hs ((hp.pow_dvd_iff_le_factorization hne2).mpr h2)
  exact haux (Icc 1 k) (fun i hi => mem_Icc.mp hi)

private lemma div_sum_factor (s : ℝ) :
    ∀ (S : Finset ℕ) (M : ℕ), M ≠ 0 →
      (∀ p ∈ S, p.Prime ∧ p.Coprime M) →
      ((∏ p ∈ S, p) * M).divisors.card = 2 ^ S.card * M.divisors.card ∧
      ‖∑ d ∈ ((∏ p ∈ S, p) * M).divisors, Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ =
        (∏ p ∈ S, (2 * |Real.cos (s * Real.log (p : ℝ) / 2)|)) *
          ‖∑ d ∈ M.divisors, Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro M _ _
    simp
  | @insert p S hpS ih =>
    intro M hM hcond
    have hp := (hcond p (mem_insert_self p S)).1
    have hpM := (hcond p (mem_insert_self p S)).2
    have hS : ∀ q ∈ S, q.Prime ∧ q.Coprime M := fun q hq => hcond q (mem_insert_of_mem hq)
    have hprod_ne : (∏ q ∈ S, q) * M ≠ 0 := by
      refine mul_ne_zero ?_ hM
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      exact (hS q hq).1.ne_zero
    have hp_cop : p.Coprime ((∏ q ∈ S, q) * M) := by
      refine Nat.Coprime.mul_right ?_ hpM
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hqp : p ≠ q := fun h => hpS (h ▸ hq)
      exact (hp.coprime_iff_not_dvd).mpr fun hd =>
        hqp (((Nat.prime_dvd_prime_iff_eq hp (hS q hq).1).mp hd))
    obtain ⟨ih_card, ih_norm⟩ := ih M hM hS
    rw [Finset.prod_insert hpS, mul_assoc, divisors_prime_mul hp hprod_ne hp_cop]
    have hdisj := disjoint_divisors_image hp hp_cop
    constructor
    · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero),
        ← two_mul, ih_card, Finset.card_insert_of_notMem hpS, pow_succ', mul_assoc]
    · rw [Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h => mul_left_cancel₀ hp.ne_zero h)]
      have hterm : ∑ d ∈ ((∏ q ∈ S, q) * M).divisors,
            Complex.exp (((s * Real.log ((p * d : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((s * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) *
            ∑ d ∈ ((∏ q ∈ S, q) * M).divisors,
              Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
        have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        rw [Nat.cast_mul, Real.log_mul hp0 hd0, mul_add, ← Complex.exp_add]
        congr 1; push_cast; ring
      rw [hterm, ← one_add_mul, norm_mul, norm_one_add_exp_mul_I, ih_norm,
        Finset.prod_insert hpS, mul_assoc]
      ring

theorem OMA.solution : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1.H2 := by
  intro k hk s y
  let P := (Ioc k.sqrt k).filter Nat.Prime
  let L := Nat.lcmUpto k
  have hL_eq : L = (Icc 1 k).lcm id := rfl
  have hL_ne : L ≠ 0 := by
    rw [hL_eq]
    exact lcm_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt (mem_Icc.mp hi).1
  have hP_dvd : ∀ p ∈ P, p ∣ L := by
    intro p hp
    have hp' := mem_filter.mp hp
    have hmem : p ∈ Icc 1 k := mem_Icc.mpr ⟨hp'.2.one_lt.le, (mem_Ioc.mp hp'.1).2⟩
    rw [hL_eq]
    exact Finset.dvd_lcm (f := id) hmem
  have hQ_dvd : (∏ p ∈ P, p) ∣ L := by
    refine Finset.prod_dvd_of_isRelPrime ?_ hP_dvd
    intro p hp q hq hpq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    exact Nat.coprime_iff_isRelPrime.mp (hp'.coprime_iff_not_dvd.mpr fun h =>
      hpq ((Nat.prime_dvd_prime_iff_eq hp' hq').mp h))
  obtain ⟨M, hM_eq⟩ := hQ_dvd
  have hM_ne : M ≠ 0 := fun h => hL_ne (by rw [hM_eq, h, mul_zero])
  have hP_cop : ∀ p ∈ P, p.Prime ∧ p.Coprime M := by
    intro p hp
    have hp' := mem_filter.mp hp
    refine ⟨hp'.2, hp'.2.coprime_iff_not_dvd.mpr fun hpm => ?_⟩
    have hsq : p ^ 2 ∣ L := by
      rw [hM_eq, sq]
      exact mul_dvd_mul (Finset.dvd_prod_of_mem _ hp) hpm
    exact prime_sq_not_dvd_lcm_Icc hp'.2 (mem_Ioc.mp hp'.1).1 (hL_eq ▸ hsq)
  obtain ⟨hcard, hnorm⟩ := div_sum_factor s P M hM_ne hP_cop
  rw [← hM_eq] at hcard hnorm
  have hre : ∑ d ∈ L.divisors, Real.cos (s * (Real.log (d : ℝ) - y)) =
      (Complex.exp (((-(s * y) : ℝ) : ℂ) * Complex.I) *
        ∑ d ∈ L.divisors, Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Complex.exp_add]
    have harg : (((-(s * y) : ℝ) : ℂ) * Complex.I + ((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I) =
        (((s * (Real.log (d : ℝ) - y) : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_ofReal_mul_I_re]
  have hM_bound : ‖∑ d ∈ M.divisors, Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (M.divisors.card : ℝ) := by
    calc
      ‖∑ d ∈ M.divisors, Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)‖
          ≤ ∑ d ∈ M.divisors, ‖Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ :=
            norm_sum_le _ _
      _ = ∑ _d ∈ M.divisors, (1 : ℝ) :=
            Finset.sum_congr rfl fun d _ => Complex.norm_exp_ofReal_mul_I _
      _ = (M.divisors.card : ℝ) := by simp
  have hprod_cos : ∏ p ∈ P, |Real.cos (s * Real.log (p : ℝ) / 2)| ≤
      Real.exp (-(∑ p ∈ P, (1 - |Real.cos (s * Real.log (p : ℝ) / 2)|))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p _ => ?_
    have := Real.add_one_le_exp (-(1 - |Real.cos (s * Real.log (p : ℝ) / 2)|))
    linarith
  have hprod_split : ∏ p ∈ P, (2 * |Real.cos (s * Real.log (p : ℝ) / 2)|) =
      (2 : ℝ) ^ P.card * ∏ p ∈ P, |Real.cos (s * Real.log (p : ℝ) / 2)| := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  calc
    |∑ d ∈ L.divisors, Real.cos (s * (Real.log (d : ℝ) - y))|
        = |(Complex.exp (((-(s * y) : ℝ) : ℂ) * Complex.I) *
            ∑ d ∈ L.divisors, Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)).re| := by
          rw [hre]
    _ ≤ ‖Complex.exp (((-(s * y) : ℝ) : ℂ) * Complex.I) *
          ∑ d ∈ L.divisors, Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ :=
          Complex.abs_re_le_norm _
    _ = ‖∑ d ∈ L.divisors, Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ := by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ = (∏ p ∈ P, (2 * |Real.cos (s * Real.log (p : ℝ) / 2)|)) *
          ‖∑ d ∈ M.divisors, Complex.exp (((s * Real.log (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ := hnorm
    _ ≤ (∏ p ∈ P, (2 * |Real.cos (s * Real.log (p : ℝ) / 2)|)) * (M.divisors.card : ℝ) :=
          mul_le_mul_of_nonneg_left hM_bound (Finset.prod_nonneg fun _ _ => by positivity)
    _ = ((2 : ℝ) ^ P.card * (M.divisors.card : ℝ)) *
          (∏ p ∈ P, |Real.cos (s * Real.log (p : ℝ) / 2)|) := by
          rw [hprod_split]; ring
    _ = (L.divisors.card : ℝ) * (∏ p ∈ P, |Real.cos (s * Real.log (p : ℝ) / 2)|) := by
          rw [hcard]; push_cast; rfl
    _ ≤ (L.divisors.card : ℝ) *
          Real.exp (-(∑ p ∈ P, (1 - |Real.cos (s * Real.log (p : ℝ) / 2)|))) :=
          mul_le_mul_of_nonneg_left hprod_cos (Nat.cast_nonneg _)

