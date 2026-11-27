import FormalConjectures.ErdosProblems.«375»

/-!
Erdős Problem 375 — bounded gap

Elementary self-contained proof that Grimm's conjecture (`Erdos375.Erdos375Prop`) implies
`p_{n+1} - p_n < p_n ^ (1 / 2 - c)` for `c = 1 / 200` and all sufficiently large `n`.

The proof counts 3-factor `y`-smooth integers `a * b * c ∈ (x, x + z]` with
`z = ⌊x ^ (49 / 100)⌋₊`, `A = ⌊x ^ (17 / 40)⌋₊`, `B = ⌊x ^ (15 / 100)⌋₊`, `y = ⌊8 * x ^ (17 / 40)⌋₊`,
using a quartic Fejér kernel minorant, Weyl-van der Corput differencing,
a discrete Kusmin-Landau exponential sum bound, and an elementary divisor bound `d(m) ≤ C * m ^ ε`.
-/

open Filter Finset

namespace OMA.Erdos375BoundedGap

/- Section 1: Elementary exponential e(t) and trigonometric helpers -/

private noncomputable def e (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private lemma e_zero : e 0 = 1 := by
  simp [e]

private lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma e_neg (x : ℝ) : e (-x) = starRingEnd ℂ (e x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma e_sub (x y : ℝ) : e (x - y) = e x * starRingEnd ℂ (e y) := by
  rw [sub_eq_add_neg, e_add, e_neg]

private lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

private lemma e_nat_mul (j : ℕ) (x : ℝ) : e ((j : ℝ) * x) = (e x) ^ j := by
  induction j with
  | zero => simp [e_zero]
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, e_add, ih, pow_succ]

private lemma e_re (x : ℝ) : (e x).re = Real.cos (2 * Real.pi * x) := by
  unfold e
  exact Complex.exp_ofReal_mul_I_re (2 * Real.pi * x)

private lemma e_im (x : ℝ) : (e x).im = Real.sin (2 * Real.pi * x) := by
  unfold e
  exact Complex.exp_ofReal_mul_I_im (2 * Real.pi * x)

private lemma norm_e_sub_one (t : ℝ) : ‖e t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have hsq : Complex.normSq (e t - 1) = (2 * |Real.sin (Real.pi * t)|) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, e_re, e_im]
    have h2 : 2 * Real.pi * t = 2 * (Real.pi * t) := by ring
    rw [h2, Real.cos_two_mul, Real.sin_two_mul]
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * t)
    rw [mul_pow, sq_abs]
    nlinarith [sq_nonneg (Real.sin (Real.pi * t)), sq_nonneg (Real.cos (Real.pi * t))]
  rw [Complex.norm_def, hsq, Real.sqrt_sq (by positivity)]

private lemma abs_sin_pi_ge_of_dist_int (t δ : ℝ) (h : ∀ m : ℤ, δ / 2 ≤ |t - m|) :
    δ ≤ |Real.sin (Real.pi * t)| := by
  set m : ℤ := ⌊t + 1 / 2⌋
  set r : ℝ := t - m
  have hr1 : -(1 / 2 : ℝ) ≤ r := by
    have : (m : ℝ) ≤ t + 1 / 2 := Int.floor_le (t + 1 / 2)
    linarith
  have hr2 : r < 1 / 2 := by
    have : t + 1 / 2 < (m : ℝ) + 1 := Int.lt_floor_add_one (t + 1 / 2)
    linarith
  have habs_r : |r| ≤ 1 / 2 := abs_le.mpr ⟨hr1, hr2.le⟩
  have hlow : δ / 2 ≤ |r| := h m
  have hsin_eq : |Real.sin (Real.pi * t)| = |Real.sin (Real.pi * r)| := by
    have ht : Real.pi * t = Real.pi * r + (m : ℤ) * Real.pi := by
      simp only [r]
      ring
    rw [ht, Real.sin_add_int_mul_pi, abs_mul]
    have h1 : |((-1 : ℝ) ^ m)| = 1 := by
      rw [abs_zpow, abs_neg, abs_one, one_zpow]
    rw [h1, one_mul]
  rw [hsin_eq]
  have hpi_r : |Real.pi * r| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hJ := Real.mul_abs_le_abs_sin hpi_r
  rw [abs_mul, abs_of_pos Real.pi_pos] at hJ
  have hcalc : 2 / Real.pi * (Real.pi * |r|) = 2 * |r| := by
    field_simp [Real.pi_pos.ne']
  linarith

/- Section 2: Quartic Fejér kernel minorant -/

private noncomputable def D (K : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range K, e ((j : ℝ) * t)

private lemma norm_D_le (K : ℕ) (t : ℝ) : ‖D K t‖ ≤ K := by
  calc ‖D K t‖ ≤ ∑ j ∈ Finset.range K, ‖e ((j : ℝ) * t)‖ := norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range K, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun j _ => norm_e _
    _ = K := by simp

private lemma norm_D_le_inv_sin (K : ℕ) (t : ℝ) (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖D K t‖ ≤ 1 / |Real.sin (Real.pi * t)| := by
  have hD : D K t = ∑ j ∈ Finset.range K, (e t) ^ j := by
    unfold D
    exact Finset.sum_congr rfl fun j _ => e_nat_mul j t
  have hne : e t ≠ 1 := by
    intro heq
    have h0 : ‖e t - 1‖ = 0 := by simp [heq]
    rw [norm_e_sub_one] at h0
    have : |Real.sin (Real.pi * t)| = 0 := by linarith
    exact hsin (abs_eq_zero.mp this)
  rw [hD, geom_sum_eq hne, norm_div, norm_e_sub_one]
  have hnum : ‖(e t) ^ K - 1‖ ≤ 2 := by
    calc ‖(e t) ^ K - 1‖ ≤ ‖(e t) ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖e t‖ ^ K + 1 := by rw [norm_pow, norm_one]
      _ = 2 := by rw [norm_e, one_pow]; norm_num
  have hpos : 0 < |Real.sin (Real.pi * t)| := abs_pos.mpr hsin
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith

open Classical in
private lemma quartic_fejer_minorant (K : ℕ) (hK : 0 < K) (u δ : ℝ) (hδ : 0 < δ) :
    ‖D K (u + δ / 2)‖ ^ 4 / (K : ℝ) ^ 4 - 1 / ((K : ℝ) * δ) ^ 4 ≤
      if ∃ m : ℤ, u < (m : ℝ) ∧ (m : ℝ) < u + δ then (1 : ℝ) else 0 := by
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  split_ifs with hex
  · have h1 : ‖D K (u + δ / 2)‖ ^ 4 / (K : ℝ) ^ 4 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_D_le K _) 4
    have h2 : (0 : ℝ) ≤ 1 / ((K : ℝ) * δ) ^ 4 := by positivity
    linarith
  · have hdist : ∀ m : ℤ, δ / 2 ≤ |(u + δ / 2) - m| := by
      intro m
      by_contra! hlt
      rw [abs_lt] at hlt
      exact hex ⟨m, by linarith, by linarith⟩
    have hsin_ge : δ ≤ |Real.sin (Real.pi * (u + δ / 2))| :=
      abs_sin_pi_ge_of_dist_int (u + δ / 2) δ hdist
    have hsin_ne : Real.sin (Real.pi * (u + δ / 2)) ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hsin_ge
      linarith
    have hD_le : ‖D K (u + δ / 2)‖ ≤ 1 / δ := by
      calc ‖D K (u + δ / 2)‖ ≤ 1 / |Real.sin (Real.pi * (u + δ / 2))| :=
            norm_D_le_inv_sin K _ hsin_ne
        _ ≤ 1 / δ := one_div_le_one_div_of_le hδ hsin_ge
    have h4 : ‖D K (u + δ / 2)‖ ^ 4 ≤ (1 / δ) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) hD_le 4
    have hdiv : ‖D K (u + δ / 2)‖ ^ 4 / (K : ℝ) ^ 4 ≤ 1 / ((K : ℝ) * δ) ^ 4 := by
      calc ‖D K (u + δ / 2)‖ ^ 4 / (K : ℝ) ^ 4
          ≤ (1 / δ) ^ 4 / (K : ℝ) ^ 4 := div_le_div_of_nonneg_right h4 (by positivity)
        _ = 1 / ((K : ℝ) * δ) ^ 4 := by field_simp
    linarith

private lemma card_eq_sum_pairs_ge (K : ℕ) (hK : 0 < K) :
    (K : ℝ) ^ 3 / 2 ≤
      ((((Finset.range K ×ˢ Finset.range K) ×ˢ (Finset.range K ×ˢ Finset.range K)).filter
        (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2)).card : ℝ) := by
  let P := Finset.range K ×ˢ Finset.range K
  let fiber (s : ℕ) := P.filter (fun p => p.1 + p.2 = s)
  have hmaps : ∀ p ∈ P, p.1 + p.2 ∈ Finset.range (2 * K) := by
    intro p hp
    simp only [P, Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  have hsum_card : ∑ s ∈ Finset.range (2 * K), ((fiber s).card : ℝ) = (K : ℝ) ^ 2 := by
    have hnat : ∑ s ∈ Finset.range (2 * K), (fiber s).card = P.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise hmaps
    have hP : P.card = K * K := by simp [P]
    have h1 : (∑ s ∈ Finset.range (2 * K), ((fiber s).card : ℝ)) = ((K * K : ℕ) : ℝ) := by
      exact_mod_cast hnat.trans hP
    rw [h1]; push_cast; ring
  have hdiag_card :
      ((P ×ˢ P).filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2)).card =
        ∑ s ∈ Finset.range (2 * K), (fiber s).card ^ 2 := by
    have hmaps4 : ∀ t ∈ (P ×ˢ P).filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2),
        t.1.1 + t.1.2 ∈ Finset.range (2 * K) := by
      intro t ht
      exact hmaps t.1 (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1
    rw [Finset.card_eq_sum_card_fiberwise hmaps4]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hEq :
        ((P ×ˢ P).filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2)).filter
          (fun t => t.1.1 + t.1.2 = s) = fiber s ×ˢ fiber s := by
      ext ⟨p1, p2⟩
      simp only [fiber, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, heq⟩, hs⟩
        exact ⟨⟨h1, hs⟩, h2, heq.symm.trans hs⟩
      · rintro ⟨⟨h1, hs1⟩, h2, hs2⟩
        exact ⟨⟨⟨h1, h2⟩, hs1.trans hs2.symm⟩, hs1⟩
    rw [hEq, Finset.card_product, sq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (2 * K))
    (fun _ => (1 : ℝ)) (fun s => ((fiber s).card : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  rw [hsum_card] at hcs
  have hdiagR :
      (((P ×ˢ P).filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2)).card : ℝ) =
        ∑ s ∈ Finset.range (2 * K), ((fiber s).card : ℝ) ^ 2 := by
    exact_mod_cast hdiag_card
  rw [hdiagR]
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  push_cast at hcs
  nlinarith

private lemma norm_D_pow_four_eq (K : ℕ) (θ : ℝ) :
    ‖D K θ‖ ^ 4 =
      (∑ t ∈ (Finset.range K ×ˢ Finset.range K) ×ˢ (Finset.range K ×ˢ Finset.range K),
        e ((((t.1.1 + t.1.2 : ℤ) - (t.2.1 + t.2.2 : ℤ)) : ℝ) * θ)).re := by
  have hcomplex :
      ((‖D K θ‖ ^ 4 : ℝ) : ℂ) =
        (D K θ * D K θ) * (starRingEnd ℂ (D K θ) * starRingEnd ℂ (D K θ)) := by
    have hmul : (D K θ) * starRingEnd ℂ (D K θ) = ((‖D K θ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h4 : ((‖D K θ‖ ^ 4 : ℝ) : ℂ) = (((‖D K θ‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
      push_cast; ring
    rw [h4, ← hmul]; ring
  have hconj : starRingEnd ℂ (D K θ) = ∑ j ∈ Finset.range K, e (-((j : ℝ) * θ)) := by
    unfold D
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (e_neg _).symm
  have hprod1 : D K θ * D K θ =
      ∑ p ∈ Finset.range K ×ˢ Finset.range K, e (((p.1 : ℝ) + (p.2 : ℝ)) * θ) := by
    unfold D
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← e_add]
    congr 1; ring
  have hprod2 : starRingEnd ℂ (D K θ) * starRingEnd ℂ (D K θ) =
      ∑ p ∈ Finset.range K ×ˢ Finset.range K, e (-(((p.1 : ℝ) + (p.2 : ℝ)) * θ)) := by
    rw [hconj, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← e_add]
    congr 1; ring
  have htot :
      ((‖D K θ‖ ^ 4 : ℝ) : ℂ) =
        ∑ t ∈ (Finset.range K ×ˢ Finset.range K) ×ˢ (Finset.range K ×ˢ Finset.range K),
          e ((((t.1.1 + t.1.2 : ℤ) - (t.2.1 + t.2.2 : ℤ)) : ℝ) * θ) := by
    rw [hcomplex, hprod1, hprod2, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← e_add]
    congr 1
    push_cast
    ring
  rw [← Complex.ofReal_re (‖D K θ‖ ^ 4), htot]

private lemma sum_norm_D_pow_four_ge (K : ℕ) (hK : 0 < K) (I : Finset ℕ) (f : ℕ → ℝ)
    (shift E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ h : ℤ, h ≠ 0 → |h| < 2 * (K : ℤ) → ‖∑ a ∈ I, e ((h : ℝ) * f a)‖ ≤ E) :
    (I.card : ℝ) / (2 * (K : ℝ)) - E ≤ (∑ a ∈ I, ‖D K (f a + shift)‖ ^ 4) / (K : ℝ) ^ 4 := by
  let Q4 := (Finset.range K ×ˢ Finset.range K) ×ˢ (Finset.range K ×ˢ Finset.range K)
  let hh (t : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ := (t.1.1 + t.1.2 : ℤ) - (t.2.1 + t.2.2 : ℤ)
  have hsum_eq :
      ∑ a ∈ I, ‖D K (f a + shift)‖ ^ 4 =
        ∑ t ∈ Q4, (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re := by
    trans ∑ a ∈ I, (∑ t ∈ Q4, e ((hh t : ℝ) * (f a + shift))).re
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [norm_D_pow_four_eq]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [hh]
      push_cast
      rfl
    · simp only [Complex.re_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← e_add]
      congr 2; ring
  rw [hsum_eq]
  let S0 := Q4.filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2)
  let S1 := Q4.filter (fun t => t.1.1 + t.1.2 ≠ t.2.1 + t.2.2)
  have hsplit :
      ∑ t ∈ Q4, (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re =
        ∑ t ∈ S0, (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re +
        ∑ t ∈ S1, (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re :=
    (Finset.sum_filter_add_sum_filter_not Q4
      (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2)
      (fun t => (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re)).symm
  rw [hsplit]
  have hS0 : (K : ℝ) ^ 3 / 2 * (I.card : ℝ) ≤
      ∑ t ∈ S0, (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re := by
    have hval : ∀ t ∈ S0,
        (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re = (I.card : ℝ) := by
      intro t ht
      have heq : t.1.1 + t.1.2 = t.2.1 + t.2.2 := (Finset.mem_filter.mp ht).2
      have h0 : hh t = 0 := by simp only [hh]; omega
      simp [h0, e_zero]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_eq_sum_pairs_ge K hK) (Nat.cast_nonneg _)
  have hS1 : -((K : ℝ) ^ 4 * E) ≤
      ∑ t ∈ S1, (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re := by
    have hterm : ∀ t ∈ S1,
        -E ≤ (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re := by
      intro t ht
      have hmem : t ∈ Q4 := (Finset.mem_filter.mp ht).1
      have hne_nat : t.1.1 + t.1.2 ≠ t.2.1 + t.2.2 := (Finset.mem_filter.mp ht).2
      have hne : hh t ≠ 0 := by simp only [hh]; omega
      have habs : |hh t| < 2 * (K : ℤ) := by
        simp only [Q4, Finset.mem_product, Finset.mem_range] at hmem
        simp only [hh]
        rw [abs_lt]
        omega
      have hb := hbound (hh t) hne habs
      have hre : -(‖e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)‖) ≤
          (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re := by
        have := Complex.abs_re_le_norm (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a))
        linarith [neg_abs_le (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re]
      rw [norm_mul, norm_e, one_mul] at hre
      linarith
    have hsum_ge : -((S1.card : ℝ) * E) ≤
        ∑ t ∈ S1, (e ((hh t : ℝ) * shift) * ∑ a ∈ I, e ((hh t : ℝ) * f a)).re := by
      calc -((S1.card : ℝ) * E) = ∑ _t ∈ S1, (-E) := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hterm
    have hcard_le : (S1.card : ℝ) ≤ (K : ℝ) ^ 4 := by
      have h1 : S1.card ≤ Q4.card := Finset.card_filter_le _ _
      have h2 : Q4.card = K * K * (K * K) := by simp [Q4]
      have h3 : (S1.card : ℝ) ≤ ((K * K * (K * K) : ℕ) : ℝ) := by
        exact_mod_cast h1.trans_eq h2
      push_cast at h3
      linarith [show (K : ℝ) * (K : ℝ) * ((K : ℝ) * (K : ℝ)) = (K : ℝ) ^ 4 by ring]
    nlinarith
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  rw [le_div_iff₀ (by positivity)]
  have hlhs : ((I.card : ℝ) / (2 * (K : ℝ)) - E) * (K : ℝ) ^ 4 =
      (K : ℝ) ^ 3 / 2 * (I.card : ℝ) - (K : ℝ) ^ 4 * E := by
    field_simp [hKpos.ne']
  linarith

/- Section 3: Discrete Kusmin-Landau exponential sum bound -/

private lemma sum_by_parts_aux (u w : ℕ → ℂ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), u k * (w (k + 1) - w k) =
      u m * w (m + 1) - u 0 * w 0 +
        ∑ k ∈ Finset.range m, (u k - u (k + 1)) * w (k + 1) := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

private lemma sum_by_parts_complex (u w : ℕ → ℂ) (L : ℕ) (hL : 1 ≤ L) :
    ∑ k ∈ Finset.range L, u k * (w (k + 1) - w k) =
      u (L - 1) * w L - u 0 * w 0 +
        ∑ k ∈ Finset.range (L - 1), (u k - u (k + 1)) * w (k + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  simpa using sum_by_parts_aux u w m

private lemma kusmin_landau (g : ℕ → ℝ) (M L : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (hlam_half : lam ≤ 1 / 2)
    (hlow : ∀ k < L, lam ≤ g (M + k + 1) - g (M + k))
    (hhigh : ∀ k < L, g (M + k + 1) - g (M + k) ≤ 1 / 2)
    (hdec : ∀ k, k + 1 < L → g (M + k + 2) - g (M + k + 1) ≤ g (M + k + 1) - g (M + k)) :
    ‖∑ k ∈ Finset.range (L + 1), e (g (M + k))‖ ≤ 2 / lam := by
  by_cases hL0 : L = 0
  · subst hL0
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, add_zero, norm_e]
    rw [le_div_iff₀ hlam]
    linarith
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL0
  rw [Finset.sum_range_succ]
  have hsplit : ‖(∑ k ∈ Finset.range L, e (g (M + k))) + e (g (M + L))‖ ≤
      ‖∑ k ∈ Finset.range L, e (g (M + k))‖ + 1 := by
    calc _ ≤ ‖∑ k ∈ Finset.range L, e (g (M + k))‖ + ‖e (g (M + L))‖ := norm_add_le _ _
      _ = _ := by rw [norm_e]
  let Δ (k : ℕ) : ℝ := g (M + k + 1) - g (M + k)
  let cotPi (t : ℝ) : ℝ := Real.cos (Real.pi * t) / Real.sin (Real.pi * t)
  let u (k : ℕ) : ℂ := ((-1 / 2 : ℝ) : ℂ) + Complex.I * ((-cotPi (Δ k) / 2 : ℝ) : ℂ)
  let w (k : ℕ) : ℂ := e (g (M + k))
  have hsin_ge : ∀ k < L, 2 * lam ≤ Real.sin (Real.pi * Δ k) := by
    intro k hk
    have h1 : 0 ≤ Real.pi * Δ k := by nlinarith [hlow k hk, Real.pi_pos]
    have h2 : Real.pi * Δ k ≤ Real.pi / 2 := by nlinarith [hhigh k hk, Real.pi_pos]
    have hJ := Real.mul_le_sin h1 h2
    have hcalc : 2 / Real.pi * (Real.pi * Δ k) = 2 * Δ k := by field_simp [Real.pi_pos.ne']
    linarith [hlow k hk]
  have hsin_pos : ∀ k < L, 0 < Real.sin (Real.pi * Δ k) := fun k hk =>
    lt_of_lt_of_le (by linarith) (hsin_ge k hk)
  have hcos_nonneg : ∀ k < L, 0 ≤ Real.cos (Real.pi * Δ k) := by
    intro k hk
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [hlow k hk, hhigh k hk, Real.pi_pos]
  have hterm : ∀ k ∈ Finset.range L, w k = u k * (w (k + 1) - w k) := by
    intro k hk
    have hk' : k < L := Finset.mem_range.mp hk
    have hsp : Real.sin (Real.pi * Δ k) ≠ 0 := (hsin_pos k hk').ne'
    have hwd : w (k + 1) - w k = w k * (e (Δ k) - 1) := by
      simp only [w, Δ]
      have hg : g (M + (k + 1)) = g (M + k) + (g (M + k + 1) - g (M + k)) := by
        have : M + (k + 1) = M + k + 1 := by omega
        rw [this]; ring
      rw [hg, e_add]; ring
    rw [hwd, ← mul_assoc, mul_comm (u k) (w k), mul_assoc]
    suffices h1 : u k * (e (Δ k) - 1) = 1 by rw [h1, mul_one]
    apply Complex.ext
    · simp only [u, cotPi, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, e_re, e_im,
        sub_zero, zero_mul, one_mul, mul_zero, add_zero, zero_add]
      have h2 : 2 * Real.pi * Δ k = 2 * (Real.pi * Δ k) := by ring
      rw [h2, Real.cos_two_mul, Real.sin_two_mul]
      field_simp [hsp]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * Δ k)]
    · simp only [u, cotPi, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, e_re, e_im,
        sub_zero, zero_mul, one_mul, mul_zero, add_zero, zero_add]
      have h2 : 2 * Real.pi * Δ k = 2 * (Real.pi * Δ k) := by ring
      rw [h2, Real.cos_two_mul, Real.sin_two_mul]
      field_simp [hsp]
      linear_combination -2 * Real.cos (Real.pi * Δ k) * Real.sin_sq_add_cos_sq (Real.pi * Δ k)
  have hsum_sbp :
      ∑ k ∈ Finset.range L, w k =
        u (L - 1) * w L - u 0 * w 0 +
          ∑ k ∈ Finset.range (L - 1), (u k - u (k + 1)) * w (k + 1) := by
    rw [Finset.sum_congr rfl hterm]
    exact sum_by_parts_complex u w L hL1
  have hnorm_u : ∀ k < L, ‖u k‖ ≤ 1 / (4 * lam) := by
    intro k hk
    have hsp := hsin_pos k hk
    have hsq : Complex.normSq (u k) = (1 / (2 * Real.sin (Real.pi * Δ k))) ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [u, cotPi, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        zero_mul, one_mul, mul_zero, add_zero, zero_add, sub_zero]
      field_simp [hsp.ne']
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * Δ k)]
    rw [Complex.norm_def, hsq, Real.sqrt_sq (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [hsin_ge k hk])
  have hcot_inc : ∀ k, k + 1 < L → cotPi (Δ k) ≤ cotPi (Δ (k + 1)) := by
    intro k hk
    have hk0 : k < L := by omega
    have hs1 := hsin_pos k hk0
    have hs2 := hsin_pos (k + 1) hk
    simp only [cotPi]
    rw [div_le_div_iff₀ hs1 hs2]
    have hdiff_nonneg : 0 ≤ Real.sin (Real.pi * Δ k - Real.pi * Δ (k + 1)) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have hd := hdec k hk
        simp only [Δ]
        have h1 : M + (k + 1) + 1 = M + k + 2 := by omega
        have h2 : M + (k + 1) = M + k + 1 := by omega
        rw [h1, h2]
        nlinarith [Real.pi_pos]
      · nlinarith [hhigh k hk0, hlow (k + 1) hk, Real.pi_pos]
    rw [Real.sin_sub] at hdiff_nonneg
    linarith
  have hnorm_diff : ∀ k ∈ Finset.range (L - 1),
      ‖(u k - u (k + 1)) * w (k + 1)‖ = (cotPi (Δ (k + 1)) - cotPi (Δ k)) / 2 := by
    intro k hk
    have hk' : k + 1 < L := by
      have := Finset.mem_range.mp hk
      omega
    rw [norm_mul]
    simp only [w, norm_e, mul_one]
    have hdiff : u k - u (k + 1) =
        Complex.I * (((cotPi (Δ (k + 1)) - cotPi (Δ k)) / 2 : ℝ) : ℂ) := by
      simp only [u]
      push_cast
      ring
    rw [hdiff, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hcot_inc k hk'])]
  have hsum_diff :
      ‖∑ k ∈ Finset.range (L - 1), (u k - u (k + 1)) * w (k + 1)‖ ≤ 1 / (4 * lam) := by
    calc ‖∑ k ∈ Finset.range (L - 1), (u k - u (k + 1)) * w (k + 1)‖
        ≤ ∑ k ∈ Finset.range (L - 1), ‖(u k - u (k + 1)) * w (k + 1)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (L - 1), (cotPi (Δ (k + 1)) - cotPi (Δ k)) / 2 :=
          Finset.sum_congr rfl hnorm_diff
      _ = (∑ k ∈ Finset.range (L - 1), (cotPi (Δ (k + 1)) - cotPi (Δ k))) / 2 := by
          rw [Finset.sum_div]
      _ = (cotPi (Δ (L - 1)) - cotPi (Δ 0)) / 2 := by
          rw [Finset.sum_range_sub (fun k => cotPi (Δ k)) (L - 1)]
      _ ≤ cotPi (Δ (L - 1)) / 2 := by
          have hc0 : 0 ≤ cotPi (Δ 0) :=
            div_nonneg (hcos_nonneg 0 (by omega)) (hsin_pos 0 (by omega)).le
          linarith
      _ ≤ (1 / Real.sin (Real.pi * Δ (L - 1))) / 2 := by
          have hsp := hsin_pos (L - 1) (by omega)
          have hcle : Real.cos (Real.pi * Δ (L - 1)) ≤ 1 := Real.cos_le_one _
          have : cotPi (Δ (L - 1)) ≤ 1 / Real.sin (Real.pi * Δ (L - 1)) :=
            div_le_div_of_nonneg_right hcle hsp.le
          linarith
      _ = 1 / (2 * Real.sin (Real.pi * Δ (L - 1))) := by ring
      _ ≤ 1 / (4 * lam) :=
          one_div_le_one_div_of_le (by positivity) (by linarith [hsin_ge (L - 1) (by omega)])
  have hmain : ‖∑ k ∈ Finset.range L, w k‖ ≤ 3 / (4 * lam) := by
    rw [hsum_sbp]
    calc ‖u (L - 1) * w L - u 0 * w 0 +
            ∑ k ∈ Finset.range (L - 1), (u k - u (k + 1)) * w (k + 1)‖
        ≤ ‖u (L - 1) * w L - u 0 * w 0‖ +
            ‖∑ k ∈ Finset.range (L - 1), (u k - u (k + 1)) * w (k + 1)‖ := norm_add_le _ _
      _ ≤ (‖u (L - 1) * w L‖ + ‖u 0 * w 0‖) +
            ‖∑ k ∈ Finset.range (L - 1), (u k - u (k + 1)) * w (k + 1)‖ := by
          linarith [norm_sub_le (u (L - 1) * w L) (u 0 * w 0)]
      _ = ‖u (L - 1)‖ + ‖u 0‖ +
            ‖∑ k ∈ Finset.range (L - 1), (u k - u (k + 1)) * w (k + 1)‖ := by
          simp only [w, norm_mul, norm_e, mul_one]
      _ ≤ 1 / (4 * lam) + 1 / (4 * lam) + 1 / (4 * lam) := by
          linarith [hnorm_u (L - 1) (by omega), hnorm_u 0 (by omega), hsum_diff]
      _ = 3 / (4 * lam) := by ring
  have h1_le : (1 : ℝ) ≤ 5 / (4 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have htot : 3 / (4 * lam) + 1 ≤ 2 / lam := by
    have : 2 / lam = 3 / (4 * lam) + 5 / (4 * lam) := by ring
    linarith
  exact hsplit.trans (by linarith [hmain])

/- Section 4: Weyl-van der Corput differencing -/

private lemma weyl_van_der_corput (f : ℕ → ℝ) (A Q : ℕ) (hQ : 1 ≤ Q) (hQA : Q ≤ A) :
    ‖∑ k ∈ Finset.range A, e (f (A + 1 + k))‖ ^ 2 ≤
      2 * (A : ℝ) ^ 2 / Q +
        (4 * (A : ℝ) / Q) *
          ∑ q ∈ Finset.Ico 1 Q,
            ‖∑ k ∈ Finset.range (A - q), e (f (A + 1 + k + q) - f (A + 1 + k))‖ := by
  let z (n : ℤ) : ℂ :=
    if (A + 1 : ℤ) ≤ n ∧ n ≤ (2 * A : ℤ) then e (f n.toNat) else 0
  let S : ℂ := ∑ k ∈ Finset.range A, e (f (A + 1 + k))
  let W : Finset ℤ := Finset.Icc ((A + 1 : ℤ) - (Q : ℤ)) (2 * (A : ℤ))
  have hz_sum_shift : ∀ r ∈ Finset.range Q, ∑ n ∈ W, z (n + (r : ℤ)) = S := by
    intro r hr
    have hrQ : r < Q := Finset.mem_range.mp hr
    have hshift : ∑ n ∈ W, z (n + (r : ℤ)) =
        ∑ m ∈ Finset.Icc ((A + 1 : ℤ) - (Q : ℤ) + (r : ℤ)) (2 * (A : ℤ) + (r : ℤ)), z m := by
      refine Finset.sum_bij (fun n _ => n + (r : ℤ)) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [W, Finset.mem_Icc] at hn ⊢
        omega
      · intro _ _ _ _ h; omega
      · intro m hm
        refine ⟨m - (r : ℤ), ?_, by omega⟩
        simp only [W, Finset.mem_Icc] at hm ⊢
        omega
      · intro _ _; rfl
    rw [hshift]
    have hsub : Finset.Icc (A + 1 : ℤ) (2 * (A : ℤ)) ⊆
        Finset.Icc ((A + 1 : ℤ) - (Q : ℤ) + (r : ℤ)) (2 * (A : ℤ) + (r : ℤ)) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · refine (Finset.sum_bij (fun k _ => ((A + 1 + k : ℕ) : ℤ)) ?_ ?_ ?_ ?_).symm
      · intro k hk
        simp only [Finset.mem_range] at hk
        simp only [Finset.mem_Icc]
        omega
      · intro k1 _ k2 _ h; omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        refine ⟨(m - (A + 1 : ℤ)).toNat, ?_, by omega⟩
        simp only [Finset.mem_range]
        omega
      · intro k hk
        simp only [Finset.mem_range] at hk
        simp only [z, Int.toNat_natCast]
        rw [if_pos (by omega)]
    · intro m _ hm
      simp only [Finset.mem_Icc] at hm
      simp only [z]
      rw [if_neg hm]
  have hQS : ((Q : ℂ) * S) = ∑ n ∈ W, ∑ r ∈ Finset.range Q, z (n + (r : ℤ)) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl hz_sum_shift, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hWcard : (W.card : ℝ) ≤ 2 * (A : ℝ) := by
    have h1 : W.card = A + Q := by
      simp only [W, Int.card_Icc]
      omega
    have h2 : A + Q ≤ 2 * A := by omega
    exact_mod_cast h1 ▸ h2
  have hcs_norm :
      (Q : ℝ) ^ 2 * ‖S‖ ^ 2 ≤ (W.card : ℝ) * ∑ n ∈ W, ‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖ ^ 2 := by
    have h1 : (Q : ℝ) * ‖S‖ ≤ ∑ n ∈ W, ‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖ := by
      have hnorm : ‖(Q : ℂ) * S‖ = (Q : ℝ) * ‖S‖ := by
        rw [norm_mul, Complex.norm_natCast]
      rw [← hnorm, hQS]
      exact norm_sum_le _ _
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq W (fun _ => (1 : ℝ))
      (fun n => ‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    have h3 : ((Q : ℝ) * ‖S‖) ^ 2 ≤ (∑ n ∈ W, ‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  have hexpand :
      ∑ n ∈ W, ‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖ ^ 2 =
        ∑ p ∈ Finset.range Q ×ˢ Finset.range Q,
          (∑ n ∈ W, z (n + (p.1 : ℤ)) * starRingEnd ℂ (z (n + (p.2 : ℤ)))).re := by
    trans ∑ n ∈ W,
        (∑ p ∈ Finset.range Q ×ˢ Finset.range Q,
          z (n + (p.1 : ℤ)) * starRingEnd ℂ (z (n + (p.2 : ℤ)))).re
    · refine Finset.sum_congr rfl fun n _ => ?_
      have hsq : ((‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖ ^ 2 : ℝ) : ℂ) =
          (∑ r ∈ Finset.range Q, z (n + (r : ℤ))) *
            starRingEnd ℂ (∑ r ∈ Finset.range Q, z (n + (r : ℤ))) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [map_sum, Finset.sum_mul_sum, ← Finset.sum_product'] at hsq
      rw [← Complex.ofReal_re (‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖ ^ 2), hsq]
    · simp only [Complex.re_sum]
      rw [Finset.sum_comm]
  have hcorr : ∀ r1 ∈ Finset.range Q, ∀ r2 ∈ Finset.range Q, r2 ≤ r1 →
      ∑ n ∈ W, z (n + (r1 : ℤ)) * starRingEnd ℂ (z (n + (r2 : ℤ))) =
        ∑ k ∈ Finset.range (A - (r1 - r2)),
          e (f (A + 1 + k + (r1 - r2)) - f (A + 1 + k)) := by
    intro r1 hr1 r2 hr2 hle
    have hr1Q : r1 < Q := Finset.mem_range.mp hr1
    have hr2Q : r2 < Q := Finset.mem_range.mp hr2
    set q := r1 - r2
    have hshift :
        ∑ n ∈ W, z (n + (r1 : ℤ)) * starRingEnd ℂ (z (n + (r2 : ℤ))) =
          ∑ m ∈ Finset.Icc ((A + 1 : ℤ) - (Q : ℤ) + (r2 : ℤ)) (2 * (A : ℤ) + (r2 : ℤ)),
            z (m + (q : ℤ)) * starRingEnd ℂ (z m) := by
      refine Finset.sum_bij (fun n _ => n + (r2 : ℤ)) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [W, Finset.mem_Icc] at hn ⊢
        omega
      · intro _ _ _ _ h; omega
      · intro m hm
        refine ⟨m - (r2 : ℤ), ?_, by omega⟩
        simp only [W, Finset.mem_Icc] at hm ⊢
        omega
      · intro n _
        have hq : n + (r2 : ℤ) + (q : ℤ) = n + (r1 : ℤ) := by omega
        rw [hq]
    rw [hshift]
    have hsub : Finset.Icc (A + 1 : ℤ) (2 * (A : ℤ) - (q : ℤ)) ⊆
        Finset.Icc ((A + 1 : ℤ) - (Q : ℤ) + (r2 : ℤ)) (2 * (A : ℤ) + (r2 : ℤ)) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · refine (Finset.sum_bij (fun k _ => ((A + 1 + k : ℕ) : ℤ)) ?_ ?_ ?_ ?_).symm
      · intro k hk
        simp only [Finset.mem_range] at hk
        simp only [Finset.mem_Icc]
        omega
      · intro k1 _ k2 _ h; omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        refine ⟨(m - (A + 1 : ℤ)).toNat, ?_, by omega⟩
        simp only [Finset.mem_range]
        omega
      · intro k hk
        simp only [Finset.mem_range] at hk
        have h1 : ((A + 1 + k : ℕ) : ℤ) + (q : ℤ) = ((A + 1 + k + q : ℕ) : ℤ) := by omega
        simp only [z, h1, Int.toNat_natCast]
        rw [if_pos (by omega), if_pos (by omega), e_sub]
    · intro m _ hm
      simp only [Finset.mem_Icc] at hm
      by_cases hm1 : (A + 1 : ℤ) ≤ m ∧ m ≤ (2 * (A : ℤ))
      · have hm2 : ¬((A + 1 : ℤ) ≤ m + (q : ℤ) ∧ m + (q : ℤ) ≤ (2 * (A : ℤ))) := by omega
        simp only [z]
        rw [if_neg hm2, zero_mul]
      · simp only [z]
        rw [if_neg hm1, map_zero, mul_zero]
  have hinner_bound :
      ∑ p ∈ Finset.range Q ×ˢ Finset.range Q,
        (∑ n ∈ W, z (n + (p.1 : ℤ)) * starRingEnd ℂ (z (n + (p.2 : ℤ)))).re ≤
      (Q : ℝ) * (A : ℝ) +
        2 * (Q : ℝ) *
          ∑ q ∈ Finset.Ico 1 Q,
            ‖∑ k ∈ Finset.range (A - q), e (f (A + 1 + k + q) - f (A + 1 + k))‖ := by
    let gVal (q : ℕ) : ℝ :=
      ‖∑ k ∈ Finset.range (A - q), e (f (A + 1 + k + q) - f (A + 1 + k))‖
    have hpt : ∀ p ∈ Finset.range Q ×ˢ Finset.range Q,
        (∑ n ∈ W, z (n + (p.1 : ℤ)) * starRingEnd ℂ (z (n + (p.2 : ℤ)))).re ≤
          if p.1 = p.2 then (A : ℝ)
          else if p.2 < p.1 then gVal (p.1 - p.2)
          else gVal (p.2 - p.1) := by
      intro ⟨r1, r2⟩ hp
      have hp1 : r1 ∈ Finset.range Q := (Finset.mem_product.mp hp).1
      have hp2 : r2 ∈ Finset.range Q := (Finset.mem_product.mp hp).2
      dsimp only
      split_ifs with heq hlt
      · subst heq
        rw [hcorr r1 hp1 r1 hp1 le_rfl]
        simp [e_zero]
      · rw [hcorr r1 hp1 r2 hp2 hlt.le]
        exact Complex.re_le_norm _
      · have hle : r1 ≤ r2 := by omega
        have hconj :
            ∑ n ∈ W, z (n + (r1 : ℤ)) * starRingEnd ℂ (z (n + (r2 : ℤ))) =
              starRingEnd ℂ (∑ n ∈ W, z (n + (r2 : ℤ)) * starRingEnd ℂ (z (n + (r1 : ℤ)))) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          simp [mul_comm]
        rw [hconj, Complex.conj_re, hcorr r2 hp2 r1 hp1 hle]
        exact Complex.re_le_norm _
    calc ∑ p ∈ Finset.range Q ×ˢ Finset.range Q,
            (∑ n ∈ W, z (n + (p.1 : ℤ)) * starRingEnd ℂ (z (n + (p.2 : ℤ)))).re
        ≤ ∑ p ∈ Finset.range Q ×ˢ Finset.range Q,
            (if p.1 = p.2 then (A : ℝ)
             else if p.2 < p.1 then gVal (p.1 - p.2)
             else gVal (p.2 - p.1)) := Finset.sum_le_sum hpt
      _ = ∑ r1 ∈ Finset.range Q, ∑ r2 ∈ Finset.range Q,
            (if r1 = r2 then (A : ℝ)
             else if r2 < r1 then gVal (r1 - r2)
             else gVal (r2 - r1)) := Finset.sum_product _ _ _
      _ ≤ (Q : ℝ) * (A : ℝ) + 2 * (Q : ℝ) * ∑ q ∈ Finset.Ico 1 Q, gVal q := by
        have hrow : ∀ r1 ∈ Finset.range Q,
            ∑ r2 ∈ Finset.range Q,
              (if r1 = r2 then (A : ℝ)
               else if r2 < r1 then gVal (r1 - r2)
               else gVal (r2 - r1)) ≤
            (A : ℝ) + 2 * ∑ q ∈ Finset.Ico 1 Q, gVal q := by
          intro r1 hr1
          have hr1Q : r1 < Q := Finset.mem_range.mp hr1
          have h1 :
              ∑ r2 ∈ Finset.range Q,
                (if r1 = r2 then (A : ℝ)
                 else if r2 < r1 then gVal (r1 - r2)
                 else gVal (r2 - r1)) =
              (A : ℝ) +
                (∑ r2 ∈ (Finset.range Q).filter (· < r1), gVal (r1 - r2)) +
                (∑ r2 ∈ (Finset.range Q).filter (r1 < ·), gVal (r2 - r1)) := by
            have hpart :
                ∑ r2 ∈ Finset.range Q,
                  (if r1 = r2 then (A : ℝ)
                   else if r2 < r1 then gVal (r1 - r2)
                   else gVal (r2 - r1)) =
                ∑ r2 ∈ (Finset.range Q).filter (fun r2 => r1 = r2), (A : ℝ) +
                ∑ r2 ∈ (Finset.range Q).filter (fun r2 => r1 ≠ r2),
                  (if r2 < r1 then gVal (r1 - r2) else gVal (r2 - r1)) := by
              rw [← Finset.sum_filter_add_sum_filter_not (Finset.range Q) (fun r2 => r1 = r2)]
              congr 1
              · refine Finset.sum_congr rfl fun r2 hr2 => ?_
                rw [if_pos (Finset.mem_filter.mp hr2).2]
              · refine Finset.sum_congr rfl fun r2 hr2 => ?_
                rw [if_neg (Finset.mem_filter.mp hr2).2]
            rw [hpart]
            have hdiag : (Finset.range Q).filter (fun r2 => r1 = r2) = {r1} := by
              ext r2
              simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
              omega
            rw [hdiag, Finset.sum_singleton]
            rw [← Finset.sum_filter_add_sum_filter_not
              ((Finset.range Q).filter (fun r2 => r1 ≠ r2)) (· < r1)]
            have hlt_eq : ((Finset.range Q).filter (fun r2 => r1 ≠ r2)).filter (· < r1) =
                (Finset.range Q).filter (· < r1) := by
              ext r2; simp only [Finset.mem_filter, Finset.mem_range]; omega
            have hgt_eq : ((Finset.range Q).filter (fun r2 => r1 ≠ r2)).filter (fun r2 => ¬r2 < r1) =
                (Finset.range Q).filter (r1 < ·) := by
              ext r2; simp only [Finset.mem_filter, Finset.mem_range]; omega
            have hs1 :
                ∑ r2 ∈ ((Finset.range Q).filter (fun r2 => r1 ≠ r2)).filter (· < r1),
                  (if r2 < r1 then gVal (r1 - r2) else gVal (r2 - r1)) =
                ∑ r2 ∈ (Finset.range Q).filter (· < r1), gVal (r1 - r2) := by
              rw [hlt_eq]
              refine Finset.sum_congr rfl fun r2 hr2 => if_pos (Finset.mem_filter.mp hr2).2
            have hs2 :
                ∑ r2 ∈ ((Finset.range Q).filter (fun r2 => r1 ≠ r2)).filter (fun r2 => ¬r2 < r1),
                  (if r2 < r1 then gVal (r1 - r2) else gVal (r2 - r1)) =
                ∑ r2 ∈ (Finset.range Q).filter (r1 < ·), gVal (r2 - r1) := by
              rw [hgt_eq]
              refine Finset.sum_congr rfl fun r2 hr2 => by
                have := (Finset.mem_filter.mp hr2).2
                rw [if_neg (by omega)]
            rw [hs1, hs2]; ring
          rw [h1]
          have hle1 : ∑ r2 ∈ (Finset.range Q).filter (· < r1), gVal (r1 - r2) ≤
              ∑ q ∈ Finset.Ico 1 Q, gVal q := by
            have himg :
                ∑ r2 ∈ (Finset.range Q).filter (· < r1), gVal (r1 - r2) =
                  ∑ q ∈ ((Finset.range Q).filter (· < r1)).image (fun r2 => r1 - r2), gVal q := by
              symm
              apply Finset.sum_image
              intro x hx y hy hxy
              have hx' := (Finset.mem_filter.mp hx).2
              have hy' := (Finset.mem_filter.mp hy).2
              dsimp only at hxy
              omega
            rw [himg]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
            intro q hq
            obtain ⟨r2, hr2, rfl⟩ := Finset.mem_image.mp hq
            simp only [Finset.mem_filter, Finset.mem_range] at hr2
            simp only [Finset.mem_Ico]
            omega
          have hle2 : ∑ r2 ∈ (Finset.range Q).filter (r1 < ·), gVal (r2 - r1) ≤
              ∑ q ∈ Finset.Ico 1 Q, gVal q := by
            have himg :
                ∑ r2 ∈ (Finset.range Q).filter (r1 < ·), gVal (r2 - r1) =
                  ∑ q ∈ ((Finset.range Q).filter (r1 < ·)).image (fun r2 => r2 - r1), gVal q := by
              symm
              apply Finset.sum_image
              intro x hx y hy hxy
              have hx' := (Finset.mem_filter.mp hx).2
              have hy' := (Finset.mem_filter.mp hy).2
              dsimp only at hxy
              omega
            rw [himg]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
            intro q hq
            obtain ⟨r2, hr2, rfl⟩ := Finset.mem_image.mp hq
            simp only [Finset.mem_filter, Finset.mem_range] at hr2
            simp only [Finset.mem_Ico]
            omega
          linarith
        calc ∑ r1 ∈ Finset.range Q, ∑ r2 ∈ Finset.range Q,
              (if r1 = r2 then (A : ℝ)
               else if r2 < r1 then gVal (r1 - r2)
               else gVal (r2 - r1))
            ≤ ∑ _r1 ∈ Finset.range Q, ((A : ℝ) + 2 * ∑ q ∈ Finset.Ico 1 Q, gVal q) :=
              Finset.sum_le_sum hrow
          _ = (Q : ℝ) * ((A : ℝ) + 2 * ∑ q ∈ Finset.Ico 1 Q, gVal q) := by
              simp [Finset.sum_const, nsmul_eq_mul]; ring
          _ = (Q : ℝ) * (A : ℝ) + 2 * (Q : ℝ) * ∑ q ∈ Finset.Ico 1 Q, gVal q := by ring
  have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr (by omega)
  have hinner_nonneg : 0 ≤ ∑ n ∈ W, ‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcomb :
      (Q : ℝ) ^ 2 * ‖S‖ ^ 2 ≤
        2 * (A : ℝ) * ((Q : ℝ) * (A : ℝ) +
          2 * (Q : ℝ) *
            ∑ q ∈ Finset.Ico 1 Q,
              ‖∑ k ∈ Finset.range (A - q), e (f (A + 1 + k + q) - f (A + 1 + k))‖) := by
    calc (Q : ℝ) ^ 2 * ‖S‖ ^ 2
        ≤ (W.card : ℝ) * ∑ n ∈ W, ‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖ ^ 2 := hcs_norm
      _ ≤ (2 * (A : ℝ)) * ∑ n ∈ W, ‖∑ r ∈ Finset.range Q, z (n + (r : ℤ))‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hWcard hinner_nonneg
      _ ≤ (2 * (A : ℝ)) * _ := by
          rw [hexpand]
          exact mul_le_mul_of_nonneg_left hinner_bound (by positivity)
  have hdiv :
      ‖S‖ ^ 2 ≤
        (2 * (A : ℝ) * ((Q : ℝ) * (A : ℝ) +
          2 * (Q : ℝ) *
            ∑ q ∈ Finset.Ico 1 Q,
              ‖∑ k ∈ Finset.range (A - q), e (f (A + 1 + k + q) - f (A + 1 + k))‖)) /
          (Q : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc ‖S‖ ^ 2 ≤ _ := hdiv
    _ = 2 * (A : ℝ) ^ 2 / (Q : ℝ) +
          (4 * (A : ℝ) / (Q : ℝ)) *
            ∑ q ∈ Finset.Ico 1 Q,
              ‖∑ k ∈ Finset.range (A - q), e (f (A + 1 + k + q) - f (A + 1 + k))‖ := by
        field_simp [hQpos.ne']
        ring

/- Section 5: Reciprocal exponential sum bound -/

private lemma harmonic_Icc_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ q ∈ Finset.Icc 1 n, (1 : ℝ) / (q : ℝ) ≤ 1 + Real.log n := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm; simp
    have hm1 : 1 ≤ m := by omega
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : m + 1 ∉ Finset.Icc 1 m := by simp
    rw [hIcc, Finset.sum_insert hnotmem]
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm1
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos (by positivity : (0 : ℝ) < (m + 1 : ℕ)) hmpos)
    rw [inv_div, Real.log_div (by positivity) hmpos.ne'] at hlog
    have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) = 1 - (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    linarith [ih hm1]

private lemma harmonic_Ico_le (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Ico 1 Q, (1 : ℝ) / (q : ℝ) ≤ 1 + Real.log Q := by
  by_cases hQ1 : Q = 1
  · subst hQ1; simp
  have hQ2 : 2 ≤ Q := by omega
  have hEq : Finset.Ico 1 Q = Finset.Icc 1 (Q - 1) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [hEq]
  have h1 := harmonic_Icc_le (Q - 1) (by omega)
  have hlog_mono : Real.log ((Q - 1 : ℕ) : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr (by omega))
  linarith

private lemma reciprocal_diff_eq (X : ℝ) (h a q : ℕ) (ha : 1 ≤ a) :
    ((h : ℝ) * X / ((a + 1 + q : ℕ) : ℝ) - (h : ℝ) * X / ((a + 1 : ℕ) : ℝ)) -
      ((h : ℝ) * X / ((a + q : ℕ) : ℝ) - (h : ℝ) * X / (a : ℝ)) =
    2 * (h : ℝ) * X *
      ∑ j ∈ Finset.range q,
        (1 : ℝ) / (((a + j : ℕ) : ℝ) * ((a + j + 1 : ℕ) : ℝ) * ((a + j + 2 : ℕ) : ℝ)) := by
  let F (j : ℕ) : ℝ := (1 : ℝ) / (((a + j : ℕ) : ℝ) * ((a + j + 1 : ℕ) : ℝ))
  have hterm : ∀ j ∈ Finset.range q,
      2 * ((1 : ℝ) / (((a + j : ℕ) : ℝ) * ((a + j + 1 : ℕ) : ℝ) * ((a + j + 2 : ℕ) : ℝ))) =
        F j - F (j + 1) := by
    intro j _
    simp only [F]
    have h0 : ((a + j : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 : ((a + j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : ((a + j + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have heq1 : ((a + (j + 1) : ℕ) : ℝ) = ((a + j + 1 : ℕ) : ℝ) := by norm_cast
    have heq2 : ((a + (j + 1) + 1 : ℕ) : ℝ) = ((a + j + 2 : ℕ) : ℝ) := by norm_cast
    rw [heq1, heq2]
    field_simp [h0, h1, h2]
    push_cast
    ring
  have hsum :
      2 * ∑ j ∈ Finset.range q,
          (1 : ℝ) / (((a + j : ℕ) : ℝ) * ((a + j + 1 : ℕ) : ℝ) * ((a + j + 2 : ℕ) : ℝ)) =
        F 0 - F q := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  have hmul :
      2 * (h : ℝ) * X *
          ∑ j ∈ Finset.range q,
            (1 : ℝ) / (((a + j : ℕ) : ℝ) * ((a + j + 1 : ℕ) : ℝ) * ((a + j + 2 : ℕ) : ℝ)) =
        (h : ℝ) * X * (F 0 - F q) := by
    linarith [congr_arg (fun t => (h : ℝ) * X * t) hsum]
  rw [hmul]
  simp only [F, add_zero]
  have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ha1 : ((a + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have haq : ((a + q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have haq1 : ((a + q + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have heq : ((a + 1 + q : ℕ) : ℝ) = ((a + q + 1 : ℕ) : ℝ) := by norm_cast; omega
  rw [heq]
  field_simp [ha0, ha1, haq, haq1]
  push_cast
  ring

private lemma exp_sum_reciprocal_bound_pos (X : ℝ) (hX : 0 < X) (A h : ℕ) (hA : 1 ≤ A) (hh : 1 ≤ h)
    (hcond : 4 * (h : ℝ) * X ≤ (A : ℝ) ^ 3) :
    ‖∑ k ∈ Finset.range A, e ((h : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))‖ ≤
      4 * Real.sqrt ((h : ℝ) * X / (A : ℝ)) +
        16 * Real.sqrt ((A : ℝ) * (1 + Real.log A)) +
        6 * Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / ((h : ℝ) * X)) := by
  have hApos : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hlog_nonneg : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg (by exact_mod_cast hA)
  set Q0 : ℕ := ⌊(A : ℝ) ^ 3 / (4 * (h : ℝ) * X)⌋₊
  set Q : ℕ := min A Q0
  have hQ0_ge1 : 1 ≤ Q0 := by
    rw [Nat.one_le_floor_iff, le_div_iff₀ (by positivity)]
    linarith
  have hQ1 : 1 ≤ Q := le_min hA hQ0_ge1
  have hQA : Q ≤ A := min_le_left _ _
  have hQQ0 : Q ≤ Q0 := min_le_right _ _
  have hQ_le_real : (Q : ℝ) ≤ (A : ℝ) ^ 3 / (4 * (h : ℝ) * X) :=
    (Nat.cast_le.mpr hQQ0).trans (Nat.floor_le (by positivity))
  have hweyl := weyl_van_der_corput (fun n => (h : ℝ) * X / (n : ℝ)) A Q hQ1 hQA
  have hinner : ∀ q ∈ Finset.Ico 1 Q,
      ‖∑ k ∈ Finset.range (A - q),
          e ((h : ℝ) * X / ((A + 1 + k + q : ℕ) : ℝ) - (h : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))‖ ≤
        8 * (A : ℝ) ^ 3 / ((h : ℝ) * X * (q : ℝ)) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Ico.mp hq).1
    have hqQ : q < Q := (Finset.mem_Ico.mp hq).2
    have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq1
    have hAq : 1 ≤ A - q := by omega
    set L : ℕ := A - q - 1
    have hAq_eq : A - q = L + 1 := by omega
    rw [hAq_eq]
    let g (n : ℕ) : ℝ := (h : ℝ) * X / ((n + q : ℕ) : ℝ) - (h : ℝ) * X / (n : ℝ)
    set lam : ℝ := (h : ℝ) * X * (q : ℝ) / (4 * (A : ℝ) ^ 3)
    have hlam_pos : 0 < lam := by positivity
    have hq_real_le : 2 * (h : ℝ) * X * (q : ℝ) / (A : ℝ) ^ 3 ≤ 1 / 2 := by
      have h1 : (q : ℝ) ≤ (A : ℝ) ^ 3 / (4 * (h : ℝ) * X) :=
        (Nat.cast_le.mpr hqQ.le).trans hQ_le_real
      rw [le_div_iff₀ (by positivity)] at h1
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hlam_half : lam ≤ 1 / 2 := by
      have : lam ≤ 2 * (h : ℝ) * X * (q : ℝ) / (A : ℝ) ^ 3 := by
        simp only [lam]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos (mul_pos hhpos hX) hqpos, pow_pos hApos 3]
      linarith
    have hKL : ‖∑ k ∈ Finset.range (L + 1), e (g (A + 1 + k))‖ ≤ 2 / lam := by
      apply kusmin_landau g (A + 1) L lam hlam_pos hlam_half
      · intro k hk
        have hdiff := reciprocal_diff_eq X h (A + 1 + k) q (by omega)
        change lam ≤ g (A + 1 + k + 1) - g (A + 1 + k)
        simp only [g]
        rw [hdiff]
        have hterm_ge : ∀ j ∈ Finset.range q,
            (1 : ℝ) / (8 * (A : ℝ) ^ 3) ≤
              (1 : ℝ) / (((A + 1 + k + j : ℕ) : ℝ) * ((A + 1 + k + j + 1 : ℕ) : ℝ) *
                ((A + 1 + k + j + 2 : ℕ) : ℝ)) := by
          intro j hj
          have hjq : j < q := Finset.mem_range.mp hj
          have hb1 : ((A + 1 + k + j : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast (by omega : A + 1 + k + j ≤ 2 * A)
          have hb2 : ((A + 1 + k + j + 1 : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast (by omega : A + 1 + k + j + 1 ≤ 2 * A)
          have hb3 : ((A + 1 + k + j + 2 : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast (by omega : A + 1 + k + j + 2 ≤ 2 * A)
          have hp1 : (0 : ℝ) < ((A + 1 + k + j : ℕ) : ℝ) := by positivity
          have hp2 : (0 : ℝ) < ((A + 1 + k + j + 1 : ℕ) : ℝ) := by positivity
          have hp3 : (0 : ℝ) < ((A + 1 + k + j + 2 : ℕ) : ℝ) := by positivity
          apply one_div_le_one_div_of_le (by positivity)
          have h12 : ((A + 1 + k + j : ℕ) : ℝ) * ((A + 1 + k + j + 1 : ℕ) : ℝ) ≤
              (2 * (A : ℝ)) * (2 * (A : ℝ)) := mul_le_mul hb1 hb2 hp2.le (by positivity)
          have h123 := mul_le_mul h12 hb3 hp3.le (by positivity)
          linarith [show (2 * (A : ℝ)) * (2 * (A : ℝ)) * (2 * (A : ℝ)) = 8 * (A : ℝ) ^ 3 by ring]
        have hsum_ge : (q : ℝ) * ((1 : ℝ) / (8 * (A : ℝ) ^ 3)) ≤
            ∑ j ∈ Finset.range q,
              (1 : ℝ) / (((A + 1 + k + j : ℕ) : ℝ) * ((A + 1 + k + j + 1 : ℕ) : ℝ) *
                ((A + 1 + k + j + 2 : ℕ) : ℝ)) := by
          calc (q : ℝ) * ((1 : ℝ) / (8 * (A : ℝ) ^ 3))
              = ∑ _j ∈ Finset.range q, (1 : ℝ) / (8 * (A : ℝ) ^ 3) := by
                  simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum hterm_ge
        have hmul_ge := mul_le_mul_of_nonneg_left hsum_ge (by positivity : 0 ≤ 2 * (h : ℝ) * X)
        calc lam = 2 * (h : ℝ) * X * ((q : ℝ) * ((1 : ℝ) / (8 * (A : ℝ) ^ 3))) := by
              simp only [lam]; ring
          _ ≤ _ := hmul_ge
      · intro k hk
        have hdiff := reciprocal_diff_eq X h (A + 1 + k) q (by omega)
        change g (A + 1 + k + 1) - g (A + 1 + k) ≤ 1 / 2
        simp only [g]
        rw [hdiff]
        have hterm_le : ∀ j ∈ Finset.range q,
            (1 : ℝ) / (((A + 1 + k + j : ℕ) : ℝ) * ((A + 1 + k + j + 1 : ℕ) : ℝ) *
              ((A + 1 + k + j + 2 : ℕ) : ℝ)) ≤ (1 : ℝ) / (A : ℝ) ^ 3 := by
          intro j _
          have hb1 : (A : ℝ) ≤ ((A + 1 + k + j : ℕ) : ℝ) := by exact_mod_cast (by omega : A ≤ A + 1 + k + j)
          have hb2 : (A : ℝ) ≤ ((A + 1 + k + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : A ≤ A + 1 + k + j + 1)
          have hb3 : (A : ℝ) ≤ ((A + 1 + k + j + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : A ≤ A + 1 + k + j + 2)
          apply one_div_le_one_div_of_le (by positivity)
          have h12 := mul_le_mul hb1 hb2 hApos.le (by positivity)
          have h123 := mul_le_mul h12 hb3 hApos.le (by positivity)
          linarith [show (A : ℝ) * (A : ℝ) * (A : ℝ) = (A : ℝ) ^ 3 by ring]
        have hsum_le :
            ∑ j ∈ Finset.range q,
              (1 : ℝ) / (((A + 1 + k + j : ℕ) : ℝ) * ((A + 1 + k + j + 1 : ℕ) : ℝ) *
                ((A + 1 + k + j + 2 : ℕ) : ℝ)) ≤ (q : ℝ) * ((1 : ℝ) / (A : ℝ) ^ 3) := by
          calc _ ≤ ∑ _j ∈ Finset.range q, (1 : ℝ) / (A : ℝ) ^ 3 := Finset.sum_le_sum hterm_le
            _ = (q : ℝ) * ((1 : ℝ) / (A : ℝ) ^ 3) := by simp [Finset.sum_const, nsmul_eq_mul]
        have hmul_le := mul_le_mul_of_nonneg_left hsum_le (by positivity : 0 ≤ 2 * (h : ℝ) * X)
        calc _ ≤ 2 * (h : ℝ) * X * ((q : ℝ) * ((1 : ℝ) / (A : ℝ) ^ 3)) := hmul_le
          _ = 2 * (h : ℝ) * X * (q : ℝ) / (A : ℝ) ^ 3 := by ring
          _ ≤ 1 / 2 := hq_real_le
      · intro k _
        have hd1 := reciprocal_diff_eq X h (A + 1 + k + 1) q (by omega)
        have hd0 := reciprocal_diff_eq X h (A + 1 + k) q (by omega)
        have heq2 : A + 1 + k + 2 = A + 1 + k + 1 + 1 := by omega
        rw [heq2]
        simp only [g]
        rw [hd1, hd0]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
        apply one_div_le_one_div_of_le (by positivity)
        have h1 : ((A + 1 + k + j : ℕ) : ℝ) ≤ ((A + 1 + k + 1 + j : ℕ) : ℝ) := by
          exact_mod_cast (by omega : A + 1 + k + j ≤ A + 1 + k + 1 + j)
        have h2 : ((A + 1 + k + j + 1 : ℕ) : ℝ) ≤ ((A + 1 + k + 1 + j + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : A + 1 + k + j + 1 ≤ A + 1 + k + 1 + j + 1)
        have h3 : ((A + 1 + k + j + 2 : ℕ) : ℝ) ≤ ((A + 1 + k + 1 + j + 2 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : A + 1 + k + j + 2 ≤ A + 1 + k + 1 + j + 2)
        have h12 := mul_le_mul h1 h2 (by positivity) (by positivity)
        exact mul_le_mul h12 h3 (by positivity) (by positivity)
    have h2lam : 2 / lam = 8 * (A : ℝ) ^ 3 / ((h : ℝ) * X * (q : ℝ)) := by
      simp only [lam]; field_simp; ring
    simpa only [g, h2lam] using hKL
  have hsum_q :
      ∑ q ∈ Finset.Ico 1 Q,
        ‖∑ k ∈ Finset.range (A - q),
            e ((h : ℝ) * X / ((A + 1 + k + q : ℕ) : ℝ) - (h : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))‖ ≤
        8 * (A : ℝ) ^ 3 / ((h : ℝ) * X) * (1 + Real.log A) := by
    calc _ ≤ ∑ q ∈ Finset.Ico 1 Q, 8 * (A : ℝ) ^ 3 / ((h : ℝ) * X * (q : ℝ)) :=
          Finset.sum_le_sum hinner
      _ = 8 * (A : ℝ) ^ 3 / ((h : ℝ) * X) * ∑ q ∈ Finset.Ico 1 Q, (1 : ℝ) / (q : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => by ring
      _ ≤ 8 * (A : ℝ) ^ 3 / ((h : ℝ) * X) * (1 + Real.log Q) :=
          mul_le_mul_of_nonneg_left (harmonic_Ico_le Q hQ1) (by positivity)
      _ ≤ 8 * (A : ℝ) ^ 3 / ((h : ℝ) * X) * (1 + Real.log A) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [Real.log_le_log (Nat.cast_pos.mpr hQ1) (Nat.cast_le.mpr hQA)]
  have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ1
  have hSsq :
      ‖∑ k ∈ Finset.range A, e ((h : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))‖ ^ 2 ≤
        2 * (A : ℝ) ^ 2 / (Q : ℝ) +
          32 * (A : ℝ) ^ 4 * (1 + Real.log A) / ((Q : ℝ) * (h : ℝ) * X) := by
    have hmul := mul_le_mul_of_nonneg_left hsum_q (by positivity : 0 ≤ 4 * (A : ℝ) / (Q : ℝ))
    have hrew : 4 * (A : ℝ) / (Q : ℝ) * (8 * (A : ℝ) ^ 3 / ((h : ℝ) * X) * (1 + Real.log A)) =
        32 * (A : ℝ) ^ 4 * (1 + Real.log A) / ((Q : ℝ) * (h : ℝ) * X) := by ring
    linarith
  have hSsq_univ :
      ‖∑ k ∈ Finset.range A, e ((h : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))‖ ^ 2 ≤
        16 * ((h : ℝ) * X / (A : ℝ)) +
          256 * ((A : ℝ) * (1 + Real.log A)) +
          32 * ((A : ℝ) ^ 3 * (1 + Real.log A) / ((h : ℝ) * X)) := by
    by_cases hcase : Q0 ≤ A
    · have hQ_eq : Q = Q0 := min_eq_right hcase
      have hQ_ge : (A : ℝ) ^ 3 / (8 * (h : ℝ) * X) ≤ (Q : ℝ) := by
        rw [hQ_eq]
        have hlt : (A : ℝ) ^ 3 / (4 * (h : ℝ) * X) < (Q0 : ℝ) + 1 := Nat.lt_floor_add_one _
        have hQ0r : (1 : ℝ) ≤ (Q0 : ℝ) := Nat.one_le_cast.mpr hQ0_ge1
        linarith [show (A : ℝ) ^ 3 / (8 * (h : ℝ) * X) = ((A : ℝ) ^ 3 / (4 * (h : ℝ) * X)) / 2 by ring]
      have ht1 : 2 * (A : ℝ) ^ 2 / (Q : ℝ) ≤ 16 * ((h : ℝ) * X / (A : ℝ)) := by
        rw [div_le_iff₀ hQpos]
        have := mul_le_mul_of_nonneg_left hQ_ge (by positivity : 0 ≤ 16 * ((h : ℝ) * X / (A : ℝ)))
        have heq : 16 * ((h : ℝ) * X / (A : ℝ)) * ((A : ℝ) ^ 3 / (8 * (h : ℝ) * X)) =
            2 * (A : ℝ) ^ 2 := by field_simp [hApos.ne', hhpos.ne', hX.ne']; ring
        linarith
      have ht2 : 32 * (A : ℝ) ^ 4 * (1 + Real.log A) / ((Q : ℝ) * (h : ℝ) * X) ≤
          256 * ((A : ℝ) * (1 + Real.log A)) := by
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left hQ_ge
          (by positivity : 0 ≤ 256 * ((A : ℝ) * (1 + Real.log A)) * ((h : ℝ) * X))
        have heq : 256 * ((A : ℝ) * (1 + Real.log A)) * ((h : ℝ) * X) *
            ((A : ℝ) ^ 3 / (8 * (h : ℝ) * X)) = 32 * (A : ℝ) ^ 4 * (1 + Real.log A) := by
          field_simp [hhpos.ne', hX.ne']; ring
        have hrew : 256 * ((A : ℝ) * (1 + Real.log A)) * ((Q : ℝ) * (h : ℝ) * X) =
            256 * ((A : ℝ) * (1 + Real.log A)) * ((h : ℝ) * X) * (Q : ℝ) := by ring
        linarith
      have ht3 : (0 : ℝ) ≤ 32 * ((A : ℝ) ^ 3 * (1 + Real.log A) / ((h : ℝ) * X)) := by positivity
      linarith
    · have hQ_eq : Q = A := min_eq_left (by omega)
      rw [hQ_eq] at hSsq
      have ht1 : 2 * (A : ℝ) ^ 2 / (A : ℝ) ≤ 256 * ((A : ℝ) * (1 + Real.log A)) := by
        have : 2 * (A : ℝ) ^ 2 / (A : ℝ) = 2 * (A : ℝ) := by field_simp [hApos.ne']
        nlinarith
      have ht2 : 32 * (A : ℝ) ^ 4 * (1 + Real.log A) / ((A : ℝ) * (h : ℝ) * X) =
          32 * ((A : ℝ) ^ 3 * (1 + Real.log A) / ((h : ℝ) * X)) := by
        field_simp [hApos.ne', hhpos.ne', hX.ne']
      have ht0 : (0 : ℝ) ≤ 16 * ((h : ℝ) * X / (A : ℝ)) := by positivity
      linarith
  set u := Real.sqrt ((h : ℝ) * X / (A : ℝ))
  set v := Real.sqrt ((A : ℝ) * (1 + Real.log A))
  set w := Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / ((h : ℝ) * X))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = (h : ℝ) * X / (A : ℝ) := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = (A : ℝ) * (1 + Real.log A) := Real.sq_sqrt (by positivity)
  have hw2 : w ^ 2 = (A : ℝ) ^ 3 * (1 + Real.log A) / ((h : ℝ) * X) := Real.sq_sqrt (by positivity)
  have hsq_le :
      ‖∑ k ∈ Finset.range A, e ((h : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))‖ ^ 2 ≤
        (4 * u + 16 * v + 6 * w) ^ 2 := by
    nlinarith [hu, hv, hw, hu2, hv2, hw2, mul_nonneg hu hv, mul_nonneg hu hw, mul_nonneg hv hw]
  nlinarith [norm_nonneg (∑ k ∈ Finset.range A, e ((h : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))),
    show 0 ≤ 4 * u + 16 * v + 6 * w by positivity]

private lemma exp_sum_reciprocal_uniform (X : ℝ) (hX : 0 < X) (A K : ℕ) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hcond : 8 * (K : ℝ) * X ≤ (A : ℝ) ^ 3) :
    ∀ h : ℤ, h ≠ 0 → |h| < 2 * (K : ℤ) →
      ‖∑ a ∈ Finset.Ioc A (2 * A), e ((h : ℝ) * (X / (a : ℝ)))‖ ≤
        6 * Real.sqrt ((K : ℝ) * X / (A : ℝ)) +
          16 * Real.sqrt ((A : ℝ) * (1 + Real.log A)) +
          6 * Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / X) := by
  intro h hh0 hhK
  have hIoc_eq : ∀ c : ℝ,
      ∑ a ∈ Finset.Ioc A (2 * A), e (c * (X / (a : ℝ))) =
        ∑ k ∈ Finset.range A, e (c * X / ((A + 1 + k : ℕ) : ℝ)) := by
    intro c
    refine (Finset.sum_bij (fun k _ => A + 1 + k) ?_ ?_ ?_ ?_).symm
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ioc]
      omega
    · intro k1 _ k2 _ heq; omega
    · intro a ha
      simp only [Finset.mem_Ioc] at ha
      refine ⟨a - (A + 1), Finset.mem_range.mpr (by omega), by omega⟩
    · intro k _
      congr 1; ring
  rw [hIoc_eq]
  set hn : ℕ := h.natAbs
  have hhn1 : 1 ≤ hn := Int.natAbs_pos.mpr hh0
  have hhn_lt : hn < 2 * K := by
    have habs : -(2 * (K : ℤ)) < h ∧ h < 2 * (K : ℤ) := abs_lt.mp hhK
    rcases Int.natAbs_eq h with hpos | hneg <;> omega
  have hnorm_eq :
      ‖∑ k ∈ Finset.range A, e ((h : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))‖ =
        ‖∑ k ∈ Finset.range A, e ((hn : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))‖ := by
    rcases Int.natAbs_eq h with hpos | hneg
    · have hr : (h : ℝ) = (hn : ℝ) := by
        have h1 : (h : ℤ) = (hn : ℤ) := hpos
        exact_mod_cast h1
      rw [hr]
    · have hr : (h : ℝ) = -(hn : ℝ) := by
        have h1 : (h : ℤ) = -(hn : ℤ) := hneg
        exact_mod_cast h1
      rw [hr]
      have hconj :
          ∑ k ∈ Finset.range A, e (-(hn : ℝ) * X / ((A + 1 + k : ℕ) : ℝ)) =
            starRingEnd ℂ (∑ k ∈ Finset.range A, e ((hn : ℝ) * X / ((A + 1 + k : ℕ) : ℝ))) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← e_neg]
        congr 1; ring
      rw [hconj, Complex.norm_conj]
  rw [hnorm_eq]
  have hcond_hn : 4 * (hn : ℝ) * X ≤ (A : ℝ) ^ 3 := by
    have hhn_le : (hn : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hhn_lt.le
    nlinarith
  have hbound := exp_sum_reciprocal_bound_pos X hX A hn hA hhn1 hcond_hn
  have hApos : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hlog_nonneg : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg (by exact_mod_cast hA)
  have ht1 : 4 * Real.sqrt ((hn : ℝ) * X / (A : ℝ)) ≤ 6 * Real.sqrt ((K : ℝ) * X / (A : ℝ)) := by
    have hhn_le : (hn : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hhn_lt.le
    have h1 : (hn : ℝ) * X / (A : ℝ) ≤ 2 * ((K : ℝ) * X / (A : ℝ)) := by
      rw [show 2 * ((K : ℝ) * X / (A : ℝ)) = (2 * (K : ℝ)) * X / (A : ℝ) by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hhn_le hX.le) hApos.le
    have hsq : (4 * Real.sqrt ((hn : ℝ) * X / (A : ℝ))) ^ 2 ≤
        (6 * Real.sqrt ((K : ℝ) * X / (A : ℝ))) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      nlinarith [div_nonneg (mul_nonneg hKpos.le hX.le) hApos.le]
    nlinarith [Real.sqrt_nonneg ((hn : ℝ) * X / (A : ℝ)), Real.sqrt_nonneg ((K : ℝ) * X / (A : ℝ))]
  have ht3 :
      6 * Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / ((hn : ℝ) * X)) ≤
        6 * Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / X) := by
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
    have hhn1r : (1 : ℝ) ≤ (hn : ℝ) := Nat.one_le_cast.mpr hhn1
    exact div_le_div_of_nonneg_left (by positivity) hX (by nlinarith)
  linarith

/- Section 6: Elementary divisor bound d(m) ≤ C * m ^ ε -/

private lemma finset_prod_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (ε : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ ε = ∏ i ∈ s, (f i) ^ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a (Finset.mem_insert_self a s))
        (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private lemma card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C > 0, ∀ m : ℕ, m ≥ 1 → (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ ε := by
  set r : ℝ := (2 : ℝ) ^ ε - 1
  have hr_pos : 0 < r := by
    have : (1 : ℝ) < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
    linarith
  have hr_le1 : r ≤ 1 := by
    have : (2 : ℝ) ^ ε ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
    rw [Real.rpow_one] at this
    linarith
  set P : ℕ := Nat.ceil ((2 : ℝ) ^ (1 / ε))
  refine ⟨(1 / r) ^ P, by positivity, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by omega
  have hcard : (m.divisors.card : ℝ) =
      ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) := by
    have h := Nat.card_divisors hm0
    exact_mod_cast h
  have hm_prod : (m : ℝ) ^ ε =
      ∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p)) ^ ε := by
    have hnat : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      have h := Nat.prod_factorization_pow_eq_self hm0
      simpa [Finsupp.prod, Nat.support_factorization] using h.symm
    have hr : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ) ^ m.factorization p := by
      exact_mod_cast hnat
    rw [hr, finset_prod_rpow _ _ _ (fun p _ => by positivity)]
  have hfactor_le : ∀ p ∈ m.primeFactors,
      ((m.factorization p : ℝ) + 1) / ((p : ℝ) ^ (m.factorization p)) ^ ε ≤
        if p < P then 1 / r else 1 := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hprime.two_le
    set k : ℕ := m.factorization p
    have hk1 : 1 ≤ k := by
      have hne : m.factorization p ≠ 0 := Finsupp.mem_support_iff.mp (Nat.support_factorization m ▸ hp)
      omega
    have hpow_eq : ((p : ℝ) ^ k) ^ ε = ((p : ℝ) ^ ε) ^ k := by
      rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul (by positivity), mul_comm,
        Real.rpow_mul (by positivity), Real.rpow_natCast]
    rw [hpow_eq]
    split_ifs with hlt
    · have h2p : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hp2 hε.le
      have h1r : (1 + r) ^ k ≤ ((p : ℝ) ^ ε) ^ k := by
        have heq : 1 + r = (2 : ℝ) ^ ε := by simp only [r]; ring
        rw [heq]
        exact pow_le_pow_left₀ (by positivity) h2p k
      have hbern : 1 + (k : ℝ) * r ≤ (1 + r) ^ k := one_add_mul_le_pow (by linarith) k
      have hkr : ((k : ℝ) + 1) * r ≤ ((p : ℝ) ^ ε) ^ k := by nlinarith
      rw [div_le_div_iff₀ (by positivity) hr_pos]
      linarith
    · have hp_ge : (2 : ℝ) ^ (1 / ε) ≤ (p : ℝ) :=
        (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
      have h2_le : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        have h1 := Real.rpow_le_rpow (by positivity) hp_ge hε.le
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one] at h1
        exact h1
      have h2k : ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k := by
        have hnat : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
        exact_mod_cast hnat
      have hpk : ((k : ℝ) + 1) ≤ ((p : ℝ) ^ ε) ^ k :=
        h2k.trans (pow_le_pow_left₀ (by norm_num) h2_le k)
      rw [div_le_one (by positivity)]
      exact hpk
  have hdiv : (m.divisors.card : ℝ) / (m : ℝ) ^ ε ≤ (1 / r) ^ P := by
    rw [hcard, hm_prod, ← Finset.prod_div_distrib]
    calc ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) / ((p : ℝ) ^ (m.factorization p)) ^ ε
        ≤ ∏ p ∈ m.primeFactors, (if p < P then 1 / r else 1) :=
          Finset.prod_le_prod (fun _ _ => by positivity) hfactor_le
      _ = ∏ _p ∈ m.primeFactors.filter (· < P), (1 / r) := by
          rw [← Finset.prod_filter_mul_prod_filter_not m.primeFactors (· < P)]
          have h1 : ∏ p ∈ m.primeFactors.filter (· < P), (if p < P then 1 / r else 1) =
              ∏ _p ∈ m.primeFactors.filter (· < P), (1 / r) :=
            Finset.prod_congr rfl fun p hp => if_pos (Finset.mem_filter.mp hp).2
          have h2 : ∏ p ∈ m.primeFactors.filter (fun p => ¬p < P), (if p < P then 1 / r else 1) = 1 :=
            Finset.prod_eq_one fun p hp => if_neg (Finset.mem_filter.mp hp).2
          rw [h1, h2, mul_one]
      _ = (1 / r) ^ (m.primeFactors.filter (· < P)).card := by
          rw [Finset.prod_const]
      _ ≤ (1 / r) ^ P := by
          have h1r : (1 : ℝ) ≤ 1 / r := by rw [le_div_iff₀ hr_pos]; linarith
          have hsub : m.primeFactors.filter (· < P) ⊆ Finset.range P := fun p hp =>
            Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
          have hcard_le : (m.primeFactors.filter (· < P)).card ≤ P := by
            simpa using Finset.card_le_card hsub
          exact pow_le_pow_right₀ h1r hcard_le
  rw [div_le_iff₀ (by positivity)] at hdiv
  exact hdiv

/- Section 7: Asymptotic assembly and main theorem -/

private lemma eventually_mul_rpow_lt_rpow {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℕ in atTop, C * (x : ℝ) ^ a < (x : ℝ) ^ b := by
  have hba : 0 < b - a := by linarith
  have htop : Tendsto (fun x : ℕ => (x : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hba).comp tendsto_natCast_atTop_atTop
  filter_upwards [htop.eventually_gt_atTop (max C 1), eventually_ge_atTop 1] with x hx hx1
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr hx1
  have hC : C < (x : ℝ) ^ (b - a) := lt_of_le_of_lt (le_max_left _ _) hx
  have hmul : C * (x : ℝ) ^ a < (x : ℝ) ^ (b - a) * (x : ℝ) ^ a :=
    mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hxpos a)
  rw [← Real.rpow_add hxpos, sub_add_cancel] at hmul
  exact hmul

private lemma eventually_rpow_floor_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ a / 2 ≤ (⌊(x : ℝ) ^ a⌋₊ : ℝ) ∧
        (⌊(x : ℝ) ^ a⌋₊ : ℝ) ≤ (x : ℝ) ^ a ∧
        1 ≤ ⌊(x : ℝ) ^ a⌋₊ := by
  have htop : Tendsto (fun x : ℕ => (x : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  filter_upwards [htop.eventually_ge_atTop 2] with x hx
  have hle : (⌊(x : ℝ) ^ a⌋₊ : ℝ) ≤ (x : ℝ) ^ a := Nat.floor_le (by linarith)
  have hlt : (x : ℝ) ^ a < (⌊(x : ℝ) ^ a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h1 : 1 ≤ ⌊(x : ℝ) ^ a⌋₊ := by
    rw [Nat.one_le_floor_iff]
    linarith
  exact ⟨by linarith, hle, h1⟩

private lemma log_le_rpow_aux (A : ℕ) (hA : 1 ≤ A) :
    1 + Real.log (A : ℝ) ≤ 101 * (A : ℝ) ^ (1 / 100 : ℝ) := by
  have hApos : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hA1 : (1 : ℝ) ≤ A := Nat.one_le_cast.mpr hA
  have hpow_ge1 : (1 : ℝ) ≤ (A : ℝ) ^ (1 / 100 : ℝ) := Real.one_le_rpow hA1 (by norm_num)
  have hlog : Real.log ((A : ℝ) ^ (1 / 100 : ℝ)) ≤ (A : ℝ) ^ (1 / 100 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_rpow hApos] at hlog
  linarith

private lemma rpow_mul_eq {x a b c : ℝ} (hx : 0 < x) (h : a + b = c) :
    x ^ a * x ^ b = x ^ c := by
  rw [← Real.rpow_add hx, h]

private lemma rpow_div_eq {x a b c : ℝ} (hx : 0 < x) (h : a - b = c) :
    x ^ a / x ^ b = x ^ c := by
  rw [← Real.rpow_sub hx, h]

private lemma self_div_rpow_eq {x b c : ℝ} (hx : 0 < x) (h : 1 - b = c) :
    x / x ^ b = x ^ c := by
  rw [show x / x ^ b = x ^ (1 : ℝ) / x ^ b by rw [Real.rpow_one]]
  exact rpow_div_eq hx h

private lemma rpow_pow_eq {x a c : ℝ} {n : ℕ} (hx : 0 ≤ x) (h : a * (n : ℝ) = c) :
    (x ^ a) ^ n = x ^ c := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, h]

private lemma sqrt_mul_rpow_eq {x k r a b : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hk : r ^ 2 = k)
    (h : a / 2 = b) :
    Real.sqrt (k * x ^ a) = r * x ^ b := by
  rw [← hk, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx, mul_one_div, h]

open Classical in
noncomputable def smoothFinset (x z y : ℕ) : Finset ℕ :=
  (Finset.range z).filter (fun i => ∀ p ∈ (x + i + 1).primeFactors, p ≤ y)

private lemma mem_smoothFinset {x z y i : ℕ} :
    i ∈ smoothFinset x z y ↔ i < z ∧ ∀ p ∈ (x + i + 1).primeFactors, p ≤ y := by
  classical
  simp [smoothFinset]

open Classical in
private lemma row_good_count_ge (x z B A K b : ℕ)
    (hx : 1 ≤ x) (hz : 1 ≤ z) (hB : 1 ≤ B) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hb1 : B < b) (hb2 : b ≤ 2 * B)
    (hKδ : 1 / ((K : ℝ) * ((z : ℝ) / (4 * (A : ℝ) * (B : ℝ)))) ^ 4 ≤ 1 / (8 * (K : ℝ)))
    (hcond : 8 * (K : ℝ) * ((x : ℝ) / (b : ℝ)) ≤ (A : ℝ) ^ 3)
    (hE :
      6 * Real.sqrt ((K : ℝ) * ((x : ℝ) / (b : ℝ)) / (A : ℝ)) +
        16 * Real.sqrt ((A : ℝ) * (1 + Real.log A)) +
        6 * Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / ((x : ℝ) / (b : ℝ))) ≤
      (A : ℝ) / (8 * (K : ℝ))) :
    (A : ℝ) / (4 * (K : ℝ)) ≤
      (((Finset.Ioc A (2 * A)).filter
        (fun a => ∃ c : ℕ, x < a * b * c ∧ a * b * c ≤ x + z)).card : ℝ) := by
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hzpos : (0 : ℝ) < z := Nat.cast_pos.mpr hz
  have hApos : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hbpos : (0 : ℝ) < b := Nat.cast_pos.mpr (by omega)
  set X : ℝ := (x : ℝ) / (b : ℝ)
  set δ : ℝ := (z : ℝ) / (4 * (A : ℝ) * (B : ℝ))
  have hX_pos : 0 < X := by positivity
  have hδ_pos : 0 < δ := by positivity
  set E : ℝ :=
    6 * Real.sqrt ((K : ℝ) * X / (A : ℝ)) +
      16 * Real.sqrt ((A : ℝ) * (1 + Real.log A)) +
      6 * Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / X)
  have hE_nonneg : 0 ≤ E := by positivity
  let isGood (a : ℕ) : Prop := ∃ c : ℕ, x < a * b * c ∧ a * b * c ≤ x + z
  have hpt : ∀ a ∈ Finset.Ioc A (2 * A),
      ‖D K (X / (a : ℝ) + δ / 2)‖ ^ 4 / (K : ℝ) ^ 4 - 1 / ((K : ℝ) * δ) ^ 4 ≤
        if isGood a then (1 : ℝ) else 0 := by
    intro a ha
    have ha1 : A < a := (Finset.mem_Ioc.mp ha).1
    have ha2 : a ≤ 2 * A := (Finset.mem_Ioc.mp ha).2
    have hapos : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
    have hminor := quartic_fejer_minorant K hK (X / (a : ℝ)) δ hδ_pos
    refine hminor.trans ?_
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      obtain ⟨m, hm1, hm2⟩ := h1
      have hm_pos : (0 : ℝ) < (m : ℝ) := lt_trans (by positivity) hm1
      have hm_int_pos : (0 : ℤ) < m := by exact_mod_cast hm_pos
      set c : ℕ := m.toNat
      have hc_eq : (c : ℝ) = (m : ℝ) := by
        have : (c : ℤ) = m := Int.toNat_of_nonneg hm_int_pos.le
        exact_mod_cast this
      rw [← hc_eq] at hm1 hm2
      have hX_div : X / (a : ℝ) = (x : ℝ) / ((a : ℝ) * (b : ℝ)) := by
        simp only [X]; rw [div_div, mul_comm (b : ℝ)]
      rw [hX_div] at hm1 hm2
      have hlow_r : (x : ℝ) < ((a * b * c : ℕ) : ℝ) := by
        rw [div_lt_iff₀ (by positivity)] at hm1
        push_cast; linarith
      have hhigh_r : ((a * b * c : ℕ) : ℝ) < (x : ℝ) + (z : ℝ) := by
        have h1' : (c : ℝ) * ((a : ℝ) * (b : ℝ)) < (x : ℝ) + δ * ((a : ℝ) * (b : ℝ)) := by
          have := mul_lt_mul_of_pos_right hm2 (by positivity : 0 < (a : ℝ) * (b : ℝ))
          have heq : (x : ℝ) / ((a : ℝ) * (b : ℝ)) * ((a : ℝ) * (b : ℝ)) = (x : ℝ) :=
            div_mul_cancel₀ _ (by positivity)
          linarith
        have hab_le : (a : ℝ) * (b : ℝ) ≤ 4 * (A : ℝ) * (B : ℝ) := by
          have haR : (a : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast ha2
          have hbR : (b : ℝ) ≤ 2 * (B : ℝ) := by exact_mod_cast hb2
          nlinarith
        have hδab : δ * ((a : ℝ) * (b : ℝ)) ≤ (z : ℝ) := by
          simp only [δ]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
        push_cast; linarith
      have hlow_n : x < a * b * c := by exact_mod_cast hlow_r
      have hhigh_n : a * b * c ≤ x + z := by
        have : a * b * c < x + z := by exact_mod_cast hhigh_r
        omega
      exact h2 ⟨c, hlow_n, hhigh_n⟩
    · exact zero_le_one
    · exact le_rfl
  have hsum_pt := Finset.sum_le_sum hpt
  have hcard_rhs :
      ∑ a ∈ Finset.Ioc A (2 * A), (if isGood a then (1 : ℝ) else 0) =
        (((Finset.Ioc A (2 * A)).filter isGood).card : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard_rhs, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul] at hsum_pt
  have hIoc_card : (Finset.Ioc A (2 * A)).card = A := by
    rw [Nat.card_Ioc]; omega
  have hfejer := sum_norm_D_pow_four_ge K hK (Finset.Ioc A (2 * A))
    (fun a => X / (a : ℝ)) (δ / 2) E hE_nonneg
    (exp_sum_reciprocal_uniform X hX_pos A K hA hK hcond)
  rw [hIoc_card] at hsum_pt hfejer
  have hsub_le : (A : ℝ) * (1 / ((K : ℝ) * δ) ^ 4) ≤ (A : ℝ) / (8 * (K : ℝ)) := by
    calc (A : ℝ) * (1 / ((K : ℝ) * δ) ^ 4)
        ≤ (A : ℝ) * (1 / (8 * (K : ℝ))) := mul_le_mul_of_nonneg_left hKδ hApos.le
      _ = (A : ℝ) / (8 * (K : ℝ)) := by ring
  have hhalf : (A : ℝ) / (2 * (K : ℝ)) - (A : ℝ) / (8 * (K : ℝ)) - (A : ℝ) / (8 * (K : ℝ)) =
      (A : ℝ) / (4 * (K : ℝ)) := by ring
  linarith

open Classical in
private lemma smooth_count_from_rows (x z B A K y : ℕ) (C0 : ℝ) (hC0 : 0 < C0)
    (hdiv : ∀ m : ℕ, m ≥ 1 → (m.divisors.card : ℝ) ≤ C0 * (m : ℝ) ^ (1 / 100 : ℝ))
    (hx : 1 ≤ x) (hz : z ≤ x) (hB : 1 ≤ B) (hA : 1 ≤ A)
    (h2A : 2 * A ≤ y) (h2B : 2 * B ≤ y)
    (hc_bound : 2 * (x : ℝ) / ((A : ℝ) * (B : ℝ)) < (y : ℝ) + 1)
    (hrows : ∀ b ∈ Finset.Ioc B (2 * B),
      (A : ℝ) / (4 * (K : ℝ)) ≤
        (((Finset.Ioc A (2 * A)).filter
          (fun a => ∃ c : ℕ, x < a * b * c ∧ a * b * c ≤ x + z)).card : ℝ))
    (hcomp :
      ((y + 1 : ℕ) : ℝ) * (C0 ^ 2 * (2 * (x : ℝ)) ^ (1 / 50 : ℝ)) <
        (B : ℝ) * ((A : ℝ) / (4 * (K : ℝ)))) :
    y + 1 < (smoothFinset x z y).card := by
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hApos : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  let isGood (a b : ℕ) : Prop := ∃ c : ℕ, x < a * b * c ∧ a * b * c ≤ x + z
  let Pgood := ((Finset.Ioc A (2 * A)) ×ˢ (Finset.Ioc B (2 * B))).filter (fun ab => isGood ab.1 ab.2)
  have hPgood_ge : (B : ℝ) * ((A : ℝ) / (4 * (K : ℝ))) ≤ (Pgood.card : ℝ) := by
    have hcard_sum : (Pgood.card : ℝ) =
        ∑ b ∈ Finset.Ioc B (2 * B),
          (((Finset.Ioc A (2 * A)).filter (fun a => isGood a b)).card : ℝ) := by
      have hnat : Pgood.card =
          ∑ b ∈ Finset.Ioc B (2 * B),
            ((Finset.Ioc A (2 * A)).filter (fun a => isGood a b)).card := by
        simp only [Pgood, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
        rw [Finset.sum_comm]
      exact_mod_cast hnat
    rw [hcard_sum]
    calc (B : ℝ) * ((A : ℝ) / (4 * (K : ℝ)))
        = ∑ _b ∈ Finset.Ioc B (2 * B), (A : ℝ) / (4 * (K : ℝ)) := by
            rw [Finset.sum_const, Nat.card_Ioc, show 2 * B - B = B by omega, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hrows
  have hPsub : Pgood ⊆
      (smoothFinset x z y).biUnion (fun i => (x + i + 1).divisors ×ˢ (x + i + 1).divisors) := by
    intro ab hab
    have hmem := (Finset.mem_filter.mp hab).1
    have ha_mem := (Finset.mem_product.mp hmem).1
    have hb_mem := (Finset.mem_product.mp hmem).2
    have ha1 : A < ab.1 := (Finset.mem_Ioc.mp ha_mem).1
    have ha2 : ab.1 ≤ 2 * A := (Finset.mem_Ioc.mp ha_mem).2
    have hb1 : B < ab.2 := (Finset.mem_Ioc.mp hb_mem).1
    have hb2 : ab.2 ≤ 2 * B := (Finset.mem_Ioc.mp hb_mem).2
    obtain ⟨c, hc1, hc2⟩ := (Finset.mem_filter.mp hab).2
    set i : ℕ := ab.1 * ab.2 * c - x - 1
    have hi_eq : x + i + 1 = ab.1 * ab.2 * c := by omega
    have hi_lt : i < z := by omega
    have hc_le_y : c ≤ y := by
      have hprod_le : (ab.1 : ℝ) * (ab.2 : ℝ) * (c : ℝ) ≤ 2 * (x : ℝ) := by
        have h1 : ab.1 * ab.2 * c ≤ 2 * x := by omega
        exact_mod_cast h1
      have hab_ge : (A : ℝ) * (B : ℝ) ≤ (ab.1 : ℝ) * (ab.2 : ℝ) :=
        mul_le_mul (by exact_mod_cast ha1.le) (by exact_mod_cast hb1.le) hBpos.le (by positivity)
      have hc_lt : (c : ℝ) < (y : ℝ) + 1 := by
        have h1 : (A : ℝ) * (B : ℝ) * (c : ℝ) ≤ 2 * (x : ℝ) := by
          have := mul_le_mul_of_nonneg_right hab_ge (Nat.cast_nonneg c)
          linarith
        have h2 : (c : ℝ) ≤ 2 * (x : ℝ) / ((A : ℝ) * (B : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        linarith
      have hc_nat : c < y + 1 := by exact_mod_cast hc_lt
      omega
    have hi_mem : i ∈ smoothFinset x z y := by
      rw [mem_smoothFinset]
      refine ⟨hi_lt, fun p hp_mem => ?_⟩
      have hp : p.Prime := (Nat.mem_primeFactors.mp hp_mem).1
      have hpdvd : p ∣ x + i + 1 := (Nat.mem_primeFactors.mp hp_mem).2.1
      rw [hi_eq] at hpdvd
      rcases hp.dvd_mul.mp hpdvd with hab_dvd | hc_dvd
      · rcases hp.dvd_mul.mp hab_dvd with ha_dvd | hb_dvd
        · exact (Nat.le_of_dvd (by omega) ha_dvd).trans (ha2.trans h2A)
        · exact (Nat.le_of_dvd (by omega) hb_dvd).trans (hb2.trans h2B)
      · have hc_pos : 0 < c := by
          by_contra hc0
          have : c = 0 := by omega
          rw [this, mul_zero] at hc1
          omega
        exact (Nat.le_of_dvd hc_pos hc_dvd).trans hc_le_y
    refine Finset.mem_biUnion.mpr ⟨i, hi_mem, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · exact Nat.mem_divisors.mpr ⟨by rw [hi_eq]; exact ⟨ab.2 * c, by ring⟩, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨by rw [hi_eq]; exact ⟨ab.1 * c, by ring⟩, by omega⟩
  have hcard_le : Pgood.card ≤ ∑ i ∈ smoothFinset x z y, ((x + i + 1).divisors.card) ^ 2 := by
    calc Pgood.card
        ≤ ((smoothFinset x z y).biUnion
            (fun i => (x + i + 1).divisors ×ˢ (x + i + 1).divisors)).card :=
          Finset.card_le_card hPsub
      _ ≤ ∑ i ∈ smoothFinset x z y, ((x + i + 1).divisors ×ˢ (x + i + 1).divisors).card :=
          Finset.card_biUnion_le
      _ = ∑ i ∈ smoothFinset x z y, ((x + i + 1).divisors.card) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => by rw [Finset.card_product, sq]
  have hcard_leR : (Pgood.card : ℝ) ≤
      ∑ i ∈ smoothFinset x z y, (((x + i + 1).divisors.card : ℝ)) ^ 2 := by
    exact_mod_cast hcard_le
  have hfib : ∀ i ∈ smoothFinset x z y,
      (((x + i + 1).divisors.card : ℝ)) ^ 2 ≤ C0 ^ 2 * (2 * (x : ℝ)) ^ (1 / 50 : ℝ) := by
    intro i hi
    have hi_lt : i < z := (mem_smoothFinset.mp hi).1
    have hd := hdiv (x + i + 1) (by omega)
    have hm_le : ((x + i + 1 : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by
      have : x + i + 1 ≤ 2 * x := by omega
      exact_mod_cast this
    have hd2 : ((x + i + 1).divisors.card : ℝ) ≤ C0 * (2 * (x : ℝ)) ^ (1 / 100 : ℝ) :=
      hd.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hm_le (by norm_num)) hC0.le)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hd2 2
    rw [mul_pow, rpow_pow_eq (by positivity) (by norm_num : (1 / 100 : ℝ) * (2 : ℕ) = 1 / 50)] at hsq
    exact hsq
  have hPgood_le :
      (Pgood.card : ℝ) ≤ ((smoothFinset x z y).card : ℝ) * (C0 ^ 2 * (2 * (x : ℝ)) ^ (1 / 50 : ℝ)) := by
    calc (Pgood.card : ℝ)
        ≤ ∑ i ∈ smoothFinset x z y, (((x + i + 1).divisors.card : ℝ)) ^ 2 := hcard_leR
      _ ≤ ∑ _i ∈ smoothFinset x z y, (C0 ^ 2 * (2 * (x : ℝ)) ^ (1 / 50 : ℝ)) :=
          Finset.sum_le_sum hfib
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hstrict :
      ((y + 1 : ℕ) : ℝ) * (C0 ^ 2 * (2 * (x : ℝ)) ^ (1 / 50 : ℝ)) <
        ((smoothFinset x z y).card : ℝ) * (C0 ^ 2 * (2 * (x : ℝ)) ^ (1 / 50 : ℝ)) := by
    linarith
  have hS_gtR : ((y + 1 : ℕ) : ℝ) < ((smoothFinset x z y).card : ℝ) :=
    lt_of_mul_lt_mul_right hstrict (by positivity)
  exact_mod_cast hS_gtR

open Classical in
private lemma row_good_count_from_rpow (x z B A K b : ℕ)
    (hx10 : 10 ≤ x) (hzB : (x : ℝ) ^ (49 / 100 : ℝ) / 2 ≤ (z : ℝ) ∧ (z : ℝ) ≤ (x : ℝ) ^ (49 / 100 : ℝ) ∧ 1 ≤ z)
    (hBB : (x : ℝ) ^ (15 / 100 : ℝ) / 2 ≤ (B : ℝ) ∧ (B : ℝ) ≤ (x : ℝ) ^ (15 / 100 : ℝ) ∧ 1 ≤ B)
    (hAB : (x : ℝ) ^ (17 / 40 : ℝ) / 2 ≤ (A : ℝ) ∧ (A : ℝ) ≤ (x : ℝ) ^ (17 / 40 : ℝ) ∧ 1 ≤ A)
    (hKB : (x : ℝ) ^ (3 / 25 : ℝ) / 2 ≤ (K : ℝ) ∧ (K : ℝ) ≤ (x : ℝ) ^ (3 / 25 : ℝ) ∧ 1 ≤ K)
    (hKδ : 1 / ((K : ℝ) * ((z : ℝ) / (4 * (A : ℝ) * (B : ℝ)))) ^ 4 ≤ 1 / (8 * (K : ℝ)))
    (hcondx : 128 * (x : ℝ) ^ (97 / 100 : ℝ) < (x : ℝ) ^ (51 / 40 : ℝ))
    (herr1x : 1000 * (x : ℝ) ^ (109 / 400 : ℝ) < (x : ℝ) ^ (61 / 200 : ℝ))
    (herr2x : 10000 * (x : ℝ) ^ (87 / 400 : ℝ) < (x : ℝ) ^ (61 / 200 : ℝ))
    (hb1 : B < b) (hb2 : b ≤ 2 * B) :
    (A : ℝ) / (4 * (K : ℝ)) ≤
      (((Finset.Ioc A (2 * A)).filter
        (fun a => ∃ c : ℕ, x < a * b * c ∧ a * b * c ≤ x + z)).card : ℝ) := by
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr (by omega)
  have hx1 : (1 : ℝ) ≤ x := Nat.one_le_cast.mpr (by omega)
  have hApos : (0 : ℝ) < A := Nat.cast_pos.mpr hAB.2.2
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hKB.2.2
  have hbpos : (0 : ℝ) < b := Nat.cast_pos.mpr (by omega)
  have hAK_ge : (x : ℝ) ^ (61 / 200 : ℝ) / 2 ≤ (A : ℝ) / (K : ℝ) := by
    have h1 := div_le_div₀ (by positivity) hAB.1 hKpos hKB.2.1
    rw [show (x : ℝ) ^ (17 / 40 : ℝ) / 2 / (x : ℝ) ^ (3 / 25 : ℝ) =
        ((x : ℝ) ^ (17 / 40 : ℝ) / (x : ℝ) ^ (3 / 25 : ℝ)) / 2 by ring,
      rpow_div_eq hxpos (by norm_num : (17 / 40 : ℝ) - 3 / 25 = 61 / 200)] at h1
    exact h1
  have hlogA : 1 + Real.log (A : ℝ) ≤ 101 * (x : ℝ) ^ (1 / 100 : ℝ) := by
    have h1 := log_le_rpow_aux A hAB.2.2
    have hAx : (A : ℝ) ≤ (x : ℝ) := by
      have : (x : ℝ) ^ (17 / 40 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      rw [Real.rpow_one] at this
      linarith [hAB.2.1]
    have h2 : (A : ℝ) ^ (1 / 100 : ℝ) ≤ (x : ℝ) ^ (1 / 100 : ℝ) :=
      Real.rpow_le_rpow hApos.le hAx (by norm_num)
    linarith
  have hA3_ge : (x : ℝ) ^ (51 / 40 : ℝ) / 8 ≤ (A : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hAB.1 3
    rw [div_pow, rpow_pow_eq hxpos.le (by norm_num : (17 / 40 : ℝ) * (3 : ℕ) = 51 / 40)] at this
    norm_num at this
    exact this
  have hA3_le : (A : ℝ) ^ 3 ≤ (x : ℝ) ^ (51 / 40 : ℝ) := by
    have := pow_le_pow_left₀ hApos.le hAB.2.1 3
    rw [rpow_pow_eq hxpos.le (by norm_num : (17 / 40 : ℝ) * (3 : ℕ) = 51 / 40)] at this
    exact this
  set X : ℝ := (x : ℝ) / (b : ℝ)
  have hX_pos : 0 < X := by positivity
  have hX_ge : (x : ℝ) ^ (17 / 20 : ℝ) / 2 ≤ X := by
    have hb_le : (b : ℝ) ≤ 2 * (x : ℝ) ^ (15 / 100 : ℝ) := by
      have : (b : ℝ) ≤ 2 * (B : ℝ) := by exact_mod_cast hb2
      linarith [hBB.2.1]
    have h1 : (x : ℝ) / (2 * (x : ℝ) ^ (15 / 100 : ℝ)) ≤ X :=
      div_le_div_of_nonneg_left hxpos.le hbpos hb_le
    rw [show (x : ℝ) / (2 * (x : ℝ) ^ (15 / 100 : ℝ)) =
        ((x : ℝ) / (x : ℝ) ^ (15 / 100 : ℝ)) / 2 by ring,
      self_div_rpow_eq hxpos (by norm_num : 1 - (15 / 100 : ℝ) = 17 / 20)] at h1
    exact h1
  have hX_le : X ≤ 2 * (x : ℝ) ^ (17 / 20 : ℝ) := by
    have hb_ge : (x : ℝ) ^ (15 / 100 : ℝ) / 2 ≤ (b : ℝ) := by
      have : (B : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1.le
      linarith [hBB.1]
    have h1 : X ≤ (x : ℝ) / ((x : ℝ) ^ (15 / 100 : ℝ) / 2) :=
      div_le_div_of_nonneg_left hxpos.le (by positivity) hb_ge
    rw [show (x : ℝ) / ((x : ℝ) ^ (15 / 100 : ℝ) / 2) =
        2 * ((x : ℝ) / (x : ℝ) ^ (15 / 100 : ℝ)) by ring,
      self_div_rpow_eq hxpos (by norm_num : 1 - (15 / 100 : ℝ) = 17 / 20)] at h1
    exact h1
  have hKX_le : (K : ℝ) * X ≤ 2 * (x : ℝ) ^ (97 / 100 : ℝ) := by
    have hm := mul_le_mul hKB.2.1 hX_le hX_pos.le (by positivity)
    rw [show (x : ℝ) ^ (3 / 25 : ℝ) * (2 * (x : ℝ) ^ (17 / 20 : ℝ)) =
        2 * ((x : ℝ) ^ (3 / 25 : ℝ) * (x : ℝ) ^ (17 / 20 : ℝ)) by ring,
      rpow_mul_eq hxpos (by norm_num : (3 / 25 : ℝ) + 17 / 20 = 97 / 100)] at hm
    exact hm
  have hcond_AX : 8 * (K : ℝ) * X ≤ (A : ℝ) ^ 3 := by linarith
  have hE1 : 6 * Real.sqrt ((K : ℝ) * X / (A : ℝ)) ≤ (A : ℝ) / (24 * (K : ℝ)) := by
    have harg : (K : ℝ) * X / (A : ℝ) ≤ 4 * (x : ℝ) ^ (109 / 200 : ℝ) := by
      have h1 := div_le_div₀ (by positivity) hKX_le (by positivity) hAB.1
      rw [show 2 * (x : ℝ) ^ (97 / 100 : ℝ) / ((x : ℝ) ^ (17 / 40 : ℝ) / 2) =
          4 * ((x : ℝ) ^ (97 / 100 : ℝ) / (x : ℝ) ^ (17 / 40 : ℝ)) by ring,
        rpow_div_eq hxpos (by norm_num : (97 / 100 : ℝ) - 17 / 40 = 109 / 200)] at h1
      exact h1
    have hsq : Real.sqrt ((K : ℝ) * X / (A : ℝ)) ≤ 2 * (x : ℝ) ^ (109 / 400 : ℝ) := by
      have h1 := Real.sqrt_le_sqrt harg
      rw [sqrt_mul_rpow_eq hxpos.le (by norm_num : (0 : ℝ) ≤ 2) (by norm_num)
        (by norm_num : (109 / 200 : ℝ) / 2 = 109 / 400)] at h1
      exact h1
    have hpos1 : (0 : ℝ) ≤ (x : ℝ) ^ (109 / 400 : ℝ) := by positivity
    linarith [show (A : ℝ) / (24 * (K : ℝ)) = ((A : ℝ) / (K : ℝ)) / 24 by ring]
  have hE2 : 16 * Real.sqrt ((A : ℝ) * (1 + Real.log A)) ≤ (A : ℝ) / (24 * (K : ℝ)) := by
    have harg : (A : ℝ) * (1 + Real.log A) ≤ 121 * (x : ℝ) ^ (87 / 200 : ℝ) := by
      have hm := mul_le_mul hAB.2.1 hlogA (by positivity) (by positivity)
      rw [show (x : ℝ) ^ (17 / 40 : ℝ) * (101 * (x : ℝ) ^ (1 / 100 : ℝ)) =
          101 * ((x : ℝ) ^ (17 / 40 : ℝ) * (x : ℝ) ^ (1 / 100 : ℝ)) by ring,
        rpow_mul_eq hxpos (by norm_num : (17 / 40 : ℝ) + 1 / 100 = 87 / 200)] at hm
      linarith [Real.rpow_pos_of_pos hxpos (87 / 200 : ℝ)]
    have hsq : Real.sqrt ((A : ℝ) * (1 + Real.log A)) ≤ 11 * (x : ℝ) ^ (87 / 400 : ℝ) := by
      have h1 := Real.sqrt_le_sqrt harg
      rw [sqrt_mul_rpow_eq hxpos.le (by norm_num : (0 : ℝ) ≤ 11) (by norm_num)
        (by norm_num : (87 / 200 : ℝ) / 2 = 87 / 400)] at h1
      exact h1
    have hpos2 : (0 : ℝ) ≤ (x : ℝ) ^ (87 / 400 : ℝ) := by positivity
    linarith [show (A : ℝ) / (24 * (K : ℝ)) = ((A : ℝ) / (K : ℝ)) / 24 by ring]
  have hE3 : 6 * Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / X) ≤ (A : ℝ) / (24 * (K : ℝ)) := by
    have harg : (A : ℝ) ^ 3 * (1 + Real.log A) / X ≤ 225 * (x : ℝ) ^ (87 / 200 : ℝ) := by
      have hnum := mul_le_mul hA3_le hlogA (by positivity) (by positivity)
      have hdiv := div_le_div₀ (by positivity) hnum (by positivity) hX_ge
      rw [show (x : ℝ) ^ (51 / 40 : ℝ) * (101 * (x : ℝ) ^ (1 / 100 : ℝ)) /
            ((x : ℝ) ^ (17 / 20 : ℝ) / 2) =
          202 * (((x : ℝ) ^ (51 / 40 : ℝ) * (x : ℝ) ^ (1 / 100 : ℝ)) /
            (x : ℝ) ^ (17 / 20 : ℝ)) by ring,
        rpow_mul_eq hxpos (by norm_num : (51 / 40 : ℝ) + 1 / 100 = 257 / 200),
        rpow_div_eq hxpos (by norm_num : (257 / 200 : ℝ) - 17 / 20 = 87 / 200)] at hdiv
      linarith [Real.rpow_pos_of_pos hxpos (87 / 200 : ℝ)]
    have hsq : Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / X) ≤ 15 * (x : ℝ) ^ (87 / 400 : ℝ) := by
      have h1 := Real.sqrt_le_sqrt harg
      rw [sqrt_mul_rpow_eq hxpos.le (by norm_num : (0 : ℝ) ≤ 15) (by norm_num)
        (by norm_num : (87 / 200 : ℝ) / 2 = 87 / 400)] at h1
      exact h1
    have hpos3 : (0 : ℝ) ≤ (x : ℝ) ^ (87 / 400 : ℝ) := by positivity
    linarith [show (A : ℝ) / (24 * (K : ℝ)) = ((A : ℝ) / (K : ℝ)) / 24 by ring]
  have hE :
      6 * Real.sqrt ((K : ℝ) * X / (A : ℝ)) +
        16 * Real.sqrt ((A : ℝ) * (1 + Real.log A)) +
        6 * Real.sqrt ((A : ℝ) ^ 3 * (1 + Real.log A) / X) ≤
      (A : ℝ) / (8 * (K : ℝ)) := by
    have : (A : ℝ) / (8 * (K : ℝ)) =
        (A : ℝ) / (24 * (K : ℝ)) + (A : ℝ) / (24 * (K : ℝ)) + (A : ℝ) / (24 * (K : ℝ)) := by ring
    linarith
  exact row_good_count_ge x z B A K b (by omega) hzB.2.2 hBB.2.2 hAB.2.2 hKB.2.2
    hb1 hb2 hKδ hcond_AX hE

open Classical in
private lemma eventually_smooth_count_gt :
    ∀ᶠ x : ℕ in atTop,
      let z := ⌊(x : ℝ) ^ (49 / 100 : ℝ)⌋₊
      let y := ⌊8 * (x : ℝ) ^ (17 / 40 : ℝ)⌋₊
      y + 1 < (smoothFinset x z y).card := by
  obtain ⟨C0, hC0_pos, hdiv_bound⟩ := card_divisors_le_rpow (1 / 100) (by norm_num) (by norm_num)
  have hK3d4 := eventually_mul_rpow_lt_rpow (a := (0 : ℝ)) (b := (1 / 50 : ℝ)) (by norm_num) 262144
  have hcond_e := eventually_mul_rpow_lt_rpow (a := (97 / 100 : ℝ)) (b := (51 / 40 : ℝ)) (by norm_num) 128
  have herr1_e := eventually_mul_rpow_lt_rpow (a := (109 / 400 : ℝ)) (b := (61 / 200 : ℝ)) (by norm_num) 1000
  have herr2_e := eventually_mul_rpow_lt_rpow (a := (87 / 400 : ℝ)) (b := (61 / 200 : ℝ)) (by norm_num) 10000
  have hfinal_e := eventually_mul_rpow_lt_rpow (a := (89 / 200 : ℝ)) (b := (91 / 200 : ℝ)) (by norm_num)
    (16 * 9 * C0 ^ 2 * (2 : ℝ) ^ (1 / 50 : ℝ))
  have hz_lt_x := eventually_mul_rpow_lt_rpow (a := (49 / 100 : ℝ)) (b := (1 : ℝ)) (by norm_num) 1
  have h1_lt_y := eventually_mul_rpow_lt_rpow (a := (0 : ℝ)) (b := (17 / 40 : ℝ)) (by norm_num) 1
  have hB_le_A := eventually_mul_rpow_lt_rpow (a := (15 / 100 : ℝ)) (b := (17 / 40 : ℝ)) (by norm_num) 1
  filter_upwards [
    eventually_ge_atTop 10,
    eventually_rpow_floor_bounds (a := (49 / 100 : ℝ)) (by norm_num),
    eventually_rpow_floor_bounds (a := (15 / 100 : ℝ)) (by norm_num),
    eventually_rpow_floor_bounds (a := (17 / 40 : ℝ)) (by norm_num),
    eventually_rpow_floor_bounds (a := (3 / 25 : ℝ)) (by norm_num),
    hK3d4, hcond_e, herr1_e, herr2_e, hfinal_e, hz_lt_x, h1_lt_y, hB_le_A
  ] with x hx10 hzB hBB hAB hKB hK3d4x hcondx herr1x herr2x hfinalx hz_lt h1_y hBA
  dsimp only
  set z : ℕ := ⌊(x : ℝ) ^ (49 / 100 : ℝ)⌋₊
  set B : ℕ := ⌊(x : ℝ) ^ (15 / 100 : ℝ)⌋₊
  set A : ℕ := ⌊(x : ℝ) ^ (17 / 40 : ℝ)⌋₊
  set K : ℕ := ⌊(x : ℝ) ^ (3 / 25 : ℝ)⌋₊
  set y : ℕ := ⌊8 * (x : ℝ) ^ (17 / 40 : ℝ)⌋₊
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr (by omega)
  have hzpos : (0 : ℝ) < z := Nat.cast_pos.mpr hzB.2.2
  have hApos : (0 : ℝ) < A := Nat.cast_pos.mpr hAB.2.2
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hBB.2.2
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hKB.2.2
  set δ : ℝ := (z : ℝ) / (4 * (A : ℝ) * (B : ℝ))
  have hδ_pos : 0 < δ := by positivity
  have hδ_ge : (x : ℝ) ^ (-(17 / 200 : ℝ)) / 8 ≤ δ := by
    have hden : 4 * (A : ℝ) * (B : ℝ) ≤ 4 * (x : ℝ) ^ (23 / 40 : ℝ) := by
      have hm := mul_le_mul hAB.2.1 hBB.2.1 hBpos.le (by positivity)
      rw [rpow_mul_eq hxpos (by norm_num : (17 / 40 : ℝ) + 15 / 100 = 23 / 40)] at hm
      linarith
    have hstep := div_le_div₀ (by positivity) hzB.1 (by positivity) hden
    have hrew : (x : ℝ) ^ (49 / 100 : ℝ) / 2 / (4 * (x : ℝ) ^ (23 / 40 : ℝ)) =
        (x : ℝ) ^ (-(17 / 200 : ℝ)) / 8 := by
      rw [show (x : ℝ) ^ (49 / 100 : ℝ) / 2 / (4 * (x : ℝ) ^ (23 / 40 : ℝ)) =
          ((x : ℝ) ^ (49 / 100 : ℝ) / (x : ℝ) ^ (23 / 40 : ℝ)) / 8 by ring,
        rpow_div_eq hxpos (by norm_num : (49 / 100 : ℝ) - 23 / 40 = -(17 / 200))]
    linarith
  have hKδ : 1 / ((K : ℝ) * δ) ^ 4 ≤ 1 / (8 * (K : ℝ)) := by
    have hK3 : (x : ℝ) ^ (9 / 25 : ℝ) / 8 ≤ (K : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hKB.1 3
      rw [div_pow, rpow_pow_eq hxpos.le (by norm_num : (3 / 25 : ℝ) * (3 : ℕ) = 9 / 25)] at this
      norm_num at this
      exact this
    have hδ4 : (x : ℝ) ^ (-(17 / 50 : ℝ)) / 4096 ≤ δ ^ 4 := by
      have := pow_le_pow_left₀ (by positivity) hδ_ge 4
      rw [div_pow, rpow_pow_eq hxpos.le (by norm_num : -(17 / 200 : ℝ) * (4 : ℕ) = -(17 / 50))] at this
      norm_num at this
      exact this
    have hprod : 8 ≤ (K : ℝ) ^ 3 * δ ^ 4 := by
      have hm := mul_le_mul hK3 hδ4 (by positivity) (by positivity)
      rw [div_mul_div_comm, rpow_mul_eq hxpos (by norm_num : (9 / 25 : ℝ) + -(17 / 50) = 1 / 50)] at hm
      norm_num at hm
      simp only [Real.rpow_zero, mul_one] at hK3d4x
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((K : ℝ) * δ) ^ 4 = (K : ℝ) * ((K : ℝ) ^ 3 * δ ^ 4) := by ring
    nlinarith
  have hrows : ∀ b ∈ Finset.Ioc B (2 * B),
      (A : ℝ) / (4 * (K : ℝ)) ≤
        (((Finset.Ioc A (2 * A)).filter
          (fun a => ∃ c : ℕ, x < a * b * c ∧ a * b * c ≤ x + z)).card : ℝ) := by
    intro b hb
    exact row_good_count_from_rpow x z B A K b hx10 hzB hBB hAB hKB hKδ hcondx herr1x herr2x
      (Finset.mem_Ioc.mp hb).1 (Finset.mem_Ioc.mp hb).2
  have hz_le_x : z ≤ x := by
    have h1 : (z : ℝ) ≤ (x : ℝ) := by
      rw [Real.rpow_one, one_mul] at hz_lt
      linarith [hzB.2.1]
    exact_mod_cast h1
  have h2A_le_y : 2 * A ≤ y := by
    apply Nat.le_floor
    calc ((2 * A : ℕ) : ℝ) = 2 * (A : ℝ) := by push_cast; ring
      _ ≤ 2 * (x : ℝ) ^ (17 / 40 : ℝ) := by linarith [hAB.2.1]
      _ ≤ 8 * (x : ℝ) ^ (17 / 40 : ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have h2B_le_y : 2 * B ≤ y := by
    apply Nat.le_floor
    rw [one_mul] at hBA
    calc ((2 * B : ℕ) : ℝ) = 2 * (B : ℝ) := by push_cast; ring
      _ ≤ 2 * (x : ℝ) ^ (17 / 40 : ℝ) := by linarith [hBB.2.1, hBA]
      _ ≤ 8 * (x : ℝ) ^ (17 / 40 : ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hAB_ge : (x : ℝ) ^ (23 / 40 : ℝ) / 4 ≤ (A : ℝ) * (B : ℝ) := by
    have hm := mul_le_mul hAB.1 hBB.1 (by positivity) (by positivity)
    rw [div_mul_div_comm, rpow_mul_eq hxpos (by norm_num : (17 / 40 : ℝ) + 15 / 100 = 23 / 40)] at hm
    norm_num at hm
    exact hm
  have hc_bound : 2 * (x : ℝ) / ((A : ℝ) * (B : ℝ)) < (y : ℝ) + 1 := by
    have h1 : 2 * (x : ℝ) / ((A : ℝ) * (B : ℝ)) ≤ 8 * (x : ℝ) ^ (17 / 40 : ℝ) := by
      have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * (x : ℝ)) (by positivity) hAB_ge
      rw [show 2 * (x : ℝ) / ((x : ℝ) ^ (23 / 40 : ℝ) / 4) =
          8 * ((x : ℝ) / (x : ℝ) ^ (23 / 40 : ℝ)) by ring,
        self_div_rpow_eq hxpos (by norm_num : 1 - (23 / 40 : ℝ) = 17 / 40)] at hdiv
      exact hdiv
    have hlt : 8 * (x : ℝ) ^ (17 / 40 : ℝ) < (y : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hcomp :
      ((y + 1 : ℕ) : ℝ) * (C0 ^ 2 * (2 * (x : ℝ)) ^ (1 / 50 : ℝ)) <
        (B : ℝ) * ((A : ℝ) / (4 * (K : ℝ))) := by
    have hy1_le : ((y + 1 : ℕ) : ℝ) ≤ 9 * (x : ℝ) ^ (17 / 40 : ℝ) := by
      have hy_le : (y : ℝ) ≤ 8 * (x : ℝ) ^ (17 / 40 : ℝ) := Nat.floor_le (by positivity)
      simp only [Real.rpow_zero, mul_one] at h1_y
      push_cast; linarith
    have hlhs :
        ((y + 1 : ℕ) : ℝ) * (C0 ^ 2 * (2 * (x : ℝ)) ^ (1 / 50 : ℝ)) ≤
          (9 * C0 ^ 2 * (2 : ℝ) ^ (1 / 50 : ℝ)) * (x : ℝ) ^ (89 / 200 : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hy1_le
        (by positivity : 0 ≤ C0 ^ 2 * (2 * (x : ℝ)) ^ (1 / 50 : ℝ))
      rw [Real.mul_rpow (by norm_num) hxpos.le,
        show 9 * (x : ℝ) ^ (17 / 40 : ℝ) *
            (C0 ^ 2 * ((2 : ℝ) ^ (1 / 50 : ℝ) * (x : ℝ) ^ (1 / 50 : ℝ))) =
          (9 * C0 ^ 2 * (2 : ℝ) ^ (1 / 50 : ℝ)) *
            ((x : ℝ) ^ (17 / 40 : ℝ) * (x : ℝ) ^ (1 / 50 : ℝ)) by ring,
        rpow_mul_eq hxpos (by norm_num : (17 / 40 : ℝ) + 1 / 50 = 89 / 200)] at h1
      rw [Real.mul_rpow (by norm_num) hxpos.le]
      exact h1
    have hrhs : (x : ℝ) ^ (91 / 200 : ℝ) / 16 ≤ (B : ℝ) * ((A : ℝ) / (4 * (K : ℝ))) := by
      have h1 : (x : ℝ) ^ (23 / 40 : ℝ) / 4 / (4 * (x : ℝ) ^ (3 / 25 : ℝ)) ≤
          (A : ℝ) * (B : ℝ) / (4 * (K : ℝ)) :=
        div_le_div₀ (by positivity) hAB_ge (by positivity) (by linarith [hKB.2.1])
      rw [show (x : ℝ) ^ (23 / 40 : ℝ) / 4 / (4 * (x : ℝ) ^ (3 / 25 : ℝ)) =
          ((x : ℝ) ^ (23 / 40 : ℝ) / (x : ℝ) ^ (3 / 25 : ℝ)) / 16 by ring,
        rpow_div_eq hxpos (by norm_num : (23 / 40 : ℝ) - 3 / 25 = 91 / 200)] at h1
      have heq : (B : ℝ) * ((A : ℝ) / (4 * (K : ℝ))) = (A : ℝ) * (B : ℝ) / (4 * (K : ℝ)) := by ring
      linarith
    linarith
  exact smooth_count_from_rows x z B A K y C0 hC0_pos hdiv_bound (by omega) hz_le_x
    hBB.2.2 hAB.2.2 h2A_le_y h2B_le_y hc_bound hrows hcomp

end OMA.Erdos375BoundedGap

theorem OMA.solution : type_of% @Erdos375.erdos_375.variants.bounded_gap := by
  intro hGrimm
  refine ⟨1 / 200, by norm_num, ?_⟩
  let p := Nat.nth Nat.Prime
  have hpTop : Tendsto p atTop atTop :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  have hsmooth := hpTop.eventually OMA.Erdos375BoundedGap.eventually_smooth_count_gt
  filter_upwards [hsmooth] with n hn
  have hp1 : 1 < p n := by
    have := Nat.add_two_le_nth_prime n
    dsimp [p]
    omega
  set z : ℕ := ⌊(p n : ℝ) ^ (49 / 100 : ℝ)⌋₊
  set y : ℕ := ⌊8 * (p n : ℝ) ^ (17 / 40 : ℝ)⌋₊
  have hgap : p (n + 1) ≤ p n + z := by
    by_contra! hgt
    have hcomp : ∀ i < z, ¬ (p n + i + 1).Prime := by
      intro i hi hiPrime
      have hlt : p n + i + 1 < p (n + 1) := by omega
      have hle := Nat.le_nth_of_lt_nth_succ hlt hiPrime
      change p n + i + 1 ≤ p n at hle
      omega
    obtain ⟨q, hq_inj, hq_prop⟩ := hGrimm (p n) hp1.le z hcomp
    let S := OMA.Erdos375BoundedGap.smoothFinset (p n) z y
    let f : ℕ → ℕ := fun i => if h : i < z then q ⟨i, h⟩ else 0
    have hsub : S.image f ⊆ Finset.range (y + 1) := by
      intro r hr
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
      have hi_mem := OMA.Erdos375BoundedGap.mem_smoothFinset.mp hi
      have hi_lt : i < z := hi_mem.1
      have hfi : f i = q ⟨i, hi_lt⟩ := dif_pos hi_lt
      rw [hfi, Finset.mem_range]
      have hq_mem : q ⟨i, hi_lt⟩ ∈ (p n + i + 1).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨(hq_prop ⟨i, hi_lt⟩).1, (hq_prop ⟨i, hi_lt⟩).2, by omega⟩
      have hle := hi_mem.2 (q ⟨i, hi_lt⟩) hq_mem
      omega
    have hinj : Set.InjOn f S := by
      intro i hi j hj heq
      have hi_lt : i < z := (OMA.Erdos375BoundedGap.mem_smoothFinset.mp hi).1
      have hj_lt : j < z := (OMA.Erdos375BoundedGap.mem_smoothFinset.mp hj).1
      simp only [f, dif_pos hi_lt, dif_pos hj_lt] at heq
      have := hq_inj heq
      exact congr_arg Fin.val this
    have hcard : S.card ≤ y + 1 := by
      calc S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range (y + 1)).card := Finset.card_le_card hsub
        _ = y + 1 := Finset.card_range (y + 1)
    exact (Nat.not_lt.mpr hcard) hn
  change (p (n + 1) : ℝ) - (p n : ℝ) < (p n : ℝ) ^ (1 / (2 : ℝ) - 1 / 200)
  have hgapR : (p (n + 1) : ℝ) ≤ (p n : ℝ) + (z : ℝ) := by exact_mod_cast hgap
  calc (p (n + 1) : ℝ) - (p n : ℝ)
      ≤ (z : ℝ) := by linarith
    _ ≤ (p n : ℝ) ^ (49 / 100 : ℝ) := Nat.floor_le (by positivity)
    _ < (p n : ℝ) ^ (1 / (2 : ℝ) - 1 / 200) :=
        Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hp1) (by norm_num)
