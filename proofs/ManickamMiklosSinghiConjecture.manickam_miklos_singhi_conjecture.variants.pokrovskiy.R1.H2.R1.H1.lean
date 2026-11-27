import OMAReductions.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1_H2_R1
import Mathlib

/-!
# Cyclic restricted sumset estimate (Pokrovskiy Claim 5.10)

We prove `OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1_H2_R1.H1`
using a short discrete Fourier / additive-energy argument on `Fin k`:

1. For any `A : Finset (Fin k)` satisfying `∀ u, u ∈ A ∨ -u ∈ A`, let
   `f_hat r = ∑ a ∈ A, exp (2π i r a / k)`.
2. For `r ≠ 0`, pairing `x` with `-x` gives
   `|2 * (f_hat r).re| ≤ 2|A| - k` and `4 * (f_hat r).im^2 ≤ k (k - |A|)`,
   hence `4 * ‖f_hat r‖^2 ≤ 4|A|^2 - 5|A|k + 2k^2`.
3. Combining with Parseval `∑_{r ≠ 0} ‖f_hat r‖^2 = |A|(k - |A|)` yields
   `2 * ∑ r, ‖f_hat r‖^4 ≤ 3 * |A|^4`, i.e., `E(A, A) ≤ (3/2) |A|^4 / k`.
4. By Cauchy-Schwarz on the additive energy `E(A, B)` and on the representation counts
   over `U = S.image (fun p => p.1 + p.2)`,
   `4 k^2 |S|^4 ≤ 9 |U|^2 |A|^4 |B|^4`.
   Together with `2500 |S| ≥ 2499 |A||B|`, this gives `3 * k ≤ 5 * |U|`.
-/

namespace OMA.Pokrovskiy510

open Finset Fin.CommRing Complex

section Fourier

variable {k : ℕ} [NeZero k]

private noncomputable def chi (r x : Fin k) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((r.val * x.val : ℕ) : ℂ) / (k : ℂ))

private lemma chi_zero_left (x : Fin k) : chi (k := k) 0 x = 1 := by
  simp [chi]

private lemma chi_zero_right (r : Fin k) : chi (k := k) r 0 = 1 := by
  simp [chi]

omit [NeZero k] in
private lemma chi_comm (r x : Fin k) : chi r x = chi x r := by
  simp [chi, Nat.mul_comm]

omit [NeZero k] in
private lemma chi_pow (r : Fin k) (n : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I * (r.val : ℂ) / (k : ℂ))) ^ n =
      Complex.exp (2 * Real.pi * Complex.I * ((r.val * n : ℕ) : ℂ) / (k : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

omit [NeZero k] in
private lemma chi_eq_pow (r x : Fin k) :
    chi r x = (Complex.exp (2 * Real.pi * Complex.I * (r.val : ℂ) / (k : ℂ))) ^ x.val := by
  rw [chi_pow, chi]

private lemma chi_add (r x y : Fin k) : chi r (x + y) = chi r x * chi r y := by
  rw [chi, chi, chi, ← Complex.exp_add]
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have hmod : (x + y).val = (x.val + y.val) % k := rfl
  have hdiv : x.val + y.val = (x + y).val + k * ((x.val + y.val) / k) := by
    rw [hmod]
    exact (Nat.mod_add_div (x.val + y.val) k).symm
  set q : ℕ := (x.val + y.val) / k
  have hmul : r.val * (x.val + y.val) = r.val * (x + y).val + r.val * q * k := by
    calc r.val * (x.val + y.val)
        = r.val * ((x + y).val + k * q) := by rw [hdiv]
      _ = r.val * (x + y).val + r.val * q * k := by ring
  have hexp :
      2 * Real.pi * Complex.I * ((r.val * x.val : ℕ) : ℂ) / (k : ℂ) +
      2 * Real.pi * Complex.I * ((r.val * y.val : ℕ) : ℂ) / (k : ℂ) =
      2 * Real.pi * Complex.I * ((r.val * (x + y).val : ℕ) : ℂ) / (k : ℂ) +
      ((r.val * q : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hmulC : ((r.val * x.val : ℕ) : ℂ) + ((r.val * y.val : ℕ) : ℂ) =
        ((r.val * (x + y).val : ℕ) : ℂ) + ((r.val * q : ℕ) : ℂ) * (k : ℂ) := by
      have : r.val * x.val + r.val * y.val = r.val * (x + y).val + r.val * q * k := by
        rw [← Nat.mul_add, hmul]
      exact_mod_cast this
    rw [← add_div, ← mul_add, hmulC, mul_add, add_div]
    congr 1
    rw [show 2 * ↑Real.pi * I * (↑(r.val * q) * ↑k) = (↑(r.val * q) * (2 * ↑Real.pi * I)) * ↑k by ring]
    exact mul_div_cancel_right₀ _ hk
  rw [hexp, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

private lemma chi_norm (r x : Fin k) : ‖chi r x‖ = 1 := by
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  rw [chi]
  have harg : 2 * Real.pi * Complex.I * ((r.val * x.val : ℕ) : ℂ) / (k : ℂ) =
      (((2 * Real.pi * ((r.val * x.val : ℕ) : ℝ) / (k : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma chi_mul_conj (r x : Fin k) : chi r x * starRingEnd ℂ (chi r x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, chi_norm]
  simp

private lemma chi_neg (r x : Fin k) : chi r (-x) = starRingEnd ℂ (chi r x) := by
  have h1 : chi r x * chi r (-x) = 1 := by
    rw [← chi_add, add_neg_cancel, chi_zero_right]
  have h2 : chi r x * starRingEnd ℂ (chi r x) = 1 := chi_mul_conj r x
  have hne : chi r x ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

private lemma chi_sub (r x y : Fin k) : chi r (x - y) = chi r x * starRingEnd ℂ (chi r y) := by
  rw [sub_eq_add_neg, chi_add, chi_neg]

private lemma chi_sq (r x : Fin k) : (chi r x) ^ 2 = chi (r + r) x := by
  rw [sq, chi_comm r x, chi_comm (r + r) x, chi_add]

private lemma sum_chi_right (r : Fin k) :
    ∑ x : Fin k, chi r x = if r = 0 then (k : ℂ) else 0 := by
  split_ifs with hr
  · subst hr
    simp [chi_zero_left]
  · set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (r.val : ℂ) / (k : ℂ))
    have hsum : ∑ x : Fin k, chi r x = ∑ i ∈ range k, ζ ^ i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ζ ^ i)]
      refine sum_congr rfl fun x _ => ?_
      exact chi_eq_pow r x
    rw [hsum]
    have hζk : ζ ^ k = 1 := by
      have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
      dsimp only [ζ]
      rw [← Complex.exp_nat_mul]
      have harg : (k : ℂ) * (2 * Real.pi * Complex.I * (r.val : ℂ) / (k : ℂ)) =
          (r.val : ℂ) * (2 * Real.pi * Complex.I) := by
        field_simp [hk]
      rw [harg]
      exact Complex.exp_nat_mul_two_pi_mul_I r.val
    have hζne : ζ ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hmul : ((r.val : ℂ) / (k : ℂ)) * (2 * Real.pi * Complex.I) =
          (n : ℂ) * (2 * Real.pi * Complex.I) := by
        linear_combination hn
      have hdiv : (r.val : ℂ) / (k : ℂ) = (n : ℂ) := mul_right_cancel₀ h2pi hmul
      have hmulC : (r.val : ℂ) = (n : ℂ) * (k : ℂ) := (div_eq_iff hkC).mp hdiv
      have hmulZ : (r.val : ℤ) = n * (k : ℤ) := by exact_mod_cast hmulC
      have hrpos : 0 < r.val := Nat.pos_of_ne_zero (fun h0 => hr (Fin.ext h0))
      have hrlt : r.val < k := r.isLt
      have hkpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast NeZero.pos k
      have hgt0 : (0 : ℤ) < n := by nlinarith
      have hlt1 : n < 1 := by nlinarith
      omega
    have hmul0 : (ζ - 1) * ∑ i ∈ range k, ζ ^ i = 0 := by
      calc (ζ - 1) * ∑ i ∈ range k, ζ ^ i
          = ζ ^ k - 1 := by rw [mul_comm]; exact geom_sum_mul ζ k
        _ = 0 := by rw [hζk, sub_self]
    exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hζne)

private lemma sum_chi_left (x : Fin k) :
    ∑ r : Fin k, chi r x = if x = 0 then (k : ℂ) else 0 := by
  have h : ∑ r : Fin k, chi r x = ∑ r : Fin k, chi x r :=
    sum_congr rfl fun r _ => chi_comm r x
  rw [h, sum_chi_right]

private noncomputable def fhat (A : Finset (Fin k)) (r : Fin k) : ℂ :=
  ∑ a ∈ A, chi r a

private lemma fhat_zero (A : Finset (Fin k)) : fhat A 0 = (A.card : ℂ) := by
  simp [fhat, chi_zero_left]

private lemma parseval (A : Finset (Fin k)) :
    ∑ r : Fin k, ‖fhat A r‖ ^ 2 = (k : ℝ) * (A.card : ℝ) := by
  have hC : ∑ r : Fin k, ((‖fhat A r‖ ^ 2 : ℝ) : ℂ) = ((k : ℝ) * (A.card : ℝ) : ℂ) := by
    have h1 : ∀ r : Fin k, ((‖fhat A r‖ ^ 2 : ℝ) : ℂ) = fhat A r * starRingEnd ℂ (fhat A r) := by
      intro r
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h1, fhat, map_sum, sum_mul_sum]
    rw [sum_comm]
    have h2 : ∑ a ∈ A, ∑ r : Fin k, ∑ b ∈ A, chi r a * starRingEnd ℂ (chi r b) =
        ∑ a ∈ A, ∑ b ∈ A, ∑ r : Fin k, chi r (a - b) := by
      refine sum_congr rfl fun a _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun b _ => ?_
      refine sum_congr rfl fun r _ => ?_
      exact (chi_sub r a b).symm
    rw [h2]
    simp_rw [sum_chi_left]
    have h3 : ∀ a ∈ A, ∑ b ∈ A, (if a - b = 0 then (k : ℂ) else 0) = (k : ℂ) := by
      intro a ha
      rw [sum_ite, sum_const_zero, add_zero]
      have hfilt : A.filter (fun b => a - b = 0) = {a} := by
        ext b
        simp only [mem_filter, mem_singleton, sub_eq_zero]
        exact ⟨fun h => h.2.symm, fun h => by subst h; exact ⟨ha, rfl⟩⟩
      rw [hfilt]
      simp
    rw [sum_congr rfl h3]
    simp [mul_comm]
  exact_mod_cast hC

private lemma parseval_ne_zero (A : Finset (Fin k)) :
    ∑ r ∈ univ.erase (0 : Fin k), ‖fhat A r‖ ^ 2 = (A.card : ℝ) * ((k : ℝ) - (A.card : ℝ)) := by
  have h := parseval A
  rw [← add_sum_erase univ (fun r => ‖fhat A r‖ ^ 2) (mem_univ (0 : Fin k))] at h
  rw [fhat_zero, Complex.norm_natCast] at h
  linarith

private def repCount (A B : Finset (Fin k)) (z : Fin k) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 + p.2 = z)).card

private lemma energy_eq_fourier (A B : Finset (Fin k)) :
    (k : ℝ) * ∑ z : Fin k, (repCount A B z : ℝ) ^ 2 =
      ∑ r : Fin k, ‖fhat A r‖ ^ 2 * ‖fhat B r‖ ^ 2 := by
  have hC : ((k : ℝ) * ∑ z : Fin k, (repCount A B z : ℝ) ^ 2 : ℂ) =
      ∑ r : Fin k, ((‖fhat A r‖ ^ 2 * ‖fhat B r‖ ^ 2 : ℝ) : ℂ) := by
    have hterm : ∀ r : Fin k,
        ((‖fhat A r‖ ^ 2 * ‖fhat B r‖ ^ 2 : ℝ) : ℂ) =
          (fhat A r * fhat B r) * starRingEnd ℂ (fhat A r * fhat B r) := by
      intro r
      rw [map_mul, Complex.ofReal_mul]
      have hA : ((‖fhat A r‖ ^ 2 : ℝ) : ℂ) = fhat A r * starRingEnd ℂ (fhat A r) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hB : ((‖fhat B r‖ ^ 2 : ℝ) : ℂ) = fhat B r * starRingEnd ℂ (fhat B r) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hA, hB]
      ring
    simp_rw [hterm]
    have hprod : ∀ r : Fin k,
        fhat A r * fhat B r = ∑ p ∈ A ×ˢ B, chi r (p.1 + p.2) := by
      intro r
      rw [fhat, fhat, sum_mul_sum, Finset.sum_product]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => (chi_add r a b).symm
    simp_rw [hprod, map_sum, sum_mul_sum]
    rw [sum_comm]
    have hswap :
        ∑ p ∈ A ×ˢ B, ∑ r : Fin k, ∑ q ∈ A ×ˢ B,
            chi r (p.1 + p.2) * starRingEnd ℂ (chi r (q.1 + q.2)) =
        ∑ p ∈ A ×ˢ B, ∑ q ∈ A ×ˢ B,
            ∑ r : Fin k, chi r ((p.1 + p.2) - (q.1 + q.2)) := by
      refine sum_congr rfl fun p _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun q _ => sum_congr rfl fun r _ => (chi_sub r _ _).symm
    rw [hswap]
    simp_rw [sum_chi_left]
    have hcount :
        ∑ p ∈ A ×ˢ B, ∑ q ∈ A ×ˢ B, (if (p.1 + p.2) - (q.1 + q.2) = 0 then (k : ℂ) else 0) =
        (k : ℂ) * ∑ z : Fin k, ((repCount A B z : ℂ) ^ 2) := by
      have hinner : ∀ p ∈ A ×ˢ B,
          ∑ q ∈ A ×ˢ B, (if (p.1 + p.2) - (q.1 + q.2) = 0 then (k : ℂ) else 0) =
          (k : ℂ) * (repCount A B (p.1 + p.2) : ℂ) := by
        intro p _
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]
        congr 2
        dsimp only [repCount]
        congr 1
        ext q
        simp only [mem_filter, sub_eq_zero, eq_comm]
      rw [sum_congr rfl hinner, ← mul_sum]
      congr 1
      have hfib : ∑ p ∈ A ×ˢ B, (repCount A B (p.1 + p.2) : ℂ) =
          ∑ z : Fin k, ∑ p ∈ (A ×ˢ B).filter (fun p => p.1 + p.2 = z),
            (repCount A B (p.1 + p.2) : ℂ) := by
        rw [sum_fiberwise_of_maps_to (fun _ _ => mem_univ _)]
      rw [hfib]
      refine sum_congr rfl fun z _ => ?_
      have hconst : ∀ p ∈ (A ×ˢ B).filter (fun p => p.1 + p.2 = z),
          (repCount A B (p.1 + p.2) : ℂ) = (repCount A B z : ℂ) := by
        intro p hp
        rw [(mem_filter.mp hp).2]
      rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul, sq]
      rfl
    rw [hcount]
    push_cast
    rfl
  exact_mod_cast hC

omit [NeZero k] in
private lemma card_double_ge (A : Finset (Fin k)) (hA : ∀ u : Fin k, u ∈ A ∨ -u ∈ A) :
    k ≤ 2 * A.card := by
  have hsub : (univ : Finset (Fin k)) ⊆ A ∪ A.image (fun x => -x) := by
    intro u _
    rcases hA u with hu | hnu
    · exact mem_union_left _ hu
    · exact mem_union_right _ (mem_image.mpr ⟨-u, hnu, neg_neg u⟩)
  have h1 : k ≤ (A ∪ A.image (fun x => -x)).card := by
    simpa [Fintype.card_fin] using card_le_card hsub
  have h2 : (A ∪ A.image (fun x => -x)).card ≤ A.card + (A.image (fun x => -x)).card :=
    card_union_le _ _
  have h3 : (A.image (fun x => -x)).card ≤ A.card := card_image_le
  omega

private lemma fhat_re_bound (A : Finset (Fin k)) (hA : ∀ u : Fin k, u ∈ A ∨ -u ∈ A)
    (r : Fin k) (hr : r ≠ 0) :
    4 * (fhat A r).re ^ 2 ≤ (2 * (A.card : ℝ) - (k : ℝ)) ^ 2 := by
  let f : Fin k → ℝ := fun x => if x ∈ A then 1 else 0
  have hre1 : (fhat A r).re = ∑ x : Fin k, f x * (chi r x).re := by
    rw [fhat, Complex.re_sum]
    rw [← sum_filter_add_sum_filter_not univ (fun x => x ∈ A)]
    have h1 : ∑ x ∈ univ.filter (fun x => x ∈ A), f x * (chi r x).re =
        ∑ a ∈ A, (chi r a).re := by
      have hfilt : univ.filter (fun x => x ∈ A) = A := by ext x; simp
      rw [hfilt]
      refine sum_congr rfl fun a ha => ?_
      simp [f, ha]
    have h2 : ∑ x ∈ univ.filter (fun x => x ∉ A), f x * (chi r x).re = 0 := by
      refine sum_eq_zero fun x hx => ?_
      have hnx : x ∉ A := (mem_filter.mp hx).2
      simp [f, hnx]
    linarith
  have hre2 : (fhat A r).re = ∑ x : Fin k, f (-x) * (chi r x).re := by
    rw [hre1]
    refine Equiv.sum_comp (Equiv.neg (Fin k)) (fun x => f x * (chi r x).re) |>.symm.trans ?_
    refine sum_congr rfl fun x _ => ?_
    simp only [Equiv.neg_apply, chi_neg, Complex.conj_re]
  have hsum_chi : ∑ x : Fin k, (chi r x).re = 0 := by
    have h := congrArg Complex.re (sum_chi_right r)
    rw [Complex.re_sum, if_neg hr, Complex.zero_re] at h
    exact h
  have h2re : 2 * (fhat A r).re = ∑ x : Fin k, (f x + f (-x) - 1) * (chi r x).re := by
    have hadd : ∑ x : Fin k, (f x + f (-x) - 1) * (chi r x).re =
        (∑ x : Fin k, f x * (chi r x).re) + (∑ x : Fin k, f (-x) * (chi r x).re) -
          (∑ x : Fin k, (chi r x).re) := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun x _ => by ring
    linarith
  have hnonneg : ∀ x : Fin k, 0 ≤ f x + f (-x) - 1 := by
    intro x
    rcases hA x with hx | hnx <;> dsimp only [f] <;> split_ifs <;> linarith
  have habs : |2 * (fhat A r).re| ≤ ∑ x : Fin k, (f x + f (-x) - 1) := by
    rw [h2re]
    calc |∑ x : Fin k, (f x + f (-x) - 1) * (chi r x).re|
        ≤ ∑ x : Fin k, |(f x + f (-x) - 1) * (chi r x).re| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Fin k, (f x + f (-x) - 1) := by
          refine sum_le_sum fun x _ => ?_
          rw [abs_mul, abs_of_nonneg (hnonneg x)]
          have hle1 : |(chi r x).re| ≤ 1 := by
            calc |(chi r x).re| ≤ ‖chi r x‖ := Complex.abs_re_le_norm _
              _ = 1 := chi_norm r x
          nlinarith [hnonneg x]
  have hsum_f : ∑ x : Fin k, f x = (A.card : ℝ) := by
    simp [f]
  have hsum_fn : ∑ x : Fin k, f (-x) = (A.card : ℝ) := by
    change ∑ x : Fin k, f (Equiv.neg (Fin k) x) = (A.card : ℝ)
    rw [Equiv.sum_comp (Equiv.neg (Fin k)) f]
    exact hsum_f
  have hsum_rhs : ∑ x : Fin k, (f x + f (-x) - 1) = 2 * (A.card : ℝ) - (k : ℝ) := by
    rw [sum_sub_distrib, sum_add_distrib, hsum_f, hsum_fn]
    simp
    ring
  rw [hsum_rhs] at habs
  have hsq : (2 * (fhat A r).re) ^ 2 ≤ (2 * (A.card : ℝ) - (k : ℝ)) ^ 2 := by
    rw [← sq_abs (2 * (fhat A r).re)]
    have h0 : 0 ≤ |2 * (fhat A r).re| := abs_nonneg _
    nlinarith
  linarith

private lemma sum_chi_im_sq_le (r : Fin k) :
    2 * ∑ x : Fin k, (chi r x).im ^ 2 ≤ (k : ℝ) := by
  have hpt : ∀ x : Fin k, 2 * (chi r x).im ^ 2 = 1 - (chi (r + r) x).re := by
    intro x
    have hnorm : (chi r x).re ^ 2 + (chi r x).im ^ 2 = 1 := by
      have h := chi_norm r x
      have hsq : ‖chi r x‖ ^ 2 = 1 := by rw [h]; norm_num
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
      linarith
    have hre : (chi (r + r) x).re = (chi r x).re ^ 2 - (chi r x).im ^ 2 := by
      rw [← chi_sq, sq, Complex.mul_re]
      ring
    linarith
  calc 2 * ∑ x : Fin k, (chi r x).im ^ 2
      = ∑ x : Fin k, 2 * (chi r x).im ^ 2 := by rw [mul_sum]
    _ = ∑ x : Fin k, (1 - (chi (r + r) x).re) := sum_congr rfl fun x _ => hpt x
    _ = (k : ℝ) - (∑ x : Fin k, chi (r + r) x).re := by
        rw [sum_sub_distrib, Complex.re_sum]
        simp
    _ ≤ (k : ℝ) := by
        rw [sum_chi_right (r + r)]
        split_ifs
        · simp
        · simp

private lemma fhat_im_bound (A : Finset (Fin k)) (hA : ∀ u : Fin k, u ∈ A ∨ -u ∈ A)
    (r : Fin k) :
    4 * (fhat A r).im ^ 2 ≤ (k : ℝ) * ((k : ℝ) - (A.card : ℝ)) := by
  let f : Fin k → ℝ := fun x => if x ∈ A then 1 else 0
  have him1 : (fhat A r).im = ∑ x : Fin k, f x * (chi r x).im := by
    rw [fhat, Complex.im_sum]
    rw [← sum_filter_add_sum_filter_not univ (fun x => x ∈ A)]
    have h1 : ∑ x ∈ univ.filter (fun x => x ∈ A), f x * (chi r x).im =
        ∑ a ∈ A, (chi r a).im := by
      have hfilt : univ.filter (fun x => x ∈ A) = A := by ext x; simp
      rw [hfilt]
      refine sum_congr rfl fun a ha => ?_
      simp [f, ha]
    have h2 : ∑ x ∈ univ.filter (fun x => x ∉ A), f x * (chi r x).im = 0 := by
      refine sum_eq_zero fun x hx => ?_
      have hnx : x ∉ A := (mem_filter.mp hx).2
      simp [f, hnx]
    linarith
  have him2 : (fhat A r).im = -∑ x : Fin k, f (-x) * (chi r x).im := by
    rw [him1, ← sum_neg_distrib]
    refine Equiv.sum_comp (Equiv.neg (Fin k)) (fun x => f x * (chi r x).im) |>.symm.trans ?_
    refine sum_congr rfl fun x _ => ?_
    simp only [Equiv.neg_apply, chi_neg, Complex.conj_im]
    ring
  have h2im : 2 * (fhat A r).im = ∑ x : Fin k, (f x - f (-x)) * (chi r x).im := by
    have hsub : ∑ x : Fin k, (f x - f (-x)) * (chi r x).im =
        (∑ x : Fin k, f x * (chi r x).im) - (∑ x : Fin k, f (-x) * (chi r x).im) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun x _ => by ring
    linarith
  have hcs : (2 * (fhat A r).im) ^ 2 ≤
      (∑ x : Fin k, (f x - f (-x)) ^ 2) * (∑ x : Fin k, (chi r x).im ^ 2) := by
    rw [h2im]
    exact Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => f x - f (-x)) (fun x => (chi r x).im)
  have hpt : ∀ x : Fin k, (f x - f (-x)) ^ 2 = 2 - f x - f (-x) := by
    intro x
    rcases hA x with hx | hnx <;> dsimp only [f] <;> split_ifs <;> ring
  have hsum_f : ∑ x : Fin k, f x = (A.card : ℝ) := by simp [f]
  have hsum_fn : ∑ x : Fin k, f (-x) = (A.card : ℝ) := by
    change ∑ x : Fin k, f (Equiv.neg (Fin k) x) = (A.card : ℝ)
    rw [Equiv.sum_comp (Equiv.neg (Fin k)) f]
    exact hsum_f
  have hfirst : ∑ x : Fin k, (f x - f (-x)) ^ 2 = 2 * ((k : ℝ) - (A.card : ℝ)) := by
    rw [sum_congr rfl fun x _ => hpt x]
    simp_rw [sub_eq_add_neg]
    rw [sum_add_distrib, sum_add_distrib, sum_neg_distrib, sum_neg_distrib, hsum_f, hsum_fn]
    simp
    ring
  have hsec := sum_chi_im_sq_le r
  have hka : 0 ≤ (k : ℝ) - (A.card : ℝ) := by
    have : A.card ≤ k := by simpa [Fintype.card_fin] using card_le_univ A
    have : (A.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
    linarith
  rw [hfirst] at hcs
  nlinarith

private lemma fourth_moment_bound (A : Finset (Fin k)) (hA : ∀ u : Fin k, u ∈ A ∨ -u ∈ A) :
    2 * ∑ r : Fin k, ‖fhat A r‖ ^ 4 ≤ 3 * (A.card : ℝ) ^ 4 := by
  set a : ℝ := (A.card : ℝ)
  set kr : ℝ := (k : ℝ)
  have hpt : ∀ r ∈ univ.erase (0 : Fin k),
      4 * ‖fhat A r‖ ^ 2 ≤ 4 * a ^ 2 - 5 * a * kr + 2 * kr ^ 2 := by
    intro r hr
    have hr0 : r ≠ 0 := (mem_erase.mp hr).1
    have hre := fhat_re_bound A hA r hr0
    have him := fhat_im_bound A hA r
    have hnorm : ‖fhat A r‖ ^ 2 = (fhat A r).re ^ 2 + (fhat A r).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    nlinarith
  have hsum_ne : 4 * ∑ r ∈ univ.erase (0 : Fin k), ‖fhat A r‖ ^ 4 ≤
      (4 * a ^ 2 - 5 * a * kr + 2 * kr ^ 2) * (a * (kr - a)) := by
    calc 4 * ∑ r ∈ univ.erase (0 : Fin k), ‖fhat A r‖ ^ 4
        = ∑ r ∈ univ.erase (0 : Fin k), (4 * ‖fhat A r‖ ^ 2) * ‖fhat A r‖ ^ 2 := by
            rw [mul_sum]
            refine sum_congr rfl fun r _ => by ring
      _ ≤ ∑ r ∈ univ.erase (0 : Fin k),
            (4 * a ^ 2 - 5 * a * kr + 2 * kr ^ 2) * ‖fhat A r‖ ^ 2 := by
            refine sum_le_sum fun r hr => ?_
            exact mul_le_mul_of_nonneg_right (hpt r hr) (sq_nonneg _)
      _ = (4 * a ^ 2 - 5 * a * kr + 2 * kr ^ 2) *
            ∑ r ∈ univ.erase (0 : Fin k), ‖fhat A r‖ ^ 2 := by
            rw [← mul_sum]
      _ = (4 * a ^ 2 - 5 * a * kr + 2 * kr ^ 2) * (a * (kr - a)) := by
            rw [parseval_ne_zero A]
  have hsplit : ∑ r : Fin k, ‖fhat A r‖ ^ 4 =
      a ^ 4 + ∑ r ∈ univ.erase (0 : Fin k), ‖fhat A r‖ ^ 4 := by
    rw [← add_sum_erase univ (fun r => ‖fhat A r‖ ^ 4) (mem_univ (0 : Fin k)),
      fhat_zero, Complex.norm_natCast]
  have h2a : kr ≤ 2 * a := by
    dsimp only [kr, a]
    exact_mod_cast card_double_ge A hA
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have hdiff : 4 * (2 * a ^ 4 - (4 * a ^ 2 - 5 * a * kr + 2 * kr ^ 2) * (a * (kr - a))) =
      a * (2 * a - kr) * (3 * (2 * a - kr) ^ 2 + 5 * kr ^ 2) := by
    ring
  have hpos : 0 ≤ a * (2 * a - kr) * (3 * (2 * a - kr) ^ 2 + 5 * kr ^ 2) := by
    have h1 : 0 ≤ a * (2 * a - kr) := mul_nonneg ha0 (by linarith)
    have h2 : 0 ≤ 3 * (2 * a - kr) ^ 2 + 5 * kr ^ 2 := by positivity
    exact mul_nonneg h1 h2
  nlinarith

end Fourier

end OMA.Pokrovskiy510

theorem OMA.solution :
    OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1_H2_R1.H1 := by
  intro k _ A B S hS hA hB hdel
  classical
  open Finset Fin.CommRing OMA.Pokrovskiy510 in
  have hkpos : 0 < k := NeZero.pos k
  have h2A : k ≤ 2 * A.card := card_double_ge A hA
  have h2B : k ≤ 2 * B.card := card_double_ge B hB
  have hAB : k ^ 2 ≤ 4 * (A.card * B.card) := by
    calc k ^ 2 = k * k := sq k
      _ ≤ (2 * A.card) * (2 * B.card) := Nat.mul_le_mul h2A h2B
      _ = 4 * (A.card * B.card) := by ring
  have hSsplit : S.card + (A ×ˢ B \ S).card = A.card * B.card := by
    rw [add_comm, Finset.card_sdiff_add_card_eq_card hS, Finset.card_product]
  have hSbound : 2499 * (A.card * B.card) ≤ 2500 * S.card := by
    omega
  set U : Finset (Fin k) := S.image (fun p => p.1 + p.2)
  have hS_le_sum : (S.card : ℝ) ≤ ∑ z ∈ U, (repCount A B z : ℝ) := by
    have hNat : S.card ≤ ∑ z ∈ U, repCount A B z := by
      have hfib : S.card = ∑ z ∈ U, (S.filter (fun p => p.1 + p.2 = z)).card := by
        rw [← Finset.card_eq_sum_card_fiberwise (f := fun p : Fin k × Fin k => p.1 + p.2)
          (fun p hp => Finset.mem_image_of_mem _ hp)]
      rw [hfib]
      refine Finset.sum_le_sum fun z _ => Finset.card_le_card ?_
      exact Finset.filter_subset_filter _ hS
    exact_mod_cast hNat
  have hcs1 : (S.card : ℝ) ^ 2 ≤ (U.card : ℝ) * ∑ z : Fin k, (repCount A B z : ℝ) ^ 2 := by
    have h1 : (S.card : ℝ) ^ 2 ≤ (∑ z ∈ U, (repCount A B z : ℝ)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h2 : (∑ z ∈ U, (repCount A B z : ℝ)) ^ 2 ≤
        (U.card : ℝ) * ∑ z ∈ U, (repCount A B z : ℝ) ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) (fun z => (repCount A B z : ℝ))
      simpa using h
    have h3 : ∑ z ∈ U, (repCount A B z : ℝ) ^ 2 ≤ ∑ z : Fin k, (repCount A B z : ℝ) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun z => sq_nonneg _
    have hU0 : (0 : ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hcs2 : (∑ r : Fin k, ‖fhat A r‖ ^ 2 * ‖fhat B r‖ ^ 2) ^ 2 ≤
      (∑ r : Fin k, ‖fhat A r‖ ^ 4) * (∑ r : Fin k, ‖fhat B r‖ ^ 4) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
      (fun r => ‖fhat A r‖ ^ 2) (fun r => ‖fhat B r‖ ^ 2)
    have hpow : ∀ x : ℝ, (x ^ 2) ^ 2 = x ^ 4 := fun x => by ring
    simpa only [hpow] using h
  have hEA := fourth_moment_bound A hA
  have hEB := fourth_moment_bound B hB
  set kr : ℝ := (k : ℝ)
  set a : ℝ := (A.card : ℝ)
  set b : ℝ := (B.card : ℝ)
  set s : ℝ := (S.card : ℝ)
  set u : ℝ := (U.card : ℝ)
  set E : ℝ := ∑ z : Fin k, (repCount A B z : ℝ) ^ 2
  have hEeq : kr * E = ∑ r : Fin k, ‖fhat A r‖ ^ 2 * ‖fhat B r‖ ^ 2 := energy_eq_fourier A B
  have h4k2E2 : 4 * (kr * E) ^ 2 ≤ 9 * a ^ 4 * b ^ 4 := by
    have hA0 : 0 ≤ ∑ r : Fin k, ‖fhat A r‖ ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
    have hB0 : 0 ≤ ∑ r : Fin k, ‖fhat B r‖ ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
    rw [hEeq]
    calc 4 * (∑ r : Fin k, ‖fhat A r‖ ^ 2 * ‖fhat B r‖ ^ 2) ^ 2
        ≤ 4 * ((∑ r : Fin k, ‖fhat A r‖ ^ 4) * (∑ r : Fin k, ‖fhat B r‖ ^ 4)) := by nlinarith
      _ = (2 * ∑ r : Fin k, ‖fhat A r‖ ^ 4) * (2 * ∑ r : Fin k, ‖fhat B r‖ ^ 4) := by ring
      _ ≤ (3 * a ^ 4) * (3 * b ^ 4) := mul_le_mul hEA hEB (by positivity) (by positivity)
      _ = 9 * a ^ 4 * b ^ 4 := by ring
  have hs4 : 4 * kr ^ 2 * s ^ 4 ≤ 9 * u ^ 2 * a ^ 4 * b ^ 4 := by
    have hs2 : s ^ 4 ≤ u ^ 2 * E ^ 2 := by
      have h0 : 0 ≤ s ^ 2 := sq_nonneg s
      have huE : 0 ≤ u * E := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      nlinarith
    calc 4 * kr ^ 2 * s ^ 4
        ≤ 4 * kr ^ 2 * (u ^ 2 * E ^ 2) := by
            have : 0 ≤ 4 * kr ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left hs2 this
      _ = u ^ 2 * (4 * (kr * E) ^ 2) := by ring
      _ ≤ u ^ 2 * (9 * a ^ 4 * b ^ 4) := mul_le_mul_of_nonneg_left h4k2E2 (sq_nonneg u)
      _ = 9 * u ^ 2 * a ^ 4 * b ^ 4 := by ring
  have hSboundR : 2499 * (a * b) ≤ 2500 * s := by
    dsimp only [a, b, s]
    exact_mod_cast hSbound
  have habpos : 0 < a * b := by
    have ha : (0 : ℝ) < a := by
      have : 0 < A.card := by omega
      dsimp only [a]
      exact_mod_cast this
    have hb : (0 : ℝ) < b := by
      have : 0 < B.card := by omega
      dsimp only [b]
      exact_mod_cast this
    exact mul_pos ha hb
  have hab4pos : 0 < a ^ 4 * b ^ 4 := by
    have hmul : a ^ 4 * b ^ 4 = (a * b) ^ 4 := by ring
    rw [hmul]
    exact pow_pos habpos 4
  have hs4_lo : (2499 : ℝ) ^ 4 * (a ^ 4 * b ^ 4) ≤ (2500 : ℝ) ^ 4 * s ^ 4 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2499 * (a * b)) hSboundR 4
    nlinarith [show (2499 * (a * b)) ^ 4 = (2499 : ℝ) ^ 4 * (a ^ 4 * b ^ 4) by ring,
      show (2500 * s) ^ 4 = (2500 : ℝ) ^ 4 * s ^ 4 by ring]
  have hcomb : 4 * (2499 : ℝ) ^ 4 * kr ^ 2 * (a ^ 4 * b ^ 4) ≤
      9 * (2500 : ℝ) ^ 4 * u ^ 2 * (a ^ 4 * b ^ 4) := by
    calc 4 * (2499 : ℝ) ^ 4 * kr ^ 2 * (a ^ 4 * b ^ 4)
        = 4 * kr ^ 2 * ((2499 : ℝ) ^ 4 * (a ^ 4 * b ^ 4)) := by ring
      _ ≤ 4 * kr ^ 2 * ((2500 : ℝ) ^ 4 * s ^ 4) := by
            exact mul_le_mul_of_nonneg_left hs4_lo (by positivity)
      _ = (2500 : ℝ) ^ 4 * (4 * kr ^ 2 * s ^ 4) := by ring
      _ ≤ (2500 : ℝ) ^ 4 * (9 * u ^ 2 * a ^ 4 * b ^ 4) := by
            exact mul_le_mul_of_nonneg_left hs4 (by positivity)
      _ = 9 * (2500 : ℝ) ^ 4 * u ^ 2 * (a ^ 4 * b ^ 4) := by ring
  have hku : 4 * (2499 : ℝ) ^ 4 * kr ^ 2 ≤ 9 * (2500 : ℝ) ^ 4 * u ^ 2 :=
    le_of_mul_le_mul_right hcomb hab4pos
  have hsq : (3 * kr) ^ 2 ≤ (5 * u) ^ 2 := by nlinarith
  have hfinalR : 3 * kr ≤ 5 * u := by
    have hk0 : 0 ≤ 3 * kr := by positivity
    have hu0 : 0 ≤ 5 * u := by positivity
    nlinarith
  dsimp only [kr, u] at hfinalR
  exact_mod_cast hfinalR
