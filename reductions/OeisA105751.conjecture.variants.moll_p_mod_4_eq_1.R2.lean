import FormalConjectures.OEIS.«105751»
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Log

/-!
# Reduction of `OeisA105751.conjecture.variants.moll_p_mod_4_eq_1`

We prove unconditionally (using no hypotheses):
1. `a_eq_gaussianInt_im`: `OeisA105751.a n` equals the exact imaginary part of
   `∏ k ∈ Finset.range (n + 1), (⟨1, k⟩ : GaussianInt)`.
2. `a_ne_zero_of_three_lt`: `OeisA105751.a n ≠ 0` for every `n > 3`, via 8-factor
   2-adic dyadic doubling blocks starting from `n = 0` and `n = 3`.
3. `exists_sq_add_one_dvd_prime_pow`: Hensel lifting `r^2 ≡ -1 (mod p^M)` for every
   prime `p ≡ 1 (mod 4)` and every `M`.
4. `padicValInt_a_lower`: for every prime `p ≡ 1 (mod 4)` and every `n > 3`,
   `n ≤ (p - 1) * padicValInt p (a n) + (p - 1) * Nat.log p n + p`,
   which unconditionally establishes the lower bound `liminf ≥ 1`.
5. `padicValInt_a_lower_and_nontie`: whenever the two `p`-adic split factors
   `P₊(n) = ∏_{k=0}^n (1 + k*r)` and `P₋(n) = ∏_{k=0}^n (1 - k*r)` have distinct
   `p`-adic valuations, there is zero cancellation and
   `padicValInt p (a n) = min (v_p P₊(n)) (v_p P₋(n)) ≤ n / (p - 1) + log_p(n^2 + 1)`.

This isolates the exact open core of Moll's Conjecture 5.5(ii): bounding the excess
valuation from `p`-adic unit cancellation on tie indices where `v_p(P₊(n)) = v_p(P₋(n))`,
split cleanly into `H1` (the canonical case `p = 5`) and `H2` (all primes `p > 5` with
`p ≡ 1 (mod 4)`).
-/

namespace OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R2

open Finset Filter Topology

-- For p = 5, on tie indices where the two 5-adic split factors have equal 5-adic valuation,
-- the excess valuation from 5-adic unit cancellation is o(n).
def H1 : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : ℤ,
    ((5 : ℤ) ^ (n + 1)) ∣ (r ^ 2 + 1) →
    padicValInt 5 (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) =
    padicValInt 5 (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)) →
    ((4 : ℚ) * ((padicValInt 5 (OeisA105751.a n) : ℚ) -
      (padicValInt 5 (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) : ℚ))) / (n : ℚ) ≤ ε

-- For every prime p > 5 with p = 1 mod 4, on tie indices where the two p-adic split factors
-- have equal p-adic valuation, the excess valuation from p-adic unit cancellation is o(n).
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → 5 < p → ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : ℤ,
    ((p : ℤ) ^ (n + 1)) ∣ (r ^ 2 + 1) →
    padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) =
    padicValInt p (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)) →
    (((p - 1 : ℚ)) * ((padicValInt p (OeisA105751.a n) : ℚ) -
      (padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) : ℚ))) / (n : ℚ) ≤ ε

/- ### Section 1: Exact Gaussian integer representation of `OeisA105751.a n` -/

lemma prod_complex_eq_gaussianInt (n : ℕ) :
    ∏ k ∈ Finset.range (n + 1), ((1 : ℂ) + (k : ℂ) * Complex.I) =
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re : ℂ) +
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im : ℂ) * Complex.I := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ (n := n + 1), Finset.prod_range_succ (n := n + 1), ih]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    push_cast
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im : ℂ) *
      ((n : ℂ) + 1) * hI2

lemma a_eq_gaussianInt_im (n : ℕ) :
    OeisA105751.a n = (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im := by
  unfold OeisA105751.a
  dsimp only
  rw [prod_complex_eq_gaussianInt]
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  exact Int.floor_intCast _

lemma gaussianInt_split_mod (n p M : ℕ) (r : ℤ)
    (hr : ((p ^ M : ℕ) : ℤ) ∣ r ^ 2 + 1) :
    ((p ^ M : ℕ) : ℤ) ∣
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re +
        r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im) -
      ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r) ∧
    ((p ^ M : ℕ) : ℤ) ∣
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re -
        r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im) -
      ∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    set z := ∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)
    set Pp := ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)
    set Pm := ∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)
    rw [Finset.prod_range_succ (n := n + 1), Finset.prod_range_succ (n := n + 1),
      Finset.prod_range_succ (n := n + 1)]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    constructor
    · have hid :
          (z.re * 1 + -1 * z.im * ↑(n + 1) + r * (z.re * ↑(n + 1) + z.im * 1)) -
            Pp * (1 + ↑(n + 1) * r) =
          (1 + ↑(n + 1) * r) * (z.re + r * z.im - Pp) - ↑(n + 1) * z.im * (r ^ 2 + 1) := by ring
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_right ih1 _) (dvd_mul_of_dvd_right hr _)
    · have hid :
          (z.re * 1 + -1 * z.im * ↑(n + 1) - r * (z.re * ↑(n + 1) + z.im * 1)) -
            Pm * (1 - ↑(n + 1) * r) =
          (1 - ↑(n + 1) * r) * (z.re - r * z.im - Pm) - ↑(n + 1) * z.im * (r ^ 2 + 1) := by ring
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_right ih2 _) (dvd_mul_of_dvd_right hr _)

lemma two_mul_r_mul_a_sub_split_dvd (n p M : ℕ) (r : ℤ)
    (hr : ((p ^ M : ℕ) : ℤ) ∣ r ^ 2 + 1) :
    ((p ^ M : ℕ) : ℤ) ∣
      2 * r * OeisA105751.a n -
        ((∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) -
         (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r))) := by
  rw [a_eq_gaussianInt_im]
  obtain ⟨h1, h2⟩ := gaussianInt_split_mod n p M r hr
  have hid :
      2 * r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im -
        ((∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) -
         (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r))) =
      (((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re +
          r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im) -
        ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) -
      (((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re -
          r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im) -
        ∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)) := by ring
  rw [hid]
  exact dvd_sub h1 h2

/- ### Section 2: Elementary 2-adic proof that `OeisA105751.a n ≠ 0` for all `n > 3` -/

lemma gaussianInt_prod_congr_mod (W₁ W₂ : ℕ → GaussianInt) (M : ℤ) (a L : ℕ)
    (h : ∀ j, M ∣ (W₁ j).re - (W₂ j).re ∧ M ∣ (W₁ j).im - (W₂ j).im) :
    M ∣ (∏ j ∈ Finset.Ico a (a + L), W₁ j).re - (∏ j ∈ Finset.Ico a (a + L), W₂ j).re ∧
    M ∣ (∏ j ∈ Finset.Ico a (a + L), W₁ j).im - (∏ j ∈ Finset.Ico a (a + L), W₂ j).im := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hsp : Finset.Ico a (a + (L + 1)) = insert (a + L) (Finset.Ico a (a + L)) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : a + L ∉ Finset.Ico a (a + L) := by simp
    rw [hsp, Finset.prod_insert hnot, Finset.prod_insert hnot]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    rcases h (a + L) with ⟨hr, hi⟩
    rcases ih with ⟨ihr, ihi⟩
    set z₁ := ∏ j ∈ Finset.Ico a (a + L), W₁ j
    set z₂ := ∏ j ∈ Finset.Ico a (a + L), W₂ j
    constructor
    · have hid :
          ((W₁ (a + L)).re * z₁.re + -1 * (W₁ (a + L)).im * z₁.im) -
            ((W₂ (a + L)).re * z₂.re + -1 * (W₂ (a + L)).im * z₂.im) =
          ((W₁ (a + L)).re - (W₂ (a + L)).re) * z₁.re + (W₂ (a + L)).re * (z₁.re - z₂.re) -
          (((W₁ (a + L)).im - (W₂ (a + L)).im) * z₁.im + (W₂ (a + L)).im * (z₁.im - z₂.im)) := by ring
      rw [hid]
      exact dvd_sub (dvd_add (dvd_mul_of_dvd_left hr _) (dvd_mul_of_dvd_right ihr _))
        (dvd_add (dvd_mul_of_dvd_left hi _) (dvd_mul_of_dvd_right ihi _))
    · have hid :
          ((W₁ (a + L)).re * z₁.im + (W₁ (a + L)).im * z₁.re) -
            ((W₂ (a + L)).re * z₂.im + (W₂ (a + L)).im * z₂.re) =
          ((W₁ (a + L)).re - (W₂ (a + L)).re) * z₁.im + (W₂ (a + L)).re * (z₁.im - z₂.im) +
          (((W₁ (a + L)).im - (W₂ (a + L)).im) * z₁.re + (W₂ (a + L)).im * (z₁.re - z₂.re)) := by ring
      rw [hid]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left hr _) (dvd_mul_of_dvd_right ihi _))
        (dvd_add (dvd_mul_of_dvd_left hi _) (dvd_mul_of_dvd_right ihr _))

lemma dyadic_block_pow2 (W : ℕ → GaussianInt)
    (hre : ∀ k, Odd (W k).re)
    (him : ∀ k, (W k).im % 8 = 4)
    (hper : ∀ m k, ((2 : ℤ) ^ (m + 4)) ∣ (W (k + 2 ^ m)).re - (W k).re ∧
                   ((2 : ℤ) ^ (m + 4)) ∣ (W (k + 2 ^ m)).im - (W k).im) :
    ∀ m a : ℕ,
      Odd (∏ j ∈ Finset.Ico a (a + 2 ^ m), W j).re ∧
      ((2 : ℤ) ^ (m + 2)) ∣ (∏ j ∈ Finset.Ico a (a + 2 ^ m), W j).im ∧
      ¬ (((2 : ℤ) ^ (m + 3)) ∣ (∏ j ∈ Finset.Ico a (a + 2 ^ m), W j).im) := by
  intro m
  induction m with
  | zero =>
    intro a
    have hIco : Finset.Ico a (a + 2 ^ 0) = {a} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton, pow_zero]; omega
    rw [hIco, Finset.prod_singleton]
    have h4 := him a
    refine ⟨hre a, ?_, ?_⟩
    · refine ⟨(W a).im / 4, ?_⟩; omega
    · rintro ⟨q, hq⟩; omega
  | succ m ih =>
    intro a
    have hsp : Finset.Ico a (a + 2 ^ (m + 1)) =
        Finset.Ico a (a + 2 ^ m) ∪ Finset.Ico (a + 2 ^ m) (a + 2 ^ m + 2 ^ m) := by
      have : a + 2 ^ (m + 1) = a + 2 ^ m + 2 ^ m := by ring
      rw [this]
      exact (Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right a (2 ^ m))
        (Nat.le_add_right (a + 2 ^ m) (2 ^ m))).symm
    have hdisj : Disjoint (Finset.Ico a (a + 2 ^ m)) (Finset.Ico (a + 2 ^ m) (a + 2 ^ m + 2 ^ m)) :=
      Finset.Ico_disjoint_Ico_consecutive a (a + 2 ^ m) (a + 2 ^ m + 2 ^ m)
    rw [hsp, Finset.prod_union hdisj]
    set z₁ := ∏ j ∈ Finset.Ico a (a + 2 ^ m), W j
    set z₂ := ∏ j ∈ Finset.Ico (a + 2 ^ m) (a + 2 ^ m + 2 ^ m), W j
    obtain ⟨hre1, hd1, hnd1⟩ := ih a
    obtain ⟨hre2, hd2, _⟩ := ih (a + 2 ^ m)
    have hshift : z₂ = ∏ j ∈ Finset.Ico a (a + 2 ^ m), W (j + 2 ^ m) := by
      refine Finset.prod_bij (fun x _ => x - 2 ^ m) ?_ ?_ ?_ ?_
      · intro x hx; rw [Finset.mem_Ico] at hx ⊢; omega
      · intro x₁ hx₁ x₂ hx₂ heq; rw [Finset.mem_Ico] at hx₁ hx₂; omega
      · intro j hj; rw [Finset.mem_Ico] at hj
        exact ⟨j + 2 ^ m, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro x hx; rw [Finset.mem_Ico] at hx; congr 1; omega
    have hcong := gaussianInt_prod_congr_mod (fun j => W (j + 2 ^ m)) W ((2 : ℤ) ^ (m + 4)) a (2 ^ m)
      (fun j => hper m j)
    rw [← hshift] at hcong
    rcases hcong with ⟨hcr, hci⟩
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    refine ⟨?_, ?_, ?_⟩
    · have hev1 : Even z₁.im := even_iff_two_dvd.mpr
        ((dvd_pow_self (2 : ℤ) (by omega : m + 2 ≠ 0)).trans hd1)
      have hmul_odd : Odd (z₁.re * z₂.re) := hre1.mul hre2
      have hmul_ev : Even (-1 * z₁.im * z₂.im) := (hev1.mul_left (-1)).mul_right _
      exact hmul_odd.add_even hmul_ev
    · have h2m3_1 : ((2 : ℤ) ^ (m + 3)) ∣ 2 * z₁.re * z₁.im := by
        rcases hd1 with ⟨q, hq⟩
        refine ⟨z₁.re * q, ?_⟩
        rw [hq, pow_succ']; ring
      have hdiff : ((2 : ℤ) ^ (m + 4)) ∣
          (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im := by
        have hid : (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im =
            z₁.re * (z₂.im - z₁.im) + z₁.im * (z₂.re - z₁.re) := by ring
        rw [hid]
        exact dvd_add (dvd_mul_of_dvd_right hci _) (dvd_mul_of_dvd_right hcr _)
      have hdiff3 : ((2 : ℤ) ^ (m + 3)) ∣
          (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im :=
        (pow_dvd_pow (2 : ℤ) (by omega : m + 3 ≤ m + 4)).trans hdiff
      have := dvd_add hdiff3 h2m3_1
      simpa using this
    · intro hd4
      have hdiff : ((2 : ℤ) ^ (m + 4)) ∣
          (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im := by
        have hid : (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im =
            z₁.re * (z₂.im - z₁.im) + z₁.im * (z₂.re - z₁.re) := by ring
        rw [hid]
        exact dvd_add (dvd_mul_of_dvd_right hci _) (dvd_mul_of_dvd_right hcr _)
      have h2r : ((2 : ℤ) ^ (m + 4)) ∣ 2 * z₁.re * z₁.im := by
        have := dvd_sub hd4 hdiff
        simpa using this
      have hri : ((2 : ℤ) ^ (m + 3)) ∣ z₁.re * z₁.im := by
        rcases h2r with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [pow_succ'] at hq
        linarith
      rcases hd1 with ⟨c, hc⟩
      have hc_odd : Odd c := by
        rw [Int.odd_iff]
        by_contra hev
        have h2c : (2 : ℤ) ∣ c := ⟨c / 2, by omega⟩
        rcases h2c with ⟨c', rfl⟩
        apply hnd1
        refine ⟨c', ?_⟩
        rw [hc, pow_succ']; ring
      have h2_dvd : (2 : ℤ) ∣ z₁.re * c := by
        rcases hri with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        have h2m3 : (2 : ℤ) ^ (m + 3) = (2 : ℤ) ^ (m + 2) * 2 := pow_succ (2 : ℤ) (m + 2)
        rw [hc, h2m3] at hq
        have hpos : (2 : ℤ) ^ (m + 2) ≠ 0 := by positivity
        have : (2 : ℤ) ^ (m + 2) * (z₁.re * c) = (2 : ℤ) ^ (m + 2) * (2 * q) := by linarith
        exact mul_left_cancel₀ hpos this
      exact (Int.not_even_iff_odd.mpr (hre1.mul hc_odd)) (even_iff_two_dvd.mpr h2_dvd)

lemma dyadic_block_prod (W : ℕ → GaussianInt)
    (hre : ∀ k, Odd (W k).re)
    (him : ∀ k, (W k).im % 8 = 4)
    (hper : ∀ m k, ((2 : ℤ) ^ (m + 4)) ∣ (W (k + 2 ^ m)).re - (W k).re ∧
                   ((2 : ℤ) ^ (m + 4)) ∣ (W (k + 2 ^ m)).im - (W k).im) :
    ∀ k a : ℕ, 1 ≤ k →
      Odd (∏ j ∈ Finset.Ico a (a + k), W j).re ∧
      ((2 : ℤ) ^ (padicValNat 2 k + 2)) ∣ (∏ j ∈ Finset.Ico a (a + k), W j).im ∧
      ¬ (((2 : ℤ) ^ (padicValNat 2 k + 3)) ∣ (∏ j ∈ Finset.Ico a (a + k), W j).im) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a hk
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set m := padicValNat 2 k
    have h2m_dvd : 2 ^ m ∣ k := pow_padicValNat_dvd
    have h2m_le : 2 ^ m ≤ k := Nat.le_of_dvd (by omega) h2m_dvd
    by_cases hkeq : k = 2 ^ m
    · rw [hkeq]
      exact dyadic_block_pow2 W hre him hper m a
    · set k' := k - 2 ^ m
      have hk'_pos : 1 ≤ k' := by omega
      have hk'_lt : k' < k := by have : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide); omega
      have h2m1_dvd_k' : 2 ^ (m + 1) ∣ k' := by
        obtain ⟨q, hq⟩ := h2m_dvd
        have hq_odd : Odd q := by
          rw [Nat.odd_iff]
          by_contra hev
          have h2q : 2 ∣ q := ⟨q / 2, by omega⟩
          rcases h2q with ⟨q', rfl⟩
          have hd : 2 ^ (m + 1) ∣ k := ⟨q', by rw [hq, pow_succ]; ring⟩
          have hle := (padicValNat_dvd_iff_le (by omega : k ≠ 0)).mp hd
          change m + 1 ≤ m at hle
          omega
        obtain ⟨t, ht⟩ := hq_odd
        refine ⟨t, ?_⟩
        have hk'_eq : k' = 2 ^ m * (q - 1) := by
          calc k' = k - 2 ^ m := rfl
            _ = 2 ^ m * q - 2 ^ m * 1 := by rw [hq, mul_one]
            _ = 2 ^ m * (q - 1) := (Nat.mul_sub_left_distrib _ _ _).symm
        rw [hk'_eq, pow_succ]
        have : q - 1 = 2 * t := by omega
        rw [this]; ring
      have hm'_ge : m + 1 ≤ padicValNat 2 k' :=
        (padicValNat_dvd_iff_le (by omega : k' ≠ 0)).mp h2m1_dvd_k'
      have hsp : Finset.Ico a (a + k) =
          Finset.Ico a (a + 2 ^ m) ∪ Finset.Ico (a + 2 ^ m) (a + 2 ^ m + k') := by
        have : a + k = a + 2 ^ m + k' := by omega
        rw [this]
        exact (Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right a (2 ^ m))
          (Nat.le_add_right (a + 2 ^ m) k')).symm
      have hdisj : Disjoint (Finset.Ico a (a + 2 ^ m)) (Finset.Ico (a + 2 ^ m) (a + 2 ^ m + k')) :=
        Finset.Ico_disjoint_Ico_consecutive a (a + 2 ^ m) (a + 2 ^ m + k')
      rw [hsp, Finset.prod_union hdisj]
      set z₁ := ∏ j ∈ Finset.Ico a (a + 2 ^ m), W j
      set z₂ := ∏ j ∈ Finset.Ico (a + 2 ^ m) (a + 2 ^ m + k'), W j
      obtain ⟨hre1, hd1, hnd1⟩ := dyadic_block_pow2 W hre him hper m a
      obtain ⟨hre2, hd2, _⟩ := ih k' hk'_lt (a + 2 ^ m) hk'_pos
      have hd2' : ((2 : ℤ) ^ (m + 3)) ∣ z₂.im :=
        (pow_dvd_pow (2 : ℤ) (by omega : m + 3 ≤ padicValNat 2 k' + 2)).trans hd2
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      refine ⟨?_, ?_, ?_⟩
      · have hev1 : Even z₁.im := even_iff_two_dvd.mpr
          ((dvd_pow_self (2 : ℤ) (by omega : m + 2 ≠ 0)).trans hd1)
        exact (hre1.mul hre2).add_even ((hev1.mul_left (-1)).mul_right _)
      · exact dvd_add (dvd_mul_of_dvd_right ((pow_dvd_pow (2 : ℤ) (by omega : m + 2 ≤ m + 3)).trans hd2') _)
          (dvd_mul_of_dvd_left hd1 _)
      · intro h3
        have h13 : ((2 : ℤ) ^ (m + 3)) ∣ z₁.im * z₂.re := by
          have := dvd_sub h3 (dvd_mul_of_dvd_right hd2' z₁.re)
          simpa using this
        rcases hd1 with ⟨c, hc⟩
        have hc_odd : Odd c := by
          rw [Int.odd_iff]
          by_contra hev
          have h2c : (2 : ℤ) ∣ c := ⟨c / 2, by omega⟩
          rcases h2c with ⟨c', rfl⟩
          exact hnd1 ⟨c', by rw [hc, pow_succ]; ring⟩
        have h2_dvd : (2 : ℤ) ∣ c * z₂.re := by
          rcases h13 with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          have h2m3 : (2 : ℤ) ^ (m + 3) = (2 : ℤ) ^ (m + 2) * 2 := pow_succ (2 : ℤ) (m + 2)
          rw [hc, h2m3] at hq
          have hpos : (2 : ℤ) ^ (m + 2) ≠ 0 := by positivity
          have : (2 : ℤ) ^ (m + 2) * (c * z₂.re) = (2 : ℤ) ^ (m + 2) * (2 * q) := by linarith
          exact mul_left_cancel₀ hpos this
        exact (Int.not_even_iff_odd.mpr (hc_odd.mul hre2)) (even_iff_two_dvd.mpr h2_dvd)

lemma prod_Ico_eight (f : ℕ → GaussianInt) (a : ℕ) :
    ∏ j ∈ Finset.Ico a (a + 8), f j =
      f a * f (a + 1) * f (a + 2) * f (a + 3) * f (a + 4) * f (a + 5) * f (a + 6) * f (a + 7) := by
  have h1 : a + 8 = (a + 7) + 1 := by omega
  have h2 : a + 7 = (a + 6) + 1 := by omega
  have h3 : a + 6 = (a + 5) + 1 := by omega
  have h4 : a + 5 = (a + 4) + 1 := by omega
  have h5 : a + 4 = (a + 3) + 1 := by omega
  have h6 : a + 3 = (a + 2) + 1 := by omega
  have h7 : a + 2 = (a + 1) + 1 := by omega
  rw [h1, Finset.prod_Ico_succ_top (by omega), h2, Finset.prod_Ico_succ_top (by omega),
    h3, Finset.prod_Ico_succ_top (by omega), h4, Finset.prod_Ico_succ_top (by omega),
    h5, Finset.prod_Ico_succ_top (by omega), h6, Finset.prod_Ico_succ_top (by omega),
    h7, Finset.prod_Ico_succ_top (by omega), Finset.prod_Ico_succ_top (by omega),
    Finset.Ico_self, Finset.prod_empty, one_mul]

lemma block8_zero_identity (k : ℕ) :
    ∏ j ∈ Finset.Ico (8 * k + 1) (8 * k + 9), (⟨1, (j : ℤ)⟩ : GaussianInt) =
      (⟨4, 0⟩ : GaussianInt) *
      ⟨-13975 + (-139680) * (k : ℤ) + (-134528) * (k : ℤ) ^ 2 + 2967552 * (k : ℤ) ^ 3 +
         14672896 * (k : ℤ) ^ 4 + 30965760 * (k : ℤ) ^ 5 + 33947648 * (k : ℤ) ^ 6 +
         18874368 * (k : ℤ) ^ 7 + 4194304 * (k : ℤ) ^ 8,
       -11700 + (-299440) * (k : ℤ) + (-2515968) * (k : ℤ) ^ 2 + (-10103296) * (k : ℤ) ^ 3 +
         (-21934080) * (k : ℤ) ^ 4 + (-26378240) * (k : ℤ) ^ 5 + (-16515072) * (k : ℤ) ^ 6 +
         (-4194304) * (k : ℤ) ^ 7⟩ := by
  rw [show 8 * k + 9 = (8 * k + 1) + 8 by omega, prod_Ico_eight]
  ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> push_cast <;> ring

lemma block8_three_identity (k : ℕ) :
    ∏ j ∈ Finset.Ico (8 * k + 4) (8 * k + 12), (⟨1, (j : ℤ)⟩ : GaussianInt) =
      (⟨4, 0⟩ : GaussianInt) *
      ⟨706745 + 9081120 * (k : ℤ) + 45249664 * (k : ℤ) ^ 2 + 119132160 * (k : ℤ) ^ 3 +
         184984576 * (k : ℤ) ^ 4 + 175472640 * (k : ℤ) ^ 5 + 100007936 * (k : ℤ) ^ 6 +
         31457280 * (k : ℤ) ^ 7 + 4194304 * (k : ℤ) ^ 8,
       -1690260 + (-14500144) * (k : ℤ) + (-51851520) * (k : ℤ) ^ 2 + (-100420096) * (k : ℤ) ^ 3 +
         (-113971200) * (k : ℤ) ^ 4 + (-75923456) * (k : ℤ) ^ 5 + (-27525120) * (k : ℤ) ^ 6 +
         (-4194304) * (k : ℤ) ^ 7⟩ := by
  rw [show 8 * k + 12 = (8 * k + 4) + 8 by omega, prod_Ico_eight]
  ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> push_cast <;> ring

lemma gaussianInt_8k_structure (k : ℕ) :
    ∃ A B : ℤ,
      ∏ j ∈ Finset.range (8 * k + 1), (⟨1, (j : ℤ)⟩ : GaussianInt) =
        ⟨(2 : ℤ) ^ (2 * k) * A, (2 : ℤ) ^ (2 * k) * B⟩ ∧
      Odd A ∧
      (k = 0 → B = 0) ∧
      (1 ≤ k → ((2 : ℤ) ^ (padicValNat 2 k + 2)) ∣ B ∧
               ¬ (((2 : ℤ) ^ (padicValNat 2 k + 3)) ∣ B)) := by
  let W0 : ℕ → GaussianInt := fun j =>
    ⟨-13975 + (-139680) * (j : ℤ) + (-134528) * (j : ℤ) ^ 2 + 2967552 * (j : ℤ) ^ 3 +
       14672896 * (j : ℤ) ^ 4 + 30965760 * (j : ℤ) ^ 5 + 33947648 * (j : ℤ) ^ 6 +
       18874368 * (j : ℤ) ^ 7 + 4194304 * (j : ℤ) ^ 8,
     -11700 + (-299440) * (j : ℤ) + (-2515968) * (j : ℤ) ^ 2 + (-10103296) * (j : ℤ) ^ 3 +
       (-21934080) * (j : ℤ) ^ 4 + (-26378240) * (j : ℤ) ^ 5 + (-16515072) * (j : ℤ) ^ 6 +
       (-4194304) * (j : ℤ) ^ 7⟩
  have hprod : ∏ j ∈ Finset.range (8 * k + 1), (⟨1, (j : ℤ)⟩ : GaussianInt) =
      (⟨(2 : ℤ) ^ (2 * k), 0⟩ : GaussianInt) * ∏ j ∈ Finset.Ico 0 k, W0 j := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hsp : Finset.range (8 * (k + 1) + 1) =
          Finset.range (8 * k + 1) ∪ Finset.Ico (8 * k + 1) (8 * k + 9) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (8 * k + 1)) (Finset.Ico (8 * k + 1) (8 * k + 9)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        rw [Finset.mem_range] at hx1; rw [Finset.mem_Ico] at hx2; omega
      have hIco_succ : Finset.Ico 0 (k + 1) = insert k (Finset.Ico 0 k) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hsp, Finset.prod_union hdisj, ih, block8_zero_identity k,
        hIco_succ, Finset.prod_insert (by simp)]
      have hpow : (⟨(2 : ℤ) ^ (2 * (k + 1)), 0⟩ : GaussianInt) =
          (⟨(2 : ℤ) ^ (2 * k), 0⟩ : GaussianInt) * ⟨4, 0⟩ := by
        ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
        · rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]; ring
        · ring
      rw [hpow]; ring
  set Z := ∏ j ∈ Finset.Ico 0 k, W0 j
  have hre : ∀ j, Odd (W0 j).re := fun j => ⟨-6988 - 69840 * j - 67264 * j ^ 2 +
    1483776 * j ^ 3 + 7336448 * j ^ 4 + 15482880 * j ^ 5 + 16973824 * j ^ 6 +
    9437184 * j ^ 7 + 2097152 * j ^ 8, by simp only [W0]; ring⟩
  have him : ∀ j, (W0 j).im % 8 = 4 := fun j => by
    have : (W0 j).im = 4 + 8 * (-1463 - 37430 * j - 314496 * j ^ 2 - 1262912 * j ^ 3 -
        2741760 * j ^ 4 - 3297280 * j ^ 5 - 2064384 * j ^ 6 - 524288 * j ^ 7) := by
      simp only [W0]; ring
    omega
  have hper : ∀ m j, ((2 : ℤ) ^ (m + 4)) ∣ (W0 (j + 2 ^ m)).re - (W0 j).re ∧
                     ((2 : ℤ) ^ (m + 4)) ∣ (W0 (j + 2 ^ m)).im - (W0 j).im := by
    intro m j
    have h16 : (2 : ℤ) ^ (m + 4) = 16 * ((2 : ℤ) ^ m) := by
      rw [pow_add]; norm_num; ring
    rw [h16]
    set d : ℤ := (2 : ℤ) ^ m
    have hcast : ((j + 2 ^ m : ℕ) : ℤ) = (j : ℤ) + d := by push_cast; rfl
    simp only [W0, hcast]
    constructor
    · refine ⟨-8730 + (-8408) * (2 * j + d) + 185472 * (3 * j ^ 2 + 3 * j * d + d ^ 2) +
        917056 * (4 * j ^ 3 + 6 * j ^ 2 * d + 4 * j * d ^ 2 + d ^ 3) +
        1935360 * (5 * j ^ 4 + 10 * j ^ 3 * d + 10 * j ^ 2 * d ^ 2 + 5 * j * d ^ 3 + d ^ 4) +
        2121728 * (6 * j ^ 5 + 15 * j ^ 4 * d + 20 * j ^ 3 * d ^ 2 + 15 * j ^ 2 * d ^ 3 + 6 * j * d ^ 4 + d ^ 5) +
        1179648 * (7 * j ^ 6 + 21 * j ^ 5 * d + 35 * j ^ 4 * d ^ 2 + 35 * j ^ 3 * d ^ 3 + 21 * j ^ 2 * d ^ 4 + 7 * j * d ^ 5 + d ^ 6) +
        262144 * (8 * j ^ 7 + 28 * j ^ 6 * d + 56 * j ^ 5 * d ^ 2 + 70 * j ^ 4 * d ^ 3 + 56 * j ^ 3 * d ^ 4 + 28 * j ^ 2 * d ^ 5 + 8 * j * d ^ 6 + d ^ 7), by ring⟩
    · refine ⟨-18715 + (-157248) * (2 * j + d) + (-631456) * (3 * j ^ 2 + 3 * j * d + d ^ 2) +
        (-1370880) * (4 * j ^ 3 + 6 * j ^ 2 * d + 4 * j * d ^ 2 + d ^ 3) +
        (-1648640) * (5 * j ^ 4 + 10 * j ^ 3 * d + 10 * j ^ 2 * d ^ 2 + 5 * j * d ^ 3 + d ^ 4) +
        (-1032192) * (6 * j ^ 5 + 15 * j ^ 4 * d + 20 * j ^ 3 * d ^ 2 + 15 * j ^ 2 * d ^ 3 + 6 * j * d ^ 4 + d ^ 5) +
        (-262144) * (7 * j ^ 6 + 21 * j ^ 5 * d + 35 * j ^ 4 * d ^ 2 + 35 * j ^ 3 * d ^ 3 + 21 * j ^ 2 * d ^ 4 + 7 * j * d ^ 5 + d ^ 6), by ring⟩
  refine ⟨Z.re, Z.im, ?_, ?_, ?_, ?_⟩
  · rw [hprod]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  · by_cases hk0 : k = 0
    · subst hk0; simp [Z]
    · simpa [Z] using (dyadic_block_prod W0 hre him hper k 0 (by omega)).1
  · rintro rfl; simp [Z]
  · intro hk1
    simpa [Z] using (dyadic_block_prod W0 hre him hper k 0 hk1).2

lemma gaussianInt_8k3_structure (k : ℕ) :
    ∃ A B : ℤ,
      ∏ j ∈ Finset.range (8 * k + 4), (⟨1, (j : ℤ)⟩ : GaussianInt) =
        ⟨(2 : ℤ) ^ (2 * k + 1) * (-5 * A), (2 : ℤ) ^ (2 * k + 1) * (-5 * B)⟩ ∧
      Odd A ∧
      (k = 0 → B = 0) ∧
      (1 ≤ k → ((2 : ℤ) ^ (padicValNat 2 k + 2)) ∣ B ∧
               ¬ (((2 : ℤ) ^ (padicValNat 2 k + 3)) ∣ B)) := by
  let W3 : ℕ → GaussianInt := fun j =>
    ⟨706745 + 9081120 * (j : ℤ) + 45249664 * (j : ℤ) ^ 2 + 119132160 * (j : ℤ) ^ 3 +
       184984576 * (j : ℤ) ^ 4 + 175472640 * (j : ℤ) ^ 5 + 100007936 * (j : ℤ) ^ 6 +
       31457280 * (j : ℤ) ^ 7 + 4194304 * (j : ℤ) ^ 8,
     -1690260 + (-14500144) * (j : ℤ) + (-51851520) * (j : ℤ) ^ 2 + (-100420096) * (j : ℤ) ^ 3 +
       (-113971200) * (j : ℤ) ^ 4 + (-75923456) * (j : ℤ) ^ 5 + (-27525120) * (j : ℤ) ^ 6 +
       (-4194304) * (j : ℤ) ^ 7⟩
  have hbase3 : ∏ j ∈ Finset.range 4, (⟨1, (j : ℤ)⟩ : GaussianInt) = ⟨-10, 0⟩ := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hprod : ∏ j ∈ Finset.range (8 * k + 4), (⟨1, (j : ℤ)⟩ : GaussianInt) =
      (⟨(2 : ℤ) ^ (2 * k + 1) * (-5), 0⟩ : GaussianInt) * ∏ j ∈ Finset.Ico 0 k, W3 j := by
    induction k with
    | zero =>
      simpa using hbase3
    | succ k ih =>
      have hsp : Finset.range (8 * (k + 1) + 4) =
          Finset.range (8 * k + 4) ∪ Finset.Ico (8 * k + 4) (8 * k + 12) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (8 * k + 4)) (Finset.Ico (8 * k + 4) (8 * k + 12)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        rw [Finset.mem_range] at hx1; rw [Finset.mem_Ico] at hx2; omega
      have hIco_succ : Finset.Ico 0 (k + 1) = insert k (Finset.Ico 0 k) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hsp, Finset.prod_union hdisj, ih, block8_three_identity k,
        hIco_succ, Finset.prod_insert (by simp)]
      have hpow : (⟨(2 : ℤ) ^ (2 * (k + 1) + 1) * (-5), 0⟩ : GaussianInt) =
          (⟨(2 : ℤ) ^ (2 * k + 1) * (-5), 0⟩ : GaussianInt) * ⟨4, 0⟩ := by
        ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
        · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]; ring
        · ring
      rw [hpow]; ring
  set Z := ∏ j ∈ Finset.Ico 0 k, W3 j
  have hre : ∀ j, Odd (W3 j).re := fun j => ⟨353372 + 4540560 * j + 22624832 * j ^ 2 +
    59566080 * j ^ 3 + 92492288 * j ^ 4 + 87736320 * j ^ 5 + 50003968 * j ^ 6 +
    15728640 * j ^ 7 + 2097152 * j ^ 8, by simp only [W3]; ring⟩
  have him : ∀ j, (W3 j).im % 8 = 4 := fun j => by
    have : (W3 j).im = 4 + 8 * (-211283 - 1812518 * j - 6481440 * j ^ 2 - 12552512 * j ^ 3 -
        14246400 * j ^ 4 - 9490432 * j ^ 5 - 3440640 * j ^ 6 - 524288 * j ^ 7) := by
      simp only [W3]; ring
    omega
  have hper : ∀ m j, ((2 : ℤ) ^ (m + 4)) ∣ (W3 (j + 2 ^ m)).re - (W3 j).re ∧
                     ((2 : ℤ) ^ (m + 4)) ∣ (W3 (j + 2 ^ m)).im - (W3 j).im := by
    intro m j
    have h16 : (2 : ℤ) ^ (m + 4) = 16 * ((2 : ℤ) ^ m) := by
      rw [pow_add]; norm_num; ring
    rw [h16]
    set d : ℤ := (2 : ℤ) ^ m
    have hcast : ((j + 2 ^ m : ℕ) : ℤ) = (j : ℤ) + d := by push_cast; rfl
    simp only [W3, hcast]
    constructor
    · refine ⟨567570 + 2828104 * (2 * j + d) + 7445760 * (3 * j ^ 2 + 3 * j * d + d ^ 2) +
        11561536 * (4 * j ^ 3 + 6 * j ^ 2 * d + 4 * j * d ^ 2 + d ^ 3) +
        10967040 * (5 * j ^ 4 + 10 * j ^ 3 * d + 10 * j ^ 2 * d ^ 2 + 5 * j * d ^ 3 + d ^ 4) +
        6250496 * (6 * j ^ 5 + 15 * j ^ 4 * d + 20 * j ^ 3 * d ^ 2 + 15 * j ^ 2 * d ^ 3 + 6 * j * d ^ 4 + d ^ 5) +
        1966080 * (7 * j ^ 6 + 21 * j ^ 5 * d + 35 * j ^ 4 * d ^ 2 + 35 * j ^ 3 * d ^ 3 + 21 * j ^ 2 * d ^ 4 + 7 * j * d ^ 5 + d ^ 6) +
        262144 * (8 * j ^ 7 + 28 * j ^ 6 * d + 56 * j ^ 5 * d ^ 2 + 70 * j ^ 4 * d ^ 3 + 56 * j ^ 3 * d ^ 4 + 28 * j ^ 2 * d ^ 5 + 8 * j * d ^ 6 + d ^ 7), by ring⟩
    · refine ⟨-906259 + (-3240720) * (2 * j + d) + (-6276256) * (3 * j ^ 2 + 3 * j * d + d ^ 2) +
        (-7123200) * (4 * j ^ 3 + 6 * j ^ 2 * d + 4 * j * d ^ 2 + d ^ 3) +
        (-4745216) * (5 * j ^ 4 + 10 * j ^ 3 * d + 10 * j ^ 2 * d ^ 2 + 5 * j * d ^ 3 + d ^ 4) +
        (-1720320) * (6 * j ^ 5 + 15 * j ^ 4 * d + 20 * j ^ 3 * d ^ 2 + 15 * j ^ 2 * d ^ 3 + 6 * j * d ^ 4 + d ^ 5) +
        (-262144) * (7 * j ^ 6 + 21 * j ^ 5 * d + 35 * j ^ 4 * d ^ 2 + 35 * j ^ 3 * d ^ 3 + 21 * j ^ 2 * d ^ 4 + 7 * j * d ^ 5 + d ^ 6), by ring⟩
  refine ⟨Z.re, Z.im, ?_, ?_, ?_, ?_⟩
  · rw [hprod]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
  · by_cases hk0 : k = 0
    · subst hk0; simp [Z]
    · simpa [Z] using (dyadic_block_prod W3 hre him hper k 0 (by omega)).1
  · rintro rfl; simp [Z]
  · intro hk1
    simpa [Z] using (dyadic_block_prod W3 hre him hper k 0 hk1).2

lemma a_ne_zero_of_three_lt (n : ℕ) (hn : 3 < n) : OeisA105751.a n ≠ 0 := by
  rw [a_eq_gaussianInt_im]
  set k := n / 8
  have hmod : n % 8 < 8 := Nat.mod_lt n (by decide)
  have hdiv : n = 8 * k + n % 8 := (Nat.div_add_mod n 8).symm
  have hr : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
            n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by omega
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hk1 : 1 ≤ k := by omega
    rw [show n = 8 * k by omega]
    obtain ⟨A, B, hZ, _, _, hB⟩ := gaussianInt_8k_structure k
    rw [hZ]
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, false_or]
    rintro rfl
    exact (hB hk1).2 (dvd_zero _)
  · rw [show n = 8 * k + 1 by omega, Finset.prod_range_succ]
    obtain ⟨A, B, hZ, hA, hB0, hB1⟩ := gaussianInt_8k_structure k
    rw [hZ]
    simp only [Zsqrtd.im_mul]
    have hBeven : Even B := by
      by_cases hk0 : k = 0
      · rw [hB0 hk0]; exact Even.zero
      · exact even_iff_two_dvd.mpr ((dvd_pow_self (2 : ℤ) (by omega)).trans (hB1 (by omega)).1)
    have hodd : Odd ((8 * (k : ℤ) + 1) * A + B) := by
      have h1 : Odd (8 * (k : ℤ) + 1) := ⟨4 * k, by ring⟩
      exact (h1.mul hA).add_even hBeven
    have hfac : (2 : ℤ) ^ (2 * k) * A * ↑(8 * k + 1) + (2 : ℤ) ^ (2 * k) * B * 1 =
        (2 : ℤ) ^ (2 * k) * ((8 * (k : ℤ) + 1) * A + B) := by push_cast; ring
    rw [hfac]
    intro hzero
    rcases mul_eq_zero.mp hzero with hpow | hsum
    · exact absurd hpow (by positivity)
    · rw [hsum] at hodd
      exact (Int.not_even_iff_odd.mpr hodd) Even.zero
  · rw [show n = 8 * k + 2 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
    obtain ⟨A, B, hZ, hA, hB0, hB1⟩ := gaussianInt_8k_structure k
    rw [hZ]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    have hBeven : Even B := by
      by_cases hk0 : k = 0
      · rw [hB0 hk0]; exact Even.zero
      · exact even_iff_two_dvd.mpr ((dvd_pow_self (2 : ℤ) (by omega)).trans (hB1 (by omega)).1)
    have hodd : Odd ((16 * (k : ℤ) + 3) * A + (1 - (8 * k + 1) * (8 * k + 2)) * B) := by
      have h1 : Odd (16 * (k : ℤ) + 3) := ⟨8 * k + 1, by ring⟩
      exact (h1.mul hA).add_even (hBeven.mul_left _)
    have hfac :
        ((2 : ℤ) ^ (2 * k) * A * 1 + -1 * ((2 : ℤ) ^ (2 * k) * B) * ↑(8 * k + 1)) * ↑(8 * k + 2) +
        ((2 : ℤ) ^ (2 * k) * A * ↑(8 * k + 1) + (2 : ℤ) ^ (2 * k) * B * 1) * 1 =
        (2 : ℤ) ^ (2 * k) * ((16 * (k : ℤ) + 3) * A + (1 - (8 * k + 1) * (8 * k + 2)) * B) := by
      push_cast; ring
    rw [hfac]
    intro hzero
    rcases mul_eq_zero.mp hzero with hpow | hsum
    · exact absurd hpow (by positivity)
    · rw [hsum] at hodd
      exact (Int.not_even_iff_odd.mpr hodd) Even.zero
  · have hk1 : 1 ≤ k := by omega
    rw [show n = 8 * k + 3 by omega]
    obtain ⟨A, B, hZ, _, _, hB⟩ := gaussianInt_8k3_structure k
    rw [hZ]
    intro hzero
    have hB0 : B = 0 := by
      have hpow : (2 : ℤ) ^ (2 * k + 1) ≠ 0 := by positivity
      rcases mul_eq_zero.mp hzero with h1 | h2
      · exact absurd h1 hpow
      · linarith
    rw [hB0] at hB
    exact (hB hk1).2 (dvd_zero _)
  · rw [show n = 8 * k + 4 by omega]
    intro him0
    have hsp : Finset.range (8 * (k + 1) + 1) =
        Finset.range (8 * k + 5) ∪ Finset.Ico (8 * k + 5) (8 * k + 9) := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range (8 * k + 5)) (Finset.Ico (8 * k + 5) (8 * k + 9)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      rw [Finset.mem_range] at hx1; rw [Finset.mem_Ico] at hx2; omega
    set z4 := ∏ j ∈ Finset.range (8 * k + 5), (⟨1, (j : ℤ)⟩ : GaussianInt)
    have hprod8 : ∏ j ∈ Finset.range (8 * (k + 1) + 1), (⟨1, (j : ℤ)⟩ : GaussianInt) =
        z4 * ⟨2 * (715 + 3952 * (k : ℤ) + 7840 * (k : ℤ) ^ 2 + 6656 * (k : ℤ) ^ 3 + 2048 * (k : ℤ) ^ 4),
              2 * (-8 * ((k : ℤ) + 1) * (128 * ((k : ℤ) + 1) ^ 2 - 72 * ((k : ℤ) + 1) + 9))⟩ := by
      rw [hsp, Finset.prod_union hdisj]
      congr 1
      have h4step : ∏ j ∈ Finset.Ico (8 * k + 5) (8 * k + 9), (⟨1, (j : ℤ)⟩ : GaussianInt) =
          ⟨1, (8 * k + 5 : ℤ)⟩ * ⟨1, (8 * k + 6 : ℤ)⟩ * ⟨1, (8 * k + 7 : ℤ)⟩ * ⟨1, (8 * k + 8 : ℤ)⟩ := by
        rw [show 8 * k + 9 = (8 * k + 8) + 1 by omega, Finset.prod_Ico_succ_top (by omega),
          show 8 * k + 8 = (8 * k + 7) + 1 by omega, Finset.prod_Ico_succ_top (by omega),
          show 8 * k + 7 = (8 * k + 6) + 1 by omega, Finset.prod_Ico_succ_top (by omega),
          show 8 * k + 6 = (8 * k + 5) + 1 by omega, Finset.prod_Ico_succ_top (by omega),
          Finset.Ico_self, Finset.prod_empty, one_mul]
        push_cast; rfl
      rw [h4step]
      ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
    obtain ⟨A, B, hZ8, _, _, hB8⟩ := gaussianInt_8k_structure (k + 1)
    rw [hprod8] at hZ8
    have hre8 := congr_arg Zsqrtd.re hZ8
    have him8 := congr_arg Zsqrtd.im hZ8
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, him0, zero_mul, mul_zero, add_zero] at hre8 him8
    set Xg : ℤ := 715 + 3952 * (k : ℤ) + 7840 * (k : ℤ) ^ 2 + 6656 * (k : ℤ) ^ 3 + 2048 * (k : ℤ) ^ 4
    have hXg_odd : Odd Xg := ⟨357 + 1976 * k + 3920 * k ^ 2 + 3328 * k ^ 3 + 1024 * k ^ 4, by
      simp only [Xg]; ring⟩
    have h2k1_z4 : ((2 : ℤ) ^ (2 * k + 1)) ∣ z4.re := by
      have hdvd : ((2 : ℤ) ^ (2 * k + 1)) ∣ z4.re * Xg := by
        refine ⟨A, ?_⟩
        have hpow : (2 : ℤ) ^ (2 * (k + 1)) = 2 * (2 : ℤ) ^ (2 * k + 1) := by
          rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ']
        rw [hpow] at hre8
        linarith
      have hcop : IsCoprime ((2 : ℤ) ^ (2 * k + 1)) Xg := by
        have hc2 : IsCoprime (2 : ℤ) Xg := by
          rw [Int.prime_two.irreducible.coprime_iff_not_dvd]
          intro h2; exact (Int.not_even_iff_odd.mpr hXg_odd) (even_iff_two_dvd.mpr h2)
        exact hc2.pow_left
      exact hcop.dvd_of_dvd_mul_right hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hk1_dvd : ((2 : ℤ) ^ padicValNat 2 (k + 1)) ∣ ((k : ℤ) + 1) := by
      have : 2 ^ padicValNat 2 (k + 1) ∣ k + 1 := pow_padicValNat_dvd
      exact_mod_cast this
    have hB_dvd : ((2 : ℤ) ^ (padicValNat 2 (k + 1) + 3)) ∣ B := by
      rcases h2k1_z4 with ⟨c, hc⟩
      rcases hk1_dvd with ⟨d, hd⟩
      refine ⟨c * (-d) * (128 * ((k : ℤ) + 1) ^ 2 - 72 * ((k : ℤ) + 1) + 9), ?_⟩
      have hpow1 : (2 : ℤ) ^ (2 * (k + 1)) = 2 * (2 : ℤ) ^ (2 * k + 1) := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ']
      have hpow2 : (2 : ℤ) ^ (padicValNat 2 (k + 1) + 3) = 8 * (2 : ℤ) ^ padicValNat 2 (k + 1) := by
        rw [pow_add]; norm_num; ring
      have hpos : (2 : ℤ) ^ (2 * (k + 1)) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpos
      have hd_sub : -8 * ((k : ℤ) + 1) = -8 * ((2 : ℤ) ^ padicValNat 2 (k + 1) * d) := by rw [hd]
      rw [← him8, hc, hpow1, hpow2, hd_sub]
      ring
    exact (hB8 (by omega)).2 hB_dvd
  · rw [show n = 8 * k + 5 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
    obtain ⟨A, B, hZ, hA, hB0, hB1⟩ := gaussianInt_8k3_structure k
    rw [hZ]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    have hBeven : Even B := by
      by_cases hk0 : k = 0
      · rw [hB0 hk0]; exact Even.zero
      · exact even_iff_two_dvd.mpr ((dvd_pow_self (2 : ℤ) (by omega)).trans (hB1 (by omega)).1)
    have hodd : Odd (-5 * ((16 * (k : ℤ) + 9) * A + (1 - (8 * k + 4) * (8 * k + 5)) * B)) := by
      have h1 : Odd (16 * (k : ℤ) + 9) := ⟨8 * k + 4, by ring⟩
      have h5 : Odd (-5 : ℤ) := ⟨-3, by ring⟩
      exact h5.mul ((h1.mul hA).add_even (hBeven.mul_left _))
    have hfac :
        ((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * 1 + -1 * ((2 : ℤ) ^ (2 * k + 1) * (-5 * B)) * ↑(8 * k + 4)) * ↑(8 * k + 5) +
        ((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * ↑(8 * k + 4) + (2 : ℤ) ^ (2 * k + 1) * (-5 * B) * 1) * 1 =
        (2 : ℤ) ^ (2 * k + 1) * (-5 * ((16 * (k : ℤ) + 9) * A + (1 - (8 * k + 4) * (8 * k + 5)) * B)) := by
      push_cast; ring
    rw [hfac]
    intro hzero
    rcases mul_eq_zero.mp hzero with hpow | hsum
    · exact absurd hpow (by positivity)
    · rw [hsum] at hodd
      exact (Int.not_even_iff_odd.mpr hodd) Even.zero
  · rw [show n = 8 * k + 6 by omega, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    obtain ⟨A, B, hZ, hA, hB0, hB1⟩ := gaussianInt_8k3_structure k
    rw [hZ]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    have hBeven : Even B := by
      by_cases hk0 : k = 0
      · rw [hB0 hk0]; exact Even.zero
      · exact even_iff_two_dvd.mpr ((dvd_pow_self (2 : ℤ) (by omega)).trans (hB1 (by omega)).1)
    set cA : ℤ := (16 * (k : ℤ) + 9) + (8 * k + 6) * (1 - (8 * k + 4) * (8 * k + 5))
    set cB : ℤ := (1 - (8 * k + 4) * (8 * k + 5)) - (8 * k + 6) * (16 * k + 9)
    have hcA_odd : Odd cA := by
      have h1 : Odd (16 * (k : ℤ) + 9) := ⟨8 * k + 4, by ring⟩
      have h2 : Even (8 * (k : ℤ) + 6) := ⟨4 * k + 3, by ring⟩
      exact h1.add_even (h2.mul_right _)
    have hodd : Odd (-5 * (cA * A + cB * B)) := by
      have h5 : Odd (-5 : ℤ) := ⟨-3, by ring⟩
      exact h5.mul ((hcA_odd.mul hA).add_even (hBeven.mul_left _))
    have hfac :
        (((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * 1 + -1 * ((2 : ℤ) ^ (2 * k + 1) * (-5 * B)) * ↑(8 * k + 4)) * 1 +
          -1 * ((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * ↑(8 * k + 4) + (2 : ℤ) ^ (2 * k + 1) * (-5 * B) * 1) * ↑(8 * k + 5)) * ↑(8 * k + 6) +
        (((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * 1 + -1 * ((2 : ℤ) ^ (2 * k + 1) * (-5 * B)) * ↑(8 * k + 4)) * ↑(8 * k + 5) +
          ((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * ↑(8 * k + 4) + (2 : ℤ) ^ (2 * k + 1) * (-5 * B) * 1) * 1) * 1 =
        (2 : ℤ) ^ (2 * k + 1) * (-5 * (cA * A + cB * B)) := by
      simp only [cA, cB]; push_cast; ring
    rw [hfac]
    intro hzero
    rcases mul_eq_zero.mp hzero with hpow | hsum
    · exact absurd hpow (by positivity)
    · rw [hsum] at hodd
      exact (Int.not_even_iff_odd.mpr hodd) Even.zero
  · rw [show n = 8 * k + 7 by omega]
    intro him0
    obtain ⟨A, B, hZ8, _, _, hB8⟩ := gaussianInt_8k_structure (k + 1)
    have hstep : ∏ j ∈ Finset.range (8 * (k + 1) + 1), (⟨1, (j : ℤ)⟩ : GaussianInt) =
        (∏ j ∈ Finset.range (8 * k + 8), (⟨1, (j : ℤ)⟩ : GaussianInt)) * ⟨1, (8 * k + 8 : ℤ)⟩ := by
      rw [show 8 * (k + 1) + 1 = (8 * k + 8) + 1 by omega, Finset.prod_range_succ]
      push_cast; rfl
    rw [hstep] at hZ8
    have hre8 := congr_arg Zsqrtd.re hZ8
    have him8 := congr_arg Zsqrtd.im hZ8
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, him0, zero_mul, mul_zero, add_zero, mul_one] at hre8 him8
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hk1_dvd : ((2 : ℤ) ^ padicValNat 2 (k + 1)) ∣ ((k : ℤ) + 1) := by
      have : 2 ^ padicValNat 2 (k + 1) ∣ k + 1 := pow_padicValNat_dvd
      exact_mod_cast this
    have hB_dvd : ((2 : ℤ) ^ (padicValNat 2 (k + 1) + 3)) ∣ B := by
      rcases hk1_dvd with ⟨d, hd⟩
      refine ⟨A * d, ?_⟩
      have hpos : (2 : ℤ) ^ (2 * (k + 1)) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpos
      rw [← him8, hre8]
      have hpow2 : (2 : ℤ) ^ (padicValNat 2 (k + 1) + 3) = 8 * (2 : ℤ) ^ padicValNat 2 (k + 1) := by
        rw [pow_add]; norm_num; ring
      rw [hpow2]
      have h8k : (8 * (k : ℤ) + 8) = 8 * ((k : ℤ) + 1) := by ring
      rw [h8k, hd]; ring
    exact (hB8 (by omega)).2 hB_dvd

/- ### Section 3: Hensel lifting and p-adic valuation bounds on split factors -/

lemma padicValInt_pow_dvd_iff {p j : ℕ} [Fact p.Prime] {a : ℤ} (ha : a ≠ 0) :
    ((p ^ j : ℕ) : ℤ) ∣ a ↔ j ≤ padicValInt p a := by
  rw [Nat.cast_pow, padicValInt_dvd_iff]
  simp [ha]

lemma exists_sq_add_one_dvd_prime_pow (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) (M : ℕ) :
    ∃ r : ℤ, ((p ^ M : ℕ) : ℤ) ∣ r ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  induction M with
  | zero => exact ⟨0, by simp⟩
  | succ M ih =>
    by_cases hM : M = 0
    · subst hM
      obtain ⟨u, hu⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
      refine ⟨(u.val : ℤ), ?_⟩
      rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [ZMod.natCast_zmod_val]
      linear_combination -hu
    · obtain ⟨r, hr⟩ := ih
      obtain ⟨q, hq⟩ := hr
      have hp_dvd_r2 : (p : ℤ) ∣ r ^ 2 + 1 :=
        (dvd_pow_self (p : ℤ) hM).trans (by exact_mod_cast (⟨q, hq⟩ : ((p ^ M : ℕ) : ℤ) ∣ r ^ 2 + 1))
      have h2r_ne0 : ((2 * r : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
        have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        rcases hpz.dvd_or_dvd h0 with h2 | hpr
        · have hle2 : p ≤ 2 := Nat.le_of_dvd (by decide) (Int.ofNat_dvd.mp h2)
          have := hp.two_le
          omega
        · have hp1 : (p : ℤ) ∣ 1 := by
            have : (1 : ℤ) = (r ^ 2 + 1) - r * r := by ring
            rw [this]
            exact dvd_sub hp_dvd_r2 (dvd_mul_of_dvd_left hpr _)
          exact hpz.not_isUnit (isUnit_of_dvd_one hp1)
      set tz : ZMod p := -((q : ZMod p) * ((2 * r : ℤ) : ZMod p)⁻¹)
      set t : ℤ := (tz.val : ℤ)
      have ht_mod : (p : ℤ) ∣ q + 2 * r * t := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        have ht_eq : (t : ZMod p) = tz := by simp [t]
        rw [ht_eq]
        have : ((2 : ZMod p) * (r : ZMod p)) * ((2 * r : ℤ) : ZMod p)⁻¹ = 1 := by
          push_cast at h2r_ne0 ⊢
          exact mul_inv_cancel₀ h2r_ne0
        simp only [tz]
        linear_combination (q : ZMod p) * (-this)
      obtain ⟨c, hc⟩ := ht_mod
      refine ⟨r + t * ((p ^ M : ℕ) : ℤ), ?_⟩
      refine ⟨c + t ^ 2 * ((p ^ (M - 1) : ℕ) : ℤ), ?_⟩
      have hpow1 : ((p ^ (M + 1) : ℕ) : ℤ) = ((p ^ M : ℕ) : ℤ) * (p : ℤ) := by
        push_cast; rw [pow_succ]
      have hpow2 : ((p ^ M : ℕ) : ℤ) = (p : ℤ) * ((p ^ (M - 1) : ℕ) : ℤ) := by
        have hM1 : M = (M - 1) + 1 := by omega
        conv_lhs => rw [hM1, pow_succ']
        push_cast; rfl
      have hpow_sq : ((p ^ M : ℕ) : ℤ) ^ 2 = ((p ^ M : ℕ) : ℤ) * (p : ℤ) * ((p ^ (M - 1) : ℕ) : ℤ) := by
        rw [sq]; conv_lhs => rhs; rw [hpow2]
        ring
      calc (r + t * ((p ^ M : ℕ) : ℤ)) ^ 2 + 1
          = (r ^ 2 + 1) + 2 * r * t * ((p ^ M : ℕ) : ℤ) + t ^ 2 * ((p ^ M : ℕ) : ℤ) ^ 2 := by ring
        _ = ((p ^ M : ℕ) : ℤ) * (q + 2 * r * t) + t ^ 2 * ((p ^ M : ℕ) : ℤ) ^ 2 := by rw [hq]; ring
        _ = ((p ^ M : ℕ) : ℤ) * ((p : ℤ) * c) +
            t ^ 2 * (((p ^ M : ℕ) : ℤ) * (p : ℤ) * ((p ^ (M - 1) : ℕ) : ℤ)) := by
            rw [hc, hpow_sq]
        _ = ((p ^ (M + 1) : ℕ) : ℤ) * (c + t ^ 2 * ((p ^ (M - 1) : ℕ) : ℤ)) := by rw [hpow1]; ring

lemma factor_ne_zero_of_sq_add_one {p n : ℕ} (hp : p.Prime) (h4 : p % 4 = 1)
    {r : ℤ} (hr : ((p ^ (n + 1) : ℕ) : ℤ) ∣ r ^ 2 + 1) (k : ℕ) :
    1 + (k : ℤ) * r ≠ 0 ∧ 1 - (k : ℤ) * r ≠ 0 := by
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  have hr_ne : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1 := by
    have hpd : (p : ℤ) ∣ r ^ 2 + 1 :=
      (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero n)).trans (by exact_mod_cast hr)
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl; simp at hpd; have := Int.le_of_dvd (by decide) hpd; omega
    · rintro rfl; norm_num at hpd; have := Int.le_of_dvd (by decide) hpd; omega
    · rintro rfl; norm_num at hpd; have := Int.le_of_dvd (by decide) hpd; omega
  have habs_r : 2 ≤ |r| := by
    rcases le_or_gt 0 r with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_neg h]; omega
  by_cases hk0 : k = 0
  · subst hk0; norm_num
  · have hkr : 2 ≤ |(k : ℤ) * r| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      have : (1 : ℤ) ≤ k := by omega
      nlinarith
    constructor
    · intro h; have : (k : ℤ) * r = -1 := by linarith
      rw [this] at hkr; norm_num at hkr
    · intro h; have : (k : ℤ) * r = 1 := by linarith
      rw [this] at hkr; norm_num at hkr

lemma sq_add_one_lt_five_pow_succ (n : ℕ) : n ^ 2 + 1 < 5 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ m ih =>
    calc (m + 1) ^ 2 + 1 ≤ 5 * (m ^ 2 + 1) := by nlinarith
      _ < 5 * 5 ^ (m + 1) := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ = 5 ^ (m + 1 + 1) := (pow_succ' 5 (m + 1)).symm

lemma factor_padicVal_le_log {p n : ℕ} (hp : p.Prime) (h4 : p % 4 = 1)
    {r : ℤ} (hr : ((p ^ (n + 1) : ℕ) : ℤ) ∣ r ^ 2 + 1) {k : ℕ} (hk : k ≤ n) :
    padicValInt p (1 + (k : ℤ) * r) ≤ Nat.log p (n ^ 2 + 1) ∧
    padicValInt p (1 - (k : ℤ) * r) ≤ Nat.log p (n ^ 2 + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  have hlog_lt : Nat.log p (n ^ 2 + 1) + 1 ≤ n + 1 := by
    have hlt : n ^ 2 + 1 < p ^ (n + 1) :=
      (sq_add_one_lt_five_pow_succ n).trans_le (Nat.pow_le_pow_left hp5 _)
    have := Nat.log_lt_of_lt_pow (by omega : n ^ 2 + 1 ≠ 0) hlt
    omega
  set L := Nat.log p (n ^ 2 + 1)
  have hnot_dvd : ∀ s : ℤ, (s = 1 ∨ s = -1) → ¬ (((p ^ (L + 1) : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r) := by
    intro s hs hdvd
    have hrL : ((p ^ (L + 1) : ℕ) : ℤ) ∣ r ^ 2 + 1 :=
      (pow_dvd_pow (p : ℤ) hlog_lt).trans (by exact_mod_cast hr)
    have hid : ((k ^ 2 + 1 : ℕ) : ℤ) =
        (k : ℤ) ^ 2 * (r ^ 2 + 1) - (s * (k : ℤ) * r - 1) * (1 + s * (k : ℤ) * r) := by
      rcases hs with rfl | rfl <;> push_cast <;> ring
    have hpk2 : ((p ^ (L + 1) : ℕ) : ℤ) ∣ ((k ^ 2 + 1 : ℕ) : ℤ) := by
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_right hrL _) (dvd_mul_of_dvd_right hdvd _)
    have hnat : p ^ (L + 1) ∣ k ^ 2 + 1 := Int.ofNat_dvd.mp hpk2
    have hle : p ^ (L + 1) ≤ k ^ 2 + 1 := Nat.le_of_dvd (by omega) hnat
    have hkn : k ^ 2 + 1 ≤ n ^ 2 + 1 := by nlinarith
    have hgt : n ^ 2 + 1 < p ^ (L + 1) := Nat.lt_pow_succ_log_self hp.one_lt (n ^ 2 + 1)
    omega
  obtain ⟨hne1, hne2⟩ := factor_ne_zero_of_sq_add_one hp h4 hr k
  constructor
  · by_contra hgt
    push Not at hgt
    have hd : ((p ^ (L + 1) : ℕ) : ℤ) ∣ 1 + (k : ℤ) * r :=
      (padicValInt_pow_dvd_iff hne1).mpr hgt
    exact hnot_dvd 1 (Or.inl rfl) (by simpa using hd)
  · by_contra hgt
    push Not at hgt
    have hd : ((p ^ (L + 1) : ℕ) : ℤ) ∣ 1 - (k : ℤ) * r :=
      (padicValInt_pow_dvd_iff hne2).mpr hgt
    exact hnot_dvd (-1) (Or.inr rfl) (by simpa [sub_eq_add_neg] using hd)

lemma card_block_dvd_linear (p j a : ℕ) (hp : p.Prime) (r s : ℤ)
    (hs : s = 1 ∨ s = -1) (hr : ((p ^ j : ℕ) : ℤ) ∣ r ^ 2 + 1) :
    #((Finset.Ico a (a + p ^ j)).filter (fun k : ℕ => ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r)) = 1 := by
  have hpj_pos : 0 < p ^ j := Nat.pow_pos hp.pos
  have : NeZero (p ^ j) := ⟨hpj_pos.ne'⟩
  have hiff : ∀ k : ℕ, ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r ↔
      (k : ZMod (p ^ j)) = ((s * r : ℤ) : ZMod (p ^ j)) := by
    intro k
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hr0 : ((r : ZMod (p ^ j)) ^ 2 + 1) = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (r ^ 2 + 1) (p ^ j)).mpr hr
      simpa using this
    rcases hs with rfl | rfl
    · push_cast
      constructor
      · intro h0
        have h1 := congr_arg (fun z : ZMod (p ^ j) => z * (r : ZMod (p ^ j))) h0
        linear_combination -h1 + (k : ZMod (p ^ j)) * hr0
      · intro heq; rw [heq]; linear_combination hr0
    · push_cast
      constructor
      · intro h0
        have h1 := congr_arg (fun z : ZMod (p ^ j) => z * (r : ZMod (p ^ j))) h0
        linear_combination h1 + (k : ZMod (p ^ j)) * hr0
      · intro heq; rw [heq]; linear_combination hr0
  set target : ZMod (p ^ j) := ((s * r : ℤ) : ZMod (p ^ j))
  set off := (target - (a : ZMod (p ^ j))).val
  have hoff : off < p ^ j := ZMod.val_lt _
  have hset : (Finset.Ico a (a + p ^ j)).filter
      (fun k : ℕ => ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r) = {a + off} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton, hiff]
    constructor
    · rintro ⟨⟨h1, h2⟩, hk⟩
      have hdiff : ((k - a : ℕ) : ZMod (p ^ j)) = target - (a : ZMod (p ^ j)) := by
        rw [Nat.cast_sub h1, hk]
      have hval := congr_arg ZMod.val hdiff
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : k - a < p ^ j)] at hval
      change k - a = off at hval
      omega
    · rintro rfl
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      push_cast
      simp [off, target]
  rw [hset, Finset.card_singleton]

lemma card_range_dvd_linear_bounds (p j n : ℕ) (hp : p.Prime) (r s : ℤ)
    (hs : s = 1 ∨ s = -1) (hr : ((p ^ j : ℕ) : ℤ) ∣ r ^ 2 + 1) :
    n / p ^ j ≤
      #((Finset.range (n + 1)).filter (fun k : ℕ => ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r)) ∧
    #((Finset.range (n + 1)).filter (fun k : ℕ => ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r)) ≤
      n / p ^ j + 1 := by
  have hpj_pos : 0 < p ^ j := Nat.pow_pos hp.pos
  set q := n / p ^ j with hq_def
  have hfull : ∀ m : ℕ,
      #((Finset.range (m * p ^ j)).filter
        (fun k : ℕ => ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r)) = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsp : Finset.range ((m + 1) * p ^ j) =
          Finset.range (m * p ^ j) ∪ Finset.Ico (m * p ^ j) (m * p ^ j + p ^ j) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
        rw [add_mul, one_mul]; omega
      have hdisj : Disjoint (Finset.range (m * p ^ j))
          (Finset.Ico (m * p ^ j) (m * p ^ j + p ^ j)) := by
        rw [Finset.disjoint_left]; intro x h1 h2
        rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
      rw [hsp, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
        ih, card_block_dvd_linear p j (m * p ^ j) hp r s hs hr]
  have hle1 : q * p ^ j ≤ n + 1 := by
    have h1 : q * p ^ j ≤ n := Nat.div_mul_le_self n (p ^ j)
    omega
  have hle2 : n + 1 ≤ (q + 1) * p ^ j := by
    rw [add_mul, one_mul]
    have h2 : n < q * p ^ j + p ^ j := by
      have := Nat.lt_div_mul_add (a := n) (b := p ^ j) hpj_pos
      simpa [hq_def, mul_comm] using this
    omega
  constructor
  · rw [← hfull q]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hle1))
  · rw [← hfull (q + 1)]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hle2))

lemma padicValInt_prod_split_bounds {p n : ℕ} (hp : p.Prime) (h4 : p % 4 = 1)
    {r : ℤ} (hr : ((p ^ (n + 1) : ℕ) : ℤ) ∣ r ^ 2 + 1) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (∑ j ∈ Finset.Icc 1 (Nat.log p n), n / p ^ j) ≤
      padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + s * (k : ℤ) * r)) ∧
    padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + s * (k : ℤ) * r)) ≤
      ∑ j ∈ Finset.Icc 1 (Nat.log p (n ^ 2 + 1)), (n / p ^ j + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : ∀ k ∈ Finset.range (n + 1), 1 + s * (k : ℤ) * r ≠ 0 := by
    intro k _
    obtain ⟨h1, h2⟩ := factor_ne_zero_of_sq_add_one hp h4 hr k
    rcases hs with rfl | rfl
    · simpa using h1
    · simpa [sub_eq_add_neg] using h2
  have hval_prod : padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + s * (k : ℤ) * r)) =
      ∑ k ∈ Finset.range (n + 1), padicValInt p (1 + s * (k : ℤ) * r) := by
    have haux : ∀ S : Finset ℕ, (∀ k ∈ S, 1 + s * (k : ℤ) * r ≠ 0) →
        padicValInt p (∏ k ∈ S, (1 + s * (k : ℤ) * r)) =
          ∑ k ∈ S, padicValInt p (1 + s * (k : ℤ) * r) := by
      intro S
      induction S using Finset.cons_induction with
      | empty => intro _; simp
      | cons a S ha ih =>
        intro hS
        rw [Finset.prod_cons, Finset.sum_cons]
        have ha0 := hS a (Finset.mem_cons_self a S)
        have hS0 : ∀ k ∈ S, 1 + s * (k : ℤ) * r ≠ 0 := fun k hk => hS k (Finset.mem_cons_of_mem hk)
        have hprod0 : ∏ k ∈ S, (1 + s * (k : ℤ) * r) ≠ 0 := Finset.prod_ne_zero_iff.mpr hS0
        rw [padicValInt.mul ha0 hprod0, ih hS0]
    exact haux (Finset.range (n + 1)) hne
  set L2 := Nat.log p (n ^ 2 + 1)
  have hL2_le : L2 ≤ n + 1 := by
    have hp5 : 5 ≤ p := by have := hp.two_le; omega
    have hlt : n ^ 2 + 1 < p ^ (n + 1) :=
      (sq_add_one_lt_five_pow_succ n).trans_le (Nat.pow_le_pow_left hp5 _)
    exact (Nat.log_lt_of_lt_pow (by omega : n ^ 2 + 1 ≠ 0) hlt).le
  have hlog_le : Nat.log p n ≤ L2 := Nat.log_mono_right (by nlinarith)
  have hval_as_sum : ∑ k ∈ Finset.range (n + 1), padicValInt p (1 + s * (k : ℤ) * r) =
      ∑ j ∈ Finset.Icc 1 L2,
        #((Finset.range (n + 1)).filter
          (fun k : ℕ => ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r)) := by
    have hterm : ∀ k ∈ Finset.range (n + 1),
        padicValInt p (1 + s * (k : ℤ) * r) =
          ∑ j ∈ Finset.Icc 1 L2,
            if ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r then 1 else 0 := by
      intro k hk
      have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hv_le : padicValInt p (1 + s * (k : ℤ) * r) ≤ L2 := by
        obtain ⟨h1, h2⟩ := factor_padicVal_le_log hp h4 hr hk_le
        rcases hs with rfl | rfl
        · simpa using h1
        · simpa [sub_eq_add_neg] using h2
      have hfilt : (Finset.Icc 1 L2).filter (fun j => ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r) =
          Finset.Icc 1 (padicValInt p (1 + s * (k : ℤ) * r)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc, padicValInt_pow_dvd_iff (hne k hk)]
        omega
      rw [← Finset.sum_filter, hfilt, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  rw [hval_prod, hval_as_sum]
  constructor
  · calc ∑ j ∈ Finset.Icc 1 (Nat.log p n), n / p ^ j
        ≤ ∑ j ∈ Finset.Icc 1 (Nat.log p n),
            #((Finset.range (n + 1)).filter
              (fun k : ℕ => ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj_le : j ≤ n + 1 := ((Finset.mem_Icc.mp hj).2.trans hlog_le).trans hL2_le
          have hrj : ((p ^ j : ℕ) : ℤ) ∣ r ^ 2 + 1 :=
            (pow_dvd_pow (p : ℤ) hj_le).trans (by exact_mod_cast hr)
          exact (card_range_dvd_linear_bounds p j n hp r s hs hrj).1
      _ ≤ ∑ j ∈ Finset.Icc 1 L2,
            #((Finset.range (n + 1)).filter
              (fun k : ℕ => ((p ^ j : ℕ) : ℤ) ∣ 1 + s * (k : ℤ) * r)) :=
          Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right hlog_le)
  · refine Finset.sum_le_sum fun j hj => ?_
    have hj_le : j ≤ n + 1 := (Finset.mem_Icc.mp hj).2.trans hL2_le
    have hrj : ((p ^ j : ℕ) : ℤ) ∣ r ^ 2 + 1 :=
      (pow_dvd_pow (p : ℤ) hj_le).trans (by exact_mod_cast hr)
    exact (card_range_dvd_linear_bounds p j n hp r s hs hrj).2

lemma sum_div_pow_bounds (p n L : ℕ) (hp : 2 ≤ p) :
    (p - 1) * (∑ j ∈ Finset.Icc 1 L, n / p ^ j) ≤ n ∧
    n ≤ (p - 1) * (∑ j ∈ Finset.Icc 1 L, n / p ^ j) + (p - 1) * L + n / p ^ L := by
  have hstep_upper : ∀ k : ℕ, (p - 1) * (∑ j ∈ Finset.Icc 1 k, n / p ^ j) + n / p ^ k ≤ n := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      have hI : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hI, Finset.sum_insert (by simp)]
      have hds : n / p ^ (k + 1) = (n / p ^ k) / p := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      have hml : p * (n / p ^ (k + 1)) ≤ n / p ^ k := by
        rw [hds, mul_comm]; exact Nat.div_mul_le_self _ p
      have hdist : (p - 1) * (n / p ^ (k + 1)) + n / p ^ (k + 1) = p * (n / p ^ (k + 1)) := by
        cases p with
        | zero => omega
        | succ p' => simp [Nat.succ_mul, add_comm]
      rw [mul_add]
      omega
  refine ⟨le_trans (Nat.le_add_right _ _) (hstep_upper L), ?_⟩
  induction L with
  | zero => simp
  | succ L ih =>
    have hIcc : Finset.Icc 1 (L + 1) = insert (L + 1) (Finset.Icc 1 L) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hdiv_step : n / p ^ (L + 1) = (n / p ^ L) / p := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have hmul_ge : n / p ^ L ≤ p * (n / p ^ (L + 1)) + (p - 1) := by
      rw [hdiv_step]
      have hmod := Nat.div_add_mod (n / p ^ L) p
      have hlt := Nat.mod_lt (n / p ^ L) (by omega : 0 < p)
      omega
    have hdist : (p - 1) * (n / p ^ (L + 1)) + n / p ^ (L + 1) = p * (n / p ^ (L + 1)) := by
      cases p with
      | zero => omega
      | succ p' => simp [Nat.succ_mul, add_comm]
    rw [mul_add, mul_add, mul_one]
    omega

lemma sq_add_one_lt_five_pow_half (m : ℕ) (hm : 4 ≤ m) :
    m ^ 2 + 1 < 5 ^ (m / 2 + 1) := by
  have heven : ∀ t : ℕ, 2 ≤ t → (2 * t) ^ 2 + 1 < 5 ^ (t + 1) := by
    intro t ht
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases ht2 : t < 2
      · have : t = 1 := by omega
        subst this; decide
      · calc (2 * (t + 1)) ^ 2 + 1 ≤ 5 * ((2 * t) ^ 2 + 1) := by nlinarith
          _ < 5 * 5 ^ (t + 1) := Nat.mul_lt_mul_of_pos_left (ih (by omega)) (by decide)
          _ = 5 ^ (t + 1 + 1) := (pow_succ' 5 (t + 1)).symm
  have hodd : ∀ t : ℕ, 2 ≤ t → (2 * t + 1) ^ 2 + 1 < 5 ^ (t + 1) := by
    intro t ht
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases ht2 : t < 2
      · have : t = 1 := by omega
        subst this; decide
      · calc (2 * (t + 1) + 1) ^ 2 + 1 ≤ 5 * ((2 * t + 1) ^ 2 + 1) := by nlinarith
          _ < 5 * 5 ^ (t + 1) := Nat.mul_lt_mul_of_pos_left (ih (by omega)) (by decide)
          _ = 5 ^ (t + 1 + 1) := (pow_succ' 5 (t + 1)).symm
  set t := m / 2
  have ht2 : 2 ≤ t := by omega
  by_cases hpar : m % 2 = 0
  · rw [show m = 2 * t by omega]; exact heven t ht2
  · rw [show m = 2 * t + 1 by omega]; exact hodd t ht2

lemma padicValInt_a_lower_and_nontie {p n : ℕ} (hp : p.Prime) (h4 : p % 4 = 1)
    (hn : 3 < n) {r : ℤ} (hr : ((p ^ (n + 1) : ℕ) : ℤ) ∣ r ^ 2 + 1) :
    min (padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)))
        (padicValInt p (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r))) ≤
      padicValInt p (OeisA105751.a n) ∧
    (padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) ≠
     padicValInt p (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)) →
      padicValInt p (OeisA105751.a n) =
        min (padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)))
            (padicValInt p (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  set Pp := ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)
  set Pm := ∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)
  set vp := padicValInt p Pp
  set vm := padicValInt p Pm
  have hPp_ne : Pp ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ =>
    (factor_ne_zero_of_sq_add_one hp h4 hr k).1
  have hPm_ne : Pm ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ =>
    (factor_ne_zero_of_sq_add_one hp h4 hr k).2
  have ha_ne : OeisA105751.a n ≠ 0 := a_ne_zero_of_three_lt n hn
  have hv_lt : ∀ v, v ≤ ∑ j ∈ Finset.Icc 1 (Nat.log p (n ^ 2 + 1)), (n / p ^ j + 1) → v < n + 1 := by
    intro v hv
    have hsum_split : ∑ j ∈ Finset.Icc 1 (Nat.log p (n ^ 2 + 1)), (n / p ^ j + 1) =
        (∑ j ∈ Finset.Icc 1 (Nat.log p (n ^ 2 + 1)), n / p ^ j) + Nat.log p (n ^ 2 + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
      omega
    have hub := (sum_div_pow_bounds p n (Nat.log p (n ^ 2 + 1)) (by omega)).1
    have hlog_bound : 4 * Nat.log p (n ^ 2 + 1) < 3 * n + 4 := by
      have hlt : n ^ 2 + 1 < p ^ (n / 2 + 1) :=
        (sq_add_one_lt_five_pow_half n hn).trans_le (Nat.pow_le_pow_left hp5 _)
      have hlog_lt := Nat.log_lt_of_lt_pow (by omega : n ^ 2 + 1 ≠ 0) hlt
      omega
    rw [hsum_split] at hv
    have h2 : 4 * ∑ j ∈ Finset.Icc 1 (Nat.log p (n ^ 2 + 1)), n / p ^ j ≤ n :=
      (Nat.mul_le_mul_right _ (by omega : 4 ≤ p - 1)).trans hub
    omega
  have hPp_eq : (∏ k ∈ Finset.range (n + 1), (1 + (1 : ℤ) * (k : ℤ) * r)) = Pp :=
    Finset.prod_congr rfl fun k _ => by ring
  have hPm_eq : (∏ k ∈ Finset.range (n + 1), (1 + (-1 : ℤ) * (k : ℤ) * r)) = Pm :=
    Finset.prod_congr rfl fun k _ => by ring
  have hvp_lt : vp < n + 1 := hv_lt vp (by
    have h := (padicValInt_prod_split_bounds hp h4 hr 1 (Or.inl rfl)).2
    rwa [hPp_eq] at h)
  have hvm_lt : vm < n + 1 := hv_lt vm (by
    have h := (padicValInt_prod_split_bounds hp h4 hr (-1) (Or.inr rfl)).2
    rwa [hPm_eq] at h)
  have h2r_cop : ¬ (p : ℤ) ∣ 2 * r := by
    intro h0
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpz.dvd_or_dvd h0 with h2 | hpr
    · have hle2 : p ≤ 2 := Nat.le_of_dvd (by decide) (Int.ofNat_dvd.mp h2)
      omega
    · have hpd : (p : ℤ) ∣ r ^ 2 + 1 :=
        (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero n)).trans (by exact_mod_cast hr)
      have hp1 : (p : ℤ) ∣ 1 := by
        have : (1 : ℤ) = (r ^ 2 + 1) - r * r := by ring
        rw [this]
        exact dvd_sub hpd (dvd_mul_of_dvd_left hpr _)
      exact hpz.not_isUnit (isUnit_of_dvd_one hp1)
  have h2r_ne0 : 2 * r ≠ 0 := fun h => h2r_cop (by rw [h]; exact dvd_zero _)
  have h2r_val : padicValInt p (2 * r) = 0 := padicValInt.eq_zero_of_not_dvd h2r_cop
  have hval_2ra : padicValInt p (2 * r * OeisA105751.a n) = padicValInt p (OeisA105751.a n) := by
    rw [padicValInt.mul h2r_ne0 ha_ne, h2r_val, zero_add]
  have hcong := two_mul_r_mul_a_sub_split_dvd n p (n + 1) r hr
  have hlower : min vp vm ≤ padicValInt p (OeisA105751.a n) := by
    rw [← hval_2ra, ← padicValInt_pow_dvd_iff (mul_ne_zero h2r_ne0 ha_ne)]
    have hle : min vp vm ≤ n + 1 := (min_le_left vp vm).trans hvp_lt.le
    have h1 : ((p ^ min vp vm : ℕ) : ℤ) ∣ Pp :=
      (padicValInt_pow_dvd_iff hPp_ne).mpr (min_le_left vp vm)
    have h2 : ((p ^ min vp vm : ℕ) : ℤ) ∣ Pm :=
      (padicValInt_pow_dvd_iff hPm_ne).mpr (min_le_right vp vm)
    have h3 : ((p ^ min vp vm : ℕ) : ℤ) ∣ 2 * r * OeisA105751.a n - (Pp - Pm) :=
      (pow_dvd_pow (p : ℤ) hle).trans (by exact_mod_cast hcong)
    have := dvd_add h3 (dvd_sub h1 h2)
    simpa using this
  refine ⟨hlower, ?_⟩
  intro hne
  apply le_antisymm _ hlower
  by_contra hgt
  push Not at hgt
  have hd_2ra : ((p ^ (min vp vm + 1) : ℕ) : ℤ) ∣ 2 * r * OeisA105751.a n := by
    rw [padicValInt_pow_dvd_iff (mul_ne_zero h2r_ne0 ha_ne), hval_2ra]
    exact hgt
  have hle1 : min vp vm + 1 ≤ n + 1 := by omega
  have h3 : ((p ^ (min vp vm + 1) : ℕ) : ℤ) ∣ 2 * r * OeisA105751.a n - (Pp - Pm) :=
    (pow_dvd_pow (p : ℤ) hle1).trans (by exact_mod_cast hcong)
  have hd_diff : ((p ^ (min vp vm + 1) : ℕ) : ℤ) ∣ Pp - Pm := by
    have := dvd_sub hd_2ra h3
    simpa using this
  rcases lt_or_gt_of_ne hne with hlt | hgt'
  · have hmin : min vp vm = vp := min_eq_left hlt.le
    rw [hmin] at hd_diff
    have hd_Pm : ((p ^ (vp + 1) : ℕ) : ℤ) ∣ Pm :=
      (padicValInt_pow_dvd_iff hPm_ne).mpr hlt
    have hd_Pp : ((p ^ (vp + 1) : ℕ) : ℤ) ∣ Pp := by
      have := dvd_add hd_diff hd_Pm
      simpa using this
    have := (padicValInt_pow_dvd_iff hPp_ne).mp hd_Pp
    omega
  · have hmin : min vp vm = vm := min_eq_right hgt'.le
    rw [hmin] at hd_diff
    have hd_Pp : ((p ^ (vm + 1) : ℕ) : ℤ) ∣ Pp :=
      (padicValInt_pow_dvd_iff hPp_ne).mpr hgt'
    have hd_Pm : ((p ^ (vm + 1) : ℕ) : ℤ) ∣ Pm := by
      have := dvd_sub hd_Pp hd_diff
      simpa using this
    have := (padicValInt_pow_dvd_iff hPm_ne).mp hd_Pm
    omega

lemma padicValInt_a_lower {p n : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) (hn : 3 < n) :
    n ≤ (p - 1) * padicValInt p (OeisA105751.a n) + (p - 1) * Nat.log p n + p := by
  obtain ⟨r, hr⟩ := exists_sq_add_one_dvd_prime_pow p hp h4 (n + 1)
  have hlow := (padicValInt_a_lower_and_nontie hp h4 hn hr).1
  have hPp := (padicValInt_prod_split_bounds hp h4 hr 1 (Or.inl rfl)).1
  have hPm := (padicValInt_prod_split_bounds hp h4 hr (-1) (Or.inr rfl)).1
  have hPp_eq : (∏ k ∈ Finset.range (n + 1), (1 + (1 : ℤ) * (k : ℤ) * r)) =
      ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r) :=
    Finset.prod_congr rfl fun k _ => by ring
  have hPm_eq : (∏ k ∈ Finset.range (n + 1), (1 + (-1 : ℤ) * (k : ℤ) * r)) =
      ∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r) :=
    Finset.prod_congr rfl fun k _ => by ring
  rw [hPp_eq] at hPp
  rw [hPm_eq] at hPm
  have hsum_le : ∑ j ∈ Finset.Icc 1 (Nat.log p n), n / p ^ j ≤ padicValInt p (OeisA105751.a n) :=
    (le_min hPp hPm).trans hlow
  have hgeo := (sum_div_pow_bounds p n (Nat.log p n) hp.two_le).2
  have hdiv_lt : n / p ^ Nat.log p n < p := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos hp.pos), ← pow_succ']
    exact Nat.lt_pow_succ_log_self hp.one_lt n
  have hmul := Nat.mul_le_mul_left (p - 1) hsum_le
  omega

/- ### Section 4: Assemble the reduction `main` -/

lemma nat_log_div_small (p : ℕ) (hp : 2 ≤ p) (δ : ℚ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (((p - 1 : ℕ) : ℚ) * (Nat.log p (n ^ 2 + 1) : ℚ) + (p : ℚ)) / (n : ℚ) ≤ δ := by
  have hpow2_sq : ∀ u : ℕ, 4 ≤ u → u ^ 2 ≤ 2 ^ u := by
    intro u hu
    induction u with
    | zero => omega
    | succ u ih =>
      by_cases hu4 : u < 4
      · have : u = 3 := by omega
        subst this; decide
      · calc (u + 1) ^ 2 ≤ 2 * u ^ 2 := by nlinarith
          _ ≤ 2 * 2 ^ u := Nat.mul_le_mul_left 2 (ih (by omega))
          _ = 2 ^ (u + 1) := (pow_succ' 2 u).symm
  obtain ⟨K, hK⟩ := exists_nat_gt ((4 * (p : ℚ)) / δ)
  set N := max 16 (2 ^ (max 4 (4 * K)))
  refine ⟨N, fun n hn => ?_⟩
  have hn16 : 16 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  rw [div_le_iff₀ hn_pos]
  set u := Nat.log 2 n
  have hu4 : 4 ≤ u := by
    have : 2 ^ 4 ≤ n := by omega
    exact (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr this
  have hu_ge_4K : 4 * K ≤ u := by
    have hle : 2 ^ (max 4 (4 * K)) ≤ n := le_trans (le_max_right _ _) hn
    have := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hle
    exact le_trans (le_max_right _ _) this
  have hlogp_le : Nat.log p (n ^ 2 + 1) ≤ 2 * u + 2 := by
    have hlt1 : n < 2 ^ (u + 1) := Nat.lt_pow_succ_log_self (by decide) n
    have hlt2 : n ^ 2 + 1 < 2 ^ (2 * u + 3) := by
      have hsq : n ^ 2 < (2 ^ (u + 1)) ^ 2 := Nat.pow_lt_pow_left hlt1 (by decide)
      have hpow : (2 ^ (u + 1)) ^ 2 = 2 ^ (2 * u + 2) := by rw [← pow_mul]; congr 1; omega
      rw [hpow] at hsq
      have hpos : 1 ≤ 2 ^ (2 * u + 2) := Nat.one_le_pow _ _ (by decide)
      calc n ^ 2 + 1 ≤ 2 ^ (2 * u + 2) := by omega
        _ < 2 * 2 ^ (2 * u + 2) := by omega
        _ = 2 ^ (2 * u + 3) := (pow_succ' 2 (2 * u + 2)).symm
    have hlt3 : n ^ 2 + 1 < p ^ (2 * u + 3) := hlt2.trans_le (Nat.pow_le_pow_left hp _)
    have := Nat.log_lt_of_lt_pow (by omega : n ^ 2 + 1 ≠ 0) hlt3
    omega
  have hu2_le_n : u ^ 2 ≤ n := (hpow2_sq u hu4).trans (Nat.pow_log_le_self 2 (by omega))
  have hK_le : 4 * K * u ≤ n := by
    calc 4 * K * u ≤ u * u := Nat.mul_le_mul_right u hu_ge_4K
      _ = u ^ 2 := (sq u).symm
      _ ≤ n := hu2_le_n
  have hnum_le : (p - 1) * Nat.log p (n ^ 2 + 1) + p ≤ 4 * p * u := by
    have h1 : (p - 1) * Nat.log p (n ^ 2 + 1) ≤ p * (2 * u + 2) :=
      Nat.mul_le_mul (by omega) hlogp_le
    nlinarith
  have hnum_q : (((p - 1 : ℕ) : ℚ) * (Nat.log p (n ^ 2 + 1) : ℚ) + (p : ℚ)) ≤
      4 * (p : ℚ) * (u : ℚ) := by exact_mod_cast hnum_le
  have hKu_q : 4 * (K : ℚ) * (u : ℚ) ≤ (n : ℚ) := by exact_mod_cast hK_le
  have h4p_lt : 4 * (p : ℚ) < δ * (K : ℚ) := by
    rw [div_lt_iff₀ hδ] at hK
    linarith
  have hu_nn : (0 : ℚ) ≤ (u : ℚ) := Nat.cast_nonneg u
  calc (((p - 1 : ℕ) : ℚ) * (Nat.log p (n ^ 2 + 1) : ℚ) + (p : ℚ))
      ≤ 4 * (p : ℚ) * (u : ℚ) := hnum_q
    _ ≤ (δ * (K : ℚ)) * (u : ℚ) := mul_le_mul_of_nonneg_right h4p_lt.le hu_nn
    _ = δ * ((K : ℚ) * (u : ℚ)) := by ring
    _ ≤ δ * (n : ℚ) := mul_le_mul_of_nonneg_left (by linarith) hδ.le

theorem main : H1 → H2 → type_of% @OeisA105751.conjecture.variants.moll_p_mod_4_eq_1 := by
  intro h1 h2 p hp h4
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_lt⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 2 by linarith)
  have hδq : (0 : ℚ) < δ := by exact_mod_cast hδ_pos
  have hδ2q : (0 : ℚ) < δ / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := nat_log_div_small p hp.two_le (δ / 2) hδ2q
  have hp5_cases : p = 5 ∨ 5 < p := by
    have := hp.two_le; omega
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → ∀ r : ℤ,
      ((p : ℤ) ^ (n + 1)) ∣ (r ^ 2 + 1) →
      padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) =
      padicValInt p (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)) →
      (((p - 1 : ℚ)) * ((padicValInt p (OeisA105751.a n) : ℚ) -
        (padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) : ℚ))) / (n : ℚ) ≤ δ / 2 := by
    rcases hp5_cases with rfl | hp5
    · obtain ⟨N₂, hN₂⟩ := h1 (δ / 2) hδ2q
      refine ⟨N₂, fun n hn r hr htie => ?_⟩
      have h51 : ((5 : ℚ) - 1) = 4 := by norm_num
      simpa [h51] using hN₂ n hn r hr htie
    · exact h2 p hp h4 hp5 (δ / 2) hδ2q
  refine ⟨max 4 (max N₁ N₂), fun n hn => ?_⟩
  have hn3 : 3 < n := by have : 4 ≤ n := le_trans (le_max_left _ _) hn; omega
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn_pos : (0 : ℚ) < (n : ℚ) := by positivity
  have hp1_cast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.cast_sub (by have := hp.two_le; omega : 1 ≤ p), Nat.cast_one]
  have hlow_q : 1 - δ ≤ ((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) / (n : ℚ) := by
    have hlow_nat := padicValInt_a_lower hp h4 hn3
    have hlog_mono : Nat.log p n ≤ Nat.log p (n ^ 2 + 1) := Nat.log_mono_right (by nlinarith)
    have hlow_nat' : n ≤ (p - 1) * padicValInt p (OeisA105751.a n) +
        (p - 1) * Nat.log p (n ^ 2 + 1) + p := by
      have := Nat.mul_le_mul_left (p - 1) hlog_mono
      omega
    have hlow_r : (n : ℚ) ≤ ((p - 1 : ℕ) : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ) +
        ((p - 1 : ℕ) : ℚ) * (Nat.log p (n ^ 2 + 1) : ℚ) + (p : ℚ) := by
      exact_mod_cast hlow_nat'
    have hdiv := hN₁ n hn1
    rw [div_le_iff₀ hn_pos] at hdiv
    rw [le_div_iff₀ hn_pos, ← hp1_cast]
    nlinarith
  have hup_q : ((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) / (n : ℚ) ≤ 1 + δ := by
    obtain ⟨r, hr⟩ := exists_sq_add_one_dvd_prime_pow p hp h4 (n + 1)
    set vp := padicValInt p (∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r))
    set vm := padicValInt p (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r))
    have hvp_up : ((p - 1 : ℚ) * (vp : ℚ)) / (n : ℚ) ≤ 1 + δ / 2 := by
      have h1 := (padicValInt_prod_split_bounds hp h4 hr 1 (Or.inl rfl)).2
      have hPp_eq : (∏ k ∈ Finset.range (n + 1), (1 + (1 : ℤ) * (k : ℤ) * r)) =
          ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r) :=
        Finset.prod_congr rfl fun k _ => by ring
      rw [hPp_eq] at h1
      have hsum_split : ∑ j ∈ Finset.Icc 1 (Nat.log p (n ^ 2 + 1)), (n / p ^ j + 1) =
          (∑ j ∈ Finset.Icc 1 (Nat.log p (n ^ 2 + 1)), n / p ^ j) + Nat.log p (n ^ 2 + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]; omega
      have h2 := (sum_div_pow_bounds p n (Nat.log p (n ^ 2 + 1)) hp.two_le).1
      have hnat : (p - 1) * vp ≤ n + (p - 1) * Nat.log p (n ^ 2 + 1) := by
        have hvp' : vp ≤ (∑ j ∈ Finset.Icc 1 (Nat.log p (n ^ 2 + 1)), n / p ^ j) +
            Nat.log p (n ^ 2 + 1) := by
          rw [← hsum_split]; exact h1
        have := Nat.mul_le_mul_left (p - 1) hvp'
        rw [mul_add] at this
        omega
      have hq : ((p - 1 : ℕ) : ℚ) * (vp : ℚ) ≤
          (n : ℚ) + ((p - 1 : ℕ) : ℚ) * (Nat.log p (n ^ 2 + 1) : ℚ) := by exact_mod_cast hnat
      have hdiv := hN₁ n hn1
      rw [div_le_iff₀ hn_pos] at hdiv
      rw [div_le_iff₀ hn_pos, ← hp1_cast]
      have hp_nn : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
      linarith
    by_cases htie : vp = vm
    · have hexcess := hN₂ n hn2 r hr htie
      have hsplit : ((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) / (n : ℚ) =
          ((p - 1 : ℚ) * (vp : ℚ)) / (n : ℚ) +
          ((p - 1 : ℚ) * ((padicValInt p (OeisA105751.a n) : ℚ) - (vp : ℚ))) / (n : ℚ) := by ring
      rw [hsplit]
      linarith
    · have heq := (padicValInt_a_lower_and_nontie hp h4 hn3 hr).2 htie
      have hle_vp : padicValInt p (OeisA105751.a n) ≤ vp := by
        rw [heq]; exact min_le_left vp vm
      have hle_q : ((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) / (n : ℚ) ≤
          ((p - 1 : ℚ) * (vp : ℚ)) / (n : ℚ) := by
        refine div_le_div_of_nonneg_right ?_ hn_pos.le
        have hp1_nn : (0 : ℚ) ≤ (p : ℚ) - 1 := by
          have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
          linarith
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle_vp) hp1_nn
      linarith
  have habs_q : |((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) / (n : ℚ) - 1| ≤ δ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Rat.dist_eq]
  have habs_r : (|((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) / (n : ℚ) - 1| : ℝ) ≤ (δ : ℝ) := by
    exact_mod_cast habs_q
  push_cast at habs_r ⊢
  linarith

end OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R2
