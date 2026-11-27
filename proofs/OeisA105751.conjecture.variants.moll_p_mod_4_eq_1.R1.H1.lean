import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1
import Mathlib

/-! # `p ^ ν_p(n!)` divides the imaginary part of `∏_{k ≤ n} (1 + k i)` when `p ≡ 1 (mod 4)`

Write `P = ∏_{k ≤ n} (1 + k √-1)` in `ℤ√-1`, so that `a n = P.im`. Put `M = p ^ ν_p(n!)`.
Hensel lifting gives `c` with `c ^ 2 = -1` in `ZMod M`. For `r = ± c` the ring map
`ℤ√-1 → ZMod M`, `√-1 ↦ r`, sends `P` to `∏ (1 + k r) = r ^ (n + 1) ∏ (k - r)`, and
`∏_{k ≤ n} (k - r)` is the image of an ascending factorial with `n + 1` factors, a multiple of
`n!`, hence of `M`. So `P.re + P.im c = P.re - P.im c = 0`, giving `2 P.im = 0` in `ZMod M`;
as `M` is odd, `M ∣ P.im`. -/

open Finset

namespace OMA.A105751

/-- The product `∏_{k ≤ n} (1 + k √-1)` in `ℤ√-1`. -/
def Q (n : ℕ) : ℤ√(-1) := ∏ k ∈ range (n + 1), (1 + (k : ℤ√(-1)) * Zsqrtd.sqrtd)

lemma lift_Q {R : Type*} [CommRing R] (r : {r : R // r * r = ((-1 : ℤ) : R)}) (n : ℕ) :
    Zsqrtd.lift r (Q n) = ∏ k ∈ range (n + 1), (1 + (k : R) * r.1) := by
  rw [Q, map_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [map_add, map_one, map_mul, map_natCast]
  simp

lemma a_eq (n : ℕ) : OeisA105751.a n = (Q n).im := by
  have h : (∏ k ∈ range (n + 1), (1 + (k : ℂ) * Complex.I)) =
      Zsqrtd.lift ⟨Complex.I, by simp⟩ (Q n) := by
    rw [lift_Q]
  show ⌊(∏ k ∈ range (n + 1), (1 + (k : ℂ) * Complex.I)).im⌋ = _
  rw [h]
  change ⌊(GaussianInt.toComplex (Q n)).im⌋ = (Q n).im
  rw [← GaussianInt.intCast_im, Int.floor_intCast]

lemma exists_sqrt_neg_one (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) :
    ∀ j : ℕ, ∃ y : ℤ, (p : ℤ) ^ j ∣ y ^ 2 + 1 := by
  have := Fact.mk hp
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (by omega : p % 4 ≠ 3)
  have base : (p : ℤ) ∣ (r.val : ℤ) ^ 2 + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, sq, ← hr]
    ring
  have two_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have := hp.two_le
    omega
  intro j
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨r.val, by simpa using base⟩
    obtain ⟨y, t, ht⟩ := ih
    have hyp : ((y : ZMod p)) ^ 2 + 1 = 0 := by
      have : (p : ℤ) ∣ y ^ 2 + 1 := by
        rw [ht]
        exact Dvd.dvd.mul_right (dvd_pow_self _ hj.ne') _
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      push_cast at this
      exact this
    have hy0 : (y : ZMod p) ≠ 0 := by
      intro h
      rw [h] at hyp
      simp at hyp
    have h2y : (2 * (y : ZMod p)) ≠ 0 := mul_ne_zero two_ne hy0
    set s : ℤ := (((-(t : ZMod p)) * (2 * (y : ZMod p))⁻¹).val : ℤ) with hs
    have hsz : (s : ZMod p) = (-(t : ZMod p)) * (2 * (y : ZMod p))⁻¹ := by
      rw [hs]
      push_cast
      rw [ZMod.natCast_zmod_val]
    have hdiv : (p : ℤ) ∣ t + 2 * y * s := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hsz]
      field_simp
      ring
    refine ⟨y + s * (p : ℤ) ^ j, ?_⟩
    have e : (y + s * (p : ℤ) ^ j) ^ 2 + 1 =
        (p : ℤ) ^ j * (t + 2 * y * s) + s ^ 2 * (p : ℤ) ^ (2 * j) := by
      linear_combination ht
    rw [e]
    apply dvd_add
    · rw [pow_succ]
      exact mul_dvd_mul_left _ hdiv
    · exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _

end OMA.A105751

open OMA.A105751 in
theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 := by
  unfold OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1
  intro p hp h4 n
  rw [a_eq]
  set v := padicValNat p n.factorial with hv
  set M := p ^ v with hM
  have hMpos : 0 < M := pow_pos hp.pos v
  have : NeZero M := ⟨hMpos.ne'⟩
  have hMdvd : M ∣ n.factorial := pow_padicValNat_dvd
  obtain ⟨y, hy⟩ := exists_sqrt_neg_one p hp h4 v
  set c : ZMod M := (y : ZMod M) with hcdef
  have hcc : c * c = -1 := by
    have h0 : ((y ^ 2 + 1 : ℤ) : ZMod M) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hM]
      push_cast
      exact hy
    push_cast at h0
    linear_combination h0
  have hc : c * c = ((-1 : ℤ) : ZMod M) := by push_cast; exact hcc
  have hc' : (-c) * (-c) = ((-1 : ℤ) : ZMod M) := by rw [neg_mul_neg]; exact hc
  have vanish : ∀ r : {r : ZMod M // r * r = ((-1 : ℤ) : ZMod M)}, Zsqrtd.lift r (Q n) = 0 := by
    intro r
    rw [lift_Q]
    have hr := r.2
    push_cast at hr
    have hfac : ∀ k ∈ range (n + 1), (1 + (k : ZMod M) * r.1) = r.1 * ((k : ZMod M) - r.1) := by
      intro k _
      linear_combination hr
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
    have hasc : ∏ k ∈ range (n + 1), ((k : ZMod M) - r.1) =
        (((-r.1).val.ascFactorial (n + 1) : ℕ) : ZMod M) := by
      rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro k _
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    rw [hasc, (ZMod.natCast_eq_zero_iff _ _).2, mul_zero]
    exact hMdvd.trans ((Nat.factorial_dvd_factorial (Nat.le_succ n)).trans
      (Nat.factorial_dvd_ascFactorial _ _))
  have h1 := vanish ⟨c, hc⟩
  have h2 := vanish ⟨-c, hc'⟩
  rw [Zsqrtd.lift_apply_apply] at h1 h2
  simp only at h1 h2
  have h3 : ((2 * (Q n).im : ℤ) : ZMod M) = 0 := by
    push_cast
    linear_combination (-c) * h1 + c * h2 + (2 * ((Q n).im : ZMod M)) * hcc
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  have hcop : IsCoprime (M : ℤ) 2 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left v ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
  have h5 : (M : ℤ) ∣ (Q n).im := hcop.dvd_of_dvd_mul_left h3
  rw [hM] at h5
  push_cast at h5
  exact h5
