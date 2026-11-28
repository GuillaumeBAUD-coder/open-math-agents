import OMAReductions.R_Erdos18_erdos_18a_R1_H1_R1
import Mathlib

-- BEGIN external module FiniteLaw

/-!
Finite entropy and pushforward infrastructure adapted from Kohlmeyer--Kruer,
Erdos18b.lean, source SHA-256
4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088.
Only the selected elementary infrastructure is ported here; no result about
Erdos 18(b) is being used to assert the new 18(c) conclusion.
-/

open Finset
namespace Erdos18c

noncomputable def finiteEntropy {ι : Type*} (S : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ x ∈ S, Real.negMulLog (p x)

theorem sum_mul_log_le_log_bound {ι : Type*} (S : Finset ι) (p : ι → ℝ) {M : ℝ}
    (hp : ∀ x ∈ S, 0 ≤ p x) (hbound : ∀ x ∈ S, p x ≤ M) :
    (∑ x ∈ S, p x * Real.log (p x)) ≤ (∑ x ∈ S, p x) * Real.log M := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hpx : p x = 0
  · simp [hpx]
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (lt_of_le_of_ne (hp x hx) (Ne.symm hpx)) (hbound x hx)) (hp x hx)

theorem finite_entropy_fiber_defect {ι : Type*} (S : Finset ι) (p : ι → ℝ) {q M : ℝ}
    (hp : ∀ x ∈ S, 0 ≤ p x) (hq : 0 < q) (hM : 0 ≤ M) (hbound : ∀ x ∈ S, p x ≤ M) :
    Real.negMulLog (∑ x ∈ S, p x) + (∑ x ∈ S, p x) * Real.log q - finiteEntropy S p ≤
      q * M - ∑ x ∈ S, p x := by
  let s := ∑ x ∈ S, p x
  have hs : 0 ≤ s := Finset.sum_nonneg hp
  by_cases hMzero : M = 0
  · have hzero : ∀ x ∈ S, p x = 0 := fun x hx => le_antisymm (hMzero ▸ hbound x hx) (hp x hx)
    have hsumzero : ∑ x ∈ S, p x = 0 := Finset.sum_eq_zero hzero
    have hentropy : finiteEntropy S p = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hzero x hx, Real.negMulLog_def]
    simp [hsumzero, hentropy, hMzero, Real.negMulLog_def]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
  have hlog := sum_mul_log_le_log_bound S p hp hbound
  have hentropy : finiteEntropy S p = -(∑ x ∈ S, p x * Real.log (p x)) := by
    simp [finiteEntropy, Real.negMulLog_def, neg_mul, Finset.sum_neg_distrib]
  change Real.negMulLog s + s * Real.log q - finiteEntropy S p ≤ q * M - s
  rw [hentropy]
  change -s * Real.log s + s * Real.log q - -(∑ x ∈ S, p x * Real.log (p x)) ≤ q * M - s
  change (∑ x ∈ S, p x * Real.log (p x)) ≤ s * Real.log M at hlog
  by_cases hszero : s = 0
  · have hlogzero : (∑ x ∈ S, p x * Real.log (p x)) ≤ 0 := by
      simpa only [hszero, zero_mul] using hlog
    simpa only [hszero, neg_zero, zero_mul, zero_add, sub_neg_eq_add, sub_zero] using
      hlogzero.trans (mul_nonneg hq.le hM)
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hszero)
  have hratio := Real.log_le_sub_one_of_pos (div_pos (mul_pos hq hMpos) hspos)
  rw [Real.log_div (mul_ne_zero hq.ne' hMpos.ne') hspos.ne', Real.log_mul hq.ne' hMpos.ne'] at hratio
  have hscaled := mul_le_mul_of_nonneg_left hratio hs
  have hcancel : s * (q * M / s) = q * M := by field_simp
  nlinarith

theorem finite_entropy_le_log_card {ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (hp : ∀ x ∈ S, 0 ≤ p x) (hsum : ∑ x ∈ S, p x = 1) :
    finiteEntropy S p ≤ Real.log (S.card : ℝ) := by
  have hSne : S.Nonempty := by
    by_contra hS
    have he := Finset.not_nonempty_iff_eq_empty.mp hS
    norm_num [he] at hsum
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  have hpoint : ∀ x ∈ S,
      (S.card : ℝ) * Real.negMulLog (p x) ≤
        1 - (S.card : ℝ) * p x + p x * (S.card : ℝ) * Real.log (S.card : ℝ) := by
    intro x hx
    have hh := Real.negMulLog_le_one_sub_self (mul_nonneg hcard.le (hp x hx))
    rw [Real.negMulLog_mul] at hh
    change p x * (-(S.card : ℝ) * Real.log (S.card : ℝ)) +
      (S.card : ℝ) * Real.negMulLog (p x) ≤ 1 - (S.card : ℝ) * p x at hh
    nlinarith
  have htotal := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, one_mul] at htotal
  apply (mul_le_mul_iff_of_pos_left hcard).mp
  simpa only [finiteEntropy, sub_self, zero_add] using htotal

noncomputable def finitePushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (b : κ) : ℝ := ∑ a : ι with π a = b, p a

theorem finite_pushforward_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) : ∑ b : κ, finitePushforward p π b = ∑ a : ι, p a := by
  exact Finset.sum_fiberwise Finset.univ π p

theorem finite_entropy_projection_defect {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (M : κ → ℝ) {q : ℝ}
    (hp : ∀ a, 0 ≤ p a) (hq : 0 < q) (hM : ∀ b, 0 ≤ M b)
    (hbound : ∀ a, p a ≤ M (π a)) :
    finiteEntropy Finset.univ (finitePushforward p π) + (∑ a : ι, p a) * Real.log q -
      finiteEntropy Finset.univ p ≤ q * (∑ b : κ, M b) - ∑ a : ι, p a := by
  have hfiber : ∀ b : κ,
      Real.negMulLog (finitePushforward p π b) + finitePushforward p π b * Real.log q -
        finiteEntropy (Finset.univ.filter (fun a => π a = b)) p ≤ q * M b - finitePushforward p π b := by
    intro b
    apply finite_entropy_fiber_defect _ p (fun a _ => hp a) hq (hM b)
    intro a ha
    have heq := (Finset.mem_filter.mp ha).2
    simpa only [heq] using hbound a
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hfiber b)
  have hentropy : (∑ b : κ, finiteEntropy (Finset.univ.filter (fun a => π a = b)) p) =
      finiteEntropy Finset.univ p := Finset.sum_fiberwise Finset.univ π (fun a => Real.negMulLog (p a))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hentropy, finite_pushforward_sum] at htotal
  exact htotal

theorem finite_pushforward_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (b : κ) :
    0 ≤ finitePushforward p π b := Finset.sum_nonneg (fun a _ => hp a)

theorem le_finite_pushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (a : ι) :
    p a ≤ finitePushforward p π (π a) := by
  exact Finset.single_le_sum (fun b _ => hp b) (by simp)

theorem finite_entropy_mono_projection {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) :
    finiteEntropy Finset.univ (finitePushforward p π) ≤ finiteEntropy Finset.univ p := by
  have hh := finite_entropy_projection_defect p π (finitePushforward p π) hp
    (show (0 : ℝ) < 1 by norm_num) (finite_pushforward_nonneg p π hp) (le_finite_pushforward p π hp)
  simp only [Real.log_one, mul_zero, add_zero, one_mul, finite_pushforward_sum, sub_self] at hh
  linarith

theorem finite_entropy_le_log_support {ι : Type*} [Fintype ι] (p : ι → ℝ) (S : Finset ι)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) (hzero : ∀ a, a ∉ S → p a = 0) :
    finiteEntropy Finset.univ p ≤ Real.log (S.card : ℝ) := by
  classical
  have hsum : ∑ a ∈ S, p a = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hzero a ha)]
    exact hmass
  have hentropy : finiteEntropy S p = finiteEntropy Finset.univ p := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha
    simp [hzero a ha, Real.negMulLog_def]
  rw [← hentropy]
  exact finite_entropy_le_log_card S p (fun a _ => hp a) hsum

theorem finite_pushforward_comp {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [DecidableEq ν] (p : ι → ℝ) (π : ι → κ) (σ : κ → ν) :
    finitePushforward (finitePushforward p π) σ = finitePushforward p (σ ∘ π) := by
  funext b
  unfold finitePushforward
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] using
    Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset ι)
      (Finset.univ.filter (fun a => σ a = b)) π p

theorem finite_entropy_pushforward_le_log_image {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) :
    finiteEntropy Finset.univ (finitePushforward p π) ≤
      Real.log ((Finset.univ.image π).card : ℝ) := by
  classical
  apply finite_entropy_le_log_support (finitePushforward p π) (Finset.univ.image π)
    (finite_pushforward_nonneg p π hp) (by rw [finite_pushforward_sum, hmass])
  intro b hb
  have he : Finset.univ.filter (fun a => π a = b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩)
  simp only [finitePushforward, he, Finset.sum_empty]

def dyadicIndex (k n : ℕ) : Fin (2 ^ k) := ⟨n % 2 ^ k, Nat.mod_lt n (by positivity)⟩

noncomputable def dyadicDistribution {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (k : ℕ) :
    Fin (2 ^ k) → ℝ := finitePushforward p (fun a => dyadicIndex k (f a))

noncomputable def dyadicEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (k : ℕ) : ℝ :=
  finiteEntropy Finset.univ (dyadicDistribution p f k)

theorem dyadic_distribution_project {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    {u v : ℕ} (huv : u ≤ v) :
    finitePushforward (dyadicDistribution p f v) (fun a => dyadicIndex u a.val) = dyadicDistribution p f u := by
  rw [dyadicDistribution, finite_pushforward_comp]
  unfold dyadicDistribution
  congr 1
  funext a
  apply Fin.ext
  exact Nat.mod_mod_of_dvd (f a) (pow_dvd_pow 2 huv)

theorem weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hmass : ∑ i ∈ S, w i = 1) :
    (∑ i ∈ S, w i * t i) ^ 2 ≤ ∑ i ∈ S, w i * (t i) ^ 2 := by
  have hleft : (∑ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * t i)) = ∑ i ∈ S, w i * t i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have hfirst : (∑ i ∈ S, (Real.sqrt (w i)) ^ 2) = 1 := by
    calc
      _ = ∑ i ∈ S, w i := Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi))
      _ = _ := hmass
  have hsecond : (∑ i ∈ S, (Real.sqrt (w i) * t i) ^ 2) = ∑ i ∈ S, w i * (t i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * t i)
  rwa [hleft, hfirst, hsecond, one_mul] at hh


end Erdos18c
-- END external module FiniteLaw

-- BEGIN external module BinaryEntropy

/-
Binary entropy estimates used in the harmonic-shift proof.  Finite-law
infrastructure is credited in FiniteLaw.lean; these analytic inequalities
are the scalar steps of the new manuscript.
-/

open Finset
namespace Erdos18c

theorem negMulLog_le_sqrt {p : ℝ} (hp : 0 ≤ p) :
    Real.negMulLog p ≤ (2 / Real.exp 1) * Real.sqrt p := by
  by_cases hp0 : p = 0
  · simp [hp0, Real.negMulLog_def]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  let t := -(Real.log p) / 2
  have he : Real.exp (-t) = Real.sqrt p := by
    apply (Real.log_injOn_pos (Real.exp_pos _) (Real.sqrt_pos.2 hp'))
    rw [Real.log_exp, Real.log_sqrt hp]
    dsimp [t]
    ring
  have hh := Real.mul_exp_neg_le_exp_neg_one t
  have ht : Real.negMulLog p = 2 * Real.sqrt p * (t * Real.exp (-t)) := by
    rw [he]
    dsimp [t]
    rw [Real.negMulLog_def]
    change -p * Real.log p = _
    calc
      -p * Real.log p = -(Real.sqrt p ^ 2) * Real.log p := by rw [Real.sq_sqrt hp]
      _ = _ := by ring
  rw [ht]
  have hscaled := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * Real.sqrt p)
  simpa only [Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled

theorem binEntropy_le_two_sqrt_min {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ≤ 2 * Real.sqrt (min p (1-p)) := by
  wlog hhalf : p ≤ 1 / 2 generalizing p
  · have h := this (sub_nonneg.mpr hp1) (by linarith : 1-p ≤ 1) (by linarith : 1-p ≤ 1/2)
    simpa [Real.binEntropy_one_sub, min_comm] using h
  have hmin : min p (1-p) = p := min_eq_left (by linarith)
  rw [hmin, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hfirst := negMulLog_le_sqrt hp
  have hsecond : Real.negMulLog (1-p) ≤ p := by
    have := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr hp1)
    linarith
  have hroot : p ≤ Real.sqrt p := by
    have hs := Real.sq_sqrt hp
    have hsn := Real.sqrt_nonneg p
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hp1)]
  have hexp : 2 / Real.exp 1 ≤ 1 := (div_le_one (Real.exp_pos _)).mpr (le_of_lt Real.exp_one_gt_two)
  have hh := mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg p)
  linarith

theorem two_min_le_binEntropy {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    2 * min p (1-p) * Real.log 2 ≤ Real.binEntropy p := by
  wlog hhalf : p ≤ 1 / 2 generalizing p
  · have h := this (sub_nonneg.mpr hp1) (by linarith : 1-p ≤ 1) (by linarith : 1-p ≤ 1/2)
    simpa [Real.binEntropy_one_sub, min_comm] using h
  have hconc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (2:ℝ)⁻¹ ∈ Set.Icc 0 1 by norm_num)
    (show 0 ≤ 1 - 2*p by linarith)
    (show 0 ≤ 2*p by linarith)
    (show (1-2*p) + 2*p = 1 by ring)
  norm_num only [smul_eq_mul, mul_zero, zero_add, Real.binEntropy_zero, mul_zero,
    zero_add, Real.binEntropy_two_inv] at hconc
  have hhalfentropy : Real.binEntropy (1/2) = Real.log 2 := by
    convert Real.binEntropy_two_inv using 1
    norm_num
  rw [hhalfentropy] at hconc
  have harg : (2*p)*(1/2) = p := by ring
  rw [harg] at hconc
  rw [min_eq_left (by linarith : p ≤ 1-p)]
  exact hconc

noncomputable def pairEntropy (x y : ℝ) : ℝ :=
  Real.negMulLog x + Real.negMulLog y - Real.negMulLog (x+y)

theorem pairEntropy_eq (x y : ℝ) :
    pairEntropy x y = (x+y) * Real.binEntropy (x/(x+y)) := by
  by_cases hs : x+y = 0
  · have hy : y = -x := by linarith
    simp [pairEntropy, hy, Real.negMulLog_def, Real.log_neg_eq_log]
  have hxid := Real.negMulLog_mul (x+y) (x/(x+y))
  have hyid := Real.negMulLog_mul (x+y) (y/(x+y))
  rw [mul_div_cancel₀ _ hs] at hxid hyid
  have hratio : 1-x/(x+y) = y/(x+y) := by field_simp; ring
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hratio, mul_add]
  unfold pairEntropy
  have hsum : x/(x+y) + y/(x+y) = 1 := by field_simp
  have hsum' := congrArg (fun t : ℝ => t * Real.negMulLog (x+y)) hsum
  nlinarith

theorem binary_probability_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x/(x+y) ∧ x/(x+y) ≤ 1 := by
  constructor
  · positivity
  · by_cases hs : x+y=0
    · simp [hs]
    · exact (div_le_one (lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs))).mpr (by linarith)

theorem mass_mul_min_probability {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x+y) * min (x/(x+y)) (1-x/(x+y)) = min x y := by
  by_cases hs : x+y=0
  · have hx0 : x=0 := by linarith
    have hy0 : y=0 := by linarith
    simp [hx0,hy0]
  have hsp : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs)
  have hratio : 1-x/(x+y)=y/(x+y) := by field_simp; ring
  rw [hratio]
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, min_eq_left ((div_le_div_iff_of_pos_right hsp).mpr hxy)]
    exact mul_div_cancel₀ _ hs
  · have hyx := le_of_not_ge hxy
    rw [min_eq_right hyx, min_eq_right ((div_le_div_iff_of_pos_right hsp).mpr hyx)]
    exact mul_div_cancel₀ _ hs

theorem pairEntropy_lower {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * min x y * Real.log 2 ≤ pairEntropy x y := by
  rw [pairEntropy_eq]
  have hp := binary_probability_bounds hx hy
  have hh := mul_le_mul_of_nonneg_left (two_min_le_binEntropy hp.1 hp.2) (add_nonneg hx hy)
  calc
    2 * min x y * Real.log 2 = (x+y) * (2 * min (x/(x+y)) (1-x/(x+y)) * Real.log 2) := by
      rw [← mass_mul_min_probability hx hy]
      ring
    _ ≤ _ := hh

theorem binary_entropy_sq_bound {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ^ 2 ≤ 4 * min p (1-p) := by
  have hh := pow_le_pow_left₀ (Real.binEntropy_nonneg hp hp1)
    (binEntropy_le_two_sqrt_min hp hp1) 2
  have hm : 0 ≤ min p (1-p) := le_min hp (sub_nonneg.mpr hp1)
  nlinarith [Real.sq_sqrt hm]

theorem sum_pairEntropy_sq_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hmass : ∑ i, (x i+y i) = 1) :
    (∑ i, pairEntropy (x i) (y i)) ^ 2 ≤ 4 * ∑ i, min (x i) (y i) := by
  have hcs := weighted_sum_sq_le univ (fun i => x i+y i)
    (fun i => Real.binEntropy (x i/(x i+y i))) (fun i _ => add_nonneg (hx i) (hy i)) hmass
  simp_rw [← pairEntropy_eq] at hcs
  apply hcs.trans
  calc
    (∑ i, (x i+y i) * Real.binEntropy (x i/(x i+y i)) ^ 2) ≤
        ∑ i, (x i+y i) * (4 * min (x i/(x i+y i)) (1-x i/(x i+y i))) := by
      apply sum_le_sum
      intro i _
      have hp := binary_probability_bounds (hx i) (hy i)
      exact mul_le_mul_of_nonneg_left (binary_entropy_sq_bound hp.1 hp.2) (add_nonneg (hx i) (hy i))
    _ = 4 * ∑ i, min (x i) (y i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [← mass_mul_min_probability (hx i) (hy i)]
      ring

theorem sum_pairEntropy_lower {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    (2 * ∑ i, min (x i) (y i)) * Real.log 2 ≤ ∑ i, pairEntropy (x i) (y i) := by
  have hh := sum_le_sum (fun i (_ : i ∈ univ) => pairEntropy_lower (hx i) (hy i))
  simpa only [← sum_mul, ← mul_sum] using hh


end Erdos18c
-- END external module BinaryEntropy

-- BEGIN external module EntropyEstimates

/-
Finite numerical estimates used by the proposed entropy argument.
These do not yet formalize the chain rule for random variables or the
conditioning/carry argument, and do not prove the full covering lemma.
-/

open Finset

namespace Erdos18c

theorem sum_squares_control {ι : Type*} (S : Finset ι) (h u : ι → ℝ)
    (hhu : ∀ i ∈ S, h i ^ 2 ≤ 2 * u i) :
    (∑ i ∈ S, h i) ^ 2 ≤ 2 * (S.card : ℝ) * ∑ i ∈ S, u i := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S h (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    (∑ i ∈ S, h i) ^ 2 ≤ (∑ i ∈ S, h i ^ 2) * (S.card : ℝ) := hcs
    _ ≤ (∑ i ∈ S, 2 * u i) * (S.card : ℝ) :=
      mul_le_mul_of_nonneg_right (Finset.sum_le_sum hhu) (Nat.cast_nonneg _)
    _ = 2 * (S.card : ℝ) * ∑ i ∈ S, u i := by
      rw [← Finset.mul_sum]
      ring

theorem minority_mass_lower {ι : Type*} (S : Finset ι) (h u : ι → ℝ) (a : ℝ)
    (hcard : 0 < S.card) (ha : 0 ≤ a)
    (hhu : ∀ i ∈ S, h i ^ 2 ≤ 2 * u i)
    (hbudget : a * S.card ≤ ∑ i ∈ S, h i) :
    a ^ 2 * S.card / 2 ≤ ∑ i ∈ S, u i := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hcard
  have hsum0 : 0 ≤ ∑ i ∈ S, h i := le_trans (mul_nonneg ha hn.le) hbudget
  have hsquare : (a * S.card) ^ 2 ≤ (∑ i ∈ S, h i) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha hn.le) hbudget 2
  have hcs := sum_squares_control S h u hhu
  have hdivide : (S.card : ℝ) * (a ^ 2 * S.card) ≤
      (S.card : ℝ) * (2 * ∑ i ∈ S, u i) := by nlinarith
  have hcancel := le_of_mul_le_mul_left hdivide hn
  linarith

theorem weighted_reciprocal_lower {ι : Type*} (S : Finset ι)
    (u d : ι → ℝ) (D H c : ℝ)
    (hD : 0 < D) (hH : 0 < H)
    (hu : ∀ i ∈ S, 0 ≤ u i)
    (hd : ∀ i ∈ S, 0 < d i ∧ d i ≤ D)
    (hmass : c * D ≤ ∑ i ∈ S, u i) :
    c / H ≤ (∑ i ∈ S, u i / d i) / H := by
  have hsum : (∑ i ∈ S, u i) / D ≤ ∑ i ∈ S, u i / d i := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    apply (div_le_div_iff₀ hD (hd i hi).1).mpr
    exact mul_le_mul_of_nonneg_left (hd i hi).2 (hu i hi)
  have hc : c ≤ (∑ i ∈ S, u i) / D := (le_div_iff₀ hD).mpr hmass
  exact div_le_div_of_nonneg_right (hc.trans hsum) hH.le

theorem harmonic_kernel_lower (j : ℕ) (u : ℕ → ℝ) (H c : ℝ)
    (hH : 0 < H)
    (hu : ∀ i ≤ j, 0 ≤ u i)
    (hmass : c * (j + 1 : ℕ) ≤ ∑ i ∈ Finset.range (j + 1), u i) :
    c / H ≤
      (∑ i ∈ Finset.range (j + 1), u i / (j + 1 - i : ℕ)) / H := by
  apply weighted_reciprocal_lower (Finset.range (j + 1)) u
    (fun i => (j + 1 - i : ℕ)) (j + 1 : ℕ) H c
  · positivity
  · exact hH
  · intro i hi
    exact hu i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  · intro i hi
    have hi' : i < j + 1 := Finset.mem_range.mp hi
    constructor
    · exact_mod_cast (show 0 < j + 1 - i by omega)
    · exact_mod_cast (show j + 1 - i ≤ j + 1 by omega)
  · exact hmass


end Erdos18c
-- END external module EntropyEstimates

-- BEGIN external module DyadicEntropy

/- Entropy increments for finite lower-bit projections. -/

open Finset
namespace Erdos18c
noncomputable section

def dyadicSplitEquiv (j : ℕ) : Fin (2^j) ⊕ Fin (2^j) ≃ Fin (2^(j+1)) :=
  finSumFinEquiv.trans (finCongr (by omega : 2^j+2^j = 2^(j+1)))

def dyadicLower (j : ℕ) (i : Fin (2^j)) : Fin (2^(j+1)) := dyadicSplitEquiv j (.inl i)
def dyadicUpper (j : ℕ) (i : Fin (2^j)) : Fin (2^(j+1)) := dyadicSplitEquiv j (.inr i)

@[simp] theorem dyadicLower_val (j : ℕ) (i : Fin (2^j)) : (dyadicLower j i).val = i.val := rfl
@[simp] theorem dyadicUpper_val (j : ℕ) (i : Fin (2^j)) : (dyadicUpper j i).val = 2^j+i.val := rfl

theorem dyadic_split_sum (j : ℕ) (F : Fin (2^(j+1)) → ℝ) :
    ∑ z, F z = ∑ i, (F (dyadicLower j i) + F (dyadicUpper j i)) := by
  have h := Fintype.sum_equiv (dyadicSplitEquiv j)
    (fun z => F (dyadicSplitEquiv j z)) F (fun _ => rfl)
  simpa only [Fintype.sum_sum_type, dyadicLower, dyadicUpper, sum_add_distrib] using h.symm

@[simp] theorem dyadicLower_mod (j : ℕ) (i : Fin (2^j)) :
    dyadicIndex j (dyadicLower j i).val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

@[simp] theorem dyadicUpper_mod (j : ℕ) (i : Fin (2^j)) :
    dyadicIndex j (dyadicUpper j i).val = i := by
  apply Fin.ext
  simp [dyadicIndex, Nat.mod_eq_of_lt i.isLt]

theorem dyadic_parent_mass (j : ℕ) (p : Fin (2^(j+1)) → ℝ) (i : Fin (2^j)) :
    finitePushforward p (fun z => dyadicIndex j z.val) i =
      p (dyadicLower j i) + p (dyadicUpper j i) := by
  unfold finitePushforward
  rw [sum_filter, dyadic_split_sum]
  simp only [dyadicLower_mod, dyadicUpper_mod]
  rw [sum_add_distrib]
  simp

theorem dyadic_entropy_increment (j : ℕ) (p : Fin (2^(j+1)) → ℝ) :
    finiteEntropy univ p - finiteEntropy univ
      (finitePushforward p (fun z => dyadicIndex j z.val)) =
      ∑ i, pairEntropy (p (dyadicLower j i)) (p (dyadicUpper j i)) := by
  unfold finiteEntropy
  rw [dyadic_split_sum]
  simp_rw [dyadic_parent_mass]
  simp only [pairEntropy, sum_sub_distrib, sum_add_distrib]

theorem dyadic_entropy_zero {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hmass : ∑ a, p a = 1) : dyadicEntropy p f 0 = 0 := by
  have hi : ∀ a : ι, dyadicIndex 0 (f a) = (0 : Fin (2^0)) := by
    intro a
    apply Fin.ext
    simp [dyadicIndex]
  have hv : dyadicDistribution p f 0 0 = 1 := by
    simpa only [dyadicDistribution, finitePushforward, hi, filter_true] using hmass
  unfold dyadicEntropy finiteEntropy
  have hh : ∀ r : Fin (2^0), r=0 := by
    intro r
    apply Fin.ext
    have hr := r.isLt
    norm_num at hr
    omega
  simp_rw [hh, hv]
  simp [Real.negMulLog_def]

def dyadicMinority {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) : ℝ :=
  2 * ∑ i, min (dyadicDistribution p f (j+1) (dyadicLower j i))
    (dyadicDistribution p f (j+1) (dyadicUpper j i))

def dyadicBitBias {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) : ℝ :=
  ∑ i, |dyadicDistribution p f (j+1) (dyadicLower j i) -
    dyadicDistribution p f (j+1) (dyadicUpper j i)|

theorem dyadic_entropy_step_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) :
    dyadicEntropy p f (j+1) - dyadicEntropy p f j =
      ∑ i, pairEntropy (dyadicDistribution p f (j+1) (dyadicLower j i))
        (dyadicDistribution p f (j+1) (dyadicUpper j i)) := by
  have hh := dyadic_entropy_increment j (dyadicDistribution p f (j+1))
  rw [dyadic_distribution_project p f (Nat.le_succ j)] at hh
  exact hh

theorem dyadic_entropy_step_sq {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (j : ℕ) :
    (dyadicEntropy p f (j+1) - dyadicEntropy p f j)^2 ≤ 2 * dyadicMinority p f j := by
  rw [dyadic_entropy_step_eq]
  have hn := finite_pushforward_nonneg p (fun a => dyadicIndex (j+1) (f a)) hp
  have hs : ∑ i, (dyadicDistribution p f (j+1) (dyadicLower j i) +
      dyadicDistribution p f (j+1) (dyadicUpper j i)) = 1 := by
    rw [← dyadic_split_sum, dyadicDistribution, finite_pushforward_sum, hmass]
  have hh := sum_pairEntropy_sq_le _ _ (fun i => hn _) (fun i => hn _) hs
  convert hh using 1 <;> simp only [dyadicMinority, dyadicDistribution]
  ring

theorem dyadic_entropy_step_lower {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (j : ℕ) :
    dyadicMinority p f j * Real.log 2 ≤ dyadicEntropy p f (j+1) - dyadicEntropy p f j := by
  rw [dyadic_entropy_step_eq]
  exact sum_pairEntropy_lower _ _
    (fun i => finite_pushforward_nonneg p _ hp _) (fun i => finite_pushforward_nonneg p _ hp _)

theorem dyadic_entropy_telescope {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hmass : ∑ a, p a = 1) (L : ℕ) :
    ∑ j ∈ range L, (dyadicEntropy p f (j+1) - dyadicEntropy p f j) = dyadicEntropy p f L := by
  induction L with
  | zero => simp [dyadic_entropy_zero p f hmass]
  | succ L ih => rw [sum_range_succ, ih]; ring

theorem dyadic_prefix_minority {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (L : ℕ) (hL : 0<L)
    (g : ℝ) (hg : 0 ≤ g)
    (hbudget : g * L * Real.log 2 ≤ dyadicEntropy p f L) :
    g^2 * (Real.log 2)^2 / 2 * L ≤ ∑ j ∈ range L, dyadicMinority p f j := by
  have hh := minority_mass_lower (range L)
    (fun j => dyadicEntropy p f (j+1) - dyadicEntropy p f j)
    (dyadicMinority p f) (g*Real.log 2) (by simpa using hL)
    (mul_nonneg hg (Real.log_nonneg (by norm_num)))
    (fun j _ => dyadic_entropy_step_sq p f hp hmass j)
    (by rw [dyadic_entropy_telescope p f hmass]; simpa only [card_range, mul_assoc, mul_left_comm, mul_comm] using hbudget)
  convert hh using 1
  simp only [card_range]
  ring

end
end Erdos18c
-- END external module DyadicEntropy

-- BEGIN external module FiniteConvolution

/-
Finite real convolution estimates. The summation/reindexing arguments adapt
the finite convolution infrastructure of the credited Kohlmeyer--Kruer 18(b)
source. The involution-bias contraction is used for the new dyadic mixing step.
-/

open Finset
namespace Erdos18c

noncomputable section
variable {G H : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]

def realConvolution (f g : G → ℝ) (x : G) : ℝ := ∑ y, f y * g (x-y)
def realShift (h : G) (f : G → ℝ) (x : G) : ℝ := f (x+h)
def realDifference (h : G) (f : G → ℝ) (x : G) : ℝ := f x - f (x+h)
def finiteL1 (f : G → ℝ) : ℝ := ∑ x, |f x|
def involutionBias (h : G) (f : G → ℝ) : ℝ := finiteL1 (realDifference h f) / 2

omit [AddCommGroup G] [DecidableEq G] in
theorem finiteL1_nonneg (f : G → ℝ) : 0 ≤ finiteL1 f :=
  sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq G] in
theorem finiteL1_shift (h : G) (f : G → ℝ) : finiteL1 (realShift h f) = finiteL1 f := by
  exact Fintype.sum_equiv (Equiv.addRight h) _ _ (fun _ => rfl)

omit [DecidableEq G] in
theorem sum_realConvolution (f g : G → ℝ) :
    ∑ x, realConvolution f g x = (∑ x, f x) * (∑ x, g x) := by
  simp only [realConvolution]
  rw [sum_comm]
  calc
    (∑ y, ∑ x, f y * g (x-y)) = ∑ y, f y * ∑ x, g x := by
      apply sum_congr rfl
      intro y _
      rw [← mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
    _ = _ := (sum_mul _ _ _).symm

omit [DecidableEq G] in
theorem realConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (x : G) :
    0 ≤ realConvolution f g x := sum_nonneg (fun y _ => mul_nonneg (hf y) (hg _))

omit [DecidableEq G] in
theorem finiteL1_convolution_le (f g : G → ℝ) :
    finiteL1 (realConvolution f g) ≤ finiteL1 f * finiteL1 g := by
  calc
    _ ≤ ∑ x, ∑ y, |f y| * |g (x-y)| := by
      apply sum_le_sum
      intro x _
      simpa only [realConvolution, abs_mul] using abs_sum_le_sum_abs (s := univ) (f := fun y => f y * g (x-y))
    _ = ∑ y, |f y| * ∑ x, |g x| := by
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      rw [← mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
    _ = _ := (sum_mul _ _ _).symm

omit [DecidableEq G] in
theorem convolution_shift_right (h : G) (f g : G → ℝ) :
    realConvolution f (realShift h g) = realShift h (realConvolution f g) := by
  funext x
  apply sum_congr rfl
  intro y _
  dsimp [realShift]
  congr 2
  abel

omit [DecidableEq G] in
theorem convolution_shift_left (h : G) (f g : G → ℝ) :
    realConvolution (realShift h f) g = realShift h (realConvolution f g) := by
  funext x
  refine Fintype.sum_equiv (Equiv.addRight h) _ _ ?_
  intro y
  dsimp [realShift]
  congr 2
  abel

omit [DecidableEq G] in
theorem convolution_difference_right (h : G) (f g : G → ℝ) :
    realConvolution f (realDifference h g) = realDifference h (realConvolution f g) := by
  funext x
  have hh := congrFun (convolution_shift_right h f g) x
  simpa only [realConvolution, realDifference, mul_sub, sum_sub_distrib,
    realShift] using congrArg (fun z => realConvolution f g x - z) hh

omit [DecidableEq G] in
theorem convolution_difference_left (h : G) (f g : G → ℝ) :
    realConvolution (realDifference h f) g = realDifference h (realConvolution f g) := by
  funext x
  have hh := congrFun (convolution_shift_left h f g) x
  simpa only [realConvolution, realDifference, sub_mul, sum_sub_distrib,
    realShift] using congrArg (fun z => realConvolution f g x - z) hh

theorem convolution_double_difference (h : G) (hh : h+h=0) (f g : G → ℝ) (x : G) :
    realConvolution (realDifference h f) (realDifference h g) x =
      2 * realDifference h (realConvolution f g) x := by
  rw [convolution_difference_left, convolution_difference_right]
  simp only [realDifference, add_assoc, hh, add_zero]
  ring

omit [DecidableEq G] in
theorem involutionBias_nonneg (h : G) (f : G → ℝ) : 0 ≤ involutionBias h f :=
  div_nonneg (finiteL1_nonneg _) (by norm_num)

omit [DecidableEq G] in
theorem involutionBias_le_l1 (h : G) (f : G → ℝ) : involutionBias h f ≤ finiteL1 f := by
  have hb : finiteL1 (realDifference h f) ≤ finiteL1 f + finiteL1 (realShift h f) := by
    calc
      _ ≤ ∑ x, (|f x| + |f (x+h)|) := sum_le_sum (fun x _ => abs_sub _ _)
      _ = _ := sum_add_distrib
  rw [finiteL1_shift] at hb
  unfold involutionBias
  linarith

theorem involutionBias_convolution_le (h : G) (hh : h+h=0) (f g : G → ℝ) :
    involutionBias h (realConvolution f g) ≤ involutionBias h f * involutionBias h g := by
  have hb := finiteL1_convolution_le (realDifference h f) (realDifference h g)
  have he : finiteL1 (realConvolution (realDifference h f) (realDifference h g)) =
      2 * finiteL1 (realDifference h (realConvolution f g)) := by
    simp only [finiteL1, convolution_double_difference h hh, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [mul_sum]
  rw [he] at hb
  unfold involutionBias
  nlinarith

def realConvolutionPow (f : G → ℝ) : ℕ → G → ℝ
  | 0 => fun x => if x=0 then 1 else 0
  | r+1 => realConvolution f (realConvolutionPow f r)

theorem involutionBias_convolutionPow_le (h : G) (hh : h+h=0) (f : G → ℝ) (r : ℕ) :
    involutionBias h (realConvolutionPow f r) ≤ involutionBias h f ^ r := by
  induction r with
  | zero =>
    have hb := involutionBias_le_l1 h (realConvolutionPow f 0)
    have hd : finiteL1 (realConvolutionPow f 0) = 1 := by
      calc
        _ = ∑ x : G, if x=0 then (1:ℝ) else 0 := by
          apply sum_congr rfl
          intro x _
          by_cases hx : x=0 <;> simp [realConvolutionPow,hx]
        _ = 1 := by simp
    simpa only [hd, pow_zero] using hb
  | succ r ih =>
    calc
      _ ≤ involutionBias h f * involutionBias h (realConvolutionPow f r) :=
        involutionBias_convolution_le h hh _ _
      _ ≤ involutionBias h f * involutionBias h f ^ r :=
        mul_le_mul_of_nonneg_left ih (involutionBias_nonneg _ _)
      _ = _ := by rw [pow_succ]; ring

theorem realConvolutionPow_probability {f : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsum : ∑ x, f x = 1) (r : ℕ) :
    (∀ x, 0 ≤ realConvolutionPow f r x) ∧ ∑ x, realConvolutionPow f r x = 1 := by
  induction r with
  | zero => simp [realConvolutionPow]; intro x; split_ifs <;> norm_num
  | succ r ih => exact ⟨realConvolution_nonneg hf ih.1, by rw [realConvolutionPow, sum_realConvolution, hsum, ih.2, one_mul]⟩

theorem sum_test_pushforward {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (T : ι → κ) (h : κ → ℝ) :
    (∑ b, h b * finitePushforward p T b) = ∑ a, h (T a) * p a := by
  simp only [finitePushforward, mul_sum, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [mul_ite, mul_zero]
  simp

omit [DecidableEq G] in
theorem sum_test_realConvolution (f g h : G → ℝ) :
    (∑ a, h a * realConvolution f g a) = ∑ x, ∑ y, h (x+y) * f x * g y := by
  simp only [realConvolution, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ ?_
  intro z
  simp only [Equiv.subRight_apply]
  have he : x+(z-x)=z := by abel
  rw [he]
  ring

theorem convolution_pushforward_left {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (T : ι → G) (g : G → ℝ) (a : G) :
    realConvolution (finitePushforward p T) g a = ∑ x, p x * g (a-T x) := by
  simpa only [realConvolution, mul_comm] using sum_test_pushforward p T (fun b => g (a-b))

omit [DecidableEq G] in
theorem pushforward_realConvolution (f g : G → ℝ) (T : G →+ H) :
    finitePushforward (realConvolution f g) T =
      realConvolution (finitePushforward f T) (finitePushforward g T) := by
  funext a
  calc
    _ = ∑ z : G, (if T z=a then (1:ℝ) else 0) * realConvolution f g z := by
      simp only [finitePushforward, sum_filter, ite_mul, one_mul, zero_mul]
    _ = ∑ x : G, ∑ y : G, (if T (x+y)=a then (1:ℝ) else 0) * f x * g y :=
      sum_test_realConvolution f g _
    _ = ∑ x : G, f x * finitePushforward g T (a-T x) := by
      apply sum_congr rfl
      intro x _
      simp only [finitePushforward, sum_filter, mul_sum]
      apply sum_congr rfl
      intro y _
      rw [map_add]
      by_cases hy : T y = a-T x
      · simp [hy]
      · have hxy : T x+T y ≠ a := by
          intro heq
          exact hy ((eq_sub_iff_add_eq').mpr heq)
        simp [hy,hxy]
    _ = _ := (convolution_pushforward_left f T _ a).symm

theorem pushforward_realConvolutionPow (f : G → ℝ) (T : G →+ H) (r : ℕ) :
    finitePushforward (realConvolutionPow f r) T =
      realConvolutionPow (finitePushforward f T) r := by
  induction r with
  | zero =>
    funext a
    simp only [realConvolutionPow, finitePushforward, sum_filter]
    have he (x : G) : (if T x=a then (if x=0 then (1:ℝ) else 0) else 0) =
        if x=0 then (if a=0 then 1 else 0) else 0 := by
      by_cases hx : x=0
      · subst x; simp [eq_comm]
      · simp [hx]
    simp_rw [he]
    simp
  | succ r ih => rw [realConvolutionPow, pushforward_realConvolution, ih, realConvolutionPow]

omit [DecidableEq G] [Fintype H] in
theorem pushforward_shift (f : G → ℝ) (T : G →+ H) (h : G) :
    finitePushforward (realShift h f) T = realShift (T h) (finitePushforward f T) := by
  funext b
  simp only [finitePushforward, realShift, sum_filter]
  refine Fintype.sum_equiv (Equiv.addRight h) _ _ ?_
  intro a
  simp [map_add]

omit [DecidableEq G] [Fintype H] in
theorem pushforward_difference (f : G → ℝ) (T : G →+ H) (h : G) :
    finitePushforward (realDifference h f) T = realDifference (T h) (finitePushforward f T) := by
  have he : finitePushforward (realDifference h f) T =
      fun b => finitePushforward f T b - finitePushforward (realShift h f) T b := by
    funext b
    simp only [finitePushforward, realDifference, realShift, sum_sub_distrib]
  rw [he, pushforward_shift]
  rfl

omit [AddCommGroup G] [AddCommGroup H] in
theorem finiteL1_pushforward_injective (f : G → ℝ) (T : G → H) (hT : Function.Injective T) :
    finiteL1 (finitePushforward f T) = finiteL1 f := by
  have he (b : H) : |finitePushforward f T b| = finitePushforward (fun a => |f a|) T b := by
    by_cases hx : ∃ a, T a=b
    · obtain ⟨a,rfl⟩ := hx
      simp [finitePushforward, hT.eq_iff, sum_filter]
    · have hn (a : G) : T a ≠ b := fun ha => hx ⟨a,ha⟩
      simp [finitePushforward, hn]
  unfold finiteL1
  simp_rw [he]
  exact finite_pushforward_sum _ _

theorem involutionBias_pushforward (f : G → ℝ) (T : G →+ H)
    (hT : Function.Injective T) (h : G) :
    involutionBias (T h) (finitePushforward f T) = involutionBias h f := by
  unfold involutionBias
  rw [← pushforward_difference, finiteL1_pushforward_injective _ T hT]

def finiteMixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (F : ι → G → ℝ) (x : G) : ℝ :=
  ∑ i, w i * F i x

omit [AddCommGroup G] [DecidableEq G] in
theorem sum_finiteMixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (F : ι → G → ℝ) :
    ∑ x, finiteMixture w F x = ∑ i, w i * ∑ x, F i x := by
  simp only [finiteMixture]
  rw [sum_comm]
  simp only [mul_sum]

omit [Fintype G] [AddCommGroup G] [DecidableEq G] in
theorem finiteMixture_nonneg {ι : Type*} [Fintype ι] (w : ι → ℝ) (F : ι → G → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hF : ∀ i x, 0 ≤ F i x) (x : G) : 0 ≤ finiteMixture w F x :=
  sum_nonneg fun i _ => mul_nonneg (hw i) (hF i x)

omit [AddCommGroup G] [DecidableEq G] [Fintype H] [AddCommGroup H] in
theorem pushforward_finiteMixture {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → G → ℝ) (T : G → H) :
    finitePushforward (finiteMixture w F) T = finiteMixture w (fun i => finitePushforward (F i) T) := by
  funext b
  unfold finitePushforward finiteMixture
  rw [sum_comm]
  simp only [mul_sum]

omit [DecidableEq G] in
theorem involutionBias_finiteMixture {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → G → ℝ) (hw : ∀ i, 0 ≤ w i) (h : G) :
    involutionBias h (finiteMixture w F) ≤ ∑ i, w i * involutionBias h (F i) := by
  have hinner (x : G) : realDifference h (finiteMixture w F) x =
      ∑ i, w i * realDifference h (F i) x := by
    simp only [finiteMixture, realDifference, mul_sub, sum_sub_distrib]
  have hb : finiteL1 (realDifference h (finiteMixture w F)) ≤
      ∑ i, w i * finiteL1 (realDifference h (F i)) := by
    unfold finiteL1
    simp_rw [hinner]
    calc
      _ ≤ ∑ x, ∑ i, |w i * realDifference h (F i) x| :=
        sum_le_sum fun x _ => abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [sum_comm]
        simp only [abs_mul, abs_of_nonneg (hw _), mul_sum]
  unfold involutionBias
  simp_rw [← mul_div_assoc]
  rw [← sum_div]
  exact div_le_div_of_nonneg_right hb (by norm_num)

theorem twice_card_cover (B : Finset G) (hcard : Fintype.card G < 2*B.card) (x : G) :
    ∃ a∈B, ∃ b∈B, a+b=x := by
  by_contra hn
  have hd : Disjoint B (B.image (fun b => x-b)) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨b,hb,he⟩ := mem_image.mp hb
    exact hn ⟨a,ha,b,hb,by rw [← he]; abel⟩
  have hc := card_le_card (subset_univ (B ∪ B.image (fun b => x-b)))
  rw [card_union_of_disjoint hd, card_image_of_injective B (fun a b h => by
    rw [sub_eq_add_neg,sub_eq_add_neg] at h
    exact neg_injective (add_left_cancel h))] at hc
  simp only [card_univ] at hc
  omega

theorem convolutionPow_support (f : G → ℝ) (r : ℕ) (x : G)
    (hx : realConvolutionPow f r x ≠ 0) :
    ∃ L : List G, L.length=r ∧ (∀ a∈L, f a≠0) ∧ L.sum=x := by
  induction r generalizing x with
  | zero =>
    have hx0 : x=0 := by by_contra h; simp [realConvolutionPow,h] at hx
    subst x
    exact ⟨[],rfl,by simp,by simp⟩
  | succ r ih =>
    obtain ⟨a,_,ha⟩ := exists_ne_zero_of_sum_ne_zero hx
    have han : f a ≠ 0 := (mul_ne_zero_iff.mp ha).1
    have htail : realConvolutionPow f r (x-a)≠0 := (mul_ne_zero_iff.mp ha).2
    obtain ⟨L,hL,hf,hs⟩ := ih (x-a) htail
    refine ⟨a::L,by simp [hL],?_,by simp [hs]⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact han
    · exact hf b hb

end
end Erdos18c
-- END external module FiniteConvolution

-- BEGIN external module DyadicConvolution

open Finset
namespace Erdos18c
noncomputable section

def dyadicProject {u v : ℕ} (h : u ≤ v) : Fin (2^v) →+ Fin (2^u) where
  toFun x := dyadicIndex u x.val
  map_zero' := by apply Fin.ext; simp [dyadicIndex]
  map_add' x y := by
    apply Fin.ext
    change (x.val+y.val) % 2^v % 2^u = (x.val%2^u+y.val%2^u)%2^u
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 h)]
    exact Nat.add_mod _ _ _

def dyadicHalf (j : ℕ) : Fin (2^(j+1)) := ⟨2^j, by
  have hp : 0 < (2:ℕ)^j := pow_pos (by norm_num) _
  rw [pow_succ]
  omega⟩

theorem dyadicHalf_add_self (j : ℕ) : dyadicHalf j + dyadicHalf j = 0 := by
  apply Fin.ext
  change (2^j+2^j)%2^(j+1)=0
  have hh : 2^j+2^j=2^(j+1) := by rw [pow_succ]; omega
  rw [hh, Nat.mod_self]

@[simp] theorem dyadicLower_add_half (j : ℕ) (i : Fin (2^j)) :
    dyadicLower j i + dyadicHalf j = dyadicUpper j i := by
  apply Fin.ext
  change (i.val+2^j)%2^(j+1)=2^j+i.val
  have hi := i.isLt
  rw [Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]
  omega

@[simp] theorem dyadicUpper_add_half (j : ℕ) (i : Fin (2^j)) :
    dyadicUpper j i + dyadicHalf j = dyadicLower j i := by
  apply Fin.ext
  change (2^j+i.val+2^j)%2^(j+1)=i.val
  have he : 2^j+i.val+2^j=2^(j+1)+i.val := by rw [pow_succ]; omega
  rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (i.isLt.trans_le (by rw [pow_succ]; omega))]

theorem dyadic_involutionBias (j : ℕ) (p : Fin (2^(j+1)) → ℝ) :
    involutionBias (dyadicHalf j) p = ∑ i, |p (dyadicLower j i)-p (dyadicUpper j i)| := by
  unfold involutionBias finiteL1 realDifference
  rw [dyadic_split_sum]
  simp only [dyadicLower_add_half, dyadicUpper_add_half,
    abs_sub_comm (p (dyadicUpper j _)) (p (dyadicLower j _))]
  rw [sum_add_distrib]
  ring

theorem dyadic_bitBias_eq_involution {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) :
    dyadicBitBias p f j = involutionBias (dyadicHalf j) (dyadicDistribution p f (j+1)) :=
  (dyadic_involutionBias j _).symm

theorem abs_sub_add_two_min (x y : ℝ) : |x-y|+2*min x y=x+y := by
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
  · rw [min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]; ring

theorem dyadic_bitBias_add_minority {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f : ι → ℕ) (hmass : ∑ a, p a=1) (j : ℕ) :
    dyadicBitBias p f j + dyadicMinority p f j = 1 := by
  have hs := sum_congr (s₁ := univ) rfl (fun (i : Fin (2^j)) _ =>
    abs_sub_add_two_min (dyadicDistribution p f (j+1) (dyadicLower j i))
      (dyadicDistribution p f (j+1) (dyadicUpper j i)))
  rw [sum_add_distrib, ← mul_sum] at hs
  change dyadicBitBias p f j + dyadicMinority p f j = _ at hs
  rw [← dyadic_split_sum, dyadicDistribution, finite_pushforward_sum, hmass] at hs
  exact hs

theorem dyadicMinority_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (j : ℕ) : 0 ≤ dyadicMinority p f j := by
  unfold dyadicMinority
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro i _
  exact le_min (finite_pushforward_nonneg p _ hp _) (finite_pushforward_nonneg p _ hp _)

theorem dyadic_bitBias_convolutionPow {k j : ℕ} (hj : j+1 ≤ k)
    (p : Fin (2^k) → ℝ) (r : ℕ) :
    dyadicBitBias (realConvolutionPow p r) Fin.val j ≤ (dyadicBitBias p Fin.val j)^r := by
  rw [dyadic_bitBias_eq_involution, dyadic_bitBias_eq_involution]
  change involutionBias (dyadicHalf j)
    (finitePushforward (realConvolutionPow p r) (dyadicProject hj)) ≤ _
  rw [pushforward_realConvolutionPow]
  exact involutionBias_convolutionPow_le _ (dyadicHalf_add_self j) _ r

end
end Erdos18c
-- END external module DyadicConvolution

-- BEGIN external module DyadicDilations

open Finset
namespace Erdos18c
noncomputable section

def dyadicScale (a m : ℕ) : Fin (2^m) →+ Fin (2^(a+m)) where
  toFun x := ⟨2^a*x.val, by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left x.isLt (by positivity)⟩
  map_zero' := by apply Fin.ext; simp
  map_add' x y := by
    apply Fin.ext
    change 2^a*((x.val+y.val)%2^m) = (2^a*x.val+2^a*y.val)%2^(a+m)
    rw [← Nat.mul_add, pow_add, Nat.mul_mod_mul_left]

theorem dyadicScale_injective (a m : ℕ) : Function.Injective (dyadicScale a m) := by
  intro x y h
  have hv := congrArg Fin.val h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2:ℕ)^a) hv

theorem dyadicScale_half (a j : ℕ) :
    dyadicScale a (j+1) (dyadicHalf j) =
      (dyadicHalf (a+j) : Fin (2^(a+(j+1)))) := by
  apply Fin.ext
  change 2^a*2^j = 2^(a+j)
  exact (pow_add 2 a j).symm

def dyadicMultiplier (k a : ℕ) (x : Fin (2^k)) : Fin (2^k) :=
  dyadicIndex k (2^a*x.val)

def dyadicDilate (k a : ℕ) (p : Fin (2^k) → ℝ) : Fin (2^k) → ℝ :=
  finitePushforward p (dyadicMultiplier k a)

theorem dyadic_multiplier_project {k m a : ℕ} (hj : a+m ≤ k) :
    (fun x : Fin (2^k) => dyadicIndex (a+m) (dyadicMultiplier k a x).val) =
      fun x : Fin (2^k) => (dyadicScale a m) (dyadicIndex m x.val) := by
  funext x
  apply Fin.ext
  dsimp [dyadicIndex,dyadicMultiplier,dyadicScale]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj)]
  rw [pow_add, Nat.mul_mod_mul_left]

theorem dyadicDilate_project {k m a : ℕ} (hj : a+m ≤ k)
    (p : Fin (2^k) → ℝ) :
    dyadicDistribution (dyadicDilate k a p) Fin.val (a+m) =
      finitePushforward (dyadicDistribution p Fin.val m) (dyadicScale a m) := by
  unfold dyadicDistribution dyadicDilate
  rw [finite_pushforward_comp, finite_pushforward_comp]
  congr 1
  exact dyadic_multiplier_project hj

def dyadicScaleBit (a j : ℕ) : Fin (2^(j+1)) →+ Fin (2^(a+j+1)) where
  toFun x := ⟨2^a*x.val, by
    rw [show (2:ℕ)^(a+j+1)=2^a*2^(j+1) by rw [Nat.add_assoc, pow_add]]
    exact Nat.mul_lt_mul_of_pos_left x.isLt (by positivity)⟩
  map_zero' := by apply Fin.ext; simp
  map_add' x y := by
    apply Fin.ext
    change 2^a*((x.val+y.val)%2^(j+1)) = (2^a*x.val+2^a*y.val)%2^(a+j+1)
    rw [← Nat.mul_add, show (2:ℕ)^(a+j+1)=2^a*2^(j+1) by rw [Nat.add_assoc, pow_add], Nat.mul_mod_mul_left]

theorem dyadicScaleBit_injective (a j : ℕ) : Function.Injective (dyadicScaleBit a j) := by
  intro x y h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2:ℕ)^a) (congrArg Fin.val h)

theorem dyadicScaleBit_half (a j : ℕ) :
    dyadicScaleBit a j (dyadicHalf j) = dyadicHalf (a+j) := by
  apply Fin.ext
  change 2^a*2^j=2^(a+j)
  exact (pow_add 2 a j).symm

theorem dyadicDilate_project_bit {k j a : ℕ} (hj : a+j+1 ≤ k)
    (p : Fin (2^k) → ℝ) :
    dyadicDistribution (dyadicDilate k a p) Fin.val (a+j+1) =
      finitePushforward (dyadicDistribution p Fin.val (j+1)) (dyadicScaleBit a j) := by
  unfold dyadicDistribution dyadicDilate
  rw [finite_pushforward_comp, finite_pushforward_comp]
  congr 1
  funext x
  apply Fin.ext
  dsimp [dyadicIndex,dyadicMultiplier,dyadicScaleBit]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj), Nat.add_assoc, pow_add, Nat.mul_mod_mul_left]

theorem dyadicDilate_bitBias_add {k a j : ℕ} (hj : a+(j+1) ≤ k)
    (p : Fin (2^k) → ℝ) :
    dyadicBitBias (dyadicDilate k a p) Fin.val (a+j) = dyadicBitBias p Fin.val j := by
  rw [dyadic_bitBias_eq_involution, dyadic_bitBias_eq_involution]
  rw [dyadicDilate_project_bit (by omega : a+j+1≤k)]
  have hh := involutionBias_pushforward (dyadicDistribution p Fin.val (j+1))
    (dyadicScaleBit a j) (dyadicScaleBit_injective _ _) (dyadicHalf j)
  rw [dyadicScaleBit_half] at hh
  exact hh

theorem dyadicDilate_bitBias {k a j : ℕ} (hj : j<k) (ha : a≤j)
    (p : Fin (2^k) → ℝ) :
    dyadicBitBias (dyadicDilate k a p) Fin.val j = dyadicBitBias p Fin.val (j-a) := by
  have he : a+(j-a)=j := Nat.add_sub_of_le ha
  have hh := dyadicDilate_bitBias_add (a:=a) (j:=j-a) (by omega : a+(j-a+1) ≤ k) p
  simpa only [he] using hh

theorem dyadicBitBias_le_one {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a=1) (j : ℕ) : dyadicBitBias p f j ≤ 1 := by
  rw [dyadic_bitBias_eq_involution]
  have hn := finite_pushforward_nonneg p (fun a => dyadicIndex (j+1) (f a)) hp
  have hs : finiteL1 (dyadicDistribution p f (j+1))=1 := by
    simp only [finiteL1, dyadicDistribution, abs_of_nonneg (hn _), finite_pushforward_sum, hsum]
  exact (involutionBias_le_l1 _ _).trans_eq hs

theorem dyadicDilate_nonneg {k a : ℕ} (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0 ≤ p x) (x : Fin (2^k)) : 0 ≤ dyadicDilate k a p x :=
  finite_pushforward_nonneg p _ hp x

theorem dyadicDilate_sum {k a : ℕ} (p : Fin (2^k) → ℝ) :
    ∑ x, dyadicDilate k a p x = ∑ x, p x := finite_pushforward_sum _ _

end
end Erdos18c
-- END external module DyadicDilations

-- BEGIN external module HarmonicMixing

open Finset
namespace Erdos18c
noncomputable section

def harmonicSum (k : ℕ) : ℝ := ∑ a ∈ range k, 1 / ((a:ℝ)+1)
def harmonicWeight (k a : ℕ) : ℝ := (1 / ((a:ℝ)+1)) / harmonicSum k
def harmonicLaw (k : ℕ) (p : Fin (2^k) → ℝ) : Fin (2^k) → ℝ :=
  finiteMixture (fun a : Fin k => harmonicWeight k a.val) (fun a => dyadicDilate k a.val p)

theorem harmonicSum_pos (k : ℕ) (hk : 0<k) : 0 < harmonicSum k := by
  have hb : (1:ℝ) ≤ harmonicSum k := by
    calc
      1 = 1 / ((0:ℝ)+1) := by norm_num
      _ ≤ _ := by
        simpa [harmonicSum] using single_le_sum (f := fun a : ℕ => 1/((a:ℝ)+1))
          (fun a _ => by positivity) (mem_range.mpr hk)
  linarith

theorem harmonicWeight_nonneg (k a : ℕ) : 0 ≤ harmonicWeight k a := by
  unfold harmonicWeight harmonicSum
  positivity

theorem harmonicWeight_sum (k : ℕ) (hk : 0<k) :
    ∑ a ∈ range k, harmonicWeight k a = 1 := by
  unfold harmonicWeight
  rw [← sum_div]
  change harmonicSum k / harmonicSum k = 1
  exact div_self (harmonicSum_pos k hk).ne'

theorem harmonicLaw_probability (k : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x, p x=1) :
    (∀ x, 0≤harmonicLaw k p x) ∧ ∑ x, harmonicLaw k p x=1 := by
  constructor
  · exact finiteMixture_nonneg _ _ (fun a => harmonicWeight_nonneg _ _)
      (fun a => dyadicDilate_nonneg p hp)
  · rw [harmonicLaw,sum_finiteMixture]
    simp_rw [dyadicDilate_sum, hs, mul_one]
    rw [Fin.sum_univ_eq_sum_range]
    exact harmonicWeight_sum k hk

def harmonicDefect (k j : ℕ) (p : Fin (2^k) → ℝ) : ℝ :=
  ∑ a ∈ range (j+1), harmonicWeight k a * dyadicMinority p Fin.val (j-a)

theorem harmonicDefect_lower (k j : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (c : ℝ)
    (hmass : c * (j+1:ℕ) ≤ ∑ t ∈ range (j+1), dyadicMinority p Fin.val t) :
    c / harmonicSum k ≤ harmonicDefect k j p := by
  have href : (∑ a ∈ range (j+1), dyadicMinority p Fin.val (j-a)) =
      ∑ t ∈ range (j+1), dyadicMinority p Fin.val t := by
    simpa using sum_range_reflect (dyadicMinority p Fin.val) (j+1)
  have hh := weighted_reciprocal_lower (range (j+1))
    (fun a => dyadicMinority p Fin.val (j-a)) (fun a => (a:ℝ)+1)
    (j+1:ℕ) (harmonicSum k) c (by positivity) (harmonicSum_pos k hk)
    (fun a _ => dyadicMinority_nonneg p Fin.val hp (j-a))
    (fun a ha => ⟨by positivity, by exact_mod_cast (mem_range.mp ha)⟩)
    (by rwa [href])
  apply hh.trans_eq
  unfold harmonicDefect harmonicWeight
  rw [sum_div]
  apply sum_congr rfl
  intro a _
  ring

theorem harmonicLaw_bias (k j : ℕ) (hj : j<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x,p x=1) :
    dyadicBitBias (harmonicLaw k p) Fin.val j ≤ 1 - harmonicDefect k j p := by
  have hk : 0<k := by omega
  let b := fun a : ℕ => dyadicBitBias (dyadicDilate k a p) Fin.val j
  have hble (a : ℕ) : b a ≤ 1 := by
    apply dyadicBitBias_le_one
    · exact dyadicDilate_nonneg p hp
    · rw [dyadicDilate_sum,hs]
  have hpos (a : ℕ) : 0 ≤ harmonicWeight k a * (1-b a) :=
    mul_nonneg (harmonicWeight_nonneg _ _) (sub_nonneg.mpr (hble a))
  have hpartial : harmonicDefect k j p ≤ ∑ a ∈ range k, harmonicWeight k a*(1-b a) := by
    calc
      _ = ∑ a ∈ range (j+1), harmonicWeight k a*(1-b a) := by
        apply sum_congr rfl
        intro a ha
        have haj : a≤j := by have := mem_range.mp ha; omega
        have hb := dyadicDilate_bitBias hj haj p
        have hu := dyadic_bitBias_add_minority p Fin.val hs (j-a)
        dsimp [b]
        rw [hb]
        congr 1
        linarith
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun a _ _ => hpos a)
  have htotal : (∑ a ∈ range k, harmonicWeight k a*(1-b a)) =
      1 - ∑ a ∈ range k, harmonicWeight k a*b a := by
    simp_rw [mul_sub, mul_one]
    rw [sum_sub_distrib,harmonicWeight_sum k hk]
  rw [htotal] at hpartial
  have hb : dyadicBitBias (harmonicLaw k p) Fin.val j ≤
      ∑ a ∈ range k, harmonicWeight k a*b a := by
    rw [dyadic_bitBias_eq_involution]
    change involutionBias (dyadicHalf j)
      (finitePushforward (harmonicLaw k p) (dyadicProject (Nat.succ_le_of_lt hj))) ≤ _
    rw [harmonicLaw,pushforward_finiteMixture]
    have hh := involutionBias_finiteMixture
      (fun a : Fin k => harmonicWeight k a.val)
      (fun a : Fin k => finitePushforward (dyadicDilate k a.val p) (dyadicProject (Nat.succ_le_of_lt hj)))
      (fun a => harmonicWeight_nonneg _ _) (dyadicHalf j)
    apply hh.trans_eq
    calc
      _ = ∑ a : Fin k, harmonicWeight k a.val * dyadicBitBias (dyadicDilate k a.val p) Fin.val j := by
        apply sum_congr rfl
        intro a _
        congr 1
        exact (dyadic_bitBias_eq_involution _ Fin.val j).symm
      _ = _ := Fin.sum_univ_eq_sum_range (fun a => harmonicWeight k a*b a) k
  linarith

theorem dyadicBitBias_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) :
    0 ≤ dyadicBitBias p f j := sum_nonneg fun _ _ => abs_nonneg _

theorem dyadic_entropy_lower_of_bias {k : ℕ} (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x,p x=1) (δ : ℝ)
    (hb : ∀ j<k, dyadicBitBias p Fin.val j ≤ δ) :
    (k:ℝ) * Real.log 2 * (1-δ) ≤ dyadicEntropy p Fin.val k := by
  have hlower : ∀ j∈range k, Real.log 2 * (1-δ) ≤
      dyadicEntropy p Fin.val (j+1)-dyadicEntropy p Fin.val j := by
    intro j hj
    have hbi := hb j (mem_range.mp hj)
    have he := dyadic_bitBias_add_minority p Fin.val hs j
    have hu : 1-δ ≤ dyadicMinority p Fin.val j := by linarith
    have hh := dyadic_entropy_step_lower p Fin.val hp j
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hu hlog]
  have hh := sum_le_sum hlower
  rw [dyadic_entropy_telescope p Fin.val hs] at hh
  simpa only [sum_const,card_range,nsmul_eq_mul,Nat.cast_id,mul_assoc] using hh

theorem harmonicLaw_power_entropy (k r : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x,p x=1) (g : ℝ) (hg : 0≤g)
    (hprefix : ∀ L, 0<L → L≤k → g * L * Real.log 2 ≤ dyadicEntropy p Fin.val L) :
    (k:ℝ) * Real.log 2 *
      (1-Real.exp (-(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k)) ≤
      dyadicEntropy (realConvolutionPow (harmonicLaw k p) r) Fin.val k := by
  let c := g^2*(Real.log 2)^2/2
  let t := c/harmonicSum k
  have hprob := harmonicLaw_probability k hk p hp hs
  have hout := realConvolutionPow_probability hprob.1 hprob.2 r
  apply dyadic_entropy_lower_of_bias _ hout.1 hout.2
  intro j hj
  have hm := dyadic_prefix_minority p Fin.val hp hs (j+1) (by omega) g hg
    (hprefix (j+1) (by omega) (by omega))
  have hdef := harmonicDefect_lower k j hk p hp c hm
  have hb0 := harmonicLaw_bias k j hj p hp hs
  have hb : dyadicBitBias (harmonicLaw k p) Fin.val j ≤ 1-t := by
    dsimp [t]
    linarith
  have hnonneg := dyadicBitBias_nonneg (harmonicLaw k p) Fin.val j
  have hbase : 0 ≤ 1-t := hnonneg.trans hb
  have hpwr := pow_le_pow_left₀ hnonneg hb r
  have hexp : 1-t ≤ Real.exp (-t) := by
    have hh := Real.add_one_le_exp (-t)
    linarith
  have hpowexp := pow_le_pow_left₀ hbase hexp r
  have hconv := dyadic_bitBias_convolutionPow (Nat.succ_le_of_lt hj) (harmonicLaw k p) r
  have hr := hconv.trans (hpwr.trans hpowexp)
  have he : Real.exp (-t) ^ r = Real.exp (-(r:ℝ)*c/harmonicSum k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [t]
    ring
  rwa [he] at hr

theorem dyadicEntropy_full (k : ℕ) (p : Fin (2^k) → ℝ) :
    dyadicEntropy p Fin.val k = finiteEntropy univ p := by
  have hid (x : Fin (2^k)) : dyadicIndex k x.val = x := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt x.isLt
  have he : dyadicDistribution p Fin.val k = p := by
    funext x
    simp [dyadicDistribution,finitePushforward,hid,sum_filter]
  rw [dyadicEntropy,he]

def finiteSupport {ι : Type*} [Fintype ι] (p : ι → ℝ) : Finset ι :=
  univ.filter fun x => p x≠0

theorem harmonicLaw_support_large (k r : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) (g : ℝ) (hg : 0≤g)
    (hprefix : ∀ L,0<L → L≤k → g*L*Real.log 2 ≤ dyadicEntropy p Fin.val L)
    (hr : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k) :
    2^k < 2*(finiteSupport (realConvolutionPow (harmonicLaw k p) r)).card := by
  let P := realConvolutionPow (harmonicLaw k p) r
  let B := finiteSupport P
  have hprob := harmonicLaw_probability k hk p hp hs
  have hout := realConvolutionPow_probability hprob.1 hprob.2 r
  have hB : B.Nonempty := by
    by_contra hB
    have hz (x : Fin (2^k)) : P x=0 := by
      by_contra hx
      exact hB ⟨x,by simp [B,finiteSupport,hx]⟩
    have hzero : ∑ x,P x=0 := sum_eq_zero fun x _ => hz x
    have hone : ∑ x,P x=1 := hout.2
    linarith
  have hcardpos : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  have hb := finite_entropy_le_log_support P B hout.1 hout.2 (fun x hx => by
    by_contra hn
    exact hx (by simp [B,finiteSupport,hn]))
  have hmain := harmonicLaw_power_entropy k r hk p hp hs g hg hprefix
  rw [dyadicEntropy_full] at hmain
  change (k:ℝ)*Real.log 2*(1-Real.exp (-(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k)) ≤ finiteEntropy univ P at hmain
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hr)
  have hrhs : Real.exp (-Real.log (2*(k:ℝ))) = (2*(k:ℝ))⁻¹ := by
    rw [Real.exp_neg,Real.exp_log (by positivity : (0:ℝ)<2*(k:ℝ))]
  rw [hrhs] at hexp
  have hdelta : (k:ℝ)*Real.exp (-(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hexp hkp.le
    have hid : (k:ℝ)*(2*(k:ℝ))⁻¹ = 1/2 := by field_simp
    have hneg : -((r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k) =
        -(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k := by ring
    rwa [hid,hneg] at hh
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hdelta hlog.le
  have hlower : ((k:ℝ)-1/2)*Real.log 2 ≤ finiteEntropy univ P := by nlinarith
  by_contra hc
  have hc' : 2*B.card ≤ 2^k := Nat.le_of_not_gt hc
  have hcR : (B.card:ℝ) ≤ (2:ℝ)^k/2 := by
    have hh : (2:ℝ)*(B.card:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast hc'
    linarith
  have hlogB := Real.log_le_log hcardpos hcR
  rw [Real.log_div (by positivity : (2:ℝ)^k≠0) (by norm_num),Real.log_pow] at hlogB
  linarith

theorem harmonicLaw_covers (k r : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) (g : ℝ) (hg : 0≤g)
    (hprefix : ∀ L,0<L → L≤k → g*L*Real.log 2 ≤ dyadicEntropy p Fin.val L)
    (hr : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k)
    (x : Fin (2^k)) :
    ∃ a∈finiteSupport (realConvolutionPow (harmonicLaw k p) r),
    ∃ b∈finiteSupport (realConvolutionPow (harmonicLaw k p) r), a+b=x := by
  apply twice_card_cover
  simpa using harmonicLaw_support_large k r hk p hp hs g hg hprefix hr

end
end Erdos18c
-- END external module HarmonicMixing

-- BEGIN H2 adapter scaffold
namespace Erdos18c
noncomputable section

def h2DigitWeight (xs : List ℕ) (_i : Fin xs.length) : ℝ := 1/(xs.length:ℝ)
def h2DigitValue (xs : List ℕ) (i : Fin xs.length) : ℕ := xs.get i
def h2DigitProjection (xs : List ℕ) (L : ℕ) : Fin (2^L) → ℝ :=
  dyadicDistribution (h2DigitWeight xs) (h2DigitValue xs) L

theorem h2DigitWeight_sum (xs : List ℕ) (hxs : 0 < xs.length) :
    ∑ i : Fin xs.length, h2DigitWeight xs i = 1 := by
  have hc : (xs.length:ℝ) ≠ 0 := by exact_mod_cast hxs.ne'
  simp only [h2DigitWeight, sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]
  field_simp

theorem h2DigitProjection_probability (xs : List ℕ) (hxs : 0 < xs.length) (L : ℕ) :
    (∀ x, 0 ≤ h2DigitProjection xs L x) ∧ ∑ x, h2DigitProjection xs L x = 1 := by
  refine ⟨?_, ?_⟩
  · change ∀ x, 0 ≤ finitePushforward (h2DigitWeight xs) (fun i => dyadicIndex L (h2DigitValue xs i)) x
    exact finite_pushforward_nonneg _ _ (fun i => by
      have hc : (0:ℝ) < xs.length := by exact_mod_cast hxs
      exact div_nonneg zero_le_one hc.le)
  · rw [h2DigitProjection, dyadicDistribution, finite_pushforward_sum, h2DigitWeight_sum xs hxs]

theorem list_filter_length_eq_indicator_sum (xs : List ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((xs.filter P).length : ℝ) =
      ∑ i : Fin xs.length, if P (xs.get i) then (1 : ℝ) else 0 := by
  have hreal : ((xs.filter P).length : ℝ) =
      (xs.map (fun x => if P x then (1 : ℝ) else 0)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        by_cases hx : P x <;> simp [hx, ih, Nat.add_comm]
  rw [hreal]
  exact (Fin.sum_univ_fun_getElem xs (fun x => if P x then (1 : ℝ) else 0)).symm

theorem finite_pushforward_support {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (T : ι → κ) (x : κ) (hx : finitePushforward p T x ≠ 0) :
    ∃ a, T a = x ∧ p a ≠ 0 := by
  obtain ⟨a, ha, hpa⟩ := exists_ne_zero_of_sum_ne_zero hx
  exact ⟨a, (mem_filter.mp ha).2, hpa⟩

theorem dyadicIndex_add (k a b : ℕ) :
    dyadicIndex k (a+b) = dyadicIndex k a + dyadicIndex k b := by
  apply Fin.ext
  exact Nat.add_mod _ _ _

theorem dyadicIndex_scale (k a b : ℕ) :
    dyadicIndex k (2^a*b) = dyadicMultiplier k a (dyadicIndex k b) := by
  apply Fin.ext
  change (2^a*b)%2^k = (2^a*(b%2^k))%2^k
  simp [Nat.mul_mod]

theorem zmod_eq_dyadicIndex_iff (L n : ℕ) (x : Fin (2^L)) :
    ((n : ZMod (2^L)) = (x.val : ZMod (2^L))) ↔ dyadicIndex L n = x := by
  rw [ZMod.natCast_eq_natCast_iff' n x.val (2^L), Nat.mod_eq_of_lt x.isLt]
  constructor
  · intro h
    apply Fin.ext
    exact h
  · intro h
    rw [← h]
    rfl

theorem h2DigitProjection_eq_count (xs : List ℕ) (hxs : 0 < xs.length)
    (L : ℕ) (x : Fin (2^L)) :
    h2DigitProjection xs L x =
      ((xs.filter fun n : ℕ => ((n : ZMod (2^L)) = (x.val : ZMod (2^L)))).length : ℝ) /
        (xs.length : ℝ) := by
  have hlen : (xs.length:ℝ) ≠ 0 := by exact_mod_cast hxs.ne'
  change (∑ i ∈ Finset.univ.filter (fun i => dyadicIndex L (h2DigitValue xs i) = x),
      h2DigitWeight xs i) = _
  rw [Finset.sum_filter]
  simp only [h2DigitWeight]
  have hfactor :
      (∑ i : Fin xs.length,
        if dyadicIndex L (h2DigitValue xs i) = x then (1/(xs.length:ℝ)) else 0) =
      (1/(xs.length:ℝ)) * ∑ i : Fin xs.length,
        if dyadicIndex L (h2DigitValue xs i) = x then (1:ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : dyadicIndex L (h2DigitValue xs i) = x <;> simp [h]
  rw [hfactor]
  have hcount := list_filter_length_eq_indicator_sum xs
    (fun n : ℕ => ((n : ZMod (2^L)) = (x.val : ZMod (2^L))))
  have hind :
      (∑ i : Fin xs.length,
        if ((xs.get i : ℕ) : ZMod (2^L)) = (x.val : ZMod (2^L)) then (1:ℝ) else 0) =
      (∑ i : Fin xs.length,
        if dyadicIndex L (xs.get i) = x then (1:ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    change (if (((xs.get i : ℕ) : ZMod (2^L)) = (x.val : ZMod (2^L))) then (1:ℝ) else 0) =
      if dyadicIndex L (xs.get i) = x then (1:ℝ) else 0
    by_cases hz : ((xs.get i : ZMod (2^L)) = (x.val : ZMod (2^L)))
    · have hd : dyadicIndex L (xs.get i) = x := (zmod_eq_dyadicIndex_iff L (xs.get i) x).mp hz
      rw [if_pos hz, if_pos hd]
    · have hd : ¬ dyadicIndex L (xs.get i) = x := by
        intro hd
        exact hz ((zmod_eq_dyadicIndex_iff L (xs.get i) x).mpr hd)
      rw [if_neg hz, if_neg hd]
  change (1/(xs.length:ℝ)) * (∑ i : Fin xs.length,
      if dyadicIndex L (xs.get i) = x then (1:ℝ) else 0) = _
  rw [← hind, ← hcount]
  field_simp [hlen]


theorem finiteEntropy_lower_of_cap {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) (M : ℝ)
    (hcap : ∀ x,p x≤M) : -Real.log M ≤ finiteEntropy univ p := by
  have hh := sum_mul_log_le_log_bound univ p (fun x _ => hp x) (fun x _ => hcap x)
  rw [hs,one_mul] at hh
  have he : finiteEntropy univ p = -(∑ x,p x*Real.log (p x)) := by
    simp [finiteEntropy,Real.negMulLog_def,neg_mul,sum_neg_distrib]
  rw [he]
  linarith

theorem h2Digit_entropy_prefix (xs : List ℕ) (hxs : 0 < xs.length) (k : ℕ)
    (hklog : 0 < Real.log (k:ℝ))
    (hcap : ∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun n : ℕ => ((n : ZMod (2 ^ L)) = z)).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ)))
    (L : ℕ) (hL : 0 < L) (hLk : L ≤ k) :
    ((3 / 2 : ℝ) / Real.log (k:ℝ)) * (L:ℝ) * Real.log 2 ≤
      dyadicEntropy (h2DigitProjection xs k) Fin.val L := by
  have he : dyadicDistribution (h2DigitProjection xs k) Fin.val L = h2DigitProjection xs L :=
    dyadic_distribution_project (h2DigitWeight xs) (h2DigitValue xs) hLk
  unfold dyadicEntropy
  rw [he]
  have hp := h2DigitProjection_probability xs hxs L
  have hcapatom : ∀ x : Fin (2^L),
      h2DigitProjection xs L x ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ)) := by
    intro x
    rw [h2DigitProjection_eq_count xs hxs L x]
    exact hcap L (by omega) hLk (x.val : ZMod (2^L))
  have hh := finiteEntropy_lower_of_cap _ hp.1 hp.2 _ hcapatom
  have hlogpow := Real.log_rpow (by norm_num : (0:ℝ)<2)
    (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ))
  rw [hlogpow] at hh
  have hrw : -((-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ)) * Real.log 2) =
      ((3 / 2 : ℝ) / Real.log (k:ℝ)) * (L:ℝ) * Real.log 2 := by
    field_simp [hklog.ne']
  rw [hrw] at hh
  exact hh


theorem h2Digit_harmonicLaw_support_repr (xs : List ℕ) (k : ℕ) (x : Fin (2^k))
    (hx : harmonicLaw k (h2DigitProjection xs k) x ≠ 0) :
    ∃ a : ℕ, a < k ∧ ∃ d ∈ xs, dyadicIndex k (2^a*d) = x := by
  change (∑ a : Fin k, harmonicWeight k a.val *
      dyadicDilate k a.val (h2DigitProjection xs k) x) ≠ 0 at hx
  obtain ⟨a, _, ha⟩ := exists_ne_zero_of_sum_ne_zero hx
  have hdilate : dyadicDilate k a.val (h2DigitProjection xs k) x ≠ 0 :=
    (mul_ne_zero_iff.mp ha).2
  change finitePushforward (h2DigitProjection xs k) (dyadicMultiplier k a.val) x ≠ 0 at hdilate
  obtain ⟨y, hymult, hpy⟩ := finite_pushforward_support
    (h2DigitProjection xs k) (dyadicMultiplier k a.val) x hdilate
  change finitePushforward (h2DigitWeight xs)
    (fun i => dyadicIndex k (h2DigitValue xs i)) y ≠ 0 at hpy
  obtain ⟨i, hi, _⟩ := finite_pushforward_support (h2DigitWeight xs)
    (fun i => dyadicIndex k (h2DigitValue xs i)) y hpy
  refine ⟨a.val, a.isLt, xs.get i, List.get_mem xs i, ?_⟩
  change dyadicIndex k (2^a.val * h2DigitValue xs i) = x
  have hscale := dyadicIndex_scale k a.val (h2DigitValue xs i)
  rw [hi, hymult] at hscale
  exact hscale


theorem convolutionPow_harmonicDigit_repr (xs : List ℕ) (k r : ℕ) (x : Fin (2^k))
    (hx : realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r x ≠ 0) :
    ∃ w : List (ℕ × ℕ), w.length = r ∧
      (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) ∧
      dyadicIndex k ((w.map fun p => 2 ^ p.1 * p.2).sum) = x := by
  induction r generalizing x with
  | zero =>
      have hx0 : x = 0 := by
        by_contra h
        simp [realConvolutionPow, h] at hx
      subst x
      exact ⟨[], by simp, by simp, by simp [dyadicIndex]⟩
  | succ r ih =>
      change (∑ a, harmonicLaw k (h2DigitProjection xs k) a *
        realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r (x-a)) ≠ 0 at hx
      obtain ⟨a, _, ha⟩ := exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨shift, hshift, digit, hdmem, hrep⟩ :=
        h2Digit_harmonicLaw_support_repr xs k a (mul_ne_zero_iff.mp ha).1
      obtain ⟨w, hwlen, hwvalid, hwcong⟩ := ih (x-a) (mul_ne_zero_iff.mp ha).2
      refine ⟨(shift,digit)::w, by simp [hwlen], ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hptail
        · exact ⟨hshift, hdmem⟩
        · exact hwvalid p hptail
      · rw [List.map_cons, List.sum_cons, dyadicIndex_add, hrep, hwcong]
        abel


theorem zmod_filter_length_eq (xs : List ℕ) (L : ℕ) (z : ZMod (2^L)) :
    ((xs.filter fun x => (x : ZMod (2^L)) = z).length) =
    ((xs.filter fun n : ℕ => ((n : ZMod (2^L)) = z)).length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : ((x : ZMod (2^L)) = z)
      · simp [hx]
        exact ih
      · simp [hx]
        exact ih

theorem harmonicSum_le (k : ℕ) : harmonicSum k ≤ 1+Real.log (k:ℝ) := by
  have he : harmonicSum k = (harmonic k : ℝ) := by
    simp [harmonicSum,harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [he]
  exact harmonic_le_one_add_log k

theorem h2_copy_condition_large (k : ℕ) (hk : 8 ≤ k) :
    Real.log (2*(k:ℝ)) ≤ ((Nat.log 2 k+1:ℝ)^4) *
      ((((3/2:ℝ)/Real.log (k:ℝ))^2*(Real.log 2)^2/2)/harmonicSum k) := by
  set t := Real.log (k:ℝ)
  set q := (Nat.log 2 k+1:ℝ)
  have hkposNat : 0 < k := by omega
  have hkpos : (0:ℝ) < k := by exact_mod_cast hkposNat
  have hkR : (8:ℝ) ≤ k := by exact_mod_cast hk
  have ht2 : 2 ≤ t := by
    have hmono : Real.log 8 ≤ Real.log (k:ℝ) := Real.log_le_log (by norm_num) hkR
    have h8 : (2:ℝ) ≤ Real.log 8 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
      have htwo := Real.log_two_gt_d9
      norm_num at htwo ⊢
      linarith
    exact h8.trans hmono
  have htpos : 0 < t := by linarith
  have hleft : Real.log (2*(k:ℝ)) ≤ (3/2)*t := by
    rw [Real.log_mul (by norm_num) hkpos.ne']
    have htwo := Real.log_two_lt_d9
    nlinarith [ht2]
  have hHpos : 0 < harmonicSum k := harmonicSum_pos k hkposNat
  have hHle : harmonicSum k ≤ (3/2)*t := by
    have hh := harmonicSum_le k
    nlinarith [ht2]
  have hpow : k < 2^(Nat.log 2 k+1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) k
  have hpowR : (k:ℝ) < ((2^(Nat.log 2 k+1) : ℕ):ℝ) := by exact_mod_cast hpow
  have hqpos : 0 < q := by positivity
  have hqlog : t ≤ q*Real.log 2 := by
    have hh := Real.log_le_log hkpos hpowR.le
    rw [Nat.cast_pow, Real.log_pow] at hh
    simpa [q, t] using hh
  have hu : (0:ℝ) < 0.6931471808 := by norm_num
  have hqmul : t < q*0.6931471808 := by
    have htwo := Real.log_two_lt_d9
    have hh := mul_lt_mul_of_pos_left htwo hqpos
    linarith
  have hqt : t/0.6931471808 ≤ q := by
    rw [div_le_iff₀ hu]
    exact hqmul.le
  have hrpow : (t/0.6931471808)^4 ≤ q^4 :=
    pow_le_pow_left₀ (div_nonneg htpos.le hu.le) hqt 4
  have hsq : (0.6931471803:ℝ)^2 ≤ (Real.log 2)^2 :=
    pow_le_pow_left₀ (by norm_num) Real.log_two_gt_d9.le 2
  have hg20 : 0 ≤ ((3/2:ℝ)/t)^2 := by positivity
  have hmulsq := mul_le_mul_of_nonneg_left hsq hg20
  have hAlower : ((3/2:ℝ)/t)^2*(0.6931471803)^2/2 ≤
      ((3/2:ℝ)/t)^2*(Real.log 2)^2/2 := by
    have hh := mul_le_mul_of_nonneg_right hmulsq (by norm_num : (0:ℝ) ≤ 1/2)
    nlinarith
  have hA_nonneg : 0 ≤ ((3/2:ℝ)/t)^2*(Real.log 2)^2/2 := by positivity
  have hdiv : (((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/((3/2)*t) ≤
      (((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/harmonicSum k :=
    div_le_div_of_nonneg_left hA_nonneg hHpos hHle
  have htDpos : 0 < (3/2)*t := mul_pos (by norm_num) htpos
  have hA0div_nonneg : 0 ≤ (((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t) := by
    exact div_nonneg (by positivity) htDpos.le
  have hqpow_nonneg : 0 ≤ q^4 := pow_nonneg hqpos.le 4
  have hmain :
      ((t/0.6931471808)^4) *
        ((((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t)) ≤
        q^4 * ((((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/harmonicSum k) := by
    calc
      ((t/0.6931471808)^4) *
          ((((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t))
          ≤ q^4 * ((((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t)) :=
        mul_le_mul_of_nonneg_right hrpow hA0div_nonneg
      _ ≤ q^4 * ((((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/((3/2)*t)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hAlower htDpos.le) hqpow_nonneg
      _ ≤ q^4 * ((((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/harmonicSum k) :=
        mul_le_mul_of_nonneg_left hdiv hqpow_nonneg
  have hnum :
      ((t/0.6931471808)^4) *
        ((((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t)) =
        (3*(0.6931471803:ℝ)^2/(4*(0.6931471808)^4))*t := by
    field_simp [htpos.ne']
    ring
  rw [hnum] at hmain
  have hC : (3/2:ℝ) ≤ 3*(0.6931471803:ℝ)^2/(4*(0.6931471808)^4) := by norm_num
  have hleftC : Real.log (2*(k:ℝ)) ≤
      (3*(0.6931471803:ℝ)^2/(4*(0.6931471808)^4))*t := by
    nlinarith [hleft]
  exact hleftC.trans hmain

open Filter in

theorem h2_pair_shift_sum_bound (xs : List ℕ) (k : ℕ) (w : List (ℕ × ℕ))
    (hxbound : ∀ x ∈ xs, x ≤ 2^k) :
    (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) →
    (w.map fun p : ℕ × ℕ => 2^p.1*p.2).sum ≤ w.length*2^(2*k) := by
  induction w with
  | nil =>
      intro hwvalid
      simp
  | cons p w ih =>
      intro hwvalid
      have hp : p.1 < k ∧ p.2 ∈ xs := hwvalid p (by simp)
      have htailvalid : ∀ q ∈ w, q.1 < k ∧ q.2 ∈ xs := by
        intro q hq
        exact hwvalid q (by simp [hq])
      have htail := ih htailvalid
      have hpow : 2^p.1 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hp.1)
      have hdigit : p.2 ≤ 2^k := hxbound p.2 hp.2
      have hterm : 2^p.1*p.2 ≤ 2^(2*k) := by
        calc
          2^p.1*p.2 ≤ 2^k*2^k := Nat.mul_le_mul hpow hdigit
          _ = 2^(2*k) := by
            rw [← pow_add]
            congr 1
            omega
      rw [List.map_cons,List.sum_cons,List.length_cons]
      exact (Nat.add_le_add hterm htail).trans_eq (by ring)

lemma pow_step16 (k : ℕ) (hk : 16 ≤ k) : (k+1)^4 ≤ 2*k^4 := by
  have hkR : (16:ℝ) ≤ k := by exact_mod_cast hk
  have hlin : ((k+1:ℕ):ℝ) ≤ (9/8:ℝ)*k := by
    norm_num
    nlinarith
  have hpow : ((k+1:ℕ):ℝ)^4 ≤ ((9/8:ℝ)*k)^4 := by
    exact pow_le_pow_left₀ (by positivity) hlin 4
  have hfactor : ((9/8:ℝ)^4) ≤ 2 := by norm_num
  have hreal : ((k+1:ℕ):ℝ)^4 ≤ 2*(k:ℝ)^4 := by
    calc
      ((k+1:ℕ):ℝ)^4 ≤ ((9/8:ℝ)*k)^4 := hpow
      _ = ((9/8:ℝ)^4)*(k:ℝ)^4 := by ring
      _ ≤ 2*(k:ℝ)^4 := mul_le_mul_of_nonneg_right hfactor (by positivity)
  exact_mod_cast hreal

theorem pow4_le_two_pow (k : ℕ) (hk : 16 ≤ k) : k^4 ≤ 2^k := by
  induction' k, hk using Nat.le_induction with k hk ih
  · norm_num
  · calc
      (k+1)^4 ≤ 2*k^4 := pow_step16 k hk
      _ ≤ 2*2^k := Nat.mul_le_mul_left 2 ih
      _ = 2^(k+1) := by rw [pow_succ]; ring

theorem pow4_le_two_pow_pred (k : ℕ) (hk : 32 ≤ k) : k^4 ≤ 2^(k-1) := by
  induction' k, hk using Nat.le_induction with k hk ih
  · norm_num
  · have hk16 : 16 ≤ k := by omega
    calc
      (k+1)^4 ≤ 2*k^4 := pow_step16 k hk16
      _ ≤ 2*2^(k-1) := Nat.mul_le_mul_left 2 ih
      _ = 2^((k-1)+1) := by
        rw [pow_succ]
        ring
      _ = 2^((k+1)-1) := by
        congr 1
        omega

theorem h2_height_bound_large (k : ℕ) (hk : 31 ≤ k) :
    (Nat.log 2 k+1)^4*2^(2*k) ≤ 2^(3*k) := by
  have hq : Nat.log 2 k+1 ≤ k+1 := Nat.succ_le_succ (Nat.log_le_self 2 k)
  have hpow : (Nat.log 2 k+1)^4 ≤ (k+1)^4 := Nat.pow_le_pow_left hq 4
  have hk32 : 32 ≤ k+1 := by omega
  have hpred := pow4_le_two_pow_pred (k+1) hk32
  have hpred' : (k+1)^4 ≤ 2^k := by
    simpa using hpred
  have hqpow : (Nat.log 2 k+1)^4 ≤ 2^k := hpow.trans hpred'
  calc
    (Nat.log 2 k+1)^4*2^(2*k) ≤ 2^k*2^(2*k) := Nat.mul_le_mul_right _ hqpow
    _ = 2^(3*k) := by
      rw [← pow_add]
      congr 1
      omega

open Filter in
theorem eventually_h2_copy_condition : ∀ᶠ k : ℕ in atTop,
    Real.log (2*(k:ℝ)) ≤ ((Nat.log 2 k+1:ℝ)^4) *
      ((((3/2:ℝ)/Real.log (k:ℝ))^2*(Real.log 2)^2/2)/harmonicSum k) := by
  filter_upwards [eventually_ge_atTop 8] with k hk
  exact h2_copy_condition_large k hk


def finToZModEmbedding (n : ℕ) [NeZero n] : Fin n ↪ ZMod n where
  toFun x := (x.val : ZMod n)
  inj' := by
    intro x y h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    apply Fin.ext
    rwa [Nat.mod_eq_of_lt x.isLt,Nat.mod_eq_of_lt y.isLt] at h

theorem h2_construct_large (k : ℕ) (hk : 31 ≤ k) (xs : List ℕ)
    (hxs : 0 < xs.length)
    (hrep : ∀ x ∈ xs, x ≤ 2 ^ k ∧ ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
      S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x)
    (hcap : ∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun x => (x : ZMod (2 ^ L)) = z).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k : ℝ))) :
    ∃ B : Finset (ZMod (2 ^ k)),
      2 ^ k < 2 * B.card ∧ ∀ y ∈ B, ∃ w : List (ℕ × ℕ),
        w.length ≤ (Nat.log 2 k + 1) ^ 4 ∧
        (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) ∧
        (w.map fun p => 2 ^ p.1 * p.2).sum ≤ 2 ^ (3 * k) ∧
        (((w.map fun p => 2 ^ p.1 * p.2).sum : ℕ) : ZMod (2 ^ k)) = y := by
  have hk8 : 8 ≤ k := by omega
  have hkpos : 0 < k := by omega
  have : NeZero (2^k) := ⟨by positivity⟩
  let r : ℕ := (Nat.log 2 k+1)^4
  let g : ℝ := (3/2:ℝ)/Real.log (k:ℝ)
  have hklog : 0 < Real.log (k:ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < k by omega)
  have hcapnat : ∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun n : ℕ => ((n : ZMod (2 ^ L)) = z)).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k : ℝ)) := by
    intro L hL hLk z
    rw [← zmod_filter_length_eq xs L z]
    exact hcap L hL hLk z
  have hprefix : ∀ L : ℕ, 0 < L → L ≤ k →
      g*(L:ℝ)*Real.log 2 ≤ dyadicEntropy (h2DigitProjection xs k) Fin.val L := by
    intro L hL hLk
    exact h2Digit_entropy_prefix xs hxs k hklog hcapnat L hL hLk
  have hp := h2DigitProjection_probability xs hxs k
  have hg : 0 ≤ g := by
    exact le_of_lt (div_pos (by norm_num) hklog)
  have hrcopy0 := h2_copy_condition_large k hk8
  have hcastpow : ((((Nat.log 2 k+1)^4 : ℕ) : ℝ)) = (Nat.log 2 k+1:ℝ)^4 := by norm_num
  have hrcopy : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k := by
    rw [mul_div_assoc]
    simpa [r,g,hcastpow] using hrcopy0
  have hdense := harmonicLaw_support_large k r hkpos (h2DigitProjection xs k) hp.1 hp.2 g hg hprefix hrcopy
  let Bfin : Finset (Fin (2^k)) := finiteSupport (realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r)
  let emb : Fin (2^k) ↪ ZMod (2^k) := finToZModEmbedding (2^k)
  refine ⟨Bfin.map emb, ?_, ?_⟩
  · simpa [Bfin] using hdense
  · intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x,hxB,rfl⟩ := hy
    have hxne : realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r x ≠ 0 := by
      have hxmem : x ∈ finiteSupport (realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r) := by
        simpa [Bfin] using hxB
      exact (Finset.mem_filter.mp hxmem).2
    obtain ⟨w,hwlen,hwvalid,hwcong⟩ := convolutionPow_harmonicDigit_repr xs k r x hxne
    refine ⟨w, ?_, hwvalid, ?_, ?_⟩
    · rw [hwlen]
    · have hxbound : ∀ x ∈ xs, x ≤ 2^k := by
        intro x hx
        exact (hrep x hx).1
      have hsum := h2_pair_shift_sum_bound xs k w hxbound hwvalid
      rw [hwlen] at hsum
      exact hsum.trans (by simpa [r] using h2_height_bound_large k hk)
    · have hz := (zmod_eq_dyadicIndex_iff k ((w.map fun p => 2 ^ p.1 * p.2).sum) x).mpr hwcong
      change (((w.map fun p => 2 ^ p.1 * p.2).sum : ℕ) : ZMod (2 ^ k)) = (x.val : ZMod (2 ^ k))
      exact hz

open Filter in
theorem erdos18_h2_kernel :
    ∀ᶠ k : ℕ in atTop, ∀ xs : List ℕ,
    0 < xs.length →
    (∀ x ∈ xs, x ≤ 2 ^ k ∧ ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
      S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x) →
    (∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun x => (x : ZMod (2 ^ L)) = z).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k : ℝ))) →
    ∃ B : Finset (ZMod (2 ^ k)),
      2 ^ k < 2 * B.card ∧ ∀ y ∈ B, ∃ w : List (ℕ × ℕ),
        w.length ≤ (Nat.log 2 k + 1) ^ 4 ∧
        (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) ∧
        (w.map fun p => 2 ^ p.1 * p.2).sum ≤ 2 ^ (3 * k) ∧
        (((w.map fun p => 2 ^ p.1 * p.2).sum : ℕ) : ZMod (2 ^ k)) = y := by
  filter_upwards [eventually_ge_atTop 31] with k hk
  intro xs hxs hrep hcap
  exact h2_construct_large k hk xs hxs hrep hcap

end
end Erdos18c
-- END H2 adapter scaffold

open OMA.R_Erdos18_erdos_18a_R1_H1_R1

theorem OMA.solution : OMA.R_Erdos18_erdos_18a_R1_H1_R1.H2 :=
  Erdos18c.erdos18_h2_kernel
