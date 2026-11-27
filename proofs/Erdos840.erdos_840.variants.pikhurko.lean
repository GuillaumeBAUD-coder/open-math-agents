import FormalConjectures.ErdosProblems.«840»
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

/-! The absolutely convergent cosine series for the absolute value of sine. -/

noncomputable section

open Complex Real Set
open scoped BigOperators

namespace PikhurkoSeries

private theorem absSin_periodic :
    Function.Periodic (fun x : ℝ => (↑|Real.sin x| : ℂ)) Real.pi := by
  intro x
  simp only [Real.sin_add_pi, abs_neg]

private def absSin : C(AddCircle Real.pi, ℂ) :=
  ⟨absSin_periodic.lift, continuous_coinduced_dom.mpr (by
    change Continuous (fun x : ℝ => (↑|Real.sin x| : ℂ))
    fun_prop)⟩

private theorem absSin_coe (x : ℝ) : absSin (x : AddCircle Real.pi) = (↑|Real.sin x| : ℂ) :=
  Function.Periodic.lift_coe absSin_periodic x

private theorem fourier_pi (n : ℤ) (x : ℝ) :
    @fourier Real.pi n (x : AddCircle Real.pi) =
      Complex.exp ((2 * (n : ℂ) * Complex.I) * x) := by
  rw [fourier_coe_apply]
  congr 1
  have hp : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply (div_eq_iff hp).2
  ring

private theorem rate (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
      ((↑(Real.cos y) : ℂ) + (2 * (n : ℂ) * Complex.I) * (↑(Real.sin y) : ℂ)) *
        Complex.exp (-(2 * (n : ℂ) * Complex.I) * (y : ℂ)))
      ((4 * (n : ℂ)^2 - 1) * ((↑(Real.sin x) : ℂ) *
        Complex.exp (-(2 * (n : ℂ) * Complex.I) * (x : ℂ)))) x := by
  let b : ℂ := 2 * (n : ℂ) * Complex.I
  have hb : b ^ 2 = -4 * (n : ℂ)^2 := by
    dsimp [b]
    calc
      (2 * (n : ℂ) * Complex.I) ^ 2 = 4 * (n : ℂ)^2 * Complex.I^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hc := (Real.hasDerivAt_cos x).ofReal_comp
  have hs := (Real.hasDerivAt_sin x).ofReal_comp
  have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have hex := (hz.const_mul (-b)).cexp
  change HasDerivAt (fun y : ℝ => ((↑(Real.cos y) : ℂ) + b * (↑(Real.sin y) : ℂ)) *
    Complex.exp (-b * (y : ℂ))) _ x
  have hder := (hc.add (hs.const_mul b)).mul hex
  simp only [Pi.add_apply] at hder
  have hd :
      ((↑(-Real.sin x) : ℂ) + b * (↑(Real.cos x) : ℂ)) * Complex.exp (-b * (x : ℂ)) +
        ((↑(Real.cos x) : ℂ) + b * (↑(Real.sin x) : ℂ)) *
          (Complex.exp (-b * (x : ℂ)) * (-b * 1)) =
      (4 * (n : ℂ)^2 - 1) * ((↑(Real.sin x) : ℂ) * Complex.exp (-b * (x : ℂ))) := by
    rw [Complex.ofReal_neg]
    calc
      _ = (-1 - b^2) * ((↑(Real.sin x) : ℂ) * Complex.exp (-b * (x : ℂ))) := by ring
      _ = _ := by rw [hb]; ring
  rwa [hd] at hder

private theorem scale_ne_zero (n : ℤ) : 4 * (n : ℝ)^2 - 1 ≠ 0 := by
  intro h
  have hf : (2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with hf | hf
  · have : 2 * (n : ℝ) = (1 : ℤ) := by push_cast; linarith
    exact (by omega : (2 : ℤ) * n ≠ 1) (by exact_mod_cast this)
  · have : 2 * (n : ℝ) = (-1 : ℤ) := by push_cast; linarith
    exact (by omega : (2 : ℤ) * n ≠ -1) (by exact_mod_cast this)

private theorem exp_end (n : ℤ) :
    Complex.exp (-(2 * (n : ℂ) * Complex.I) * (↑Real.pi : ℂ)) = 1 := by
  convert Complex.exp_int_mul_two_pi_mul_I (-n) using 2
  push_cast
  ring

private theorem coeff_integral (n : ℤ) :
    (∫ x in (0 : ℝ)..Real.pi, ((↑(Real.sin x) : ℂ) *
      Complex.exp (-(2 * (n : ℂ) * Complex.I) * (x : ℂ)))) =
        (↑((-2 / (4 * (n : ℝ)^2 - 1)) : ℝ) : ℂ) := by
  let g := fun x : ℝ => ((↑(Real.sin x) : ℂ) *
      Complex.exp (-(2 * (n : ℂ) * Complex.I) * (x : ℂ)))
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := Real.pi)
    (fun x _ => rate n x) ((continuous_const.mul hg).intervalIntegrable _ _)
  simp only [Real.cos_pi, Real.sin_pi, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero,
    mul_zero, add_zero, exp_end, mul_one, Real.cos_zero, Real.sin_zero, Complex.exp_zero] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hd : 4 * (n : ℂ)^2 - 1 ≠ 0 := by exact_mod_cast scale_ne_zero n
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_intCast, Complex.ofReal_one]
  apply (eq_div_iff hd).2
  rw [mul_comm]
  convert hi using 1; ring

private instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

private def a (n : ℤ) : ℝ := -2 / (Real.pi * (4 * (n : ℝ)^2 - 1))

private theorem coeff (n : ℤ) :
    fourierCoeff absSin n = (↑(a n) : ℂ) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
  have hi : (∫ x in (0 : ℝ)..Real.pi, fourier (-n) (x : AddCircle Real.pi) •
      absSin (x : AddCircle Real.pi)) =
      ∫ x in (0 : ℝ)..Real.pi, ((↑(Real.sin x) : ℂ) *
        Complex.exp (-(2 * (n : ℂ) * Complex.I) * (x : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le Real.pi_pos.le] at hx
    change fourier (-n) (x : AddCircle Real.pi) • absSin (x : AddCircle Real.pi) = _
    rw [fourier_pi, absSin_coe, abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hx), smul_eq_mul,
      mul_comm]
    congr 2
    push_cast
    ring
  rw [hi, coeff_integral]
  simp [a, real_smul, div_eq_mul_inv, mul_left_comm, mul_comm]

def weight (n : ℕ) : ℝ := 2 / (4 * ((n : ℝ) + 1)^2 - 1)

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  unfold weight
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  apply div_nonneg (by norm_num)
  nlinarith [sq_nonneg (n : ℝ)]

private theorem summable_weight : Summable weight := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    by simpa only [one_div] using (Real.summable_nat_pow_inv (p := 2)).2 (by decide)
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hp
  refine Summable.of_nonneg_of_le weight_nonneg (fun n => ?_) (hs.mul_left 2)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  unfold weight
  rw [← mul_div_assoc, mul_one]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [sq_nonneg (n : ℝ)]

private theorem a_even : Function.Even a := by
  intro n
  simp [a]

private theorem a_succ (n : ℕ) : a ((n : ℤ) + 1) = -(weight n) / Real.pi := by
  simp only [a, weight, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem coeff_summable : Summable (fourierCoeff absSin) := by
  have hs : Summable (fun n : ℤ => a n) := by
    suffices Summable (fun n : ℕ => a (n : ℤ)) by
      refine summable_int_iff_summable_nat_and_neg.2 ⟨this, ?_⟩
      exact this.congr (fun n => (a_even (n : ℤ)).symm)
    apply (summable_nat_add_iff 1).1
    refine (summable_weight.neg.div_const Real.pi).congr (fun n => ?_)
    show -(weight n) / Real.pi = a ((n + 1 : ℕ) : ℤ)
    rw [Nat.cast_add, Nat.cast_one, a_succ]
  exact (Complex.ofRealCLM.hasSum hs.hasSum).summable.congr
    (fun n => (coeff n).symm)

private def cosineTerm (x : ℝ) (n : ℤ) : ℝ := a n * Real.cos (2 * (n : ℝ) * x)

private theorem cosineTerm_congr (x : ℝ) (n : ℤ) :
    (fourierCoeff absSin n * fourier n (x : AddCircle Real.pi)).re = cosineTerm x n := by
  rw [coeff, fourier_pi, Complex.re_ofReal_mul, Complex.exp_re]
  have hr : ((2 * (n : ℂ) * I) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have hi : ((2 * (n : ℂ) * I) * (x : ℂ)).im = 2 * (n : ℝ) * x := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hr, hi, Real.exp_zero, one_mul]
  rfl

private theorem cosineTerm_even (x : ℝ) : (cosineTerm x).Even := by
  intro n
  unfold cosineTerm
  rw [a_even, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]

theorem cosine_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => weight n * Real.cos (2 * ((n : ℝ) + 1) * x))
      (1 - Real.pi / 2 * |Real.sin x|) := by
  let f := cosineTerm x
  have hs : HasSum f |Real.sin x| := by
    have hc := Complex.reCLM.hasSum
      (has_pointwise_sum_fourier_series_of_summable coeff_summable (x : AddCircle Real.pi))
    simpa only [real_smul, smul_eq_mul, Complex.reCLM_apply, cosineTerm_congr,
      absSin_coe, Complex.ofReal_re, f] using hc
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat (cosineTerm_even x) hs.summable
  change (∑' n : ℤ, f n) = f 0 + 2 • ∑' n : ℕ+, f ((n : ℕ) : ℤ) at hsplit
  rw [hs.tsum_eq, tsum_pnat_eq_tsum_succ (f := fun m : ℕ => f (m : ℤ)), two_smul] at hsplit
  have hzero : f 0 = 2 / Real.pi := by
    simp [f, cosineTerm, a]
  rw [hzero] at hsplit
  let g := fun n : ℕ => weight n * Real.cos (2 * ((n : ℝ) + 1) * x)
  have hg : Summable g := by
    refine Summable.of_norm_bounded summable_weight (fun n => ?_)
    simp only [g, Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg n)]
    exact mul_le_of_le_one_right (weight_nonneg n) (Real.abs_cos_le_one _)
  have hterm (n : ℕ) : f ((n + 1 : ℕ) : ℤ) = -(g n) / Real.pi := by
    change a ((n + 1 : ℕ) : ℤ) * Real.cos (2 * (((n + 1 : ℕ) : ℤ) : ℝ) * x) = _
    rw [Nat.cast_add, Nat.cast_one, a_succ]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, g]
    ring
  simp_rw [hterm] at hsplit
  rw [tsum_div_const, tsum_neg] at hsplit
  have heq : (∑' n, g n) = 1 - Real.pi / 2 * |Real.sin x| := by
    have hp := Real.pi_pos
    field_simp at hsplit
    linarith
  exact heq ▸ hg.hasSum

theorem weight_hasSum : HasSum weight 1 := by
  simpa using cosine_hasSum 0

end PikhurkoSeries

open Filter Asymptotics
open scoped Finset Pointwise Topology

namespace PikhurkoModes

private lemma norm_sum_pow_le_card (A : Finset ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∑ a ∈ A, z ^ a‖ ≤ (A.card : ℝ) := by
  simpa only [norm_pow, hz, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
    (norm_sum_le A (fun a => z ^ a))

private lemma interval_sum_zero {N : ℕ} {z : ℂ} (hz : z ≠ 1) (hzN : z ^ (2 * N) = 1) :
    ∑ j ∈ Finset.Icc 1 (2 * N), z ^ j = 0 := by
  have hh := geom_sum_Ico_mul z (show 1 ≤ 2 * N + 1 by omega)
  have hI : Finset.Ico 1 (2 * N + 1) = Finset.Icc 1 (2 * N) := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hI, pow_succ, hzN, one_mul, pow_one, sub_self] at hh
  exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hz)

private lemma norm_pow_sum_of_subset {S T : Finset ℕ} (hS : S ⊆ T)
    {z : ℂ} (hz : ‖z‖ = 1) (hT : ∑ s ∈ T, z ^ s = 0) :
    ‖∑ s ∈ S, z ^ s‖ ≤ (T.card : ℝ) - S.card := by
  have h := Finset.sum_sdiff (f := fun s : ℕ => z ^ s) hS
  rw [hT, add_eq_zero_iff_eq_neg] at h
  have hb := norm_sum_pow_le_card (T \ S) hz
  rw [h, norm_neg, Finset.card_sdiff_of_subset hS, Nat.cast_sub (Finset.card_le_card hS)] at hb
  exact hb

/-- A nontrivial character on the cyclic interval of length `2N` has a small
Fourier coefficient when the sumset has few repeated representations. -/
theorem norm_square_le (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (hzN : z ^ (2 * N) = 1) :
    ‖∑ a ∈ A, z ^ a‖ ^ 2 ≤ (A.card : ℝ) ^ 2 + 4 * (N : ℝ) - 4 * (A + A).card + 4 * A.card := by
  classical
  let P := A ×ˢ A
  let addPair (p : ℕ × ℕ) : ℕ := p.1 + p.2
  let S := A + A
  let D := A.image (fun a => a + a)
  let B := S \ D
  let rep (s : ℕ) := (P.filter (fun p => addPair p = s)).card
  let base (s : ℕ) : ℕ := if s ∈ B then 2 else 0
  let rest (s : ℕ) := rep s - base s
  have hmap : (P : Set (ℕ × ℕ)).MapsTo addPair (S : Set ℕ) := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_add.mpr ⟨p.1, h1, p.2, h2, rfl⟩
  have hbase (s : ℕ) : base s ≤ rep s := by
    by_cases hs : s ∈ B
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (Finset.mem_sdiff.mp hs).1
      have hne : a ≠ b := by
        intro he
        subst b
        exact (Finset.mem_sdiff.mp hs).2 (Finset.mem_image.mpr ⟨a, ha, hab⟩)
      have hsub : ({(a, b), (b, a)} : Finset (ℕ × ℕ)) ⊆ P.filter (fun p => addPair p = s) := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩
        · obtain rfl := Finset.mem_singleton.mp hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, (Nat.add_comm b a).trans hab⟩
      have hpair : (a, b) ≠ (b, a) := fun h => hne (congrArg Prod.fst h)
      simpa [base, hs, rep, hpair] using Finset.card_le_card hsub
    · simp [base, hs]
  have hrep (s : ℕ) : rep s = base s + rest s := by
    dsimp only [rest]
    have := hbase s
    omega
  have hfilter : S.filter (· ∈ B) = B := by
    ext s
    exact Finset.mem_filter.trans ⟨And.right, fun hs => ⟨(Finset.mem_sdiff.mp hs).1, hs⟩⟩
  have hrep_sum : (∑ s ∈ S, rep s) = A.card ^ 2 := by
    rw [← Finset.card_eq_sum_card_fiberwise hmap]
    exact (Finset.card_product _ _).trans (pow_two _).symm
  have hbase_sum : (∑ s ∈ S, base s) = 2 * B.card := by
    change (∑ s ∈ S, if s ∈ B then 2 else 0) = _
    rw [← Finset.sum_filter, hfilter]
    exact (Finset.sum_const_nat (fun _ _ => rfl)).trans (Nat.mul_comm B.card 2)
  have hsums := Finset.sum_congr rfl (fun s (_ : s ∈ S) => hrep s)
  rw [Finset.sum_add_distrib, hrep_sum, hbase_sum] at hsums
  have hrest_sum : (∑ s ∈ S, (rest s : ℝ)) = (A.card : ℝ) ^ 2 - 2 * B.card := by
    have hn : (A.card : ℝ) ^ 2 = 2 * (B.card : ℝ) + ∑ s ∈ S, (rest s : ℝ) := by
      exact_mod_cast hsums
    linarith
  have hfourier (s : ℕ) :
      (∑ p ∈ P.filter (fun p => addPair p = s), z ^ addPair p) = (rep s : ℂ) * z ^ s := by
    calc
      _ = ∑ _ ∈ P.filter (fun p => addPair p = s), z ^ s :=
        Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
      _ = _ := by simp [rep, nsmul_eq_mul]
  have hmode : (∑ a ∈ A, z ^ a) ^ 2 = ∑ s ∈ S, (rep s : ℂ) * z ^ s := by
    calc
      _ = ∑ p ∈ P, z ^ addPair p := by
        rw [pow_two, Finset.sum_product, Finset.sum_mul]
        simp only [Finset.mul_sum, addPair, pow_add]
      _ = ∑ s ∈ S, ∑ p ∈ P.filter (fun p => addPair p = s), z ^ addPair p :=
        (Finset.sum_fiberwise_of_maps_to hmap (fun p => z ^ addPair p)).symm
      _ = _ := Finset.sum_congr rfl fun s _ => hfourier s
  have hbase_complex : (∑ s ∈ S, (base s : ℂ) * z ^ s) = 2 * ∑ s ∈ B, z ^ s := by
    rw [Finset.mul_sum, ← hfilter, Finset.sum_filter]
    exact Finset.sum_congr rfl fun s _ => by
      by_cases hs : s ∈ B <;> simp [base, hs]
  have hsplit : (∑ a ∈ A, z ^ a) ^ 2 =
      (2 : ℂ) * (∑ s ∈ B, z ^ s) + ∑ s ∈ S, (rest s : ℂ) * z ^ s := by
    rw [hmode, ← hbase_complex, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    conv_lhs => rw [hrep s]
    rw [Nat.cast_add, add_mul]
  have hS : S ⊆ Finset.Icc 1 (2 * N) := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    have ha' := Finset.mem_Icc.mp (hA ha)
    have hb' := Finset.mem_Icc.mp (hA hb)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hB : B ⊆ Finset.Icc 1 (2 * N) := fun _ hs => hS (Finset.mem_sdiff.mp hs).1
  have hmodeB := norm_pow_sum_of_subset hB hz (interval_sum_zero hz1 hzN)
  rw [Nat.card_Icc, show 2 * N + 1 - 1 = 2 * N by omega, Nat.cast_mul, Nat.cast_ofNat] at hmodeB
  have hmodeRest : ‖∑ s ∈ S, (rest s : ℂ) * z ^ s‖ ≤ (A.card : ℝ) ^ 2 - 2 * B.card := by
    have hbound := norm_sum_le S (fun s => (rest s : ℂ) * z ^ s)
    simpa only [norm_mul, norm_pow, hz, one_pow, mul_one, Complex.norm_natCast, hrest_sum] using hbound
  have hnorm : ‖(∑ a ∈ A, z ^ a) ^ 2‖ ≤ (A.card : ℝ) ^ 2 + 4 * N - 4 * B.card := by
    rw [hsplit]
    have h := norm_add_le ((2 : ℂ) * ∑ s ∈ B, z ^ s) (∑ s ∈ S, (rest s : ℂ) * z ^ s)
    rw [norm_mul, Complex.norm_two] at h
    linarith only [h, hmodeB, hmodeRest]
  have hcount : S.card ≤ B.card + A.card := by
    have hD : D ⊆ S := by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_add.mpr ⟨a, ha, a, ha, rfl⟩
    have h := Finset.card_sdiff_of_subset hD
    have hDle : D.card ≤ A.card := Finset.card_image_le
    have hDS := Finset.card_le_card hD
    change B.card = S.card - D.card at h
    omega
  have hR : (S.card : ℝ) ≤ (B.card : ℝ) + A.card := by exact_mod_cast hcount
  rw [norm_pow] at hnorm
  change ‖∑ a ∈ A, z ^ a‖ ^ 2 ≤ (A.card : ℝ) ^ 2 + 4 * N - 4 * S.card + 4 * A.card
  linarith only [hnorm, hR]

end PikhurkoModes

namespace PikhurkoModes

private noncomputable def angle (N a : ℕ) : ℝ := Real.pi * (a : ℝ) / (N : ℝ)

private noncomputable def root (N t : ℕ) : ℂ :=
  Complex.exp ((angle N t : ℂ) * Complex.I)

private lemma root_pow_eq (N t a : ℕ) :
    root N t ^ a = Complex.exp (((t : ℝ) * angle N a : ℝ) * Complex.I) := by
  rw [root, ← Complex.exp_nat_mul]
  congr 1
  simp only [angle, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

private lemma root_norm (N t : ℕ) : ‖root N t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma root_pow_length {N : ℕ} (hN : 0 < N) (t : ℕ) : root N t ^ (2 * N) = 1 := by
  rw [root_pow_eq]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have ha : angle N (2 * N) = 2 * Real.pi := by
    simp only [angle, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  rw [ha]
  push_cast
  rw [show (t : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I =
    (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring, Complex.exp_nat_mul_two_pi_mul_I]

private lemma root_ne_one {N t : ℕ} (hN : 0 < N) (ht : 0 < t) (htN : t < 2 * N) :
    root N t ≠ 1 := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : root N t = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) /
      (((2 * N : ℕ) : ℂ))) := by
    rw [root]
    congr 1
    simp only [angle, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
      Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  rw [he]
  intro h
  have hd := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := t) (N := 2 * N) (by omega)).mp h
  exact (not_le_of_gt htN) (Nat.le_of_dvd ht hd)

private noncomputable def coefficient (A : Finset ℕ) (N t : ℕ) : ℂ :=
  ∑ a ∈ A, root N t ^ a

private noncomputable def squareBound (A : Finset ℕ) (N : ℕ) : ℝ :=
  (A.card : ℝ) ^ 2 + 4 * (N : ℝ) - 4 * (A + A).card + 4 * A.card

private lemma coefficient_le {A : Finset ℕ} {N t : ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hN : 0 < N) (ht : 0 < t) (htN : t < 2 * N) :
    ‖coefficient A N t‖ ≤ Real.sqrt (squareBound A N) := by
  have h := norm_square_le A N hA (root N t) (root_norm N t)
    (root_ne_one hN ht htN) (root_pow_length hN t)
  change ‖coefficient A N t‖ ^ 2 ≤ squareBound A N at h
  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans h)).mpr h

private lemma coefficient_sin (A : Finset ℕ) (N : ℕ) :
    (coefficient A N 1).im = ∑ a ∈ A, Real.sin (angle N a) := by
  simp only [coefficient, Complex.im_sum, root_pow_eq, Nat.cast_one, one_mul,
    Complex.exp_ofReal_mul_I_im]

private lemma coefficient_cos (A : Finset ℕ) (N n : ℕ) :
    (coefficient A N (2 * (n + 1))).re =
      ∑ a ∈ A, Real.cos (2 * ((n : ℝ) + 1) * angle N a) := by
  simp only [coefficient, Complex.re_sum, root_pow_eq, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one, Complex.exp_ofReal_mul_I_re]

private lemma wave_partial_lower (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hSum : HasSum w 1)
    {y : ℝ}
    (hWave : HasSum (fun n : ℕ => w n * Real.cos (2 * ((n : ℝ) + 1) * y))
      (1 - (Real.pi / 2) * |Real.sin y|))
    (hy : 0 ≤ Real.sin y) (M : ℕ) :
    (∑ n ∈ Finset.range M, w n) ≤ (Real.pi / 2) * Real.sin y +
      ∑ n ∈ Finset.range M, w n * Real.cos (2 * ((n : ℝ) + 1) * y) := by
  let f (n : ℕ) := w n * Real.cos (2 * ((n : ℝ) + 1) * y)
  have hf : HasSum f (1 - (Real.pi / 2) * |Real.sin y|) := hWave
  have htail : (∑' n, f (n + M)) ≤ ∑' n, w (n + M) :=
    Summable.tsum_le_tsum (fun n => by
      dsimp only [f]
      exact mul_le_of_le_one_right (hw _) (Real.cos_le_one _))
      ((summable_nat_add_iff _).mpr hf.summable) ((summable_nat_add_iff _).mpr hSum.summable)
  have hF := hf.summable.sum_add_tsum_nat_add M
  have hW := hSum.summable.sum_add_tsum_nat_add M
  rw [hf.tsum_eq, abs_of_nonneg hy] at hF
  rw [hSum.tsum_eq] at hW
  change (∑ n ∈ Finset.range M, w n) ≤
    (Real.pi / 2) * Real.sin y + ∑ n ∈ Finset.range M, f n
  linarith only [htail, hF, hW]

private lemma weighted_bound (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hSum : HasSum w 1)
    (hWave : ∀ y : ℝ, HasSum (fun n : ℕ => w n * Real.cos (2 * ((n : ℝ) + 1) * y))
      (1 - (Real.pi / 2) * |Real.sin y|))
    (A : Finset ℕ) {N M : ℕ} (hA : A ⊆ Finset.Icc 1 N) (hMN : M < N) :
    (∑ n ∈ Finset.range M, w n) * (A.card : ℝ) ≤
      (Real.pi / 2 + 1) * Real.sqrt (squareBound A N) := by
  have hN : 0 < N := by omega
  have hsin_nonneg (a : ℕ) (ha : a ∈ A) : 0 ≤ Real.sin (angle N a) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · unfold angle
      positivity
    · unfold angle
      apply (div_le_iff₀ (by exact_mod_cast hN)).mpr
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast (Finset.mem_Icc.mp (hA ha)).2) Real.pi_pos.le
  have hsum := Finset.sum_le_sum (fun a (ha : a ∈ A) =>
    wave_partial_lower w hw hSum (hWave (angle N a)) (hsin_nonneg a ha) M)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← coefficient_sin, Finset.sum_comm] at hsum
  simp_rw [← Finset.mul_sum, ← coefficient_cos] at hsum
  rw [mul_comm (A.card : ℝ)] at hsum
  have h1 : (coefficient A N 1).im ≤ Real.sqrt (squareBound A N) :=
    (Complex.im_le_norm _).trans (coefficient_le hA hN (by decide) (by omega))
  have h2 (n : ℕ) (hn : n ∈ Finset.range M) :
      (coefficient A N (2 * (n + 1))).re ≤ Real.sqrt (squareBound A N) :=
    (Complex.re_le_norm _).trans
      (coefficient_le hA hN (by omega) (by have := Finset.mem_range.mp hn; omega))
  have h3 : (∑ n ∈ Finset.range M, w n) ≤ 1 :=
    hSum.summable.sum_le_tsum _ (fun n _ => hw n) |>.trans_eq hSum.tsum_eq
  calc
    _ ≤ (Real.pi / 2) * (coefficient A N 1).im +
        ∑ n ∈ Finset.range M, w n * (coefficient A N (2 * (n + 1))).re := hsum
    _ ≤ (Real.pi / 2) * Real.sqrt (squareBound A N) +
        ∑ n ∈ Finset.range M, w n * Real.sqrt (squareBound A N) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
        (Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (h2 n hn) (hw n))
    _ = (Real.pi / 2 + (∑ n ∈ Finset.range M, w n)) * Real.sqrt (squareBound A N) := by
      rw [← Finset.sum_mul, add_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add (le_refl _) h3) (Real.sqrt_nonneg _)

end PikhurkoModes

namespace PikhurkoModes

private lemma normalized_squareBound (A : ℕ → Finset ℕ) {c : ℝ} (hc : 0 < c)
    (hk : (fun N ↦ (#(A N) : ℝ)) ~[atTop] (fun N ↦ c * Real.sqrt N))
    (hs : (fun N ↦ (#(A N + A N) : ℝ)) ~[atTop] (fun N ↦ ((#(A N)).choose 2 : ℝ))) :
    Tendsto (fun N : ℕ ↦ (#(A N) : ℝ) ^ 2 / (N : ℝ)) atTop (𝓝 (c ^ 2)) ∧
    Tendsto (fun N : ℕ ↦ squareBound (A N) N / (N : ℝ)) atTop (𝓝 (4 - c ^ 2)) := by
  have hSqrt : Tendsto (fun N : ℕ ↦ Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hK : Tendsto (fun N : ℕ ↦ (#(A N) : ℝ) / Real.sqrt N) atTop (𝓝 c) := by
    refine (((hk.div (IsEquivalent.refl (u := fun N : ℕ ↦ Real.sqrt N))).congr_right
      (w := fun _ ↦ c) ?_).tendsto_const)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact mul_div_cancel_right₀ _ ((Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne')
  have hK2 : Tendsto (fun N : ℕ ↦ (#(A N) : ℝ) ^ 2 / (N : ℝ)) atTop (𝓝 (c ^ 2)) := by
    convert hK.pow 2 using 1
    ext N
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hK0 : Tendsto (fun N : ℕ ↦ (#(A N) : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    convert hK.div_atTop hSqrt using 1
    ext N
    rw [div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hKC : Tendsto (fun N : ℕ ↦ c * Real.sqrt N) atTop atTop :=
    hSqrt.const_mul_atTop hc
  have hk1 := hk.sub_isLittleO (w := fun _ ↦ (1 : ℝ))
    (isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hKC)))
  have hC := ((hk.mul hk1).div (IsEquivalent.refl (u := fun _ : ℕ ↦ (2 : ℝ)))).congr_left
    (w := fun N ↦ ((#(A N)).choose 2 : ℝ))
    (Eventually.of_forall fun N ↦ by simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply,
      Nat.cast_choose_two])
  have hSum : Tendsto (fun N : ℕ ↦ (#(A N + A N) : ℝ) / N) atTop (𝓝 (c ^ 2 / 2)) := by
    refine (((hs.trans hC).div (IsEquivalent.refl (u := fun N : ℕ ↦ (N : ℝ)))).congr_right
      (w := fun _ ↦ c ^ 2 / 2) ?_).tendsto_const
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [show c * Real.sqrt N * (c * Real.sqrt N) = c ^ 2 * (Real.sqrt N * Real.sqrt N) by ring,
      Real.mul_self_sqrt (Nat.cast_nonneg N)]
    field_simp
  have hB : Tendsto (fun N : ℕ ↦ (#(A N) : ℝ) ^ 2 / N + 4 -
      4 * ((#(A N + A N) : ℝ) / N) + 4 * ((#(A N) : ℝ) / N)) atTop
      (𝓝 (c ^ 2 + 4 - 4 * (c ^ 2 / 2) + 4 * 0)) :=
    ((hK2.add tendsto_const_nhds).sub (hSum.const_mul 4)).add (hK0.const_mul 4)
  rw [show c ^ 2 + 4 - 4 * (c ^ 2 / 2) + 4 * 0 = 4 - c ^ 2 by ring] at hB
  refine ⟨hK2, hB.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [squareBound, add_div, sub_div, mul_div_assoc, mul_div_cancel_right₀ _ hN']

/-- The finite character bounds and the cosine expansion imply the asymptotic
upper bound for every quasi-Sidon constant. -/
theorem from_expansion (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hSum : HasSum w 1)
    (hWave : ∀ y : ℝ, HasSum (fun n : ℕ => w n * Real.cos (2 * ((n : ℝ) + 1) * y))
      (1 - (Real.pi / 2) * |Real.sin y|))
    (c : ℝ) (hc : Erdos840.IsQuasiSidonConstant c) :
    c ≤ (1 / 4 + 1 / (Real.pi + 2) ^ 2) ^ (-(1 : ℝ) / 2) := by
  by_cases hcp : 0 < c
  · obtain ⟨A, hA, hk, hs⟩ := hc
    obtain ⟨hK, hB⟩ := normalized_squareBound A hcp hk hs
    let D := Real.pi / 2 + 1
    let W (M : ℕ) := ∑ n ∈ Finset.range M, w n
    have hStep (M : ℕ) : W M ^ 2 * c ^ 2 ≤ D ^ 2 * (4 - c ^ 2) := by
      apply le_of_tendsto_of_tendsto (hK.const_mul (W M ^ 2)) (hB.const_mul (D ^ 2))
      filter_upwards [eventually_gt_atTop M] with N hN
      have hco := norm_square_le (A N) N (hA N) (root N 1) (root_norm N 1)
        (root_ne_one (by omega) (by decide) (by omega)) (root_pow_length (by omega) 1)
      have hSq0 : 0 ≤ squareBound (A N) N := (sq_nonneg _).trans hco
      have hW := weighted_bound w hw hSum hWave (A N) (hA N) hN
      have hW0 : 0 ≤ W M := Finset.sum_nonneg fun n _ => hw n
      have hsq := pow_le_pow_left₀ (mul_nonneg hW0 (Nat.cast_nonneg _)) hW 2
      change (W M * (#(A N) : ℝ)) ^ 2 ≤ (D * Real.sqrt (squareBound (A N) N)) ^ 2 at hsq
      rw [mul_pow, mul_pow, Real.sq_sqrt hSq0] at hsq
      change W M ^ 2 * ((#(A N) : ℝ) ^ 2 / (N : ℝ)) ≤
        D ^ 2 * (squareBound (A N) N / (N : ℝ))
      rw [← mul_div_assoc, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hsq (Nat.cast_nonneg _)
    have hW : Tendsto W atTop (𝓝 1) := hSum.tendsto_sum_nat
    have hL := (hW.pow 2).mul_const (c ^ 2)
    have hPi : c ^ 2 ≤ D ^ 2 * (4 - c ^ 2) := by
      simpa only [one_pow, one_mul] using le_of_tendsto hL (Eventually.of_forall hStep)
    let k : ℝ := 1 / 4 + 1 / (Real.pi + 2) ^ 2
    have hkpos : 0 < k := by dsimp only [k]; positivity
    have hp : c ^ 2 / (Real.pi + 2) ^ 2 ≤ 1 - c ^ 2 / 4 := by
      apply (div_le_iff₀ (by positivity)).mpr
      dsimp only [D] at hPi
      nlinarith only [hPi]
    have hcsq : c ^ 2 * k ≤ 1 := by
      calc
        _ = c ^ 2 / 4 + c ^ 2 / (Real.pi + 2) ^ 2 := by dsimp only [k]; ring
        _ ≤ 1 := by linarith only [hp]
    change c ≤ k ^ (-(1 : ℝ) / 2)
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hkpos.le, ← Real.sqrt_eq_rpow]
    apply (sq_le_sq₀ hcp.le (by positivity)).mp
    rw [inv_pow, Real.sq_sqrt hkpos.le]
    simpa only [one_div] using (le_div_iff₀ hkpos).mpr hcsq
  · exact (le_of_not_gt hcp).trans (by positivity)

end PikhurkoModes

theorem OMA.solution : type_of% @Erdos840.erdos_840.variants.pikhurko := by
  intro c hc
  exact PikhurkoModes.from_expansion PikhurkoSeries.weight PikhurkoSeries.weight_nonneg
    PikhurkoSeries.weight_hasSum PikhurkoSeries.cosine_hasSum c hc