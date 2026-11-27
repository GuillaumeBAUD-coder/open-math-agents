import OMAReductions.R_Erdos233_erdos_233_variants_upper_bound_R1_H2_R1
/-! A mean-square bound for waves with real frequencies grouped in unit bins. -/

-- Credit: @MrSeizy
-- Gaussian integral and logarithmic substitution adapted from @senamakel,
-- Erdos233.erdos_233.variants.upper_bound.R1.H2, mean_value and mean_square.
open Complex MeasureTheory Filter
open scoped Real
namespace OMA.BinnedWaves

private noncomputable def wave {ι : Type} (γ : ι → ℝ) (c : ι → ℂ) (u : ℝ) :=
  ∑' i, c i * exp (((γ i * u : ℝ) : ℂ) * I)

private lemma norm_wave_term {ι : Type} (γ : ι → ℝ) (c : ι → ℂ) (i : ι) (u : ℝ) :
    ‖c i * exp (((γ i * u : ℝ) : ℂ) * I)‖ = ‖c i‖ := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]

private lemma continuous_wave {ι : Type} (γ : ι → ℝ) {c : ι → ℂ} (hc : Summable fun i => ‖c i‖) :
    Continuous (wave γ c) :=
  continuous_tsum (fun i => by fun_prop) hc (fun i u => (norm_wave_term γ c i u).le)

private lemma exp_gauss_le (τ : ℝ) :
    Real.exp (1 - τ ^ 2 / 4) ≤ 2 * Real.exp 1 / (1 + τ ^ 2) := by
  have hD : 0 < 1 + τ ^ 2 := by positivity
  have hx : 0 ≤ τ ^ 2 / 4 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have h2 : 1 + τ ^ 2 ≤ 2 * Real.exp (τ ^ 2 / 4) := by nlinarith [sq_nonneg (τ ^ 2 / 4 - 1)]
  rw [le_div_iff₀ hD, Real.exp_sub]
  have hpos := Real.exp_pos (τ ^ 2 / 4)
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [Real.exp_pos 1]
private lemma gauss_bound (s τ : ℝ) :
    ‖∫ u : ℝ, cexp (-1 * (u : ℂ) ^ 2 + (2 * s + τ * I) * u + (1 - s ^ 2))‖ ≤
      2 * Real.exp 1 * Real.pi ^ (1 / 2 : ℝ) / (1 + τ ^ 2) := by
  rw [integral_cexp_quadratic (by simp)]
  have h1 : (Real.pi : ℂ) / -(-1) = ((Real.pi : ℝ) : ℂ) := by simp
  have h2 : ((1 : ℂ) - s ^ 2) - (2 * s + τ * I) ^ 2 / (4 * -1) =
      ((1 - τ ^ 2 / 4 : ℝ) : ℂ) + ((s * τ : ℝ) : ℂ) * I := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [h1, h2, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos, norm_exp]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  have : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  rw [this, mul_comm (2 * Real.exp 1), mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa [mul_div_assoc] using exp_gauss_le τ)
    (by positivity)
private lemma wave_identity (s γ γ' u : ℝ) :
    ((Real.exp 1 * Real.exp (-(u - s) ^ 2) : ℝ) : ℂ) *
        (exp (((γ * u : ℝ) : ℂ) * I) * (starRingEnd ℂ) (exp (((γ' * u : ℝ) : ℂ) * I))) =
      cexp (-1 * (u : ℂ) ^ 2 + (2 * s + ((γ - γ' : ℝ) : ℂ) * I) * u + (1 - s ^ 2)) := by
  rw [← exp_conj]
  push_cast
  simp only [map_mul, conj_ofReal, conj_I]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

private lemma gaussian_mean {ι : Type} [Countable ι] (γ : ι → ℝ) (c : ι → ℂ)
    (hc : Summable fun i => ‖c i‖) (U : ℝ) :
    ∫ u in U..U + 2, ‖wave γ c u‖ ^ 2 ≤
      (2 * Real.exp 1 * Real.pi ^ (1 / 2 : ℝ)) *
        ∑' p : ι × ι, ‖c p.1‖ * ‖c p.2‖ / (1 + (γ p.1 - γ p.2) ^ 2) := by
  set B : ℝ := 2 * Real.exp 1 * Real.pi ^ (1 / 2 : ℝ) with hBdef
  have hB : 0 < B := by positivity
  set s : ℝ := U + 1 with hs
  set W : ℝ → ℝ := fun u => Real.exp 1 * Real.exp (-(u - s) ^ 2) with hW
  set f := wave γ c with hf
  set A : ι → ℝ := fun ρ => ‖c ρ‖ with hA
  have hA0 : ∀ ρ, 0 ≤ A ρ := fun ρ => by positivity
  set S : ℝ := ∑' ρ, A ρ
  have hfb : ∀ u, ‖f u‖ ≤ S := fun u =>
    tsum_of_norm_bounded hc.hasSum (fun ρ => (norm_wave_term γ c ρ u).le)
  have hfc : Continuous f := continuous_wave γ hc
  have hWc : Continuous W := by fun_prop
  have hW0 : ∀ u, 0 ≤ W u := fun u => by positivity
  have hWint : Integrable W := by
    have := ((integrable_exp_neg_mul_sq one_pos).comp_sub_right s).const_mul (Real.exp 1)
    simpa [hW] using this
  have hWf : Integrable (fun u => W u * ‖f u‖ ^ 2) := by
    refine (hWint.mul_const (S ^ 2)).mono' (by fun_prop) (ae_of_all _ fun u => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hfb u) 2) (hW0 u)
  have step1 : ∫ u in U..U + 2, ‖f u‖ ^ 2 ≤ ∫ u, W u * ‖f u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    calc ∫ u in Set.Ioc U (U + 2), ‖f u‖ ^ 2
        ≤ ∫ u in Set.Ioc U (U + 2), W u * ‖f u‖ ^ 2 := by
          refine setIntegral_mono_on ?_ hWf.integrableOn measurableSet_Ioc fun u hu => ?_
          · exact ((hfc.norm.pow 2).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
          · have h1 : 1 ≤ W u := by
              simp only [hW, ← Real.exp_add]
              apply Real.one_le_exp
              nlinarith [hu.1, hu.2]
            nlinarith [sq_nonneg ‖f u‖]
      _ ≤ ∫ u, W u * ‖f u‖ ^ 2 :=
          setIntegral_le_integral hWf (ae_of_all _ fun u => by positivity)
  set G : ι × ι → ℝ → ℂ := fun p u =>
    (c p.1 * (starRingEnd ℂ) (c p.2)) *
      (((W u : ℝ) : ℂ) * (exp (((γ p.1 * u : ℝ) : ℂ) * I) *
        (starRingEnd ℂ) (exp (((γ p.2 * u : ℝ) : ℂ) * I)))) with hG
  clear_value G
  have hGq : ∀ p u, G p u = (c p.1 * (starRingEnd ℂ) (c p.2)) *
      cexp (-1 * (u : ℂ) ^ 2 + (2 * s + ((γ p.1 - γ p.2 : ℝ) : ℂ) * I) * u
        + (1 - s ^ 2)) := fun p u => by
    simp only [hG, hW]; rw [wave_identity]
  have hGnorm : ∀ p u, ‖G p u‖ = A p.1 * A p.2 * W u := fun p u => by
    simp only [hG, hA, norm_mul, RCLike.norm_conj, norm_exp_ofReal_mul_I,
      Complex.norm_real, Real.norm_of_nonneg (hW0 u)]
    ring
  have hpt : ∀ u, (((W u * ‖f u‖ ^ 2 : ℝ)) : ℂ) = ∑' p, G p u := fun u => by
    have hn : ∀ u ρ, ‖c ρ * exp (((γ ρ * u : ℝ) : ℂ) * I)‖ = A ρ :=
      fun u ρ => norm_wave_term γ c ρ u
    have hn' : ∀ u ρ, ‖(starRingEnd ℂ) (c ρ * exp (((γ ρ * u : ℝ) : ℂ) * I))‖
        = A ρ := fun u ρ => by rw [RCLike.norm_conj, hn]
    have hsq : (((‖f u‖ ^ 2 : ℝ)) : ℂ) = f u * (starRingEnd ℂ) (f u) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [ofReal_mul, hsq, hf, wave, conj_tsum,
      tsum_mul_tsum_of_summable_norm (by simpa only [hn u] using hc)
        (by simpa only [hn' u] using hc), ← tsum_mul_left]
    congr 1
    funext p
    simp only [hG, map_mul]
    ring
  have hGint : ∀ p, Integrable (G p) := fun p => by
    have := (integrable_cexp_quadratic (b := 1) (by simp)
      (2 * s + ((γ p.1 - γ p.2 : ℝ) : ℂ) * I) (1 - s ^ 2)).const_mul
      (c p.1 * (starRingEnd ℂ) (c p.2))
    refine this.congr (ae_of_all _ fun u => ?_)
    simp only [hGq]
  have hGsum : Summable fun p => ∫ u, ‖G p u‖ := by
    simp only [hGnorm]
    simp only [integral_const_mul]
    exact (hc.mul_of_nonneg hc (fun ρ => hA0 ρ) (fun ρ => hA0 ρ)).mul_right _
  set bnd : ι × ι → ℝ := fun p =>
    B * (A p.1 * A p.2) / (1 + (γ p.1 - γ p.2) ^ 2) with hbnd
  clear_value bnd
  have hGbound : ∀ p, ‖∫ u, G p u‖ ≤ bnd p := fun p => by
    simp only [hGq]
    rw [integral_const_mul, norm_mul]
    have hn : ‖c p.1 * (starRingEnd ℂ) (c p.2)‖ =
        A p.1 * A p.2 := by
      simp only [hA, norm_mul, RCLike.norm_conj]
    rw [hn]
    calc A p.1 * A p.2 * ‖_‖ ≤ A p.1 * A p.2 * (B / (1 + (γ p.1 - γ p.2) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hA0 _) (hA0 _))
          rw [hBdef]; exact gauss_bound s _
      _ = bnd p := by simp only [hbnd]; ring
  have hbnd_s : Summable bnd := by
    apply Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      ((hc.mul_of_nonneg hc (fun i => norm_nonneg _) (fun i => norm_nonneg _)).mul_left B)
    · rw [hbnd]
      positivity
    · rw [hbnd]
      exact div_le_self (by positivity) (by nlinarith [sq_nonneg (γ p.1 - γ p.2)])
  have hint0 : 0 ≤ ∫ u, W u * ‖f u‖ ^ 2 := integral_nonneg fun u => by positivity
  have step4 : ∫ u, W u * ‖f u‖ ^ 2 ≤ ∑' p, bnd p := by
    have e1 : ∫ u, W u * ‖f u‖ ^ 2 = ‖((∫ u, W u * ‖f u‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hint0]
    rw [e1, ← integral_complex_ofReal]
    simp only [hpt]
    rw [← integral_tsum_of_summable_integral_norm hGint hGsum]
    exact tsum_of_norm_bounded hbnd_s.hasSum hGbound
  apply (step1.trans step4).trans_eq
  rw [← tsum_mul_left]
  exact tsum_congr fun p => by rw [hbnd]; ring


private noncomputable def kernel (z : ℤ) : ℝ := 1 / (1 + (z : ℝ) ^ 2)

private lemma kernel_bounds (z : ℤ) : 0 ≤ kernel z ∧ kernel z ≤ 1 := by
  unfold kernel
  exact ⟨by positivity, (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (z : ℝ)])⟩

private lemma kernel_sum : Summable kernel := by
  classical
  apply Summable.of_nonneg_of_le (fun z => (kernel_bounds z).1) (f := fun z : ℤ =>
    (if z = 0 then (1 : ℝ) else 0) + 1 / (z : ℝ) ^ 2)
  · intro z
    by_cases hz : z = 0
    · simp [hz, kernel]
    · simp only [hz, if_false, zero_add, kernel]
      apply one_div_le_one_div_of_le
      · exact sq_pos_of_ne_zero (by exact_mod_cast hz)
      · linarith
  · exact (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable.add (Real.summable_one_div_int_pow.mpr (by decide))

private lemma row {k : ℕ} :
    Summable (fun l : ℕ => kernel ((k : ℤ) - l)) ∧
    ∑' l : ℕ, kernel ((k : ℤ) - l) ≤ ∑' z : ℤ, kernel z := by
  have hi : Function.Injective (fun l : ℕ => (k : ℤ) - l) := by
    intro a b h
    exact_mod_cast (sub_right_inj.mp h : (a : ℤ) = b)
  have hs := kernel_sum.comp_injective hi
  exact ⟨hs, hs.tsum_le_tsum_of_inj _ hi (fun z _ => (kernel_bounds z).1)
    (fun _ => le_rfl) kernel_sum⟩

-- Taking absolute values contracts distances, and flooring changes the difference by at most one.
private lemma kernel_floor (u v : ℝ) :
    1 / (1 + (u - v) ^ 2) ≤ 3 * kernel ((⌊|u|⌋₊ : ℤ) - ⌊|v|⌋₊) := by
  have h1 := Nat.floor_le (abs_nonneg u)
  have h2 := Nat.lt_floor_add_one |u|
  have h3 := Nat.floor_le (abs_nonneg v)
  have h4 := Nat.lt_floor_add_one |v|
  have hd := abs_abs_sub_abs_le_abs_sub u v
  have hdiff : |(⌊|u|⌋₊ : ℝ) - (⌊|v|⌋₊ : ℝ)| ≤ |u-v| + 1 := by
    have hh := abs_le.mp hd
    apply abs_le.mpr
    constructor <;> linarith [hh.1, hh.2]
  have hp := sq_le_sq' (by linarith [abs_nonneg (u-v), abs_nonneg ((⌊|u|⌋₊ : ℝ) - (⌊|v|⌋₊ : ℝ))]) hdiff
  unfold kernel
  push_cast
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [sq_abs] at hp
  nlinarith [sq_abs (u-v), sq_nonneg (|u-v| - 1)]

private noncomputable def mass {ι : Type} (b : ι → ℕ) (A : ι → ℝ) (k : ℕ) :=
  ∑' i : b ⁻¹' {k}, A i

private lemma regroup {ι : Type} {A : ι → ℝ} (b : ι → ℕ) (f : ℕ → ℝ)
    (h : Summable fun i => A i * f (b i)) :
    ∑' i, A i * f (b i) = ∑' k, mass b A k * f k := by
  rw [← (h.hasSum.tsum_fiberwise b).tsum_eq]
  apply tsum_congr
  intro k
  rw [mass, ← tsum_mul_right]
  exact tsum_congr fun i => by rw [show b i = k from i.property]

private lemma pair_expand {ι : Type} {A : ι → ℝ} (hA : Summable A) (h0 : ∀ i, 0 ≤ A i)
    (K : ι → ι → ℝ) (hK : ∀ i j, 0 ≤ K i j ∧ K i j ≤ 1) :
    Summable (fun p : ι × ι => (A p.1 * A p.2) * K p.1 p.2) ∧
    ∑' p : ι × ι, (A p.1 * A p.2) * K p.1 p.2 =
      ∑' i, A i * ∑' j, A j * K i j := by
  have hs : Summable (fun p : ι × ι => (A p.1 * A p.2) * K p.1 p.2) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (mul_nonneg (h0 _) (h0 _)) (hK _ _).1)
      (fun p => mul_le_of_le_one_right (mul_nonneg (h0 _) (h0 _)) (hK _ _).2)
      (hA.mul_of_nonneg hA h0 h0)
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod' (fun i => hs.prod_factor i)]
  exact tsum_congr fun i => by rw [← tsum_mul_left]; simp only [mul_assoc]

private lemma rows_control (M : ℕ → ℝ) (hM : Summable M) (h0 : ∀ k, 0 ≤ M k) :
    let H : ℕ × ℕ → ℝ := fun p => M p.1 ^ 2 * kernel ((p.1 : ℤ) - p.2)
    Summable H ∧ ∑' p, H p ≤ (∑' k, M k ^ 2) * ∑' z : ℤ, kernel z := by
  dsimp only
  let D := ∑' z : ℤ, kernel z
  let H : ℕ × ℕ → ℝ := fun p => M p.1 ^ 2 * kernel ((p.1 : ℤ) - p.2)
  have hH0 : ∀ p, 0 ≤ H p := fun p => mul_nonneg (sq_nonneg _) (kernel_bounds _).1
  have hs2 : Summable (fun k => M k ^ 2) := by
    apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _ (hM.mul_right (∑' k, M k))
    intro k
    rw [sq]
    exact mul_le_mul_of_nonneg_left (hM.le_tsum k (fun l _ => h0 l)) (h0 k)
  have hr (k : ℕ) : Summable (fun l => H (k,l)) := (row (k := k)).1.mul_left (M k ^ 2)
  have hb (k : ℕ) : ∑' l, H (k,l) ≤ M k ^ 2 * D := by
    simp only [H, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (row (k := k)).2 (sq_nonneg _)
  have hH : Summable H := (summable_prod_of_nonneg hH0).2 ⟨hr,
    Summable.of_nonneg_of_le (fun k => tsum_nonneg fun l => hH0 (k,l)) hb (hs2.mul_right D)⟩
  refine ⟨hH, ?_⟩
  change ∑' p, H p ≤ (∑' k, M k ^ 2) * D
  rw [hH.tsum_prod' hr, ← tsum_mul_right]
  exact hH.prod.tsum_le_tsum hb (hs2.mul_right D)

-- Symmetrize the two bin masses and sum the resulting squared terms along rows.
private lemma schur (M : ℕ → ℝ) (hM : Summable M) (h0 : ∀ k, 0 ≤ M k) :
    ∑' p : ℕ × ℕ, M p.1 * M p.2 * kernel ((p.1 : ℤ) - p.2) ≤
      (∑' z : ℤ, kernel z) * ∑' k, M k ^ 2 := by
  let D := ∑' z : ℤ, kernel z
  let H : ℕ × ℕ → ℝ := fun p => M p.1 ^ 2 * kernel ((p.1 : ℤ) - p.2)
  obtain ⟨hH,hbound⟩ := rows_control M hM h0
  have hswap : Summable (fun p : ℕ × ℕ => H p.swap) := hH.prod_symm
  have hpair := (pair_expand hM h0 (fun k l => kernel ((k : ℤ) - l))
    (fun k l => kernel_bounds _)).1
  have hle (p : ℕ × ℕ) : M p.1 * M p.2 * kernel ((p.1 : ℤ) - p.2) ≤
      (H p + H p.swap) * (1 / 2) := by
    obtain ⟨k,l⟩ := p
    have he : kernel ((l : ℤ) - k) = kernel ((k : ℤ) - l) := by
      unfold kernel
      push_cast
      ring
    change M k * M l * kernel ((k : ℤ) - l) ≤
      (M k ^ 2 * kernel ((k : ℤ) - l) + M l ^ 2 * kernel ((l : ℤ) - k)) * (1 / 2)
    rw [he]
    nlinarith only [mul_nonneg (sq_nonneg (M k - M l)) (kernel_bounds ((k : ℤ) - l)).1]
  calc
    _ ≤ ∑' p : ℕ × ℕ, (H p + H p.swap) * (1 / 2) :=
      hpair.tsum_le_tsum hle ((hH.add hswap).mul_right _)
    _ = ∑' p, H p := by
      have e : (∑' p : ℕ × ℕ, H p.swap) = ∑' p, H p := (Equiv.prodComm ℕ ℕ).tsum_eq H
      rw [tsum_mul_right, hH.tsum_add hswap, e]
      ring
    _ ≤ (∑' k, M k ^ 2) * D := hbound
    _ = _ := mul_comm _ _

private lemma binned_kernel {ι : Type} (γ : ι → ℝ) (A : ι → ℝ) (hA : Summable A)
    (h0 : ∀ i, 0 ≤ A i) :
    ∑' p : ι × ι, A p.1 * A p.2 / (1 + (γ p.1 - γ p.2) ^ 2) ≤
      3 * (∑' z : ℤ, kernel z) * ∑' k, mass (fun i => ⌊|γ i|⌋₊) A k ^ 2 := by
  let b := fun i => ⌊|γ i|⌋₊
  let M := mass b A
  let K := fun k l : ℕ => kernel ((k : ℤ) - l)
  have hM : Summable M := (hA.hasSum.tsum_fiberwise b).summable
  have hM0 : ∀ k, 0 ≤ M k := fun k => tsum_nonneg fun i => h0 i
  have hb := pair_expand hA h0 (fun i j => K (b i) (b j)) (fun _ _ => kernel_bounds _)
  have hm := pair_expand hM hM0 K (fun _ _ => kernel_bounds _)
  have hi (k : ℕ) : Summable fun j => A j * K k (b j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (h0 _) (kernel_bounds _).1)
      (fun j => mul_le_of_le_one_right (h0 _) (kernel_bounds _).2) hA
  let f := fun k => ∑' j, A j * K k (b j)
  have hf (i : ι) : 0 ≤ f (b i) := tsum_nonneg fun j => mul_nonneg (h0 _) (kernel_bounds _).1
  have hfs : Summable fun i => A i * f (b i) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (h0 _) (hf i)) _ (hA.mul_right (∑' j, A j))
    intro i
    apply mul_le_mul_of_nonneg_left _ (h0 _)
    exact (hi _).tsum_le_tsum (fun j => mul_le_of_le_one_right (h0 _) (kernel_bounds _).2) hA
  have he : ∑' p : ι × ι, A p.1 * A p.2 * K (b p.1) (b p.2) =
      ∑' p : ℕ × ℕ, M p.1 * M p.2 * K p.1 p.2 := by
    rw [hb.2, hm.2, regroup b f hfs]
    exact tsum_congr fun k => congrArg (M k * ·) (regroup b (K k) (hi k))
  have ha' : Summable fun p : ι × ι => A p.1 * A p.2 / (1 + (γ p.1 - γ p.2) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun p => div_nonneg (mul_nonneg (h0 _) (h0 _)) (by positivity))
      _ (hA.mul_of_nonneg hA h0 h0)
    exact fun p => div_le_self (mul_nonneg (h0 _) (h0 _)) (by nlinarith [sq_nonneg (γ p.1 - γ p.2)])
  calc
    _ ≤ ∑' p : ι × ι, 3 * (A p.1 * A p.2 * K (b p.1) (b p.2)) := by
      apply ha'.tsum_le_tsum _ (hb.1.mul_left 3)
      intro p
      have h := mul_le_mul_of_nonneg_left (kernel_floor (γ p.1) (γ p.2)) (mul_nonneg (h0 p.1) (h0 p.2))
      simpa only [div_eq_mul_inv, one_mul, mul_left_comm, mul_assoc, mul_comm] using h
    _ = 3 * ∑' p : ℕ × ℕ, M p.1 * M p.2 * K p.1 p.2 := by rw [tsum_mul_left, he]
    _ ≤ 3 * ((∑' z : ℤ, kernel z) * ∑' k, M k ^ 2) :=
      mul_le_mul_of_nonneg_left (schur M hM hM0) (by norm_num)
    _ = _ := by dsimp [M,b]; ring

open intervalIntegral in
private lemma log_substitution (F : ℝ → ℂ) (hFc : Continuous F) (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun y => (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2) volume x (4*x) ∧
    ∫ y in x..4*x, (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2 ≤
      256*x^4 * ∫ u in Real.log x..Real.log x+2, ‖F u‖^2 := by
  have hx0 : 0 < x := by linarith
  have hx4 : x ≤ 4 * x := by linarith
  have hlogc : ContinuousOn Real.log (Set.Icc x (4 * x)) :=
    Real.continuousOn_log.mono fun y hy => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (lt_of_lt_of_le hx0 hy.1).ne'
  have hG : ContinuousOn (fun y => ‖F (Real.log y)‖ ^ 2) (Set.Icc x (4 * x)) :=
    ((hFc.comp_continuousOn hlogc).norm).pow 2
  have hpow : ContinuousOn (fun y : ℝ => y ^ (3 / 2 : ℝ)) (Set.Icc x (4 * x)) :=
    fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).continuousWithinAt
  have hInt : ContinuousOn (fun y => (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2)
      (Set.Icc x (4 * x)) :=
    (hpow.mul ((hFc.comp_continuousOn hlogc).norm)).pow 2
  have hII : IntervalIntegrable (fun y => (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2)
      volume x (4 * x) :=
    (hInt.mono (by rw [Set.uIcc_of_le hx4])).intervalIntegrable
  refine ⟨hII, ?_⟩
  have hGI : IntervalIntegrable (fun y => ‖F (Real.log y)‖ ^ 2) volume x (4 * x) :=
    (hG.mono (by rw [Set.uIcc_of_le hx4])).intervalIntegrable
  have h1 : ∫ y in x..4 * x, (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2
      ≤ ∫ y in x..4 * x, 64 * x ^ 3 * ‖F (Real.log y)‖ ^ 2 := by
    refine integral_mono_on hx4 hII (hGI.const_mul _) fun y hy => ?_
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have e : (y ^ (3 / 2 : ℝ)) ^ 2 = y ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
    rw [mul_pow, e]
    have : y ^ 3 ≤ (4 * x) ^ 3 := pow_le_pow_left₀ hy0 hy.2 3
    have h0 : 0 ≤ ‖F (Real.log y)‖ ^ 2 := by positivity
    nlinarith
  have h2 : ∫ y in x..4 * x, ‖F (Real.log y)‖ ^ 2
      = ∫ u in Real.log x..Real.log (4 * x), ‖F u‖ ^ 2 * Real.exp u := by
    have hsub := integral_comp_mul_deriv' (a := Real.log x) (b := Real.log (4 * x))
      (f := Real.exp) (f' := Real.exp) (g := fun y => ‖F (Real.log y)‖ ^ 2)
      (fun u _ => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn (by
        refine ContinuousOn.pow (ContinuousOn.norm (hFc.comp_continuousOn ?_)) 2
        exact Real.continuousOn_log.mono fun y hy => by
          obtain ⟨u, -, rfl⟩ := hy
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact (Real.exp_pos u).ne')
    rw [Real.exp_log hx0, Real.exp_log (by linarith)] at hsub
    rw [← hsub]
    refine integral_congr fun u _ => ?_
    simp [Function.comp, Real.log_exp]
  have hlog4 : Real.log (4 * x) = Real.log x + Real.log 4 := by
    rw [Real.log_mul (by norm_num) hx0.ne']; ring
  have hlog4' : Real.log 4 < 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hab : Real.log x ≤ Real.log (4 * x) := by rw [hlog4]; linarith
  have hFI : ∀ a b : ℝ, IntervalIntegrable (fun u => ‖F u‖ ^ 2) volume a b := fun a b =>
    ((hFc.norm).pow 2).intervalIntegrable _ _
  have h3 : ∫ u in Real.log x..Real.log (4 * x), ‖F u‖ ^ 2 * Real.exp u
      ≤ 4 * x * ∫ u in Real.log x..Real.log x + 2, ‖F u‖ ^ 2 := by
    calc ∫ u in Real.log x..Real.log (4 * x), ‖F u‖ ^ 2 * Real.exp u
        ≤ ∫ u in Real.log x..Real.log (4 * x), 4 * x * ‖F u‖ ^ 2 := by
          refine integral_mono_on hab
            ((((hFc.norm).pow 2).mul Real.continuous_exp).intervalIntegrable _ _)
            ((hFI _ _).const_mul _) fun u hu => ?_
          have : Real.exp u ≤ 4 * x := by
            calc Real.exp u ≤ Real.exp (Real.log (4 * x)) := Real.exp_le_exp.2 hu.2
              _ = 4 * x := Real.exp_log (by linarith)
          have h0 : 0 ≤ ‖F u‖ ^ 2 := by positivity
          nlinarith
      _ = 4 * x * ∫ u in Real.log x..Real.log (4 * x), ‖F u‖ ^ 2 := integral_const_mul _ _
      _ ≤ 4 * x * ∫ u in Real.log x..Real.log x + 2, ‖F u‖ ^ 2 := by
          gcongr
          exact integral_mono_interval le_rfl hab (by rw [hlog4]; linarith)
            (Filter.Eventually.of_forall fun u => by positivity) (hFI _ _)
  calc ∫ y in x..4 * x, (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2
      ≤ ∫ y in x..4 * x, 64 * x ^ 3 * ‖F (Real.log y)‖ ^ 2 := h1
    _ = 64 * x ^ 3 * ∫ y in x..4 * x, ‖F (Real.log y)‖ ^ 2 := integral_const_mul _ _
    _ ≤ 64 * x ^ 3 * (4 * x * ∫ u in Real.log x..Real.log x + 2, ‖F u‖ ^ 2) := by
        rw [h2]; gcongr
    _ = _ := by ring

private lemma amplitude {ι : Type} (γ : ι → ℝ) (c : ι → ℂ) {y : ℝ} (hy : 0 < y) :
    ‖∑' i, c i * (y : ℂ) ^ ((3 / 2 : ℂ) + (γ i : ℂ) * I)‖ =
      y ^ (3 / 2 : ℝ) * ‖wave γ c (Real.log y)‖ := by
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  have he (i : ι) : (y : ℂ) ^ ((3 / 2 : ℂ) + (γ i : ℂ) * I) =
      ((y ^ (3 / 2 : ℝ) : ℝ) : ℂ) * exp (((γ i * Real.log y : ℝ) : ℂ) * I) := by
    rw [cpow_add _ _ hyc, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_cpow hy.le]
    congr 1
    rw [cpow_def_of_ne_zero hyc, ← ofReal_log hy.le]
    congr 1
    push_cast
    ring
  have h : (∑' i, c i * (y : ℂ) ^ ((3 / 2 : ℂ) + (γ i : ℂ) * I)) =
      ((y ^ (3 / 2 : ℝ) : ℝ) : ℂ) * wave γ c (Real.log y) := by
    unfold wave
    rw [← tsum_mul_left]
    exact tsum_congr fun i => by rw [he]; ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _)]

private lemma mass_bin {ι : Type} (γ : ι → ℝ) (a : ι → ℂ) (k : ℕ) :
    mass (fun i => ⌊|γ i|⌋₊) (fun i => ‖a i‖) k =
      ∑' i, if (k : ℝ) ≤ |γ i| ∧ |γ i| < (k : ℝ) + 1 then ‖a i‖ else 0 := by
  classical
  rw [mass, tsum_subtype _ (fun i => ‖a i‖)]
  apply tsum_congr
  intro i
  simp [Set.indicator, Nat.floor_eq_iff (abs_nonneg (γ i))]

end OMA.BinnedWaves

open OMA.BinnedWaves in
theorem OMA.solution : OMA.R_Erdos233_erdos_233_variants_upper_bound_R1_H2_R1.H2 := by
  classical
  let B := 2 * Real.exp 1 * Real.pi ^ (1 / 2 : ℝ)
  let D := ∑' z : ℤ, kernel z
  have hD : 0 < D := by
    have h := kernel_sum.le_tsum 0 (fun z _ => (kernel_bounds z).1)
    exact lt_of_lt_of_le (by norm_num [kernel] : 0 < kernel 0) h
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨256 * B * (3 * D), by positivity, ?_⟩
  intro ι γ a ha x hx
  let S := Function.support a
  have : Countable S := ha.of_norm.countable_support.to_subtype
  let g : S → ℝ := fun i => γ i
  let c : S → ℂ := fun i => a i
  have hc : Summable fun i => ‖c i‖ := ha.subtype S
  obtain ⟨hint,hsub⟩ := log_substitution (wave g c) (continuous_wave g hc) x hx
  have hsupp (y : ℝ) : (∑' i : S, c i * (y : ℂ) ^ ((3/2 : ℂ) + (g i : ℂ) * I)) =
      ∑' i, a i * (y : ℂ) ^ ((3/2 : ℂ) + (γ i : ℂ) * I) := by
    apply tsum_subtype_eq_of_support_subset (s := S) (f := fun i => a i * (y : ℂ) ^ ((3/2 : ℂ) + (γ i : ℂ) * I))
    intro i h hi
    apply h
    simp [hi]
  have he : Set.EqOn (fun y : ℝ => ‖∑' i, a i * (y : ℂ) ^ ((3/2 : ℂ) + (γ i : ℂ) * I)‖ ^ 2)
      (fun y => (y ^ (3/2 : ℝ) * ‖wave g c (Real.log y)‖) ^ 2) (Set.uIcc x (4*x)) := by
    intro y hy
    rw [Set.uIcc_of_le (by linarith)] at hy
    change ‖_‖ ^ 2 = _ ^ 2
    rw [← hsupp, amplitude g c (by linarith [hy.1] : 0 < y)]
  refine ⟨hint.congr (he.symm.mono Set.uIoc_subset_uIcc), ?_⟩
  rw [intervalIntegral.integral_congr he]
  have hG := gaussian_mean g c hc (Real.log x)
  have hK := binned_kernel g (fun i => ‖c i‖) hc (fun i => norm_nonneg _)
  have hmass (k : ℕ) : mass (fun i => ⌊|g i|⌋₊) (fun i => ‖c i‖) k =
      ∑' i, if (k : ℝ) ≤ |γ i| ∧ |γ i| < (k : ℝ) + 1 then ‖a i‖ else 0 := by
    rw [mass_bin]
    apply tsum_subtype_eq_of_support_subset (s := S)
      (f := fun i => if (k : ℝ) ≤ |γ i| ∧ |γ i| < (k : ℝ) + 1 then ‖a i‖ else 0)
    intro i h hi
    apply h
    simp [hi]
  simp only [hmass] at hK
  have hw := hG.trans (mul_le_mul_of_nonneg_left hK hB.le)
  apply hsub.trans
  exact (mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 256*x^4)).trans_eq (by dsimp [B,D]; ring)
