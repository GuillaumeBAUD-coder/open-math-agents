import FormalConjectures.ErdosProblems.«840»

/-! A finite Fourier proof of Pikhurko’s upper bound for quasi-Sidon sets. -/

open Finset Filter Asymptotics
open scoped Pointwise

-- Credit: @MrSeizy
namespace OMA

-- In a singleton sum fiber the unique ordered pair must be diagonal.
-- Subtracting the constant function 2 bounds the square of each nontrivial Fourier sum.
private lemma spectrum {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (hzN : z ^ (2 * N) = 1) :
    ‖∑ a ∈ A, z ^ a‖ ^ 2 ≤ (#A : ℝ)^2 + 4*N - 4*↑(#(A+A)) + 2*↑(#A) := by
  classical
  let T := Icc 1 (2*N)
  let P := A ×ˢ A
  let f := fun p : ℕ × ℕ ↦ p.1 + p.2
  let r := fun t ↦ #(P.filter (fun p ↦ f p = t))
  let B := A.image (fun a ↦ a+a)
  have hm : ∀ p ∈ P, f p ∈ T := by
    rintro ⟨a,b⟩ hp
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    have := mem_Icc.mp (hA ha)
    have := mem_Icc.mp (hA hb)
    apply mem_Icc.mpr
    dsimp [f]
    omega
  have hs : A+A ⊆ T := by
    rintro t ht
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp ht
    exact hm (a,b) (mem_product.mpr ⟨ha,hb⟩)
  have hpoint (t : ℕ) :
      |(r t : ℝ)-2| ≤ ↑(r t) + 2 - 4*(if t ∈ A+A then 1 else 0) +
        2*(if t ∈ B then 1 else 0) := by
    by_cases ht : t ∈ A+A
    · obtain ⟨a,ha,b,hb,hab⟩ := mem_add.mp ht
      have hp : (a,b) ∈ P.filter (fun p ↦ f p = t) :=
        mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab⟩
      have hr : (1 : ℝ) ≤ r t := by exact_mod_cast card_pos.mpr ⟨_,hp⟩
      by_cases hd : t ∈ B
      · simp only [ht, hd, if_true]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · have hne : a ≠ b := by
          intro he
          exact hd (mem_image.mpr ⟨a, ha, by simpa [← he] using hab⟩)
        have hp' : (b,a) ∈ P.filter (fun p ↦ f p = t) :=
          mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩, by simpa [f,add_comm] using hab⟩
        have hr' : 2 ≤ r t := one_lt_card.mpr ⟨_,hp,_,hp', by simp [hne]⟩
        have hr'' : (2 : ℝ) ≤ r t := by exact_mod_cast hr'
        simp only [ht, hd, if_true, if_false]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    · simp only [ht, if_false]
      split_ifs <;> exact abs_le.mpr ⟨by have := Nat.cast_nonneg (α := ℝ) (r t); linarith,
        by linarith⟩
  have hsum : ∑ t ∈ T, (r t : ℝ) = (#A : ℝ)^2 := by
    exact_mod_cast (show ∑ t ∈ T, r t = #A ^ 2 by
      rw [← card_eq_sum_card_fiberwise (f := f) hm]
      simp [P,pow_two])
  have hS : (∑ t ∈ T, (if t ∈ A+A then 1 else 0 : ℝ)) = ↑(#(A+A)) := by
    rw [sum_ite_mem, inter_eq_right.mpr hs]; simp
  have hB : (∑ t ∈ T, (if t ∈ B then 1 else 0 : ℝ)) ≤ ↑(#A) := by
    rw [sum_ite_mem]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast (card_le_card (inter_subset_right) |>.trans (card_image_le (s := A)))
  have hT : #T = 2*N := by simp [T,Nat.card_Icc]
  have hD := sum_le_sum (s := T) (fun t _ ↦ hpoint t)
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,hsum,hS,sum_const,
    nsmul_eq_mul,hT,Nat.cast_mul,Nat.cast_ofNat] at hD
  have horth : ∑ t ∈ T, z^t = 0 := by
    change ∑ t ∈ Icc 1 (2*N), z^t = 0
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp only [Nat.add_one_sub_one, pow_add,
      pow_one, ← mul_sum]
    have hg := geom_sum_mul z (2*N)
    rw [hzN,sub_self,mul_eq_zero] at hg
    rw [hg.resolve_right (sub_ne_zero.mpr hz1),mul_zero]
  have hpoly : (∑ a ∈ A, z^a)^2 = ∑ t ∈ T, (↑(r t)-2 : ℂ)*z^t := by
    rw [show (∑ t ∈ T, (↑(r t)-2 : ℂ)*z^t) =
      (∑ t ∈ T, (↑(r t) : ℂ)*z^t) - 2*(∑ t ∈ T, z^t) by
        simp only [sub_mul,sum_sub_distrib,mul_sum], horth, mul_zero,sub_zero]
    have he := sum_fiberwise_of_maps_to' hm (fun t ↦ z^t)
    simp only [sum_const,nsmul_eq_mul] at he
    rw [pow_two,sum_mul_sum, show (∑ t ∈ T, (↑(r t) : ℂ)*z^t) = _ from he, sum_product]
    simp [f,pow_add]
  calc
    _ = ‖(∑ a ∈ A, z^a)^2‖ := (norm_pow _ _).symm
    _ ≤ ∑ t ∈ T, ‖(↑(r t)-2 : ℂ)*z^t‖ := hpoly ▸ norm_sum_le _ _
    _ = ∑ t ∈ T, |(r t : ℝ)-2| := by
      apply sum_congr rfl
      intro t _
      rw [norm_mul,norm_pow,hz,one_pow,mul_one]
      simpa only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_ofNat, Real.norm_eq_abs] using Complex.norm_real ((r t : ℝ)-2)
    _ ≤ _ := by linarith

open Complex
private noncomputable def phase (x : ℝ) := Complex.exp ((x : ℂ)*I)

private lemma phase_pow (x : ℝ) (n : ℕ) : phase x ^ n = phase (n*x) := by
  unfold phase
  rw [← exp_nat_mul]
  push_cast
  ring_nf

private lemma phase_parts (x : ℝ) : phase x = Real.cos x + (Real.sin x : ℂ)*I := by
  simp [phase, exp_mul_I]

private lemma phase_pair (x : ℝ) :
    phase x + phase (-x) = 2*(Real.cos x : ℂ) ∧
    phase x - phase (-x) = 2*I*(Real.sin x : ℂ) := by
  simp only [phase_parts,Real.cos_neg,Real.sin_neg,ofReal_neg]
  constructor <;> ring

private lemma phase_inv (x : ℝ) : phase (-x) = (phase x)⁻¹ := by
  simp [phase,neg_mul,exp_neg]

-- Sum the two geometric progressions with ratios exp(±iθ) z. Their N-th
-- powers are both −1, giving the sine coefficient after subtraction.
private lemma sine_geom (N : ℕ) (θ φ : ℝ) (hθ : N*θ = Real.pi)
    (hz : phase φ ^ N = 1) :
    (∑ t ∈ range N, (Real.sin (t*θ) : ℂ)*phase φ ^ t) *
    ((Real.cos φ : ℂ) - Real.cos θ) = Real.sin θ := by
  let z := phase φ
  let w := phase θ
  let v := phase (-θ)
  have hw : w^N = -1 := by rw [show w = phase θ from rfl, phase_pow,hθ]; exact exp_pi_mul_I
  have hv : v^N = -1 := by simp [v,phase_inv,inv_pow,← show w = phase θ from rfl,hw]
  have hzz : z ≠ 0 := exp_ne_zero _
  have hwv : w*v=1 := by simp [w,v,phase_inv,phase]
  have hzc : 2*z*(Real.cos φ : ℂ) = z^2+1 := by
    rw [show 2*z*(Real.cos φ : ℂ) = z*(2*(Real.cos φ : ℂ)) by ring,
      ← (phase_pair φ).1,phase_inv]
    change z*(z+z⁻¹)=z^2+1
    rw [mul_add,mul_inv_cancel₀ hzz,pow_two]
  have hden : (w*z-1)*(v*z-1) = 2*z*((Real.cos φ : ℂ)-Real.cos θ) := by
    linear_combination z^2*hwv - hzc - z*(phase_pair θ).1
  let U := ∑ t ∈ range N, (w*z)^t
  let V := ∑ t ∈ range N, (v*z)^t
  have hU : U*(w*z-1) = -2 := by
    dsimp [U]; rw [geom_sum_mul,mul_pow,hw,show z^N=1 from hz]; norm_num
  have hV : V*(v*z-1) = -2 := by
    dsimp [V]; rw [geom_sum_mul,mul_pow,hv,show z^N=1 from hz]; norm_num
  let S := ∑ t ∈ range N, (Real.sin (t*θ) : ℂ)*z^t
  have hS : 2*I*S = U-V := by
    dsimp [S,U,V]
    rw [mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro t _
    simp only [mul_pow,w,v,phase_pow, mul_neg]
    linear_combination -(z^t)*(phase_pair ((t:ℝ)*θ)).2
  have he : (U-V)*(2*z*((Real.cos φ : ℂ)-Real.cos θ)) = 2*z*(w-v) := by
    rw [← hden]
    linear_combination (v*z-1)*hU - (w*z-1)*hV
  apply mul_left_cancel₀ (show (4:ℂ)*I*z ≠ 0 by exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hzz)
  change 4*I*z*(S*((Real.cos φ : ℂ)-Real.cos θ)) = _
  rw [← hS, show w-v=2*I*(Real.sin θ : ℂ) from (phase_pair θ).2] at he
  linear_combination he

private lemma char_phase {N : ℕ} [NeZero N] (j : ZMod N) :
    ZMod.stdAddChar j = phase (2*(j.val:ℝ)*(Real.pi/N)) := by
  rw [ZMod.stdAddChar_apply,ZMod.toCircle_apply]
  unfold phase
  push_cast
  ring_nf

private lemma char_power {N : ℕ} [NeZero N] (j : ZMod N) (a : ℕ) :
    ZMod.stdAddChar j ^ a = ZMod.stdAddChar ((a : ZMod N)*j) := by
  rw [← AddChar.map_nsmul_eq_pow,nsmul_eq_mul]

private lemma char_order {N : ℕ} [NeZero N] (j : ZMod N) :
    ZMod.stdAddChar j ^ N = 1 := by simp [char_power]

private noncomputable def sineGrid (N : ℕ) (t : ZMod N) : ℂ :=
  Real.sin ((t.val : ℝ)*(Real.pi/N))

private lemma dft_formula {N : ℕ} [NeZero N] (j : ZMod N) :
    ZMod.dft (sineGrid N) j *
    ((Real.cos (2*((-j).val:ℝ)*(Real.pi/N)) : ℂ) - Real.cos (Real.pi/N)) =
      Real.sin (Real.pi/N) := by
  let θ := Real.pi/N
  let φ := 2*((-j).val:ℝ)*θ
  have hz : phase φ = ZMod.stdAddChar (-j) := (char_phase _).symm
  have hn : (N:ℝ) ≠ 0 := NeZero.ne _
  have hh := sine_geom N θ φ (by dsimp [θ]; field_simp) (hz ▸ char_order (-j))
  convert hh using 2
  rw [ZMod.dft_apply, ← Fin.sum_univ_eq_sum_range]
  refine (Fintype.sum_equiv (ZMod.finEquiv N).symm.toEquiv _ _ ?_)
  intro t
  have ht : (((ZMod.finEquiv N).symm.toEquiv t : Fin N) : ℕ) = t.val := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  simp only [ht, hz,char_power,ZMod.natCast_zmod_val, mul_neg, smul_eq_mul,sineGrid,θ,mul_comm]

-- Every nonzero grid angle lies strictly between θ and 2π − θ.
private lemma cos_gap {N : ℕ} [NeZero N] (hN : 2 ≤ N) (j : ZMod N) (hj : j ≠ 0) :
    Real.cos (2*(j.val:ℝ)*(Real.pi/N)) < Real.cos (Real.pi/N) := by
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hθ : 0 < Real.pi/N := by positivity
  have hmul : (N:ℝ)*(Real.pi/N)=Real.pi := by field_simp
  have hj1 : (1:ℝ) ≤ j.val := by
    exact_mod_cast (show 1 ≤ j.val by have := (ZMod.val_eq_zero j).not.mpr hj; omega)
  have hj2 : (j.val:ℝ)+1 ≤ N := by exact_mod_cast j.val_lt
  have hlo := mul_le_mul_of_nonneg_right hj1 hθ.le
  have hhi := mul_le_mul_of_nonneg_right hj2 hθ.le
  apply sub_neg.mp
  rw [Real.cos_sub_cos]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos (by norm_num)
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith only [hlo,hhi,hmul,hθ]
  · apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith only [hlo,hhi,hmul,hθ]

private noncomputable def weight (N : ℕ) (j : ZMod N) : ℝ :=
  Real.sin (Real.pi/N) /
    (Real.cos (2*((-j).val:ℝ)*(Real.pi/N)) - Real.cos (Real.pi/N)) / N

private lemma theta_lt {N : ℕ} (hn : 2 ≤ N) : Real.pi/N < Real.pi := by
  have h : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact div_lt_self Real.pi_pos h

private lemma sine_inversion {N : ℕ} [NeZero N] (hn : 2 ≤ N) (a : ZMod N) :
    sineGrid N a = ∑ j : ZMod N, (weight N j : ℂ) * ZMod.stdAddChar (j*a) := by
  have hN : (N:ℝ) ≠ 0 := NeZero.ne _
  have hNc : (N:ℂ) ≠ 0 := NeZero.ne _
  have hden (j : ZMod N) :
      Real.cos (2*((-j).val:ℝ)*(Real.pi/N)) - Real.cos (Real.pi/N) ≠ 0 := by
    by_cases hj : j = 0
    · subst j
      simp only [neg_zero,ZMod.val_zero,Nat.cast_zero,mul_zero,zero_mul,Real.cos_zero]
      apply sub_ne_zero.mpr
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) le_rfl (theta_lt hn).le
        (show 0 < Real.pi/N by positivity)
      simpa using h.ne'
    · exact (sub_neg.mpr (cos_gap hn (-j) (neg_ne_zero.mpr hj))).ne
  have hb (j : ZMod N) : ZMod.dft (sineGrid N) j = (N:ℂ) * (weight N j : ℂ) := by
    unfold weight
    rw [Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast,
      mul_div_cancel₀ _ hNc]
    apply (eq_div_iff _).mpr (dft_formula j)
    exact_mod_cast hden j
  have hi := ZMod.invDFT_apply (ZMod.dft (sineGrid N)) a
  rw [LinearEquiv.symm_apply_apply,smul_eq_mul,mul_sum] at hi
  rw [hi]
  apply sum_congr rfl
  intro j _
  rw [hb,smul_eq_mul]
  field_simp

private lemma weight_neg {N : ℕ} [NeZero N] (hn : 2 ≤ N) (j : ZMod N) (hj : j ≠ 0) :
    weight N j ≤ 0 := by
  have hp : 0 < Real.pi/N := by positivity
  have hs := Real.sin_pos_of_pos_of_lt_pi hp (theta_lt hn)
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonneg_of_nonpos hs.le (sub_nonpos.mpr (cos_gap hn (-j) (neg_ne_zero.mpr hj)).le))
    (Nat.cast_nonneg N)

-- Inversion at the origin identifies the total absolute weight off zero.
private lemma weight_total {N : ℕ} [NeZero N] (hn : 2 ≤ N) :
    ∑ j ∈ (univ : Finset (ZMod N)).erase 0, |weight N j| = weight N 0 := by
  have he := sine_inversion hn (0 : ZMod N)
  simp only [sineGrid,ZMod.val_zero,Nat.cast_zero, zero_mul,Real.sin_zero,ofReal_zero,
    mul_zero,AddChar.map_zero_eq_one,mul_one,← Complex.ofReal_sum] at he
  have hsum : (0 : ℝ) = ∑ j : ZMod N, weight N j := by exact_mod_cast he
  rw [← add_sum_erase _ _ (mem_univ 0)] at hsum
  calc
    _ = ∑ j ∈ (univ : Finset (ZMod N)).erase 0, -weight N j :=
      sum_congr rfl fun j hj ↦ abs_of_nonpos (weight_neg hn j (ne_of_mem_erase hj))
    _ = _ := by rw [sum_neg_distrib]; linarith

-- Write the grid mean cot(π/(2N))/N using sinc to take its limit at zero.
private noncomputable def meanWeight (N : ℕ) : ℝ :=
  (2 / Real.pi) * Real.cos (Real.pi / (2*N)) / Real.sinc (Real.pi / (2*N))

private lemma weight_zero {N : ℕ} [NeZero N] (hn : 2 ≤ N) :
    weight N 0 = meanWeight N := by
  let x := Real.pi/(2*N)
  have hx : 0 < x := by dsimp [x]; positivity
  have hN : (0:ℝ)< N := by exact_mod_cast (show 0<N by omega)
  have hxt : Real.pi/N = 2*x := by dsimp [x]; ring
  have hsin : Real.sin x ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hx (by
    have := theta_lt hn
    linarith)).ne'
  simp only [meanWeight,weight,neg_zero,ZMod.val_zero,Nat.cast_zero,mul_zero,
    zero_mul,Real.cos_zero]
  change Real.sin (Real.pi/N)/(1-Real.cos (Real.pi/N))/N =
    (2/Real.pi)*Real.cos x/Real.sinc x
  rw [hxt, Real.sin_two_mul, Real.cos_two_mul', Real.sinc_of_ne_zero hx.ne',
    show 1 - (Real.cos x ^ 2 - Real.sin x ^ 2) = 2 * Real.sin x ^ 2 by
      linarith [Real.sin_sq_add_cos_sq x]]
  dsimp [x]
  dsimp [x] at hsin
  field_simp

-- Sum the inversion formula over A. The sine sum is the imaginary part
-- of the first Fourier sum, while each nonconstant grid mode has order dividing N.
private lemma finite_bound {N : ℕ} (hn : 2 ≤ N) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
    (meanWeight N * (#A : ℝ))^2 ≤ (1+meanWeight N)^2 *
      ((#A : ℝ)^2 + 4*N - 4*↑(#(A+A)) + 2*↑(#A)) := by
  classical
  have : NeZero N := ⟨by omega⟩
  let θ := Real.pi/N
  let w := phase θ
  let D := (#A : ℝ)^2 + 4*N - 4*↑(#(A+A)) + 2*↑(#A)
  let M := Real.sqrt D
  have hn0 : (N : ℝ) ≠ 0 := NeZero.ne _
  have hw : w^N = -1 := by
    rw [show w = phase θ from rfl,phase_pow, show (N:ℝ)*θ=Real.pi by dsimp [θ]; field_simp]
    exact exp_pi_mul_I
  have hw1 : w ≠ 1 := by intro h; rw [h,one_pow] at hw; norm_num at hw
  have hsw := spectrum A hA w (norm_exp_ofReal_mul_I _) hw1
    (show w^(2*N)=1 by rw [mul_comm,pow_mul,hw]; norm_num)
  have hD : 0 ≤ D := le_trans (sq_nonneg _) hsw
  have hM : M^2 = D := Real.sq_sqrt hD
  have hnorm (v : ℂ) (hv : ‖v‖^2 ≤ D) : ‖v‖ ≤ M :=
    Real.le_sqrt_of_sq_le hv
  have hfirst : ‖∑ a ∈ A, sineGrid N (a : ZMod N)‖ ≤ M := by
    have he : ∑ a ∈ A, sineGrid N (a : ZMod N) = ((∑ a ∈ A, w^a).im : ℂ) := by
      rw [im_sum,ofReal_sum]
      apply sum_congr rfl
      intro a ha
      have hle := (mem_Icc.mp (hA ha)).2
      rw [show w=phase θ from rfl, phase_pow]
      change (Real.sin _ : ℂ) = ((Complex.exp _).im : ℂ)
      rw [exp_ofReal_mul_I_im]
      rcases lt_or_eq_of_le hle with hlt | rfl
      · rw [ZMod.val_natCast_of_lt hlt]
      · rw [ZMod.natCast_self,ZMod.val_zero,Nat.cast_zero,zero_mul,Real.sin_zero,
          show (a:ℝ)*θ = Real.pi by dsimp [θ]; field_simp, Real.sin_pi]
    rw [he, Complex.norm_real,Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hnorm _ hsw)
  let F := fun j : ZMod N ↦ ∑ a ∈ A, ZMod.stdAddChar j ^ a
  have hrest (j : ZMod N) (hj : j ≠ 0) : ‖F j‖ ≤ M := by
    apply hnorm
    apply spectrum A hA
    · rw [char_phase]; exact norm_exp_ofReal_mul_I _
    · intro he
      apply hj
      apply ZMod.injective_stdAddChar
      simpa using he
    · rw [mul_comm,pow_mul,char_order,one_pow]
  let J := (univ : Finset (ZMod N)).erase 0
  have hsum : ∑ a ∈ A, sineGrid N (a : ZMod N) =
      (weight N 0 : ℂ) * (#A : ℂ) + ∑ j ∈ J, (weight N j : ℂ) * F j := by
    simp_rw [sine_inversion hn]
    rw [sum_comm, ← add_sum_erase _ _ (mem_univ 0)]
    simp only [zero_mul,AddChar.map_zero_eq_one,mul_one,sum_const,nsmul_eq_mul]
    rw [mul_comm (weight N 0 : ℂ)]
    congr 1
    apply sum_congr rfl
    intro j _
    simp only [F,mul_sum,char_power,mul_comm j]
  have hbM : ‖∑ j ∈ J, (weight N j : ℂ) * F j‖ ≤ weight N 0 * M := by
    calc
      _ ≤ ∑ j ∈ J, ‖(weight N j : ℂ) * F j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ J, |weight N j| * M := by
        apply sum_le_sum
        intro j hj
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hrest j (ne_of_mem_erase hj)) (abs_nonneg _)
      _ = _ := by rw [← sum_mul,weight_total hn]
  have hb0 : 0 ≤ weight N 0 := weight_total hn ▸ sum_nonneg fun _ _ ↦ abs_nonneg _
  have hbound : weight N 0 * (#A : ℝ) ≤ (1+weight N 0)*M := by
    have he := norm_sub_le (∑ a ∈ A, sineGrid N (a : ZMod N))
      (∑ j ∈ J, (weight N j : ℂ) * F j)
    rw [hsum,add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hb0, Complex.norm_natCast] at he
    rw [← hsum] at he
    linarith
  rw [← weight_zero hn]
  have hsq := pow_le_pow_left₀ (mul_nonneg hb0 (Nat.cast_nonneg _)) hbound 2
  simpa only [mul_pow,hM] using hsq

private lemma mean_limit : Tendsto meanWeight atTop (nhds (2/Real.pi)) := by
  have h : Tendsto (fun N : ℕ ↦ Real.pi/(2*N)) atTop (nhds 0) := by
    have hi : Tendsto (fun N : ℕ ↦ ((N:ℝ)⁻¹)) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hi.const_mul (Real.pi/2)
  have hcos := (Real.continuous_cos.tendsto 0).comp h
  have hsinc := (Real.continuous_sinc.tendsto 0).comp h
  change Tendsto (fun N : ℕ ↦ (2/Real.pi)*Real.cos (Real.pi/(2*(N:ℝ))) /
    Real.sinc (Real.pi/(2*(N:ℝ)))) atTop _
  simpa [Function.comp_def, Pi.div_def] using
    (hcos.const_mul (2/Real.pi)).div hsinc (by simp)

end OMA

open OMA

-- The binomial asymptotic follows the Erdős–Freud upper-bound proof in the source
-- module, using Nat.cast_choose_two as in the merged lower bound by @marcusbuffett.
theorem OMA.solution : type_of% @Erdos840.erdos_840.variants.pikhurko := by
  intro c hc
  by_cases hc0 : 0 < c
  swap
  · exact (le_of_not_gt hc0).trans (Real.rpow_nonneg (by positivity) _)
  obtain ⟨A, hAsub, hk, hs⟩ := hc
  have hsqrt : Tendsto (fun N : ℕ ↦ c * Real.sqrt N) atTop atTop :=
    Tendsto.const_mul_atTop hc0 (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hk1 := hk.sub_isLittleO (w := fun _ ↦ (1 : ℝ))
    (isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hsqrt)))
  have hC := ((hk.mul hk1).div (IsEquivalent.refl (u := fun _ : ℕ ↦ (2 : ℝ)))).congr_left
    (w := fun N ↦ ((#(A N)).choose 2 : ℝ))
    (Eventually.of_forall fun N ↦ by simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply,
      Nat.cast_choose_two])
  have hlim : Tendsto (fun N : ℕ ↦ (#(A N + A N) : ℝ) / N) atTop (nhds (c ^ 2 / 2)) := by
    refine (((hs.trans hC).div (IsEquivalent.refl (u := fun N : ℕ ↦ (N : ℝ)))).congr_right
      (w := fun _ ↦ c ^ 2 / 2) ?_).tendsto_const
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [show c * Real.sqrt N * (c * Real.sqrt N) = c ^ 2 * (Real.sqrt N * Real.sqrt N) by ring,
      hsq]
    field_simp
  let k := fun N : ℕ ↦ (#(A N) : ℝ) / Real.sqrt N
  have hk' : Tendsto k atTop (nhds c) := by
    refine ((hk.div (IsEquivalent.refl (u := fun N : ℕ ↦ Real.sqrt N))).congr_right
      (w := fun _ ↦ c) ?_).tendsto_const
    filter_upwards [eventually_gt_atTop 0] with N hN
    have h : 0 < Real.sqrt N := by positivity
    simp [h.ne']
  have hi : Tendsto (fun N : ℕ ↦ (Real.sqrt N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hineq : (2/Real.pi*c)^2 ≤ (1+2/Real.pi)^2 *
      (c^2 + 4 - 4*(c^2/2) + 2*(c*0)) := by
    apply le_of_tendsto_of_tendsto ((mean_limit.mul hk').pow 2)
      (((tendsto_const_nhds.add mean_limit).pow 2).mul
        ((((hk'.pow 2).add_const 4).sub (hlim.const_mul 4)).add ((hk'.mul hi).const_mul 2)))
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hsq := Real.sq_sqrt hpos.le
    have hr : Real.sqrt N ≠ 0 := by positivity
    have he := div_le_div_of_nonneg_right (finite_bound hN (A N) (hAsub N)) hpos.le
    change (meanWeight N*k N)^2 ≤ (1+meanWeight N)^2 *
      ((k N)^2 + 4 - 4*((#(A N+A N):ℝ)/N) + 2*(k N*(Real.sqrt N)⁻¹))
    dsimp [k]
    rw [show (meanWeight N * ((#(A N):ℝ)/Real.sqrt N))^2 =
        (meanWeight N * (#(A N):ℝ))^2/N by rw [← mul_div_assoc, div_pow,hsq],
      div_pow,hsq,show (#(A N):ℝ)/Real.sqrt N*(Real.sqrt N)⁻¹ = (#(A N):ℝ)/N by
        conv_rhs => rw [← hsq]
        ring]
    convert he using 1
    field_simp
  let b : ℝ := 1/4+1/(Real.pi+2)^2
  have hp := Real.pi_pos
  have hp2 : 0 < Real.pi+2 := by positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hf : c^2*b ≤ 1 := by
    dsimp [b]
    field_simp at hineq ⊢
    nlinarith only [hineq]
  change c ≤ b^(-(1:ℝ)/2)
  rw [neg_div,Real.rpow_neg hb.le,← Real.sqrt_eq_rpow,← one_div,
    le_div_iff₀ (Real.sqrt_pos.2 hb)]
  have he : (c*Real.sqrt b)^2 ≤ 1 := by simpa [mul_pow, Real.sq_sqrt hb.le] using hf
  nlinarith only [he,sq_nonneg (c*Real.sqrt b-1)]
