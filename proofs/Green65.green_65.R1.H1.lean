import OMAReductions.R_Green65_green_65_R1
/-! Port of openai/math 3344da59991ed94f9ba711217b29c1d760badfa6 (OAI.Combinatorics.SquareDifference, Apache-2.0), adapted to the pinned Mathlib. -/
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
lemma gaussSum_norm_sq {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) : ‖gaussSum χ ψ‖ ^ 2 = Fintype.card F := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hr := congrArg Complex.re h
  simpa [Complex.mul_conj, Complex.sq_norm] using hr
lemma square_sum_eq_gaussSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ a : F, ψ (a ^ 2) =
      gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
  classical
  calc
    ∑ a : F, ψ (a ^ 2) =
        ∑ b : F, ∑ a ∈ (univ.filter fun a : F => a ^ 2 = b), ψ (a ^ 2) :=
      (sum_fiberwise univ (fun a : F => a ^ 2) (fun a => ψ (a ^ 2))).symm
    _ = ∑ b : F, ((quadraticChar F b : ℂ) + 1) * ψ b := by
      apply sum_congr rfl
      intro b _
      have hc : ((univ.filter fun a : F => a ^ 2 = b).card : ℂ) =
          (quadraticChar F b : ℂ) + 1 := by
        have hc' := quadraticChar_card_sqrts hF b
        simp only [Set.toFinset_ofPred] at hc'
        exact_mod_cast hc'
      simp_rw [sum_congr rfl (fun a ha => congrArg ψ (mem_filter.mp ha).2)]
      simp only [sum_const, nsmul_eq_mul, hc]
    _ = gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
      simp [add_mul, sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, gaussSum]
lemma square_sum_norm_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ a : F, ψ (a ^ 2)‖ ^ 2 = Fintype.card F := by
  have hp : ψ ≠ 1 := by simpa using hψ (show (1 : F) ≠ 0 from one_ne_zero)
  rw [square_sum_eq_gaussSum hF hp]
  apply gaussSum_norm_sq _ hψ
  exact (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).mpr (quadraticChar_ne_one hF)
noncomputable def squareIndicator {F : Type*} [Field F] (x : F) : ℝ :=
  by
  classical
  exact if x ≠ 0 ∧ IsSquare x then 1 else 0
lemma squareIndicator_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (x : F) : squareIndicator x =
      ((quadraticChar F x : ℝ) + 1 - if x = 0 then 1 else 0) / 2 := by
  classical
  by_cases hx : x = 0
  · simp [hx, squareIndicator]
  by_cases hs : IsSquare x
  · simp [squareIndicator, hx, hs, (quadraticChar_one_iff_isSquare hx).mpr hs]
  · simp [squareIndicator, hx, hs, quadraticChar_neg_one_iff_not_isSquare.mpr hs]
lemma squareIndicator_nonneg {F : Type*} [Field F] (x : F) :
    0 ≤ squareIndicator x := by
  classical
  unfold squareIndicator
  split_ifs <;> norm_num
lemma squareIndicator_le_one {F : Type*} [Field F] (x : F) :
    squareIndicator x ≤ 1 := by
  classical
  unfold squareIndicator
  split_ifs <;> norm_num
lemma squareIndicator_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) :
    ∑ x : F, squareIndicator x = (Fintype.card F - 1 : ℝ) / 2 := by
  classical
  simp_rw [squareIndicator_eq, sub_div, add_div, sum_sub_distrib, sum_add_distrib,
    ← sum_div]
  have hz : ∑ x : F, (quadraticChar F x : ℝ) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hF
  rw [hz]
  simp only [zero_div, zero_add, sum_const, card_univ, nsmul_eq_mul, mul_one,
    sum_ite_eq', mem_univ, ite_true]
lemma squareIndicator_char_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ x : F, (squareIndicator x : ℂ) * ψ x =
      (∑ x : F, ψ (x ^ 2) - 1) / 2 := by
  classical
  rw [square_sum_eq_gaussSum hF hψ]
  simp_rw [squareIndicator_eq, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  simp_rw [sub_div, add_div, sub_mul, add_mul, sum_sub_distrib, sum_add_distrib]
  have hcast (x : F) : ((if x = 0 then 1 else 0 : ℝ) : ℂ) =
      if x = 0 then 1 else 0 := by split_ifs <;> simp
  simp_rw [hcast, div_mul_eq_mul_div, ← sum_div]
  simp [AddChar.sum_eq_zero_of_ne_one hψ, gaussSum]
lemma squareIndicator_char_sum_norm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ x : F, (squareIndicator x : ℂ) * ψ x‖ ≤
      (Real.sqrt (Fintype.card F) + 1) / 2 := by
  have hp : ψ ≠ 1 := by simpa using hψ (show (1 : F) ≠ 0 from one_ne_zero)
  have hnorm : ‖∑ a : F, ψ (a ^ 2)‖ = Real.sqrt (Fintype.card F) := by
    rw [← square_sum_norm_sq hF hψ, Real.sqrt_sq (norm_nonneg _)]
  rw [squareIndicator_char_sum hF hp, norm_div]
  norm_num only [Complex.norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ‖(∑ a : F, ψ (a ^ 2)) - 1‖ ≤ ‖∑ a : F, ψ (a ^ 2)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = Real.sqrt (Fintype.card F) + 1 := by rw [hnorm, norm_one]
lemma dft_inner {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    ∑ k : ZMod N, star (ZMod.dft f k) * ZMod.dft g k =
      (N : ℂ) * ∑ x : ZMod N, star (f x) * g x := by
  classical
  have hs (x : ZMod N) : star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) :=
    (AddChar.map_neg_eq_conj _ x).symm
  simp_rw [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul, hs, neg_neg,
    sum_mul, mul_sum]
  have hprod (k x y : ZMod N) :
      star (f x) * ZMod.stdAddChar (x * k) *
          (ZMod.stdAddChar (-(y * k)) * g y) =
      ZMod.stdAddChar (k * (x - y)) * (star (f x) * g y) := by
    rw [mul_comm (star (f x)), mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [hprod]
  rw [sum_comm]
  simp_rw [sum_comm (f := fun k y : ZMod N =>
    ZMod.stdAddChar (k * ( _ - y)) * (star (f _) * g y))]
  simp_rw [← sum_mul, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp only [Nat.cast_ite, ZMod.card, Nat.cast_zero, ite_mul, zero_mul,
    sub_eq_zero, sum_ite_eq, mem_univ, ite_true]
lemma dft_parseval {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖ZMod.dft f k‖ ^ 2 =
      (N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 := by
  have h := dft_inner f f
  simp_rw [← starRingEnd_apply, Complex.conj_mul'] at h
  exact_mod_cast h
lemma dft_convolution {N : ℕ} [NeZero N] (a b : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun x => ∑ y : ZMod N, a (x - y) * b y) k =
      ZMod.dft a k * ZMod.dft b k := by
  classical
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]
  have hshift (y : ZMod N) :
      ∑ x : ZMod N, ZMod.stdAddChar (-(x * k)) * (a (x - y) * b y) =
        ∑ t : ZMod N, ZMod.stdAddChar (-((t + y) * k)) * (a t * b y) := by
    apply Fintype.sum_equiv (Equiv.subRight y)
    intro x
    simp
  simp_rw [hshift, add_mul, neg_add, AddChar.map_add_eq_mul]
  apply sum_congr rfl
  intro y _
  rw [sum_mul]
  apply sum_congr rfl
  intro x _
  ring
lemma convolution_l2_sq_le {N : ℕ} [NeZero N] (a b : ZMod N → ℂ)
    {M : ℝ} (ha : ∀ k, ‖ZMod.dft a k‖ ≤ M) :
    ∑ x : ZMod N, ‖∑ y : ZMod N, a (x - y) * b y‖ ^ 2 ≤
      M ^ 2 * ∑ y : ZMod N, ‖b y‖ ^ 2 := by
  have hm : 0 ≤ M := (norm_nonneg _).trans (ha 0)
  have hbnd : ∑ k : ZMod N,
      ‖ZMod.dft (fun x => ∑ y : ZMod N, a (x - y) * b y) k‖ ^ 2 ≤
      M ^ 2 * ∑ k : ZMod N, ‖ZMod.dft b k‖ ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro k _
    rw [dft_convolution, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha k) 2)
      (sq_nonneg _)
  rw [dft_parseval, dft_parseval] at hbnd
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  nlinarith
lemma centered_square_dft_bound {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (k : ZMod p) :
    ‖ZMod.dft (fun x : ZMod p => (squareIndicator x : ℂ) - 1 / 2) k‖ ≤
      (Real.sqrt p + 1) / 2 := by
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  by_cases hk : k = 0
  · subst k
    rw [ZMod.dft_apply_zero, sum_sub_distrib]
    have hs : ∑ x : ZMod p, (squareIndicator x : ℂ) = (p - 1 : ℂ) / 2 := by
      have hsum := squareIndicator_sum hF
      rw [ZMod.card] at hsum
      exact_mod_cast hsum
    rw [hs]
    simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    have heq : (p - 1 : ℂ) / 2 - (p : ℂ) * (1 / 2) = -(1 / 2) := by ring
    rw [heq, norm_neg, norm_div, norm_one]
    norm_num only [Complex.norm_ofNat]
    linarith [Real.sqrt_nonneg (p : ℝ)]
  · let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar.mulShift (-k)
    have hn : ψ ≠ 1 := ZMod.isPrimitive_stdAddChar p (neg_ne_zero.mpr hk)
    have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hn
    have hdft : ZMod.dft (fun x : ZMod p => (squareIndicator x : ℂ) - 1 / 2) k =
        ∑ x : ZMod p, (squareIndicator x : ℂ) * ψ x := by
      simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, sum_sub_distrib]
      have heq (x : ZMod p) : ZMod.stdAddChar (-(x * k)) = ψ x := by
        simp [ψ, AddChar.mulShift_apply, mul_comm]
      simp_rw [heq]
      rw [← sum_mul, AddChar.sum_eq_zero_of_ne_one hn, zero_mul, sub_zero]
      apply sum_congr rfl
      intro x _
      exact mul_comm _ _
    rw [hdft]
    simpa only [ZMod.card] using squareIndicator_char_sum_norm hF hψ
lemma centered_square_convolution_l2 {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f : ZMod p → ℝ) :
    ∑ x : ZMod p, (∑ y : ZMod p, (squareIndicator (x - y) - 1 / 2) * f y) ^ 2 ≤
      ((Real.sqrt p + 1) / 2) ^ 2 * ∑ y : ZMod p, (f y) ^ 2 := by
  have h := convolution_l2_sq_le
    (fun x : ZMod p => (squareIndicator x : ℂ) - 1 / 2)
    (fun x : ZMod p => (f x : ℂ)) (centered_square_dft_bound hp)
  have hsum (x : ZMod p) :
      ∑ y : ZMod p, ((squareIndicator (x - y) : ℂ) - 1 / 2) * (f y : ℂ) =
        ((∑ y : ZMod p, (squareIndicator (x - y) - 1 / 2) * f y : ℝ) : ℂ) := by
    push_cast
    rfl
  simp_rw [hsum, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h
lemma single_square_mixing_unnormalized {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f g : ZMod p → ℝ) :
    |∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)| ≤
      ((Real.sqrt p + 1) / 2) * Real.sqrt (∑ x : ZMod p, (f x) ^ 2) *
        Real.sqrt (∑ y : ZMod p, (g y) ^ 2) := by
  let c (y : ZMod p) := ∑ x : ZMod p, (squareIndicator (y - x) - 1 / 2) * f x
  have hc := centered_square_convolution_l2 hp f
  have hcs := sum_mul_sq_le_sq_mul_sq univ g c
  have hf : 0 ≤ ∑ x : ZMod p, (f x) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hg : 0 ≤ ∑ y : ZMod p, (g y) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hM : 0 ≤ (Real.sqrt (p : ℝ) + 1) / 2 := by positivity
  have hbnd : (∑ y : ZMod p, g y * c y) ^ 2 ≤
      (((Real.sqrt p + 1) / 2) * Real.sqrt (∑ x : ZMod p, (f x) ^ 2) *
        Real.sqrt (∑ y : ZMod p, (g y) ^ 2)) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hf, Real.sq_sqrt hg]
    calc
      _ ≤ (∑ y : ZMod p, (g y) ^ 2) * (∑ y : ZMod p, (c y) ^ 2) := hcs
      _ ≤ (∑ y : ZMod p, (g y) ^ 2) *
          (((Real.sqrt p + 1) / 2) ^ 2 * ∑ x : ZMod p, (f x) ^ 2) :=
        mul_le_mul_of_nonneg_left hc hg
      _ = _ := by ring
  have heq : (∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)) =
      ∑ y : ZMod p, g y * c y := by
    rw [sum_comm]
    simp only [c, mul_sum]
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro x _
    ring
  rw [heq]
  exact abs_le_of_sq_le_sq hbnd (mul_nonneg (mul_nonneg hM (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))
lemma single_square_mixing_bounded {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f g : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    |(∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)) / (p : ℝ) ^ 2| ≤
      (Real.sqrt p + 1) / (2 * p) := by
  have hnp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)
  have hfp : ∑ x : ZMod p, (f x) ^ 2 ≤ (p : ℝ) := by
    calc
      _ ≤ ∑ _x : ZMod p, (1 : ℝ) := sum_le_sum (fun x _ => by
        have := (sq_le_sq₀ (abs_nonneg (f x)) zero_le_one).mpr (hf x)
        simpa only [sq_abs, one_pow] using this)
      _ = _ := by simp
  have hgp : ∑ x : ZMod p, (g x) ^ 2 ≤ (p : ℝ) := by
    calc
      _ ≤ ∑ _x : ZMod p, (1 : ℝ) := sum_le_sum (fun x _ => by
        have := (sq_le_sq₀ (abs_nonneg (g x)) zero_le_one).mpr (hg x)
        simpa only [sq_abs, one_pow] using this)
      _ = _ := by simp
  have h := single_square_mixing_unnormalized hp f g
  have hh : |∑ x : ZMod p, ∑ y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)| ≤
      ((Real.sqrt p + 1) / 2) * p := by
    calc
      _ ≤ _ := h
      _ ≤ ((Real.sqrt p + 1) / 2) * Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) := by
        gcongr
      _ = _ := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hnp.le]
  rw [abs_div, abs_of_pos (pow_pos hnp 2)]
  calc
    _ ≤ (((Real.sqrt p + 1) / 2) * p) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp
lemma expect_update {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (u : W) (H : (W → X) → ℝ) :
    (𝔼 z : W → X, 𝔼 x : X, H (Function.update z u x)) = 𝔼 z : W → X, H z := by
  let e : ((W → X) × X) ≃ ((W → X) × X) :=
    { toFun := fun a => (Function.update a.1 u a.2, a.1 u)
      invFun := fun a => (Function.update a.1 u a.2, a.1 u)
      left_inv := by rintro ⟨z, x⟩; simp
      right_inv := by rintro ⟨z, x⟩; simp }
  have he := Fintype.expect_equiv e
    (fun a : (W → X) × X => H (Function.update a.1 u a.2))
    (fun a : (W → X) × X => H a.1) (fun _ => rfl)
  rw [← univ_product_univ, expect_product, expect_product] at he
  simpa only [expect_const univ_nonempty] using he
lemma expect_update_two {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (u v : W) (H : (W → X) → ℝ) :
    (𝔼 z : W → X, 𝔼 x : X, 𝔼 y : X,
      H (Function.update (Function.update z u x) v y)) = 𝔼 z : W → X, H z := by
  calc
    _ = 𝔼 z : W → X, 𝔼 y : X, H (Function.update z v y) :=
      expect_update u (fun z => 𝔼 y : X, H (Function.update z v y))
    _ = _ := expect_update v H
lemma single_square_mixing_expect {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f g : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    |𝔼 x : ZMod p, 𝔼 y : ZMod p,
        f x * g y * (squareIndicator (y - x) - 1 / 2)| ≤
      (Real.sqrt p + 1) / (2 * p) := by
  have h := single_square_mixing_bounded hp f g hf hg
  simpa only [Fintype.expect_eq_sum_div_card, ZMod.card, ← sum_div, div_div,
    ← pow_two] using h
lemma edge_product_factor {W X : Type*} [DecidableEq W]
    (E : Finset (W × W)) (A : X → X → ℝ) {u v : W} (huv : u ≠ v)
    (he : ∀ e ∈ E, ¬ ((e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u)))
    (z : W → X) (x y : X) :
    (∏ e ∈ E, A ((Function.update (Function.update z u x) v y) e.1)
        ((Function.update (Function.update z u x) v y) e.2)) =
      (∏ e ∈ E, if e.1 = v ∨ e.2 = v then 1 else
        A ((Function.update z u x) e.1) ((Function.update z u x) e.2)) *
      (∏ e ∈ E, if e.1 = v ∨ e.2 = v then
        A ((Function.update z v y) e.1) ((Function.update z v y) e.2) else 1) := by
  classical
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro e heE
  by_cases hv : e.1 = v ∨ e.2 = v
  · have hne1 : e.1 ≠ u := by
      have := he e heE
      aesop
    have hne2 : e.2 ≠ u := by
      have := he e heE
      aesop
    simp [hv, Function.update_apply, hne1, hne2]
  · have hv1 := (not_or.mp hv).1
    have hv2 := (not_or.mp hv).2
    simp [Function.update_apply, hv1, hv2]
lemma graph_edge_error {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (E : Finset (W × W)) (A : X → X → ℝ)
    (hA0 : ∀ x y, 0 ≤ A x y) (hA1 : ∀ x y, A x y ≤ 1)
    {δ : ℝ} (hmix : ∀ f g : X → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
      |𝔼 x : X, 𝔼 y : X, f x * g y * (A x y - 1 / 2)| ≤ δ)
    {u v : W} (huv : u ≠ v)
    (he : ∀ e ∈ E, ¬ ((e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u))) :
    |𝔼 z : W → X, (A (z u) (z v) - 1 / 2) * ∏ e ∈ E, A (z e.1) (z e.2)| ≤ δ := by
  classical
  let F (z : W → X) (x : X) := ∏ e ∈ E, if e.1 = v ∨ e.2 = v then 1 else
    A ((Function.update z u x) e.1) ((Function.update z u x) e.2)
  let G (z : W → X) (y : X) := ∏ e ∈ E, if e.1 = v ∨ e.2 = v then
    A ((Function.update z v y) e.1) ((Function.update z v y) e.2) else 1
  have hF (z : W → X) (x : X) : |F z x| ≤ 1 := by
    dsimp [F]
    rw [abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro e _
    split_ifs
    · norm_num
    · rw [abs_of_nonneg (hA0 _ _)]
      exact hA1 _ _
  have hG (z : W → X) (y : X) : |G z y| ≤ 1 := by
    dsimp [G]
    rw [abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro e _
    split_ifs
    · rw [abs_of_nonneg (hA0 _ _)]
      exact hA1 _ _
    · norm_num
  let H (z : W → X) := (A (z u) (z v) - 1 / 2) * ∏ e ∈ E, A (z e.1) (z e.2)
  have hH (z : W → X) (x y : X) :
      H (Function.update (Function.update z u x) v y) =
        F z x * G z y * (A x y - 1 / 2) := by
    dsimp [H, F, G]
    rw [edge_product_factor E A huv he]
    simp only [Function.update_of_ne huv, Function.update_self]
    ring
  change |𝔼 z : W → X, H z| ≤ δ
  rw [← expect_update_two u v H]
  simp_rw [hH]
  calc
    _ ≤ 𝔼 z : W → X, |𝔼 x : X, 𝔼 y : X,
        F z x * G z y * (A x y - 1 / 2)| := abs_expect_le _ _
    _ ≤ δ := expect_le univ_nonempty (fun z _ => hmix (F z) (G z) (hF z) (hG z))
lemma graph_counting {W X : Type*} [Fintype W] [Fintype X] [Nonempty X]
    [DecidableEq W] (E : Finset (W × W)) (A : X → X → ℝ)
    (hA0 : ∀ x y, 0 ≤ A x y) (hA1 : ∀ x y, A x y ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmix : ∀ f g : X → ℝ, (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) →
      |𝔼 x : X, 𝔼 y : X, f x * g y * (A x y - 1 / 2)| ≤ δ)
    (hnoloop : ∀ e ∈ E, e.1 ≠ e.2)
    (hnoopp : ∀ e ∈ E, (e.2, e.1) ∉ E) :
    |(𝔼 z : W → X, ∏ e ∈ E, A (z e.1) (z e.2)) - (1 / 2 : ℝ) ^ E.card| ≤
      E.card * δ := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert e E hne ih =>
    have hloop := hnoloop e (mem_insert_self e E)
    have hcross : ∀ a ∈ E, ¬ ((a.1 = e.1 ∧ a.2 = e.2) ∨
        (a.1 = e.2 ∧ a.2 = e.1)) := by
      intro a ha h
      rcases h with h | h
      · have hae : a = e := Prod.ext h.1 h.2
        exact hne (hae ▸ ha)
      · have hae : a = (e.2, e.1) := Prod.ext h.1 h.2
        exact hnoopp e (mem_insert_self e E) (mem_insert_of_mem (hae ▸ ha))
    have herr := graph_edge_error E A hA0 hA1 hmix hloop hcross
    have hind := ih (fun a ha => hnoloop a (mem_insert_of_mem ha))
      (fun a ha hop => hnoopp a (mem_insert_of_mem ha) (mem_insert_of_mem hop))
    let S : ℝ := 𝔼 z : W → X, ∏ a ∈ E, A (z a.1) (z a.2)
    let R : ℝ := 𝔼 z : W → X,
      (A (z e.1) (z e.2) - 1 / 2) * ∏ a ∈ E, A (z a.1) (z a.2)
    have heq : (𝔼 z : W → X, ∏ a ∈ insert e E, A (z a.1) (z a.2)) =
        R + (1 / 2) * S := by
      dsimp [R, S]
      simp only [prod_insert hne, sub_mul, expect_sub_distrib, ← mul_expect]
      ring
    rw [heq, card_insert_of_notMem hne, pow_succ, Nat.cast_add, Nat.cast_one]
    have hrewrite : R + 1 / 2 * S - (1 / 2 : ℝ) ^ E.card * (1 / 2) =
        R + 1 / 2 * (S - (1 / 2 : ℝ) ^ E.card) := by ring
    rw [hrewrite]
    calc
      _ ≤ |R| + |1 / 2 * (S - (1 / 2 : ℝ) ^ E.card)| := abs_add_le _ _
      _ = |R| + 1 / 2 * |S - (1 / 2 : ℝ) ^ E.card| := by
        rw [abs_mul]
        norm_num
      _ ≤ δ + 1 / 2 * (E.card * δ) := add_le_add herr (mul_le_mul_of_nonneg_left hind (by norm_num))
      _ ≤ (E.card + 1) * δ := by nlinarith [mul_nonneg (Nat.cast_nonneg E.card) hδ]
lemma graph_count {W : Type*} [Fintype W] [DecidableEq W]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (E : Finset (W × W))
    (hnoloop : ∀ e ∈ E, e.1 ≠ e.2) (hnoopp : ∀ e ∈ E, (e.2, e.1) ∉ E) :
    |(𝔼 z : W → ZMod p, ∏ e ∈ E, squareIndicator (z e.2 - z e.1)) -
      (1 / 2 : ℝ) ^ E.card| ≤ E.card * ((Real.sqrt p + 1) / (2 * p)) := by
  exact graph_counting E (fun x y : ZMod p => squareIndicator (y - x))
    (fun _ _ => squareIndicator_nonneg _) (fun _ _ => squareIndicator_le_one _)
    (by positivity) (single_square_mixing_expect hp) hnoloop hnoopp
lemma four_cycle_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (B : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ) :
    (𝔼 x : X, 𝔼 y : Y, f x * B x y * g y) ^ 4 ≤
      (𝔼 x : X, 𝔼 x' : X, 𝔼 y : Y, 𝔼 y' : Y,
        B x y * B x y' * B x' y * B x' y') *
      (𝔼 x : X, (f x) ^ 2) ^ 2 * (𝔼 y : Y, (g y) ^ 2) ^ 2 := by
  classical
  let T (x : X) := 𝔼 y : Y, B x y * g y
  let C (y y' : Y) := 𝔼 x : X, B x y * B x y'
  have h1 := expect_mul_sq_le_sq_mul_sq univ f T
  have h2 := expect_mul_sq_le_sq_mul_sq (univ : Finset (Y × Y))
    (fun yy => g yy.1 * g yy.2) (fun yy => C yy.1 yy.2)
  have hT : (𝔼 x : X, (T x) ^ 2) =
      𝔼 yy : Y × Y, (g yy.1 * g yy.2) * C yy.1 yy.2 := by
    rw [← univ_product_univ, expect_product]
    dsimp [T, C]
    simp_rw [sq, expect_mul, mul_expect]
    rw [expect_comm]
    congr 1
    ext y
    rw [expect_comm]
    congr 1
    ext y'
    apply expect_congr rfl
    intro x _
    ring
  have hgg : (𝔼 yy : Y × Y, (g yy.1 * g yy.2) ^ 2) =
      (𝔼 y : Y, (g y) ^ 2) ^ 2 := by
    rw [← univ_product_univ, expect_product]
    simp_rw [mul_pow, ← mul_expect, ← expect_mul]
    ring
  have hC : (𝔼 yy : Y × Y, (C yy.1 yy.2) ^ 2) =
      𝔼 x : X, 𝔼 x' : X, 𝔼 y : Y, 𝔼 y' : Y,
        B x y * B x y' * B x' y * B x' y' := by
    rw [← univ_product_univ, expect_product]
    dsimp [C]
    simp_rw [sq, expect_mul, mul_expect]
    rw [expect_comm]
    simp_rw [expect_comm (univ : Finset Y) (univ : Finset X)]
    rw [expect_comm]
    apply expect_congr rfl
    intro x _
    apply expect_congr rfl
    intro x' _
    apply expect_congr rfl
    intro y _
    apply expect_congr rfl
    intro y' _
    ring
  rw [hgg, hC, ← hT] at h2
  have hF : 0 ≤ 𝔼 x : X, (f x) ^ 2 := expect_nonneg (fun _ _ => sq_nonneg _)
  have hT0 : 0 ≤ 𝔼 x : X, (T x) ^ 2 := expect_nonneg (fun _ _ => sq_nonneg _)
  have hrewrite : (𝔼 x : X, 𝔼 y : Y, f x * B x y * g y) =
      𝔼 x : X, f x * T x := by
    dsimp [T]
    simp_rw [mul_expect, mul_assoc]
  rw [hrewrite, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  calc
    _ ≤ ((𝔼 x : X, (f x) ^ 2) * (𝔼 x : X, (T x) ^ 2)) ^ 2 :=
      (sq_le_sq₀ (sq_nonneg _) (mul_nonneg hF hT0)).mpr h1
    _ = (𝔼 x : X, (f x) ^ 2) ^ 2 * (𝔼 x : X, (T x) ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ (𝔼 x : X, (f x) ^ 2) ^ 2 *
        ((𝔼 y : Y, (g y) ^ 2) ^ 2 *
          (𝔼 x : X, 𝔼 x' : X, 𝔼 y : Y, 𝔼 y' : Y,
            B x y * B x y' * B x' y * B x' y')) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
def directedCrossEdge {I J A B : Type*} (dir : I → J → Bool)
    (e : (I × J) × (A × B)) : ((I × A) ⊕ (J × B)) × ((I × A) ⊕ (J × B)) :=
  if dir e.1.1 e.1.2 then
    (Sum.inl (e.1.1, e.2.1), Sum.inr (e.1.2, e.2.2))
  else (Sum.inr (e.1.2, e.2.2), Sum.inl (e.1.1, e.2.1))
lemma directedCrossEdge_injective {I J A B : Type*} (dir : I → J → Bool) :
    Function.Injective (directedCrossEdge (A := A) (B := B) dir) := by
  rintro ⟨⟨i,j⟩,⟨a,b⟩⟩ ⟨⟨i',j'⟩,⟨a',b'⟩⟩ h
  dsimp [directedCrossEdge] at h
  split_ifs at h <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, and_false]
lemma directedCrossEdge_noloop {I J A B : Type*} (dir : I → J → Bool)
    (e : (I × J) × (A × B)) :
    (directedCrossEdge dir e).1 ≠ (directedCrossEdge dir e).2 := by
  dsimp [directedCrossEdge]
  split_ifs <;> simp
lemma directedCrossEdge_noopp {I J A B : Type*} (dir : I → J → Bool)
    (e e' : (I × J) × (A × B)) :
    directedCrossEdge dir e' ≠ ((directedCrossEdge dir e).2, (directedCrossEdge dir e).1) := by
  rcases e with ⟨⟨i,j⟩,⟨a,b⟩⟩
  rcases e' with ⟨⟨i',j'⟩,⟨a',b'⟩⟩
  dsimp [directedCrossEdge]
  split_ifs <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, not_false_eq_true]
  all_goals rintro ⟨⟨hi,ha⟩,⟨hj,hb⟩⟩; subst_vars; simp_all
noncomputable def listKernel {I J : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × J)) (dir : I → J → Bool) (x : I → ZMod p) (y : J → ZMod p) : ℝ :=
  ∏ e ∈ E, if dir e.1 e.2 then squareIndicator (y e.2 - x e.1)
    else squareIndicator (x e.1 - y e.2)
lemma copied_graph_count {I J A B : Type*}
    [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool) (F : Finset (A × B)) :
    |(𝔼 z : (I × A) ⊕ (J × B) → ZMod p,
        ∏ ab ∈ F, listKernel E dir (fun i => z (Sum.inl (i, ab.1)))
          (fun j => z (Sum.inr (j, ab.2)))) - (1 / 2 : ℝ) ^ (E.card * F.card)| ≤
      (E.card * F.card : ℕ) * ((Real.sqrt p + 1) / (2 * p)) := by
  classical
  let G := (E ×ˢ F).image (directedCrossEdge dir)
  have hnoloop : ∀ e ∈ G, e.1 ≠ e.2 := by
    intro e he
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    exact directedCrossEdge_noloop dir a
  have hnoopp : ∀ e ∈ G, (e.2, e.1) ∉ G := by
    intro e he h
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    obtain ⟨a', _, ha'⟩ := mem_image.mp h
    exact directedCrossEdge_noopp dir a a' ha'
  have hc : G.card = E.card * F.card := by
    rw [card_image_of_injective _ (directedCrossEdge_injective dir), card_product]
  have hprod (z : (I × A) ⊕ (J × B) → ZMod p) :
      (∏ e ∈ G, squareIndicator (z e.2 - z e.1)) =
        ∏ ab ∈ F, listKernel E dir (fun i => z (Sum.inl (i, ab.1)))
          (fun j => z (Sum.inr (j, ab.2))) := by
    rw [prod_image (directedCrossEdge_injective dir).injOn, prod_product, prod_comm]
    apply prod_congr rfl
    intro ab _
    dsimp [listKernel]
    apply prod_congr rfl
    intro ij _
    dsimp [directedCrossEdge]
    split_ifs <;> rfl
  have h := graph_count hp G hnoloop hnoopp
  simpa only [hc, hprod] using h
lemma centered_product_moment_bound {T X : Type*} [Fintype X] [Nonempty X]
    [DecidableEq T] (S : Finset T) (hS : S.Nonempty) (K : T → X → ℝ)
    {c δ : ℝ} (hc : |c| ≤ 1) (hδ : 0 ≤ δ)
    (hmom : ∀ F ⊆ S, |(𝔼 x : X, ∏ i ∈ F, K i x) - c ^ F.card| ≤ F.card * δ) :
    |𝔼 x : X, ∏ i ∈ S, (K i x - c)| ≤
      (∑ F ∈ S.powerset, (F.card : ℝ)) * δ := by
  classical
  have hmain : (∑ F ∈ S.powerset, c ^ F.card * (-c) ^ (S \ F).card) = 0 := by
    have h := prod_add (fun _ : T => c) (fun _ : T => -c) S
    simpa [hS.card_pos.ne'] using h.symm
  have hexpand : (𝔼 x : X, ∏ i ∈ S, (K i x - c)) =
      ∑ F ∈ S.powerset, (𝔼 x : X, ∏ i ∈ F, K i x) * (-c) ^ (S \ F).card := by
    simp_rw [sub_eq_add_neg, prod_add, prod_const, expect_sum_comm, ← expect_mul]
  rw [hexpand, ← sub_zero (∑ F ∈ S.powerset,
    (𝔼 x : X, ∏ i ∈ F, K i x) * (-c) ^ (S \ F).card), ← hmain, ← sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ F ∈ S.powerset,
        |((𝔼 x : X, ∏ i ∈ F, K i x) - c ^ F.card) * (-c) ^ (S \ F).card| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ F ∈ S.powerset, (F.card : ℝ) * δ := by
      apply sum_le_sum
      intro F hF
      rw [abs_mul]
      have hpow : |(-c) ^ (S \ F).card| ≤ 1 := by
        rw [abs_pow, abs_neg]
        exact pow_le_one₀ (abs_nonneg _) hc
      calc
        _ ≤ (F.card * δ) * 1 :=
          mul_le_mul (hmom F (mem_powerset.mp hF)) hpow (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hδ)
        _ = _ := mul_one _
    _ = _ := (sum_mul _ _ _).symm
def fourListsEquiv (I J X : Type*) :
    ((I × Bool) ⊕ (J × Bool) → X) ≃ ((I → X) × (I → X)) × ((J → X) × (J → X)) where
  toFun z := ((fun i => z (.inl (i, false)), fun i => z (.inl (i, true))),
    (fun j => z (.inr (j, false)), fun j => z (.inr (j, true))))
  invFun z := fun w => match w with
    | .inl (i, false) => z.1.1 i
    | .inl (i, true) => z.1.2 i
    | .inr (j, false) => z.2.1 j
    | .inr (j, true) => z.2.2 j
  left_inv z := by funext w; rcases w with ⟨i, b⟩ | ⟨j, b⟩ <;> cases b <;> rfl
  right_inv z := rfl
lemma expect_fourLists {I J X : Type*} [Fintype I] [Fintype J] [Fintype X]
    [DecidableEq I] [DecidableEq J]
    (H : (I → X) → (I → X) → (J → X) → (J → X) → ℝ) :
    (𝔼 z : (I × Bool) ⊕ (J × Bool) → X,
      H (fun i => z (.inl (i, false))) (fun i => z (.inl (i, true)))
        (fun j => z (.inr (j, false))) (fun j => z (.inr (j, true)))) =
      𝔼 x : I → X, 𝔼 x' : I → X, 𝔼 y : J → X, 𝔼 y' : J → X, H x x' y y' := by
  classical
  calc
    _ = 𝔼 z : ((I → X) × (I → X)) × ((J → X) × (J → X)),
        H z.1.1 z.1.2 z.2.1 z.2.2 :=
      Fintype.expect_equiv (fourListsEquiv I J X) _ _ (fun _ => rfl)
    _ = _ := by simp_rw [← univ_product_univ, expect_product]
lemma list_four_cycle {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool) :
    |𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
      𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
        (listKernel E dir x y - (1 / 2 : ℝ) ^ E.card) *
        (listKernel E dir x y' - (1 / 2 : ℝ) ^ E.card) *
        (listKernel E dir x' y - (1 / 2 : ℝ) ^ E.card) *
        (listKernel E dir x' y' - (1 / 2 : ℝ) ^ E.card)| ≤
      32 * E.card * ((Real.sqrt p + 1) / (2 * p)) := by
  classical
  let S : Finset (Bool × Bool) := univ
  let K (ab : Bool × Bool) (z : (I × Bool) ⊕ (J × Bool) → ZMod p) :=
    listKernel E dir (fun i => z (.inl (i, ab.1))) (fun j => z (.inr (j, ab.2)))
  have h := centered_product_moment_bound S univ_nonempty K
    (c := (1 / 2 : ℝ) ^ E.card) (δ := E.card * ((Real.sqrt p + 1) / (2 * p)))
    (by rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num))
    (by positivity) (fun F _ => by
      have h := copied_graph_count hp E dir F
      simpa only [K, pow_mul, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h)
  have hsum : (∑ F ∈ S.powerset, (F.card : ℝ)) = 32 := by
    rw [sum_powerset_apply_card]
    norm_num [S, Fintype.card_prod, Fintype.card_bool, sum_range_succ, Nat.choose]
  rw [hsum] at h
  have heq : (𝔼 z : (I × Bool) ⊕ (J × Bool) → ZMod p,
      ∏ ab ∈ S, (K ab z - (1 / 2 : ℝ) ^ E.card)) =
      𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
        𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
          (listKernel E dir x y - (1 / 2 : ℝ) ^ E.card) *
          (listKernel E dir x y' - (1 / 2 : ℝ) ^ E.card) *
          (listKernel E dir x' y - (1 / 2 : ℝ) ^ E.card) *
          (listKernel E dir x' y' - (1 / 2 : ℝ) ^ E.card) := by
    rw [← expect_fourLists]
    apply expect_congr rfl
    intro z _
    simp only [S, K, Fintype.prod_prod_type, Fintype.prod_bool]
    ring
  rw [heq] at h
  simpa only [mul_assoc] using h
lemma square_delta_le {p : ℕ} [Fact p.Prime] :
    (Real.sqrt p + 1) / (2 * p) ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.Prime.one_lt Fact.out).le
  have hs : (1 : ℝ) ≤ Real.sqrt p := by simpa using Real.sqrt_le_sqrt hp1
  rw [show -(1 : ℝ) / 2 = 1 / 2 - 1 by norm_num, Real.rpow_sub hp,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  apply (div_le_div_iff₀ (by positivity) hp).mpr
  nlinarith
lemma list_mixing {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool)
    (f : (I → ZMod p) → ℝ) (g : (J → ZMod p) → ℝ) :
    |𝔼 x : I → ZMod p, 𝔼 y : J → ZMod p,
      f x * (listKernel E dir x y - (1 / 2 : ℝ) ^ E.card) * g y| ≤
      (32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) *
        Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2) *
        Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2) := by
  let B (x : I → ZMod p) (y : J → ZMod p) :=
    listKernel E dir x y - (1 / 2 : ℝ) ^ E.card
  let C : ℝ := (32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCp : C ^ 4 = 32 * E.card * (p : ℝ) ^ (-(1 : ℝ) / 2) := by
    dsimp [C]
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity),
      ← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have ht := list_four_cycle hp E dir
  have ht' : (𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
      𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
        B x y * B x y' * B x' y * B x' y') ≤ C ^ 4 := by
    calc
      _ ≤ |𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
        𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
          B x y * B x y' * B x' y * B x' y'| := le_abs_self _
      _ ≤ 32 * E.card * ((Real.sqrt p + 1) / (2 * p)) := ht
      _ ≤ 32 * E.card * (p : ℝ) ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left square_delta_le (by positivity)
      _ = _ := hCp.symm
  have hF : 0 ≤ 𝔼 x : I → ZMod p, (f x) ^ 2 :=
    expect_nonneg (fun _ _ => sq_nonneg _)
  have hG : 0 ≤ 𝔼 y : J → ZMod p, (g y) ^ 2 :=
    expect_nonneg (fun _ _ => sq_nonneg _)
  have h4 : (𝔼 x : I → ZMod p, 𝔼 y : J → ZMod p, f x * B x y * g y) ^ 4 ≤
      (C * Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2) *
        Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2)) ^ 4 := by
    calc
      _ ≤ (𝔼 x : I → ZMod p, 𝔼 x' : I → ZMod p,
          𝔼 y : J → ZMod p, 𝔼 y' : J → ZMod p,
            B x y * B x y' * B x' y * B x' y') *
          (𝔼 x : I → ZMod p, (f x) ^ 2) ^ 2 *
          (𝔼 y : J → ZMod p, (g y) ^ 2) ^ 2 := four_cycle_bound B f g
      _ ≤ C ^ 4 * (𝔼 x : I → ZMod p, (f x) ^ 2) ^ 2 *
          (𝔼 y : J → ZMod p, (g y) ^ 2) ^ 2 := by gcongr
      _ = _ := by
        have hf4 : (Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2)) ^ 4 =
            (𝔼 x : I → ZMod p, (f x) ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hF]
        have hg4 : (Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2)) ^ 4 =
            (𝔼 y : J → ZMod p, (g y) ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hG]
        calc
          _ = C ^ 4 * (Real.sqrt (𝔼 x : I → ZMod p, (f x) ^ 2)) ^ 4 *
              (Real.sqrt (𝔼 y : J → ZMod p, (g y) ^ 2)) ^ 4 := by rw [hf4, hg4]
          _ = _ := by ring
  apply (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
  have habs (a : ℝ) : |a| ^ 4 = a ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  simpa only [habs] using h4
lemma posSemidef_entrywise_pow {I : Type*} [Fintype I]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) (k : ℕ) :
    (Matrix.of fun i j => A i j ^ k).PosSemidef := by
  induction k with
  | zero => simpa [Matrix.vecMulVec] using Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  | succ k hk => simpa [Matrix.hadamard, pow_succ] using hk.hadamard hA
lemma posSemidef_entrywise_exp {I : Type*} [Fintype I]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) :
    (Matrix.of fun i j => Real.exp (A i j)).PosSemidef := by
  classical
  let T (n : ℕ) : Matrix I I ℝ :=
    ∑ k ∈ range n, (Nat.factorial k : ℝ)⁻¹ • (Matrix.of fun i j => A i j ^ k)
  have hT (n : ℕ) : (T n).PosSemidef := by
    exact Matrix.posSemidef_sum (range n) fun k _ =>
      (posSemidef_entrywise_pow hA k).smul (by positivity)
  have ht (i j : I) : Filter.Tendsto (fun n => T n i j)
      Filter.atTop (nhds (Real.exp (A i j))) := by
    simpa [T, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
    rw [show A j i = A i j by simpa using hA.isHermitian.apply i j]
  · have ht' : Filter.Tendsto (fun n => star v ⬝ᵥ (T n).mulVec v)
        Filter.atTop (nhds (star v ⬝ᵥ (Matrix.of fun i j => Real.exp (A i j)).mulVec v)) := by
      simp only [dotProduct, Matrix.mulVec]
      apply tendsto_finsetSum
      intro i _
      apply Filter.Tendsto.const_mul
      apply tendsto_finsetSum
      intro j _
      exact (ht i j).mul_const _
    apply ge_of_tendsto ht'
    exact Filter.Eventually.of_forall fun n =>
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hT n)).2 v
lemma posSemidef_entrywise_prod {I L : Type*} [Fintype I]
    (s : Finset L) (A : L → Matrix I I ℝ) (hA : ∀ l ∈ s, (A l).PosSemidef) :
    (Matrix.of fun i j => ∏ l ∈ s, A l i j).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Matrix.vecMulVec] using
      Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  | @insert l s hl hs =>
    simpa [prod_insert hl, Matrix.hadamard] using
      (hA l (mem_insert_self _ _)).hadamard
        (hs fun k hk => hA k (mem_insert_of_mem hk))
lemma posSemidef_product_gap {I L : Type*} [Fintype I]
    (s : Finset L) (a : L → ℝ) (A : L → Matrix I I ℝ)
    (ha : ∀ l ∈ s, 0 ≤ a l) (hA : ∀ l ∈ s, (A l).PosSemidef) :
    (Matrix.of fun i j => (∏ l ∈ s, (1 + a l * A l i j)) -
      (∏ l ∈ s, a l) * (∏ l ∈ s, A l i j)).PosSemidef := by
  classical
  have hOne : (Matrix.of fun _ _ : I => (1 : ℝ)).PosSemidef := by
    simpa [Matrix.vecMulVec] using Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  induction s using Finset.induction_on with
  | empty =>
    convert (Matrix.PosSemidef.zero : (0 : Matrix I I ℝ).PosSemidef) using 1
    ext i j
    simp
  | @insert l s hl hs =>
    have hal := ha l (mem_insert_self _ _)
    have hAl := hA l (mem_insert_self _ _)
    have has : ∀ k ∈ s, 0 ≤ a k := fun k hk => ha k (mem_insert_of_mem hk)
    have hAs : ∀ k ∈ s, (A k).PosSemidef := fun k hk => hA k (mem_insert_of_mem hk)
    have hfactors (k : L) (hk : k ∈ s) :
        (Matrix.of fun i j => 1 + a k * A k i j).PosSemidef := by
      convert hOne.add ((hAs k hk).smul (has k hk)) using 1
      ext i j
      simp [Matrix.add_apply, Matrix.smul_apply]
    have hc := posSemidef_entrywise_prod s
      (fun k => Matrix.of fun i j => 1 + a k * A k i j) hfactors
    have hd := hc.add ((hAl.hadamard (hs has hAs)).smul hal)
    convert hd using 1
    ext i j
    simp only [Matrix.of_apply, prod_insert hl, Matrix.add_apply, Matrix.smul_apply,
      Matrix.hadamard_apply, smul_eq_mul]
    ring
lemma posSemidef_equality {I J : Type*} [Fintype I] [DecidableEq J]
    (f : I → J) : (Matrix.of fun i j => if f i = f j then (1 : ℝ) else 0).PosSemidef := by
  have hd : (Matrix.diagonal (fun _ : J => (1 : ℝ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun _ => zero_le_one)
  simpa [Matrix.submatrix, Matrix.diagonal_apply] using hd.submatrix f
lemma posSemidef_exp_agreement_gap {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (κ : ℝ) (hκ : 0 ≤ κ) :
    (Matrix.of fun j k : I → J =>
      Real.exp (κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0) -
      (Real.exp κ - 1) ^ Fintype.card I * (if j = k then 1 else 0)).PosSemidef := by
  classical
  have h := posSemidef_product_gap (univ : Finset I) (fun _ => Real.exp κ - 1)
    (fun x => Matrix.of fun j k : I → J => if j x = k x then (1 : ℝ) else 0)
    (fun _ _ => sub_nonneg.mpr (Real.one_le_exp_iff.mpr hκ))
    (fun x _ => posSemidef_equality (fun j : I → J => j x))
  convert h using 1
  ext j k
  simp only [Matrix.of_apply, prod_const, card_univ, prod_boole, mem_univ, forall_true_left]
  simp only [← funext_iff]
  congr 1
  rw [mul_sum, Real.exp_sum]
  apply prod_congr rfl
  intro x _
  split_ifs with hx <;> simp
lemma posSemidef_gram {I K : Type*} [Fintype I] [Fintype K]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) (v : K → I → ℝ) :
    (Matrix.of fun j k => ∑ x : I, ∑ y : I, v j x * A x y * v k y).PosSemidef := by
  convert hA.mul_mul_conjTranspose_same (Matrix.of v) using 1
  ext j k
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    sum_mul]
  rw [sum_comm]
noncomputable def indexCross {I J : Type*} [Fintype I] [DecidableEq J]
    (A : Matrix I I ℝ) (j k : I → J) : ℝ :=
  ∑ x : I, ∑ y : I, A x y * (if j x = k y then 1 else 0)
lemma posSemidef_indexCross {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) :
    (Matrix.of (indexCross (J := J) A)).PosSemidef := by
  classical
  have h (a : J) := posSemidef_gram hA (fun j : I → J =>
    fun x => if j x = a then (1 : ℝ) else 0)
  convert Matrix.posSemidef_sum univ (fun a _ => h a) using 1
  ext j k
  simp only [Matrix.of_apply, Matrix.sum_apply, indexCross]
  symm
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  simp [ite_mul, mul_ite, eq_comm]
lemma indexCross_sub_scalar_one {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℝ) (κ : ℝ) (j k : I → J) :
    indexCross (A - κ • 1) j k = indexCross A j k -
      κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0 := by
  simp only [indexCross, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, sub_mul, sum_sub_distrib]
  congr 1
  have hxy (x y : I) : κ * (if x = y then (1 : ℝ) else 0) *
      (if j x = k y then 1 else 0) =
      if y = x then κ * (if j x = k x then 1 else 0) else 0 := by
    by_cases h : y = x
    · subst y; simp
    · simp [h, Ne.symm h]
  simp_rw [hxy]
  simp only [sum_ite_eq', mem_univ, ite_true]
  rw [mul_sum]
lemma exponential_index_matrix_lower {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I I ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hA : (A - κ • 1).PosSemidef) :
    (Matrix.of (fun j k : I → J => Real.exp (indexCross A j k)) -
      (Real.exp κ - 1) ^ Fintype.card I • 1).PosSemidef := by
  classical
  let lam := (Real.exp κ - 1) ^ Fintype.card I
  let D := Matrix.of (indexCross (J := J) (A - κ • 1))
  let R := Matrix.of (fun j k => Real.exp (D j k))
  have hD : D.PosSemidef := posSemidef_indexCross hA
  have hR : R.PosSemidef := posSemidef_entrywise_exp hD
  have hlam : 0 ≤ lam := pow_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hκ)) _
  have hdiag : (Matrix.diagonal (fun j => lam * (R j j - 1))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    apply mul_nonneg hlam
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr hD.diag_nonneg)
  let E := Matrix.of fun j k : I → J =>
    Real.exp (κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0) -
      lam * (if j = k then 1 else 0)
  have hE : E.PosSemidef := posSemidef_exp_agreement_gap κ hκ
  have hmat : (Matrix.of (fun j k : I → J => Real.exp (indexCross A j k)) -
      lam • 1) = E.hadamard R + Matrix.diagonal (fun j => lam * (R j j - 1)) := by
    ext j k
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      Matrix.add_apply, Matrix.hadamard_apply, Matrix.diagonal_apply, smul_eq_mul]
    have he : Real.exp (indexCross A j k) =
        Real.exp (κ * ∑ x : I, if j x = k x then (1 : ℝ) else 0) * R j k := by
      dsimp [R, D]
      rw [indexCross_sub_scalar_one, Real.exp_sub]
      field_simp
    rw [he]
    dsimp only [E, Matrix.of_apply]
    by_cases hjk : j = k
    · subst k
      simp only [ite_true]
      ring
    · simp only [hjk, ite_false, mul_zero, sub_zero, add_zero]
  change (Matrix.of (fun j k : I → J => Real.exp (indexCross A j k)) -
    lam • (1 : Matrix (I → J) (I → J) ℝ)).PosSemidef
  rw [hmat]
  exact (hE.hadamard hR).add hdiag
lemma posSemidef_of_diagonal_dominance {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian)
    (hdom : ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ A i i) : A.PosSemidef := by
  rw [hA.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have hμ : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    change hA.eigenvalues i ∈ spectrum ℝ (Matrix.toLinAlgEquiv' A)
    rw [AlgEquiv.spectrum_eq]
    exact hA.eigenvalues_mem_spectrum_real i
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ
  simp only [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs] at hk
  have ht := (abs_le.mp hk).1
  have hd := hdom k
  change 0 ≤ hA.eigenvalues i
  linarith
lemma matrix_gap_of_diagonal_dominance {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) (κ : ℝ)
    (hdom : ∀ i, κ + ∑ j ∈ univ.erase i, |A i j| ≤ A i i) :
    (A - κ • 1).PosSemidef := by
  apply posSemidef_of_diagonal_dominance
    (hA.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])))
  intro i
  calc
    ∑ j ∈ univ.erase i, |(A - κ • 1) i j| = ∑ j ∈ univ.erase i, |A i j| := by
      apply sum_congr rfl
      intro j hj
      have hji := (mem_erase.mp hj).1
      simp [Matrix.sub_apply, Matrix.smul_apply, Ne.symm hji]
    _ ≤ A i i - κ := by linarith [hdom i]
    _ = (A - κ • 1) i i := by simp
lemma matrix_lower_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} {lam : ℝ} (hC : (C - lam • 1).PosSemidef) (v : I → ℝ) :
    lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * C i j * v j := by
  have h := hC.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, dotProduct_sub] at h
  have hid : star v ⬝ᵥ (lam • (1 : Matrix I I ℝ)).mulVec v = lam * ∑ i, (v i) ^ 2 := by
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, star_trivial, dotProduct,
      Pi.smul_apply, smul_eq_mul, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hc : star v ⬝ᵥ C.mulVec v = ∑ i, ∑ j, v i * C i j * v j := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, mul_sum, mul_assoc]
  rw [hid, hc] at h
  linarith
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
lemma weighted_matrix_lower_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} {lam : ℝ} (hC : (C - lam • 1).PosSemidef) (hlam : 0 ≤ lam)
    (a f : I → ℝ) (ha : ∀ i, 1 ≤ a i) :
    lam * ∑ i, (f i) ^ 2 ≤ ∑ i, ∑ j, (a i * f i) * C i j * (a j * f j) := by
  calc
    lam * ∑ i, (f i) ^ 2 ≤ lam * ∑ i, (a i * f i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hlam
      apply sum_le_sum
      intro i _
      have ha2 : 0 ≤ (a i) ^ 2 - 1 := by nlinarith [ha i]
      nlinarith [mul_nonneg ha2 (sq_nonneg (f i))]
    _ ≤ _ := matrix_lower_quadratic hC _
lemma marked_index_average {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hA : (A - κ • 1).PosSemidef) (a f : (I → J) → ℝ) (ha : ∀ j, 1 ≤ a j) :
    ((Real.exp κ - 1) ^ Fintype.card I / (Fintype.card J : ℝ) ^ Fintype.card I) *
      (𝔼 j : I → J, (f j) ^ 2) ≤
      𝔼 j : I → J, 𝔼 k : I → J,
        (a j * f j) * Real.exp (indexCross A j k) * (a k * f k) := by
  classical
  have h := weighted_matrix_lower_quadratic (exponential_index_matrix_lower A κ hκ hA)
    (pow_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hκ)) _) a f ha
  have hd := div_le_div_of_nonneg_right h
    (sq_nonneg (Fintype.card (I → J) : ℝ))
  simp only [Matrix.of_apply] at hd
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Nat.cast_pow, ← sum_div,
    div_div] at hd ⊢
  convert hd using 1 <;> first | rfl | ring
abbrev WordVertex (B : Type*) (h : ℕ) := B → Equiv.Perm (Fin h)
abbrev PositionPair (h : ℕ) := {p : Fin h × Fin h // p.1 < p.2}
def vertexSwap {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (p : PositionPair h) : WordVertex B h :=
  Function.update v b (v b * Equiv.swap p.1.1 p.1.2)
def reflect {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : WordVertex B h) : WordVertex B h :=
  Function.update v b (Equiv.swap α β * v b)
def cutPlus {B : Type*} {h : ℕ} (b : B) (α β : Fin h) (v : WordVertex B h) : Prop :=
  (v b).symm α < (v b).symm β
instance cutPlusDecidable {B : Type*} {h : ℕ} (b : B) (α β : Fin h) :
    DecidablePred (cutPlus b α β) :=
  fun v => inferInstanceAs (Decidable ((v b).symm α < (v b).symm β))
lemma vertexSwap_involutive {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (p : PositionPair h) : Function.Involutive (fun v : WordVertex B h => vertexSwap v b p) := by
  intro v
  ext a
  by_cases hab : a = b
  · subst a
    simp [vertexSwap, mul_assoc]
  · simp [vertexSwap, hab]
lemma reflect_involutive {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) : Function.Involutive (reflect b α β) := by
  intro v
  ext a
  by_cases hab : a = b
  · subst a
    simp [reflect, ← mul_assoc]
  · simp [reflect, hab]
lemma reflect_vertexSwap {B : Type*} [DecidableEq B] {h : ℕ}
    (b c : B) (α β : Fin h) (p : PositionPair h) (v : WordVertex B h) :
    reflect b α β (vertexSwap v c p) = vertexSwap (reflect b α β v) c p := by
  ext a
  by_cases hab : a = b <;> by_cases hac : a = c <;>
    simp_all [reflect, vertexSwap, mul_assoc]
lemma reflect_cutPlus {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : WordVertex B h) :
    cutPlus b α β (reflect b α β v) ↔ (v b).symm β < (v b).symm α := by
  simp [cutPlus, reflect, Equiv.Perm.mul_def]
lemma swap_reverse_gap {h : ℕ} (i j a b : Fin h) (hij : i < j) (hab : a < b)
    (hrev : Equiv.swap a b j < Equiv.swap a b i) (hnot : ¬ (a = i ∧ b = j)) :
    j.val - i.val + 1 ≤ b.val - a.val := by
  simp only [Equiv.swap_apply_def] at hrev
  split_ifs at hrev <;> subst_vars <;> simp_all <;> omega
lemma vertexSwap_symm_apply {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (p : PositionPair h) (α : Fin h) :
    (vertexSwap v b p b).symm α = Equiv.swap p.1.1 p.1.2 ((v b).symm α) := by
  simp [vertexSwap, Equiv.Perm.mul_def]
lemma reflect_eq_positional {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (α β : Fin h) (hp : cutPlus b α β v) :
    reflect b α β v = vertexSwap v b ⟨((v b).symm α, (v b).symm β), hp⟩ := by
  ext a x
  by_cases hab : a = b
  · subst a
    simp only [reflect, vertexSwap, Function.update_self, Equiv.Perm.mul_apply]
    have hh := Equiv.trans_swap_trans_symm α β (v b)
    have hh' := congrArg (fun e : Fin h ≃ Fin h => (v b) (e x)) hh
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using congrArg Fin.val hh'
  · simp [reflect, vertexSwap, hab]
noncomputable def interaction {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v w : WordVertex B h) : ℝ :=
  ∑ b ∈ S, ∑ p : PositionPair h,
    if w = vertexSwap v b p then δ ^ (p.1.2.val - p.1.1.val) else 0
lemma interaction_nonneg {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (v w : WordVertex B h) :
    0 ≤ interaction S δ v w := by
  unfold interaction
  positivity
lemma interaction_eq_zero_of_not_neighbour {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v w : WordVertex B h)
    (hw : ∀ b ∈ S, ∀ p : PositionPair h, w ≠ vertexSwap v b p) :
    interaction S δ v w = 0 := by
  classical
  apply sum_eq_zero
  intro b hb
  exact sum_eq_zero fun p _ => if_neg (hw b hb p)
lemma interaction_symm {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v w : WordVertex B h) :
    interaction S δ v w = interaction S δ w v := by
  classical
  unfold interaction
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro p _
  simp only [show (w = vertexSwap v b p) ↔ (v = vertexSwap w b p) from
    ⟨fun hh => ((congrArg (fun z => vertexSwap z b p) hh).trans
      (vertexSwap_involutive b p v)).symm,
     fun hh => ((congrArg (fun z => vertexSwap z b p) hh).trans
      (vertexSwap_involutive b p w)).symm⟩]
lemma interaction_reflect {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (α β : Fin h) (v w : WordVertex B h) :
    interaction S δ (reflect b α β v) (reflect b α β w) = interaction S δ v w := by
  classical
  unfold interaction
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro p _
  simp only [← reflect_vertexSwap, (reflect_involutive b α β).injective.eq_iff]
lemma cross_gap {B : Type*} [DecidableEq B] {h : ℕ}
    (b c : B) (α β : Fin h) (x y : WordVertex B h)
    (hx : cutPlus b α β x) (hy : cutPlus b α β y) (hxy : y ≠ x)
    (p : PositionPair h) (heq : reflect b α β y = vertexSwap x c p) :
    b = c ∧ ((x b).symm β).val - ((x b).symm α).val + 1 ≤ p.1.2.val - p.1.1.val := by
  have hrev : (vertexSwap x c p b).symm β < (vertexSwap x c p b).symm α := by
    rw [← heq]
    simpa [reflect, cutPlus, Equiv.Perm.mul_def] using hy
  have hbc : b = c := by
    by_contra hn
    simp only [vertexSwap, Function.update_of_ne hn] at hrev
    exact lt_asymm hx hrev
  subst c
  refine ⟨rfl, ?_⟩
  rw [vertexSwap_symm_apply, vertexSwap_symm_apply] at hrev
  apply swap_reverse_gap _ _ _ _ hx p.2 hrev
  rintro ⟨ha, hb⟩
  apply hxy
  apply (reflect_involutive b α β).injective
  rw [heq, reflect_eq_positional x b α β hx]
  congr 1
  apply Subtype.ext
  exact Prod.ext ha hb
abbrev CutHalf {B : Type*} {h : ℕ} (b : B) (α β : Fin h) :=
  {v : WordVertex B h // cutPlus b α β v}
noncomputable def crossInteraction {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (α β : Fin h) :
    Matrix (CutHalf b α β) (CutHalf b α β) ℝ :=
  Matrix.of fun x y => interaction S δ x.1 (reflect b α β y.1)
lemma crossInteraction_symmetric {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (α β : Fin h) :
    (crossInteraction S δ b α β).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial, crossInteraction, Matrix.of_apply]
  calc
    interaction S δ y.1 (reflect b α β x.1) =
        interaction S δ (reflect b α β y.1) x.1 := by
      rw [← interaction_reflect S δ b α β y.1 (reflect b α β x.1),
        reflect_involutive b α β x.1]
    _ = interaction S δ x.1 (reflect b α β y.1) := interaction_symm _ _ _ _
lemma crossInteraction_diagonal_lower {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (b : B) (hb : b ∈ S)
    (α β : Fin h) (x : CutHalf b α β) :
    δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val) ≤
      crossInteraction S δ b α β x x := by
  classical
  let p : PositionPair h := ⟨((x.1 b).symm α, (x.1 b).symm β), x.2⟩
  let f (c : B) (q : PositionPair h) : ℝ :=
    if reflect b α β x.1 = vertexSwap x.1 c q then δ ^ (q.1.2.val - q.1.1.val) else 0
  have hf (c : B) (q : PositionPair h) : 0 ≤ f c q :=
    ite_nonneg (pow_nonneg hδ _) le_rfl
  have hp : f b p ≤ ∑ q : PositionPair h, f b q :=
    single_le_sum (fun q _ => hf b q) (mem_univ p)
  have hb' : (∑ q : PositionPair h, f b q) ≤ ∑ c ∈ S, ∑ q : PositionPair h, f c q :=
    single_le_sum (fun c _ => sum_nonneg fun q _ => hf c q) hb
  change δ ^ _ ≤ ∑ c ∈ S, ∑ q : PositionPair h, f c q
  refine le_trans ?_ (hp.trans hb')
  dsimp [f]
  rw [if_pos (reflect_eq_positional x.1 b α β x.2)]
lemma crossInteraction_generator_bound {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (b c : B)
    (α β : Fin h) (x : CutHalf b α β) (p : PositionPair h) :
    ∑ y ∈ univ.erase x, (if reflect b α β y.1 = vertexSwap x.1 c p then
      δ ^ (p.1.2.val - p.1.1.val) else 0) ≤
    if c = b then δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) else 0 := by
  classical
  by_cases hex : ∃ y ∈ (univ : Finset (CutHalf b α β)).erase x,
      reflect b α β y.1 = vertexSwap x.1 c p
  · obtain ⟨y, hy, heq⟩ := hex
    have hyx : y.1 ≠ x.1 := fun hh => (mem_erase.mp hy).1 (Subtype.ext hh)
    obtain ⟨hbc, hgap⟩ := cross_gap b c α β x.1 y.1 x.2 y.2 hyx p heq
    subst c
    rw [if_pos rfl]
    calc
      _ = δ ^ (p.1.2.val - p.1.1.val) := by
        rw [sum_eq_single y, if_pos heq]
        · intro z _ hzy
          rw [if_neg]
          intro hz
          apply hzy
          apply Subtype.ext
          exact (reflect_involutive b α β).injective (hz.trans heq.symm)
        · exact fun hn => False.elim (hn hy)
      _ ≤ _ := pow_le_pow_of_le_one hδ hδ1 hgap
  · have hz : ∀ y ∈ (univ : Finset (CutHalf b α β)).erase x,
        reflect b α β y.1 ≠ vertexSwap x.1 c p := by simpa using hex
    rw [sum_eq_zero (fun y hy => if_neg (hz y hy))]
    split_ifs <;> positivity
lemma crossInteraction_offdiag_bound {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (b : B) (hb : b ∈ S)
    (α β : Fin h) (x : CutHalf b α β) :
    ∑ y ∈ univ.erase x, |crossInteraction S δ b α β x y| ≤
      (h : ℝ) ^ 2 * δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) := by
  classical
  simp only [crossInteraction, Matrix.of_apply]
  simp_rw [abs_of_nonneg (interaction_nonneg S hδ _ _)]
  unfold interaction
  rw [sum_comm]
  conv_lhs => arg 2; ext c; rw [sum_comm]
  calc
    _ ≤ ∑ c ∈ S, ∑ _p : PositionPair h,
        if c = b then δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) else 0 := by
      apply sum_le_sum
      intro c hc
      apply sum_le_sum
      intro p hp
      exact crossInteraction_generator_bound hδ hδ1 b c α β x p
    _ = (Fintype.card (PositionPair h) : ℝ) *
        δ ^ (((x.1 b).symm β).val - ((x.1 b).symm α).val + 1) := by
      simp [sum_ite_eq', hb]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hδ _)
      have hc : Fintype.card (PositionPair h) ≤ h ^ 2 := by
        have hh := Fintype.card_subtype_le (fun p : Fin h × Fin h => p.1 < p.2)
        simpa [Fintype.card_prod, pow_two] using hh
      exact_mod_cast hc
lemma crossInteraction_diagonal_dominance {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hscale : (h : ℝ) ^ 2 * δ = 1 / 10) (b : B) (hb : b ∈ S)
    (α β : Fin h) (x : CutHalf b α β) :
    (9 / 10 : ℝ) * δ ^ (h - 1) + ∑ y ∈ univ.erase x,
      |crossInteraction S δ b α β x y| ≤ crossInteraction S δ b α β x x := by
  classical
  let g := ((x.1 b).symm β).val - ((x.1 b).symm α).val
  have hg : g ≤ h - 1 := by
    have hh := ((x.1 b).symm β).isLt
    dsimp [g]
    omega
  have hpow : δ ^ (h - 1) ≤ δ ^ g := pow_le_pow_of_le_one hδ hδ1 hg
  have hoff := crossInteraction_offdiag_bound S hδ hδ1 b hb α β x
  have hdiag := crossInteraction_diagonal_lower S hδ b hb α β x
  have heq : (h : ℝ) ^ 2 * δ ^ (g + 1) = (1 / 10 : ℝ) * δ ^ g := by
    rw [pow_succ]
    calc
      (h : ℝ) ^ 2 * (δ ^ g * δ) = ((h : ℝ) ^ 2 * δ) * δ ^ g := by ring
      _ = _ := by rw [hscale]
  change _ ≤ (h : ℝ) ^ 2 * δ ^ (g + 1) at hoff
  rw [heq] at hoff
  linarith
def tupleH : ℕ := 24
def tupleT : ℕ := 80
def tupleBlocks : ℕ := 2 * tupleT + 1
noncomputable def tupleDelta : ℝ := 1 / (10 * (tupleH : ℝ) ^ 2)
noncomputable def tupleKappa : ℝ := (9 / 10) * tupleDelta ^ (tupleH - 1)
lemma tupleDelta_pos : 0 < tupleDelta := by norm_num [tupleDelta, tupleH]
lemma tupleDelta_le_one : tupleDelta ≤ 1 := by norm_num [tupleDelta, tupleH]
lemma tupleDelta_scale : (tupleH : ℝ) ^ 2 * tupleDelta = 1 / 10 := by
  norm_num [tupleDelta, tupleH]
lemma tupleKappa_pos : 0 < tupleKappa := by
  unfold tupleKappa
  exact mul_pos (by norm_num) (pow_pos tupleDelta_pos _)
lemma cutPlus_reflect_iff_not {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) (v : WordVertex B h) :
    cutPlus b α β (reflect b α β v) ↔ ¬ cutPlus b α β v := by
  rw [reflect_cutPlus]
  have hne : (v b).symm α ≠ (v b).symm β := (v b).symm.injective.ne hαβ
  exact lt_iff_not_ge.trans (not_congr (le_iff_lt_or_eq.trans (or_iff_left hne)))
noncomputable def halfSumEquiv {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) :
    CutHalf b α β ⊕ CutHalf b α β ≃ WordVertex B h where
  toFun := Sum.elim Subtype.val (fun v => reflect b α β v.1)
  invFun := fun v => if hp : cutPlus b α β v then Sum.inl ⟨v, hp⟩ else
    Sum.inr ⟨reflect b α β v, (cutPlus_reflect_iff_not b hαβ v).mpr hp⟩
  left_inv := by
    rintro (x | x)
    · simp [x.2]
    · have hn : ¬ cutPlus b α β (reflect b α β x.1) := by
        rw [cutPlus_reflect_iff_not b hαβ]
        exact not_not.mpr x.2
      simp [hn]
      exact Subtype.ext (reflect_involutive b α β x.1)
  right_inv := by
    intro v
    by_cases hv : cutPlus b α β v
    · simp [hv]
    · simp only [dif_neg hv, Sum.elim_inr]
      exact reflect_involutive b α β v
lemma card_cutHalf {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) :
    2 * Fintype.card (CutHalf b α β) = (Nat.factorial h) ^ Fintype.card B := by
  classical
  have hh := Fintype.card_congr (halfSumEquiv b hαβ)
  simpa [Fintype.card_sum, Fintype.card_fun, Fintype.card_perm, two_mul] using hh
def addressEdge {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    (c : G) (T : ℕ) (u v : B → G) : Prop :=
  T ≤ (univ.filter fun b => v b = u b * c).card
lemma addressEdge_irrefl {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    {c : G} (hc : c ≠ 1) {T : ℕ} (hT : 0 < T) (u : B → G) : ¬ addressEdge c T u u := by
  have hh (b : B) : u b ≠ u b * c := by
    intro hh
    apply hc
    exact (mul_left_cancel (show u b * c = u b * 1 by simpa using hh.symm))
  simp [addressEdge, hh, hT.not_ge]
lemma addressEdge_asymm {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    {c : G} (hc : c ^ 2 ≠ 1) {T : ℕ} (hT : Fintype.card B < 2 * T)
    {u v : B → G} (huv : addressEdge c T u v) : ¬ addressEdge c T v u := by
  classical
  intro hvu
  let s := univ.filter fun b : B => v b = u b * c
  let t := univ.filter fun b : B => u b = v b * c
  have hdis : Disjoint s t := by
    rw [disjoint_left]
    intro b hbs hbt
    have hs : v b = u b * c := (mem_filter.mp hbs).2
    have ht : u b = v b * c := (mem_filter.mp hbt).2
    apply hc
    apply mul_left_cancel (a := u b)
    calc
      u b * c ^ 2 = (u b * c) * c := by rw [pow_two, mul_assoc]
      _ = u b := by rw [← hs, ← ht]
      _ = u b * 1 := (mul_one _).symm
  have hcard : s.card + t.card ≤ Fintype.card B := by
    rw [← card_union_of_disjoint hdis]
    exact card_le_univ _
  change T ≤ s.card at huv
  change T ≤ t.card at hvu
  omega
lemma addressEdge_left_translate {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    (c : G) (T : ℕ) (a u v : B → G) :
    addressEdge c T (fun b => a b * u b) (fun b => a b * v b) ↔ addressEdge c T u v := by
  simp only [addressEdge, mul_assoc, mul_right_inj]
lemma addressEdge_mono_blocks {B C G : Type*} [Fintype B] [Fintype C]
    [DecidableEq G] [Group G] (c : G) (T : ℕ) (f : B ↪ C) (u v : C → G)
    (hedge : addressEdge c T (u ∘ f) (v ∘ f)) : addressEdge c T u v := by
  classical
  apply le_trans hedge
  apply card_le_card_of_injOn f
  · intro b hb
    simpa using hb
  · exact f.injective.injOn
lemma crossInteraction_gap {B : Type*} [Fintype B] [DecidableEq B]
    (S : Finset B) (b : B) (hb : b ∈ S) (α β : Fin tupleH) :
    (crossInteraction S tupleDelta b α β - tupleKappa • 1).PosSemidef := by
  classical
  apply matrix_gap_of_diagonal_dominance (crossInteraction_symmetric S tupleDelta b α β)
  exact crossInteraction_diagonal_dominance S tupleDelta_pos.le tupleDelta_le_one
    tupleDelta_scale b hb α β
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
noncomputable def indexEnergy {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (j : I → J) : ℝ := (1 / 2) * indexCross H j j
noncomputable def indexWeight {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (j : I → J) : ℝ := Real.exp (indexEnergy H j)
lemma indexEnergy_nonneg {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (hH : ∀ x y, 0 ≤ H x y) (j : I → J) :
    0 ≤ indexEnergy H j := by
  unfold indexEnergy indexCross
  apply mul_nonneg (by norm_num)
  exact sum_nonneg fun x _ => sum_nonneg fun y _ => mul_nonneg (hH x y) (by positivity)
lemma one_le_indexWeight {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (hH : ∀ x y, 0 ≤ H x y) (j : I → J) :
    1 ≤ indexWeight H j := Real.one_le_exp_iff.mpr (indexEnergy_nonneg H hH j)
lemma indexCross_equiv {I K J : Type*} [Fintype I] [Fintype K] [DecidableEq J]
    (e : I ≃ K) (H : Matrix K K ℝ) (j k : K → J) :
    indexCross (H.submatrix e e) (j ∘ e) (k ∘ e) = indexCross H j k := by
  unfold indexCross
  apply Fintype.sum_equiv e
  intro x
  exact Fintype.sum_equiv e _ _ (fun y => rfl)
lemma indexCross_transpose {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (j k : I → J) :
    indexCross H.transpose k j = indexCross H j k := by
  unfold indexCross
  rw [sum_comm]
  simp only [Matrix.transpose_apply, eq_comm]
lemma indexCross_sum {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix (I ⊕ I) (I ⊕ I) ℝ) (j k : I → J) :
    indexCross H (Sum.elim j k) (Sum.elim j k) =
      indexCross (H.submatrix Sum.inl Sum.inl) j j +
      indexCross (H.submatrix Sum.inl Sum.inr) j k +
      indexCross (H.submatrix Sum.inr Sum.inl) k j +
      indexCross (H.submatrix Sum.inr Sum.inr) k k := by
  simp only [indexCross, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.submatrix_apply, sum_add_distrib]
  simp only [add_assoc, add_left_comm]
  rfl
lemma indexWeight_factor {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix (I ⊕ I) (I ⊕ I) ℝ)
    (hsym : ∀ x y, H (Sum.inr x) (Sum.inl y) = H (Sum.inl y) (Sum.inr x))
    (href : ∀ x y, H (Sum.inr x) (Sum.inr y) = H (Sum.inl x) (Sum.inl y))
    (j k : I → J) :
    indexWeight H (Sum.elim j k) =
      indexWeight (H.submatrix Sum.inl Sum.inl) j *
      Real.exp (indexCross (H.submatrix Sum.inl Sum.inr) j k) *
      indexWeight (H.submatrix Sum.inl Sum.inl) k := by
  have hrl : H.submatrix Sum.inr Sum.inl = (H.submatrix Sum.inl Sum.inr).transpose := by
    ext x y
    exact hsym x y
  have hrr : H.submatrix Sum.inr Sum.inr = H.submatrix Sum.inl Sum.inl := by
    ext x y
    exact href x y
  simp only [indexWeight, indexEnergy, indexCross_sum, hrl, hrr, indexCross_transpose]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring
lemma expect_sum_function {I J M : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [AddCommMonoid M] [Module ℚ≥0 M] (f : (I ⊕ I → J) → M) :
    (𝔼 j : I ⊕ I → J, f j) = 𝔼 j : I → J, 𝔼 k : I → J, f (Sum.elim j k) := by
  calc
    _ = 𝔼 jk : (I → J) × (I → J), f (Sum.elim jk.1 jk.2) := by
      apply Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow I I J)
      intro j
      congr 1
      ext (i | i) <;> rfl
    _ = _ := by rw [← univ_product_univ, expect_product]
lemma reflected_index_weight_lower {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (H : Matrix (I ⊕ I) (I ⊕ I) ℝ)
    (hpos : ∀ x y, 0 ≤ H (Sum.inl x) (Sum.inl y))
    (hsym : ∀ x y, H (Sum.inr x) (Sum.inl y) = H (Sum.inl y) (Sum.inr x))
    (href : ∀ x y, H (Sum.inr x) (Sum.inr y) = H (Sum.inl x) (Sum.inl y))
    (κ : ℝ) (hκ : 0 ≤ κ) (hgap : (H.submatrix Sum.inl Sum.inr - κ • 1).PosSemidef)
    (f : (I → J) → ℝ) :
    ((Real.exp κ - 1) ^ Fintype.card I / (Fintype.card J : ℝ) ^ Fintype.card I) *
      (𝔼 j : I → J, (f j) ^ 2) ≤
      𝔼 j : I ⊕ I → J, indexWeight H j * f (j ∘ Sum.inl) * f (j ∘ Sum.inr) := by
  rw [expect_sum_function]
  simp only [indexWeight_factor H hsym href]
  have hh := marked_index_average (H.submatrix Sum.inl Sum.inr) κ hκ hgap
    (indexWeight (H.submatrix Sum.inl Sum.inl)) f (one_le_indexWeight _ hpos)
  convert hh using 1
  apply expect_congr rfl
  intro j _
  apply expect_congr rfl
  intro k _
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  ring
lemma card_positionPair (h : ℕ) : Fintype.card (PositionPair h) = h.choose 2 := by
  simpa [Fintype.card_subtype] using (Fintype.card_product_filter_lt (α := Fin h))
lemma interaction_row_sum {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v : WordVertex B h) :
    ∑ w : WordVertex B h, interaction S δ v w =
      ∑ _b ∈ S, ∑ p : PositionPair h, δ ^ (p.1.2.val - p.1.1.val) := by
  classical
  unfold interaction
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [sum_comm]
  simp
lemma interaction_row_sum_le {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (v : WordVertex B h) :
    ∑ w : WordVertex B h, interaction S δ v w ≤ (S.card : ℝ) * (h.choose 2 : ℝ) * δ := by
  rw [interaction_row_sum]
  calc
    _ ≤ ∑ _b ∈ S, ∑ _p : PositionPair h, δ := by
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro p _
      have hg : 1 ≤ p.1.2.val - p.1.1.val := by have := p.2; omega
      simpa using pow_le_pow_of_le_one hδ hδ1 hg
    _ = _ := by simp [card_positionPair, mul_assoc]
abbrev TupleVertex := WordVertex (Fin tupleBlocks) tupleH
abbrev TupleAddress (S : Finset (Fin tupleBlocks)) :=
  {b : Fin tupleBlocks // b ∉ S} → Equiv.Perm (Fin tupleH)
def tupleR : ℕ := Nat.factorial tupleH / 2
abbrev TupleListIndex (S : Finset (Fin tupleBlocks)) := Fin (tupleR ^ S.card)
abbrev TupleListEntry (S : Finset (Fin tupleBlocks)) := TupleAddress S × TupleListIndex S
def tupleProjection (S : Finset (Fin tupleBlocks)) (v : TupleVertex) : TupleAddress S :=
  fun b => v b.1
def tupleCycle : Equiv.Perm (Fin tupleH) := finRotate tupleH
def cycleVertex (j : ℕ) : TupleVertex := fun _ => tupleCycle ^ j
lemma tupleCycle_ne_one : tupleCycle ≠ 1 := by decide
lemma tupleCycle_sq_ne_one : tupleCycle ^ 2 ≠ 1 := by decide
lemma card_tupleVertex : Fintype.card TupleVertex = (Nat.factorial tupleH) ^ tupleBlocks := by
  simp [TupleVertex, WordVertex, Fintype.card_perm]
lemma tupleR_pos : 0 < tupleR := by norm_num [tupleR, tupleH]
instance tupleListIndexNonempty (S : Finset (Fin tupleBlocks)) : Nonempty (TupleListIndex S) :=
  Fin.pos_iff_nonempty.mp (pow_pos tupleR_pos _)
lemma card_cleanBlocks (S : Finset (Fin tupleBlocks)) :
    Fintype.card {b : Fin tupleBlocks // b ∉ S} = tupleBlocks - S.card := by
  classical
  rw [Fintype.card_subtype]
  have heq : (univ.filter fun b : Fin tupleBlocks => b ∉ S) = univ \ S := by ext; simp
  rw [heq, card_sdiff_of_subset (subset_univ S)]
  simp
lemma card_tupleAddress (S : Finset (Fin tupleBlocks)) :
    Fintype.card (TupleAddress S) = (Nat.factorial tupleH) ^ (tupleBlocks - S.card) := by
  simp [TupleAddress, Fintype.card_perm]
noncomputable def tupleListEdges (S : Finset (Fin tupleBlocks)) :
    Finset (TupleListEntry S × TupleListEntry S) := by
  classical
  exact if S.card ≤ tupleT then
    univ.filter fun e => addressEdge tupleCycle (tupleT + 1) e.1.1 e.2.1 else ∅
lemma tupleListEdges_no_loop (S : Finset (Fin tupleBlocks))
    (e : TupleListEntry S × TupleListEntry S) (he : e ∈ tupleListEdges S) : e.1 ≠ e.2 := by
  classical
  unfold tupleListEdges at he
  split_ifs at he with hs
  · intro heq
    have hh := (mem_filter.mp he).2
    rw [heq] at hh
    exact addressEdge_irrefl tupleCycle_ne_one (by norm_num [tupleT]) e.2.1 hh
  · simp at he
lemma tupleListEdges_no_opp (S : Finset (Fin tupleBlocks))
    (e : TupleListEntry S × TupleListEntry S) (he : e ∈ tupleListEdges S) :
    (e.2, e.1) ∉ tupleListEdges S := by
  classical
  unfold tupleListEdges at he ⊢
  split_ifs at he ⊢ with hs
  · intro hop
    apply addressEdge_asymm tupleCycle_sq_ne_one _ (mem_filter.mp he).2 (mem_filter.mp hop).2
    rw [card_cleanBlocks]
    simp only [tupleBlocks, tupleT]
    omega
  · simp at he
lemma expect_precompose {I K J M : Type*} [Fintype I] [Fintype K] [Fintype J]
    [DecidableEq I] [DecidableEq K] [AddCommMonoid M] [Module ℚ≥0 M]
    (e : I ≃ K) (f : (I → J) → M) :
    (𝔼 j : I → J, f j) = 𝔼 j : K → J, f (j ∘ e) := by
  apply Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl J))
  intro j
  congr 1
  funext i
  simp
lemma indexWeight_equiv {I K J : Type*} [Fintype I] [Fintype K] [DecidableEq J]
    (e : I ≃ K) (H : Matrix K K ℝ) (j : K → J) :
    indexWeight (H.submatrix e e) (j ∘ e) = indexWeight H j := by
  simp only [indexWeight, indexEnergy, indexCross_equiv]
lemma marked_interaction_weight_lower {B : Type*} [Fintype B] [DecidableEq B]
    {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset B) (b : B) (hb : b ∈ S) {α β : Fin tupleH} (hαβ : α ≠ β)
    (f : (CutHalf b α β → J) → ℝ) :
    ((Real.exp tupleKappa - 1) ^ Fintype.card (CutHalf b α β) /
      (Fintype.card J : ℝ) ^ Fintype.card (CutHalf b α β)) *
      (𝔼 j : CutHalf b α β → J, (f j) ^ 2) ≤
      𝔼 j : WordVertex B tupleH → J, indexWeight (interaction S tupleDelta) j *
        f (fun x => j x.1) * f (fun x => j (reflect b α β x.1)) := by
  classical
  let e := halfSumEquiv b hαβ
  let H : Matrix (CutHalf b α β ⊕ CutHalf b α β) (CutHalf b α β ⊕ CutHalf b α β) ℝ :=
    Matrix.submatrix (interaction S tupleDelta) e e
  have hp : ∀ x y, 0 ≤ H (Sum.inl x) (Sum.inl y) :=
    fun x y => interaction_nonneg S tupleDelta_pos.le x.1 y.1
  have hs : ∀ x y, H (Sum.inr x) (Sum.inl y) = H (Sum.inl y) (Sum.inr x) :=
    fun x y => interaction_symm S tupleDelta _ _
  have hr : ∀ x y, H (Sum.inr x) (Sum.inr y) = H (Sum.inl x) (Sum.inl y) :=
    fun x y => interaction_reflect S tupleDelta b α β x.1 y.1
  have hg : (H.submatrix Sum.inl Sum.inr - tupleKappa • 1).PosSemidef :=
    crossInteraction_gap S b hb α β
  have hh := reflected_index_weight_lower H hp hs hr tupleKappa tupleKappa_pos.le hg f
  rw [expect_precompose e] at hh
  have hw (j : WordVertex B tupleH → J) :
      indexWeight H (j ∘ e) = indexWeight (interaction S tupleDelta) j :=
    indexWeight_equiv e _ j
  refine hh.trans_eq ?_
  apply expect_congr rfl
  intro j _
  rw [hw]
  rfl
noncomputable def tupleWeight (S : Finset (Fin tupleBlocks))
    (j : TupleVertex → TupleListIndex S) : ℝ := indexWeight (interaction S tupleDelta) j
noncomputable def tupleValidity {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : ℝ :=
  ∏ e ∈ tupleListEdges S, squareIndicator (Y e.2 - Y e.1)
def tupleOutput {p : ℕ} (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) (j : TupleVertex → TupleListIndex S) :
    TupleVertex → ZMod p := fun v => Y (tupleProjection S v, j v)
noncomputable def tupleComponent {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (G : (TupleVertex → ZMod p) → ℝ) : ℝ :=
  𝔼 Y : TupleListEntry S → ZMod p, 𝔼 j : TupleVertex → TupleListIndex S,
    tupleValidity S Y * tupleWeight S j * G (tupleOutput S Y j)
noncomputable def tupleCutForm {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (F : (CutHalf b α β → ZMod p) → ℝ) : ℝ :=
  tupleComponent S (fun z => F (fun x => z x.1) * F (fun x => z (reflect b α β x.1)))
lemma tupleValidity_nonneg {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : 0 ≤ tupleValidity S Y := by
  unfold tupleValidity
  exact prod_nonneg fun e _ => squareIndicator_nonneg _
lemma tupleProjection_reflect (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (hb : b ∈ S) (α β : Fin tupleH) (v : TupleVertex) :
    tupleProjection S (reflect b α β v) = tupleProjection S v := by
  funext a
  have hab : a.1 ≠ b := by intro h; exact a.2 (h ▸ hb)
  simp [tupleProjection, reflect, hab]
lemma tuple_marked_lower {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∈ S) {α β : Fin tupleH} (hαβ : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    ((Real.exp tupleKappa - 1) ^ Fintype.card (CutHalf b α β) /
      (Fintype.card (TupleListIndex S) : ℝ) ^ Fintype.card (CutHalf b α β)) *
      (𝔼 Y : TupleListEntry S → ZMod p, 𝔼 j : CutHalf b α β → TupleListIndex S,
        tupleValidity S Y * (F (fun x => Y (tupleProjection S x.1, j x))) ^ 2) ≤
      tupleCutForm S b α β F := by
  classical
  unfold tupleCutForm tupleComponent
  rw [mul_expect]
  apply expect_le_expect
  intro Y _
  have hh := mul_le_mul_of_nonneg_left
    (marked_interaction_weight_lower S b hb hαβ
      (fun j : CutHalf b α β → TupleListIndex S =>
        F (fun x => Y (tupleProjection S x.1, j x)))) (tupleValidity_nonneg S Y)
  simp only [mul_expect] at hh ⊢
  convert hh using 1
  · apply expect_congr rfl
    intro j _
    ring
  · apply expect_congr rfl
    intro j _
    simp only [tupleWeight, tupleOutput, tupleProjection_reflect S b hb α β]
    ring
lemma indexEnergy_le_of_row {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (hH : ∀ x y, 0 ≤ H x y) (C : ℝ)
    (hC : ∀ x, ∑ y, H x y ≤ C) (j : I → J) :
    indexEnergy H j ≤ (Fintype.card I : ℝ) * C / 2 := by
  unfold indexEnergy indexCross
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ x, ∑ y, H x y := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      split_ifs <;> simp_all
    _ ≤ (1 / 2 : ℝ) * ∑ _x : I, C :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => hC x) (by norm_num)
    _ = _ := by simp; ring
noncomputable def tupleWeightBound : ℝ :=
  Real.exp ((Fintype.card TupleVertex : ℝ) * (tupleT + 1) *
    (tupleH.choose 2 : ℝ) * tupleDelta / 2)
lemma tupleWeight_one_le (S : Finset (Fin tupleBlocks))
    (j : TupleVertex → TupleListIndex S) : 1 ≤ tupleWeight S j :=
  one_le_indexWeight _ (interaction_nonneg S tupleDelta_pos.le) j
lemma tupleWeight_le (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (j : TupleVertex → TupleListIndex S) : tupleWeight S j ≤ tupleWeightBound := by
  unfold tupleWeight tupleWeightBound indexWeight
  apply Real.exp_le_exp.mpr
  refine (indexEnergy_le_of_row (interaction S tupleDelta) (interaction_nonneg S tupleDelta_pos.le)
    ((S.card : ℝ) * (tupleH.choose 2 : ℝ) * tupleDelta)
    (interaction_row_sum_le S tupleDelta_pos.le tupleDelta_le_one) j).trans ?_
  have hSc : (S.card : ℝ) ≤ (tupleT : ℝ) + 1 := by exact_mod_cast hS
  have hδ := tupleDelta_pos.le
  calc
    _ ≤ (Fintype.card TupleVertex : ℝ) *
        (((tupleT : ℝ) + 1) * (tupleH.choose 2 : ℝ) * tupleDelta) / 2 := by gcongr
    _ = _ := by ring
lemma tupleComponent_nonneg {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (G : (TupleVertex → ZMod p) → ℝ) (hG : ∀ z, 0 ≤ G z) :
    0 ≤ tupleComponent S G := by
  apply expect_nonneg
  intro Y _
  apply expect_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (tupleValidity_nonneg S Y)
    (le_trans (by norm_num) (tupleWeight_one_le S j))) (hG _)
lemma tupleWeight_empty (j : TupleVertex → TupleListIndex ∅) : tupleWeight ∅ j = 1 := by
  simp [tupleWeight, indexWeight, indexEnergy, indexCross, interaction]
lemma tuple_leading_mass {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    |tupleComponent (p := p) ∅ (fun _ => 1) -
        (1 / 2 : ℝ) ^ (tupleListEdges ∅).card| ≤
      ((tupleListEdges ∅).card : ℝ) * ((Real.sqrt p + 1) / (2 * p)) := by
  have heq : tupleComponent (p := p) ∅ (fun _ => 1) =
      𝔼 Y : TupleListEntry ∅ → ZMod p, tupleValidity ∅ Y := by
    simp [tupleComponent, tupleWeight_empty]
  rw [heq]
  exact graph_count hp (tupleListEdges ∅) (tupleListEdges_no_loop ∅) (tupleListEdges_no_opp ∅)
noncomputable def reflectEquiv {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) : Equiv.Perm (WordVertex B h) :=
  Function.Involutive.toPerm (reflect b α β) (reflect_involutive b α β)
lemma interaction_zero_of_unmarked_word {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (hb : b ∉ S) (v w : WordVertex B h)
    (hvw : v b ≠ w b) : interaction S δ v w = 0 := by
  classical
  apply interaction_eq_zero_of_not_neighbour
  intro c hc p heq
  apply hvw
  have hcb : b ≠ c := by intro h; exact hb (h ▸ hc)
  have hh := congrArg (fun v : WordVertex B h => v b) heq
  simpa [vertexSwap, hcb] using hh.symm
lemma unmarked_crossInteraction_zero {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (hb : b ∉ S) {α β : Fin h} (hne : α ≠ β) :
    crossInteraction S δ b α β = 0 := by
  classical
  ext x y
  apply interaction_zero_of_unmarked_word S δ b hb
  intro heq
  have hn : ¬ cutPlus b α β (reflect b α β y.1) :=
    by
      rw [cutPlus_reflect_iff_not b hne]
      exact not_not.mpr y.2
  apply hn
  change (reflect b α β y.1 b).symm α < (reflect b α β y.1 b).symm β
  rw [← heq]
  exact x.2
lemma unmarked_weight_factor {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    {J : Type*} [DecidableEq J] (S : Finset B) (δ : ℝ) (b : B) (hb : b ∉ S)
    {α β : Fin h} (hne : α ≠ β) (j k : CutHalf b α β → J) :
    indexWeight (Matrix.submatrix (interaction S δ) (halfSumEquiv b hne) (halfSumEquiv b hne))
      (Sum.elim j k) =
      indexWeight (Matrix.submatrix (interaction S δ) Subtype.val Subtype.val) j *
      indexWeight (Matrix.submatrix (interaction S δ) Subtype.val Subtype.val) k := by
  classical
  rw [indexWeight_factor]
  · have hz := unmarked_crossInteraction_zero S δ b hb hne
    change indexWeight _ j * Real.exp (indexCross (crossInteraction S δ b α β) j k) *
      indexWeight _ k = _
    rw [hz]
    simp only [indexCross, Matrix.zero_apply, zero_mul, sum_const_zero, Real.exp_zero,
      mul_one]
    rfl
  · intro x y
    exact interaction_symm S δ _ _
  · intro x y
    exact interaction_reflect S δ b α β x.1 y.1
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
noncomputable def tupleAddressReflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) : Equiv.Perm (TupleAddress S) :=
  Function.Involutive.toPerm
    (fun u a => (if a.1 = b then Equiv.swap α β else 1) * u a)
    (by
      intro u
      funext a
      by_cases ha : a.1 = b <;> simp [ha, ← mul_assoc])
lemma tupleProjection_reflect_all (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (v : TupleVertex) :
    tupleProjection S (reflect b α β v) = tupleAddressReflect S b α β (tupleProjection S v) := by
  funext a
  by_cases ha : a.1 = b <;> simp [tupleProjection, reflect, tupleAddressReflect, ha]
noncomputable def tupleEntryReflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) : Equiv.Perm (TupleListEntry S) :=
  Equiv.prodCongr (tupleAddressReflect S b α β) (Equiv.refl _)
lemma tupleListEdges_reflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (e : TupleListEntry S × TupleListEntry S) :
    (tupleEntryReflect S b α β e.1, tupleEntryReflect S b α β e.2) ∈ tupleListEdges S ↔
      e ∈ tupleListEdges S := by
  classical
  unfold tupleListEdges
  split_ifs with hs
  · simp only [mem_filter, mem_univ, true_and]
    exact addressEdge_left_translate tupleCycle (tupleT + 1)
      (fun a : {a : Fin tupleBlocks // a ∉ S} => if a.1 = b then Equiv.swap α β else 1)
      e.1.1 e.2.1
  · simp
lemma tupleValidity_reflect {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (Y : TupleListEntry S → ZMod p) :
    tupleValidity S (Y ∘ tupleEntryReflect S b α β) = tupleValidity S Y := by
  classical
  apply prod_equiv (Equiv.prodCongr (tupleEntryReflect S b α β) (tupleEntryReflect S b α β))
  · intro e
    exact (tupleListEdges_reflect S b α β e).symm
  · intro e _
    rfl
lemma tupleWeight_reflect (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (α β : Fin tupleH) (j : TupleVertex → TupleListIndex S) :
    tupleWeight S (j ∘ reflect b α β) = tupleWeight S j := by
  classical
  have heq : Matrix.submatrix (interaction (h := tupleH) S tupleDelta)
      (reflectEquiv b α β) (reflectEquiv b α β) = interaction S tupleDelta := by
    ext x y
    change interaction S tupleDelta (reflect b α β x) (reflect b α β y) = _
    exact interaction_reflect S tupleDelta b α β x y
  have hh := indexWeight_equiv (reflectEquiv b α β) (interaction S tupleDelta) j
  have hleft : indexWeight (Matrix.submatrix (interaction S tupleDelta)
      (reflectEquiv b α β) (reflectEquiv b α β)) (j ∘ reflect b α β) =
      indexWeight (interaction S tupleDelta) (j ∘ reflect b α β) := congrArg (fun H => indexWeight H (j ∘ reflect b α β)) heq
  exact hleft.symm.trans hh
lemma tupleOutput_reflect {p : ℕ} (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (α β : Fin tupleH) (Y : TupleListEntry S → ZMod p) (j : TupleVertex → TupleListIndex S) :
    tupleOutput S (Y ∘ tupleEntryReflect S b α β) (j ∘ reflect b α β) =
      tupleOutput S Y j ∘ reflect b α β := by
  funext v
  simp only [tupleOutput, Function.comp_def, tupleProjection_reflect_all,
    tupleEntryReflect, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
lemma tupleComponent_reflect {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (G : (TupleVertex → ZMod p) → ℝ) :
    tupleComponent S (fun z => G (z ∘ reflect b α β)) = tupleComponent S G := by
  classical
  symm
  unfold tupleComponent
  rw [expect_precompose (tupleEntryReflect S b α β)
    (fun Y => 𝔼 j : TupleVertex → TupleListIndex S,
      tupleValidity S Y * tupleWeight S j * G (tupleOutput S Y j))]
  apply expect_congr rfl
  intro Y _
  rw [expect_precompose (reflectEquiv b α β)
    (fun j => tupleValidity S (Y ∘ tupleEntryReflect S b α β) *
      tupleWeight S j * G (tupleOutput S (Y ∘ tupleEntryReflect S b α β) j))]
  apply expect_congr rfl
  intro j _
  change tupleValidity S (Y ∘ tupleEntryReflect S b α β) *
      tupleWeight S (j ∘ reflect b α β) *
      G (tupleOutput S (Y ∘ tupleEntryReflect S b α β) (j ∘ reflect b α β)) = _
  rw [tupleValidity_reflect, tupleWeight_reflect, tupleOutput_reflect]
lemma tupleCutForm_symmetric {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH)
    (F G : (CutHalf b α β → ZMod p) → ℝ) :
    tupleComponent S (fun z => F (fun x => z x.1) * G (fun x => z (reflect b α β x.1))) =
      tupleComponent S (fun z => G (fun x => z x.1) * F (fun x => z (reflect b α β x.1))) := by
  rw [← tupleComponent_reflect (p := p) S b α β
    (fun z => G (fun x => z x.1) * F (fun x => z (reflect b α β x.1)))]
  apply congrArg (fun H : (TupleVertex → ZMod p) → ℝ => tupleComponent S H)
  funext z
  change F (fun x => z x.1) * G (fun x => z (reflect b α β x.1)) =
    G (fun x => z (reflect b α β x.1)) *
      F (fun x => z (reflect b α β (reflect b α β x.1)))
  have hz : (fun x : CutHalf b α β => z (reflect b α β (reflect b α β x.1))) =
      fun x : CutHalf b α β => z x.1 := funext fun x => congrArg z (reflect_involutive b α β x.1)
  rw [hz, mul_comm]
def symbolPotential {h : ℕ} (w : Equiv.Perm (Fin h)) : ℤ :=
  ∑ i : Fin h, (i.val : ℤ) * ((w.symm i).val : ℤ)
lemma symbolPotential_swap {h : ℕ} (w : Equiv.Perm (Fin h))
    {α β : Fin h} (hne : α ≠ β) :
    symbolPotential (Equiv.swap α β * w) - symbolPotential w =
      ((β.val : ℤ) - α.val) * (((w.symm α).val : ℤ) - (w.symm β).val) := by
  unfold symbolPotential
  rw [← sum_sub_distrib]
  calc
    _ = ∑ i : Fin h, (
      (if i = α then (α.val : ℤ) * ((w.symm β).val : ℤ) - (α.val : ℤ) * (w.symm α).val else 0) +
      (if i = β then (β.val : ℤ) * ((w.symm α).val : ℤ) - (β.val : ℤ) * (w.symm β).val else 0)) := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i = α
      · subst i
        simp [Equiv.Perm.mul_def, hne]
      · by_cases hj : i = β
        · subst i
          simp [Equiv.Perm.mul_def, hne.symm]
        · simp [Equiv.Perm.mul_def, Equiv.swap_apply_of_ne_of_ne hi hj, hi, hj]
    _ = _ := by
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
      ring
def wordPotential {B : Type*} [Fintype B] {h : ℕ} (v : WordVertex B h) : ℤ :=
  ∑ b : B, symbolPotential (v b)
lemma wordPotential_reflect {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hne : α ≠ β) (v : WordVertex B h) :
    wordPotential (reflect b α β v) - wordPotential v =
      ((β.val : ℤ) - α.val) * (((v b).symm α).val - ((v b).symm β).val) := by
  unfold wordPotential
  rw [← sum_sub_distrib, sum_eq_single b]
  · simpa [reflect] using symbolPotential_swap (v b) hne
  · intro c _ hcb
    simp [reflect, hcb]
  · simp
def foldWord {B : Type*} [DecidableEq B] {h : ℕ} (b : B) (α β : Fin h)
    (v : WordVertex B h) : WordVertex B h :=
  if cutPlus b α β v then v else reflect b α β v
lemma foldWord_potential_le {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hab : α < β) (v : WordVertex B h) :
    wordPotential v ≤ wordPotential (foldWord b α β v) := by
  unfold foldWord
  split_ifs with hv
  · exact le_rfl
  · have hgap := wordPotential_reflect b hab.ne v
    have h₁ : 0 ≤ (β.val : ℤ) - α.val := sub_nonneg.mpr (by exact_mod_cast hab.le)
    have h₂ : 0 ≤ (((v b).symm α).val : ℤ) - ((v b).symm β).val := by
      have hh : (v b).symm β ≤ (v b).symm α := le_of_not_gt hv
      exact sub_nonneg.mpr (by exact_mod_cast hh)
    have := mul_nonneg h₁ h₂
    omega
lemma foldWord_potential_lt {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hab : α < β) (v : WordVertex B h)
    (hv : ¬ cutPlus b α β v) :
    wordPotential v < wordPotential (foldWord b α β v) := by
  rw [foldWord, if_neg hv]
  have hgap := wordPotential_reflect b hab.ne v
  have h₁ : 0 < (β.val : ℤ) - α.val := sub_pos.mpr (by exact_mod_cast hab)
  have h₂ : 0 < (((v b).symm α).val : ℤ) - ((v b).symm β).val := by
    have hh : (v b).symm β < (v b).symm α :=
      lt_of_le_of_ne (le_of_not_gt hv) (by intro hh; exact hab.ne ((v b).symm.injective hh.symm))
    exact sub_pos.mpr (by exact_mod_cast hh)
  have := mul_pos h₁ h₂
  omega
lemma exists_unsorted_cut {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (hv : v ≠ fun _ => 1) :
    ∃ b : B, ∃ α β : Fin h, α < β ∧ ¬ cutPlus b α β v := by
  by_contra! hn
  apply hv
  funext b
  have hm : Monotone ((v b).symm) := by
    intro α β hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    · exact (hn b α β hab).le
  have heq : (v b).symm = 1 := (Equiv.Perm.monotone_iff _).mp hm
  exact inv_eq_one.mp heq
abbrev WordCut (B : Type*) (h : ℕ) := B × PositionPair h
def foldMap {B : Type*} [DecidableEq B] {h : ℕ} (cs : List (WordCut B h)) :
    WordVertex B h → WordVertex B h :=
  cs.foldr (fun c f => foldWord c.1 c.2.1.1 c.2.1.2 ∘ f) id
lemma exists_constant_fold {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ} :
    ∃ cs : List (WordCut B h), ∀ v : WordVertex B h, foldMap cs v = fun _ => 1 := by
  classical
  let R : Finset (WordVertex B h → WordVertex B h) :=
    univ.filter fun f => ∃ cs : List (WordCut B h), foldMap cs = f
  have hR : R.Nonempty := ⟨id, mem_filter.mpr ⟨mem_univ _, ⟨[], rfl⟩⟩⟩
  obtain ⟨f, hf, hmax⟩ := R.exists_max_image (fun f => ∑ v, wordPotential (f v)) hR
  obtain ⟨cs, rfl⟩ := (mem_filter.mp hf).2
  refine ⟨cs, fun v => ?_⟩
  by_contra hv
  obtain ⟨b, α, β, hab, hv⟩ := exists_unsorted_cut (foldMap cs v) hv
  let c : WordCut B h := (b, ⟨(α, β), hab⟩)
  have hmem : foldMap (c :: cs) ∈ R :=
    mem_filter.mpr ⟨mem_univ _, ⟨c :: cs, rfl⟩⟩
  have hlt : (∑ w : WordVertex B h, wordPotential (foldMap cs w)) <
      ∑ w : WordVertex B h, wordPotential (foldMap (c :: cs) w) := by
    apply sum_lt_sum
    · intro w _
      exact foldWord_potential_le b hab (foldMap cs w)
    · exact ⟨v, mem_univ _, foldWord_potential_lt b hab (foldMap cs v) hv⟩
  exact (not_lt_of_ge (hmax _ hmem)) hlt
lemma max_fold_preserved {V A : Type*} [Fintype V] [Fintype A]
    (Λ : (V → A) → ℝ) {M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ a, |Λ a| ≤ M) (φ ψ : V → V)
    (hfold : ∀ a, |Λ a| ^ 2 ≤ Λ (a ∘ φ) * Λ (a ∘ ψ))
    (hpos : ∀ a, 0 ≤ Λ (a ∘ φ) ∧ 0 ≤ Λ (a ∘ ψ))
    (a : V → A) (ha : |Λ a| = M) : |Λ (a ∘ φ)| = M := by
  have hx := (hpos a).1
  have hy := (hpos a).2
  have hxy := hfold a
  have hxb := hbound (a ∘ φ)
  have hyb := hbound (a ∘ ψ)
  rw [ha] at hxy
  rw [abs_of_nonneg hx] at hxb ⊢
  rw [abs_of_nonneg hy] at hyb
  nlinarith [mul_le_mul_of_nonneg_left hyb hx,
    mul_le_mul_of_nonneg_left hxb hx, sq_nonneg (M - Λ (a ∘ φ))]
lemma word_folding_maximum {B A : Type*} [Fintype B] [DecidableEq B]
    [Fintype A] [Nonempty A] {h : ℕ}
    (Λ : (WordVertex B h → A) → ℝ)
    (hfold : ∀ b α β, α ≠ β → ∀ a,
      |Λ a| ^ 2 ≤ Λ (a ∘ foldWord b α β) * Λ (a ∘ foldWord b β α))
    (hpos : ∀ b α β, α ≠ β → ∀ a, 0 ≤ Λ (a ∘ foldWord b α β)) :
    ∃ i : A, ∀ a : WordVertex B h → A, |Λ a| ≤ |Λ (fun _ => i)| := by
  classical
  obtain ⟨a, _, hmax⟩ := univ.exists_max_image (fun a : WordVertex B h → A => |Λ a|)
    univ_nonempty
  have hbnd : ∀ a', |Λ a'| ≤ |Λ a| := fun a' => hmax a' (mem_univ _)
  have hpres (b : B) (α β : Fin h) (hne : α ≠ β) (a' : WordVertex B h → A)
      (ha' : |Λ a'| = |Λ a|) : |Λ (a' ∘ foldWord b α β)| = |Λ a| :=
    max_fold_preserved Λ (abs_nonneg _) hbnd _ _ (hfold b α β hne)
      (fun a' => ⟨hpos b α β hne a', hpos b β α hne.symm a'⟩) a' ha'
  have hseq (cs : List (WordCut B h)) (a' : WordVertex B h → A)
      (ha' : |Λ a'| = |Λ a|) : |Λ (a' ∘ foldMap cs)| = |Λ a| := by
    induction cs generalizing a' with
    | nil => exact ha'
    | cons c cs ih =>
      exact ih (a' ∘ foldWord c.1 c.2.1.1 c.2.1.2)
        (hpres c.1 c.2.1.1 c.2.1.2 c.2.2.ne a' ha')
  obtain ⟨cs, hcs⟩ := exists_constant_fold (B := B) (h := h)
  have heq : a ∘ foldMap cs = fun _ => a (fun _ => 1) := funext fun v => congrArg a (hcs v)
  refine ⟨a (fun _ => 1), fun a' => ?_⟩
  have hs := hseq cs a rfl
  rw [heq] at hs
  exact (hbnd a').trans_eq hs.symm
noncomputable def graphValidity {I : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (z : I → ZMod p) : ℝ :=
  ∏ e ∈ E, squareIndicator (z e.2 - z e.1)
lemma graphValidity_all {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset (I × I)) (z : I → ZMod p) :
    graphValidity E z = ∏ i, ∏ j, if (i,j) ∈ E then squareIndicator (z j - z i) else 1 := by
  classical
  rw [graphValidity, ← Fintype.prod_ite_mem]
  rw [← univ_product_univ, prod_product]
noncomputable def cutInternalEdges {I : Type*} [Fintype I]
    (E : Finset ((I ⊕ I) × (I ⊕ I))) : Finset (I × I) := by
  classical
  exact univ.filter fun e => (Sum.inl e.1, Sum.inl e.2) ∈ E
noncomputable def cutCrossEdges {I : Type*} [Fintype I]
    (E : Finset ((I ⊕ I) × (I ⊕ I))) : Finset (I × I) := by
  classical
  exact univ.filter fun e => (Sum.inl e.1, Sum.inr e.2) ∈ E ∨
    (Sum.inr e.2, Sum.inl e.1) ∈ E
noncomputable def cutCrossDirection {I : Type*}
    (E : Finset ((I ⊕ I) × (I ⊕ I))) (i j : I) : Bool := by
  classical
  exact decide ((Sum.inl i, Sum.inr j) ∈ E)
lemma cutCrossEdges_factor {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset ((I ⊕ I) × (I ⊕ I)))
    (hnoopp : ∀ e ∈ E, (e.2,e.1) ∉ E) (x y : I → ZMod p) :
    listKernel (cutCrossEdges E) (cutCrossDirection E) x y =
      (∏ i, ∏ j, if (Sum.inl i, Sum.inr j) ∈ E then squareIndicator (y j - x i) else 1) *
      (∏ j, ∏ i, if (Sum.inr j, Sum.inl i) ∈ E then squareIndicator (x i - y j) else 1) := by
  classical
  rw [listKernel, ← Fintype.prod_ite_mem, ← univ_product_univ, prod_product]
  rw [prod_comm (f := fun j i => if (Sum.inr j, Sum.inl i) ∈ E then
    squareIndicator (x i - y j) else 1)]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  by_cases hpm : (Sum.inl i, Sum.inr j) ∈ E
  · have hmp := hnoopp _ hpm
    simp [cutCrossEdges, cutCrossDirection, hpm, hmp]
  · by_cases hmp : (Sum.inr j, Sum.inl i) ∈ E <;>
      simp [cutCrossEdges, cutCrossDirection, hpm, hmp]
lemma graphValidity_cut {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset ((I ⊕ I) × (I ⊕ I)))
    (hnoopp : ∀ e ∈ E, (e.2,e.1) ∉ E)
    (href : ∀ i j, (Sum.inr i, Sum.inr j) ∈ E ↔ (Sum.inl i, Sum.inl j) ∈ E)
    (x y : I → ZMod p) :
    graphValidity E (Sum.elim x y) =
      graphValidity (cutInternalEdges E) x * graphValidity (cutInternalEdges E) y *
        listKernel (cutCrossEdges E) (cutCrossDirection E) x y := by
  classical
  rw [graphValidity_all, Fintype.prod_sum_type]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, prod_mul_distrib]
  rw [cutCrossEdges_factor E hnoopp, graphValidity_all, graphValidity_all]
  simp only [cutInternalEdges, mem_filter, mem_univ, true_and, href]
  ring
lemma graphValidity_nonneg {I : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (z : I → ZMod p) : 0 ≤ graphValidity E z := by
  exact prod_nonneg fun e _ => squareIndicator_nonneg _
lemma graphValidity_sq {I : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (z : I → ZMod p) : graphValidity E z ^ 2 = graphValidity E z := by
  classical
  unfold graphValidity
  rw [← prod_pow]
  apply prod_congr rfl
  intro e _
  unfold squareIndicator
  split_ifs <;> norm_num
lemma list_quadratic_lower {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (E : Finset (I × I))
    (dir : I → I → Bool) (f : (I → ZMod p) → ℝ) :
    -(32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) *
      (𝔼 x : I → ZMod p, (f x)^2) ≤
      𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, f x * listKernel E dir x y * f y := by
  have h := list_mixing hp E dir f f
  have hv : 0 ≤ 𝔼 x : I → ZMod p, (f x)^2 := expect_nonneg (fun _ _ => sq_nonneg _)
  have hs : Real.sqrt (𝔼 x : I → ZMod p, (f x)^2) *
      Real.sqrt (𝔼 x : I → ZMod p, (f x)^2) = 𝔼 x : I → ZMod p, (f x)^2 :=
    Real.mul_self_sqrt hv
  rw [mul_assoc, hs] at h
  have hex : (𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p,
      f x * (listKernel E dir x y - (1/2:ℝ)^E.card) * f y) =
      (𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, f x * listKernel E dir x y * f y) -
        (1/2:ℝ)^E.card * (𝔼 x : I → ZMod p, f x)^2 := by
    simp only [sub_mul, mul_sub, expect_sub_distrib, ← expect_mul, ← mul_expect]
    ring
  rw [hex] at h
  have hc : 0 ≤ (1/2:ℝ)^E.card * (𝔼 x : I → ZMod p, f x)^2 := by positivity
  have hl := (abs_le.mp h).1
  nlinarith
open scoped Classical
noncomputable def graphPullback {I K : Type*} [Fintype I]
    (e : I ≃ K) (E : Finset (K × K)) : Finset (I × I) := by
  classical
  exact univ.filter fun ij => (e ij.1, e ij.2) ∈ E
lemma graphValidity_pullback {I K : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (e : I ≃ K) (E : Finset (K × K)) (z : K → ZMod p) :
    graphValidity (graphPullback e E) (z ∘ e) = graphValidity E z := by
  classical
  apply prod_equiv (Equiv.prodCongr e e)
  · intro ij
    simp only [graphPullback, mem_filter, mem_univ, true_and, Equiv.prodCongr_apply]
    rfl
  · intro ij _
    rfl
abbrev TupleHalfAddress (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    (α β : Fin tupleH) := CutHalf (⟨b, hb⟩ : {c : Fin tupleBlocks // c ∉ S}) α β
abbrev TupleHalfEntry (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    (α β : Fin tupleH) := TupleHalfAddress S b hb α β × TupleListIndex S
noncomputable instance tupleHalfEntryFintype (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) (α β : Fin tupleH) :
    Fintype (TupleHalfEntry S b hb α β) := by
  classical
  unfold TupleHalfEntry
  infer_instance
noncomputable def tupleEntryHalfEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    TupleHalfEntry S b hb α β ⊕ TupleHalfEntry S b hb α β ≃ TupleListEntry S :=
  (Equiv.sumProdDistrib _ _ _).symm.trans
    (Equiv.prodCongr (halfSumEquiv (⟨b, hb⟩ : {c : Fin tupleBlocks // c ∉ S}) hne) (Equiv.refl _))
lemma tupleEntryHalfEquiv_inl (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a : TupleHalfEntry S b hb α β) :
    tupleEntryHalfEquiv S b hb hne (Sum.inl a) = (a.1.1, a.2) := rfl
lemma tupleEntryHalfEquiv_inr (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a : TupleHalfEntry S b hb α β) :
    tupleEntryHalfEquiv S b hb hne (Sum.inr a) =
      tupleEntryReflect S b α β (a.1.1, a.2) := by
  apply Prod.ext
  · funext c
    change reflect (⟨b,hb⟩ : {c : Fin tupleBlocks // c ∉ S}) α β a.1.1 c =
      (if c.1 = b then Equiv.swap α β else 1) * a.1.1 c
    have he : c = ⟨b,hb⟩ ↔ c.1 = b := Subtype.ext_iff
    by_cases hc : c = ⟨b,hb⟩
    · subst c; simp [reflect]
    · have hc' : c.1 ≠ b := fun h => hc (he.mpr h)
      simp [reflect, hc, hc']
  · rfl
def tupleHalfProjection (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (hb : b ∉ S) (α β : Fin tupleH) (x : CutHalf b α β) : TupleHalfAddress S b hb α β :=
  ⟨tupleProjection S x.1, x.2⟩
noncomputable def tupleHalfWeight (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (j : CutHalf b α β → TupleListIndex S) : ℝ :=
  indexWeight (Matrix.submatrix (interaction S tupleDelta) Subtype.val Subtype.val) j
noncomputable def tupleUnmarkedGraph (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :=
  graphPullback (tupleEntryHalfEquiv S b hb hne) (tupleListEdges S)
lemma tupleUnmarkedGraph_noopp (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    ∀ e ∈ tupleUnmarkedGraph S b hb hne, (e.2,e.1) ∉ tupleUnmarkedGraph S b hb hne := by
  classical
  intro e he hh
  simp only [tupleUnmarkedGraph, graphPullback, mem_filter, mem_univ, true_and] at he hh
  exact tupleListEdges_no_opp S _ he hh
lemma tupleUnmarkedGraph_reflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a c : TupleHalfEntry S b hb α β) :
    (Sum.inr a, Sum.inr c) ∈ tupleUnmarkedGraph S b hb hne ↔
      (Sum.inl a, Sum.inl c) ∈ tupleUnmarkedGraph S b hb hne := by
  classical
  simp only [tupleUnmarkedGraph, graphPullback, mem_filter, mem_univ, true_and,
    tupleEntryHalfEquiv_inl, tupleEntryHalfEquiv_inr]
  exact tupleListEdges_reflect S b α β ((a.1.1,a.2),(c.1.1,c.2))
lemma tupleOutput_half (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    {p : ℕ} (x y : TupleHalfEntry S b hb α β → ZMod p)
    (j k : CutHalf b α β → TupleListIndex S) :
    tupleOutput S ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm)
      ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) ∘ (halfSumEquiv b hne) =
      Sum.elim (fun v => x (tupleHalfProjection S b hb α β v, j v))
        (fun v => y (tupleHalfProjection S b hb α β v, k v)) := by
  funext v
  rcases v with v | v
  · change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
        (tupleProjection S v.1, (Sum.elim j k) ((halfSumEquiv b hne).symm ((halfSumEquiv b hne) (Sum.inl v))))) = _
    rw [Equiv.symm_apply_apply]
    change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
      ((tupleEntryHalfEquiv S b hb hne) (Sum.inl (tupleHalfProjection S b hb α β v, j v)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  · change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
        (tupleProjection S (reflect b α β v.1),
          (Sum.elim j k) ((halfSumEquiv b hne).symm ((halfSumEquiv b hne) (Sum.inr v))))) = _
    rw [Equiv.symm_apply_apply]
    change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
      (tupleProjection S (reflect b α β v.1), k v)) = _
    rw [tupleProjection_reflect_all]
    have he := tupleEntryHalfEquiv_inr S b hb hne (tupleHalfProjection S b hb α β v, k v)
    change _ = (tupleAddressReflect S b α β (tupleProjection S v.1), k v) at he
    rw [← he, Equiv.symm_apply_apply]
    rfl
lemma tupleHalfWeight_one_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (j : CutHalf b α β → TupleListIndex S) :
    1 ≤ tupleHalfWeight S b α β j :=
  one_le_indexWeight _ (fun _ _ => interaction_nonneg S tupleDelta_pos.le _ _) j
lemma tupleHalfWeight_le (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (j : CutHalf b α β → TupleListIndex S) : tupleHalfWeight S b α β j ≤ tupleWeightBound := by
  let J := (Sum.elim j j) ∘ (halfSumEquiv b hne).symm
  have hW := tupleWeight_le S hS J
  have he := indexWeight_equiv (halfSumEquiv b hne) (interaction S tupleDelta) J
  have hj : J ∘ halfSumEquiv b hne = Sum.elim j j := by
    funext x
    exact congrArg (Sum.elim j j) ((halfSumEquiv b hne).symm_apply_apply x)
  rw [hj, unmarked_weight_factor S tupleDelta b hb hne] at he
  change tupleHalfWeight S b α β j * tupleHalfWeight S b α β j = tupleWeight S J at he
  rw [← he] at hW
  have h1 := tupleHalfWeight_one_le S b α β j
  nlinarith
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical
lemma expect_two_halves {I L K V A J : Type*} [Fintype I] [Fintype L] [Fintype K]
    [Fintype V] [Fintype A] [Fintype J] [DecidableEq I] [DecidableEq L]
    [DecidableEq K] [DecidableEq V]
    (e : I ⊕ I ≃ K) (f : L ⊕ L ≃ V) (G : (K → A) → (V → J) → ℝ) :
    (𝔼 Y : K → A, 𝔼 j : V → J, G Y j) =
      𝔼 x : I → A, 𝔼 y : I → A, 𝔼 j : L → J, 𝔼 k : L → J,
        G ((Sum.elim x y) ∘ e.symm) ((Sum.elim j k) ∘ f.symm) := by
  rw [expect_precompose e.symm, expect_sum_function]
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  rw [expect_precompose f.symm, expect_sum_function]
lemma tupleValidity_half {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (x y : TupleHalfEntry S b hb α β → ZMod p) :
    tupleValidity S ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm) =
      graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) x *
      graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) y *
      listKernel (cutCrossEdges (tupleUnmarkedGraph S b hb hne))
        (cutCrossDirection (tupleUnmarkedGraph S b hb hne)) x y := by
  let e := tupleEntryHalfEquiv S b hb hne
  have hh := graphValidity_pullback e (tupleListEdges S) ((Sum.elim x y) ∘ e.symm)
  have he : ((Sum.elim x y) ∘ e.symm) ∘ e = Sum.elim x y := by
    funext z
    exact congrArg (Sum.elim x y) (e.symm_apply_apply z)
  rw [he] at hh
  change graphValidity (tupleUnmarkedGraph S b hb hne) (Sum.elim x y) = _ at hh
  change graphValidity (tupleListEdges S) _ = _
  rw [← hh]
  exact graphValidity_cut _ (tupleUnmarkedGraph_noopp S b hb hne)
    (tupleUnmarkedGraph_reflect S b hb hne) x y
lemma tupleWeight_half (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (j k : CutHalf b α β → TupleListIndex S) :
    tupleWeight S ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) =
      tupleHalfWeight S b α β j * tupleHalfWeight S b α β k := by
  have hh := indexWeight_equiv (halfSumEquiv b hne) (interaction S tupleDelta)
    ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm)
  have he : ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) ∘ (halfSumEquiv b hne) =
      Sum.elim j k := by
    funext z
    exact congrArg (Sum.elim j k) ((halfSumEquiv b hne).symm_apply_apply z)
  rw [he, unmarked_weight_factor S tupleDelta b hb hne] at hh
  exact hh.symm
lemma tupleCutForm_unmarked_factor {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) (F : (CutHalf b α β → ZMod p) → ℝ) :
    tupleCutForm S b α β F =
      𝔼 x : TupleHalfEntry S b hb α β → ZMod p,
      𝔼 y : TupleHalfEntry S b hb α β → ZMod p,
      𝔼 j : CutHalf b α β → TupleListIndex S,
      𝔼 k : CutHalf b α β → TupleListIndex S,
        graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) x *
        graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) y *
        listKernel (cutCrossEdges (tupleUnmarkedGraph S b hb hne))
          (cutCrossDirection (tupleUnmarkedGraph S b hb hne)) x y *
        (tupleHalfWeight S b α β j * tupleHalfWeight S b α β k) *
        F (fun v => x (tupleHalfProjection S b hb α β v, j v)) *
        F (fun v => y (tupleHalfProjection S b hb α β v, k v)) := by
  classical
  unfold tupleCutForm tupleComponent
  rw [expect_two_halves (tupleEntryHalfEquiv S b hb hne) (halfSumEquiv b hne)]
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  apply expect_congr rfl
  intro j _
  apply expect_congr rfl
  intro k _
  rw [tupleValidity_half S b hb hne, tupleWeight_half S b hb hne]
  have hh := tupleOutput_half S b hb hne x y j k
  have hl : (fun v : CutHalf b α β => tupleOutput S
      ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm)
      ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) v.1) =
      fun v => x (tupleHalfProjection S b hb α β v, j v) := by
    funext v
    exact congrFun hh (Sum.inl v)
  have hr : (fun v : CutHalf b α β => tupleOutput S
      ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm)
      ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) (reflect b α β v.1)) =
      fun v => y (tupleHalfProjection S b hb α β v, k v) := by
    funext v
    exact congrFun hh (Sum.inr v)
  dsimp only
  rw [hl, hr]
  ring
lemma weighted_average_sq_le {J : Type*} [Fintype J] [Nonempty J]
    (W f : J → ℝ) {B : ℝ} (hW : ∀ j, 0 ≤ W j ∧ W j ≤ B) :
    (𝔼 j : J, W j * f j)^2 ≤ B^2 * (𝔼 j : J, (f j)^2) := by
  have hc := expect_mul_sq_le_sq_mul_sq univ W f
  have hw : (𝔼 j : J, (W j)^2) ≤ B^2 :=
    expect_le univ_nonempty (fun j _ => pow_le_pow_left₀ (hW j).1 (hW j).2 _)
  exact hc.trans (mul_le_mul_of_nonneg_right hw (expect_nonneg fun _ _ => sq_nonneg _))
lemma list_factorized_quadratic {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq L] [Nonempty J] {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (dir : I → I → Bool)
    (K : (I → ZMod p) → ℝ) (W : (L → J) → ℝ)
    (f : (I → ZMod p) → (L → J) → ℝ) :
    (𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, 𝔼 j : L → J, 𝔼 k : L → J,
      K x * K y * listKernel E dir x y * (W j * W k) * f x j * f y k) =
      𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p,
        (K x * (𝔼 j : L → J, W j * f x j)) * listKernel E dir x y *
          (K y * (𝔼 k : L → J, W k * f y k)) := by
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  conv_lhs => arg 2; ext j; arg 2; ext k; rw [show
    K x * K y * listKernel E dir x y * (W j * W k) * f x j * f y k =
      (K x * listKernel E dir x y * K y) * ((W j * f x j) * (W k * f y k)) by ring]
  simp only [← mul_expect, ← expect_mul]
  ring
lemma list_factorized_lower {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq L] [Nonempty J] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × I)) (dir : I → I → Bool)
    (K : (I → ZMod p) → ℝ) (hK : ∀ x, 0 ≤ K x ∧ (K x)^2 = K x)
    (W : (L → J) → ℝ) {B : ℝ} (hW : ∀ j, 0 ≤ W j ∧ W j ≤ B)
    (f : (I → ZMod p) → (L → J) → ℝ) :
    -(32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) * B^2 *
      (𝔼 x : I → ZMod p, 𝔼 j : L → J, K x * (f x j)^2) ≤
      𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, 𝔼 j : L → J, 𝔼 k : L → J,
        K x * K y * listKernel E dir x y * (W j * W k) * f x j * f y k := by
  rw [list_factorized_quadratic]
  let G (x : I → ZMod p) := K x * (𝔼 j : L → J, W j * f x j)
  have h := list_quadratic_lower hp E dir G
  have hg : (𝔼 x : I → ZMod p, (G x)^2) ≤
      B^2 * (𝔼 x : I → ZMod p, 𝔼 j : L → J, K x * (f x j)^2) := by
    rw [mul_expect]
    apply expect_le_expect
    intro x _
    dsimp [G]
    rw [mul_pow, (hK x).2, ← mul_expect]
    calc
      _ ≤ K x * (B^2 * (𝔼 j : L → J, (f x j)^2)) :=
        mul_le_mul_of_nonneg_left (weighted_average_sq_le W (f x) hW) (hK x).1
      _ = _ := by ring
  have hc : 0 ≤ (32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) := by positivity
  have hm := mul_le_mul_of_nonpos_left hg (neg_nonpos.mpr hc)
  change _ ≤ 𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, G x * listKernel E dir x y * G y
  calc
    _ = -((32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8)) *
      (B^2 * (𝔼 x : I → ZMod p, 𝔼 j : L → J, K x * (f x j)^2)) := by ring
    _ ≤ -((32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8)) *
      (𝔼 x : I → ZMod p, (G x)^2) := hm
    _ ≤ _ := by simpa only [neg_mul] using h
noncomputable def tupleUnmarkedMoment {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) (F : (CutHalf b α β → ZMod p) → ℝ) : ℝ :=
  𝔼 x : TupleHalfEntry S b hb α β → ZMod p,
  𝔼 j : CutHalf b α β → TupleListIndex S,
    graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) x *
      (F (fun v => x (tupleHalfProjection S b hb α β v, j v))) ^ 2
lemma tupleUnmarkedMoment_nonneg {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleUnmarkedMoment S b hb hne F :=
  expect_nonneg fun _ _ => expect_nonneg fun _ _ =>
    mul_nonneg (graphValidity_nonneg _ _) (sq_nonneg _)
lemma tuple_unmarked_error_exact {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    -(32 * (cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card : ℝ) ^ ((1 : ℝ) / 4) *
      (p : ℝ) ^ (-(1 : ℝ) / 8) * tupleWeightBound ^ 2 *
        tupleUnmarkedMoment S b hb hne F ≤ tupleCutForm S b α β F := by
  rw [tupleCutForm_unmarked_factor S b hb hne]
  exact list_factorized_lower hp _ _ _ (fun x =>
    ⟨graphValidity_nonneg _ x, graphValidity_sq _ x⟩)
    (tupleHalfWeight S b α β) (fun j =>
      ⟨(tupleHalfWeight_one_le S b α β j).trans' (by norm_num),
        tupleHalfWeight_le S hS b hb hne j⟩) _
lemma card_tupleHalfEntry_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) (α β : Fin tupleH) :
    Fintype.card (TupleHalfEntry S b hb α β) ≤ Fintype.card TupleVertex := by
  classical
  have hsub : Fintype.card (TupleHalfAddress S b hb α β) ≤
      (Nat.factorial tupleH) ^ (tupleBlocks - S.card) := by
    rw [← card_tupleAddress S]
    exact Fintype.card_subtype_le _
  have hS : S.card ≤ tupleBlocks := by
    simpa using (card_le_card (subset_univ S))
  have hr : tupleR ≤ Nat.factorial tupleH := Nat.div_le_self _ _
  rw [card_tupleVertex]
  rw [show Fintype.card (TupleHalfEntry S b hb α β) =
      Fintype.card (TupleHalfAddress S b hb α β) * (tupleR ^ S.card) by
        simp only [TupleHalfEntry, Fintype.card_prod, TupleListIndex, Fintype.card_fin]]
  calc
    _ ≤ (Nat.factorial tupleH) ^ (tupleBlocks - S.card) *
        (Nat.factorial tupleH) ^ S.card := Nat.mul_le_mul hsub (Nat.pow_le_pow_left hr _)
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hS]
lemma card_relation_le_sq {I : Type*} [Fintype I] (E : Finset (I × I))
    {d : ℕ} (hd : Fintype.card I ≤ d) : E.card ≤ d^2 := by
  calc
    _ ≤ Fintype.card (I × I) := card_le_univ _
    _ = (Fintype.card I)^2 := by rw [Fintype.card_prod, sq]
    _ ≤ _ := Nat.pow_le_pow_left hd _
lemma card_tupleCrossEdges_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    (cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card ≤ (Fintype.card TupleVertex)^2 :=
  card_relation_le_sq _ (card_tupleHalfEntry_le S b hb α β)
noncomputable def tupleUnmarkedConstant : ℝ :=
  (32 * (Fintype.card TupleVertex : ℝ)^2) ^ ((1 : ℝ) / 4) * tupleWeightBound^2
lemma tuple_unmarked_error {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    -tupleUnmarkedConstant * (p : ℝ)^(-(1 : ℝ)/8) *
      tupleUnmarkedMoment S b hb hne F ≤ tupleCutForm S b α β F := by
  have hc : (32 * ((cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card : ℝ)) ^ ((1:ℝ)/4) ≤
      (32 * (Fintype.card TupleVertex : ℝ)^2) ^ ((1:ℝ)/4) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have ht : ((cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card : ℝ) ≤
        (Fintype.card TupleVertex : ℝ)^2 := by
      exact_mod_cast card_tupleCrossEdges_le S b hb hne
    linarith
  have hm : 0 ≤ (p : ℝ)^(-(1:ℝ)/8) * tupleWeightBound^2 *
      tupleUnmarkedMoment S b hb hne F :=
    mul_nonneg (by positivity) (tupleUnmarkedMoment_nonneg S b hb hne F)
  have ht := mul_le_mul_of_nonneg_right hc hm
  have he := tuple_unmarked_error_exact hp S hS b hb hne F
  dsimp [tupleUnmarkedConstant]
  nlinarith
lemma tupleUnmarkedGraph_terminal (S : Finset (Fin tupleBlocks))
    (hs : S.card = tupleT + 1) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) :
    tupleUnmarkedGraph S b hb hne = ∅ := by
  have ht : ¬ S.card ≤ tupleT := by omega
  simp [tupleUnmarkedGraph, graphPullback, tupleListEdges, ht]
lemma tuple_terminal_positive {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset (Fin tupleBlocks)) (hs : S.card = tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleCutForm S b α β F := by
  have h := tuple_unmarked_error_exact hp S (by omega) b hb hne F
  simpa only [tupleUnmarkedGraph_terminal S hs b hb hne, cutCrossEdges,
    notMem_empty, or_self, filter_false, card_empty, Nat.cast_zero, mul_zero,
    Real.zero_rpow (by norm_num : (1 : ℝ)/4 ≠ 0), neg_zero, zero_mul] using h
abbrev TupleCutWord (α β : Fin tupleH) :=
  {w : Equiv.Perm (Fin tupleH) // w.symm α < w.symm β}
noncomputable def orderedPermEquiv {h : ℕ} (α β : Fin h) :
    {w : Equiv.Perm (Fin h) // w.symm α < w.symm β} ≃ (CutHalf () α β : Type) where
  toFun w := ⟨fun _ => w.1, w.2⟩
  invFun w := ⟨w.1 (), w.2⟩
  left_inv _ := rfl
  right_inv w := by ext u; cases u; rfl
lemma card_orderedPerm {h : ℕ} {α β : Fin h} (hne : α ≠ β) :
    Fintype.card {w : Equiv.Perm (Fin h) // w.symm α < w.symm β} = Nat.factorial h / 2 := by
  have hh := card_cutHalf () hne
  rw [← Fintype.card_congr (orderedPermEquiv α β), Fintype.card_unit, pow_one] at hh
  omega
lemma card_tupleCutWord {α β : Fin tupleH} (hne : α ≠ β) :
    Fintype.card (TupleCutWord α β) = tupleR :=
  card_orderedPerm hne
def tupleMarkAddress (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (a : TupleAddress S) : TupleAddress (insert b S) :=
  fun c => a ⟨c.1, fun hc => c.2 (mem_insert_of_mem hc)⟩
def tupleUnmarkAddress (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (u : TupleAddress (insert b S)) (w : Equiv.Perm (Fin tupleH)) : TupleAddress S :=
  fun c => if hc : c.1 = b then w else u ⟨c.1, by simp [hc, c.2]⟩
lemma tupleUnmarkAddress_at (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S)
    (u : TupleAddress (insert b S)) (w : Equiv.Perm (Fin tupleH)) :
    tupleUnmarkAddress S b u w ⟨b, hb⟩ = w := by
  simp [tupleUnmarkAddress]
lemma tupleMark_unmark (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (u : TupleAddress (insert b S)) (w : Equiv.Perm (Fin tupleH)) :
    tupleMarkAddress S b (tupleUnmarkAddress S b u w) = u := by
  funext c
  have hb : c.1 ≠ b := by intro h; exact c.2 (by simp [h])
  simp [tupleMarkAddress, tupleUnmarkAddress, hb]
lemma tupleUnmark_mark (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (hb : b ∉ S) (a : TupleAddress S) :
    tupleUnmarkAddress S b (tupleMarkAddress S b a) (a ⟨b,hb⟩) = a := by
  funext c
  by_cases hc : c.1 = b
  · have he : c = ⟨b,hb⟩ := Subtype.ext hc
    subst c
    simp [tupleUnmarkAddress]
  · simp [tupleUnmarkAddress, tupleMarkAddress, hc]
noncomputable def tupleHalfAddressEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) (α β : Fin tupleH) :
    TupleHalfAddress S b hb α β ≃ TupleAddress (insert b S) × TupleCutWord α β where
  toFun a := (tupleMarkAddress S b a.1, ⟨a.1 ⟨b,hb⟩, a.2⟩)
  invFun a := ⟨tupleUnmarkAddress S b a.1 a.2.1, by
    change (tupleUnmarkAddress S b a.1 a.2.1 ⟨b,hb⟩).symm α <
      (tupleUnmarkAddress S b a.1 a.2.1 ⟨b,hb⟩).symm β
    rw [tupleUnmarkAddress_at]
    exact a.2.2⟩
  left_inv a := Subtype.ext (tupleUnmark_mark S b hb a.1)
  right_inv a := by
    apply Prod.ext
    · exact tupleMark_unmark S b a.1 a.2.1
    · apply Subtype.ext
      exact tupleUnmarkAddress_at S b hb a.1 a.2.1
noncomputable def tupleMarkIndexEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    TupleListIndex (insert b S) ≃ TupleCutWord α β × TupleListIndex S :=
  Fintype.equivOfCardEq (by
    simp only [TupleListIndex, Fintype.card_fin, Fintype.card_prod,
      card_tupleCutWord hne, card_insert_of_notMem hb, pow_succ, mul_comm])
noncomputable def tupleRegroupEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    TupleHalfEntry S b hb α β ≃ TupleListEntry (insert b S) :=
  ((Equiv.prodCongr (tupleHalfAddressEquiv S b hb α β) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)).trans
      (Equiv.prodCongr (Equiv.refl _) (tupleMarkIndexEquiv S b hb hne).symm)
lemma expect_ge_single {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) (i : I) :
    (Fintype.card I : ℝ)⁻¹ * f i ≤ 𝔼 j : I, f j := by
  rw [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  rw [mul_comm ((Fintype.card I : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_right (single_le_sum (fun j _ => hf j) (mem_univ i))
    (inv_nonneg.mpr (Nat.cast_nonneg _))
lemma expect_prod_function {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
    [DecidableEq V] (f : (V → W × I) → ℝ) :
    (𝔼 j : V → W × I, f j) =
      𝔼 w : V → W, 𝔼 i : V → I, f (fun v => (w v, i v)) := by
  calc
    _ = 𝔼 j : (V → W) × (V → I), f (fun v => (j.1 v,j.2 v)) :=
      Fintype.expect_equiv (Equiv.arrowProdEquivProdArrow V (fun _ => W) (fun _ => I))
        _ _ (fun _ => rfl)
    _ = _ := by rw [← univ_product_univ, expect_product]
lemma expect_restrict_first {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
    [DecidableEq V] (f : (V → W × I) → ℝ) (hf : ∀ j, 0 ≤ f j) (w : V → W) :
    ((Fintype.card W : ℝ) ^ Fintype.card V)⁻¹ *
      (𝔼 i : V → I, f (fun v => (w v, i v))) ≤ 𝔼 j : V → W × I, f j := by
  rw [expect_prod_function]
  simpa only [Fintype.card_fun, Nat.cast_pow] using
    expect_ge_single (fun w : V → W => 𝔼 i : V → I, f (fun v => (w v,i v)))
      (fun w => expect_nonneg fun i _ => hf _) w
def tupleWordOfHalf (b : Fin tupleBlocks) (α β : Fin tupleH) (v : CutHalf b α β) :
    TupleCutWord α β := ⟨v.1 b, v.2⟩
lemma tupleRegroup_projection (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (v : CutHalf b α β) (i : TupleListIndex S) :
    tupleRegroupEquiv S b hb hne (tupleHalfProjection S b hb α β v, i) =
      (tupleProjection (insert b S) v.1,
        (tupleMarkIndexEquiv S b hb hne).symm (tupleWordOfHalf b α β v, i)) := by
  apply Prod.ext
  · rfl
  · rfl
lemma tuple_regroup_edges (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    graphPullback (tupleRegroupEquiv S b hb hne) (tupleListEdges (insert b S)) ⊆
      cutInternalEdges (tupleUnmarkedGraph S b hb hne) := by
  intro a ha
  simp only [graphPullback, mem_filter, mem_univ, true_and] at ha
  simp only [cutInternalEdges, mem_filter, mem_univ, true_and, tupleUnmarkedGraph,
    graphPullback, tupleEntryHalfEquiv_inl, tupleListEdges, if_pos hs]
  unfold tupleListEdges at ha
  split_ifs at ha with hnew
  · have h := (mem_filter.mp ha).2
    let f : {c : Fin tupleBlocks // c ∉ insert b S} ↪
        {c : Fin tupleBlocks // c ∉ S} :=
      ⟨fun c => ⟨c.1, fun hc => c.2 (mem_insert_of_mem hc)⟩,
        fun c d he => Subtype.ext (congrArg (fun x : {c : Fin tupleBlocks // c ∉ S} => x.val) he)⟩
    exact addressEdge_mono_blocks tupleCycle (tupleT + 1) f a.1.1.1 a.2.1.1 h
  · simp at ha
lemma graphValidity_antitone {I : Type*} {p : ℕ} [Fact p.Prime]
    {E E' : Finset (I × I)} (hE : E' ⊆ E) (z : I → ZMod p) :
    graphValidity E z ≤ graphValidity E' z :=
  prod_le_prod_of_subset_of_le_one hE (fun _ _ => squareIndicator_nonneg _)
    (fun _ _ _ => squareIndicator_le_one _)
lemma tuple_regroup_validity {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (Y : TupleListEntry (insert b S) → ZMod p) :
    graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne))
      (Y ∘ tupleRegroupEquiv S b hb hne) ≤ tupleValidity (insert b S) Y := by
  have h := graphValidity_antitone (tuple_regroup_edges S hs b hb hne)
    (Y ∘ tupleRegroupEquiv S b hb hne)
  rw [graphValidity_pullback] at h
  exact h
lemma tuple_regroup_moment {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    ((tupleR : ℝ)^Fintype.card (CutHalf b α β))⁻¹ * tupleUnmarkedMoment S b hb hne F ≤
      𝔼 Y : TupleListEntry (insert b S) → ZMod p,
      𝔼 j : CutHalf b α β → TupleListIndex (insert b S),
        tupleValidity (insert b S) Y *
          (F (fun v => Y (tupleProjection (insert b S) v.1, j v)))^2 := by
  unfold tupleUnmarkedMoment
  rw [expect_precompose (tupleRegroupEquiv S b hb hne)]
  rw [mul_expect]
  apply expect_le_expect
  intro Y _
  have hV := tuple_regroup_validity S hs b hb hne Y
  have hrest := expect_restrict_first
    (fun j : CutHalf b α β → TupleCutWord α β × TupleListIndex S =>
      tupleValidity (insert b S) Y * (F (fun v =>
        Y (tupleProjection (insert b S) v.1, (tupleMarkIndexEquiv S b hb hne).symm (j v))))^2)
    (fun j => mul_nonneg (tupleValidity_nonneg _ _) (sq_nonneg _)) (tupleWordOfHalf b α β)
  rw [card_tupleCutWord hne] at hrest
  have he : (𝔼 j : CutHalf b α β → TupleListIndex (insert b S),
      tupleValidity (insert b S) Y * (F (fun v => Y (tupleProjection (insert b S) v.1,j v)))^2) =
      𝔼 j : CutHalf b α β → TupleCutWord α β × TupleListIndex S,
      tupleValidity (insert b S) Y * (F (fun v =>
        Y (tupleProjection (insert b S) v.1, (tupleMarkIndexEquiv S b hb hne).symm (j v))))^2 := by
    apply Fintype.expect_equiv
      (Equiv.arrowCongr (Equiv.refl _) (tupleMarkIndexEquiv S b hb hne))
    intro j
    simp
  rw [he]
  refine le_trans ?_ hrest
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
  apply expect_le_expect
  intro j _
  dsimp only [Function.comp_apply]
  simp only [tupleRegroup_projection]
  exact mul_le_mul_of_nonneg_right hV (sq_nonneg _)
lemma card_cutHalf_eq_div {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hne : α ≠ β) :
    Fintype.card (CutHalf b α β) = (Nat.factorial h)^Fintype.card B / 2 := by
  have hh := card_cutHalf b hne
  omega
def tupleHalfCount : ℕ := (Nat.factorial tupleH)^tupleBlocks / 2
lemma card_tupleHalf (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β) :
    Fintype.card (CutHalf b α β) = tupleHalfCount := by
  simpa only [tupleHalfCount, Fintype.card_fin] using card_cutHalf_eq_div b hne
lemma tupleR_one_le : 1 ≤ (tupleR : ℝ) := by exact_mod_cast tupleR_pos
noncomputable def tupleMarkedConstant : ℝ :=
  (Real.exp tupleKappa - 1)^tupleHalfCount /
    ((tupleR : ℝ)^(tupleT + 1))^tupleHalfCount
lemma tupleMarkedConstant_pos : 0 < tupleMarkedConstant := by
  exact div_pos (pow_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr tupleKappa_pos)) _)
    (pow_pos (pow_pos (Nat.cast_pos.mpr tupleR_pos) _) _)
lemma tupleMarkedConstant_le (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β) :
    tupleMarkedConstant ≤ (Real.exp tupleKappa - 1)^Fintype.card (CutHalf b α β) /
      (Fintype.card (TupleListIndex S) : ℝ)^Fintype.card (CutHalf b α β) := by
  rw [card_tupleHalf b hne]
  simp only [TupleListIndex, Fintype.card_fin, Nat.cast_pow]
  apply div_le_div_of_nonneg_left
    (pow_nonneg (sub_nonneg.mpr (Real.one_le_exp tupleKappa_pos.le)) _)
    (pow_pos (pow_pos (Nat.cast_pos.mpr tupleR_pos) _) _)
  exact pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg _) _)
    (pow_le_pow_right₀ tupleR_one_le hs) _
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical
lemma tuple_marked_uniform {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∈ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    tupleMarkedConstant * (𝔼 Y : TupleListEntry S → ZMod p,
      𝔼 j : CutHalf b α β → TupleListIndex S,
        tupleValidity S Y * (F (fun v => Y (tupleProjection S v.1, j v)))^2) ≤
      tupleCutForm S b α β F := by
  refine le_trans (mul_le_mul_of_nonneg_right (tupleMarkedConstant_le S hs b hne) ?_)
    (tuple_marked_lower S b hb hne F)
  exact expect_nonneg fun Y _ => expect_nonneg fun j _ =>
    mul_nonneg (tupleValidity_nonneg _ _) (sq_nonneg _)
lemma tuple_marking_domination {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    tupleMarkedConstant * ((tupleR : ℝ)^tupleHalfCount)⁻¹ *
      tupleUnmarkedMoment S b hb hne F ≤ tupleCutForm (insert b S) b α β F := by
  have hr := tuple_regroup_moment S hs b hb hne F
  rw [card_tupleHalf b hne] at hr
  have hs' : (insert b S).card ≤ tupleT + 1 := by
    rw [card_insert_of_notMem hb]; omega
  have h := mul_le_mul_of_nonneg_left hr tupleMarkedConstant_pos.le
  rw [← mul_assoc] at h
  exact h.trans (tuple_marked_uniform (insert b S) hs' b (mem_insert_self ..) hne F)
lemma truncated_sum_nonneg_of_pairs {B : Type*} [Fintype B] [DecidableEq B]
    (b : B) (t : ℕ) (f : Finset B → ℝ)
    (hpair : ∀ S, b ∉ S → S.card ≤ t → 0 ≤ f S + f (insert b S))
    (hterm : ∀ S, b ∉ S → S.card = t + 1 → 0 ≤ f S) :
    0 ≤ ∑ S ∈ (univ : Finset B).powerset, if S.card ≤ t + 1 then f S else 0 := by
  classical
  rw [← insert_erase (mem_univ b), sum_powerset_insert (notMem_erase b univ), ← sum_add_distrib]
  apply sum_nonneg
  intro S hS
  have hb : b ∉ S := notMem_mono (mem_powerset.mp hS) (notMem_erase b univ)
  rw [card_insert_of_notMem hb]
  by_cases ht : S.card ≤ t
  · simp only [if_pos (by omega : S.card ≤ t + 1),
      if_pos (by omega : S.card + 1 ≤ t + 1)]
    exact hpair S hb ht
  · by_cases he : S.card = t + 1
    · simp only [he, le_refl, ite_true, if_neg (by omega : ¬ t + 1 + 1 ≤ t + 1), add_zero]
      exact hterm S hb he
    · simp [show ¬ S.card ≤ t + 1 by omega, show ¬ S.card + 1 ≤ t + 1 by omega]
lemma balanced_rpow_error {C a p : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hp : 0 < p)
    (hthreshold : (C / a)^16 ≤ p) :
    C * p^(-(1 : ℝ)/8) ≤ a * p^(-(1 : ℝ)/16) := by
  have hroot := Real.rpow_le_rpow (pow_nonneg (div_nonneg hC ha.le) 16) hthreshold
    (by norm_num : 0 ≤ (1 : ℝ)/16)
  have hx : ((C/a)^16)^((1 : ℝ)/16) = C/a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hC ha.le)]
    norm_num
  rw [hx] at hroot
  have hh := mul_le_mul_of_nonneg_right hroot
    (mul_nonneg ha.le (Real.rpow_nonneg hp.le (-(1 : ℝ)/8)))
  have hpow : p^((1 : ℝ)/16) * p^(-(1 : ℝ)/8) = p^(-(1 : ℝ)/16) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  calc
    C * p^(-(1 : ℝ)/8) = (C/a) * (a * p^(-(1 : ℝ)/8)) := by field_simp
    _ ≤ p^((1 : ℝ)/16) * (a * p^(-(1 : ℝ)/8)) := hh
    _ = a * p^(-(1 : ℝ)/16) := by rw [mul_left_comm, hpow]
lemma tupleUnmarkedConstant_nonneg : 0 ≤ tupleUnmarkedConstant :=
  mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) _)
    (sq_nonneg _)
noncomputable def tupleReflectionThreshold : ℝ :=
  max 3 ((tupleUnmarkedConstant * (tupleR : ℝ)^tupleHalfCount /
    tupleMarkedConstant)^16)
lemma tuple_pair_positive {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ))
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleCutForm S b α β F + (p : ℝ)^(-(1 : ℝ)/16) *
      tupleCutForm (insert b S) b α β F := by
  have hp3 : (3 : ℝ) ≤ p := (le_max_left _ _).trans hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp3
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hp3
  let a := tupleMarkedConstant * ((tupleR : ℝ)^tupleHalfCount)⁻¹
  have hr : 0 < (tupleR : ℝ)^tupleHalfCount := pow_pos (Nat.cast_pos.mpr tupleR_pos) _
  have ha : 0 < a := mul_pos tupleMarkedConstant_pos (inv_pos.mpr hr)
  have hC : tupleUnmarkedConstant / a =
      tupleUnmarkedConstant * (tupleR : ℝ)^tupleHalfCount / tupleMarkedConstant := by
    dsimp [a]
    field_simp
  have hthreshold : (tupleUnmarkedConstant / a)^16 ≤ (p : ℝ) := by
    rw [hC]
    exact (le_max_right _ _).trans hp
  have hc := balanced_rpow_error tupleUnmarkedConstant_nonneg ha hp0 hthreshold
  have hl := tuple_unmarked_error hp2 S (by omega) b hb hne F
  have hd := tuple_marking_domination S hs b hb hne F
  have hd' := mul_le_mul_of_nonneg_left hd
    (Real.rpow_nonneg hp0.le (-(1 : ℝ)/16))
  have hD := tupleUnmarkedMoment_nonneg S b hb hne F
  have hcd := mul_le_mul_of_nonneg_right hc hD
  dsimp [a] at hcd
  nlinarith
noncomputable def tupleMixtureWeight (p : ℕ) (S : Finset (Fin tupleBlocks)) : ℝ :=
  (p : ℝ)^(-(S.card : ℝ)/16)
lemma tupleMixtureWeight_nonneg (p : ℕ) (S : Finset (Fin tupleBlocks)) :
    0 ≤ tupleMixtureWeight p S := Real.rpow_nonneg (Nat.cast_nonneg _) _
lemma tupleMixtureWeight_insert {p : ℕ} (hp : 0 < p)
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S) :
    tupleMixtureWeight p (insert b S) = tupleMixtureWeight p S * (p : ℝ)^(-(1 : ℝ)/16) := by
  unfold tupleMixtureWeight
  rw [card_insert_of_notMem hb, Nat.cast_add, Nat.cast_one]
  rw [show -((S.card : ℝ)+1)/16 = -(S.card : ℝ)/16 + -(1 : ℝ)/16 by ring]
  exact Real.rpow_add (Nat.cast_pos.mpr hp) _ _
noncomputable def tupleMixture {p : ℕ} [Fact p.Prime]
    (G : (TupleVertex → ZMod p) → ℝ) : ℝ :=
  ∑ S ∈ (univ : Finset (Fin tupleBlocks)).powerset,
    if S.card ≤ tupleT + 1 then tupleMixtureWeight p S * tupleComponent S G else 0
lemma tupleMixture_reflection_positive {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ))
    (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleMixture (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  apply truncated_sum_nonneg_of_pairs b tupleT
  · intro S hb hs
    have hh := mul_nonneg (tupleMixtureWeight_nonneg p S) (tuple_pair_positive hp S hs b hb hne F)
    rw [tupleMixtureWeight_insert (Fact.out : p.Prime).pos S b hb]
    simpa only [tupleCutForm, mul_add, mul_assoc] using hh
  · intro S hb hs
    exact mul_nonneg (tupleMixtureWeight_nonneg p S)
      (tuple_terminal_positive (by
        have hc : (3 : ℝ) ≤ p := (le_max_left _ _).trans hp
        intro h; subst p; norm_num at hc) S hs b hb hne F)
lemma tupleMixture_symmetric {p : ℕ} [Fact p.Prime]
    (b : Fin tupleBlocks) (α β : Fin tupleH)
    (F G : (CutHalf b α β → ZMod p) → ℝ) :
    tupleMixture (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
    tupleMixture (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  apply sum_congr rfl
  intro S _
  split_ifs
  · rw [tupleCutForm_symmetric]
  · rfl
noncomputable def tupleComponentMap {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) : ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ where
  toFun := tupleComponent S
  map_add' F G := by simp [tupleComponent, mul_add, expect_add_distrib]
  map_smul' c F := by
    simp only [tupleComponent, Pi.smul_apply, smul_eq_mul]
    simp_rw [show ∀ a b d : ℝ, a * b * (c * d) = c * (a * b * d) by intros; ring]
    simp_rw [← mul_expect]
    rfl
noncomputable def tupleMixtureMap {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ where
  toFun := tupleMixture
  map_add' F G := by
    unfold tupleMixture
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro S _
    split_ifs with hs
    · change _ * tupleComponentMap S (F+G) = _
      rw [map_add, mul_add]
      rfl
    · simp
  map_smul' c F := by
    change tupleMixture (c • F) = c * tupleMixture F
    unfold tupleMixture
    rw [mul_sum]
    apply sum_congr rfl
    intro S _
    split_ifs with hs
    · change _ * tupleComponentMap S (c • F) = _
      rw [map_smul, smul_eq_mul]
      change tupleMixtureWeight p S * (c * tupleComponent S F) =
        c * (tupleMixtureWeight p S * tupleComponent S F)
      ring
    · simp
lemma tupleMixtureMap_apply {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) : tupleMixtureMap F = tupleMixture F := by
  simp only [tupleMixtureMap, LinearMap.coe_mk, AddHom.coe_mk]
lemma tupleMixture_nonneg {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) (hF : ∀ z, 0 ≤ F z) :
    0 ≤ tupleMixture F := by
  apply sum_nonneg
  intro S _
  split_ifs
  · exact mul_nonneg (tupleMixtureWeight_nonneg p S) (tupleComponent_nonneg S F hF)
  · exact le_rfl
noncomputable def tupleLeadingEdges : ℕ := (tupleListEdges ∅).card
noncomputable def tupleLeadingMassLower : ℝ := (1/2 : ℝ)^(tupleLeadingEdges+1)
noncomputable def tupleMassThreshold : ℝ :=
  max 3 (((2 : ℝ)^(tupleLeadingEdges+1) * tupleLeadingEdges)^2)
lemma tupleLeadingMassLower_pos : 0 < tupleLeadingMassLower := pow_pos (by norm_num) _
lemma error_le_of_square_threshold {E c p : ℝ} (hE : 0 ≤ E) (hc : 0 < c)
    (hp : 0 < p) (h : (E/c)^2 ≤ p) : E * p^(-(1 : ℝ)/2) ≤ c := by
  have hh := Real.rpow_le_rpow (sq_nonneg (E/c)) h (by norm_num : 0 ≤ (1 : ℝ)/2)
  have he : ((E/c)^2)^((1 : ℝ)/2) = E/c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hE hc.le)]
    norm_num
  rw [he] at hh
  have hh' := mul_le_mul_of_nonneg_right hh
    (mul_nonneg hc.le (Real.rpow_nonneg hp.le (-(1 : ℝ)/2)))
  have hp' : p^((1 : ℝ)/2) * p^(-(1 : ℝ)/2) = 1 := by
    rw [← Real.rpow_add hp]
    norm_num
  calc
    _ = (E/c) * (c * p^(-(1 : ℝ)/2)) := by field_simp
    _ ≤ p^((1 : ℝ)/2) * (c * p^(-(1 : ℝ)/2)) := hh'
    _ = c := by rw [mul_left_comm, hp', mul_one]
lemma leading_mass_lower_of_count (e : ℕ) {m p : ℝ}
    (hp : max 3 (((2 : ℝ)^(e+1) * e)^2) ≤ p)
    (hcount : |m-(1/2 : ℝ)^e| ≤ (e : ℝ)*p^(-(1 : ℝ)/2)) :
    (1/2 : ℝ)^(e+1) ≤ m := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<3) ((le_max_left _ _).trans hp)
  have hc0 : 0 < (1/2 : ℝ)^(e+1) := pow_pos (by norm_num) _
  have he : (e : ℝ) / (1/2 : ℝ)^(e+1) = (2 : ℝ)^(e+1)*e := by
    rw [one_div_pow]
    field_simp
  have hc := error_le_of_square_threshold (Nat.cast_nonneg e) hc0 hp0
    (by rw [he]; exact (le_max_right _ _).trans hp)
  have hc2 : (1/2 : ℝ)^e = 2*(1/2 : ℝ)^(e+1) := by rw [pow_succ]; ring
  have he' := hcount.trans hc
  rw [abs_le, hc2] at he'
  linarith [he'.1]
lemma tupleLeading_mass_lower {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) :
    tupleLeadingMassLower ≤ tupleComponent (p := p) ∅ (fun _ => 1) := by
  apply leading_mass_lower_of_count tupleLeadingEdges hp
  have hp3 : (3 : ℝ) ≤ p := (le_max_left _ _).trans hp
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hp3
  exact (tuple_leading_mass hp2).trans (mul_le_mul_of_nonneg_left
    (square_delta_le (p := p)) (Nat.cast_nonneg tupleLeadingEdges))
lemma tupleMixture_mass_lower {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) :
    tupleLeadingMassLower ≤ tupleMixture (p := p) (fun _ => 1) := by
  refine (tupleLeading_mass_lower hp).trans ?_
  have hterm : ∀ S : Finset (Fin tupleBlocks), 0 ≤
      if S.card ≤ tupleT+1 then tupleMixtureWeight p S * tupleComponent (p := p) S (fun _ => 1) else 0 := by
    intro S
    split_ifs
    · exact mul_nonneg (tupleMixtureWeight_nonneg p S)
        (tupleComponent_nonneg S _ (fun _ => by norm_num))
    · exact le_rfl
  have hh := single_le_sum (s := (univ : Finset (Fin tupleBlocks)).powerset)
    (fun S _ => hterm S) (a := ∅) (mem_powerset.mpr (empty_subset _))
  simpa only [card_empty, Nat.zero_le, ite_true, tupleMixtureWeight, Nat.cast_zero,
    neg_zero, zero_div, Real.rpow_zero, one_mul, tupleMixture] using hh
noncomputable def tupleLaw {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ :=
  (tupleMixture (p := p) (fun _ => 1))⁻¹ • tupleMixtureMap
lemma tupleLaw_probability {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) : tupleLaw (p := p) (fun _ => 1) = 1 := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleMixture_mass_lower hp)
  simp only [tupleLaw, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply,
    inv_mul_cancel₀ hm.ne']
lemma tupleLaw_reflection_positive {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ))
    (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleLaw (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  apply mul_nonneg (inv_nonneg.mpr (tupleMixture_nonneg _ (fun _ => by norm_num)))
  rw [tupleMixtureMap_apply]
  exact tupleMixture_reflection_positive hp b hne F
lemma tupleLaw_symmetric {p : ℕ} [Fact p.Prime]
    (b : Fin tupleBlocks) (α β : Fin tupleH)
    (F G : (CutHalf b α β → ZMod p) → ℝ) :
    tupleLaw (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
    tupleLaw (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  simp only [tupleLaw, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply,
    tupleMixture_symmetric b α β F G]
lemma linearFunctional_density {X : Type*} [Fintype X] [DecidableEq X]
    (L : (X → ℝ) →ₗ[ℝ] ℝ) (f : X → ℝ) :
    L f = ∑ x, L (fun y => if y = x then 1 else 0) * f x := by
  classical
  have hf : f = ∑ x, f x • (fun y => if y = x then (1 : ℝ) else 0) := by
    ext y
    simp
  conv_lhs => rw [hf, map_sum]
  apply sum_congr rfl
  intro x _
  simp [mul_comm]
lemma cut_cauchy_schwarz {X I : Type*}
    (L : (X → ℝ) →ₗ[ℝ] ℝ) (left right : X → I)
    (hsym : ∀ F G : I → ℝ,
      L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)))
    (hpos : ∀ F : I → ℝ, 0 ≤ L (fun z => F (left z) * F (right z)))
    (F G : I → ℝ) :
    |L (fun z => F (left z) * G (right z))|^2 ≤
      L (fun z => F (left z) * F (right z)) *
      L (fun z => G (left z) * G (right z)) := by
  have hquad (t : ℝ) := hpos (fun x => t * F x + G x)
  have heq (t : ℝ) :
      (fun z => (t * F (left z) + G (left z)) *
        (t * F (right z) + G (right z))) =
      (t*t) • (fun z => F (left z) * F (right z)) +
      t • (fun z => F (left z) * G (right z)) +
      t • (fun z => G (left z) * F (right z)) +
      (fun z => G (left z) * G (right z)) := by
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [heq, map_add, map_smul, smul_eq_mul, ← hsym F G] at hquad
  have hq := discrim_le_zero (fun t => show 0 ≤
    L (fun z => F (left z) * F (right z)) * (t*t) +
      (2*L (fun z => F (left z) * G (right z))) * t +
      L (fun z => G (left z) * G (right z)) by nlinarith [hquad t])
  rw [discrim] at hq
  rw [sq_abs]
  nlinarith
noncomputable def multilinearIntegral {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → X → ℝ) : ℝ :=
  L (fun z => ∏ v, a v (z v))
noncomputable def diagonalIntegral {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) : ℝ :=
  multilinearIntegral L (fun _ => g)
lemma multilinearIntegral_div {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → X → ℝ) (c : V → ℝ) :
    multilinearIntegral L (fun v x => a v x / c v) =
      multilinearIntegral L a / ∏ v, c v := by
  unfold multilinearIntegral
  simp_rw [prod_div_distrib]
  have he : (fun z : V → X => (∏ v, a v (z v)) / ∏ v, c v) =
      (∏ v, c v)⁻¹ • (fun z : V → X => ∏ v, a v (z v)) := by
    ext z
    simp [div_eq_mul_inv, mul_comm]
  rw [he, map_smul, smul_eq_mul]
  ring
lemma diagonalIntegral_div {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) (c : ℝ) :
    diagonalIntegral L (fun x => g x / c) =
      diagonalIntegral L g / c^(Fintype.card V) := by
  unfold diagonalIntegral
  simpa only [prod_const, card_univ] using
    multilinearIntegral_div L (fun _ => g) (fun _ => c)
lemma holder_of_finite_maximum {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g)
    (hmax : ∀ a : V → X → ℝ, ∃ i : V,
      |multilinearIntegral L a| ≤ diagonalIntegral L (a i))
    (a : V → X → ℝ) :
    |multilinearIntegral L a| ≤
      ∏ v, (diagonalIntegral L (a v))^((1 : ℝ)/(Fintype.card V : ℝ)) := by
  classical
  let d : ℝ := Fintype.card V
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  have hε (ε : ℝ) (hε : 0 < ε) :
      |multilinearIntegral L a| ≤ ∏ v, (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d) := by
    let c (v : V) : ℝ := (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d)
    have hc (v : V) : 0 < c v := Real.rpow_pos_of_pos (by linarith [hdiag (a v)]) _
    have hcp (v : V) : c v ^ Fintype.card V = diagonalIntegral L (a v)+ε := by
      dsimp [c]
      rw [← Real.rpow_mul_natCast (le_of_lt (by linarith [hdiag (a v)] :
        0 < diagonalIntegral L (a v)+ε))]
      change (diagonalIntegral L (a v)+ε)^((1/d)*d) = _
      rw [one_div_mul_cancel hd.ne', Real.rpow_one]
    obtain ⟨i, hi⟩ := hmax (fun v x => a v x / c v)
    rw [multilinearIntegral_div, diagonalIntegral_div, hcp] at hi
    have hle : diagonalIntegral L (a i) / (diagonalIntegral L (a i)+ε) ≤ 1 := by
      apply (div_le_one (by linarith [hdiag (a i)])).mpr
      linarith
    have hprod : 0 < ∏ v, c v := prod_pos fun v _ => hc v
    rw [abs_div, abs_of_pos hprod] at hi
    exact (div_le_one hprod).mp (hi.trans hle)
  have hc : Continuous (fun ε : ℝ =>
      ∏ v, (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d)) := by
    apply continuous_finsetProd
    intro v _
    exact (Real.continuous_rpow_const (div_nonneg zero_le_one hd.le)).comp
      (continuous_const.add continuous_id)
  have ht := hc.continuousAt.tendsto.mono_left (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 by
    exact inf_le_left)
  have hevent : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      |multilinearIntegral L a| ≤ ∏ v, (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hεpos
    exact hε ε hεpos
  have hh := ge_of_tendsto ht hevent
  simpa only [add_zero] using hh
lemma prod_word_split {B M : Type*} [Fintype B] [DecidableEq B] [CommMonoid M]
    {h : ℕ} (b : B) {α β : Fin h} (hne : α ≠ β) (f : WordVertex B h → M) :
    ∏ v, f v = (∏ v : CutHalf b α β, f v.1) *
      ∏ v : CutHalf b α β, f (reflect b α β v.1) := by
  classical
  rw [← Fintype.prod_equiv (halfSumEquiv b hne) (fun v => f (halfSumEquiv b hne v)) f
    (fun _ => rfl)]
  exact Fintype.prod_sum_type _
lemma foldWord_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : CutHalf b α β) :
    foldWord b α β v.1 = v.1 := if_pos v.2
lemma foldWord_reflect_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hne : α ≠ β) (v : CutHalf b α β) :
    foldWord b α β (reflect b α β v.1) = v.1 := by
  have hn : ¬ cutPlus b α β (reflect b α β v.1) := by
    rw [cutPlus_reflect_iff_not b hne]
    exact not_not.mpr v.2
  rw [foldWord, if_neg hn, reflect_involutive]
lemma reflect_comm {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) : reflect b α β = reflect b β α := by
  funext v
  simp only [reflect, Equiv.swap_comm α β]
lemma foldWord_opposite_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : CutHalf b α β) :
    foldWord b β α v.1 = reflect b α β v.1 := by
  have hn : ¬ cutPlus b β α v.1 := not_lt_of_gt v.2
  rw [foldWord, if_neg hn, reflect_comm b β α]
lemma foldWord_opposite_reflect_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : CutHalf b α β) :
    foldWord b β α (reflect b α β v.1) = reflect b α β v.1 := by
  apply if_pos
  rw [reflect_comm b α β, reflect_cutPlus]
  exact v.2
noncomputable def halfProduct {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (a : WordVertex B h → X → ℝ)
    (x : CutHalf b α β → X) : ℝ := ∏ v, a v.1 (x v)
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical
lemma prod_word_fold {B X : Type*} [Fintype B] [DecidableEq B]
    {h : ℕ} (b : B) {α β : Fin h} (hne : α ≠ β)
    (a : WordVertex B h → X → ℝ) (z : WordVertex B h → X) :
    (∏ v, (a ∘ foldWord b α β) v (z v)) =
      halfProduct b α β a (fun v => z v.1) *
      halfProduct b α β a (fun v => z (reflect b α β v.1)) := by
  classical
  rw [prod_word_split b hne]
  simp only [Function.comp_apply, foldWord_half, foldWord_reflect_half b hne, halfProduct]
lemma prod_word_opposite_fold {B X : Type*} [Fintype B] [DecidableEq B]
    {h : ℕ} (b : B) {α β : Fin h} (hne : α ≠ β)
    (a : WordVertex B h → X → ℝ) (z : WordVertex B h → X) :
    (∏ v, (a ∘ foldWord b β α) v (z v)) =
      halfProduct b α β (a ∘ reflect b α β) (fun v => z v.1) *
      halfProduct b α β (a ∘ reflect b α β) (fun v => z (reflect b α β v.1)) := by
  classical
  rw [prod_word_split b hne]
  simp only [Function.comp_apply, foldWord_opposite_half, foldWord_opposite_reflect_half,
    halfProduct]
lemma wordIntegral_folding {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (L : ((WordVertex B h → X) → ℝ) →ₗ[ℝ] ℝ)
    (b : B) {α β : Fin h} (hne : α ≠ β)
    (hsym : ∀ F G : (CutHalf b α β → X) → ℝ,
      L (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ F : (CutHalf b α β → X) → ℝ,
      0 ≤ L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (a : WordVertex B h → X → ℝ) :
    |multilinearIntegral L a|^2 ≤
      multilinearIntegral L (a ∘ foldWord b α β) *
      multilinearIntegral L (a ∘ foldWord b β α) ∧
      0 ≤ multilinearIntegral L (a ∘ foldWord b α β) := by
  have hsplit : multilinearIntegral L a =
      L (fun z => halfProduct b α β a (fun v => z v.1) *
        halfProduct b α β (a ∘ reflect b α β) (fun v => z (reflect b α β v.1))) := by
    unfold multilinearIntegral
    apply congrArg L
    funext z
    exact prod_word_split b hne (fun v => a v (z v))
  simp only [multilinearIntegral, prod_word_fold b hne, prod_word_opposite_fold b hne]
  constructor
  · have hcs := cut_cauchy_schwarz L (fun z v => z v.1)
      (fun z v => z (reflect b α β v.1)) hsym hpos
      (halfProduct b α β a) (halfProduct b α β (a ∘ reflect b α β))
    rw [← hsplit] at hcs
    exact hcs
  · exact hpos _
lemma word_diagonal_nonneg {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (L : ((WordVertex B h → X) → ℝ) →ₗ[ℝ] ℝ)
    (b : B) {α β : Fin h} (hne : α ≠ β)
    (hpos : ∀ F : (CutHalf b α β → X) → ℝ,
      0 ≤ L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (g : X → ℝ) : 0 ≤ diagonalIntegral L g := by
  have hf : (fun _ : WordVertex B h => g) ∘ foldWord b α β = fun _ => g := rfl
  unfold diagonalIntegral multilinearIntegral
  rw [← hf]
  simp_rw [prod_word_fold b hne]
  exact hpos _
lemma word_signed_holder {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (L : ((WordVertex B h → X) → ℝ) →ₗ[ℝ] ℝ)
    (b₀ : B) {α₀ β₀ : Fin h} (hne₀ : α₀ ≠ β₀)
    (hsym : ∀ b α β, ∀ F G : (CutHalf b α β → X) → ℝ,
      L (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ b α β, α ≠ β → ∀ F : (CutHalf b α β → X) → ℝ,
      0 ≤ L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (a : WordVertex B h → X → ℝ) :
    |multilinearIntegral L a| ≤
      ∏ v, (diagonalIntegral L (a v))^((1 : ℝ)/(Fintype.card (WordVertex B h) : ℝ)) := by
  classical
  have hd := word_diagonal_nonneg L b₀ hne₀ (hpos b₀ α₀ β₀ hne₀)
  apply holder_of_finite_maximum L hd ?_ a
  intro a
  obtain ⟨i, hi⟩ := word_folding_maximum
    (fun r : WordVertex B h → WordVertex B h => multilinearIntegral L (a ∘ r))
    (fun b α β hne r => (wordIntegral_folding L b hne (hsym b α β)
      (hpos b α β hne) (a ∘ r)).1)
    (fun b α β hne r => (wordIntegral_folding L b hne (hsym b α β)
      (hpos b α β hne) (a ∘ r)).2)
  refine ⟨i, ?_⟩
  have hh := hi id
  change |multilinearIntegral L a| ≤ |diagonalIntegral L (a i)| at hh
  rwa [abs_of_nonneg (hd (a i))] at hh
noncomputable def diagonalRoot {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) : ℝ :=
  (diagonalIntegral L g)^((1 : ℝ)/(Fintype.card V : ℝ))
lemma diagonalRoot_pow {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g) (g : X → ℝ) :
    (diagonalRoot L g)^(Fintype.card V) = diagonalIntegral L g := by
  unfold diagonalRoot
  rw [← Real.rpow_mul_natCast (hdiag g)]
  rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Real.rpow_one]
noncomputable def cutKernel {Ω I : Type*} [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I) : Matrix I I ℝ :=
  fun x y => L (fun z => if left z = x ∧ right z = y then 1 else 0)
lemma cut_form_eq_sum {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I) (F G : I → ℝ) :
    L (fun z => F (left z) * G (right z)) =
      ∑ x, ∑ y, cutKernel L left right x y * F x * G y := by
  classical
  have he : (fun z => F (left z) * G (right z)) =
      ∑ x, ∑ y, (F x * G y) • (fun z => if left z = x ∧ right z = y then (1 : ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_and]
    simp
  rw [he, map_sum]
  apply sum_congr rfl
  intro x _
  rw [map_sum]
  apply sum_congr rfl
  intro y _
  rw [map_smul, smul_eq_mul]
  change (F x * G y) * cutKernel L left right x y = _
  ring
lemma cutKernel_posSemidef {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hsym : ∀ F G : I → ℝ,
      L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)))
    (hpos : ∀ F : I → ℝ, 0 ≤ L (fun z => F (left z) * F (right z))) :
    (cutKernel L left right).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext x y
    have hs := hsym (fun z => if z=x then 1 else 0) (fun z => if z=y then 1 else 0)
    have he (x y : I) (z : Ω) :
        (if left z=x then (1 : ℝ) else 0) * (if right z=y then 1 else 0) =
          if left z=x ∧ right z=y then 1 else 0 := by split_ifs <;> simp_all
    simp_rw [he] at hs
    exact hs.symm
  · intro F
    have hh := hpos F
    rw [cut_form_eq_sum] at hh
    simpa only [dotProduct, Matrix.mulVec, star_trivial, sum_mul, mul_sum,
      mul_left_comm, mul_comm, mul_assoc] using hh
lemma matrix_prod_posSemidef {J I : Type*} [Fintype J] [Fintype I]
    (K : J → Matrix I I ℝ) (hK : ∀ j, (K j).PosSemidef) :
    Matrix.PosSemidef (fun x y => ∏ j, K j x y) := by
  classical
  have hs (s : Finset J) : Matrix.PosSemidef (fun x y => ∏ j ∈ s, K j x y) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun x y => ∏ j ∈ (∅ : Finset J), K j x y) =
          Matrix.vecMulVec (fun _ : I => (1 : ℝ)) (star (fun _ : I => (1 : ℝ))) := by
        ext x y
        simp [Matrix.vecMulVec]
      rw [he]
      exact Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
    | @insert j s hj ih =>
      have he : (fun x y => ∏ k ∈ insert j s, K k x y) =
          (K j).hadamard (fun x y => ∏ k ∈ s, K k x y) := by
        ext x y
        change (∏ k ∈ insert j s, K k x y) = K j x y * ∏ k ∈ s, K k x y
        exact prod_insert hj
      rw [he]
      exact (hK j).hadamard ih
  exact hs univ
lemma cut_positive_of_kernel {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hK : (cutKernel L left right).PosSemidef) (F : I → ℝ) :
    0 ≤ L (fun z => F (left z) * F (right z)) := by
  rw [cut_form_eq_sum]
  have hh := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hK).2 F
  simpa only [dotProduct, Matrix.mulVec, star_trivial, sum_mul, mul_sum,
    mul_left_comm, mul_comm, mul_assoc] using hh
lemma cut_symmetric_of_kernel {Ω I : Type*} [Fintype I] [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I)
    (hK : (cutKernel L left right).PosSemidef) (F G : I → ℝ) :
    L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)) := by
  rw [cut_form_eq_sum, cut_form_eq_sum, sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  have hs : cutKernel L left right x y = cutKernel L left right y x := by
    have h := congrFun (congrFun hK.isHermitian x) y
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  rw [hs]
  ring
noncomputable def lawDensity {Ω : Type*} [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (x : Ω) : ℝ :=
  L (fun y => if y=x then 1 else 0)
noncomputable def tensorLaw {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) : ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * F (fun v j => z j v)
  map_add' F G := by simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c F := by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← mul_sum, RingHom.id_apply]
lemma tensorLaw_fubini {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (F : ∀ j, (V → X j) → ℝ) :
    tensorLaw L (fun z => ∏ j, F j (fun v => z v j)) = ∏ j, L j (F j) := by
  change (∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * ∏ j, F j (z j)) = _
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j z => lawDensity (L j) z * F j z)]
  apply prod_congr rfl
  intro j _
  exact (linearFunctional_density (L j) (F j)).symm
lemma tensorLaw_probability {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (hL : ∀ j, L j (fun _ => 1)=1) :
    tensorLaw L (fun _ => 1) = 1 := by
  have hh := tensorLaw_fubini L (fun _ _ => 1)
  simpa only [prod_const_one, hL] using hh
lemma prod_indicator_forall {J : Type*} [Fintype J] (P : J → Prop) [DecidablePred P]
    [Decidable (∀ j, P j)] :
    (∏ j, if P j then (1 : ℝ) else 0) = if ∀ j, P j then 1 else 0 := by
  classical
  by_cases h : ∀ j, P j
  · simp [h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    rw [if_neg h]
    exact prod_eq_zero (mem_univ j) (if_neg hj)
lemma tensorLaw_cutKernel {J V W : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (l r : W → V)
    (x y : W → ∀ j, X j) :
    cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w)) x y =
      ∏ j, cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))
        (fun w => x w j) (fun w => y w j) := by
  classical
  unfold cutKernel
  have he (z : V → ∀ j, X j) :
      (if (fun w => z (l w))=x ∧ (fun w => z (r w))=y then (1 : ℝ) else 0) =
      ∏ j, if (fun w => z (l w) j)=(fun w => x w j) ∧
        (fun w => z (r w) j)=(fun w => y w j) then 1 else 0 := by
    rw [prod_indicator_forall]
    congr 1
    apply propext
    constructor
    · rintro ⟨hl, hr⟩ j
      exact ⟨funext fun w => congrFun (congrFun hl w) j,
        funext fun w => congrFun (congrFun hr w) j⟩
    · intro h
      exact ⟨funext fun w => funext fun j => congrFun (h j).1 w,
        funext fun w => funext fun j => congrFun (h j).2 w⟩
  simp_rw [he]
  exact tensorLaw_fubini L (fun j z => if (fun w => z (l w))=(fun w => x w j) ∧
    (fun w => z (r w))=(fun w => y w j) then 1 else 0)
lemma tensorLaw_cut_positive {J V W : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (l r : W → V)
    (hsym : ∀ j, ∀ F G : (W → X j) → ℝ,
      L j (fun z => F (fun w => z (l w)) * G (fun w => z (r w))) =
      L j (fun z => G (fun w => z (l w)) * F (fun w => z (r w))))
    (hpos : ∀ j, ∀ F : (W → X j) → ℝ,
      0 ≤ L j (fun z => F (fun w => z (l w)) * F (fun w => z (r w)))) :
    (cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w))).PosSemidef := by
  classical
  have he : cutKernel (tensorLaw L) (fun z w => z (l w)) (fun z w => z (r w)) =
      fun x y => ∏ j, cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))
        (fun w => x w j) (fun w => y w j) := by
    funext x y
    exact tensorLaw_cutKernel L l r x y
  rw [he]
  let K (j : J) : Matrix (W → ∀ j, X j) (W → ∀ j, X j) ℝ :=
    (cutKernel (L j) (fun z w => z (l w)) (fun z w => z (r w))).submatrix
      (fun x w => x w j) (fun x w => x w j)
  have hK (j : J) : (K j).PosSemidef :=
    (cutKernel_posSemidef (L j) _ _ (hsym j) (hpos j)).submatrix _
  exact matrix_prod_posSemidef K hK
lemma tensorLaw_word_symmetric {J B : Type*} [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] {h : ℕ}
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((WordVertex B h → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ j b α β, ∀ F G : (CutHalf b α β → X j) → ℝ,
      L j (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L j (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ j b α β, α ≠ β → ∀ F : (CutHalf b α β → X j) → ℝ,
      0 ≤ L j (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (b : B) (α β : Fin h) (F G : (CutHalf b α β → ∀ j, X j) → ℝ) :
    tensorLaw L (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      tensorLaw L (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  classical
  by_cases hne : α = β
  · subst β
    have he (z : WordVertex B h → ∀ j, X j) : (fun v : CutHalf b α α =>
        z (reflect b α α v.1)) = fun v => z v.1 := by
      funext v
      exact False.elim (lt_irrefl _ v.2)
    simp_rw [he, mul_comm (F _) (G _)]
  · exact cut_symmetric_of_kernel (tensorLaw L) _ _
      (tensorLaw_cut_positive L (fun v : CutHalf b α β => v.1)
        (fun v => reflect b α β v.1) (fun j => hsym j b α β)
        (fun j => hpos j b α β hne)) F G
lemma tensorLaw_word_positive {J B : Type*} [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] {h : ℕ}
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((WordVertex B h → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hsym : ∀ j b α β, ∀ F G : (CutHalf b α β → X j) → ℝ,
      L j (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
      L j (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (hpos : ∀ j b α β, α ≠ β → ∀ F : (CutHalf b α β → X j) → ℝ,
      0 ≤ L j (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))))
    (b : B) {α β : Fin h} (hne : α ≠ β)
    (F : (CutHalf b α β → ∀ j, X j) → ℝ) :
    0 ≤ tensorLaw L (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  classical
  exact cut_positive_of_kernel (tensorLaw L) _ _
    (tensorLaw_cut_positive L (fun v : CutHalf b α β => v.1)
      (fun v => reflect b α β v.1) (fun j => hsym j b α β)
      (fun j => hpos j b α β hne)) F
noncomputable def productTupleLaw {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] :
    ((TupleVertex → ∀ j, ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw (fun j => tupleLaw (p := p j))
lemma productTupleLaw_diagonal_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (hp : ∀ j, tupleReflectionThreshold ≤ (p j : ℝ)) (g : (∀ j, ZMod (p j)) → ℝ) :
    0 ≤ diagonalIntegral (productTupleLaw p) g := by
  exact word_diagonal_nonneg (productTupleLaw p) (⟨0, by decide⟩ : Fin tupleBlocks)
    (show (⟨0, by decide⟩ : Fin tupleH) ≠ ⟨1, by decide⟩ by decide)
    (tensorLaw_word_positive (fun j => tupleLaw (p := p j))
      (fun _j => tupleLaw_symmetric)
      (fun j b _α _β hne => tupleLaw_reflection_positive (hp j) b hne)
      (⟨0, by decide⟩ : Fin tupleBlocks) (by decide)) g
lemma productTupleLaw_signed_holder {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (hp : ∀ j, tupleReflectionThreshold ≤ (p j : ℝ))
    (a : TupleVertex → (∀ j, ZMod (p j)) → ℝ) :
    |multilinearIntegral (productTupleLaw p) a| ≤
      ∏ v, diagonalRoot (productTupleLaw p) (a v) := by
  exact word_signed_holder (productTupleLaw p) (⟨0, by decide⟩ : Fin tupleBlocks)
    (show (⟨0, by decide⟩ : Fin tupleH) ≠ ⟨1, by decide⟩ by decide)
    (tensorLaw_word_symmetric (fun j => tupleLaw (p := p j))
      (fun _j => tupleLaw_symmetric)
      (fun j b _α _β hne => tupleLaw_reflection_positive (hp j) b hne))
    (tensorLaw_word_positive (fun j => tupleLaw (p := p j))
      (fun _j => tupleLaw_symmetric)
      (fun j b _α _β hne => tupleLaw_reflection_positive (hp j) b hne)) a
lemma squareIndicator_mul_sq {F : Type*} [Field F] (q : F) (hq : q ≠ 0) (x : F) :
    squareIndicator (q^2*x) = squareIndicator x := by
  classical
  have hs : IsSquare (q^2*x) ↔ IsSquare x := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y/q, ?_⟩
      apply (mul_right_cancel₀ (pow_ne_zero 2 hq))
      calc
        x*q^2 = y*y := by rw [mul_comm]; exact hy
        _ = ((y/q)*(y/q))*q^2 := by field_simp
    · rintro ⟨y, rfl⟩
      exact ⟨q*y, by ring⟩
  unfold squareIndicator
  rw [hs]
  have hn : q^2*x ≠ 0 ↔ x ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact and_iff_right (pow_ne_zero 2 hq)
  simp only [hn]
lemma tupleValidity_affine {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (q a : ZMod p) (hq : q ≠ 0) (Y : TupleListEntry S → ZMod p) :
    tupleValidity S (fun i => q^2 * Y i + a) = tupleValidity S Y := by
  unfold tupleValidity
  apply prod_congr rfl
  intro e _
  rw [show (q^2*Y e.2+a)-(q^2*Y e.1+a)=q^2*(Y e.2-Y e.1) by ring]
  exact squareIndicator_mul_sq q hq _
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical
noncomputable def affineEquiv {F : Type*} [Field F] (q a : F) (hq : q ≠ 0) : F ≃ F where
  toFun x := q^2*x+a
  invFun y := (y-a)/q^2
  left_inv x := by field_simp; ring
  right_inv y := by field_simp; ring
lemma tupleComponent_affine {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (q a : ZMod p) (hq : q ≠ 0) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleComponent S (fun z => F (fun v => q^2*z v+a)) = tupleComponent S F := by
  classical
  let e : (TupleListEntry S → ZMod p) ≃ (TupleListEntry S → ZMod p) :=
    Equiv.piCongrRight fun _ => affineEquiv q a hq
  unfold tupleComponent
  let g := fun Y => 𝔼 j : TupleVertex → TupleListIndex S,
    tupleValidity S Y * tupleWeight S j * F (tupleOutput S Y j)
  have hr : (𝔼 Y, g (e Y)) = 𝔼 Y, g Y :=
    Fintype.expect_equiv e _ _ (fun _ => rfl)
  rw [← hr]
  apply expect_congr rfl
  intro Y _
  apply expect_congr rfl
  intro j _
  change _ = tupleValidity S (fun i => q^2*Y i+a) * tupleWeight S j *
    F (fun v => q^2 * tupleOutput S Y j v + a)
  rw [tupleValidity_affine S q a hq]
lemma tupleMixture_affine {p : ℕ} [Fact p.Prime]
    (q a : ZMod p) (hq : q ≠ 0) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleMixture (fun z => F (fun v => q^2*z v+a)) = tupleMixture F := by
  unfold tupleMixture
  simp_rw [tupleComponent_affine _ q a hq]
lemma tupleLaw_affine {p : ℕ} [Fact p.Prime]
    (q a : ZMod p) (hq : q ≠ 0) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleLaw (fun z => F (fun v => q^2*z v+a)) = tupleLaw F := by
  simp only [tupleLaw, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply]
  rw [tupleMixture_affine q a hq]
lemma invariant_marginal_uniform {V G : Type*} [Nonempty G] [Fintype G] [AddGroup G]
    (L : ((V → G) → ℝ) →ₗ[ℝ] ℝ)
    (hinv : ∀ a F, L (fun z => F (fun v => z v+a))=L F)
    (v : V) (f : G → ℝ) : L (fun z => f (z v)) = L (fun _ => 1) * 𝔼 x, f x := by
  classical
  have he (z : V → G) : 𝔼 a : G, f (z v+a) = 𝔼 x, f x := by
    exact Fintype.expect_equiv (Equiv.addLeft (z v)) _ _ (fun _ => rfl)
  have hsum : (fun z : V → G => 𝔼 a : G, f (z v+a)) =
      (Fintype.card G : ℝ)⁻¹ • ∑ a : G, (fun z : V → G => f (z v+a)) := by
    ext z
    rw [Fintype.expect_eq_sum_div_card]
    simp [div_eq_mul_inv, mul_comm]
  have hlinear := congrArg L hsum
  simp only [he, map_smul, map_sum] at hlinear
  have hi (a : G) : L (fun z => f (z v+a)) = L (fun z => f (z v)) :=
    hinv a (fun z => f (z v))
  simp_rw [hi] at hlinear
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [sum_const, card_univ, nsmul_eq_mul, smul_eq_mul,
    inv_mul_cancel_left₀ hcard] at hlinear
  rw [← hlinear]
  have hc : (fun _ : V → G => 𝔼 x : G, f x) = (𝔼 x : G, f x) • (fun _ => (1 : ℝ)) := by
    ext; simp
  rw [hc, map_smul]
  simp only [smul_eq_mul, mul_comm]
lemma diagonalRoot_one {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hL : L (fun _ => 1)=1) :
    diagonalRoot L (fun _ => 1)=1 := by
  simp [diagonalRoot, diagonalIntegral, multilinearIntegral, hL]
lemma holder_mean {V X : Type*} [Fintype V] [Fintype X] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hL : L (fun _ => 1)=1)
    (hm : ∀ v (f : X → ℝ), L (fun z => f (z v))=𝔼 x, f x)
    (hh : ∀ a : V → X → ℝ, |multilinearIntegral L a| ≤ ∏ v, diagonalRoot L (a v))
    (f : X → ℝ) : |𝔼 x, f x| ≤ diagonalRoot L f := by
  classical
  let v : V := Classical.choice inferInstance
  have h := hh (fun w => if w=v then f else fun _ => 1)
  have he : multilinearIntegral L (fun w => if w=v then f else fun _ => 1) = 𝔼 x, f x := by
    unfold multilinearIntegral
    simp only [ite_apply]
    rw [show (fun z : V → X => ∏ w, if w=v then f (z w) else (1 : ℝ)) =
      (fun z => f (z v)) by funext z; simp]
    exact hm v f
  rw [he] at h
  have he' : (∏ w : V, diagonalRoot L (if w=v then f else fun _ => 1))=diagonalRoot L f := by
    simp only [apply_ite, diagonalRoot_one L hL]
    simp
  rwa [he'] at h
lemma lawDensity_equiv {Ω : Type*} [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ Ω)
    (hL : ∀ F, L (fun z => F (e z))=L F) (x : Ω) :
    lawDensity L (e x)=lawDensity L x := by
  unfold lawDensity
  rw [← hL (fun y => if y=e x then 1 else 0)]
  simp only [Equiv.apply_eq_iff_eq]
lemma tensorLaw_equiv {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (e : ∀ j, X j ≃ X j)
    (hL : ∀ j F, L j (fun z => F (fun v => e j (z v)))=L j F)
    (F : (V → ∀ j, X j) → ℝ) :
    tensorLaw L (fun z => F (fun v j => e j (z v j)))=tensorLaw L F := by
  classical
  let ej (j : J) : (V → X j) ≃ (V → X j) := Equiv.piCongrRight fun _ => e j
  let E : (∀ j, V → X j) ≃ (∀ j, V → X j) := Equiv.piCongrRight ej
  have hinv (j : J) (z : V → X j) : lawDensity (L j) (ej j z)=lawDensity (L j) z :=
    lawDensity_equiv (L j) (ej j) (hL j) z
  unfold tensorLaw
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Fintype.sum_equiv E _ _
  intro z
  change (∏ j, lawDensity (L j) (z j))*F (fun v j => e j (z j v)) =
    (∏ j, lawDensity (L j) (ej j (z j)))*F (fun v j => e j (z j v))
  simp only [hinv]
lemma productTupleLaw_affine {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (q a : ∀ j, ZMod (p j)) (hq : ∀ j, q j ≠ 0)
    (F : (TupleVertex → ∀ j, ZMod (p j)) → ℝ) :
    productTupleLaw p (fun z => F (fun v j => q j^2*z v j+a j))=productTupleLaw p F := by
  exact tensorLaw_equiv (fun _ => tupleLaw) (fun j => affineEquiv (q j) (a j) (hq j))
    (fun j => tupleLaw_affine (q j) (a j) (hq j)) F
lemma productTupleLaw_probability {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (hp : ∀ j, tupleMassThreshold ≤ (p j : ℝ)) :
    productTupleLaw p (fun _ => 1)=1 :=
  tensorLaw_probability _ (fun j => tupleLaw_probability (hp j))
lemma productTupleLaw_marginal {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (hp : ∀ j, tupleMassThreshold ≤ (p j : ℝ))
    (v : TupleVertex) (f : (∀ j, ZMod (p j)) → ℝ) :
    productTupleLaw p (fun z => f (z v)) = 𝔼 x, f x := by
  have hinv (a : ∀ j, ZMod (p j)) (F : (TupleVertex → ∀ j, ZMod (p j)) → ℝ) :
      productTupleLaw p (fun z => F (fun v => z v+a))=productTupleLaw p F := by
    change productTupleLaw p (fun z => F (fun v j => z v j+a j))=productTupleLaw p F
    simpa only [one_pow, one_mul] using
      productTupleLaw_affine p (fun _ => 1) a (fun _ => one_ne_zero) F
  rw [invariant_marginal_uniform _ hinv v f, productTupleLaw_probability p hp, one_mul]
lemma productTupleLaw_mean {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (hp : ∀ j, max tupleMassThreshold tupleReflectionThreshold ≤ (p j : ℝ))
    (f : (∀ j, ZMod (p j)) → ℝ) :
    |𝔼 x, f x| ≤ diagonalRoot (productTupleLaw p) f := by
  apply holder_mean _ (productTupleLaw_probability p (fun j => (le_max_left _ _).trans (hp j)))
    (productTupleLaw_marginal p (fun j => (le_max_left _ _).trans (hp j)))
  exact productTupleLaw_signed_holder p (fun j => (le_max_right _ _).trans (hp j))
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical
instance tupleEmptyIndexSubsingleton : Subsingleton (TupleListIndex ∅) where
  allEq i j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    simp only [card_empty, pow_zero] at hi hj
    omega
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical
end SquareDifference
namespace SquareDifference
open Finset
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open Finset
end SquareDifference
namespace SquareDifference
open Finset
end SquareDifference
namespace SquareDifference
open Finset
end SquareDifference
namespace SquareDifference
open Finset
end SquareDifference
namespace SquareDifference
open Finset
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference
end SquareDifference
end LiftAnalysis
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference
noncomputable def expPhase (t : ℝ) : ℂ := Real.fourierChar t
@[simp] lemma expPhase_zero : expPhase 0 = 1 := by simp [expPhase]
@[simp] lemma norm_expPhase (t : ℝ) : ‖expPhase t‖ = 1 := Circle.norm_coe _
lemma expPhase_add (s t : ℝ) : expPhase (s+t) = expPhase s * expPhase t := by
  simp [expPhase, AddChar.map_add_eq_mul]
lemma expPhase_neg (t : ℝ) : expPhase (-t) = conj (expPhase t) := by
  simp only [expPhase, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
lemma expPhase_nat_mul (t : ℝ) (n : ℕ) : expPhase (n*t) = expPhase t^n := by
  simpa only [expPhase, nsmul_eq_mul, Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ))
    (AddChar.map_nsmul_eq_pow Real.fourierChar n t)
lemma stdAddChar_eq_expPhase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a=expPhase ((a.val : ℝ)/p) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring
lemma expPhase_sum {I : Type*} (s : Finset I) (f : I → ℝ) :
    expPhase (∑ i∈s, f i)=∏ i∈s, expPhase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [sum_insert hi, prod_insert hi, expPhase_add, ih]
variable {J : Type*} [Fintype J]
variable (p : J → ℕ) [∀ j, NeZero (p j)]
abbrev ResidueSpace := ∀ j, ZMod (p j)
noncomputable def prodChar (a z : ResidueSpace p) : ℂ :=
  ∏ j, ZMod.stdAddChar (a j*z j)
noncomputable def frequencyAngle (a : ResidueSpace p) : ℝ :=
  ∑ j, (a j).val/(p j : ℝ)
noncomputable def primeSupport (a : ResidueSpace p) : Finset J :=
  univ.filter fun j => a j ≠ 0
noncomputable def supportDenominator (a : ResidueSpace p) : ℕ :=
  ∏ j∈primeSupport p a, p j
@[simp] lemma prodChar_zero (z : ResidueSpace p) : prodChar p 0 z=1 := by
  simp [prodChar, AddChar.map_zero_eq_one]
@[simp] lemma prodChar_zero_right (a : ResidueSpace p) : prodChar p a 0=1 := by
  simp [prodChar, AddChar.map_zero_eq_one]
lemma prodChar_add (a b z : ResidueSpace p) :
    prodChar p (a+b) z=prodChar p a z*prodChar p b z := by
  simp only [prodChar, Pi.add_apply, add_mul, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_add_right (a z w : ResidueSpace p) :
    prodChar p a (z+w)=prodChar p a z*prodChar p a w := by
  simp only [prodChar, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_neg (a z : ResidueSpace p) : prodChar p (-a) z=conj (prodChar p a z) := by
  simp only [prodChar, Pi.neg_apply, neg_mul, AddChar.map_neg_eq_conj, map_prod]
lemma prodChar_sub (a b z : ResidueSpace p) :
    prodChar p (a-b) z=prodChar p a z*conj (prodChar p b z) := by
  rw [sub_eq_add_neg, prodChar_add, prodChar_neg]
lemma prodChar_symm (a z : ResidueSpace p) : prodChar p a z=prodChar p z a := by
  simp only [prodChar, mul_comm]
lemma prodChar_nat_diagonal (a : ResidueSpace p) (n : ℕ) :
    prodChar p a (fun j => (n : ZMod (p j)))=expPhase (n*frequencyAngle p a) := by
  simp only [prodChar, frequencyAngle, mul_sum, expPhase_sum]
  apply prod_congr rfl; intro j _
  rw [expPhase_nat_mul, ← stdAddChar_eq_expPhase]
  simpa only [nsmul_eq_mul, Nat.cast_comm, mul_comm] using
    AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := p j)) n (a j)
lemma complex_expect_prod_pi [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
    (f : ∀ j, X j → ℂ) :
    (𝔼 x : ∀ j, X j, ∏ j, f j (x j))=∏ j, (𝔼 t : X j, f j t) := by
  classical
  simp only [expect_eq_sum_div_card, card_univ, prod_div_distrib,
    Fintype.card_pi, Nat.cast_prod]
  rw [Fintype.prod_sum]
omit [Fintype J] in
lemma prime_char_expect (j : J) (a : ZMod (p j)) :
    (𝔼 z : ZMod (p j), ZMod.stdAddChar (a*z))=if a=0 then 1 else 0 := by
  rw [expect_eq_sum_div_card]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (p j))]
  simp only [card_univ, ZMod.card]
  split_ifs <;> simp_all
lemma prodChar_expect [DecidableEq J] (a : ResidueSpace p) :
    (𝔼 z, prodChar p a z)=if a=0 then 1 else 0 := by
  classical
  unfold prodChar
  rw [complex_expect_prod_pi (fun j (z : ZMod (p j)) => ZMod.stdAddChar (a j*z))]
  simp_rw [prime_char_expect]
  by_cases ha : a=0
  · simp [ha]
  · rw [if_neg ha]
    have hex : ∃ j, a j ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    obtain ⟨j, hj⟩ := hex
    exact prod_eq_zero (mem_univ j) (if_neg hj)
lemma prodChar_orthogonal [DecidableEq J] (a b : ResidueSpace p) :
    (𝔼 z, prodChar p a z*conj (prodChar p b z))=if a=b then 1 else 0 := by
  simp_rw [← prodChar_sub]
  rw [prodChar_expect]
  simp only [sub_eq_zero]
noncomputable def residueGate (q : ℕ) (x : ZMod q) : ℝ :=
  (if x=0 then (q : ℝ) else 0)-1
lemma sum_char_nonzero {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ a : ZMod q, if a≠0 then ZMod.stdAddChar (a*x) else 0)=
      (residueGate q x : ℂ) := by
  classical
  have hs := AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q)
  have he : (∑ a : ZMod q, ZMod.stdAddChar (a*x))=
      (∑ a : ZMod q, if a≠0 then ZMod.stdAddChar (a*x) else 0)+1 := by
    calc
      _ = ∑ a : ZMod q, ((if a≠0 then ZMod.stdAddChar (a*x) else 0)+if a=0 then 1 else 0) := by
        apply sum_congr rfl; intro a _
        by_cases ha : a=0 <;> simp [ha, AddChar.map_zero_eq_one]
      _ = _ := by simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  have hs' : (∑ a : ZMod q, ZMod.stdAddChar (a*x))=if x=0 then (q : ℂ) else 0 := by
    simpa only [ZMod.card, apply_ite, Nat.cast_zero] using hs
  unfold residueGate
  push_cast
  rw [hs'] at he
  split_ifs at * <;> push_cast <;> linear_combination -he
omit [∀ j, NeZero (p j)] in
lemma exact_support_iff [DecidableEq J] (U : Finset J) (a : ResidueSpace p) :
    primeSupport p a=U ↔ ∀j, (a j≠0 ↔ j∈U) := by
  simp only [Finset.ext_iff, primeSupport, mem_filter, mem_univ, true_and]
lemma sum_char_exact [DecidableEq J] (U : Finset J) (z : ResidueSpace p) :
    (∑ a : ResidueSpace p, if primeSupport p a=U then prodChar p a z else 0)=
      ∏ j∈U, (residueGate (p j) (z j) : ℂ) := by
  classical
  let w := fun j (a : ZMod (p j)) =>
    if (if j∈U then a≠0 else a=0) then ZMod.stdAddChar (a*z j) else 0
  have he (a : ResidueSpace p) : (if primeSupport p a=U then prodChar p a z else 0)=∏j, w j (a j) := by
    by_cases ha : primeSupport p a=U
    · rw [if_pos ha]
      apply prod_congr rfl; intro j _
      have hj := (exact_support_iff p U a).mp ha j
      by_cases hU : j∈U <;> simp_all [w]
    · rw [if_neg ha]
      have hn : ∃j, ¬ (a j≠0 ↔ j∈U) := by
        simpa only [exact_support_iff, not_forall] using ha
      obtain ⟨j,hj⟩ := hn
      symm
      apply prod_eq_zero (mem_univ j)
      by_cases hU : j∈U <;> simp_all [w]
  simp only [he]
  rw [← Fintype.prod_sum]
  have hj (j : J) : (∑ a : ZMod (p j), w j a)=if j∈U then (residueGate (p j) (z j) : ℂ) else 1 := by
    by_cases hU : j∈U
    · simp only [w, hU, ite_true]
      exact sum_char_nonzero (z j)
    · simp only [w, hU, ite_false, sum_ite_eq', mem_univ, ite_true, zero_mul, AddChar.map_zero_eq_one]
  simp_rw [hj]
  rw [prod_ite_mem]
  simp
noncomputable def exactGate [DecidableEq J] (U : Finset J) (z : ResidueSpace p) : ℝ :=
  ∏j∈U, residueGate (p j) (z j)
lemma exactGate_fourier [DecidableEq J] (U : Finset J) (z : ResidueSpace p) :
    (exactGate p U z : ℂ) = ∑a∈univ.filter (fun a => primeSupport p a=U), prodChar p a z := by
  rw [sum_filter, sum_char_exact]
  simp only [exactGate, Complex.ofReal_prod]
lemma prodChar_neg_right (a z : ResidueSpace p) : prodChar p a (-z)=conj (prodChar p a z) := by
  rw [prodChar_symm, prodChar_neg, prodChar_symm]
lemma prodChar_sub_right (a z w : ResidueSpace p) :
    prodChar p a (z-w)=prodChar p a z*conj (prodChar p a w) := by
  rw [sub_eq_add_neg, prodChar_add_right, prodChar_neg_right]
noncomputable def fourierPolynomial [DecidableEq J] (c : ResidueSpace p → ℂ) (z : ResidueSpace p) : ℂ :=
  ∑a, c a*prodChar p a z
noncomputable def gateCoefficient [DecidableEq J] (L : ℕ) (f : ℕ → ℂ)
    (B : Finset J) (z a : ResidueSpace p) : ℂ :=
  (L : ℂ)⁻¹*∑n∈range L, f n*expPhase (-(n : ℝ)*frequencyAngle p a)*
    (exactGate p B (z-fun j => (n : ZMod (p j))) : ℂ)
noncomputable def coordinateFreeze [DecidableEq J] (W : Finset J)
    (z x : ResidueSpace p) : ResidueSpace p := fun j => if j∈W then z j else x j
omit [Fintype J] [∀j, NeZero (p j)] in
lemma exactGate_freeze [DecidableEq J] (U W : Finset J) (z x : ResidueSpace p) :
    exactGate p U (coordinateFreeze p W z x)=
      exactGate p (U∩W) z*exactGate p (U\W) x := by
  classical
  have he : U=(U∩W)∪(U\W) := by rw [union_comm, sdiff_union_inter]
  conv_lhs => rw [he]
  rw [exactGate, prod_union (disjoint_sdiff_inter U W).symm]
  congr 1
  · apply prod_congr rfl; intro j hj
    simp only [coordinateFreeze, (mem_inter.mp hj).2, ite_true]
  · apply prod_congr rfl; intro j hj
    simp only [coordinateFreeze, (mem_sdiff.mp hj).2, ite_false]
omit [Fintype J] [∀j, NeZero (p j)] in
lemma coordinateFreeze_sub [DecidableEq J] (W : Finset J) (z x t : ResidueSpace p) :
    coordinateFreeze p W z x-t=coordinateFreeze p W (z-t) (x-t) := by
  ext j
  by_cases hj : j∈W <;> simp [coordinateFreeze, hj]
noncomputable def liftPiece [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U : Finset J) (z : ResidueSpace p) : ℝ :=
  (L : ℝ)⁻¹*∑n∈range L, f n*exactGate p U (z-fun j => (n : ZMod (p j)))
lemma liftPiece_freeze_fourier [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U W : Finset J) (z x : ResidueSpace p) :
    (liftPiece p L f U (coordinateFreeze p W z x) : ℂ)=
      fourierPolynomial p (fun a => if primeSupport p a=U\W then
        gateCoefficient p L (fun n => (f n : ℂ)) (U∩W) z a else 0) x := by
  classical
  have he (n : ℕ) : (exactGate p U (coordinateFreeze p W z x-fun j => (n : ZMod (p j))) : ℂ)=
      (exactGate p (U∩W) (z-fun j => (n : ZMod (p j))) : ℂ)*
        ∑a∈univ.filter (fun a => primeSupport p a=U\W),
          prodChar p a x*conj (expPhase ((n : ℝ)*frequencyAngle p a)) := by
    rw [coordinateFreeze_sub, exactGate_freeze, Complex.ofReal_mul,
      exactGate_fourier p (U\W)]
    simp only [prodChar_sub_right, prodChar_nat_diagonal]
  simp only [liftPiece, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_sum, he]
  simp only [fourierPolynomial, gateCoefficient, ite_mul, zero_mul]
  rw [← sum_filter]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro a _
  rw [sum_mul]
  apply sum_congr rfl; intro n _
  rw [show expPhase (-(n : ℝ)*frequencyAngle p a)=
      conj (expPhase ((n : ℝ)*frequencyAngle p a)) by rw [neg_mul, expPhase_neg]]
  ring
end SquareDifference
end LiftAnalysis
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference
end SquareDifference
namespace SquareDifference
open Finset
section Fiber
variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J]
  (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]
end Fiber
end SquareDifference
end LiftAnalysis
namespace SquareDifference
open Finset
section FrozenAnalysis
variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  {X : J → Type*} [instFintypeXj : ∀j,Fintype (X j)] [instNonemptyXj : ∀j,Nonempty (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]
end FrozenAnalysis
end SquareDifference
namespace SquareDifference
open Finset
end SquareDifference
namespace SquareDifference
open Finset
end SquareDifference
namespace LiftAnalysis
namespace SquareDifference
open Finset
section ActualLift
variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]
noncomputable def supportFamily (Q : ℕ) : Finset (Finset J) :=
  univ.filter (fun U => ∏j∈U,p j≤Q)
noncomputable def truncatedLift (L Q : ℕ) (f : ℕ → ℝ) (x : ResidueSpace p) : ℝ :=
  ∑U∈supportFamily p Q,liftPiece p L f U x
end ActualLift
end SquareDifference
end LiftAnalysis
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open Finset
section Projections
variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  {X : J → Type*} [∀j,Fintype (X j)] [instNonemptyXj : ∀j,Nonempty (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]
end Projections
section GroupProjection
variable {J : Type*} [Fintype J] [DecidableEq J]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,AddCommGroup (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]
end GroupProjection
end SquareDifference
namespace SquareDifference
open Finset
section FrozenFamily
variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]
end FrozenFamily
end SquareDifference
namespace SquareDifference
open Finset
noncomputable abbrev liftSupportFamily {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.supportFamily p
noncomputable abbrev actualLiftPiece {J : Type*} [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.liftPiece p
noncomputable abbrev actualTruncatedLift {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.truncatedLift p
section LiftProjection
variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ)
  [∀j,Fact (p j).Prime]
end LiftProjection
end SquareDifference
namespace SquareDifference
open Finset
section LowFiber
variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,NeZero (p j)]
end LowFiber
end SquareDifference
namespace SquareDifference
open Finset
end SquareDifference
namespace SquareDifference
open Finset
instance tupleVertexNontrivial : Nontrivial TupleVertex := by
  refine ⟨⟨cycleVertex 0,cycleVertex 1,?_⟩⟩
  intro h
  apply tupleCycle_ne_one
  have he := congrFun h (⟨0,by decide⟩ : Fin tupleBlocks)
  simpa only [cycleVertex,pow_zero,pow_one] using he.symm
section ActualTails
variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
end ActualTails
end SquareDifference
namespace SquareDifference
open Finset
section ActualTransfer
variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
end ActualTransfer
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
section RootSieve
variable {I : Type*} [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : ∀i, AddChar (ZMod (m i)) ℂ)
end RootSieve
section RootSieveComplete
variable {I : Type*} [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : ∀i, AddChar (ZMod (m i)) ℂ)
end RootSieveComplete
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
noncomputable def primaryModulus (q p : ℕ) : ℕ := p^(max 1 (q.factorization p))
lemma primaryModulus_pos {q p : ℕ} (hp : p.Prime) : 0<primaryModulus q p := pow_pos hp.pos _
instance primaryModulus_neZero (q p : ℕ) [Fact p.Prime] : NeZero (primaryModulus q p) :=
  ⟨(primaryModulus_pos (Fact.out : p.Prime)).ne'⟩
noncomputable def expPhase (t : ℝ) : ℂ := Real.fourierChar t
section CRTRootSieve
variable {I : Type*} [Fintype I] [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))
end CRTRootSieve
section PrimaryCoefficient
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
  (q : ℕ) [NeZero q]
  (hq : q∣∏i, primaryModulus q (p i))
noncomputable def primaryActive : Finset I := univ.filter (fun i => p i∣q)
omit [DecidableEq I] [∀i, Fact (p i).Prime] [NeZero q] in
@[simp] lemma mem_primaryActive (i : I) : i∈primaryActive p q ↔ p i∣q := by
  simp only [primaryActive,mem_filter,mem_univ,true_and]
end PrimaryCoefficient
section KernelCoefficient
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
  (b : ℚ) (hb : b.den ∣ ∏ i, primaryModulus b.den (p i))
  (R : Finset I) (c : ∀ i, ZMod (p i))
end KernelCoefficient
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
section ActualWeight
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime]
  (R : Finset I) (c : ∀i, ZMod (p i))
variable (q : ℕ) [NeZero q] (hpq : ∀i,p i∣q)
end ActualWeight
section CompleteWeight
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))
variable (hinj : Function.Injective p) (b : ℚ)
  (hb : b.den∣∏i,primaryModulus b.den (p i))
end CompleteWeight
noncomputable def smallQuadraticModulus (p : ℕ) : ℕ := if p=2 then 8 else p
lemma smallQuadraticModulus_pos {p : ℕ} (hp : p.Prime) : 0<smallQuadraticModulus p := by
  unfold smallQuadraticModulus
  split_ifs
  · norm_num
  · exact hp.pos
instance {p : ℕ} [Fact p.Prime] : NeZero (smallQuadraticModulus p) :=
  ⟨(smallQuadraticModulus_pos (Fact.out : p.Prime)).ne'⟩
section CompleteCRT
variable {I : Type*} [Fintype I] [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))
end CompleteCRT
@[simp] lemma expPhase_zero : expPhase 0 = 1 := by simp [expPhase]
@[simp] lemma norm_expPhase (t : ℝ) : ‖expPhase t‖ = 1 := Circle.norm_coe _
lemma expPhase_add (s t : ℝ) : expPhase (s+t) = expPhase s * expPhase t := by
  simp [expPhase, AddChar.map_add_eq_mul]
lemma expPhase_neg (t : ℝ) : expPhase (-t) = conj (expPhase t) := by
  simp only [expPhase, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
lemma expPhase_nat_mul (t : ℝ) (n : ℕ) : expPhase (n*t) = expPhase t^n := by
  simpa only [expPhase, nsmul_eq_mul, Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ))
    (AddChar.map_nsmul_eq_pow Real.fourierChar n t)
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
open scoped Classical
section ActualKernelCoefficient
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))
end ActualKernelCoefficient
lemma stdAddChar_eq_expPhase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a=expPhase ((a.val : ℝ)/p) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring
section ActualKernelTerms
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))
end ActualKernelTerms
end SquareDifference
namespace SquareDifference
open Finset
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
open Finset
end SquareDifference
namespace SquareDifference
open Finset
section GridModel
variable {I : Type*} [Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
include hinj
variable (R : Finset I) (c : ∀i,ZMod (p i))
omit hinj in
instance smallProductNeZero : NeZero (∏i,smallQuadraticModulus (p i)) :=
  ⟨(prod_pos (fun i _ => smallQuadraticModulus_pos (Fact.out : (p i).Prime))).ne'⟩
end GridModel
end SquareDifference
namespace SquareDifference
open Finset
section SmallCoordinates
variable {I : Type*} [instFintypeI : Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
variable (R : Finset I) (c : ∀i,ZMod (p i))
end SmallCoordinates
end SquareDifference
open Filter
open scoped Topology
namespace SquareDifference
end SquareDifference
namespace SquareDifference
open Finset
section UniformFinal
variable {I : Type*} [instFintypeI : Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [instFactNatPrimepi : ∀i, Fact (p i).Prime]
  (R : Finset I) (c : ∀i,ZMod (p i))
end UniformFinal
end SquareDifference
open Finset Complex
open scoped BigOperators ComplexConjugate
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace SquareDifference
section CyclicFourier
variable {q : ℕ} [NeZero q]
end CyclicFourier
end SquareDifference
namespace SquareDifference
open Finset
section SequenceKernel
variable {q : ℕ} [instNeZeroq : NeZero q]
end SequenceKernel
end SquareDifference
namespace SquareDifference
open Finset
section OrderedModel
variable {q : ℕ} [NeZero q]
end OrderedModel
end SquareDifference
namespace SquareDifference
open Finset
section KernelTransforms
variable {q : ℕ} [NeZero q]
end KernelTransforms
end SquareDifference
namespace SquareDifference
open Finset
section ActualBilinear
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime]
  (R : Finset I) (c : ∀i,ZMod (p i))
end ActualBilinear
end SquareDifference
namespace SquareDifference
open Finset
section DualCoordinates
variable {q : ℕ} [NeZero q]
end DualCoordinates
section ProductDual
variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)] (hcop : Pairwise fun i j => (m i).Coprime (m j))
end ProductDual
end SquareDifference
namespace SquareDifference
open Finset
section SmallDual
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)
end SmallDual
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference
open Finset
section PairFourier
variable {J : Type*} [Fintype J] [DecidableEq J]
  (p : J → ℕ) [∀j,NeZero (p j)]
noncomputable def residueFourier (F : ResidueSpace p → ℂ) (a : ResidueSpace p) : ℂ :=
  𝔼 x,F x*conj (prodChar p a x)
lemma residueFourier_polynomial (c : ResidueSpace p → ℂ) (a : ResidueSpace p) :
    residueFourier p (fourierPolynomial p c) a=c a := by
  unfold residueFourier fourierPolynomial
  simp only [sum_mul,mul_assoc,expect_sum_comm]
  simp only [← mul_expect,prodChar_orthogonal,mul_ite,mul_one,mul_zero]
  simp
end PairFourier
end SquareDifference
namespace SquareDifference
end SquareDifference
end LiftAnalysis
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference
end SquareDifference
end LiftAnalysis
end
end OAI
namespace OAI
section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference
end SquareDifference
namespace SquareDifference
open scoped ComplexConjugate
section PairTail
variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ)
  [∀j,Fact (p j).Prime]
end PairTail
end SquareDifference
namespace SquareDifference
open Finset
section RootModel
variable {I : Type*} [instFintypeI : Fintype I] [instDecidableEqI : DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)] (R : Finset I)
end RootModel
end SquareDifference
end LiftAnalysis
namespace SquareDifference
open Finset
open scoped ComplexConjugate
section ModelPair
variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)]
  (hcop : Pairwise fun i j => (m i).Coprime (m j))
end ModelPair
end SquareDifference
namespace SquareDifference
open Finset
section RootCombination
variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [instNeZeromi : ∀i,NeZero (m i)] (R : Finset I)
end RootCombination
section ActualRootCombination
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)
end ActualRootCombination
end SquareDifference
namespace SquareDifference
open Finset
section BilinearGrid
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)
include hinj
end BilinearGrid
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators ComplexConjugate
namespace SquareDifference
namespace PairBridge
open LiftAnalysis.SquareDifference
section Fourier
variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ)
  [instNeZeropj : ∀j,NeZero (p j)]
lemma actualLiftPiece_eq {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (L : ℕ) (f : ℕ → ℝ) (U : Finset J) (x : ResidueSpace p) :
    actualLiftPiece p L f U x=liftPiece p L f U x := rfl
lemma actualSupportFamily_eq {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (Q : ℕ) :
    liftSupportFamily p Q=univ.filter (fun U : Finset J => ∏j∈U,p j≤Q) := rfl
noncomputable def sequenceCoeff (L : ℕ) (f : ℕ → ℝ) (a : ResidueSpace p) : ℂ :=
  (L : ℂ)⁻¹*∑n∈range L,(f n:ℂ)*conj (prodChar p a (fun j => (n:ZMod (p j))))
lemma gateCoefficient_empty (L : ℕ) (f : ℕ → ℝ) (z a : ResidueSpace p) :
    gateCoefficient p L (fun n => (f n:ℂ)) ∅ z a=sequenceCoeff p L f a := by
  simp only [gateCoefficient,exactGate,prod_empty,Complex.ofReal_one,mul_one,
    sequenceCoeff,prodChar_nat_diagonal,neg_mul,LiftAnalysis.SquareDifference.expPhase_neg]
lemma actualPiece_polynomial (L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    (fun x => (actualLiftPiece p L f U x:ℂ))=
      fourierPolynomial p (fun a => if primeSupport p a=U then sequenceCoeff p L f a else 0) := by
  funext x
  have h := LiftAnalysis.SquareDifference.liftPiece_freeze_fourier p L f U ∅ (0:ResidueSpace p) x
  have hc : LiftAnalysis.SquareDifference.coordinateFreeze p ∅ (0:ResidueSpace p) x=x := by
    funext j
    simp only [LiftAnalysis.SquareDifference.coordinateFreeze,notMem_empty,ite_false]
  rw [hc] at h
  simpa only [sdiff_empty,inter_empty,gateCoefficient_empty,actualLiftPiece_eq] using h
lemma polynomial_sum {T : Type*} (s : Finset T) (c : T → ResidueSpace p → ℂ) :
    (fun x => ∑t∈s,fourierPolynomial p (c t) x)=
      fourierPolynomial p (fun a => ∑t∈s,c t a) := by
  funext x
  simp only [fourierPolynomial,sum_mul]
  rw [sum_comm]
lemma actualLift_polynomial (L Q : ℕ) (f : ℕ → ℝ) :
    (fun x => (actualTruncatedLift p L Q f x:ℂ))=
      fourierPolynomial p (fun a => if supportDenominator p a≤Q then sequenceCoeff p L f a else 0) := by
  change (fun x => (((∑U∈liftSupportFamily p Q,actualLiftPiece p L f U x):ℝ):ℂ))=_
  simp only [Complex.ofReal_sum]
  have he (U : Finset J) (x : ResidueSpace p) := congrFun (actualPiece_polynomial p L f U) x
  simp_rw [he]
  rw [polynomial_sum]
  congr 1
  funext a
  simp only [actualSupportFamily_eq,sum_filter]
  rw [sum_eq_single (primeSupport p a)]
  · simp only [ite_true,LiftAnalysis.SquareDifference.supportDenominator]
    rfl
  · intro U _ hU
    by_cases h : ∏j∈U,p j≤Q
    · simp only [h,ite_true,Ne.symm hU,ite_false]
    · simp only [h,ite_false]
  · simp
lemma actualLift_fourier (L Q : ℕ) (f : ℕ → ℝ) (a : ResidueSpace p) :
    residueFourier p (fun x => (actualTruncatedLift p L Q f x:ℂ)) a=
      if supportDenominator p a≤Q then sequenceCoeff p L f a else 0 := by
  rw [actualLift_polynomial,residueFourier_polynomial]
lemma actualLift_mean (L Q : ℕ) (hQ : 1≤Q) (f : ℕ → ℝ) :
    (𝔼 x,actualTruncatedLift p L Q f x)=(L:ℝ)⁻¹*∑n∈range L,f n := by
  have h := actualLift_fourier p L Q f (0:ResidueSpace p)
  have hc (x : ResidueSpace p) : prodChar p (0:ResidueSpace p) x=1 := by
    simp only [prodChar,Pi.zero_apply,zero_mul,AddChar.map_zero_eq_one,prod_const_one]
  have hd : supportDenominator p (0:ResidueSpace p)=1 := by
    simp only [supportDenominator,primeSupport,Pi.zero_apply,ne_eq,not_true_eq_false,filter_false,prod_empty]
  simp only [residueFourier,hc,map_one,mul_one,hd,if_pos hQ,sequenceCoeff] at h
  apply Complex.ofReal_injective
  simpa only [expect_eq_sum_div_card,Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast,
    Complex.ofReal_mul,Complex.ofReal_inv] using h
end Fourier
end PairBridge
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
noncomputable def natIndicator (A : Finset ℕ) (n : ℕ) : ℝ := if n∈A then 1 else 0
lemma sum_natIndicator (N : ℕ) (A : Finset ℕ) (hA : A⊆range N) :
    (∑n∈range N,natIndicator A n)=(A.card:ℝ) := by
  unfold natIndicator
  rw [sum_boole]
  congr 1
  exact congrArg Finset.card (filter_mem_eq_inter.trans (inter_eq_right.mpr hA))
section Functional
variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
noncomputable def setFunctional (N Q : ℕ) (A : Finset ℕ) : ℝ :=
  diagonalIntegral (productTupleLaw p) (actualTruncatedLift p N Q (natIndicator A))
lemma setFunctional_density (hp : ∀j,max tupleMassThreshold tupleReflectionThreshold≤(p j:ℝ))
    (N Q : ℕ) (hQ : 1≤Q) (A : Finset ℕ) (hA : A⊆range N) :
    ((A.card:ℝ)/(N:ℝ))^(Fintype.card TupleVertex)≤ setFunctional p N Q A := by
  have hm := productTupleLaw_mean p hp (actualTruncatedLift p N Q (natIndicator A))
  rw [PairBridge.actualLift_mean p N Q hQ,sum_natIndicator N A hA] at hm
  have h0 : 0≤(A.card:ℝ)/(N:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [show (N:ℝ)⁻¹*(A.card:ℝ)=(A.card:ℝ)/(N:ℝ) by ring,abs_of_nonneg h0] at hm
  have hh := pow_le_pow_left₀ h0 hm (Fintype.card TupleVertex)
  rw [diagonalRoot_pow _ (productTupleLaw_diagonal_nonneg p (fun j => (le_max_right _ _).trans (hp j)))] at hh
  exact hh
end Functional
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section ResidueCombine
variable {J : Type*} [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]
  (hp : Pairwise fun i j => (p i).Coprime (p j))
  (M : ℕ) [instNeZeroM : NeZero M] (hM : ∀j,M.Coprime (p j))
include hp hM
end ResidueCombine
section ActualResidueTransfer
variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
  (hp : Pairwise fun i j => (p i).Coprime (p j))
  (M : ℕ) [NeZero M] (hM : ∀j,M.Coprime (p j))
include hp hM
end ActualResidueTransfer
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators ComplexConjugate
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Interval
variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]
end Interval
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace LiftAnalysis
namespace SquareDifference
open Finset
section SupportCounting
variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ)
  [∀j,Fact (p j).Prime] (hinj : Function.Injective p)
include hinj
end SupportCounting
end SquareDifference
end LiftAnalysis
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Counting
variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
end Counting
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators ComplexConjugate
namespace SquareDifference.PairBridge
open LiftAnalysis.SquareDifference
section Outside
variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)] (B : Finset J)
end Outside
end SquareDifference.PairBridge
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open Finset
section TensorExpansion
variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (L E : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
end TensorExpansion
end SquareDifference
namespace SquareDifference
open Finset
section TensorFreeze
variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (M L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
end TensorFreeze
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
section TensorPair
variable {J V : Type*} [Fintype J] [instDecidableEqJ : DecidableEq J] [Fintype V] [DecidableEq V]
  {X Ω : J → Type*} [instFintypeXj : ∀j,Fintype (X j)] [∀j,DecidableEq (X j)] [∀j,Fintype (Ω j)]
  (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (u v : V)
  (a b : ∀j,Ω j → X j)
end TensorPair
section PiProduct
variable {J : Type*} [Fintype J] [DecidableEq J] {X Y : J → Type*}
  [∀j,Fintype (X j)] [∀j,Fintype (Y j)]
end PiProduct
section FrozenPair
variable [Fintype TupleVertex] [DecidableEq TupleVertex]
open LiftAnalysis.SquareDifference PairBridge
variable {J : Type*} [Fintype J] [DecidableEq J]
  (p : J → ℕ) [∀j,Fact (p j).Prime] (hp : ∀j,tupleMassThreshold ≤ (p j:ℝ))
end FrozenPair
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
section Localized
variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
  (hL : ∀j F,(∀z,0≤F z) → 0≤L j F) (hm : ∀j,L j (fun _ => 1)=1)
end Localized
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
def OtherVertices {V : Type*} (u v : V) := {w : V // w≠u ∧ w≠v}
instance {V : Type*} [Fintype V] [DecidableEq V] (u v : V) : Fintype (OtherVertices u v) := inferInstanceAs (Fintype {w : V // w≠u ∧ w≠v})
instance {V : Type*} [DecidableEq V] (u v : V) : DecidableEq (OtherVertices u v) := inferInstanceAs (DecidableEq {w : V // w≠u ∧ w≠v})
section PieceBound
variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  (p : J → ℕ) [∀j,Fact (p j).Prime]
end PieceBound
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Truncate
variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]
end Truncate
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators ComplexConjugate
namespace SquareDifference
open LiftAnalysis.SquareDifference
section KernelPair
variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)
  (R : Finset I) (c : ∀i,ZMod (p i))
end KernelPair
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators ComplexConjugate
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Reindex
variable {J K : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] [instFintypeK : Fintype K] [instDecidableEqK : DecidableEq K]
  (p : J → ℕ) (m : K → ℕ) [instNeZeropj : ∀j,NeZero (p j)] [∀k,NeZero (m k)]
  (e : K ≃ J) (hm : m=fun k => p (e k))
end Reindex
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Indexed
variable {S J : Type*} [instFintypeS : Fintype S] [instDecidableEqS : DecidableEq S] [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ)
abbrev extendedPrime : S ⊕ J → ℕ := Sum.elim ps p
noncomputable def extendedRoots (B : Finset J) : Finset (S ⊕ J) := univ.disjSum B
@[simp] lemma inl_mem_extendedRoots {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J] (B : Finset J) (s : S) : Sum.inl s∈extendedRoots (S:=S) B := by simp [extendedRoots]
@[simp] lemma inr_mem_extendedRoots {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J] (B : Finset J) (j : J) : Sum.inr j∈extendedRoots (S:=S) B ↔ j∈B := by simp [extendedRoots]
instance extendedPrime_prime [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime] :
    ∀i,Fact (extendedPrime ps p i).Prime := fun i => by cases i <;> dsimp [extendedPrime] <;> infer_instance
end Indexed
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Extended
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime]
end Extended
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators ComplexConjugate
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Selected
variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]
end Selected
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators ComplexConjugate
namespace SquareDifference
open LiftAnalysis.SquareDifference PairBridge
section Coefficient
variable {J : Type*} [Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]
end Coefficient
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Small
variable {S : Type*} [Fintype S] [instDecidableEqS : DecidableEq S] (ps : S → ℕ)
noncomputable def smallModulus : ℕ := ∏s,smallQuadraticModulus (ps s)
lemma smallModulus_dvd {S : Type*}
    [Fintype S]
    [DecidableEq S]
    (ps : S → ℕ) (s : S) : smallQuadraticModulus (ps s)∣smallModulus ps := dvd_prod_of_mem _ (mem_univ s)
noncomputable def smallProjection (s : S) : ZMod (smallModulus ps) →+* ZMod (smallQuadraticModulus (ps s)) :=
  ZMod.castHom (smallModulus_dvd ps s) _
@[simp] lemma smallProjection_nat (s : S) (n : ℕ) : smallProjection ps s (n:ZMod (smallModulus ps))=(n:ZMod (smallQuadraticModulus (ps s))) := map_natCast _ _
end Small
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Roots
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [instFactNatPrimepsi : ∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]
end Roots
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators ComplexConjugate
namespace SquareDifference
open LiftAnalysis.SquareDifference PairBridge
section LowPair
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]
end LowPair
section PairTail
variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
end PairTail
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference PairBridge
section FullPair
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]
end FullPair
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section GenericLow
variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  (p : J → ℕ) [∀j,Fact (p j).Prime]
end GenericLow
section Retained
variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]
end Retained
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
end SquareDifference
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Low
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]
end Low
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped Topology
namespace SquareDifference
noncomputable def sourceBeta : ℝ := 1/100000
noncomputable def powerCutoff (N : ℕ) (a : ℝ) : ℕ := ⌊(N:ℝ)^a⌋₊
lemma sourceBeta_pos : 0<sourceBeta := by norm_num [sourceBeta]
lemma powerCutoff_pos (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : 0≤a) : 0<powerCutoff N a := by
  exact Nat.floor_pos.mpr (Real.one_le_rpow (by exact_mod_cast hN) ha)
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped Topology
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped Topology
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped Topology
namespace SquareDifference
open LiftAnalysis.SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped Topology
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Ordered
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]
end Ordered
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Global
variable {S J : Type} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]
end Global
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped Topology
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped BigOperators Topology
namespace SquareDifference
open LiftAnalysis.SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
section Mixed
variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
end Mixed
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped BigOperators Topology
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Mixed
variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
end Mixed
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
section Small
variable {S : Type*} [Fintype S] [instDecidableEqS : DecidableEq S] (ps : S → ℕ) [∀s,Fact (ps s).Prime]
end Small
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
section Average
variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
end Average
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped BigOperators Topology
namespace SquareDifference
section Budget
variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
end Budget
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped BigOperators Topology
namespace SquareDifference
open LiftAnalysis.SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped Topology
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped BigOperators Topology
namespace SquareDifference
open LiftAnalysis.SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
namespace SquareDifference
def smallPrimeSet (P : ℕ) : Finset ℕ := (range P).filter Nat.Prime
def largePrimeSet (P N : ℕ) : Finset ℕ := (Icc P N).filter Nat.Prime
abbrev SmallPrime (P : ℕ) := ↥(smallPrimeSet P)
abbrev LargePrime (P N : ℕ) := ↥(largePrimeSet P N)
def smallPrimes (P : ℕ) : SmallPrime P → ℕ := Subtype.val
def largePrimes (P N : ℕ) : LargePrime P N → ℕ := Subtype.val
instance smallPrimes_fact (P : ℕ) (s : SmallPrime P) : Fact (smallPrimes P s).Prime :=
  ⟨(mem_filter.mp s.property).2⟩
instance largePrimes_fact (P N : ℕ) (s : LargePrime P N) : Fact (largePrimes P N s).Prime :=
  ⟨(mem_filter.mp s.property).2⟩
lemma largePrimes_ge (P N : ℕ) (s : LargePrime P N) : P≤largePrimes P N s := (mem_Icc.mp (mem_filter.mp s.property).1).1
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
open scoped BigOperators
namespace SquareDifference
open LiftAnalysis.SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset Filter
open scoped Topology
namespace SquareDifference
end SquareDifference
end
end OAI
namespace OAI
section
open Finset
namespace SquareDifference
end SquareDifference
end
end OAI
open Finset OAI.SquareDifference
noncomputable def Fexpl : ℕ → ℕ → Finset ℕ → ℝ :=
fun (P N : ℕ) (A : Finset ℕ) => open Finset in
  let H := 24; let T := 80
  let V := Fin (2*T+1) → Equiv.Perm (Fin H)
  let J := {q // q ∈ (Icc P N).filter Nat.Prime}
  haveI : ∀ j : J, NeZero j.1 := fun j => ⟨(mem_filter.1 j.2).2.ne_zero⟩
  let g : (∀ j : J, ZMod j.1) → ℝ := fun x => ∑ U ∈ univ.filter (fun U : Finset J => ∏ j ∈ U, j.1 ≤ ⌊(N:ℝ)^(1/100000:ℝ)⌋₊),
    (N:ℝ)⁻¹ * ∑ n ∈ range N, (if n ∈ A then 1 else 0) * ∏ j ∈ U, ((if x j - n = 0 then (j.1:ℝ) else 0) - 1)
  let M : (q : ℕ) → [NeZero q] → ((V → ZMod q) → ℝ) → ℝ := fun q _ G =>
    ∑ S ∈ (univ : Finset (Fin (2*T+1))).powerset, let E := ({b // b ∉ S} → Equiv.Perm (Fin H)) × Fin ((H.factorial/2)^S.card)
    if S.card ≤ T+1 then (q:ℝ)^(-(S.card:ℝ)/16) *
      univ.expect fun Y : E → ZMod q => univ.expect fun i : V → Fin ((H.factorial/2)^S.card) =>
      (∏ e ∈ (by classical exact if S.card ≤ T then univ.filter fun e : E × E =>
          T+1 ≤ (univ.filter fun b => e.2.1 b = e.1.1 b * finRotate H).card else ∅),
        (by classical exact if Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) then (1:ℝ) else 0)) *
      Real.exp (1/2 * ∑ v, ∑ w, (∑ b ∈ S, ∑ π : {π : Fin H × Fin H // π.1 < π.2},
          if w = Function.update v b (v b * Equiv.swap π.1.1 π.1.2) then (1/(10*(H:ℝ)^2))^(π.1.2.val - π.1.1.val) else 0) *
        if i v = i w then 1 else 0) *
      G fun v => Y (fun b => v b.1, i v)
    else 0
  ∑ z : ∀ j : J, V → ZMod j.1, (∏ j, (M j.1 fun _ => 1)⁻¹ * M j.1 fun y => if y = z j then 1 else 0) * ∏ v, g fun j => z j v

lemma validity_expl (q : ℕ) [Fact q.Prime] (S : Finset (Fin tupleBlocks)) (Y : TupleListEntry S → ZMod q) :
    tupleValidity S Y = (∏ e ∈ (by classical exact if S.card ≤ 80 then univ.filter fun e : TupleListEntry S × TupleListEntry S =>
          80+1 ≤ (univ.filter fun b => e.2.1 b = e.1.1 b * finRotate tupleH).card else ∅),
        (by classical exact if Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) then (1:ℝ) else 0)) := by
  unfold tupleValidity tupleListEdges addressEdge squareIndicator tupleCycle tupleT
  congr!
lemma weight_expl (S : Finset (Fin tupleBlocks)) (i : TupleVertex → TupleListIndex S) : tupleWeight S i = Real.exp (1/2 * ∑ v, ∑ w, (∑ b ∈ S, ∑ π : {π : Fin 24 × Fin 24 // π.1 < π.2},
          if w = Function.update v b (v b * Equiv.swap π.1.1 π.1.2) then (1/(10*((24:ℕ):ℝ)^2))^(π.1.2.val - π.1.1.val) else 0) *
        if i v = i w then 1 else 0) := by
  unfold tupleWeight indexWeight indexEnergy indexCross interaction vertexSwap tupleDelta
  rfl
lemma component_expl (q : ℕ) [Fact q.Prime] (S : Finset (Fin tupleBlocks)) (G : (TupleVertex → ZMod q) → ℝ) :
    tupleComponent S G = (let H := 24; let T := 80; let E := ({b // b ∉ S} → Equiv.Perm (Fin H)) × Fin ((H.factorial/2)^S.card)
      univ.expect fun Y : E → ZMod q => univ.expect fun i : (Fin (2*T+1) → Equiv.Perm (Fin H)) → Fin ((H.factorial/2)^S.card) =>
      (∏ e ∈ (by classical exact if S.card ≤ T then univ.filter fun e : E × E =>
          T+1 ≤ (univ.filter fun b => e.2.1 b = e.1.1 b * finRotate H).card else ∅),
        (by classical exact if Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) then (1:ℝ) else 0)) *
      Real.exp (1/2 * ∑ v, ∑ w, (∑ b ∈ S, ∑ π : {π : Fin H × Fin H // π.1 < π.2},
          if w = Function.update v b (v b * Equiv.swap π.1.1 π.1.2) then (1/(10*(H:ℝ)^2))^(π.1.2.val - π.1.1.val) else 0) *
        if i v = i w then 1 else 0) *
      G fun v => Y (fun b => v b.1, i v)) := by
  unfold tupleComponent
  simp only [validity_expl, weight_expl]
  rfl
lemma law_apply {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀ j, Fact (p j).Prime] (F : (TupleVertex → ∀ j, ZMod (p j)) → ℝ) :
    productTupleLaw p F = ∑ z : ∀ j, TupleVertex → ZMod (p j), (∏ j, (tupleMixture (p := p j) fun _ => 1)⁻¹ * tupleMixture (p := p j) fun y => if y = z j then 1 else 0) * F (fun v j => z j v) := by
  unfold productTupleLaw tensorLaw lawDensity tupleLaw
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply]
lemma Fexpl_eq (P N : ℕ) (A : Finset ℕ) : Fexpl P N A = setFunctional (largePrimes P N) N (powerCutoff N sourceBeta) A := by
  unfold setFunctional diagonalIntegral multilinearIntegral
  rw [law_apply]
  unfold tupleMixture tupleMixtureWeight
  simp only [component_expl]
  unfold Fexpl actualTruncatedLift OAI.LiftAnalysis.SquareDifference.truncatedLift OAI.LiftAnalysis.SquareDifference.supportFamily OAI.LiftAnalysis.SquareDifference.liftPiece OAI.LiftAnalysis.SquareDifference.exactGate OAI.LiftAnalysis.SquareDifference.residueGate natIndicator powerCutoff sourceBeta largePrimes tupleBlocks tupleT
  rfl
theorem green65_H1 : ∀ᶠ P : ℕ in Filter.atTop, ∃ d : ℕ, 0 < d ∧ ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.range N → ((A.card:ℝ)/N)^d ≤
  (fun (P N : ℕ) (A : Finset ℕ) => open Finset in
  let H := 24; let T := 80
  let V := Fin (2*T+1) → Equiv.Perm (Fin H)
  let J := {q // q ∈ (Icc P N).filter Nat.Prime}
  haveI : ∀ j : J, NeZero j.1 := fun j => ⟨(mem_filter.1 j.2).2.ne_zero⟩
  let g : (∀ j : J, ZMod j.1) → ℝ := fun x => ∑ U ∈ univ.filter (fun U : Finset J => ∏ j ∈ U, j.1 ≤ ⌊(N:ℝ)^(1/100000:ℝ)⌋₊),
    (N:ℝ)⁻¹ * ∑ n ∈ range N, (if n ∈ A then 1 else 0) * ∏ j ∈ U, ((if x j - n = 0 then (j.1:ℝ) else 0) - 1)
  let M : (q : ℕ) → [NeZero q] → ((V → ZMod q) → ℝ) → ℝ := fun q _ G =>
    ∑ S ∈ (univ : Finset (Fin (2*T+1))).powerset, let E := ({b // b ∉ S} → Equiv.Perm (Fin H)) × Fin ((H.factorial/2)^S.card)
    if S.card ≤ T+1 then (q:ℝ)^(-(S.card:ℝ)/16) *
      univ.expect fun Y : E → ZMod q => univ.expect fun i : V → Fin ((H.factorial/2)^S.card) =>
      (∏ e ∈ (by classical exact if S.card ≤ T then univ.filter fun e : E × E =>
          T+1 ≤ (univ.filter fun b => e.2.1 b = e.1.1 b * finRotate H).card else ∅),
        (by classical exact if Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) then (1:ℝ) else 0)) *
      Real.exp (1/2 * ∑ v, ∑ w, (∑ b ∈ S, ∑ π : {π : Fin H × Fin H // π.1 < π.2},
          if w = Function.update v b (v b * Equiv.swap π.1.1 π.1.2) then (1/(10*(H:ℝ)^2))^(π.1.2.val - π.1.1.val) else 0) *
        if i v = i w then 1 else 0) *
      G fun v => Y (fun b => v b.1, i v)
    else 0
  ∑ z : ∀ j : J, V → ZMod j.1, (∏ j, (M j.1 fun _ => 1)⁻¹ * M j.1 fun y => if y = z j then 1 else 0) * ∏ v, g fun j => z j v) P N A := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (max tupleMassThreshold tupleReflectionThreshold)] with P hP
  refine ⟨Fintype.card TupleVertex, Fintype.card_pos, fun N hN A hA => ?_⟩
  show _ ≤ Fexpl P N A
  rw [Fexpl_eq]
  exact setFunctional_density (largePrimes P N) (fun j => hP.trans (by exact_mod_cast largePrimes_ge P N j)) N _ (powerCutoff_pos N hN _ sourceBeta_pos.le) A hA
theorem OMA.solution : OMA.R_Green65_green_65_R1.H1 := green65_H1
