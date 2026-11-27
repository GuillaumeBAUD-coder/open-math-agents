import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

/-!
# Proof of step H1 for OeisA105751 (moll_p_mod_4_eq_1, R1)

For every prime `p ≡ 1 (mod 4)` and every `n : ℕ`, `(p : ℤ) ^ padicValNat p n.factorial ∣ OeisA105751.a n`.
-/

-- Step OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H1: hypothesis H1 of reduction OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1
-- Credit: @nijv

namespace H1Proof

/-- The Gaussian integer `∏_{k < n} (1 + k i)`. -/
def Zg (n : ℕ) : GaussianInt := ∏ k ∈ Finset.range n, (⟨1, k⟩ : GaussianInt)

lemma a_eq (n : ℕ) : OeisA105751.a n = (Zg (n + 1)).im := by
  unfold OeisA105751.a Zg
  have h : (∏ k ∈ Finset.range (n + 1), (1 + (k : ℂ) * Complex.I)) =
      GaussianInt.toComplex (∏ k ∈ Finset.range (n + 1), (⟨1, k⟩ : GaussianInt)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [GaussianInt.toComplex_def']
    push_cast
    ring
  simp only
  rw [h, ← GaussianInt.intCast_im, Int.floor_intCast]

/-- For a prime `p ≡ 1 (mod 4)` and any `e : ℕ`, there exists `r : ℤ` with `p ^ (e + 1) ∣ r ^ 2 + 1`. -/
lemma exists_sq_add_one_dvd_pow (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) :
    ∀ e : ℕ, ∃ r : ℤ, (p : ℤ) ^ (e + 1) ∣ r ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  intro e
  induction e with
  | zero =>
    have hsq : IsSquare (-1 : ZMod p) := (ZMod.exists_sq_eq_neg_one_iff).2 (by omega)
    rcases hsq with ⟨x, hx⟩
    refine ⟨(x.val : ℤ), ?_⟩
    rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, pow_two, ← hx]
    ring
  | succ e ih =>
    rcases ih with ⟨r, q, hq⟩
    have hp_dvd : (p : ℤ) ∣ r ^ 2 + 1 :=
      dvd_trans (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero e)) ⟨q, hq⟩
    have hr_sq : (r : ZMod p) ^ 2 + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (r ^ 2 + 1) p).2 hp_dvd
      simpa using this
    have h2_ne : (2 : ZMod p) ≠ 0 := by
      intro h2
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by simpa using h2)
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hge : 2 ≤ p := hp.two_le
      omega
    have hr_ne : (r : ZMod p) ≠ 0 := by
      intro hr0
      rw [hr0] at hr_sq
      simp at hr_sq
    have h2r_ne : ((2 * r : ℤ) : ZMod p) ≠ 0 := by
      push_cast
      exact mul_ne_zero h2_ne hr_ne
    let u : ZMod p := -(q : ZMod p) * (((2 * r : ℤ) : ZMod p))⁻¹
    let t : ℤ := (u.val : ℤ)
    have ht : (p : ℤ) ∣ q + 2 * r * t := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hu : (t : ZMod p) = u := by
        simp only [t, Int.cast_natCast, ZMod.natCast_zmod_val]
      have hcalc : ((q + 2 * r * t : ℤ) : ZMod p) =
          (q : ZMod p) + ((2 * r : ℤ) : ZMod p) * u := by
        rw [← hu]
        push_cast
        ring
      rw [hcalc]
      simp only [u]
      calc
        (q : ZMod p) + ((2 * r : ℤ) : ZMod p) * (-(q : ZMod p) * (((2 * r : ℤ) : ZMod p))⁻¹)
            = (q : ZMod p) -
                (q : ZMod p) * (((2 * r : ℤ) : ZMod p) * (((2 * r : ℤ) : ZMod p))⁻¹) := by ring
        _ = 0 := by rw [mul_inv_cancel₀ h2r_ne, mul_one, sub_self]
    rcases ht with ⟨c, hc⟩
    refine ⟨r + t * (p : ℤ) ^ (e + 1), c + t ^ 2 * (p : ℤ) ^ e, ?_⟩
    linear_combination hq + (p : ℤ) ^ (e + 1) * hc

/-- Modulo `M` dividing `s ^ 2 + 1`, `(Zg n).re + s * (Zg n).im ≡ ∏_{k < n} (1 + k s)`. -/
lemma dvd_re_add_mul_im_sub_prod (M s : ℤ) (hs : M ∣ s ^ 2 + 1) (n : ℕ) :
    M ∣ (Zg n).re + s * (Zg n).im - ∏ k ∈ Finset.range n, (1 + (k : ℤ) * s) := by
  induction n with
  | zero =>
    simp [Zg]
  | succ n ih =>
    have hstep : Zg (n + 1) = Zg n * ⟨1, n⟩ := Finset.prod_range_succ _ _
    have hprod : ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * s) =
        (∏ k ∈ Finset.range n, (1 + (k : ℤ) * s)) * (1 + (n : ℤ) * s) :=
      Finset.prod_range_succ _ _
    have hre : (Zg (n + 1)).re = (Zg n).re - (n : ℤ) * (Zg n).im := by
      rw [hstep, Zsqrtd.re_mul]
      ring
    have him : (Zg (n + 1)).im = (Zg n).im + (n : ℤ) * (Zg n).re := by
      rw [hstep, Zsqrtd.im_mul]
      ring
    have hid : (Zg (n + 1)).re + s * (Zg (n + 1)).im -
          ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * s) =
        ((Zg n).re + s * (Zg n).im - ∏ k ∈ Finset.range n, (1 + (k : ℤ) * s)) *
          (1 + (n : ℤ) * s) -
        (n : ℤ) * (Zg n).im * (s ^ 2 + 1) := by
      rw [hre, him, hprod]
      ring
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_left ih _) (dvd_mul_of_dvd_right hs _)

/-- If `M ∣ f i - g i` for all `i ∈ S`, then `M ∣ ∏ f - ∏ g`. -/
lemma dvd_prod_sub_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (f g : ι → ℤ) (M : ℤ)
    (h : ∀ i ∈ S, M ∣ f i - g i) :
    M ∣ (∏ i ∈ S, f i) - (∏ i ∈ S, g i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa := h a (Finset.mem_insert_self a S)
    have hS := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hid : f a * ∏ x ∈ S, f x - g a * ∏ x ∈ S, g x =
        (f a - g a) * ∏ x ∈ S, f x + g a * ((∏ x ∈ S, f x) - (∏ x ∈ S, g x)) := by
      ring
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_left hfa _) (dvd_mul_of_dvd_right hS _)

/-- `n!` divides the product of any `n` consecutive integers. -/
lemma factorial_dvd_prod_range_add (m : ℤ) (n : ℕ) :
    (n.factorial : ℤ) ∣ ∏ k ∈ Finset.range n, (m + (k : ℤ)) := by
  have hnat : ∀ a : ℕ, (n.factorial : ℤ) ∣ ∏ k ∈ Finset.range n, ((a : ℤ) + (k : ℤ)) := by
    intro a
    have hdvd : n.factorial ∣ ∏ k ∈ Finset.range n, (a + k) := by
      rw [← Nat.ascFactorial_eq_prod_range]
      exact Nat.factorial_dvd_ascFactorial a n
    have := Int.natCast_dvd_natCast.2 hdvd
    simpa [Nat.cast_prod] using this
  by_cases hm0 : 0 ≤ m
  · lift m to ℕ using hm0
    exact hnat m
  · by_cases hmn : 0 < m + (n : ℤ)
    · let k0 : ℕ := (-m).toNat
      have hk0_cast : (k0 : ℤ) = -m := Int.toNat_of_nonneg (by omega)
      have hk0_lt : k0 < n := by omega
      have hzero : ∏ k ∈ Finset.range n, (m + (k : ℤ)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 hk0_lt) (by omega)
      rw [hzero]
      exact dvd_zero _
    · rcases n with _ | n
      · simp
      · let a : ℕ := (-m - (n : ℤ)).toNat
        have ha_cast : (a : ℤ) = -m - (n : ℤ) := Int.toNat_of_nonneg (by omega)
        have hrefl : ∏ k ∈ Finset.range (n + 1), (m + (k : ℤ)) =
            ∏ k ∈ Finset.range (n + 1), (m + ((n - k : ℕ) : ℤ)) := by
          simpa using (Finset.prod_range_reflect (fun k : ℕ => m + (k : ℤ)) (n + 1)).symm
        rw [hrefl]
        have hcongr : ∏ k ∈ Finset.range (n + 1), (m + ((n - k : ℕ) : ℤ)) =
            ∏ k ∈ Finset.range (n + 1), ((-1 : ℤ) * ((a : ℤ) + (k : ℤ))) := by
          refine Finset.prod_congr rfl (fun k hk => ?_)
          rw [Finset.mem_range] at hk
          have hsub : ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) := by omega
          omega
        rw [hcongr, Finset.prod_mul_distrib]
        exact dvd_mul_of_dvd_right (hnat a) _

/-- If `M ∣ s ^ 2 + 1` and `M ∣ n!`, then `M ∣ ∏_{k ≤ n} (1 + k s)`. -/
lemma dvd_prod_one_add_mul (M s : ℤ) (n : ℕ) (hs : M ∣ s ^ 2 + 1) (hfac : M ∣ (n.factorial : ℤ)) :
    M ∣ ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * s) := by
  have hpeel : ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * s) =
      ∏ k ∈ Finset.range n, (1 + ((k + 1 : ℕ) : ℤ) * s) := by
    rw [Finset.prod_range_succ']
    simp
  rw [hpeel]
  have hmul : (-s) ^ n * ∏ k ∈ Finset.range n, (1 + ((k + 1 : ℕ) : ℤ) * s) =
      ∏ k ∈ Finset.range n, ((-s) * (1 + ((k + 1 : ℕ) : ℤ) * s)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hsub : M ∣ (∏ k ∈ Finset.range n, ((-s) * (1 + ((k + 1 : ℕ) : ℤ) * s))) -
      (∏ k ∈ Finset.range n, ((1 - s) + (k : ℤ))) := by
    refine dvd_prod_sub_prod _ _ _ _ (fun k _ => ?_)
    have hid : (-s) * (1 + ((k + 1 : ℕ) : ℤ) * s) - ((1 - s) + (k : ℤ)) =
        -(((k + 1 : ℕ) : ℤ)) * (s ^ 2 + 1) := by
      push_cast
      ring
    rw [hid]
    exact dvd_mul_of_dvd_right hs _
  have hdvd_rhs : M ∣ ∏ k ∈ Finset.range n, ((1 - s) + (k : ℤ)) :=
    dvd_trans hfac (factorial_dvd_prod_range_add (1 - s) n)
  have hdvd_lhs : M ∣ (-s) ^ n * ∏ k ∈ Finset.range n, (1 + ((k + 1 : ℕ) : ℤ) * s) := by
    rw [hmul]
    have hadd := dvd_add hsub hdvd_rhs
    simpa using hadd
  rcases hs with ⟨q, hq⟩
  have hcop1 : IsCoprime (-s) M := ⟨s, q, by linear_combination -hq⟩
  have hcop : IsCoprime ((-s) ^ n) M := hcop1.pow_left
  exact hcop.symm.dvd_of_dvd_mul_left hdvd_lhs

end H1Proof

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 := by
  intro p hp hmod n
  cases hE : padicValNat p n.factorial with
  | zero =>
    simp
  | succ e =>
    set M : ℤ := (p : ℤ) ^ (e + 1)
    have hfac : M ∣ (n.factorial : ℤ) := by
      have hnat : p ^ (e + 1) ∣ n.factorial := by
        rw [← hE]
        exact pow_padicValNat_dvd
      simpa [M] using Int.natCast_dvd_natCast.2 hnat
    rcases H1Proof.exists_sq_add_one_dvd_pow p hp hmod e with ⟨r, hr⟩
    have hneg_r : M ∣ (-r) ^ 2 + 1 := by simpa [neg_sq] using hr
    have hpos : M ∣ (H1Proof.Zg (n + 1)).re + r * (H1Proof.Zg (n + 1)).im := by
      have h1 := H1Proof.dvd_re_add_mul_im_sub_prod M r hr (n + 1)
      have h2 := H1Proof.dvd_prod_one_add_mul M r n hr hfac
      simpa using dvd_add h1 h2
    have hneg : M ∣ (H1Proof.Zg (n + 1)).re + (-r) * (H1Proof.Zg (n + 1)).im := by
      have h1 := H1Proof.dvd_re_add_mul_im_sub_prod M (-r) hneg_r (n + 1)
      have h2 := H1Proof.dvd_prod_one_add_mul M (-r) n hneg_r hfac
      simpa using dvd_add h1 h2
    have h2r_im : M ∣ (2 * r) * (H1Proof.Zg (n + 1)).im := by
      have hsub := dvd_sub hpos hneg
      have hid : ((H1Proof.Zg (n + 1)).re + r * (H1Proof.Zg (n + 1)).im) -
          ((H1Proof.Zg (n + 1)).re + (-r) * (H1Proof.Zg (n + 1)).im) =
          (2 * r) * (H1Proof.Zg (n + 1)).im := by ring
      rwa [hid] at hsub
    have hcop2 : IsCoprime (2 : ℤ) M := by
      have h2p : IsCoprime (2 : ℤ) (p : ℤ) := ⟨-(p / 2 : ℤ), 1, by omega⟩
      exact h2p.pow_right
    have hcopr : IsCoprime r M := by
      rcases hr with ⟨q, hq⟩
      exact ⟨-r, q, by linear_combination -hq⟩
    have hcop : IsCoprime (2 * r) M := hcop2.mul_left hcopr
    rw [H1Proof.a_eq]
    exact hcop.symm.dvd_of_dvd_mul_left h2r_im
