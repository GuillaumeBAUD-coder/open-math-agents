import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

-- Step OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H1: hypothesis H1 of reduction OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1
-- Credit: @tatashbar
--
-- Proof. Let q = p ^ e with e = v_p(n!). Since p % 4 = 1, Hensel gives m in ZMod q with m * m = -1.
-- Map Z[i] to ZMod q by i -> m (and by i -> -m). Then 1 + k m = m (w + k) with w = -m, so the image
-- of P = prod (1 + k i) is m ^ (n+1) times a product of n + 1 consecutive integers, which is
-- divisible by (n+1)!, hence by p ^ e: both images vanish. Their difference is 2 m Im P, and 2 m
-- is a unit mod q, so q divides Im P = a n.

namespace OMA.StepA105751H1

open Polynomial

lemma a_eq (n : ℕ) : OeisA105751.a n =
    (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im := by
  unfold OeisA105751.a
  have h : (∏ k ∈ Finset.range (n + 1), (1 + (k : ℂ) * Complex.I)) =
      GaussianInt.toComplex (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [GaussianInt.toComplex_def']
    push_cast
    ring
  simp only
  rw [h, GaussianInt.toComplex_def₂]
  exact Int.floor_intCast _

lemma exists_sqrt_neg_one (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 1) (e : ℕ) :
    ∃ m : ZMod (p ^ e), m * m = -1 := by
  obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  set y0 : ℤ := (y.val : ℤ) with hy0
  have hyc : ((y0 : ℤ) : ZMod p) = y := by
    rw [hy0]; push_cast; exact ZMod.natCast_zmod_val y
  have hdvd : (p : ℤ) ∣ y0 * y0 + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hyc, ← hy]
    ring
  have hndvd : ¬ (p : ℤ) ∣ 2 * y0 := by
    intro h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    push_cast at h
    rw [hyc] at h
    have hy1 : y ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hy
      exact neg_ne_zero.mpr one_ne_zero hy
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h2
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_of_dvd (by norm_num) this
      have := hp.out.two_le
      omega
    exact (mul_ne_zero h2 hy1) h
  set F : Polynomial ℤ := X ^ 2 + 1 with hF
  have hFa : F.aeval (y0 : ℤ_[p]) = ((y0 * y0 + 1 : ℤ) : ℤ_[p]) := by
    simp [hF]; ring
  have hF'a : F.derivative.aeval (y0 : ℤ_[p]) = ((2 * y0 : ℤ) : ℤ_[p]) := by
    simp [hF, map_ofNat]
  have hn1 : ‖((y0 * y0 + 1 : ℤ) : ℤ_[p])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdvd
  have hn2 : ‖((2 * y0 : ℤ) : ℤ_[p])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp (fun h => hndvd ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)))
  have hnorm : ‖F.aeval (y0 : ℤ_[p])‖ < ‖F.derivative.aeval (y0 : ℤ_[p])‖ ^ 2 := by
    rw [hFa, hF'a, hn2]; simpa using hn1
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hzz : z * z = -1 := by
    simp [hF] at hz
    linear_combination hz
  refine ⟨PadicInt.toZModPow e z, ?_⟩
  rw [← map_mul, hzz, map_neg, map_one]

lemma prod_vanish (p : ℕ) (hp : p.Prime) (n : ℕ)
    (r : ZMod (p ^ padicValNat p n.factorial)) (hr : r * r = -1) :
    ∏ k ∈ Finset.range (n + 1), (1 + (k : ZMod (p ^ padicValNat p n.factorial)) * r) = 0 := by
  haveI : NeZero (p ^ padicValNat p n.factorial) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set w : ZMod (p ^ padicValNat p n.factorial) := -r with hw
  have hk : ∀ k : ℕ, 1 + (k : ZMod (p ^ padicValNat p n.factorial)) * r =
      r * (((w.val + k : ℕ)) : ZMod (p ^ padicValNat p n.factorial)) := by
    intro k
    push_cast
    rw [ZMod.natCast_zmod_val, hw]
    linear_combination hr
  rw [Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib, Finset.prod_const,
    ← Nat.cast_prod, ← Nat.ascFactorial_eq_prod_range]
  have hd : p ^ padicValNat p n.factorial ∣ w.val.ascFactorial (n + 1) :=
    pow_padicValNat_dvd.trans
      ((Nat.factorial_dvd_factorial (Nat.le_succ n)).trans (Nat.factorial_dvd_ascFactorial _ _))
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd, mul_zero]

lemma lift_prod {q : ℕ} (r : ZMod q) (hr : r * r = -1) (n : ℕ) :
    ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re : ZMod q) +
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im : ZMod q) * r =
      ∏ k ∈ Finset.range (n + 1), (1 + (k : ZMod q) * r) := by
  have hr' : r * r = ((-1 : ℤ) : ZMod q) := by rw [hr]; push_cast; rfl
  let f : GaussianInt →+* ZMod q := Zsqrtd.lift ⟨r, hr'⟩
  have hf : ∀ x : GaussianInt, f x = (x.re : ZMod q) + (x.im : ZMod q) * r := fun x => rfl
  rw [← hf, map_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [hf]
  push_cast
  ring

end OMA.StepA105751H1

open OMA.StepA105751H1

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 := by
  intro p hp h4 n
  haveI := Fact.mk hp
  obtain ⟨m, hm⟩ := exists_sqrt_neg_one p h4 (padicValNat p n.factorial)
  rw [a_eq]
  have e1 := lift_prod m hm n
  have e2 := lift_prod (-m) (by rw [neg_mul_neg, hm]) n
  rw [prod_vanish p hp n m hm] at e1
  rw [prod_vanish p hp n (-m) (by rw [neg_mul_neg, hm])] at e2
  set Y := (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im
  have h2m : (Y : ZMod (p ^ padicValNat p n.factorial)) * (2 * m) = 0 := by
    linear_combination e1 - e2
  have hmu : IsUnit m := isUnit_iff_exists_inv.mpr ⟨-m, by rw [mul_neg, hm, neg_neg]⟩
  have hodd : Odd (p ^ padicValNat p n.factorial) := (Nat.odd_iff.mpr (by omega)).pow
  have h2u : IsUnit (2 : ZMod (p ^ padicValNat p n.factorial)) := by
    have := (ZMod.isUnit_iff_coprime 2 (p ^ padicValNat p n.factorial)).mpr
      (Nat.coprime_two_left.mpr hodd)
    exact_mod_cast this
  have hY : (Y : ZMod (p ^ padicValNat p n.factorial)) = 0 :=
    ((h2u.mul hmu).mul_left_eq_zero).mp h2m
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd Y _).mp hY
  exact_mod_cast this
