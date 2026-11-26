import FormalConjectures.OEIS.«105751»

-- Problem: Imaginary part of $\prod_{k=0}^n (1 + k \cdot i)$, $i = \sqrt{-1}$
-- Upstream: formal-conjectures FormalConjectures/OEIS/105751.lean:72 (declaration OeisA105751.prime_divides_some_term)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

namespace OMA

/-- Over `ZMod p`, `∏_{k < p} (X - k) = X ^ p - X`. -/
lemma prod_X_sub_range (p : ℕ) [Fact p.Prime] :
    (∏ k ∈ Finset.range p, (X - C (k : ZMod p))) = (X ^ p - X : (ZMod p)[X]) := by
  have hp := (Fact.out : p.Prime)
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hmonic : (X ^ p - X : (ZMod p)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.one_lt)
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [hcard] at hroots
  have hnat := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.one_lt
  have key := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
    (by rw [hroots, hnat, Finset.card_val, Finset.card_univ, hcard])
  rw [hroots] at key
  rw [← key]
  change _ = ∏ a : ZMod p, (X - C a)
  refine Finset.prod_nbij' (fun k : ℕ => (k : ZMod p)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intro a _; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro k hk
    rw [Finset.mem_range] at hk
    exact ZMod.val_cast_of_lt hk
  · intro a _; exact ZMod.natCast_zmod_val a
  · intros; rfl

/-- Over `ℤ`, `∏_{k < p} (X - k) = X ^ p - X + p * R` for some integer polynomial `R`. -/
lemma prod_X_sub_range_int (p : ℕ) [Fact p.Prime] :
    ∃ R : ℤ[X], (∏ k ∈ Finset.range p, (X - C (k : ℤ))) = X ^ p - X + C (p : ℤ) * R := by
  have hmap : ((∏ k ∈ Finset.range p, (X - C (k : ℤ))) - (X ^ p - X)).map
      (Int.castRingHom (ZMod p)) = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_X, Polynomial.map_pow,
      map_natCast, Polynomial.map_natCast]
    have h := prod_X_sub_range p
    simp only [map_natCast] at h
    rw [h, sub_self]
  obtain ⟨R, hR⟩ : C (p : ℤ) ∣ (∏ k ∈ Finset.range p, (X - C (k : ℤ))) - (X ^ p - X) := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have := congrArg (fun q => q.coeff i) hmap
    simp only [coeff_map, coeff_zero, eq_intCast] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 this
  exact ⟨R, by rw [← hR]; ring⟩

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

lemma Zg_ne_zero (n : ℕ) : Zg n ≠ 0 := by
  unfold Zg
  rw [Finset.prod_ne_zero_iff]
  intro k _ h
  have := congrArg Zsqrtd.re h
  simp at this

/-- For an odd prime `p`, `p` divides the imaginary part of `∏_{k < p} (1 + k i)`. -/
lemma dvd_im (p : ℕ) [Fact p.Prime] (hodd : Odd p) : (p : ℤ) ∣ (Zg p).im := by
  obtain ⟨R, hR⟩ := prod_X_sub_range_int p
  obtain ⟨m, hm⟩ := hodd
  set I : GaussianInt := ⟨0, 1⟩ with hIdef
  have hI : I ^ 2 = -1 := by ext <;> simp [hIdef, pow_two]
  have hfac : ∀ k : ℕ, (⟨1, k⟩ : GaussianInt) = I * ((k : GaussianInt) - I) := by
    intro k; ext <;> simp [hIdef]
  have hZ : Zg p = I ^ p * ∏ k ∈ Finset.range p, ((k : GaussianInt) - I) := by
    unfold Zg
    rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
  have hneg : ∏ k ∈ Finset.range p, ((k : GaussianInt) - I) =
      (-1) ^ p * ∏ k ∈ Finset.range p, (I - (k : GaussianInt)) := by
    simp only [show ∀ k : ℕ, (k : GaussianInt) - I = (-1) * (I - k) from fun k => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hev := congrArg (fun q : ℤ[X] => q.eval₂ (Int.castRingHom GaussianInt) I) hR
  simp only [Polynomial.eval₂_finsetProd, eval₂_sub, eval₂_X, eval₂_add, eval₂_mul,
    eval₂_pow, eq_intCast, Int.cast_natCast, Polynomial.eval₂_natCast] at hev
  set Rv := R.eval₂ (Int.castRingHom GaussianInt) I
  set uz : ℤ := (-1) ^ m with huz
  set u : GaussianInt := (uz : GaussianInt) with hu
  have hu2 : u ^ 2 = 1 := by
    have : uz ^ 2 = 1 := by rw [huz, ← pow_mul, mul_comm, pow_mul]; simp
    rw [hu, ← Int.cast_pow, this, Int.cast_one]
  have hIp : I ^ p = u * I := by
    rw [hm, pow_succ, pow_mul, hI, hu, huz]; push_cast; ring
  have hp1 : (-1 : GaussianInt) ^ p = -1 := by rw [hm]; simp [pow_succ, pow_mul]
  have hZ' : Zg p = (((1 : ℤ) - uz : ℤ) : GaussianInt) + (p : GaussianInt) * (-(u * I * Rv)) := by
    rw [hZ, hneg, hev, hIp, hp1]
    push_cast
    rw [← hu]
    linear_combination (u - u ^ 2) * hI + hu2
  have hdvd : ((p : ℤ) : GaussianInt) ∣ Zg p - (((1 : ℤ) - uz : ℤ) : GaussianInt) :=
    ⟨-(u * I * Rv), by rw [hZ']; push_cast; ring⟩
  rw [Zsqrtd.intCast_dvd] at hdvd
  have := hdvd.2
  simpa [Zsqrtd.im_intCast] using this

end OMA

theorem OMA.solution : type_of% @OeisA105751.prime_divides_some_term := by
  intro p hp
  have := Fact.mk hp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact ⟨4, by rw [OeisA105751.a_4]; norm_num, by rw [OeisA105751.a_4]; norm_num⟩
  have h1 := OMA.dvd_im p hodd
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  by_cases him : (OMA.Zg p).im = 0
  · refine ⟨p, ?_, ?_⟩
    · rw [OMA.a_eq]
      have hstep : OMA.Zg (p + 1) = OMA.Zg p * ⟨1, p⟩ := Finset.prod_range_succ _ _
      rw [hstep, Zsqrtd.im_mul, him]
      have hre : (OMA.Zg p).re ≠ 0 := by
        intro h
        exact OMA.Zg_ne_zero p (Zsqrtd.ext h him)
      simp [hre, hp.ne_zero]
    · rw [OMA.a_eq]
      have hstep : OMA.Zg (p + 1) = OMA.Zg p * ⟨1, p⟩ := Finset.prod_range_succ _ _
      rw [hstep, Zsqrtd.im_mul, him]
      simp
  · refine ⟨p - 1, ?_, ?_⟩
    · rw [OMA.a_eq, hp1]; exact him
    · rw [OMA.a_eq, hp1]; exact h1
