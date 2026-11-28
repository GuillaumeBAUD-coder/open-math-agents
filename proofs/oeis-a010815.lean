import OMAStatements.S_oeis_a010815

open OMA.S_oeis_a010815

/-!
Part 1: 2D Lattice Theta Functions and AGM Identities
-/

private noncomputable def qVal : ℝ := Real.exp (-Real.pi)

private noncomputable def th3 (c : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-c * (n : ℝ) ^ 2)

private noncomputable def th4 (c : ℝ) : ℝ :=
  ∑' n : ℤ, (-1 : ℝ) ^ n.natAbs * Real.exp (-c * (n : ℝ) ^ 2)

private noncomputable def th2 (c : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-c * ((n : ℝ) + 1 / 2) ^ 2)

private def evenOddIntEquiv : ℤ ⊕ ℤ ≃ ℤ where
  toFun := Sum.elim (fun n => 2 * n) (fun n => 2 * n + 1)
  invFun m := if m % 2 = 0 then Sum.inl (m / 2) else Sum.inr ((m - 1) / 2)
  left_inv x := by
    rcases x with n | n
    · dsimp only [Sum.elim_inl]
      split_ifs
      · congr 1; omega
      · omega
    · dsimp only [Sum.elim_inr]
      split_ifs
      · omega
      · congr 1; omega
  right_inv m := by
    dsimp only
    split_ifs <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> omega

private def parityPairEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun p => (p.1 + p.2, p.1 - p.2)) (fun p => (p.1 + p.2 + 1, p.1 - p.2))
  invFun p :=
    if (p.1 + p.2) % 2 = 0 then
      Sum.inl ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
    else
      Sum.inr ((p.1 + p.2 - 1) / 2, (p.1 - p.2 - 1) / 2)
  left_inv x := by
    rcases x with ⟨u, v⟩ | ⟨u, v⟩
    · dsimp only [Sum.elim_inl]
      split_ifs
      · congr 1; ext <;> dsimp only <;> omega
      · omega
    · dsimp only [Sum.elim_inr]
      split_ifs
      · omega
      · congr 1; ext <;> dsimp only <;> omega
  right_inv p := by
    rcases p with ⟨a, b⟩
    dsimp only
    split_ifs <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> ext <;> dsimp only <;> omega

private def intSplitZeroEquiv : (Unit ⊕ ℕ) ⊕ ℕ ≃ ℤ where
  toFun
    | Sum.inl (Sum.inl ()) => 0
    | Sum.inl (Sum.inr n) => (n : ℤ) + 1
    | Sum.inr n => -((n : ℤ) + 1)
  invFun m :=
    if m = 0 then Sum.inl (Sum.inl ())
    else if 0 < m then Sum.inl (Sum.inr (m - 1).toNat)
    else Sum.inr (-m - 1).toNat
  left_inv x := by
    rcases x with (⟨⟩ | n) | n
    · simp
    · dsimp only
      split_ifs
      · omega
      · congr 2; omega
      · omega
    · dsimp only
      split_ifs
      · omega
      · omega
      · congr 1; omega
  right_inv m := by
    dsimp only
    split_ifs <;> dsimp only <;> omega

private lemma tsum_int_split_zero {f : ℤ → ℝ} (hf : Summable f) :
    (∑' m : ℤ, f m) = f 0 + ∑' n : ℕ, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))) := by
  have hsum := (intSplitZeroEquiv.summable_iff (f := f)).mpr hf
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  have h1a := h1.comp_injective Sum.inl_injective
  have h1b := h1.comp_injective Sum.inr_injective
  rw [← intSplitZeroEquiv.tsum_eq]
  change (∑' x : (Unit ⊕ ℕ) ⊕ ℕ, (f ∘ intSplitZeroEquiv) x) = _
  rw [h1.tsum_sum h2]
  change (∑' x : Unit ⊕ ℕ, ((f ∘ intSplitZeroEquiv) ∘ Sum.inl) x) + _ = _
  rw [h1a.tsum_sum h1b]
  have h0 : (∑' u : Unit, ((f ∘ intSplitZeroEquiv) ∘ Sum.inl) (Sum.inl u)) = f 0 := by
    rw [tsum_fintype, Fintype.sum_unique]
    rfl
  rw [h0, add_assoc]
  congr 1
  exact (h1b.tsum_add h2).symm

private lemma even_natAbs_iff (a : ℤ) : Even a.natAbs ↔ Even a := by
  rw [Nat.even_iff, Int.even_iff]
  omega

private lemma neg_one_pow_natAbs_mul (a b : ℤ) :
    (-1 : ℝ) ^ a.natAbs * (-1 : ℝ) ^ b.natAbs = (-1 : ℝ) ^ (a + b).natAbs := by
  rw [← pow_add]
  have hpar : Even (a.natAbs + b.natAbs) ↔ Even (a + b).natAbs := by
    rw [Nat.even_add, even_natAbs_iff, even_natAbs_iff, even_natAbs_iff, Int.even_add]
  rcases Nat.even_or_odd (a.natAbs + b.natAbs) with h | h
  · rw [h.neg_one_pow, (hpar.mp h).neg_one_pow]
  · have h2 : Odd (a + b).natAbs := by
      rcases Nat.even_or_odd (a + b).natAbs with he | ho
      · exact absurd (hpar.mpr he) (Nat.not_even_iff_odd.mpr h)
      · exact ho
    rw [h.neg_one_pow, h2.neg_one_pow]

private lemma neg_one_pow_natAbs_neg (a : ℤ) :
    (-1 : ℝ) ^ (-a).natAbs = (-1 : ℝ) ^ a.natAbs := by
  rw [Int.natAbs_neg]

private lemma neg_one_pow_natAbs_two_mul (u : ℤ) :
    (-1 : ℝ) ^ (2 * u).natAbs = 1 := by
  have he : Even (2 * u).natAbs := by
    rw [even_natAbs_iff]
    exact even_two_mul u
  exact he.neg_one_pow

private lemma neg_one_pow_natAbs_two_mul_add_one (u : ℤ) :
    (-1 : ℝ) ^ (2 * u + 1).natAbs = -1 := by
  have ho : Odd (2 * u + 1).natAbs := by
    rcases Nat.even_or_odd (2 * u + 1).natAbs with he | ho
    · rw [even_natAbs_iff] at he
      rcases he with ⟨k, hk⟩
      omega
    · exact ho
  exact ho.neg_one_pow

private lemma summable_exp_neg_mul_int_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnat : Summable fun m : ℕ => Real.exp (-c * (m : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
      (summable_geometric_of_lt_one hr0 hr1)
    have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      cases m with
      | zero => norm_num
      | succ m =>
        have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_cast; omega
        nlinarith
    calc
      Real.exp (-c * (m : ℝ) ^ 2) ≤ Real.exp (-c * (m : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp ((m : ℕ) * (-c)) := by congr 1; ring
      _ = (Real.exp (-c)) ^ m := Real.exp_nat_mul (-c) m
  have hneg : Summable fun m : ℕ => Real.exp (-c * ((-m : ℤ) : ℝ) ^ 2) := by
    simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hnat
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨by simpa using hnat, hneg⟩

private lemma summable_th3 {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2) :=
  summable_exp_neg_mul_int_sq hc

private lemma summable_th4 {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => (-1 : ℝ) ^ n.natAbs * Real.exp (-c * (n : ℝ) ^ 2) := by
  refine ((summable_th3 hc).norm.congr fun n => ?_).of_norm
  simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul]

private lemma summable_th2 {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * ((n : ℝ) + 1 / 2) ^ 2) := by
  have h := summable_exp_neg_mul_int_sq (by linarith : (0 : ℝ) < c / 4)
  have hsum := (evenOddIntEquiv.summable_iff).mpr h
  refine (hsum.comp_injective Sum.inr_injective).congr fun n => ?_
  simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inr, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  congr 1
  ring

private lemma summable_prod_of_norm {f g : ℤ → ℝ}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun y => ‖g y‖) :
    Summable fun p : ℤ × ℤ => f p.1 * g p.2 := by
  have hnorm : Summable fun p : ℤ × ℤ => ‖f p.1 * g p.2‖ := by
    have hprod : Summable fun p : ℤ × ℤ => ‖f p.1‖ * ‖g p.2‖ := by
      refine (summable_prod_of_nonneg fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _)).mpr ?_
      refine ⟨fun x => hg.mul_left ‖f x‖, ?_⟩
      simp only [tsum_mul_left]
      exact hf.mul_right (∑' y, ‖g y‖)
    refine hprod.congr fun p => ?_
    rw [norm_mul]
  exact hnorm.of_norm

private lemma tsum_mul_tsum_eq_tsum_prod {f g : ℤ → ℝ}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun y => ‖g y‖) :
    (∑' x : ℤ, f x) * (∑' y : ℤ, g y) = ∑' p : ℤ × ℤ, f p.1 * g p.2 := by
  have hp := summable_prod_of_norm hf hg
  rw [hp.tsum_prod]
  simp only [tsum_mul_left, tsum_mul_right]

private lemma th3_sq_eq {c : ℝ} (hc : 0 < c) :
    th3 c ^ 2 = th3 (2 * c) ^ 2 + th2 (2 * c) ^ 2 := by
  have h3 := summable_th3 hc
  have hprod : Summable fun p : ℤ × ℤ =>
      Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    have hp := summable_prod_of_norm h3.norm h3.norm
    refine hp.congr fun p => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have hL : th3 c ^ 2 = ∑' p : ℤ × ℤ, Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [sq, th3, tsum_mul_tsum_eq_tsum_prod h3.norm h3.norm]
    refine tsum_congr fun p => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have hsum := (parityPairEquiv.summable_iff (f := fun p : ℤ × ℤ =>
    Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)))).mpr hprod
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [hL, ← parityPairEquiv.tsum_eq]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ),
    ((fun p : ℤ × ℤ => Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) ∘ parityPairEquiv) x) = _
  rw [h1.tsum_sum h2]
  have h2c : 0 < 2 * c := by linarith
  have hA := summable_th3 h2c
  have hB := summable_th2 h2c
  congr 1
  · rw [sq, th3, tsum_mul_tsum_eq_tsum_prod hA.norm hA.norm]
    refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl,
      Int.cast_add, Int.cast_sub, ← Real.exp_add]
    congr 1
    ring
  · rw [sq, th2, tsum_mul_tsum_eq_tsum_prod hB.norm hB.norm]
    refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr,
      Int.cast_add, Int.cast_sub, Int.cast_one, ← Real.exp_add]
    congr 1
    ring

private lemma th4_sq_eq {c : ℝ} (hc : 0 < c) :
    th4 c ^ 2 = th3 (2 * c) ^ 2 - th2 (2 * c) ^ 2 := by
  have h4n : Summable fun n : ℤ => ‖(-1 : ℝ) ^ n.natAbs * Real.exp (-c * (n : ℝ) ^ 2)‖ := by
    refine (summable_th3 hc).congr fun n => ?_
    simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul, abs_of_pos (Real.exp_pos _)]
  have hp := summable_prod_of_norm h4n h4n
  have hprod : Summable fun p : ℤ × ℤ =>
      (-1 : ℝ) ^ (p.1 + p.2).natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    refine hp.congr fun p => ?_
    calc
      (-1 : ℝ) ^ p.1.natAbs * Real.exp (-c * (p.1 : ℝ) ^ 2) *
          ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2))
          = ((-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ p.2.natAbs) *
              (Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by ring
      _ = (-1 : ℝ) ^ (p.1 + p.2).natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
            rw [neg_one_pow_natAbs_mul, ← Real.exp_add]
            congr 2
            ring
  have hL : th4 c ^ 2 = ∑' p : ℤ × ℤ,
      (-1 : ℝ) ^ (p.1 + p.2).natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [sq, th4, tsum_mul_tsum_eq_tsum_prod h4n h4n]
    refine tsum_congr fun p => ?_
    calc
      (-1 : ℝ) ^ p.1.natAbs * Real.exp (-c * (p.1 : ℝ) ^ 2) *
          ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2))
          = ((-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ p.2.natAbs) *
              (Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by ring
      _ = (-1 : ℝ) ^ (p.1 + p.2).natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
            rw [neg_one_pow_natAbs_mul, ← Real.exp_add]
            congr 2
            ring
  have hsum := (parityPairEquiv.summable_iff (f := fun p : ℤ × ℤ =>
    (-1 : ℝ) ^ (p.1 + p.2).natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)))).mpr hprod
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [hL, ← parityPairEquiv.tsum_eq]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ),
    ((fun p : ℤ × ℤ =>
      (-1 : ℝ) ^ (p.1 + p.2).natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) ∘
      parityPairEquiv) x) = _
  rw [h1.tsum_sum h2, sub_eq_add_neg]
  have h2c : 0 < 2 * c := by linarith
  have hA := summable_th3 h2c
  have hB := summable_th2 h2c
  congr 1
  · rw [sq, th3, tsum_mul_tsum_eq_tsum_prod hA.norm hA.norm]
    refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl,
      Int.cast_add, Int.cast_sub, ← Real.exp_add]
    have hadd : p.1 + p.2 + (p.1 - p.2) = 2 * p.1 := by ring
    rw [hadd, neg_one_pow_natAbs_two_mul, one_mul]
    congr 1
    ring
  · rw [sq, th2, tsum_mul_tsum_eq_tsum_prod hB.norm hB.norm, ← tsum_neg]
    refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr,
      Int.cast_add, Int.cast_sub, Int.cast_one, ← Real.exp_add]
    have hadd : p.1 + p.2 + 1 + (p.1 - p.2) = 2 * p.1 + 1 := by ring
    rw [hadd, neg_one_pow_natAbs_two_mul_add_one, neg_one_mul]
    congr 2
    ring

private lemma th3_mul_th4_eq {c : ℝ} (hc : 0 < c) :
    th3 c * th4 c = th4 (2 * c) ^ 2 := by
  have h3 := summable_th3 hc
  have h4n : Summable fun n : ℤ => ‖(-1 : ℝ) ^ n.natAbs * Real.exp (-c * (n : ℝ) ^ 2)‖ := by
    refine h3.congr fun n => ?_
    simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul, abs_of_pos (Real.exp_pos _)]
  have hp := summable_prod_of_norm h3.norm h4n
  have hprod : Summable fun p : ℤ × ℤ =>
      (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    refine hp.congr fun p => ?_
    calc
      Real.exp (-c * (p.1 : ℝ) ^ 2) *
          ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2))
          = (-1 : ℝ) ^ p.2.natAbs *
              (Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by ring
      _ = (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
            rw [← Real.exp_add]
            congr 2
            ring
  have hL : th3 c * th4 c = ∑' p : ℤ × ℤ,
      (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [th3, th4, tsum_mul_tsum_eq_tsum_prod h3.norm h4n]
    refine tsum_congr fun p => ?_
    calc
      Real.exp (-c * (p.1 : ℝ) ^ 2) *
          ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2))
          = (-1 : ℝ) ^ p.2.natAbs *
              (Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by ring
      _ = (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
            rw [← Real.exp_add]
            congr 2
            ring
  have hsum := (parityPairEquiv.summable_iff (f := fun p : ℤ × ℤ =>
    (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)))).mpr hprod
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [hL, ← parityPairEquiv.tsum_eq]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ),
    ((fun p : ℤ × ℤ =>
      (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) ∘
      parityPairEquiv) x) = _
  rw [h1.tsum_sum h2]
  have h2c : 0 < 2 * c := by linarith
  have hA4n : Summable fun n : ℤ => ‖(-1 : ℝ) ^ n.natAbs * Real.exp (-(2 * c) * (n : ℝ) ^ 2)‖ := by
    refine (summable_th3 h2c).congr fun n => ?_
    simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul, abs_of_pos (Real.exp_pos _)]
  have hpart1 : (∑' p : ℤ × ℤ,
      ((fun p : ℤ × ℤ => (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) ∘
        parityPairEquiv) (Sum.inl p)) = th4 (2 * c) ^ 2 := by
    rw [sq, th4, tsum_mul_tsum_eq_tsum_prod hA4n hA4n]
    refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl,
      Int.cast_add, Int.cast_sub]
    calc
      (-1 : ℝ) ^ (p.1 - p.2).natAbs * Real.exp (-c * ((p.1 + p.2 : ℝ) ^ 2 + (p.1 - p.2 : ℝ) ^ 2))
          = ((-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ (-p.2).natAbs) *
              Real.exp (-(2 * c) * (p.1 : ℝ) ^ 2 + -(2 * c) * (p.2 : ℝ) ^ 2) := by
            rw [neg_one_pow_natAbs_mul, sub_eq_add_neg]
            congr 2
            ring
      _ = (-1 : ℝ) ^ p.1.natAbs * Real.exp (-(2 * c) * (p.1 : ℝ) ^ 2) *
            ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-(2 * c) * (p.2 : ℝ) ^ 2)) := by
            rw [neg_one_pow_natAbs_neg, Real.exp_add]
            ring
  have hpart2 : (∑' p : ℤ × ℤ,
      ((fun p : ℤ × ℤ => (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) ∘
        parityPairEquiv) (Sum.inr p)) = 0 := by
    let inv : ℤ × ℤ ≃ ℤ × ℤ :=
      { toFun := fun p => (p.1, -1 - p.2)
        invFun := fun p => (p.1, -1 - p.2)
        left_inv := fun ⟨_, _⟩ => Prod.ext rfl (by dsimp only; omega)
        right_inv := fun ⟨_, _⟩ => Prod.ext rfl (by dsimp only; omega) }
    set S := ∑' p : ℤ × ℤ,
      ((fun p : ℤ × ℤ => (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) ∘
        parityPairEquiv) (Sum.inr p)
    have hneg : S = -S := by
      calc
        S = ∑' p : ℤ × ℤ,
              ((fun p : ℤ × ℤ =>
                (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) ∘
                parityPairEquiv) (Sum.inr (inv p)) := (inv.tsum_eq _).symm
        _ = ∑' p : ℤ × ℤ,
              -(((fun p : ℤ × ℤ =>
                (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) ∘
                parityPairEquiv) (Sum.inr p)) := by
              refine tsum_congr fun ⟨u, v⟩ => ?_
              simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr, inv,
                Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_one]
              have hsign : (-1 : ℝ) ^ (u - (-1 - v)).natAbs = -((-1 : ℝ) ^ (u - v).natAbs) := by
                have heq : u - (-1 - v) = (u - v) + (2 * v + 1) := by ring
                rw [heq, ← neg_one_pow_natAbs_mul, neg_one_pow_natAbs_two_mul_add_one]
                ring
              rw [hsign]
              have hexp :
                  -c * ((u + (-1 - v) + 1 : ℝ) ^ 2 + (u - (-1 - v) : ℝ) ^ 2) =
                    -c * ((u + v + 1 : ℝ) ^ 2 + (u - v : ℝ) ^ 2) := by ring
              rw [hexp]
              ring
        _ = -S := tsum_neg
    linarith
  rw [hpart1, hpart2, add_zero]

private lemma th2_sq_eq {c : ℝ} (hc : 0 < c) :
    th2 c ^ 2 = 2 * th3 (2 * c) * th2 (2 * c) := by
  have h2 := summable_th2 hc
  have hp := summable_prod_of_norm h2.norm h2.norm
  have hprod : Summable fun p : ℤ × ℤ =>
      Real.exp (-c * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
    refine hp.congr fun p => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have hL : th2 c ^ 2 = ∑' p : ℤ × ℤ,
      Real.exp (-c * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
    rw [sq, th2, tsum_mul_tsum_eq_tsum_prod h2.norm h2.norm]
    refine tsum_congr fun p => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have hsum := (parityPairEquiv.summable_iff (f := fun p : ℤ × ℤ =>
    Real.exp (-c * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)))).mpr hprod
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2' := hsum.comp_injective Sum.inr_injective
  rw [hL, ← parityPairEquiv.tsum_eq]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ),
    ((fun p : ℤ × ℤ =>
      Real.exp (-c * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2))) ∘
      parityPairEquiv) x) = _
  rw [h1.tsum_sum h2']
  have h2c : 0 < 2 * c := by linarith
  have hA := summable_th3 h2c
  have hB := summable_th2 h2c
  have hpart1 : (∑' p : ℤ × ℤ,
      ((fun p : ℤ × ℤ =>
        Real.exp (-c * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2))) ∘
        parityPairEquiv) (Sum.inl p)) = th2 (2 * c) * th3 (2 * c) := by
    rw [th2, th3, tsum_mul_tsum_eq_tsum_prod hB.norm hA.norm]
    refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl,
      Int.cast_add, Int.cast_sub, ← Real.exp_add]
    congr 1
    ring
  have hpart2 : (∑' p : ℤ × ℤ,
      ((fun p : ℤ × ℤ =>
        Real.exp (-c * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2))) ∘
        parityPairEquiv) (Sum.inr p)) = th3 (2 * c) * th2 (2 * c) := by
    let shift : ℤ × ℤ ≃ ℤ × ℤ :=
      { toFun := fun p => (p.1 + 1, p.2)
        invFun := fun p => (p.1 - 1, p.2)
        left_inv := fun ⟨_, _⟩ => Prod.ext (by dsimp only; omega) rfl
        right_inv := fun ⟨_, _⟩ => Prod.ext (by dsimp only; omega) rfl }
    rw [th3, th2, tsum_mul_tsum_eq_tsum_prod hA.norm hB.norm]
    conv_rhs => rw [← shift.tsum_eq]
    refine tsum_congr fun ⟨u, v⟩ => ?_
    dsimp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr, shift]
    rw [← Real.exp_add]
    push_cast
    congr 1
    ring
  rw [hpart1, hpart2]
  ring

private lemma th3_agm {c : ℝ} (hc : 0 < c) :
    (th3 c ^ 2 + th4 c ^ 2) / 2 = th3 (2 * c) ^ 2 := by
  rw [th3_sq_eq hc, th4_sq_eq hc]
  ring

private lemma th3_split_zero {c : ℝ} (hc : 0 < c) :
    th3 c = 1 + 2 * ∑' n : ℕ, Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [th3, tsum_int_split_zero (summable_th3 hc), ← tsum_mul_left]
  have h0 : Real.exp (-c * ((0 : ℤ) : ℝ) ^ 2) = 1 := by simp
  rw [h0]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_sq,
    Nat.cast_add, Nat.cast_one]
  ring

private lemma th4_split_zero {c : ℝ} (hc : 0 < c) :
    th4 c = 1 + 2 * ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [th4, tsum_int_split_zero (summable_th4 hc), ← tsum_mul_left]
  have h0 : (-1 : ℝ) ^ (0 : ℤ).natAbs * Real.exp (-c * ((0 : ℤ) : ℝ) ^ 2) = 1 := by simp
  rw [h0]
  congr 1
  refine tsum_congr fun n => ?_
  have hna1 : ((n : ℤ) + 1).natAbs = n + 1 := by omega
  have hna2 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
  rw [hna1, hna2]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_sq,
    Nat.cast_add, Nat.cast_one]
  ring

private lemma summable_exp_neg_succ_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hsum := (intSplitZeroEquiv.summable_iff (f := fun m : ℤ =>
    Real.exp (-c * (m : ℝ) ^ 2))).mpr (summable_th3 hc)
  refine ((hsum.comp_injective Sum.inl_injective).comp_injective Sum.inr_injective).congr fun n => ?_
  simp [intSplitZeroEquiv]

private lemma tsum_exp_neg_succ_sq_le {c : ℝ} (hc : 0 < c) :
    ∑' n : ℕ, Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) ≤
      Real.exp (-c) / (1 - Real.exp (-c)) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable fun n : ℕ => Real.exp (-c) * (Real.exp (-c)) ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle : ∑' n : ℕ, Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) ≤
      ∑' n : ℕ, Real.exp (-c) * (Real.exp (-c)) ^ n := by
    refine (summable_exp_neg_succ_sq hc).tsum_le_tsum (fun n => ?_) hgeom
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
    have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    calc
      Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) ≤ Real.exp (-c * ((n + 1 : ℕ) : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * (-c)) := by congr 1; ring
      _ = (Real.exp (-c)) ^ (n + 1) := Real.exp_nat_mul (-c) (n + 1)
      _ = Real.exp (-c) * (Real.exp (-c)) ^ n := by rw [pow_succ']
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle
  simpa only [div_eq_mul_inv] using hle

private lemma th3_sub_one_abs_le {c : ℝ} (hc : 0 < c) :
    |th3 c - 1| ≤ 2 * (Real.exp (-c) / (1 - Real.exp (-c))) := by
  rw [th3_split_zero hc, add_sub_cancel_left]
  have hnn : 0 ≤ ∑' n : ℕ, Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  rw [abs_of_nonneg (by linarith)]
  linarith [tsum_exp_neg_succ_sq_le hc]

private lemma th4_sub_one_abs_le {c : ℝ} (hc : 0 < c) :
    |th4 c - 1| ≤ 2 * (Real.exp (-c) / (1 - Real.exp (-c))) := by
  rw [th4_split_zero hc, add_sub_cancel_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsum : Summable fun n : ℕ =>
      ‖(-1 : ℝ) ^ (n + 1) * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)‖ := by
    refine (summable_exp_neg_succ_sq hc).congr fun n => ?_
    simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul, abs_of_pos (Real.exp_pos _)]
  have hle : |∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)| ≤
      ∑' n : ℕ, Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      |∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)|
          = ‖∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)‖ := rfl
      _ ≤ ∑' n : ℕ, ‖(-1 : ℝ) ^ (n + 1) * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)‖ :=
            norm_tsum_le_tsum_norm hsum
      _ = ∑' n : ℕ, Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) := by
            refine tsum_congr fun n => ?_
            simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul,
              abs_of_pos (Real.exp_pos _)]
  linarith [tsum_exp_neg_succ_sq_le hc]

private lemma exp_neg_two_le_quarter : Real.exp (-2 : ℝ) ≤ 1 / 4 := by
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [h2]
    nlinarith
  rw [Real.exp_neg]
  have hpos : 0 < Real.exp 2 := Real.exp_pos 2
  rw [inv_eq_one_div, div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 4)]
  linarith

private lemma th4_pos_of_two_le {c : ℝ} (hc : 2 ≤ c) : 0 < th4 c := by
  have hc0 : 0 < c := by linarith
  have hr : Real.exp (-c) ≤ 1 / 4 :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_two_le_quarter
  have h1r : 3 / 4 ≤ 1 - Real.exp (-c) := by linarith
  have hdiv : Real.exp (-c) / (1 - Real.exp (-c)) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-c))]
    linarith
  have habs := th4_sub_one_abs_le hc0
  rw [abs_le] at habs
  linarith

private lemma th3_pos {c : ℝ} (hc : 0 < c) : 0 < th3 c := by
  have hge : Real.exp (-c * ((0 : ℤ) : ℝ) ^ 2) ≤ th3 c :=
    (summable_th3 hc).le_tsum 0 fun _ _ => (Real.exp_pos _).le
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero] at hge
  linarith

private lemma th2_pos {c : ℝ} (hc : 0 < c) : 0 < th2 c := by
  have hge : Real.exp (-c * (((0 : ℤ) : ℝ) + 1 / 2) ^ 2) ≤ th2 c :=
    (summable_th2 hc).le_tsum 0 fun _ _ => (Real.exp_pos _).le
  linarith [Real.exp_pos (-c * (((0 : ℤ) : ℝ) + 1 / 2) ^ 2)]

private lemma th4_le_th3 {c : ℝ} (hc : 0 < c) : th4 c ≤ th3 c := by
  refine (summable_th4 hc).tsum_le_tsum (fun n => ?_) (summable_th3 hc)
  have hle : (-1 : ℝ) ^ n.natAbs ≤ 1 := by
    rcases Nat.even_or_odd n.natAbs with h | h
    · rw [h.neg_one_pow]
    · rw [h.neg_one_pow]; norm_num
  nlinarith [Real.exp_pos (-c * (n : ℝ) ^ 2)]

private lemma th3_half_pi_eq_add :
    th3 (Real.pi / 2) = th3 (2 * Real.pi) + th2 (2 * Real.pi) := by
  have hhc : 0 < Real.pi / 2 := by positivity
  have hsum := (evenOddIntEquiv.summable_iff (f := fun m : ℤ =>
    Real.exp (-(Real.pi / 2) * (m : ℝ) ^ 2))).mpr (summable_th3 hhc)
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [th3, ← evenOddIntEquiv.tsum_eq]
  change (∑' x : ℤ ⊕ ℤ,
    ((fun m : ℤ => Real.exp (-(Real.pi / 2) * (m : ℝ) ^ 2)) ∘ evenOddIntEquiv) x) = _
  rw [h1.tsum_sum h2, th3, th2]
  congr 1
  · refine tsum_congr fun n => ?_
    simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inl,
      Int.cast_mul, Int.cast_ofNat]
    congr 1
    ring
  · refine tsum_congr fun n => ?_
    simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inr,
      Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    congr 1
    ring

private lemma th2_two_pi_eq :
    th2 (2 * Real.pi) = (Real.sqrt 2 - 1) * th3 (2 * Real.pi) := by
  have hpois := Real.tsum_exp_neg_mul_int_sq (by norm_num : (0 : ℝ) < 2)
  have hL : (∑' n : ℤ, Real.exp (-Real.pi * 2 * (n : ℝ) ^ 2)) = th3 (2 * Real.pi) := by
    rw [th3]
    refine tsum_congr fun n => ?_
    congr 1
    ring
  have hR : (∑' n : ℤ, Real.exp (-Real.pi / 2 * (n : ℝ) ^ 2)) = th3 (Real.pi / 2) := by
    rw [th3]
    refine tsum_congr fun n => ?_
    congr 1
    ring
  rw [hL, hR, ← Real.sqrt_eq_rpow 2, th3_half_pi_eq_add] at hpois
  have hsq : Real.sqrt 2 ≠ 0 := by positivity
  have hmul : Real.sqrt 2 * th3 (2 * Real.pi) = th3 (2 * Real.pi) + th2 (2 * Real.pi) := by
    calc
      Real.sqrt 2 * th3 (2 * Real.pi)
          = Real.sqrt 2 * (1 / Real.sqrt 2 * (th3 (2 * Real.pi) + th2 (2 * Real.pi))) := by
              rw [← hpois]
      _ = (Real.sqrt 2 * (1 / Real.sqrt 2)) * (th3 (2 * Real.pi) + th2 (2 * Real.pi)) := by ring
      _ = 1 * (th3 (2 * Real.pi) + th2 (2 * Real.pi)) := by rw [mul_one_div_cancel hsq]
      _ = th3 (2 * Real.pi) + th2 (2 * Real.pi) := one_mul _
  linarith

private lemma th3_pi_sq_eq_sqrt_two_mul_th4_pi_sq :
    th3 Real.pi ^ 2 = Real.sqrt 2 * th4 Real.pi ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h3 := th3_sq_eq hpi
  have h4 := th4_sq_eq hpi
  have hr := th2_two_pi_eq
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnum : (1 : ℝ) + (Real.sqrt 2 - 1) ^ 2 = Real.sqrt 2 * (1 - (Real.sqrt 2 - 1) ^ 2) := by
    have hL : (1 : ℝ) + (Real.sqrt 2 - 1) ^ 2 = 4 - 2 * Real.sqrt 2 := by nlinarith [hs2]
    have hR1 : (1 : ℝ) - (Real.sqrt 2 - 1) ^ 2 = 2 * Real.sqrt 2 - 2 := by nlinarith [hs2]
    rw [hL, hR1]
    nlinarith [hs2]
  rw [h3, h4, hr]
  calc
    th3 (2 * Real.pi) ^ 2 + ((Real.sqrt 2 - 1) * th3 (2 * Real.pi)) ^ 2
        = (1 + (Real.sqrt 2 - 1) ^ 2) * th3 (2 * Real.pi) ^ 2 := by ring
    _ = Real.sqrt 2 * (1 - (Real.sqrt 2 - 1) ^ 2) * th3 (2 * Real.pi) ^ 2 := by rw [hnum]
    _ = Real.sqrt 2 * (th3 (2 * Real.pi) ^ 2 - ((Real.sqrt 2 - 1) * th3 (2 * Real.pi)) ^ 2) := by
          ring

private lemma th2_pi_eq_th4_pi : th2 Real.pi = th4 Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 := th2_sq_eq hpi
  have h4 := th4_sq_eq hpi
  have hr := th2_two_pi_eq
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : th2 Real.pi ^ 2 = th4 Real.pi ^ 2 := by
    rw [h2, h4, hr]
    nlinarith
  have h2p : 0 ≤ th2 Real.pi := (th2_pos hpi).le
  have h4p : 0 ≤ th4 Real.pi := (th4_pos_of_two_le (by linarith [Real.pi_gt_three])).le
  exact (sq_eq_sq₀ h2p h4p).mp hsq

/-!
Part 2: Gauss AGM Integral, Landen Transformation, and Beta Integral
-/

private noncomputable def ellInt (a b x : ℝ) : ℝ :=
  1 / Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2))

private noncomputable def J (a b : ℝ) : ℝ :=
  ∫ x : ℝ, ellInt a b x

private lemma ellInt_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 < ellInt a b x := by
  rw [ellInt]
  positivity

private lemma ellInt_continuous {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous (ellInt a b) := by
  refine continuous_const.div ?_ (fun x => by positivity)
  exact ((continuous_pow 2 |>.add continuous_const).mul
    (continuous_pow 2 |>.add continuous_const)).sqrt

private lemma ellInt_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasureTheory.Integrable (ellInt a b) := by
  let m : ℝ := min (min a b) 1
  have hm : 0 < m := lt_min (lt_min ha hb) one_pos
  have hma : m ≤ a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmb : m ≤ b := le_trans (min_le_left _ _) (min_le_right _ _)
  have hm1 : m ≤ 1 := min_le_right _ _
  have hdom : MeasureTheory.Integrable (fun x : ℝ => (1 / m ^ 2) * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (1 / m ^ 2)
  refine hdom.mono' (ellInt_continuous ha hb).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_pos (ellInt_pos ha hb x), ellInt]
  have h1 : m ^ 2 * (1 + x ^ 2) ≤ x ^ 2 + a ^ 2 := by
    have hm2 : m ^ 2 ≤ 1 := by nlinarith
    have hma2 : m ^ 2 ≤ a ^ 2 := by nlinarith
    nlinarith [sq_nonneg x]
  have h2 : m ^ 2 * (1 + x ^ 2) ≤ x ^ 2 + b ^ 2 := by
    have hm2 : m ^ 2 ≤ 1 := by nlinarith
    have hmb2 : m ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith [sq_nonneg x]
  have hprod : (m ^ 2 * (1 + x ^ 2)) ^ 2 ≤ (x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) := by
    rw [sq]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hsqrt : m ^ 2 * (1 + x ^ 2) ≤ Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)) := by
    calc
      m ^ 2 * (1 + x ^ 2) = Real.sqrt ((m ^ 2 * (1 + x ^ 2)) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)) := Real.sqrt_le_sqrt hprod
  have hrhs : (1 / m ^ 2) * (1 + x ^ 2)⁻¹ = 1 / (m ^ 2 * (1 + x ^ 2)) := by
    rw [one_div, one_div, mul_inv]
  rw [hrhs]
  exact one_div_le_one_div_of_le (by positivity) hsqrt

private lemma J_eq_two_mul_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    J a b = 2 * ∫ x in Set.Ioi (0 : ℝ), ellInt a b x := by
  have hint := ellInt_integrable ha hb
  have huniv : J a b = ∫ x in Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ), ellInt a b x := by
    rw [Set.Iic_union_Ioi, MeasureTheory.setIntegral_univ, J]
  rw [huniv, MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
    hint.integrableOn hint.integrableOn, MeasureTheory.integral_Iic_eq_integral_Iio]
  have himg : (fun x : ℝ => -x) '' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · rintro ⟨x, hx, rfl⟩; linarith
    · intro hy; exact ⟨-y, by linarith, neg_neg y⟩
  have hneg : ∫ x in Set.Iio (0 : ℝ), ellInt a b x = ∫ x in Set.Ioi (0 : ℝ), ellInt a b x := by
    rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt) neg_injective.injOn]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [abs_neg, abs_one, one_smul, ellInt, neg_sq]
  rw [hneg]
  ring

private lemma J_landen {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    J ((a + b) / 2) (Real.sqrt (a * b)) = J a b := by
  set A : ℝ := (a + b) / 2
  set B : ℝ := Real.sqrt (a * b)
  let f : ℝ → ℝ := fun x => (x - a * b / x) / 2
  let f' : ℝ → ℝ := fun x => (1 + a * b / x ^ 2) / 2
  have himg : f '' Set.Ioi (0 : ℝ) = Set.univ := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_univ, iff_true]
    let r : ℝ := Real.sqrt (u ^ 2 + a * b)
    have hr2 : r ^ 2 = u ^ 2 + a * b := Real.sq_sqrt (by positivity)
    have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
    have hxpos : 0 < u + r := by
      have hab : 0 < a * b := mul_pos ha hb
      have hlt : u ^ 2 < r ^ 2 := by linarith
      have habs : |u| < r := by
        rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hrpos.le]
        exact Real.sqrt_lt_sqrt (sq_nonneg u) hlt
      linarith [neg_le_abs u]
    refine ⟨u + r, hxpos, ?_⟩
    dsimp only [f]
    have hdiv : a * b / (u + r) = r - u := by
      rw [div_eq_iff hxpos.ne']
      nlinarith
    rw [hdiv]
    ring
  have hinj : Set.InjOn f (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx' : 0 < x := hx
    have hy' : 0 < y := hy
    dsimp only [f] at hxy
    have h1 : x - a * b / x = y - a * b / y := by linarith
    have h2 : (x - a * b / x) * (x * y) = (y - a * b / y) * (x * y) := by rw [h1]
    have hl : (x - a * b / x) * (x * y) = x ^ 2 * y - a * b * y := by
      calc
        (x - a * b / x) * (x * y) = x * (x * y) - (a * b / x * x) * y := by ring
        _ = x ^ 2 * y - a * b * y := by rw [div_mul_cancel₀ _ hx'.ne']; ring
    have hr : (y - a * b / y) * (x * y) = y ^ 2 * x - a * b * x := by
      calc
        (y - a * b / y) * (x * y) = y * (x * y) - (a * b / y * y) * x := by ring
        _ = y ^ 2 * x - a * b * x := by rw [div_mul_cancel₀ _ hy'.ne']; ring
    rw [hl, hr] at h2
    have hfac : (x - y) * (x * y + a * b) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with hsub | hpos
    · linarith
    · exfalso; nlinarith [mul_pos hx' hy', mul_pos ha hb]
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (f' x) (Set.Ioi (0 : ℝ)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 : HasDerivAt (fun t : ℝ => t - a * b * t⁻¹) (1 - a * b * (-(x ^ 2)⁻¹)) x :=
      (hasDerivAt_id x).sub ((hasDerivAt_inv hx0).const_mul (a * b))
    have h2 : HasDerivAt f ((1 - a * b * (-(x ^ 2)⁻¹)) / 2) x := by
      have heq : f = fun t => (t - a * b * t⁻¹) / 2 := by
        ext t
        show (t - a * b / t) / 2 = (t - a * b * t⁻¹) / 2
        rw [div_eq_mul_inv (a * b) t]
      rw [heq]
      exact h1.div_const 2
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    dsimp only [f']
    rw [div_eq_mul_inv (a * b) (x ^ 2)]
    ring
  have hsub : J A B = ∫ x in Set.Ioi (0 : ℝ), |f' x| • ellInt A B (f x) := by
    rw [J, ← MeasureTheory.setIntegral_univ, ← himg]
    exact MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
      (ellInt A B)
  rw [hsub, J_eq_two_mul_Ioi ha hb, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : 0 < x := hx
  have hfp : 0 < f' x := by dsimp only [f']; positivity
  rw [smul_eq_mul, abs_of_pos hfp, ellInt, ellInt]
  have hf'eq : f' x = (x ^ 2 + a * b) / (2 * x ^ 2) := by
    dsimp only [f']
    rw [eq_div_iff (by positivity : 2 * x ^ 2 ≠ 0)]
    calc
      (1 + a * b / x ^ 2) / 2 * (2 * x ^ 2) = x ^ 2 + a * b / x ^ 2 * x ^ 2 := by ring
      _ = x ^ 2 + a * b := by rw [div_mul_cancel₀ _ (by positivity)]
  have hA2 : f x ^ 2 + A ^ 2 = (x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) / (4 * x ^ 2) := by
    dsimp only [f, A]
    rw [eq_div_iff (by positivity : 4 * x ^ 2 ≠ 0)]
    have hinv : a * b / x * x = a * b := div_mul_cancel₀ _ hx'.ne'
    calc
      (((x - a * b / x) / 2) ^ 2 + ((a + b) / 2) ^ 2) * (4 * x ^ 2)
          = (x ^ 2 - 2 * x * (a * b / x * x) / x + (a * b / x * x) ^ 2 / x ^ 2) * x ^ 2 +
              (a + b) ^ 2 * x ^ 2 := by
            rw [hinv]
            calc
              (((x - a * b / x) / 2) ^ 2 + ((a + b) / 2) ^ 2) * (4 * x ^ 2)
                  = (x ^ 2 - 2 * x * (a * b / x) + (a * b / x) ^ 2) * x ^ 2 +
                      (a + b) ^ 2 * x ^ 2 := by ring
              _ = (x ^ 2 - 2 * x * (a * b) / x + (a * b) ^ 2 / x ^ 2) * x ^ 2 +
                      (a + b) ^ 2 * x ^ 2 := by
                    congr 2; ring
      _ = x ^ 4 - 2 * a * b * x ^ 2 + (a * b) ^ 2 + (a + b) ^ 2 * x ^ 2 := by
            rw [hinv]
            have h3 : (2 * x * (a * b) / x) * x ^ 2 = 2 * a * b * x ^ 2 := by
              calc
                (2 * x * (a * b) / x) * x ^ 2 = (2 * (a * b)) * (x / x) * x ^ 2 := by ring
                _ = 2 * a * b * x ^ 2 := by rw [div_self hx'.ne']; ring
            have h4 : ((a * b) ^ 2 / x ^ 2) * x ^ 2 = (a * b) ^ 2 :=
              div_mul_cancel₀ _ (by positivity)
            linear_combination -h3 + h4
      _ = (x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) := by ring
  have hB2 : f x ^ 2 + B ^ 2 = ((x ^ 2 + a * b) / (2 * x)) ^ 2 := by
    dsimp only [f, B]
    rw [Real.sq_sqrt (by positivity)]
    have hinv : a * b / x * x = a * b := div_mul_cancel₀ _ hx'.ne'
    have h4x : (4 * x ^ 2 : ℝ) ≠ 0 := by positivity
    refine mul_right_cancel₀ h4x ?_
    have hL : (((x - a * b / x) / 2) ^ 2 + a * b) * (4 * x ^ 2) =
        x ^ 4 + 2 * a * b * x ^ 2 + (a * b) ^ 2 := by
      calc
        (((x - a * b / x) / 2) ^ 2 + a * b) * (4 * x ^ 2)
            = x ^ 4 - 2 * x ^ 2 * (a * b / x * x) + (a * b / x * x) ^ 2 + 4 * a * b * x ^ 2 := by
                ring
        _ = x ^ 4 + 2 * a * b * x ^ 2 + (a * b) ^ 2 := by rw [hinv]; ring
    have hR : ((x ^ 2 + a * b) / (2 * x)) ^ 2 * (4 * x ^ 2) =
        x ^ 4 + 2 * a * b * x ^ 2 + (a * b) ^ 2 := by
      have hsq : ((x ^ 2 + a * b) / (2 * x)) ^ 2 = (x ^ 2 + a * b) ^ 2 / (4 * x ^ 2) := by
        rw [div_pow]
        congr 1
        ring
      rw [hsq, div_mul_cancel₀ _ h4x]
      ring
    linarith
  have hsqrt :
      Real.sqrt ((f x ^ 2 + A ^ 2) * (f x ^ 2 + B ^ 2)) =
        Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)) * ((x ^ 2 + a * b) / (4 * x ^ 2)) := by
    rw [hA2, hB2, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      Real.sqrt_div (by positivity)]
    have h4x : Real.sqrt (4 * x ^ 2) = 2 * x := by
      have heq : 4 * x ^ 2 = (2 * x) ^ 2 := by ring
      rw [heq, Real.sqrt_sq (by positivity)]
    rw [h4x]
    ring
  rw [hf'eq, hsqrt]
  have hd1 : Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)) ≠ 0 := by positivity
  have hd2 : x ^ 2 + a * b ≠ 0 := by positivity
  have hd3 : (4 * x ^ 2 : ℝ) ≠ 0 := by positivity
  have hden : Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)) * ((x ^ 2 + a * b) / (4 * x ^ 2)) ≠ 0 :=
    mul_ne_zero hd1 (div_ne_zero hd2 hd3)
  rw [mul_one_div, mul_one_div, div_eq_div_iff hden hd1]
  calc
    (x ^ 2 + a * b) / (2 * x ^ 2) * Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2))
        = (2 * ((x ^ 2 + a * b) / (4 * x ^ 2))) *
            Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)) := by
          congr 1
          rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
          ring
    _ = 2 * (Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)) * ((x ^ 2 + a * b) / (4 * x ^ 2))) := by
          ring

private lemma J_scale {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    J (c * a) (c * b) = c⁻¹ * J a b := by
  rw [J_eq_two_mul_Ioi (mul_pos hc ha) (mul_pos hc hb), J_eq_two_mul_Ioi ha hb]
  have hcomp := MeasureTheory.integral_comp_mul_left_Ioi (ellInt (c * a) (c * b)) (0 : ℝ) hc
  rw [mul_zero, smul_eq_mul] at hcomp
  have hpt : ∫ x in Set.Ioi (0 : ℝ), ellInt (c * a) (c * b) (c * x) =
      (c ^ 2)⁻¹ * ∫ x in Set.Ioi (0 : ℝ), ellInt a b x := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [ellInt]
    have hfac : ((c * x) ^ 2 + (c * a) ^ 2) * ((c * x) ^ 2 + (c * b) ^ 2) =
        (c ^ 2) ^ 2 * ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)) := by ring
    rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), one_div,
      mul_inv, one_div]
  rw [hpt] at hcomp
  have hI : ∫ x in Set.Ioi (0 : ℝ), ellInt (c * a) (c * b) x =
      c⁻¹ * ∫ x in Set.Ioi (0 : ℝ), ellInt a b x := by
    have h1 := congrArg (fun t => c * t) hcomp.symm
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h1
    rw [h1, ← mul_assoc, sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hI]
  ring

private lemma J_one_one : J 1 1 = Real.pi := by
  have heq : ellInt 1 1 = fun x : ℝ => (1 + x ^ 2)⁻¹ := by
    ext x
    simp only [ellInt, one_pow]
    rw [← sq, Real.sqrt_sq (by positivity), one_div, add_comm]
  rw [J, heq, integral_univ_inv_one_add_sq]

private lemma J_diag {c : ℝ} (hc : 0 < c) : J c c = Real.pi / c := by
  have h := J_scale (a := 1) (b := 1) (c := c) one_pos one_pos hc
  rw [mul_one, J_one_one] at h
  rw [div_eq_inv_mul]
  exact h

private lemma J_le_of_le {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 < a₁) (hb₁ : 0 < b₁)
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : J a₂ b₂ ≤ J a₁ b₁ := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha
  have hb₂ : 0 < b₂ := lt_of_lt_of_le hb₁ hb
  refine MeasureTheory.integral_mono (ellInt_integrable ha₂ hb₂) (ellInt_integrable ha₁ hb₁) ?_
  intro x
  simp only [ellInt]
  refine one_div_le_one_div_of_le (by positivity) (Real.sqrt_le_sqrt ?_)
  have h1 : x ^ 2 + a₁ ^ 2 ≤ x ^ 2 + a₂ ^ 2 := by nlinarith
  have h2 : x ^ 2 + b₁ ^ 2 ≤ x ^ 2 + b₂ ^ 2 := by nlinarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

private lemma J_theta_iter (n : ℕ) :
    J (th3 (2 ^ n * Real.pi) ^ 2) (th4 (2 ^ n * Real.pi) ^ 2) =
      J (th3 Real.pi ^ 2) (th4 Real.pi ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set c : ℝ := 2 ^ n * Real.pi
    have hc2 : 2 ≤ c := by
      have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith [Real.pi_gt_three]
    have hc0 : 0 < c := by linarith
    have h3p : 0 < th3 c := th3_pos hc0
    have h4p : 0 < th4 c := th4_pos_of_two_le hc2
    have h2n : (2 : ℝ) ^ (n + 1) * Real.pi = 2 * c := by
      dsimp only [c]; rw [pow_succ]; ring
    rw [h2n, ← th3_agm hc0]
    have hgm : th4 (2 * c) ^ 2 = Real.sqrt (th3 c ^ 2 * th4 c ^ 2) := by
      rw [← th3_mul_th4_eq hc0, ← mul_pow, Real.sqrt_sq (mul_pos h3p h4p).le]
    rw [hgm, J_landen (sq_pos_of_pos h3p) (sq_pos_of_pos h4p), ih]

private lemma tendsto_th3_iter :
    Filter.Tendsto (fun n : ℕ => th3 (2 ^ n * Real.pi)) Filter.atTop (nhds 1) := by
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-(2 ^ n * Real.pi))) Filter.atTop (nhds 0) := by
    have hq0 : 0 ≤ qVal := (Real.exp_pos _).le
    have hq1 : qVal < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
    have hpow : Filter.Tendsto (fun n : ℕ => qVal ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    refine squeeze_zero (fun n => (Real.exp_pos _).le) (fun n => ?_) hpow
    have hge : (n : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    calc
      Real.exp (-(2 ^ n * Real.pi)) ≤ Real.exp (-((n : ℝ) * Real.pi)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      _ = Real.exp ((n : ℕ) * (-Real.pi)) := by congr 1; ring
      _ = qVal ^ n := Real.exp_nat_mul (-Real.pi) n
  have hbound : Filter.Tendsto
      (fun n : ℕ => 2 * (Real.exp (-(2 ^ n * Real.pi)) / (1 - Real.exp (-(2 ^ n * Real.pi)))))
      Filter.atTop (nhds 0) := by
    have h0 : (2 : ℝ) * ((0 : ℝ) / (1 - 0)) = 0 := by norm_num
    rw [← h0]
    exact (hexp.div (tendsto_const_nhds.sub hexp) (by norm_num)).const_mul 2
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hbound
  rcases hbound ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hc0 : 0 < 2 ^ n * Real.pi := by positivity
  have h1 := th3_sub_one_abs_le hc0
  have h2 := hN n hn
  rw [Real.dist_eq, sub_zero] at h2
  have hnn : 0 ≤ 2 * (Real.exp (-(2 ^ n * Real.pi)) / (1 - Real.exp (-(2 ^ n * Real.pi)))) := by
    have hlt : Real.exp (-(2 ^ n * Real.pi)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    positivity
  rw [abs_of_nonneg hnn] at h2
  rw [Real.dist_eq]
  linarith

private lemma tendsto_th4_iter :
    Filter.Tendsto (fun n : ℕ => th4 (2 ^ n * Real.pi)) Filter.atTop (nhds 1) := by
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-(2 ^ n * Real.pi))) Filter.atTop (nhds 0) := by
    have hq0 : 0 ≤ qVal := (Real.exp_pos _).le
    have hq1 : qVal < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
    have hpow : Filter.Tendsto (fun n : ℕ => qVal ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    refine squeeze_zero (fun n => (Real.exp_pos _).le) (fun n => ?_) hpow
    have hge : (n : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    calc
      Real.exp (-(2 ^ n * Real.pi)) ≤ Real.exp (-((n : ℝ) * Real.pi)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      _ = Real.exp ((n : ℕ) * (-Real.pi)) := by congr 1; ring
      _ = qVal ^ n := Real.exp_nat_mul (-Real.pi) n
  have hbound : Filter.Tendsto
      (fun n : ℕ => 2 * (Real.exp (-(2 ^ n * Real.pi)) / (1 - Real.exp (-(2 ^ n * Real.pi)))))
      Filter.atTop (nhds 0) := by
    have h0 : (2 : ℝ) * ((0 : ℝ) / (1 - 0)) = 0 := by norm_num
    rw [← h0]
    exact (hexp.div (tendsto_const_nhds.sub hexp) (by norm_num)).const_mul 2
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hbound
  rcases hbound ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hc0 : 0 < 2 ^ n * Real.pi := by positivity
  have h1 := th4_sub_one_abs_le hc0
  have h2 := hN n hn
  rw [Real.dist_eq, sub_zero] at h2
  have hnn : 0 ≤ 2 * (Real.exp (-(2 ^ n * Real.pi)) / (1 - Real.exp (-(2 ^ n * Real.pi)))) := by
    have hlt : Real.exp (-(2 ^ n * Real.pi)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    positivity
  rw [abs_of_nonneg hnn] at h2
  rw [Real.dist_eq]
  linarith

private lemma J_theta_pi_eq_pi :
    J (th3 Real.pi ^ 2) (th4 Real.pi ^ 2) = Real.pi := by
  have hlo : ∀ n : ℕ, Real.pi / th3 (2 ^ n * Real.pi) ^ 2 ≤
      J (th3 Real.pi ^ 2) (th4 Real.pi ^ 2) := by
    intro n
    set c : ℝ := 2 ^ n * Real.pi
    have hc2 : 2 ≤ c := by
      have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith [Real.pi_gt_three]
    have hc0 : 0 < c := by linarith
    have h3p : 0 < th3 c := th3_pos hc0
    have h4p : 0 < th4 c := th4_pos_of_two_le hc2
    have hle : th4 c ^ 2 ≤ th3 c ^ 2 := by nlinarith [th4_le_th3 hc0]
    rw [← J_theta_iter n, ← J_diag (sq_pos_of_pos h3p)]
    exact J_le_of_le (sq_pos_of_pos h3p) (sq_pos_of_pos h4p) le_rfl hle
  have hhi : ∀ n : ℕ, J (th3 Real.pi ^ 2) (th4 Real.pi ^ 2) ≤
      Real.pi / th4 (2 ^ n * Real.pi) ^ 2 := by
    intro n
    set c : ℝ := 2 ^ n * Real.pi
    have hc2 : 2 ≤ c := by
      have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith [Real.pi_gt_three]
    have hc0 : 0 < c := by linarith
    have h3p : 0 < th3 c := th3_pos hc0
    have h4p : 0 < th4 c := th4_pos_of_two_le hc2
    have hle : th4 c ^ 2 ≤ th3 c ^ 2 := by nlinarith [th4_le_th3 hc0]
    rw [← J_theta_iter n, ← J_diag (sq_pos_of_pos h4p)]
    exact J_le_of_le (sq_pos_of_pos h4p) (sq_pos_of_pos h4p) hle le_rfl
  have htlo : Filter.Tendsto (fun n : ℕ => Real.pi / th3 (2 ^ n * Real.pi) ^ 2)
      Filter.atTop (nhds Real.pi) := by
    have h : Filter.Tendsto (fun n : ℕ => Real.pi / th3 (2 ^ n * Real.pi) ^ 2)
        Filter.atTop (nhds (Real.pi / (1 : ℝ) ^ 2)) :=
      Filter.Tendsto.div tendsto_const_nhds (tendsto_th3_iter.pow 2) (by norm_num)
    simpa only [one_pow, div_one] using h
  have hthi : Filter.Tendsto (fun n : ℕ => Real.pi / th4 (2 ^ n * Real.pi) ^ 2)
      Filter.atTop (nhds Real.pi) := by
    have h : Filter.Tendsto (fun n : ℕ => Real.pi / th4 (2 ^ n * Real.pi) ^ 2)
        Filter.atTop (nhds (Real.pi / (1 : ℝ) ^ 2)) :=
      Filter.Tendsto.div tendsto_const_nhds (tendsto_th4_iter.pow 2) (by norm_num)
    simpa only [one_pow, div_one] using h
  have h1 : Real.pi ≤ J (th3 Real.pi ^ 2) (th4 Real.pi ^ 2) :=
    le_of_tendsto_of_tendsto htlo tendsto_const_nhds (Filter.Eventually.of_forall hlo)
  have h2 : J (th3 Real.pi ^ 2) (th4 Real.pi ^ 2) ≤ Real.pi :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hthi (Filter.Eventually.of_forall hhi)
  linarith

private lemma beta_real_eq :
    ∫ t in Set.Ioo (0 : ℝ) 1, t ^ (-(3 / 4 : ℝ)) * (1 - t) ^ (-(1 / 2 : ℝ)) =
      Real.Gamma (1 / 4) * Real.Gamma (1 / 2) / Real.Gamma (3 / 4) := by
  have hu : 0 < ((1 / 4 : ℝ) : ℂ).re := by norm_num
  have hv : 0 < ((1 / 2 : ℝ) : ℂ).re := by norm_num
  have hconv := Complex.betaIntegral_convergent hu hv
  have hbg := Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv
  have hsum : ((1 / 4 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = ((3 / 4 : ℝ) : ℂ) := by norm_num
  rw [hsum, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at hbg
  have hre := congrArg Complex.re hbg
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] at hre
  have hbi : (Complex.betaIntegral ((1 / 4 : ℝ) : ℂ) ((1 / 2 : ℝ) : ℂ)).re =
      ∫ t in Set.Ioo (0 : ℝ) 1, t ^ (-(3 / 4 : ℝ)) * (1 - t) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hcomm := Complex.reCLM.integral_comp_comm hconv.1
    change Complex.reCLM _ = _
    rw [← hcomm, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 ≤ t := ht.1.le
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    have he1 : ((1 / 4 : ℝ) : ℂ) - 1 = ((-(3 / 4 : ℝ) : ℝ) : ℂ) := by norm_num
    have he2 : ((1 / 2 : ℝ) : ℂ) - 1 = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by norm_num
    have h1t : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
    change ((t : ℂ) ^ (((1 / 4 : ℝ) : ℂ) - 1) * (1 - (t : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) - 1)).re = _
    rw [he1, he2, h1t, ← Complex.ofReal_cpow ht0, ← Complex.ofReal_cpow ht1,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hbi] at hre
  have hg34 : Real.Gamma (3 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  rw [eq_div_iff hg34, mul_comm]
  exact hre.symm

private lemma beta_real_eq_J :
    ∫ t in Set.Ioo (0 : ℝ) 1, t ^ (-(3 / 4 : ℝ)) * (1 - t) ^ (-(1 / 2 : ℝ)) =
      Real.sqrt 2 * J 1 (1 / Real.sqrt 2) := by
  let f : ℝ → ℝ := fun x => 1 / (1 + x ^ 2) ^ 2
  let f' : ℝ → ℝ := fun x => -4 * x / (1 + x ^ 2) ^ 3
  have himg : f '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
    ext t
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · rintro ⟨x, hx, rfl⟩
      dsimp only [f]
      have hgt : 1 < (1 + x ^ 2) ^ 2 := by nlinarith [sq_pos_of_pos hx]
      exact ⟨by positivity, (div_lt_one (by positivity)).mpr hgt⟩
    · rintro ⟨ht0, ht1⟩
      have hsqt0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      have hsqt1 : Real.sqrt t < 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt ht0.le ht1
      have hinv1 : 1 < 1 / Real.sqrt t := (one_lt_div hsqt0).mpr hsqt1
      let x : ℝ := Real.sqrt (1 / Real.sqrt t - 1)
      have hxpos : 0 < x := Real.sqrt_pos.mpr (by linarith)
      refine ⟨x, hxpos, ?_⟩
      dsimp only [f, x]
      rw [Real.sq_sqrt (by linarith)]
      have h1 : 1 + (1 / Real.sqrt t - 1) = 1 / Real.sqrt t := by ring
      rw [h1, one_div_pow, Real.sq_sqrt ht0.le, one_div_one_div]
  have hinj : Set.InjOn f (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx' : 0 < x := hx
    have hy' : 0 < y := hy
    dsimp only [f] at hxy
    have hsq : (1 + x ^ 2) ^ 2 = (1 + y ^ 2) ^ 2 := by
      have h1 := congrArg Inv.inv hxy
      simpa only [one_div, inv_inv] using h1
    have h1 : 1 + x ^ 2 = 1 + y ^ 2 := (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
    have h2 : x ^ 2 = y ^ 2 := by linarith
    exact (sq_eq_sq₀ hx'.le hy'.le).mp h2
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (f' x) (Set.Ioi (0 : ℝ)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => (1 + u ^ 2) ^ 2) (2 * (1 + x ^ 2) ^ 1 * (2 * x)) x := by
      have hbase : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * x) x := by
        have hp := (hasDerivAt_pow 2 x).const_add (1 : ℝ)
        refine hp.congr_deriv ?_
        norm_num
      exact hbase.pow 2
    have h2 : HasDerivAt f (-(2 * (1 + x ^ 2) ^ 1 * (2 * x)) / ((1 + x ^ 2) ^ 2) ^ 2) x := by
      have heq : f = fun u => ((1 + u ^ 2) ^ 2)⁻¹ := by
        ext u; dsimp only [f]; rw [one_div]
      rw [heq]
      exact h1.inv (by positivity)
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    dsimp only [f']
    have hp : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  have hpt : ∫ x in Set.Ioi (0 : ℝ),
      |f' x| • (f x ^ (-(3 / 4 : ℝ)) * (1 - f x) ^ (-(1 / 2 : ℝ))) =
      ∫ x in Set.Ioi (0 : ℝ), 4 * ellInt (Real.sqrt 2) 1 x := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : 0 < x := hx
    set u : ℝ := 1 + x ^ 2
    have hu : 0 < u := by positivity
    have hf'abs : |f' x| = 4 * x / u ^ 3 := by
      dsimp only [f', u]
      have hneg : -4 * x / (1 + x ^ 2) ^ 3 = -(4 * x / (1 + x ^ 2) ^ 3) := by ring
      rw [hneg, abs_neg, abs_of_pos (by positivity)]
    have hfx1 : f x ^ (-(3 / 4 : ℝ)) = u * Real.sqrt u := by
      dsimp only [f, u]
      rw [one_div, ← Real.rpow_natCast (1 + x ^ 2) 2, ← Real.rpow_neg hu.le,
        ← Real.rpow_mul hu.le]
      have hexp : (-((2 : ℕ) : ℝ)) * -(3 / 4 : ℝ) = (1 : ℝ) + 1 / 2 := by norm_num
      rw [hexp, Real.rpow_add hu, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have h1mf : 1 - f x = x ^ 2 * (x ^ 2 + 2) / u ^ 2 := by
      dsimp only [f, u]
      rw [eq_div_iff (by positivity : (1 + x ^ 2) ^ 2 ≠ 0)]
      calc
        (1 - 1 / (1 + x ^ 2) ^ 2) * (1 + x ^ 2) ^ 2
            = (1 + x ^ 2) ^ 2 - 1 / (1 + x ^ 2) ^ 2 * (1 + x ^ 2) ^ 2 := by ring
        _ = (1 + x ^ 2) ^ 2 - 1 := by rw [div_mul_cancel₀ _ (by positivity)]
        _ = x ^ 2 * (x ^ 2 + 2) := by ring
    have hfx2 : (1 - f x) ^ (-(1 / 2 : ℝ)) = u / (x * Real.sqrt (x ^ 2 + 2)) := by
      rw [h1mf, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
        Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq hx'.le, Real.sqrt_sq hu.le, inv_div]
    rw [smul_eq_mul, hf'abs, hfx1, hfx2, ellInt]
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [hsq2, one_pow, Real.sqrt_mul (by positivity)]
    have hu_eq : x ^ 2 + 1 = u := by dsimp only [u]; ring
    rw [hu_eq]
    have hsu : Real.sqrt u ≠ 0 := by positivity
    have hs2 : Real.sqrt (x ^ 2 + 2) ≠ 0 := by positivity
    have hden1 : u ^ 3 * (x * Real.sqrt (x ^ 2 + 2)) ≠ 0 := by positivity
    have hden2 : Real.sqrt (x ^ 2 + 2) * Real.sqrt u ≠ 0 := by positivity
    calc
      4 * x / u ^ 3 * (u * Real.sqrt u * (u / (x * Real.sqrt (x ^ 2 + 2))))
          = 4 * x * u ^ 2 * Real.sqrt u / (u ^ 3 * (x * Real.sqrt (x ^ 2 + 2))) := by
            simp only [div_eq_mul_inv, mul_inv]
            ring
      _ = 4 / (Real.sqrt (x ^ 2 + 2) * Real.sqrt u) := by
            rw [div_eq_div_iff hden1 hden2]
            have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
            calc
              4 * x * u ^ 2 * Real.sqrt u * (Real.sqrt (x ^ 2 + 2) * Real.sqrt u)
                  = 4 * x * u ^ 2 * (Real.sqrt u * Real.sqrt u) * Real.sqrt (x ^ 2 + 2) := by ring
              _ = 4 * (u ^ 3 * (x * Real.sqrt (x ^ 2 + 2))) := by rw [hsq]; ring
      _ = 4 * (1 / (Real.sqrt (x ^ 2 + 2) * Real.sqrt u)) := by ring
  rw [hpt, MeasureTheory.integral_const_mul]
  have hJ2 := J_eq_two_mul_Ioi (a := Real.sqrt 2) (b := 1) (by positivity) one_pos
  have hsc := J_scale (a := 1) (b := 1 / Real.sqrt 2) (c := Real.sqrt 2)
    one_pos (by positivity) (by positivity)
  have hmul : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 :=
    mul_one_div_cancel (by positivity : Real.sqrt 2 ≠ 0)
  rw [mul_one, hmul] at hsc
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc
    4 * ∫ x in Set.Ioi (0 : ℝ), ellInt (Real.sqrt 2) 1 x
        = 2 * J (Real.sqrt 2) 1 := by linarith
    _ = 2 * ((Real.sqrt 2)⁻¹ * J 1 (1 / Real.sqrt 2)) := by rw [hsc]
    _ = (2 * (Real.sqrt 2)⁻¹) * J 1 (1 / Real.sqrt 2) := by ring
    _ = Real.sqrt 2 * J 1 (1 / Real.sqrt 2) := by
          congr 1
          calc
            2 * (Real.sqrt 2)⁻¹ = (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt 2)⁻¹ := by rw [hsq2]
            _ = Real.sqrt 2 * (Real.sqrt 2 * (Real.sqrt 2)⁻¹) := by ring
            _ = Real.sqrt 2 := by
                  rw [mul_inv_cancel₀ (by positivity : Real.sqrt 2 ≠ 0), mul_one]

private lemma J_one_inv_sqrt_two :
    J 1 (1 / Real.sqrt 2) = Real.pi * Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2 := by
  have h1 := beta_real_eq
  have h2 := beta_real_eq_J
  rw [h2] at h1
  have href := Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
  have hsub : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  have hmul : Real.pi * (1 / 4 : ℝ) = Real.pi / 4 := by ring
  rw [hsub, hmul, Real.sin_pi_div_four] at href
  have hsq2 : Real.sqrt 2 ≠ 0 := by positivity
  have hg34 : Real.Gamma (3 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hg14 : Real.Gamma (1 / 4) = Real.sqrt 2 * Real.pi / Real.Gamma (3 / 4) := by
    have hdiv : Real.pi / (Real.sqrt 2 / 2) = Real.sqrt 2 * Real.pi := by
      rw [div_eq_iff (by positivity : Real.sqrt 2 / 2 ≠ 0)]
      have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      calc
        Real.pi = Real.pi * (2 / 2) := by norm_num
        _ = Real.sqrt 2 * Real.pi * (Real.sqrt 2 / 2) := by
              calc
                Real.pi * (2 / 2) = Real.pi * (Real.sqrt 2 * Real.sqrt 2 / 2) := by rw [hs]
                _ = Real.sqrt 2 * Real.pi * (Real.sqrt 2 / 2) := by ring
    rw [hdiv] at href
    rw [eq_div_iff hg34]
    exact href
  rw [hg14, Real.Gamma_one_half_eq] at h1
  have hrhs : Real.sqrt 2 * Real.pi / Real.Gamma (3 / 4) * Real.sqrt Real.pi / Real.Gamma (3 / 4) =
      Real.sqrt 2 * (Real.pi * Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2) := by
    rw [mul_div_right_comm, div_div, ← sq]
    ring
  rw [hrhs] at h1
  exact mul_left_cancel₀ hsq2 h1

private lemma th3_pi_sq_eq_gamma :
    th3 Real.pi ^ 2 = Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2 := by
  have h3p : 0 < th3 Real.pi ^ 2 := sq_pos_of_pos (th3_pos Real.pi_pos)
  have h4eq : th4 Real.pi ^ 2 = th3 Real.pi ^ 2 * (1 / Real.sqrt 2) := by
    have h := th3_pi_sq_eq_sqrt_two_mul_th4_pi_sq
    rw [mul_one_div, eq_div_iff (by positivity : Real.sqrt 2 ≠ 0)]
    linarith
  have hsc := J_scale (a := 1) (b := 1 / Real.sqrt 2) (c := th3 Real.pi ^ 2)
    one_pos (by positivity) h3p
  rw [mul_one, ← h4eq, J_theta_pi_eq_pi, J_one_inv_sqrt_two] at hsc
  have hmul := congrArg (fun t => th3 Real.pi ^ 2 * t) hsc
  rw [← mul_assoc, mul_inv_cancel₀ h3p.ne', one_mul] at hmul
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  refine mul_left_cancel₀ hpi ?_
  calc
    Real.pi * th3 Real.pi ^ 2 = th3 Real.pi ^ 2 * Real.pi := by ring
    _ = Real.pi * Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2 := hmul
    _ = Real.pi * (Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2) := by ring

/-!
Part 3: Elementary Direct-Induction Jacobi Triple Product
-/

private noncomputable def jtpProd (q z : ℝ) (N : ℕ) : ℝ :=
  (∏ j ∈ Finset.range N, (1 - q ^ (2 * (j + 1)))) *
    (∏ k ∈ Finset.range N, (1 + z * q ^ (2 * k + 1)) * (1 + z⁻¹ * q ^ (2 * k + 1)))

private def jtpA (q : ℝ) (N n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (N - n), (1 - q ^ (2 * (N + n + 1 + j)))

private def jtpB (q : ℝ) (N n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 - q ^ (2 * (N - j)))

private def jtpCoeff (q : ℝ) (N n : ℕ) : ℝ :=
  if n ≤ N then jtpA q N n * jtpB q N n else 0

private noncomputable def symTerm (z : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => z ^ (n + 1) + (z⁻¹) ^ (n + 1)

private lemma jtpA_step_lo (q : ℝ) (N n : ℕ) (hn : n < N) :
    jtpA q N n = (1 - q ^ (2 * (N + n + 1))) * jtpA q N (n + 1) := by
  dsimp only [jtpA]
  have hsub : N - n = (N - (n + 1)) + 1 := by omega
  rw [hsub, Finset.prod_range_succ']
  simp only [Nat.add_zero]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 2
  omega

private lemma jtpA_step_hi (q : ℝ) (N n : ℕ) (hn : n < N) :
    jtpA q (N + 1) n = jtpA q N (n + 1) * (1 - q ^ (4 * N + 2)) * (1 - q ^ (4 * N + 4)) := by
  dsimp only [jtpA]
  have hsub : N + 1 - n = (N - (n + 1)) + 2 := by omega
  rw [hsub, Finset.prod_range_succ, Finset.prod_range_succ]
  congr 2
  · refine Finset.prod_congr rfl fun j _ => ?_
    congr 2
    omega
  · congr 2; omega
  · congr 2; omega

private lemma jtpB_step_lo (q : ℝ) (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    jtpB q N n = jtpB q N (n - 1) * (1 - q ^ (2 * (N - n + 1))) := by
  dsimp only [jtpB]
  have hsub : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hsub]
  rw [Finset.prod_range_succ]
  have hexp : 2 * (N - (n - 1)) = 2 * (N - n + 1) := by omega
  rw [hexp]

private lemma jtpB_step_succN (q : ℝ) (N n : ℕ) (hn : 1 ≤ n) :
    jtpB q (N + 1) n = (1 - q ^ (2 * N + 2)) * jtpB q N (n - 1) := by
  dsimp only [jtpB]
  have hsub : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hsub]
  rw [Finset.prod_range_succ']
  simp only [Nat.sub_zero]
  rw [mul_comm]
  have h1 : 2 * (N + 1) = 2 * N + 2 := by omega
  rw [h1]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have h2 : 2 * (N + 1 - (j + 1)) = 2 * (N - j) := by omega
  rw [h2]

private lemma jtpCoeff_step_zero (q : ℝ) (N : ℕ) :
    (1 - q ^ (2 * N + 2)) *
        ((1 + q ^ (4 * N + 2)) * (jtpCoeff q N 0 * q ^ (0 ^ 2)) +
          2 * q ^ (2 * N + 1) * (jtpCoeff q N 1 * q ^ (1 ^ 2))) =
      jtpCoeff q (N + 1) 0 * q ^ (0 ^ 2) := by
  cases N with
  | zero =>
    have hno : ¬ (1 ≤ 0) := by omega
    have h01 : 0 ≤ 1 := by omega
    simp only [jtpCoeff, Nat.le_refl, hno, h01, ↓reduceIte, jtpA, jtpB, Nat.sub_zero,
      Finset.prod_range_zero]
    rw [Finset.prod_range_one]
    ring
  | succ M =>
    have h0 : 0 ≤ M + 1 := Nat.zero_le _
    have h1 : 1 ≤ M + 1 := by omega
    have h0' : 0 ≤ M + 2 := Nat.zero_le _
    simp only [jtpCoeff, h0, h1, h0', ↓reduceIte]
    have hA0 := jtpA_step_lo q (M + 1) 0 (by omega)
    have hA1 := jtpA_step_hi q (M + 1) 0 (by omega)
    have hB0 : jtpB q (M + 1) 0 = 1 := by simp [jtpB]
    have hB0' : jtpB q (M + 2) 0 = 1 := by simp [jtpB]
    have hB1 : jtpB q (M + 1) 1 = 1 - q ^ (2 * (M + 1)) := by
      simp [jtpB]
    rw [hA0, hA1, hB0, hB0', hB1]
    set X : ℝ := q ^ (2 * (M + 1))
    set Q : ℝ := q ^ 2
    have h1a : q ^ (2 * (M + 1 + 0 + 1)) = Q * X := by
      dsimp only [X, Q]; rw [← pow_add]; congr 1; omega
    have h1b : q ^ (2 * (M + 1) + 2) = Q * X := by
      dsimp only [X, Q]; rw [← pow_add]; congr 1; omega
    have h1c : q ^ (4 * (M + 1) + 2) = Q * X ^ 2 := by
      dsimp only [X, Q]; rw [← pow_mul, ← pow_add]; congr 1; omega
    have h1d : q ^ (4 * (M + 1) + 4) = Q ^ 2 * X ^ 2 := by
      dsimp only [X, Q]; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
    have h1e : q ^ (2 * (M + 1) + 1) * q ^ (1 ^ 2) = Q * X := by
      dsimp only [X, Q]; rw [← pow_add, ← pow_add]; congr 1; omega
    have h0sq : q ^ (0 ^ 2) = 1 := by norm_num
    rw [h0sq, h1a, h1b, h1c, h1d]
    calc
      (1 - Q * X) * ((1 + Q * X ^ 2) * ((1 - Q * X) * jtpA q (M + 1) 1 * 1 * 1) +
          2 * q ^ (2 * (M + 1) + 1) * (jtpA q (M + 1) 1 * (1 - X) * q ^ (1 ^ 2)))
          = (1 - Q * X) * ((1 + Q * X ^ 2) * (1 - Q * X) +
              2 * (q ^ (2 * (M + 1) + 1) * q ^ (1 ^ 2)) * (1 - X)) * jtpA q (M + 1) 1 := by ring
      _ = (1 - Q * X) * ((1 + Q * X ^ 2) * (1 - Q * X) + 2 * (Q * X) * (1 - X)) *
            jtpA q (M + 1) 1 := by rw [h1e]
      _ = jtpA q (M + 1) 1 * (1 - Q * X ^ 2) * (1 - Q ^ 2 * X ^ 2) * 1 * 1 := by ring

private lemma jtpCoeff_step_pos (q : ℝ) (N m : ℕ) (hm : m ≤ N) :
    (1 - q ^ (2 * N + 2)) *
        ((1 + q ^ (4 * N + 2)) * (jtpCoeff q N (m + 1) * q ^ ((m + 1) ^ 2)) +
          q ^ (2 * N + 1) * (jtpCoeff q N m * q ^ (m ^ 2)) +
          q ^ (2 * N + 1) * (jtpCoeff q N (m + 2) * q ^ ((m + 2) ^ 2))) =
      jtpCoeff q (N + 1) (m + 1) * q ^ ((m + 1) ^ 2) := by
  have hleN1 : m + 1 ≤ N + 1 := by omega
  rcases eq_or_lt_of_le hm with rfl | hlt
  · have hno1 : ¬ (m + 1 ≤ m) := by omega
    have hno2 : ¬ (m + 2 ≤ m) := by omega
    simp only [jtpCoeff, Nat.le_refl, hno1, hno2, ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add]
    have hA1 : jtpA q m m = 1 := by simp [jtpA]
    have hA2 : jtpA q (m + 1) (m + 1) = 1 := by simp [jtpA]
    have hB := jtpB_step_succN q m (m + 1) (by omega)
    rw [hA1, hA2, hB, Nat.add_sub_cancel]
    have hexp : q ^ (2 * m + 1) * q ^ (m ^ 2) = q ^ ((m + 1) ^ 2) := by
      rw [← pow_add]; congr 1; ring
    calc
      (1 - q ^ (2 * m + 2)) * (q ^ (2 * m + 1) * (1 * jtpB q m m * q ^ (m ^ 2)))
          = (1 - q ^ (2 * m + 2)) * jtpB q m m * (q ^ (2 * m + 1) * q ^ (m ^ 2)) := by ring
      _ = 1 * ((1 - q ^ (2 * m + 2)) * jtpB q m m) * q ^ ((m + 1) ^ 2) := by rw [hexp]; ring
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with heq | hlt2
    · have hmN : m + 1 = N := heq
      have hno2 : ¬ (m + 2 ≤ N) := by omega
      simp only [jtpCoeff, hm, Nat.succ_le_of_lt hlt, hno2, hleN1, ↓reduceIte,
        zero_mul, mul_zero, add_zero]
      have hAn : jtpA q N (m + 1) = 1 := by rw [hmN]; simp [jtpA]
      have hAm : jtpA q N m = 1 - q ^ (4 * N) := by
        dsimp only [jtpA]
        have hs : N - m = 1 := by omega
        rw [hs, Finset.prod_range_one]
        congr 2; omega
      have hAn1 : jtpA q (N + 1) (m + 1) = 1 - q ^ (4 * N + 4) := by
        dsimp only [jtpA]
        have hs : N + 1 - (m + 1) = 1 := by omega
        rw [hs, Finset.prod_range_one]
        congr 2; omega
      have hBn : jtpB q N (m + 1) = jtpB q N m * (1 - q ^ 2) := by
        have h := jtpB_step_lo q N (m + 1) (by omega) (by omega)
        rw [Nat.add_sub_cancel] at h
        rw [h]
        congr 3; omega
      have hBn1 : jtpB q (N + 1) (m + 1) = (1 - q ^ (2 * N + 2)) * jtpB q N m := by
        have h := jtpB_step_succN q N (m + 1) (by omega)
        rw [Nat.add_sub_cancel] at h
        exact h
      rw [hAn, hAm, hAn1, hBn, hBn1]
      have hexp : q ^ (2 * N + 1) * q ^ (m ^ 2) = q ^ 2 * q ^ ((m + 1) ^ 2) := by
        rw [← pow_add, ← pow_add]; congr 1
        have hN : N = m + 1 := hmN.symm
        rw [hN]; ring
      have h42 : q ^ (4 * N + 2) = q ^ 2 * q ^ (4 * N) := by
        rw [← pow_add]; congr 1; omega
      have h44 : q ^ (4 * N + 4) = q ^ 2 * (q ^ 2 * q ^ (4 * N)) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [h42, h44]
      calc
        (1 - q ^ (2 * N + 2)) *
            ((1 + q ^ 2 * q ^ (4 * N)) * (1 * (jtpB q N m * (1 - q ^ 2)) * q ^ ((m + 1) ^ 2)) +
              q ^ (2 * N + 1) * ((1 - q ^ (4 * N)) * jtpB q N m * q ^ (m ^ 2)))
            = (1 - q ^ (2 * N + 2)) * jtpB q N m *
                ((1 + q ^ 2 * q ^ (4 * N)) * (1 - q ^ 2) * q ^ ((m + 1) ^ 2) +
                  (1 - q ^ (4 * N)) * (q ^ (2 * N + 1) * q ^ (m ^ 2))) := by ring
        _ = (1 - q ^ (2 * N + 2)) * jtpB q N m *
              ((1 + q ^ 2 * q ^ (4 * N)) * (1 - q ^ 2) * q ^ ((m + 1) ^ 2) +
                (1 - q ^ (4 * N)) * (q ^ 2 * q ^ ((m + 1) ^ 2))) := by rw [hexp]
        _ = (1 - q ^ 2 * (q ^ 2 * q ^ (4 * N))) * ((1 - q ^ (2 * N + 2)) * jtpB q N m) *
              q ^ ((m + 1) ^ 2) := by ring
    · have hle1 : m + 1 ≤ N := by omega
      have hle2 : m + 2 ≤ N := by omega
      simp only [jtpCoeff, hm, hle1, hle2, hleN1, ↓reduceIte]
      have hAn := jtpA_step_lo q N (m + 1) hlt2
      have hAm := jtpA_step_lo q N m hlt
      rw [hAn] at hAm
      have hAn1 := jtpA_step_hi q N (m + 1) hlt2
      have hBn := jtpB_step_lo q N (m + 1) (by omega) hle1
      rw [Nat.add_sub_cancel] at hBn
      have hBn2 := jtpB_step_lo q N (m + 2) (by omega) hle2
      have hsub2 : m + 2 - 1 = m + 1 := by omega
      rw [hsub2, hBn] at hBn2
      have hBn1 := jtpB_step_succN q N (m + 1) (by omega)
      rw [Nat.add_sub_cancel] at hBn1
      rw [hAm, hAn, hAn1, hBn2, hBn, hBn1]
      set X : ℝ := q ^ (2 * (N - (m + 1)))
      set Y : ℝ := q ^ (2 * (m + 1))
      set Q : ℝ := q ^ 2
      have he1 : q ^ (2 * (N - (m + 2) + 1)) = X := by
        dsimp only [X]; congr 1; omega
      have he2 : q ^ (2 * (N - (m + 1) + 1)) = Q * X := by
        dsimp only [X, Q]; rw [← pow_add]; congr 1; omega
      have he3 : q ^ (2 * (N + m + 1)) = X * Y ^ 2 := by
        dsimp only [X, Y]; rw [← pow_mul, ← pow_add]; congr 1; omega
      have he4 : q ^ (2 * (N + (m + 1) + 1)) = Q * X * Y ^ 2 := by
        dsimp only [X, Y, Q]; rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
      have he5 : q ^ (4 * N + 2) = Q * X ^ 2 * Y ^ 2 := by
        dsimp only [X, Y, Q]; rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
      have he6 : q ^ (4 * N + 4) = Q ^ 2 * X ^ 2 * Y ^ 2 := by
        dsimp only [X, Y, Q]; rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 1; omega
      have hm_exp : q ^ (2 * N + 1) * q ^ (m ^ 2) = Q * X * q ^ ((m + 1) ^ 2) := by
        dsimp only [X, Q]; rw [← pow_add, ← pow_add, ← pow_add]; congr 1
        have h1 : N = (N - (m + 1)) + (m + 1) := by omega
        calc
          2 * N + 1 + m ^ 2 = 2 * ((N - (m + 1)) + (m + 1)) + 1 + m ^ 2 := by rw [← h1]
          _ = 2 + 2 * (N - (m + 1)) + (m + 1) ^ 2 := by ring
      have hp_exp : q ^ (2 * N + 1) * q ^ ((m + 2) ^ 2) = Q * X * Y ^ 2 * q ^ ((m + 1) ^ 2) := by
        dsimp only [X, Y, Q]; rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
        congr 1
        have h1 : N = (N - (m + 1)) + (m + 1) := by omega
        calc
          2 * N + 1 + (m + 2) ^ 2 = 2 * ((N - (m + 1)) + (m + 1)) + 1 + (m + 2) ^ 2 := by rw [← h1]
          _ = 2 + 2 * (N - (m + 1)) + 2 * (m + 1) * 2 + (m + 1) ^ 2 := by ring
      rw [he1, he2, he3, he4, he5, he6]
      set P : ℝ := (1 - q ^ (2 * N + 2)) * jtpA q N (m + 2) * jtpB q N m
      calc
        (1 - q ^ (2 * N + 2)) *
            ((1 + Q * X ^ 2 * Y ^ 2) *
                ((1 - Q * X * Y ^ 2) * jtpA q N (m + 2) * (jtpB q N m * (1 - Q * X)) *
                  q ^ ((m + 1) ^ 2)) +
              q ^ (2 * N + 1) *
                ((1 - X * Y ^ 2) * ((1 - Q * X * Y ^ 2) * jtpA q N (m + 2)) * jtpB q N m *
                  q ^ (m ^ 2)) +
              q ^ (2 * N + 1) *
                (jtpA q N (m + 2) * (jtpB q N m * (1 - Q * X) * (1 - X)) * q ^ ((m + 2) ^ 2)))
            = P * ((1 + Q * X ^ 2 * Y ^ 2) * (1 - Q * X * Y ^ 2) * (1 - Q * X) * q ^ ((m + 1) ^ 2) +
                (1 - X * Y ^ 2) * (1 - Q * X * Y ^ 2) * (q ^ (2 * N + 1) * q ^ (m ^ 2)) +
                (1 - Q * X) * (1 - X) * (q ^ (2 * N + 1) * q ^ ((m + 2) ^ 2))) := by
              dsimp only [P]; ring
        _ = P * ((1 + Q * X ^ 2 * Y ^ 2) * (1 - Q * X * Y ^ 2) * (1 - Q * X) * q ^ ((m + 1) ^ 2) +
              (1 - X * Y ^ 2) * (1 - Q * X * Y ^ 2) * (Q * X * q ^ ((m + 1) ^ 2)) +
              (1 - Q * X) * (1 - X) * (Q * X * Y ^ 2 * q ^ ((m + 1) ^ 2))) := by
              rw [hm_exp, hp_exp]
        _ = jtpA q N (m + 2) * (1 - Q * X ^ 2 * Y ^ 2) * (1 - Q ^ 2 * X ^ 2 * Y ^ 2) *
              ((1 - q ^ (2 * N + 2)) * jtpB q N m) * q ^ ((m + 1) ^ 2) := by
              dsimp only [P]; ring

private lemma symTerm_mul_add_inv {z : ℝ} (hz : z ≠ 0) (k : ℕ) :
    (z + z⁻¹) * symTerm z (k + 1) =
      symTerm z (k + 2) + (if k = 0 then 2 else 1) * symTerm z k := by
  cases k with
  | zero =>
    simp only [symTerm, Nat.zero_add, pow_one, ↓reduceIte, mul_one]
    have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
    calc
      (z + z⁻¹) * (z + z⁻¹) = z ^ 2 + (z⁻¹) ^ 2 + 2 * (z * z⁻¹) := by ring
      _ = z ^ 2 + (z⁻¹) ^ 2 + 2 := by rw [hzz]; ring
  | succ j =>
    simp only [symTerm, Nat.succ_ne_zero, ↓reduceIte, one_mul]
    have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
    calc
      (z + z⁻¹) * (z ^ (j + 2) + (z⁻¹) ^ (j + 2))
          = (z ^ (j + 3) + (z⁻¹) ^ (j + 3)) +
              (z * z⁻¹) * (z ^ (j + 1) + (z⁻¹) ^ (j + 1)) := by
            rw [pow_succ, pow_succ, pow_succ, pow_succ]
            ring
      _ = (z ^ (j + 3) + (z⁻¹) ^ (j + 3)) + (z ^ (j + 1) + (z⁻¹) ^ (j + 1)) := by
            rw [hzz, one_mul]

private lemma sum_mul_add_inv {z : ℝ} (hz : z ≠ 0) (f : ℕ → ℝ) (N : ℕ)
    (hf1 : f (N + 1) = 0) (hf2 : f (N + 2) = 0) :
    (z + z⁻¹) * ∑ n ∈ Finset.range (N + 1), f n * symTerm z n =
      2 * f 1 * symTerm z 0 +
        ∑ m ∈ Finset.range (N + 1), (f m + f (m + 2)) * symTerm z (m + 1) := by
  rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
  have h0 : (z + z⁻¹) * (f 0 * symTerm z 0) = f 0 * symTerm z 1 := by
    simp only [symTerm, mul_one]
    ring
  rw [h0]
  have hsplit : ∑ k ∈ Finset.range N, (z + z⁻¹) * (f (k + 1) * symTerm z (k + 1)) =
      (∑ k ∈ Finset.range N, f (k + 1) * symTerm z (k + 2)) +
      (∑ k ∈ Finset.range N, f (k + 1) * ((if k = 0 then 2 else 1) * symTerm z k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    calc
      (z + z⁻¹) * (f (k + 1) * symTerm z (k + 1))
          = f (k + 1) * ((z + z⁻¹) * symTerm z (k + 1)) := by ring
      _ = f (k + 1) * (symTerm z (k + 2) + (if k = 0 then 2 else 1) * symTerm z k) := by
            rw [symTerm_mul_add_inv hz k]
      _ = f (k + 1) * symTerm z (k + 2) +
            f (k + 1) * ((if k = 0 then 2 else 1) * symTerm z k) := by ring
  rw [hsplit]
  have hup : (∑ k ∈ Finset.range N, f (k + 1) * symTerm z (k + 2)) + f 0 * symTerm z 1 =
      ∑ m ∈ Finset.range (N + 1), f m * symTerm z (m + 1) := by
    rw [Finset.sum_range_succ']
  have hdn : ∑ k ∈ Finset.range N, f (k + 1) * ((if k = 0 then 2 else 1) * symTerm z k) =
      2 * f 1 * symTerm z 0 + ∑ m ∈ Finset.range (N + 1), f (m + 2) * symTerm z (m + 1) := by
    cases N with
    | zero =>
      rw [Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have hf1' : f 1 = 0 := hf1
      have hf2' : f 2 = 0 := hf2
      rw [hf1', hf2']
      ring
    | succ M =>
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, Nat.succ_ne_zero, one_mul]
      rw [add_comm]
      congr 1
      · ring
      · rw [Finset.sum_range_succ, Finset.sum_range_succ, hf1, hf2, zero_mul, zero_mul,
          add_zero, add_zero]
  have hcomb : ∑ m ∈ Finset.range (N + 1), (f m + f (m + 2)) * symTerm z (m + 1) =
      (∑ m ∈ Finset.range (N + 1), f m * symTerm z (m + 1)) +
      (∑ m ∈ Finset.range (N + 1), f (m + 2) * symTerm z (m + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => by ring
  linarith

private lemma jtpProd_eq_sum {q z : ℝ} (hz : z ≠ 0) (N : ℕ) :
    jtpProd q z N = ∑ n ∈ Finset.range (N + 1), jtpCoeff q N n * symTerm z n * q ^ (n ^ 2) := by
  induction N with
  | zero =>
    simp [jtpProd, jtpCoeff, jtpA, jtpB, symTerm]
  | succ N ih =>
    have hstep : jtpProd q z (N + 1) =
        (1 - q ^ (2 * N + 2)) * ((1 + q ^ (4 * N + 2)) + q ^ (2 * N + 1) * (z + z⁻¹)) *
          jtpProd q z N := by
      dsimp only [jtpProd]
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
      have hfac : (1 + z * q ^ (2 * N + 1)) * (1 + z⁻¹ * q ^ (2 * N + 1)) =
          (1 + q ^ (4 * N + 2)) + q ^ (2 * N + 1) * (z + z⁻¹) := by
        have hq : q ^ (2 * N + 1) * q ^ (2 * N + 1) = q ^ (4 * N + 2) := by
          rw [← pow_add]; congr 1; omega
        calc
          (1 + z * q ^ (2 * N + 1)) * (1 + z⁻¹ * q ^ (2 * N + 1))
              = 1 + (z * z⁻¹) * (q ^ (2 * N + 1) * q ^ (2 * N + 1)) +
                  q ^ (2 * N + 1) * (z + z⁻¹) := by ring
          _ = (1 + q ^ (4 * N + 2)) + q ^ (2 * N + 1) * (z + z⁻¹) := by rw [hzz, hq]; ring
      have h2n : 2 * (N + 1) = 2 * N + 2 := by omega
      rw [hfac, h2n]
      ring
    set f : ℕ → ℝ := fun n => jtpCoeff q N n * q ^ (n ^ 2)
    have hf1 : f (N + 1) = 0 := by simp [f, jtpCoeff]
    have hf2 : f (N + 2) = 0 := by simp [f, jtpCoeff]
    have hih : jtpProd q z N = ∑ n ∈ Finset.range (N + 1), f n * symTerm z n := by
      rw [ih]
      refine Finset.sum_congr rfl fun n _ => by dsimp only [f]; ring
    have hS1 : (1 + q ^ (4 * N + 2)) * ∑ n ∈ Finset.range (N + 1), f n * symTerm z n =
        (1 + q ^ (4 * N + 2)) * f 0 * symTerm z 0 +
          ∑ m ∈ Finset.range (N + 1), (1 + q ^ (4 * N + 2)) * f (m + 1) * symTerm z (m + 1) := by
      have hext : ∑ n ∈ Finset.range (N + 1), f n * symTerm z n =
          ∑ n ∈ Finset.range (N + 2), f n * symTerm z n := by
        symm
        rw [Finset.sum_range_succ, hf1, zero_mul, add_zero]
      rw [hext, Finset.sum_range_succ', mul_add, Finset.mul_sum, add_comm]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun m _ => by ring
    have hS2 := sum_mul_add_inv hz f N hf1 hf2
    rw [hstep, hih]
    have hexpand :
        (1 - q ^ (2 * N + 2)) * ((1 + q ^ (4 * N + 2)) + q ^ (2 * N + 1) * (z + z⁻¹)) *
            ∑ n ∈ Finset.range (N + 1), f n * symTerm z n =
          (1 - q ^ (2 * N + 2)) * ((1 + q ^ (4 * N + 2)) * f 0 + 2 * q ^ (2 * N + 1) * f 1) *
              symTerm z 0 +
            ∑ m ∈ Finset.range (N + 1),
              (1 - q ^ (2 * N + 2)) *
                ((1 + q ^ (4 * N + 2)) * f (m + 1) + q ^ (2 * N + 1) * f m +
                  q ^ (2 * N + 1) * f (m + 2)) * symTerm z (m + 1) := by
      calc
        (1 - q ^ (2 * N + 2)) * ((1 + q ^ (4 * N + 2)) + q ^ (2 * N + 1) * (z + z⁻¹)) *
              ∑ n ∈ Finset.range (N + 1), f n * symTerm z n
            = (1 - q ^ (2 * N + 2)) *
                ((1 + q ^ (4 * N + 2)) * ∑ n ∈ Finset.range (N + 1), f n * symTerm z n +
                  q ^ (2 * N + 1) *
                    ((z + z⁻¹) * ∑ n ∈ Finset.range (N + 1), f n * symTerm z n)) := by ring
        _ = (1 - q ^ (2 * N + 2)) *
              ((1 + q ^ (4 * N + 2)) * f 0 * symTerm z 0 +
                  ∑ m ∈ Finset.range (N + 1),
                    (1 + q ^ (4 * N + 2)) * f (m + 1) * symTerm z (m + 1) +
                q ^ (2 * N + 1) *
                  (2 * f 1 * symTerm z 0 +
                    ∑ m ∈ Finset.range (N + 1), (f m + f (m + 2)) * symTerm z (m + 1))) := by
              rw [hS1, hS2]
        _ = (1 - q ^ (2 * N + 2)) * ((1 + q ^ (4 * N + 2)) * f 0 + 2 * q ^ (2 * N + 1) * f 1) *
                symTerm z 0 +
              ((1 - q ^ (2 * N + 2)) *
                ∑ m ∈ Finset.range (N + 1), (1 + q ^ (4 * N + 2)) * f (m + 1) * symTerm z (m + 1) +
               (1 - q ^ (2 * N + 2)) * q ^ (2 * N + 1) *
                ∑ m ∈ Finset.range (N + 1), (f m + f (m + 2)) * symTerm z (m + 1)) := by ring
        _ = (1 - q ^ (2 * N + 2)) * ((1 + q ^ (4 * N + 2)) * f 0 + 2 * q ^ (2 * N + 1) * f 1) *
                symTerm z 0 +
              ∑ m ∈ Finset.range (N + 1),
                (1 - q ^ (2 * N + 2)) *
                  ((1 + q ^ (4 * N + 2)) * f (m + 1) + q ^ (2 * N + 1) * f m +
                    q ^ (2 * N + 1) * f (m + 2)) * symTerm z (m + 1) := by
              congr 1
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun m _ => by ring
    rw [hexpand]
    conv_rhs => rw [Finset.sum_range_succ', add_comm]
    congr 1
    · have h0 := jtpCoeff_step_zero q N
      dsimp only [f]
      rw [h0]
      ring
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hmle : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hp := jtpCoeff_step_pos q N m hmle
      dsimp only [f]
      rw [hp]
      ring

private lemma one_sub_sum_le_prod (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hih := ih hfs
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1a : 0 ≤ 1 - f a := by linarith
    have hs0 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg fun i hi => (hfs i hi).1
    nlinarith

private lemma prod_one_sub_le_one (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    ∏ i ∈ s, (1 - f i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hih := ih hfs
    have hnn : 0 ≤ ∏ i ∈ s, (1 - f i) := Finset.prod_nonneg fun i hi => by linarith [(hfs i hi).2]
    rw [Finset.prod_insert ha]
    nlinarith

private lemma jtpCoeff_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (N n : ℕ) :
    0 ≤ jtpCoeff q N n ∧ jtpCoeff q N n ≤ 1 := by
  dsimp only [jtpCoeff]
  split_ifs with h
  · have hA0 : 0 ≤ jtpA q N n := Finset.prod_nonneg fun j _ => by
      have hle : q ^ (2 * (N + n + 1 + j)) ≤ 1 := pow_le_one₀ hq0.le hq1.le
      linarith
    have hA1 : jtpA q N n ≤ 1 := prod_one_sub_le_one _ _ fun j _ =>
      ⟨by positivity, pow_le_one₀ hq0.le hq1.le⟩
    have hB0 : 0 ≤ jtpB q N n := Finset.prod_nonneg fun j _ => by
      have hle : q ^ (2 * (N - j)) ≤ 1 := pow_le_one₀ hq0.le hq1.le
      linarith
    have hB1 : jtpB q N n ≤ 1 := prod_one_sub_le_one _ _ fun j _ =>
      ⟨by positivity, pow_le_one₀ hq0.le hq1.le⟩
    exact ⟨mul_nonneg hA0 hB0, by nlinarith⟩
  · exact ⟨le_rfl, by norm_num⟩

private lemma tendsto_jtpCoeff {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    Filter.Tendsto (fun N : ℕ => jtpCoeff q N n) Filter.atTop (nhds 1) := by
  have hq2_0 : 0 ≤ q ^ 2 := by positivity
  have hq2_1 : q ^ 2 < 1 := by nlinarith
  have hA : Filter.Tendsto (fun N : ℕ => jtpA q N n) Filter.atTop (nhds 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun N : ℕ => 1 - (q ^ 2) ^ N / (1 - q ^ 2))
      (h := fun _ => (1 : ℝ)) ?_ tendsto_const_nhds ?_ ?_
    · simpa only [zero_div, sub_zero] using
        tendsto_const_nhds.sub
          ((tendsto_pow_atTop_nhds_zero_of_lt_one hq2_0 hq2_1).div_const (1 - q ^ 2))
    · refine Filter.Eventually.of_forall fun N => ?_
      have hbern := one_sub_sum_le_prod (Finset.range (N - n))
        (fun j => q ^ (2 * (N + n + 1 + j)))
        (fun j _ => ⟨by positivity, pow_le_one₀ hq0.le hq1.le⟩)
      have hsum : ∑ j ∈ Finset.range (N - n), q ^ (2 * (N + n + 1 + j)) ≤
          (q ^ 2) ^ N / (1 - q ^ 2) := by
        calc
          ∑ j ∈ Finset.range (N - n), q ^ (2 * (N + n + 1 + j))
              ≤ ∑ j ∈ Finset.range (N - n), (q ^ 2) ^ N * (q ^ 2) ^ j := by
                refine Finset.sum_le_sum fun j _ => ?_
                rw [← pow_add, ← pow_mul]
                exact pow_le_pow_of_le_one hq0.le hq1.le (by omega)
          _ = (q ^ 2) ^ N * ∑ j ∈ Finset.range (N - n), (q ^ 2) ^ j := by
                rw [← Finset.mul_sum]
          _ ≤ (q ^ 2) ^ N * (∑' j : ℕ, (q ^ 2) ^ j) := by
                exact mul_le_mul_of_nonneg_left
                  ((summable_geometric_of_lt_one hq2_0 hq2_1).sum_le_tsum _
                    (fun _ _ => by positivity)) (by positivity)
          _ = (q ^ 2) ^ N / (1 - q ^ 2) := by
                rw [tsum_geometric_of_lt_one hq2_0 hq2_1, div_eq_mul_inv]
      dsimp only [jtpA]
      linarith
    · refine Filter.Eventually.of_forall fun N => ?_
      exact prod_one_sub_le_one _ _ fun j _ => ⟨by positivity, pow_le_one₀ hq0.le hq1.le⟩
  have hB : Filter.Tendsto (fun N : ℕ => jtpB q N n) Filter.atTop (nhds 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun N : ℕ => 1 - (n : ℝ) * (q ^ 2) ^ (N - n))
      (h := fun _ => (1 : ℝ)) ?_ tendsto_const_nhds ?_ ?_
    · have hshift : Filter.Tendsto (fun N : ℕ => (q ^ 2) ^ (N - n)) Filter.atTop (nhds 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq2_0 hq2_1).comp
          (Filter.tendsto_sub_atTop_nat n)
      simpa only [mul_zero, sub_zero] using
        tendsto_const_nhds.sub (hshift.const_mul (n : ℝ))
    · refine Filter.eventually_atTop.mpr ⟨n, fun N hN => ?_⟩
      have hbern := one_sub_sum_le_prod (Finset.range n)
        (fun j => q ^ (2 * (N - j)))
        (fun j _ => ⟨by positivity, pow_le_one₀ hq0.le hq1.le⟩)
      have hsum : ∑ j ∈ Finset.range n, q ^ (2 * (N - j)) ≤ (n : ℝ) * (q ^ 2) ^ (N - n) := by
        calc
          ∑ j ∈ Finset.range n, q ^ (2 * (N - j))
              ≤ ∑ _j ∈ Finset.range n, (q ^ 2) ^ (N - n) := by
                refine Finset.sum_le_sum fun j hj => ?_
                have hjn : j < n := Finset.mem_range.mp hj
                rw [← pow_mul]
                exact pow_le_pow_of_le_one hq0.le hq1.le (by omega)
          _ = (n : ℝ) * (q ^ 2) ^ (N - n) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp only [jtpB]
      linarith
    · refine Filter.Eventually.of_forall fun N => ?_
      exact prod_one_sub_le_one _ _ fun j _ => ⟨by positivity, pow_le_one₀ hq0.le hq1.le⟩
  have hmul : Filter.Tendsto (fun N : ℕ => jtpA q N n * jtpB q N n) Filter.atTop (nhds 1) := by
    simpa only [mul_one] using hA.mul hB
  refine hmul.congr' (Filter.eventually_atTop.mpr ⟨n, fun N hN => ?_⟩)
  simp only [jtpCoeff, hN, ↓reduceIte]

private lemma summable_symTerm_mul_pow_sq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (z : ℝ) :
    Summable fun n : ℕ => |symTerm z n| * q ^ (n ^ 2) := by
  let M : ℝ := max |z| |z⁻¹| + 1
  have hM1 : 1 ≤ M := by
    dsimp only [M]
    linarith [le_max_left |z| |z⁻¹|, abs_nonneg z]
  have hM0 : 0 < M := by linarith
  have hbound : ∀ n : ℕ, |symTerm z n| ≤ 2 * M ^ n := by
    intro n
    cases n with
    | zero => simp [symTerm]
    | succ k =>
      dsimp only [symTerm]
      have h1 : |z| ≤ M := by dsimp only [M]; linarith [le_max_left |z| |z⁻¹|]
      have h2 : |z⁻¹| ≤ M := by dsimp only [M]; linarith [le_max_right |z| |z⁻¹|]
      calc
        |z ^ (k + 1) + (z⁻¹) ^ (k + 1)| ≤ |z ^ (k + 1)| + |(z⁻¹) ^ (k + 1)| := abs_add_le _ _
        _ = |z| ^ (k + 1) + |z⁻¹| ^ (k + 1) := by rw [abs_pow, abs_pow]
        _ ≤ M ^ (k + 1) + M ^ (k + 1) := by
              exact add_le_add (pow_le_pow_left₀ (abs_nonneg _) h1 _)
                (pow_le_pow_left₀ (abs_nonneg _) h2 _)
        _ = 2 * M ^ (k + 1) := by ring
  have ht : Filter.Tendsto (fun n : ℕ => M * q ^ n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul M
  rw [Metric.tendsto_atTop] at ht
  rcases ht (1 / 2) (by norm_num) with ⟨N0, hN0⟩
  rw [← summable_nat_add_iff N0]
  have hgeom : Summable fun k : ℕ => 2 * (1 / 2 : ℝ) ^ (k + N0) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective N0)).mul_left 2
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hgeom
  have hk := hN0 (k + N0) (Nat.le_add_left N0 k)
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hk
  calc
    |symTerm z (k + N0)| * q ^ ((k + N0) ^ 2)
        ≤ 2 * M ^ (k + N0) * q ^ ((k + N0) ^ 2) :=
          mul_le_mul_of_nonneg_right (hbound (k + N0)) (by positivity)
    _ = 2 * (M * q ^ (k + N0)) ^ (k + N0) := by
          rw [mul_pow, ← pow_mul, sq]
          ring
    _ ≤ 2 * (1 / 2 : ℝ) ^ (k + N0) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hk.le _) (by norm_num)

private lemma jtp_tendsto {q z : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hz : z ≠ 0) :
    Filter.Tendsto (jtpProd q z) Filter.atTop
      (nhds (∑' n : ℕ, symTerm z n * q ^ (n ^ 2))) := by
  have heq : jtpProd q z = fun N : ℕ => ∑' n : ℕ, jtpCoeff q N n * symTerm z n * q ^ (n ^ 2) := by
    ext N
    rw [jtpProd_eq_sum hz N]
    refine (tsum_eq_sum (s := Finset.range (N + 1)) fun n hn => ?_).symm
    have hgt : ¬ (n ≤ N) := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    simp only [jtpCoeff, hgt, ↓reduceIte, zero_mul]
  rw [heq]
  refine tendsto_tsum_of_dominated_convergence (summable_symTerm_mul_pow_sq hq0 hq1 z)
    (fun n => ?_) (Filter.Eventually.of_forall fun N n => ?_)
  · simpa only [one_mul] using
      ((tendsto_jtpCoeff hq0 hq1 n).mul_const (symTerm z n)).mul_const (q ^ (n ^ 2))
  · have hb := jtpCoeff_bounds hq0 hq1 N n
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_pos (pow_pos hq0 _)]
    have hnn : 0 ≤ |symTerm z n| * q ^ (n ^ 2) := by positivity
    calc
      jtpCoeff q N n * |symTerm z n| * q ^ (n ^ 2)
          = jtpCoeff q N n * (|symTerm z n| * q ^ (n ^ 2)) := by ring
      _ ≤ 1 * (|symTerm z n| * q ^ (n ^ 2)) := mul_le_mul_of_nonneg_right hb.2 hnn
      _ = |symTerm z n| * q ^ (n ^ 2) := one_mul _

/-!
Part 4: Euler Pentagonal Formula, Product Identities, and Final Evaluation
-/

private def phiProd (q : ℝ) (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, (1 - q ^ (k + 1))

private noncomputable def phiLim (q : ℝ) : ℝ :=
  ⨅ N : ℕ, phiProd q N

private lemma phiProd_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
    0 ≤ phiProd q N := by
  refine Finset.prod_nonneg fun k _ => ?_
  linarith [pow_le_one₀ hq0 hq1 (n := k + 1)]

private lemma phiProd_antitone {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Antitone (phiProd q) := by
  refine antitone_nat_of_succ_le fun N => ?_
  dsimp only [phiProd]
  rw [Finset.prod_range_succ]
  have h0 : 0 ≤ phiProd q N := phiProd_nonneg hq0 hq1 N
  have h1 : 1 - q ^ (N + 1) ≤ 1 := by linarith [pow_nonneg hq0 (N + 1)]
  dsimp only [phiProd] at h0
  nlinarith

private lemma tendsto_phiProd {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Filter.Tendsto (phiProd q) Filter.atTop (nhds (phiLim q)) :=
  tendsto_atTop_ciInf (phiProd_antitone hq0 hq1) ⟨0, by rintro _ ⟨N, rfl⟩; exact phiProd_nonneg hq0 hq1 N⟩

private lemma phiLim_pos {q : ℝ} (hq0 : 0 < q) (hqhalf : q < 1 / 2) :
    0 < phiLim q := by
  have hq1 : q < 1 := by linarith
  have hlow : ∀ N : ℕ, 1 - q / (1 - q) ≤ phiProd q N := by
    intro N
    have hbern := one_sub_sum_le_prod (Finset.range N) (fun k => q ^ (k + 1))
      (fun k _ => ⟨by positivity, pow_le_one₀ hq0.le hq1.le⟩)
    have hsum : ∑ k ∈ Finset.range N, q ^ (k + 1) ≤ q / (1 - q) := by
      calc
        ∑ k ∈ Finset.range N, q ^ (k + 1)
            = q * ∑ k ∈ Finset.range N, q ^ k := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => by rw [pow_succ']
        _ ≤ q * ∑' k : ℕ, q ^ k :=
              mul_le_mul_of_nonneg_left
                ((summable_geometric_of_lt_one hq0.le hq1).sum_le_tsum _ (fun _ _ => by positivity))
                hq0.le
        _ = q / (1 - q) := by
              rw [tsum_geometric_of_lt_one hq0.le hq1, div_eq_mul_inv]
    dsimp only [phiProd]
    linarith
  have hle : 1 - q / (1 - q) ≤ phiLim q :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_phiProd hq0.le hq1.le)
      (Filter.Eventually.of_forall hlow)
  have hpos : 0 < 1 - q / (1 - q) := by
    have hdiv : q / (1 - q) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  linarith

private lemma phiProd_two_mul (q : ℝ) (N : ℕ) :
    phiProd q (2 * N) = (∏ k ∈ Finset.range N, (1 - q ^ (2 * k + 1))) * phiProd (q ^ 2) N := by
  induction N with
  | zero => simp [phiProd]
  | succ N ih =>
    have h2 : 2 * (N + 1) = 2 * N + 2 := by omega
    dsimp only [phiProd] at ih ⊢
    rw [h2, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, Finset.prod_range_succ]
    have hp : (q ^ 2) ^ (N + 1) = q ^ (2 * N + 2) := by
      have he : 2 * (N + 1) = 2 * N + 2 := by omega
      rw [← pow_mul, he]
    rw [hp]
    ring

private lemma jtpProd_pent_eq {c : ℝ} (N : ℕ) :
    jtpProd (Real.exp (-(3 / 2) * c)) (-Real.exp (c / 2)) N = phiProd (Real.exp (-c)) (3 * N) := by
  induction N with
  | zero => simp [jtpProd, phiProd]
  | succ N ih =>
    dsimp only [jtpProd, phiProd] at ih ⊢
    have h3 : 3 * (N + 1) = 3 * N + 3 := by omega
    rw [h3, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ]
    have hf1 : (Real.exp (-(3 / 2) * c)) ^ (2 * (N + 1)) = (Real.exp (-c)) ^ (3 * N + 3) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hf2 : -Real.exp (c / 2) * (Real.exp (-(3 / 2) * c)) ^ (2 * N + 1) =
        -((Real.exp (-c)) ^ (3 * N + 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, neg_mul, ← Real.exp_add]
      congr 2; push_cast; ring
    have hf3 : (-Real.exp (c / 2))⁻¹ * (Real.exp (-(3 / 2) * c)) ^ (2 * N + 1) =
        -((Real.exp (-c)) ^ (3 * N + 2)) := by
      rw [inv_neg, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul, neg_mul, ← Real.exp_add]
      congr 2; push_cast; ring
    rw [hf1, hf2, hf3]
    calc
      (∏ j ∈ Finset.range N, (1 - Real.exp (-(3 / 2) * c) ^ (2 * (j + 1)))) *
          (1 - Real.exp (-c) ^ (3 * N + 3)) *
          ((∏ k ∈ Finset.range N,
              (1 + -Real.exp (c / 2) * Real.exp (-(3 / 2) * c) ^ (2 * k + 1)) *
                (1 + (-Real.exp (c / 2))⁻¹ * Real.exp (-(3 / 2) * c) ^ (2 * k + 1))) *
            ((1 + -Real.exp (-c) ^ (3 * N + 1)) * (1 + -Real.exp (-c) ^ (3 * N + 2))))
          = ((∏ j ∈ Finset.range N, (1 - Real.exp (-(3 / 2) * c) ^ (2 * (j + 1)))) *
              (∏ k ∈ Finset.range N,
                (1 + -Real.exp (c / 2) * Real.exp (-(3 / 2) * c) ^ (2 * k + 1)) *
                  (1 + (-Real.exp (c / 2))⁻¹ * Real.exp (-(3 / 2) * c) ^ (2 * k + 1)))) *
            (1 - Real.exp (-c) ^ (3 * N + 1)) *
            (1 - Real.exp (-c) ^ (3 * N + 2)) *
            (1 - Real.exp (-c) ^ (3 * N + 3)) := by ring
      _ = (∏ k ∈ Finset.range (3 * N), (1 - Real.exp (-c) ^ (k + 1))) *
            (1 - Real.exp (-c) ^ (3 * N + 1)) *
            (1 - Real.exp (-c) ^ (3 * N + 2)) *
            (1 - Real.exp (-c) ^ (3 * N + 3)) := by rw [ih]

private def pent (m : ℤ) : ℕ :=
  (m * (3 * m - 1) / 2).natAbs

private lemma two_mul_pent (m : ℤ) : 2 * (pent m : ℤ) = m * (3 * m - 1) := by
  have hnonneg : 0 ≤ m * (3 * m - 1) := by
    rcases le_or_gt m 0 with hm | hm
    · nlinarith
    · have hm1 : 1 ≤ m := by omega
      nlinarith
  have hdvd : 2 ∣ m * (3 * m - 1) := by
    rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨k * (3 * m - 1), ?_⟩; rw [hk]; ring
    · refine ⟨m * (3 * k + 1), ?_⟩; rw [hk]; ring
  have hdiv_nonneg : 0 ≤ m * (3 * m - 1) / 2 := Int.ediv_nonneg hnonneg (by norm_num)
  dsimp only [pent]
  rw [Int.natAbs_of_nonneg hdiv_nonneg]
  exact Int.mul_ediv_cancel' hdvd

private lemma pent_injective : Function.Injective pent := by
  intro m₁ m₂ h
  have h1 := two_mul_pent m₁
  have h2 := two_mul_pent m₂
  have heq : m₁ * (3 * m₁ - 1) = m₂ * (3 * m₂ - 1) := by
    rw [← h1, ← h2, h]
  have hfac : (m₁ - m₂) * (3 * (m₁ + m₂) - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with hsub | hmod
  · omega
  · omega

private lemma a_pent (m : ℤ) : a (pent m) = (-1 : ℝ) ^ m.natAbs := by
  dsimp only [a]
  split_ifs with hex
  · have hch : Classical.choose hex = m := by
      have h1 := Classical.choose_spec hex
      have h2 := two_mul_pent m
      have heq : Classical.choose hex * (3 * Classical.choose hex - 1) = m * (3 * m - 1) := by
        linarith
      have hfac : (Classical.choose hex - m) * (3 * (Classical.choose hex + m) - 1) = 0 := by
        linarith
      rcases mul_eq_zero.mp hfac with hsub | hmod
      · omega
      · omega
    rw [hch]
  · exact absurd ⟨m, two_mul_pent m⟩ hex

private lemma a_eq_zero_of_not_mem_range {k : ℕ} (hk : k ∉ Set.range pent) : a k = 0 := by
  dsimp only [a]
  split_ifs with hex
  · exfalso
    rcases hex with ⟨m, hm⟩
    apply hk
    refine ⟨m, ?_⟩
    have h2 := two_mul_pent m
    omega
  · rfl

private lemma tsum_a_eq_pent_tsum :
    (∑' k : ℕ, a k / Real.exp ((k : ℝ) * Real.pi)) =
      ∑' n : ℕ, symTerm (-Real.exp (Real.pi / 2)) n *
        (Real.exp (-(3 / 2) * Real.pi)) ^ (n ^ 2) := by
  have hs_sym : Summable fun n : ℕ =>
      symTerm (-Real.exp (Real.pi / 2)) n * (Real.exp (-(3 / 2) * Real.pi)) ^ (n ^ 2) := by
    have hq0 : 0 < Real.exp (-(3 / 2) * Real.pi) := Real.exp_pos _
    have hq1 : Real.exp (-(3 / 2) * Real.pi) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    refine ((summable_symTerm_mul_pow_sq hq0 hq1 (-Real.exp (Real.pi / 2))).congr fun n => ?_).of_norm
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hq0 _)]
  have hbij : (∑' k : ℕ, a k / Real.exp ((k : ℝ) * Real.pi)) =
      ∑' m : ℤ, (-1 : ℝ) ^ m.natAbs * Real.exp (-((pent m : ℝ) * Real.pi)) := by
    refine tsum_eq_tsum_of_ne_zero_bij
      (f := fun k : ℕ => a k / Real.exp ((k : ℝ) * Real.pi))
      (g := fun m : ℤ => (-1 : ℝ) ^ m.natAbs * Real.exp (-((pent m : ℝ) * Real.pi)))
      (i := fun m => pent m.1) ?_ ?_ ?_
    · rintro ⟨m₁, _⟩ ⟨m₂, _⟩ h
      exact Subtype.ext (pent_injective h)
    · intro k hk
      by_cases hmem : k ∈ Set.range pent
      · rcases hmem with ⟨m, rfl⟩
        refine ⟨⟨m, ?_⟩, rfl⟩
        rw [Function.mem_support]
        have hne : (-1 : ℝ) ^ m.natAbs ≠ 0 := pow_ne_zero _ (by norm_num)
        exact mul_ne_zero hne (Real.exp_pos _).ne'
      · exfalso
        rw [Function.mem_support] at hk
        rw [a_eq_zero_of_not_mem_range hmem, zero_div] at hk
        exact hk rfl
    · rintro ⟨m, _⟩
      rw [a_pent m, div_eq_mul_inv, ← Real.exp_neg]
  rw [hbij]
  have hs_int : Summable fun m : ℤ =>
      (-1 : ℝ) ^ m.natAbs * Real.exp (-((pent m : ℝ) * Real.pi)) := by
    have hpos : Summable fun m : ℤ => Real.exp (-((pent m : ℝ) * Real.pi)) := by
      have hdom := summable_th3 (by linarith [Real.pi_pos] : 0 < Real.pi / 2)
      have hle : ∀ m : ℤ, Real.exp (-((pent m : ℝ) * Real.pi)) ≤
          Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2) * (m : ℝ) ^ 2) := by
        intro m
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h2p : 2 * (pent m : ℝ) = (m : ℝ) * (3 * (m : ℝ) - 1) := by
          exact_mod_cast two_mul_pent m
        have hsq : 0 ≤ (m : ℝ) ^ 2 - (m : ℝ) + 1 / 2 := by
          nlinarith [sq_nonneg ((m : ℝ) - 1 / 2)]
        nlinarith [Real.pi_pos]
      exact Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hle
        (hdom.mul_left (Real.exp (Real.pi / 2)))
    refine (hpos.congr fun m => ?_).of_norm
    rw [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul, abs_of_pos (Real.exp_pos _)]
  rw [tsum_int_split_zero hs_int, hs_sym.tsum_eq_zero_add]
  have h0 : (-1 : ℝ) ^ (0 : ℤ).natAbs * Real.exp (-((pent 0 : ℝ) * Real.pi)) = 1 := by
    simp [pent]
  have hsym0 : symTerm (-Real.exp (Real.pi / 2)) 0 * (Real.exp (-(3 / 2) * Real.pi)) ^ (0 ^ 2) = 1 := by
    simp [symTerm]
  rw [h0, hsym0]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [symTerm]
  have hp_pos : (pent ((n : ℤ) + 1) : ℝ) = ((n + 1 : ℕ) : ℝ) * (3 * ((n + 1 : ℕ) : ℝ) - 1) / 2 := by
    have h := two_mul_pent ((n : ℤ) + 1)
    have hr : 2 * (pent ((n : ℤ) + 1) : ℝ) = ((n : ℝ) + 1) * (3 * ((n : ℝ) + 1) - 1) := by
      exact_mod_cast h
    push_cast
    linarith
  have hp_neg : (pent (-((n : ℤ) + 1)) : ℝ) = ((n + 1 : ℕ) : ℝ) * (3 * ((n + 1 : ℕ) : ℝ) + 1) / 2 := by
    have h := two_mul_pent (-((n : ℤ) + 1))
    have hr : 2 * (pent (-((n : ℤ) + 1)) : ℝ) = (-((n : ℝ) + 1)) * (3 * (-((n : ℝ) + 1)) - 1) := by
      exact_mod_cast h
    push_cast
    linarith
  have hna1 : ((n : ℤ) + 1).natAbs = n + 1 := by omega
  have hna2 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
  rw [hna1, hna2, hp_pos, hp_neg, add_mul]
  have ht1 : (-Real.exp (Real.pi / 2)) ^ (n + 1) * (Real.exp (-(3 / 2) * Real.pi)) ^ ((n + 1) ^ 2) =
      (-1 : ℝ) ^ (n + 1) * Real.exp (-(((n + 1 : ℕ) : ℝ) * (3 * ((n + 1 : ℕ) : ℝ) - 1) / 2 * Real.pi)) := by
    rw [neg_eq_neg_one_mul, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2; push_cast; ring
  have ht2 : ((-Real.exp (Real.pi / 2))⁻¹) ^ (n + 1) * (Real.exp (-(3 / 2) * Real.pi)) ^ ((n + 1) ^ 2) =
      (-1 : ℝ) ^ (n + 1) * Real.exp (-(((n + 1 : ℕ) : ℝ) * (3 * ((n + 1 : ℕ) : ℝ) + 1) / 2 * Real.pi)) := by
    rw [inv_neg, ← Real.exp_neg, neg_eq_neg_one_mul, mul_pow, ← Real.exp_nat_mul,
      ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2; push_cast; ring
  rw [ht1, ht2]

private lemma phiLim_qVal_eq_tsum :
    phiLim qVal = ∑' k : ℕ, a k / Real.exp ((k : ℝ) * Real.pi) := by
  have hq0 : 0 < Real.exp (-(3 / 2) * Real.pi) := Real.exp_pos _
  have hq1 : Real.exp (-(3 / 2) * Real.pi) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hz : -Real.exp (Real.pi / 2) ≠ 0 := neg_ne_zero.mpr (Real.exp_pos _).ne'
  have ht1 := jtp_tendsto hq0 hq1 hz
  have heq : jtpProd (Real.exp (-(3 / 2) * Real.pi)) (-Real.exp (Real.pi / 2)) =
      fun N => phiProd qVal (3 * N) := by
    ext N
    exact jtpProd_pent_eq (c := Real.pi) N
  rw [heq, ← tsum_a_eq_pent_tsum] at ht1
  have hqv0 : 0 ≤ qVal := (Real.exp_pos _).le
  have hqv1 : qVal ≤ 1 := (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])).le
  have hsub : Filter.Tendsto (fun N : ℕ => 3 * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => by omega : ∀ N, N ≤ 3 * N) Filter.tendsto_id
  have ht2 := (tendsto_phiProd hqv0 hqv1).comp hsub
  exact tendsto_nhds_unique ht2 ht1

private lemma symTerm_tsum_one {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, symTerm 1 n * (Real.exp (-c)) ^ (n ^ 2)) = th3 c := by
  have hq0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hq1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : Summable fun n : ℕ => symTerm 1 n * (Real.exp (-c)) ^ (n ^ 2) := by
    refine ((summable_symTerm_mul_pow_sq hq0 hq1 1).congr fun n => ?_).of_norm
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hq0 _)]
  rw [hs.tsum_eq_zero_add, th3_split_zero hc, ← tsum_mul_left]
  have h0 : symTerm 1 0 * (Real.exp (-c)) ^ (0 ^ 2) = 1 := by simp [symTerm]
  rw [h0]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [symTerm, one_pow, inv_one, ← Real.exp_nat_mul]
  have hexp : (((n + 1) ^ 2 : ℕ) : ℝ) * (-c) = -c * ((n + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
  rw [hexp]
  ring

private lemma symTerm_tsum_neg_one {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, symTerm (-1) n * (Real.exp (-c)) ^ (n ^ 2)) = th4 c := by
  have hq0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hq1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : Summable fun n : ℕ => symTerm (-1) n * (Real.exp (-c)) ^ (n ^ 2) := by
    refine ((summable_symTerm_mul_pow_sq hq0 hq1 (-1)).congr fun n => ?_).of_norm
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hq0 _)]
  rw [hs.tsum_eq_zero_add, th4_split_zero hc, ← tsum_mul_left]
  have h0 : symTerm (-1) 0 * (Real.exp (-c)) ^ (0 ^ 2) = 1 := by simp [symTerm]
  rw [h0]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [symTerm, inv_neg, inv_one, ← Real.exp_nat_mul]
  have hexp : (((n + 1) ^ 2 : ℕ) : ℝ) * (-c) = -c * ((n + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
  rw [hexp]
  ring

private lemma symTerm_tsum_q {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, symTerm (Real.exp (-c)) n * (Real.exp (-c)) ^ (n ^ 2)) =
      Real.exp (c / 4) * th2 c := by
  have hq0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hq1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs_sym : Summable fun n : ℕ => symTerm (Real.exp (-c)) n * (Real.exp (-c)) ^ (n ^ 2) := by
    refine ((summable_symTerm_mul_pow_sq hq0 hq1 (Real.exp (-c))).congr fun n => ?_).of_norm
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hq0 _)]
  have hrhs : Real.exp (c / 4) * th2 c =
      ∑' m : ℤ, Real.exp (-c * ((m : ℝ) ^ 2 + (m : ℝ))) := by
    rw [th2, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hrhs]
  have hs_int : Summable fun m : ℤ => Real.exp (-c * ((m : ℝ) ^ 2 + (m : ℝ))) := by
    refine ((summable_th2 hc).mul_left (Real.exp (c / 4))).congr fun m => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  rw [tsum_int_split_zero hs_int, hs_sym.tsum_eq_zero_add]
  have h0 : Real.exp (-c * (((0 : ℤ) : ℝ) ^ 2 + ((0 : ℤ) : ℝ))) = 1 := by simp
  have hsym0 : symTerm (Real.exp (-c)) 0 * (Real.exp (-c)) ^ (0 ^ 2) = 1 := by simp [symTerm]
  rw [h0, hsym0]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [symTerm, add_mul, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring

private lemma phiLim_sq_eq {c : ℝ} (hc : 0 < c) :
    phiLim (Real.exp (-c)) ^ 2 = phiLim (Real.exp (-c) ^ 2) * th4 c := by
  set q : ℝ := Real.exp (-c)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hfin : ∀ N : ℕ, phiProd q (2 * N) ^ 2 = phiProd (q ^ 2) N * jtpProd q (-1) N := by
    intro N
    rw [phiProd_two_mul q N]
    dsimp only [jtpProd, phiProd]
    have h1 : ∏ j ∈ Finset.range N, (1 - q ^ (2 * (j + 1))) =
        ∏ k ∈ Finset.range N, (1 - (q ^ 2) ^ (k + 1)) := by
      refine Finset.prod_congr rfl fun k _ => by rw [← pow_mul]
    have h2 : ∏ k ∈ Finset.range N,
        (1 + (-1 : ℝ) * q ^ (2 * k + 1)) * (1 + (-1 : ℝ)⁻¹ * q ^ (2 * k + 1)) =
        (∏ k ∈ Finset.range N, (1 - q ^ (2 * k + 1))) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun k _ => by norm_num; ring
    rw [h1, h2]
    ring
  have hsub : Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => by omega : ∀ N, N ≤ 2 * N) Filter.tendsto_id
  have htL : Filter.Tendsto (fun N : ℕ => phiProd q (2 * N) ^ 2) Filter.atTop (nhds (phiLim q ^ 2)) :=
    ((tendsto_phiProd hq0.le hq1.le).comp hsub).pow 2
  have htR1 : Filter.Tendsto (phiProd (q ^ 2)) Filter.atTop (nhds (phiLim (q ^ 2))) :=
    tendsto_phiProd (by positivity) (by nlinarith)
  have htR2 : Filter.Tendsto (jtpProd q (-1)) Filter.atTop (nhds (th4 c)) := by
    rw [← symTerm_tsum_neg_one hc]
    exact jtp_tendsto hq0 hq1 (by norm_num)
  have htR := htR1.mul htR2
  have heq : (fun N : ℕ => phiProd q (2 * N) ^ 2) = fun N => phiProd (q ^ 2) N * jtpProd q (-1) N :=
    funext hfin
  rw [heq] at htL
  exact tendsto_nhds_unique htL htR

private lemma prod_one_add_even_shift (q : ℝ) (N : ℕ) :
    (1 + q ^ (2 * N)) * (∏ k ∈ Finset.range N, (1 + q ^ (2 * k))) =
      2 * ∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 2)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have h2n : 2 * (N + 1) = 2 * N + 2 := by omega
    rw [h2n]
    calc
      (1 + q ^ (2 * N + 2)) * ((∏ k ∈ Finset.range N, (1 + q ^ (2 * k))) * (1 + q ^ (2 * N)))
          = (1 + q ^ (2 * N + 2)) *
              ((1 + q ^ (2 * N)) * ∏ k ∈ Finset.range N, (1 + q ^ (2 * k))) := by ring
      _ = (1 + q ^ (2 * N + 2)) * (2 * ∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 2))) := by rw [ih]
      _ = 2 * ((∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 2))) * (1 + q ^ (2 * N + 2))) := by ring

private lemma phiLim_cube_eq {c : ℝ} (hc : 2 ≤ c) :
    Real.exp (c / 4) * th2 c * th3 c * th4 c = 2 * phiLim (Real.exp (-c) ^ 2) ^ 3 := by
  set q : ℝ := Real.exp (-c)
  set r : ℝ := q ^ 2
  have hc0 : 0 < c := by linarith
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by dsimp only [r]; nlinarith
  have hfin : ∀ N : ℕ,
      (1 + q ^ (2 * N)) * jtpProd q q N * jtpProd q 1 N * jtpProd q (-1) N * phiProd r N ^ 2 =
        2 * phiProd r N ^ 3 * phiProd r (2 * N) ^ 2 := by
    intro N
    have hphi_r : ∏ j ∈ Finset.range N, (1 - q ^ (2 * (j + 1))) = phiProd r N := by
      dsimp only [phiProd, r]
      refine Finset.prod_congr rfl fun j _ => by rw [← pow_mul]
    have hj_q : (1 + q ^ (2 * N)) * jtpProd q q N =
        2 * phiProd r N * (∏ k ∈ Finset.range N, (1 + r ^ (k + 1))) ^ 2 := by
      dsimp only [jtpProd]
      rw [hphi_r, Finset.prod_mul_distrib]
      have h1 : ∏ k ∈ Finset.range N, (1 + q * q ^ (2 * k + 1)) =
          ∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 2)) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← pow_succ']
      have h2 : ∏ k ∈ Finset.range N, (1 + q⁻¹ * q ^ (2 * k + 1)) =
          ∏ k ∈ Finset.range N, (1 + q ^ (2 * k)) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        have hinv : q⁻¹ * q ^ (2 * k + 1) = q ^ (2 * k) := by
          rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ hq0.ne', one_mul]
        rw [hinv]
      have h3 : ∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 2)) =
          ∏ k ∈ Finset.range N, (1 + r ^ (k + 1)) := by
        dsimp only [r]
        refine Finset.prod_congr rfl fun k _ => ?_
        have he : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [← pow_mul, he]
      rw [h1, h2]
      calc
        (1 + q ^ (2 * N)) *
            (phiProd r N * ((∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 2))) *
              (∏ k ∈ Finset.range N, (1 + q ^ (2 * k)))))
            = phiProd r N * (∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 2))) *
                ((1 + q ^ (2 * N)) * ∏ k ∈ Finset.range N, (1 + q ^ (2 * k))) := by ring
        _ = phiProd r N * (∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 2))) *
              (2 * ∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 2))) := by
                rw [prod_one_add_even_shift]
        _ = 2 * phiProd r N * (∏ k ∈ Finset.range N, (1 + r ^ (k + 1))) ^ 2 := by
              rw [h3]; ring
    have hj_1m1 : jtpProd q 1 N * jtpProd q (-1) N =
        phiProd r N ^ 2 * (∏ k ∈ Finset.range N, (1 - r ^ (2 * k + 1))) ^ 2 := by
      dsimp only [jtpProd]
      rw [hphi_r]
      have h1 : ∏ k ∈ Finset.range N,
          (1 + 1 * q ^ (2 * k + 1)) * (1 + (1 : ℝ)⁻¹ * q ^ (2 * k + 1)) =
          (∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 1))) ^ 2 := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun k _ => by norm_num; ring
      have h2 : ∏ k ∈ Finset.range N,
          (1 + (-1 : ℝ) * q ^ (2 * k + 1)) * (1 + (-1 : ℝ)⁻¹ * q ^ (2 * k + 1)) =
          (∏ k ∈ Finset.range N, (1 - q ^ (2 * k + 1))) ^ 2 := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun k _ => by norm_num; ring
      have h3 : (∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 1))) *
          (∏ k ∈ Finset.range N, (1 - q ^ (2 * k + 1))) =
          ∏ k ∈ Finset.range N, (1 - r ^ (2 * k + 1)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        have hp : q ^ (2 * k + 1) * q ^ (2 * k + 1) = r ^ (2 * k + 1) := by
          dsimp only [r]; rw [← pow_add, ← pow_mul]; congr 1; omega
        calc
          (1 + q ^ (2 * k + 1)) * (1 - q ^ (2 * k + 1))
              = 1 - q ^ (2 * k + 1) * q ^ (2 * k + 1) := by ring
          _ = 1 - r ^ (2 * k + 1) := by rw [hp]
      rw [h1, h2]
      calc
        phiProd r N * (∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 1))) ^ 2 *
            (phiProd r N * (∏ k ∈ Finset.range N, (1 - q ^ (2 * k + 1))) ^ 2)
            = phiProd r N ^ 2 *
                ((∏ k ∈ Finset.range N, (1 + q ^ (2 * k + 1))) *
                  (∏ k ∈ Finset.range N, (1 - q ^ (2 * k + 1)))) ^ 2 := by ring
        _ = phiProd r N ^ 2 * (∏ k ∈ Finset.range N, (1 - r ^ (2 * k + 1))) ^ 2 := by rw [h3]
    have hmerge : phiProd r N * (∏ k ∈ Finset.range N, (1 + r ^ (k + 1))) *
        (∏ k ∈ Finset.range N, (1 - r ^ (2 * k + 1))) = phiProd r (2 * N) := by
      rw [phiProd_two_mul r N]
      have hprod : phiProd r N * (∏ k ∈ Finset.range N, (1 + r ^ (k + 1))) = phiProd (r ^ 2) N := by
        dsimp only [phiProd]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        have hp : r ^ (k + 1) * r ^ (k + 1) = (r ^ 2) ^ (k + 1) := by
          rw [← mul_pow, sq]
        calc
          (1 - r ^ (k + 1)) * (1 + r ^ (k + 1)) = 1 - r ^ (k + 1) * r ^ (k + 1) := by ring
          _ = 1 - (r ^ 2) ^ (k + 1) := by rw [hp]
      rw [hprod, mul_comm]
    calc
      (1 + q ^ (2 * N)) * jtpProd q q N * jtpProd q 1 N * jtpProd q (-1) N * phiProd r N ^ 2
          = ((1 + q ^ (2 * N)) * jtpProd q q N) * (jtpProd q 1 N * jtpProd q (-1) N) *
              phiProd r N ^ 2 := by ring
      _ = (2 * phiProd r N * (∏ k ∈ Finset.range N, (1 + r ^ (k + 1))) ^ 2) *
            (phiProd r N ^ 2 * (∏ k ∈ Finset.range N, (1 - r ^ (2 * k + 1))) ^ 2) *
            phiProd r N ^ 2 := by rw [hj_q, hj_1m1]
      _ = 2 * phiProd r N ^ 3 *
            (phiProd r N * (∏ k ∈ Finset.range N, (1 + r ^ (k + 1))) *
              (∏ k ∈ Finset.range N, (1 - r ^ (2 * k + 1)))) ^ 2 := by ring
      _ = 2 * phiProd r N ^ 3 * phiProd r (2 * N) ^ 2 := by rw [hmerge]
  have ht1 : Filter.Tendsto (fun N : ℕ => 1 + q ^ (2 * N)) Filter.atTop (nhds 1) := by
    have hpow : Filter.Tendsto (fun N : ℕ => r ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
    have hadd : Filter.Tendsto (fun N : ℕ => (1 : ℝ) + r ^ N) Filter.atTop (nhds 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add hpow
    refine hadd.congr fun N => ?_
    dsimp only [r]
    rw [← pow_mul]
  have ht2 : Filter.Tendsto (jtpProd q q) Filter.atTop (nhds (Real.exp (c / 4) * th2 c)) := by
    rw [← symTerm_tsum_q hc0]
    exact jtp_tendsto hq0 hq1 hq0.ne'
  have ht3 : Filter.Tendsto (jtpProd q 1) Filter.atTop (nhds (th3 c)) := by
    rw [← symTerm_tsum_one hc0]
    exact jtp_tendsto hq0 hq1 one_ne_zero
  have ht4 : Filter.Tendsto (jtpProd q (-1)) Filter.atTop (nhds (th4 c)) := by
    rw [← symTerm_tsum_neg_one hc0]
    exact jtp_tendsto hq0 hq1 (by norm_num)
  have ht5 : Filter.Tendsto (phiProd r) Filter.atTop (nhds (phiLim r)) :=
    tendsto_phiProd hr0.le hr1.le
  have hsub : Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => by omega : ∀ N, N ≤ 2 * N) Filter.tendsto_id
  have ht6 : Filter.Tendsto (fun N : ℕ => phiProd r (2 * N)) Filter.atTop (nhds (phiLim r)) :=
    ht5.comp hsub
  have htL := (((ht1.mul ht2).mul ht3).mul ht4).mul (ht5.pow 2)
  have htR := ((ht5.pow 3).const_mul 2).mul (ht6.pow 2)
  have heq :
      (fun N : ℕ => (1 + q ^ (2 * N)) * jtpProd q q N * jtpProd q 1 N * jtpProd q (-1) N *
        phiProd r N ^ 2) =
      fun N : ℕ => 2 * phiProd r N ^ 3 * phiProd r (2 * N) ^ 2 := funext hfin
  rw [heq] at htL
  have hlim := tendsto_nhds_unique htL htR
  have hr_half : r < 1 / 2 := by
    have hq_le : q ≤ 1 / 4 :=
      le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_two_le_quarter
    dsimp only [r]
    nlinarith
  have hphi_pos : 0 < phiLim r := phiLim_pos hr0 hr_half
  have hphi2_ne : phiLim r ^ 2 ≠ 0 := (sq_pos_of_pos hphi_pos).ne'
  refine mul_right_cancel₀ hphi2_ne ?_
  calc
    Real.exp (c / 4) * th2 c * th3 c * th4 c * phiLim r ^ 2
        = 1 * (Real.exp (c / 4) * th2 c) * th3 c * th4 c * phiLim r ^ 2 := by ring
    _ = 2 * phiLim r ^ 3 * phiLim r ^ 2 := hlim

theorem OMA.solution : type_of% @OMA.S_oeis_a010815.main := by
  rw [← phiLim_qVal_eq_tsum]
  set L : ℝ := phiLim qVal
  set R : ℝ := (1 / 2) * Real.exp (Real.pi / 24) * Real.pi ^ (1 / 4 : ℝ) * 2 ^ (5 / 8 : ℝ) /
    Real.Gamma (3 / 4)
  have hpi2 : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hq0 : 0 < qVal := Real.exp_pos _
  have hq_half : qVal < 1 / 2 := by
    have hq4 : qVal ≤ 1 / 4 :=
      le_trans (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])) exp_neg_two_le_quarter
    linarith
  have hLpos : 0 < L := phiLim_pos hq0 hq_half
  have hg34 : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hRpos : 0 < R := by
    dsimp only [R]
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  have hsq : L ^ 2 = phiLim (qVal ^ 2) * th4 Real.pi := phiLim_sq_eq Real.pi_pos
  have hcube : Real.exp (Real.pi / 4) * th2 Real.pi * th3 Real.pi * th4 Real.pi =
      2 * phiLim (qVal ^ 2) ^ 3 := phiLim_cube_eq hpi2
  have h24 : th2 Real.pi = th4 Real.pi := th2_pi_eq_th4_pi
  have h34 : th3 Real.pi ^ 2 = Real.sqrt 2 * th4 Real.pi ^ 2 := th3_pi_sq_eq_sqrt_two_mul_th4_pi_sq
  have h3g : th3 Real.pi ^ 2 = Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2 := th3_pi_sq_eq_gamma
  have hL6 : 2 * L ^ 6 = Real.exp (Real.pi / 4) * th3 Real.pi * th4 Real.pi ^ 5 := by
    calc
      2 * L ^ 6 = 2 * (L ^ 2) ^ 3 := by ring
      _ = (2 * phiLim (qVal ^ 2) ^ 3) * th4 Real.pi ^ 3 := by rw [hsq]; ring
      _ = (Real.exp (Real.pi / 4) * th2 Real.pi * th3 Real.pi * th4 Real.pi) * th4 Real.pi ^ 3 := by
            rw [← hcube]
      _ = Real.exp (Real.pi / 4) * th3 Real.pi * th4 Real.pi ^ 5 := by rw [h24]; ring
  have hL12 : 4 * L ^ 12 = Real.exp (Real.pi / 2) * th3 Real.pi ^ 2 * th4 Real.pi ^ 10 := by
    have he : Real.exp (Real.pi / 4) ^ 2 = Real.exp (Real.pi / 2) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    calc
      4 * L ^ 12 = (2 * L ^ 6) ^ 2 := by ring
      _ = Real.exp (Real.pi / 4) ^ 2 * th3 Real.pi ^ 2 * th4 Real.pi ^ 10 := by rw [hL6]; ring
      _ = Real.exp (Real.pi / 2) * th3 Real.pi ^ 2 * th4 Real.pi ^ 10 := by rw [he]
  have hL24_1 : 512 * L ^ 24 = Real.exp Real.pi * (th3 Real.pi ^ 2) ^ 12 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h10 : (th3 Real.pi ^ 2) ^ 10 = 32 * (th4 Real.pi ^ 10) ^ 2 := by
      calc
        (th3 Real.pi ^ 2) ^ 10 = (Real.sqrt 2 * th4 Real.pi ^ 2) ^ 10 := by rw [h34]
        _ = (Real.sqrt 2 ^ 2) ^ 5 * (th4 Real.pi ^ 10) ^ 2 := by ring
        _ = 32 * (th4 Real.pi ^ 10) ^ 2 := by rw [hs2]; norm_num
    have he : Real.exp (Real.pi / 2) ^ 2 = Real.exp Real.pi := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    calc
      512 * L ^ 24 = 32 * (4 * L ^ 12) ^ 2 := by ring
      _ = Real.exp (Real.pi / 2) ^ 2 * (th3 Real.pi ^ 2) ^ 2 * (32 * (th4 Real.pi ^ 10) ^ 2) := by
            rw [hL12]; ring
      _ = Real.exp Real.pi * (th3 Real.pi ^ 2) ^ 2 * (th3 Real.pi ^ 2) ^ 10 := by rw [he, h10]
      _ = Real.exp Real.pi * (th3 Real.pi ^ 2) ^ 12 := by ring
  have hL24 : 512 * L ^ 24 = Real.exp Real.pi * Real.pi ^ 6 / Real.Gamma (3 / 4) ^ 24 := by
    rw [hL24_1, h3g, div_pow]
    have hsp : Real.sqrt Real.pi ^ 12 = Real.pi ^ 6 := by
      calc
        Real.sqrt Real.pi ^ 12 = (Real.sqrt Real.pi ^ 2) ^ 6 := by ring
        _ = Real.pi ^ 6 := by rw [Real.sq_sqrt Real.pi_pos.le]
    rw [hsp]
    ring
  have hR24 : 512 * R ^ 24 = Real.exp Real.pi * Real.pi ^ 6 / Real.Gamma (3 / 4) ^ 24 := by
    dsimp only [R]
    have hexp : Real.exp (Real.pi / 24) ^ 24 = Real.exp Real.pi := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hpi6 : (Real.pi ^ (1 / 4 : ℝ)) ^ 24 = Real.pi ^ 6 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
      have he : (1 / 4 : ℝ) * (24 : ℕ) = (6 : ℕ) := by norm_num
      rw [he, Real.rpow_natCast]
    have htwo : (2 ^ (5 / 8 : ℝ)) ^ 24 = (2 : ℝ) ^ 15 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have he : (5 / 8 : ℝ) * (24 : ℕ) = (15 : ℕ) := by norm_num
      rw [he, Real.rpow_natCast]
    rw [div_pow, mul_pow, mul_pow, mul_pow, hexp, hpi6, htwo]
    norm_num
    ring
  have heq24 : L ^ 24 = R ^ 24 := by linarith
  exact (pow_left_inj₀ hLpos.le hRpos.le (by norm_num : (24 : ℕ) ≠ 0)).mp heq24
