import OMAReductions.R_oeis_a224274_R1

/-!
# Proof of `oeis-a224274.R1.H1`

Proves that for every odd prime `p`, `a(p) = (4 * p).choose p / 4 ≡ 1 [MOD p ^ 3]`.

For `p = 3`, `a(3) = 55 ≡ 1 [MOD 27]` directly. For `p ≥ 5`:
1. Since `4 * p * (4 * p - 1).choose (p - 1) = p * (4 * p).choose p`, we have
   `a(p) = (4 * p - 1).choose (p - 1)`.
2. Moreover `(4 * p - 1).choose (p - 1) * (p - 1)! = ∏ k ∈ Ico 1 p, (k + 3 * p)`.
3. Expanding the product modulo `p ^ 3` gives
   `∏ k ∈ Ico 1 p, (k + 3 * p) ≡ (p - 1)! + 3 * p * e₁ + 9 * p ^ 2 * e₂ [MOD p ^ 3]`,
   where `e₁ = ∑ k ∈ Ico 1 p, (p - 1)! / k` and
   `e₂ = ∑_{1 ≤ i < j < p} (p - 1)! / (i * j)`.
4. Over `ZMod p` (a field of characteristic `p ≥ 5`), the power sums
   `∑ x : (ZMod p)ˣ, (x : ZMod p)⁻¹ = 0` and `∑ x : (ZMod p)ˣ, ((x : ZMod p)⁻¹)^2 = 0`
   (scaling by a primitive root / element `c` with `c ^ 2 ≠ 1` in `ZMod p`).
5. Pairing `k` with `p - k` in `ZMod (p ^ 2)` gives `2 * ∑ k, k⁻¹ = p * ∑ k, (k * (p - k))⁻¹`,
   which vanishes modulo `p ^ 2` by step 4, proving `p ^ 2 ∣ e₁` (Wolstenholme's theorem) and
   `p ∣ e₂`.
6. Therefore `∏ k ∈ Ico 1 p, (k + 3 * p) ≡ (p - 1)! [MOD p ^ 3]`. Since `((p - 1)!).Coprime (p ^ 3)`,
   canceling `(p - 1)!` yields `a(p) ≡ 1 [MOD p ^ 3]`.
-/

namespace OeisA224274R1H1Proof

open Finset

private lemma a_eq_choose_pred {p : ℕ} (hp : 0 < p) :
    OMA.S_oeis_a224274.a p = (4 * p - 1).choose (p - 1) := by
  unfold OMA.S_oeis_a224274.a
  have h1 : (4 * p) * (4 * p - 1).choose (p - 1) = p * (4 * p).choose p := by
    have h := Nat.add_one_mul_choose_eq (4 * p - 1) (p - 1)
    rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at h
    linarith
  have h2 : (4 * p).choose p = 4 * (4 * p - 1).choose (p - 1) := by
    have : p * (4 * p).choose p = p * (4 * (4 * p - 1).choose (p - 1)) := by linarith
    exact Nat.eq_of_mul_eq_mul_left hp this
  rw [h2, Nat.mul_div_cancel_left _ (by decide)]

private lemma choose_mul_factorial_eq_prod {p : ℕ} (hp : 0 < p) :
    (4 * p - 1).choose (p - 1) * (p - 1).factorial = ∏ k ∈ Ico 1 p, (k + 3 * p) := by
  have hdesc : (4 * p - 1).descFactorial (p - 1) =
      (p - 1).factorial * (4 * p - 1).choose (p - 1) :=
    Nat.descFactorial_eq_factorial_mul_choose (4 * p - 1) (p - 1)
  rw [mul_comm, ← hdesc]
  rw [Nat.descFactorial_eq_prod_range]
  refine Finset.prod_nbij' (fun i => 4 * p - 1 - i - 3 * p) (fun k => p - 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico]; omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]; omega
  · intro i hi
    rw [Finset.mem_range] at hi; omega
  · intro k hk
    rw [Finset.mem_Ico] at hk; omega
  · intro i hi
    rw [Finset.mem_range] at hi; omega

private lemma sum_inv_pow_eq_zero_zmod {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {d : ℕ} (hd1 : d = 1 ∨ d = 2) :
    ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹) ^ d = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  -- Compare with sum over all units (ZMod p)ˣ
  have hsum_units : ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹) ^ d =
      ∑ x : (ZMod p)ˣ, ((x : ZMod p)⁻¹) ^ d := by
    refine Finset.sum_nbij'
      (fun k => if hk : k ∈ Ico 1 p then
        Units.mk0 (k : ZMod p) (by
          rw [Finset.mem_Ico] at hk
          intro h0
          have hdvd := (ZMod.natCast_eq_zero_iff k p).mp h0
          have := Nat.le_of_dvd (by omega) hdvd
          omega)
      else 1)
      (fun x => (x : ZMod p).val) ?_ ?_ ?_ ?_ ?_
    · intro k _; exact Finset.mem_univ _
    · intro x _
      rw [Finset.mem_Ico]
      refine ⟨?_, ZMod.val_lt _⟩
      have hne : (x : ZMod p) ≠ 0 := x.ne_zero
      by_contra h0
      have hv : (x : ZMod p).val = 0 := by omega
      exact hne ((ZMod.val_eq_zero (x : ZMod p)).mp hv)
    · intro k hk
      simp only [hk, ↓reduceDIte, Units.val_mk0]
      rw [Finset.mem_Ico] at hk
      exact ZMod.val_natCast_of_lt hk.2
    · intro x _
      have hmem : (x : ZMod p).val ∈ Ico 1 p := by
        rw [Finset.mem_Ico]
        refine ⟨?_, ZMod.val_lt _⟩
        have hne : (x : ZMod p) ≠ 0 := x.ne_zero
        by_contra h0
        have hv : (x : ZMod p).val = 0 := by omega
        exact hne ((ZMod.val_eq_zero (x : ZMod p)).mp hv)
      simp only [hmem, ↓reduceDIte]
      ext
      simp
    · intro k hk
      simp only [hk, ↓reduceDIte, Units.val_mk0]
  rw [hsum_units]
  -- Multiply by c^d where c = 2 : (ZMod p)ˣ; since p ≥ 5, 2^d ≠ 1 in ZMod p
  have h2ne0 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have := Nat.le_of_dvd (by decide) hdvd
    omega
  let c : (ZMod p)ˣ := Units.mk0 (2 : ZMod p) h2ne0
  have hcd_ne1 : ((c : ZMod p)⁻¹) ^ d ≠ 1 := by
    intro heq
    have hc_pow : (2 : ZMod p) ^ d = 1 := by
      have h1 : ((2 : ZMod p) ^ d)⁻¹ = 1 := by
        simpa [c, inv_pow] using heq
      exact inv_eq_one.mp h1
    rcases hd1 with rfl | rfl
    · have h10 : ((1 : ℕ) : ZMod p) = 0 := by
        have h1 : (2 : ZMod p) - 1 = 0 := sub_eq_zero.mpr (by simpa using hc_pow)
        push_cast; linear_combination h1
      have := (ZMod.natCast_eq_zero_iff 1 p).mp h10
      have := Nat.le_of_dvd (by decide) this
      omega
    · have h30 : ((3 : ℕ) : ZMod p) = 0 := by
        have h3 : (2 : ZMod p) ^ 2 - 1 = 0 := sub_eq_zero.mpr hc_pow
        push_cast; linear_combination h3
      have := (ZMod.natCast_eq_zero_iff 3 p).mp h30
      have := Nat.le_of_dvd (by decide) this
      omega
  set S : ZMod p := ∑ x : (ZMod p)ˣ, ((x : ZMod p)⁻¹) ^ d
  have hscale : ((c : ZMod p)⁻¹) ^ d * S = S := by
    rw [Finset.mul_sum]
    have hbi : ∑ x : (ZMod p)ˣ, ((c : ZMod p)⁻¹) ^ d * ((x : ZMod p)⁻¹) ^ d =
        ∑ x : (ZMod p)ˣ, (((c * x : (ZMod p)ˣ) : ZMod p)⁻¹) ^ d := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Units.val_mul, mul_inv, mul_pow]
    rw [hbi]
    exact Fintype.sum_equiv (Equiv.mulLeft c) _ _ (fun _ => rfl)
  have hfac : (((c : ZMod p)⁻¹) ^ d - 1) * S = 0 := by
    rw [sub_mul, one_mul, hscale, sub_self]
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hcd_ne1
  · exact h0

-- In ZMod (p^3), for any finite set s, ∏_{k ∈ s} (k + 3*p) splits into degree 0, 1, 2 in (3*p)
-- because (3*p)^3 = 27 * p^3 = 0 in ZMod (p^3)!
private lemma prod_add_const_zmod_cube {p : ℕ} (s : Finset ℕ) (a : ZMod (p ^ 3))
    (ha3 : a ^ 3 = 0) :
    ∏ k ∈ s, ((k : ZMod (p ^ 3)) + a) =
      (∏ k ∈ s, (k : ZMod (p ^ 3))) +
      a * (∑ k ∈ s, ∏ j ∈ s.erase k, (j : ZMod (p ^ 3))) +
      a ^ 2 * (∑ k ∈ s, ∑ j ∈ s.erase k,
        if k < j then ∏ i ∈ (s.erase k).erase j, (i : ZMod (p ^ 3)) else 0) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x t hx ih =>
    have hpx : ∏ k ∈ insert x t, ((k : ZMod (p ^ 3)) + a) =
        ((x : ZMod (p ^ 3)) + a) * ∏ k ∈ t, ((k : ZMod (p ^ 3)) + a) :=
      Finset.prod_insert hx
    rw [hpx, ih]
    set P0 := ∏ k ∈ t, (k : ZMod (p ^ 3))
    set P1 := ∑ k ∈ t, ∏ j ∈ t.erase k, (j : ZMod (p ^ 3))
    set P2 := ∑ k ∈ t, ∑ j ∈ t.erase k,
        if k < j then ∏ i ∈ (t.erase k).erase j, (i : ZMod (p ^ 3)) else 0
    have hlhs : ((x : ZMod (p ^ 3)) + a) * (P0 + a * P1 + a ^ 2 * P2) =
        (x : ZMod (p ^ 3)) * P0 + a * (P0 + (x : ZMod (p ^ 3)) * P1) +
        a ^ 2 * (P1 + (x : ZMod (p ^ 3)) * P2) := by
      have : a * (a ^ 2 * P2) = 0 := by rw [← mul_assoc, ← pow_succ', ha3, zero_mul]
      linear_combination this
    rw [hlhs]
    -- Match the three coefficients with the RHS sums over insert x t
    have h0 : ∏ k ∈ insert x t, (k : ZMod (p ^ 3)) = (x : ZMod (p ^ 3)) * P0 :=
      Finset.prod_insert hx
    have h1 : ∑ k ∈ insert x t, ∏ j ∈ (insert x t).erase k, (j : ZMod (p ^ 3)) =
        P0 + (x : ZMod (p ^ 3)) * P1 := by
      rw [Finset.sum_insert hx, Finset.erase_insert hx]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkx : x ≠ k := fun h => hx (h ▸ hk)
      rw [Finset.erase_insert_of_ne hkx, Finset.prod_insert (by simp [hx])]
    have h2 : ∑ k ∈ insert x t, ∑ j ∈ (insert x t).erase k,
          (if k < j then ∏ i ∈ ((insert x t).erase k).erase j, (i : ZMod (p ^ 3)) else 0) =
        P1 + (x : ZMod (p ^ 3)) * P2 := by
      rw [Finset.sum_insert hx, Finset.erase_insert hx]
      have hrest : ∑ k ∈ t, ∑ j ∈ (insert x t).erase k,
            (if k < j then ∏ i ∈ ((insert x t).erase k).erase j, (i : ZMod (p ^ 3)) else 0) =
          (∑ k ∈ t, if k < x then ∏ i ∈ t.erase k, (i : ZMod (p ^ 3)) else 0) +
          (x : ZMod (p ^ 3)) * P2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkx : x ≠ k := fun h => hx (h ▸ hk)
        rw [Finset.erase_insert_of_ne hkx, Finset.sum_insert (by simp [hx]),
          Finset.erase_insert (by simp [hx])]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjx : x ≠ j := fun h => hx (Finset.mem_of_mem_erase (h ▸ hj))
        rw [Finset.erase_insert_of_ne hjx]
        split_ifs
        · rw [Finset.prod_insert (by simp [hx])]
        · rw [mul_zero]
      rw [hrest, ← add_assoc]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkx : x ≠ k := fun h => hx (h ▸ hk)
      rcases lt_or_gt_of_ne hkx with hlt | hgt
      · have hnot : ¬ (k < x) := by omega
        simp [hlt, hnot]
      · have hnot : ¬ (x < k) := by omega
        simp [hgt, hnot]
    rw [h0, h1, h2]

end OeisA224274R1H1Proof

theorem OMA.solution : OMA.R_oeis_a224274_R1.H1 := by
  intro p hp hodd
  have hp_ge3 : 3 ≤ p := by
    have h2 := hp.two_le
    obtain ⟨m, hm⟩ := hodd
    omega
  by_cases hp3 : p = 3
  · subst hp3; decide
  have hp5 : 5 ≤ p := by
    have : p ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
    omega
  have : Fact p.Prime := ⟨hp⟩
  rw [OeisA224274R1H1Proof.a_eq_choose_pred hp.pos]
  -- Sufficient to prove in ZMod (p^3) that ((4p-1).choose (p-1) : ZMod (p^3)) = 1
  rw [← ZMod.natCast_eq_natCast_iff]
  have hfac_cop : Nat.Coprime (p - 1).factorial (p ^ 3) := by
    refine Nat.Coprime.pow_right 3 ?_
    exact (hp.coprime_iff_not_dvd.mpr fun hd => by
      have hle := (Nat.Prime.dvd_factorial hp).mp hd
      omega).symm
  -- Multiply by ((p - 1)! : ZMod (p^3)), which is a unit in ZMod (p^3)
  let u : (ZMod (p ^ 3))ˣ := ZMod.unitOfCoprime (p - 1).factorial hfac_cop
  have hu_val : (u : ZMod (p ^ 3)) = ((p - 1).factorial : ZMod (p ^ 3)) :=
    ZMod.coe_unitOfCoprime _ _
  suffices hprod : ((4 * p - 1).choose (p - 1) : ZMod (p ^ 3)) * ((p - 1).factorial : ZMod (p ^ 3)) =
      ((p - 1).factorial : ZMod (p ^ 3)) by
    rw [← hu_val] at hprod
    have h1 : ((4 * p - 1).choose (p - 1) : ZMod (p ^ 3)) * (u : ZMod (p ^ 3)) =
        (1 : ZMod (p ^ 3)) * (u : ZMod (p ^ 3)) := by simpa using hprod
    have h2 := congrArg (fun x => x * (u⁻¹ : ZMod (p ^ 3))) h1
    simpa [mul_assoc] using h2
  rw [← Nat.cast_mul, OeisA224274R1H1Proof.choose_mul_factorial_eq_prod hp.pos, Nat.cast_prod]
  have hcast_prod : ∏ k ∈ Finset.Ico 1 p, (((k + 3 * p : ℕ) : ZMod (p ^ 3))) =
      ∏ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 3)) + (3 * p : ZMod (p ^ 3))) := by
    refine Finset.prod_congr rfl fun k _ => by push_cast; rfl
  rw [hcast_prod]
  have ha3 : ((3 * p : ZMod (p ^ 3))) ^ 3 = 0 := by
    have : ((3 * p : ZMod (p ^ 3))) ^ 3 = (27 : ZMod (p ^ 3)) * ((p ^ 3 : ℕ) : ZMod (p ^ 3)) := by
      push_cast; ring
    rw [this, ZMod.natCast_self, mul_zero]
  rw [OeisA224274R1H1Proof.prod_add_const_zmod_cube (Finset.Ico 1 p) (3 * p : ZMod (p ^ 3)) ha3]
  -- Base term equals (p - 1)!
  have hbase : ∏ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3)) = ((p - 1).factorial : ZMod (p ^ 3)) := by
    rw [← Nat.cast_prod]
    congr 1
    conv_lhs => rw [show p = p - 1 + 1 by omega]
    exact Finset.prod_Ico_id_eq_factorial (p - 1)
  rw [hbase]
  -- Every k ∈ Ico 1 p is a unit in ZMod (p^3)
  have hk_cop : ∀ k ∈ Finset.Ico 1 p, Nat.Coprime k (p ^ 3) := fun k hk => by
    rw [Finset.mem_Ico] at hk
    refine Nat.Coprime.pow_right 3 ?_
    exact (hp.coprime_iff_not_dvd.mpr fun hd => by
      have := Nat.le_of_dvd (by omega) hd; omega).symm
  let inv3 : ℕ → ZMod (p ^ 3) := fun k =>
    if hk : k ∈ Finset.Ico 1 p then ((ZMod.unitOfCoprime k (hk_cop k hk))⁻¹ : (ZMod (p ^ 3))ˣ) else 0
  have hinv3_mul : ∀ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3)) * inv3 k = 1 := fun k hk => by
    simp only [inv3, hk, ↓reduceDIte]
    rw [← ZMod.coe_unitOfCoprime k (hk_cop k hk)]
    exact Units.mul_inv _
  -- Rewrite erase products in terms of (p - 1)! * inv3 k
  have herase1 : ∀ k ∈ Finset.Ico 1 p,
      ∏ j ∈ (Finset.Ico 1 p).erase k, (j : ZMod (p ^ 3)) =
        ((p - 1).factorial : ZMod (p ^ 3)) * inv3 k := fun k hk => by
    have hmul : (k : ZMod (p ^ 3)) * ∏ j ∈ (Finset.Ico 1 p).erase k, (j : ZMod (p ^ 3)) =
        ((p - 1).factorial : ZMod (p ^ 3)) := by
      rw [Finset.mul_prod_erase _ _ hk, hbase]
    calc ∏ j ∈ (Finset.Ico 1 p).erase k, (j : ZMod (p ^ 3))
        = (inv3 k * (k : ZMod (p ^ 3))) * ∏ j ∈ (Finset.Ico 1 p).erase k, (j : ZMod (p ^ 3)) := by
            rw [mul_comm (inv3 k), hinv3_mul k hk, one_mul]
      _ = inv3 k * ((k : ZMod (p ^ 3)) * ∏ j ∈ (Finset.Ico 1 p).erase k, (j : ZMod (p ^ 3))) := by
            ring
      _ = ((p - 1).factorial : ZMod (p ^ 3)) * inv3 k := by rw [hmul, mul_comm]
  have herase2 : ∀ k ∈ Finset.Ico 1 p, ∀ j ∈ (Finset.Ico 1 p).erase k,
      ∏ i ∈ ((Finset.Ico 1 p).erase k).erase j, (i : ZMod (p ^ 3)) =
        ((p - 1).factorial : ZMod (p ^ 3)) * inv3 k * inv3 j := fun k hk j hj => by
    have hj_mem : j ∈ Finset.Ico 1 p := Finset.mem_of_mem_erase hj
    have hmul : (j : ZMod (p ^ 3)) * ∏ i ∈ ((Finset.Ico 1 p).erase k).erase j, (i : ZMod (p ^ 3)) =
        ((p - 1).factorial : ZMod (p ^ 3)) * inv3 k := by
      rw [Finset.mul_prod_erase _ _ hj, herase1 k hk]
    calc ∏ i ∈ ((Finset.Ico 1 p).erase k).erase j, (i : ZMod (p ^ 3))
        = (inv3 j * (j : ZMod (p ^ 3))) *
            ∏ i ∈ ((Finset.Ico 1 p).erase k).erase j, (i : ZMod (p ^ 3)) := by
            rw [mul_comm (inv3 j), hinv3_mul j hj_mem, one_mul]
      _ = inv3 j * ((j : ZMod (p ^ 3)) *
            ∏ i ∈ ((Finset.Ico 1 p).erase k).erase j, (i : ZMod (p ^ 3))) := by ring
      _ = ((p - 1).factorial : ZMod (p ^ 3)) * inv3 k * inv3 j := by rw [hmul]; ring
  -- Helper: projection ZMod (p^3) →+* ZMod p maps inv3 k to (k : ZMod p)⁻¹
  let proj1 : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by decide)) (ZMod p)
  have hproj1_inv : ∀ k ∈ Finset.Ico 1 p, proj1 (inv3 k) = (k : ZMod p)⁻¹ := fun k hk => by
    have hm := congrArg proj1 (hinv3_mul k hk)
    rw [map_mul, map_natCast, map_one] at hm
    have hkne0 : (k : ZMod p) ≠ 0 := by
      rw [Finset.mem_Ico] at hk
      intro h0
      have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
      omega
    exact eq_inv_of_mul_eq_one_right hm
  -- Helper: if proj1 x = 0 then (p : ZMod (p^3))^2 * x = 0
  have hkill_p2 : ∀ x : ZMod (p ^ 3), proj1 x = 0 → ((p : ZMod (p ^ 3)) ^ 2) * x = 0 := by
    intro x hx
    have hxp : (p : ℕ) ∣ x.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : proj1 ((x.val : ℕ) : ZMod (p ^ 3)) = (x.val : ZMod p) := map_natCast proj1 x.val
      rw [ZMod.natCast_zmod_val] at this
      rw [← this, hx]
    obtain ⟨m, hm⟩ := hxp
    have hxeq : x = (p : ZMod (p ^ 3)) * (m : ZMod (p ^ 3)) := by
      rw [← ZMod.natCast_zmod_val x, hm, Nat.cast_mul]
    rw [hxeq]
    calc ((p : ZMod (p ^ 3)) ^ 2) * ((p : ZMod (p ^ 3)) * (m : ZMod (p ^ 3)))
        = ((p ^ 3 : ℕ) : ZMod (p ^ 3)) * (m : ZMod (p ^ 3)) := by push_cast; ring
      _ = 0 := by rw [ZMod.natCast_self, zero_mul]
  -- Helper: projection ZMod (p^3) →+* ZMod (p^2) kills p * x
  let proj2 : ZMod (p ^ 3) →+* ZMod (p ^ 2) :=
    ZMod.castHom (Nat.pow_dvd_pow p (by decide : 2 ≤ 3)) (ZMod (p ^ 2))
  have hkill_p1 : ∀ x : ZMod (p ^ 3), proj2 x = 0 → (p : ZMod (p ^ 3)) * x = 0 := by
    intro x hx
    have hxp : p ^ 2 ∣ x.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : proj2 ((x.val : ℕ) : ZMod (p ^ 3)) = (x.val : ZMod (p ^ 2)) := map_natCast proj2 x.val
      rw [ZMod.natCast_zmod_val] at this
      rw [← this, hx]
    obtain ⟨m, hm⟩ := hxp
    have hxeq : x = ((p ^ 2 : ℕ) : ZMod (p ^ 3)) * (m : ZMod (p ^ 3)) := by
      rw [← ZMod.natCast_zmod_val x, hm, Nat.cast_mul]
    rw [hxeq]
    calc (p : ZMod (p ^ 3)) * (((p ^ 2 : ℕ) : ZMod (p ^ 3)) * (m : ZMod (p ^ 3)))
        = ((p ^ 3 : ℕ) : ZMod (p ^ 3)) * (m : ZMod (p ^ 3)) := by push_cast; ring
      _ = 0 := by rw [ZMod.natCast_self, zero_mul]
  -- Term 1: (3 * p) * ∑ k, (p - 1)! * inv3 k = 0 in ZMod (p^3)
  have hterm1 : (3 * p : ZMod (p ^ 3)) *
      (∑ k ∈ Finset.Ico 1 p, ∏ j ∈ (Finset.Ico 1 p).erase k, (j : ZMod (p ^ 3))) = 0 := by
    have hrewrite : ∑ k ∈ Finset.Ico 1 p, ∏ j ∈ (Finset.Ico 1 p).erase k, (j : ZMod (p ^ 3)) =
        ((p - 1).factorial : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k hk => herase1 k hk
    rw [hrewrite]
    -- Show proj2 (∑ k, inv3 k) = 0 by pairing k with p - k
    set S1 : ZMod (p ^ 3) := ∑ k ∈ Finset.Ico 1 p, inv3 k
    have hS1_proj2 : proj2 S1 = 0 := by
      -- Since 2 is a unit in ZMod (p^2), show 2 * proj2 S1 = 0
      have h2_cop : Nat.Coprime 2 (p ^ 2) := by
        refine Nat.Coprime.pow_right 2 ?_
        exact (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
      let u2 : (ZMod (p ^ 2))ˣ := ZMod.unitOfCoprime 2 h2_cop
      suffices h2S : (2 : ZMod (p ^ 2)) * proj2 S1 = 0 by
        have h1 : (u2 : ZMod (p ^ 2)) * proj2 S1 = 0 := by
          rwa [ZMod.coe_unitOfCoprime]
        have h2 := congrArg (fun x => (u2⁻¹ : ZMod (p ^ 2)) * x) h1
        simpa [mul_assoc] using h2
      have hpair : ∑ k ∈ Finset.Ico 1 p, inv3 (p - k) = S1 := by
        refine Finset.sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_
        · intro k hk; rw [Finset.mem_Ico] at hk ⊢; omega
        · intro k hk; rw [Finset.mem_Ico] at hk ⊢; omega
        · intro k hk; rw [Finset.mem_Ico] at hk; omega
        · intro k hk; rw [Finset.mem_Ico] at hk; omega
        · intro _ _; rfl
      have h2eq : (2 : ZMod (p ^ 3)) * S1 =
          (p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k * inv3 (p - k) := by
        rw [two_mul, Finset.mul_sum]
        conv_lhs => rhs; rw [← hpair]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hpk : p - k ∈ Finset.Ico 1 p := by rw [Finset.mem_Ico] at hk ⊢; omega
        have hadd : (k : ZMod (p ^ 3)) + ((p - k : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) := by
          rw [← Nat.cast_add, Nat.add_sub_of_le (by rw [Finset.mem_Ico] at hk; omega)]
        calc inv3 k + inv3 (p - k)
            = inv3 k * ((p - k : ℕ) : ZMod (p ^ 3)) * inv3 (p - k) +
              (k : ZMod (p ^ 3)) * inv3 k * inv3 (p - k) := by
                rw [mul_assoc (inv3 k), hinv3_mul (p - k) hpk, mul_one, hinv3_mul k hk, one_mul]
          _ = ((k : ZMod (p ^ 3)) + ((p - k : ℕ) : ZMod (p ^ 3))) * (inv3 k * inv3 (p - k)) := by
                ring
          _ = (p : ZMod (p ^ 3)) * (inv3 k * inv3 (p - k)) := by rw [hadd]
      have h2proj := congrArg proj2 h2eq
      rw [map_mul, map_ofNat, map_mul, map_natCast] at h2proj
      rw [h2proj]
      -- Now show proj2 (∑ inv3 k * inv3 (p - k)) is divisible by p (its image in ZMod p is 0)
      set T : ZMod (p ^ 3) := ∑ k ∈ Finset.Ico 1 p, inv3 k * inv3 (p - k)
      have hT_proj1 : proj1 T = 0 := by
        rw [map_sum]
        have hterm : ∑ k ∈ Finset.Ico 1 p, proj1 (inv3 k * inv3 (p - k)) =
            - ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hpk : p - k ∈ Finset.Ico 1 p := by rw [Finset.mem_Ico] at hk ⊢; omega
          rw [map_mul, hproj1_inv k hk, hproj1_inv (p - k) hpk]
          have hneg : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
            rw [Nat.cast_sub (by rw [Finset.mem_Ico] at hk; omega), ZMod.natCast_self, zero_sub]
          rw [hneg, inv_neg, sq]
          ring
        rw [hterm, OeisA224274R1H1Proof.sum_inv_pow_eq_zero_zmod hp hp5 (Or.inr rfl), neg_zero]
      -- proj1 T = 0 implies p ∣ (proj2 T).val, so p * proj2 T = 0 in ZMod (p^2)
      have hp_dvd_T : p ∣ T.val := by
        rw [← ZMod.natCast_eq_zero_iff]
        have : proj1 ((T.val : ℕ) : ZMod (p ^ 3)) = (T.val : ZMod p) := map_natCast proj1 T.val
        rw [ZMod.natCast_zmod_val] at this
        rw [← this, hT_proj1]
      obtain ⟨m, hm⟩ := hp_dvd_T
      have hTeq : T = (p : ZMod (p ^ 3)) * (m : ZMod (p ^ 3)) := by
        rw [← ZMod.natCast_zmod_val T, hm, Nat.cast_mul]
      rw [hTeq, map_mul, map_natCast]
      calc (p : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * proj2 (m : ZMod (p ^ 3)))
          = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * proj2 (m : ZMod (p ^ 3)) := by push_cast; ring
        _ = 0 := by rw [ZMod.natCast_self, zero_mul]
    have hkill := hkill_p1 S1 hS1_proj2
    calc (3 * p : ZMod (p ^ 3)) * (((p - 1).factorial : ZMod (p ^ 3)) * S1)
        = (3 : ZMod (p ^ 3)) * ((p - 1).factorial : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * S1) := by
            ring
      _ = 0 := by rw [hkill, mul_zero]
  -- Term 2: (3 * p)^2 * ∑_{k < j} (p - 1)! * inv3 k * inv3 j = 0 in ZMod (p^3)
  have hterm2 : (3 * p : ZMod (p ^ 3)) ^ 2 *
      (∑ k ∈ Finset.Ico 1 p, ∑ j ∈ (Finset.Ico 1 p).erase k,
        if k < j then ∏ i ∈ ((Finset.Ico 1 p).erase k).erase j, (i : ZMod (p ^ 3)) else 0) = 0 := by
    set S2 : ZMod (p ^ 3) := ∑ k ∈ Finset.Ico 1 p, ∑ j ∈ (Finset.Ico 1 p).erase k,
      if k < j then ∏ i ∈ ((Finset.Ico 1 p).erase k).erase j, (i : ZMod (p ^ 3)) else 0
    have hS2_proj1 : proj1 S2 = 0 := by
      have h2ne0 : (2 : ZMod p) ≠ 0 := by
        intro h0
        have := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0))
        omega
      -- 2 * proj1 S2 = (p - 1)! * ((∑ k⁻¹)^2 - ∑ (k⁻¹)^2) = 0 in ZMod p
      have hproj_S2 : proj1 S2 = ((p - 1).factorial : ZMod p) *
          ∑ k ∈ Finset.Ico 1 p, ∑ j ∈ (Finset.Ico 1 p).erase k,
            if k < j then (k : ZMod p)⁻¹ * (j : ZMod p)⁻¹ else 0 := by
        simp only [S2, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun j hj => ?_
        have hj_mem : j ∈ Finset.Ico 1 p := Finset.mem_of_mem_erase hj
        split_ifs
        · rw [herase2 k hk j hj, map_mul, map_mul, map_natCast,
            hproj1_inv k hk, hproj1_inv j hj_mem, mul_assoc]
        · rw [map_zero, mul_zero]
      rw [hproj_S2]
      suffices hinner : ∑ k ∈ Finset.Ico 1 p, ∑ j ∈ (Finset.Ico 1 p).erase k,
          (if k < j then (k : ZMod p)⁻¹ * (j : ZMod p)⁻¹ else 0) = 0 by
        rw [hinner, mul_zero]
      -- 2 * inner = (∑ k⁻¹)^2 - ∑ (k⁻¹)^2 = 0 - 0 = 0
      set A := ∑ k ∈ Finset.Ico 1 p, ∑ j ∈ (Finset.Ico 1 p).erase k,
        if k < j then (k : ZMod p)⁻¹ * (j : ZMod p)⁻¹ else 0
      have h2A : (2 : ZMod p) * A =
          (∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹) ^ 2 -
          ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 := by
        have hsq : (∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹) ^ 2 =
            ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 +
            ∑ k ∈ Finset.Ico 1 p, ∑ j ∈ (Finset.Ico 1 p).erase k,
              (k : ZMod p)⁻¹ * (j : ZMod p)⁻¹ := by
          rw [sq, Finset.sum_mul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ hk, sq]
        have hsplit : ∑ k ∈ Finset.Ico 1 p, ∑ j ∈ (Finset.Ico 1 p).erase k,
              (k : ZMod p)⁻¹ * (j : ZMod p)⁻¹ = (2 : ZMod p) * A := by
          have hgt : ∑ k ∈ Finset.Ico 1 p, ∑ j ∈ (Finset.Ico 1 p).erase k,
                (if j < k then (k : ZMod p)⁻¹ * (j : ZMod p)⁻¹ else 0) = A := by
            dsimp only [A]
            rw [Finset.sum_sigma', Finset.sum_sigma']
            refine Finset.sum_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
            · rintro ⟨k, j⟩ hp
              simp only [Finset.mem_sigma, Finset.mem_erase] at hp ⊢
              exact ⟨hp.2.2, hp.2.1.symm, hp.1⟩
            · rintro ⟨k, j⟩ hp
              simp only [Finset.mem_sigma, Finset.mem_erase] at hp ⊢
              exact ⟨hp.2.2, hp.2.1.symm, hp.1⟩
            · rintro ⟨k, j⟩ _; rfl
            · rintro ⟨k, j⟩ _; rfl
            · rintro ⟨k, j⟩ _
              dsimp only
              split_ifs
              · ring
              · rfl
          rw [two_mul]
          conv_rhs => rhs; rw [← hgt]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : j ≠ k := (Finset.mem_erase.mp hj).1
          rcases lt_or_gt_of_ne hne with h1 | h2
          · have hnot : ¬ (k < j) := by omega
            simp [h1, hnot]
          · have hnot : ¬ (j < k) := by omega
            simp [h2, hnot]
        rw [hsq, hsplit, add_sub_cancel_left]
      have hs1 : ∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹ = 0 := by
        simpa using OeisA224274R1H1Proof.sum_inv_pow_eq_zero_zmod hp hp5 (Or.inl rfl)
      have hs2 : ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 = 0 :=
        OeisA224274R1H1Proof.sum_inv_pow_eq_zero_zmod hp hp5 (Or.inr rfl)
      rw [hs1, hs2, zero_pow (by decide), sub_zero] at h2A
      exact (mul_eq_zero.mp h2A).resolve_left h2ne0
    have hkill := hkill_p2 S2 hS2_proj1
    calc (3 * p : ZMod (p ^ 3)) ^ 2 * S2
        = (9 : ZMod (p ^ 3)) * (((p : ZMod (p ^ 3)) ^ 2) * S2) := by ring
      _ = 0 := by rw [hkill, mul_zero]
  rw [hterm1, hterm2, add_zero, add_zero]
