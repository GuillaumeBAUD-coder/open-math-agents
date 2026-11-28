import OMAStatements.S_oeis_a179077

open Finset PowerSeries
open scoped PowerSeries

namespace OMA.A179077

open OMA.S_oeis_a179077

/-
The Genocchi exponential generating function is twice the difference between
the Bernoulli series at X and at 2X. At p − 1, von Staudt–Clausen expresses the
Bernoulli value as an integer minus a sum of prime reciprocals. Multiplication
by 2^p − 2 clears all these denominators. Modulo p, only its own reciprocal term survives.
-/

private theorem genocchiEq (n : ℕ) :
    genocchi n = 2 * (1 - (2 : ℚ) ^ n) * bernoulli n := by
  let B := bernoulliPowerSeries ℚ
  let E := exp ℚ
  let R := rescale (2 : ℚ) B
  have htwo : (2 : PowerSeries ℚ) = C (2 : ℚ) := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
    norm_num
  have hB : B * (E - 1) = X := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hR := congrArg (rescale (2 : ℚ)) hB
  simp only [map_mul, map_sub, map_one, rescale_X, ← htwo] at hR
  have hE : rescale (2 : ℚ) E = E ^ 2 := by
    simpa [E] using (exp_pow_eq_rescale_exp (A := ℚ) 2).symm
  rw [hE] at hR
  change R * (E ^ 2 - 1) = 2 * X at hR
  have hne : E - 1 ≠ 0 := by
    intro h
    have h' := congrArg (coeff 1) h
    norm_num [E, coeff_exp, coeff_one] at h'
  have hG : (2 * B - 2 * R) * (E + 1) = 2 * X := by
    apply mul_right_cancel₀ hne
    linear_combination 2 * (E + 1) * hB - 2 * hR
  have hInv : (E + 1) * (E + 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp [E])
  have hPS : 2 * X * (E + 1)⁻¹ = 2 * B - 2 * R := by
    linear_combination (2 * B - 2 * R) * hInv - (E + 1)⁻¹ * hG
  change (n.factorial : ℚ) * coeff n (2 * X * (E + 1)⁻¹) = _
  rw [hPS, map_sub, htwo, coeff_C_mul, coeff_C_mul]
  simp only [R, coeff_rescale, B, bernoulliPowerSeries, coeff_mk, Algebra.algebraMap_self,
    RingHom.id_apply]
  have hfact : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  <;> ring

private def numerator (e : ℕ) : ℤ := 2 * ((2 : ℤ) ^ e - 1)

private theorem numeratorEq {p : ℕ} (hp : p.Prime) :
    numerator (p - 1) = (2 : ℤ) ^ p - 2 := by
  unfold numerator
  rw [← Nat.sub_add_cancel hp.one_lt.le, pow_succ]
  simp
  ring

private theorem primeDvdNumerator {e q : ℕ} (hq : q.Prime) (hqe : (q - 1) ∣ e) :
    (q : ℤ) ∣ numerator e := by
  let : Fact q.Prime := ⟨hq⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [numerator, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Int.cast_one]
  by_cases hz : (2 : ZMod q) = 0
  · rw [hz, zero_mul]
  · obtain ⟨j, rfl⟩ := hqe
    rw [pow_mul, ZMod.pow_card_sub_one_eq_one hz, one_pow, sub_self, mul_zero]

private theorem primeCase {p : ℕ} (hp : p.Prime) :
    ∃ g : ℤ, (g : ℚ) = genocchi (p - 1) ∧
      (((2 : ℤ) ^ p - 2) / (p : ℤ)) % (p : ℤ) = g % (p : ℤ) := by
  by_cases htwo : p = 2
  · subst p
    refine ⟨1, ?_, by norm_num⟩
    norm_num [genocchiEq, bernoulli_one]
  let : Fact p.Prime := ⟨hp⟩
  let e := p - 1
  let k := e / 2
  have he : 2 * k = e := by
    have hmod := hp.mod_two_eq_one_iff_ne_two.mpr htwo
    have hmin := hp.two_le
    dsimp [k, e]
    omega
  let S := (range (e + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ e
  let d := numerator e
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  rw [he] at hz
  change (z : ℚ) = bernoulli e + ∑ q ∈ S, (1 : ℚ) / q at hz
  have hd (q : ℕ) (hq : q ∈ S) : (q : ℤ) ∣ d := by
    have hgood := (mem_filter.mp hq).2
    exact primeDvdNumerator hgood.1 hgood.2
  let g : ℤ := -(d * z) + ∑ q ∈ S, d / (q : ℤ)
  have hsum :
      (∑ q ∈ S, ((d / (q : ℤ) : ℤ) : ℚ)) = ∑ q ∈ S, (d : ℚ) * ((1 : ℚ) / q) := by
    apply sum_congr rfl
    intro q hq
    rw [Int.cast_div_charZero (hd q hq), Int.cast_natCast]
    ring
  refine ⟨g, ?_, ?_⟩
  · change (g : ℚ) = genocchi e
    simp only [g, Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_sum]
    rw [hsum, ← mul_sum, genocchiEq]
    have hcast : (d : ℚ) = 2 * ((2 : ℚ) ^ e - 1) := by
      simp [d, numerator]
    rw [hcast]
    linear_combination -(2 * ((2 : ℚ) ^ e - 1)) * hz
  · rw [← numeratorEq hp]
    change (d / (p : ℤ)) ≡ g [ZMOD (p : ℤ)]
    apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    have hpS : p ∈ S := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr ?_, hp, dvd_refl _⟩
      dsimp [e]
      omega
    have hdz : (d : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hd p hpS)
    have hqz (q : ℕ) (hq : q ∈ S) (hqp : q ≠ p) :
        ((d / (q : ℤ) : ℤ) : ZMod p) = 0 := by
      have hqP := (mem_filter.mp hq).2.1
      have hqL := mem_range.mp (mem_filter.mp hq).1
      have hqLt : q < p := by
        have hpPos := hp.pos
        dsimp [e] at hqL
        omega
      have hqNZ : (q : ZMod p) ≠ 0 := by
        intro h
        exact (not_le_of_gt hqLt) (Nat.le_of_dvd hqP.pos
          ((CharP.cast_eq_zero_iff (ZMod p) p q).mp h))
      have hm : ((d / (q : ℤ) : ℤ) : ZMod p) * (q : ZMod p) = 0 := by
        simpa only [Int.cast_mul, Int.cast_natCast, hdz] using
          congrArg (fun v : ℤ => (v : ZMod p)) (Int.ediv_mul_cancel (hd q hq))
      exact (mul_eq_zero.mp hm).resolve_right hqNZ
    simp only [g, Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_sum, hdz,
      zero_mul, neg_zero, zero_add]
    rw [sum_eq_single_of_mem p hpS hqz]

theorem solution : type_of% @OMA.S_oeis_a179077.main := by
  intro n _
  have hp : (prime n).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  simpa [a] using primeCase hp

end OMA.A179077

theorem OMA.solution : type_of% @OMA.S_oeis_a179077.main := OMA.A179077.solution
