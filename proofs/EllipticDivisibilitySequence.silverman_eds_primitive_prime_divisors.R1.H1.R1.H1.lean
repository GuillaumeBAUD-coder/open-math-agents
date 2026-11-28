import OMAReductions.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H1_R1

/-!
# Proof of `EllipticDivisibilitySequence.silverman_eds_primitive_prime_divisors.R1.H1.R1.H1`

Uses Ward's elliptic recurrence and `ward_rank` to prove that for any prime `p` outside
`{2, 3} ∪ |W 2|.primeFactors ∪ |W 3|.primeFactors` dividing `W n`, the quotient sequence
`A k = W (k * n) / W n` satisfies `A k ≡ k * γ ^ ((k^2 - 1) / 2)` (odd `k`) and
`A k ≡ (k / 2) * A 2 * γ ^ ((k^2 - 4) / 2)` (even `k`) modulo `p`, where
`γ = -W (n + 1) * W (n - 1)` is a `p`-adic unit. In particular `p ∤ A k` whenever `p.Coprime k`.
-/

-- Step EllipticDivisibilitySequence.silverman_eds_primitive_prime_divisors.R1.H1.R1.H1
-- Credit: @KevinBigham

namespace SilvermanEDSR1H1R1H1

open EllipticDivisibilitySequence

private lemma W_zero_and_neg {W : ℤ → ℤ} (hw : IsNonsingularEDS W) :
    W 0 = 0 ∧ ∀ m : ℤ, W (-m) = -W m := by
  obtain ⟨_, _, E, x, y, _, _, hψ⟩ := hw
  constructor
  · have h0 : (W 0 : ℚ) = 0 := by
      rw [hψ 0, WeierstrassCurve.ψ_zero]
      simp [Polynomial.evalEval]
    exact_mod_cast h0
  · intro m
    have hm : (W (-m) : ℚ) = -(W m : ℚ) := by
      rw [hψ (-m), hψ m, WeierstrassCurve.ψ_neg]
      simp [Polynomial.evalEval]
    exact_mod_cast hm

private lemma ward_rel {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W) (h1 : W 1 = 1) (a b : ℤ) :
    W (a + b) * W (a - b) = W (a + 1) * W (a - 1) * W b ^ 2 - W (b + 1) * W (b - 1) * W a ^ 2 := by
  have rel := hw.1 a b 1
  simp only [IsEllipticNet.rel, add_zero, h1, mul_one] at rel
  linear_combination rel

private lemma dvd_int_iff_dvd_natAbs (p : ℕ) (x : ℤ) : (p : ℤ) ∣ x ↔ p ∣ x.natAbs :=
  Int.dvd_natAbs.symm.trans Int.natCast_dvd_natCast

private lemma isUnit_intCast_zmod_sq {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) :
    IsUnit ((x : ℤ) : ZMod (p ^ 2)) := by
  have hndvd : ¬ p ∣ x.natAbs := fun h => hx ((dvd_int_iff_dvd_natAbs p x).mpr h)
  have hcop : Nat.Coprime x.natAbs (p ^ 2) :=
    ((hp.coprime_iff_not_dvd.mpr hndvd).pow_left 2).symm
  have hcopZ : IsCoprime x ((p ^ 2 : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop
  obtain ⟨a, b, hab⟩ := hcopZ
  have hmod : ((a : ℤ) : ZMod (p ^ 2)) * (x : ZMod (p ^ 2)) = 1 := by
    have h := congrArg (fun t : ℤ => (t : ZMod (p ^ 2))) hab
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
      add_zero, Int.cast_one] at h
    exact h
  exact ⟨⟨((x : ℤ) : ZMod (p ^ 2)), (a : ZMod (p ^ 2)), by rw [mul_comm]; exact hmod, hmod⟩, rfl⟩

private lemma intCast_zmod_sq_zero_of_dvd {p : ℕ} {x : ℤ} (hx : (p : ℤ) ∣ x) :
    ((x ^ 2 : ℤ) : ZMod (p ^ 2)) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 : (p : ℤ) ^ 2 ∣ x ^ 2 := pow_dvd_pow_of_dvd hx 2
  simpa using h2

private lemma A2_sq_mod_sq {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W) (h1 : W 1 = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ (W 2).natAbs) (hp3 : ¬ p ∣ (W 3).natAbs)
    {n : ℕ} (hWn_ne : W (n : ℤ) ≠ 0) (hpWn : p ∣ (W (n : ℤ)).natAbs) :
    let γ : ℤ := -(W ((n : ℤ) + 1) * W ((n : ℤ) - 1))
    let A2 : ℤ := W (2 * (n : ℤ)) / W (n : ℤ)
    ((A2 : ℤ) : ZMod (p ^ 2)) ^ 2 = 4 * ((γ : ℤ) : ZMod (p ^ 2)) ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  intro γ A2
  have hpWnZ : (p : ℤ) ∣ W (n : ℤ) := (dvd_int_iff_dvd_natAbs p _).mpr hpWn
  have hp2Z : ¬ (p : ℤ) ∣ W 2 := fun h => hp2 ((dvd_int_iff_dvd_natAbs p _).mp h)
  have hp3Z : ¬ (p : ℤ) ∣ W 3 := fun h => hp3 ((dvd_int_iff_dvd_natAbs p _).mp h)
  have hz (m : ℤ) : ((W m : ℤ) : ZMod p) = 0 ↔ (p : ℤ) ∣ W m := ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hzn : ((W (n : ℤ) : ℤ) : ZMod p) = 0 := (hz _).mpr hpWnZ
  have hz3 : ((W 3 : ℤ) : ZMod p) ≠ 0 := fun h => hp3Z ((hz 3).mp h)
  let X : ℤ := W ((n : ℤ) + 2) * W ((n : ℤ) - 1) ^ 2
  let Y : ℤ := W ((n : ℤ) - 2) * W ((n : ℤ) + 1) ^ 2
  have hX_sq_p : ((X : ℤ) : ZMod p) ^ 2 = ((γ : ℤ) : ZMod p) ^ 3 * ((W 2 : ℤ) : ZMod p) ^ 2 := by
    have r1 := congrArg (fun t : ℤ => (t : ZMod p)) (ward_rel hw h1 ((n : ℤ) + 2) 2)
    have r2 := congrArg (fun t : ℤ => (t : ZMod p)) (ward_rel hw h1 ((n : ℤ) + 1) 2)
    have hr1 : ((W 3 : ℤ) : ZMod p) * ((W ((n : ℤ) + 2) : ℤ) : ZMod p) ^ 2 =
        ((W ((n : ℤ) + 3) : ℤ) : ZMod p) * ((W ((n : ℤ) + 1) : ℤ) : ZMod p) *
          ((W 2 : ℤ) : ZMod p) ^ 2 := by
      have hsub : (n : ℤ) + 2 - 2 = (n : ℤ) := by ring
      have hadd : (n : ℤ) + 2 + 1 = (n : ℤ) + 3 := by ring
      have hsub1 : (n : ℤ) + 2 - 1 = (n : ℤ) + 1 := by ring
      have h21 : (2 : ℤ) + 1 = 3 := by decide
      have h2m : (2 : ℤ) - 1 = 1 := by decide
      rw [hsub, hadd, hsub1, h21, h2m, h1] at r1
      simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, hzn, mul_zero, mul_one] at r1
      linear_combination r1
    have hr2 : ((W ((n : ℤ) + 3) : ℤ) : ZMod p) * ((W ((n : ℤ) - 1) : ℤ) : ZMod p) =
        -((W 3 : ℤ) : ZMod p) * ((W ((n : ℤ) + 1) : ℤ) : ZMod p) ^ 2 := by
      have hadd : (n : ℤ) + 1 + 2 = (n : ℤ) + 3 := by ring
      have hsub : (n : ℤ) + 1 - 2 = (n : ℤ) - 1 := by ring
      have hadd1 : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by ring
      have hsub1 : (n : ℤ) + 1 - 1 = (n : ℤ) := by ring
      have h21 : (2 : ℤ) + 1 = 3 := by decide
      have h2m : (2 : ℤ) - 1 = 1 := by decide
      rw [hadd, hsub, hadd1, hsub1, h21, h2m, h1] at r2
      simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, hzn, mul_zero,
        zero_mul, mul_one, zero_sub] at r2
      linear_combination r2
    apply mul_left_cancel₀ hz3
    dsimp only [X, γ]
    push_cast
    linear_combination
      ((W ((n : ℤ) - 1) : ℤ) : ZMod p) ^ 4 * hr1 +
      ((W ((n : ℤ) + 1) : ℤ) : ZMod p) * ((W ((n : ℤ) - 1) : ℤ) : ZMod p) ^ 3 *
        ((W 2 : ℤ) : ZMod p) ^ 2 * hr2
  have hY_sq_p : ((Y : ℤ) : ZMod p) ^ 2 = ((γ : ℤ) : ZMod p) ^ 3 * ((W 2 : ℤ) : ZMod p) ^ 2 := by
    have r1 := congrArg (fun t : ℤ => (t : ZMod p)) (ward_rel hw h1 ((n : ℤ) - 2) 2)
    have r2 := congrArg (fun t : ℤ => (t : ZMod p)) (ward_rel hw h1 ((n : ℤ) - 1) 2)
    have hr1 : ((W 3 : ℤ) : ZMod p) * ((W ((n : ℤ) - 2) : ℤ) : ZMod p) ^ 2 =
        ((W ((n : ℤ) - 1) : ℤ) : ZMod p) * ((W ((n : ℤ) - 3) : ℤ) : ZMod p) *
          ((W 2 : ℤ) : ZMod p) ^ 2 := by
      have hadd : (n : ℤ) - 2 + 2 = (n : ℤ) := by ring
      have hadd1 : (n : ℤ) - 2 + 1 = (n : ℤ) - 1 := by ring
      have hsub1 : (n : ℤ) - 2 - 1 = (n : ℤ) - 3 := by ring
      have h21 : (2 : ℤ) + 1 = 3 := by decide
      have h2m : (2 : ℤ) - 1 = 1 := by decide
      rw [hadd, hadd1, hsub1, h21, h2m, h1] at r1
      simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, hzn, zero_mul, mul_one] at r1
      linear_combination r1
    have hr2 : ((W ((n : ℤ) + 1) : ℤ) : ZMod p) * ((W ((n : ℤ) - 3) : ℤ) : ZMod p) =
        -((W 3 : ℤ) : ZMod p) * ((W ((n : ℤ) - 1) : ℤ) : ZMod p) ^ 2 := by
      have hadd : (n : ℤ) - 1 + 2 = (n : ℤ) + 1 := by ring
      have hsub : (n : ℤ) - 1 - 2 = (n : ℤ) - 3 := by ring
      have hadd1 : (n : ℤ) - 1 + 1 = (n : ℤ) := by ring
      have hsub1 : (n : ℤ) - 1 - 1 = (n : ℤ) - 2 := by ring
      have h21 : (2 : ℤ) + 1 = 3 := by decide
      have h2m : (2 : ℤ) - 1 = 1 := by decide
      rw [hadd, hsub, hadd1, hsub1, h21, h2m, h1] at r2
      simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, hzn, zero_mul,
        mul_one, zero_sub] at r2
      linear_combination r2
    apply mul_left_cancel₀ hz3
    dsimp only [Y, γ]
    push_cast
    linear_combination
      ((W ((n : ℤ) + 1) : ℤ) : ZMod p) ^ 4 * hr1 +
      ((W ((n : ℤ) + 1) : ℤ) : ZMod p) ^ 3 * ((W ((n : ℤ) - 1) : ℤ) : ZMod p) *
        ((W 2 : ℤ) : ZMod p) ^ 2 * hr2
  have hXY_int : X * Y = -(γ ^ 3 * W 2 ^ 2) - W 3 * W (n : ℤ) ^ 2 * (W ((n : ℤ) + 1) ^ 2 * W ((n : ℤ) - 1) ^ 2) := by
    have r := ward_rel hw h1 (n : ℤ) 2
    have h21 : (2 : ℤ) + 1 = 3 := by decide
    have h2m : (2 : ℤ) - 1 = 1 := by decide
    rw [h21, h2m, h1, mul_one] at r
    dsimp only [X, Y, γ]
    linear_combination W ((n : ℤ) + 1) ^ 2 * W ((n : ℤ) - 1) ^ 2 * r
  have hXY_p : ((X : ℤ) : ZMod p) * ((Y : ℤ) : ZMod p) =
      -(((γ : ℤ) : ZMod p) ^ 3 * ((W 2 : ℤ) : ZMod p) ^ 2) := by
    have h := congrArg (fun t : ℤ => (t : ZMod p)) hXY_int
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_neg, Int.cast_pow, hzn, zero_pow two_ne_zero,
      mul_zero, zero_mul, sub_zero] at h
    exact h
  have hXY_p2 : ((X : ℤ) : ZMod (p ^ 2)) * ((Y : ℤ) : ZMod (p ^ 2)) =
      -(((γ : ℤ) : ZMod (p ^ 2)) ^ 3 * ((W 2 : ℤ) : ZMod (p ^ 2)) ^ 2) := by
    have h := congrArg (fun t : ℤ => (t : ZMod (p ^ 2))) hXY_int
    have hwn2 : ((W (n : ℤ) ^ 2 : ℤ) : ZMod (p ^ 2)) = 0 := intCast_zmod_sq_zero_of_dvd hpWnZ
    have hwn2' : ((W (n : ℤ) : ℤ) : ZMod (p ^ 2)) ^ 2 = 0 := by simpa using hwn2
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_neg, Int.cast_pow, hwn2', mul_zero,
      zero_mul, sub_zero] at h
    exact h
  have hXpY_p : ((X + Y : ℤ) : ZMod p) = 0 := by
    have hsq : (((X + Y : ℤ) : ZMod p)) ^ 2 = 0 := by
      push_cast
      linear_combination hX_sq_p + hY_sq_p + 2 * hXY_p
    exact sq_eq_zero_iff.mp hsq
  have hXpY_dvd : (p : ℤ) ∣ X + Y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hXpY_p
  have hXpY_sq_p2 : (((X + Y : ℤ) : ZMod (p ^ 2))) ^ 2 = 0 := by
    simpa using intCast_zmod_sq_zero_of_dvd hXpY_dvd
  have hA2W2 : A2 * W 2 = X - Y := by
    have hdvd : W (n : ℤ) ∣ W (2 * (n : ℤ)) := hw.2 (n : ℤ) (2 * (n : ℤ)) (dvd_mul_left _ 2)
    have hmul : W (n : ℤ) * A2 = W (2 * (n : ℤ)) := Int.mul_ediv_cancel' hdvd
    have heven := hw.1 ((n : ℤ) + 1) ((n : ℤ) - 1) 1
    rw [IsEllipticNet.rel_even, h1, one_pow, mul_one] at heven
    have hzero : W (n : ℤ) * (A2 * W 2 - (X - Y)) = 0 := by
      dsimp only [X, Y]
      linear_combination heven + W 2 * hmul
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hWn_ne)
  have hsq_eq : ((A2 : ℤ) : ZMod (p ^ 2)) ^ 2 * ((W 2 : ℤ) : ZMod (p ^ 2)) ^ 2 =
      4 * ((γ : ℤ) : ZMod (p ^ 2)) ^ 3 * ((W 2 : ℤ) : ZMod (p ^ 2)) ^ 2 := by
    have h := congrArg (fun t : ℤ => (t : ZMod (p ^ 2))) hA2W2
    push_cast at h hXpY_sq_p2 ⊢
    linear_combination
      (((A2 : ℤ) : ZMod (p ^ 2)) * ((W 2 : ℤ) : ZMod (p ^ 2)) +
        (((X : ℤ) : ZMod (p ^ 2)) - ((Y : ℤ) : ZMod (p ^ 2)))) * h +
      hXpY_sq_p2 - 4 * hXY_p2
  have hu : IsUnit (((W 2 : ℤ) : ZMod (p ^ 2)) ^ 2) := (isUnit_intCast_zmod_sq hp hp2Z).pow 2
  exact hu.mul_right_cancel hsq_eq

private lemma neighbor_prod_mod_sq {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W) (h1 : W 1 = 1)
    (hneg : ∀ m : ℤ, W (-m) = -W m)
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hpWn : p ∣ (W (n : ℤ)).natAbs)
    (hγ_ndvd : ¬ (p : ℤ) ∣ -(W ((n : ℤ) + 1) * W ((n : ℤ) - 1))) (k : ℕ) :
    let γ : ℤ := -(W ((n : ℤ) + 1) * W ((n : ℤ) - 1))
    ((W ((k : ℤ) * (n : ℤ) + 1) * W ((k : ℤ) * (n : ℤ) - 1) : ℤ) : ZMod (p ^ 2)) =
      -((γ : ℤ) : ZMod (p ^ 2)) ^ (k ^ 2) := by
  intro γ
  have hpWnZ : (p : ℤ) ∣ W (n : ℤ) := (dvd_int_iff_dvd_natAbs p _).mpr hpWn
  have hwn2 : ((W (n : ℤ) : ℤ) : ZMod (p ^ 2)) ^ 2 = 0 := by
    simpa using intCast_zmod_sq_zero_of_dvd hpWnZ
  let c (j : ℤ) : ZMod (p ^ 2) := ((W (j * (n : ℤ) + 1) : ℤ) : ZMod (p ^ 2))
  have hc_rec (j : ℤ) : c (j + 1) * c (j - 1) = ((γ : ℤ) : ZMod (p ^ 2)) * c j ^ 2 := by
    have r := congrArg (fun t : ℤ => (t : ZMod (p ^ 2))) (ward_rel hw h1 (j * (n : ℤ) + 1) (n : ℤ))
    have h1' : j * (n : ℤ) + 1 + (n : ℤ) = (j + 1) * (n : ℤ) + 1 := by ring
    have h2' : j * (n : ℤ) + 1 - (n : ℤ) = (j - 1) * (n : ℤ) + 1 := by ring
    rw [h1', h2'] at r
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, hwn2, mul_zero, zero_sub] at r
    dsimp only [c, γ]
    push_cast
    linear_combination r
  have hpair : ∀ m : ℕ, c (m : ℤ) * c (-(m : ℤ)) = ((γ : ℤ) : ZMod (p ^ 2)) ^ (m ^ 2) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      match m with
      | 0 =>
        simp [c, h1]
      | 1 =>
        dsimp only [c, γ]
        have hneg1 : (-1 : ℤ) * (n : ℤ) + 1 = -((n : ℤ) - 1) := by ring
        simp only [Nat.cast_one, one_mul]
        rw [hneg1, hneg]
        push_cast
        ring
      | m + 2 =>
        have hprev := ih m (by omega)
        have hmid := ih (m + 1) (by omega)
        have rpos := hc_rec ((m : ℤ) + 1)
        have rneg := hc_rec (-((m : ℤ) + 1))
        have hstep1 : c (((m + 2 : ℕ) : ℤ)) * c (m : ℤ) =
            ((γ : ℤ) : ZMod (p ^ 2)) * c (((m + 1 : ℕ) : ℤ)) ^ 2 := by
          have e1 : ((m : ℤ) + 1) + 1 = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
          have e2 : ((m : ℤ) + 1) - 1 = (m : ℤ) := by ring
          have e3 : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [e1, e2, e3] at rpos
          exact rpos
        have hstep2 : c (-((m : ℤ))) * c (-((m + 2 : ℕ) : ℤ)) =
            ((γ : ℤ) : ZMod (p ^ 2)) * c (-((m + 1 : ℕ) : ℤ)) ^ 2 := by
          have e1 : -((m : ℤ) + 1) + 1 = -(m : ℤ) := by ring
          have e2 : -((m : ℤ) + 1) - 1 = -((m + 2 : ℕ) : ℤ) := by push_cast; ring
          have e3 : -((m : ℤ) + 1) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [e1, e2, e3] at rneg
          exact rneg
        have hmul : (c (((m + 2 : ℕ) : ℤ)) * c (-((m + 2 : ℕ) : ℤ))) *
            (c (m : ℤ) * c (-(m : ℤ))) =
            ((γ : ℤ) : ZMod (p ^ 2)) ^ ((m + 2) ^ 2) * ((γ : ℤ) : ZMod (p ^ 2)) ^ (m ^ 2) := by
          calc
            (c (((m + 2 : ℕ) : ℤ)) * c (-((m + 2 : ℕ) : ℤ))) * (c (m : ℤ) * c (-(m : ℤ)))
                = (c (((m + 2 : ℕ) : ℤ)) * c (m : ℤ)) * (c (-(m : ℤ)) * c (-((m + 2 : ℕ) : ℤ))) := by
                  ring
            _ = (((γ : ℤ) : ZMod (p ^ 2)) * c (((m + 1 : ℕ) : ℤ)) ^ 2) *
                (((γ : ℤ) : ZMod (p ^ 2)) * c (-((m + 1 : ℕ) : ℤ)) ^ 2) := by
                  rw [hstep1, hstep2]
            _ = ((γ : ℤ) : ZMod (p ^ 2)) ^ 2 *
                (c (((m + 1 : ℕ) : ℤ)) * c (-((m + 1 : ℕ) : ℤ))) ^ 2 := by ring
            _ = ((γ : ℤ) : ZMod (p ^ 2)) ^ 2 *
                (((γ : ℤ) : ZMod (p ^ 2)) ^ ((m + 1) ^ 2)) ^ 2 := by rw [hmid]
            _ = ((γ : ℤ) : ZMod (p ^ 2)) ^ (2 + 2 * (m + 1) ^ 2) := by
                  rw [← pow_mul, ← pow_add]; ring_nf
            _ = ((γ : ℤ) : ZMod (p ^ 2)) ^ ((m + 2) ^ 2 + m ^ 2) := by
                  congr 1; ring
            _ = ((γ : ℤ) : ZMod (p ^ 2)) ^ ((m + 2) ^ 2) *
                ((γ : ℤ) : ZMod (p ^ 2)) ^ (m ^ 2) := pow_add _ _ _
        rw [hprev] at hmul
        have hu : IsUnit (((γ : ℤ) : ZMod (p ^ 2)) ^ (m ^ 2)) :=
          (isUnit_intCast_zmod_sq hp hγ_ndvd).pow (m ^ 2)
        exact hu.mul_right_cancel hmul
  have hspec := hpair k
  have hnegk : -((k : ℤ)) * (n : ℤ) + 1 = -((k : ℤ) * (n : ℤ) - 1) := by ring
  dsimp only [c] at hspec
  rw [hnegk, hneg] at hspec
  push_cast at hspec ⊢
  linear_combination -hspec

private def modelF {R : Type*} [CommRing R] (γ a2 : R) (m : ℕ) : R :=
  if m = 0 then 0
  else if m % 2 = 1 then (m : R) * γ ^ ((m ^ 2 - 1) / 2)
  else ((m / 2 : ℕ) : R) * a2 * γ ^ ((m ^ 2 - 4) / 2)

private lemma modelF_sq {R : Type*} [CommRing R] {γ a2 : R} (ha2 : a2 ^ 2 = 4 * γ ^ 3)
    {m : ℕ} (hm : 1 ≤ m) :
    modelF γ a2 m ^ 2 = (m : R) ^ 2 * γ ^ (m ^ 2 - 1) := by
  have hm0 : m ≠ 0 := by omega
  unfold modelF
  rw [if_neg hm0]
  by_cases hodd : m % 2 = 1
  · rw [if_pos hodd]
    have hdiv : 2 * ((m ^ 2 - 1) / 2) = m ^ 2 - 1 := by
      have hm2 : (m ^ 2 - 1) % 2 = 0 := by
        obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
        have : (2 * t + 1) ^ 2 - 1 = 2 * (2 * t ^ 2 + 2 * t) := by
          have : (2 * t + 1) ^ 2 = 2 * (2 * t ^ 2 + 2 * t) + 1 := by ring
          omega
        omega
      omega
    calc
      ((m : R) * γ ^ ((m ^ 2 - 1) / 2)) ^ 2
          = (m : R) ^ 2 * γ ^ (2 * ((m ^ 2 - 1) / 2)) := by
            rw [mul_pow, ← pow_mul, mul_comm _ 2]
      _ = (m : R) ^ 2 * γ ^ (m ^ 2 - 1) := by rw [hdiv]
  · rw [if_neg hodd]
    obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t := ⟨m / 2, by omega⟩
    have ht : 1 ≤ t := by omega
    have hdiv : 2 * (((2 * t) ^ 2 - 4) / 2) + 3 = (2 * t) ^ 2 - 1 := by
      have h1 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      have h2 : 4 ≤ 4 * t ^ 2 := by nlinarith
      omega
    have hhalf : (2 * t) / 2 = t := by omega
    rw [hhalf]
    calc
      ((t : R) * a2 * γ ^ (((2 * t) ^ 2 - 4) / 2)) ^ 2
          = (t : R) ^ 2 * a2 ^ 2 * γ ^ (2 * (((2 * t) ^ 2 - 4) / 2)) := by
            rw [mul_pow, mul_pow, ← pow_mul, mul_comm _ 2]
      _ = (t : R) ^ 2 * (4 * γ ^ 3) * γ ^ (2 * (((2 * t) ^ 2 - 4) / 2)) := by rw [ha2]
      _ = ((2 * t : ℕ) : R) ^ 2 * (γ ^ (2 * (((2 * t) ^ 2 - 4) / 2)) * γ ^ 3) := by
            push_cast; ring
      _ = ((2 * t : ℕ) : R) ^ 2 * γ ^ (2 * (((2 * t) ^ 2 - 4) / 2) + 3) := by rw [← pow_add]
      _ = ((2 * t : ℕ) : R) ^ 2 * γ ^ ((2 * t) ^ 2 - 1) := by rw [hdiv]

private lemma modelF_one_step {R : Type*} [CommRing R] {γ a2 : R} (ha2 : a2 ^ 2 = 4 * γ ^ 3)
    {k : ℕ} (hk : 2 ≤ k) :
    modelF γ a2 (k + 1) * modelF γ a2 (k - 1) = γ * modelF γ a2 k ^ 2 - γ ^ (k ^ 2) := by
  have hrhs : γ * modelF γ a2 k ^ 2 - γ ^ (k ^ 2) = ((k : R) ^ 2 - 1) * γ ^ (k ^ 2) := by
    rw [modelF_sq ha2 (by omega)]
    have hpow : γ * γ ^ (k ^ 2 - 1) = γ ^ (k ^ 2) := by
      have hk1 : 1 ≤ k ^ 2 := by nlinarith
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk1]
    calc
      γ * ((k : R) ^ 2 * γ ^ (k ^ 2 - 1)) - γ ^ (k ^ 2)
          = (k : R) ^ 2 * (γ * γ ^ (k ^ 2 - 1)) - γ ^ (k ^ 2) := by ring
      _ = (k : R) ^ 2 * γ ^ (k ^ 2) - γ ^ (k ^ 2) := by rw [hpow]
      _ = ((k : R) ^ 2 - 1) * γ ^ (k ^ 2) := by ring
  rw [hrhs]
  unfold modelF
  rw [if_neg (by omega : k + 1 ≠ 0), if_neg (by omega : k - 1 ≠ 0)]
  by_cases hodd : k % 2 = 0
  · obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t := ⟨k / 2, by omega⟩
    have ht : 1 ≤ t := by omega
    rw [if_pos (by omega : (2 * t + 1) % 2 = 1), if_pos (by omega : (2 * t - 1) % 2 = 1)]
    have hexp : ((2 * t + 1) ^ 2 - 1) / 2 + ((2 * t - 1) ^ 2 - 1) / 2 = (2 * t) ^ 2 := by
      have h1 : (2 * t + 1) ^ 2 - 1 = 2 * (2 * t ^ 2 + 2 * t) := by
        have : (2 * t + 1) ^ 2 = 2 * (2 * t ^ 2 + 2 * t) + 1 := by ring
        omega
      have h2 : (2 * t - 1) ^ 2 - 1 = 2 * (2 * t ^ 2 - 2 * t) := by
        have : (2 * t - 1) + 1 = 2 * t := by omega
        have hsq : (2 * t - 1) ^ 2 + 4 * t = 4 * t ^ 2 + 1 := by nlinarith
        have hge : 2 * t ≤ 2 * t ^ 2 := by nlinarith
        omega
      have h3 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      have hge : 2 * t ≤ 2 * t ^ 2 := by nlinarith
      omega
    have hcoeff : ((2 * t + 1 : ℕ) : R) * ((2 * t - 1 : ℕ) : R) = ((2 * t : ℕ) : R) ^ 2 - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * t)]
      push_cast
      ring
    calc
      ((2 * t + 1 : ℕ) : R) * γ ^ (((2 * t + 1) ^ 2 - 1) / 2) *
          (((2 * t - 1 : ℕ) : R) * γ ^ (((2 * t - 1) ^ 2 - 1) / 2))
          = (((2 * t + 1 : ℕ) : R) * ((2 * t - 1 : ℕ) : R)) *
            (γ ^ (((2 * t + 1) ^ 2 - 1) / 2) * γ ^ (((2 * t - 1) ^ 2 - 1) / 2)) := by ring
      _ = (((2 * t : ℕ) : R) ^ 2 - 1) *
            γ ^ (((2 * t + 1) ^ 2 - 1) / 2 + ((2 * t - 1) ^ 2 - 1) / 2) := by
          rw [hcoeff, pow_add]
      _ = (((2 * t : ℕ) : R) ^ 2 - 1) * γ ^ ((2 * t) ^ 2) := by rw [hexp]
  · obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t + 1 := ⟨k / 2, by omega⟩
    have ht : 1 ≤ t := by omega
    rw [if_neg (by omega : (2 * t + 1 + 1) % 2 ≠ 1), if_neg (by omega : (2 * t + 1 - 1) % 2 ≠ 1)]
    have hd1 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    have hd2 : (2 * t + 1 - 1) / 2 = t := by omega
    have hexp : ((2 * t + 1 + 1) ^ 2 - 4) / 2 + ((2 * t + 1 - 1) ^ 2 - 4) / 2 + 3 =
        (2 * t + 1) ^ 2 := by
      have e1 : 2 * t + 1 + 1 = 2 * (t + 1) := by omega
      have e2 : 2 * t + 1 - 1 = 2 * t := by omega
      rw [e1, e2]
      have s1 : (2 * (t + 1)) ^ 2 = 4 * t ^ 2 + 8 * t + 4 := by ring
      have s2 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      have s3 : (2 * t + 1) ^ 2 = 4 * t ^ 2 + 4 * t + 1 := by ring
      have hge : 4 ≤ 4 * t ^ 2 := by nlinarith
      omega
    rw [hd1, hd2]
    calc
      ((t + 1 : ℕ) : R) * a2 * γ ^ (((2 * t + 1 + 1) ^ 2 - 4) / 2) *
          ((t : R) * a2 * γ ^ (((2 * t + 1 - 1) ^ 2 - 4) / 2))
          = ((t + 1 : ℕ) : R) * (t : R) * a2 ^ 2 *
            (γ ^ (((2 * t + 1 + 1) ^ 2 - 4) / 2) * γ ^ (((2 * t + 1 - 1) ^ 2 - 4) / 2)) := by
            ring
      _ = ((t + 1 : ℕ) : R) * (t : R) * (4 * γ ^ 3) *
            γ ^ (((2 * t + 1 + 1) ^ 2 - 4) / 2 + ((2 * t + 1 - 1) ^ 2 - 4) / 2) := by
          rw [ha2, ← pow_add]
      _ = (((2 * t + 1 : ℕ) : R) ^ 2 - 1) *
            (γ ^ (((2 * t + 1 + 1) ^ 2 - 4) / 2 + ((2 * t + 1 - 1) ^ 2 - 4) / 2) * γ ^ 3) := by
          push_cast; ring
      _ = (((2 * t + 1 : ℕ) : R) ^ 2 - 1) *
            γ ^ (((2 * t + 1 + 1) ^ 2 - 4) / 2 + ((2 * t + 1 - 1) ^ 2 - 4) / 2 + 3) := by
          rw [← pow_add]
      _ = (((2 * t + 1 : ℕ) : R) ^ 2 - 1) * γ ^ ((2 * t + 1) ^ 2) := by rw [hexp]

private lemma modelF_two_step {R : Type*} [CommRing R] {γ a2 : R} (ha2 : a2 ^ 2 = 4 * γ ^ 3)
    {k : ℕ} (hk : 3 ≤ k) :
    modelF γ a2 (k + 2) * modelF γ a2 (k - 2) =
      -(γ ^ (k ^ 2) * a2 ^ 2) + γ ^ 4 * modelF γ a2 k ^ 2 := by
  have hrhs : -(γ ^ (k ^ 2) * a2 ^ 2) + γ ^ 4 * modelF γ a2 k ^ 2 =
      ((k : R) ^ 2 - 4) * γ ^ (k ^ 2 + 3) := by
    rw [modelF_sq ha2 (by omega), ha2]
    have hpow1 : γ ^ (k ^ 2) * γ ^ 3 = γ ^ (k ^ 2 + 3) := (pow_add γ _ _).symm
    have hpow2 : γ ^ 4 * γ ^ (k ^ 2 - 1) = γ ^ (k ^ 2 + 3) := by
      rw [← pow_add]
      congr 1
      have hk1 : 1 ≤ k ^ 2 := by nlinarith
      omega
    calc
      -(γ ^ (k ^ 2) * (4 * γ ^ 3)) + γ ^ 4 * ((k : R) ^ 2 * γ ^ (k ^ 2 - 1))
          = (k : R) ^ 2 * (γ ^ 4 * γ ^ (k ^ 2 - 1)) - 4 * (γ ^ (k ^ 2) * γ ^ 3) := by ring
      _ = (k : R) ^ 2 * γ ^ (k ^ 2 + 3) - 4 * γ ^ (k ^ 2 + 3) := by rw [hpow1, hpow2]
      _ = ((k : R) ^ 2 - 4) * γ ^ (k ^ 2 + 3) := by ring
  rw [hrhs]
  unfold modelF
  rw [if_neg (by omega : k + 2 ≠ 0), if_neg (by omega : k - 2 ≠ 0)]
  by_cases hodd : k % 2 = 1
  · obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t + 1 := ⟨k / 2, by omega⟩
    have ht : 1 ≤ t := by omega
    rw [if_pos (by omega : (2 * t + 1 + 2) % 2 = 1), if_pos (by omega : (2 * t + 1 - 2) % 2 = 1)]
    have hexp : ((2 * t + 1 + 2) ^ 2 - 1) / 2 + ((2 * t + 1 - 2) ^ 2 - 1) / 2 =
        (2 * t + 1) ^ 2 + 3 := by
      have e1 : 2 * t + 1 + 2 = 2 * t + 3 := by omega
      have e2 : 2 * t + 1 - 2 = 2 * t - 1 := by omega
      rw [e1, e2]
      have s1 : (2 * t + 3) ^ 2 - 1 = 2 * (2 * t ^ 2 + 6 * t + 4) := by
        have : (2 * t + 3) ^ 2 = 2 * (2 * t ^ 2 + 6 * t + 4) + 1 := by ring
        omega
      have s2 : (2 * t - 1) ^ 2 - 1 = 2 * (2 * t ^ 2 - 2 * t) := by
        have : (2 * t - 1) + 1 = 2 * t := by omega
        have hsq : (2 * t - 1) ^ 2 + 4 * t = 4 * t ^ 2 + 1 := by nlinarith
        have hge : 2 * t ≤ 2 * t ^ 2 := by nlinarith
        omega
      have s3 : (2 * t + 1) ^ 2 = 4 * t ^ 2 + 4 * t + 1 := by ring
      have hge : 2 * t ≤ 2 * t ^ 2 := by nlinarith
      omega
    have hcoeff : ((2 * t + 1 + 2 : ℕ) : R) * ((2 * t + 1 - 2 : ℕ) : R) =
        ((2 * t + 1 : ℕ) : R) ^ 2 - 4 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * t + 1)]
      push_cast
      ring
    calc
      ((2 * t + 1 + 2 : ℕ) : R) * γ ^ (((2 * t + 1 + 2) ^ 2 - 1) / 2) *
          (((2 * t + 1 - 2 : ℕ) : R) * γ ^ (((2 * t + 1 - 2) ^ 2 - 1) / 2))
          = (((2 * t + 1 + 2 : ℕ) : R) * ((2 * t + 1 - 2 : ℕ) : R)) *
            (γ ^ (((2 * t + 1 + 2) ^ 2 - 1) / 2) * γ ^ (((2 * t + 1 - 2) ^ 2 - 1) / 2)) := by
            ring
      _ = (((2 * t + 1 : ℕ) : R) ^ 2 - 4) *
            γ ^ (((2 * t + 1 + 2) ^ 2 - 1) / 2 + ((2 * t + 1 - 2) ^ 2 - 1) / 2) := by
          rw [hcoeff, pow_add]
      _ = (((2 * t + 1 : ℕ) : R) ^ 2 - 4) * γ ^ ((2 * t + 1) ^ 2 + 3) := by rw [hexp]
  · obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t := ⟨k / 2, by omega⟩
    have ht : 2 ≤ t := by omega
    rw [if_neg (by omega : (2 * t + 2) % 2 ≠ 1), if_neg (by omega : (2 * t - 2) % 2 ≠ 1)]
    have hd1 : (2 * t + 2) / 2 = t + 1 := by omega
    have hd2 : (2 * t - 2) / 2 = t - 1 := by omega
    have hexp : ((2 * t + 2) ^ 2 - 4) / 2 + ((2 * t - 2) ^ 2 - 4) / 2 + 3 =
        (2 * t) ^ 2 + 3 := by
      have s1 : (2 * t + 2) ^ 2 = 4 * t ^ 2 + 8 * t + 4 := by ring
      have s2 : (2 * t - 2) ^ 2 + 8 * t = 4 * t ^ 2 + 4 := by
        have : (2 * t - 2) + 2 = 2 * t := by omega
        nlinarith
      have s3 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      have hge1 : 8 * t ≤ 4 * t ^ 2 := by nlinarith
      have hge2 : 4 ≤ (2 * t - 2) ^ 2 := by nlinarith
      omega
    rw [hd1, hd2]
    have hcoeff : ((t + 1 : ℕ) : R) * ((t - 1 : ℕ) : R) * 4 = ((2 * t : ℕ) : R) ^ 2 - 4 := by
      rw [Nat.cast_sub (by omega : 1 ≤ t)]
      push_cast
      ring
    calc
      ((t + 1 : ℕ) : R) * a2 * γ ^ (((2 * t + 2) ^ 2 - 4) / 2) *
          (((t - 1 : ℕ) : R) * a2 * γ ^ (((2 * t - 2) ^ 2 - 4) / 2))
          = ((t + 1 : ℕ) : R) * ((t - 1 : ℕ) : R) * a2 ^ 2 *
            (γ ^ (((2 * t + 2) ^ 2 - 4) / 2) * γ ^ (((2 * t - 2) ^ 2 - 4) / 2)) := by ring
      _ = (((t + 1 : ℕ) : R) * ((t - 1 : ℕ) : R) * 4) *
            (γ ^ (((2 * t + 2) ^ 2 - 4) / 2 + ((2 * t - 2) ^ 2 - 4) / 2) * γ ^ 3) := by
          rw [ha2, ← pow_add]; ring
      _ = (((2 * t : ℕ) : R) ^ 2 - 4) *
            γ ^ (((2 * t + 2) ^ 2 - 4) / 2 + ((2 * t - 2) ^ 2 - 4) / 2 + 3) := by
          rw [hcoeff, ← pow_add]
      _ = (((2 * t : ℕ) : R) ^ 2 - 4) * γ ^ ((2 * t) ^ 2 + 3) := by rw [hexp]

private lemma modelF_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {γ a2 : ZMod p} (hγ : γ ≠ 0) (ha2 : a2 ^ 2 = 4 * γ ^ 3) {m : ℕ} (hm : ¬ p ∣ m) :
    modelF γ a2 m ≠ 0 := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hm_nz : (m : ZMod p) ≠ 0 := by
    intro h
    exact hm ((ZMod.natCast_eq_zero_iff m p).mp h)
  have h2_nz : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hp' : p.Prime := Fact.out
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp hd)
  have ha2_nz : a2 ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at ha2
    have h4 : (4 : ZMod p) = (2 : ZMod p) ^ 2 := by norm_num
    rw [h4] at ha2
    exact mul_ne_zero (pow_ne_zero 2 h2_nz) (pow_ne_zero 3 hγ) ha2.symm
  unfold modelF
  rw [if_neg hm0]
  by_cases hodd : m % 2 = 1
  · rw [if_pos hodd]
    exact mul_ne_zero hm_nz (pow_ne_zero _ hγ)
  · rw [if_neg hodd]
    have hhalf_nz : ((m / 2 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have h2m : (2 : ZMod p) * ((m / 2 : ℕ) : ZMod p) = (m : ZMod p) := by
        have hm2 : 2 * (m / 2) = m := by omega
        calc
          (2 : ZMod p) * ((m / 2 : ℕ) : ZMod p) = ((2 * (m / 2) : ℕ) : ZMod p) := by push_cast; rfl
          _ = (m : ZMod p) := by rw [hm2]
      rw [h, mul_zero] at h2m
      exact hm_nz h2m.symm
    exact mul_ne_zero (mul_ne_zero hhalf_nz ha2_nz) (pow_ne_zero _ hγ)

end SilvermanEDSR1H1R1H1

theorem OMA.solution :
    OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H1_R1.H1 := by
  intro W hw hne
  refine ⟨({2, 3} : Finset ℕ) ∪ (W 2).natAbs.primeFactors ∪ (W 3).natAbs.primeFactors, ?_⟩
  intro p hpS hp n k hn hk hpWn hcop
  have : Fact p.Prime := ⟨hp⟩
  have hp2_ne : p ≠ 2 := by
    intro h
    exact hpS (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [h])))
  have hp3_ne : p ≠ 3 := by
    intro h
    exact hpS (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [h])))
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    by_contra! hlt
    interval_cases p
    · exact hp2_ne rfl
    · exact hp3_ne rfl
    · norm_num at hp
  have hpW2 : ¬ p ∣ (W 2).natAbs := by
    intro hd
    have h2ne : (W 2).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hne 2 (by decide))
    exact hpS (Finset.mem_union_left _ (Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hp, hd, h2ne⟩)))
  have hpW3 : ¬ p ∣ (W 3).natAbs := by
    intro hd
    have h3ne : (W 3).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hne 3 (by decide))
    exact hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, hd, h3ne⟩))
  obtain ⟨hW0, hWneg⟩ := SilvermanEDSR1H1R1H1.W_zero_and_neg hw
  have h1 : W 1 = 1 := hw.2.1
  obtain ⟨r, hr_pos, hrank⟩ :=
    OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H1_R1.ward_rank
      hw.1 h1 hp hpW3 ⟨n, hn, hpWn⟩
  have hr4 : 4 ≤ r := by
    by_contra! hlt
    interval_cases r
    · exact hp.not_dvd_one (by simpa [h1] using (hrank 1 (by decide)).mpr (dvd_refl 1))
    · exact hpW2 ((hrank 2 (by decide)).mpr (dvd_refl 2))
    · exact hpW3 ((hrank 3 (by decide)).mpr (dvd_refl 3))
  have hrn : r ∣ n := (hrank n hn).mp hpWn
  have hn4 : 4 ≤ n := hr4.trans (Nat.le_of_dvd hn hrn)
  have hpWn1 : ¬ p ∣ (W ((n : ℤ) + 1)).natAbs := by
    intro hd
    have hd' : p ∣ (W ((n + 1 : ℕ) : ℤ)).natAbs := by simpa using hd
    have hrn1 : r ∣ n + 1 := (hrank (n + 1) (by omega)).mp hd'
    have hr1 : r ∣ 1 := (Nat.dvd_add_right hrn).mp hrn1
    have := Nat.le_of_dvd (by decide) hr1
    omega
  have hpWnm1 : ¬ p ∣ (W ((n : ℤ) - 1)).natAbs := by
    intro hd
    have heq : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [← heq] at hd
    have hrnm1 : r ∣ n - 1 := (hrank (n - 1) (by omega)).mp hd
    have hr1 : r ∣ 1 := by
      have : n - 1 + 1 = n := by omega
      exact (Nat.dvd_add_right hrnm1).mp (this ▸ hrn)
    have := Nat.le_of_dvd (by decide) hr1
    omega
  let γ : ℤ := -(W ((n : ℤ) + 1) * W ((n : ℤ) - 1))
  have hγ_ndvd : ¬ (p : ℤ) ∣ γ := by
    intro hd
    have hd' : (p : ℤ) ∣ W ((n : ℤ) + 1) * W ((n : ℤ) - 1) := dvd_neg.mp hd
    have hprimeZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hprimeZ.dvd_or_dvd hd' with h | h
    · exact hpWn1 ((SilvermanEDSR1H1R1H1.dvd_int_iff_dvd_natAbs p _).mp h)
    · exact hpWnm1 ((SilvermanEDSR1H1R1H1.dvd_int_iff_dvd_natAbs p _).mp h)
  let A (m : ℕ) : ℤ := W ((m : ℤ) * (n : ℤ)) / W (n : ℤ)
  have hWn_ne : W (n : ℤ) ≠ 0 := hne (n : ℤ) (by omega)
  have hA_mul (m : ℕ) : W (n : ℤ) * A m = W ((m : ℤ) * (n : ℤ)) :=
    Int.mul_ediv_cancel' (hw.1.2 (n : ℤ) ((m : ℤ) * (n : ℤ)) (dvd_mul_left _ _))
  have hA0 : A 0 = 0 := by simp [A, hW0]
  have hA1 : A 1 = 1 := by simp [A, Int.ediv_self hWn_ne]
  have hA2_sq_p2 : ((A 2 : ℤ) : ZMod (p ^ 2)) ^ 2 = 4 * ((γ : ℤ) : ZMod (p ^ 2)) ^ 3 := by
    simpa [A, γ] using SilvermanEDSR1H1R1H1.A2_sq_mod_sq hw.1 h1 hp hpW2 hpW3 hWn_ne hpWn
  let proj : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
  have hproj_int (x : ℤ) : proj ((x : ℤ) : ZMod (p ^ 2)) = ((x : ℤ) : ZMod p) := map_intCast proj x
  have hA2_sq_p : ((A 2 : ℤ) : ZMod p) ^ 2 = 4 * ((γ : ℤ) : ZMod p) ^ 3 := by
    have h := congrArg proj hA2_sq_p2
    simp only [map_pow, map_mul, map_ofNat, hproj_int] at h
    exact h
  have hγ_nz : ((γ : ℤ) : ZMod p) ≠ 0 := by
    intro h
    exact hγ_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd γ p).mp h)
  have hnbr (m : ℕ) :
      ((W ((m : ℤ) * (n : ℤ) + 1) * W ((m : ℤ) * (n : ℤ) - 1) : ℤ) : ZMod p) =
        -((γ : ℤ) : ZMod p) ^ (m ^ 2) := by
    have h := congrArg proj
      (SilvermanEDSR1H1R1H1.neighbor_prod_mod_sq hw.1 h1 hWneg hp hpWn hγ_ndvd m)
    simp only [map_neg, map_pow, hproj_int] at h
    exact h
  have hrec1 (m : ℕ) (hm : 1 ≤ m) :
      ((A (m + 1) : ℤ) : ZMod p) * ((A (m - 1) : ℤ) : ZMod p) =
        ((γ : ℤ) : ZMod p) * ((A m : ℤ) : ZMod p) ^ 2 - ((γ : ℤ) : ZMod p) ^ (m ^ 2) := by
    have r := SilvermanEDSR1H1R1H1.ward_rel hw.1 h1 ((m : ℤ) * (n : ℤ)) (n : ℤ)
    have h1' : (m : ℤ) * (n : ℤ) + (n : ℤ) = ((m + 1 : ℕ) : ℤ) * (n : ℤ) := by push_cast; ring
    have h2' : (m : ℤ) * (n : ℤ) - (n : ℤ) = ((m - 1 : ℕ) : ℤ) * (n : ℤ) := by
      rw [Nat.cast_sub hm]; push_cast; ring
    rw [h1', h2', ← hA_mul (m + 1), ← hA_mul (m - 1), ← hA_mul m] at r
    have hzero : W (n : ℤ) ^ 2 *
        (A (m + 1) * A (m - 1) - (W ((m : ℤ) * (n : ℤ) + 1) * W ((m : ℤ) * (n : ℤ) - 1) +
          γ * A m ^ 2)) = 0 := by
      dsimp only [γ]
      linear_combination r
    have hint : A (m + 1) * A (m - 1) =
        W ((m : ℤ) * (n : ℤ) + 1) * W ((m : ℤ) * (n : ℤ) - 1) + γ * A m ^ 2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 hWn_ne))
    have hmod := congrArg (fun t : ℤ => (t : ZMod p)) hint
    have hnb := hnbr m
    simp only [Int.cast_mul, Int.cast_add, Int.cast_pow] at hmod hnb ⊢
    linear_combination hmod + hnb
  have hrec2 (m : ℕ) (hm : 2 ≤ m) :
      ((A (m + 2) : ℤ) : ZMod p) * ((A (m - 2) : ℤ) : ZMod p) =
        -(((γ : ℤ) : ZMod p) ^ (m ^ 2) * ((A 2 : ℤ) : ZMod p) ^ 2) +
          ((γ : ℤ) : ZMod p) ^ 4 * ((A m : ℤ) : ZMod p) ^ 2 := by
    have r := SilvermanEDSR1H1R1H1.ward_rel hw.1 h1 ((m : ℤ) * (n : ℤ)) (2 * (n : ℤ))
    have h1' : (m : ℤ) * (n : ℤ) + 2 * (n : ℤ) = ((m + 2 : ℕ) : ℤ) * (n : ℤ) := by
      push_cast; ring
    have h2' : (m : ℤ) * (n : ℤ) - 2 * (n : ℤ) = ((m - 2 : ℕ) : ℤ) * (n : ℤ) := by
      rw [Nat.cast_sub hm]; push_cast; ring
    have h2n : (2 : ℤ) * (n : ℤ) = ((2 : ℕ) : ℤ) * (n : ℤ) := by norm_num
    rw [h1', h2', h2n, ← hA_mul (m + 2), ← hA_mul (m - 2), ← hA_mul 2, ← hA_mul m] at r
    have hzero : W (n : ℤ) ^ 2 *
        (A (m + 2) * A (m - 2) -
          (W ((m : ℤ) * (n : ℤ) + 1) * W ((m : ℤ) * (n : ℤ) - 1) * A 2 ^ 2 -
            W (((2 : ℕ) : ℤ) * (n : ℤ) + 1) * W (((2 : ℕ) : ℤ) * (n : ℤ) - 1) * A m ^ 2)) = 0 := by
      linear_combination r
    have hint : A (m + 2) * A (m - 2) =
        W ((m : ℤ) * (n : ℤ) + 1) * W ((m : ℤ) * (n : ℤ) - 1) * A 2 ^ 2 -
          W (((2 : ℕ) : ℤ) * (n : ℤ) + 1) * W (((2 : ℕ) : ℤ) * (n : ℤ) - 1) * A m ^ 2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 hWn_ne))
    have hmod := congrArg (fun t : ℤ => (t : ZMod p)) hint
    have hnbm := hnbr m
    have hnb2 := hnbr 2
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow] at hmod hnbm hnb2 ⊢
    norm_num at hnb2
    linear_combination hmod + ((A 2 : ℤ) : ZMod p) ^ 2 * hnbm - ((A m : ℤ) : ZMod p) ^ 2 * hnb2
  have hA_eq : ∀ m : ℕ, ((A m : ℤ) : ZMod p) =
      SilvermanEDSR1H1R1H1.modelF ((γ : ℤ) : ZMod p) ((A 2 : ℤ) : ZMod p) m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      match m with
      | 0 => simp [hA0, SilvermanEDSR1H1R1H1.modelF]
      | 1 => simp [hA1, SilvermanEDSR1H1R1H1.modelF]
      | 2 => simp [SilvermanEDSR1H1R1H1.modelF]
      | m + 3 =>
        by_cases hd : p ∣ m + 1
        · have hm4 : 4 ≤ m + 1 := by
            have := Nat.le_of_dvd (by omega) hd
            omega
          have hnd : ¬ p ∣ m - 1 := by
            intro h
            have h2 : p ∣ 2 := by
              have e : (m - 1) + 2 = m + 1 := by omega
              exact (Nat.dvd_add_right h).mp (e ▸ hd)
            have := Nat.le_of_dvd (by decide) h2
            omega
          have hnz := SilvermanEDSR1H1R1H1.modelF_ne_zero_zmod hp2_ne hγ_nz hA2_sq_p hnd
          have hr := hrec2 (m + 1) (by omega)
          have hf := SilvermanEDSR1H1R1H1.modelF_two_step hA2_sq_p (k := m + 1) (by omega)
          have e1 : m + 1 + 2 = m + 3 := by omega
          have e2 : m + 1 - 2 = m - 1 := by omega
          rw [e1, e2] at hr hf
          rw [ih (m - 1) (by omega), ih (m + 1) (by omega)] at hr
          exact mul_right_cancel₀ hnz (hr.trans hf.symm)
        · have hnz := SilvermanEDSR1H1R1H1.modelF_ne_zero_zmod hp2_ne hγ_nz hA2_sq_p hd
          have hr := hrec1 (m + 2) (by omega)
          have hf := SilvermanEDSR1H1R1H1.modelF_one_step hA2_sq_p (k := m + 2) (by omega)
          have e1 : m + 2 + 1 = m + 3 := by omega
          have e2 : m + 2 - 1 = m + 1 := by omega
          rw [e1, e2] at hr hf
          rw [ih (m + 1) (by omega), ih (m + 2) (by omega)] at hr
          exact mul_right_cancel₀ hnz (hr.trans hf.symm)
  have hndvd_k : ¬ p ∣ k := fun h => by
    have h1' : p ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) h
    exact hp.not_dvd_one h1'
  have hAk_nz : ((A k : ℤ) : ZMod p) ≠ 0 := by
    rw [hA_eq k]
    exact SilvermanEDSR1H1R1H1.modelF_ne_zero_zmod hp2_ne hγ_nz hA2_sq_p hndvd_k
  have hpAk : ¬ p ∣ (A k).natAbs := fun hd =>
    hAk_nz ((ZMod.intCast_zmod_eq_zero_iff_dvd (A k) p).mpr
      ((SilvermanEDSR1H1R1H1.dvd_int_iff_dvd_natAbs p _).mpr hd))
  have hmul_nat : (W ((n * k : ℕ) : ℤ)).natAbs = (W (n : ℤ)).natAbs * (A k).natAbs := by
    have hcomm : ((n * k : ℕ) : ℤ) = (k : ℤ) * (n : ℤ) := by push_cast; ring
    rw [hcomm, ← hA_mul k, Int.natAbs_mul]
  have hWn_nat_ne : (W (n : ℤ)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hWn_ne
  have hAk_nat_ne : (A k).natAbs ≠ 0 := by
    intro h
    have : A k = 0 := Int.natAbs_eq_zero.mp h
    rw [this, Int.cast_zero] at hAk_nz
    exact hAk_nz rfl
  rw [hmul_nat, Nat.factorization_mul hWn_nat_ne hAk_nat_ne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpAk, add_zero]
