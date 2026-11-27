import FormalConjectures.OEIS.«212334»
import Mathlib

/-!
Proof that $a(p) \equiv 1 \pmod{p^5}$ for all primes $p \ge 5$, where
$a(n) = \sum_{k=0}^{n-1} \binom{n}{k} \binom{n-1}{k} \binom{n+k-1}{k}^2$ is OEIS A212334.
-/

-- Problem: Balanced walks on a 4-dimensional cubic lattice with neighbor steps - conjecture 1
-- Upstream: formal-conjectures FormalConjectures/OEIS/212334.lean:66 (declaration OeisA212334.conjecture_1)
-- Credit: @aarushvan (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OeisA212334Proof

private def term (p k : ℕ) : ℕ :=
  p.choose k * (p - 1).choose k * (p + k - 1).choose k ^ 2

private lemma a_eq_one_add_sum {p : ℕ} (hp : 0 < p) :
    OeisA212334.a p = 1 + ∑ k ∈ Finset.Ico 1 p, term p k := by
  unfold OeisA212334.a
  rw [if_neg hp.ne']
  have hrange : Finset.range p = Finset.Ico 0 p := by
    ext x
    simp
  rw [hrange, Finset.sum_eq_sum_Ico_succ_bot hp]
  simp [term]

private lemma fac_mul_choose_p {p k : ℕ} (hk1 : 1 ≤ k) (hkp : k ≤ p) :
    (k.factorial : ℤ) * (p.choose k : ℤ) =
      (p : ℤ) * ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) - (j : ℤ)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have ih' := ih (by omega) (by omega)
      have hch := congrArg (Nat.cast (R := ℤ)) (Nat.choose_succ_right_eq p k)
      push_cast at hch
      have hsub : ((p - k : ℕ) : ℤ) = (p : ℤ) - (k : ℤ) := by
        rw [Nat.cast_sub (by omega)]
      rw [hsub] at hch
      have hfac : ((k + 1).factorial : ℤ) = ((k : ℤ) + 1) * (k.factorial : ℤ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [Finset.prod_Ico_succ_top (by omega)]
      calc
        ((k + 1).factorial : ℤ) * (p.choose (k + 1) : ℤ)
            = (k.factorial : ℤ) * ((p.choose (k + 1) : ℤ) * ((k : ℤ) + 1)) := by
              rw [hfac]; ring
        _ = (k.factorial : ℤ) * ((p.choose k : ℤ) * ((p : ℤ) - (k : ℤ))) := by
              rw [hch]
        _ = ((k.factorial : ℤ) * (p.choose k : ℤ)) * ((p : ℤ) - (k : ℤ)) := by ring
        _ = ((p : ℤ) * ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) - (j : ℤ))) * ((p : ℤ) - (k : ℤ)) := by
              rw [ih']
        _ = (p : ℤ) * ((∏ j ∈ Finset.Ico 1 k, ((p : ℤ) - (j : ℤ))) * ((p : ℤ) - (k : ℤ))) := by
              ring

private lemma fac_mul_choose_p_sub_one {p k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    (k.factorial : ℤ) * ((p - 1).choose k : ℤ) =
      ((p : ℤ) - (k : ℤ)) * ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) - (j : ℤ)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, one_mul, Nat.choose_one_right,
        Finset.Ico_self, Finset.prod_empty, mul_one]
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    · have ih' := ih (by omega) (by omega)
      have hch := congrArg (Nat.cast (R := ℤ)) (Nat.choose_succ_right_eq (p - 1) k)
      push_cast at hch
      have hsub1 : ((p - 1 - k : ℕ) : ℤ) = (p : ℤ) - ((k : ℤ) + 1) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hsub1] at hch
      have hfac : ((k + 1).factorial : ℤ) = ((k : ℤ) + 1) * (k.factorial : ℤ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [Finset.prod_Ico_succ_top (by omega)]
      push_cast
      calc
        ((k + 1).factorial : ℤ) * ((p - 1).choose (k + 1) : ℤ)
            = (k.factorial : ℤ) * (((p - 1).choose (k + 1) : ℤ) * ((k : ℤ) + 1)) := by
              rw [hfac]; ring
        _ = (k.factorial : ℤ) * (((p - 1).choose k : ℤ) * ((p : ℤ) - ((k : ℤ) + 1))) := by
              rw [hch]
        _ = ((k.factorial : ℤ) * ((p - 1).choose k : ℤ)) * ((p : ℤ) - ((k : ℤ) + 1)) := by ring
        _ = (((p : ℤ) - (k : ℤ)) * ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) - (j : ℤ))) *
              ((p : ℤ) - ((k : ℤ) + 1)) := by rw [ih']
        _ = ((p : ℤ) - ((k : ℤ) + 1)) *
              ((∏ j ∈ Finset.Ico 1 k, ((p : ℤ) - (j : ℤ))) * ((p : ℤ) - (k : ℤ))) := by ring

private lemma fac_mul_choose_p_add_nat {p k : ℕ} (hp : 1 ≤ p) (hk1 : 1 ≤ k) :
    k.factorial * (p + k - 1).choose k = p * ∏ j ∈ Finset.Ico 1 k, (p + j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have ih' := ih (by omega)
      have h1 : p + (k + 1) - 1 = p + k := by omega
      have hch1 := Nat.choose_mul_factorial_mul_factorial (n := p + k) (k := k + 1) (by omega)
      rw [show p + k - (k + 1) = p - 1 by omega] at hch1
      have hch0 := Nat.choose_mul_factorial_mul_factorial (n := p + k - 1) (k := k) (by omega)
      rw [show p + k - 1 - k = p - 1 by omega] at hch0
      have hpk : (p + k).factorial = (p + k) * (p + k - 1).factorial :=
        (Nat.mul_factorial_pred (by omega)).symm
      have hmul :
          ((k + 1).factorial * (p + k).choose (k + 1)) * (p - 1).factorial =
            ((p + k) * (k.factorial * (p + k - 1).choose k)) * (p - 1).factorial := by
        calc
          ((k + 1).factorial * (p + k).choose (k + 1)) * (p - 1).factorial
              = (p + k).choose (k + 1) * (k + 1).factorial * (p - 1).factorial := by ring
          _ = (p + k).factorial := hch1
          _ = (p + k) * (p + k - 1).factorial := hpk
          _ = (p + k) * ((p + k - 1).choose k * k.factorial * (p - 1).factorial) := by
                rw [hch0]
          _ = ((p + k) * (k.factorial * (p + k - 1).choose k)) * (p - 1).factorial := by ring
      have hstep :
          (k + 1).factorial * (p + k).choose (k + 1) =
            (p + k) * (k.factorial * (p + k - 1).choose k) :=
        Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (p - 1)) hmul
      rw [h1, hstep, ih', Finset.prod_Ico_succ_top (by omega)]
      ring

private lemma fac_mul_choose_p_add {p k : ℕ} (hp : 1 ≤ p) (hk1 : 1 ≤ k) :
    (k.factorial : ℤ) * ((p + k - 1).choose k : ℤ) =
      (p : ℤ) * ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) + (j : ℤ)) := by
  have hnat := congrArg (Nat.cast (R := ℤ)) (fac_mul_choose_p_add_nat hp hk1)
  push_cast at hnat
  exact hnat

private lemma fac4_mul_term_int {p k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    ((k.factorial : ℤ) ^ 4) * (term p k : ℤ) =
      (p : ℤ) ^ 3 * ((p : ℤ) - (k : ℤ)) *
        ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 := by
  have h1 := fac_mul_choose_p hk1 hkp.le
  have h2 := fac_mul_choose_p_sub_one hk1 hkp
  have h3 := fac_mul_choose_p_add (p := p) (by omega) hk1
  set A : ℤ := ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) - (j : ℤ))
  set B : ℤ := ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) + (j : ℤ))
  have hAB : A * B = ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) ^ 2 - (j : ℤ) ^ 2) := by
    dsimp [A, B]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  have hAB2 : (A * B) ^ 2 = ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 := by
    rw [hAB, sq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  have hterm :
      ((k.factorial : ℤ) ^ 4) * (term p k : ℤ) =
        ((k.factorial : ℤ) * (p.choose k : ℤ)) *
          ((k.factorial : ℤ) * ((p - 1).choose k : ℤ)) *
            ((k.factorial : ℤ) * ((p + k - 1).choose k : ℤ)) ^ 2 := by
    unfold term
    push_cast
    ring
  rw [hterm, h1, h2, h3]
  calc
    ((p : ℤ) * A) * (((p : ℤ) - (k : ℤ)) * A) * ((p : ℤ) * B) ^ 2
        = (p : ℤ) ^ 3 * ((p : ℤ) - (k : ℤ)) * (A * B) ^ 2 := by ring
    _ = (p : ℤ) ^ 3 * ((p : ℤ) - (k : ℤ)) *
          ∏ j ∈ Finset.Ico 1 k, ((p : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 := by rw [hAB2]

private lemma fac4_mul_term_zmod {p k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    ((k.factorial : ZMod (p ^ 5)) ^ 4) * (term p k : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) ^ 3 * ((p : ZMod (p ^ 5)) - (k : ZMod (p ^ 5))) *
        ∏ j ∈ Finset.Ico 1 k, ((p : ZMod (p ^ 5)) ^ 2 - (j : ZMod (p ^ 5)) ^ 2) ^ 2 := by
  have h := congrArg (Int.castRingHom (ZMod (p ^ 5))) (fac4_mul_term_int hk1 hkp)
  simpa [map_mul, map_pow, map_sub, map_prod] using h

private lemma pow5_eq_zero (p : ℕ) : (p : ZMod (p ^ 5)) ^ 5 = 0 := by
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self (p ^ 5)

private lemma p3_mul_prod_sq_sub (p : ℕ) (s : Finset ℕ) :
    (p : ZMod (p ^ 5)) ^ 3 *
        ∏ j ∈ s, ((p : ZMod (p ^ 5)) ^ 2 - (j : ZMod (p ^ 5)) ^ 2) ^ 2 =
      (p : ZMod (p ^ 5)) ^ 3 * ∏ j ∈ s, (j : ZMod (p ^ 5)) ^ 4 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := pow5_eq_zero p
    calc
      (p : ZMod (p ^ 5)) ^ 3 *
          (((p : ZMod (p ^ 5)) ^ 2 - (a : ZMod (p ^ 5)) ^ 2) ^ 2 *
            ∏ j ∈ s, ((p : ZMod (p ^ 5)) ^ 2 - (j : ZMod (p ^ 5)) ^ 2) ^ 2)
          = ((p : ZMod (p ^ 5)) ^ 2 - (a : ZMod (p ^ 5)) ^ 2) ^ 2 *
              ((p : ZMod (p ^ 5)) ^ 3 *
                ∏ j ∈ s, ((p : ZMod (p ^ 5)) ^ 2 - (j : ZMod (p ^ 5)) ^ 2) ^ 2) := by ring
      _ = ((p : ZMod (p ^ 5)) ^ 2 - (a : ZMod (p ^ 5)) ^ 2) ^ 2 *
              ((p : ZMod (p ^ 5)) ^ 3 * ∏ j ∈ s, (j : ZMod (p ^ 5)) ^ 4) := by rw [ih]
      _ = ((p : ZMod (p ^ 5)) ^ 3 * (a : ZMod (p ^ 5)) ^ 4 +
            (p : ZMod (p ^ 5)) ^ 5 * ((p : ZMod (p ^ 5)) ^ 2 - 2 * (a : ZMod (p ^ 5)) ^ 2)) *
              ∏ j ∈ s, (j : ZMod (p ^ 5)) ^ 4 := by ring
      _ = (p : ZMod (p ^ 5)) ^ 3 *
            ((a : ZMod (p ^ 5)) ^ 4 * ∏ j ∈ s, (j : ZMod (p ^ 5)) ^ 4) := by
          rw [hp5]; ring

private lemma prod_Ico_one_pow4 {k : ℕ} (hk1 : 1 ≤ k) :
    ∏ j ∈ Finset.Ico 1 k, j ^ 4 = (k - 1).factorial ^ 4 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · rw [Finset.prod_Ico_succ_top (by omega), ih (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [← mul_pow, mul_comm, Nat.mul_factorial_pred hk0]

private lemma zmod_mul_inv_pow {p m : ℕ} (hcop : Nat.Coprime m p) :
    (m : ZMod (p ^ 5)) * (m : ZMod (p ^ 5))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime m (p ^ 5)).mpr (hcop.pow_right 5))

private lemma coprime_of_pos_lt_prime {p m : ℕ} (hp : p.Prime) (hm0 : 0 < m) (hmp : m < p) :
    Nat.Coprime m p :=
  (hp.coprime_iff_not_dvd.mpr fun hd => by
    have := Nat.le_of_dvd hm0 hd
    omega).symm

private lemma coprime_fac_pred_of_lt_prime {p k : ℕ} (hp : p.Prime) (hkp : k < p) :
    Nat.Coprime (k - 1).factorial p :=
  (hp.coprime_iff_not_dvd.mpr ((hp.dvd_factorial).not.mpr (by omega))).symm

private lemma term_zmod_eq {p k : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    (term p k : ZMod (p ^ 5)) =
      (p : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 4 -
        (p : ZMod (p ^ 5)) ^ 3 * ((k : ZMod (p ^ 5))⁻¹) ^ 3 := by
  have hfac4 := fac4_mul_term_zmod hk1 hkp
  have hprod :
      ∏ j ∈ Finset.Ico 1 k, (j : ZMod (p ^ 5)) ^ 4 = ((k - 1).factorial : ZMod (p ^ 5)) ^ 4 := by
    have hnat := congrArg (Nat.castRingHom (ZMod (p ^ 5))) (prod_Ico_one_pow4 hk1)
    simpa [map_prod, map_pow] using hnat
  have hp3 :
      (p : ZMod (p ^ 5)) ^ 3 *
          ∏ j ∈ Finset.Ico 1 k, ((p : ZMod (p ^ 5)) ^ 2 - (j : ZMod (p ^ 5)) ^ 2) ^ 2 =
        (p : ZMod (p ^ 5)) ^ 3 * ((k - 1).factorial : ZMod (p ^ 5)) ^ 4 := by
    rw [p3_mul_prod_sq_sub, hprod]
  have hrhs :
      ((k.factorial : ZMod (p ^ 5)) ^ 4) * (term p k : ZMod (p ^ 5)) =
        ((p : ZMod (p ^ 5)) - (k : ZMod (p ^ 5))) *
          ((p : ZMod (p ^ 5)) ^ 3 * ((k - 1).factorial : ZMod (p ^ 5)) ^ 4) := by
    calc
      ((k.factorial : ZMod (p ^ 5)) ^ 4) * (term p k : ZMod (p ^ 5))
          = ((p : ZMod (p ^ 5)) - (k : ZMod (p ^ 5))) *
              ((p : ZMod (p ^ 5)) ^ 3 *
                ∏ j ∈ Finset.Ico 1 k, ((p : ZMod (p ^ 5)) ^ 2 - (j : ZMod (p ^ 5)) ^ 2) ^ 2) := by
              rw [hfac4]; ring
      _ = ((p : ZMod (p ^ 5)) - (k : ZMod (p ^ 5))) *
              ((p : ZMod (p ^ 5)) ^ 3 * ((k - 1).factorial : ZMod (p ^ 5)) ^ 4) := by rw [hp3]
  set kf : ZMod (p ^ 5) := (k : ZMod (p ^ 5))
  set ff : ZMod (p ^ 5) := ((k - 1).factorial : ZMod (p ^ 5))
  have hkfac : (k.factorial : ZMod (p ^ 5)) = kf * ff := by
    have hn : k.factorial = k * (k - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
    dsimp [kf, ff]
    rw [hn]
    push_cast
    ring
  have hkinv : kf * kf⁻¹ = 1 := zmod_mul_inv_pow (coprime_of_pos_lt_prime hp (by omega) hkp)
  have hfinv : ff * ff⁻¹ = 1 := zmod_mul_inv_pow (coprime_fac_pred_of_lt_prime hp hkp)
  rw [hkfac, mul_pow] at hrhs
  calc
    (term p k : ZMod (p ^ 5))
        = (kf * kf⁻¹) ^ 4 * (ff * ff⁻¹) ^ 4 * (term p k : ZMod (p ^ 5)) := by
          rw [hkinv, hfinv]; ring
    _ = ((kf⁻¹) ^ 4 * (ff⁻¹) ^ 4) * ((kf ^ 4 * ff ^ 4) * (term p k : ZMod (p ^ 5))) := by ring
    _ = ((kf⁻¹) ^ 4 * (ff⁻¹) ^ 4) *
          (((p : ZMod (p ^ 5)) - kf) * ((p : ZMod (p ^ 5)) ^ 3 * ff ^ 4)) := by rw [hrhs]
    _ = (ff * ff⁻¹) ^ 4 * ((kf⁻¹) ^ 4 * (((p : ZMod (p ^ 5)) - kf) * (p : ZMod (p ^ 5)) ^ 3)) := by
          ring
    _ = 1 ^ 4 * ((p : ZMod (p ^ 5)) ^ 4 * (kf⁻¹) ^ 4 -
          (p : ZMod (p ^ 5)) ^ 3 * (kf * kf⁻¹) * (kf⁻¹) ^ 3) := by
          rw [hfinv]; ring
    _ = (p : ZMod (p ^ 5)) ^ 4 * (kf⁻¹) ^ 4 - (p : ZMod (p ^ 5)) ^ 3 * (kf⁻¹) ^ 3 := by
          rw [hkinv]; ring

private lemma pair_inv_cube_zmod {p k : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    (p : ZMod (p ^ 5)) ^ 3 *
        (((k : ZMod (p ^ 5))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3) =
      -3 * (p : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 4 := by
  set P : ZMod (p ^ 5) := (p : ZMod (p ^ 5))
  set x : ZMod (p ^ 5) := (k : ZMod (p ^ 5))
  set y : ZMod (p ^ 5) := ((p - k : ℕ) : ZMod (p ^ 5))
  have hp5 : P ^ 5 = 0 := pow5_eq_zero p
  have hy_eq : y = P - x := by
    dsimp [P, x, y]
    rw [Nat.cast_sub hkp.le]
  have hx : x * x⁻¹ = 1 := zmod_mul_inv_pow (coprime_of_pos_lt_prime hp (by omega) hkp)
  have hy : y * y⁻¹ = 1 := zmod_mul_inv_pow (coprime_of_pos_lt_prime hp (by omega) (by omega))
  have h1 : y ^ 3 * (P ^ 3 * ((x⁻¹) ^ 3 + (y⁻¹) ^ 3)) = 3 * P ^ 4 * x⁻¹ := by
    have hy3 : P ^ 3 * y ^ 3 = -P ^ 3 * x ^ 3 + 3 * P ^ 4 * x ^ 2 + P ^ 5 * (-3 * x + P) := by
      rw [hy_eq]; ring
    calc
      y ^ 3 * (P ^ 3 * ((x⁻¹) ^ 3 + (y⁻¹) ^ 3))
          = (P ^ 3 * y ^ 3) * (x⁻¹) ^ 3 + P ^ 3 * (y * y⁻¹) ^ 3 := by ring
      _ = (-P ^ 3 * x ^ 3 + 3 * P ^ 4 * x ^ 2 + P ^ 5 * (-3 * x + P)) * (x⁻¹) ^ 3 +
            P ^ 3 * 1 ^ 3 := by rw [hy3, hy]
      _ = -P ^ 3 * (x * x⁻¹) ^ 3 + 3 * P ^ 4 * (x * x⁻¹) ^ 2 * x⁻¹ +
            P ^ 5 * (-3 * x + P) * (x⁻¹) ^ 3 + P ^ 3 := by ring
      _ = 3 * P ^ 4 * x⁻¹ := by rw [hx, hp5]; ring
  have h2 : y ^ 3 * (-3 * P ^ 4 * (x⁻¹) ^ 4) = 3 * P ^ 4 * x⁻¹ := by
    have hy3' : P ^ 4 * y ^ 3 = -P ^ 4 * x ^ 3 + P ^ 5 * (3 * x ^ 2 - 3 * P * x + P ^ 2) := by
      rw [hy_eq]; ring
    calc
      y ^ 3 * (-3 * P ^ 4 * (x⁻¹) ^ 4)
          = -3 * (P ^ 4 * y ^ 3) * (x⁻¹) ^ 4 := by ring
      _ = -3 * (-P ^ 4 * x ^ 3 + P ^ 5 * (3 * x ^ 2 - 3 * P * x + P ^ 2)) * (x⁻¹) ^ 4 := by
          rw [hy3']
      _ = 3 * P ^ 4 * (x * x⁻¹) ^ 3 * x⁻¹ -
            3 * P ^ 5 * (3 * x ^ 2 - 3 * P * x + P ^ 2) * (x⁻¹) ^ 4 := by ring
      _ = 3 * P ^ 4 * x⁻¹ := by rw [hx, hp5]; ring
  calc
    P ^ 3 * ((x⁻¹) ^ 3 + (y⁻¹) ^ 3)
        = (y * y⁻¹) ^ 3 * (P ^ 3 * ((x⁻¹) ^ 3 + (y⁻¹) ^ 3)) := by rw [hy]; ring
    _ = (y⁻¹) ^ 3 * (y ^ 3 * (P ^ 3 * ((x⁻¹) ^ 3 + (y⁻¹) ^ 3))) := by ring
    _ = (y⁻¹) ^ 3 * (y ^ 3 * (-3 * P ^ 4 * (x⁻¹) ^ 4)) := by rw [h1, h2]
    _ = (y * y⁻¹) ^ 3 * (-3 * P ^ 4 * (x⁻¹) ^ 4) := by ring
    _ = -3 * P ^ 4 * (x⁻¹) ^ 4 := by rw [hy]; ring

private lemma sum_pow_four_zmod_p {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) :
    (∑ x : ZMod p, x ^ 4) = 0 := by
  have hp : p.Prime := Fact.out
  have h2ne0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have hle := Nat.le_of_dvd (by omega) hd
    omega
  have h15ne0 : (2 : ZMod p) ^ 4 - 1 ≠ 0 := by
    intro h
    have h15 : ((15 : ℕ) : ZMod p) = 0 := by
      have : ((15 : ℕ) : ZMod p) = (2 : ZMod p) ^ 4 - 1 := by norm_num
      rw [this]
      exact h
    have hd : p ∣ 3 * 5 := (ZMod.natCast_eq_zero_iff 15 p).mp h15
    rcases hp.dvd_mul.mp hd with h3 | h5
    · have := Nat.le_of_dvd (by omega) h3; omega
    · have := Nat.le_of_dvd (by omega) h5; omega
  set T : ZMod p := ∑ x : ZMod p, x ^ 4
  have hmul : (2 : ZMod p) ^ 4 * T = T := by
    have heqv := Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p) h2ne0)
      (fun x : ZMod p => ((2 : ZMod p) * x) ^ 4) (fun x : ZMod p => x ^ 4) (fun _ => rfl)
    calc
      (2 : ZMod p) ^ 4 * T
          = ∑ x : ZMod p, (2 : ZMod p) ^ 4 * x ^ 4 := Finset.mul_sum Finset.univ _ _
      _ = ∑ x : ZMod p, ((2 : ZMod p) * x) ^ 4 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [mul_pow]
      _ = T := heqv
  have hsub : ((2 : ZMod p) ^ 4 - 1) * T = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left h15ne0

private lemma sum_Ico_inv_pow4_zmod_p {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) :
    (∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 4) = 0 := by
  have hp : p.Prime := Fact.out
  have hrange : Finset.range p = Finset.Ico 0 p := by
    ext x
    simp
  have hsplit :
      (∑ k ∈ Finset.range p, ((k : ZMod p)⁻¹) ^ 4) =
        ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 4 := by
    rw [hrange, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
    simp
  have hbij :
      (∑ k ∈ Finset.range p, ((k : ZMod p)⁻¹) ^ 4) = ∑ x : ZMod p, (x⁻¹) ^ 4 := by
    refine Finset.sum_bij (fun k _ => (k : ZMod p)) ?_ ?_ ?_ ?_
    · intro k _; exact Finset.mem_univ _
    · intro a ha b hb hab
      rw [Finset.mem_range] at ha hb
      have hv := congrArg ZMod.val hab
      rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hv
    · intro b _
      exact ⟨b.val, Finset.mem_range.mpr (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
    · intro _ _; rfl
  have heqv := Fintype.sum_equiv (Equiv.inv (ZMod p))
    (fun x : ZMod p => (x⁻¹) ^ 4) (fun x : ZMod p => x ^ 4) (fun _ => rfl)
  rw [← hsplit, hbij, heqv]
  exact sum_pow_four_zmod_p hp7

end OeisA212334Proof

theorem OMA.solution : type_of% @OeisA212334.conjecture_1 := by
  intro p hp hp5
  have hp_pos : 0 < p := hp.pos
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ 5) := ⟨pow_ne_zero 5 hp.ne_zero⟩
  set P : ZMod (p ^ 5) := (p : ZMod (p ^ 5))
  set S3 : ZMod (p ^ 5) := ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 5))⁻¹) ^ 3
  set S4 : ZMod (p ^ 5) := ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 5))⁻¹) ^ 4
  have ha_sum : (OeisA212334.a p : ZMod (p ^ 5)) = 1 + (P ^ 4 * S4 - P ^ 3 * S3) := by
    rw [OeisA212334Proof.a_eq_one_add_sum hp_pos]
    push_cast
    have hterms :
        ∑ k ∈ Finset.Ico 1 p, (OeisA212334Proof.term p k : ZMod (p ^ 5)) =
          ∑ k ∈ Finset.Ico 1 p,
            (P ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 4 - P ^ 3 * ((k : ZMod (p ^ 5))⁻¹) ^ 3) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      exact OeisA212334Proof.term_zmod_eq hp hk.1 hk.2
    rw [hterms, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS3_refl : ∑ k ∈ Finset.Ico 1 p, (((p - k : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3 = S3 := by
    have href := Finset.sum_Ico_reflect (fun k => ((k : ZMod (p ^ 5))⁻¹) ^ 3) 1 (by omega : p ≤ p + 1)
    rwa [show p + 1 - p = 1 by omega, show p + 1 - 1 = p by omega] at href
  have h2S3 : 2 * (P ^ 3 * S3) = -3 * P ^ 4 * S4 := by
    have hpair :
        ∑ k ∈ Finset.Ico 1 p,
            P ^ 3 * (((k : ZMod (p ^ 5))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3) =
          ∑ k ∈ Finset.Ico 1 p, -3 * P ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 4 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      exact OeisA212334Proof.pair_inv_cube_zmod hp hk.1 hk.2
    have hlhs :
        ∑ k ∈ Finset.Ico 1 p,
            P ^ 3 * (((k : ZMod (p ^ 5))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 5))⁻¹) ^ 3) =
          2 * (P ^ 3 * S3) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hS3_refl]
      ring
    have hrhs :
        ∑ k ∈ Finset.Ico 1 p, -3 * P ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 4 = -3 * P ^ 4 * S4 := by
      rw [← Finset.mul_sum]
    rw [← hlhs, ← hrhs]
    exact hpair
  have h2a : 2 * ((OeisA212334.a p : ZMod (p ^ 5)) - 1) = 5 * P ^ 4 * S4 := by
    rw [ha_sum]
    calc
      2 * (1 + (P ^ 4 * S4 - P ^ 3 * S3) - 1)
          = 2 * P ^ 4 * S4 - 2 * (P ^ 3 * S3) := by ring
      _ = 2 * P ^ 4 * S4 - (-3 * P ^ 4 * S4) := by rw [h2S3]
      _ = 5 * P ^ 4 * S4 := by ring
  have h5P4S4 : 5 * P ^ 4 * S4 = 0 := by
    by_cases hp5eq : p = 5
    · subst hp5eq
      have hp5z : P ^ 5 = 0 := OeisA212334Proof.pow5_eq_zero 5
      calc
        5 * P ^ 4 * S4 = P ^ 5 * S4 := by dsimp [P]; ring
        _ = 0 := by rw [hp5z, zero_mul]
    · have hp7 : 7 ≤ p := by
        have hne6 : p ≠ 6 := fun h => by subst h; exact absurd hp (by decide)
        omega
      let f : ZMod (p ^ 5) →+* ZMod p := ZMod.castHom ⟨p ^ 4, by ring⟩ (ZMod p)
      have hfS4 : f S4 = 0 := by
        dsimp [S4]
        rw [map_sum]
        have hcongr :
            ∑ k ∈ Finset.Ico 1 p, f (((k : ZMod (p ^ 5))⁻¹) ^ 4) =
              ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 4 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_Ico] at hk
          rw [map_pow]
          congr 1
          have hk_ne0 : (k : ZMod p) ≠ 0 := by
            intro h
            have hd : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp h
            have := Nat.le_of_dvd hk.1 hd
            omega
          have hkinv :
              (k : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹ = 1 :=
            OeisA212334Proof.zmod_mul_inv_pow
              (OeisA212334Proof.coprime_of_pos_lt_prime hp hk.1 hk.2)
          have hmul1 : (k : ZMod p) * f ((k : ZMod (p ^ 5))⁻¹) = 1 := by
            have hfm := congrArg f hkinv
            simpa [map_mul, map_one, map_natCast] using hfm
          have hmul2 : (k : ZMod p) * (k : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hk_ne0
          exact mul_left_cancel₀ hk_ne0 (hmul1.trans hmul2.symm)
        rw [hcongr]
        exact OeisA212334Proof.sum_Ico_inv_pow4_zmod_p hp7
      have hval : (S4.val : ZMod p) = 0 := by
        have hcast : ((S4.val : ℕ) : ZMod (p ^ 5)) = S4 := ZMod.natCast_zmod_val S4
        have hfc : f ((S4.val : ℕ) : ZMod (p ^ 5)) = f S4 := congrArg f hcast
        rw [map_natCast, hfS4] at hfc
        exact hfc
      have hdvd : p ∣ S4.val := (ZMod.natCast_eq_zero_iff S4.val p).mp hval
      rcases hdvd with ⟨q, hq⟩
      have hS4_mul : S4 = P * (q : ZMod (p ^ 5)) := by
        have hcast : S4 = (S4.val : ZMod (p ^ 5)) := (ZMod.natCast_zmod_val S4).symm
        rw [hcast, hq]
        dsimp [P]
        push_cast
        rfl
      have hp5z : P ^ 5 = 0 := OeisA212334Proof.pow5_eq_zero p
      rw [hS4_mul]
      calc
        5 * P ^ 4 * (P * (q : ZMod (p ^ 5))) = P ^ 5 * (5 * (q : ZMod (p ^ 5))) := by ring
        _ = 0 := by rw [hp5z, zero_mul]
  rw [h5P4S4] at h2a
  have h2cop : Nat.Coprime 2 p := by
    refine OeisA212334Proof.coprime_of_pos_lt_prime hp (by omega) (by omega)
  have h2inv : (2 : ZMod (p ^ 5)) * (2 : ZMod (p ^ 5))⁻¹ = 1 :=
    OeisA212334Proof.zmod_mul_inv_pow h2cop
  have hsub0 : (OeisA212334.a p : ZMod (p ^ 5)) - 1 = 0 := by
    calc
      (OeisA212334.a p : ZMod (p ^ 5)) - 1
          = (2 : ZMod (p ^ 5))⁻¹ * (2 : ZMod (p ^ 5)) * ((OeisA212334.a p : ZMod (p ^ 5)) - 1) := by
            rw [mul_comm ((2 : ZMod (p ^ 5))⁻¹), h2inv, one_mul]
      _ = (2 : ZMod (p ^ 5))⁻¹ * (2 * ((OeisA212334.a p : ZMod (p ^ 5)) - 1)) := by ring
      _ = 0 := by rw [h2a, mul_zero]
  have heq1 : (OeisA212334.a p : ZMod (p ^ 5)) = (1 : ZMod (p ^ 5)) := sub_eq_zero.mp hsub0
  have hmod : OeisA212334.a p % (p ^ 5) = 1 % (p ^ 5) :=
    (ZMod.natCast_eq_natCast_iff' (OeisA212334.a p) 1 (p ^ 5)).mp (by simpa using heq1)
  have hlt1 : 1 < p ^ 5 := by
    have : 5 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left hp5 5
    omega
  rwa [Nat.mod_eq_of_lt hlt1] at hmod
