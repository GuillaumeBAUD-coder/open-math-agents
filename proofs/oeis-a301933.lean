import OMAStatements.S_oeis_a301933
import Mathlib

-- Problem: A301933: G.f. A(x) satisfies: A(x) = x*(1 + 4*A(x)*A'(x)) / (1 + A(x)*A'(x)).
-- Upstream: statements/oeis-a301933.lean (declaration OMA.S_oeis_a301933.main)
-- Credit: @sun-jiao (statement and characteristic-two approach noted by @anmolspace)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

section OeisA301933Proof

private def qTerm (f : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (m + 1),
    if i = 0 then 0 else f i * (f (m - i + 1) * ((m - i + 1 : ℕ) : ℤ))

private def nextCoeff (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0
  else if n = 1 then 1
  else
    4 * qTerm f (n - 1) -
      ∑ r ∈ Finset.range (n + 1), if r = 0 ∨ r = n then 0 else f r * qTerm f (n - r)

private def seqUpTo : ℕ → (ℕ → ℤ)
  | 0 => fun _ => 0
  | N + 1 =>
    let prev := seqUpTo N
    fun k => if k = N + 1 then nextCoeff prev (N + 1) else prev k

private def aSeq (n : ℕ) : ℤ := seqUpTo n n

private lemma seqUpTo_stable {k N : ℕ} (h : k ≤ N) : seqUpTo N k = aSeq k := by
  induction N with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero h
    subst hk
    rfl
  | succ N ih =>
    by_cases hk : k = N + 1
    · subst hk
      rfl
    · have hle : k ≤ N := by omega
      simp [seqUpTo, hk, ih hle]

private lemma qTerm_congr {f g : ℕ → ℤ} {m : ℕ} (h : ∀ j ≤ m, f j = g j) :
    qTerm f m = qTerm g m := by
  unfold qTerm
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  split_ifs with hi0
  · rfl
  · have h1 : i ≤ m := by omega
    have h2 : m - i + 1 ≤ m := by omega
    rw [h i h1, h (m - i + 1) h2]

private lemma aSeq_zero : aSeq 0 = 0 := rfl

private lemma aSeq_one : aSeq 1 = 1 := rfl

private lemma aSeq_ge_two {n : ℕ} (hn : 2 ≤ n) :
    aSeq n =
      4 * qTerm aSeq (n - 1) -
        ∑ r ∈ Finset.range (n + 1),
          if r = 0 ∨ r = n then 0 else aSeq r * qTerm aSeq (n - r) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hstep : aSeq (m + 1) = nextCoeff (seqUpTo m) (m + 1) := by
    simp [aSeq, seqUpTo]
  rw [hstep]
  unfold nextCoeff
  have hne0 : m + 1 ≠ 0 := by omega
  have hne1 : m + 1 ≠ 1 := by omega
  rw [if_neg hne0, if_neg hne1]
  have hq : qTerm (seqUpTo m) m = qTerm aSeq m :=
    qTerm_congr fun j hj => seqUpTo_stable hj
  have hsum :
      (∑ r ∈ Finset.range (m + 2),
        if r = 0 ∨ r = m + 1 then 0 else seqUpTo m r * qTerm (seqUpTo m) (m + 1 - r)) =
      ∑ r ∈ Finset.range (m + 2),
        if r = 0 ∨ r = m + 1 then 0 else aSeq r * qTerm aSeq (m + 1 - r) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    split_ifs with hr0
    · rfl
    · push Not at hr0
      have hrle : r ≤ m := by omega
      have hsub : m + 1 - r ≤ m := by omega
      rw [seqUpTo_stable hrle, qTerm_congr fun j hj => seqUpTo_stable (le_trans hj hsub)]
  simpa [hq] using congrArg (4 * qTerm aSeq m - ·) hsum

private lemma qTerm_zero (f : ℕ → ℤ) : qTerm f 0 = 0 := by
  simp [qTerm]

private lemma coeff_mul_deriv_aSeq (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.mk aSeq * PowerSeries.derivative ℤ (PowerSeries.mk aSeq)) =
      qTerm aSeq m := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold qTerm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
  split_ifs with hi0
  · subst hi0
    simp [aSeq_zero]
  · rfl

private lemma exists_defines : ∃ A : PowerSeries ℤ, OMA.S_oeis_a301933.Defines A := by
  let A : PowerSeries ℤ := PowerSeries.mk aSeq
  refine ⟨A, ?_, ?_, ?_⟩
  · simp [A, aSeq_zero]
  · simp [A, aSeq_one]
  · ext n
    have hmul :
        PowerSeries.coeff n (A * (A * PowerSeries.derivative ℤ A)) =
          ∑ r ∈ Finset.range (n + 1),
            if r = 0 ∨ r = n then 0 else aSeq r * qTerm aSeq (n - r) := by
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [PowerSeries.coeff_mk, coeff_mul_deriv_aSeq]
      split_ifs with hr
      · rcases hr with rfl | rfl
        · simp [aSeq_zero]
        · simp [qTerm_zero]
      · rfl
    have hlhs :
        PowerSeries.coeff n (A * (1 + A * PowerSeries.derivative ℤ A)) =
          aSeq n +
            ∑ r ∈ Finset.range (n + 1),
              if r = 0 ∨ r = n then 0 else aSeq r * qTerm aSeq (n - r) := by
      rw [mul_add, mul_one, map_add, PowerSeries.coeff_mk, hmul]
    rw [hlhs]
    rcases n with _ | _ | k
    · simp [aSeq_zero, PowerSeries.coeff_zero_eq_constantCoeff]
    · have hsum1 :
          (∑ r ∈ Finset.range 2,
            if r = 0 ∨ r = 1 then 0 else aSeq r * qTerm aSeq (1 - r)) = 0 := by
        simp [Finset.sum_range_succ]
      have hA0 : PowerSeries.constantCoeff A = 0 := by simp [A, aSeq_zero]
      simp [aSeq_one, PowerSeries.coeff_succ_X_mul, hsum1, hA0]
    · have hn2 : 2 ≤ k + 2 := by omega
      have ha := aSeq_ge_two hn2
      rw [PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_one,
        if_neg (Nat.succ_ne_zero k), zero_add]
      have h4 :
          PowerSeries.coeff (k + 1) (4 * A * PowerSeries.derivative ℤ A) =
            4 * qTerm aSeq (k + 1) := by
        rw [mul_assoc]
        change PowerSeries.coeff (k + 1)
            (PowerSeries.C (4 : ℤ) * (A * PowerSeries.derivative ℤ A)) = _
        rw [PowerSeries.coeff_C_mul, coeff_mul_deriv_aSeq]
      rw [h4]
      change aSeq (k + 2) +
          (∑ r ∈ Finset.range (k + 2 + 1),
            if r = 0 ∨ r = k + 2 then 0 else aSeq r * qTerm aSeq (k + 2 - r)) =
        4 * qTerm aSeq (k + 2 - 1)
      linarith

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma ps_zmod2_add_self (f : PowerSeries (ZMod 2)) : f + f = 0 := by
  ext n
  simpa using zmod2_add_self (PowerSeries.coeff n f)

private lemma zmod2_frobenius_id (x : ZMod 2) : frobenius (ZMod 2) 2 x = x := by
  rw [frobenius_def]
  fin_cases x <;> rfl

private lemma map_deriv_zmod2 (A : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (PowerSeries.derivative ℤ A) =
      PowerSeries.derivative (ZMod 2) (PowerSeries.map (Int.castRingHom (ZMod 2)) A) := by
  ext n
  simp [PowerSeries.coeff_derivative]

private lemma deriv_deriv_zmod2 (Y : PowerSeries (ZMod 2)) :
    PowerSeries.derivative (ZMod 2) (PowerSeries.derivative (ZMod 2) Y) = 0 := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, map_zero, mul_assoc]
  push_cast
  have hz : (((n : ZMod 2) + 1 + 1) * ((n : ZMod 2) + 1)) = 0 := by
    generalize (n : ZMod 2) = x
    fin_cases x <;> decide
  rw [hz, mul_zero]

private lemma deriv_mul_zmod2 (f g : PowerSeries (ZMod 2)) :
    PowerSeries.derivative (ZMod 2) (f * g) =
      f * PowerSeries.derivative (ZMod 2) g + g * PowerSeries.derivative (ZMod 2) f := by
  rw [(PowerSeries.derivative (ZMod 2)).leibniz f g]
  simp [smul_eq_mul]

private lemma coeff_sq_zmod2 (Y : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (Y ^ 2) = if 2 ∣ n then PowerSeries.coeff (n / 2) Y else 0 := by
  have hsq :
      Y ^ 2 =
        PowerSeries.map (frobenius (ZMod 2) 2) (PowerSeries.expand 2 two_ne_zero Y) :=
    (MvPowerSeries.map_frobenius_expand 2 two_ne_zero (f := Y)).symm
  rw [hsq, PowerSeries.coeff_map, PowerSeries.coeff_expand, zmod2_frobenius_id]

private lemma coeff_mod2_iff_pow_two (Y : PowerSeries (ZMod 2))
    (hY1 : PowerSeries.coeff 1 Y = 1) (hYeq : Y = PowerSeries.X + Y ^ 2) :
    ∀ n : ℕ, 0 < n → (PowerSeries.coeff n Y = 1 ↔ ∃ k : ℕ, n = 2 ^ k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn1 : n = 1
    · subst hn1
      simp only [hY1, true_iff]
      exact ⟨0, rfl⟩
    · have hstep : PowerSeries.coeff n Y = PowerSeries.coeff n (Y ^ 2) := by
        have hc := congrArg (PowerSeries.coeff n) hYeq
        simpa [PowerSeries.coeff_X, hn1] using hc
      rw [hstep, coeff_sq_zmod2]
      split_ifs with hdvd
      · obtain ⟨m, rfl⟩ := hdvd
        have hm0 : 0 < m := by omega
        have hmlt : m < 2 * m := by omega
        rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2), ih m hmlt hm0]
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨k + 1, by ring⟩
        · rintro ⟨k, hk⟩
          rcases k with _ | k
          · omega
          · exact ⟨k, Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (by simpa [pow_succ'] using hk)⟩
      · constructor
        · intro h01
          exact absurd h01 zero_ne_one
        · rintro ⟨k, rfl⟩
          rcases k with _ | k
          · exact False.elim (hn1 rfl)
          · exact False.elim (hdvd ⟨2 ^ k, by ring⟩)

end OeisA301933Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a301933.main := by
  refine ⟨exists_defines, ?_⟩
  intro A hA n hn
  let Y : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) A
  have hY1 : PowerSeries.coeff 1 Y = 1 := by
    simp [Y, hA.2.1]
  have h4 : (PowerSeries.map (Int.castRingHom (ZMod 2))) (4 : PowerSeries ℤ) = 0 := by
    ext m
    change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff m (PowerSeries.C (4 : ℤ))) = 0
    rw [PowerSeries.coeff_C]
    split_ifs
    · decide
    · simp
  have hYrel : Y * (1 + Y * PowerSeries.derivative (ZMod 2) Y) = PowerSeries.X := by
    have hm := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hA.2.2
    rw [map_mul, map_add, map_one, map_mul, map_deriv_zmod2,
      map_mul, PowerSeries.map_X, map_add, map_one, map_mul, map_mul, h4,
      zero_mul, zero_mul, add_zero, mul_one] at hm
    exact hm
  have hdYY : PowerSeries.derivative (ZMod 2) (Y * Y) = 0 := by
    rw [deriv_mul_zmod2, ps_zmod2_add_self]
  have hdterm :
      PowerSeries.derivative (ZMod 2) (Y * (Y * PowerSeries.derivative (ZMod 2) Y)) = 0 := by
    rw [← mul_assoc, deriv_mul_zmod2, deriv_deriv_zmod2, hdYY, mul_zero, mul_zero, add_zero]
  have hdY : PowerSeries.derivative (ZMod 2) Y = 1 := by
    have hd := congrArg (PowerSeries.derivative (ZMod 2)) hYrel
    have hlhs :
        PowerSeries.derivative (ZMod 2) (Y * (1 + Y * PowerSeries.derivative (ZMod 2) Y)) =
          PowerSeries.derivative (ZMod 2) Y := by
      rw [mul_add, mul_one, map_add, hdterm, add_zero]
    rw [hlhs, PowerSeries.derivative_X] at hd
    exact hd
  have hYeq : Y = PowerSeries.X + Y ^ 2 := by
    have h1 : Y + Y ^ 2 = PowerSeries.X := by
      simpa [hdY, mul_add, sq] using hYrel
    calc
      Y = Y + (Y ^ 2 + Y ^ 2) := by rw [ps_zmod2_add_self, add_zero]
      _ = (Y + Y ^ 2) + Y ^ 2 := by ring
      _ = PowerSeries.X + Y ^ 2 := by rw [h1]
  have hmapQ :
      PowerSeries.map (Int.castRingHom (ZMod 2)) (A * PowerSeries.derivative ℤ A) = Y := by
    rw [map_mul, map_deriv_zmod2]
    change Y * PowerSeries.derivative (ZMod 2) Y = Y
    rw [hdY, mul_one]
  have hYpow := coeff_mod2_iff_pow_two Y hY1 hYeq n hn
  have hAodd : Odd (PowerSeries.coeff (R := ℤ) n A) ↔ ∃ k : ℕ, n = 2 ^ k := by
    rw [← ZMod.intCast_eq_one_iff_odd]
    have hc : ((PowerSeries.coeff (R := ℤ) n A : ZMod 2)) = PowerSeries.coeff (R := ZMod 2) n Y := by
      simp [Y]
    rw [hc]
    exact hYpow
  have hQodd :
      Odd (PowerSeries.coeff (R := ℤ) n (A * PowerSeries.derivative ℤ A)) ↔ ∃ k : ℕ, n = 2 ^ k := by
    rw [← ZMod.intCast_eq_one_iff_odd]
    have hc :
        ((PowerSeries.coeff (R := ℤ) n (A * PowerSeries.derivative ℤ A) : ZMod 2)) =
          PowerSeries.coeff (R := ZMod 2) n Y := by
      have hm := congrArg (PowerSeries.coeff (R := ZMod 2) n) hmapQ
      rwa [PowerSeries.coeff_map] at hm
    rw [hc]
    exact hYpow
  exact ⟨hAodd, hQodd⟩
