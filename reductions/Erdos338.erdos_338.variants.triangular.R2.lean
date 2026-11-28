import FormalConjectures.ErdosProblems.«338»
import Mathlib

/-! # Ordinary and restricted sums of triangular numbers
The Legendre three-square proof below is the ATLAS adaptation retained in
open-math-agents, proofs/oeis-a004215.lean (upstream ATLAS dcb77c85757e945810657e5dce688ae82ff8eb25).
Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved. License at end.
The parity conversion and the order-two obstruction are from the existing
triangular-number reductions and the proof of the order-two obstruction.
The reflection, removal of ordinary representations, and square-kernel
reduction are the new parts. -/

namespace Nat

/-- Divisibility step of Ankeny's proof: a small nonzero lattice value divisible
by both `m` and `k` (which are coprime since `m ∣ k + 1`) and below `2 * m * k`
must equal `m * k`. -/
private theorem ankeny_lattice_value_eq {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hmk : m ∣ k + 1) {b : ℤ} (hb : (k : ℤ) ∣ b ^ 2 + (m : ℤ))
    {R X T : ℤ} (hne : ¬ (R = 0 ∧ X = 0 ∧ T = 0))
    (hRX : (m : ℤ) ∣ R - X) (hXT : (k : ℤ) ∣ X - b * T)
    (hlt : (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 < 2 * (m : ℤ) * (k : ℤ)) :
    (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 = (m : ℤ) * (k : ℤ) := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hVnn : (0 : ℤ) ≤ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := by
    positivity
  have hVne : (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 ≠ 0 := by
    intro hV0
    have e1 : (0 : ℤ) ≤ (k : ℤ) * R ^ 2 := by positivity
    have e2 : (0 : ℤ) ≤ X ^ 2 := by positivity
    have e3 : (0 : ℤ) ≤ (m : ℤ) * T ^ 2 := by positivity
    have g1 : (k : ℤ) * R ^ 2 = 0 := le_antisymm (by linarith) e1
    have g2 : X ^ 2 = 0 := le_antisymm (by linarith) e2
    have g3 : (m : ℤ) * T ^ 2 = 0 := le_antisymm (by linarith) e3
    obtain ⟨hR, hX, hT⟩ : (k : ℤ) * R ^ 2 = 0 ∧ X ^ 2 = 0 ∧ (m : ℤ) * T ^ 2 = 0 :=
      ⟨g1, g2, g3⟩
    have hR0 : R = 0 := by
      by_contra hR
      have hpos2 : (0 : ℤ) < (k : ℤ) * R ^ 2 :=
        mul_pos hkZ (sq_pos_of_ne_zero hR)
      linarith
    have hX0 : X = 0 := by
      by_contra hX
      have hpos : (0 : ℤ) < X ^ 2 := sq_pos_of_ne_zero hX
      linarith
    have hT0 : T = 0 := by
      by_contra hT
      have hpos2 : (0 : ℤ) < (m : ℤ) * T ^ 2 :=
        mul_pos hmZ (sq_pos_of_ne_zero hT)
      linarith
    exact hne ⟨hR0, hX0, hT0⟩
  have hVpos : (0 : ℤ) < (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 :=
    lt_of_le_of_ne hVnn (Ne.symm hVne)
  -- `k` divides the value, via `X ≡ b * T`.
  have hX : b * T ≡ X [ZMOD (k : ℤ)] := Int.modEq_iff_dvd.mpr hXT
  have hkV : (k : ℤ) ∣ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := by
    have e1 : (b * T) ^ 2 ≡ X ^ 2 [ZMOD (k : ℤ)] := hX.pow 2
    have e2 : (b * T) ^ 2 + (m : ℤ) * T ^ 2 ≡ X ^ 2 + (m : ℤ) * T ^ 2
        [ZMOD (k : ℤ)] := e1.add_right _
    have hrr : (b * T) ^ 2 + (m : ℤ) * T ^ 2 = (b ^ 2 + (m : ℤ)) * T ^ 2 := by
      ring
    rw [hrr] at e2
    have hzero : (b ^ 2 + (m : ℤ)) * T ^ 2 ≡ 0 [ZMOD (k : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hb _)
    have hfin : X ^ 2 + (m : ℤ) * T ^ 2 ≡ 0 [ZMOD (k : ℤ)] := e2.symm.trans hzero
    have hdvd : (k : ℤ) ∣ X ^ 2 + (m : ℤ) * T ^ 2 := by
      have h := hfin.dvd
      rwa [zero_sub, dvd_neg] at h
    have h1 : (k : ℤ) ∣ (k : ℤ) * R ^ 2 := dvd_mul_right _ _
    have h := h1.add hdvd
    rwa [← add_assoc] at h
  -- `m` divides the value, via `R ≡ X` and `k + 1 ≡ 0`.
  have hR : X ≡ R [ZMOD (m : ℤ)] := Int.modEq_iff_dvd.mpr hRX
  have hmV : (m : ℤ) ∣ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := by
    have e1 : (k : ℤ) * X ^ 2 ≡ (k : ℤ) * R ^ 2 [ZMOD (m : ℤ)] :=
      (Int.ModEq.refl _).mul (hR.pow 2)
    have hmid : (k : ℤ) * X ^ 2 + X ^ 2 ≡ (k : ℤ) * R ^ 2 + X ^ 2
        [ZMOD (m : ℤ)] := e1.add (Int.ModEq.refl _)
    have hring : (k : ℤ) * X ^ 2 + X ^ 2 = ((k : ℤ) + 1) * X ^ 2 := by ring
    rw [hring] at hmid
    have hkm : ((k : ℤ) + 1) * X ^ 2 ≡ 0 [ZMOD (m : ℤ)] := by
      have hcast : (m : ℤ) ∣ ((k : ℤ) + 1) := by exact_mod_cast hmk
      exact Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hcast _)
    have hfin : (k : ℤ) * R ^ 2 + X ^ 2 ≡ 0 [ZMOD (m : ℤ)] :=
      hmid.symm.trans hkm
    have hdvd : (m : ℤ) ∣ (k : ℤ) * R ^ 2 + X ^ 2 := by
      have h := hfin.dvd
      rwa [zero_sub, dvd_neg] at h
    have h2 : (m : ℤ) ∣ (m : ℤ) * T ^ 2 := dvd_mul_right _ _
    exact hdvd.add h2
  -- `(m : ℤ)` and `(k : ℤ)` are coprime since `m ∣ k + 1`, so their product
  -- divides the value.
  have hiso : IsCoprime (m : ℤ) (k : ℤ) := by
    obtain ⟨t, ht⟩ := hmk
    refine ⟨(t : ℤ), -1, ?_⟩
    have h2 : ((k + 1 : ℕ) : ℤ) = ((m * t : ℕ) : ℤ) := by exact_mod_cast ht
    push_cast at h2
    linear_combination -h2
  have hmkV : (m : ℤ) * (k : ℤ)
      ∣ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := hiso.mul_dvd hmV hkV
  have hmkZ : (0 : ℤ) < (m : ℤ) * (k : ℤ) := mul_pos hmZ hkZ
  obtain ⟨j, hj⟩ := hmkV
  have hjpos : 0 < j := by
    by_contra h
    push Not at h
    have hle : (m : ℤ) * (k : ℤ) * j ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hmkZ) h
    linarith
  have hjlt : j < 2 := by
    by_contra h
    push Not at h
    have hle : 2 * ((m : ℤ) * (k : ℤ)) ≤ (m : ℤ) * (k : ℤ) * j := by
      calc 2 * ((m : ℤ) * (k : ℤ)) = ((m : ℤ) * (k : ℤ)) * 2 := by ring
        _ ≤ ((m : ℤ) * (k : ℤ)) * j :=
          mul_le_mul_of_nonneg_left h (le_of_lt hmkZ)
    linarith
  have hj1 : j = 1 := by omega
  rw [hj1, mul_one] at hj
  exact hj

/-- Valuation step: if `-d` is not a square in `ZMod p`, then every value of
`X ^ 2 + d * T ^ 2` has even `p`-adic valuation. -/
private theorem even_padicValInt_sq_add_mul_sq_of_not_isSquare {p : ℕ} [Fact p.Prime]
    {d : ℤ} (hd : ¬ IsSquare (-(d : ZMod p))) (X T : ℤ) :
    Even (padicValInt p (X ^ 2 + d * T ^ 2)) := by
  have hp2 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have key : ∀ N : ℕ, ∀ X T : ℤ, X.natAbs + T.natAbs = N →
      Even (padicValInt p (X ^ 2 + d * T ^ 2)) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro X T hNT
      by_cases h0 : X ^ 2 + d * T ^ 2 = 0
      · rw [h0, padicValInt.zero]
        exact ⟨0, rfl⟩
      by_cases hdvd : (p : ℤ) ∣ X ^ 2 + d * T ^ 2
      · have hT : (p : ℤ) ∣ T := by
          by_contra hT
          have hTz : (T : ZMod p) ≠ 0 := fun hz =>
            hT ((ZMod.intCast_zmod_eq_zero_iff_dvd T p).mp hz)
          have hcast : (X : ZMod p) ^ 2 + (d : ZMod p) * (T : ZMod p) ^ 2 = 0 := by
            have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
            push_cast at h
            exact h
          set x : ZMod p := (X : ZMod p) with hx
          set t : ZMod p := (T : ZMod p) with ht
          set δ : ZMod p := (d : ZMod p) with hδ
          have hx2 : x ^ 2 = -(δ * t ^ 2) := by linear_combination hcast
          have e2 : (t⁻¹) ^ 2 * t ^ 2 = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hTz, one_pow]
          have e3 : -(δ * t ^ 2) * (t⁻¹) ^ 2 = -δ := by
            have e4 : -(δ * t ^ 2) * (t⁻¹) ^ 2 = -δ * ((t⁻¹) ^ 2 * t ^ 2) := by
              ring
            rw [e4, e2, mul_one]
          have hsq : -(δ) = (x * t⁻¹) * (x * t⁻¹) := by
            have e : (x * t⁻¹) * (x * t⁻¹) = x ^ 2 * (t⁻¹) ^ 2 := by ring
            rw [e, hx2, e3]
          exact hd ⟨x * t⁻¹, hsq⟩
        have hT2 : (p : ℤ) ∣ d * T ^ 2 :=
          dvd_mul_of_dvd_right (dvd_pow hT two_ne_zero) _
        have hX2 : (p : ℤ) ∣ X ^ 2 := (dvd_add_left hT2).mp hdvd
        have hX : (p : ℤ) ∣ X := hpZ.dvd_of_dvd_pow hX2
        obtain ⟨X', hX'⟩ := hX
        obtain ⟨T', hT'⟩ := hT
        have hfactor : X ^ 2 + d * T ^ 2
            = (p : ℤ) ^ 2 * (X' ^ 2 + d * T' ^ 2) := by
          rw [hX', hT']
          ring
        have hSne : X' ^ 2 + d * T' ^ 2 ≠ 0 := by
          intro hcon
          apply h0
          rw [hfactor, hcon, mul_zero]
        have hpp : padicValInt p ((p : ℤ) ^ 2) = 2 := by
          have h1 : (p : ℤ) ^ 2 = (p : ℤ) * (p : ℤ) := by ring
          have hp0 : (p : ℤ) ≠ 0 := by
            have := hp2
            omega
          rw [h1, padicValInt.mul hp0 hp0, padicValInt.self hp2]
        have hval : padicValInt p (X ^ 2 + d * T ^ 2)
            = 2 + padicValInt p (X' ^ 2 + d * T' ^ 2) := by
          rw [hfactor, padicValInt.mul (by positivity) hSne, hpp]
        have eX : X.natAbs = p * X'.natAbs := by
          rw [hX', Int.natAbs_mul, Int.natAbs_natCast]
        have eT : T.natAbs = p * T'.natAbs := by
          rw [hT', Int.natAbs_mul, Int.natAbs_natCast]
        have hXle : X'.natAbs ≤ X.natAbs := by
          rw [eX]
          exact le_mul_of_one_le_left (Nat.zero_le _) hp2.le
        have hTle : T'.natAbs ≤ T.natAbs := by
          rw [eT]
          exact le_mul_of_one_le_left (Nat.zero_le _) hp2.le
        have hne00 : X ≠ 0 ∨ T ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply h0
          rw [hcon.1, hcon.2]
          simp
        have hltN : X'.natAbs + T'.natAbs < N := by
          have hXlt : X ≠ 0 → X'.natAbs < X.natAbs := by
            intro hneX
            have hneX' : X' ≠ 0 := by
              intro hcon
              apply hneX
              rw [hX', hcon, mul_zero]
            rw [eX]
            have hpos : 0 < X'.natAbs := Int.natAbs_pos.mpr hneX'
            calc X'.natAbs = 1 * X'.natAbs := (one_mul _).symm
              _ < p * X'.natAbs := by
                rw [one_mul]
                exact lt_mul_of_one_lt_left hpos hp2
          have hTlt : T ≠ 0 → T'.natAbs < T.natAbs := by
            intro hneT
            have hneT' : T' ≠ 0 := by
              intro hcon
              apply hneT
              rw [hT', hcon, mul_zero]
            rw [eT]
            have hpos : 0 < T'.natAbs := Int.natAbs_pos.mpr hneT'
            calc T'.natAbs = 1 * T'.natAbs := (one_mul _).symm
              _ < p * T'.natAbs := by
                rw [one_mul]
                exact lt_mul_of_one_lt_left hpos hp2
          rcases hne00 with hneX | hneT
          · have := hXlt hneX
            omega
          · have := hTlt hneT
            omega
        have ihE := ih _ hltN X' T' rfl
        rw [hval]
        obtain ⟨r, hr⟩ := ihE
        exact ⟨r + 1, by omega⟩
      · rw [padicValInt.eq_zero_of_not_dvd hdvd]
        exact ⟨0, rfl⟩
  exact key _ X T rfl

/-- Two-square step: from `m = R ^ 2 + N` and `k * N = X ^ 2 + m * T ^ 2`,
with `m` squarefree and no prime factor of `k` congruent to `3 mod 4`,
conclude `N` is a sum of two natural squares. -/
private theorem ankeny_exists_two_sq_of_rep {m k : ℕ} (hm : Squarefree m)
    (hk : 0 < k) (hmk : m ∣ k + 1)
    (hk4 : ∀ p : ℕ, p.Prime → p ∣ k → p % 4 ≠ 3)
    {R X T : ℤ} {N : ℕ} (hRm : (m : ℤ) = R ^ 2 + (N : ℤ))
    (hrep : (k : ℤ) * (N : ℤ) = X ^ 2 + (m : ℤ) * T ^ 2) :
    ∃ a c : ℕ, N = a ^ 2 + c ^ 2 := by
  by_cases hN0 : N = 0
  · subst hN0
    exact ⟨0, 0, by simp⟩
  rw [Nat.eq_sq_add_sq_iff]
  intro q hq hq4
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqdvdN : q ∣ N := Nat.dvd_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqprime⟩
  have hpZq : _root_.Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqprime
  have hqN : (q : ℤ) ∣ (N : ℤ) := by exact_mod_cast hqdvdN
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hqprime.ne_zero
  by_cases hqm : (q : ℤ) ∣ (m : ℤ)
  · -- Case `q ∣ m`: derive a contradiction from `-1` being a square mod `q`.
    have hqmN : q ∣ m := Int.natCast_dvd_natCast.mp hqm
    have hqk1 : q ∣ k + 1 := dvd_trans hqmN hmk
    rcases hqmN with ⟨m₁, hm₁⟩
    have hqm1 : ¬ q ∣ m₁ := by
      intro hd
      obtain ⟨t, ht⟩ := hd
      have hqq : q * q ∣ m := ⟨t, by rw [hm₁, ht]; ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hm) q hqprime hqq
    have hR2 : (q : ℤ) ∣ R ^ 2 := by
      have e : R ^ 2 = (m : ℤ) - (N : ℤ) := by omega
      rw [e]
      obtain ⟨a, ha⟩ := hqm
      obtain ⟨b, hb⟩ := hqN
      exact ⟨a - b, by linear_combination ha - hb⟩
    have hR : (q : ℤ) ∣ R := hpZq.dvd_of_dvd_pow hR2
    have hX2 : (q : ℤ) ∣ X ^ 2 := by
      have e : X ^ 2 = (k : ℤ) * (N : ℤ) - (m : ℤ) * T ^ 2 := by omega
      rw [e]
      obtain ⟨a, ha⟩ := dvd_mul_of_dvd_right hqN ((k : ℤ))
      obtain ⟨b, hb⟩ := dvd_mul_of_dvd_right hqm (T ^ 2)
      exact ⟨a - b, by linear_combination ha - hb⟩
    have hX : (q : ℤ) ∣ X := hpZq.dvd_of_dvd_pow hX2
    obtain ⟨R₁, hR₁⟩ := hR
    obtain ⟨X₁, hX₁⟩ := hX
    obtain ⟨N₁, hN₁⟩ := hqdvdN
    have hdiv : (k : ℤ) * (N₁ : ℤ) = (q : ℤ) * X₁ ^ 2 + (m₁ : ℤ) * T ^ 2 := by
      have h := hrep
      rw [hN₁, hm₁, hX₁] at h
      push_cast at h
      have h2 : ((k : ℤ) * (N₁ : ℤ)) * (q : ℤ)
          = ((q : ℤ) * X₁ ^ 2 + (m₁ : ℤ) * T ^ 2) * (q : ℤ) := by
        linear_combination h
      exact mul_right_cancel₀ hq0 h2
    have hNm : (N₁ : ℤ) = (m₁ : ℤ) - (q : ℤ) * R₁ ^ 2 := by
      have h := hRm
      rw [hN₁, hm₁, hR₁] at h
      push_cast at h
      have hcan : ((m₁ : ℤ) - (N₁ : ℤ)) * (q : ℤ)
          = ((q : ℤ) * R₁ ^ 2) * (q : ℤ) := by
        linear_combination h
      have hcan2 := mul_right_cancel₀ hq0 hcan
      omega
    have hdivZ : (k : ZMod q) * ((N₁ : ℕ) : ZMod q)
        = ((m₁ : ℕ) : ZMod q) * (T : ZMod q) ^ 2 := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) hdiv
      simpa using h
    have hNmZ : ((N₁ : ℕ) : ZMod q) = ((m₁ : ℕ) : ZMod q) := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) hNm
      simpa using h
    rw [hNmZ] at hdivZ
    have hm1z : ((m₁ : ℕ) : ZMod q) ≠ 0 := by
      intro hz
      apply hqm1
      have hz' : ((((m₁ : ℕ)) : ℤ) : ZMod q) = 0 := by exact_mod_cast hz
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hz'
      exact Int.natCast_dvd_natCast.mp hdvd
    have hkT : (k : ZMod q) = (T : ZMod q) ^ 2 := by
      have h := hdivZ
      rw [mul_comm ((m₁ : ℕ) : ZMod q) _] at h
      exact mul_right_cancel₀ hm1z h
    have hk1 : ((k : ℕ) : ZMod q) = -1 := by
      have hdvd : (q : ℤ) ∣ ((k : ℕ) : ℤ) + 1 := by exact_mod_cast hqk1
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
      have hz2 : ((k : ℕ) : ZMod q) + 1 = 0 := by
        simpa using hz
      linear_combination hz2
    have hsqN : IsSquare (-1 : ZMod q) := ⟨(T : ZMod q), by rw [← hk1, hkT, pow_two]⟩
    exact absurd hq4 (ZMod.exists_sq_eq_neg_one_iff.mp hsqN)
  · -- Case `¬ q ∣ m`: the valuation of `N` is even.
    have hqmB : ¬ q ∣ m := fun hd => hqm (by exact_mod_cast hd)
    have hqk : ¬ q ∣ k := fun hd => (hk4 q hqprime hd) hq4
    have hNq : ((N : ℕ) : ZMod q) = 0 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hqN
      exact_mod_cast h
    have hRmZ : ((m : ℕ) : ZMod q) = (R : ZMod q) ^ 2 + ((N : ℕ) : ZMod q) := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) hRm
      simpa using h
    have hnsqB : ¬ IsSquare (-((((m : ℕ)) : ℤ) : ZMod q)) := by
      intro hs
      have hRz : (R : ZMod q) ≠ 0 := by
        intro hz
        apply hqmB
        have h : ((m : ℕ) : ZMod q) = 0 := by
          rw [hRmZ, hz, hNq]
          simp
        have h' : ((((m : ℕ)) : ℤ) : ZMod q) = 0 := by exact_mod_cast h
        have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
        exact Int.natCast_dvd_natCast.mp hdvd
      obtain ⟨s, hs⟩ := hs
      have hRmz : (R : ZMod q) ^ 2 = ((((m : ℕ)) : ℤ) : ZMod q) := by
        have h := hRmZ
        rw [hNq, add_zero] at h
        exact_mod_cast h.symm
      have hsq1 : (-1 : ZMod q)
          = (s * (R : ZMod q)⁻¹) * (s * (R : ZMod q)⁻¹) := by
        have eR : (R : ZMod q) * (R : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ hRz
        have e : (s * (R : ZMod q)⁻¹) * (s * (R : ZMod q)⁻¹)
            = (s * s) * ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) := by ring
        have e3 : ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) * (R : ZMod q) ^ 2 = 1 := by
          have e4 : ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) * (R : ZMod q) ^ 2
              = ((R : ZMod q) * (R : ZMod q)⁻¹) ^ 2 := by ring
          rw [e4, eR, one_pow]
        have e6 : -((R : ZMod q) ^ 2) * ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹)
            = -1 := by
          have e7 : -((R : ZMod q) ^ 2) * ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹)
              = -(((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) * (R : ZMod q) ^ 2) := by
            ring
          rw [e7, e3]
        rw [e, ← hs, ← hRmz]
        exact e6.symm
      exact (ZMod.exists_sq_eq_neg_one_iff.mp ⟨_, hsq1⟩) hq4
    have hmul : padicValInt q ((k : ℤ) * (N : ℤ))
        = padicValNat q k + padicValNat q N := by
      have hk0 : (k : ℤ) ≠ 0 := by
        have := hk
        omega
      have hN0' : (N : ℤ) ≠ 0 := by
        have := hN0
        omega
      rw [padicValInt.mul hk0 hN0', padicValInt.of_nat, padicValInt.of_nat]
    have heven := even_padicValInt_sq_add_mul_sq_of_not_isSquare (p := q) hnsqB X T
    rw [← hrep, hmul, padicValNat.eq_zero_of_not_dvd hqk, zero_add] at heven
    exact heven

/-- Jacobi step, case `m ≡ 1 (mod 4)`: `-m` is a nonzero square in `ZMod q`. -/
private theorem isSquare_neg_of_one_mod_four_case {q m : ℕ} [Fact q.Prime]
    (hq : q % 4 = 1) (hm : m % 4 = 1) (hdvd : m ∣ q + 1) :
    IsSquare (-((m : ℕ) : ZMod q)) ∧ (-((m : ℕ) : ZMod q)) ≠ 0 := by
  have hqprime : q.Prime := Fact.out
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  have h2q := hqprime.two_le
  -- `q` does not divide `m`.
  have hqm0 : ((m : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdZ : (q : ℤ) ∣ ((m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hz)
    have hdvdN : q ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨s, hs⟩ := hdvd
    rcases hdvdN with ⟨t, ht⟩
    have hqq1 : q ∣ q + 1 := ⟨t * s, by rw [hs, ht]; ring⟩
    have hqq1Z : (q : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hqq1
    have hq1Z : (q : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hqq1Z
      exact ⟨a - 1, by linear_combination ha⟩
    have hq1 : q ∣ 1 := Int.natCast_dvd_natCast.mp hq1Z
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hq1
    omega
  -- `q ≡ -1 (mod m)` as integers.
  have hmod : (q : ℤ) % ((m : ℕ) : ℤ) = (-1 : ℤ) % ((m : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hcast : ((m : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hdvd
    have h0 : ((q : ℤ) + 1) % ((m : ℕ) : ℤ) = 0 := Int.emod_eq_zero_of_dvd hcast
    have heq : (q : ℤ) - (-1) = (q : ℤ) + 1 := by ring
    rw [heq]
    exact h0
  have hchiq : ZMod.χ₄ (↑q : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hq
  have hchim : ZMod.χ₄ (↑m : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hm
  have hleg : legendreSym q (-((m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg _ hqodd, hchiq, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four hm hqodd,
      jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hmodd, hchim]
  have hne' : (Int.cast (-((m : ℕ) : ℤ)) : ZMod q) ≠ 0 := by
    intro h
    apply hqm0
    have h3 := h
    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h3
    exact h3
  have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
    have h := (legendreSym.eq_one_iff q hne').mp hleg
    simpa using h
  exact ⟨hsq, by simpa using hqm0⟩

/-- Jacobi step, case `m ≡ 3 (mod 8)`: `-m` is a nonzero square in `ZMod q`. -/
private theorem isSquare_neg_of_three_mod_eight_case {q m : ℕ} [Fact q.Prime]
    (hq : q % 4 = 1) (hm : m % 8 = 3) (hdvd : m ∣ 2 * q + 1) :
    IsSquare (-((m : ℕ) : ZMod q)) ∧ (-((m : ℕ) : ZMod q)) ≠ 0 := by
  have hqprime : q.Prime := Fact.out
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  have h2q := hqprime.two_le
  -- `q` does not divide `m`.
  have hqm0 : ((m : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdZ : (q : ℤ) ∣ ((m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hz)
    have hdvdN : q ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨s, hs⟩ := hdvd
    rcases hdvdN with ⟨t, ht⟩
    have hqq1 : q ∣ 2 * q + 1 := ⟨t * s, by rw [hs, ht]; ring⟩
    have hqq1Z : (q : ℤ) ∣ 2 * (q : ℤ) + 1 := by exact_mod_cast hqq1
    have hq1Z : (q : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hqq1Z
      exact ⟨a - 2, by linear_combination ha⟩
    have hq1 : q ∣ 1 := Int.natCast_dvd_natCast.mp hq1Z
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hq1
    omega
  -- `-2 * q ≡ 1 (mod m)` as integers.
  have hmod2 : (-2 * (q : ℤ)) % ((m : ℕ) : ℤ) = (1 : ℤ) % ((m : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hdvd2 : ((m : ℕ) : ℤ) ∣ (-2 * (q : ℤ)) - 1 := by
      have hcast : ((m : ℕ) : ℤ) ∣ 2 * (q : ℤ) + 1 := by exact_mod_cast hdvd
      obtain ⟨a, ha⟩ := hcast
      exact ⟨-a, by linear_combination -ha⟩
    exact Int.emod_eq_zero_of_dvd hdvd2
  have hchiq : ZMod.χ₄ (↑q : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hq
  have hchi8 : ZMod.χ₈' (↑m : ZMod 8) = 1 := by
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, if_neg (by omega : ¬ m % 2 = 0),
      if_pos (Or.inr hm)]
  have hJq : jacobiSym ((q : ℤ)) m = 1 := by
    have h2q1 : jacobiSym (-2 * (q : ℤ)) m = 1 := by
      rw [jacobiSym.mod_left' hmod2, jacobiSym.one_left]
    have hsplit := jacobiSym.mul_left (-2 : ℤ) ((q : ℤ)) m
    have hneg2 : jacobiSym (-2 : ℤ) m = 1 := by
      rw [jacobiSym.at_neg_two hmodd]
      exact hchi8
    rw [hsplit, hneg2, one_mul] at h2q1
    exact h2q1
  have hleg : legendreSym q (-((m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg _ hqodd, hchiq, one_mul,
      (jacobiSym.quadratic_reciprocity_one_mod_four hq hmodd).symm, hJq]
  have hne' : (Int.cast (-((m : ℕ) : ℤ)) : ZMod q) ≠ 0 := by
    intro h
    apply hqm0
    have h3 := h
    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h3
    exact h3
  have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
    have h := (legendreSym.eq_one_iff q hne').mp hleg
    simpa using h
  exact ⟨hsq, by simpa using hqm0⟩

/-- Jacobi step, case `m ≡ 2 (mod 4)`: then `q ≡ 1 (mod 4)` and `-m` is a
nonzero square in `ZMod q`. Here `m = 2 * m'` with `m'` odd. -/
private theorem isSquare_neg_of_two_mod_four_case {q m : ℕ} [Fact q.Prime]
    (hm : m % 4 = 2) (hdvd : m ∣ q + 1) (hq8 : q % 8 = (m - 1) % 8) :
    q % 4 = 1 ∧ IsSquare (-((m : ℕ) : ZMod q))
      ∧ (-((m : ℕ) : ZMod q)) ≠ 0 := by
  have hqprime : q.Prime := Fact.out
  have hq4 : q % 4 = 1 := by omega
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmeven : Even m := Nat.even_iff.mpr (by omega)
  obtain ⟨m', hm'⟩ := hmeven
  have hm2 : m = 2 * m' := by omega
  have hm'odd : Odd m' := by
    rw [Nat.odd_iff]
    omega
  have h2q := hqprime.two_le
  -- `q` does not divide `m`.
  have hqm0 : ((m : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdZ : (q : ℤ) ∣ ((m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hz)
    have hdvdN : q ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨s, hs⟩ := hdvd
    rcases hdvdN with ⟨t, ht⟩
    have hqq1 : q ∣ q + 1 := ⟨t * s, by rw [hs, ht]; ring⟩
    have hqq1Z : (q : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hqq1
    have hq1Z : (q : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hqq1Z
      exact ⟨a - 1, by linear_combination ha⟩
    have hq1 : q ∣ 1 := Int.natCast_dvd_natCast.mp hq1Z
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hq1
    omega
  have hmZ : ((m : ℕ) : ℤ) = 2 * ((m' : ℕ) : ℤ) := by exact_mod_cast hm2
  -- `q ≡ -1 (mod m')` as integers.
  have hmod' : (q : ℤ) % ((m' : ℕ) : ℤ) = (-1 : ℤ) % ((m' : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hdvd' : m' ∣ q + 1 :=
      dvd_trans ⟨2, by rw [hm2]; ring⟩ hdvd
    have hcast : ((m' : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hdvd'
    have h0 : ((q : ℤ) + 1) % ((m' : ℕ) : ℤ) = 0 := Int.emod_eq_zero_of_dvd hcast
    have heq : (q : ℤ) - (-1) = (q : ℤ) + 1 := by ring
    rw [heq]
    exact h0
  have e1 : (-((m : ℕ) : ℤ)) = -(2 * ((m' : ℕ) : ℤ)) := by rw [hmZ]
  have hchiq : ZMod.χ₄ (↑q : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hq4
  have hleg : legendreSym q (-((m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, e1, jacobiSym.neg _ hqodd,
      jacobiSym.mul_left, jacobiSym.at_two hqodd,
      (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hm'odd).symm,
      jacobiSym.mod_left' hmod', jacobiSym.at_neg_one hm'odd]
    have h2 : m' % 2 = 1 := Nat.odd_iff.mp hm'odd
    have hm'4 : m' % 4 = 1 ∨ m' % 4 = 3 := by omega
    rcases hm'4 with h1 | h3
    · have e41 : ZMod.χ₄ (↑q : ZMod 4) = 1 := hchiq
      have e81 : ZMod.χ₈ (↑q : ZMod 8) = 1 := by
        have hq81 : q % 8 = 1 := by omega
        rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ q % 2 = 0),
          if_pos (by omega : q % 8 = 1 ∨ q % 8 = 7)]
      have e4m : ZMod.χ₄ (↑m' : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four h1
      rw [e41, e81, e4m]
      norm_num
    · have e41 : ZMod.χ₄ (↑q : ZMod 4) = 1 := hchiq
      have e85 : ZMod.χ₈ (↑q : ZMod 8) = -1 := by
        have hq85 : q % 8 = 5 := by omega
        rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ q % 2 = 0),
          if_neg (by omega : ¬ (q % 8 = 1 ∨ q % 8 = 7))]
      have e4m : ZMod.χ₄ (↑m' : ZMod 4) = -1 := by
        rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega : ¬ m' % 2 = 0),
          if_neg (by omega : ¬ m' % 4 = 1)]
      rw [e41, e85, e4m]
      norm_num
  have hne' : (Int.cast (-((m : ℕ) : ℤ)) : ZMod q) ≠ 0 := by
    intro h
    apply hqm0
    have h3 := h
    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h3
    exact h3
  have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
    have h := (legendreSym.eq_one_iff q hne').mp hleg
    simpa using h
  exact ⟨hq4, hsq, by simpa using hqm0⟩

/-- An odd `a` coprime to `n` is coprime to `4 * n`. -/
private theorem ankeny_coprime_aux {a n : ℕ} (hodd : Odd a)
    (hcop : Nat.Coprime a n) : Nat.Coprime a (4 * n) := by
  have h2 : Nat.Coprime a 2 := by
    obtain ⟨t, ht⟩ := hodd
    have hbez : IsCoprime (((a : ℕ)) : ℤ) (((2 : ℕ)) : ℤ) := by
      refine ⟨1, -(t : ℤ), ?_⟩
      have htZ : ((a : ℕ) : ℤ) = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
      omega
    have h := Int.isCoprime_iff_nat_coprime.mp hbez
    simpa using h
  have h4 : Nat.Coprime a 4 := by
    have h := Nat.coprime_mul_iff_right.mpr ⟨h2, h2⟩
    rwa [show (2 : ℕ) * 2 = 4 from rfl] at h
  exact Nat.coprime_mul_iff_right.mpr ⟨h4, hcop⟩

/-- Dirichlet helper: a residue `a` coprime to `4 * m` yields a prime
`q ≡ a (mod 4 * m)` exceeding `4 * m`. -/
private theorem ankeny_dirichlet_prime {m a : ℕ} (hm : 0 < m)
    (hcop : Nat.Coprime a (4 * m)) :
    ∃ q : ℕ, q.Prime ∧ (4 * m) < q ∧ q % (4 * m) = a % (4 * m) := by
  have hne : NeZero (4 * m) := ⟨by omega⟩
  have hunit : IsUnit ((a : ℕ) : ZMod (4 * m)) :=
    (ZMod.isUnit_iff_coprime a (4 * m)).mpr hcop
  obtain ⟨q, hqgt, hqprime, hqeq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * m) hunit (4 * m)
  exact ⟨q, hqprime, hqgt,
    (ZMod.natCast_eq_natCast_iff' q a (4 * m)).mp hqeq⟩

/-- From `-m` a square mod `q`, get an integer root `b₀` with `q ∣ b₀ ^ 2 + m`. -/
private theorem ankeny_sq_root_mod {q m : ℕ} [NeZero q]
    (hsq : IsSquare (-((m : ℕ) : ZMod q))) :
    ∃ b₀ : ℤ, (q : ℤ) ∣ b₀ ^ 2 + (m : ℤ) := by
  obtain ⟨s, hs⟩ := hsq
  refine ⟨((s.val : ℕ) : ℤ), ?_⟩
  have hsq0 : (((s.val : ℕ)) : ZMod q) = s := ZMod.natCast_zmod_val s
  have hcast : (s ^ 2 + ((m : ℕ) : ZMod q)) = 0 := by
    rw [pow_two, ← hs, neg_add_cancel]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_pow, Int.cast_natCast, hsq0]
  exact hcast

/-- The sum-of-squares ball in `Fin 3 → ℝ`: volume, convexity, symmetry,
openness. It is the preimage of the Euclidean ball under `WithLp.toLp`. -/
private theorem volume_setOf_sum_sq_lt_fin_three {r : ℝ} (hr : 0 < r) :
    MeasureTheory.volume {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
        = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
    ∧ Convex ℝ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
    ∧ (∀ x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2},
      -x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2})
    ∧ IsOpen {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
  have hmem : ∀ x : Fin 3 → ℝ,
      (∑ i, (x i) ^ 2 < r ^ 2)
        ↔ WithLp.toLp 2 x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r := by
    intro x
    rw [Metric.mem_ball, _root_.dist_zero_right, EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
    rw [Real.sqrt_lt' hr]
  have hset : {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
      = WithLp.toLp 2 ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r := by
    ext x
    simp only [Set.mem_preimage]
    exact hmem x
  have hvol : MeasureTheory.volume {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
      = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [hset, (PiLp.volume_preserving_toLp (ι := Fin 3)).measure_preimage
      measurableSet_ball.nullMeasurableSet]
    exact EuclideanSpace.volume_ball_fin_three _ _
  have hconv : Convex ℝ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
    rw [hset]
    exact Convex.linear_preimage (convex_ball _ _)
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
  have hsymm : ∀ x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2},
      -x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
    intro x hx
    change ∑ i, ((-x) i) ^ 2 < r ^ 2
    simp only [Pi.neg_apply, neg_sq]
    exact hx
  have hopen : IsOpen {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
    rw [hset]
    exact Continuous.isOpen_preimage (PiLp.continuous_toLp 2 _) _ Metric.isOpen_ball
  exact ⟨hvol, hconv, hsymm, hopen⟩

/-- Minkowski for an ellipsoid in `ℝ³`: a real `3 × 3` matrix with nonzero
determinant sends some nonzero integer vector into the ball of radius `r`,
provided `8 * |det M| < (π * 4 / 3) * r ^ 3`. -/
private theorem exists_int_ne_zero_sum_sq_mulVec_lt
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hdet : M.det ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (hvol : 8 * |M.det| < (Real.pi * 4 / 3) * r ^ 3) :
    ∃ u : Fin 3 → ℤ, u ≠ 0 ∧
      ∑ i, ((M.mulVec (fun i => ((u i : ℤ) : ℝ))) i) ^ 2 < r ^ 2 := by
  obtain ⟨hBvol, hBconv, hBsymm, -⟩ := volume_setOf_sum_sq_lt_fin_three hr
  set f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' M with hf
  set S : Set (Fin 3 → ℝ) := f ⁻¹' {x | ∑ i, (x i) ^ 2 < r ^ 2} with hS
  have hSconv : Convex ℝ S := hBconv.linear_preimage f
  have hSsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hx' : f x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := hx
    have hneg : f (-x) ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
      rw [map_neg]
      exact hBsymm _ hx'
    exact hneg
  have hdetf : LinearMap.det f ≠ 0 := by
    rw [hf, LinearMap.det_toLin']
    exact hdet
  have hSvol : MeasureTheory.volume S = ENNReal.ofReal (|M.det|⁻¹) *
      (ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) := by
    rw [hS,
      MeasureTheory.Measure.addHaar_preimage_linearMap MeasureTheory.volume hdetf,
      hBvol]
    congr 1
    rw [hf, LinearMap.det_toLin', abs_inv]
  have hFvol : MeasureTheory.volume
      (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]
    simp
  have hfin : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  have hDpos : 0 < |M.det| := abs_pos.mpr hdet
  have hlat : MeasureTheory.volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) *
      2 ^ Module.finrank ℝ (Fin 3 → ℝ) < MeasureTheory.volume S := by
    rw [hFvol, hfin, one_mul]
    have h2 : (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num,
        ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat]
    rw [h2, hSvol, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r ^ 3),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ |M.det|⁻¹),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hmul := mul_lt_mul_of_pos_right hvol (inv_pos.mpr hDpos)
    have hinv : (8 : ℝ) = 8 * |M.det| * |M.det|⁻¹ := by field_simp
    rw [hinv]
    linear_combination hmul
  have : Countable
      ↥((Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup) :=
    inferInstanceAs
      (Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))))
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) MeasureTheory.volume)
      hSsymm hSconv hlat
  have hymem : (↑x : Fin 3 → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3))) :=
    x.2
  rw [Module.Basis.mem_span_iff_repr_mem] at hymem
  choose u hu using hymem
  have hAlg : ∀ n : ℤ, (algebraMap ℤ ℝ) n = (((n : ℤ)) : ℝ) := fun n => by simp
  have hu' : ∀ i, (((u i : ℤ)) : ℝ) = (↑x : Fin 3 → ℝ) i := by
    intro i
    have h1 := hu i
    rw [Pi.basisFun_repr, hAlg] at h1
    exact h1
  refine ⟨u, ?_, ?_⟩
  · intro hu0
    apply hx0
    have hy0 : (↑x : Fin 3 → ℝ) = 0 := by
      funext i
      have h1 : u i = 0 := by simp [hu0]
      simp only [← hu' i, h1, Int.cast_zero, Pi.zero_apply]
    exact Subtype.ext (by simpa using hy0)
  · have hM : M.mulVec (fun i => ((u i : ℤ) : ℝ)) = f (↑x : Fin 3 → ℝ) := by
      rw [hf, Matrix.toLin'_apply]
      congr 1
      funext i
      exact hu' i
    rw [hM]
    simpa [hS] using hxS

/-- Small lattice point step of Ankeny's proof: for `m > 0`, `k > 0` and `b : ℤ`
there are integers `R, X, T`, not all zero, with `m ∣ R - X`, `k ∣ X - b * T`
and `k * R ^ 2 + X ^ 2 + m * T ^ 2 < 2 * m * k`. -/
private theorem ankeny_exists_small_lattice_point {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (b : ℤ) :
    ∃ R X T : ℤ, ¬ (R = 0 ∧ X = 0 ∧ T = 0) ∧ (m : ℤ) ∣ R - X ∧ (k : ℤ) ∣ X - b * T ∧
      (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 < 2 * (m : ℤ) * (k : ℤ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![Real.sqrt (k : ℝ) * (m : ℝ), Real.sqrt (k : ℝ) * (k : ℝ),
        Real.sqrt (k : ℝ) * ((b : ℤ) : ℝ);
       0, (k : ℝ), ((b : ℤ) : ℝ);
       0, 0, Real.sqrt (m : ℝ)] with hM
  set r : ℝ := Real.sqrt (2 * (m : ℝ) * (k : ℝ)) with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    exact Real.sqrt_pos.mpr (by positivity)
  have hdetM : M.det
      = Real.sqrt (k : ℝ) * (m : ℝ) * ((k : ℝ) * Real.sqrt (m : ℝ)) := by
    rw [Matrix.det_fin_three, hM]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hsk : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hdetpos : 0 < M.det := by
    rw [hdetM]
    positivity
  have hdet : M.det ≠ 0 := ne_of_gt hdetpos
  have hsq : Real.sqrt (k : ℝ) * Real.sqrt (m : ℝ)
      = Real.sqrt ((m : ℝ) * (k : ℝ)) := by
    rw [mul_comm ((m : ℝ)) ((k : ℝ))]
    exact (Real.sqrt_mul hkR.le _).symm
  have hsq2 : Real.sqrt (2 * (m : ℝ) * (k : ℝ))
      = Real.sqrt 2 * Real.sqrt ((m : ℝ) * (k : ℝ)) := by
    rw [show 2 * (m : ℝ) * (k : ℝ) = 2 * ((m : ℝ) * (k : ℝ)) by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  have ht1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]
    norm_num
  have h8 : (8 : ℝ) < Real.pi * 4 / 3 * 2 * Real.sqrt 2 := by
    have hpi := Real.pi_gt_three
    have h3 : (3 : ℝ) < Real.pi * Real.sqrt 2 := by
      nlinarith [hpi, ht1, Real.pi_pos,
        Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hr2 : r ^ 2 = 2 * (m : ℝ) * (k : ℝ) := by
    rw [hr_def]
    exact Real.sq_sqrt (by positivity)
  have hvol : 8 * |M.det| < (Real.pi * 4 / 3) * r ^ 3 := by
    have e1 : |M.det|
        = (m : ℝ) * (k : ℝ) * Real.sqrt ((m : ℝ) * (k : ℝ)) := by
      have e1' : Real.sqrt (k : ℝ) * (m : ℝ) * ((k : ℝ) * Real.sqrt (m : ℝ))
          = (m : ℝ) * (k : ℝ) * (Real.sqrt (k : ℝ) * Real.sqrt (m : ℝ)) := by ring
      rw [abs_of_pos hdetpos, hdetM, e1', hsq]
    have e2 : r ^ 3
        = 2 * ((m : ℝ) * (k : ℝ))
          * (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (k : ℝ))) := by
      have er3 : r ^ 3 = r ^ 2 * r := by ring
      rw [er3, hr2, hr_def, hsq2]
      ring
    have hP : (0 : ℝ) < (m : ℝ) * (k : ℝ) * Real.sqrt ((m : ℝ) * (k : ℝ)) := by
      positivity
    have hmain := mul_lt_mul_of_pos_left h8 hP
    rw [e1, e2]
    linear_combination hmain
  obtain ⟨u, hu0, hult⟩ := exists_int_ne_zero_sum_sq_mulVec_lt M hdet r hr_pos hvol
  set T : ℤ := u 2 with hT
  set X : ℤ := (k : ℤ) * u 1 + b * u 2 with hX
  set R : ℤ := (m : ℤ) * u 0 + X with hR
  have e0 : (M.mulVec (fun i => ((u i : ℤ) : ℝ))) 0
      = Real.sqrt (k : ℝ) * ((R : ℤ) : ℝ) := by
    rw [hR, hX]
    push_cast
    rw [hM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  have e1 : (M.mulVec (fun i => ((u i : ℤ) : ℝ))) 1 = ((X : ℤ) : ℝ) := by
    rw [hX]
    push_cast
    rw [hM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  have e2 : (M.mulVec (fun i => ((u i : ℤ) : ℝ))) 2
      = Real.sqrt (m : ℝ) * ((T : ℤ) : ℝ) := by
    rw [hT, hM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hksq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hkR.le
  have hmsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  rw [Fin.sum_univ_three, e0, e1, e2, mul_pow, mul_pow, hksq, hmsq, hr2] at hult
  have hint : (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2
      < 2 * (m : ℤ) * (k : ℤ) := by
    exact_mod_cast hult
  have hdivR : (m : ℤ) ∣ R - X := ⟨u 0, by rw [hR]; ring⟩
  have hdivX : (k : ℤ) ∣ X - b * T := ⟨u 1, by rw [hX, hT]; ring⟩
  have hne : ¬ (R = 0 ∧ X = 0 ∧ T = 0) := by
    rintro ⟨hR0, hX0, hT0⟩
    apply hu0
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have hu2 : u 2 = 0 := by
      rw [hT] at hT0
      exact hT0
    have hu1 : u 1 = 0 := by
      have hX' : (k : ℤ) * u 1 + b * u 2 = 0 := by
        rw [← hX]
        exact hX0
      rw [hu2, mul_zero, add_zero] at hX'
      exact eq_zero_of_ne_zero_of_mul_left_eq_zero hk0 hX'
    have hu0' : u 0 = 0 := by
      have hR' : (m : ℤ) * u 0 + X = 0 := by
        rw [← hR]
        exact hR0
      rw [hX0, add_zero] at hR'
      exact eq_zero_of_ne_zero_of_mul_left_eq_zero hm0 hR'
    funext i
    fin_cases i
    · simpa using hu0'
    · simpa using hu1
    · simpa using hu2
  exact ⟨R, X, T, hne, hdivR, hdivX, hint⟩

/-- Three-square assembly: from the auxiliary modulus (`m ∣ k + 1`,
`k ∣ b ^ 2 + m`, no prime factor of `k` is `3 mod 4`), the small lattice value
`m * k` yields `m` as a sum of three natural squares. -/
private theorem ankeny_exists_three_sq_of_aux {m k : ℕ} (hm : Squarefree m)
    (hk : 0 < k) (hmk : m ∣ k + 1) {b : ℤ} (hb : (k : ℤ) ∣ b ^ 2 + (m : ℤ))
    (hk4 : ∀ p : ℕ, p.Prime → p ∣ k → p % 4 ≠ 3) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  obtain ⟨R, X, T, hne, hRX, hXT, hlt⟩ :=
    ankeny_exists_small_lattice_point hmpos hk b
  have hval := ankeny_lattice_value_eq hmpos hk hmk hb hne hRX hXT hlt
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hmpos
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hRle : R ^ 2 ≤ (m : ℤ) := by
    have h1 : (k : ℤ) * R ^ 2 ≤ (k : ℤ) * (m : ℤ) := by
      have hnn : (0 : ℤ) ≤ X ^ 2 + (m : ℤ) * T ^ 2 := by positivity
      linarith
    exact le_of_mul_le_mul_left h1 hkZ
  have hsq : ((((R.natAbs ^ 2 : ℕ))) : ℤ) = R ^ 2 := by
    exact_mod_cast Int.natAbs_sq R
  have hRnat : R.natAbs ^ 2 ≤ m := by
    have h2 : (((R.natAbs ^ 2 : ℕ)) : ℤ) ≤ ((m : ℕ) : ℤ) := by
      rw [hsq]
      exact hRle
    exact_mod_cast h2
  set N : ℕ := m - R.natAbs ^ 2 with hN
  have hNadd : R.natAbs ^ 2 + N = m := Nat.add_sub_cancel' hRnat
  have hRm : (m : ℤ) = R ^ 2 + (N : ℤ) := by
    have h2 : (N : ℤ) = (m : ℤ) - R ^ 2 := by
      rw [hN, Nat.cast_sub hRnat, hsq]
    linarith
  have hrep : (k : ℤ) * (N : ℤ) = X ^ 2 + (m : ℤ) * T ^ 2 := by
    linear_combination -hval - (k : ℤ) * hRm
  obtain ⟨a, c, hac⟩ := ankeny_exists_two_sq_of_rep hm hk hmk hk4 hRm hrep
  exact ⟨R.natAbs, a, c, by omega⟩

/-- Auxiliary modulus (Dirichlet plus reciprocity): for `m` with
`m % 8 ∈ {1, 2, 3, 5, 6}` there are `k > 0` and `b` with `m ∣ k + 1`,
`k ∣ b ^ 2 + m`, and no prime factor of `k` is `3 mod 4`. -/
private theorem ankeny_exists_aux_modulus {m : ℕ} (hm : 0 < m)
    (hmod : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : ℤ, m ∣ k + 1 ∧ (k : ℤ) ∣ b ^ 2 + (m : ℤ)
      ∧ ∀ p : ℕ, p.Prime → p ∣ k → p % 4 ≠ 3 := by
  have hcase : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 8 = 3 := by omega
  rcases hcase with h4 | h4 | h8
  · -- Case `m % 4 = 1`: `a = 2 * m - 1`, `k = q`.
    have hm1 : 1 ≤ m := by omega
    have hodd : Odd (2 * m - 1) := Nat.odd_iff.mpr (by omega)
    have hcopm : Nat.Coprime (2 * m - 1) m := by
      have haZ : (((2 * m - 1 : ℕ)) : ℤ) = 2 * (m : ℤ) - 1 := by omega
      have hbez : IsCoprime (((2 * m - 1 : ℕ)) : ℤ) (((m : ℕ)) : ℤ) := ⟨-1, 2, by omega⟩
      have h := Int.isCoprime_iff_nat_coprime.mp hbez
      simpa using h
    have hcop := ankeny_coprime_aux hodd hcopm
    obtain ⟨q, hqprime, hqgt, hqm_eq⟩ := ankeny_dirichlet_prime hm hcop
    have ha4 : (2 * m - 1) % 4 = 1 := by omega
    have ha_lt : 2 * m - 1 < 4 * m := by omega
    rw [Nat.mod_eq_of_lt ha_lt] at hqm_eq
    have hq4 : q % 4 = 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have hq : q = (2 * m - 1) + 4 * (m * (q / (4 * m))) := by
        linear_combination -hdiv
      rw [hq, Nat.add_mul_mod_self_left, ha4]
    have hdivm : m ∣ q + 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      refine ⟨4 * (q / (4 * m)) + 2, ?_⟩
      calc q + 1 = (4 * m * (q / (4 * m)) + (2 * m - 1)) + 1 := by omega
        _ = 4 * m * (q / (4 * m)) + 2 * m := by
          rw [add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ 2 * m)]
        _ = m * (4 * (q / (4 * m)) + 2) := by ring
    have : Fact q.Prime := ⟨hqprime⟩
    have : NeZero q := ⟨hqprime.ne_zero⟩
    obtain ⟨hsq, hne⟩ := isSquare_neg_of_one_mod_four_case hq4 h4 hdivm
    obtain ⟨b₀, hb0⟩ := ankeny_sq_root_mod hsq
    refine ⟨q, hqprime.pos, b₀, hdivm, hb0, ?_⟩
    intro p hpprime hpk
    have h2 := hpprime.two_le
    rcases (Nat.dvd_prime hqprime).mp hpk with h | h
    · omega
    · rw [h]
      omega
  · -- Case `m % 4 = 2`: `a = m - 1`, `k = q`.
    have hm2 : 2 ≤ m := by omega
    have hodd : Odd (m - 1) := Nat.odd_iff.mpr (by omega)
    have hcopm : Nat.Coprime (m - 1) m := by
      have haZ : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := by omega
      have hbez : IsCoprime (((m - 1 : ℕ)) : ℤ) (((m : ℕ)) : ℤ) := ⟨-1, 1, by omega⟩
      have h := Int.isCoprime_iff_nat_coprime.mp hbez
      simpa using h
    have hcop := ankeny_coprime_aux hodd hcopm
    obtain ⟨q, hqprime, hqgt, hqm_eq⟩ := ankeny_dirichlet_prime hm hcop
    have ha4 : (m - 1) % 4 = 1 := by omega
    have ha_lt : m - 1 < 4 * m := by omega
    rw [Nat.mod_eq_of_lt ha_lt] at hqm_eq
    have hq4 : q % 4 = 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have hq : q = (m - 1) + 4 * (m * (q / (4 * m))) := by
        linear_combination -hdiv
      rw [hq, Nat.add_mul_mod_self_left, ha4]
    have hdivm : m ∣ q + 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      refine ⟨4 * (q / (4 * m)) + 1, ?_⟩
      calc q + 1 = (4 * m * (q / (4 * m)) + (m - 1)) + 1 := by omega
        _ = 4 * m * (q / (4 * m)) + m := by
          rw [add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ m)]
        _ = m * (4 * (q / (4 * m)) + 1) := by ring
    have hq8 : q % 8 = (m - 1) % 8 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have e8 : 8 * ((m / 2) * (q / (4 * m))) = 4 * (m * (q / (4 * m))) := by
        have hm2eq : m = 2 * (m / 2) := by omega
        calc 8 * ((m / 2) * (q / (4 * m)))
            = 4 * ((2 * (m / 2)) * (q / (4 * m))) := by ring
          _ = 4 * (m * (q / (4 * m))) := by rw [← hm2eq]
      have hq : q = (m - 1) + 8 * ((m / 2) * (q / (4 * m))) := by
        linear_combination -hdiv - e8
      rw [hq, Nat.add_mul_mod_self_left]
    have : Fact q.Prime := ⟨hqprime⟩
    have : NeZero q := ⟨hqprime.ne_zero⟩
    obtain ⟨hq4', hsq, hne⟩ := isSquare_neg_of_two_mod_four_case h4 hdivm hq8
    obtain ⟨b₀, hb0⟩ := ankeny_sq_root_mod hsq
    refine ⟨q, hqprime.pos, b₀, hdivm, hb0, ?_⟩
    intro p hpprime hpk
    have h2 := hpprime.two_le
    rcases (Nat.dvd_prime hqprime).mp hpk with h | h
    · omega
    · rw [h]
      omega
  · -- Case `m % 8 = 3`: `a = (m - 1) / 2`, `k = 2 * q`.
    have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
    have hodd : Odd ((m - 1) / 2) := Nat.odd_iff.mpr (by omega)
    have hcopm : Nat.Coprime ((m - 1) / 2) m := by
      have haZ : 2 * ((((m - 1) / 2 : ℕ)) : ℤ) = (m : ℤ) - 1 := by omega
      have hbez : IsCoprime ((((m - 1) / 2 : ℕ)) : ℤ) (((m : ℕ)) : ℤ) := ⟨-2, 1, by omega⟩
      have h := Int.isCoprime_iff_nat_coprime.mp hbez
      simpa only [Int.natAbs_natCast] using h
    have hcop := ankeny_coprime_aux hodd hcopm
    obtain ⟨q, hqprime, hqgt, hqm_eq⟩ := ankeny_dirichlet_prime hm hcop
    have ha4 : ((m - 1) / 2) % 4 = 1 := by omega
    have ha_lt : (m - 1) / 2 < 4 * m := by omega
    rw [Nat.mod_eq_of_lt ha_lt] at hqm_eq
    have hq4 : q % 4 = 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have hq : q = ((m - 1) / 2) + 4 * (m * (q / (4 * m))) := by
        linear_combination -hdiv
      rw [hq, Nat.add_mul_mod_self_left, ha4]
    have hdivm : m ∣ 2 * q + 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have e : 2 * ((m - 1) / 2) + 1 = m := by omega
      refine ⟨8 * (q / (4 * m)) + 1, ?_⟩
      calc 2 * q + 1 = 2 * (4 * m * (q / (4 * m)) + (m - 1) / 2) + 1 := by
            omega
        _ = 8 * m * (q / (4 * m)) + (2 * ((m - 1) / 2) + 1) := by ring
        _ = 8 * m * (q / (4 * m)) + m := by rw [e]
        _ = m * (8 * (q / (4 * m)) + 1) := by ring
    have : Fact q.Prime := ⟨hqprime⟩
    have : NeZero q := ⟨hqprime.ne_zero⟩
    obtain ⟨hsq, hne⟩ := isSquare_neg_of_three_mod_eight_case hq4 h8 hdivm
    obtain ⟨b₀, hb0⟩ := ankeny_sq_root_mod hsq
    have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
    obtain ⟨tq, htq⟩ := hqodd
    have hqoddZ : Odd (((q : ℕ)) : ℤ) := ⟨(tq : ℤ), by exact_mod_cast htq⟩
    obtain ⟨tm, htm⟩ := hmodd
    have hmoddZ : Odd (((m : ℕ)) : ℤ) := ⟨(tm : ℤ), by exact_mod_cast htm⟩
    have hqpos : 0 < q := hqprime.pos
    have hcop2q : IsCoprime (((2 : ℕ)) : ℤ) (((q : ℕ)) : ℤ) := ⟨-tq, 1, by omega⟩
    have hdivs : ∀ p : ℕ, p.Prime → p ∣ 2 * q → p % 4 ≠ 3 := by
      intro p hpprime hpk
      have h2 := hpprime.two_le
      rcases (Nat.Prime.dvd_mul hpprime).mp hpk with h | h
      · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2'
        · omega
        · rw [h2']
          decide
      · rcases (Nat.dvd_prime hqprime).mp h with h1 | h2'
        · omega
        · rw [h2']
          omega
    by_cases hbodd : Odd b₀
    · have h2dvd : (2 : ℤ) ∣ b₀ ^ 2 + (m : ℤ) := by
        have hsq_odd : Odd (b₀ ^ 2) := by
          rw [pow_two]
          exact hbodd.mul hbodd
        have heven2 : Even (b₀ ^ 2 + (m : ℤ)) := hsq_odd.add_odd hmoddZ
        obtain ⟨r, hr⟩ := heven2
        exact ⟨r, by omega⟩
      have h2q : (((2 * q : ℕ)) : ℤ) ∣ b₀ ^ 2 + (m : ℤ) := by
        have h := hcop2q.mul_dvd h2dvd hb0
        have e : (((2 * q : ℕ)) : ℤ) = ((2 : ℕ) : ℤ) * (((q : ℕ)) : ℤ) := by simp
        rw [e]
        exact h
      exact ⟨2 * q, mul_pos (by norm_num) hqprime.pos, b₀, hdivm, h2q, hdivs⟩
    · have heven : Even b₀ := Int.not_odd_iff_even.mp hbodd
      have hbodd' : Odd (b₀ + ((q : ℕ) : ℤ)) := heven.add_odd hqoddZ
      have hqb : (q : ℤ) ∣ (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ) := by
        have e : (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ)
            = (b₀ ^ 2 + (m : ℤ)) + (q : ℤ) * (2 * b₀ + (q : ℤ)) := by ring
        rw [e]
        exact dvd_add hb0 (dvd_mul_right _ _)
      have h2dvd : (2 : ℤ) ∣ (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ) := by
        have hsq_odd : Odd ((b₀ + ((q : ℕ) : ℤ)) ^ 2) := by
          rw [pow_two]
          exact hbodd'.mul hbodd'
        have heven2 : Even ((b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ)) :=
          hsq_odd.add_odd hmoddZ
        obtain ⟨r, hr⟩ := heven2
        exact ⟨r, by omega⟩
      have h2q : (((2 * q : ℕ)) : ℤ) ∣ (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ) := by
        have h := hcop2q.mul_dvd h2dvd hqb
        have e : (((2 * q : ℕ)) : ℤ) = ((2 : ℕ) : ℤ) * (((q : ℕ)) : ℤ) := by simp
        rw [e]
        exact h
      exact ⟨2 * q, mul_pos (by norm_num) hqprime.pos, b₀ + ((q : ℕ) : ℤ), hdivm, h2q, hdivs⟩

/-- Squarefree case: every squarefree `m` with `m % 8 ≠ 7` is a sum of three
natural squares. -/
private theorem exists_three_sq_of_squarefree_of_mod_eight_ne_seven {m : ℕ}
    (hm : Squarefree m) (h7 : m % 8 ≠ 7) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  have h4 : ¬ 4 ∣ m := by
    intro hdvd
    have h22 : 2 * 2 ∣ m := by
      have h44 : (4 : ℕ) = 2 * 2 := rfl
      rwa [h44] at hdvd
    exact (Nat.squarefree_iff_prime_squarefree.mp hm) 2 Nat.prime_two h22
  have hmod : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6 := by
    have h8 : m % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have h0 : m % 8 ≠ 0 := by
      intro h0
      apply h4
      have hdvd8 : 8 ∣ m := Nat.dvd_of_mod_eq_zero h0
      omega
    have h44 : m % 8 ≠ 4 := by
      intro h44
      apply h4
      have hdiv := Nat.div_add_mod m 8
      omega
    omega
  obtain ⟨k, hk, b, hmk, hb, hk4⟩ := ankeny_exists_aux_modulus hmpos hmod
  exact ankeny_exists_three_sq_of_aux hm hk hmk hb hk4

/-- An odd natural is `1`, `3`, `5`, or `7` mod `8`. -/
private theorem odd_mod_eight {c : ℕ} (h : Odd c) :
    c % 8 = 1 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 7 := by
  obtain ⟨t, ht⟩ := h
  omega

/-- Legendre's three-square theorem: a natural number `n` is a sum of three
    squares provided it is not of the form `4 ^ a * (8 * b + 7)`.
    Source: Soufiane Mezroui, Abdelmalek Azizi, and M'hammed Ziane,
    "On a Conjecture of Farhi", Journal of Integer Sequences 17 (2014),
    source TeX lines 122-127,
    https://cs.uwaterloo.ca/journals/JIS/VOL17/Mezroui/soufiane4.tex
    (full source SHA-256
    `e3121b115a35156b3aae46f175bfb165ab45588165b59569ce5d9061c52c104f`,
    normalized theorem-span SHA-256
    `fd5d4315a995eda1995848786e22b3563ea1dd2080f3a1598e907d36082a6180`).

    Proves `Wanted` entry `exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven`. -/
theorem exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven
    (n : Nat)
    (h : ¬ ∃ a b : Nat, n = 4 ^ a * (8 * b + 7)) :
    ∃ x y z : Nat, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, by simp⟩
  obtain ⟨e, n', hn4, hn_eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 4 (by norm_num)
  have hn'pos : 0 < n' := Nat.pos_of_ne_zero fun h0 => hn.ne' (by rw [hn_eq, h0, mul_zero])
  obtain ⟨m, c, hmpos, hc, hcm, hmsq⟩ := Nat.sq_mul_squarefree_of_pos hn'pos
  have hcodd : Odd c := by
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    obtain ⟨t, ht⟩ := hcon
    apply hn4
    have h4c : 4 ∣ c ^ 2 := ⟨t * t, by rw [ht]; ring⟩
    have hc2n : c ^ 2 ∣ n' := ⟨m, hcm.symm⟩
    exact dvd_trans h4c hc2n
  have hc2 : c ^ 2 % 8 = 1 := by
    have hodd8 := odd_mod_eight hcodd
    rw [Nat.pow_mod]
    rcases hodd8 with h | h | h | h <;> rw [h]
  have hnm : n' % 8 = m % 8 := by
    have e : (c ^ 2 * m) % 8 = m % 8 := by
      rw [Nat.mul_mod, hc2, Nat.one_mul]
      omega
    rwa [hcm] at e
  have hm7 : m % 8 ≠ 7 := by
    intro hm7
    apply h
    have hnm7 : n' % 8 = 7 := hnm.trans hm7
    have hn'' : n' = 8 * (n' / 8) + 7 := by omega
    refine ⟨e, n' / 8, ?_⟩
    rw [hn_eq, ← hn'']
  obtain ⟨x, y, z, hxyz⟩ :=
    exists_three_sq_of_squarefree_of_mod_eight_ne_seven hmsq hm7
  have h4e : (4 : ℕ) ^ e = (2 ^ e) ^ 2 := by
    have g1 : (4 : ℕ) ^ e = 2 ^ (2 * e) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have g2 : (2 ^ e) ^ 2 = 2 ^ (e * 2) := by
      rw [← pow_mul]
    rw [g1, g2, mul_comm e 2]
  have hfin : (2 ^ e * c * x) ^ 2 + (2 ^ e * c * y) ^ 2 + (2 ^ e * c * z) ^ 2
      = 4 ^ e * n' := by
    rw [← hcm, ← hxyz, h4e]
    ring
  refine ⟨2 ^ e * c * x, 2 ^ e * c * y, 2 ^ e * c * z, ?_⟩
  rw [hn_eq]
  exact hfin

end Nat

namespace OMA.R_Erdos338_erdos_338_variants_triangular_R2
open Erdos338 Finset Filter

lemma odd_square {u : ℕ} (hu : u % 2 = 1) :
    8*(u/2 * (u/2+1) / 2)+1 = u^2 := by
  have ht := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one (u/2))
  have h : u = 2*(u/2)+1 := by omega
  calc 8 * (u/2 * (u/2+1) / 2) + 1 = (2*(u/2)+1)^2 := by nlinarith
    _ = u^2 := by rw [← h]

lemma odd_coords {a b c m : ℕ} (he : a^2+b^2+c^2=8*m+3) :
    a%2=1 ∧ b%2=1 ∧ c%2=1 := by
  have hr : ((a%8)^2 + (b%8)^2 + (c%8)^2) % 8 = 3 := by
    calc
      _ = (a^2+b^2+c^2)%8 := by
        have ha : a % 8 ≡ a [MOD 8] := Nat.mod_modEq _ _
        have hb : b % 8 ≡ b [MOD 8] := Nat.mod_modEq _ _
        have hc : c % 8 ≡ c [MOD 8] := Nat.mod_modEq _ _
        exact ((ha.pow 2).add (hb.pow 2)).add (hc.pow 2)
      _ = 3 := by rw [he]; omega
  have check : ∀ x y z : Fin 8, (x.val^2+y.val^2+z.val^2)%8=3 →
      x.val%2=1 ∧ y.val%2=1 ∧ z.val%2=1 := by decide
  have hh := check ⟨a%8, Nat.mod_lt _ (by decide)⟩
    ⟨b%8, Nat.mod_lt _ (by decide)⟩ ⟨c%8, Nat.mod_lt _ (by decide)⟩ hr
  dsimp at hh
  omega


lemma square_rep (n : ℕ) (hn : n%8=3) : ∃ a b c : ℕ, a^2+b^2+c^2=n := by
  apply Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven
  rintro ⟨t,b,rfl⟩
  cases t with
  | zero => simp at hn
  | succ t =>
    rw [pow_succ] at hn
    have hh : 4^t*4*(8*b+7) = 4*(4^t*(8*b+7)) := by ring
    rw [hh] at hn
    omega

lemma ordinary_three : HasOrder (Set.range fun k : ℕ => k*(k+1)/2) 3 := by
  apply Filter.Eventually.of_forall
  intro m
  obtain ⟨a,b,c,he⟩ := square_rep (8*m+3) (by omega)
  obtain ⟨ha,hb,hc⟩ := odd_coords he
  let T (x : ℕ) := x*(x+1)/2
  refine ⟨({T (a/2),T (b/2),T (c/2)} : Multiset ℕ),?_,by simp,?_⟩
  · intro x hx
    simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> exact ⟨_,rfl⟩
  · simp only [Multiset.insert_eq_cons,Multiset.sum_cons,Multiset.sum_singleton]
    dsimp [T]
    have ea := odd_square ha
    have eb := odd_square hb
    have ec := odd_square hc
    omega

lemma no_two : ¬ HasOrder (Set.range fun k : ℕ => k*(k+1)/2) 2 := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  obtain ⟨S, hS, hc, hs⟩ := hN (9 * N + 5) (by omega)
  have t : ∀ x ∈ S, x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 3 ∨ x % 9 = 6 := by
    intro x hx
    obtain ⟨k, rfl⟩ := hS x hx
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 18 ∧ k = 18 * q + r := ⟨k / 18, k % 18, by omega, by omega⟩
    dsimp only
    rw [show (18 * q + r) * (18 * q + r + 1) = r * (r + 1) + 2 * (9 * (18 * q * q + q * (2 * r + 1))) by ring,
      Nat.add_mul_div_left _ _ two_pos, Nat.add_mul_mod_self_left]
    interval_cases r <;> simp
  obtain h | h | h : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  · simp_all
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 h
    have := t a (by simp)
    simp at hs
    omega
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 h
    have := t a (by simp)
    have := t b (by simp)
    simp at hs
    omega

lemma hasOrder_of_hasRestrictedOrder {A : Set ℕ} {t : ℕ} (h : HasRestrictedOrder A t) :
    HasOrder A t := by
  unfold HasRestrictedOrder HasOrder at *
  filter_upwards [h] with m ⟨S, hS, hc, hs⟩
  exact ⟨S.val, hS, hc, by rw [← hs, Finset.sum_eq_multiset_sum, Multiset.map_id']⟩

lemma hasOrder_mono {A : Set ℕ} {h h' : ℕ} (H : HasOrder A h) (hh : h ≤ h') :
    HasOrder A h' := by
  unfold HasOrder at *
  filter_upwards [H] with m ⟨S, hS, hc, hs⟩
  exact ⟨S, hS, hc.trans hh, hs⟩


theorem ordinary_order : basisOrder (Set.range fun k : ℕ => k*(k+1)/2) = 3 := by
  unfold basisOrder
  apply le_antisymm (iInf₂_le 3 ordinary_three)
  refine le_iInf₂ fun k hk => ?_
  by_contra h
  have h' : (k : ℕ∞) < 3 := lt_of_not_ge h
  have h'' : k < 3 := by exact_mod_cast h'
  exact no_two (hasOrder_mono hk (by omega))

lemma distinct_witness {m a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : a^2+b^2+c^2=8*m+3) :
    ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ Set.range fun k : ℕ => k*(k+1)/2) ∧
      S.card ≤ 3 ∧ ∑ x ∈ S, x = m := by
  obtain ⟨ha,hb,hc⟩ := odd_coords he
  have ea := odd_square ha
  have eb := odd_square hb
  have ec := odd_square hc
  let tri (j : ℕ) := j*(j+1)/2
  have ne {x y : ℕ} (hx : x%2=1) (hy : y%2=1) (hxy : x ≠ y) :
      tri (x/2) ≠ tri (y/2) := by
    intro h
    have ex : 8*tri (x/2)+1 = x^2 := odd_square hx
    have ey : 8*tri (y/2)+1 = y^2 := odd_square hy
    have eq : x^2 = y^2 := by rw [← ex, ← ey, h]
    exact hxy (Nat.pow_left_injective (by decide : 2 ≠ 0) eq)
  have nab := ne ha hb hab
  have nac := ne ha hc hac
  have nbc := ne hb hc hbc
  refine ⟨{tri (a/2), tri (b/2), tri (c/2)}, ?_, ?_, ?_⟩
  · intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · simp [nab,nac,nbc]
  · simp [nab,nac,nbc]
    dsimp [tri]
    omega

/-- Reflection of a vector with coordinates a, a, 3v gives absolute coordinates
a+2v, |a-2v|, v. Only two ratios can make the new coordinates coincide. -/
lemma reflect_three {a v : ℕ} (ha : 0<a) (hv : 0<v) (h1 : a ≠ v) (h3 : a ≠ 3*v) :
    ∃ x y z : ℕ, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x^2+y^2+z^2=2*a^2+(3*v)^2 := by
  by_cases h : 2*v ≤ a
  · refine ⟨a+2*v,a-2*v,v,by omega,by omega,by omega,?_⟩
    zify [h]
    ring
  · have h' : a ≤ 2*v := by omega
    refine ⟨a+2*v,2*v-a,v,by omega,by omega,by omega,?_⟩
    zify [h']
    ring

lemma distinct_of_no_binary {s : ℕ} (hm : s%8=3)
    (h : ¬ ∃ a b : ℕ, 2*a^2+b^2=s) :
    ∃ x y z : ℕ, x≠y ∧ x≠z ∧ y≠z ∧ x^2+y^2+z^2=s := by
  obtain ⟨a,b,c,e⟩ := square_rep s hm
  refine ⟨a,b,c,?_,?_,?_,e⟩
  · rintro rfl; exact h ⟨a,c,by linarith⟩
  · rintro rfl; exact h ⟨a,b,by linarith⟩
  · rintro rfl; exact h ⟨b,a,by linarith⟩

/-- Squarefree integers congruent to 11 modulo 24 and greater than 11
already admit three distinct squares. -/
theorem squarefree_eleven {s : ℕ} (hs : Squarefree s) (h8 : s%8=3)
    (hmod : s%3=2) (large : 11<s) :
    ∃ x y z : ℕ, x≠y ∧ x≠z ∧ y≠z ∧ x^2+y^2+z^2=s := by
  by_cases hb : ∃ a b : ℕ, 2*a^2+b^2=s
  · obtain ⟨a,b,e⟩ := hb
    have tab : ∀ a b : Fin 3, (2*a.val^2+b.val^2)%3=2 → b.val=0 ∧ a.val≠0 := by decide
    have em : (2*(a%3)^2+(b%3)^2)%3=2 := by
      have am : a%3 ≡ a [MOD 3] := Nat.mod_modEq _ _
      have bm : b%3 ≡ b [MOD 3] := Nat.mod_modEq _ _
      calc
        _ = (2*a^2+b^2)%3 := ((Nat.ModEq.refl 2 |>.mul (am.pow 2)).add (bm.pow 2))
        _ = 2 := by rwa [e]
    obtain ⟨hb0,ha0⟩ := tab ⟨_,Nat.mod_lt a (by decide)⟩ ⟨_,Nat.mod_lt b (by decide)⟩ em
    change b%3=0 at hb0
    change a%3≠0 at ha0
    let v := b/3
    have eb : b=3*v := by dsimp [v]; omega
    have he : a^2+a^2+b^2=8*(s/8)+3 := by omega
    have oddb := (odd_coords he).2.2
    have hv : 0<v := by omega
    have han : 0<a := by omega
    have ne : a≠v := by
      intro hav
      have ex : s=v*v*11 := by rw [←e,eb,hav]; ring
      have unit := hs v (show v*v ∣ s from ⟨11,ex⟩)
      have ev : v=1 := Nat.isUnit_iff.mp unit
      simp [ev] at ex
      omega
    obtain ⟨x,y,z,d1,d2,d3,ee⟩ := reflect_three han hv ne (by omega)
    exact ⟨x,y,z,d1,d2,d3,ee.trans (by rwa [←eb])⟩
  · exact distinct_of_no_binary h8 hb

/-- In a squarefree binary representation, an integral ratio of the two
coordinates forces the smaller coordinate to be one. -/
private lemma large_ratios {s a b : ℕ} (sf : Squarefree s) (he : 2*a^2+b^2=s)
    (hs : 99<s) : ∀ k : ℕ, k ≤ 7 → a ≠ k*b ∧ b ≠ k*a := by
  intro k hk
  have lift {v d : ℕ} (e : s=v*v*d) : s=d := by
    have h : v=1 := Nat.isUnit_iff.mp (sf v ⟨d,e⟩)
    simpa [h] using e
  constructor
  · intro eq
    have e : s=b*b*(2*k^2+1) := by rw [←he,eq]; ring
    have := lift e
    nlinarith only [hs,this,Nat.pow_le_pow_left hk 2]
  · intro eq
    have e : s=a*a*(2+k^2) := by rw [←he,eq]; ring
    have := lift e
    nlinarith only [hs,this,Nat.pow_le_pow_left hk 2]

private lemma fifth_turn {s a b : ℕ} (sf : Squarefree s) (hs : 99<s)
    (he : 2*a^2+b^2=s) {w u v : ℤ} (sign : w=(b:ℤ) ∨ w= -(b:ℤ))
    (hu : 5*u=3*(a:ℤ)+4*w) (hv : 5*v=4*(a:ℤ)-3*w) :
    ∃ x y z : ℕ, x≠y ∧ x≠z ∧ y≠z ∧ x^2+y^2+z^2=s := by
  obtain ⟨h2,h2'⟩ := large_ratios sf he hs 2 (by decide)
  obtain ⟨h3,h3'⟩ := large_ratios sf he hs 3 (by decide)
  obtain ⟨h7,h7'⟩ := large_ratios sf he hs 7 (by decide)
  have avoid {k : ℤ} (hk : k.natAbs=a) : k=(a:ℤ) ∨ k= -(a:ℤ) :=
    Int.natAbs_eq_natAbs_iff.mp (show k.natAbs=(a:ℤ).natAbs from hk)
  refine ⟨u.natAbs,v.natAbs,a,?_,?_,?_,?_⟩
  · intro h
    have := Int.natAbs_eq_natAbs_iff.mp h
    omega
  · intro h
    have := avoid h
    omega
  · intro h
    have := avoid h
    omega
  · have ww : w^2=(b:ℤ)^2 := by rcases sign with e|e <;> rw [e] <;> ring
    have norm : u^2+v^2=(a:ℤ)^2+w^2 := by
      have h1 := congrArg (fun i : ℤ => i^2) hu
      have h2 := congrArg (fun i : ℤ => i^2) hv
      nlinarith only [h1,h2]
    zify
    rw [sq_abs,sq_abs,norm,ww,← he]
    push_cast
    ring

/-- If the squarefree binary value is a nonzero square modulo five, either
rotate the two equal coordinates, or rotate an unequal pair by the 3-4-5
orthogonal matrix. Coincidences after the rotation force s ≤ 99. -/
theorem squarefree_five {s a b : ℕ} (sf : Squarefree s) (hs : 99<s)
    (he : 2*a^2+b^2=s) (hm : s%5=1 ∨ s%5=4) :
    ∃ x y z : ℕ, x≠y ∧ x≠z ∧ y≠z ∧ x^2+y^2+z^2=s := by
  by_cases ha : a%5=0
  · let k := a/5
    have ea : a=5*k := by dsimp [k]; omega
    have hk : 0<k := by
      by_contra! h
      have az : a=0 := by omega
      have e : s=b*b := by rw [←he,az]; ring
      have hb := Nat.isUnit_iff.mp (sf b (e ▸ dvd_refl _))
      simp [hb] at e
      omega
    have small {d : ℕ} (hd : d ≤ 99) (eq : s=k*k*d) : False := by
      have ek : k=1 := Nat.isUnit_iff.mp (sf k ⟨d,eq⟩)
      simp [ek] at eq
      omega
    refine ⟨7*k,k,b,by omega,?_,?_,?_⟩
    · intro h
      exact small (d:=99) (by decide) (by rw [←he,←h,ea]; ring)
    · intro h
      exact small (d:=51) (by decide) (by rw [←he,←h,ea]; ring)
    · rw [←he,ea]; ring
  · have tab : ∀ a b : Fin 5, a.val ≠ 0 →
        ((2*a.val^2+b.val^2)%5=1 ∨ (2*a.val^2+b.val^2)%5=4) →
        (b.val=(3*a.val)%5 ∨ b.val=(2*a.val)%5) := by decide
    have er : (2*(a%5)^2+(b%5)^2)%5=s%5 := by
      rw [←he]
      have am : a%5 ≡ a [MOD 5] := Nat.mod_modEq _ _
      have bm : b%5 ≡ b [MOD 5] := Nat.mod_modEq _ _
      exact ((Nat.ModEq.refl 2 |>.mul (am.pow 2)).add (bm.pow 2))
    have h := tab ⟨_,Nat.mod_lt a (by decide)⟩ ⟨_,Nat.mod_lt b (by decide)⟩ ha (by simpa only [er] using hm)
    change b%5=(3*(a%5))%5 ∨ b%5=(2*(a%5))%5 at h
    rcases h with h|h
    · apply fifth_turn sf hs he (w:=(b:ℤ)) (u:=(3*(a:ℤ)+4*b)/5) (v:=(4*(a:ℤ)-3*b)/5) (Or.inl rfl) <;> omega
    · apply fifth_turn sf hs he (w:= -(b:ℤ)) (u:=(3*(a:ℤ)-4*b)/5) (v:=(4*(a:ℤ)+3*b)/5) (Or.inr rfl) <;> omega

private lemma binary_nonzero_mod_five {s a b : ℕ} (sf : Squarefree s) (e : 2*a^2+b^2=s) : s%5≠0 := by
  intro h
  have tab : ∀ a b : Fin 5, (2*a.val^2+b.val^2)%5=0 → a.val=0 ∧ b.val=0 := by decide
  have am : a%5 ≡ a [MOD 5] := Nat.mod_modEq _ _
  have bm : b%5 ≡ b [MOD 5] := Nat.mod_modEq _ _
  have ee : (2*(a%5)^2+(b%5)^2)%5=(2*a^2+b^2)%5 :=
    ((Nat.ModEq.refl 2 |>.mul (am.pow 2)).add (bm.pow 2))
  obtain ⟨ha,hb⟩ := tab ⟨_,Nat.mod_lt a (by decide)⟩ ⟨_,Nat.mod_lt b (by decide)⟩ (ee.trans (by rwa [e]))
  change a%5=0 at ha
  change b%5=0 at hb
  obtain ⟨u,hu⟩ := Nat.dvd_of_mod_eq_zero ha
  obtain ⟨v,hv⟩ := Nat.dvd_of_mod_eq_zero hb
  have unit := sf 5 (show 5*5 ∣ s from ⟨2*u^2+v^2,by rw [←e,hu,hv]; ring⟩)
  exact (by decide : (5:ℕ) ≠ 1) (Nat.isUnit_iff.mp unit)

private lemma residual_mod {s : ℕ} (h8 : s%8=3) (h3 : s%3≠2) (h5 : s%5=2 ∨ s%5=3) :
    s%120=3 ∨ s%120=27 ∨ s%120=43 ∨ s%120=67 := by
  have tab : ∀ u : Fin 120, u.val%8=3 → u.val%3≠2 → (u.val%5=2 ∨ u.val%5=3) →
      u.val=3 ∨ u.val=27 ∨ u.val=43 ∨ u.val=67 := by decide
  apply tab ⟨s%120,Nat.mod_lt _ (by decide)⟩
  · simpa only [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 120)] using h8
  · simpa only [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 120)] using h3
  · simpa only [Nat.mod_mod_of_dvd _ (by decide : 5 ∣ 120)] using h5

-- Only squarefree values still admitting the binary form and in the four indicated residue classes.
def H1 : Prop := ∃ K : ℕ, ∀ s : ℕ, K ≤ s → Squarefree s →
  (s%120=3 ∨ s%120=27 ∨ s%120=43 ∨ s%120=67) →
  (∃ a b : ℕ, 2*a^2+b^2=s) →
  ∃ x y z : ℕ, x≠y ∧ x≠z ∧ y≠z ∧ x^2+y^2+z^2=s

-- For any bounded squarefree part, eventually a square multiple has a distinct triple.
def H2 : Prop := ∀ K : ℕ, ∀ᶠ m : ℕ in atTop, ∀ s t : ℕ,
  s ≤ K → Squarefree s → t^2*s=8*m+3 →
  ∃ x y z : ℕ, x≠y ∧ x≠z ∧ y≠z ∧ x^2+y^2+z^2=8*m+3

theorem main : H1 → H2 → type_of% @Erdos338.erdos_338.variants.triangular := by
  rintro ⟨K,hK⟩ hsmall
  have hr : HasRestrictedOrder (Set.range fun k : ℕ => k*(k+1)/2) 3 := by
    filter_upwards [hsmall (max K 99)] with m hm
    obtain ⟨s,t,hs,ht,eq,sf⟩ := Nat.sq_mul_squarefree_of_pos (show 0<8*m+3 by omega)
    suffices ∃ x y z : ℕ, x≠y ∧ x≠z ∧ y≠z ∧ x^2+y^2+z^2=8*m+3 by
      obtain ⟨a,b,c,hab,hac,hbc,h⟩ := this
      exact distinct_witness hab hac hbc h
    by_cases small : s ≤ max K 99
    · exact hm s t small sf eq
    have hmod : s%8=3 := by
      have rt : t%8=1 ∨ t%8=3 ∨ t%8=5 ∨ t%8=7 := by
        by_contra! no
        have h : 2 ∣ t := by omega
        obtain ⟨v,ev⟩ := h
        rw [ev,show (2*v)^2*s=4*(v^2*s) by ring] at eq
        omega
      have e : (t^2*s)%8=3 := by omega
      rw [Nat.mul_mod,Nat.pow_mod] at e
      rcases rt with h|h|h|h <;> rw [h] at e <;> norm_num at e <;> omega
    have good : ∃ x y z : ℕ, x≠y ∧ x≠z ∧ y≠z ∧ x^2+y^2+z^2=s := by
      by_cases mod3 : s%3=2
      · exact squarefree_eleven sf hmod mod3 (by omega)
      by_cases bin : ∃ a b : ℕ, 2*a^2+b^2=s
      · obtain ⟨a,b,e⟩ := bin
        by_cases h5 : s%5=1 ∨ s%5=4
        · exact squarefree_five sf (by omega) e h5
        have h0 := binary_nonzero_mod_five sf e
        have small5 := Nat.mod_lt s (by decide : 0<5)
        exact hK s (by omega) sf (residual_mod hmod mod3 (by omega)) ⟨a,b,e⟩
      · exact distinct_of_no_binary hmod bin
    obtain ⟨x,y,z,xy,xz,yz,e⟩ := good
    refine ⟨t*x,t*y,t*z,?_,?_,?_,?_⟩
    · exact fun h => xy (Nat.eq_of_mul_eq_mul_left ht h)
    · exact fun h => xz (Nat.eq_of_mul_eq_mul_left ht h)
    · exact fun h => yz (Nat.eq_of_mul_eq_mul_left ht h)
    rw [←eq,←e]
    ring
  refine ⟨ordinary_order,?_⟩
  unfold restrictedOrder
  apply le_antisymm (iInf₂_le 3 hr)
  refine le_iInf₂ fun k hk => ?_
  by_contra h
  have h' : (k : ℕ∞) < 3 := lt_of_not_ge h
  have h'' : k < 3 := by exact_mod_cast h'
  exact no_two (hasOrder_mono (hasOrder_of_hasRestrictedOrder hk) (by omega))

end OMA.R_Erdos338_erdos_338_variants_triangular_R2
/-
Codebase is not intended for use to train, fine-tune, distill, evaluate, or otherwise develop ML models


                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
