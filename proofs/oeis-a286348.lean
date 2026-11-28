import OMAStatements.S_oeis_a286348
import Mathlib

-- Problem oeis-a286348: if (1 + y)^x + (-y)^x is a (positive) prime, then x = 0, or x = 2^k with k >= 1, or x is
-- an odd prime.
-- Upstream: statements/oeis-a286348.lean (declaration OMA.S_oeis_a286348.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: for y = 0 or y = -1 the value is 1 (if x > 0), and for x = 1 it is 1 as well. Otherwise the two bases are
-- v + 1 and -v for a natural v >= 1. If x is none of the three allowed shapes, then x = q * m with q an odd prime
-- and m >= 2. For even m the value is U^q + V^q with U = (v+1)^m, V = v^m, divisible by U + V with 1 < U + V < value.
-- For odd m it is U^q - V^q, divisible by U - V, and 2 <= U - V < U^q - V^q because
-- U^(n+1) - V^(n+1) >= U^n (U - V). In both cases the value has a proper divisor, so it is not prime.

private lemma pow_sub_ge_a286348 (U V n : ℕ) (hVU : V ≤ U) :
    U ^ n * (U - V) ≤ U ^ (n + 1) - V ^ (n + 1) := by
  have hv : V ^ n ≤ U ^ n := Nat.pow_le_pow_left hVU n
  have h : U ^ n * (U - V) + V ^ (n + 1) ≤ U ^ (n + 1) := by
    calc U ^ n * (U - V) + V ^ (n + 1) = U ^ n * (U - V) + V ^ n * V := by ring
      _ ≤ U ^ n * (U - V) + U ^ n * V := Nat.add_le_add_left (Nat.mul_le_mul_right V hv) _
      _ = U ^ n * (U - V + V) := by ring
      _ = U ^ (n + 1) := by rw [Nat.sub_add_cancel hVU, pow_succ]
  omega

private lemma not_prime_add_a286348 (v m q : ℕ) (hv : 1 ≤ v) (hm : 1 ≤ m) (hq : Odd q) (hq3 : 3 ≤ q) :
    ¬ ((v + 1) ^ (q * m) + v ^ (q * m)).Prime := by
  have e1 : (v + 1) ^ (q * m) = ((v + 1) ^ m) ^ q := by rw [mul_comm, pow_mul]
  have e2 : v ^ (q * m) = (v ^ m) ^ q := by rw [mul_comm, pow_mul]
  rw [e1, e2]
  have hm0 : m ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  have hU : 2 ≤ (v + 1) ^ m := by
    calc 2 ≤ v + 1 := by omega
      _ ≤ (v + 1) ^ m := Nat.le_self_pow hm0 _
  have hV : 1 ≤ v ^ m := Nat.one_le_pow _ _ hv
  have hdvd : (v + 1) ^ m + v ^ m ∣ ((v + 1) ^ m) ^ q + (v ^ m) ^ q := by
    have h := Odd.add_dvd_pow_add_pow (((v + 1) ^ m : ℕ) : ℤ) ((v ^ m : ℕ) : ℤ) hq
    exact_mod_cast h
  have hlt1 : (v + 1) ^ m < ((v + 1) ^ m) ^ q := lt_self_pow₀ (by omega) (by omega)
  have hle2 : v ^ m ≤ (v ^ m) ^ q := Nat.le_self_pow hq0 _
  exact Nat.not_prime_of_dvd_of_lt hdvd (by omega) (by omega)

private lemma not_prime_sub_a286348 (v m q : ℕ) (hv : 1 ≤ v) (hm : 2 ≤ m) (hq3 : 3 ≤ q) :
    ¬ ((v + 1) ^ (q * m) - v ^ (q * m)).Prime := by
  have e1 : (v + 1) ^ (q * m) = ((v + 1) ^ m) ^ q := by rw [mul_comm, pow_mul]
  have e2 : v ^ (q * m) = (v ^ m) ^ q := by rw [mul_comm, pow_mul]
  rw [e1, e2]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hm0 : m' ≠ 0 := by omega
  have hq0 : q' ≠ 0 := by omega
  have hVU : v ^ (m' + 1) ≤ (v + 1) ^ (m' + 1) := Nat.pow_le_pow_left (Nat.le_succ v) _
  have hd := pow_sub_ge_a286348 (v + 1) v m' (Nat.le_succ v)
  have h1 : v + 1 - v = 1 := by omega
  rw [h1, mul_one] at hd
  have hU2 : 2 ≤ (v + 1) ^ m' := by
    calc 2 ≤ v + 1 := by omega
      _ ≤ (v + 1) ^ m' := Nat.le_self_pow hm0 _
  have hN := pow_sub_ge_a286348 ((v + 1) ^ (m' + 1)) (v ^ (m' + 1)) q' hVU
  have hUq : 2 ≤ ((v + 1) ^ (m' + 1)) ^ q' := by
    calc 2 ≤ v + 1 := by omega
      _ ≤ (v + 1) ^ (m' + 1) := Nat.le_self_pow (Nat.succ_ne_zero m') _
      _ ≤ ((v + 1) ^ (m' + 1)) ^ q' := Nat.le_self_pow hq0 _
  have hdvd : (v + 1) ^ (m' + 1) - v ^ (m' + 1)
      ∣ ((v + 1) ^ (m' + 1)) ^ (q' + 1) - (v ^ (m' + 1)) ^ (q' + 1) :=
    Nat.sub_dvd_pow_sub_pow _ _ _
  have h2d : 2 * ((v + 1) ^ (m' + 1) - v ^ (m' + 1))
      ≤ ((v + 1) ^ (m' + 1)) ^ q' * ((v + 1) ^ (m' + 1) - v ^ (m' + 1)) :=
    Nat.mul_le_mul_right _ hUq
  exact Nat.not_prime_of_dvd_of_lt hdvd (by omega) (by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a286348.main := by
  intro y x hpos hprime
  by_contra hcon
  have hx0 : x ≠ 0 := fun h => hcon (Or.inl h)
  have hpow : ∀ k, 1 ≤ k → x ≠ 2 ^ k := fun k hk h => hcon (Or.inr (Or.inl ⟨k, hk, h⟩))
  have hodd : ¬ (x.Prime ∧ Odd x) := fun h => hcon (Or.inr (Or.inr h))
  by_cases hy0 : y = 0
  · subst hy0
    simp [hx0] at hprime
    exact Nat.not_prime_one hprime
  by_cases hy1 : y = -1
  · subst hy1
    simp [hx0] at hprime
    exact Nat.not_prime_one hprime
  obtain ⟨v, hv, hN⟩ : ∃ v : ℕ, 1 ≤ v ∧
      (1 + y) ^ x + (-y) ^ x = ((v : ℤ) + 1) ^ x + (-(v : ℤ)) ^ x := by
    rcases lt_or_gt_of_ne hy0 with h | h
    · refine ⟨(-y - 1).toNat, by omega, ?_⟩
      have hc : ((-y - 1).toNat : ℤ) = -y - 1 := Int.toNat_of_nonneg (by omega)
      rw [hc]
      ring
    · refine ⟨y.toNat, by omega, ?_⟩
      have hc : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
      rw [hc]
      ring
  rw [hN] at hprime
  by_cases hx1 : x = 1
  · subst hx1
    have h1 : ((v : ℤ) + 1) ^ 1 + (-(v : ℤ)) ^ 1 = 1 := by ring
    rw [h1] at hprime
    simp at hprime
    exact Nat.not_prime_one hprime
  obtain ⟨e, t, ht, hxe⟩ := Nat.exists_eq_two_pow_mul_odd hx0
  by_cases ht1 : t = 1
  · subst ht1
    rw [mul_one] at hxe
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      exact hx1 (by simpa using hxe)
    · exact hpow e he hxe
  · obtain ⟨q, hq⟩ : ∃ q, q = t.minFac := ⟨_, rfl⟩
    have hqp : q.Prime := by rw [hq]; exact Nat.minFac_prime ht1
    have hqt : q ∣ t := by rw [hq]; exact Nat.minFac_dvd t
    have hqodd : Odd q := ht.of_dvd_nat hqt
    have hq3 : 3 ≤ q := by
      have h2 := hqp.two_le
      obtain ⟨s, hs⟩ := hqodd
      omega
    have hqx : q ∣ x := by rw [hxe]; exact Dvd.dvd.mul_left hqt _
    obtain ⟨m, hm⟩ := hqx
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hx0 (by simpa using hm)
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hm
      exact hodd ⟨by rw [hm]; exact hqp, by rw [hm]; exact hqodd⟩
    subst hm
    rcases Nat.even_or_odd m with hme | hmo
    · have hxev : Even (q * m) := hme.mul_left q
      have hc : ((v : ℤ) + 1) ^ (q * m) + (-(v : ℤ)) ^ (q * m)
          = (((v + 1) ^ (q * m) + v ^ (q * m) : ℕ) : ℤ) := by
        rw [Even.neg_pow hxev]
        push_cast
        ring
      rw [hc, Int.toNat_natCast] at hprime
      exact not_prime_add_a286348 v m q hv (by omega) hqodd hq3 hprime
    · have hxod : Odd (q * m) := hqodd.mul hmo
      have hle : v ^ (q * m) ≤ (v + 1) ^ (q * m) := Nat.pow_le_pow_left (Nat.le_succ v) _
      have hc : ((v : ℤ) + 1) ^ (q * m) + (-(v : ℤ)) ^ (q * m)
          = (((v + 1) ^ (q * m) - v ^ (q * m) : ℕ) : ℤ) := by
        rw [Odd.neg_pow hxod, Nat.cast_sub hle]
        push_cast
        ring
      rw [hc, Int.toNat_natCast] at hprime
      exact not_prime_sub_a286348 v m q hv (by omega) hq3 hprime
