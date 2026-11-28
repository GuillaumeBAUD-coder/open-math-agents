import OMAStatements.S_oeis_a182207

-- Problem: A182207: Carmichael numbers of the form C = p*(2p-1)*(n*(2p-2)+p),
-- where p and 2p-1 are prime numbers.
-- Upstream: formal-conjectures statements/oeis-a182207.lean:0 (declaration OMA.S_oeis_a182207.main)
--
-- This is the general statement of the OEIS entry (OEIS only reports a check of the first 30 terms).
--
-- Proof.
-- Write q = 2p-1. Since C is Carmichael and q is an odd prime divisor of C, Korselt's
-- congruence holds at q:  q - 1 = 2p-2  divides  C - 1.  (The necessary direction of
-- Korselt's criterion follows from the definitional property because the exponent of the
-- unit group (ZMod C)ˣ is the Carmichael function λ(C), which divides C - 1:
-- every unit u satisfies u^(C-1) = 1, hence λ(C) ∣ C-1, and λ(q) = q - 1 for an odd prime q
-- because (ZMod q)ˣ is cyclic.  See `carm_dvd` and `prime_sub_dvd` below.)
--
-- Now write C = p * q * m (p and q are distinct primes, so p*q ∣ C).  Reducing
-- C - 1 ≡ 0 (mod 2p-2) and using q = (2p-2) + 1 ≡ 1 (mod 2p-2) gives
--        p * m ≡ 1  (mod 2p-2).
-- Since p is odd, p + 1 is even and
--        p * p - 1 = (p-1)(p+1) ≡ 0  (mod 2p-2),
-- so p * m ≡ p * p (mod 2p-2).  As gcd(p, 2p-2) = 1 we may cancel p, obtaining
--        m ≡ p  (mod 2p-2).
-- Writing m = (2p-2) * (m / (2p-2)) + p (which holds because m % (2p-2) = p and p < 2p-2)
-- gives the required form with n = m / (2p-2).
--
-- The case p = 2 is vacuous: then C is even while q - 1 = 2 ∣ C - 1 forces C odd.
-- (n = 0 is allowed by the pin, so m = p is covered.)
--
-- Credit: @MBimrose (the owner of the agent is credited as the solver)

open OMA.S_oeis_a182207

namespace OMA.A182207Proof

open ArithmeticFunction

/-- Korselt's congruence at any prime divisor: `λ(C) ∣ C - 1` for a Carmichael number `C`,
where `λ` is the Carmichael function (the exponent of `(ZMod C)ˣ`). -/
theorem carm_dvd (C : ℕ) (h : IsCarmichael C) : carmichael C ∣ C - 1 := by
  obtain ⟨h1, -, hb⟩ := h
  have : NeZero C := ⟨by omega⟩
  rw [carmichael_eq_exponent']
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro v
  have hc := ZMod.val_coe_unit_coprime v
  have hm := hb _ hc
  have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  push_cast at hz
  rw [ZMod.natCast_zmod_val] at hz
  ext
  push_cast
  exact hz

/-- Korselt's condition at an odd prime divisor `p` of a Carmichael number `C`: `p - 1 ∣ C - 1`. -/
theorem prime_sub_dvd (C p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpC : p ∣ C)
    (h : IsCarmichael C) : p - 1 ∣ C - 1 := by
  have h1 := carm_dvd C h
  have h2 := carmichael_dvd hpC
  have h3 := carmichael_pow_of_prime_ne_two 1 hp hp2
  rw [pow_one, Nat.totient_prime hp] at h3
  rw [← h3]
  exact h2.trans h1

/-- The main arithmetic step: for an odd prime `p` and `2p-2 ∣ p(2p-1)m - 1`, one has
`m ≡ p (mod 2p-2)`. -/
theorem key_modeq (p m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p * (2 * p - 1) * m ≡ 1 [MOD 2 * p - 2]) : m ≡ p [MOD 2 * p - 2] := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  -- (2p-1) ≡ 1 mod (2p-2)
  have hqmod : 2 * p - 1 ≡ 1 [MOD 2 * p - 2] := by
    have h0 : 2 * p - 2 ≡ 0 [MOD 2 * p - 2] := Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)
    have h1 : 2 * p - 2 + 1 = 2 * p - 1 := by omega
    rw [← h1]
    simpa using h0.add_right 1
  -- p(2p-1)m ≡ p*m
  have hmul : p * (2 * p - 1) * m ≡ p * m [MOD 2 * p - 2] := by
    have h' : p * (2 * p - 1) * m ≡ p * 1 * m [MOD 2 * p - 2] :=
      (Nat.ModEq.refl p).mul hqmod |>.mul (Nat.ModEq.refl m)
    simpa using h'
  have hpm : p * m ≡ 1 [MOD 2 * p - 2] := hmul.symm.trans h
  -- p*p ≡ 1 mod (2p-2), since p*p - 1 = (p-1)(p+1) and p + 1 is even
  have hp2mod : p * p ≡ 1 [MOD 2 * p - 2] := by
    have hodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨c, hc⟩ := hodd
    have hdiv : 2 * p - 2 ∣ p * p - 1 := by
      have hsq : p * p - 1 = (p - 1) * (p + 1) := by
        rw [mul_self_tsub_one p]
        ring
      have hc' : p + 1 = 2 * (c + 1) := by omega
      have hd : 2 * p - 2 = 2 * (p - 1) := by omega
      rw [hsq, hc', hd]
      exact ⟨c + 1, by ring⟩
    have h0 : p * p - 1 ≡ 0 [MOD 2 * p - 2] := Nat.modEq_zero_iff_dvd.mpr hdiv
    have h1 : p * p - 1 + 1 = p * p := by
      have : 1 ≤ p * p := by nlinarith [hp.two_le]
      omega
    rw [← h1]
    simpa using h0.add_right 1
  -- cancel p, which is coprime to 2p-2
  have hcop : Nat.Coprime (2 * p - 2) p := by
    have h2p : Nat.Coprime 2 p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hd
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      have hp2' := hp.two_le
      have : p = 2 := by omega
      exact hp2 this
    have hp1 : Nat.Coprime (p - 1) p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hd
      have hle : p ≤ p - 1 := Nat.le_of_dvd (by omega) hd
      omega
    have hmul' : Nat.Coprime (2 * (p - 1)) p := Nat.Coprime.mul_left h2p hp1
    have hd : 2 * (p - 1) = 2 * p - 2 := by omega
    rwa [hd] at hmul'
  exact Nat.ModEq.cancel_left_of_coprime (m := 2 * p - 2) (c := p) hcop (hpm.trans hp2mod.symm)

/-- A182207 in the form used for the main theorem. -/
theorem main_aux (C p : ℕ) (hC : IsCarmichael C) (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (hpC : p ∣ C) (hqC : 2 * p - 1 ∣ C) :
    ∃ n : ℕ, C = p * (2 * p - 1) * (n * (2 * p - 2) + p) := by
  have hqne2 : 2 * p - 1 ≠ 2 := by
    intro h
    have := hp.two_le
    omega
  -- Korselt at q = 2p-1: q - 1 = 2p-2 divides C - 1
  have hdvd : 2 * p - 2 ∣ C - 1 := by
    have h1 : 2 * p - 1 - 1 = 2 * p - 2 := by omega
    rw [← h1]
    exact prime_sub_dvd C (2 * p - 1) hq hqne2 hqC hC
  rcases eq_or_ne p 2 with hp2 | hp2
  · -- p = 2: C would be even, yet 2 ∣ C - 1
    subst hp2
    have h2 : 2 ∣ C - 1 := by simpa using hdvd
    have hsub : C - (C - 1) = 1 := by
      have := hC.1
      omega
    have h1 : 2 ∣ C - (C - 1) := Nat.dvd_sub hpC h2
    rw [hsub] at h1
    omega
  · -- p odd: p and q are distinct primes, so p*q ∣ C
    have hpq : Nat.Coprime p (2 * p - 1) := by
      rw [hp.coprime_iff_not_dvd]
      intro hd
      have h2p : p ∣ 2 * p := ⟨2, by ring⟩
      have h1 : p ∣ (2 * p) - (2 * p - 1) := Nat.dvd_sub h2p hd
      have h2 : (2 * p) - (2 * p - 1) = 1 := by
        have := hp.two_le
        omega
      rw [h2] at h1
      have := Nat.le_of_dvd (by norm_num) h1
      have := hp.two_le
      omega
    obtain ⟨m, hm⟩ : p * (2 * p - 1) ∣ C :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hpq hpC hqC
    have hCe : C ≡ 1 [MOD 2 * p - 2] := by
      have h0 : C - 1 ≡ 0 [MOD 2 * p - 2] := Nat.modEq_zero_iff_dvd.mpr hdvd
      have hC1 : 1 < C := hC.1
      have h1 : C - 1 + 1 = C := Nat.sub_add_cancel (by omega)
      rw [← h1]
      simpa using h0.add_right 1
    rw [hm] at hCe
    have hmodeq : m ≡ p [MOD 2 * p - 2] := key_modeq p m hp hp2 hCe
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    have hplt : p < 2 * p - 2 := by omega
    have hmod : m % (2 * p - 2) = p := by
      have h' : m % (2 * p - 2) = p % (2 * p - 2) := hmodeq
      rw [Nat.mod_eq_of_lt hplt] at h'
      exact h'
    have hmdec : m = (2 * p - 2) * (m / (2 * p - 2)) + p := by
      have h2 := Nat.div_add_mod m (2 * p - 2)
      rw [hmod] at h2
      omega
    refine ⟨m / (2 * p - 2), ?_⟩
    rw [hm]
    conv_lhs => rw [hmdec]
    rw [mul_comm (2 * p - 2) (m / (2 * p - 2))]

end OMA.A182207Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a182207.main := by
  intro C p hC hp hq hpC hqC
  exact OMA.A182207Proof.main_aux C p hC hp hq hpC hqC
