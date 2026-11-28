import OMAStatements.S_oeis_a217853

-- Problem: A217853: Fermat pseudoprimes to base 3 of the form (3^(4*k + 2) - 1)/8.
-- Upstream: formal-conjectures statements/oeis-a217853.lean:0 (declaration OMA.S_oeis_a217853.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof (Grok Bot w3): for every prime p = 2k+1 >= 5, N = (3^(2p)-1)/8 is a Fermat pseudoprime
-- to base 3. Write 3^p = 8q+3; then N = (4q+1)(2q+1) is composite, and 3^(2p) = 8N+1 = 1 mod N.
-- By Fermat 3^p = 3 mod p, so p | 8q, p | q, and N - 1 = 2q(4q+3) is a multiple of 2p, giving
-- 3^(N-1) = 1 mod N. Infinitely many primes give infinitely many k.

namespace OMA.A217853Proof

lemma key (k : ℕ) (hk : 2 ≤ k) (hp : (2 * k + 1).Prime) :
    Nat.FermatPsp ((3 ^ (4 * k + 2) - 1) / 8) 3 := by
  set p := 2 * k + 1 with hpdef
  set x := 3 ^ p with hx
  have h3 : 3 ^ (4 * k + 2) = x ^ 2 := by
    rw [hx, ← pow_mul, show p * 2 = 4 * k + 2 by omega]
  have hx8 : x % 8 = 3 := by
    rw [hx, hpdef, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  have hxbig : 243 ≤ x := by
    rw [hx]; calc (243:ℕ) = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨q, hq⟩ : ∃ q, x = 8 * q + 3 := ⟨x / 8, by omega⟩
  have hsq : x ^ 2 - 1 = 8 * ((4 * q + 1) * (2 * q + 1)) :=
    Nat.sub_eq_of_eq_add (by rw [hq]; ring)
  have hN : (3 ^ (4 * k + 2) - 1) / 8 = (4 * q + 1) * (2 * q + 1) := by
    rw [h3, hsq, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hN]
  set N := (4 * q + 1) * (2 * q + 1) with hNdef
  have hq2 : 30 ≤ q := by omega
  -- Fermat: p ∣ x - 3 = 8 q
  have := Fact.mk hp
  have hF : ((3 ^ p : ℕ) : ZMod p) = ((3 : ℕ) : ZMod p) := by
    push_cast; exact ZMod.pow_card _
  have hmod : 3 ≡ 3 ^ p [MOD p] := ((ZMod.natCast_eq_natCast_iff _ _ _).1 hF).symm
  have hdvd : p ∣ 3 ^ p - 3 := (Nat.modEq_iff_dvd' (by omega)).1 hmod
  rw [← hx, hq, show 8 * q + 3 - 3 = 8 * q by omega] at hdvd
  have hcop : Nat.Coprime p 8 := by
    rw [show (8:ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
  have hpq : p ∣ q := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨r, hr⟩ := hpq
  have hN1 : N - 1 = (2 * p) * (r * (4 * q + 3)) := by
    rw [hNdef]
    apply Nat.sub_eq_of_eq_add
    have : q = p * r := hr
    nlinarith [this]
  have hx2 : x ^ 2 ≡ 1 [MOD N] := by
    have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : x ^ 2 = 8 * N + 1 := by rw [hNdef]; omega
    unfold Nat.ModEq; rw [this]; simp [Nat.add_mod]
  have hpow : 3 ^ (N - 1) ≡ 1 [MOD N] := by
    rw [hN1, pow_mul, show 3 ^ (2 * p) = x ^ 2 by rw [hx, ← pow_mul, mul_comm]]
    simpa using hx2.pow (r * (4 * q + 3))
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 hpow.symm
  · exact Nat.not_prime_mul (by omega) (by omega)
  · rw [hNdef]; nlinarith

theorem infin : {k : ℕ | Nat.FermatPsp ((3 ^ (4 * k + 2) - 1) / 8) 3}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (2 * B + 5)
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two (by omega))
  have hk := hB (show p / 2 ∈ _ from key (p / 2) (by omega) (by rwa [show 2 * (p / 2) + 1 = p by omega]))
  omega

end OMA.A217853Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a217853.main :=
  OMA.A217853Proof.infin
