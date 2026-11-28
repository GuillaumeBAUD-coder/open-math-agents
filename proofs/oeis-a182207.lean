import OMAStatements.S_oeis_a182207
import Mathlib

/-!
# Proof of the OEIS A182207 conjecture

Credit: @sntntHb (proof written with Claude Code).

Sketch: first a Korselt-type step. If a prime `q` divides a Carmichael number `C`, write
`C = q ^ e * C'` with `q ∤ C'`, take a generator `g` of the cyclic group `(ZMod q)ˣ` and, by the
Chinese remainder theorem, a base `b ≡ g (mod q)`, `b ≡ 1 (mod C')`. Then `b` is coprime to `C`, so
`g ^ (C - 1) = 1` and `q - 1 = orderOf g` divides `C - 1`. With `q = 2p - 1` this gives
`2p - 2 ∣ C - 1`; in particular `p ≠ 2` (else `2 ∣ C` and `2 ∣ C - 1`). Write `p = 2s + 1` and
`C = p (2p - 1) m`. From `p ^ 2 (2p - 1) ≡ 1` and `p C ≡ p (mod 4s)` one gets the integer identity
`m = (2s + 1) + 4s N` with `N = (2s + 1) t - (4s^2 + 5s + 2) m`, where `C - 1 = 4s t`; since `m > 0`,
`N ≥ 0`, and `n = N` works.
-/

namespace OMA.A182207Proof

open OMA.S_oeis_a182207

theorem korselt_one (C q : ℕ) (hC : IsCarmichael C) (hq : q.Prime) (hqC : q ∣ C) :
    q - 1 ∣ C - 1 := by
  obtain ⟨hC1, -, hF⟩ := hC
  haveI := Fact.mk hq
  obtain ⟨e, C', hC'q, hCe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := C) (by omega) q
    hq.one_lt.ne'
  have hcop : Nat.Coprime q C' := (Nat.Prime.coprime_iff_not_dvd hq).mpr hC'q
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hord : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hq]
  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop ((g : ZMod q).val) 1
  have hbq : (b : ZMod q) = g := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hb1]
    simp
  have hbcop : b.Coprime C := by
    rw [hCe]
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]
      intro hd
      have h0 : (b : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff b q).mpr hd
      rw [hbq] at h0
      exact g.ne_zero h0
    · have h := Nat.ModEq.gcd_eq hb2
      simpa [Nat.Coprime] using h
  have h' : b ^ (C - 1) ≡ 1 [MOD q] := Nat.ModEq.of_dvd hqC (hF b hbcop)
  have h'' : (g : ZMod q) ^ (C - 1) = 1 := by
    rw [← hbq]
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h'
    simpa using this
  have hu : g ^ (C - 1) = 1 := Units.ext (by simpa using h'')
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hu

theorem main' : ∀ C p : ℕ, IsCarmichael C → p.Prime → (2 * p - 1).Prime → p ∣ C →
    2 * p - 1 ∣ C → ∃ n : ℕ, C = p * (2 * p - 1) * (n * (2 * p - 2) + p) := by
  intro C p hC hp hq hpC hqC
  have hC1 := hC.1
  have hK := korselt_one C (2 * p - 1) hC hq hqC
  have hp2 := hp.two_le
  have hpq : p ≠ 2 * p - 1 := by omega
  have hcop : Nat.Coprime p (2 * p - 1) := (Nat.coprime_primes hp hq).mpr hpq
  obtain ⟨m, hm⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpC hqC
  obtain ⟨t, ht⟩ := hK
  have hpodd : p ≠ 2 := by
    rintro rfl
    obtain ⟨u, hu⟩ := hpC
    omega
  obtain ⟨s, hs⟩ := hp.odd_of_ne_two hpodd
  subst hs
  have hs1 : 1 ≤ s := by omega
  have e1 : 2 * (2 * s + 1) - 1 = 4 * s + 1 := by omega
  have e2 : 2 * (2 * s + 1) - 2 = 4 * s := by omega
  rw [e1] at hm ht
  rw [e1, e2]
  have ht' : C = 1 + 4 * s * t := by
    rw [show 4 * s + 1 - 1 = 4 * s by omega] at ht
    omega
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hm
      omega
    · exact h
  have h1 : (C : ℤ) = (2 * s + 1) * (4 * s + 1) * m := by exact_mod_cast hm
  have h2 : (C : ℤ) = 1 + 4 * s * t := by exact_mod_cast ht'
  have key : (m : ℤ) = (2 * s + 1) + 4 * s * ((2 * s + 1) * t - (4 * s ^ 2 + 5 * s + 2) * m) := by
    linear_combination (2 * (s : ℤ) + 1) * (h2 - h1)
  set N : ℤ := (2 * s + 1) * t - (4 * s ^ 2 + 5 * s + 2) * m with hN
  have hs1' : (1 : ℤ) ≤ s := by exact_mod_cast hs1
  have hm0' : (0 : ℤ) < m := by exact_mod_cast hm0
  have hN0 : 0 ≤ N := by
    by_contra h
    have hN1 : N ≤ -1 := by omega
    nlinarith
  refine ⟨N.toNat, ?_⟩
  rw [hm]
  congr 1
  have hc : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hN0
  zify
  rw [hc]
  linarith

end OMA.A182207Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a182207.main := OMA.A182207Proof.main'
