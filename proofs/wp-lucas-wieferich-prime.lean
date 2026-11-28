import OMAStatements.S_wp_lucas_wieferich_prime

/-!
Proof of the statement as formalized. NOTE: this does not settle the open problem about
Lucas–Wieferich primes. The genuine notion requires `p ^ 2 ∣ U_{p - (D/p)}`; the formal statement
only asks for `p ∣ U_{p - (D/p)}`, which is the classical law of apparition for Lucas sequences
and holds for every odd prime not dividing `D = a ^ 2 + 4`.

Argument. For each `N` put `m = 2 * N!` and let `p` be a prime factor of `D * m ^ 2 - 1`. Then
`p ∤ m`, so `p > N` and `p` is odd, and `D ≡ (m⁻¹) ^ 2 (mod p)` is a nonzero square, so the Jacobi
symbol `(D / p)` is `1`. In `ZMod p` the roots `r₁, r₂ = (a ± m⁻¹) / 2` of `x² - a x - 1` satisfy
the Binet identity `(r₁ - r₂) U_n = r₁ ^ n - r₂ ^ n`; by Fermat `r₁ ^ (p-1) = r₂ ^ (p-1) = 1`,
hence `U_{p-1} ≡ 0 (mod p)`.
-/

open OMA.S_wp_lucas_wieferich_prime

namespace OMA.Proof_wp_lucas_wieferich_prime

lemma lucasU_succ_succ (a : ℤ) (n : ℕ) :
    lucasU a (n + 2) = a * lucasU a (n + 1) + lucasU a n := by
  rw [lucasU]

lemma binet {R : Type} [CommRing R] (a : ℤ) (r1 r2 : R) (hs : r1 + r2 = (a : R))
    (hp : r1 * r2 = -1) (n : ℕ) :
    (r1 - r2) * (lucasU a n : R) = r1 ^ n - r2 ^ n ∧
      (r1 - r2) * (lucasU a (n + 1) : R) = r1 ^ (n + 1) - r2 ^ (n + 1) := by
  induction n with
  | zero => simp [lucasU]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    obtain ⟨h1, h2⟩ := ih
    rw [lucasU_succ_succ]
    push_cast
    linear_combination (a : R) * h2 + h1 + (r2 ^ (n + 1) - r1 ^ (n + 1)) * hs
      + (r1 ^ n - r2 ^ n) * hp

theorem key (a : ℤ) (ha : 0 < a) (N : ℕ) : ∃ p, N < p ∧ IsLucasWieferichPrime a p := by
  obtain ⟨d, hdD⟩ : ∃ d : ℕ, (d : ℤ) = a ^ 2 + 4 :=
    ⟨(a ^ 2 + 4).toNat, Int.toNat_of_nonneg (by positivity)⟩
  have hd5 : 5 ≤ d := by
    have : (5 : ℤ) ≤ (d : ℤ) := by rw [hdD]; nlinarith
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 * N.factorial := ⟨_, rfl⟩
  have hm2 : 2 ≤ m := by have := N.factorial_pos; omega
  have hdm : 20 ≤ d * m ^ 2 := by nlinarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K + 1 = d * m ^ 2 := ⟨d * m ^ 2 - 1, by omega⟩
  have hK1 : K ≠ 1 := by omega
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = K.minFac := ⟨_, rfl⟩
  have hpp : p.Prime := hpdef ▸ Nat.minFac_prime hK1
  have hpK : p ∣ K := hpdef ▸ Nat.minFac_dvd K
  have : Fact p.Prime := ⟨hpp⟩
  have hz : (d : ZMod p) * (m : ZMod p) ^ 2 = 1 := by
    have h0 : ((K : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff K p).mpr hpK
    have h1 : ((K + 1 : ℕ) : ZMod p) = ((d * m ^ 2 : ℕ) : ZMod p) := by rw [hK]
    push_cast at h1
    rw [h0, zero_add] at h1
    exact h1.symm
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hNp : N < p := by
    by_contra hle
    have hle' : p ≤ N := not_lt.mp hle
    have h1 : p ∣ N.factorial := (Nat.Prime.dvd_factorial hpp).mpr hle'
    have h2 : p ∣ m := hm ▸ Dvd.dvd.mul_left h1 2
    exact hm0 ((ZMod.natCast_eq_zero_iff m p).mpr h2)
  have hp2 : p ≠ 2 := by
    intro h2
    have h3 : p ∣ m := by rw [h2, hm]; exact Dvd.intro _ rfl
    exact hm0 ((ZMod.natCast_eq_zero_iff m p).mpr h3)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have h'' := (ZMod.natCast_eq_zero_iff 2 p).mp h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h'')
  obtain ⟨s, hsdef⟩ : ∃ s : ZMod p, s = (m : ZMod p)⁻¹ := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := hsdef ▸ inv_ne_zero hm0
  have hms : (m : ZMod p) * s = 1 := by rw [hsdef]; exact mul_inv_cancel₀ hm0
  have hds : (d : ZMod p) = s ^ 2 := by
    linear_combination s ^ 2 * hz - (d : ZMod p) * ((m : ZMod p) * s + 1) * hms
  have hDs : (((a ^ 2 + 4 : ℤ)) : ZMod p) = s ^ 2 := by
    rw [← hdD, Int.cast_natCast]; exact hds
  have ha2 : (a : ZMod p) ^ 2 + 4 = s ^ 2 := by
    have := hDs
    push_cast at this
    exact this
  obtain ⟨r1, hr1⟩ : ∃ r1 : ZMod p, r1 = ((a : ZMod p) + s) / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ZMod p, r2 = ((a : ZMod p) - s) / 2 := ⟨_, rfl⟩
  have e1 : 2 * r1 = (a : ZMod p) + s := by rw [hr1]; field_simp
  have e2 : 2 * r2 = (a : ZMod p) - s := by rw [hr2]; field_simp
  have hsum : r1 + r2 = (a : ZMod p) := by
    have h : 2 * (r1 + r2) = 2 * (a : ZMod p) := by linear_combination e1 + e2
    exact mul_left_cancel₀ h2ne h
  have hdiff : r1 - r2 = s := by
    have h : 2 * (r1 - r2) = 2 * s := by linear_combination e1 - e2
    exact mul_left_cancel₀ h2ne h
  have hprod : r1 * r2 = -1 := by
    have h : 2 * (2 * (r1 * r2)) = 2 * (2 * (-1)) := by
      linear_combination (2 * r2) * e1 + ((a : ZMod p) + s) * e2 + ha2
    exact mul_left_cancel₀ h2ne (mul_left_cancel₀ h2ne h)
  have hr1ne : r1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    have : (1 : ZMod p) = 0 := by linear_combination hprod
    exact one_ne_zero this
  have hr2ne : r2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    have : (1 : ZMod p) = 0 := by linear_combination hprod
    exact one_ne_zero this
  have hb := (binet a r1 r2 (by rw [hsum]) hprod (p - 1)).1
  rw [hdiff, ZMod.pow_card_sub_one_eq_one hr1ne, ZMod.pow_card_sub_one_eq_one hr2ne,
    sub_self] at hb
  have hU : ((lucasU a (p - 1) : ℤ) : ZMod p) = 0 := (mul_eq_zero.mp hb).resolve_left hs0
  have hdvd : (p : ℤ) ∣ lucasU a (p - 1) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hU
  have hD0 : (((a ^ 2 + 4 : ℤ)) : ZMod p) ≠ 0 := by rw [hDs]; exact pow_ne_zero 2 hs0
  have hleg : legendreSym p (a ^ 2 + 4) = 1 :=
    (legendreSym.eq_one_iff p hD0).mpr ⟨s, by rw [hDs]; ring⟩
  have hjac : jacobiSym (a ^ 2 + 4) p = 1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]; exact hleg
  refine ⟨p, hNp, hpp, ?_⟩
  have hdisc : lucasDiscriminant a = a ^ 2 + 4 := rfl
  rw [hdisc, hjac]
  have htn : ((p : ℤ) - 1).toNat = p - 1 := by
    have := hpp.pos
    omega
  rw [htn]
  exact hdvd

end OMA.Proof_wp_lucas_wieferich_prime

theorem OMA.solution : type_of% @OMA.S_wp_lucas_wieferich_prime.main := by
  intro a ha
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, hlt, hp⟩ := OMA.Proof_wp_lucas_wieferich_prime.key a ha N
  exact absurd (hN hp) (not_le.mpr hlt)
