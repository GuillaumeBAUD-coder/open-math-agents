import OMAStatements.S_oeis_a342992

-- A342992: every positive integer coprime to five has a multiple
-- whose decimal digits all lie in the two-element alphabet {2, 3}.
-- Credit: @begcdn
namespace OMA.PrimeDigits

def twoOrThree (x : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 x, d = 2 ∨ d = 3

-- Prepend one digit. The new quotient by 2^k changes by d * 5^k,
-- so exactly one of the two choices makes that quotient even.
lemma powerBlock (k : ℕ) : ∃ x : ℕ, (Nat.digits 10 x).length = k ∧
    twoOrThree x ∧ 2 ^ k ∣ x := by
  induction k with
  | zero => exact ⟨0, by simp, by simp [twoOrThree], by simp⟩
  | succ k ih =>
    obtain ⟨x, hlen, hgood, u, hu⟩ := ih
    have hodd : Odd (5 ^ k : ℕ) := (show Odd (5 : ℕ) by decide).pow
    obtain ⟨d, hd, v, hv⟩ : ∃ d : ℕ, (d = 2 ∨ d = 3) ∧
        2 ∣ u + 5 ^ k * d := by
      by_cases h : 2 ∣ u
      · exact ⟨2, Or.inl rfl, dvd_add h (dvd_mul_left 2 _)⟩
      · refine ⟨3, Or.inr rfl, ?_⟩
        obtain ⟨a, ha⟩ := hodd
        omega
    have hsingle : Nat.digits 10 d = [d] :=
      Nat.digits_of_lt _ _ (by omega) (by omega)
    have happend : Nat.digits 10 (x + 10 ^ k * d) = Nat.digits 10 x ++ [d] := by
      simpa only [hlen, hsingle] using
        (Nat.digits_append_digits (b := 10) (m := d) (n := x) (by decide)).symm
    refine ⟨x + 10 ^ k * d, by simp [happend, hlen], ?_, v, ?_⟩
    · intro j hj
      rw [happend, List.mem_append] at hj
      rcases hj with hj | hj
      · exact hgood j hj
      · exact (List.mem_singleton.mp hj).symm ▸ hd
    · calc
        x + 10 ^ k * d = 2 ^ k * (u + 5 ^ k * d) := by
          rw [hu, show (10 : ℕ) = 2 * 5 by decide, mul_pow]; ring
        _ = 2 ^ (k + 1) * v := by rw [hv, pow_succ]; ring

-- Concatenating t copies multiplies x by a factor congruent to t
-- whenever shifting one block acts as the identity modulo m.
lemma repeatBlock (x m : ℕ) (hx : twoOrThree x)
    (hshift : 10 ^ (Nat.digits 10 x).length ≡ 1 [MOD m]) (t : ℕ) :
    ∃ s : ℕ, s ≡ t [MOD m] ∧ (0 < t → 0 < s) ∧ twoOrThree (x * s) := by
  induction t with
  | zero => exact ⟨0, Nat.ModEq.rfl, by omega, by simp [twoOrThree]⟩
  | succ t ih =>
    obtain ⟨s, hs, _, hxs⟩ := ih
    refine ⟨1 + 10 ^ (Nat.digits 10 x).length * s, ?_, by omega, ?_⟩
    · simpa [Nat.add_comm] using (hshift.mul hs).add_left 1
    · intro d hd
      rw [show x * (1 + 10 ^ (Nat.digits 10 x).length * s) =
          x + 10 ^ (Nat.digits 10 x).length * (x * s) by ring,
        ← Nat.digits_append_digits (by decide : 0 < 10), List.mem_append] at hd
      exact hd.elim (hx d) (hxs d)

end OMA.PrimeDigits

theorem OMA.solution : type_of% @OMA.S_oeis_a342992.main := by
  intro n hn hfive
  obtain ⟨v, m, hodd, hfactor⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have hm : 0 < m := by
    obtain ⟨a, ha⟩ := hodd
    omega
  have hc5 : Nat.Coprime 5 m := (Nat.prime_five.coprime_iff_not_dvd).mpr fun h =>
    hfive (hfactor ▸ dvd_mul_of_dvd_right h _)
  have hc10 : Nat.Coprime 10 m := hodd.coprime_two_left.mul_left hc5
  let L := m.totient * (v + 1)
  have hphi := Nat.totient_pos.mpr hm
  have hlarge : v + 1 ≤ L := by
    dsimp [L]
    simpa using Nat.mul_le_mul_right (v + 1) hphi
  obtain ⟨x, hxlen, hx, hxdiv⟩ := OMA.PrimeDigits.powerBlock L
  have hxpos : 0 < x := by
    by_contra! hz
    simp [show x = 0 by omega] at hxlen
    omega
  have hshift : 10 ^ (Nat.digits 10 x).length ≡ 1 [MOD m] := by
    rw [hxlen, show L = m.totient * (v + 1) from rfl, pow_mul]
    simpa using (Nat.ModEq.pow_totient hc10).pow (v + 1)
  obtain ⟨s, hs, hspos, hdigits⟩ := OMA.PrimeDigits.repeatBlock x m hx hshift m
  have hsd : m ∣ s := Nat.modEq_zero_iff_dvd.mp
    (hs.trans (dvd_refl m).modEq_zero_nat)
  have hxd : 2 ^ v ∣ x := (pow_dvd_pow 2 (by omega : v ≤ L)).trans hxdiv
  have hprod : n ∣ x * s := hfactor ▸ Nat.mul_dvd_mul hxd hsd
  obtain ⟨k, hk⟩ := hprod
  have hpos := Nat.mul_pos hxpos (hspos hm)
  refine ⟨k, ?_, ?_⟩
  · by_contra! h
    simp [show k = 0 by omega] at hk
    omega
  · rw [Nat.mul_comm k n, ← hk]
    intro d hd
    rcases hdigits d hd with rfl | rfl <;> decide
