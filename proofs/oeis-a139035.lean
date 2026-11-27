import OMAStatements.S_oeis_a139035

/-!
Proof of OEIS A139035: for prime p, if orderOf (-2 : ZMod p) = p - 1, then p is odd
and (-2)^((p-1)/2) = -1 in ZMod p, so -4 = (-2)^((p-1)/2 + 2).
Thus orderOf (-4 : ZMod p) = (2*k) / gcd(2*k, k+2), which equals 2*k iff k is odd, i.e. p % 4 = 3.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a139035.main := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  have haux : orderOf (-2 : ZMod p) = p - 1 →
      (p % 4 = 3 ↔ orderOf (-4 : ZMod p) = p - 1) := by
    intro hx
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h0 : (-2 : ZMod 2) = 0 := by
        rw [show (2 : ZMod 2) = ((2 : ℕ) : ZMod 2) from rfl, ZMod.natCast_self, neg_zero]
      rw [h0, orderOf_zero] at hx
      omega
    have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    set k := (p - 1) / 2
    have hpk : 2 * k = p - 1 := by omega
    have hkpos : 1 ≤ k := by omega
    have hsq : ((-2 : ZMod p) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm k 2, hpk, ← hx, pow_orderOf_eq_one]
    have hxk : (-2 : ZMod p) ^ k = -1 := by
      rcases sq_eq_one_iff.mp hsq with h1 | h1
      · have hdvd : p - 1 ∣ k := by
          rw [← hx]
          exact orderOf_dvd_iff_pow_eq_one.mpr h1
        have hle := Nat.le_of_dvd hkpos hdvd
        omega
      · exact h1
    have h4 : (-4 : ZMod p) = (-2 : ZMod p) ^ (k + 2) := by
      rw [pow_add, hxk]
      ring
    have hord4 : orderOf (-4 : ZMod p) = (2 * k) / Nat.gcd (2 * k) (k + 2) := by
      rw [h4, orderOf_pow' (-2 : ZMod p) (by omega), hx, hpk]
    rw [hord4, ← hpk]
    constructor
    · intro hp4
      have hkodd : k % 2 = 1 := by omega
      set d := Nat.gcd (2 * k) (k + 2)
      have hdL : d ∣ 2 * k := Nat.gcd_dvd_left _ _
      have hdR : d ∣ k + 2 := Nat.gcd_dvd_right _ _
      have hdnot2 : ¬ 2 ∣ d := by
        intro h2d
        have h2k : 2 ∣ k + 2 := h2d.trans hdR
        omega
      have hcop : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr hdnot2
      have hdk : d ∣ k := hcop.symm.dvd_of_dvd_mul_left hdL
      have hd2 : d ∣ 2 := by
        have hsub := Nat.dvd_sub hdR hdk
        simpa using hsub
      have hd1 : d = 1 := by
        have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd2
        have hd0 : d ≠ 0 := Nat.gcd_ne_zero_left (by omega)
        interval_cases d <;> simp_all
      rw [hd1, Nat.div_one]
    · intro heq
      set d := Nat.gcd (2 * k) (k + 2)
      have hd0 : d ≠ 0 := Nat.gcd_ne_zero_left (by omega)
      have hd1 : d = 1 := by
        by_contra hne
        have hd2 : 2 ≤ d := by omega
        have hlt := Nat.div_lt_self (by omega : 0 < 2 * k) hd2
        omega
      have hkodd : k % 2 = 1 := by
        by_contra hkeven
        have h2k : 2 ∣ k := by omega
        have h2d : 2 ∣ d := Nat.dvd_gcd (dvd_mul_of_dvd_right h2k 2) (dvd_add h2k dvd_rfl)
        rw [hd1] at h2d
        omega
      omega
  constructor
  · rintro ⟨hp4, hx⟩
    exact ⟨hx, (haux hx).mp hp4⟩
  · rintro ⟨hx, h4⟩
    exact ⟨(haux hx).mpr h4, hx⟩
