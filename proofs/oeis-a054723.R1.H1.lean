import OMAReductions.R_oeis_a054723_R1

-- Step oeis-a054723.R1.H1: hypothesis H1 of reduction oeis-a054723.R1
-- Credit: @sovrana

theorem fwd (p : ℕ) (hp4 : p % 4 = 3) (hq : (2 * p + 1).Prime) : 2 * p + 1 ∣ 2 ^ p - 1 := by
  haveI : Fact (2 * p + 1).Prime := ⟨hq⟩
  have h2 : (2 * p + 1) ≠ 2 := by omega
  have hsq : IsSquare (2 : ZMod (2 * p + 1)) := by
    rw [ZMod.exists_sq_eq_two_iff h2]
    right; omega
  have hne : (2 : ZMod (2 * p + 1)) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 (2 * p + 1)).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have := (ZMod.euler_criterion (2 * p + 1) hne).1 hsq
  have hd : (2 * p + 1) / 2 = p := by omega
  rw [hd] at this
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
  simp [this]

theorem bwd (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hd : 2 * p + 1 ∣ 2 ^ p - 1) : (2 * p + 1).Prime := by
  set q := 2 * p + 1 with hqdef
  have hq1 : q ≠ 1 := by omega
  have hr : (q.minFac).Prime := Nat.minFac_prime hq1
  set r := q.minFac with hrdef
  haveI : Fact r.Prime := ⟨hr⟩
  have hrq : r ∣ q := Nat.minFac_dvd q
  have hrd : r ∣ 2 ^ p - 1 := dvd_trans hrq hd
  have h1 : (2 : ZMod r) ^ p = 1 := by
    have := (ZMod.natCast_eq_zero_iff (2 ^ p - 1) r).2 hrd
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow] at this
    simpa [sub_eq_zero] using this
  have hr2 : r ≠ 2 := by
    intro h
    rw [h] at hrq
    omega
  have hne : (2 : ZMod r) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 r).1 (by exact_mod_cast h)
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this
    exact hr2 this
  have hord : orderOf (2 : ZMod r) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have hord_ne : orderOf (2 : ZMod r) ≠ 1 := by
    intro h
    rw [orderOf_eq_one_iff] at h
    have : (2 : ZMod r) - 1 = 0 := by rw [h]; ring
    have h' : (1 : ZMod r) = 0 := by
      have : (2 : ZMod r) = 1 := h
      have e : (2 : ZMod r) = 1 + 1 := by norm_num
      rw [e] at this
      simpa using this
    exact one_ne_zero h'
  have hord_p : orderOf (2 : ZMod r) = p := by
    rcases (Nat.dvd_prime hp).1 hord with h | h
    · exact absurd h hord_ne
    · exact h
  have hdv : p ∣ r - 1 := hord_p ▸ ZMod.orderOf_dvd_card_sub_one hne
  have hqodd : Odd q := ⟨p, by omega⟩
  have hrodd : Odd r := by
    rcases hr.eq_two_or_odd' with h | h
    · exact absurd h hr2
    · exact h
  obtain ⟨c, hc⟩ := hdv
  obtain ⟨t, ht⟩ := hrodd
  have hpodd : p % 2 = 1 := by omega
  have hceven : c % 2 = 0 := by
    rcases Nat.even_or_odd c with ⟨e, he⟩ | ⟨e, he⟩
    · omega
    · exfalso
      have : r - 1 = 2 * t := by omega
      rw [hc, he] at this
      have : p * (2 * e + 1) = 2 * t := this
      have h3 : (p * (2 * e + 1)) % 2 = 1 := by
        rw [Nat.mul_mod, hpodd]; omega
      omega
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exfalso
      rw [h] at hc
      have : r ≥ 2 := hr.two_le
      omega
    · exact h
  have hge : 2 * p + 1 ≤ r := by
    have : 2 ≤ c := by omega
    have : p * 2 ≤ p * c := Nat.mul_le_mul_left p this
    have hr2' : r - 1 = p * c := hc
    have : 2 ≤ r := hr.two_le
    omega
  have hle : r ≤ q := Nat.le_of_dvd (by omega) hrq
  have : r = q := by omega
  rw [← this]; exact hr

theorem sol : ∀ p : ℕ, p.Prime → p % 4 = 3 → ((2 * p + 1).Prime ↔ 2 * p + 1 ∣ 2 ^ p - 1) :=
  fun p hp hp4 => ⟨fwd p hp4, bwd p hp hp4⟩

theorem OMA.solution : OMA.R_oeis_a054723_R1.H1 := sol
