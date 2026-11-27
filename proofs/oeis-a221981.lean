import OMAStatements.S_oeis_a221981
import Mathlib

namespace A221981
open OMA.S_oeis_a221981

lemma five_prime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

lemma four_ne : ((4 : ℤ) : ZMod 5) ≠ 0 := by decide

lemma four_sq : ((4 : ℤ) : ZMod 5) = 2 * 2 := by decide

lemma three_nonsq : ∀ r : ZMod 5, ¬ (((3 : ℤ) : ZMod 5) = r * r) := by decide

lemma leg5_4 : @legendreSym 5 five_prime 4 = 1 := by
  have h5 : Fact (Nat.Prime 5) := five_prime
  rw [legendreSym.eq_one_iff 5 four_ne]
  exact ⟨2, four_sq⟩

lemma leg5_3 : @legendreSym 5 five_prime 3 = -1 := by
  have h5 : Fact (Nat.Prime 5) := five_prime
  rw [legendreSym.eq_neg_one_iff]
  rintro ⟨r, hr⟩
  exact three_nonsq r hr

lemma nonres_pow (r : ℕ) [Fact r.Prime] (hr : 2 < r) (g : ℤ) (h : legendreSym r g = -1) :
    ((g : ℤ) : ZMod r) ^ (r / 2) ≠ 1 := by
  have h1 := legendreSym.eq_pow r g
  rw [h] at h1
  intro hc
  rw [hc] at h1
  have h2 : Fact (2 < r) := ⟨hr⟩
  exact ZMod.neg_one_ne_one (n := r) (by simpa using h1)

lemma ne_zero_of_leg (r : ℕ) [Fact r.Prime] (g : ℤ) (h : legendreSym r g = -1) :
    ((g : ℤ) : ZMod r) ≠ 0 := by
  intro h0
  rw [← legendreSym.eq_zero_iff] at h0
  rw [h] at h0
  norm_num at h0

lemma leg_five (r : ℕ) [Fact r.Prime] (hr : r ≠ 2) :
    legendreSym r 5 = @legendreSym 5 five_prime (((r % 5 : ℕ) : ℤ)) := by
  have h5 : Fact (Nat.Prime 5) := five_prime
  have e := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := r) (by norm_num) hr
  have e2 := legendreSym.mod 5 (r : ℤ)
  have e3 : ((r : ℤ) % ((5 : ℕ) : ℤ)) = ((r % 5 : ℕ) : ℤ) := by push_cast; rfl
  rw [e3] at e2
  rw [← e2, ← e]
  rfl

lemma p_odd (p : ℕ) (hp : p.Prime) (hq : (4 * p + 1).Prime) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h | h
  · subst h
    norm_num at hq
  · exact h

lemma partA (q : ℕ) (h : InSeq q) : orderOf (40 : ZMod q) = q - 1 := by
  obtain ⟨hq, p, hp, hp5, rfl⟩ := h
  have hfq : Fact (4 * p + 1).Prime := ⟨hq⟩
  have hpodd := p_odd p hp hq
  have hq2 : 4 * p + 1 ≠ 2 := by omega
  have h2 : legendreSym (4 * p + 1) 2 = -1 := by
    rw [legendreSym.at_two hq2, ZMod.χ₈_nat_eq_if_mod_eight]
    rw [if_neg (by omega), if_neg (by omega)]
  have h5 : legendreSym (4 * p + 1) 5 = 1 := by
    rw [leg_five _ hq2]
    have e : (4 * p + 1) % 5 = 4 := by omega
    rw [e]
    exact leg5_4
  have hleg : legendreSym (4 * p + 1) 40 = -1 := by
    have e : (40 : ℤ) = 2 * 2 * 2 * 5 := by norm_num
    rw [e, legendreSym.mul, legendreSym.mul, legendreSym.mul, h2, h5]
    norm_num
  have h40 : (40 : ZMod (4 * p + 1)) ^ ((4 * p + 1) / 2) ≠ 1 := by
    simpa using nonres_pow (4 * p + 1) (by omega) 40 hleg
  have hx0 : (40 : ZMod (4 * p + 1)) ≠ 0 := by
    simpa using ne_zero_of_leg (4 * p + 1) 40 hleg
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega) (ZMod.pow_card_sub_one_eq_one hx0)
  intro l hl hdvd
  have e : 4 * p + 1 - 1 = 4 * p := by omega
  rw [e] at hdvd ⊢
  rcases (Nat.Prime.dvd_mul hl).mp hdvd with h4 | hlp
  · have h4' : l ∣ 2 ^ 2 := by simpa using h4
    have hl2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h4')
    subst hl2
    have e2 : 4 * p / 2 = (4 * p + 1) / 2 := by omega
    rw [e2]
    exact h40
  · have hlp' : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).mp hlp
    subst hlp'
    have e3 : 4 * l / l = 4 := Nat.mul_div_cancel _ hl.pos
    rw [e3]
    intro hc
    have hz : ((2559999 : ℕ) : ZMod (4 * l + 1)) = 0 := by
      have e4 : ((2559999 : ℕ) : ZMod (4 * l + 1)) = 40 ^ 4 - 1 := by norm_num
      rw [e4, hc, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at hz
    have e5 : 2559999 = 3 * 13 * 41 * 1601 := by norm_num
    rw [e5] at hz
    rcases (Nat.Prime.dvd_mul hq).mp hz with hz | hz
    · rcases (Nat.Prime.dvd_mul hq).mp hz with hz | hz
      · rcases (Nat.Prime.dvd_mul hq).mp hz with hz | hz
        · have := Nat.le_of_dvd (by norm_num) hz
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hz
          omega
      · have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hz
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hz
      omega

lemma partB (q : ℕ) (h : InSeq q) (hr : (8 * q + 1).Prime) :
    orderOf (10 : ZMod (8 * q + 1)) = 8 * q + 1 - 1 := by
  obtain ⟨hq, p, hp, hp5, rfl⟩ := h
  have hfr : Fact (8 * (4 * p + 1) + 1).Prime := ⟨hr⟩
  have hpodd := p_odd p hp hq
  have hr2 : 8 * (4 * p + 1) + 1 ≠ 2 := by omega
  have h2 : legendreSym (8 * (4 * p + 1) + 1) 2 = 1 := by
    rw [legendreSym.at_two hr2, ZMod.χ₈_nat_eq_if_mod_eight]
    rw [if_neg (by omega), if_pos (by omega)]
  have h5 : legendreSym (8 * (4 * p + 1) + 1) 5 = -1 := by
    rw [leg_five _ hr2]
    have e : (8 * (4 * p + 1) + 1) % 5 = 3 := by omega
    rw [e]
    exact leg5_3
  have hleg : legendreSym (8 * (4 * p + 1) + 1) 10 = -1 := by
    have e : (10 : ℤ) = 2 * 5 := by norm_num
    rw [e, legendreSym.mul, h2, h5]
    norm_num
  have h10 : (10 : ZMod (8 * (4 * p + 1) + 1)) ^ ((8 * (4 * p + 1) + 1) / 2) ≠ 1 := by
    simpa using nonres_pow (8 * (4 * p + 1) + 1) (by omega) 10 hleg
  have hx0 : (10 : ZMod (8 * (4 * p + 1) + 1)) ≠ 0 := by
    simpa using ne_zero_of_leg (8 * (4 * p + 1) + 1) 10 hleg
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega) (ZMod.pow_card_sub_one_eq_one hx0)
  intro l hl hdvd
  have e : 8 * (4 * p + 1) + 1 - 1 = 8 * (4 * p + 1) := by omega
  rw [e] at hdvd ⊢
  rcases (Nat.Prime.dvd_mul hl).mp hdvd with h8 | hlq
  · have h8' : l ∣ 2 ^ 3 := by simpa using h8
    have hl2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h8')
    subst hl2
    have e2 : 8 * (4 * p + 1) / 2 = (8 * (4 * p + 1) + 1) / 2 := by omega
    rw [e2]
    exact h10
  · have hlq' : l = 4 * p + 1 := (Nat.prime_dvd_prime_iff_eq hl hq).mp hlq
    subst hlq'
    have e3 : 8 * (4 * p + 1) / (4 * p + 1) = 8 := Nat.mul_div_cancel _ hl.pos
    rw [e3]
    intro hc
    have hz : ((99999999 : ℕ) : ZMod (8 * (4 * p + 1) + 1)) = 0 := by
      have e4 : ((99999999 : ℕ) : ZMod (8 * (4 * p + 1) + 1)) = 10 ^ 8 - 1 := by norm_num
      rw [e4, hc, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at hz
    have e5 : 99999999 = 9 * 11 * 73 * 101 * 137 := by norm_num
    rw [e5] at hz
    have hp7 : 7 ≤ p := by
      have := hp.two_le
      omega
    rcases (Nat.Prime.dvd_mul hr).mp hz with hz | hz
    · rcases (Nat.Prime.dvd_mul hr).mp hz with hz | hz
      · rcases (Nat.Prime.dvd_mul hr).mp hz with hz | hz
        · rcases (Nat.Prime.dvd_mul hr).mp hz with hz | hz
          · have := Nat.le_of_dvd (by norm_num) hz
            omega
          · have := Nat.le_of_dvd (by norm_num) hz
            omega
        · have := Nat.le_of_dvd (by norm_num) hz
          omega
      · have := Nat.le_of_dvd (by norm_num) hz
        omega
    · have := Nat.le_of_dvd (by norm_num) hz
      omega

end A221981

theorem OMA.solution : type_of% @OMA.S_oeis_a221981.main :=
  ⟨A221981.partA, A221981.partB⟩
