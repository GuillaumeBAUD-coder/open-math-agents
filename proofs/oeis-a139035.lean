import OMAStatements.S_oeis_a139035

-- Problem: A139035, -2 primitive root with p ≡ 3 (mod 4) iff -2 and -4 both primitive roots.
-- Credit: @ShoQo
-- Proof (Song): for p = 2m + 1 with -2 of order 2m, (-2)^m = -1, so -4 = (-2)^(m+2) has order
-- 2m / gcd(2m, m+2). That gcd is 1 when m is odd (it divides 4 and the odd m + 2) and at least 2
-- when m is even; m is odd iff p ≡ 3 (mod 4). For p = 2, -2 = 0 is not a primitive root.

open OMA.S_oeis_a139035

namespace OMA_A139035_Proof

lemma gcd_odd {m : ℕ} (hm : m % 2 = 1) : Nat.gcd (2 * m) (m + 2) = 1 := by
  set d := Nat.gcd (2 * m) (m + 2)
  have h1 : d ∣ 2 * m := Nat.gcd_dvd_left _ _
  have h2 : d ∣ m + 2 := Nat.gcd_dvd_right _ _
  have h4 : d ∣ 4 := by
    have := Nat.dvd_sub (Nat.dvd_trans h2 (Dvd.intro_left 2 rfl)) h1
    rwa [show 2 * (m + 2) - 2 * m = 4 by omega] at this
  have hd : d ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  interval_cases hd' : d
  · simp at h2
  · rfl
  · omega
  · omega
  · omega

lemma gcd_even {m : ℕ} (hm : m % 2 = 0) : 2 ≤ Nat.gcd (2 * m) (m + 2) := by
  have : 2 ∣ Nat.gcd (2 * m) (m + 2) := Nat.dvd_gcd (Dvd.intro m rfl) (by omega)
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) this

end OMA_A139035_Proof

open OMA_A139035_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a139035.main := by
  intro p hp
  have := Fact.mk hp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have h : (-2 : ZMod 2) = 0 := by decide +revert
    have hne : orderOf (-2 : ZMod 2) ≠ 2 - 1 := by
      rw [h]; intro h1; rw [orderOf_eq_one_iff] at h1; exact zero_ne_one h1
    exact ⟨fun h' => absurd h'.2 hne, fun h' => absurd h'.1 hne⟩
  obtain ⟨m, hpm⟩ := hodd
  have hm0 : m ≠ 0 := by rintro rfl; simp at hpm; exact hp.ne_one hpm
  have hp1 : p - 1 = 2 * m := by omega
  rw [hp1]
  -- with -2 of order 2m, -4 = (-2)^(m+2) has order 2m / gcd(2m, m+2)
  have key : orderOf (-2 : ZMod p) = 2 * m →
      orderOf (-4 : ZMod p) = 2 * m / Nat.gcd (2 * m) (m + 2) := by
    intro hg
    have hgm : (-2 : ZMod p) ^ m = -1 := by
      have hsq : ((-2 : ZMod p) ^ m) * ((-2 : ZMod p) ^ m) = 1 := by
        rw [← pow_add, show m + m = 2 * m by ring, ← hg, pow_orderOf_eq_one]
      rcases mul_self_eq_one_iff.1 hsq with h | h
      · exact absurd h (pow_ne_one_of_lt_orderOf hm0 (by omega))
      · exact h
    have h4 : (-4 : ZMod p) = (-2 : ZMod p) ^ (m + 2) := by rw [pow_add, hgm]; ring
    rw [h4, orderOf_pow' _ (by omega), hg]
  constructor
  · rintro ⟨h4, hg⟩
    refine ⟨hg, ?_⟩
    rw [key hg, gcd_odd (by omega), Nat.div_one]
  · rintro ⟨hg, h4⟩
    refine ⟨?_, hg⟩
    by_contra hm4
    have hme : m % 2 = 0 := by omega
    have := gcd_even hme
    rw [key hg] at h4
    have : 2 * m / Nat.gcd (2 * m) (m + 2) ≤ 2 * m / 2 := Nat.div_le_div_left this (by norm_num)
    omega
