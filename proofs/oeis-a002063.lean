import OMAStatements.S_oeis_a002063
import Mathlib

/-!
# A002063: the squares that are sums of two distinct powers of two

If s² = 2^i + 2^j = 2^i(1 + 2^k) with k = j − i ≥ 1, write s = 2^a·t with t odd; comparing 2-adic
parts gives i = 2a and t² = 1 + 2^k. Then (t − 1)(t + 1) = 2^k, so t − 1 and t + 1 are powers of two
differing by 2, forcing t = 3 and k = 3. Hence the square is 2^(2a)·9 = 9·4^a. Conversely
9·4^n = (3·2^n)² = 2^(2n) + 2^(2n+3).
-/

namespace PA002063

theorem two_pow_mul_odd_inj {i e u w : ℕ} (hu : Odd u) (hw : Odd w) (h : 2 ^ i * u = 2 ^ e * w) :
    i = e ∧ u = w := by
  have key : ∀ {i e u w : ℕ}, Odd u → Odd w → 2 ^ i * u = 2 ^ e * w → i ≤ e := by
    intro i e u w hu hw h
    by_contra hlt
    rw [not_le] at hlt
    have : 2 ^ i = 2 ^ e * 2 ^ (i - e) := by rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc] at h
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h
    have heven : Even (2 ^ (i - e) * u) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right u
    rw [h2] at heven
    exact (Nat.not_even_iff_odd.mpr hw) heven
  have h1 := key hu hw h
  have h2 := key hw hu h.symm
  have hie : i = e := le_antisymm h1 h2
  subst hie
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem odd_sq_eq (t k : ℕ) (ht : Odd t) (_hk : 1 ≤ k) (h : t ^ 2 = 1 + 2 ^ k) : t = 3 ∧ k = 3 := by
  have ht1 : 1 ≤ t := ht.pos
  have hprod : (t - 1) * (t + 1) = 2 ^ k := by
    have : (t - 1) * (t + 1) + 1 = t ^ 2 := by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    omega
  obtain ⟨u, hu, hu'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ hprod)
  obtain ⟨v, hv, hv'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro_left _ hprod)
  have huv : 2 ^ v = 2 ^ u + 2 := by omega
  have hu1 : u = 1 := by
    rcases (by omega : u = 0 ∨ u = 1 ∨ 2 ≤ u) with h0 | h1 | h2
    · exfalso
      rw [h0] at hu'
      have : t = 2 := by simp at hu'; omega
      rw [this] at ht
      exact (Nat.not_even_iff_odd.mpr ht) even_two
    · exact h1
    · exfalso
      have h4u : 4 ∣ 2 ^ u := by have := pow_dvd_pow 2 h2; norm_num at this; exact this
      rcases (by omega : v = 0 ∨ v = 1 ∨ 2 ≤ v) with g | g | g
      · rw [g, pow_zero] at huv; have := Nat.one_le_two_pow (n := u); omega
      · rw [g, pow_one] at huv; have := Nat.one_le_two_pow (n := u); omega
      · have h4v : 4 ∣ 2 ^ v := by have := pow_dvd_pow 2 g; norm_num at this; exact this
        omega
  rw [hu1] at hu'
  have ht3 : t = 3 := by simp at hu'; omega
  refine ⟨ht3, ?_⟩
  rw [ht3] at h
  have h8 : 2 ^ k = 2 ^ 3 := by omega
  exact Nat.pow_right_injective (le_refl 2) h8

end PA002063

theorem OMA.solution : type_of% @OMA.S_oeis_a002063.main := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨⟨s, hs⟩, i, j, hij, hm⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
      have : 0 < 2 ^ i + 2 ^ j := by positivity
      omega
    obtain ⟨a, t, ht, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hs0
    obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
    have hk : 1 ≤ k := by omega
    have h1 : 2 ^ i * (1 + 2 ^ k) = 2 ^ (2 * a) * t ^ 2 := by
      calc 2 ^ i * (1 + 2 ^ k) = 2 ^ i + 2 ^ (i + k) := by ring
        _ = m := hm.symm
        _ = 2 ^ (2 * a) * t ^ 2 := by rw [hs]; ring
    have hodd1 : Odd (1 + 2 ^ k) := by
      rw [add_comm]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    obtain ⟨hia, hut⟩ := PA002063.two_pow_mul_odd_inj hodd1 (ht.pow) h1
    obtain ⟨ht3, hk3⟩ := PA002063.odd_sq_eq t k ht hk hut.symm
    refine ⟨a, ?_⟩
    rw [hs, ht3, show (4 : ℕ) ^ a = 2 ^ a * 2 ^ a by rw [← mul_pow]; norm_num]
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨⟨3 * 2 ^ n, ?_⟩, 2 * n, 2 * n + 3, by omega, ?_⟩
    · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
    · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, pow_add]; ring
