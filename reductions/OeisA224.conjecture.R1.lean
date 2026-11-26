import FormalConjectures.OEIS.«224»

-- Reduction OeisA224.conjecture.R1 of Number of squares $\bmod n$
-- Credit: @BetAdmin237
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Target (Ordowski, 2017): for n > 1, n is an odd prime iff n^2 = 1 mod a(n)(a(n)-1),
-- where a(n) = A000224(n) is the number of squares mod n.
--
-- What this file proves outright:
--  * the forward direction: a(p) = (p+1)/2 for every odd prime p (lemma card_squares_prime),
--    so a(p)(a(p)-1) = (p^2-1)/4 divides p^2-1;
--  * every even n >= 2 fails the congruence: a(n) >= 2, so a(n)(a(n)-1) is even,
--    while n^2 - 1 is odd (this also handles n = 2).
-- What remains open is the converse for odd composite n, split by the shape of n:
--  H1: odd prime powers p^k with k >= 2 (a(p^k) has an explicit closed form, so this is
--      a concrete divisibility question);
--  H2: odd n > 1 that are not prime powers (where a(n) is multiplicative over the
--      prime-power factors of n).

namespace OMA.R_OeisA224_conjecture_R1

open OeisA224

def H1 : Prop :=
  ∀ p k : ℕ, p.Prime → p ≠ 2 → 2 ≤ k →
    ¬ (p ^ k) ^ 2 ≡ 1 [MOD OeisA224.a (p ^ k) * (OeisA224.a (p ^ k) - 1)]

def H2 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → ¬ IsPrimePow n →
    ¬ n ^ 2 ≡ 1 [MOD OeisA224.a n * (OeisA224.a n - 1)]

lemma two_le_a (n : ℕ) (hn : 2 ≤ n) : 2 ≤ OeisA224.a n := by
  unfold OeisA224.a
  rw [if_neg (by omega)]
  have h0 : 0 ∈ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
  have h1 : 1 ∈ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) :=
    Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), by
      simp only [one_pow]; exact Nat.mod_eq_of_lt (by omega)⟩
  have hsub : ({0, 1} : Finset ℕ) ⊆ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0
    · exact h1
  have := Finset.card_le_card hsub
  simpa using this

lemma even_fails (n : ℕ) (hn : 2 ≤ n) (he : Even n) :
    ¬ n ^ 2 ≡ 1 [MOD OeisA224.a n * (OeisA224.a n - 1)] := by
  intro h
  have h2 : 2 ∣ OeisA224.a n * (OeisA224.a n - 1) := by
    have := Nat.even_mul_pred_self (OeisA224.a n)
    exact even_iff_two_dvd.mp this
  have h' : n ^ 2 ≡ 1 [MOD 2] := Nat.ModEq.of_dvd h2 h
  obtain ⟨r, rfl⟩ := he
  unfold Nat.ModEq at h'
  have : (r + r) ^ 2 % 2 = 0 := by
    have : (r + r) ^ 2 = 2 * (2 * r * r) := by ring
    rw [this]; simp
  omega

lemma card_squares_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    OeisA224.a p = (p + 1) / 2 := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by
    have := hp.two_le; rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact ⟨p / 2, by omega⟩
  unfold OeisA224.a
  rw [if_neg (by omega)]
  have key : ∀ x y : ℕ, x ^ 2 % p = y ^ 2 % p ↔ ((x : ZMod p)) ^ 2 = ((y : ZMod p)) ^ 2 := by
    intro x y
    rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff]
    push_cast; rfl
  have himg : (Finset.range p).image (fun k : ℕ => k ^ 2 % p) =
      (Finset.range (m + 1)).image (fun k : ℕ => k ^ 2 % p) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_range] at hk
      by_cases hkm : k ≤ m
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
      · refine Finset.mem_image.mpr ⟨p - k, Finset.mem_range.mpr (by omega), ?_⟩
        rw [key]
        rw [Nat.cast_sub hk.le, ZMod.natCast_self]
        ring
    · apply Finset.image_subset_image
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  · omega
  · intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    have h := (key x y).mp hxy
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · have := (ZMod.natCast_eq_natCast_iff' x y p).mp h
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    · have h' : ((x + y : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
        push_cast; rw [h]; ring
      have := (ZMod.natCast_eq_natCast_iff' (x + y) 0 p).mp h'
      rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at this
      omega

lemma prime_holds (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ 2 ≡ 1 [MOD OeisA224.a p * (OeisA224.a p - 1)] := by
  rw [card_squares_prime p hp hp2]
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact ⟨p / 2, by omega⟩
  subst hm
  have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [e1, Nat.add_sub_cancel]
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd' (by nlinarith)]
  refine ⟨4, ?_⟩
  have : (2 * m + 1) ^ 2 = 4 * ((m + 1) * m) + 1 := by ring
  rw [this, Nat.add_sub_cancel]
  ring

theorem main : H1 → H2 → type_of% @OeisA224.conjecture := by
  intro h1 h2 n hn
  constructor
  · rintro ⟨hp, hp2⟩
    exact prime_holds n hp hp2
  · intro hcong
    by_cases hprime : n.Prime
    · refine ⟨hprime, ?_⟩
      rintro rfl
      exact even_fails 2 le_rfl even_two hcong
    · exfalso
      rcases Nat.even_or_odd n with he | ho
      · exact even_fails n hn he hcong
      · by_cases hpp : IsPrimePow n
        · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
          have hk2 : 2 ≤ k := by
            by_contra hlt
            have : k = 1 := by omega
            subst this
            exact hprime (by simpa using hp)
          have hp2 : p ≠ 2 := by
            rintro rfl
            have : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
            exact (Nat.not_even_iff_odd.mpr ho) this
          exact h1 p k hp hp2 hk2 hcong
        · exact h2 n hn ho hpp hcong

end OMA.R_OeisA224_conjecture_R1
