import OMAStatements.S_oeis_a280364

-- Problem: A280364, 2 X 2 matrices with entries in {0,...,n} whose permanent equals determinant^n.
-- Credit: @Dariusthedoggie
-- Proof idea: with x = ad, y = bc and D = x - y, the equation x + y = D^n forces D in {0,1,-1}
-- (|D| >= 3 and |D| = 2 are ruled out by size, or by a prime factor larger than n when n <= 6).
-- So a(n) = (2n+1)^2 + (2n+1) + [n even](2n+1) for n >= 1, and a(0) = 0.

namespace OMA.P280364

open OMA.S_oeis_a280364

lemma two_mul_sq_lt_two_pow (n : ℕ) (h : 7 ≤ n) : 2 * n ^ 2 < 2 ^ n := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : 2 * (k + 1) ^ 2 ≤ 2 * (2 * k ^ 2) := by nlinarith
    rw [pow_succ 2 k]
    linarith

lemma two_mul_sq_lt_three_pow (n : ℕ) (h : 2 ≤ n) : 2 * n ^ 2 < 3 ^ n := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : 2 * (k + 1) ^ 2 ≤ 2 * (3 * k ^ 2) := by nlinarith
    rw [pow_succ 3 k]
    linarith

lemma no_prime_prod {n a b p : ℕ} (hp : p.Prime) (hpn : n < p) (ha : a ≤ n) (hb : b ≤ n) :
    a * b ≠ p := by
  intro h
  rw [← h] at hp
  rcases Nat.prime_mul_iff.mp hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega

lemma avoid {n x : ℕ} (hx' : ∀ p, p.Prime → n < p → x ≠ p) (p : ℕ) (hp : p.Prime) :
    p ≤ n ∨ x ≠ p := by
  by_cases h : p ≤ n
  · exact Or.inl h
  · exact Or.inr (hx' p hp (by omega))

lemma key {n x y : ℕ} (hn : 2 ≤ n) (hx : x ≤ n ^ 2) (hy : y ≤ n ^ 2)
    (hx' : ∀ p, p.Prime → n < p → x ≠ p) (hy' : ∀ p, p.Prime → n < p → y ≠ p)
    (h : (x : ℤ) + y = ((x : ℤ) - y) ^ n) :
    (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (Even n ∧ x = 0 ∧ y = 1) := by
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = (x : ℤ) - y := ⟨_, rfl⟩
  rw [← hD] at h
  have hn0 : n ≠ 0 := by omega
  by_cases hD1 : |D| ≤ 1
  · have : D = -1 ∨ D = 0 ∨ D = 1 := by
      rcases abs_le.mp hD1 with ⟨h1, h2⟩
      omega
    rcases this with rfl | rfl | rfl
    · rcases Nat.even_or_odd n with he | ho
      · rw [he.neg_one_pow] at h
        right; right
        exact ⟨he, by omega, by omega⟩
      · rw [ho.neg_one_pow] at h
        omega
    · rw [zero_pow hn0] at h
      left; omega
    · rw [one_pow] at h
      right; left; omega
  · push Not at hD1
    have hpos : 0 ≤ D ^ n := by rw [← h]; positivity
    have habs : (x : ℤ) + y = |D| ^ n := by
      rw [h, ← abs_pow, abs_of_nonneg hpos]
    have hsum : (x : ℤ) + y ≤ 2 * (n : ℤ) ^ 2 := by
      have : ((x + y : ℕ) : ℤ) ≤ ((2 * n ^ 2 : ℕ) : ℤ) := by
        exact_mod_cast (by omega : x + y ≤ 2 * n ^ 2)
      push_cast at this
      exact this
    by_cases h3 : 3 ≤ |D|
    · exfalso
      have h1 : (3 : ℤ) ^ n ≤ |D| ^ n := pow_le_pow_left₀ (by norm_num) h3 n
      have h2 : ((2 * n ^ 2 : ℕ) : ℤ) < ((3 ^ n : ℕ) : ℤ) := by
        exact_mod_cast two_mul_sq_lt_three_pow n hn
      push_cast at h2
      linarith
    · have hD2 : |D| = 2 := by omega
      rw [hD2] at habs
      have hn7 : n < 7 := by
        by_contra hc
        push Not at hc
        have h2 : ((2 * n ^ 2 : ℕ) : ℤ) < ((2 ^ n : ℕ) : ℤ) := by
          exact_mod_cast two_mul_sq_lt_two_pow n hc
        push_cast at h2
        linarith
      exfalso
      have hD' : D = 2 ∨ D = -2 := by
        rcases abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.mp hD2 with h | h
        · left; exact h
        · right; exact h
      have px := fun p (hp : p.Prime) => avoid hx' p hp
      have py := fun p (hp : p.Prime) => avoid hy' p hp
      have x3 := px 3 (by norm_num); have y3 := py 3 (by norm_num)
      have x5 := px 5 (by norm_num); have y5 := py 5 (by norm_num)
      have x7 := px 7 (by norm_num); have y7 := py 7 (by norm_num)
      have x17 := px 17 (by norm_num); have y17 := py 17 (by norm_num)
      have x31 := px 31 (by norm_num); have y31 := py 31 (by norm_num)
      clear px py hx' hy'
      interval_cases n <;> rcases hD' with rfl | rfl <;> norm_num at h <;> omega

lemma accept_iff {n a b c d : ℕ} (hn : 1 ≤ n) (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n)
    (hd : d ≤ n) :
    accept n (a * b) (c * d) ↔
      (a * b = 0 ∧ c * d = 0) ∨ (a * b = 1 ∧ c * d = 0) ∨ (Even n ∧ a * b = 0 ∧ c * d = 1) := by
  unfold accept
  constructor
  · intro h
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [pow_one] at h
      have hab : a * b ≤ 1 := by
        have := Nat.mul_le_mul ha hb
        simpa using this
      have hcd : c * d = 0 := by
        have : ((c * d : ℕ) : ℤ) = 0 := by push_cast at h ⊢; linarith
        exact_mod_cast this
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hab with h0 | h0
      · left; exact ⟨h0, hcd⟩
      · right; left; exact ⟨h0, hcd⟩
    · have hx : a * b ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul ha hb
      have hy : c * d ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul hc hd
      exact key h2 hx hy (fun p hp hpn => no_prime_prod hp hpn ha hb)
        (fun p hp hpn => no_prime_prod hp hpn hc hd) (by exact_mod_cast h)
  · have hn0 : n ≠ 0 := by omega
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨he, h1, h2⟩)
    · rw [h1, h2]; simp [zero_pow hn0]
    · rw [h1, h2]; simp
    · rw [h1, h2]; simp [he.neg_one_pow]

/-- Pairs with product zero. -/
def Z (n : ℕ) : Finset (ℕ × ℕ) := (entryPairs n).filter (fun p => pairProduct p = 0)

/-- Pairs with product one. -/
def O (n : ℕ) : Finset (ℕ × ℕ) := (entryPairs n).filter (fun p => pairProduct p = 1)

lemma card_Z (n : ℕ) : (Z n).card = 2 * n + 1 := by
  have : Z n = (Finset.range (n + 1)).image (fun a => (a, 0)) ∪
      (Finset.range n).image (fun b => (0, b + 1)) := by
    ext ⟨a, b⟩
    simp only [Z, entryPairs, pairProduct, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, Finset.mem_union, Finset.mem_image, Prod.mk.injEq, mul_eq_zero]
    constructor
    · rintro ⟨⟨ha, hb⟩, h | h⟩
      · rcases Nat.eq_zero_or_pos b with hb0 | hb0
        · left; exact ⟨a, ha, rfl, hb0.symm⟩
        · right; exact ⟨b - 1, by omega, h.symm, by omega⟩
      · left; exact ⟨a, ha, rfl, h.symm⟩
    · rintro (⟨x, hx, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩)
      · exact ⟨⟨hx, by omega⟩, Or.inr rfl⟩
      · exact ⟨⟨by omega, by omega⟩, Or.inl rfl⟩
  rw [this, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h),
      Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
    simp; ring
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    rintro _ ⟨x, _, rfl⟩ y _ h
    simp only [Prod.mk.injEq] at h
    omega

lemma O_eq (n : ℕ) (hn : 1 ≤ n) : O n = {(1, 1)} := by
  ext ⟨a, b⟩
  simp only [O, entryPairs, pairProduct, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Finset.mem_singleton, Prod.mk.injEq, mul_eq_one]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨rfl, rfl⟩; exact ⟨⟨by omega, by omega⟩, rfl, rfl⟩

lemma matrices_eq (n : ℕ) (hn : 1 ≤ n) :
    matrices n = (Z n ×ˢ Z n ∪ O n ×ˢ Z n) ∪ (if Even n then Z n ×ˢ O n else ∅) := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
  have key := fun (ha : a < n + 1) (hb : b < n + 1) (hc : c < n + 1) (hd : d < n + 1) =>
    accept_iff (a := a) (b := b) (c := c) (d := d) hn (by omega) (by omega) (by omega) (by omega)
  rw [matrices, Finset.mem_filter]
  split_ifs with he
  · simp only [Z, O, Finset.mem_union, Finset.mem_product, Finset.mem_filter]
    simp only [entryPairs, pairProduct, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hc, hd⟩, h⟩
      rcases (key ha hb hc hd).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨-, h1, h2⟩
      · exact Or.inl (Or.inl ⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩)
      · exact Or.inl (Or.inr ⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩)
      · exact Or.inr ⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩
    · rintro ((⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩ | ⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩) |
        ⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩)
      · exact ⟨⟨⟨ha, hb⟩, hc, hd⟩, (key ha hb hc hd).mpr (Or.inl ⟨h1, h2⟩)⟩
      · exact ⟨⟨⟨ha, hb⟩, hc, hd⟩, (key ha hb hc hd).mpr (Or.inr (Or.inl ⟨h1, h2⟩))⟩
      · exact ⟨⟨⟨ha, hb⟩, hc, hd⟩, (key ha hb hc hd).mpr (Or.inr (Or.inr ⟨he, h1, h2⟩))⟩
  · simp only [Z, O, Finset.mem_union, Finset.mem_product, Finset.mem_filter,
      Finset.notMem_empty, or_false]
    simp only [entryPairs, pairProduct, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hc, hd⟩, h⟩
      rcases (key ha hb hc hd).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨he', h1, h2⟩
      · exact Or.inl ⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩
      · exact Or.inr ⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩
      · exact absurd he' he
    · rintro (⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩ | ⟨⟨⟨ha, hb⟩, h1⟩, ⟨hc, hd⟩, h2⟩)
      · exact ⟨⟨⟨ha, hb⟩, hc, hd⟩, (key ha hb hc hd).mpr (Or.inl ⟨h1, h2⟩)⟩
      · exact ⟨⟨⟨ha, hb⟩, hc, hd⟩, (key ha hb hc hd).mpr (Or.inr (Or.inl ⟨h1, h2⟩))⟩

lemma a_formula (n : ℕ) (hn : 1 ≤ n) :
    a n = (2 * n + 1) ^ 2 + (2 * n + 1) + (if Even n then 2 * n + 1 else 0) := by
  have hZO : Disjoint (Z n) (O n) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Z, O, Finset.mem_filter] at h1 h2
    omega
  unfold a
  rw [matrices_eq n hn]
  have hd1 : Disjoint (Z n ×ˢ Z n) (O n ×ˢ Z n) :=
    Finset.disjoint_product.mpr (Or.inl hZO)
  split_ifs with he
  · have hd2 : Disjoint (Z n ×ˢ Z n ∪ O n ×ˢ Z n) (Z n ×ˢ O n) := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_product.mpr (Or.inr hZO),
        Finset.disjoint_product.mpr (Or.inr hZO)⟩
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
    simp only [Finset.card_product, card_Z, O_eq n hn, Finset.card_singleton]
    ring
  · rw [Finset.union_empty, Finset.card_union_of_disjoint hd1]
    simp only [Finset.card_product, card_Z, O_eq n hn, Finset.card_singleton]
    ring

lemma a_zero : a 0 = 0 := by
  unfold a matrices
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
  simp only [entryPairs, Finset.mem_product, Finset.mem_range] at h
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := h
  obtain rfl : a = 0 := by omega
  obtain rfl : b = 0 := by omega
  obtain rfl : c = 0 := by omega
  obtain rfl : d = 0 := by omega
  simp [accept, pairProduct]

lemma a_even (n : ℕ) (hn : 0 < n) (he : Even n) : a n = 4 * n ^ 2 + 8 * n + 3 := by
  rw [a_formula n hn, if_pos he]; ring

lemma a_odd (n : ℕ) (ho : Odd n) : a n = 4 * n ^ 2 + 6 * n + 2 := by
  have hn : 1 ≤ n := ho.pos
  rw [a_formula n hn, if_neg (Nat.not_even_iff_odd.mpr ho)]; ring

end OMA.P280364

namespace OMA.P280364

open OMA.S_oeis_a280364 PowerSeries

lemma rec_eq (n : ℕ) (hn : 5 < n) : (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) -
    a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega]
  rw [a_formula (m + 6) (by omega), a_formula (m + 5) (by omega), a_formula (m + 4) (by omega),
    a_formula (m + 3) (by omega), a_formula (m + 2) (by omega), a_formula (m + 1) (by omega)]
  rcases Nat.even_or_odd m with hm | hm
  · have h1 : ¬ Even (m + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hm
    have h2 : Even (m + 2) := by rw [Nat.even_add]; simp [hm]
    have h3 : ¬ Even (m + 3) := by rw [Nat.even_add]; simp [hm]; decide
    have h4 : Even (m + 4) := by rw [Nat.even_add]; simp [hm]; decide
    have h5 : ¬ Even (m + 5) := by rw [Nat.even_add]; simp [hm]; decide
    have h6 : Even (m + 6) := by rw [Nat.even_add]; simp [hm]; decide
    rw [if_neg h1, if_pos h2, if_neg h3, if_pos h4, if_neg h5, if_pos h6]
    push_cast; ring
  · have hm' : ¬ Even m := Nat.not_even_iff_odd.mpr hm
    have h1 : Even (m + 1) := by rw [Nat.even_add_one]; exact hm'
    have h2 : ¬ Even (m + 2) := by rw [Nat.even_add]; simp [hm']
    have h3 : Even (m + 3) := by rw [Nat.even_add]; simp [hm']; decide
    have h4 : ¬ Even (m + 4) := by rw [Nat.even_add]; simp [hm']; decide
    have h5 : Even (m + 5) := by rw [Nat.even_add]; simp [hm']; decide
    have h6 : ¬ Even (m + 6) := by rw [Nat.even_add]; simp [hm']; decide
    rw [if_pos h1, if_neg h2, if_pos h3, if_neg h4, if_pos h5, if_neg h6]
    push_cast; ring

lemma ogf_mul :
    ogf * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      X * (12 + 23 * X - 3 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4) := by
  have hl : ogf * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      ogf - ogf * X ^ 1 - C (2 : ℚ) * (ogf * X ^ 2) + C (2 : ℚ) * (ogf * X ^ 3) +
        ogf * X ^ 4 - ogf * X ^ 5 := by
    rw [map_ofNat]; ring
  have hr : (X : PowerSeries ℚ) * (12 + 23 * X - 3 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4) =
      C (12 : ℚ) * X ^ 1 + C (23 : ℚ) * X ^ 2 - C (3 : ℚ) * X ^ 3 - C (3 : ℚ) * X ^ 4 +
        C (3 : ℚ) * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C_mul_X_pow, coeff_C, ogf, coeff_mk]
  have v1 : a 1 = 12 := by rw [a_odd 1 (by decide)]; norm_num
  have v2 : a 2 = 35 := by rw [a_even 2 (by norm_num) (by decide)]; norm_num
  have v3 : a 3 = 56 := by rw [a_odd 3 (by decide)]; norm_num
  have v4 : a 4 = 99 := by rw [a_even 4 (by norm_num) (by decide)]; norm_num
  have v5 : a 5 = 132 := by rw [a_odd 5 (by decide)]; norm_num
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [a_zero, v1, v2, v3, v4, v5] <;> norm_num
  · have hr := rec_eq n (by omega)
    have hq : (a n : ℚ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
      exact_mod_cast hr
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    have d1 : n ≠ 1 := by omega
    have d2 : n ≠ 2 := by omega
    have d3 : n ≠ 3 := by omega
    have d4 : n ≠ 4 := by omega
    have d5 : n ≠ 5 := by omega
    have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    have e3 : n - 3 ≠ 0 := by omega
    have e4 : n - 4 ≠ 0 := by omega
    have e5 : n - 5 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, c5, d1, d2, d3, d4, d5, e1, e2, e3, e4, e5, if_true, if_false]
    rw [hq]; ring

theorem main_proof :
    (∀ n : ℕ, 0 < n → Even n → a n = 4 * n ^ 2 + 8 * n + 3) ∧
    (∀ n : ℕ, Odd n → a n = 4 * n ^ 2 + 6 * n + 2) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = (a (n - 1) : ℤ) + 2 * (a (n - 2) : ℤ) -
      2 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ) + (a (n - 5) : ℤ)) ∧
    (let X : PowerSeries ℚ := PowerSeries.X;
      ogf = X * (12 + 23 * X - 3 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4) *
        (((1 - X) ^ 3 * (1 + X) ^ 2)⁻¹)) := by
  refine ⟨a_even, a_odd, rec_eq, ?_⟩
  intro X
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp [X])]
  exact ogf_mul

end OMA.P280364

theorem OMA.solution : type_of% @OMA.S_oeis_a280364.main := OMA.P280364.main_proof
