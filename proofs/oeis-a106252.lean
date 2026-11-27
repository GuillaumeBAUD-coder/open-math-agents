import OMAStatements.S_oeis_a106252
import Mathlib

/-!
# OEIS A106252: triples `x ≤ y ≤ z ≤ n` where each number divides the sum of the other two

We classify the triples and count them: `a n = n + ⌊n/2⌋ + ⌊n/3⌋`. The conjectured relation
`a (n + 7) - a (n + 6) = a (n + 1) - a n` then follows by arithmetic.

**Classification.** Let `1 ≤ x ≤ y ≤ z`. Since `z ∣ x + y` and `0 < x + y ≤ 2 z`, either
`x + y = 2 z`, which forces `x = y = z`, or `x + y = z`. In the second case `y ∣ x + z = 2 x + y`
gives `y ∣ 2 x`, and `2 x ≤ 2 y` leaves `y = 2 x` or `y = x`. So the triples are exactly

  `(k, k, k)`,   `(k, k, 2 k)`,   `(k, 2 k, 3 k)`,

and all of these do satisfy the three divisibility conditions.
-/

open OMA.S_oeis_a106252

namespace OMA.A106252

/-- The classification of the triples. -/
lemma mem_triples_iff (n x y z : ℕ) :
    (x, y, z) ∈ triples n ↔
      1 ≤ x ∧ z ≤ n ∧ ((y = x ∧ z = x) ∨ (y = x ∧ z = 2 * x) ∨ (y = 2 * x ∧ z = 3 * x)) := by
  simp only [triples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hx1, hxn⟩, ⟨hy1, hyn⟩, ⟨hz1, hzn⟩⟩, hxy, hyz, -, hy, hz⟩
    refine ⟨hx1, hzn, ?_⟩
    -- `z ∣ x + y` and `0 < x + y ≤ 2 z`, so `x + y = z` or `x + y = 2 z`
    obtain ⟨c, hc⟩ := hz
    have hc12 : c = 1 ∨ c = 2 := by
      have hc0 : c ≠ 0 := by rintro rfl; omega
      have hc2 : c ≤ 2 := by
        by_contra h
        have : z * 3 ≤ z * c := Nat.mul_le_mul_left z (by omega)
        omega
      omega
    rcases hc12 with rfl | rfl
    · -- `x + y = z`: then `y ∣ 2 x`, so `2 x = y` or `2 x = 2 y`
      have hz' : z = x + y := by omega
      subst hz'
      have hy2 : y ∣ 2 * x := by
        have h2 : x + (x + y) = 2 * x + y := by ring
        rw [h2] at hy
        exact (Nat.dvd_add_iff_left (dvd_refl y)).2 hy
      obtain ⟨d, hd⟩ := hy2
      have hd12 : d = 1 ∨ d = 2 := by
        have hd0 : d ≠ 0 := by rintro rfl; omega
        have hd2 : d ≤ 2 := by
          by_contra h
          have : y * 3 ≤ y * d := Nat.mul_le_mul_left y (by omega)
          omega
        omega
      rcases hd12 with rfl | rfl
      · right; right; omega
      · right; left; omega
    · -- `x + y = 2 z`: then `x = y = z`
      left; omega
  · rintro ⟨hx1, hzn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨⟨⟨hx1, hzn⟩, ⟨hx1, hzn⟩, ⟨hx1, hzn⟩⟩, le_rfl, le_rfl,
        ⟨2, by ring⟩, ⟨2, by ring⟩, ⟨2, by ring⟩⟩
    · exact ⟨⟨⟨hx1, by omega⟩, ⟨hx1, by omega⟩, ⟨by omega, hzn⟩⟩, le_rfl, by omega,
        ⟨3, by ring⟩, ⟨3, by ring⟩, ⟨1, by ring⟩⟩
    · exact ⟨⟨⟨hx1, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, hzn⟩⟩, by omega, by omega,
        ⟨5, by ring⟩, ⟨2, by ring⟩, ⟨1, by ring⟩⟩

/-- The three families of triples. -/
def fam1 (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (Finset.Icc 1 n).image fun k => (k, k, k)

def fam2 (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (Finset.Icc 1 (n / 2)).image fun k => (k, k, 2 * k)

def fam3 (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (Finset.Icc 1 (n / 3)).image fun k => (k, 2 * k, 3 * k)

lemma triples_eq (n : ℕ) : triples n = fam1 n ∪ (fam2 n ∪ fam3 n) := by
  ext ⟨x, y, z⟩
  rw [mem_triples_iff]
  simp only [fam1, fam2, fam3, Finset.mem_union, Finset.mem_image, Finset.mem_Icc,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hx1, hzn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨_, ⟨hx1, hzn⟩, rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨_, ⟨hx1, by omega⟩, rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, ⟨hx1, by omega⟩, rfl, rfl, rfl⟩)
  · rintro (⟨k, ⟨hk1, hkn⟩, rfl, rfl, rfl⟩ | ⟨k, ⟨hk1, hkn⟩, rfl, rfl, rfl⟩ |
      ⟨k, ⟨hk1, hkn⟩, rfl, rfl, rfl⟩)
    · exact ⟨hk1, hkn, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hk1, by omega, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨hk1, by omega, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

lemma card_fam1 (n : ℕ) : (fam1 n).card = n := by
  rw [fam1, Finset.card_image_of_injective _ (fun a b h => by
    simp only [Prod.mk.injEq] at h; exact h.1)]
  simp

lemma card_fam2 (n : ℕ) : (fam2 n).card = n / 2 := by
  rw [fam2, Finset.card_image_of_injective _ (fun a b h => by
    simp only [Prod.mk.injEq] at h; exact h.1)]
  simp

lemma card_fam3 (n : ℕ) : (fam3 n).card = n / 3 := by
  rw [fam3, Finset.card_image_of_injective _ (fun a b h => by
    simp only [Prod.mk.injEq] at h; exact h.1)]
  simp

lemma disjoint_fam2_fam3 (n : ℕ) : Disjoint (fam2 n) (fam3 n) := by
  rw [Finset.disjoint_left]
  intro t h2 h3
  simp only [fam2, fam3, Finset.mem_image, Finset.mem_Icc] at h2 h3
  obtain ⟨k, hk, rfl⟩ := h2
  obtain ⟨j, hj, h⟩ := h3
  simp only [Prod.mk.injEq] at h
  omega

lemma disjoint_fam1 (n : ℕ) : Disjoint (fam1 n) (fam2 n ∪ fam3 n) := by
  rw [Finset.disjoint_left]
  intro t h1 h23
  simp only [fam1, fam2, fam3, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at h1 h23
  obtain ⟨k, hk, rfl⟩ := h1
  rcases h23 with ⟨j, hj, h⟩ | ⟨j, hj, h⟩ <;>
  · simp only [Prod.mk.injEq] at h
    omega

/-- The count: `a n = n + ⌊n/2⌋ + ⌊n/3⌋`. -/
theorem a_eq (n : ℕ) : a n = n + n / 2 + n / 3 := by
  rw [a, triples_eq, Finset.card_union_of_disjoint (disjoint_fam1 n),
    Finset.card_union_of_disjoint (disjoint_fam2_fam3 n), card_fam1, card_fam2, card_fam3]
  ring

end OMA.A106252

open OMA.A106252 in
theorem OMA.solution : type_of% @OMA.S_oeis_a106252.main := by
  intro n
  rw [a_eq, a_eq, a_eq, a_eq]
  omega
