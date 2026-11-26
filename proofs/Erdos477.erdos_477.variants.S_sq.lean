import FormalConjectures.ErdosProblems.«477»

/-!
# No additive complement for the squares

This is the case `a = 1`, `k = 0`, `c = 0` of the following argument for
`g x = a * x ^ 2 + a * k * x + c`.

* Every multiple of `4 * a` is a difference of two values of `g`: for `k = 2 * j` use
  `g (x + 2) - g x = 4 * a * (x + 1 + j)`, and for `k = 2 * j + 1` use
  `g (x + 1) - g x = 2 * a * (x + j + 1)`.
* So if two distinct elements of `A` are congruent modulo `4 * a`, some integer has two
  representations.
* Otherwise `A` is finite. The values of `g` are bounded on one side (below if `a > 0`, above if
  `a < 0`), so `A + g(ℤ)` is bounded on that side and some integer has no representation.
-/

namespace OMA.E477

/-- Every multiple of `4 * a` is a difference of two values of `a * x ^ 2 + a * k * x + c`. -/
lemma exists_diff (a k c t : ℤ) :
    ∃ x y : ℤ, (a * x ^ 2 + a * k * x + c) - (a * y ^ 2 + a * k * y + c) = 4 * a * t := by
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · refine ⟨t - 1 - j + 2, t - 1 - j, ?_⟩
    subst hj
    ring
  · refine ⟨2 * t - j - 1 + 1, 2 * t - j - 1, ?_⟩
    subst hj
    ring

/-- The values of `a * x ^ 2 + a * k * x + c` stay on one side of `c - a * k ^ 2`. -/
lemma value_bound (a k c x : ℤ) :
    (0 < a → c - a * k ^ 2 ≤ a * x ^ 2 + a * k * x + c) ∧
      (a < 0 → a * x ^ 2 + a * k * x + c ≤ c - a * k ^ 2) := by
  have h : 0 ≤ x ^ 2 + k * x + k ^ 2 := by nlinarith [sq_nonneg (2 * x + k), sq_nonneg k]
  constructor
  · intro ha
    nlinarith [mul_nonneg ha.le h]
  · intro ha
    nlinarith [mul_nonneg (neg_nonneg.2 ha.le) h]

/-- The core statement, for the function `g x = a * x ^ 2 + a * k * x + c`. -/
lemma core (a k c : ℤ) (ha : a ≠ 0) (R : Set ℤ)
    (hR : ∀ r, r ∈ R ↔ ∃ x : ℤ, a * x ^ 2 + a * k * x + c = r) (A : Set ℤ) :
    ∃ z, ¬ ∃! p ∈ A ×ˢ R, z = p.1 + p.2 := by
  by_cases h : ∃ a1 ∈ A, ∃ a2 ∈ A, a1 ≠ a2 ∧ (4 * a) ∣ (a1 - a2)
  · obtain ⟨a1, h1, a2, h2, hne, t, ht⟩ := h
    obtain ⟨x, y, hxy⟩ := exists_diff a k c t
    refine ⟨a1 + (a * y ^ 2 + a * k * y + c), ?_⟩
    rintro ⟨p, -, huniq⟩
    have e1 := huniq (a1, a * y ^ 2 + a * k * y + c) ⟨⟨h1, (hR _).2 ⟨y, rfl⟩⟩, rfl⟩
    have e2 := huniq (a2, a * x ^ 2 + a * k * x + c)
      ⟨⟨h2, (hR _).2 ⟨x, rfl⟩⟩, by simp only; linarith⟩
    have : a1 = a2 := congrArg Prod.fst (e1.trans e2.symm)
    exact hne this
  · have h' : ∀ a1 ∈ A, ∀ a2 ∈ A, (4 * a) ∣ (a1 - a2) → a1 = a2 := by
      intro a1 h1 a2 h2 hd
      by_contra hne
      exact h ⟨a1, h1, a2, h2, hne, hd⟩
    have h4a : (4 * a) ≠ 0 := mul_ne_zero (by norm_num) ha
    have hfin : A.Finite := by
      apply Set.Finite.of_finite_image (f := fun x : ℤ => x % (4 * a))
      · apply (Set.finite_Ico (0 : ℤ) |4 * a|).subset
        rintro _ ⟨x, -, rfl⟩
        exact ⟨Int.emod_nonneg x h4a, Int.emod_lt_abs x h4a⟩
      · intro a1 h1 a2 h2 he
        have hd : (4 * a) ∣ (a2 - a1) := Int.ModEq.dvd he
        exact (h' a2 h2 a1 h1 hd).symm
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · obtain ⟨M, hM⟩ := hfin.bddAbove
      refine ⟨M + (c - a * k ^ 2) + 1, ?_⟩
      rintro ⟨p, ⟨⟨hp1, hp2⟩, hz⟩, -⟩
      obtain ⟨x, hx⟩ := (hR _).1 hp2
      have b1 := hM hp1
      have b2 := (value_bound a k c x).2 hneg
      rw [hx] at b2
      linarith
    · obtain ⟨m, hm⟩ := hfin.bddBelow
      refine ⟨m + (c - a * k ^ 2) - 1, ?_⟩
      rintro ⟨p, ⟨⟨hp1, hp2⟩, hz⟩, -⟩
      obtain ⟨x, hx⟩ := (hR _).1 hp2
      have b1 := hm hp1
      have b2 := (value_bound a k c x).1 hpos
      rw [hx] at b2
      linarith

end OMA.E477

open Polynomial

theorem OMA.solution : type_of% @Erdos477.erdos_477.variants.S_sq := by
  intro A
  refine OMA.E477.core 1 0 0 one_ne_zero _ (fun r => ?_) A
  simp
