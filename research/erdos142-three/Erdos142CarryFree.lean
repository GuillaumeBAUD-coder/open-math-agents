import FormalConjectures.ErdosProblems.«142»

/-!
# A classical product construction for the three-term variant of Erdos problem 142

Partial contribution for `Erdos142.erdos_142.variants.three`.
The original asymptotic-equivalence problem is not asserted here.

For positive m, the principal theorem `r_product_le` proves
`r 3 m * r 3 n <= r 3 ((2*m-1)*(n-1)+m)`.
Its iteration `r_pow_le` proves
`(r 3 m)^d <= r 3 (((2*m-1)^d+1)/2)` for every natural d.
All occurrences of r in these conclusions are the original upstream definition.

The construction is classical. The ternary digit construction is described in
the footnote on p. 263 of Erdos and Turan, On Some Sequences of Integers (1936).
The corollary `ternary_lower` formalizes its resulting lower bound:
https://www.renyi.hu/~p_erdos/1936-05.pdf
No new extremal values or asymptotic estimates are claimed.

Compatibility arguments below adapt already merged open-math-agents proofs;
these are explicitly distinguished from the product contribution.
-/

namespace Erdos142CarryFree

open Finset

/- The following compatibility lemmas re-express existing arguments in
reductions/Erdos142.erdos_142.variants.lower.R3.lean and
proofs/Erdos142.erdos_142.variants.lower.R3.H1.lean.
They are supporting infrastructure, not claimed as a new contribution. -/

theorem apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) =
        {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact hterms i (mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

theorem apFree_three_iff (A : Set ℕ) :
    A.IsAPOfLengthFree (3 : ℕ) ↔ ThreeAPFree A := by
  rw [apFree_iff (by norm_num)]
  constructor
  · intro h a ha b hb c hc habc
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · apply h ⟨a, b - a, by omega, ?_⟩
      intro i hi
      interval_cases i
      · simpa using ha
      · have he : a + 1 * (b - a) = b := by omega
        rwa [he]
      · have he : a + 2 * (b - a) = c := by omega
        rwa [he]
    · apply h ⟨c, b - c, by omega, ?_⟩
      intro i hi
      interval_cases i
      · simpa using hc
      · have he : c + 1 * (b - c) = b := by omega
        rwa [he]
      · have he : c + 2 * (b - c) = a := by omega
        rwa [he]
  · rintro h ⟨a, d, hd, hterms⟩
    have h0 := hterms 0 (by norm_num)
    have h1 := hterms 1 (by norm_num)
    have h2 := hterms 2 (by norm_num)
    have he := h h0 h1 h2 (by omega)
    omega

/-- The upstream one-based extremal number equals Mathlib's zero-based one. -/
theorem r_eq_rothNumberNat (N : ℕ) : Erdos142.r 3 N = rothNumberNat N := by
  have hmax : Erdos142.r 3 N = addRothNumber (Icc 1 N) := by
    unfold Erdos142.r Set.IsAPOfLengthFree.maxCard
    apply le_antisymm
    · apply csSup_le'
      rintro _ ⟨S, hS, hf, rfl⟩
      exact ((apFree_three_iff _).mp hf).le_addRothNumber hS
    · obtain ⟨S, hS, hc, hf⟩ := addRothNumber_spec (Icc 1 N)
      refine le_csSup ?_ ⟨S, hS, (apFree_three_iff _).mpr hf, hc⟩
      refine ⟨N, ?_⟩
      rintro _ ⟨T, hT, -, rfl⟩
      simpa using card_le_card hT
  have hI : Icc 1 N = Ico 1 (N + 1) := by
    ext x
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hmax, hI, addRothNumber_Ico]
  simp

end Erdos142CarryFree

/-
# Carry-free products of three-term-progression-free sets

This is the classical elementary digit construction, not a new asymptotic bound.
The radix `2 * m - 1` exceeds every sum of two digits in `range m`.
Consequently equality of two encoded two-term sums determines their low-digit
sums, and then their high-digit sums.  This makes the encoding preserve
three-term-progression freeness, with the uniform endpoint for this encoding.
-/

namespace Erdos142CarryFree

open Finset

/-- Encode a low digit in `range m` and a high digit using radix `2*m-1`. -/
def encode (m : ℕ) (p : ℕ × ℕ) : ℕ := p.1 + (2 * m - 1) * p.2

/-- Equality of encoded progression sums separates into the two digit equations. -/
theorem no_carry_sums {m a b c d e f : ℕ}
    (hm : 0 < m) (ha : a < m) (hc : c < m) (he : e < m)
    (hxyz : (a + (2 * m - 1) * b) + (e + (2 * m - 1) * f) =
      (c + (2 * m - 1) * d) + (c + (2 * m - 1) * d)) :
    a + e = c + c ∧ b + f = d + d := by
  have hk : 0 < 2 * m - 1 := by omega
  have hae : a + e < 2 * m - 1 := by omega
  have hcc : c + c < 2 * m - 1 := by omega
  have hsum : (a + e) + (2 * m - 1) * (b + f) =
      (c + c) + (2 * m - 1) * (d + d) := by
    simp only [Nat.mul_add]
    omega
  have hlow : a + e = c + c := by
    have hmod := congrArg (fun x : ℕ ↦ x % (2 * m - 1)) hsum
    simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hae, Nat.mod_eq_of_lt hcc]
      using hmod
  have hhigh : b + f = d + d := by
    rw [hlow] at hsum
    exact Nat.eq_of_mul_eq_mul_left hk (Nat.add_left_cancel hsum)
  exact ⟨hlow, hhigh⟩

theorem encode_injOn {m : ℕ} (hm : 0 < m) {A B : Finset ℕ}
    (hA : A ⊆ range m) : Set.InjOn (encode m) (A ×ˢ B : Finset (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  have ha : a < m := mem_range.mp (hA (mem_product.mp hab).1)
  have hc : c < m := mem_range.mp (hA (mem_product.mp hcd).1)
  have hk : 0 < 2 * m - 1 := by omega
  have ha' : a < 2 * m - 1 := by omega
  have hc' : c < 2 * m - 1 := by omega
  change a + (2 * m - 1) * b = c + (2 * m - 1) * d at heq
  have hac : a = c := by
    have hmod := congrArg (fun x : ℕ ↦ x % (2 * m - 1)) heq
    simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hc']
      using hmod
  have hbd : b = d := by
    rw [hac] at heq
    exact Nat.eq_of_mul_eq_mul_left hk (Nat.add_left_cancel heq)
  exact Prod.ext hac hbd

theorem threeAPFree_encoded_product {m : ℕ} (hm : 0 < m) {A B : Finset ℕ}
    (hA : A ⊆ range m) (hAf : ThreeAPFree (A : Set ℕ))
    (hBf : ThreeAPFree (B : Set ℕ)) :
    ThreeAPFree (((A ×ˢ B).image (encode m)) : Set ℕ) := by
  rintro x hx y hy z hz hxyz
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hx
  obtain ⟨⟨c, d⟩, hcd, rfl⟩ := mem_image.mp hy
  obtain ⟨⟨e, f⟩, hef, rfl⟩ := mem_image.mp hz
  obtain ⟨haA, hbB⟩ := mem_product.mp hab
  obtain ⟨hcA, hdB⟩ := mem_product.mp hcd
  obtain ⟨heA, hfB⟩ := mem_product.mp hef
  have ha : a < m := mem_range.mp (hA haA)
  have hc : c < m := mem_range.mp (hA hcA)
  have he : e < m := mem_range.mp (hA heA)
  change (a + (2 * m - 1) * b) + (e + (2 * m - 1) * f) =
    (c + (2 * m - 1) * d) + (c + (2 * m - 1) * d) at hxyz
  obtain ⟨hlow, hhigh⟩ := no_carry_sums hm ha hc he hxyz
  have hac : a = c := hAf haA hcA heA hlow
  have hbd : b = d := hBf hbB hdB hfB hhigh
  change a + (2 * m - 1) * b = c + (2 * m - 1) * d
  rw [hac, hbd]

theorem encoded_product_card {m : ℕ} (hm : 0 < m) {A B : Finset ℕ}
    (hA : A ⊆ range m) :
    ((A ×ˢ B).image (encode m)).card = A.card * B.card := by
  rw [card_image_of_injOn (encode_injOn hm hA), card_product]

theorem encoded_product_subset {m n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range m) (hB : B ⊆ range n) :
    (A ×ˢ B).image (encode m) ⊆ range ((2 * m - 1) * (n - 1) + m) := by
  intro x hx
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hx
  have ha : a < m := mem_range.mp (hA (mem_product.mp hab).1)
  have hb : b < n := mem_range.mp (hB (mem_product.mp hab).2)
  have hb' : b ≤ n - 1 := by omega
  have hmul := Nat.mul_le_mul_left (2 * m - 1) hb'
  apply mem_range.mpr
  change a + (2 * m - 1) * b < (2 * m - 1) * (n - 1) + m
  omega

/-- The digit product gives an explicit set, its size, and a uniform ambient interval bound. -/
theorem product_construction {m n : ℕ} (hm : 0 < m) {A B : Finset ℕ}
    (hA : A ⊆ range m) (hB : B ⊆ range n)
    (hAf : ThreeAPFree (A : Set ℕ)) (hBf : ThreeAPFree (B : Set ℕ)) :
    ∃ C : Finset ℕ, C ⊆ range ((2 * m - 1) * (n - 1) + m) ∧
      C.card = A.card * B.card ∧ ThreeAPFree (C : Set ℕ) := by
  exact ⟨(A ×ˢ B).image (encode m), encoded_product_subset hA hB,
    encoded_product_card hm hA, threeAPFree_encoded_product hm hA hAf hBf⟩

/-- Classical product lower bound, expressed using Mathlib's zero-based Roth number. -/
theorem rothNumberNat_product_le {m n : ℕ} (hm : 0 < m) :
    rothNumberNat m * rothNumberNat n ≤ rothNumberNat ((2 * m - 1) * (n - 1) + m) := by
  obtain ⟨A, hA, hAc, hAf⟩ := rothNumberNat_spec m
  obtain ⟨B, hB, hBc, hBf⟩ := rothNumberNat_spec n
  obtain ⟨C, hC, hCc, hCf⟩ := product_construction hm hA hB hAf hBf
  rw [← hAc, ← hBc, ← hCc]
  exact hCf.le_addRothNumber hC

end Erdos142CarryFree

namespace Erdos142CarryFree

/-- The classical carry-free product lower bound for the exact upstream extremal function. -/
theorem r_product_le {m n : ℕ} (hm : 0 < m) :
    Erdos142.r 3 m * Erdos142.r 3 n ≤
      Erdos142.r 3 ((2 * m - 1) * (n - 1) + m) := by
  simpa only [r_eq_rothNumberNat] using rothNumberNat_product_le (n := n) hm

end Erdos142CarryFree

/-
# Iteration of the carry-free product construction

This corollary propagates a finite seed into an infinite sequence of lower bounds.
It is the classical digit construction, not a new asymptotic estimate.
The file is combined with the bridge and product lemmas for submission.
-/

namespace Erdos142CarryFree

/-- Length of the interval occupied by the repeated digit construction. -/
def productSpan (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => (2 * m - 1) * (productSpan m d - 1) + m

theorem productSpan_pos {m : ℕ} (hm : 0 < m) (d : ℕ) :
    0 < productSpan m d := by
  cases d with
  | zero => simp [productSpan]
  | succ d =>
    change 0 < (2 * m - 1) * (productSpan m d - 1) + m
    omega

theorem two_mul_productSpan {m : ℕ} (hm : 0 < m) (d : ℕ) :
    2 * productSpan m d = (2 * m - 1) ^ d + 1 := by
  induction d with
  | zero => simp [productSpan]
  | succ d ih =>
    have hp := productSpan_pos hm d
    have hs : productSpan m d - 1 + 1 = productSpan m d := by omega
    have hradix : (2 * m - 1) + 1 = 2 * m := by omega
    have hs_mul := congrArg (fun x : ℕ => (2 * m - 1) * x) hs
    have ih_mul := congrArg (fun x : ℕ => (2 * m - 1) * x) ih
    change 2 * ((2 * m - 1) * (productSpan m d - 1) + m) =
      (2 * m - 1) ^ (d + 1) + 1
    simp only [Nat.mul_add, Nat.mul_one] at hs_mul ih_mul
    rw [Nat.mul_left_comm (2 * m - 1) 2] at ih_mul
    rw [Nat.pow_succ, Nat.mul_add, Nat.mul_comm ((2 * m - 1) ^ d) (2 * m - 1)]
    omega

theorem productSpan_eq {m : ℕ} (hm : 0 < m) (d : ℕ) :
    productSpan m d = ((2 * m - 1) ^ d + 1) / 2 := by
  have h := two_mul_productSpan hm d
  omega

theorem r_one : Erdos142.r 3 1 = 1 := by
  rw [r_eq_rothNumberNat, rothNumberNat_def, Finset.range_one, addRothNumber_singleton]

theorem r_pow_le_productSpan {m : ℕ} (hm : 0 < m) (d : ℕ) :
    (Erdos142.r 3 m) ^ d ≤ Erdos142.r 3 (productSpan m d) := by
  induction d with
  | zero => simp [productSpan, r_one]
  | succ d ih =>
    calc
      (Erdos142.r 3 m) ^ (d + 1) = Erdos142.r 3 m * (Erdos142.r 3 m) ^ d := by
        rw [Nat.pow_succ, Nat.mul_comm]
      _ ≤ Erdos142.r 3 m * Erdos142.r 3 (productSpan m d) :=
        Nat.mul_le_mul_left _ ih
      _ ≤ Erdos142.r 3 (productSpan m (d + 1)) := by
        exact r_product_le hm

/-- Any certified seed bound propagates through all powers of radix `2*m-1`. -/
theorem r_pow_le {m : ℕ} (hm : 0 < m) (d : ℕ) :
    (Erdos142.r 3 m) ^ d ≤ Erdos142.r 3 (((2 * m - 1) ^ d + 1) / 2) := by
  rw [← productSpan_eq hm d]
  exact r_pow_le_productSpan hm d

/-- A certified seed lower bound propagates to any sufficiently large interval. -/
-- Suggested in coordination note #84603; independently rechecked here.
theorem seed_lower {m k N d : ℕ} (hm : 0 < m)
    (hk : k ≤ Erdos142.r 3 m)
    (hN : (2 * m - 1) ^ d + 1 ≤ 2 * N) :
    k ^ d ≤ Erdos142.r 3 N := by
  calc
    k ^ d ≤ Erdos142.r 3 m ^ d := Nat.pow_le_pow_left hk d
    _ ≤ Erdos142.r 3 (((2 * m - 1) ^ d + 1) / 2) := r_pow_le hm d
    _ ≤ Erdos142.r 3 N := by
      rw [r_eq_rothNumberNat, r_eq_rothNumberNat]
      exact rothNumberNat.mono (by omega)

end Erdos142CarryFree

namespace Erdos142CarryFree

/-- The two-point seed is optimal in an interval of length two. -/
theorem r_two : Erdos142.r 3 2 = 2 := by
  rw [r_eq_rothNumberNat, rothNumberNat_def]
  have h : ThreeAPFree (Finset.range 2 : Set ℕ) := by decide
  simpa using h.addRothNumber_eq

/-- The classical ternary-digit lower bound recorded by Erdős and Turán in 1936. -/
theorem ternary_lower (d : ℕ) :
    2 ^ d ≤ Erdos142.r 3 ((3 ^ d + 1) / 2) := by
  simpa only [r_two, Nat.reduceMul, Nat.reduceSub] using
    r_pow_le (m := 2) (by decide) d

end Erdos142CarryFree

