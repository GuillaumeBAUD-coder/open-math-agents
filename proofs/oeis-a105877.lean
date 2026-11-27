import OMAStatements.S_oeis_a105877
import Mathlib

/-!
# OEIS A105877: primes for which `-5 t²` can be a primitive root

Let `p` be an odd prime and suppose `-5 t²` is a primitive root modulo `p` for some `t`.

**Step 1: `-5` is not a square modulo `p`.** If `-5 = u²`, then `-5 t² = (u t)²`, and raising to
the power `(p - 1) / 2` gives `(u t) ^ (p - 1) = 1` by Fermat's little theorem. A primitive root
has order `p - 1`, so this is impossible.

**Step 2: quadratic reciprocity.** The Legendre symbol is multiplicative, so
`(-5 / p) = (-1 / p) (5 / p)`. Here `(-1 / p)` depends on `p mod 4`, and since `5 ≡ 1 (mod 4)`
reciprocity gives `(5 / p) = (p / 5)`, which depends on `p mod 5`. Going through the residues
of `p` modulo `20`, the product is `-1` exactly for `p ≡ 11, 13, 17, 19 (mod 20)`.

**Step 3.** For those residues the tens digit of `p` is odd.
-/

namespace OMA.A105877

/-- Step 1: a primitive root of the form `-5 t²` forces `-5` to be a non-square. -/
lemma not_isSquare_neg_five {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) {t : ZMod p}
    (ht : IsPrimitiveRoot ((-5 : ZMod p) * t ^ 2) (p - 1)) : ¬ IsSquare (-5 : ZMod p) := by
  rintro ⟨u, hu⟩
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h <;> omega
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by omega
  have hg : (-5 : ZMod p) * t ^ 2 = (u * t) ^ 2 := by rw [hu]; ring
  -- the primitive root is not killed by the exponent `(p - 1) / 2` …
  have hne : ((-5 : ZMod p) * t ^ 2) ^ ((p - 1) / 2) ≠ 1 :=
    ht.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  -- … but a square is
  apply hne
  rw [hg, ← pow_mul, hhalf]
  apply ZMod.pow_card_sub_one_eq_one
  intro h0
  have h1 := ht.pow_eq_one
  rw [hg, h0] at h1
  simp [zero_pow (show p - 1 ≠ 0 by omega)] at h1

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Modulo `5` itself, `-5 = 0` is a square. -/
lemma isSquare_neg_five_mod_five : IsSquare (-5 : ZMod 5) := ⟨0, by decide⟩

/-- The Legendre symbols modulo `5`. -/
lemma legendre_five_four : legendreSym 5 4 = 1 :=
  (legendreSym.eq_one_iff 5 (by decide)).2 ⟨2, by decide⟩

lemma legendre_five_two : legendreSym 5 2 = -1 :=
  (legendreSym.eq_neg_one_iff 5).2 (by rintro ⟨r, hr⟩; revert r; decide)

lemma legendre_five_three : legendreSym 5 3 = -1 :=
  (legendreSym.eq_neg_one_iff 5).2 (by rintro ⟨r, hr⟩; revert r; decide)

/-- Step 2: if `-5` is a non-square modulo the odd prime `p`, then `p ≡ 11, 13, 17, 19 (mod 20)`. -/
lemma mod_twenty {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) (hns : ¬ IsSquare (-5 : ZMod p)) :
    p % 20 = 11 ∨ p % 20 = 13 ∨ p % 20 = 17 ∨ p % 20 = 19 := by
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h <;> omega
  -- `p ≠ 5`, since `-5 = 0` is a square modulo `5`
  have hp5 : p ≠ 5 := by
    rintro rfl
    exact hns isSquare_neg_five_mod_five
  have h5 : p % 5 ≠ 0 := by
    intro h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 (Nat.dvd_of_mod_eq_zero h)).symm
  -- the Legendre symbol of `-5` is `-1`, and it factors
  have hls : legendreSym p (-5) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    push_cast
    exact hns
  have hmul : legendreSym p (-5) = legendreSym p (-1) * legendreSym p 5 := by
    rw [← legendreSym.mul]
    norm_num
  -- `(-1 / p)` from `p mod 4`
  have hneg : legendreSym p (-1) = ZMod.χ₄ p := legendreSym.at_neg_one (by omega)
  -- `(5 / p) = (p / 5)` by reciprocity, and `(p / 5)` depends on `p mod 5`
  have hrec : legendreSym p 5 = legendreSym 5 p := by
    have h := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num)
      (by omega)
    exact_mod_cast h
  have hmod : legendreSym 5 p = legendreSym 5 ((p % 5 : ℕ) : ℤ) := by
    rw [legendreSym.mod 5 (p : ℤ)]
    push_cast
    rfl
  rw [hmul, hneg, hrec, hmod] at hls
  -- go through the residues of `p` modulo `20`
  by_contra hcon
  have hcases : p % 20 = 1 ∨ p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 9 := by omega
  rcases hcases with h | h | h | h
  · have h4 : p % 4 = 1 := by omega
    have h5' : p % 5 = 1 := by omega
    rw [ZMod.χ₄_nat_one_mod_four h4, h5'] at hls
    simp at hls
  · have h4 : p % 4 = 3 := by omega
    have h5' : p % 5 = 3 := by omega
    rw [ZMod.χ₄_nat_three_mod_four h4, h5'] at hls
    simp [legendre_five_three] at hls
  · have h4 : p % 4 = 3 := by omega
    have h5' : p % 5 = 2 := by omega
    rw [ZMod.χ₄_nat_three_mod_four h4, h5'] at hls
    simp [legendre_five_two] at hls
  · have h4 : p % 4 = 1 := by omega
    have h5' : p % 5 = 4 := by omega
    rw [ZMod.χ₄_nat_one_mod_four h4, h5'] at hls
    simp [legendre_five_four] at hls

end OMA.A105877

open OMA.A105877 in
theorem OMA.solution : type_of% @OMA.S_oeis_a105877.main := by
  intro p hp hp2 t ht
  have : Fact p.Prime := ⟨hp⟩
  have h20 := mod_twenty hp2 (not_isSquare_neg_five hp2 ht)
  refine ⟨h20, Nat.odd_iff.2 ?_⟩
  omega
