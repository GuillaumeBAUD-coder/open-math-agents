import OMAStatements.S_oeis_a003625
import Mathlib

/- A root of X^2 + X + 2 mod an odd prime p exists iff -7 is a square (complete the square),
   and by quadratic reciprocity (-7 / p) = (p / 7), which is 1 exactly for p mod 7 in {1, 2, 4}.
   The primes 2 and 7 have the roots 0 and 3. -/

open Polynomial

instance oma_fact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem oma_roots (p : ℕ) [Fact p.Prime] :
    Irreducible ((X : (ZMod p)[X]) ^ 2 + X + 2) ↔ ∀ x : ZMod p, x ^ 2 + x + 2 ≠ 0 := by
  have hdeg : ((X : (ZMod p)[X]) ^ 2 + X + 2).natDegree = 2 := by compute_degree!
  have hne : ((X : (ZMod p)[X]) ^ 2 + X + 2) ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  constructor
  · intro h x hx
    have : x ∈ ((X : (ZMod p)[X]) ^ 2 + X + 2).roots := by
      rw [mem_roots hne]; simp [hx]
    rw [h] at this; simp at this
  · intro h
    refine Multiset.eq_zero_of_forall_notMem fun x hx => h x ?_
    rw [mem_roots hne] at hx; simpa using hx

theorem oma_square (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) :
    (∃ x : ZMod p, x ^ 2 + x + 2 = 0) ↔ IsSquare (((-7 : ℤ)) : ZMod p) := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this
    exact h2 this
  push_cast
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨2 * x + 1, by linear_combination (-4 : ZMod p) * hx⟩
  · rintro ⟨y, hy⟩
    have hi : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ htwo
    refine ⟨(y - 1) * 2⁻¹, ?_⟩
    linear_combination (-(2 : ZMod p)⁻¹ ^ 2) * hy - (2⁻¹ * y + 3 * 2⁻¹ + 2) * hi

theorem oma_legendre (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) (_h7 : p ≠ 7) :
    legendreSym p (-7) = legendreSym 7 ((p % 7 : ℕ) : ℤ) := by
  have hodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd Fact.out).resolve_left h2
  have hm : legendreSym p (-7) = legendreSym p (-1) * legendreSym p 7 := by
    rw [← legendreSym.mul]; norm_num
  have hq := legendreSym.quadratic_reciprocity' (p := 7) (q := p) (by norm_num) h2
  rw [hm, legendreSym.at_neg_one h2, ZMod.χ₄_eq_neg_one_pow hodd]
  push_cast at hq
  rw [hq]
  have h4 : ((-1 : ℤ) ^ (p / 2)) * (-1) ^ (7 / 2 * (p / 2)) = 1 := by
    rw [← pow_add, show p / 2 + 7 / 2 * (p / 2) = 2 * (2 * (p / 2)) by omega, pow_mul]; norm_num
  rw [← mul_assoc, h4, one_mul, legendreSym.mod]
  push_cast
  rfl

theorem OMA.solution : type_of% @OMA.S_oeis_a003625.main := by
  intro p hp
  rw [oma_roots]
  by_cases h2 : p = 2
  · subst h2
    simp only [show (2 : ℕ) % 7 = 2 by norm_num]
    constructor
    · rintro (h | h | h) <;> omega
    · intro h; exact (h 0 (by rfl)).elim
  by_cases h7 : p = 7
  · subst h7
    constructor
    · rintro (h | h | h) <;> omega
    · intro h; exact (h 3 (by rfl)).elim
  have hsq : (∀ x : ZMod p, x ^ 2 + x + 2 ≠ 0) ↔ ¬ IsSquare (((-7 : ℤ)) : ZMod p) := by
    rw [← oma_square p h2]; push Not; rfl
  have hnz : (((-7 : ℤ)) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have : (p : ℤ) ∣ 7 := by simpa using h
    have h' : p ∣ 7 := by exact_mod_cast this
    exact h7 ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp h')
  rw [hsq, ← legendreSym.eq_one_iff p hnz, oma_legendre p h2 h7]
  have hr : p % 7 ≠ 0 := by
    intro h
    have : 7 ∣ p := Nat.dvd_of_mod_eq_zero h
    exact h7 ((Nat.prime_dvd_prime_iff_eq (by norm_num) (Fact.out)).mp this).symm
  have hlt : p % 7 < 7 := Nat.mod_lt _ (by norm_num)
  generalize p % 7 = r at hr hlt ⊢
  interval_cases r <;> first | (exfalso; omega) | decide
