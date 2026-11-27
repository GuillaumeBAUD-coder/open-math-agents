import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The large-deficit part of Su and Xia, section 8.7, in natural-number arithmetic.
H1 isolates the cubic rate of growth on powers of two. The companion lemma
dyadic_comparison derives it from the weak Sims upper bound and the Higman lower
bound. H2 is the odd-order consequence of Blackburn--Neumann--Venkataraman,
Corollary 16.21. The constant in its cubic exponent is strictly smaller for
odd orders, because all prime divisors are at least three. H3 is the cost of
combining the 2-part and the odd part after prescribing the Sylow types, from
their Theorem 16.20. All constants are uniform in the orders under comparison.
-/

open Filter Finset Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1

/-- Cubic comparison on powers of two with quadratic slack. -/
def H1 : Prop := ∃ C : ℕ, ∀ a m : ℕ, 3 ≤ m → a ≤ m →
  2^(2*m^3) * g (2^a)^27 ≤ g (2^m)^27 * 2^(2*a^3 + C*(m+1)^2)

/-- Odd orders have a smaller cubic exponent. -/
def H2 : Prop := ∃ D : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → g q^27 ≤ 2^(r^3+D)

/-- Uniform quadratic overhead for prescribing the Sylow types. -/
def H3 : Prop := ∃ E : ℕ, ∀ a q m : ℕ, Odd q → 2^a*q < 2^m →
  g (2^a*q)^27 ≤ g (2^a)^27 * g q^27 * 2^(E*(m+1)^2)

/-- A cubic saving absorbs the uniform quadratic cost of choosing compatible Sylow data. -/
theorem cubic_budget {a r C D E : ℕ}
    (hr : 4 * (C + D + E + 27) + 1 ≤ r) :
    27 * (a+r) + 2*a^3 + C*(a+r+1)^2 + r^3 + D + E*(a+r+1)^2 ≤ 2*(a+r)^3 := by
  have hm : 1 ≤ a+r := by omega
  have hh : (a+r+1)^2 ≤ 4*(a+r)^2 := by
    have ht : a+r+1 ≤ 2*(a+r) := by omega
    nlinarith [Nat.pow_le_pow_left ht 2]
  have hs : a+r ≤ (a+r)^2 := by nlinarith [Nat.mul_le_mul_left (a+r) hm]
  have hu : 1 ≤ (a+r)^2 := by omega
  have hsmall := Nat.mul_le_mul_left D hu
  have hbig := Nat.mul_le_mul_right ((a+r)^2) hr
  nlinarith only [Nat.mul_le_mul_left C hh, Nat.mul_le_mul_left E hh,
    Nat.mul_le_mul_left 27 hs, hsmall, hbig, Nat.zero_le (a^2*r), Nat.zero_le (a*r^2),
    Nat.zero_le ((a+r)^2), Nat.zero_le (D*(a+r)^2)]

/-- Comparison on powers of two, odd orders, and the cost of prescribing the Sylow types. -/
theorem large_deficit_of_counts (f : ℕ → ℕ) {C D E : ℕ}
    (dyadic : ∀ a m : ℕ, 3 ≤ m → a ≤ m →
      2^(2*m^3) * f (2^a)^27 ≤ f (2^m)^27 * 2^(2*a^3 + C*(m+1)^2))
    (odd_count : ∀ q r : ℕ, Odd q → q < 2^r → f q ^ 27 ≤ 2^(r^3 + D))
    (mixed : ∀ a q m : ℕ, Odd q → 2^a*q < 2^m →
      f (2^a*q)^27 ≤ f (2^a)^27 * f q^27 * 2^(E*(m+1)^2)) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ k : ℕ in atTop, ∀ n ∈ Ico 1 (2^(k+R)),
      ¬2^k ∣ n → 2^(k+R) * f n ≤ f (2^(k+R)) := by
  let R := 4 * (C+D+E+27) + 1
  refine ⟨R, by dsimp [R]; omega, eventually_atTop.mpr ⟨3, ?_⟩⟩
  intro k hk n hn hdiv
  obtain ⟨hnpos,hnlt⟩ := mem_Ico.mp hn
  obtain ⟨a,q,hodd,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have ha : a < k := by
    by_contra! h
    exact hdiv ((Nat.pow_dvd_pow 2 h).trans (dvd_mul_right _ _))
  let r := k+R-a
  have hsum : a+r = k+R := by dsimp [r]; omega
  have hR : R ≤ r := by dsimp [r]; omega
  rw [← hsum] at hnlt ⊢
  have hq : q < 2^r := by
    rw [pow_add] at hnlt
    exact Nat.lt_of_mul_lt_mul_left hnlt
  let m := a+r
  have hdy := dyadic a m (by dsimp [m]; omega) (by dsimp [m]; omega)
  have ho := odd_count q r hodd hq
  have hmix := mixed a q m hodd hnlt
  have he := cubic_budget (a := a) (C := C) (D := D) (E := E) hR
  have bound : 2^(2*m^3) * (2^m * f (2^a*q))^27 ≤ 2^(2*m^3) * f (2^m)^27 := calc
    _ = (2^(2*m^3) * f (2^a*q)^27) * 2^(27*m) := by rw [mul_pow, ← pow_mul, Nat.mul_comm m 27]; ring
    _ ≤ (2^(2*m^3) * (f (2^a)^27 * f q^27 * 2^(E*(m+1)^2))) * 2^(27*m) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hmix)
    _ = (2^(2*m^3) * f (2^a)^27) * f q^27 * 2^(E*(m+1)^2) * 2^(27*m) := by ring
    _ ≤ (f (2^m)^27 * 2^(2*a^3+C*(m+1)^2)) * 2^(r^3+D) * 2^(E*(m+1)^2) * 2^(27*m) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hdy ho))
    _ = 2^(27*m + 2*a^3 + C*(m+1)^2 + r^3 + D + E*(m+1)^2) * f (2^m)^27 := by
      simp only [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) he)
  exact (Nat.pow_le_pow_iff_left (by decide : 27 ≠ 0)).mp
    (Nat.le_of_mul_le_mul_left bound (Nat.two_pow_pos _))

/-- Higman's lower bound and the weak form of Sims' estimate suffice on powers of two. -/
theorem dyadic_comparison (f : ℕ → ℕ) {A : ℕ}
    (lower : ∀ m : ℕ, 3 ≤ m → 2^(2*m^3) ≤ f (2^m)^27 * 2^(12*m^2))
    (upper : ∀ a : ℕ, f (2^a)^27 ≤ 2^(2*a^3 + A*(a+1)^2)) :
    ∀ a m : ℕ, 3 ≤ m → a ≤ m → 2^(2*m^3) * f (2^a)^27 ≤
      f (2^m)^27 * 2^(2*a^3 + (A+12)*(m+1)^2) := by
  intro a m hm ham
  have ha := Nat.pow_le_pow_left (show a+1 ≤ m+1 by omega) 2
  have hm' := Nat.pow_le_pow_left (show m ≤ m+1 by omega) 2
  calc
    _ ≤ (f (2^m)^27 * 2^(12*m^2)) * 2^(2*a^3+A*(a+1)^2) :=
      Nat.mul_le_mul (lower m hm) (upper a)
    _ = f (2^m)^27 * 2^(12*m^2 + (2*a^3+A*(a+1)^2)) := by simp only [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
      (by nlinarith only [Nat.mul_le_mul_left A ha, Nat.mul_le_mul_left 12 hm']))

theorem main : H1 → H2 → H3 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3.H1 := by
  rintro ⟨C,hC⟩ ⟨D,hD⟩ ⟨E,hE⟩
  exact large_deficit_of_counts g hC hD hE

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1