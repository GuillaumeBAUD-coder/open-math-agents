import OMAStatements.S_mse_2363374
import Mathlib

namespace Mse2363374Aux

/-- The exponent vector of `a ^ p.1 * b ^ p.2`. -/
noncomputable def mon (p : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p.1 + Finsupp.single 1 p.2

lemma mon_inj : Function.Injective mon := by
  intro p q h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  simp [mon] at h0 h1
  exact Prod.ext h0 h1

open MvPolynomial in
lemma coeff_mono (p q : ℕ × ℕ) (c : ℤ) :
    coeff (mon q) (monomial (mon p) c : MvPolynomial (Fin 2) ℤ) = if p = q then c else 0 := by
  rw [coeff_monomial]
  by_cases h : p = q
  · simp [h]
  · rw [if_neg h, if_neg (fun h' => h (mon_inj h'))]

open MvPolynomial in
lemma term (a b : ℕ) (c : ℤ) :
    (C c * X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) ℤ) = monomial (mon (a, b)) c := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul]
  simp [mon]

/-- The exponent pairs of the fourteen monomials of the seventh polynomial. -/
def pairs : Finset (ℕ × ℕ) := {(0, 1), (0, 2), (0, 3), (0, 4), (2, 0), (2, 1), (2, 2), (2, 3), (4, 0), (4, 1), (4, 2), (6, 0), (6, 1), (8, 0)}

open MvPolynomial OMA.S_mse_2363374 in
lemma seq7 : seq 7 =
      monomial (mon (0, 1)) (1 : ℤ) +
      monomial (mon (0, 2)) (4 : ℤ) +
      monomial (mon (0, 3)) (6 : ℤ) +
      monomial (mon (0, 4)) (5 : ℤ) +
      monomial (mon (2, 0)) (1 : ℤ) +
      monomial (mon (2, 1)) (6 : ℤ) +
      monomial (mon (2, 2)) (10 : ℤ) +
      monomial (mon (2, 3)) (8 : ℤ) +
      monomial (mon (4, 0)) (3 : ℤ) +
      monomial (mon (4, 1)) (6 : ℤ) +
      monomial (mon (4, 2)) (8 : ℤ) +
      monomial (mon (6, 0)) (2 : ℤ) +
      monomial (mon (6, 1)) (4 : ℤ) +
      monomial (mon (8, 0)) (1 : ℤ) := by
  simp only [← term]
  simp only [seq, map_ofNat, map_one]
  ring

open MvPolynomial OMA.S_mse_2363374 in
lemma sub7 : pairs.image mon ⊆ (seq 7).support := by
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨q, hq, rfl⟩ := hm
  rw [mem_support_iff, seq7]
  simp only [coeff_add, coeff_mono]
  unfold pairs at hq
  fin_cases hq <;> simp

lemma card7 : (pairs.image mon).card = 14 := by
  rw [Finset.card_image_of_injective _ mon_inj]
  rfl

end Mse2363374Aux

open OMA.S_mse_2363374 Mse2363374Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2363374.main) := by
  intro h
  have h7 := h 7 (by norm_num)
  have hle : 14 ≤ (seq 7).support.card := card7 ▸ Finset.card_le_card sub7
  rw [h7] at hle
  have hf : Nat.fib 7 = 13 := by norm_num
  omega
