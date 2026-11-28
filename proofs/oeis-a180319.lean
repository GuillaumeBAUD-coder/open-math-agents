import OMAStatements.S_oeis_a180319
import Mathlib

/-! Proof for OEIS A180319: the ordered knight-move pairs on the n by 2n board split into eight
disjoint classes according to the displacement (plus or minus 1, plus or minus 2) or
(plus or minus 2, plus or minus 1). Each class is the image of an injective map from a product of
ranges, sending a base cell x to the pair (x + (a, b), x + (c, d)), so the class sizes are
(n - 1)(2n - 2) four times and (n - 2)(2n - 1) four times, giving
a(n) = 4((n - 1)(2n - 2) + (n - 2)(2n - 1)) in truncated natural arithmetic for every n, which is
4(4n^2 - 9n + 4) for n at least 2 and 0 for n = 0, 1. The recurrence follows from the closed form
by ring arithmetic, and the generating function identity by expanding (1 - x)^3 and comparing
coefficients, checking small indices directly.
Credit: Sudharsan Rajendiran -/

namespace OMA.P180319
open OMA.S_oeis_a180319 PowerSeries

def emb (a b c d : ℕ) (x : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((x.1 + a, x.2 + b), (x.1 + c, x.2 + d))

lemma emb_inj (a b c d : ℕ) : Function.Injective (emb a b c d) := by
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
  simp only [emb, Prod.mk.injEq] at h
  ext <;> simp <;> omega

lemma piece (n a b c d : ℕ) (ha : a = 0 ∨ c = 0) (hb : b = 0 ∨ d = 0) :
    ((board n ×ˢ board n).filter (fun pq : (ℕ × ℕ) × (ℕ × ℕ) =>
      pq.1.1 + c = pq.2.1 + a ∧ pq.1.2 + d = pq.2.2 + b)).card =
      (n - (a + c)) * (2 * n - (b + d)) := by
  have : (board n ×ˢ board n).filter (fun pq : (ℕ × ℕ) × (ℕ × ℕ) =>
      pq.1.1 + c = pq.2.1 + a ∧ pq.1.2 + d = pq.2.2 + b) =
      (Finset.range (n - (a + c)) ×ˢ Finset.range (2 * n - (b + d))).image (emb a b c d) := by
    ext ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩
    simp only [board, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      emb, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩
      refine ⟨p1 - a, p2 - b, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩
    · rintro ⟨x, y, ⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩
      subst h3 h4 h5 h6
      omega
  rw [this, Finset.card_image_of_injective _ (emb_inj a b c d), Finset.card_product,
    Finset.card_range, Finset.card_range]

lemma card_or {α : Type*} [DecidableEq α] (s : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x ∈ s, P x → ¬ Q x) :
    (s.filter (fun x => P x ∨ Q x)).card = (s.filter P).card + (s.filter Q).card := by
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter.2 h

lemma a_nat (n : ℕ) : a n = 4 * ((n - 1) * (2 * n - 2) + (n - 2) * (2 * n - 1)) := by
  unfold a
  rw [Finset.filter_congr (q := fun pq : (ℕ × ℕ) × (ℕ × ℕ) =>
    (pq.1.1 + 1 = pq.2.1 + 0 ∧ pq.1.2 + 2 = pq.2.2 + 0) ∨
    (pq.1.1 + 1 = pq.2.1 + 0 ∧ pq.1.2 + 0 = pq.2.2 + 2) ∨
    (pq.1.1 + 0 = pq.2.1 + 1 ∧ pq.1.2 + 2 = pq.2.2 + 0) ∨
    (pq.1.1 + 0 = pq.2.1 + 1 ∧ pq.1.2 + 0 = pq.2.2 + 2) ∨
    (pq.1.1 + 2 = pq.2.1 + 0 ∧ pq.1.2 + 1 = pq.2.2 + 0) ∨
    (pq.1.1 + 2 = pq.2.1 + 0 ∧ pq.1.2 + 0 = pq.2.2 + 1) ∨
    (pq.1.1 + 0 = pq.2.1 + 2 ∧ pq.1.2 + 1 = pq.2.2 + 0) ∨
    (pq.1.1 + 0 = pq.2.1 + 2 ∧ pq.1.2 + 0 = pq.2.2 + 1))]
  swap
  · rintro ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ _
    simp only [Int.natAbs_eq_iff]
    push_cast
    omega
  rw [card_or _ _ _ (by intro x _; omega), card_or _ _ _ (by intro x _; omega),
    card_or _ _ _ (by intro x _; omega), card_or _ _ _ (by intro x _; omega),
    card_or _ _ _ (by intro x _; omega), card_or _ _ _ (by intro x _; omega),
    card_or _ _ _ (by intro x _; omega)]
  rw [piece n 0 0 1 2 (by omega) (by omega), piece n 0 2 1 0 (by omega) (by omega),
    piece n 1 0 0 2 (by omega) (by omega), piece n 1 2 0 0 (by omega) (by omega),
    piece n 0 0 2 1 (by omega) (by omega), piece n 0 1 2 0 (by omega) (by omega),
    piece n 2 0 0 1 (by omega) (by omega), piece n 2 1 0 0 (by omega) (by omega)]
  simp only [Nat.zero_add, Nat.add_zero]
  ring

lemma closed (m : ℕ) : (a (m + 2) : ℤ) = 4 * (4 - 9 * ((m + 2 : ℕ) : ℤ) + 4 * ((m + 2 : ℕ) : ℤ) ^ 2) := by
  rw [a_nat]
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : 2 * (m + 2) - 2 = 2 * m + 2 := by omega
  have h3 : m + 2 - 2 = m := by omega
  have h4 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
  rw [h1, h2, h3, h4]
  push_cast
  ring

lemma part1 (n : ℕ) (hn : 1 < n) : (a n : ℤ) = 4 * (4 - 9 * n + 4 * n ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact closed m

lemma part2 (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = (m + 2) + 2 by omega, show m + 5 - 2 = (m + 1) + 2 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 = (m + 3) + 2 by omega,
    closed, closed, closed, closed]
  push_cast
  ring

lemma a0 : a 0 = 0 := by rw [a_nat]
lemma a1 : a 1 = 0 := by rw [a_nat]

lemma aq (m : ℕ) : (a (m + 2) : ℚ) = 4 * (4 - 9 * ((m : ℚ) + 2) + 4 * ((m : ℚ) + 2) ^ 2) := by
  rw [a_nat]
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : 2 * (m + 2) - 2 = 2 * m + 2 := by omega
  have h3 : m + 2 - 2 = m := by omega
  have h4 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
  rw [h1, h2, h3, h4]
  push_cast
  ring

lemma part3 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 3 =
      4 * PowerSeries.X ^ 2 * (2 + 7 * PowerSeries.X - PowerSeries.X ^ 2) := by
  have hD : ((1 - X) ^ 3 : PowerSeries ℚ) =
      C (1 : ℚ) * X ^ 0 + C (-3 : ℚ) * X ^ 1 + C (3 : ℚ) * X ^ 2 + C (-1 : ℚ) * X ^ 3 := by
    simp only [map_neg, map_one, map_ofNat]; ring
  have hN : (4 * X ^ 2 * (2 + 7 * X - X ^ 2) : PowerSeries ℚ) =
      C (8 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-4 : ℚ) * X ^ 4 := by
    simp only [map_neg, map_ofNat]; ring
  rw [hD, hN]
  ext d
  simp only [mul_add, map_add, mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X_pow',
    coeff_mk, coeff_C]
  rcases d with _ | _ | _ | _ | _ | m
  · simp
  · simp [a1]
  · simp [aq, a1]; norm_num
  · simp [aq, a1]; norm_num
  · simp [aq, a1]; norm_num
  · simp only [show 0 ≤ m + 5 from Nat.zero_le _, show 1 ≤ m + 5 by omega,
      show 2 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega, if_true,
      show m + 5 ≠ 0 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega,
      show m + 5 ≠ 4 by omega, if_false, show m + 5 - 0 = (m + 3) + 2 by omega,
      show m + 5 - 1 = (m + 2) + 2 by omega, show m + 5 - 2 = (m + 1) + 2 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 3 + 2 ≠ 0 by omega,
      show m + 2 + 2 ≠ 0 by omega, show m + 1 + 2 ≠ 0 by omega, show m + 2 ≠ 0 by omega, aq, show m + 5 ≠ 1 by omega, show m + 5 - 4 ≠ 0 by omega, show m + 5 - 2 ≠ 0 by omega, show m + 5 - 3 ≠ 0 by omega, if_false, add_zero]
    push_cast
    ring

end OMA.P180319

theorem OMA.solution : type_of% @OMA.S_oeis_a180319.main :=
  ⟨OMA.P180319.part1, OMA.P180319.part2, OMA.P180319.part3⟩
