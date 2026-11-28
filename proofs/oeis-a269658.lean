import OMAStatements.S_oeis_a269658
import Mathlib

/-!
Proof of the formulas for OEIS A269658: the words `f` of length 5 over `0..n` with no repeated
rise `v, v + 1` (positions `i < j` with `f(i+1) = f(i) + 1`, `f j = f i`, `f(j+1) = f(i+1)`).

* A repeated rise can only sit at positions (0, 2), (0, 3) or (1, 3) (adjacent positions would
  need `f(i+1) = f i`), and these three patterns exclude each other. Each pattern fixes four
  letters from the lower value `x < n` of the rise and leaves one letter free, so the invalid
  words are in bijection with three copies of `Fin n × Fin (n + 1)`.
* Hence a(n) = (n + 1)^5 - 3 n (n + 1); the recurrence and the generating function follow,
  the latter coefficient by coefficient.
-/

namespace OMA.Helpers

open OMA.S_oeis_a269658

/-- The three shapes of a word with a repeated rise `v, v + 1`, at positions (0, 2), (0, 3)
and (1, 3); `x` is the lower value of the rise and `y` the free letter. -/
def a269658_word (n : ℕ) :
    (Fin n × Fin (n + 1)) ⊕ (Fin n × Fin (n + 1)) ⊕ (Fin n × Fin (n + 1)) →
      Fin 5 → Fin (n + 1)
  | Sum.inl (x, y) => ![x.castSucc, x.succ, x.castSucc, x.succ, y]
  | Sum.inr (Sum.inl (x, y)) => ![x.castSucc, x.succ, y, x.castSucc, x.succ]
  | Sum.inr (Sum.inr (x, y)) => ![y, x.castSucc, x.succ, x.castSucc, x.succ]

theorem a269658_word_bad (n : ℕ) (t) : ¬ isValid n (a269658_word n t) := by
  unfold isValid
  push Not
  rcases t with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩
  · exact ⟨0, 2, by decide, by simp [a269658_word], by simp [a269658_word], by simp [a269658_word]⟩
  · exact ⟨0, 3, by decide, by simp [a269658_word], by simp [a269658_word], by simp [a269658_word]⟩
  · exact ⟨1, 3, by decide, by simp [a269658_word], by simp [a269658_word], by simp [a269658_word]⟩

theorem a269658_word_inj (n : ℕ) : Function.Injective (a269658_word n) := by
  intro t s h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  rcases t with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩ <;> rcases s with ⟨x', y'⟩ | ⟨x', y'⟩ | ⟨x', y'⟩ <;>
    simp [a269658_word, Fin.ext_iff] at h0 h1 h2 h3 h4 ⊢ <;> omega

theorem a269658_word_surj (n : ℕ) (f : Fin 5 → Fin (n + 1)) (hf : ¬ isValid n f) :
    ∃ t, a269658_word n t = f := by
  unfold isValid at hf
  push Not at hf
  obtain ⟨i, j, hij, h1, h2, h3⟩ := hf
  fin_cases i <;> fin_cases j <;> simp at hij h1 h2 h3
  · rw [h2] at h1; omega
  · refine ⟨Sum.inl (⟨(f 0).val, by omega⟩, f 4), ?_⟩
    funext k
    fin_cases k <;> simp [a269658_word, Fin.ext_iff] <;> omega
  · refine ⟨Sum.inr (Sum.inl (⟨(f 0).val, by omega⟩, f 2)), ?_⟩
    funext k
    fin_cases k <;> simp [a269658_word, Fin.ext_iff] <;> omega
  · rw [h2] at h1; omega
  · refine ⟨Sum.inr (Sum.inr (⟨(f 1).val, by omega⟩, f 0)), ?_⟩
    funext k
    fin_cases k <;> simp [a269658_word, Fin.ext_iff] <;> omega
  · rw [h2] at h1; omega

/-- The invalid words are counted by the three shapes. -/
def a269658_toBad (n : ℕ) (t : (Fin n × Fin (n + 1)) ⊕ (Fin n × Fin (n + 1)) ⊕ (Fin n × Fin (n + 1))) :
    {f : Fin 5 → Fin (n + 1) // ¬ isValid n f} :=
  ⟨a269658_word n t, a269658_word_bad n t⟩

theorem a269658_toBad_bij (n : ℕ) : Function.Bijective (a269658_toBad n) := by
  constructor
  · intro t s h
    exact a269658_word_inj n (congrArg Subtype.val h)
  · rintro ⟨f, hf⟩
    obtain ⟨t, ht⟩ := a269658_word_surj n f hf
    exact ⟨t, Subtype.ext ht⟩

theorem a269658_card_bad (n : ℕ) :
    Fintype.card {f : Fin 5 → Fin (n + 1) // ¬ isValid n f} = 3 * (n * (n + 1)) := by
  rw [← Fintype.card_of_bijective (a269658_toBad_bij n)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The closed form `a(n) = (n + 1)^5 - 3 n (n + 1)` (in ℕ). -/
theorem a269658_closed_nat (n : ℕ) : a n + 3 * (n * (n + 1)) = (n + 1) ^ 5 := by
  have h1 := a269658_card_bad n
  have h2 := Fintype.card_subtype_compl (fun f : Fin 5 → Fin (n + 1) => isValid n f)
  have h3 := Fintype.card_subtype_le (fun f : Fin 5 → Fin (n + 1) => isValid n f)
  have h4 : Fintype.card (Fin 5 → Fin (n + 1)) = (n + 1) ^ 5 := by
    simp [Fintype.card_fin]
  unfold a
  rw [h1, h4] at h2
  rw [h4] at h3
  omega

theorem a269658_closed (n : ℕ) : a n = (n + 1) ^ 5 - 3 * n * (n + 1) := by
  have := a269658_closed_nat n
  rw [mul_assoc]
  omega

theorem a269658_closed_int (n : ℕ) : (a n : ℤ) = ((n : ℤ) + 1) ^ 5 - 3 * n * (n + 1) := by
  have h := a269658_closed_nat n
  have h' : ((a n + 3 * (n * (n + 1)) : ℕ) : ℤ) = (((n + 1) ^ 5 : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

theorem a269658_closed_rat (n : ℕ) : (a n : ℚ) = ((n : ℚ) + 1) ^ 5 - 3 * n * (n + 1) := by
  have h := a269658_closed_nat n
  have h' : ((a n + 3 * (n * (n + 1)) : ℕ) : ℚ) = (((n + 1) ^ 5 : ℕ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

theorem a269658_rec (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) -
      15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega]
  simp only [a269658_closed_int]
  push_cast
  ring

theorem a269658_gf :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 6 =
      1 + 20 * PowerSeries.X + 84 * PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3 +
        7 * PowerSeries.X ^ 4 := by
  set p : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ)) with hp
  have e1 : p * (1 - PowerSeries.X) ^ 6 =
      p - PowerSeries.C (6 : ℚ) * (p * PowerSeries.X ^ 1)
        + PowerSeries.C (15 : ℚ) * (p * PowerSeries.X ^ 2)
        - PowerSeries.C (20 : ℚ) * (p * PowerSeries.X ^ 3)
        + PowerSeries.C (15 : ℚ) * (p * PowerSeries.X ^ 4)
        - PowerSeries.C (6 : ℚ) * (p * PowerSeries.X ^ 5) + p * PowerSeries.X ^ 6 := by
    simp only [map_ofNat]
    ring
  have e2 : (1 + 20 * PowerSeries.X + 84 * PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3 +
        7 * PowerSeries.X ^ 4 : PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (20 : ℚ) * PowerSeries.X ^ 1
        + PowerSeries.C (84 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 3
        + PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 4 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', hp, PowerSeries.coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> simp [a269658_closed_rat] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    rw [if_pos (show 1 ≤ j + 6 by omega), if_pos (show 2 ≤ j + 6 by omega),
      if_pos (show 3 ≤ j + 6 by omega), if_pos (show 4 ≤ j + 6 by omega),
      if_pos (show 5 ≤ j + 6 by omega), if_pos (show 6 ≤ j + 6 by omega),
      if_neg (show ¬ (j + 6 = 0) by omega), if_neg (show ¬ (j + 6 = 1) by omega),
      if_neg (show ¬ (j + 6 = 2) by omega), if_neg (show ¬ (j + 6 = 3) by omega),
      if_neg (show ¬ (j + 6 = 4) by omega),
      show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega,
      show j + 6 - 5 = j + 1 by omega, show j + 6 - 6 = j by omega]
    simp only [a269658_closed_rat]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a269658.main :=
  ⟨OMA.Helpers.a269658_gf, OMA.Helpers.a269658_rec, OMA.Helpers.a269658_closed⟩
