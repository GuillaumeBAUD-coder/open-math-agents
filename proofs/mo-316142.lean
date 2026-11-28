import OMAStatements.S_mo_316142
import Mathlib

/-!
MathOverflow 316142: n = 2, F = ℚ, A = {0, 1, 2}: the sums a₁ + 2a₂ over distinct a₁, a₂ ∈ A are 1, 2, 4, 5, fewer than the bound 5.
-/

namespace OMA.P316142

/-- For `A = {0, 1, 2} ⊆ ℚ` and `n = 2`, every value `a₁ + 2 a₂` lies in `{1, 2, 4, 5}`. -/
theorem sub :
    {s : ℚ | ∃ a : Fin 2 → ℚ, Function.Injective a ∧ (∀ k, a k ∈ ({0, 1, 2} : Finset ℚ)) ∧
      s = ∑ k : Fin 2, ((k : ℕ) + 1 : ℚ) * a k} ⊆ ↑({1, 2, 4, 5} : Finset ℚ) := by
  rintro s ⟨a, ha, hA, rfl⟩
  have hne : a 0 ≠ a 1 := ha.ne (by decide)
  have h0 := hA 0
  have h1 := hA 1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Finset.coe_insert,
    Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;>
    simp only [h0, h1] at hne ⊢ <;> first | exact absurd rfl hne | norm_num

theorem disproof :
    ¬ ∀ (n : ℕ), 1 ≤ n → ∀ (F : Type) [Field F], (ringChar F = 0 ∨ n + 1 < ringChar F) →
      ∀ A : Finset F, n + (if n = 3 then 1 else 0) ≤ A.card →
        (if ringChar F = 0 then (A.card - n) * (n * (n + 1) / 2) + n * (n ^ 2 - 1) / 6 + 1
          else min (ringChar F) ((A.card - n) * (n * (n + 1) / 2) + n * (n ^ 2 - 1) / 6 + 1)) ≤
          {s : F | ∃ a : Fin n → F, Function.Injective a ∧ (∀ k, a k ∈ A) ∧
            s = ∑ k : Fin n, ((k : ℕ) + 1 : F) * a k}.ncard := by
  intro h
  have hc : ringChar ℚ = 0 := ringChar.eq_zero
  have hA : ({0, 1, 2} : Finset ℚ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
      Finset.card_singleton]
  have key := h 2 (by norm_num) ℚ (Or.inl hc) {0, 1, 2} (by rw [hA]; norm_num)
  rw [if_pos hc, hA] at key
  have hle := Set.ncard_le_ncard sub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hle
  have h4 : ({1, 2, 4, 5} : Finset ℚ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
      Finset.card_insert_of_notMem (by norm_num), Finset.card_singleton]
  have h5 : (3 - 2) * (2 * (2 + 1) / 2) + 2 * (2 ^ 2 - 1) / 6 + 1 = 5 := by norm_num
  rw [h5] at key
  rw [h4] at hle
  omega

end OMA.P316142

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_316142.main) := OMA.P316142.disproof
