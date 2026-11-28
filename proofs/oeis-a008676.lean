import OMAStatements.S_oeis_a008676
import Mathlib

namespace A008676

open OMA.S_oeis_a008676 in
lemma step (n : ℕ) : a (n + 15) = a n + 1 := by
  unfold a
  have hset : representations (n + 15) =
      insert ((2 * n) % 5, (n + 15 - 3 * ((2 * n) % 5)) / 5)
        ((representations n).image (fun p : ℕ × ℕ => (p.1 + 5, p.2))) := by
    ext ⟨x, y⟩
    simp only [representations, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_insert, Finset.mem_image, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨⟨hx, hy⟩, h⟩
      by_cases h5 : 5 ≤ x
      · right
        exact ⟨x - 5, y, ⟨⟨by omega, by omega⟩, by omega⟩, by omega, rfl⟩
      · left
        constructor <;> omega
    · rintro (⟨hx, hy⟩ | ⟨u, v, ⟨⟨hu, hv⟩, h⟩, hx, hy⟩)
      · refine ⟨⟨by omega, by omega⟩, by omega⟩
      · refine ⟨⟨by omega, by omega⟩, by omega⟩
  have hnot : ((2 * n) % 5, (n + 15 - 3 * ((2 * n) % 5)) / 5) ∉
      (representations n).image (fun p : ℕ × ℕ => (p.1 + 5, p.2)) := by
    simp only [Finset.mem_image, Prod.mk.injEq, Prod.exists, not_exists, not_and]
    intro u v _ hu
    omega
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 + 5, p.2)) := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  rw [hset, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj]

set_option maxRecDepth 100000 in
open OMA.S_oeis_a008676 in
lemma small : ∀ n < 15, (a n : ℤ) = (2 * ((n : ℤ) + 3)) / 3 - (3 * ((n : ℤ) + 3)) / 5 := by
  decide

end A008676

theorem OMA.solution : type_of% @OMA.S_oeis_a008676.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 15
    · exact A008676.small n h
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
      have h1 := ih m (by omega)
      rw [A008676.step]
      push_cast
      have e1 : (2 * ((m : ℤ) + 15 + 3)) / 3 = (2 * ((m : ℤ) + 3)) / 3 + 10 := by
        rw [show 2 * ((m : ℤ) + 15 + 3) = 2 * ((m : ℤ) + 3) + 10 * 3 by ring,
          Int.add_mul_ediv_right _ _ (by norm_num)]
      have e2 : (3 * ((m : ℤ) + 15 + 3)) / 5 = (3 * ((m : ℤ) + 3)) / 5 + 9 := by
        rw [show 3 * ((m : ℤ) + 15 + 3) = 3 * ((m : ℤ) + 3) + 9 * 5 by ring,
          Int.add_mul_ediv_right _ _ (by norm_num)]
      rw [e1, e2, h1]
      ring
