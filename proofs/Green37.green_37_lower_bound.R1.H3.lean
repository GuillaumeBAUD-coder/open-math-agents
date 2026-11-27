import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step Green37.green_37_lower_bound.R1.H3: hypothesis H3 of reduction Green37.green_37_lower_bound.R1
-- Credit: @ivillar
-- The cover {0, ..., kN} (as in upstream m_le_mul_add_one) shows the defining set is nonempty, so
-- m N k is attained. k = 1: the progression for d = 1 puts a point in A. k = 2: each d in [1, N]
-- gives a, a + d in A; (d, b) maps injectively into the ordered off-diagonal pairs of A.

namespace OMA.W3Green37H3

open Green37

theorem cover_nonempty (N k : ℕ) :
    { m | ∃ A : Finset ℕ, A.card = m ∧ IsAPCover (A : Set ℕ) N k }.Nonempty := by
  refine ⟨k * N + 1, Finset.range (k * N + 1), Finset.card_range _, ?_⟩
  intro d hd
  refine ⟨0, ((Finset.range k).image (fun i ↦ i * d) : Set ℕ), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
    exact Nat.lt_succ_of_le (Nat.mul_le_mul (Nat.le_of_lt hi) hd.2)
  · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _
        (fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hd.1 h), Finset.card_range]
  · ext x; simp

theorem exists_min (N k : ℕ) :
    ∃ A : Finset ℕ, A.card = m N k ∧ IsAPCover (A : Set ℕ) N k :=
  Nat.sInf_mem (cover_nonempty N k)

theorem part1 (N : ℕ) (hN : 1 ≤ N) : 1 ≤ m N 1 := by
  obtain ⟨A, hA, hcov⟩ := exists_min N 1
  obtain ⟨a, s, hs, hap⟩ := hcov 1 ⟨le_refl 1, hN⟩
  have h0 : a ∈ s := by
    rw [hap.eq]; exact ⟨0, by norm_num, by simp⟩
  have ha : a ∈ A := by exact_mod_cast hs h0
  rw [← hA]
  exact Finset.card_pos.2 ⟨a, ha⟩

theorem part2 (N : ℕ) : 2 * N ≤ m N 2 * (m N 2 - 1) := by
  obtain ⟨A, hA, hcov⟩ := exists_min N 2
  have hex : ∀ d, 1 ≤ d ∧ d ≤ N → ∃ a, a ∈ A ∧ a + d ∈ A := by
    intro d hd
    obtain ⟨a, s, hs, hap⟩ := hcov d hd
    have h0 : a ∈ s := by
      rw [hap.eq]; exact ⟨0, by norm_num, by simp⟩
    have h1 : a + d ∈ s := by
      rw [hap.eq]; exact ⟨1, by norm_num, by simp⟩
    exact ⟨a, by exact_mod_cast hs h0, by exact_mod_cast hs h1⟩
  choose! f hf using hex
  let g : ℕ × Bool → ℕ × ℕ := fun x => if x.2 then (f x.1, f x.1 + x.1) else (f x.1 + x.1, f x.1)
  have hmaps : ∀ x ∈ Finset.Icc 1 N ×ˢ (Finset.univ : Finset Bool), g x ∈ A.offDiag := by
    rintro ⟨d, b⟩ hx
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true] at hx
    obtain ⟨h1, h2⟩ := hf d hx
    obtain ⟨hd1, hd2⟩ := hx
    rw [Finset.mem_offDiag]
    cases b
    · simp only [g, Bool.false_eq_true, if_false]
      exact ⟨h2, h1, by omega⟩
    · simp only [g, if_true]
      exact ⟨h1, h2, by omega⟩
  have hinj : Set.InjOn g (Finset.Icc 1 N ×ˢ (Finset.univ : Finset Bool) : Finset (ℕ × Bool)) := by
    rintro ⟨d, b⟩ hx ⟨d', b'⟩ hx' he
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc,
      Finset.coe_univ, Set.mem_univ, and_true] at hx hx'
    cases b <;> cases b' <;> simp only [g, Prod.mk.injEq, if_true, Bool.false_eq_true, if_false] at he <;>
      first
      | (obtain ⟨he1, he2⟩ := he; exact Prod.ext (by omega) rfl)
      | (exfalso; omega)
  have hle := Finset.card_le_card_of_injOn g hmaps hinj
  rw [Finset.card_product, Nat.card_Icc, Finset.card_univ, Fintype.card_bool,
    Finset.offDiag_card, hA] at hle
  rw [Nat.mul_sub_one]
  omega

theorem key : (∀ N : ℕ, 1 ≤ N → 1 ≤ Green37.m N 1) ∧
    (∀ N : ℕ, 2 * N ≤ Green37.m N 2 * (Green37.m N 2 - 1)) :=
  ⟨part1, part2⟩

end OMA.W3Green37H3

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  unfold OMA.R_Green37_green_37_lower_bound_R1.H3
  exact OMA.W3Green37H3.key
