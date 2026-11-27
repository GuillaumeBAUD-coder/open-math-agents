import OMAReductions.R_Erdos372_erdos_372_R1

/-! # Heath-Brown divisibility sets

Induction on `k`: if `A` works and `L = ∏ a ∈ A, a`, then `{L} ∪ (L + A)` works.
For `a < b` in `A`, `b - a ∣ a ∣ L`, so `b - a ∣ L + a`, and each `b ∣ L`. -/

theorem OMA.solution : OMA.R_Erdos372_erdos_372_R1.H2 := by
  intro k
  induction k with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨A, hcard, hpos, hdiv⟩ := ih
    set L := ∏ a ∈ A, a with hL
    have hLpos : 0 < L := Finset.prod_pos hpos
    have hdvdL : ∀ a ∈ A, a ∣ L := fun a ha => Finset.dvd_prod_of_mem _ ha
    refine ⟨insert L (A.image (fun a => L + a)), ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (add_right_injective L),
        hcard]
      intro h
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp h
      have := hpos a ha
      omega
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hLpos
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
        omega
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact absurd hxy (lt_irrefl _)
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
          rw [Nat.add_sub_cancel_left]
          exact hdvdL b hb
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        rcases Finset.mem_insert.mp hy with rfl | hy
        · omega
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
          have hab : a < b := by omega
          rw [Nat.add_sub_add_left]
          have h1 := hdiv a ha b hb hab
          exact dvd_add (h1.trans (hdvdL a ha)) h1
