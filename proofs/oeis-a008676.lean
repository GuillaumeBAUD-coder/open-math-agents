import OMAStatements.S_oeis_a008676

open OMA.S_oeis_a008676 Finset

/-- Count the partitions by their coordinate in an interval of consecutive integers. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a008676.main := by
  intro n
  let lower := 3 * (n + 3) / 5
  let upper := 2 * (n + 3) / 3
  let coordinate (p : ℕ × ℕ) := 2 * (p.1 + 1) + 3 * p.2
  have representation {x y : ℕ} :
      (x, y) ∈ representations n ↔ 3 * x + 5 * y = n := by
    simp only [representations, mem_filter, mem_product, mem_range]
    constructor
    · exact And.right
    · intro h
      exact ⟨⟨by omega, by omega⟩, h⟩
  have bounds {x y : ℕ} (h : 3 * x + 5 * y = n) :
      lower < coordinate (x, y) ∧ coordinate (x, y) ≤ upper := by
    dsimp [lower, upper, coordinate]
    constructor <;> omega
  have count : (representations n).card = (range (upper - lower)).card := by
    apply Finset.card_bij (fun p _ => coordinate p - lower - 1)
    · rintro ⟨x, y⟩ hp
      have ht := bounds (representation.mp hp)
      apply mem_range.mpr
      omega
    · rintro ⟨x, y⟩ hxy ⟨w, z⟩ hwz eq
      have h₁ := representation.mp hxy
      have h₂ := representation.mp hwz
      have b₁ := bounds h₁
      have b₂ := bounds h₂
      have ht : coordinate (x, y) = coordinate (w, z) := by omega
      change 2 * (x + 1) + 3 * y = 2 * (w + 1) + 3 * z at ht
      apply Prod.ext <;> dsimp <;> omega
    · intro i hi
      have hi' := mem_range.mp hi
      let t := lower + i + 1
      have ht : lower < t ∧ t ≤ upper := by dsimp [t]; omega
      have hleft : 3 * (n + 3) < 5 * t := by dsimp [lower, upper] at ht; omega
      have hright : 3 * t ≤ 2 * (n + 3) := by dsimp [lower, upper] at ht; omega
      let x := 5 * t - 3 * (n + 3) - 1
      let y := 2 * (n + 3) - 3 * t
      have hxy : 3 * x + 5 * y = n := by dsimp [x, y]; omega
      have he : coordinate (x, y) = t := by dsimp [coordinate, x, y]; omega
      refine ⟨(x, y), representation.mpr hxy, ?_⟩
      rw [he]
      dsimp [t]
      omega
  rw [card_range] at count
  change ((representations n).card : ℤ) = _
  rw [count]
  exact Int.ofNat_sub (by dsimp [lower, upper]; omega)
