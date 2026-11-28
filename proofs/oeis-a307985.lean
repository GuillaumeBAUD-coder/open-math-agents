import OMAStatements.S_oeis_a307985

open OMA.S_oeis_a307985

private theorem triangle_middle {n x b z : ℕ} (_hx : 1 ≤ x)
    (he : x + b + z = n) (hxb : x ≤ b) (hbz : b ≤ z) (ht : z < x + b)
    (hd : b ∣ n) : n = 3 * b := by
  obtain ⟨k, hk⟩ := hd
  have h₁ : 2 < k := by
    by_contra! h
    have hm := Nat.mul_le_mul_left b h
    omega
  have h₂ : k < 4 := by
    by_contra! h
    have hm := Nat.mul_le_mul_left b h
    omega
  have hk₃ : k = 3 := by omega
  rw [hk, hk₃, Nat.mul_comm]

private theorem triangle_count (n : ℕ) :
    a n = if n % 3 = 0 then (n / 3 + 1) / 2 else 0 := by
  let b := n / 3
  let build (x : ℕ) : ℕ × ℕ × ℕ := (x, b, 2 * b - x)
  have hshape : triangles n =
      if n % 3 = 0 then (Finset.Icc (b / 2 + 1) b).image build else ∅ := by
    by_cases hn : n % 3 = 0
    · rw [if_pos hn]
      have hnb : n = 3 * b := by dsimp [b]; omega
      ext p
      rcases p with ⟨x, y, z⟩
      simp only [triangles, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨hx, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩, he, hxy, hyz, ht, hd⟩
        have hny := triangle_middle hx he hxy hyz ht hd
        have hy : y = b := by omega
        subst y
        have hz : 2 * b - x = z := by omega
        exact ⟨x, ⟨by omega, hxy⟩, by simp [build, hz]⟩
      · rintro ⟨t, ⟨ht, htb⟩, h⟩
        change (t, b, 2 * b - t) = (x, y, z) at h
        cases h
        refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
          ⟨by omega, by omega⟩⟩, by omega, htb, by omega, by omega, ⟨3, by omega⟩⟩
    · rw [if_neg hn]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨x, y, z⟩ h
      simp only [triangles, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
      obtain ⟨⟨⟨hx, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩, he, hxy, hyz, ht, hd⟩ := h
      have hny := triangle_middle hx he hxy hyz ht hd
      omega
  unfold a
  rw [hshape]
  split_ifs with hn
  · rw [Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h), Nat.card_Icc]
    change b + 1 - (b / 2 + 1) = (b + 1) / 2
    omega
  · rfl

theorem OMA.solution : type_of% @OMA.S_oeis_a307985.main := by
  intro n hn
  rw [triangle_count n, triangle_count (n - 3), triangle_count (n - 6),
    triangle_count (n - 9)]
  have h₃ : (n - 3) % 3 = n % 3 := by omega
  have h₆ : (n - 6) % 3 = n % 3 := by omega
  have h₉ : (n - 9) % 3 = n % 3 := by omega
  rw [h₃, h₆, h₉]
  split_ifs <;> omega