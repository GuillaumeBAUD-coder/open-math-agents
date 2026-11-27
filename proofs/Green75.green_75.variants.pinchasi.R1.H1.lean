import OMAReductions.R_Green75_green_75_variants_pinchasi_R1

-- Step Green75.green_75.variants.pinchasi.R1.H1
-- Credit: @caa1982

open Green75 Finset

theorem OMA.solution : OMA.R_Green75_green_75_variants_pinchasi_R1.H1 := by
  classical
  intro X
  let bad : Finset ℝ := (X ×ˢ X).image (fun pq => -(pq.1.1 - pq.2.1) / (pq.1.2 - pq.2.2))
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset bad
  let e : (ℝ × ℝ) ↪ (ℝ × ℝ) :=
    { toFun := fun p => (p.1 + c * p.2, p.2)
      inj' := fun p q h => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        rw [h2] at h1
        exact Prod.ext (by linarith) h2 }
  refine ⟨e, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    have h1 : p.1 + c * p.2 = q.1 + c * q.2 := hxy
    by_cases h2 : p.2 = q.2
    · rw [h2] at h1
      congr 1
      exact Prod.ext (by linarith) h2
    · exfalso
      apply hc
      refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
      have hne : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr h2
      field_simp [hne]
      linarith
  · intro p q
    have hcross : ∀ x : ℝ × ℝ, cross (e p) (e q) (e x) = cross p q x := by
      intro x
      change ((q.1 + c * q.2) - (p.1 + c * p.2)) * (x.2 - p.2) -
        (q.2 - p.2) * ((x.1 + c * x.2) - (p.1 + c * p.2)) =
        (q.1 - p.1) * (x.2 - p.2) - (q.2 - p.2) * (x.1 - p.1)
      ring
    have hleft : leftCount (X.map e) (e p) (e q) = leftCount X p q := by
      unfold leftCount
      rw [Finset.filter_map, Finset.card_map]
      congr 1
      ext x
      simp [hcross]
    have hright : rightCount (X.map e) (e p) (e q) = rightCount X p q := by
      unfold rightCount
      rw [Finset.filter_map, Finset.card_map]
      congr 1
      ext x
      simp [hcross]
    unfold imbalance
    rw [hleft, hright]
