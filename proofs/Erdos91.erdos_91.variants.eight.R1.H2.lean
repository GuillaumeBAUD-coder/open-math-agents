import OMAReductions.R_Erdos91_erdos_91_variants_eight_R1

/-! Two eight-point configurations in the triangular lattice. -/

namespace OMA.Erdos91Eight

open EuclideanGeometry Finset Erdos91

private def firstPoints : Finset (ℤ × ℤ) :=
  {(-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 1), (2, -1)}

private def secondPoints : Finset (ℤ × ℤ) :=
  {(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0)}

private noncomputable def point (p : ℤ × ℤ) : ℝ² :=
  !₂[(p.1 : ℝ) + (p.2 : ℝ) / 2, (p.2 : ℝ) * Real.sqrt 3 / 2]

private noncomputable def lattice : (ℤ × ℤ) ↪ ℝ² where
  toFun := point
  inj' := by
    intro p q h
    have hx := congrArg (fun x : ℝ² => x 0) h
    have hy := congrArg (fun x : ℝ² => x 1) h
    simp only [point, Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
    have hp : (p.2 : ℝ) = q.2 := by
      apply mul_right_cancel₀ (by positivity : Real.sqrt (3 : ℝ) ≠ 0)
      linarith
    exact Prod.ext (by exact_mod_cast (show (p.1 : ℝ) = q.1 by linarith)) (by exact_mod_cast hp)

private def squareDistance (p q : ℤ × ℤ) : ℤ :=
  let x := p.1 - q.1
  let y := p.2 - q.2
  x ^ 2 + x * y + y ^ 2

private theorem lattice_square (p q : ℤ × ℤ) :
    dist (lattice p) (lattice q) ^ 2 = (squareDistance p q : ℝ) := by
  change dist (point p) (point q) ^ 2 = _
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [point, Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs,
    squareDistance, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_mul]
  calc
    _ = ((p.1 : ℝ) - q.1 + ((p.2 : ℝ) - q.2) / 2) ^ 2 +
        ((p.2 : ℝ) - q.2) ^ 2 * (Real.sqrt 3) ^ 2 / 4 := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring

private def squaredValues : Finset ℤ := {1, 3, 4, 7}

private theorem first_values :
    firstPoints.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues := by decide

private theorem second_values :
    secondPoints.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues := by decide

private theorem offDiag_map {α β : Type} (e : α ↪ β) (S : Finset α) :
    (S.map e).offDiag = S.offDiag.map (e.prodMap e) := by
  ext p
  rcases p with ⟨p, q⟩
  simp only [mem_offDiag, mem_map]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨(x, y), ⟨hx, hy, fun h => hxy (congrArg e h)⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, h⟩
    have h' : (e x, e y) = (p, q) := h
    cases h'
    exact ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, fun he => hxy (e.injective he)⟩

private theorem distances_le_four (S : Finset (ℤ × ℤ))
    (hc : S.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues) :
    distinctDistances (S.map lattice) ≤ 4 := by
  classical
  unfold distinctDistances distanceSet
  apply le_trans (card_le_card (t := squaredValues.image (fun z : ℤ => Real.sqrt (z : ℝ))) ?_)
    ((card_image_le).trans (by decide))
  intro d hd
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
  rw [offDiag_map] at hp
  obtain ⟨q, hq, rfl⟩ := mem_map.mp hp
  refine mem_image.mpr ⟨squareDistance q.1 q.2, ?_, ?_⟩
  · rw [← hc]
    exact mem_image.mpr ⟨q, hq, rfl⟩
  · change Real.sqrt (squareDistance q.1 q.2 : ℝ) = dist (lattice q.1) (lattice q.2)
    rw [← lattice_square, Real.sqrt_sq dist_nonneg]

private theorem unit_minimum (S : Finset (ℤ × ℤ))
    (hc : S.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues) :
    (∀ z ∈ (S.map lattice).offDiag, (1 : ℝ) ≤ dist z.1 z.2 ^ 2) ∧
      ∃ z ∈ (S.map lattice).offDiag, dist z.1 z.2 ^ 2 = (1 : ℝ) := by
  rw [offDiag_map]
  constructor
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := mem_map.mp hz
    change (1 : ℝ) ≤ dist (lattice q.1) (lattice q.2) ^ 2
    rw [lattice_square]
    have h : squareDistance q.1 q.2 ∈ squaredValues := by
      rw [← hc]
      exact mem_image.mpr ⟨q, hq, rfl⟩
    simp only [squaredValues, mem_insert, mem_singleton] at h
    rcases h with h | h | h | h <;> rw [h] <;> norm_num
  · have h : (1 : ℤ) ∈ S.offDiag.image (fun p => squareDistance p.1 p.2) := by
      rw [hc]
      decide
    obtain ⟨q, hq, h1⟩ := mem_image.mp h
    refine ⟨(lattice.prodMap lattice) q, mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    change dist (lattice q.1) (lattice q.2) ^ 2 = 1
    rw [lattice_square, h1, Int.cast_one]

private noncomputable def unitCount (S : Finset ℝ²) : ℕ :=
  S.offDiag.filter (fun z => dist z.1 z.2 ^ 2 = (1 : ℝ)) |>.card

private theorem unitCount_lattice (S : Finset (ℤ × ℤ)) :
    unitCount (S.map lattice) = (S.offDiag.filter fun z => squareDistance z.1 z.2 = 1).card := by
  classical
  rw [unitCount, offDiag_map, filter_map, card_map]
  congr 1
  ext z
  simp only [mem_filter, Function.comp_apply]
  change (z ∈ S.offDiag ∧ dist (lattice z.1) (lattice z.2) ^ 2 = 1) ↔
    z ∈ S.offDiag ∧ squareDistance z.1 z.2 = 1
  rw [lattice_square, ← Int.cast_one (R := ℝ), Int.cast_inj]

private theorem first_units : (firstPoints.offDiag.filter
    fun z => squareDistance z.1 z.2 = 1).card = 20 := by decide

private theorem second_units : (secondPoints.offDiag.filter
    fun z => squareDistance z.1 z.2 = 1).card = 28 := by decide

private theorem unitCount_invariant (A B : Finset ℝ²)
    (hA : (∀ z ∈ A.offDiag, (1 : ℝ) ≤ dist z.1 z.2 ^ 2) ∧
      ∃ z ∈ A.offDiag, dist z.1 z.2 ^ 2 = (1 : ℝ))
    (hB : (∀ z ∈ B.offDiag, (1 : ℝ) ≤ dist z.1 z.2 ^ 2) ∧
      ∃ z ∈ B.offDiag, dist z.1 z.2 ^ 2 = (1 : ℝ))
    (hs : DilationEquivSimilar A B) : unitCount A = unitCount B := by
  classical
  obtain ⟨f, hf⟩ := hs
  let e : ℝ² ↪ ℝ² := ⟨f, f.injective⟩
  have hmap : A.map e = B := by
    ext p
    rw [mem_map]
    change (∃ q ∈ (A : Set ℝ²), f q = p) ↔ p ∈ (B : Set ℝ²)
    rw [← hf]
    rfl
  have hpair : A.offDiag.map (e.prodMap e) = B.offDiag :=
    (offDiag_map e A).symm.trans (congrArg Finset.offDiag hmap)
  have hsquare (z : ℝ² × ℝ²) :
      dist ((e.prodMap e) z).1 ((e.prodMap e) z).2 ^ 2 =
        (Dilation.ratio f : ℝ) ^ 2 * dist z.1 z.2 ^ 2 := by
    change dist (f z.1) (f z.2) ^ 2 = _
    rw [Dilation.dist_eq, mul_pow]
  have hratio : (Dilation.ratio f : ℝ) ^ 2 = 1 := by
    apply le_antisymm
    · obtain ⟨z, hz, hd⟩ := hB.2
      rw [← hpair] at hz
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hz
      rw [hsquare] at hd
      calc
        (Dilation.ratio f : ℝ) ^ 2 = (Dilation.ratio f : ℝ) ^ 2 * 1 := by ring
        _ ≤ (Dilation.ratio f : ℝ) ^ 2 * dist u.1 u.2 ^ 2 :=
          mul_le_mul_of_nonneg_left (hA.1 u hu) (sq_nonneg _)
        _ = 1 := hd
    · obtain ⟨z, hz, hd⟩ := hA.2
      have hzB : (e.prodMap e) z ∈ B.offDiag := by
        rw [← hpair]
        exact mem_map.mpr ⟨z, hz, rfl⟩
      have hh := hB.1 _ hzB
      rwa [hsquare, hd, mul_one] at hh
  unfold unitCount
  rw [← hpair, filter_map, card_map]
  congr 1
  ext z
  simp only [mem_filter, Function.comp_apply, hsquare, hratio, one_mul]

theorem witnesses :
    ∃ A B : Finset ℝ², A.card = 8 ∧ B.card = 8 ∧
      distinctDistances A ≤ 4 ∧ distinctDistances B ≤ 4 ∧ ¬DilationEquivSimilar A B := by
  refine ⟨firstPoints.map lattice, secondPoints.map lattice, ?_, ?_,
    distances_le_four _ first_values, distances_le_four _ second_values, ?_⟩
  · rw [card_map]
    decide
  · rw [card_map]
    decide
  · intro h
    have hc := unitCount_invariant _ _ (unit_minimum _ first_values) (unit_minimum _ second_values) h
    rw [unitCount_lattice, unitCount_lattice, first_units, second_units] at hc
    omega

end OMA.Erdos91Eight

theorem OMA.solution : OMA.R_Erdos91_erdos_91_variants_eight_R1.H2 := by
  exact OMA.Erdos91Eight.witnesses
