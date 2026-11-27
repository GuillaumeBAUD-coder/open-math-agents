import OMAReductions.R_Erdos100_erdos_100_variants_guth_katz_R1

/-! Every distance between two points of A lies in [0, diam A], and two different distances
differ by at least 1, so the integer part is injective on the set of distances and takes
values in {0, ..., floor (diam A)}. -/

theorem OMA.solution : OMA.R_Erdos100_erdos_100_variants_guth_katz_R1.H2 := by
  intro A hsep
  have hM0 : 0 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) := Metric.diam_nonneg
  have hbd : ∀ d ∈ distanceSet A,
      0 ≤ d ∧ d ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro d hd
    rw [distanceSet, Finset.mem_image] at hd
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hd
    rw [Finset.mem_offDiag] at hpq
    exact ⟨dist_nonneg, Metric.dist_le_diam_of_mem A.finite_toSet.isBounded
      (Finset.mem_coe.2 hpq.1) (Finset.mem_coe.2 hpq.2.1)⟩
  have hsepD : ∀ x ∈ distanceSet A, ∀ y ∈ distanceSet A, x ≠ y → 1 ≤ |x - y| := by
    intro x hx y hy hne
    rw [distanceSet, Finset.mem_image] at hx hy
    obtain ⟨⟨p1, q1⟩, h1, rfl⟩ := hx
    obtain ⟨⟨p2, q2⟩, h2, rfl⟩ := hy
    rw [Finset.mem_offDiag] at h1 h2
    exact hsep p1 q1 p2 q2 h1.1 h1.2.1 h2.1 h2.2.1 hne
  have hinj : Set.InjOn (fun x : ℝ => ⌊x⌋₊) (distanceSet A : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have h := hsepD x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy) hne
    have hx0 := (hbd x (Finset.mem_coe.1 hx)).1
    have hy0 := (hbd y (Finset.mem_coe.1 hy)).1
    have e : ⌊x⌋₊ = ⌊y⌋₊ := hxy
    have h1 := Nat.floor_le hx0
    have h2 := Nat.lt_floor_add_one x
    have h3 := Nat.floor_le hy0
    have h4 := Nat.lt_floor_add_one y
    rw [e] at h1 h2
    rcases abs_cases (x - y) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] at h <;> linarith
  have hmaps : ∀ x ∈ distanceSet A,
      ⌊x⌋₊ ∈ Finset.range (⌊Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2)))⌋₊ + 1) := by
    intro x hx
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.floor_le_floor (hbd x hx).2)
  have hcard := Finset.card_le_card_of_injOn (fun x : ℝ => ⌊x⌋₊) hmaps hinj
  rw [Finset.card_range] at hcard
  have h5 : (distinctDistances A : ℝ) ≤
      (⌊Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2)))⌋₊ : ℝ) + 1 := by
    unfold distinctDistances
    exact_mod_cast hcard
  linarith [Nat.floor_le hM0]
