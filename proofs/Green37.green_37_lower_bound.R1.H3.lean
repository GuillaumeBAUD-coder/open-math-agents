import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step Green37.green_37_lower_bound.R1.H3: hypothesis H3 of reduction Green37.green_37_lower_bound.R1
-- Credit: @anmolspace
-- Proof: a cover for d = 1 needs an element, so m N 1 >= 1; for k = 2 each d in [1, N] gives a pair
-- (a, a + d) in A, and the pairs (a, a+d), (a+d, a) are 2N distinct off-diagonal pairs of A.

namespace OMA.SG37H3

lemma apcard (a d k : ℕ) (hd : 0 < d) :
    ENat.card ({a + n • d | (n : ℕ) (_ : n < ((k : ℕ) : ℕ∞))} : Set ℕ) = k := by
  have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro x y h
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
  have e : ({a + n • d | (n : ℕ) (_ : n < ((k : ℕ) : ℕ∞))} : Set ℕ)
      = (((Finset.range k).image (fun n : ℕ => a + n * d) : Finset ℕ) : Set ℕ) := by
    ext x
    simp [smul_eq_mul]
  rw [e]
  change (((Finset.range k).image (fun n : ℕ => a + n * d) : Finset ℕ) : Set ℕ).encard = k
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj, Finset.card_range]

lemma cover_nonempty (N k : ℕ) :
    {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k}.Nonempty := by
  refine ⟨_, Finset.range (k * N + 1), rfl, ?_⟩
  intro d hd
  unfold Set.ContainsAP
  refine ⟨0, {0 + n • d | (n : ℕ) (_ : n < ((k : ℕ) : ℕ∞))}, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := hx
    have hn' : n < k := by exact_mod_cast hn
    have hle : n * d ≤ k * N := Nat.mul_le_mul (le_of_lt hn') hd.2
    rw [Finset.mem_coe, Finset.mem_range, smul_eq_mul, zero_add]
    exact Nat.lt_succ_of_le hle
  · unfold Set.IsAPOfLengthWith
    exact ⟨apcard 0 d k (by omega), rfl⟩

lemma mem_ap (a d n k : ℕ) (hn : n < k) :
    a + n * d ∈ ({a + n • d | (n : ℕ) (_ : n < ((k : ℕ) : ℕ∞))} : Set ℕ) :=
  ⟨n, Nat.cast_lt.mpr hn, by rw [smul_eq_mul]⟩

lemma two_mem (A : Set ℕ) (d : ℕ) (h : Set.ContainsAP A 2 d) : ∃ a, a ∈ A ∧ a + d ∈ A := by
  obtain ⟨a, s, hsA, hcard, hs⟩ := h
  refine ⟨a, hsA ?_, hsA ?_⟩
  · rw [hs]
    have := mem_ap a d 0 2 (by norm_num)
    simpa using this
  · rw [hs]
    have := mem_ap a d 1 2 (by norm_num)
    simpa using this

theorem part1 : ∀ N : ℕ, 1 ≤ N → 1 ≤ Green37.m N 1 := by
  intro N hN
  obtain ⟨A, hA, hcov⟩ := Nat.sInf_mem (cover_nonempty N 1)
  unfold Green37.m
  rw [← hA]
  obtain ⟨a, s, hsA, hcard, hs⟩ := hcov 1 ⟨le_refl 1, hN⟩
  have ha : a ∈ (A : Set ℕ) := by
    apply hsA
    rw [hs]
    have := mem_ap a 1 0 1 (by norm_num)
    simpa using this
  exact Finset.card_pos.mpr ⟨a, ha⟩

theorem part2 : ∀ N : ℕ, 2 * N ≤ Green37.m N 2 * (Green37.m N 2 - 1) := by
  intro N
  classical
  obtain ⟨A, hA, hcov⟩ := Nat.sInf_mem (cover_nonempty N 2)
  unfold Green37.m
  rw [← hA]
  have hc : ∀ d ∈ Finset.Icc 1 N, ∃ a, a ∈ (A : Set ℕ) ∧ a + d ∈ (A : Set ℕ) := by
    intro d hd
    exact two_mem _ d (hcov d (Finset.mem_Icc.mp hd))
  choose! f hf using hc
  have h1 : ((Finset.Icc 1 N).image (fun d => (f d, f d + d))).card = N := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      omega
  have h2 : ((Finset.Icc 1 N).image (fun d => (f d + d, f d))).card = N := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      omega
  have hdisj : Disjoint ((Finset.Icc 1 N).image (fun d => (f d, f d + d)))
      ((Finset.Icc 1 N).image (fun d => (f d + d, f d))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp1
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hp2
    rw [Finset.mem_Icc] at hx hy
    simp only [Prod.mk.injEq] at hxy
    omega
  have hsub : (Finset.Icc 1 N).image (fun d => (f d, f d + d))
      ∪ (Finset.Icc 1 N).image (fun d => (f d + d, f d)) ⊆ A.offDiag := by
    intro p hp
    rw [Finset.mem_offDiag]
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨ha, hb⟩ := hf x hx
      have hx1 := (Finset.mem_Icc.mp hx).1
      exact ⟨Finset.mem_coe.mp ha, Finset.mem_coe.mp hb, by simp only; omega⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨ha, hb⟩ := hf x hx
      have hx1 := (Finset.mem_Icc.mp hx).1
      exact ⟨Finset.mem_coe.mp hb, Finset.mem_coe.mp ha, by simp only; omega⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, h1, h2, Finset.offDiag_card] at hle
  rw [Nat.mul_sub_one]
  calc 2 * N = N + N := by ring
    _ ≤ _ := hle

end OMA.SG37H3

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 :=
  ⟨OMA.SG37H3.part1, OMA.SG37H3.part2⟩
