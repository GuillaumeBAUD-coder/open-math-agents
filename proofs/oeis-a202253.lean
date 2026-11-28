import OMAStatements.S_oeis_a202253

namespace OeisA202253Proof

open Finset OMA.S_oeis_a202253

private noncomputable def uvSet (n : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter fun p => p.1 % 3 = p.2 % 3

private lemma card_arrays_eq_card_uvSet (n : ℕ) : (arrays n).card = (uvSet n).card := by
  refine Finset.card_bij (fun t _ => (t.1 - t.2.1, t.2.1 - t.2.2)) ?_ ?_ ?_
  · intro ⟨x, y, z⟩ ht
    simp only [arrays, mem_filter, mem_product, mem_Icc] at ht
    simp only [uvSet, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨ht.2.2.1, ht.2.2.2.1⟩, ⟨ht.2.2.2.2.1, ht.2.2.2.2.2⟩⟩, ?_⟩
    omega
  · intro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ heq
    simp only [arrays, mem_filter, mem_product, mem_Icc] at h₁ h₂
    simp only [Prod.mk.injEq] at heq
    have hx : x₁ = x₂ := by omega
    have hy : y₁ = y₂ := by omega
    have hz : z₁ = z₂ := by omega
    subst hx; subst hy; subst hz; rfl
  · intro ⟨u, v⟩ huv
    simp only [uvSet, mem_filter, mem_product, mem_Icc] at huv
    rcases huv with ⟨⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩, hmod⟩
    set y : ℤ := (v - u) / 3
    set x : ℤ := y + u
    set z : ℤ := y - v
    refine ⟨(x, y, z), ?_, ?_⟩
    · simp only [arrays, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
        by omega, by omega, by omega, by omega, by omega⟩
    · simp only [Prod.mk.injEq]
      exact ⟨by omega, by omega⟩

private noncomputable def resCount (n : ℕ) (r : ℤ) : ℕ :=
  ((Icc (-(n : ℤ)) n).filter fun u => u % 3 = r).card

private lemma card_uvSet_eq_sum_sq (n : ℕ) :
    (uvSet n).card = resCount n 0 ^ 2 + resCount n 1 ^ 2 + resCount n 2 ^ 2 := by
  set S0 := (Icc (-(n : ℤ)) n).filter fun u => u % 3 = 0
  set S1 := (Icc (-(n : ℤ)) n).filter fun u => u % 3 = 1
  set S2 := (Icc (-(n : ℤ)) n).filter fun u => u % 3 = 2
  have hunion : uvSet n = (S0 ×ˢ S0) ∪ (S1 ×ˢ S1) ∪ (S2 ×ˢ S2) := by
    ext ⟨u, v⟩
    simp only [uvSet, S0, S1, S2, mem_union, mem_product, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hu, hv⟩, hmod⟩
      have hcases : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
      rcases hcases with h | h | h
      · left; left; exact ⟨⟨hu, h⟩, ⟨hv, hmod.symm.trans h⟩⟩
      · left; right; exact ⟨⟨hu, h⟩, ⟨hv, hmod.symm.trans h⟩⟩
      · right; exact ⟨⟨hu, h⟩, ⟨hv, hmod.symm.trans h⟩⟩
    · rintro ((⟨⟨hu, h1⟩, ⟨hv, h2⟩⟩ | ⟨⟨hu, h1⟩, ⟨hv, h2⟩⟩) | ⟨⟨hu, h1⟩, ⟨hv, h2⟩⟩) <;>
        exact ⟨⟨hu, hv⟩, by omega⟩
  have hdisj01 : Disjoint (S0 ×ˢ S0) (S1 ×ˢ S1) := by
    rw [Finset.disjoint_left]
    intro ⟨u, v⟩ h1 h2
    simp only [S0, S1, mem_product, mem_filter] at h1 h2
    omega
  have hdisj012 : Disjoint ((S0 ×ˢ S0) ∪ (S1 ×ˢ S1)) (S2 ×ˢ S2) := by
    rw [Finset.disjoint_left]
    intro ⟨u, v⟩ h1 h2
    simp only [S0, S1, S2, mem_union, mem_product, mem_filter] at h1 h2
    rcases h1 with h1 | h1 <;> omega
  rw [hunion, Finset.card_union_of_disjoint hdisj012, Finset.card_union_of_disjoint hdisj01,
      Finset.card_product, Finset.card_product, Finset.card_product]
  simp only [resCount, S0, S1, S2, sq]

private lemma card_filter_mod3 (n : ℕ) (r : ℤ) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    resCount n r = ((Icc ((-(n : ℤ) - r + 2) / 3) ((n - r) / 3)).card) := by
  unfold resCount
  refine Finset.card_bij (fun u _ => (u - r) / 3) ?_ ?_ ?_
  · intro u hu
    simp only [mem_filter, mem_Icc] at hu
    simp only [mem_Icc]
    omega
  · intro u₁ h₁ u₂ h₂ heq
    simp only [mem_filter, mem_Icc] at h₁ h₂
    omega
  · intro k hk
    simp only [mem_Icc] at hk
    refine ⟨3 * k + r, ?_, ?_⟩
    · simp only [mem_filter, mem_Icc]
      refine ⟨⟨by omega, by omega⟩, by omega⟩
    · omega

theorem main_proof : ∀ n : ℕ, 1 ≤ n → a n = 1 + 2 * ((2 * n ^ 2 + 2 * n) / 3) := by
  intro n _hn
  unfold a
  rw [card_arrays_eq_card_uvSet, card_uvSet_eq_sum_sq,
      card_filter_mod3 n 0 (by omega) (by omega),
      card_filter_mod3 n 1 (by omega) (by omega),
      card_filter_mod3 n 2 (by omega) (by omega),
      Int.card_Icc, Int.card_Icc, Int.card_Icc]
  set q := n / 3
  have hmod : n = 3 * q ∨ n = 3 * q + 1 ∨ n = 3 * q + 2 := by omega
  rcases hmod with h | h | h
  · have hc0 : (((n : ℤ) - 0) / 3 + 1 - (-(n : ℤ) - 0 + 2) / 3).toNat = 2 * q + 1 := by omega
    have hc1 : (((n : ℤ) - 1) / 3 + 1 - (-(n : ℤ) - 1 + 2) / 3).toNat = 2 * q := by omega
    have hc2 : (((n : ℤ) - 2) / 3 + 1 - (-(n : ℤ) - 2 + 2) / 3).toNat = 2 * q := by omega
    have hdiv : (2 * n ^ 2 + 2 * n) / 3 = 6 * q ^ 2 + 2 * q := by
      have : 2 * n ^ 2 + 2 * n = 3 * (6 * q ^ 2 + 2 * q) := by rw [h]; ring
      omega
    rw [hc0, hc1, hc2, hdiv]
    ring
  · have hc0 : (((n : ℤ) - 0) / 3 + 1 - (-(n : ℤ) - 0 + 2) / 3).toNat = 2 * q + 1 := by omega
    have hc1 : (((n : ℤ) - 1) / 3 + 1 - (-(n : ℤ) - 1 + 2) / 3).toNat = 2 * q + 1 := by omega
    have hc2 : (((n : ℤ) - 2) / 3 + 1 - (-(n : ℤ) - 2 + 2) / 3).toNat = 2 * q + 1 := by omega
    have hdiv : (2 * n ^ 2 + 2 * n) / 3 = 6 * q ^ 2 + 6 * q + 1 := by
      have : 2 * n ^ 2 + 2 * n = 3 * (6 * q ^ 2 + 6 * q + 1) + 1 := by rw [h]; ring
      omega
    rw [hc0, hc1, hc2, hdiv]
    ring
  · have hc0 : (((n : ℤ) - 0) / 3 + 1 - (-(n : ℤ) - 0 + 2) / 3).toNat = 2 * q + 1 := by omega
    have hc1 : (((n : ℤ) - 1) / 3 + 1 - (-(n : ℤ) - 1 + 2) / 3).toNat = 2 * q + 2 := by omega
    have hc2 : (((n : ℤ) - 2) / 3 + 1 - (-(n : ℤ) - 2 + 2) / 3).toNat = 2 * q + 2 := by omega
    have hdiv : (2 * n ^ 2 + 2 * n) / 3 = 6 * q ^ 2 + 10 * q + 4 := by
      have : 2 * n ^ 2 + 2 * n = 3 * (6 * q ^ 2 + 10 * q + 4) := by rw [h]; ring
      omega
    rw [hc0, hc1, hc2, hdiv]
    ring

end OeisA202253Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a202253.main :=
  OeisA202253Proof.main_proof
