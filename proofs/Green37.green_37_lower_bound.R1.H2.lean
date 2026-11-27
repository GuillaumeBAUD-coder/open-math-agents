import OMAReductions.R_Green37_green_37_lower_bound_R1

-- Step Green37.green_37_lower_bound.R1.H2: hypothesis H2 of reduction Green37.green_37_lower_bound.R1
-- Credit: @anmolspace
-- Proof: an AP cover with length k2 is one with length k1 <= k2 (truncate each progression),
-- and covers always exist (range (k2*N+1)), so the infimum can only grow with k.

namespace OMA.SG37

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

lemma containsAP_mono (A : Set ℕ) (k1 k2 d : ℕ) (hk : k1 ≤ k2) (hd : 0 < d)
    (h : Set.ContainsAP A k2 d) : Set.ContainsAP A k1 d := by
  obtain ⟨a, s, hsA, hcard, hs⟩ := h
  unfold Set.ContainsAP
  refine ⟨a, {a + n • d | (n : ℕ) (_ : n < ((k1 : ℕ) : ℕ∞))}, ?_, ?_⟩
  · intro x hx
    apply hsA
    rw [hs]
    obtain ⟨n, hn, rfl⟩ := hx
    exact ⟨n, lt_of_lt_of_le hn (Nat.cast_le.mpr hk), rfl⟩
  · unfold Set.IsAPOfLengthWith
    exact ⟨apcard a d k1 hd, rfl⟩

theorem main : ∀ N k₁ k₂ : ℕ, k₁ ≤ k₂ → Green37.m N k₁ ≤ Green37.m N k₂ := by
  intro N k1 k2 hk
  unfold Green37.m
  have hne : {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k2}.Nonempty := by
    refine ⟨_, Finset.range (k2 * N + 1), rfl, ?_⟩
    intro d hd
    unfold Set.ContainsAP
    refine ⟨0, {0 + n • d | (n : ℕ) (_ : n < ((k2 : ℕ) : ℕ∞))}, ?_, ?_⟩
    · intro x hx
      obtain ⟨n, hn, rfl⟩ := hx
      have hn' : n < k2 := by exact_mod_cast hn
      have hle : n * d ≤ k2 * N := Nat.mul_le_mul (le_of_lt hn') hd.2
      rw [Finset.mem_coe, Finset.mem_range, smul_eq_mul, zero_add]
      exact Nat.lt_succ_of_le hle
    · unfold Set.IsAPOfLengthWith
      exact ⟨apcard 0 d k2 (by omega), rfl⟩
  apply Nat.sInf_le
  obtain ⟨A, hA, hcov⟩ := Nat.sInf_mem hne
  exact ⟨A, hA, fun d hd => containsAP_mono _ k1 k2 d hk (by omega) (hcov d hd)⟩

end OMA.SG37

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := OMA.SG37.main
