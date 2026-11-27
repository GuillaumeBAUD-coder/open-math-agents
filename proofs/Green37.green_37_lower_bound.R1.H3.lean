import OMAReductions.R_Green37_green_37_lower_bound_R1

lemma OMA.min_cover (N k : ℕ) :
    ∃ A : Finset ℕ, A.card = Green37.m N k ∧ Green37.IsAPCover (A : Set ℕ) N k := by
  let S : Set ℕ := {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k}
  have hne : S.Nonempty := by
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
  change sInf S ∈ S
  exact Nat.sInf_mem hne

lemma OMA.cover_pair (A : Finset ℕ) (N d : ℕ)
    (hA : Green37.IsAPCover (A : Set ℕ) N 2) (hd : d ∈ Finset.Icc 1 N) :
    ∃ a : ℕ, a ∈ A ∧ a + d ∈ A := by
  obtain ⟨a, s, hs, hap⟩ := hA d (Finset.mem_Icc.mp hd)
  refine ⟨a, hs ?_, hs ?_⟩
  · rw [hap.2]
    exact ⟨0, by norm_num, by simp⟩
  · rw [hap.2]
    exact ⟨1, by norm_num, by simp⟩

lemma OMA.cover_count (A : Finset ℕ) (N : ℕ)
    (hA : Green37.IsAPCover (A : Set ℕ) N 2) :
    2 * N ≤ A.card * (A.card - 1) := by
  classical
  have hwit : ∀ d : ℕ, ∃ a : ℕ, d ∈ Finset.Icc 1 N → a ∈ A ∧ a + d ∈ A := by
    intro d
    by_cases hd : d ∈ Finset.Icc 1 N
    · obtain ⟨a, ha, hb⟩ := OMA.cover_pair A N d hA hd
      exact ⟨a, fun _ => ⟨ha, hb⟩⟩
    · exact ⟨0, fun h => False.elim (hd h)⟩
  choose f hf using hwit
  have hc : (Finset.Icc 1 N).card ≤ ((A ×ˢ A).filter (fun p => p.1 < p.2)).card := by
    apply Finset.card_le_card_of_injOn (fun d => (f d, f d + d))
    · intro d hd
      have hfd := hf d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hfd.1, hfd.2⟩, by omega⟩
    · intro d hd e he hde
      have hfirst := congrArg Prod.fst hde
      have hsecond := congrArg Prod.snd hde
      simp only at hfirst hsecond
      omega
  have hc' : N ≤ A.card.choose 2 := by
    simpa [Finset.card_product_filter_lt] using hc
  rw [Nat.choose_two_right] at hc'
  omega

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  constructor
  · intro N hN
    obtain ⟨A, hcard, hcover⟩ := OMA.min_cover N 1
    obtain ⟨a, s, hs, hap⟩ := hcover 1 ⟨by omega, hN⟩
    have ha : a ∈ A := by
      apply hs
      rw [hap.2]
      exact ⟨0, by norm_num, by simp⟩
    have hpositive : 0 < A.card := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  · intro N
    obtain ⟨A, hcard, hcover⟩ := OMA.min_cover N 2
    have hc := OMA.cover_count A N hcover
    simpa [hcard] using hc
