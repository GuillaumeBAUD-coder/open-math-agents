import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R3.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R3
-- Proof: a Turan / Caro-Wei type greedy bound (repeatedly remove a vertex of minimum closed degree
-- together with its closed neighbourhood) applied to the graph joining the two endpoints of every
-- k-term progression of A; the case p <= k is handled separately.

open Finset

/-- Greedy independence bound: for a symmetric relation `r` on a finite set `A` there is a subset `B`
on which `r` only relates equal points, with `|A|^2 ≤ |B| * (sum of closed degrees)`. -/
theorem OMA.greedy_indep {V : Type*} [DecidableEq V] (r : V → V → Prop) [DecidableRel r]
    (hsymm : ∀ x y, r x y → r y x) :
    ∀ (n : ℕ) (A : Finset V), A.card = n → ∃ B ⊆ A, (∀ x ∈ B, ∀ y ∈ B, r x y → x = y) ∧
      A.card ^ 2 ≤ B.card * ∑ x ∈ A, (A.filter fun y => y = x ∨ r x y).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨v, hvA, hvmin⟩ :=
    Finset.exists_min_image A (fun x => (A.filter fun y => y = x ∨ r x y).card) hne
  have hNA : (A.filter fun y => y = v ∨ r v y) ⊆ A := filter_subset _ _
  have hvN : v ∈ (A.filter fun y => y = v ∨ r v y) := by simp [hvA]
  have hcard : (A \ (A.filter fun y => y = v ∨ r v y)).card + (A.filter fun y => y = v ∨ r v y).card
      = A.card := Finset.card_sdiff_add_card_eq_card hNA
  have hNpos : 0 < (A.filter fun y => y = v ∨ r v y).card := card_pos.mpr ⟨v, hvN⟩
  obtain ⟨B', hB'A, hB'ind, hB'cnt⟩ :=
    ih (A \ (A.filter fun y => y = v ∨ r v y)).card (by omega) _ rfl
  have hvA' : v ∉ A \ (A.filter fun y => y = v ∨ r v y) := by
    intro h
    exact (mem_sdiff.mp h).2 hvN
  refine ⟨insert v B', ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hvA
    · exact sdiff_subset (hB'A hx)
  · have key : ∀ x ∈ B', ¬ r v x := by
      intro x hx hr
      have hxm := mem_sdiff.mp (hB'A hx)
      exact hxm.2 (mem_filter.mpr ⟨hxm.1, Or.inr hr⟩)
    intro x hx y hy hxy
    rcases mem_insert.mp hx with hx' | hx' <;> rcases mem_insert.mp hy with hy' | hy'
    · rw [hx', hy']
    · rw [hx'] at hxy
      exact absurd hxy (key y hy')
    · rw [hy'] at hxy
      exact absurd (hsymm _ _ hxy) (key x hx')
    · exact hB'ind x hx' y hy' hxy
  · rw [card_insert_of_notMem (fun h => hvA' (hB'A h))]
    have h1 : ∑ x ∈ A \ (A.filter fun y => y = v ∨ r v y),
        ((A \ (A.filter fun y => y = v ∨ r v y)).filter fun y => y = x ∨ r x y).card
        ≤ ∑ x ∈ A \ (A.filter fun y => y = v ∨ r v y), (A.filter fun y => y = x ∨ r x y).card :=
      sum_le_sum fun x _ => card_le_card (filter_subset_filter _ sdiff_subset)
    have h2 : ∑ x ∈ A \ (A.filter fun y => y = v ∨ r v y), (A.filter fun y => y = x ∨ r x y).card
        + ∑ x ∈ (A.filter fun y => y = v ∨ r v y), (A.filter fun y => y = x ∨ r x y).card
        = ∑ x ∈ A, (A.filter fun y => y = x ∨ r x y).card := sum_sdiff hNA
    have h3 : (A.filter fun y => y = v ∨ r v y).card * (A.filter fun y => y = v ∨ r v y).card
        ≤ ∑ x ∈ (A.filter fun y => y = v ∨ r v y), (A.filter fun y => y = x ∨ r x y).card := by
      calc (A.filter fun y => y = v ∨ r v y).card * (A.filter fun y => y = v ∨ r v y).card
          = ∑ _x ∈ (A.filter fun y => y = v ∨ r v y), (A.filter fun y => y = v ∨ r v y).card := by
            simp
        _ ≤ _ := sum_le_sum fun x hx => hvmin x (hNA hx)
    have h4 : A.card * (A.filter fun y => y = v ∨ r v y).card
        ≤ ∑ x ∈ A, (A.filter fun y => y = x ∨ r x y).card := by
      calc A.card * (A.filter fun y => y = v ∨ r v y).card
          = ∑ _x ∈ A, (A.filter fun y => y = v ∨ r v y).card := by simp
        _ ≤ _ := sum_le_sum fun x hx => hvmin x hx
    generalize (∑ x ∈ A, (A.filter fun y => y = x ∨ r x y).card) = S at *
    generalize (∑ x ∈ A \ (A.filter fun y => y = v ∨ r v y),
        ((A \ (A.filter fun y => y = v ∨ r v y)).filter fun y => y = x ∨ r x y).card) = S' at *
    generalize (∑ x ∈ A \ (A.filter fun y => y = v ∨ r v y),
        (A.filter fun y => y = x ∨ r x y).card) = S1 at *
    generalize (∑ x ∈ (A.filter fun y => y = v ∨ r v y),
        (A.filter fun y => y = x ∨ r x y).card) = S2 at *
    generalize (A \ (A.filter fun y => y = v ∨ r v y)).card = m at *
    generalize (A.filter fun y => y = v ∨ r v y).card = t at *
    generalize B'.card = b at *
    rw [← hcard]
    rw [← hcard] at h4
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have hm : m = 0 := by
        have : m ^ 2 ≤ 0 := by simpa using hB'cnt
        exact pow_eq_zero_iff (two_ne_zero) |>.mp (Nat.le_zero.mp this)
      subst hm
      nlinarith
    · have hQ : m ^ 2 + b * t ^ 2 ≤ b * S := by nlinarith
      have hmain : b * (m + t) ^ 2 ≤ b * ((b + 1) * S) := by
        zify at hQ ⊢
        nlinarith [sq_nonneg ((m : ℤ) - b * t), mul_le_mul_of_nonneg_left hQ
          (show (0 : ℤ) ≤ (b : ℤ) + 1 by positivity)]
      exact le_of_mul_le_mul_left hmain hb

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3.H2 := by
  classical
  intro p hp k hk A
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases hkp : p ≤ k
  · have hfull : ∀ (B : Finset (ZMod p)) (a d : ZMod p),
        (∀ i : Fin k, a + (i.val : ZMod p) * d ∈ B) → d ≠ 0 → ∀ z, z ∈ B := by
      intro B a d h hd z
      have hlt : ((z - a) / d).val < k := lt_of_lt_of_le (ZMod.val_lt _) hkp
      have h1 := h ⟨_, hlt⟩
      simp only [ZMod.natCast_zmod_val] at h1
      rwa [div_mul_cancel₀ _ hd, add_sub_cancel] at h1
    by_cases hA : ∀ z, z ∈ A
    · refine ⟨{0}, fun x _ => hA x, ?_, ?_⟩
      · intro a d h
        by_contra hd
        have h1 := hfull _ a d h hd 1
        simp at h1
      · have hT : ∀ u ∈ (univ : Finset (ZMod p × ZMod p)),
            ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A := fun u _ i => hA _
        rw [filter_true_of_mem hT, eq_univ_iff_forall.mpr hA]
        simp [sq]
    · refine ⟨A, Subset.refl _, ?_, ?_⟩
      · intro a d h
        by_contra hd
        exact hA (hfull A a d h hd)
      · rw [sq]
        apply Nat.mul_le_mul_left
        apply card_le_card_of_injOn (fun x => ((x, 0) : ZMod p × ZMod p))
        · intro x hx
          simpa using fun _ : Fin k => hx
        · intro x _ y _ h
          simpa using h
  · rw [not_le] at hkp
    have hsymm : ∀ x y : ZMod p,
        (∃ d : ZMod p, (∀ i : Fin k, x + (i.val : ZMod p) * d ∈ A) ∧
          y = x + ((k - 1 : ℕ) : ZMod p) * d) →
        (∃ d : ZMod p, (∀ i : Fin k, y + (i.val : ZMod p) * d ∈ A) ∧
          x = y + ((k - 1 : ℕ) : ZMod p) * d) := by
      rintro x y ⟨d, hd, rfl⟩
      refine ⟨-d, ?_, by ring⟩
      intro i
      have h1 := hd ⟨k - 1 - i.val, by omega⟩
      have h2 : ((k - 1 - i.val : ℕ) : ZMod p) = ((k - 1 : ℕ) : ZMod p) - (i.val : ZMod p) :=
        Nat.cast_sub (by omega)
      simp only [h2] at h1
      have h3 : x + ((k - 1 : ℕ) : ZMod p) * d + (i.val : ZMod p) * -d
          = x + (((k - 1 : ℕ) : ZMod p) - (i.val : ZMod p)) * d := by ring
      rw [h3]
      exact h1
    obtain ⟨B, hBA, hind, hcnt⟩ := OMA.greedy_indep
      (fun x y : ZMod p => ∃ d : ZMod p, (∀ i : Fin k, x + (i.val : ZMod p) * d ∈ A) ∧
          y = x + ((k - 1 : ℕ) : ZMod p) * d) hsymm A.card A rfl
    refine ⟨B, hBA, ?_, ?_⟩
    · intro a d h
      have hx : a ∈ B := by simpa using h ⟨0, by omega⟩
      have hy : a + ((k - 1 : ℕ) : ZMod p) * d ∈ B := h ⟨k - 1, by omega⟩
      have h1 := hind a hx _ hy ⟨d, fun i => hBA (h i), rfl⟩
      have h0 : ((k - 1 : ℕ) : ZMod p) * d = 0 := by
        have h2 : a + ((k - 1 : ℕ) : ZMod p) * d = a + 0 := by rw [add_zero]; exact h1.symm
        exact add_left_cancel h2
      rcases mul_eq_zero.mp h0 with h3 | h3
      · exfalso
        rw [ZMod.natCast_eq_zero_iff] at h3
        have := Nat.le_of_dvd (by omega) h3
        omega
      · exact h3
    · refine hcnt.trans (Nat.mul_le_mul_left _ ?_)
      rw [← card_sigma]
      apply card_le_card_of_surjOn
        (fun u : ZMod p × ZMod p =>
          (⟨u.1, u.1 + ((k - 1 : ℕ) : ZMod p) * u.2⟩ : Σ _ : ZMod p, ZMod p))
      rintro ⟨x, y⟩ hs
      obtain ⟨hxA, hf⟩ := mem_sigma.mp (mem_coe.mp hs)
      dsimp only at hxA hf
      rcases (mem_filter.mp hf).2 with hxy | ⟨d, hd, hxy⟩
      · refine ⟨(x, 0), ?_, ?_⟩
        · simpa using fun _ : Fin k => hxA
        · simp [hxy]
      · refine ⟨(x, d), ?_, ?_⟩
        · simpa using hd
        · simp [hxy]
