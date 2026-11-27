import OMAReductions.R_Erdos92_erdos_92_variants_weak_R1

-- Step Erdos92.erdos_92.variants.weak.R1.H2: hypothesis H2 of reduction Erdos92.erdos_92.variants.weak.R1

/-!
Degeneracy. Let `D' = ⌊D⌋`. In any non-empty `Q ⊆ P` some point has at most `D'` points of `Q` at
distance one: otherwise every point of `Q` would have at least `D' + 1` equidistant points, giving
`D' + 1 ≤ f |Q| ≤ D'`. Removing such a point removes at most `D'` unit distances, so by induction
`Q` has at most `|Q| D'` unit distances.
-/

open scoped Classical

namespace OMA

/-- The number of points of `Q` at distance one from `x`. -/
noncomputable def udeg (x : EuclideanSpace ℝ (Fin 2)) (Q : Finset (EuclideanSpace ℝ (Fin 2))) :
    ℕ := ((Q.erase x).filter fun p => dist x p = 1).card

theorem udeg_le_max (x : EuclideanSpace ℝ (Fin 2)) (Q : Finset (EuclideanSpace ℝ (Fin 2)))
    (h : 1 ≤ udeg x Q) : udeg x Q ≤ Erdos92.maxEquidistantPointsAt x Q := by
  unfold Erdos92.maxEquidistantPointsAt
  apply le_csSup (Finset.bddAbove _)
  rw [Finset.mem_coe, Finset.mem_image]
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  refine ⟨1, ?_, rfl⟩
  rw [Finset.mem_image]
  exact ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩

theorem exists_low (Q : Finset (EuclideanSpace ℝ (Fin 2))) (hQ : Q.Nonempty) (D' : ℕ)
    (hf : Erdos92.f Q.card ≤ D') : ∃ x ∈ Q, udeg x Q ≤ D' := by
  by_contra hcon
  push_neg at hcon
  have hprop : Erdos92.hasMinEquidistantProperty (D' + 1) Q :=
    ⟨hQ, fun x hx => le_trans (Nat.succ_le_of_lt (hcon x hx))
      (udeg_le_max x Q (by have := hcon x hx; omega))⟩
  have hmem : D' + 1 ∈ Erdos92.possible_f_values Q.card := ⟨Q, rfl, hprop⟩
  have hle : D' + 1 ≤ Erdos92.f Q.card :=
    le_csSup (Erdos92.possible_f_values_BddAbove Q.card) hmem
  omega

theorem unit_erase (Q : Finset (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2)) :
    unitDistNum Q ≤ unitDistNum (Q.erase x) + udeg x Q := by
  unfold unitDistNum udeg
  have hsub : Q.sym2.filter (fun p => dist p.out.1 p.out.2 = 1) ⊆
      (Q.erase x).sym2.filter (fun p => dist p.out.1 p.out.2 = 1) ∪
        ((Q.erase x).filter (fun p => dist x p = 1)).image (fun y => s(x, y)) := by
    intro p hp
    obtain ⟨hpQ, hpd⟩ := Finset.mem_filter.mp hp
    obtain ⟨ab, hpout⟩ : ∃ ab, p.out = ab := ⟨_, rfl⟩
    obtain ⟨a, b⟩ := ab
    have hout : s(a, b) = p := by
      have h := Quot.out_eq p
      rw [hpout] at h
      exact h
    rw [hpout] at hpd
    have hpd' : dist a b = 1 := hpd
    have ha : a ∈ Q := (Finset.mem_sym2_iff.mp hpQ) a (by rw [← hout]; exact Sym2.mem_mk_left a b)
    have hb : b ∈ Q := (Finset.mem_sym2_iff.mp hpQ) b (by rw [← hout]; exact Sym2.mem_mk_right a b)
    have hab : a ≠ b := by
      intro h
      rw [h, dist_self] at hpd'
      norm_num at hpd'
    by_cases hax : a = x
    · rw [← hax]
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨fun h => hab h.symm, hb⟩, hpd'⟩, hout⟩
    · by_cases hbx : b = x
      · rw [← hbx]
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hab, ha⟩, by rw [dist_comm]; exact hpd'⟩,
          by rw [Sym2.eq_swap]; exact hout⟩
      · apply Finset.mem_union_left
        refine Finset.mem_filter.mpr ⟨?_, hp |> Finset.mem_filter.mp |>.2⟩
        rw [Finset.mem_sym2_iff]
        intro c hc
        rw [← hout, Sym2.mem_iff] at hc
        rcases hc with rfl | rfl
        · exact Finset.mem_erase.mpr ⟨hax, ha⟩
        · exact Finset.mem_erase.mpr ⟨hbx, hb⟩
  calc (Q.sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).card
      ≤ ((Q.erase x).sym2.filter (fun p => dist p.out.1 p.out.2 = 1) ∪
          ((Q.erase x).filter (fun p => dist x p = 1)).image (fun y => s(x, y))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Q.erase x).sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).card +
          (((Q.erase x).filter (fun p => dist x p = 1)).image (fun y => s(x, y))).card :=
        Finset.card_union_le _ _
    _ ≤ ((Q.erase x).sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).card +
          ((Q.erase x).filter (fun p => dist x p = 1)).card :=
        Nat.add_le_add_left Finset.card_image_le _

theorem main_bound (P : Finset (EuclideanSpace ℝ (Fin 2))) (D' : ℕ)
    (hf : ∀ m ≤ P.card, Erdos92.f m ≤ D') :
    ∀ k : ℕ, ∀ Q : Finset (EuclideanSpace ℝ (Fin 2)), Q ⊆ P → Q.card = k →
      unitDistNum Q ≤ k * D' := by
  intro k
  induction k with
  | zero =>
    intro Q _ hQ
    rw [Finset.card_eq_zero] at hQ
    subst hQ
    simp [unitDistNum]
  | succ k ih =>
    intro Q hQP hQ
    have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx, hdeg⟩ := exists_low Q hne D' (hf _ (Finset.card_le_card hQP))
    have h1 := unit_erase Q x
    have h2 := ih (Q.erase x) ((Finset.erase_subset x Q).trans hQP)
      (by rw [Finset.card_erase_of_mem hx, hQ]; rfl)
    have e : (k + 1) * D' = k * D' + D' := by ring
    omega

end OMA

theorem OMA.solution : OMA.R_Erdos92_erdos_92_variants_weak_R1.H2 := by
  unfold OMA.R_Erdos92_erdos_92_variants_weak_R1.H2
  intro P D hD
  have hD0 : 0 ≤ D := le_trans (Nat.cast_nonneg _) (hD 0 (Nat.zero_le _))
  have hf : ∀ m ≤ P.card, Erdos92.f m ≤ ⌊D⌋₊ := fun m hm => Nat.le_floor (hD m hm)
  have h := OMA.main_bound P ⌊D⌋₊ hf P.card P (Finset.Subset.refl _) rfl
  have h1 : (unitDistNum P : ℝ) ≤ (P.card : ℝ) * ((⌊D⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
  have h2 : ((⌊D⌋₊ : ℕ) : ℝ) ≤ D := Nat.floor_le hD0
  have hc : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 hc, mul_nonneg hc hD0]
