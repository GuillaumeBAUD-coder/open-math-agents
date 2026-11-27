import OMAReductions.R_Erdos20_erdos_20_R1

/-! Count rainbow colorings on a finite support and average over all colorings. -/

open Finset

namespace OMA.RainbowColoring

lemma count_rainbow {α : Type} [DecidableEq α] (U A : Finset α) (n : ℕ)
    (hAU : A ⊆ U) (hA : A.card = n) :
    (univ.filter fun c : U → Fin n =>
      Function.Bijective (fun x : A => c ⟨x, hAU x.property⟩)).card =
        n.factorial * n ^ (U.card - n) := by
  classical
  let good (c : U → Fin n) :=
    Function.Bijective (fun x : A => c ⟨x, hAU x.property⟩)
  let e : {c : U → Fin n // good c} ≃
      (A ≃ Fin n) × (↥(U \ A) → Fin n) :=
    { toFun := fun c =>
        (Equiv.ofBijective (fun x : A => c.val ⟨x, hAU x.property⟩) c.property,
          fun x => c.val ⟨x, (mem_sdiff.mp x.property).1⟩)
      invFun := fun p =>
        ⟨fun x => if h : x.val ∈ A then p.1 ⟨x, h⟩
          else p.2 ⟨x, mem_sdiff.mpr ⟨x.property, h⟩⟩, by
            change Function.Bijective _
            convert p.1.bijective using 1
            funext x
            simp [x.property]⟩
      left_inv := by
        intro c
        apply Subtype.ext
        funext x
        by_cases h : x.val ∈ A <;> simp [h]
      right_inv := by
        intro p
        apply Prod.ext
        · apply Equiv.ext
          intro x
          simp
        · funext x
          simp [(mem_sdiff.mp x.property).2] }
  rw [← Fintype.card_subtype]
  change Fintype.card {c : U → Fin n // good c} = _
  rw [Fintype.card_congr e, Fintype.card_prod,
    Fintype.card_equiv (A.equivFinOfCardEq hA), Fintype.card_fun]
  simp [Finset.card_sdiff_of_subset hAU, hA]

end OMA.RainbowColoring

-- Step Erdos20.erdos_20.R1.H1: hypothesis H1 of reduction Erdos20.erdos_20.R1
-- Credit: @DeepDuke
-- H1 := ∀ (α : Type) (n : ℕ), 0 < n →     ∀ (F : Finset (Finset α)), (∀ A ∈ F, A.card = n) →       ∃ (c : α → Fin n) (G : Finset (Finset α)),         G ⊆ F ∧         (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧         F.card * n.factorial ≤ G.card * n ^ n

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 := by
  classical
  intro α n hn F hF
  let z : Fin n := ⟨0, hn⟩
  by_cases hEmpty : F = ∅
  · exact ⟨fun _ => z, ∅, by simp [hEmpty], by simp, by simp [hEmpty]⟩
  let U : Finset α := F.biUnion id
  have hAU (A : Finset α) (hA : A ∈ F) : A ⊆ U := by
    intro x hx
    exact mem_biUnion.mpr ⟨A, hA, hx⟩
  let color (c : U → Fin n) (x : α) : Fin n :=
    if hx : x ∈ U then c ⟨x, hx⟩ else z
  let good (c : U → Fin n) (A : Finset α) :=
    Function.Bijective (fun x : A => color c x)
  let score (c : U → Fin n) := (F.filter (good c)).card
  have count (A : Finset α) (hA : A ∈ F) :
      (univ.filter fun c : U → Fin n => good c A).card =
        n.factorial * n ^ (U.card - n) := by
    have heq (c : U → Fin n) :
        (fun x : A => color c x) = (fun x : A => c ⟨x, hAU A hA x.property⟩) := by
      funext x
      simp [color, hAU A hA x.property]
    simpa only [good, heq] using OMA.RainbowColoring.count_rainbow U A n (hAU A hA) (hF A hA)
  have total : (∑ c : U → Fin n, score c) =
      F.card * (n.factorial * n ^ (U.card - n)) := by
    change (∑ c : U → Fin n, (F.filter (good c)).card) = _
    rw [show (∑ c : U → Fin n, (F.filter (good c)).card) =
        ∑ A ∈ F, (univ.filter fun c : U → Fin n => good c A).card from
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow good]
    calc
      (∑ A ∈ F, (univ.filter fun c : U → Fin n => good c A).card) =
          ∑ _A ∈ F, n.factorial * n ^ (U.card - n) :=
        sum_congr rfl (fun A hA => count A hA)
      _ = _ := by simp
  have hnonempty : (univ : Finset (U → Fin n)).Nonempty := ⟨fun _ => z, mem_univ _⟩
  obtain ⟨c, _, hc⟩ := exists_max_image univ score hnonempty
  refine ⟨color c, F.filter (good c), filter_subset _ _, ?_, ?_⟩
  · intro A hA
    exact (mem_filter.mp hA).2
  · have hsum : (∑ d : U → Fin n, score d) ≤ n ^ U.card * score c := by
      calc
        (∑ d : U → Fin n, score d) ≤ ∑ _d : U → Fin n, score c :=
          sum_le_sum hc
        _ = n ^ U.card * score c := by simp
    rw [total] at hsum
    obtain ⟨A, hA⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hnu : n ≤ U.card := (hF A hA) ▸ card_le_card (hAU A hA)
    have hpow : n ^ U.card = n ^ n * n ^ (U.card - n) := by
      rw [← pow_add, Nat.add_sub_of_le hnu]
    rw [hpow] at hsum
    apply Nat.le_of_mul_le_mul_right (c := n ^ (U.card - n))
    · simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsum
    · exact pow_pos hn _

