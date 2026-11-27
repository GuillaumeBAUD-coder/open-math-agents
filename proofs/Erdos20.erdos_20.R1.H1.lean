import OMAReductions.R_Erdos20_erdos_20_R1

-- Step Erdos20.erdos_20.R1.H1: hypothesis H1 of reduction Erdos20.erdos_20.R1
-- Credit: @smurali12
-- H1 := ∀ (α : Type) (n : ℕ), 0 < n →     ∀ (F : Finset (Finset α)), (∀ A ∈ F, A.card = n) →       ∃ (c : α → Fin n) (G : Finset (Finset α)),         G ⊆ F ∧         (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧         F.card * n.factorial ≤ G.card * n ^ n

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 := by
  classical
  intro α n hn F hF
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · exact ⟨fun _ => ⟨0, hn⟩, ∅, Finset.Subset.refl _, fun _ h => by simp at h, by simp⟩
  let U : Finset α := F.biUnion id
  have hnU : n ≤ U.card := by
    obtain ⟨A₀, hA₀⟩ := hFne
    rw [← hF A₀ hA₀]
    exact Finset.card_le_card (Finset.subset_biUnion_of_mem id hA₀)
  let extend : (U → Fin n) → α → Fin n := fun f x => if hx : x ∈ U then f ⟨x, hx⟩ else ⟨0, hn⟩
  let good : (U → Fin n) → Finset (Finset α) :=
    fun f => F.filter (fun A => Function.Bijective (fun x : A => extend f x))
  have hcount :
      ∑ f : U → Fin n, (good f).card =
        ∑ A ∈ F, (Finset.univ.filter (fun f : U → Fin n =>
          Function.Bijective (fun x : A => extend f x))).card := by
    simp_rw [good, Finset.card_filter]
    rw [Finset.sum_comm]
  have hfiber :
      ∀ A ∈ F,
        (Finset.univ.filter (fun f : U → Fin n =>
          Function.Bijective (fun x : A => extend f x))).card =
          n.factorial * n ^ (U.card - n) := by
    intro A hA
    have hAU : A ⊆ U := Finset.subset_biUnion_of_mem id hA
    let S := Finset.univ.filter (fun f : U → Fin n =>
      Function.Bijective (fun x : A => extend f x))
    let e : S ≃ (A ≃ Fin n) × ((U \ A : Finset α) → Fin n) :=
      { toFun := fun ⟨f, hf⟩ =>
          (Equiv.ofBijective (fun x : A => extend f x) (Finset.mem_filter.mp hf).2,
           fun b => f ⟨b.1, (Finset.mem_sdiff.mp b.2).1⟩)
        invFun := fun ⟨g, h⟩ =>
          ⟨fun u => if hu : u.1 ∈ A then g ⟨u.1, hu⟩ else h ⟨u.1, Finset.mem_sdiff.mpr ⟨u.2, hu⟩⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
             have hfun :
                 (fun x : A => extend (fun u => if hu : u.1 ∈ A then g ⟨u.1, hu⟩
                   else h ⟨u.1, Finset.mem_sdiff.mpr ⟨u.2, hu⟩⟩) x) = g := by
               funext x
               simp [extend, hAU x.2, x.2]
             rw [hfun]
             exact g.bijective⟩⟩
        left_inv := fun ⟨f, hf⟩ => by
          refine Subtype.ext (funext fun u => ?_)
          by_cases hu : u.1 ∈ A
          · simp [extend, dif_pos hu]
          · simp [dif_neg hu]
        right_inv := fun ⟨g, h⟩ => by
          refine Prod.ext ?_ ?_
          · ext x
            simp [extend, hAU x.2]
          · funext b
            simp [dif_neg (Finset.mem_sdiff.mp b.2).2] }
    have hS : S.card = Fintype.card S := (Fintype.card_coe S).symm
    rw [show (Finset.univ.filter (fun f : U → Fin n =>
        Function.Bijective (fun x : A => extend f x))).card = S.card from rfl, hS]
    rw [Fintype.card_congr e, Fintype.card_prod]
    have hcardA : Fintype.card A = n := by rw [Fintype.card_coe, hF A hA]
    have heq1 : Fintype.card (A ≃ Fin n) = n.factorial := by
      rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hcardA), hcardA]
    have heq2 : Fintype.card ((U \ A : Finset α) → Fin n) = n ^ (U.card - n) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
        Finset.card_sdiff, Finset.inter_eq_left.mpr hAU, hF A hA]
    rw [heq1, heq2]
  have hsum : ∑ f : U → Fin n, (good f).card = F.card * (n.factorial * n ^ (U.card - n)) := by
    rw [hcount]
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
  have hex : ∃ f : U → Fin n, F.card * n.factorial ≤ (good f).card * n ^ n := by
    by_contra! hcontra
    have hpow_pos : 0 < n ^ (U.card - n) := Nat.pow_pos hn
    have hstep : ∀ f : U → Fin n,
        (good f).card * n ^ U.card < F.card * n.factorial * n ^ (U.card - n) := by
      intro f
      have h1 := Nat.mul_lt_mul_of_pos_right (hcontra f) hpow_pos
      have hpow_eq : n ^ n * n ^ (U.card - n) = n ^ U.card := by
        rw [← pow_add, Nat.add_sub_cancel' hnU]
      calc
        (good f).card * n ^ U.card
          = (good f).card * (n ^ n * n ^ (U.card - n)) := by rw [hpow_eq]
        _ = (good f).card * n ^ n * n ^ (U.card - n) := by ring
        _ < F.card * n.factorial * n ^ (U.card - n) := h1
    let f₀ : U → Fin n := fun _ => ⟨0, hn⟩
    have hsum_lt :=
      Finset.sum_lt_sum (s := (Finset.univ : Finset (U → Fin n)))
        (fun f _ => (hstep f).le) ⟨f₀, Finset.mem_univ _, hstep f₀⟩
    have hL :
        ∑ f : U → Fin n, (good f).card * n ^ U.card =
          F.card * (n.factorial * n ^ (U.card - n)) * n ^ U.card := by
      rw [← Finset.sum_mul, hsum]
    have hR :
        ∑ _f : U → Fin n, F.card * n.factorial * n ^ (U.card - n) =
          n ^ U.card * (F.card * n.factorial * n ^ (U.card - n)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_coe, smul_eq_mul]
    rw [hL, hR] at hsum_lt
    have heq_sides :
        F.card * (n.factorial * n ^ (U.card - n)) * n ^ U.card =
          n ^ U.card * (F.card * n.factorial * n ^ (U.card - n)) := by ring
    omega
  obtain ⟨f, hf⟩ := hex
  exact ⟨extend f, good f, Finset.filter_subset _ _, fun A hA => (Finset.mem_filter.mp hA).2, hf⟩

