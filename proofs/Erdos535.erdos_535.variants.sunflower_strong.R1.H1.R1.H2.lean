import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1

/-! Transfer sunflower-free set families to word families by rainbow coloring.
The word encoding and factorial estimate are adapted from reduction Erdos20.erdos_20.R1.
Credit: @DeepDuke
-/

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

lemma OMA.RainbowColoring.extract :
    ∀ (α : Type) (n : ℕ), 0 < n →
      ∀ (F : Finset (Finset α)), (∀ A ∈ F, A.card = n) →
        ∃ (c : α → Fin n) (G : Finset (Finset α)),
          G ⊆ F ∧ (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧
          F.card * n.factorial ≤ G.card * n ^ n := by
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


namespace OMA.RainbowColoring

lemma word_family_of_rainbow {α : Type} [DecidableEq α] {n r : ℕ}
    {G F : Finset (Finset α)} (hGF : G ⊆ F) (c : α → Fin n)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x))
    (hfree : ¬ ∃ S ⊆ F, S.card = r ∧ ∃ K : Finset α,
      ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K) :
    ∃ (m : ℕ) (W : Finset (Fin n → Fin m)),
      W.card = G.card ∧
      ∀ w : Fin r → Fin n → Fin m,
        (∀ i, w i ∈ W) →
        (∀ j : Fin n, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b := by
  classical
  let U : Finset α := G.biUnion id
  let e (A : G) : (A : Finset α) ≃ Fin n := Equiv.ofBijective _ (hc A A.property)
  let pt (A : G) (j : Fin n) : U :=
    ⟨(e A).symm j, Finset.mem_biUnion.mpr ⟨A, A.property, ((e A).symm j).property⟩⟩
  let encode (A : G) (j : Fin n) : Fin U.card := U.equivFin (pt A j)
  let decode (u : Fin U.card) : α := U.equivFin.symm u
  have hdec_inj : Function.Injective decode :=
    Subtype.val_injective.comp U.equivFin.symm.injective
  have hmem : ∀ (A : G) (x : α), x ∈ (A : Finset α) ↔ decode (encode A (c x)) = x := by
    intro A x
    have hdecode (j : Fin n) : decode (encode A j) = ((e A).symm j).val := by
      simp [decode, encode, pt]
    rw [hdecode]
    constructor
    · intro hx
      have he : (e A) ⟨x, hx⟩ = c x := rfl
      rw [← he, Equiv.symm_apply_apply]
    · intro hx
      exact hx ▸ ((e A).symm (c x)).property
  have henc_inj : Function.Injective encode := by
    intro A B hab
    apply Subtype.ext
    ext x
    rw [hmem, hmem, hab]
  let W : Finset (Fin n → Fin U.card) := Finset.univ.image encode
  refine ⟨U.card, W, ?_, ?_⟩
  · simp [W, Finset.card_image_of_injective _ henc_inj]
  · intro w hw hadm
    by_contra hnc
    push Not at hnc
    obtain ⟨a₀, b₀, hab₀⟩ := hnc
    have hwinj : Function.Injective w := by
      intro i j hij
      by_contra hne
      apply hab₀
      funext j₀
      rcases hadm j₀ with hconst | hinj
      · exact hconst a₀ b₀
      · exact (hne (hinj (congrFun hij j₀))).elim
    have hlift : ∀ i : Fin r, ∃ A : G, encode A = w i := by
      intro i
      obtain ⟨A, _, hA⟩ := Finset.mem_image.mp (hw i)
      exact ⟨A, hA⟩
    choose A hA using hlift
    have hAinj : Function.Injective (fun i : Fin r => (A i : Finset α)) := by
      intro i j hij
      apply hwinj
      rw [← hA i, ← hA j, Subtype.ext hij]
    have hAmem (i : Fin r) (x : α) :
        x ∈ (A i : Finset α) ↔ decode (w i (c x)) = x := by
      rw [← hA i, hmem]
    let K : Finset α := U.filter fun x => ∀ i : Fin r, x ∈ (A i : Finset α)
    let emb : Fin r ↪ Finset α := ⟨fun i => (A i : Finset α), hAinj⟩
    apply hfree
    refine ⟨Finset.univ.map emb, ?_, by simp, K, ?_⟩
    · intro X hX
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hX
      exact hGF (A i).property
    · intro X hX Y hY hXY
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hX
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hY
      have hij : i ≠ j := fun h => hXY (congrArg emb h)
      ext x
      constructor
      · intro hx
        obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨A i, (A i).property, hi⟩, ?_⟩
        have heq : w i (c x) = w j (c x) :=
          hdec_inj (((hAmem i x).mp hi).trans ((hAmem j x).mp hj).symm)
        rcases hadm (c x) with hconst | hinj
        · intro t
          exact (hAmem t x).mpr ((congrArg decode (hconst t i)).trans ((hAmem i x).mp hi))
        · exact (hij (hinj heq)).elim
      · intro hx
        have hall := (Finset.mem_filter.mp hx).2
        exact Finset.mem_inter.mpr ⟨hall i, hall j⟩

lemma pow_self_le_three_pow_mul_factorial (n : ℕ) :
    n ^ n ≤ 3 ^ n * n.factorial := by
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hExp : Real.exp n ≤ (3 : ℝ) ^ n := by
    calc
      Real.exp n = (Real.exp 1) ^ n := by simp [← Real.exp_nat_mul]
      _ ≤ (3 : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have h := (div_le_iff₀ hn).mp
    ((Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n).trans hExp)
  exact_mod_cast h

end OMA.RainbowColoring

theorem OMA.solution :
    OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1.H2 := by
  intro r k hk F hF hfree
  obtain ⟨c, G, hGF, hc, hsize⟩ := OMA.RainbowColoring.extract ℕ k hk F hF
  obtain ⟨m, W, hW, hword⟩ := OMA.RainbowColoring.word_family_of_rainbow hGF c hc hfree
  refine ⟨m, W, ?_, hword⟩
  rw [hW]
  apply Nat.le_of_mul_le_mul_right (c := k.factorial) _ (Nat.factorial_pos k)
  calc
    F.card * k.factorial ≤ G.card * k ^ k := hsize
    _ ≤ G.card * (3 ^ k * k.factorial) :=
      Nat.mul_le_mul_left _ (OMA.RainbowColoring.pow_self_le_three_pow_mul_factorial k)
    _ = (3 ^ k * G.card) * k.factorial := by ac_rfl
