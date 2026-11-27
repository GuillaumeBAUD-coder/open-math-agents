import OMAReductions.R_Erdos20_erdos_20_R1
import Mathlib.Tactic

/-!
# Step Proof for Erdos Problem 20 (`Erdos20.erdos_20.R1.H1`)
-/

theorem prove_Erdos20_H1 :
    ∀ (α : Type) (n : ℕ), 0 < n →
      ∀ (F : Finset (Finset α)), (∀ A ∈ F, A.card = n) →
        ∃ (c : α → Fin n) (G : Finset (Finset α)),
          G ⊆ F ∧
          (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧
          F.card * n.factorial ≤ G.card * n ^ n := by
  intro α n hn F hF
  classical
  let U : Finset α := F.biUnion id
  have hsubU : ∀ A ∈ F, A ⊆ U := by
    intro A hA x hx
    exact Finset.mem_biUnion.mpr ⟨A, hA, hx⟩
  let C := U → Fin n
  let extColor (f : C) (x : α) : Fin n :=
    if hx : x ∈ U then f ⟨x, hx⟩ else ⟨0, hn⟩
  let G (f : C) : Finset (Finset α) :=
    F.filter (fun A => Function.Bijective (fun x : A => extColor f x))
  have hswap : ∑ f : C, (G f).card =
      ∑ A ∈ F, (Finset.univ.filter
        (fun f : C => Function.Bijective (fun x : A => extColor f x))).card := by
    simp only [G, Finset.card_filter]
    exact Finset.sum_comm
  have hcount_each : ∀ A ∈ F,
      (Finset.univ.filter
        (fun f : C => Function.Bijective (fun x : A => extColor f x))).card * n ^ n =
        n.factorial * n ^ U.card := by
    intro A hA
    have hAU : A ⊆ U := hsubU A hA
    have hAcard : A.card = n := hF A hA
    let R : Finset α := U \ A
    let φ : (A ≃ Fin n) × (R → Fin n) ≃
        {f : C // Function.Bijective (fun x : A => extColor f x)} :=
      { toFun := fun p =>
          ⟨fun u => if huA : u.1 ∈ A then p.1 ⟨u.1, huA⟩
              else p.2 ⟨u.1, Finset.mem_sdiff.mpr ⟨u.2, huA⟩⟩, by
            have heq : (fun x : A => extColor
                (fun u : U => if huA : u.1 ∈ A then p.1 ⟨u.1, huA⟩
                  else p.2 ⟨u.1, Finset.mem_sdiff.mpr ⟨u.2, huA⟩⟩) x) = p.1 := by
              funext x
              simp [extColor, hAU x.2, x.2]
            rw [heq]
            exact p.1.bijective⟩
        invFun := fun q =>
          (Equiv.ofBijective (fun x : A => extColor q.1 x) q.2,
           fun r => q.1 ⟨r.1, (Finset.mem_sdiff.mp r.2).1⟩)
        left_inv := by
          rintro ⟨e, g⟩
          apply Prod.ext
          · apply Equiv.ext
            intro x
            simp [extColor, hAU x.2]
          · funext r
            have hr : r.1 ∉ A := (Finset.mem_sdiff.mp r.2).2
            simp [hr]
        right_inv := by
          rintro ⟨f, hf⟩
          apply Subtype.ext
          funext u
          by_cases huA : u.1 ∈ A
          · simp [extColor, huA, u.2]
          · simp [huA] }
    have hfilter_card :
        (Finset.univ.filter
          (fun f : C => Function.Bijective (fun x : A => extColor f x))).card =
          Fintype.card {f : C // Function.Bijective (fun x : A => extColor f x)} := by
      rw [← Finset.card_univ]
      symm
      refine Finset.card_bij (fun q _ => q.1) ?_ ?_ ?_
      · intro q _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩
      · intro q₁ _ q₂ _ h
        exact Subtype.ext h
      · intro f hf
        exact ⟨⟨f, (Finset.mem_filter.mp hf).2⟩, Finset.mem_univ _, rfl⟩
    have hcard_equiv : Fintype.card (A ≃ Fin n) = n.factorial := by
      rw [Fintype.card_equiv (Finset.equivFinOfCardEq hAcard), Fintype.card_coe, hAcard]
    have hcard_fun : Fintype.card (R → Fin n) = n ^ R.card := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    have hRA : R.card + n = U.card := by
      rw [← hAcard]
      exact Finset.card_sdiff_add_card_eq_card hAU
    rw [hfilter_card, ← Fintype.card_congr φ, Fintype.card_prod, hcard_equiv, hcard_fun,
      mul_assoc, ← pow_add, hRA]
  have hcardC : Fintype.card C = n ^ U.card := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hsum_eq : ∑ f : C, (G f).card * n ^ n = ∑ _f : C, F.card * n.factorial := by
    rw [← Finset.sum_mul, hswap, Finset.sum_mul]
    calc ∑ A ∈ F, (Finset.univ.filter
            (fun f : C => Function.Bijective (fun x : A => extColor f x))).card * n ^ n
        = ∑ _A ∈ F, n.factorial * n ^ U.card := Finset.sum_congr rfl hcount_each
      _ = F.card * (n.factorial * n ^ U.card) := by rw [Finset.sum_const, smul_eq_mul]
      _ = n ^ U.card * (F.card * n.factorial) := by ring
      _ = ∑ _f : C, F.card * n.factorial := by
          rw [Finset.sum_const, Finset.card_univ, hcardC, smul_eq_mul]
  have hC_ne : (Finset.univ : Finset C).Nonempty :=
    ⟨fun _ => ⟨0, hn⟩, Finset.mem_univ _⟩
  have hex : ∃ f : C, F.card * n.factorial ≤ (G f).card * n ^ n := by
    by_contra! hlt
    have hsum_lt : ∑ f ∈ (Finset.univ : Finset C), (G f).card * n ^ n <
        ∑ _f ∈ (Finset.univ : Finset C), F.card * n.factorial :=
      Finset.sum_lt_sum_of_nonempty hC_ne (fun f _ => hlt f)
    exact hsum_lt.ne hsum_eq
  obtain ⟨f, hf⟩ := hex
  exact ⟨extColor f, G f, Finset.filter_subset _ _,
    fun A hA => (Finset.mem_filter.mp hA).2, hf⟩

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 :=
  prove_Erdos20_H1
