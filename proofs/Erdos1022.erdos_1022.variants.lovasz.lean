import FormalConjectures.ErdosProblems.«1022»

-- Problem: Erdős Problem 1022 — lovasz
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1022.lean:81 (declaration Erdos1022.erdos_1022.variants.lovasz)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.O10

/-- Linear algebra step: more vertices than sets gives a nonzero weighting `G` of the vertices
whose sum over every set vanishes. -/
theorem exists_weight (F : Finset (Finset ℕ)) (X : Finset ℕ) (h : F.card < X.card) :
    ∃ G : ℕ → ℚ, (∀ A ∈ F, ∑ x ∈ X, (if x ∈ A then G x else 0) = 0) ∧ ∃ x ∈ X, G x ≠ 0 := by
  classical
  let f : X → (F → ℚ) := fun x A => if (x : ℕ) ∈ (A : Finset ℕ) then 1 else 0
  have hli : ¬ LinearIndependent ℚ f := by
    intro hl
    have h1 := hl.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at h1
    omega
  obtain ⟨g, hsum, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
  let G : ℕ → ℚ := fun x => if hx : x ∈ X then g ⟨x, hx⟩ else 0
  refine ⟨G, ?_, ⟨i0.1, i0.2, ?_⟩⟩
  · intro A hA
    have h2 := congrFun hsum ⟨A, hA⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, f] at h2
    calc ∑ x ∈ X, (if x ∈ A then G x else 0)
        = ∑ i : X, (if (i : ℕ) ∈ A then G i else 0) := (Finset.sum_coe_sort X _).symm
      _ = ∑ i : X, g i * (if (i : ℕ) ∈ A then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hG : G i = g i := by simp [G, i.2]
          split_ifs <;> simp [hG]
      _ = 0 := h2
  · simpa [G, i0.2] using hi0

theorem key (n : ℕ) : ∀ F : Finset (Finset ℕ), F.card = n → (∀ A ∈ F, 2 ≤ A.card) →
    (∀ X : Finset ℕ, X.Nonempty → (F.filter (· ⊆ X)).card < X.card) → F.HasPropertyB := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hFn hF hsp
  rcases F.eq_empty_or_nonempty with hE | ⟨A0, hA0⟩
  · subst hE
    exact ⟨fun _ => 0, by simp⟩
  let X : Finset ℕ := F.biUnion id
  have hAX : ∀ A ∈ F, A ⊆ X := fun A hA => Finset.subset_biUnion_of_mem id hA
  have hXne : X.Nonempty := by
    have h2 := hF A0 hA0
    obtain ⟨v, hv⟩ : A0.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨v, hAX A0 hA0 hv⟩
  have hlt : F.card < X.card := by
    have h1 := hsp X hXne
    have hfil : F.filter (· ⊆ X) = F := Finset.filter_true_of_mem hAX
    rw [hfil] at h1
    exact h1
  obtain ⟨G, hG, x0, hx0X, hx0⟩ := exists_weight F X hlt
  have hGA : ∀ A ∈ F, ∑ x ∈ A, G x = 0 := by
    intro A hA
    have h1 := hG A hA
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hAX A hA)] at h1
    exact h1
  let F0 := F.filter (fun A => ∀ v ∈ A, G v = 0)
  have hF0sub : F0 ⊆ F := Finset.filter_subset _ _
  have hF0lt : F0.card < n := by
    rw [← hFn]
    apply Finset.card_lt_card
    rw [Finset.filter_ssubset]
    obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx0X
    exact ⟨A, hA, fun h => hx0 (h x0 hxA)⟩
  obtain ⟨c, hc⟩ := ih F0.card hF0lt F0 rfl (fun A hA => hF A (hF0sub hA)) (by
    intro Y hY
    calc (F0.filter (· ⊆ Y)).card ≤ (F.filter (· ⊆ Y)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hF0sub)
      _ < Y.card := hsp Y hY)
  refine ⟨fun v => if 0 < G v then 0 else if G v < 0 then 1 else c v, ?_⟩
  intro A hA
  by_cases hz : ∀ v ∈ A, G v = 0
  · have hA0' : A ∈ F0 := Finset.mem_filter.mpr ⟨hA, hz⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hc A hA0'
    refine ⟨x, hx, y, hy, ?_⟩
    simp only [hz x hx, hz y hy, lt_irrefl, if_false]
    exact hxy
  · push Not at hz
    obtain ⟨v, hvA, hv⟩ := hz
    have hsum := hGA A hA
    have hpos : ∃ p ∈ A, 0 < G p := by
      by_contra hcon
      push Not at hcon
      have h1 : ∑ x ∈ A, -G x = 0 := by rw [Finset.sum_neg_distrib, hsum, neg_zero]
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => by linarith [hcon i hi])).mp h1 v hvA
      exact hv (by linarith)
    have hneg : ∃ q ∈ A, G q < 0 := by
      by_contra hcon
      push Not at hcon
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg hcon).mp hsum v hvA
      exact hv h2
    obtain ⟨p, hpA, hp⟩ := hpos
    obtain ⟨q, hqA, hq⟩ := hneg
    refine ⟨p, hpA, q, hqA, ?_⟩
    have hq' : ¬ 0 < G q := by linarith
    simp only [hp, hq, hq', if_true, if_false]
    decide

theorem tri_card : ∀ A ∈ ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset ℕ)), A.card = 2 := by
  intro A hA
  simp only [Finset.mem_insert, Finset.mem_singleton] at hA
  rcases hA with rfl | rfl | rfl <;> rfl

theorem pair_ne (f : ℕ → Fin 2) (a b : ℕ)
    (h : ∃ x ∈ ({a, b} : Finset ℕ), ∃ y ∈ ({a, b} : Finset ℕ), f x ≠ f y) : f a ≠ f b := by
  obtain ⟨x, hx, y, hy, hne⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hne
  · exact hne
  · exact hne.symm
  · exact absurd rfl hne

end OMA.O10

theorem OMA.solution : type_of% @Erdos1022.erdos_1022.variants.lovasz := by
  constructor
  · intro F hF hsp
    apply OMA.O10.key F.card F rfl hF
    intro X hX
    have h1 := hsp X hX
    rw [one_mul] at h1
    exact_mod_cast h1
  · intro c hc
    by_contra hlt
    push Not at hlt
    let T : Finset (Finset ℕ) := {{0, 1}, {1, 2}, {0, 2}}
    have hTc : ∀ A ∈ T, A.card = 2 := OMA.O10.tri_card
    obtain ⟨f, hf⟩ := hc T (fun A hA => (hTc A hA).ge) (by
      intro X hX
      have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
      have hle : (T.hypergraphInduce X).card ≤ X.card := by
        unfold Finset.hypergraphInduce
        by_cases h3 : 3 ≤ X.card
        · calc (T.filter (· ⊆ X)).card ≤ T.card := Finset.card_filter_le _ _
            _ ≤ 3 := Finset.card_le_three
            _ ≤ X.card := h3
        · have hsub : T.filter (· ⊆ X) ⊆ {X} := by
            intro A hA
            rw [Finset.mem_filter] at hA
            rw [Finset.mem_singleton]
            exact Finset.eq_of_subset_of_card_le hA.2 (by rw [hTc A hA.1]; omega)
          calc (T.filter (· ⊆ X)).card ≤ ({X} : Finset (Finset ℕ)).card := Finset.card_le_card hsub
            _ = 1 := Finset.card_singleton X
            _ ≤ X.card := hX.card_pos
      have hle' : ((T.hypergraphInduce X).card : ℝ) ≤ X.card := by exact_mod_cast hle
      nlinarith)
    have h01 := OMA.O10.pair_ne f 0 1 (hf {0, 1} (by simp [T]))
    have h12 := OMA.O10.pair_ne f 1 2 (hf {1, 2} (by simp [T]))
    have h02 := OMA.O10.pair_ne f 0 2 (hf {0, 2} (by simp [T]))
    have a := (f 0).isLt
    have b := (f 1).isLt
    have d := (f 2).isLt
    have e1 : (f 0).val ≠ (f 1).val := fun h => h01 (Fin.ext h)
    have e2 : (f 1).val ≠ (f 2).val := fun h => h12 (Fin.ext h)
    have e3 : (f 0).val ≠ (f 2).val := fun h => h02 (Fin.ext h)
    omega
