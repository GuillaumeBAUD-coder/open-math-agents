import FormalConjectures.ErdosProblems.«318»

-- Problem: Erdős Problem 318 — i
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/318.lean:127 (declaration Erdos318.erdos_318.parts.i)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped Topology

theorem OMA.solution : type_of% @Erdos318.erdos_318.parts.i := by
  let A : Set ℕ := {n : ℕ | Odd n} ∪ {2}
  refine ⟨A, ?_, ?_⟩
  · refine ⟨1 / 2, by norm_num, ?_⟩
    have hev := Nat.hasDensity_even
    rw [Set.HasDensity] at hev ⊢
    have hpart : ∀ᶠ b : ℕ in Filter.atTop,
        A.partialDensity Set.univ b = 1 - ({n : ℕ | Even n}).partialDensity Set.univ b + 1 / (b : ℝ) := by
      rw [Filter.eventually_atTop]
      refine ⟨3, fun b hb => ?_⟩
      simp only [Set.partialDensity, Set.inter_univ]
      have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h_univ : (Set.univ ∩ Set.Iio b).ncard = b := by
        rw [Set.univ_inter, ← Finset.coe_Iio, Set.ncard_coe_finset, Nat.card_Iio]
      have h_even_fin : ({n : ℕ | Even n} ∩ Set.Iio b).Finite :=
        (Set.finite_Iio b).inter_of_right _
      have h_odd_fin : ({n : ℕ | Odd n} ∩ Set.Iio b).Finite :=
        (Set.finite_Iio b).inter_of_right _
      have h_disj_eo : Disjoint ({n : ℕ | Even n} ∩ Set.Iio b) ({n : ℕ | Odd n} ∩ Set.Iio b) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact Nat.not_even_iff_odd.mpr hx2.1 hx1.1
      have h_union_eo : ({n : ℕ | Even n} ∩ Set.Iio b) ∪ ({n : ℕ | Odd n} ∩ Set.Iio b) = Set.Iio b := by
        ext x
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio]
        constructor
        · rintro (h | h) <;> exact h.2
        · intro hx
          rcases Nat.even_or_odd x with h | h
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr ⟨h, hx⟩
      have h_eo_sum : ({n : ℕ | Even n} ∩ Set.Iio b).ncard + ({n : ℕ | Odd n} ∩ Set.Iio b).ncard = b := by
        rw [← Set.ncard_union_eq h_disj_eo h_even_fin h_odd_fin, h_union_eo, ← Finset.coe_Iio,
          Set.ncard_coe_finset, Nat.card_Iio]
      have h_A_eq : A ∩ Set.Iio b = insert 2 ({n : ℕ | Odd n} ∩ Set.Iio b) := by
        ext x
        simp only [A, Set.mem_inter_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq,
          Set.mem_singleton_iff, Set.mem_Iio]
        constructor
        · rintro ⟨h1 | rfl, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact Or.inl rfl
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨Or.inr rfl, by omega⟩
          · exact ⟨Or.inl h1, h2⟩
      have h_not_odd2 : 2 ∉ ({n : ℕ | Odd n} ∩ Set.Iio b) := by
        simp [show ¬ Odd 2 by decide]
      have h_A_card : (A ∩ Set.Iio b).ncard = ({n : ℕ | Odd n} ∩ Set.Iio b).ncard + 1 := by
        rw [h_A_eq, Set.ncard_insert_of_notMem h_not_odd2 h_odd_fin]
      rw [h_univ, h_A_card]
      have h_even_le : ({n : ℕ | Even n} ∩ Set.Iio b).ncard ≤ b := by omega
      push_cast
      rw [show (({n : ℕ | Odd n} ∩ Set.Iio b).ncard : ℝ) =
          (b : ℝ) - (({n : ℕ | Even n} ∩ Set.Iio b).ncard : ℝ) by
        rw [← Nat.cast_sub h_even_le]
        exact_mod_cast (by omega : ({n : ℕ | Odd n} ∩ Set.Iio b).ncard = b - ({n : ℕ | Even n} ∩ Set.Iio b).ncard)]
      field_simp
    have hlim : Filter.Tendsto (fun b : ℕ => 1 - ({n : ℕ | Even n}).partialDensity Set.univ b + 1 / (b : ℝ))
        Filter.atTop (𝓝 (1 - 1 / 2 + 0)) :=
      ((tendsto_const_nhds.sub hev).add tendsto_one_div_atTop_nhds_zero_nat)
    rw [show (1 - 1 / 2 + 0 : ℝ) = 1 / 2 by norm_num] at hlim
    exact hlim.congr' (hpart.mono fun b hb => hb.symm)
  · simp only [Erdos318.P₁, not_forall, not_exists, not_and]
    refine ⟨fun n => if n = 2 then 1 else -1, fun h => ?_, fun h => ?_, fun x ⟨y, hy⟩ => ?_,
      fun S hSne hSsub hsum => ?_⟩
    · have : (-1 : ℝ) = 1 := by
        simpa using congr_fun h ⟨1, ⟨Or.inl (by decide), by decide⟩⟩
      norm_num at this
    · have : (1 : ℝ) = -1 := by
        simpa using congr_fun h ⟨2, ⟨Or.inr rfl, by decide⟩⟩
      norm_num at this
    · by_cases y = 2 <;> simp_all
    · by_cases h2 : 2 ∈ S
      · let T : Finset ℕ := S.erase 2
        have hTsub : ∀ n ∈ T, Odd n ∧ n ≠ 0 := by
          intro n hn
          have hnS : n ∈ S := Finset.mem_of_mem_erase hn
          have hn2 : n ≠ 2 := Finset.ne_of_mem_erase hn
          have hnA := hSsub hnS
          simp only [Set.mem_diff, Set.mem_singleton_iff, A, Set.mem_union, Set.mem_setOf_eq] at hnA
          rcases hnA.1 with hodd | rfl
          · exact ⟨hodd, hnA.2⟩
          · exact absurd rfl hn2
        have hS_split : ∑ n ∈ S, (if n = 2 then (1 : ℝ) else -1) / (n : ℝ) =
            1 / 2 - ∑ n ∈ T, 1 / (n : ℝ) := by
          rw [← Finset.add_sum_erase S (fun n => (if n = 2 then (1 : ℝ) else -1) / (n : ℝ)) h2]
          simp only [↓reduceIte, Nat.cast_ofNat]
          have hTsum : ∑ n ∈ T, (if n = 2 then (1 : ℝ) else -1) / (n : ℝ) = - ∑ n ∈ T, 1 / (n : ℝ) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun n hn => ?_
            have hn2 : n ≠ 2 := Finset.ne_of_mem_erase hn
            simp [hn2, neg_div]
          rw [hTsum]
          ring
        have hhalf : (1 / 2 : ℝ) = ∑ n ∈ T, 1 / (n : ℝ) := by linarith
        let P : ℕ := ∏ n ∈ T, n
        have hP_odd : Odd P := by
          refine Finset.prod_induction _ (fun m => Odd m) (fun a b ha hb => ha.mul hb) odd_one ?_
          intro n hn
          exact (hTsub n hn).1
        have hP_pos : 0 < P := by
          refine Finset.prod_pos fun n hn => Nat.pos_of_ne_zero (hTsub n hn).2
        let Q : ℕ := ∑ n ∈ T, P / n
        have hmul : (P : ℝ) = 2 * (Q : ℝ) := by
          have h1 : (P : ℝ) = 2 * (P : ℝ) * (1 / 2 : ℝ) := by ring
          rw [h1, hhalf, Finset.mul_sum]
          have h2 : ∑ n ∈ T, 2 * (P : ℝ) * (1 / (n : ℝ)) = 2 * ∑ n ∈ T, ((P / n : ℕ) : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n hn => ?_
            have hdvd : n ∣ P := Finset.dvd_prod_of_mem _ hn
            have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hTsub n hn).2
            rw [Nat.cast_div hdvd hn0]
            ring
          rw [h2]
          push_cast [Q]
          rfl
        have hP_eq : P = 2 * Q := by exact_mod_cast hmul
        have hP_even : Even P := ⟨Q, by omega⟩
        exact (Nat.not_even_iff_odd.mpr hP_odd) hP_even
      · have hneg : ∑ n ∈ S, (if n = 2 then (1 : ℝ) else -1) / (n : ℝ) < 0 := by
          refine Finset.sum_neg (fun n hn => ?_) hSne
          have hn2 : n ≠ 2 := fun heq => h2 (heq ▸ hn)
          have hn0 : n ≠ 0 := (hSsub hn).2
          simp only [hn2, ↓reduceIte, neg_div, Left.neg_neg_iff]
          positivity
        linarith
