import FormalConjectures.ErdosProblems.«21»

-- Problem: Erdős Problem 21 — lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/21.lean:91 (declaration Erdos21.erdos_21.variants.lower)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

private noncomputable def erdos21Phi (n m : ℕ) : ℝ :=
  min (((m : ℝ) + 1) / 2)
    (min ((m : ℝ) / 3 + (n : ℝ) / 6 + 2 / 3) ((m : ℝ) / 4 + (n : ℝ) / 3 + 3 / 4))

private lemma erdos21Phi_le_line1 (n m : ℕ) :
    erdos21Phi n m ≤ (m : ℝ) / 4 + (n : ℝ) / 3 + 3 / 4 :=
  le_trans (min_le_right _ _) (min_le_right _ _)

private lemma erdos21Phi_step_two {n m m' : ℕ} (hm : m ≤ n + 1) (hm' : m' + 2 ≤ m) :
    1 + erdos21Phi n m' ≤ erdos21Phi n m := by
  have h1 : erdos21Phi n m' ≤ ((m' : ℝ) + 1) / 2 := min_le_left _ _
  have hmR : (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hm
  have hm'R : (m' : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hm'
  refine le_min (by linarith) (le_min (by linarith) (by linarith))

private lemma erdos21Phi_step_three {n m m' : ℕ} (hm1 : n + 1 ≤ m) (hm2 : m ≤ 2 * n + 1)
    (hm' : m' + 3 ≤ m) : 1 + erdos21Phi n m' ≤ erdos21Phi n m := by
  have h1 : erdos21Phi n m' ≤ (m' : ℝ) / 3 + (n : ℝ) / 6 + 2 / 3 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hm1R : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm1
  have hm2R : (m : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hm2
  have hm'R : (m' : ℝ) + 3 ≤ (m : ℝ) := by exact_mod_cast hm'
  refine le_min (by linarith) (le_min (by linarith) (by linarith))

private lemma erdos21Phi_step_four {n m m' : ℕ} (hm : 2 * n + 1 ≤ m) (hm' : m' + 4 ≤ m) :
    1 + erdos21Phi n m' ≤ erdos21Phi n m := by
  have h1 : erdos21Phi n m' ≤ (m' : ℝ) / 4 + (n : ℝ) / 3 + 3 / 4 :=
    erdos21Phi_le_line1 n m'
  have hmR : 2 * (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm'R : (m' : ℝ) + 4 ≤ (m : ℝ) := by exact_mod_cast hm'
  refine le_min (by linarith) (le_min (by linarith) (by linarith))

private lemma erdos21Phi_base_zero (n : ℕ) : (0 : ℝ) ≤ erdos21Phi n 0 := by
  refine le_min (by norm_num) (le_min (by positivity) (by positivity))

private lemma erdos21Phi_base_one (n : ℕ) : (1 : ℝ) ≤ erdos21Phi n 1 := by
  refine le_min (by norm_num) (le_min ?_ ?_) <;>
    · simp only [Nat.cast_one]
      linarith [Nat.cast_nonneg (α := ℝ) n]

private lemma erdos21Phi_base_two {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ erdos21Phi n 2 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine le_min (by norm_num) (le_min (by norm_num; linarith) (by norm_num; linarith))

private lemma erdos21Phi_base_three {n : ℕ} (hn : 2 ≤ n) : (2 : ℝ) ≤ erdos21Phi n 3 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine le_min (by norm_num) (le_min (by norm_num; linarith) (by norm_num; linarith))

private lemma erdos21Phi_base_four {n : ℕ} (hn : 3 ≤ n) : (2 : ℝ) ≤ erdos21Phi n 4 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine le_min (by norm_num) (le_min (by norm_num; linarith) (by norm_num; linarith))

private lemma erdos21_exists_high_degree {n d : ℕ} (hd : 2 ≤ d)
    {H : Finset (Finset ℕ)}
    (hcard : ∀ A ∈ H, A.card = n)
    (hinter : ∀ A ∈ H, ∀ B ∈ H, (A ∩ B).Nonempty)
    (hm : n * (d - 2) + 2 ≤ H.card) :
    ∃ v : ℕ, d ≤ (H.filter (fun A => v ∈ A)).card := by
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  rcases hHne with ⟨A₀, hA₀⟩
  by_contra hcon
  push Not at hcon
  have hupper : ∑ v ∈ A₀, ((H.erase A₀).filter (fun A => v ∈ A)).card ≤ n * (d - 2) := by
    calc ∑ v ∈ A₀, ((H.erase A₀).filter (fun A => v ∈ A)).card
        ≤ ∑ _v ∈ A₀, (d - 2) := by
          refine Finset.sum_le_sum (fun v hv => ?_)
          have hdeg := hcon v
          have hmem : A₀ ∈ H.filter (fun A => v ∈ A) := Finset.mem_filter.mpr ⟨hA₀, hv⟩
          have herase : (H.filter (fun A => v ∈ A)).erase A₀ =
              (H.erase A₀).filter (fun A => v ∈ A) := by
            ext A
            simp only [Finset.mem_erase, Finset.mem_filter]
            tauto
          rw [← herase, Finset.card_erase_of_mem hmem]
          omega
      _ = n * (d - 2) := by
          rw [Finset.sum_const, smul_eq_mul, hcard A₀ hA₀]
  have hlower : H.card - 1 ≤ ∑ v ∈ A₀, ((H.erase A₀).filter (fun A => v ∈ A)).card := by
    calc H.card - 1
        = (H.erase A₀).card := (Finset.card_erase_of_mem hA₀).symm
      _ = ∑ _A ∈ H.erase A₀, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ A ∈ H.erase A₀, ∑ v ∈ A₀, (if v ∈ A then 1 else 0) := by
          refine Finset.sum_le_sum (fun A hA => ?_)
          rcases hinter A₀ hA₀ A (Finset.mem_of_mem_erase hA) with ⟨x, hx⟩
          rw [Finset.mem_inter] at hx
          have hsingle : (if x ∈ A then 1 else 0) ≤
              ∑ v ∈ A₀, (if v ∈ A then 1 else 0) :=
            Finset.single_le_sum (f := fun v => if v ∈ A then 1 else 0)
              (fun _ _ => Nat.zero_le _) hx.1
          simpa [hx.2] using hsingle
      _ = ∑ v ∈ A₀, ∑ A ∈ H.erase A₀, (if v ∈ A then 1 else 0) := Finset.sum_comm
      _ = ∑ v ∈ A₀, ((H.erase A₀).filter (fun A => v ∈ A)).card := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.card_filter]
  omega

private lemma erdos21_filter_not_add_filter_card {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter (fun x => ¬ p x)).card + (s.filter p).card = s.card := by
  have hdisj : Disjoint (s.filter (fun x => ¬ p x)) (s.filter p) :=
    Finset.disjoint_left.mpr (fun _ h1 h2 => (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
  have hunion : s.filter (fun x => ¬ p x) ∪ s.filter p = s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

private lemma erdos21_exists_hitting_set {n : ℕ} (hn : 3 ≤ n) :
    ∀ m : ℕ, ∀ H : Finset (Finset ℕ),
      H.card = m →
      (∀ A ∈ H, A.card = n) →
      (∀ A ∈ H, ∀ B ∈ H, (A ∩ B).Nonempty) →
      ∃ S : Finset ℕ, (∀ A ∈ H, (S ∩ A).Nonempty) ∧ (S.card : ℝ) ≤ erdos21Phi n m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m IH =>
    intro H hm hcard hinter
    have step : ∀ v d : ℕ, 1 ≤ d → d ≤ (H.filter (fun A => v ∈ A)).card →
        (∀ m', m' + d ≤ m → 1 + erdos21Phi n m' ≤ erdos21Phi n m) →
        ∃ S : Finset ℕ, (∀ A ∈ H, (S ∩ A).Nonempty) ∧ (S.card : ℝ) ≤ erdos21Phi n m := by
      intro v d hd hdeg hphi
      have hsum : (H.filter (fun A => v ∉ A)).card + (H.filter (fun A => v ∈ A)).card = m := by
        rw [erdos21_filter_not_add_filter_card H (fun A => v ∈ A), hm]
      have hlt : (H.filter (fun A => v ∉ A)).card < m := by omega
      have hle : (H.filter (fun A => v ∉ A)).card + d ≤ m := by omega
      rcases IH (H.filter (fun A => v ∉ A)).card hlt (H.filter (fun A => v ∉ A)) rfl
          (fun A hA => hcard A (Finset.mem_filter.mp hA).1)
          (fun A hA B hB => hinter A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1) with
        ⟨S', hS'hit, hS'card⟩
      refine ⟨insert v S', ?_, ?_⟩
      · intro A hA
        by_cases hv : v ∈ A
        · exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_insert_self v S', hv⟩⟩
        · rcases hS'hit A (Finset.mem_filter.mpr ⟨hA, hv⟩) with ⟨x, hx⟩
          rw [Finset.mem_inter] at hx
          exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hx.1, hx.2⟩⟩
      · have hcardS : (insert v S').card ≤ S'.card + 1 := Finset.card_insert_le v S'
        have hcardSR : ((insert v S').card : ℝ) ≤ (S'.card : ℝ) + 1 := by exact_mod_cast hcardS
        have hstep := hphi (H.filter (fun A => v ∉ A)).card hle
        linarith
    by_cases hm0 : m = 0
    · subst hm0
      rw [Finset.card_eq_zero.mp hm]
      exact ⟨∅, fun _ hA => (Finset.notMem_empty _ hA).elim, by simpa using erdos21Phi_base_zero n⟩
    · by_cases hm1 : m = 1
      · subst hm1
        rcases Finset.card_eq_one.mp hm with ⟨A, hA⟩
        subst hA
        have hAne : A.Nonempty := Finset.card_pos.mp (by rw [hcard A (Finset.mem_singleton_self A)]; omega)
        rcases hAne with ⟨v, hv⟩
        refine ⟨{v}, ?_, ?_⟩
        · intro B hB
          rw [Finset.mem_singleton] at hB
          subst hB
          exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, hv⟩⟩
        · simpa using erdos21Phi_base_one n
      · by_cases hm2 : m = 2
        · subst hm2
          rcases Finset.card_pos.mp (by omega : 0 < H.card) with ⟨A, hA⟩
          have hecard : (H.erase A).card = 1 := by rw [Finset.card_erase_of_mem hA, hm]
          rcases Finset.card_eq_one.mp hecard with ⟨B, hB⟩
          have hBin : B ∈ H := Finset.mem_of_mem_erase (by rw [hB]; exact Finset.mem_singleton_self B)
          rcases hinter A hA B hBin with ⟨v, hv⟩
          rw [Finset.mem_inter] at hv
          refine ⟨{v}, ?_, ?_⟩
          · intro C hC
            by_cases hCA : C = A
            · subst hCA
              exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, hv.1⟩⟩
            · have hCB : C ∈ H.erase A := Finset.mem_erase.mpr ⟨hCA, hC⟩
              rw [hB, Finset.mem_singleton] at hCB
              subst hCB
              exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, hv.2⟩⟩
          · simpa using erdos21Phi_base_two (by omega)
        · by_cases hm4 : m ≤ 4
          · rcases erdos21_exists_high_degree (d := 2) (by omega) hcard hinter (by rw [hm]; omega) with
              ⟨v, hv⟩
            have hsum : (H.filter (fun C => v ∉ C)).card + (H.filter (fun C => v ∈ C)).card = m := by
              rw [erdos21_filter_not_add_filter_card H (fun C => v ∈ C), hm]
            have hH'le : (H.filter (fun C => v ∉ C)).card ≤ 2 := by omega
            have hH'lt : (H.filter (fun C => v ∉ C)).card < m := by omega
            rcases IH (H.filter (fun C => v ∉ C)).card hH'lt (H.filter (fun C => v ∉ C)) rfl
                (fun C hC => hcard C (Finset.mem_filter.mp hC).1)
                (fun C hC D hD => hinter C (Finset.mem_filter.mp hC).1 D (Finset.mem_filter.mp hD).1) with
              ⟨S', hS'hit, hS'card⟩
            have hphiH' : erdos21Phi n (H.filter (fun C => v ∉ C)).card ≤ 3 / 2 := by
              have h1 : erdos21Phi n (H.filter (fun C => v ∉ C)).card ≤
                  (((H.filter (fun C => v ∉ C)).card : ℝ) + 1) / 2 := min_le_left _ _
              have h2 : ((H.filter (fun C => v ∉ C)).card : ℝ) ≤ 2 := by exact_mod_cast hH'le
              linarith
            have hS'le1 : S'.card ≤ 1 := by
              by_contra hgt
              have h2 : (2 : ℝ) ≤ (S'.card : ℝ) := by exact_mod_cast (by omega : 2 ≤ S'.card)
              linarith
            refine ⟨insert v S', ?_, ?_⟩
            · intro C hC
              by_cases hvC : v ∈ C
              · exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_insert_self v S', hvC⟩⟩
              · rcases hS'hit C (Finset.mem_filter.mpr ⟨hC, hvC⟩) with ⟨x, hx⟩
                rw [Finset.mem_inter] at hx
                exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hx.1, hx.2⟩⟩
            · have hcardS : (insert v S').card ≤ 2 := le_trans (Finset.card_insert_le v S') (by omega)
              have hcardSR : ((insert v S').card : ℝ) ≤ 2 := by exact_mod_cast hcardS
              have h2le : (2 : ℝ) ≤ erdos21Phi n m := by
                have hm34 : m = 3 ∨ m = 4 := by omega
                rcases hm34 with rfl | rfl
                · exact erdos21Phi_base_three (by omega)
                · exact erdos21Phi_base_four hn
              linarith
          · have hm5 : 5 ≤ m := by omega
            by_cases hm_low : m ≤ n + 1
            · rcases erdos21_exists_high_degree (d := 2) (by omega) hcard hinter
                  (by rw [hm]; omega) with ⟨v, hv⟩
              exact step v 2 (by omega) hv (fun _ hle => erdos21Phi_step_two hm_low hle)
            · by_cases hm_mid : m ≤ 2 * n + 1
              · rcases erdos21_exists_high_degree (d := 3) (by omega) hcard hinter
                    (by rw [hm]; omega) with ⟨v, hv⟩
                exact step v 3 (by omega) hv
                  (fun _ hle => erdos21Phi_step_three (by omega) hm_mid hle)
              · rcases erdos21_exists_high_degree (d := 4) (by omega) hcard hinter
                    (by rw [hm]; omega) with ⟨v, hv⟩
                exact step v 4 (by omega) hv (fun _ hle => erdos21Phi_step_four (by omega) hle)

private lemma erdos21_family_nonempty {n : ℕ} (hn : 1 ≤ n) :
    {m : ℕ | ∃ F : Finset (Finset ℕ), Erdos21.IsErdosLovaszFamily n F ∧ F.card = m}.Nonempty := by
  let U := Finset.range (2 * n - 1)
  let F := U.powersetCard n
  refine ⟨F.card, F, ⟨?_, ?_, ?_⟩, rfl⟩
  · intro A hA
    exact (Finset.mem_powersetCard.mp hA).2
  · intro A hA B hB
    have hAU : A ⊆ U := (Finset.mem_powersetCard.mp hA).1
    have hBU : B ⊆ U := (Finset.mem_powersetCard.mp hB).1
    have hAc : A.card = n := (Finset.mem_powersetCard.mp hA).2
    have hBc : B.card = n := (Finset.mem_powersetCard.mp hB).2
    have hUcard : U.card = 2 * n - 1 := Finset.card_range (2 * n - 1)
    have hunion : (A ∪ B).card ≤ 2 * n - 1 := hUcard ▸ Finset.card_le_card (Finset.union_subset hAU hBU)
    have hsum := Finset.card_union_add_card_inter A B
    exact Finset.card_pos.mp (by omega)
  · intro S hS
    have hsub : U ⊆ (U \ S) ∪ S := by
      intro x hx
      by_cases hxS : x ∈ S
      · exact Finset.mem_union_right _ hxS
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
    have hcardU : U.card ≤ (U \ S).card + S.card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le (U \ S) S)
    have hUcard : U.card = 2 * n - 1 := Finset.card_range (2 * n - 1)
    rw [hUcard] at hcardU
    have hR : n ≤ (U \ S).card := by omega
    rcases Finset.exists_subset_card_eq hR with ⟨A, hAR, hAc⟩
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨Finset.Subset.trans hAR Finset.sdiff_subset, hAc⟩, ?_⟩
    exact Finset.disjoint_left.mpr (fun x hxS hxA => (Finset.mem_sdiff.mp (hAR hxA)).2 hxS)

theorem OMA.solution : type_of% @Erdos21.erdos_21.variants.lower := by
  intro n
  by_cases hn0 : n = 0
  · subst hn0
    have hnn : (0 : ℝ) ≤ (Erdos21.f 0 : ℝ) := Nat.cast_nonneg _
    linarith
  · by_cases hn1 : n = 1
    · subst hn1
      have hnn : (0 : ℝ) ≤ (Erdos21.f 1 : ℝ) := Nat.cast_nonneg _
      linarith
    · have hne := erdos21_family_nonempty (by omega : 1 ≤ n)
      rcases Nat.sInf_mem hne with ⟨F, hF, hFcard⟩
      have hFcard' : F.card = Erdos21.f n := hFcard
      change (8 / 3 : ℝ) * (n : ℝ) - 3 ≤ (Erdos21.f n : ℝ)
      rw [← hFcard']
      by_cases hn2 : n = 2
      · subst hn2
        rcases hF.2.2 ∅ (by simp) with ⟨A, hA, _⟩
        have hA2 : A.card = 2 := hF.1 A hA
        rcases Finset.card_pos.mp (by omega : 0 < A.card) with ⟨a, ha⟩
        rcases hF.2.2 {a} (by simp) with ⟨B, hB, hdisjAB⟩
        have hBA : B ≠ A := by
          intro h
          subst h
          exact Finset.disjoint_left.mp hdisjAB (Finset.mem_singleton_self a) ha
        rcases hF.2.1 A hA B hB with ⟨b, hb⟩
        rw [Finset.mem_inter] at hb
        rcases hF.2.2 {b} (by simp) with ⟨C, hC, hdisjC⟩
        have hCA : C ≠ A := by
          intro h
          subst h
          exact Finset.disjoint_left.mp hdisjC (Finset.mem_singleton_self b) hb.1
        have hCB : C ≠ B := by
          intro h
          subst h
          exact Finset.disjoint_left.mp hdisjC (Finset.mem_singleton_self b) hb.2
        have hsub : {A, B, C} ⊆ F := by
          intro X hX
          simp only [Finset.mem_insert, Finset.mem_singleton] at hX
          rcases hX with rfl | rfl | rfl <;> assumption
        have h3 : 3 ≤ F.card := by
          have hc1 : ({B, C} : Finset (Finset ℕ)).card = 2 := Finset.card_pair hCB.symm
          have hAn : A ∉ ({B, C} : Finset (Finset ℕ)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rintro (rfl | rfl) <;> contradiction
          have hc2 : ({A, B, C} : Finset (Finset ℕ)).card = 3 := by
            rw [Finset.card_insert_of_notMem hAn, hc1]
          exact hc2 ▸ Finset.card_le_card hsub
        have h3R : (3 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast h3
        norm_num
        linarith
      · have hn3 : 3 ≤ n := by omega
        by_contra hlt
        push Not at hlt
        rcases erdos21_exists_hitting_set hn3 F.card F rfl hF.1 hF.2.1 with ⟨S, hShit, hScard⟩
        have hline1 := erdos21Phi_le_line1 n F.card
        have hSlt : (S.card : ℝ) < (n : ℝ) := by linarith
        have hSltNat : S.card < n := by exact_mod_cast hSlt
        rcases hF.2.2 S (by omega) with ⟨A, hA, hdisj⟩
        rcases hShit A hA with ⟨x, hx⟩
        rw [Finset.mem_inter] at hx
        exact Finset.disjoint_left.mp hdisj hx.1 hx.2
