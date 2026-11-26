import FormalConjectures.ErdosProblems.«650»

-- Problem: Erdős Problem 650 — erdos suranyi
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/650.lean:95 (declaration Erdos650.erdos_650.variants.erdos_suranyi)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Erdos650.erdos_650.variants.erdos_suranyi := by
  intro m
  by_cases hm : m = 0
  · subst hm
    simp
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  let S : Set ℕ :=
    {r : ℕ | ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N, A.card = m → ∀ x : ℝ, 1 ≤ x →
      ∃ a b : Fin r → ℕ, Function.Injective a ∧ Function.Injective b ∧
        (∀ i, a i ∈ A) ∧ (∀ i, (b i : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ))) ∧ (∀ i, a i ∣ b i)}
  have hS_bdd : BddAbove S := by
    refine ⟨m, fun r hr => ?_⟩
    obtain ⟨a, _, ha_inj, _, ha_mem, _, _⟩ :=
      hr m (Finset.Icc 1 m) (fun _ h => h) (by simp) 1 le_rfl
    have hle := Fintype.card_le_of_injective (fun i : Fin r => (⟨a i, ha_mem i⟩ : Finset.Icc 1 m))
      (fun i j hij => ha_inj (congrArg Subtype.val hij))
    simpa [Fintype.card_coe] using hle
  obtain ⟨r0, hr0_def⟩ : ∃ r0 : ℕ, r0 = ⌈Real.sqrt m⌉₊ := ⟨_, rfl⟩
  have hr0_mem : r0 ∈ S := by
    intro N A hAN hAcard x hx
    have hN1 : 1 ≤ N := by
      have hne : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨z, hz⟩ := hne
      have hz' := Finset.mem_Icc.mp (hAN hz)
      omega
    have hmult1 : ∀ a ∈ Finset.Icc 1 N,
        ∃ b : ℕ, (b : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ)) ∧ a ∣ b := by
      intro a ha
      obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
      have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha1
      let q : ℕ := ⌊x / (a : ℝ)⌋₊ + 1
      refine ⟨q * a, ⟨?_, ?_⟩, dvd_mul_left a q⟩
      · have hlt : x / (a : ℝ) < (q : ℝ) := by
          push_cast [q]
          exact Nat.lt_floor_add_one (x / (a : ℝ))
        have hlt2 := (div_lt_iff₀ ha_pos).mp hlt
        push_cast
        exact hlt2
      · have hle : (⌊x / (a : ℝ)⌋₊ : ℝ) ≤ x / (a : ℝ) :=
          Nat.floor_le (div_nonneg (by linarith) ha_pos.le)
        have hle2 : (⌊x / (a : ℝ)⌋₊ : ℝ) * (a : ℝ) ≤ x := (le_div_iff₀ ha_pos).mp hle
        have haN_r : (a : ℝ) ≤ N := by exact_mod_cast haN
        have hN1_r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        push_cast [q]
        linarith
    have hmult2 : ∀ a : ℕ, 1 ≤ a → a < N →
        ∃ u v : ℕ, u < v ∧ v - u = a ∧
          (u : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ)) ∧
          (v : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ)) ∧
          a ∣ u ∧ a ∣ v := by
      intro a ha1 haN
      have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha1
      let q : ℕ := ⌊x / (a : ℝ)⌋₊ + 1
      refine ⟨q * a, (q + 1) * a, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, dvd_mul_left a q, dvd_mul_left a (q + 1)⟩
      · nlinarith
      · have : (q + 1) * a = q * a + a := by ring
        omega
      · have hlt : x / (a : ℝ) < (q : ℝ) := by
          push_cast [q]
          exact Nat.lt_floor_add_one (x / (a : ℝ))
        have hlt2 := (div_lt_iff₀ ha_pos).mp hlt
        push_cast
        exact hlt2
      · have hle : (⌊x / (a : ℝ)⌋₊ : ℝ) ≤ x / (a : ℝ) :=
          Nat.floor_le (div_nonneg (by linarith) ha_pos.le)
        have hle2 : (⌊x / (a : ℝ)⌋₊ : ℝ) * (a : ℝ) ≤ x := (le_div_iff₀ ha_pos).mp hle
        have haN_r : (a : ℝ) < N := by exact_mod_cast haN
        push_cast [q]
        linarith
      · have hlt : x / (a : ℝ) < (q : ℝ) := by
          push_cast [q]
          exact Nat.lt_floor_add_one (x / (a : ℝ))
        have hlt2 := (div_lt_iff₀ ha_pos).mp hlt
        have hqa : (q : ℝ) * a < ((q : ℝ) + 1) * a := by nlinarith
        push_cast
        linarith
      · have hle : (⌊x / (a : ℝ)⌋₊ : ℝ) ≤ x / (a : ℝ) :=
          Nat.floor_le (div_nonneg (by linarith) ha_pos.le)
        have hle2 : (⌊x / (a : ℝ)⌋₊ : ℝ) * (a : ℝ) ≤ x := (le_div_iff₀ ha_pos).mp hle
        have haN_r : (a : ℝ) < N := by exact_mod_cast haN
        push_cast [q]
        linarith
    let M : ℕ → Prop := fun r =>
      ∃ a b : Fin r → ℕ, Function.Injective a ∧ Function.Injective b ∧
        (∀ i, a i ∈ A) ∧ (∀ i, (b i : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ))) ∧ (∀ i, a i ∣ b i)
    have hM_bdd : BddAbove {r : ℕ | M r} := by
      refine ⟨m, fun r ⟨a, _, ha_inj, _, ha_mem, _, _⟩ => ?_⟩
      have hle := Fintype.card_le_of_injective (fun i : Fin r => (⟨a i, ha_mem i⟩ : A))
        (fun i j hij => ha_inj (congrArg Subtype.val hij))
      simpa [Fintype.card_coe, hAcard] using hle
    have hM_ne : ({r : ℕ | M r}).Nonempty := by
      refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i <;> exact i.elim0
    obtain ⟨k, hk_def, hMk, hnotMk1⟩ : ∃ k : ℕ, k = sSup {r : ℕ | M r} ∧ M k ∧ ¬ M (k + 1) := by
      refine ⟨sSup {r : ℕ | M r}, rfl, Nat.sSup_mem hM_ne hM_bdd, fun h => ?_⟩
      have hle : sSup {r : ℕ | M r} + 1 ≤ sSup {r : ℕ | M r} := le_csSup hM_bdd h
      omega
    obtain ⟨a, b, ha_inj, hb_inj, ha_mem, hb_mem, hdvd⟩ := hMk
    have h_extend : ∀ a' ∈ A, a' ∉ Finset.image a Finset.univ →
        ∀ b' : ℕ, (b' : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ)) → a' ∣ b' →
        b' ∈ Finset.image b Finset.univ := by
      intro a' ha' ha'_not b' hb' hdvd'
      by_contra hb'_not
      apply hnotMk1
      refine ⟨Fin.snoc a a', Fin.snoc b b', ?_, ?_, ?_, ?_, ?_⟩
      · intro i j
        refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro hij
        · rfl
        · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact False.elim (ha'_not (Finset.mem_image.mpr ⟨j', Finset.mem_univ _, hij.symm⟩))
        · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij
          exact False.elim (ha'_not (Finset.mem_image.mpr ⟨i', Finset.mem_univ _, hij⟩))
        · simp only [Fin.snoc_castSucc] at hij
          exact congrArg Fin.castSucc (ha_inj hij)
      · intro i j
        refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro hij
        · rfl
        · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact False.elim (hb'_not (Finset.mem_image.mpr ⟨j', Finset.mem_univ _, hij.symm⟩))
        · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij
          exact False.elim (hb'_not (Finset.mem_image.mpr ⟨i', Finset.mem_univ _, hij⟩))
        · simp only [Fin.snoc_castSucc] at hij
          exact congrArg Fin.castSucc (hb_inj hij)
      · intro i
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · simpa using ha'
        · simpa using ha_mem i'
      · intro i
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · simpa using hb'
        · simpa using hb_mem i'
      · intro i
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · simpa using hdvd'
        · simpa using hdvd i'
    have hk_ge1 : 1 ≤ k := by
      by_contra hk0
      have hne : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a0, ha0⟩ := hne
      obtain ⟨b0, hb0, hd0⟩ := hmult1 a0 (hAN ha0)
      have ha0_not : a0 ∉ Finset.image a Finset.univ := by
        intro h
        obtain ⟨i, _, _⟩ := Finset.mem_image.mp h
        exact absurd i.isLt (by omega)
      have hb0_mem := h_extend a0 ha0 ha0_not b0 hb0 hd0
      obtain ⟨i, _, _⟩ := Finset.mem_image.mp hb0_mem
      exact absurd i.isLt (by omega)
    have hm_le_k2 : m ≤ k ^ 2 := by
      by_cases hm_eq1 : m = 1
      · nlinarith
      by_cases hm_eq2 : m = 2
      · obtain ⟨x1, x2, hne12, hAeq⟩ := Finset.card_eq_two.mp (hm_eq2 ▸ hAcard)
        have hM2 : M 2 := by
          have hpair : ∀ u v : ℕ, u < v → u ∈ A → v ∈ A → M 2 := by
            intro u v huv hu hv
            have hu1 : 1 ≤ u := (Finset.mem_Icc.mp (hAN hu)).1
            have hvN : v ≤ N := (Finset.mem_Icc.mp (hAN hv)).2
            have huN : u < N := lt_of_lt_of_le huv hvN
            obtain ⟨y1, hy1, hdy1⟩ := hmult1 v (hAN hv)
            obtain ⟨w1, w2, hw12, _, hmw1, hmw2, hdw1, hdw2⟩ := hmult2 u hu1 huN
            have hchoose : ∃ w : ℕ, w ≠ y1 ∧ (w : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ)) ∧ u ∣ w := by
              by_cases hw1_eq : w1 = y1
              · exact ⟨w2, by omega, hmw2, hdw2⟩
              · exact ⟨w1, hw1_eq, hmw1, hdw1⟩
            obtain ⟨w, hwy1, hmw, hdw⟩ := hchoose
            refine ⟨fun i => if i = 0 then u else v, fun i => if i = 0 then w else y1, ?_, ?_, ?_, ?_, ?_⟩
            · intro i j hij
              fin_cases i <;> fin_cases j
              · rfl
              · simp at hij; omega
              · simp at hij; omega
              · rfl
            · intro i j hij
              fin_cases i <;> fin_cases j
              · rfl
              · exact absurd (by simpa using hij) hwy1
              · exact absurd (by simpa using hij.symm) hwy1
              · rfl
            · intro i; fin_cases i <;> [exact hu; exact hv]
            · intro i; fin_cases i <;> [exact hmw; exact hy1]
            · intro i; fin_cases i <;> [exact hdw; exact hdy1]
          rcases lt_or_gt_of_ne hne12 with hlt | hlt
          · exact hpair x1 x2 hlt (by simp [hAeq]) (by simp [hAeq])
          · exact hpair x2 x1 hlt (by simp [hAeq]) (by simp [hAeq])
        have h2k : 2 ≤ k := hk_def ▸ le_csSup hM_bdd hM2
        nlinarith
      have hm3 : 3 ≤ m := by omega
      have hk2 : 2 ≤ k := by
        by_contra hk1
        have hk_eq1 : k = 1 := by omega
        let SA := Finset.image a Finset.univ
        have hSA_card : SA.card ≤ 1 := Finset.card_image_le.trans (by simp [hk_eq1])
        have hdiff_sub : A \ SA ⊆ {N} := by
          intro a' ha'
          rw [Finset.mem_sdiff] at ha'
          rcases ha' with ⟨ha'A, ha'SA⟩
          rw [Finset.mem_singleton]
          by_contra ha'neN
          have ha'Icc := Finset.mem_Icc.mp (hAN ha'A)
          have ha'ltN : a' < N := lt_of_le_of_ne ha'Icc.2 ha'neN
          obtain ⟨u, v, huv, _, hu_mem, hv_mem, hdu, hdv⟩ := hmult2 a' ha'Icc.1 ha'ltN
          have huB := h_extend a' ha'A ha'SA u hu_mem hdu
          have hvB := h_extend a' ha'A ha'SA v hv_mem hdv
          have hB_card : (Finset.image b Finset.univ).card ≤ 1 :=
            Finset.card_image_le.trans (by simp [hk_eq1])
          have hpair_sub : ({u, v} : Finset ℕ) ⊆ Finset.image b Finset.univ := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          have h2le1 := (Finset.card_pair (ne_of_lt huv)).symm.trans_le
            ((Finset.card_le_card hpair_sub).trans hB_card)
          omega
        have hA_sub : A ⊆ (A \ SA) ∪ SA := fun z hz => by
          by_cases h : z ∈ SA <;> simp [hz, h]
        have hcard_le := (Finset.card_le_card hA_sub).trans (Finset.card_union_le _ _)
        have hdiff_le := (Finset.card_le_card hdiff_sub).trans (Finset.card_singleton N).le
        omega
      let SA := Finset.image a Finset.univ
      let TB := Finset.image b Finset.univ
      let g : Finset ℕ → ℕ := fun t => t.sup id - (t.erase (t.sup id)).sup id
      have hsub_img : (A \ SA).erase N ⊆ (TB.powersetCard 2).image g := by
        intro a' ha'
        rw [Finset.mem_erase, Finset.mem_sdiff] at ha'
        rcases ha' with ⟨ha'N, ha'A, ha'SA⟩
        have ha'Icc := Finset.mem_Icc.mp (hAN ha'A)
        have ha'ltN : a' < N := lt_of_le_of_ne ha'Icc.2 ha'N
        obtain ⟨u, v, huv, hvu, hu_mem, hv_mem, hdu, hdv⟩ := hmult2 a' ha'Icc.1 ha'ltN
        have huTB := h_extend a' ha'A ha'SA u hu_mem hdu
        have hvTB := h_extend a' ha'A ha'SA v hv_mem hdv
        refine Finset.mem_image.mpr ⟨{u, v}, Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair (ne_of_lt huv)⟩, ?_⟩
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        · have hsup : ({u, v} : Finset ℕ).sup id = v := by
            simp [Finset.sup_insert, Finset.sup_singleton, max_eq_right (le_of_lt huv)]
          have herase : ({u, v} : Finset ℕ).erase v = {u} := by
            ext z
            simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hzv, rfl | rfl⟩
              · rfl
              · exact False.elim (hzv rfl)
            · rintro rfl
              exact ⟨ne_of_lt huv, Or.inl rfl⟩
          simp [g, hsup, herase, hvu]
      have hcard_img : ((A \ SA).erase N).card ≤ (TB.powersetCard 2).card :=
        (Finset.card_le_card hsub_img).trans Finset.card_image_le
      rw [Finset.card_powersetCard, Nat.choose_two_right] at hcard_img
      have hTB_le : TB.card ≤ k := Finset.card_image_le.trans (Finset.card_fin k).le
      have hSA_le : SA.card ≤ k := Finset.card_image_le.trans (Finset.card_fin k).le
      have hA_sub : A ⊆ (A \ SA) ∪ SA := by
        rw [Finset.sdiff_union_self_eq_union]
        exact Finset.subset_union_left
      have hA_le := (Finset.card_le_card hA_sub).trans (Finset.card_union_le _ _)
      have herase_sub : A \ SA ⊆ insert N ((A \ SA).erase N) := by
        intro z hz
        by_cases h : z = N
        · rw [h]; exact Finset.mem_insert_self N _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hz⟩)
      have herase_le : (A \ SA).card ≤ ((A \ SA).erase N).card + 1 :=
        (Finset.card_le_card herase_sub).trans (Finset.card_insert_le _ _)
      have hchoose_le : TB.card * (TB.card - 1) / 2 ≤ k * (k - 1) / 2 :=
        Nat.div_le_div_right (Nat.mul_le_mul hTB_le (Nat.sub_le_sub_right hTB_le 1))
      have hdiv_mul : k * (k - 1) / 2 * 2 ≤ k * (k - 1) := Nat.div_mul_le_self _ 2
      have hmul_le : m ≤ k + 1 + k * (k - 1) / 2 := by omega
      have h2m : 2 * m ≤ 2 * k + 2 + k * (k - 1) := by omega
      have hk_sq : 2 * k + 2 + k * (k - 1) ≤ 2 * k ^ 2 := by
        have hk_sub : k - 1 + 1 = k := by omega
        nlinarith
      omega
    have hr0_le_k : r0 ≤ k := by
      rw [hr0_def]
      refine Nat.ceil_le.mpr ?_
      have hm_r : (m : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hm_le_k2
      calc
        Real.sqrt m ≤ Real.sqrt ((k : ℝ) ^ 2) := Real.sqrt_le_sqrt hm_r
        _ = (k : ℝ) := Real.sqrt_sq (Nat.cast_nonneg k)
    refine ⟨a ∘ Fin.castLE hr0_le_k, b ∘ Fin.castLE hr0_le_k, ?_, ?_, ?_, ?_, ?_⟩
    · exact ha_inj.comp (fun i j hij => by simpa [Fin.ext_iff] using hij)
    · exact hb_inj.comp (fun i j hij => by simpa [Fin.ext_iff] using hij)
    · intro i
      exact ha_mem (Fin.castLE hr0_le_k i)
    · intro i
      exact hb_mem (Fin.castLE hr0_le_k i)
    · intro i
      exact hdvd (Fin.castLE hr0_le_k i)
  have hr0_le_f : r0 ≤ Erdos650.f m := le_csSup hS_bdd hr0_mem
  have h1 : Real.sqrt m ≤ (r0 : ℝ) := hr0_def ▸ Nat.le_ceil (Real.sqrt m)
  have h2 : (r0 : ℝ) ≤ (Erdos650.f m : ℝ) := by exact_mod_cast hr0_le_f
  exact le_trans h1 h2
