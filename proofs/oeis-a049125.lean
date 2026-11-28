import OMAStatements.S_oeis_a049125

namespace Antigravity2_oeis_a049125

open OMA.S_oeis_a049125 PowerSeries Finset BigOperators

def Valid (m : ℕ) (e : Fin m → ℕ) : Prop :=
  (∀ i : Fin m, e i ≤ i.val) ∧ ∀ i j k : Fin m, i < j → j < k → e i < e k

instance (m : ℕ) (e : Fin m → ℕ) : Decidable (Valid m e) := by
  unfold Valid
  infer_instance

def validFinset (m : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun i : Fin m => range (i.val + 1)).filter fun e => Valid m e

lemma mem_validFinset {m : ℕ} {e : Fin m → ℕ} :
    e ∈ validFinset m ↔ Valid m e := by
  simp only [validFinset, mem_filter, Fintype.mem_piFinset, mem_range, Nat.lt_succ_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma invSeqCount_eq_card (m : ℕ) : invSeqCount m = (validFinset m).card := by
  unfold invSeqCount
  have hset : {e : Fin m → ℕ | (∀ i : Fin m, e i ≤ i.val) ∧
      ∀ i j k : Fin m, i < j → j < k → e i < e k} = (validFinset m : Set (Fin m → ℕ)) := by
    ext e
    simp [mem_validFinset, Valid]
  rw [hset, Set.ncard_coe_finset]

def maxVal {m : ℕ} (e : Fin m → ℕ) : ℕ :=
  Finset.univ.sup e

lemma le_maxVal {m : ℕ} (e : Fin m → ℕ) (i : Fin m) : e i ≤ maxVal e :=
  Finset.le_sup (Finset.mem_univ i)

lemma maxVal_le_iff {m : ℕ} (e : Fin m → ℕ) (k : ℕ) :
    maxVal e ≤ k ↔ ∀ i : Fin m, e i ≤ k := by
  simp [maxVal]

lemma maxVal_lt_of_forall_lt {m : ℕ} (hm : 0 < m) (e : Fin m → ℕ) (k : ℕ)
    (h : ∀ i : Fin m, e i < k) : maxVal e < k := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty e
  change maxVal e < k
  unfold maxVal
  rw [hi]
  exact h i

lemma maxVal_le_pred {m : ℕ} {e : Fin m → ℕ} (he : Valid m e) : maxVal e ≤ m - 1 := by
  rw [maxVal_le_iff]
  intro i
  have := he.1 i
  omega

def slack {m : ℕ} (e : Fin m → ℕ) : ℕ :=
  if m = 0 then 0 else (m - 1) - maxVal e

lemma slack_le {m : ℕ} (e : Fin m → ℕ) : slack e ≤ m := by
  unfold slack
  split_ifs <;> omega

def validSlack (m h : ℕ) : Finset (Fin m → ℕ) :=
  (validFinset m).filter fun e => slack e = h

def f (m h : ℕ) : ℕ := (validSlack m h).card

lemma f_zero_zero : f 0 0 = 1 := by
  unfold f validSlack
  have hcard : (validFinset 0).filter (fun e => slack e = 0) = {Fin.elim0} := by
    ext e
    simp only [mem_filter, mem_validFinset, mem_singleton]
    constructor
    · intro _; funext i; exact Fin.elim0 i
    · rintro rfl
      refine ⟨⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, by simp [slack]⟩
  rw [hcard, card_singleton]

lemma f_zero_succ (h : ℕ) : f 0 (h + 1) = 0 := by
  unfold f validSlack
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e _
  simp [slack]

lemma f_eq_zero_of_gt {m h : ℕ} (hmh : m < h) : f m h = 0 := by
  unfold f validSlack
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e _
  have := slack_le e
  omega

lemma invSeqCount_eq_sum_f (m : ℕ) :
    invSeqCount m = ∑ h ∈ range (m + 1), f m h := by
  rw [invSeqCount_eq_card]
  have hpart : validFinset m = (range (m + 1)).biUnion (validSlack m) := by
    ext e
    simp only [mem_biUnion, mem_range, validSlack, mem_filter]
    constructor
    · intro he
      exact ⟨slack e, Nat.lt_succ_of_le (slack_le e), he, rfl⟩
    · rintro ⟨_, _, he, _⟩
      exact he
  rw [hpart, card_biUnion]
  · rfl
  · intro h1 _ h2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [validSlack, mem_filter] at he1 he2
    exact hne (he1.2.symm.trans he2.2)

lemma f_one_zero : f 1 0 = 1 := by
  unfold f validSlack
  have hcard : (validFinset 1).filter (fun e => slack e = 0) = {fun _ => 0} := by
    ext e
    simp only [mem_filter, mem_validFinset, mem_singleton]
    constructor
    · intro h
      funext i
      have hi : i.val = 0 := by omega
      have := h.1.1 i
      omega
    · rintro rfl
      refine ⟨⟨fun _ => Nat.zero_le _, fun i j k hij hjk => ?_⟩, ?_⟩
      · exfalso; omega
      · simp [slack, maxVal]
  rw [hcard, card_singleton]

lemma f_one_succ (h : ℕ) : f 1 (h + 1) = 0 := by
  unfold f validSlack
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he
  have hle : maxVal e ≤ 0 := maxVal_le_pred (mem_validFinset.mp he)
  simp [slack]

lemma f_succ_zero (m : ℕ) : f (m + 1) 0 = ∑ h' ∈ range (m + 1), f m h' := by
  cases m with
  | zero => simp [f_one_zero, f_zero_zero]
  | succ m' =>
    set n := m' + 1
    rw [← invSeqCount_eq_sum_f n, invSeqCount_eq_card]
    unfold f validSlack
    refine Finset.card_bij (fun e _ => fun i : Fin n => e (Fin.castSucc i)) ?_ ?_ ?_
    · intro e he
      simp only [mem_filter, mem_validFinset] at he ⊢
      exact ⟨fun i => he.1.1 (Fin.castSucc i),
        fun i j k hij hjk => he.1.2 _ _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij)
          (Fin.castSucc_lt_castSucc_iff.mpr hjk)⟩
    · intro e1 he1 e2 he2 hpre
      simp only [mem_filter, mem_validFinset] at he1 he2
      have hlast1 : e1 ⟨n, by omega⟩ = n := by
        have hmax : maxVal e1 = n := by
          have hs := he1.2
          simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] at hs
          have hle := maxVal_le_pred he1.1
          omega
        have : Nonempty (Fin (n + 1)) := ⟨⟨0, by omega⟩⟩
        obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty e1
        have heq : e1 i = n := by rw [← hi]; exact hmax
        have hile : i.val = n := by have := he1.1.1 i; omega
        have hi_eq : i = ⟨n, by omega⟩ := Fin.ext hile
        rwa [← hi_eq]
      have hlast2 : e2 ⟨n, by omega⟩ = n := by
        have hmax : maxVal e2 = n := by
          have hs := he2.2
          simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] at hs
          have hle := maxVal_le_pred he2.1
          omega
        have : Nonempty (Fin (n + 1)) := ⟨⟨0, by omega⟩⟩
        obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty e2
        have heq : e2 i = n := by rw [← hi]; exact hmax
        have hile : i.val = n := by have := he2.1.1 i; omega
        have hi_eq : i = ⟨n, by omega⟩ := Fin.ext hile
        rwa [← hi_eq]
      funext i
      by_cases hi : i.val < n
      · exact congrFun hpre ⟨i.val, hi⟩
      · have hieq : i = ⟨n, by omega⟩ := Fin.ext (by show i.val = n; omega)
        rw [hieq, hlast1, hlast2]
    · intro e' he'
      rw [mem_validFinset] at he'
      let e : Fin (n + 1) → ℕ := fun i =>
        if hi : i.val < n then e' ⟨i.val, hi⟩ else n
      refine ⟨e, ?_, ?_⟩
      · simp only [mem_filter, mem_validFinset]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro i
          simp only [e]
          split_ifs with hi
          · exact he'.1 ⟨i.val, hi⟩
          · omega
        · intro i j k hij hjk
          have hi : i.val < n := by omega
          simp only [e, hi, dite_true]
          by_cases hk : k.val < n
          · have hj : j.val < n := by omega
            simp only [hk, dite_true]
            exact he'.2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk
          · simp only [hk, dite_false]
            have := he'.1 ⟨i.val, hi⟩
            omega
        · simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
          have hge : n ≤ maxVal e := by
            have := le_maxVal e ⟨n, by omega⟩
            simpa [e] using this
          have hle : maxVal e ≤ n := by
            rw [maxVal_le_iff]
            intro i
            simp only [e]
            split_ifs with hi
            · have := he'.1 ⟨i.val, hi⟩; omega
            · omega
          omega
      · funext i
        simp [e, i.isLt]

lemma f_succ_succ (m h : ℕ) (hm : 1 ≤ m) :
    f (m + 1) (h + 1) =
      (∑ h' ∈ Icc (h + 1) m, f m h') +
      (∑ h'' ∈ Icc h (m - 1), (h'' + 1 - h) * f (m - 1) h'') := by
  by_cases hhm : m < h + 1
  · have h0 : f (m + 1) (h + 1) = 0 := by
      unfold f validSlack
      rw [card_eq_zero, filter_eq_empty_iff]
      intro e _
      simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      omega
    have h1 : Icc (h + 1) m = ∅ := Icc_eq_empty (by omega)
    have h2 : Icc h (m - 1) = ∅ := Icc_eq_empty (by omega)
    rw [h0, h1, h2]
    simp
  have hhm' : h + 1 ≤ m := by omega
  set S := validSlack (m + 1) (h + 1)
  set S1 := S.filter fun e => e ⟨m - 1, by omega⟩ < e ⟨m, by omega⟩
  set S2 := S.filter fun e => e ⟨m, by omega⟩ ≤ e ⟨m - 1, by omega⟩
  have hsplit : S.card = S1.card + S2.card := by
    have hunion : S = S1 ∪ S2 := by
      ext e
      simp only [S1, S2, mem_union, mem_filter]
      constructor
      · intro he
        rcases lt_or_ge (e ⟨m - 1, by omega⟩) (e ⟨m, by omega⟩) with hlt | hge
        · exact Or.inl ⟨he, hlt⟩
        · exact Or.inr ⟨he, hge⟩
      · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      simp only [S1, S2, mem_filter] at he1 he2
      omega
    rw [hunion, card_union_of_disjoint hdisj]
  change S.card = _
  rw [hsplit]
  congr 1
  · -- S1.card = ∑ h' ∈ Icc (h + 1) m, f m h'
    have hT1 : (∑ h' ∈ Icc (h + 1) m, f m h') =
        ((validFinset m).filter fun e' => h + 1 ≤ slack e').card := by
      have hbi : (validFinset m).filter (fun e' => h + 1 ≤ slack e') =
          (Icc (h + 1) m).biUnion (validSlack m) := by
        ext e'
        simp only [mem_filter, mem_biUnion, mem_Icc, validSlack]
        constructor
        · rintro ⟨he', hle⟩
          exact ⟨slack e', ⟨hle, slack_le e'⟩, he', rfl⟩
        · rintro ⟨h', ⟨hh', _⟩, he', rfl⟩
          exact ⟨he', hh'⟩
      rw [hbi, card_biUnion]
      · rfl
      · intro a _ b _ hab
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro e ha hb
        simp only [validSlack, mem_filter] at ha hb
        exact hab (ha.2.symm.trans hb.2)
    rw [hT1]
    refine Finset.card_bij (fun e _ => fun i : Fin m => e (Fin.castSucc i)) ?_ ?_ ?_
    · intro e he
      simp only [S1, S, validSlack, mem_filter, mem_validFinset] at he ⊢
      obtain ⟨⟨hval, hsl⟩, hinc⟩ := he
      have hpre_val : Valid m (fun i : Fin m => e (Fin.castSucc i)) :=
        ⟨fun i => hval.1 (Fin.castSucc i),
         fun i j k hij hjk => hval.2 _ _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij)
           (Fin.castSucc_lt_castSucc_iff.mpr hjk)⟩
      have hall_lt : ∀ i : Fin m, e (Fin.castSucc i) < e ⟨m, by omega⟩ := by
        intro i
        by_cases him : i.val = m - 1
        · have : Fin.castSucc i = ⟨m - 1, by omega⟩ := Fin.ext him
          rw [this]; exact hinc
        · exact hval.2 (Fin.castSucc i) ⟨m - 1, by omega⟩ ⟨m, by omega⟩
            (by show i.val < m - 1; omega) (by show m - 1 < m; omega)
      have hmax_e : maxVal e = e ⟨m, by omega⟩ := by
        apply le_antisymm
        · rw [maxVal_le_iff]
          intro i
          by_cases hi : i.val < m
          · exact (hall_lt ⟨i.val, hi⟩).le
          · have : i = ⟨m, by omega⟩ := Fin.ext (by show i.val = m; omega)
            rw [this]
        · exact le_maxVal e ⟨m, by omega⟩
      have hmax_pre_lt : maxVal (fun i : Fin m => e (Fin.castSucc i)) < e ⟨m, by omega⟩ :=
        maxVal_lt_of_forall_lt hm _ _ hall_lt
      simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] at hsl
      have hm0 : m ≠ 0 := by omega
      simp only [slack, hm0, if_false]
      have hle_m : e ⟨m, by omega⟩ ≤ m := hval.1 ⟨m, by omega⟩
      refine ⟨hpre_val, ?_⟩
      omega
    · intro e1 he1 e2 he2 hpre
      simp only [S1, S, validSlack, mem_filter, mem_validFinset] at he1 he2
      have hmax_last : ∀ e : Fin (m + 1) → ℕ, Valid (m + 1) e → slack e = h + 1 →
          e ⟨m - 1, by omega⟩ < e ⟨m, by omega⟩ → e ⟨m, by omega⟩ = m - (h + 1) := by
        intro e hval hsl hinc
        have hall_lt : ∀ i : Fin m, e (Fin.castSucc i) < e ⟨m, by omega⟩ := by
          intro i
          by_cases him : i.val = m - 1
          · have : Fin.castSucc i = ⟨m - 1, by omega⟩ := Fin.ext him
            rw [this]; exact hinc
          · exact hval.2 (Fin.castSucc i) ⟨m - 1, by omega⟩ ⟨m, by omega⟩
              (by show i.val < m - 1; omega) (by show m - 1 < m; omega)
        have hmax_e : maxVal e = e ⟨m, by omega⟩ := by
          apply le_antisymm
          · rw [maxVal_le_iff]
            intro i
            by_cases hi : i.val < m
            · exact (hall_lt ⟨i.val, hi⟩).le
            · have : i = ⟨m, by omega⟩ := Fin.ext (by show i.val = m; omega)
              rw [this]
          · exact le_maxVal e ⟨m, by omega⟩
        simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hmax_e] at hsl
        have hle_m : e ⟨m, by omega⟩ ≤ m := hval.1 ⟨m, by omega⟩
        omega
      have hl1 := hmax_last e1 he1.1.1 he1.1.2 he1.2
      have hl2 := hmax_last e2 he2.1.1 he2.1.2 he2.2
      funext i
      by_cases hi : i.val < m
      · exact congrFun hpre ⟨i.val, hi⟩
      · have hieq : i = ⟨m, by omega⟩ := Fin.ext (by show i.val = m; omega)
        rw [hieq, hl1, hl2]
    · intro e' he'
      simp only [mem_filter, mem_validFinset] at he'
      obtain ⟨hval', hsl'⟩ := he'
      have hm0 : m ≠ 0 := by omega
      simp only [slack, hm0, if_false] at hsl'
      have hmax'_le : maxVal e' ≤ m - 1 := maxVal_le_pred hval'
      have hmax'_lt : maxVal e' < m - (h + 1) := by omega
      let e : Fin (m + 1) → ℕ := fun i =>
        if hi : i.val < m then e' ⟨i.val, hi⟩ else m - (h + 1)
      refine ⟨e, ?_, ?_⟩
      · simp only [S1, S, validSlack, mem_filter, mem_validFinset]
        have he_val : Valid (m + 1) e := by
          refine ⟨?_, ?_⟩
          · intro i
            simp only [e]
            split_ifs with hi
            · exact hval'.1 ⟨i.val, hi⟩
            · omega
          · intro i j k hij hjk
            have hi : i.val < m := by omega
            simp only [e, hi, dite_true]
            by_cases hk : k.val < m
            · have hj : j.val < m := by omega
              simp only [hk, dite_true]
              exact hval'.2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk
            · simp only [hk, dite_false]
              exact lt_of_le_of_lt (le_maxVal e' ⟨i.val, hi⟩) hmax'_lt
        have hmax_e : maxVal e = m - (h + 1) := by
          apply le_antisymm
          · rw [maxVal_le_iff]
            intro i
            simp only [e]
            split_ifs with hi
            · exact (lt_of_le_of_lt (le_maxVal e' ⟨i.val, hi⟩) hmax'_lt).le
            · exact le_rfl
          · have := le_maxVal e ⟨m, by omega⟩
            simpa [e] using this
        have hsl_e : slack e = h + 1 := by
          simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hmax_e]
          omega
        have hinc_e : e ⟨m - 1, by omega⟩ < e ⟨m, by omega⟩ := by
          have h1 : m - 1 < m := by omega
          have h2 : ¬ m < m := Nat.lt_irrefl m
          simp only [e, h1, h2, dite_true, dite_false]
          exact lt_of_le_of_lt (le_maxVal e' ⟨m - 1, h1⟩) hmax'_lt
        exact ⟨⟨he_val, hsl_e⟩, hinc_e⟩
      · funext i
        simp [e, i.isLt]
  · -- S2.card = ∑ h'' ∈ Icc h (m - 1), (h'' + 1 - h) * f (m - 1) h''
    set P : Finset ((Fin (m - 1) → ℕ) × ℕ) :=
      (validFinset (m - 1)).biUnion fun e'' =>
        (Icc (m - 1 - slack e'') (m - (h + 1))).map
          ⟨fun y => (e'', y), fun y1 y2 hy => (Prod.mk.inj hy).2⟩
    have hP_card : P.card = ∑ h'' ∈ Icc h (m - 1), (h'' + 1 - h) * f (m - 1) h'' := by
      have hdisj : (validFinset (m - 1) : Set (Fin (m - 1) → ℕ)).PairwiseDisjoint
          (fun e'' => (Icc (m - 1 - slack e'') (m - (h + 1))).map
            ⟨fun y => (e'', y), fun y1 y2 hy => (Prod.mk.inj hy).2⟩) := by
        intro e1 _ e2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [mem_map] at hp1 hp2
        obtain ⟨y1, _, rfl⟩ := hp1
        obtain ⟨y2, _, heq⟩ := hp2
        exact hne (Prod.mk.inj heq).1.symm
      rw [card_biUnion hdisj]
      have hcard_each : ∀ e'' ∈ validFinset (m - 1),
          ((Icc (m - 1 - slack e'') (m - (h + 1))).map
            ⟨fun y => (e'', y), fun y1 y2 hy => (Prod.mk.inj hy).2⟩).card =
          if h ≤ slack e'' then slack e'' + 1 - h else 0 := by
        intro e'' _
        rw [card_map, Nat.card_Icc]
        have hsl_le : slack e'' ≤ m - 1 := slack_le e''
        by_cases hh : h ≤ slack e''
        · rw [if_pos hh]
          omega
        · rw [if_neg hh]
          omega
      rw [sum_congr rfl hcard_each]
      have hpart : validFinset (m - 1) = (range m).biUnion (validSlack (m - 1)) := by
        ext e''
        simp only [mem_biUnion, mem_range, validSlack, mem_filter]
        constructor
        · intro he''
          have := slack_le e''
          exact ⟨slack e'', by omega, he'', rfl⟩
        · rintro ⟨_, _, he'', _⟩
          exact he''
      rw [hpart, sum_biUnion]
      · have hterm : ∀ h'' ∈ range m,
            ∑ e'' ∈ validSlack (m - 1) h'', (if h ≤ slack e'' then slack e'' + 1 - h else 0) =
            if h ≤ h'' then (h'' + 1 - h) * f (m - 1) h'' else 0 := by
          intro h'' _
          have hc : ∀ e'' ∈ validSlack (m - 1) h'',
              (if h ≤ slack e'' then slack e'' + 1 - h else 0) =
              if h ≤ h'' then h'' + 1 - h else 0 := by
            intro e'' he''
            simp only [validSlack, mem_filter] at he''
            rw [he''.2]
          rw [sum_congr rfl hc, sum_const, smul_eq_mul]
          by_cases hh : h ≤ h''
          · simp [hh, f, mul_comm]
          · simp [hh]
        rw [sum_congr rfl hterm]
        rw [← sum_filter]
        refine sum_congr ?_ fun _ _ => rfl
        ext h''
        simp only [mem_filter, mem_range, mem_Icc]
        omega
      · intro a _ b _ hab
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro e ha hb
        simp only [validSlack, mem_filter] at ha hb
        exact hab (ha.2.symm.trans hb.2)
    rw [← hP_card]
    refine Finset.card_bij
      (fun e _ => (fun i : Fin (m - 1) => e ⟨i.val, by omega⟩, e ⟨m, by omega⟩)) ?_ ?_ ?_
    · intro e he
      simp only [S2, S, validSlack, mem_filter, mem_validFinset] at he
      obtain ⟨⟨hval, hsl⟩, hdec⟩ := he
      let e'' : Fin (m - 1) → ℕ := fun i => e ⟨i.val, by omega⟩
      have hval'' : Valid (m - 1) e'' :=
        ⟨fun i => hval.1 ⟨i.val, by omega⟩,
         fun i j k hij hjk => hval.2 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ ⟨k.val, by omega⟩ hij hjk⟩
      have hall_lt_y : ∀ i : Fin (m - 1), e'' i < e ⟨m, by omega⟩ := fun i =>
        hval.2 ⟨i.val, by omega⟩ ⟨m - 1, by omega⟩ ⟨m, by omega⟩
          (by show i.val < m - 1; omega) (by show m - 1 < m; omega)
      have hmax_e : maxVal e = e ⟨m - 1, by omega⟩ := by
        apply le_antisymm
        · rw [maxVal_le_iff]
          intro i
          by_cases hi : i.val < m - 1
          · exact le_trans (hall_lt_y ⟨i.val, hi⟩).le hdec
          · by_cases hi2 : i.val = m - 1
            · have : i = ⟨m - 1, by omega⟩ := Fin.ext hi2
              rw [this]
            · have : i = ⟨m, by omega⟩ := Fin.ext (by show i.val = m; omega)
              rw [this]; exact hdec
        · exact le_maxVal e ⟨m - 1, by omega⟩
      simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hmax_e] at hsl
      have hx_le : e ⟨m - 1, by omega⟩ ≤ m - 1 := hval.1 ⟨m - 1, by omega⟩
      have hx_eq : e ⟨m - 1, by omega⟩ = m - (h + 1) := by omega
      simp only [P, mem_biUnion, mem_map, mem_Icc]
      refine ⟨e'', mem_validFinset.mpr hval'', e ⟨m, by omega⟩, ⟨?_, ?_⟩, rfl⟩
      · by_cases hm1 : m = 1
        · subst hm1; simp [slack]
        · have hm2 : 0 < m - 1 := by omega
          have hlt := maxVal_lt_of_forall_lt hm2 e'' (e ⟨m, by omega⟩) hall_lt_y
          have hle := maxVal_le_pred hval''
          have hne0 : m - 1 ≠ 0 := by omega
          simp only [slack, hne0, if_false]
          omega
      · rw [← hx_eq]; exact hdec
    · intro e1 he1 e2 he2 hpair
      simp only [S2, S, validSlack, mem_filter, mem_validFinset] at he1 he2
      have hx_of : ∀ e : Fin (m + 1) → ℕ, Valid (m + 1) e → slack e = h + 1 →
          e ⟨m, by omega⟩ ≤ e ⟨m - 1, by omega⟩ → e ⟨m - 1, by omega⟩ = m - (h + 1) := by
        intro e hval hsl hdec
        have hmax_e : maxVal e = e ⟨m - 1, by omega⟩ := by
          apply le_antisymm
          · rw [maxVal_le_iff]
            intro i
            by_cases hi : i.val < m - 1
            · have hlt := hval.2 ⟨i.val, by omega⟩ ⟨m - 1, by omega⟩ ⟨m, by omega⟩
                (by show i.val < m - 1; omega) (by show m - 1 < m; omega)
              exact le_trans hlt.le hdec
            · by_cases hi2 : i.val = m - 1
              · have : i = ⟨m - 1, by omega⟩ := Fin.ext hi2; rw [this]
              · have : i = ⟨m, by omega⟩ := Fin.ext (by show i.val = m; omega); rw [this]; exact hdec
          · exact le_maxVal e ⟨m - 1, by omega⟩
        simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hmax_e] at hsl
        have hx_le : e ⟨m - 1, by omega⟩ ≤ m - 1 := hval.1 ⟨m - 1, by omega⟩
        omega
      have hx1 := hx_of e1 he1.1.1 he1.1.2 he1.2
      have hx2 := hx_of e2 he2.1.1 he2.1.2 he2.2
      have hpre := (Prod.mk.inj hpair).1
      have hy := (Prod.mk.inj hpair).2
      funext i
      by_cases hi : i.val < m - 1
      · exact congrFun hpre ⟨i.val, hi⟩
      · by_cases hi2 : i.val = m - 1
        · have : i = ⟨m - 1, by omega⟩ := Fin.ext hi2
          rw [this, hx1, hx2]
        · have : i = ⟨m, by omega⟩ := Fin.ext (by show i.val = m; omega)
          rw [this, hy]
    · intro p hp
      simp only [P, mem_biUnion, mem_map, mem_Icc] at hp
      obtain ⟨e'', he'', y, ⟨hy_lo, hy_hi⟩, rfl⟩ := hp
      rw [mem_validFinset] at he''
      have hm_ge : h + 1 ≤ m := hhm'
      let e : Fin (m + 1) → ℕ := fun i =>
        if hi : i.val < m - 1 then e'' ⟨i.val, hi⟩
        else if i.val = m - 1 then m - (h + 1)
        else y
      have hall_lt_y : ∀ i : Fin (m - 1), e'' i < y := by
        intro i
        have hm2 : m - 1 ≠ 0 := by have := i.isLt; omega
        have hle := maxVal_le_pred he''
        simp only [slack, hm2, if_false] at hy_lo
        have := le_maxVal e'' i
        omega
      refine ⟨e, ?_, ?_⟩
      · simp only [S2, S, validSlack, mem_filter, mem_validFinset]
        have he_val : Valid (m + 1) e := by
          refine ⟨?_, ?_⟩
          · intro i
            simp only [e]
            split_ifs with hi1 hi2
            · exact he''.1 ⟨i.val, hi1⟩
            · omega
            · omega
          · intro i j k hij hjk
            have hi : i.val < m - 1 := by omega
            simp only [e, hi, dite_true]
            by_cases hk1 : k.val < m - 1
            · have hj : j.val < m - 1 := by omega
              simp only [hk1, dite_true]
              exact he''.2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk1⟩ hij hjk
            · simp only [hk1, dite_false]
              by_cases hk2 : k.val = m - 1
              · simp only [hk2, if_true]
                exact lt_of_lt_of_le (hall_lt_y ⟨i.val, hi⟩) hy_hi
              · simp only [hk2, if_false]
                exact hall_lt_y ⟨i.val, hi⟩
        have hmax_e : maxVal e = m - (h + 1) := by
          apply le_antisymm
          · rw [maxVal_le_iff]
            intro i
            simp only [e]
            split_ifs with hi1 hi2
            · exact le_trans (hall_lt_y ⟨i.val, hi1⟩).le hy_hi
            · exact le_rfl
            · exact hy_hi
          · have := le_maxVal e ⟨m - 1, by omega⟩
            simpa [e] using this
        have hsl_e : slack e = h + 1 := by
          simp only [slack, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hmax_e]
          omega
        have hdec_e : e ⟨m, by omega⟩ ≤ e ⟨m - 1, by omega⟩ := by
          have h1 : ¬ m < m - 1 := by omega
          have h2 : m ≠ m - 1 := by omega
          have h3 : ¬ m - 1 < m - 1 := Nat.lt_irrefl _
          simp only [e, h1, h2, h3, dite_false, if_false, if_true]
          exact hy_hi
        exact ⟨⟨he_val, hsl_e⟩, hdec_e⟩
      · apply Prod.ext
        · funext i
          change (if hi : i.val < m - 1 then e'' ⟨i.val, hi⟩
            else if i.val = m - 1 then m - (h + 1) else y) = e'' i
          simp [i.isLt]
        · change (if hi : m < m - 1 then e'' ⟨m, hi⟩
            else if m = m - 1 then m - (h + 1) else y) = y
          have h1 : ¬ m < m - 1 := by omega
          have h2 : m ≠ m - 1 := by omega
          simp [h1, h2]

lemma coeff_mul_eq (f g : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (f * g) =
      ∑ i ∈ range (n + 1), PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) n

def aAlg : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let lhs := 2 * aAlg (n + 1) +
      ∑ i ∈ (range (n + 2)).attach,
        have _ : i.1 < n + 2 := mem_range.mp i.2
        have _ : n + 1 - i.1 < n + 2 := by omega
        aAlg i.1 * aAlg (n + 1 - i.1)
    let a2 := ∑ i ∈ (Icc 1 (n + 1)).attach,
      have hi := mem_Icc.mp i.2
      have _ : i.1 < n + 2 := by omega
      have _ : n + 2 - i.1 < n + 2 := by omega
      aAlg i.1 * aAlg (n + 2 - i.1)
    let a3 := ∑ i ∈ (Icc 1 (n + 1)).attach,
      have hi := mem_Icc.mp i.2
      have _ : i.1 < n + 2 := by omega
      ∑ j ∈ (Icc 1 (n + 1 - i.1)).attach,
        have hj := mem_Icc.mp j.2
        have _ : j.1 < n + 2 := by omega
        have _ : n + 2 - i.1 - j.1 < n + 2 := by omega
        aAlg i.1 * aAlg j.1 * aAlg (n + 2 - i.1 - j.1)
    lhs - a2 + a3

lemma aAlg_zero : aAlg 0 = 0 := by rw [aAlg]
lemma aAlg_one : aAlg 1 = 1 := by rw [aAlg]
lemma aAlg_succ_succ (n : ℕ) :
    aAlg (n + 2) =
      (2 * aAlg (n + 1) + ∑ i ∈ range (n + 2), aAlg i * aAlg (n + 1 - i)) -
      (∑ i ∈ Icc 1 (n + 1), aAlg i * aAlg (n + 2 - i)) +
      (∑ i ∈ Icc 1 (n + 1), ∑ j ∈ Icc 1 (n + 1 - i),
        aAlg i * aAlg j * aAlg (n + 2 - i - j)) := by
  rw [aAlg]
  have h1 : (∑ i ∈ (range (n + 2)).attach, aAlg i.1 * aAlg (n + 1 - i.1)) =
      ∑ i ∈ range (n + 2), aAlg i * aAlg (n + 1 - i) :=
    sum_attach (range (n + 2)) (fun i => aAlg i * aAlg (n + 1 - i))
  have h2 : (∑ i ∈ (Icc 1 (n + 1)).attach, aAlg i.1 * aAlg (n + 2 - i.1)) =
      ∑ i ∈ Icc 1 (n + 1), aAlg i * aAlg (n + 2 - i) :=
    sum_attach (Icc 1 (n + 1)) (fun i => aAlg i * aAlg (n + 2 - i))
  have h3 : (∑ i ∈ (Icc 1 (n + 1)).attach,
        ∑ j ∈ (Icc 1 (n + 1 - i.1)).attach, aAlg i.1 * aAlg j.1 * aAlg (n + 2 - i.1 - j.1)) =
      ∑ i ∈ Icc 1 (n + 1), ∑ j ∈ Icc 1 (n + 1 - i), aAlg i * aAlg j * aAlg (n + 2 - i - j) := by
    trans (∑ i ∈ (Icc 1 (n + 1)).attach,
        ∑ j ∈ Icc 1 (n + 1 - i.1), aAlg i.1 * aAlg j * aAlg (n + 2 - i.1 - j))
    · refine sum_congr rfl fun i _ => ?_
      exact sum_attach (Icc 1 (n + 1 - i.1)) (fun j => aAlg i.1 * aAlg j * aAlg (n + 2 - i.1 - j))
    · exact sum_attach (Icc 1 (n + 1))
        (fun i => ∑ j ∈ Icc 1 (n + 1 - i), aAlg i * aAlg j * aAlg (n + 2 - i - j))
  exact congrArg₂ (· + ·) (congrArg₂ (· - ·) (congrArg (2 * aAlg (n + 1) + ·) h1) h2) h3

noncomputable def Aalg : PowerSeries ℚ := PowerSeries.mk aAlg

lemma coeff_Aalg_zero : PowerSeries.coeff 0 Aalg = 0 := by simp [Aalg, aAlg_zero]
lemma coeff_Aalg_one : PowerSeries.coeff 1 Aalg = 1 := by simp [Aalg, aAlg_one]

lemma Aalg_eq : (1 + Aalg) ^ 2 * PowerSeries.X = Aalg * (1 + Aalg - Aalg ^ 2) := by
  ext n
  cases n with
  | zero =>
    simp [Aalg, aAlg_zero]
  | succ m =>
    cases m with
    | zero =>
      rw [mul_comm, PowerSeries.coeff_succ_X_mul, sq, coeff_mul_eq, coeff_mul_eq]
      simp [sum_range_succ, Aalg, aAlg_zero, aAlg_one, sq, coeff_mul_eq]
    | succ k =>
      have hLHS : PowerSeries.coeff (k + 2) ((1 + Aalg) ^ 2 * PowerSeries.X) =
          2 * aAlg (k + 1) + ∑ i ∈ range (k + 2), aAlg i * aAlg (k + 1 - i) := by
        rw [mul_comm, PowerSeries.coeff_succ_X_mul]
        have hexp : (1 + Aalg) ^ 2 = 1 + PowerSeries.C 2 * Aalg + Aalg * Aalg := by
          have h2 : PowerSeries.C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat _ 2
          rw [h2]; ring
        rw [hexp, map_add, map_add, PowerSeries.coeff_one, if_neg (by omega : k + 1 ≠ 0),
          zero_add, PowerSeries.coeff_C_mul, coeff_mul_eq]
        simp [Aalg]
      have hA2 : PowerSeries.coeff (k + 2) (Aalg * Aalg) =
          ∑ i ∈ Icc 1 (k + 1), aAlg i * aAlg (k + 2 - i) := by
        rw [coeff_mul_eq]
        simp only [Aalg, coeff_mk]
        rw [sum_range_succ, sum_range_succ']
        simp only [aAlg_zero, zero_mul, mul_zero, Nat.sub_self, add_zero]
        refine sum_nbij (fun i => i + 1) ?_ ?_ ?_ ?_
        · intro i hi; simp only [mem_range, mem_Icc] at hi ⊢; omega
        · intro a _ b _ h; dsimp only at h; omega
        · intro i hi
          simp only [mem_coe, mem_Icc] at hi
          exact ⟨i - 1, by simp only [mem_coe, mem_range]; omega, by dsimp only; omega⟩
        · intro _ _; rfl
      have hA3 : PowerSeries.coeff (k + 2) (Aalg * Aalg * Aalg) =
          ∑ i ∈ Icc 1 (k + 1), ∑ j ∈ Icc 1 (k + 1 - i),
            aAlg i * aAlg j * aAlg (k + 2 - i - j) := by
        rw [coeff_mul_eq]
        have hstep : ∑ s ∈ range (k + 3),
            PowerSeries.coeff s (Aalg * Aalg) * PowerSeries.coeff (k + 2 - s) Aalg =
            ∑ s ∈ Icc 2 (k + 1),
              (∑ i ∈ Icc 1 (s - 1), aAlg i * aAlg (s - i)) * aAlg (k + 2 - s) := by
          have hzero : ∀ s ∈ range (k + 3), s ∉ Icc 2 (k + 1) →
              PowerSeries.coeff s (Aalg * Aalg) * PowerSeries.coeff (k + 2 - s) Aalg = 0 := by
            intro s hs hnot
            simp only [mem_range] at hs
            simp only [mem_Icc, not_and_or, not_le] at hnot
            rcases hnot with hlt | hgt
            · have hs01 : s = 0 ∨ s = 1 := by omega
              rcases hs01 with rfl | rfl
              · simp [coeff_mul_eq, Aalg, aAlg_zero]
              · simp [coeff_mul_eq, sum_range_succ, Aalg, aAlg_zero]
            · have hsk : s = k + 2 := by omega
              subst hsk
              simp [Aalg, aAlg_zero]
          rw [← sum_subset (show Icc 2 (k + 1) ⊆ range (k + 3) by
            intro s hs; simp only [mem_Icc, mem_range] at hs ⊢; omega) hzero]
          refine sum_congr rfl fun s hs => ?_
          simp only [mem_Icc] at hs
          congr 1
          · rw [coeff_mul_eq]
            simp only [Aalg, coeff_mk]
            have hsub : Icc 1 (s - 1) ⊆ range (s + 1) := by
              intro i hi; simp only [mem_Icc, mem_range] at hi ⊢; omega
            symm
            refine sum_subset hsub ?_
            intro i hi hnot
            simp only [mem_range] at hi
            simp only [mem_Icc, not_and_or, not_le] at hnot
            rcases hnot with h0 | hs'
            · have : i = 0 := by omega
              subst this; simp [aAlg_zero]
            · have : i = s := by omega
              subst this; simp [aAlg_zero]
          · simp [Aalg]
        rw [hstep]
        have hflat1 : ∑ s ∈ Icc 2 (k + 1),
              (∑ i ∈ Icc 1 (s - 1), aAlg i * aAlg (s - i)) * aAlg (k + 2 - s) =
            ∑ p ∈ (Icc 2 (k + 1)).sigma (fun s => Icc 1 (s - 1)),
              aAlg p.2 * aAlg (p.1 - p.2) * aAlg (k + 2 - p.1) := by
          rw [sum_sigma]
          refine sum_congr rfl fun s _ => ?_
          rw [sum_mul]
        have hflat2 : ∑ i ∈ Icc 1 (k + 1), ∑ j ∈ Icc 1 (k + 1 - i),
              aAlg i * aAlg j * aAlg (k + 2 - i - j) =
            ∑ p ∈ (Icc 1 (k + 1)).sigma (fun i => Icc 1 (k + 1 - i)),
              aAlg p.1 * aAlg p.2 * aAlg (k + 2 - p.1 - p.2) := by
          rw [sum_sigma]
        rw [hflat1, hflat2]
        refine sum_nbij (fun p => ⟨p.2, p.1 - p.2⟩) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [mem_sigma, mem_Icc] at hp ⊢
          omega
        · intro p1 hp1 p2 hp2 heq
          simp only [mem_coe, mem_sigma, mem_Icc] at hp1 hp2
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
          obtain ⟨h2, h1⟩ := heq
          exact Sigma.ext (by omega) (heq_of_eq h2)
        · intro q hq
          simp only [mem_coe, mem_sigma, mem_Icc] at hq
          refine ⟨⟨q.1 + q.2, q.1⟩, ?_, ?_⟩
          · simp only [mem_coe, mem_sigma, mem_Icc]; omega
          · exact Sigma.ext rfl (heq_of_eq (by dsimp only; omega))
        · intro p hp
          simp only [mem_sigma, mem_Icc] at hp
          have h1 : k + 2 - p.2 - (p.1 - p.2) = k + 2 - p.1 := by omega
          rw [h1]
      have hRHS : PowerSeries.coeff (k + 2) (Aalg * (1 + Aalg - Aalg ^ 2)) =
          aAlg (k + 2) + PowerSeries.coeff (k + 2) (Aalg * Aalg) -
            PowerSeries.coeff (k + 2) (Aalg * Aalg * Aalg) := by
        have hring : Aalg * (1 + Aalg - Aalg ^ 2) = Aalg + Aalg * Aalg - Aalg * Aalg * Aalg := by
          ring
        rw [hring, map_sub, map_add]
        simp [Aalg]
      rw [hLHS, hRHS, hA2, hA3, aAlg_succ_succ]
      ring

lemma isUnit_one_add_Aalg : IsUnit (1 + Aalg) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [Aalg, aAlg_zero]

noncomputable def invOneAddA : PowerSeries ℚ := (isUnit_one_add_Aalg.unit⁻¹ : (PowerSeries ℚ)ˣ)

lemma one_add_Aalg_mul_inv : (1 + Aalg) * invOneAddA = 1 :=
  isUnit_one_add_Aalg.unit.mul_inv

noncomputable def B : PowerSeries ℚ := Aalg ^ 2 * invOneAddA

lemma isUnit_one_sub_B : IsUnit (1 - B) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [B, Aalg, aAlg_zero]

noncomputable def invOneSubB : PowerSeries ℚ := (isUnit_one_sub_B.unit⁻¹ : (PowerSeries ℚ)ˣ)

lemma one_sub_B_mul_inv : (1 - B) * invOneSubB = 1 :=
  isUnit_one_sub_B.unit.mul_inv

lemma X_mul_one_add_A_mul_invOneSubB : PowerSeries.X * (1 + Aalg) * invOneSubB = Aalg := by
  have h1 : (1 - B) * (1 + Aalg) = 1 + Aalg - Aalg ^ 2 := by
    calc (1 - B) * (1 + Aalg)
        = (1 + Aalg) - Aalg ^ 2 * ((1 + Aalg) * invOneAddA) := by simp only [B]; ring
      _ = 1 + Aalg - Aalg ^ 2 := by rw [one_add_Aalg_mul_inv, mul_one]
  have h2 : (1 - B) * (PowerSeries.X * (1 + Aalg) * invOneSubB) = (1 - B) * Aalg := by
    have hL : (1 - B) * (PowerSeries.X * (1 + Aalg) * invOneSubB) = PowerSeries.X * (1 + Aalg) := by
      calc (1 - B) * (PowerSeries.X * (1 + Aalg) * invOneSubB)
          = PowerSeries.X * (1 + Aalg) * ((1 - B) * invOneSubB) := by ring
        _ = PowerSeries.X * (1 + Aalg) := by rw [one_sub_B_mul_inv, mul_one]
    have hR : (1 - B) * Aalg = PowerSeries.X * (1 + Aalg) := by
      have hmul : (1 + Aalg) * ((1 - B) * Aalg) = (1 + Aalg) * (PowerSeries.X * (1 + Aalg)) := by
        calc (1 + Aalg) * ((1 - B) * Aalg)
            = Aalg * ((1 - B) * (1 + Aalg)) := by ring
          _ = Aalg * (1 + Aalg - Aalg ^ 2) := by rw [h1]
          _ = (1 + Aalg) ^ 2 * PowerSeries.X := Aalg_eq.symm
          _ = (1 + Aalg) * (PowerSeries.X * (1 + Aalg)) := by ring
      have hne : (1 + Aalg) ≠ 0 := isUnit_one_add_Aalg.ne_zero
      exact mul_left_cancel₀ hne hmul
    rw [hL, hR]
  exact mul_left_cancel₀ isUnit_one_sub_B.ne_zero h2

lemma X_sq_mul_one_add_A_mul_invOneSubB_sq :
    PowerSeries.X ^ 2 * (1 + Aalg) * invOneSubB ^ 2 = B := by
  have hmul : (1 + Aalg) * (PowerSeries.X ^ 2 * (1 + Aalg) * invOneSubB ^ 2) = (1 + Aalg) * B := by
    calc (1 + Aalg) * (PowerSeries.X ^ 2 * (1 + Aalg) * invOneSubB ^ 2)
        = (PowerSeries.X * (1 + Aalg) * invOneSubB) ^ 2 := by ring
      _ = Aalg ^ 2 := by rw [X_mul_one_add_A_mul_invOneSubB]
      _ = Aalg ^ 2 * ((1 + Aalg) * invOneAddA) := by rw [one_add_Aalg_mul_inv, mul_one]
      _ = (1 + Aalg) * B := by simp only [B]; ring
  exact mul_left_cancel₀ isUnit_one_add_Aalg.ne_zero hmul

noncomputable def Fser (h : ℕ) : PowerSeries ℚ := (1 + Aalg) * B ^ h

lemma coeff_B_zero : PowerSeries.coeff 0 B = 0 := by
  simp [B, sq, coeff_mul_eq, Aalg, aAlg_zero]

lemma coeff_B_one : PowerSeries.coeff 1 B = 0 := by
  have hA2_0 : PowerSeries.coeff 0 (Aalg ^ 2) = 0 := by
    simp [sq, coeff_mul_eq, Aalg, aAlg_zero]
  have hA2_1 : PowerSeries.coeff 1 (Aalg ^ 2) = 0 := by
    simp [sq, coeff_mul_eq, sum_range_succ, Aalg, aAlg_zero]
  simp only [B, coeff_mul_eq, sum_range_succ, range_zero, sum_empty, zero_add]
  simp [hA2_0, hA2_1]

lemma coeff_B_pow_eq_zero {h m : ℕ} (hm : m < 2 * h) : PowerSeries.coeff m (B ^ h) = 0 := by
  induction h generalizing m with
  | zero => omega
  | succ h ih =>
    rw [pow_succ, coeff_mul_eq]
    refine Finset.sum_eq_zero fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    by_cases hlt : i < 2 * h
    · rw [ih hlt, zero_mul]
    · have hrem : m - i = 0 ∨ m - i = 1 := by omega
      rcases hrem with h0 | h1
      · rw [h0, coeff_B_zero, mul_zero]
      · rw [h1, coeff_B_one, mul_zero]

lemma coeff_mul_B_pow_eq_zero (P : PowerSeries ℚ) {h m : ℕ} (hm : m < 2 * h) :
    PowerSeries.coeff m (P * B ^ h) = 0 := by
  rw [coeff_mul_eq]
  refine Finset.sum_eq_zero fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [coeff_B_pow_eq_zero (by omega : m - i < 2 * h), mul_zero]

lemma geom_sum_powerSeries (N : ℕ) :
    (∑ r ∈ range (N + 1), B ^ r) = invOneSubB - B ^ (N + 1) * invOneSubB := by
  have h1 : (1 - B) * (∑ r ∈ range (N + 1), B ^ r) = 1 - B ^ (N + 1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, mul_add, ih, pow_succ']
      ring
  have h2 : (1 - B) * (∑ r ∈ range (N + 1), B ^ r) =
      (1 - B) * (invOneSubB - B ^ (N + 1) * invOneSubB) := by
    rw [h1, mul_sub]
    have hL : (1 - B) * invOneSubB = 1 := one_sub_B_mul_inv
    have hR : (1 - B) * (B ^ (N + 1) * invOneSubB) = B ^ (N + 1) := by
      calc (1 - B) * (B ^ (N + 1) * invOneSubB)
          = B ^ (N + 1) * ((1 - B) * invOneSubB) := by ring
        _ = B ^ (N + 1) := by rw [one_sub_B_mul_inv, mul_one]
    rw [hL, hR]
  exact mul_left_cancel₀ isUnit_one_sub_B.ne_zero h2

lemma deriv_geom_sum_powerSeries (N : ℕ) :
    (∑ r ∈ range (N + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r) =
      invOneSubB ^ 2 - (((N + 2 : ℕ) : PowerSeries ℚ) - ((N + 1 : ℕ) : PowerSeries ℚ) * B) *
        B ^ (N + 1) * invOneSubB ^ 2 := by
  have hstep1 : (1 - B) * (∑ r ∈ range (N + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r) =
      (∑ r ∈ range (N + 1), B ^ r) - ((N + 1 : ℕ) : PowerSeries ℚ) * B ^ (N + 1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ (fun r => ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r) (N + 1), mul_add, ih,
        sum_range_succ (fun r => B ^ r) (N + 1)]
      push_cast
      rw [pow_succ (a := B) (n := N + 1)]
      ring
  have hstep2 : (1 - B) ^ 2 * (∑ r ∈ range (N + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r) =
      1 - (((N + 2 : ℕ) : PowerSeries ℚ) - ((N + 1 : ℕ) : PowerSeries ℚ) * B) * B ^ (N + 1) := by
    rw [sq, mul_assoc, hstep1, mul_sub]
    have hg : (1 - B) * (∑ r ∈ range (N + 1), B ^ r) = 1 - B ^ (N + 1) := by
      rw [geom_sum_powerSeries, mul_sub, one_sub_B_mul_inv]
      have haux : (1 - B) * (B ^ (N + 1) * invOneSubB) = B ^ (N + 1) := by
        calc (1 - B) * (B ^ (N + 1) * invOneSubB)
            = B ^ (N + 1) * ((1 - B) * invOneSubB) := by ring
          _ = B ^ (N + 1) := by rw [one_sub_B_mul_inv, mul_one]
      rw [haux]
    rw [hg]
    push_cast
    ring
  have hmul : (1 - B) ^ 2 * (∑ r ∈ range (N + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r) =
      (1 - B) ^ 2 * (invOneSubB ^ 2 -
        (((N + 2 : ℕ) : PowerSeries ℚ) - ((N + 1 : ℕ) : PowerSeries ℚ) * B) *
          B ^ (N + 1) * invOneSubB ^ 2) := by
    rw [hstep2, mul_sub]
    have hsq : (1 - B) ^ 2 * invOneSubB ^ 2 = 1 := by
      rw [← mul_pow, one_sub_B_mul_inv, one_pow]
    have h2 : (1 - B) ^ 2 * ((((N + 2 : ℕ) : PowerSeries ℚ) - ((N + 1 : ℕ) : PowerSeries ℚ) * B) *
          B ^ (N + 1) * invOneSubB ^ 2) =
        (((N + 2 : ℕ) : PowerSeries ℚ) - ((N + 1 : ℕ) : PowerSeries ℚ) * B) * B ^ (N + 1) := by
      calc (1 - B) ^ 2 * ((((N + 2 : ℕ) : PowerSeries ℚ) - ((N + 1 : ℕ) : PowerSeries ℚ) * B) *
              B ^ (N + 1) * invOneSubB ^ 2)
          = ((((N + 2 : ℕ) : PowerSeries ℚ) - ((N + 1 : ℕ) : PowerSeries ℚ) * B) *
              B ^ (N + 1)) * ((1 - B) ^ 2 * invOneSubB ^ 2) := by ring
        _ = (((N + 2 : ℕ) : PowerSeries ℚ) - ((N + 1 : ℕ) : PowerSeries ℚ) * B) * B ^ (N + 1) := by
              rw [hsq, mul_one]
    rw [hsq, h2]
  exact mul_left_cancel₀ (pow_ne_zero 2 isUnit_one_sub_B.ne_zero) hmul

lemma coeff_Fser_zero (h : ℕ) : PowerSeries.coeff 0 (Fser h) = if h = 0 then 1 else 0 := by
  cases h with
  | zero => simp [Fser, Aalg, aAlg_zero]
  | succ h =>
    simp only [Nat.succ_ne_zero, if_false, Fser]
    exact coeff_mul_B_pow_eq_zero (1 + Aalg) (by omega)

lemma coeff_Fser_succ_zero (m : ℕ) :
    PowerSeries.coeff (m + 1) (Fser 0) =
      ∑ h' ∈ range (m + 1), PowerSeries.coeff m (Fser h') := by
  have h1 : PowerSeries.coeff (m + 1) (Fser 0) = PowerSeries.coeff (m + 1) Aalg := by
    simp [Fser]
  rw [h1, ← X_mul_one_add_A_mul_invOneSubB]
  have hsum : ∑ h' ∈ range (m + 1), PowerSeries.coeff m (Fser h') =
      PowerSeries.coeff (m + 1) (PowerSeries.X * (1 + Aalg) * (∑ r ∈ range (m + 1), B ^ r)) := by
    rw [mul_assoc, PowerSeries.coeff_succ_X_mul, mul_sum, map_sum]
    refine sum_congr rfl fun r _ => by rfl
  rw [hsum, geom_sum_powerSeries m, mul_sub, map_sub]
  have hrem : PowerSeries.coeff (m + 1)
      (PowerSeries.X * (1 + Aalg) * (B ^ (m + 1) * invOneSubB)) = 0 := by
    have hrearr : PowerSeries.X * (1 + Aalg) * (B ^ (m + 1) * invOneSubB) =
        (PowerSeries.X * (1 + Aalg) * invOneSubB) * B ^ (m + 1) := by ring
    rw [hrearr]
    exact coeff_mul_B_pow_eq_zero _ (by omega)
  rw [hrem, sub_zero]

lemma coeff_Fser_succ_succ (m h : ℕ) (hm : 1 ≤ m) :
    PowerSeries.coeff (m + 1) (Fser (h + 1)) =
      (∑ h' ∈ Icc (h + 1) m, PowerSeries.coeff m (Fser h')) +
      (∑ h'' ∈ Icc h (m - 1), ((h'' + 1 - h : ℕ) : ℚ) * PowerSeries.coeff (m - 1) (Fser h'')) := by
  have hF_split : Fser (h + 1) = Aalg * B ^ (h + 1) + B ^ (h + 1) := by
    simp only [Fser]; ring
  rw [hF_split, map_add]
  congr 1
  · have hsum1 : ∑ h' ∈ Icc (h + 1) m, PowerSeries.coeff m (Fser h') =
        ∑ r ∈ range (m + 1), PowerSeries.coeff m (Fser (h + 1 + r)) := by
      have hsub : Icc (h + 1) m ⊆ (range (m + 1)).image (fun r => h + 1 + r) := by
        intro h' hh'
        simp only [mem_Icc, mem_image, mem_range] at hh' ⊢
        exact ⟨h' - (h + 1), by omega, by omega⟩
      have hzero : ∀ h' ∈ (range (m + 1)).image (fun r => h + 1 + r), h' ∉ Icc (h + 1) m →
          PowerSeries.coeff m (Fser h') = 0 := by
        intro h' hh' hnot
        simp only [mem_image, mem_range] at hh'
        obtain ⟨r, _, rfl⟩ := hh'
        simp only [mem_Icc, not_and_or, not_le] at hnot
        have hgt : m < h + 1 + r := by omega
        unfold Fser
        exact coeff_mul_B_pow_eq_zero (1 + Aalg) (by omega)
      rw [sum_subset hsub hzero, sum_image (fun a _ b _ hab => by omega)]
    rw [hsum1]
    have hpack : ∑ r ∈ range (m + 1), PowerSeries.coeff m (Fser (h + 1 + r)) =
        PowerSeries.coeff (m + 1) (PowerSeries.X * (1 + Aalg) * B ^ (h + 1) *
          (∑ r ∈ range (m + 1), B ^ r)) := by
      rw [mul_assoc, mul_assoc, PowerSeries.coeff_succ_X_mul]
      have : (1 + Aalg) * (B ^ (h + 1) * ∑ r ∈ range (m + 1), B ^ r) =
          ∑ r ∈ range (m + 1), Fser (h + 1 + r) := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun r _ => by simp only [Fser, pow_add]
      rw [this, map_sum]
    rw [hpack, geom_sum_powerSeries m, mul_sub, map_sub]
    have hmain : PowerSeries.X * (1 + Aalg) * B ^ (h + 1) * invOneSubB = Aalg * B ^ (h + 1) := by
      calc PowerSeries.X * (1 + Aalg) * B ^ (h + 1) * invOneSubB
          = (PowerSeries.X * (1 + Aalg) * invOneSubB) * B ^ (h + 1) := by ring
        _ = Aalg * B ^ (h + 1) := by rw [X_mul_one_add_A_mul_invOneSubB]
    have hrem : PowerSeries.coeff (m + 1)
        (PowerSeries.X * (1 + Aalg) * B ^ (h + 1) * (B ^ (m + 1) * invOneSubB)) = 0 := by
      have : PowerSeries.X * (1 + Aalg) * B ^ (h + 1) * (B ^ (m + 1) * invOneSubB) =
          (PowerSeries.X * (1 + Aalg) * B ^ (h + 1) * invOneSubB) * B ^ (m + 1) := by ring
      rw [this]
      exact coeff_mul_B_pow_eq_zero _ (by omega)
    rw [hmain, hrem, sub_zero]
  · have hsum2 : ∑ h'' ∈ Icc h (m - 1), ((h'' + 1 - h : ℕ) : ℚ) * PowerSeries.coeff (m - 1) (Fser h'') =
        ∑ r ∈ range (m + 1), ((r + 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) (Fser (h + r)) := by
      have hsub : Icc h (m - 1) ⊆ (range (m + 1)).image (fun r => h + r) := by
        intro h'' hh''
        simp only [mem_Icc, mem_image, mem_range] at hh'' ⊢
        exact ⟨h'' - h, by omega, by omega⟩
      have hzero : ∀ h'' ∈ (range (m + 1)).image (fun r => h + r), h'' ∉ Icc h (m - 1) →
          ((h'' + 1 - h : ℕ) : ℚ) * PowerSeries.coeff (m - 1) (Fser h'') = 0 := by
        intro h'' hh'' hnot
        simp only [mem_image, mem_range] at hh''
        obtain ⟨r, _, rfl⟩ := hh''
        simp only [mem_Icc, not_and_or, not_le] at hnot
        have hgt : m - 1 < h + r := by omega
        unfold Fser
        rw [coeff_mul_B_pow_eq_zero (1 + Aalg) (by omega), mul_zero]
      rw [sum_subset hsub hzero, sum_image (fun a _ b _ hab => by omega)]
      refine sum_congr rfl fun r _ => ?_
      have : h + r + 1 - h = r + 1 := by omega
      rw [this]
    rw [hsum2]
    have hpack : ∑ r ∈ range (m + 1), ((r + 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) (Fser (h + r)) =
        PowerSeries.coeff (m + 1) (PowerSeries.X ^ 2 * (1 + Aalg) * B ^ h *
          (∑ r ∈ range (m + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r)) := by
      have hm2 : m + 1 = ((m - 1) + 1) + 1 := by omega
      have hX2 : PowerSeries.X ^ 2 * (1 + Aalg) * B ^ h *
          (∑ r ∈ range (m + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r) =
          PowerSeries.X * (PowerSeries.X * ((1 + Aalg) * B ^ h *
            (∑ r ∈ range (m + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r))) := by ring
      rw [hX2]
      have hcoeff_shift : PowerSeries.coeff (m + 1)
          (PowerSeries.X * (PowerSeries.X * ((1 + Aalg) * B ^ h *
            (∑ r ∈ range (m + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r)))) =
          PowerSeries.coeff (m - 1) ((1 + Aalg) * B ^ h *
            (∑ r ∈ range (m + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r)) := by
        conv_lhs => rw [hm2]
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, ← hm2]
      rw [hcoeff_shift]
      have hsum_eq : (1 + Aalg) * B ^ h *
            (∑ r ∈ range (m + 1), ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r) =
          ∑ r ∈ range (m + 1), PowerSeries.C ((r + 1 : ℕ) : ℚ) * Fser (h + r) := by
        rw [mul_sum]
        refine sum_congr rfl fun r _ => ?_
        have hC : PowerSeries.C ((r + 1 : ℕ) : ℚ) = ((r + 1 : ℕ) : PowerSeries ℚ) := map_natCast _ _
        rw [hC]
        simp only [Fser, pow_add]
        ring
      rw [hsum_eq, map_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [PowerSeries.coeff_C_mul]
    rw [hpack, deriv_geom_sum_powerSeries m, mul_sub, map_sub]
    have hmain : PowerSeries.X ^ 2 * (1 + Aalg) * B ^ h * invOneSubB ^ 2 = B ^ (h + 1) := by
      calc PowerSeries.X ^ 2 * (1 + Aalg) * B ^ h * invOneSubB ^ 2
          = (PowerSeries.X ^ 2 * (1 + Aalg) * invOneSubB ^ 2) * B ^ h := by ring
        _ = B * B ^ h := by rw [X_sq_mul_one_add_A_mul_invOneSubB_sq]
        _ = B ^ (h + 1) := by rw [pow_succ']
    have hrem : PowerSeries.coeff (m + 1)
        (PowerSeries.X ^ 2 * (1 + Aalg) * B ^ h *
          ((((m + 2 : ℕ) : PowerSeries ℚ) - ((m + 1 : ℕ) : PowerSeries ℚ) * B) *
            B ^ (m + 1) * invOneSubB ^ 2)) = 0 := by
      have : PowerSeries.X ^ 2 * (1 + Aalg) * B ^ h *
          ((((m + 2 : ℕ) : PowerSeries ℚ) - ((m + 1 : ℕ) : PowerSeries ℚ) * B) *
            B ^ (m + 1) * invOneSubB ^ 2) =
          (PowerSeries.X ^ 2 * (1 + Aalg) * B ^ h *
            (((m + 2 : ℕ) : PowerSeries ℚ) - ((m + 1 : ℕ) : PowerSeries ℚ) * B) * invOneSubB ^ 2) *
            B ^ (m + 1) := by ring
      rw [this]
      exact coeff_mul_B_pow_eq_zero _ (by omega)
    rw [hmain, hrem, sub_zero]

lemma f_eq_coeff_Fser : ∀ m h : ℕ, (f m h : ℚ) = PowerSeries.coeff m (Fser h) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro h
    cases m with
    | zero =>
      cases h with
      | zero => simp [f_zero_zero, coeff_Fser_zero]
      | succ h => simp [f_zero_succ, coeff_Fser_zero]
    | succ m' =>
      cases h with
      | zero =>
        rw [f_succ_zero, coeff_Fser_succ_zero]
        push_cast
        refine sum_congr rfl fun h' _ => ih m' (Nat.lt_succ_self m') h'
      | succ h' =>
        cases m' with
        | zero =>
          rw [f_one_succ]
          symm
          unfold Fser
          exact coeff_mul_B_pow_eq_zero (1 + Aalg) (by omega)
        | succ m'' =>
          have hm1 : 1 ≤ m'' + 1 := Nat.succ_pos m''
          rw [f_succ_succ (m'' + 1) h' hm1, coeff_Fser_succ_succ (m'' + 1) h' hm1]
          push_cast
          congr 1
          · refine sum_congr rfl fun k _ => ih (m'' + 1) (Nat.lt_succ_self _) k
          · refine sum_congr rfl fun k _ => ?_
            rw [ih m'' (by omega) k]

lemma A_eq_Aalg : A = Aalg := by
  ext n
  cases n with
  | zero => simp [A, Aalg, aAlg_zero]
  | succ m =>
    simp only [A, coeff_mk, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    have h1 : (invSeqCount m : ℚ) = (f (m + 1) 0 : ℚ) := by
      rw [invSeqCount_eq_sum_f, f_succ_zero]
    rw [h1, f_eq_coeff_Fser (m + 1) 0]
    simp [Fser]

lemma solve_main : (1 + A) ^ 2 * PowerSeries.X = A * (1 + A - A ^ 2) := by
  rw [A_eq_Aalg]
  exact Aalg_eq

end Antigravity2_oeis_a049125

theorem OMA.solution : type_of% @OMA.S_oeis_a049125.main :=
  Antigravity2_oeis_a049125.solve_main
