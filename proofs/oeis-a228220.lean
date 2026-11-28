import OMAStatements.S_oeis_a228220
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval

-- Problem: OEIS A228220 (signed second differences of length-5 words over 0..n).
-- Upstream: statements/oeis-a228220.lean (declaration OMA.S_oeis_a228220.main)
-- Credit: @advancedsuperintelligence

namespace A228220Proof

open Finset PowerSeries OMA.S_oeis_a228220

private abbrev State := Bool × Bool × Fin 5

private def IsCanon (n : ℕ) (w : Word n) : Prop :=
  (∃ i : Fin 5, (w i).val = 0) ∧
  (∃ i j : Fin 5, i.val < j.val ∧ (n - (w i).val + i.val) + (w j).val < j.val)

private instance decIsCanon (n : ℕ) : DecidablePred (IsCanon n) := fun w => by
  unfold IsCanon; infer_instance

private lemma differences_eq_iff {n : ℕ} (w w' : Word n) :
    differences w = differences w' ↔
      ∃ c v : ℤ, ∀ i : Fin 5, ((w' i).val : ℤ) = ((w i).val : ℤ) + c + (i.val : ℤ) * v := by
  constructor
  · intro h
    have h0 : ((w 0).val : ℤ) - 2 * (w 1).val + (w 2).val =
        ((w' 0).val : ℤ) - 2 * (w' 1).val + (w' 2).val := by
      simpa [differences] using congr_fun h 0
    have h1 : ((w 1).val : ℤ) - 2 * (w 2).val + (w 3).val =
        ((w' 1).val : ℤ) - 2 * (w' 2).val + (w' 3).val := by
      simpa [differences] using congr_fun h 1
    have h2 : ((w 2).val : ℤ) - 2 * (w 3).val + (w 4).val =
        ((w' 2).val : ℤ) - 2 * (w' 3).val + (w' 4).val := by
      simpa [differences] using congr_fun h 2
    refine ⟨((w' 0).val : ℤ) - ((w 0).val : ℤ),
            (((w' 1).val : ℤ) - ((w 1).val : ℤ)) - (((w' 0).val : ℤ) - ((w 0).val : ℤ)), ?_⟩
    intro i
    fin_cases i <;> dsimp <;> linarith
  · rintro ⟨c, v, h⟩
    funext i
    simp only [differences]
    have hi0 := h ⟨i.val, by omega⟩
    have hi1 := h ⟨i.val + 1, by omega⟩
    have hi2 := h ⟨i.val + 2, by omega⟩
    dsimp at hi0 hi1 hi2
    linarith

private lemma canon_inj {n : ℕ} {w w' : Word n} (hw : IsCanon n w) (hw' : IsCanon n w')
    (heq : differences w = differences w') : w = w' := by
  obtain ⟨c, v, hcv⟩ := (differences_eq_iff w w').mp heq
  have hv_nonneg : 0 ≤ v := by
    by_contra hlt
    have hv1 : v ≤ -1 := by omega
    obtain ⟨i, j, hij, hbound⟩ := hw.2
    have hi := hcv i
    have hj := hcv j
    have hwi : (w i).val ≤ n := Nat.lt_succ_iff.mp (w i).isLt
    have hw'i : (w' i).val ≤ n := Nat.lt_succ_iff.mp (w' i).isLt
    have hw'j : (w' j).val ≤ n := Nat.lt_succ_iff.mp (w' j).isLt
    have hji : (1 : ℤ) ≤ (j.val : ℤ) - (i.val : ℤ) := by omega
    have hbd : ((n : ℤ) - (w i).val + i.val) + (w j).val < j.val := by omega
    nlinarith
  have hv_nonpos : v ≤ 0 := by
    by_contra hgt
    have hv1 : 1 ≤ v := by omega
    obtain ⟨i, j, hij, hbound⟩ := hw'.2
    have hi := hcv i
    have hj := hcv j
    have hwi : (w i).val ≤ n := Nat.lt_succ_iff.mp (w i).isLt
    have hwj : (w j).val ≤ n := Nat.lt_succ_iff.mp (w j).isLt
    have hw'i : (w' i).val ≤ n := Nat.lt_succ_iff.mp (w' i).isLt
    have hji : (1 : ℤ) ≤ (j.val : ℤ) - (i.val : ℤ) := by omega
    have hbd : ((n : ℤ) - (w' i).val + i.val) + (w' j).val < j.val := by omega
    nlinarith
  have hv0 : v = 0 := le_antisymm hv_nonpos hv_nonneg
  subst hv0
  obtain ⟨i0, hi0⟩ := hw.1
  obtain ⟨j0, hj0⟩ := hw'.1
  have hc1 := hcv i0
  have hc2 := hcv j0
  have hc0 : c = 0 := by omega
  subst hc0
  funext i
  ext
  have hi := hcv i
  omega

private lemma exists_canon {n : ℕ} (w : Word n) :
    ∃ w' : Word n, IsCanon n w' ∧ differences w' = differences w := by
  let validSlope (v : ℤ) : Prop :=
    ∀ i j : Fin 5, ((w i).val : ℤ) + (i.val : ℤ) * v - (((w j).val : ℤ) + (j.val : ℤ) * v) ≤ n
  have : DecidablePred validSlope := fun v => by unfold validSlope; infer_instance
  let V : Finset ℤ := (Finset.Icc (-(2 * (n : ℤ))) 0).filter validSlope
  have h0_mem : (0 : ℤ) ∈ V := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, le_rfl⟩, ?_⟩
    intro i j
    have hi : (w i).val ≤ n := Nat.lt_succ_iff.mp (w i).isLt
    omega
  have hVne : V.Nonempty := ⟨0, h0_mem⟩
  let v : ℤ := V.min' hVne
  have hv_mem : v ∈ V := Finset.min'_mem V hVne
  have hv_le : v ≤ 0 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv_mem).1).2
  have hv_valid : validSlope v := (Finset.mem_filter.mp hv_mem).2
  have hv_min : ¬ validSlope (v - 1) := by
    intro hvalid
    have hge : -(2 * (n : ℤ)) ≤ v - 1 := by
      have h01 := hvalid 0 1
      have h0le : (w 0).val ≤ n := Nat.lt_succ_iff.mp (w 0).isLt
      have h1le : (w 1).val ≤ n := Nat.lt_succ_iff.mp (w 1).isLt
      dsimp at h01
      omega
    have hmem : v - 1 ∈ V := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hge, by omega⟩, hvalid⟩
    have hle := Finset.min'_le V (v - 1) hmem
    omega
  let f : Fin 5 → ℤ := fun i => ((w i).val : ℤ) + (i.val : ℤ) * v
  let m : ℤ := Finset.univ.inf' Finset.univ_nonempty f
  have hm_le : ∀ i : Fin 5, m ≤ f i := fun i => Finset.inf'_le f (Finset.mem_univ i)
  obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
  have hbound : ∀ i : Fin 5, 0 ≤ f i - m ∧ f i - m ≤ n := by
    intro i
    refine ⟨by linarith [hm_le i], ?_⟩
    dsimp only [m]
    rw [hi0]
    exact hv_valid i i0
  let w' : Word n := fun i => ⟨(f i - m).toNat, by have := hbound i; omega⟩
  have hw'_val : ∀ i : Fin 5, ((w' i).val : ℤ) = f i - m := by
    intro i
    have := (hbound i).1
    dsimp [w']
    omega
  refine ⟨w', ⟨⟨i0, ?_⟩, ?_⟩, ?_⟩
  · have := hw'_val i0
    dsimp only [m] at this
    rw [hi0] at this
    omega
  · unfold validSlope at hv_min
    push Not at hv_min
    obtain ⟨i, j, hij⟩ := hv_min
    have hwi := hw'_val i
    have hwj := hw'_val j
    have hwi_le : (w' i).val ≤ n := Nat.lt_succ_iff.mp (w' i).isLt
    have hwj_le : (w' j).val ≤ n := Nat.lt_succ_iff.mp (w' j).isLt
    have hdiff : ((w' i).val : ℤ) - ((w' j).val : ℤ) + (j.val : ℤ) - (i.val : ℤ) > (n : ℤ) := by
      dsimp [f] at hwi hwj
      linarith
    refine ⟨i, j, by omega, by omega⟩
  · symm
    rw [differences_eq_iff]
    refine ⟨-m, v, ?_⟩
    intro i
    rw [hw'_val i]
    dsimp [f]
    ring

private lemma a_eq_canon_card (n : ℕ) :
    a n = (Finset.univ.filter (IsCanon n)).card := by
  classical
  unfold a
  have hEq : (Finset.univ : Finset (Word n)).image differences =
      (Finset.univ.filter (IsCanon n)).image differences := by
    ext d
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨w', hw', hd⟩ := exists_canon w
      exact ⟨w', hw', hd⟩
    · rintro ⟨w, _, rfl⟩
      exact ⟨w, rfl⟩
  rw [hEq, Finset.card_image_of_injOn]
  intro w hw w' hw' heq
  exact canon_inj (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hw').2 heq

private def step (n pos v : ℕ) (st : State) : State :=
  (st.1 || decide (v = 0),
   st.2.1 || decide (st.2.2.val + v < pos),
   ⟨min st.2.2.val (min 4 (n - v + pos)), by omega⟩)

private def initState : State := (false, false, ⟨4, by omega⟩)

private def runPrefix (n : ℕ) : (k : ℕ) → (Fin k → Fin (n + 1)) → State
  | 0, _ => initState
  | k + 1, w => step n k (w (Fin.last k)).val (runPrefix n k (Fin.init w))

private lemma runPrefix5_eq (n : ℕ) (w : Word n) :
    runPrefix n 5 w =
      step n 4 (w 4).val (step n 3 (w 3).val (step n 2 (w 2).val
        (step n 1 (w 1).val (step n 0 (w 0).val initState)))) := rfl

private lemma runPrefix5_iff_isCanon (n : ℕ) (w : Word n) :
    ((runPrefix n 5 w).1 = true ∧ (runPrefix n 5 w).2.1 = true) ↔ IsCanon n w := by
  rw [runPrefix5_eq]
  have h1 : (step n 4 (w 4).val (step n 3 (w 3).val (step n 2 (w 2).val
      (step n 1 (w 1).val (step n 0 (w 0).val initState))))).1 = true ↔
      ∃ i : Fin 5, (w i).val = 0 := by
    simp only [step, initState, Bool.or_eq_true, decide_eq_true_eq, Bool.false_or]
    constructor
    · rintro ((((h | h) | h) | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
      · exact ⟨4, h⟩
    · rintro ⟨i, hi⟩
      fin_cases i
      · left; left; left; left; exact hi
      · left; left; left; right; exact hi
      · left; left; right; exact hi
      · left; right; exact hi
      · right; exact hi
  have h2 : (step n 4 (w 4).val (step n 3 (w 3).val (step n 2 (w 2).val
      (step n 1 (w 1).val (step n 0 (w 0).val initState))))).2.1 = true ↔
      ∃ i j : Fin 5, i.val < j.val ∧ (n - (w i).val + i.val) + (w j).val < j.val := by
    simp only [step, initState, Bool.or_eq_true, decide_eq_true_eq, Bool.false_or]
    constructor
    · intro h
      rcases h with (((h0 | h1) | h2) | h3) | h4
      · simp at h0
      · refine ⟨0, 1, by decide, ?_⟩; omega
      · by_cases c0 : n - (w 0).val + 0 + (w 2).val < 2
        · exact ⟨0, 2, by decide, c0⟩
        · refine ⟨1, 2, by decide, ?_⟩; omega
      · by_cases c0 : n - (w 0).val + 0 + (w 3).val < 3
        · exact ⟨0, 3, by decide, c0⟩
        · by_cases c1 : n - (w 1).val + 1 + (w 3).val < 3
          · exact ⟨1, 3, by decide, c1⟩
          · refine ⟨2, 3, by decide, ?_⟩; omega
      · by_cases c0 : n - (w 0).val + 0 + (w 4).val < 4
        · exact ⟨0, 4, by decide, c0⟩
        · by_cases c1 : n - (w 1).val + 1 + (w 4).val < 4
          · exact ⟨1, 4, by decide, c1⟩
          · by_cases c2 : n - (w 2).val + 2 + (w 4).val < 4
            · exact ⟨2, 4, by decide, c2⟩
            · refine ⟨3, 4, by decide, ?_⟩; omega
    · rintro ⟨i, j, hij, hlt⟩
      fin_cases i <;> fin_cases j <;> dsimp at hij hlt ⊢ <;> omega
  exact and_congr h1 h2

private def dp (n : ℕ) : ℕ → State → ℕ
  | 0, st => if st = initState then 1 else 0
  | pos + 1, st' =>
      ∑ st : State, dp n pos st * ((Finset.range (n + 1)).filter (fun v => step n pos v st = st')).card

private lemma card_fin_filter_eq_range (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun v : Fin (n + 1) => p v.val)).card =
      ((Finset.range (n + 1)).filter p).card := by
  refine Finset.card_bij (fun v _ => v.val) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hv ⊢
    exact ⟨v.isLt, hv⟩
  · intro v1 _ v2 _ h
    exact Fin.ext h
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    refine ⟨⟨v, hv.1⟩, ?_, rfl⟩
    simp [hv.2]

private lemma dp_eq_card (n : ℕ) :
    ∀ k st, dp n k st = (Finset.univ.filter (fun w : Fin k → Fin (n + 1) => runPrefix n k w = st)).card := by
  intro k
  induction k with
  | zero =>
    intro st
    simp only [dp, runPrefix]
    by_cases h : st = initState
    · subst h
      simp
    · have hne : initState ≠ st := Ne.symm h
      simp [h, hne]
  | succ k ih =>
    intro st'
    simp only [dp]
    have hbij :
        (Finset.univ.filter (fun w : Fin (k + 1) → Fin (n + 1) => runPrefix n (k + 1) w = st')).card =
        (Finset.univ.filter (fun p : (Fin k → Fin (n + 1)) × Fin (n + 1) =>
          step n k p.2.val (runPrefix n k p.1) = st')).card := by
      refine Finset.card_bij (fun w _ => (Fin.init w, w (Fin.last k))) ?_ ?_ ?_
      · intro w hw
        rw [Finset.mem_filter] at hw ⊢
        exact ⟨Finset.mem_univ _, hw.2⟩
      · intro w1 _ w2 _ h
        have h1 : Fin.init w1 = Fin.init w2 := congr_arg Prod.fst h
        have h2 : w1 (Fin.last k) = w2 (Fin.last k) := congr_arg Prod.snd h
        funext i
        refine Fin.lastCases h2 ?_ i
        intro j
        exact congr_fun h1 j
      · intro p hp
        rw [Finset.mem_filter] at hp
        refine ⟨Fin.snoc p.1 p.2, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          simp only [runPrefix, Fin.snoc_last, Fin.init_snoc]
          exact hp.2
        · ext <;> simp [Fin.snoc_last, Fin.init_snoc]
    rw [hbij]
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun p : (Fin k → Fin (n + 1)) × Fin (n + 1) =>
        step n k p.2.val (runPrefix n k p.1) = st'))
      (t := (Finset.univ : Finset State))
      (f := fun p => runPrefix n k p.1)
      (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    apply Finset.sum_congr rfl
    intro st _
    rw [ih st, ← card_fin_filter_eq_range]
    rw [← Finset.card_product]
    congr 1
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨hu, hv⟩
      exact ⟨by rw [hu]; exact hv, hu⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨rfl, h1⟩

private lemma a_eq_dp (n : ℕ) :
    a n = ∑ best : Fin 5, dp n 5 (true, true, best) := by
  rw [a_eq_canon_card]
  have hfilt : Finset.univ.filter (IsCanon n) =
      Finset.univ.filter (fun w : Word n => (runPrefix n 5 w).1 = true ∧ (runPrefix n 5 w).2.1 = true) := by
    ext w
    simp [runPrefix5_iff_isCanon]
  rw [hfilt]
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun w : Word n => (runPrefix n 5 w).1 = true ∧ (runPrefix n 5 w).2.1 = true))
    (t := (Finset.univ : Finset (Fin 5)))
    (f := fun w => (runPrefix n 5 w).2.2)
    (fun _ _ => Finset.mem_univ _)
  rw [hfib]
  apply Finset.sum_congr rfl
  intro best _
  rw [dp_eq_card n 5 (true, true, best)]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
  tauto

private def stepLow (pos v : ℕ) (st : State) : State :=
  (st.1 || decide (v = 0), st.2.1 || decide (st.2.2.val + v < pos), st.2.2)

private def stepHigh (pos r : ℕ) (st : State) : State :=
  (st.1, st.2.1, ⟨min st.2.2.val (min 4 (r + pos)), by omega⟩)

private def constWeight (pos : ℕ) (st st' : State) : ℕ :=
  ((Finset.range 4).filter (fun v => stepLow pos v st = st')).card +
  ((Finset.range 4).filter (fun r => stepHigh pos r st = st')).card

private lemma weight_eq_linear (m pos : ℕ) (hpos : pos < 5) (st st' : State) :
    ((Finset.range (m + 8)).filter (fun v => step (m + 7) pos v st = st')).card =
      constWeight pos st st' + if st = st' then m else 0 := by
  have hsplit : Finset.range (m + 8) =
      (Finset.range 4 ∪ Finset.Ico 4 (m + 4)) ∪ Finset.Ico (m + 4) (m + 8) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hd1 : Disjoint (Finset.range 4) (Finset.Ico 4 (m + 4)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_range, Finset.mem_Ico] at hv1 hv2
    omega
  have hd2 : Disjoint (Finset.range 4 ∪ Finset.Ico 4 (m + 4)) (Finset.Ico (m + 4) (m + 8)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at hv1 hv2
    omega
  rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd2),
      Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd1)]
  have hlow : (Finset.range 4).filter (fun v => step (m + 7) pos v st = st') =
      (Finset.range 4).filter (fun v => stepLow pos v st = st') := by
    apply Finset.filter_congr
    intro v hv
    rw [Finset.mem_range] at hv
    have heq : step (m + 7) pos v st = stepLow pos v st := by
      unfold step stepLow
      ext <;> simp only []
      · omega
    rw [heq]
  have hmid : ((Finset.Ico 4 (m + 4)).filter (fun v => step (m + 7) pos v st = st')).card =
      if st = st' then m else 0 := by
    have hconst : ∀ v ∈ Finset.Ico 4 (m + 4), step (m + 7) pos v st = st := by
      intro v hv
      rw [Finset.mem_Ico] at hv
      unfold step
      have hv0 : decide (v = 0) = false := by simp; omega
      have hvlt : decide (st.2.2.val + v < pos) = false := by simp; omega
      rcases st with ⟨b1, b2, ⟨b3, hb3⟩⟩
      simp only [hv0, hvlt, Bool.or_false]
      refine Prod.ext rfl (Prod.ext rfl (Fin.ext ?_))
      dsimp
      omega
    have heq : (Finset.Ico 4 (m + 4)).filter (fun v => step (m + 7) pos v st = st') =
        (Finset.Ico 4 (m + 4)).filter (fun _ => st = st') := by
      apply Finset.filter_congr
      intro v hv
      rw [hconst v hv]
    rw [heq]
    by_cases h : st = st'
    · simp [h]
    · simp [h]
  have hhigh : ((Finset.Ico (m + 4) (m + 8)).filter (fun v => step (m + 7) pos v st = st')).card =
      ((Finset.range 4).filter (fun r => stepHigh pos r st = st')).card := by
    refine Finset.card_bij (fun v _ => m + 7 - v) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hv ⊢
      refine ⟨by omega, ?_⟩
      have heq : step (m + 7) pos v st = stepHigh pos (m + 7 - v) st := by
        unfold step stepHigh
        have hv0 : decide (v = 0) = false := by simp; omega
        have hvlt : decide (st.2.2.val + v < pos) = false := by simp; omega
        simp only [hv0, hvlt, Bool.or_false]
      rw [← heq]
      exact hv.2
    · intro v1 hv1 v2 hv2 h
      simp only [Finset.mem_filter, Finset.mem_Ico] at hv1 hv2
      omega
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      refine ⟨m + 7 - r, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨by omega, ?_⟩
      have heq : step (m + 7) pos (m + 7 - r) st = stepHigh pos r st := by
        unfold step stepHigh
        have hv0 : decide (m + 7 - r = 0) = false := by simp; omega
        have hvlt : decide (st.2.2.val + (m + 7 - r) < pos) = false := by simp; omega
        have hsub : m + 7 - (m + 7 - r) = r := by omega
        simp only [hv0, hvlt, Bool.or_false, hsub]
      rw [heq]
      exact hr.2
  rw [hlow, hmid, hhigh, constWeight]
  omega

private def dpPoly : ℕ → State → Fin 6 → ℕ
  | 0, st, d => if st = initState ∧ d.val = 0 then 1 else 0
  | pos + 1, st', d =>
      (∑ st : State, dpPoly pos st d * constWeight pos st st') +
      (if h : 0 < d.val then dpPoly pos st' ⟨d.val - 1, by omega⟩ else 0)

private def evalP (p : Fin 6 → ℕ) (m : ℕ) : ℕ :=
  ∑ d : Fin 6, p d * m ^ d.val

private lemma dpPoly_zero_of_gt : ∀ pos st (d : Fin 6), pos < d.val → dpPoly pos st d = 0 := by
  intro pos
  induction pos with
  | zero =>
    intro st d hd
    simp only [dpPoly]
    have : d.val ≠ 0 := by omega
    simp [this]
  | succ pos ih =>
    intro st' d hd
    simp only [dpPoly]
    have h1 : ∑ st : State, dpPoly pos st d * constWeight pos st st' = 0 := by
      apply Finset.sum_eq_zero
      intro st _
      rw [ih st d (by omega), zero_mul]
    have h2 : (if h : 0 < d.val then dpPoly pos st' ⟨d.val - 1, by omega⟩ else 0) = 0 := by
      split_ifs with h
      · exact ih st' ⟨d.val - 1, by omega⟩ (by dsimp; omega)
      · rfl
    rw [h1, h2]

private lemma evalP_shift (p : Fin 6 → ℕ) (hp5 : p 5 = 0) (m : ℕ) :
    evalP (fun d => if h : 0 < d.val then p ⟨d.val - 1, by omega⟩ else 0) m = evalP p m * m := by
  unfold evalP
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  dsimp
  rw [hp5]
  ring

private lemma dp_eq_evalP (m : ℕ) :
    ∀ pos, pos ≤ 5 → ∀ st, dp (m + 7) pos st = evalP (dpPoly pos st) m := by
  intro pos
  induction pos with
  | zero =>
    intro _ st
    simp only [dp, evalP, dpPoly, Fin.sum_univ_six]
    by_cases h : st = initState <;> simp [h]
  | succ pos ih =>
    intro hle st'
    have hpos : pos < 5 := by omega
    simp only [dp]
    have h1 : ∀ st : State,
        dp (m + 7) pos st * ((Finset.range (m + 8)).filter (fun v => step (m + 7) pos v st = st')).card =
        evalP (dpPoly pos st) m * constWeight pos st st' +
        (if st = st' then evalP (dpPoly pos st) m * m else 0) := by
      intro st
      rw [ih (by omega) st, weight_eq_linear m pos hpos st st']
      split_ifs <;> ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    have h2 : ∑ st : State, evalP (dpPoly pos st) m * constWeight pos st st' =
        evalP (fun d => ∑ st : State, dpPoly pos st d * constWeight pos st st') m := by
      unfold evalP
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro st _
      ring
    have h3 : evalP (dpPoly pos st') m * m =
        evalP (fun d => if h : 0 < d.val then dpPoly pos st' ⟨d.val - 1, by omega⟩ else 0) m := by
      symm
      exact evalP_shift (dpPoly pos st') (dpPoly_zero_of_gt pos st' 5 hpos) m
    rw [h2, h3]
    simp only [evalP]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    change (∑ st : State, dpPoly pos st d * constWeight pos st st') * m ^ d.val +
        (if h : 0 < d.val then dpPoly pos st' ⟨d.val - 1, by omega⟩ else 0) * m ^ d.val =
      ((∑ st : State, dpPoly pos st d * constWeight pos st st') +
        (if h : 0 < d.val then dpPoly pos st' ⟨d.val - 1, by omega⟩ else 0)) * m ^ d.val
    ring

private def totalPoly (d : Fin 6) : ℕ :=
  ∑ best : Fin 5, dpPoly 5 (true, true, best) d

private lemma totalPoly_vals :
    totalPoly 0 = 7309 ∧ totalPoly 1 = 3067 ∧ totalPoly 2 = 429 ∧
    totalPoly 3 = 20 ∧ totalPoly 4 = 0 ∧ totalPoly 5 = 0 := by
  decide

private lemma dp_small_vals :
    (∑ best : Fin 5, dp 1 5 (true, true, best)) = 31 ∧
    (∑ best : Fin 5, dp 2 5 (true, true, best)) = 199 ∧
    (∑ best : Fin 5, dp 3 5 (true, true, best)) = 625 ∧
    (∑ best : Fin 5, dp 4 5 (true, true, best)) = 1429 ∧
    (∑ best : Fin 5, dp 5 5 (true, true, best)) = 2731 ∧
    (∑ best : Fin 5, dp 6 5 (true, true, best)) = 4651 := by
  decide

private lemma a_closed_form (n : ℕ) (hn : 1 ≤ n) :
    a n = 20 * n ^ 3 + 9 * n ^ 2 + n + 1 := by
  by_cases h7 : 7 ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h7
    rw [a_eq_dp]
    have hsum : ∑ best : Fin 5, dp (m + 7) 5 (true, true, best) = evalP totalPoly m := by
      have hbest : ∀ best : Fin 5, dp (m + 7) 5 (true, true, best) =
          evalP (dpPoly 5 (true, true, best)) m := fun b => dp_eq_evalP m 5 le_rfl (true, true, b)
      simp_rw [hbest]
      unfold evalP totalPoly
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_mul]
    rw [hsum]
    unfold evalP
    simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := totalPoly_vals
    dsimp
    rw [h0, h1, h2, h3, h4, h5]
    ring
  · obtain ⟨s1, s2, s3, s4, s5, s6⟩ := dp_small_vals
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
    · rw [a_eq_dp]; exact s1
    · rw [a_eq_dp]; exact s2
    · rw [a_eq_dp]; exact s3
    · rw [a_eq_dp]; exact s4
    · rw [a_eq_dp]; exact s5
    · rw [a_eq_dp]; exact s6

private lemma rec_main (n : ℕ) (hn : 4 < n) :
    (a n : ℚ) = 4 * (a (n - 1) : ℚ) - 6 * (a (n - 2) : ℚ) +
      4 * (a (n - 3) : ℚ) - (a (n - 4) : ℚ) := by
  have h0 : (a n : ℚ) = 20 * (n : ℚ) ^ 3 + 9 * (n : ℚ) ^ 2 + (n : ℚ) + 1 := by
    exact_mod_cast a_closed_form n (by omega)
  have h1 : (a (n - 1) : ℚ) = 20 * ((n - 1 : ℕ) : ℚ) ^ 3 + 9 * ((n - 1 : ℕ) : ℚ) ^ 2 + ((n - 1 : ℕ) : ℚ) + 1 := by
    exact_mod_cast a_closed_form (n - 1) (by omega)
  have h2 : (a (n - 2) : ℚ) = 20 * ((n - 2 : ℕ) : ℚ) ^ 3 + 9 * ((n - 2 : ℕ) : ℚ) ^ 2 + ((n - 2 : ℕ) : ℚ) + 1 := by
    exact_mod_cast a_closed_form (n - 2) (by omega)
  have h3 : (a (n - 3) : ℚ) = 20 * ((n - 3 : ℕ) : ℚ) ^ 3 + 9 * ((n - 3 : ℕ) : ℚ) ^ 2 + ((n - 3 : ℕ) : ℚ) + 1 := by
    exact_mod_cast a_closed_form (n - 3) (by omega)
  have h4 : (a (n - 4) : ℚ) = 20 * ((n - 4 : ℕ) : ℚ) ^ 3 + 9 * ((n - 4 : ℕ) : ℚ) ^ 2 + ((n - 4 : ℕ) : ℚ) + 1 := by
    exact_mod_cast a_closed_form (n - 4) (by omega)
  have c1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have c2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have c3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by rw [Nat.cast_sub (by omega)]; norm_num
  have c4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [h0, h1, h2, h3, h4, c1, c2, c3, c4]
  ring

private lemma gf_main :
    ordinary * (1 - X) ^ 4 = X * (31 + 75 * X + 15 * X ^ 2 - X ^ 3) := by
  have hmul : ordinary * (1 - X) ^ 4 =
      ordinary - (4 : ℚ) • (X ^ 1 * ordinary) + (6 : ℚ) • (X ^ 2 * ordinary) -
      (4 : ℚ) • (X ^ 3 * ordinary) + X ^ 4 * ordinary := by
    simp only [Algebra.smul_def, map_ofNat]
    ring
  have hrhs : (X * (31 + 75 * X + 15 * X ^ 2 - X ^ 3) : PowerSeries ℚ) =
      (31 : ℚ) • (X ^ 1 : PowerSeries ℚ) + (75 : ℚ) • (X ^ 2 : PowerSeries ℚ) +
      (15 : ℚ) • (X ^ 3 : PowerSeries ℚ) - (X ^ 4 : PowerSeries ℚ) := by
    simp only [Algebra.smul_def, map_ofNat]
    ring
  rw [hmul, hrhs]
  ext k
  have hf : ∀ n : ℕ, (if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      if n = 0 then 0 else 20 * (n : ℚ) ^ 3 + 9 * (n : ℚ) ^ 2 + (n : ℚ) + 1 := by
    intro n
    split_ifs with h
    · rfl
    · have hval : (a n : ℚ) = ((20 * n ^ 3 + 9 * n ^ 2 + n + 1 : ℕ) : ℚ) := by
        exact_mod_cast a_closed_form n (by omega)
      rw [hval]
      push_cast
      ring
  simp only [map_add, map_sub, map_smul, smul_eq_mul, PowerSeries.coeff_X_pow_mul',
             PowerSeries.coeff_X_pow, ordinary, PowerSeries.coeff_mk, hf]
  rcases k with _ | _ | _ | _ | _ | m
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have e0 : m + 1 + 1 + 1 + 1 + 1 = m + 5 := by omega
    have h1 : m + 5 - 1 = m + 4 := by omega
    have h2 : m + 5 - 2 = m + 3 := by omega
    have h3 : m + 5 - 3 = m + 2 := by omega
    have h4 : m + 5 - 4 = m + 1 := by omega
    rw [e0, h1, h2, h3, h4]
    have c0 : ¬ (m + 5 = 0) := by omega
    have c1 : ¬ (m + 4 = 0) := by omega
    have c2 : ¬ (m + 3 = 0) := by omega
    have c3 : ¬ (m + 2 = 0) := by omega
    have c4 : ¬ (m + 1 = 0) := by omega
    have l1 : 1 ≤ m + 5 := by omega
    have l2 : 2 ≤ m + 5 := by omega
    have l3 : 3 ≤ m + 5 := by omega
    have l4 : 4 ≤ m + 5 := by omega
    have n1 : ¬ (m + 5 = 1) := by omega
    have n2 : ¬ (m + 5 = 2) := by omega
    have n3 : ¬ (m + 5 = 3) := by omega
    have n4 : ¬ (m + 5 = 4) := by omega
    simp only [c0, c1, c2, c3, c4, l1, l2, l3, l4, n1, n2, n3, n4, ite_true, ite_false]
    push_cast
    ring

end A228220Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a228220.main :=
  ⟨A228220Proof.gf_main, A228220Proof.rec_main⟩
