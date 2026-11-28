import OMAReductions.R_oeis_a026125_R1

open PowerSeries

/-!
Construct the implicit series coefficient by coefficient. The closed forms for
the suffix-walk series satisfy the same recurrences as the walk counts, which
follow by partitioning the walks by their first step.
-/

private def rootCoeff : ℕ → ℤ
  | 0 => 0
  | n + 1 => (if n = 0 then 1 else 0) + rootCoeff n +
      ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).attach, rootCoeff p.val.1 * rootCoeff p.val.2
termination_by n => n
decreasing_by
  all_goals
    first
    | omega
    | have hp := Finset.HasAntidiagonal.mem_antidiagonal.mp p.property
      omega

private theorem implicit_root :
    ∃ r : PowerSeries ℤ, r = X * (1 + r + r ^ 2) := by
  refine ⟨PowerSeries.mk rootCoeff, ?_⟩
  ext n
  cases n with
  | zero => simp [rootCoeff]
  | succ n =>
      rw [coeff_mk, coeff_succ_X_mul, map_add, map_add, pow_two, coeff_mul, rootCoeff]
      simp only [coeff_mk, coeff_one]
      congr 1
      exact Finset.sum_attach _ (fun p : ℕ × ℕ => rootCoeff p.1 * rootCoeff p.2)

private abbrev S := PowerSeries ℤ

/-- Closed form for the suffix-walk series divided by the excursion series. -/
private noncomputable def suffixFactor (r : S) : ℕ → S
  | 0 => r ^ 4
  | 1 => r ^ 3 + r ^ 5
  | 2 => r ^ 2 + r ^ 4 + r ^ 6
  | 3 => r + r ^ 3 + r ^ 5 + r ^ 7
  | n + 4 => r ^ n * (1 + r ^ 2 + r ^ 4 + r ^ 6 + r ^ 8)

private noncomputable def suffixSeries (r : S) (a : ℕ) : S :=
  (1 + r + r ^ 2) * suffixFactor r a

private theorem suffix_zero (r : S) (hr : r = X * (1 + r + r ^ 2)) :
    suffixSeries r 0 = X * (suffixSeries r 0 + suffixSeries r 1) := by
  simp only [suffixSeries, suffixFactor]
  linear_combination (r ^ 4 + (r ^ 3 + r ^ 5)) * hr

private theorem suffix_succ (r : S) (hr : r = X * (1 + r + r ^ 2)) (a : ℕ) :
    suffixSeries r (a + 1) =
      (if a = 3 then 1 else 0) +
        X * (suffixSeries r a + suffixSeries r (a + 1) + suffixSeries r (a + 2)) := by
  let q := suffixFactor r a + suffixFactor r (a + 1) + suffixFactor r (a + 2)
  have hz : X * (suffixSeries r a + suffixSeries r (a + 1) + suffixSeries r (a + 2)) =
      r * q := by
    dsimp [suffixSeries, q]
    linear_combination -(suffixFactor r a + suffixFactor r (a + 1) +
      suffixFactor r (a + 2)) * hr
  rw [hz]
  clear hz hr
  dsimp [q, suffixSeries]
  by_cases ha : a < 4
  · interval_cases a <;> norm_num [suffixFactor] <;> ring
  · obtain ⟨m, rfl⟩ : ∃ m, a = m + 4 := ⟨a - 4, by omega⟩
    have hm : m + 4 ≠ 3 := by omega
    simp only [hm, if_false, zero_add, suffixFactor, pow_succ]
    ring

private theorem suffix_generating (r : S) (hr : r = X * (1 + r + r ^ 2)) :
    X * (suffixSeries r 0 + suffixSeries r 2) = r ^ 3 + (2 : ℤ) • r ^ 5 + r ^ 7 := by
  simp only [suffixSeries, suffixFactor, zsmul_eq_mul]
  push_cast <;> linear_combination -(r ^ 4 + (r ^ 2 + r ^ 4 + r ^ 6)) * hr

private theorem suffix_count_comparison (r : S) (hr : r = X * (1 + r + r ^ 2))
    (count : ℕ → ℕ → ℤ)
    (empty : ∀ a, count a 0 = if a = 4 then 1 else 0)
    (atZero : ∀ n, count 0 (n + 1) = count 0 n + count 1 n)
    (aboveZero : ∀ a n, count (a + 1) (n + 1) =
      count a n + count (a + 1) n + count (a + 2) n) :
    ∀ n a, coeff n (suffixSeries r a) = count a n := by
  have hr0 : constantCoeff r = 0 := by
    calc
      constantCoeff r = constantCoeff (X * (1 + r + r ^ 2)) := congrArg constantCoeff hr
      _ = 0 := by simp
  intro n
  induction n with
  | zero =>
      intro a
      rw [empty, coeff_zero_eq_constantCoeff_apply]
      by_cases ha : a < 5
      · interval_cases a <;> norm_num [suffixSeries, suffixFactor, hr0]
      · obtain ⟨m, rfl⟩ : ∃ m, a = m + 5 := ⟨a - 5, by omega⟩
        have hm : m + 5 ≠ 4 := by omega
        simp [suffixSeries, suffixFactor, show m + 5 = (m + 1) + 4 by omega,
          hr0, hm]
  | succ n ih =>
      intro a
      cases a with
      | zero =>
          rw [suffix_zero r hr, coeff_succ_X_mul, map_add, ih, ih, atZero]
      | succ a =>
          rw [suffix_succ r hr, map_add, coeff_succ_X_mul, aboveZero]
          split_ifs <;> simp [coeff_one, map_add, ih]

private theorem h1_of_counts
    (count : ℕ → ℕ → ℤ)
    (empty : ∀ a, count a 0 = if a = 4 then 1 else 0)
    (atZero : ∀ n, count 0 (n + 1) = count 0 n + count 1 n)
    (aboveZero : ∀ a n, count (a + 1) (n + 1) =
      count a n + count (a + 1) n + count (a + 2) n)
    (firstEmpty : OMA.S_oeis_a026125.a 0 = 0)
    (firstStep : ∀ n, OMA.S_oeis_a026125.a (n + 1) = count 0 n + count 2 n) :
    OMA.R_oeis_a026125_R1.H1 := by
  obtain ⟨r, hr⟩ := implicit_root
  refine ⟨r, hr, ?_⟩
  have h := suffix_count_comparison r hr count empty atZero aboveZero
  intro n
  rw [← suffix_generating r hr]
  cases n with
  | zero => simp [firstEmpty]
  | succ n => rw [coeff_succ_X_mul, map_add, h, h, firstStep]

private def adjacent (a b : ℕ) : Prop := |(b : ℤ) - (a : ℤ)| ≤ 1

private def suffixWalks (a n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | s 0 = a ∧ s (Fin.last n) = 4 ∧
    ∀ i j : Fin (n + 1), j.val = i.val + 1 → adjacent (s i) (s j)}

private theorem suffix_cons_iff {a n : ℕ} (s : Fin (n + 1) → ℕ) :
    Fin.cons a s ∈ suffixWalks a (n + 1) ↔
      adjacent a (s 0) ∧ s ∈ suffixWalks (s 0) n := by
  change (_ = a ∧ _ = 4 ∧ _) ↔ adjacent a (s 0) ∧ (_ = _ ∧ _ = 4 ∧ _)
  have hlast : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext rfl
  constructor
  · rintro ⟨_, hend, hstep⟩
    refine ⟨?_, rfl, ?_, ?_⟩
    · simpa using hstep 0 (Fin.succ 0) rfl
    · simpa only [← hlast, Fin.cons_succ] using hend
    · intro i j hij
      simpa only [Fin.cons_succ] using hstep i.succ j.succ (by simpa using congrArg Nat.succ hij)
  · rintro ⟨hfirst, _, hend, hstep⟩
    refine ⟨Fin.cons_zero _ _, ?_, ?_⟩
    · simpa only [← hlast, Fin.cons_succ] using hend
    · intro i j
      induction i using Fin.cases with
      | zero =>
          intro hij
          have hj : j = (Fin.succ 0 : Fin (n + 2)) := Fin.ext (by simpa using hij)
          simpa [hj] using hfirst
      | succ i' =>
          intro hij
          induction j using Fin.cases with
          | zero => simp only [Fin.val_zero, Fin.val_succ] at *; omega
          | succ j' => simpa only [Fin.cons_succ] using hstep i' j' (by simp only [Fin.val_zero, Fin.val_succ] at *; omega)

private theorem adjacent_cases (a b : ℕ) :
    adjacent a b ↔ b = a ∨ b = a + 1 ∨ (0 < a ∧ b + 1 = a) := by
  unfold adjacent
  rw [abs_le]
  omega

private theorem suffix_finite (a n : ℕ) : (suffixWalks a n).Finite := by
  have bound (s : suffixWalks a n) (i : Fin (n + 1)) : s.val i ≤ a + i.val := by
    have hs := s.property
    change s.val 0 = a ∧ s.val (Fin.last n) = 4 ∧ _ at hs
    induction i using Fin.induction with
    | zero => simpa using hs.1.le
    | succ i ih =>
        have h := (abs_le.mp (hs.2.2 i.castSucc i.succ rfl)).2
        simp only [Fin.val_castSucc, Fin.val_succ] at ih ⊢
        omega
  let emb (s : suffixWalks a n) (i : Fin (n + 1)) : Fin (a + n + 1) :=
    ⟨s.val i, by have := bound s i; have := i.isLt; omega⟩
  haveI : Finite (suffixWalks a n) := Finite.of_injective emb (by
    intro s t h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i))
  exact Set.toFinite _

private def startingWith (a b n : ℕ) : Set (Fin (n + 2) → ℕ) :=
  Fin.cons a '' suffixWalks b n

private theorem mem_startingWith {a b n : ℕ} {s : Fin (n + 2) → ℕ} :
    s ∈ startingWith a b n ↔ s 0 = a ∧ Fin.tail s ∈ suffixWalks b n := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ht
  · rintro ⟨hs, ht⟩
    exact ⟨Fin.tail s, ht, by rw [← hs, Fin.cons_self_tail]⟩

private theorem startingWith_disjoint {a b c n : ℕ} (h : b ≠ c) :
    Disjoint (startingWith a b n) (startingWith a c n) := by
  refine Set.disjoint_left.mpr ?_
  intro s hb hc
  have hb' : Fin.tail s 0 = b := (mem_startingWith.mp hb).2.1
  have hc' : Fin.tail s 0 = c := (mem_startingWith.mp hc).2.1
  exact h (hb'.symm.trans hc')

private theorem startingWith_ncard (a b n : ℕ) :
    (startingWith a b n).ncard = (suffixWalks b n).ncard := by
  apply Set.ncard_image_of_injective
  intro s t h
  simpa using congrArg Fin.tail h

private theorem suffix_tail_iff {a n : ℕ} {s : Fin (n + 2) → ℕ} :
    s ∈ suffixWalks a (n + 1) ↔
      s 0 = a ∧ adjacent a (Fin.tail s 0) ∧
        Fin.tail s ∈ suffixWalks (Fin.tail s 0) n := by
  constructor
  · intro hs
    have hstart : s 0 = a := hs.1
    have hcons : Fin.cons a (Fin.tail s) = s := by rw [← hstart, Fin.cons_self_tail]
    exact ⟨hstart, suffix_cons_iff _ |>.mp (hcons.symm ▸ hs)⟩
  · rintro ⟨hstart, hstep, htail⟩
    have hcons : Fin.cons a (Fin.tail s) = s := by rw [← hstart, Fin.cons_self_tail]
    rw [← hcons]
    exact (suffix_cons_iff _).mpr ⟨hstep, htail⟩

private theorem mem_suffix_split {a n : ℕ} {s : Fin (n + 2) → ℕ} :
    s ∈ suffixWalks a (n + 1) ↔
      s ∈ startingWith a a n ∪ startingWith a (a + 1) n ∨
        ∃ b, b + 1 = a ∧ s ∈ startingWith a b n := by
  rw [suffix_tail_iff, Set.mem_union]
  constructor
  · rintro ⟨hstart, hstep, htail⟩
    rcases (adjacent_cases _ _).mp hstep with h | h | ⟨_, h⟩
    · exact Or.inl (Or.inl (mem_startingWith.mpr ⟨hstart, h ▸ htail⟩))
    · exact Or.inl (Or.inr (mem_startingWith.mpr ⟨hstart, h ▸ htail⟩))
    · exact Or.inr ⟨_, h, mem_startingWith.mpr ⟨hstart, htail⟩⟩
  · rintro ((h | h) | ⟨b, hb, h⟩)
    · obtain ⟨hstart, htail⟩ := mem_startingWith.mp h
      have hb : Fin.tail s 0 = a := htail.1
      exact ⟨hstart, (adjacent_cases _ _).mpr (Or.inl hb), hb.symm ▸ htail⟩
    · obtain ⟨hstart, htail⟩ := mem_startingWith.mp h
      have hb : Fin.tail s 0 = a + 1 := htail.1
      exact ⟨hstart, (adjacent_cases _ _).mpr (Or.inr (Or.inl hb)), hb.symm ▸ htail⟩
    · obtain ⟨hstart, htail⟩ := mem_startingWith.mp h
      have hc : Fin.tail s 0 = b := htail.1
      exact ⟨hstart, (adjacent_cases _ _).mpr (Or.inr (Or.inr ⟨by omega, by omega⟩)),
        hc.symm ▸ htail⟩

private noncomputable def suffixCount (a n : ℕ) : ℤ := (suffixWalks a n).ncard

private theorem startingWith_finite (a b n : ℕ) : (startingWith a b n).Finite :=
  (suffix_finite b n).image _

private theorem suffixCount_atZero (n : ℕ) :
    suffixCount 0 (n + 1) = suffixCount 0 n + suffixCount 1 n := by
  have h : suffixWalks 0 (n + 1) = startingWith 0 0 n ∪ startingWith 0 1 n := by
    ext s
    rw [mem_suffix_split]
    simp
  unfold suffixCount
  rw [h, Set.ncard_union_eq (startingWith_disjoint (by omega))
    (startingWith_finite ..) (startingWith_finite ..), startingWith_ncard, startingWith_ncard]
  push_cast <;> rfl

private theorem suffixCount_aboveZero (a n : ℕ) :
    suffixCount (a + 1) (n + 1) = suffixCount a n + suffixCount (a + 1) n + suffixCount (a + 2) n := by
  have h : suffixWalks (a + 1) (n + 1) =
      startingWith (a + 1) a n ∪ (startingWith (a + 1) (a + 1) n ∪ startingWith (a + 1) (a + 2) n) := by
    ext s
    rw [mem_suffix_split]
    simp [or_comm]
  unfold suffixCount
  rw [h, Set.ncard_union_eq (Set.disjoint_union_right.mpr ⟨
      (startingWith_disjoint (by omega)), (startingWith_disjoint (by omega))⟩)
    (startingWith_finite ..) ((startingWith_finite ..).union (startingWith_finite ..)),
    Set.ncard_union_eq (startingWith_disjoint (by omega))
      (startingWith_finite ..) (startingWith_finite ..)]
  simp only [startingWith_ncard, Nat.cast_add, add_assoc]

private theorem suffixCount_empty (a : ℕ) :
    suffixCount a 0 = if a = 4 then 1 else 0 := by
  by_cases ha : a = 4
  · subst a
    have h : suffixWalks 4 0 = {fun _ => 4} := by
      ext s
      constructor
      · intro hs
        apply Set.mem_singleton_iff.mpr
        funext i
        have hi : i = 0 := Fin.ext (by have := i.isLt; simpa using (show i.val = 0 by omega))
        simpa [hi] using hs.1
      · intro hs
        obtain rfl := Set.mem_singleton_iff.mp hs
        refine ⟨rfl, rfl, ?_⟩
        intro i j hij
        exact False.elim (by have := j.isLt; omega)
    simp [suffixCount, h]
  · have h : suffixWalks a 0 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro s hs
      exact ha (hs.1.symm.trans hs.2.1)
    simp [suffixCount, h, ha]

private theorem initial_empty : OMA.S_oeis_a026125.a 0 = 0 := by
  have h : OMA.S_oeis_a026125.walks 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hstart := hs.1 0 rfl
    have hend := hs.2.1 0 rfl
    omega
  simp [OMA.S_oeis_a026125.a, h]

private theorem initial_step (n : ℕ) :
    OMA.S_oeis_a026125.a (n + 1) = suffixCount 0 n + suffixCount 2 n := by
  have h : OMA.S_oeis_a026125.walks (n + 1) = startingWith 1 0 n ∪ startingWith 1 2 n := by
    ext s
    rw [Set.mem_union, mem_startingWith, mem_startingWith]
    change (∀ i, i.val = 0 → s i = 1) ∧
        (∀ i, i.val = n + 1 → s i = 4) ∧
        (∀ i j, j.val = i.val + 1 → j.val ≤ 1 → |(s j : ℤ) - (s i : ℤ)| = 1) ∧
        (∀ i j, j.val = i.val + 1 → 1 < j.val → adjacent (s i) (s j)) ↔ _
    constructor
    · rintro ⟨hfirst, hend, hforced, hstep⟩
      have hstart : s 0 = 1 := hfirst 0 rfl
      have hd : |(Fin.tail s 0 : ℤ) - 1| = 1 := by
        simpa [Fin.tail, hstart] using hforced 0 (Fin.succ 0) rfl (by simp)
      have htail : Fin.tail s ∈ suffixWalks (Fin.tail s 0) n := by
        refine ⟨rfl, hend _ rfl, ?_⟩
        intro i j hij
        exact hstep i.succ j.succ (by simp only [Fin.val_zero, Fin.val_succ] at *; omega) (by simp only [Fin.val_zero, Fin.val_succ] at *; omega)
      have hb : Fin.tail s 0 = 0 ∨ Fin.tail s 0 = 2 := by
        rcases le_total (1 : ℤ) (Fin.tail s 0 : ℤ) with hs | hs
        · rw [abs_of_nonneg (sub_nonneg.mpr hs)] at hd
          omega
        · rw [abs_of_nonpos (sub_nonpos.mpr hs)] at hd
          omega
      rcases hb with hb | hb
      · exact Or.inl ⟨hstart, hb ▸ htail⟩
      · exact Or.inr ⟨hstart, hb ▸ htail⟩
    · intro hs
      have hstart : s 0 = 1 := hs.elim And.left And.left
      have hend : Fin.tail s (Fin.last n) = 4 :=
        hs.elim (fun h => h.2.2.1) (fun h => h.2.2.1)
      have hstep : ∀ i j : Fin (n + 1), j.val = i.val + 1 →
          adjacent (Fin.tail s i) (Fin.tail s j) :=
        hs.elim (fun h => h.2.2.2) (fun h => h.2.2.2)
      have hb : Fin.tail s 0 = 0 ∨ Fin.tail s 0 = 2 :=
        hs.elim (fun h => Or.inl h.2.1) (fun h => Or.inr h.2.1)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [show i = 0 from Fin.ext hi]
        exact hstart
      · intro i hi
        rw [show i = (Fin.last n).succ from Fin.ext hi]
        exact hend
      · intro i j hij hj
        have hi' : i = 0 := Fin.ext (by simp only [Fin.val_zero, Fin.val_succ] at *; omega)
        have hj' : j = Fin.succ 0 := Fin.ext (by simp only [Fin.val_zero, Fin.val_succ] at *; omega)
        rw [hi', hj', hstart]
        change |(Fin.tail s 0 : ℤ) - 1| = 1
        rcases hb with hb | hb <;> norm_num [hb]
      · intro i j
        induction i using Fin.cases with
        | zero => intro hij hj; simp only [Fin.val_zero, Fin.val_succ] at *; omega
        | succ i' =>
            intro hij hj
            induction j using Fin.cases with
            | zero => simp only [Fin.val_zero, Fin.val_succ] at *; omega
            | succ j' => exact hstep i' j' (by simp only [Fin.val_zero, Fin.val_succ] at *; omega)
  unfold OMA.S_oeis_a026125.a suffixCount
  rw [h, Set.ncard_union_eq (startingWith_disjoint (by decide))
    (startingWith_finite ..) (startingWith_finite ..), startingWith_ncard, startingWith_ncard]
  push_cast <;> rfl

theorem OMA.solution : OMA.R_oeis_a026125_R1.H1 :=
  h1_of_counts suffixCount suffixCount_empty suffixCount_atZero suffixCount_aboveZero
    initial_empty initial_step
