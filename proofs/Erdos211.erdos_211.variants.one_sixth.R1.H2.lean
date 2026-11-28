import OMAReductions.R_Erdos211_erdos_211_variants_one_sixth_R1

-- Step Erdos211.erdos_211.variants.one_sixth.R1.H2: hypothesis H2 of reduction Erdos211.erdos_211.variants.one_sixth.R1
-- Credit: @LiJiaHua1024
-- Proof of Melchior's mean-multiplicity inequality via projective duality and combinatorial sweep-line.

namespace OMA.MelchiorSweep

noncomputable section

open Finset EuclideanGeometry Erdos211
open scoped BigOperators Classical

/-- Two affine linear functions that do not meet on `[x₁, x₂]` maintain their strict order. -/
private lemma affine_same_order_of_no_root {m₁ c₁ m₂ c₂ x₁ x₂ : ℝ} (hle : x₁ ≤ x₂)
    (hne : ∀ x, x₁ ≤ x → x ≤ x₂ → m₁ * x + c₁ ≠ m₂ * x + c₂) :
    (m₁ * x₁ + c₁ < m₂ * x₁ + c₂) ↔ (m₁ * x₂ + c₁ < m₂ * x₂ + c₂) := by
  let a := (m₂ * x₁ + c₂) - (m₁ * x₁ + c₁)
  let b := (m₂ * x₂ + c₂) - (m₁ * x₂ + c₁)
  have ha0 : a ≠ 0 := sub_ne_zero.mpr (hne x₁ le_rfl hle).symm
  have hb0 : b ≠ 0 := sub_ne_zero.mpr (hne x₂ hle le_rfl).symm
  have hprod : 0 < a * b := by
    by_contra hle0
    push Not at hle0
    have hlt0 : a * b < 0 := lt_of_le_of_ne hle0 (mul_ne_zero ha0 hb0)
    have hab : a - b ≠ 0 := by
      intro h0
      have : a = b := sub_eq_zero.mp h0
      rw [this] at hlt0
      nlinarith [sq_nonneg b]
    let lam := a / (a - b)
    have hlam0 : 0 ≤ lam := by
      dsimp only [lam]
      by_cases ha : 0 < a
      · have hb : b < 0 := by nlinarith
        exact div_nonneg ha.le (by linarith)
      · have ha' : a < 0 := lt_of_le_of_ne (not_lt.mp ha) ha0
        have hb : 0 < b := by nlinarith
        exact div_nonneg_of_nonpos ha'.le (by linarith)
    have hlam1 : lam ≤ 1 := by
      dsimp only [lam]
      by_cases ha : 0 < a
      · have hb : b < 0 := by nlinarith
        exact (div_le_one (by linarith)).mpr (by linarith)
      · have ha' : a < 0 := lt_of_le_of_ne (not_lt.mp ha) ha0
        have hb : 0 < b := by nlinarith
        exact (div_le_one_of_neg (by linarith)).mpr (by linarith)
    let x₀ := (1 - lam) * x₁ + lam * x₂
    have hx1 : x₁ ≤ x₀ := by dsimp only [x₀]; nlinarith
    have hx2 : x₀ ≤ x₂ := by dsimp only [x₀]; nlinarith
    have hlin : (m₂ * x₀ + c₂) - (m₁ * x₀ + c₁) = (1 - lam) * a + lam * b := by
      dsimp only [x₀, a, b]; ring
    have hzero : (1 - lam) * a + lam * b = 0 := by
      dsimp only [lam]; field_simp [hab]; ring
    exact hne x₀ hx1 hx2 (by linarith)
  constructor
  · intro h
    have ha : 0 < a := sub_pos.mpr h
    have hb : 0 < b := by nlinarith
    exact sub_pos.mp hb
  · intro h
    have hb : 0 < b := sub_pos.mpr h
    have ha : 0 < a := by nlinarith
    exact sub_pos.mp ha

/- ### Part 1: Pure combinatorial sweep-line proof of `∑ r_t ≤ 3 * M` -/

private structure SweepData (n M : ℕ) where
  m : Fin n → ℝ
  c : Fin n → ℝ
  hm : StrictMono m
  v : Fin M → ℝ × ℝ
  hv : StrictMono fun t => (v t).1
  hM : 0 < M
  hpair : ∀ i j : Fin n, i ≠ j →
    ∃ t : Fin M, m i * (v t).1 + c i = (v t).2 ∧ m j * (v t).1 + c j = (v t).2
  hnc : ∀ t : Fin M, (univ.filter fun i : Fin n => m i * (v t).1 + c i = (v t).2).card < n

namespace SweepData

variable {n M : ℕ} (D : SweepData n M)

private def f (i : Fin n) (x : ℝ) : ℝ := D.m i * x + D.c i

private def I (t : Fin M) : Finset (Fin n) := univ.filter fun i => D.f i (D.v t).1 = (D.v t).2

private def r (t : Fin M) : ℕ := (D.I t).card

private def p (t : Fin M) : ℕ := (univ.filter fun j : Fin n => D.f j (D.v t).1 < (D.v t).2).card

private def ξ (s : Fin (M + 1)) : ℝ :=
  if h0 : s.val = 0 then (D.v ⟨0, D.hM⟩).1 - 1
  else if hlt : s.val < M then ((D.v ⟨s.val - 1, by omega⟩).1 + (D.v ⟨s.val, hlt⟩).1) / 2
  else (D.v ⟨M - 1, by have := D.hM; omega⟩).1 + 1

private def pos (s : Fin (M + 1)) (i : Fin n) : ℕ :=
  (univ.filter fun j : Fin n => D.f j (D.ξ s) < D.f i (D.ξ s)).card

private def C (k : ℕ) : Finset (Fin M) :=
  univ.filter fun t : Fin M => D.p t + 1 ≤ k ∧ k + 1 ≤ D.p t + D.r t

private def T (k : ℕ) : Finset (Fin M) :=
  univ.filter fun t : Fin M => k = D.p t ∨ k = D.p t + D.r t

private lemma uniq {i j : Fin n} (hij : i ≠ j) {x₁ x₂ : ℝ}
    (h1 : D.f i x₁ = D.f j x₁) (h2 : D.f i x₂ = D.f j x₂) : x₁ = x₂ := by
  have hmne : D.m i - D.m j ≠ 0 := sub_ne_zero.mpr (D.hm.injective.ne hij)
  have hmul : (D.m i - D.m j) * (x₁ - x₂) = 0 := by
    dsimp only [f] at h1 h2; linarith
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h hmne
  · linarith

private lemma pair_uniq {i j : Fin n} (hij : i ≠ j) {t₁ t₂ : Fin M}
    (hi1 : i ∈ D.I t₁) (hj1 : j ∈ D.I t₁) (hi2 : i ∈ D.I t₂) (hj2 : j ∈ D.I t₂) : t₁ = t₂ := by
  have h1 : D.f i (D.v t₁).1 = D.f j (D.v t₁).1 :=
    (mem_filter.mp hi1).2.trans (mem_filter.mp hj1).2.symm
  have h2 : D.f i (D.v t₂).1 = D.f j (D.v t₂).1 :=
    (mem_filter.mp hi2).2.trans (mem_filter.mp hj2).2.symm
  exact D.hv.injective (D.uniq hij h1 h2)

private lemma ξ_lt (t : Fin M) : D.ξ t.castSucc < (D.v t).1 := by
  dsimp only [ξ]
  by_cases h0 : t.val = 0
  · simp only [Fin.val_castSucc, h0, ↓reduceDIte]
    have ht : t = ⟨0, D.hM⟩ := Fin.ext h0
    rw [ht]; linarith
  · simp only [Fin.val_castSucc, h0, ↓reduceDIte, t.isLt]
    have hprev : (D.v ⟨t.val - 1, by omega⟩).1 < (D.v t).1 :=
      D.hv (show (⟨t.val - 1, by omega⟩ : Fin M) < t by simp [Fin.lt_def]; omega)
    linarith

private lemma lt_ξ (t : Fin M) : (D.v t).1 < D.ξ t.succ := by
  dsimp only [ξ]
  have hne : t.val + 1 ≠ 0 := by omega
  simp only [Fin.val_succ, hne, ↓reduceDIte]
  split_ifs with hlt
  · have hnext : (D.v t).1 < (D.v ⟨t.val + 1, hlt⟩).1 :=
      D.hv (show t < ⟨t.val + 1, hlt⟩ by simp [Fin.lt_def])
    have heq : (⟨t.val + 1 - 1, by omega⟩ : Fin M) = t := Fin.ext (by simp)
    rw [heq]; linarith
  · have htlt := t.isLt
    have heq : (⟨M - 1, by have := D.hM; omega⟩ : Fin M) = t := Fin.ext (by simp; omega)
    rw [heq]; linarith

private lemma ξ_ne_v (s : Fin (M + 1)) (t : Fin M) : D.ξ s ≠ (D.v t).1 := by
  by_cases h : s.val ≤ t.val
  · by_cases heq : s.val = t.val
    · have hs : s = t.castSucc := Fin.ext heq
      rw [hs]; exact (D.ξ_lt t).ne
    · have h1 : D.ξ s < (D.v ⟨s.val, by omega⟩).1 := by
        have h' := D.ξ_lt ⟨s.val, by omega⟩
        have hs : (⟨s.val, by omega⟩ : Fin M).castSucc = s := Fin.ext rfl
        rwa [hs] at h'
      have h2 : (D.v ⟨s.val, by omega⟩).1 < (D.v t).1 :=
        D.hv (show (⟨s.val, by omega⟩ : Fin M) < t by simp [Fin.lt_def]; omega)
      linarith
  · have h1 : (D.v t).1 ≤ (D.v ⟨s.val - 1, by omega⟩).1 :=
      D.hv.monotone (show t ≤ ⟨s.val - 1, by omega⟩ by simp [Fin.le_def]; omega)
    have h2 : (D.v ⟨s.val - 1, by omega⟩).1 < D.ξ s := by
      have h' := D.lt_ξ ⟨s.val - 1, by omega⟩
      have hs : (⟨s.val - 1, by omega⟩ : Fin M).succ = s := Fin.ext (by simp; omega)
      rwa [hs] at h'
    linarith

private lemma ξ_inj (s : Fin (M + 1)) (i j : Fin n) (heq : D.f i (D.ξ s) = D.f j (D.ξ s)) : i = j := by
  by_contra hij
  obtain ⟨t, hti, htj⟩ := D.hpair i j hij
  exact D.ξ_ne_v s t (D.uniq hij heq (hti.trans htj.symm))

private lemma no_root_in_slab (t : Fin M) {i j : Fin n} (hij : i ≠ j)
    (hnot : i ∉ D.I t ∨ j ∉ D.I t) {x : ℝ}
    (hx1 : D.ξ t.castSucc ≤ x) (hx2 : x ≤ D.ξ t.succ) : D.f i x ≠ D.f j x := by
  intro heq
  obtain ⟨t', ht'i, ht'j⟩ := D.hpair i j hij
  have hxeq : x = (D.v t').1 := D.uniq hij heq (ht'i.trans ht'j.symm)
  have htt' : t' = t := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (D.v t').1 ≤ (D.v ⟨t.val - 1, by omega⟩).1 :=
        D.hv.monotone (show t' ≤ ⟨t.val - 1, by omega⟩ by simp [Fin.le_def]; omega)
      have hlt' : (D.v ⟨t.val - 1, by omega⟩).1 < D.ξ t.castSucc := by
        have h' := D.lt_ξ ⟨t.val - 1, by omega⟩
        have hteq : (⟨t.val - 1, by omega⟩ : Fin M).succ = t.castSucc := Fin.ext (by simp; omega)
        rwa [hteq] at h'
      linarith
    · have hlt' : D.ξ t.succ < (D.v ⟨t.val + 1, by omega⟩).1 := by
        have h' := D.ξ_lt ⟨t.val + 1, by omega⟩
        have hteq : (⟨t.val + 1, by omega⟩ : Fin M).castSucc = t.succ := Fin.ext (by simp)
        rwa [hteq] at h'
      have hle : (D.v ⟨t.val + 1, by omega⟩).1 ≤ (D.v t').1 :=
        D.hv.monotone (show (⟨t.val + 1, by omega⟩ : Fin M) ≤ t' by simp [Fin.le_def]; omega)
      linarith
  subst htt'
  rcases hnot with hi | hj
  · exact hi (mem_filter.mpr ⟨mem_univ i, ht'i⟩)
  · exact hj (mem_filter.mpr ⟨mem_univ j, ht'j⟩)

private lemma cross_same (t : Fin M) (i j : Fin n) (hnot : i ∉ D.I t ∨ j ∉ D.I t) :
    D.f j (D.ξ t.castSucc) < D.f i (D.ξ t.castSucc) ↔ D.f j (D.ξ t.succ) < D.f i (D.ξ t.succ) := by
  by_cases hij : i = j
  · subst hij; simp
  exact affine_same_order_of_no_root (le_trans (D.ξ_lt t).le (D.lt_ξ t).le)
    (fun x hx1 hx2 h => D.no_root_in_slab t hij hnot hx1 hx2 h.symm)

private lemma left_half_same (t : Fin M) (i j : Fin n) (hnot : i ∉ D.I t ∨ j ∉ D.I t) :
    D.f j (D.ξ t.castSucc) < D.f i (D.ξ t.castSucc) ↔ D.f j (D.v t).1 < D.f i (D.v t).1 := by
  by_cases hij : i = j
  · subst hij; simp
  exact affine_same_order_of_no_root (D.ξ_lt t).le
    (fun x hx1 hx2 h => D.no_root_in_slab t hij hnot hx1 (le_trans hx2 (D.lt_ξ t).le) h.symm)

private lemma notI_cmp (t : Fin M) (i j : Fin n) (hi : i ∈ D.I t) (hj : j ∉ D.I t) :
    (D.f j (D.ξ t.castSucc) < D.f i (D.ξ t.castSucc) ↔ D.f j (D.v t).1 < (D.v t).2) ∧
    (D.f j (D.ξ t.succ) < D.f i (D.ξ t.succ) ↔ D.f j (D.v t).1 < (D.v t).2) := by
  have hfi : D.f i (D.v t).1 = (D.v t).2 := (mem_filter.mp hi).2
  have h1 := D.left_half_same t i j (Or.inr hj)
  rw [hfi] at h1
  exact ⟨h1, (D.cross_same t i j (Or.inr hj)).symm.trans h1⟩

private lemma pos_lt (s : Fin (M + 1)) (i : Fin n) : D.pos s i < n := by
  have hilt := i.isLt
  calc D.pos s i ≤ (univ.erase i).card := by
        apply card_le_card
        intro j hj
        rw [mem_erase]
        refine ⟨fun h => ?_, mem_univ j⟩
        subst h; exact lt_irrefl _ (mem_filter.mp hj).2
    _ < n := by rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]; omega

private lemma pos_inj (s : Fin (M + 1)) : Function.Injective (D.pos s) := by
  intro i j heq
  by_contra hij
  have hne : D.f i (D.ξ s) ≠ D.f j (D.ξ s) := fun h => hij (D.ξ_inj s i j h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hsub : (univ.filter fun l : Fin n => D.f l (D.ξ s) < D.f i (D.ξ s)) ⊂
        (univ.filter fun l : Fin n => D.f l (D.ξ s) < D.f j (D.ξ s)) := by
      rw [ssubset_iff_of_subset]
      · exact ⟨i, mem_filter.mpr ⟨mem_univ i, hlt⟩, by simp⟩
      · intro l hl; exact mem_filter.mpr ⟨mem_univ l, lt_trans (mem_filter.mp hl).2 hlt⟩
    exact (card_lt_card hsub).ne heq
  · have hsub : (univ.filter fun l : Fin n => D.f l (D.ξ s) < D.f j (D.ξ s)) ⊂
        (univ.filter fun l : Fin n => D.f l (D.ξ s) < D.f i (D.ξ s)) := by
      rw [ssubset_iff_of_subset]
      · exact ⟨j, mem_filter.mpr ⟨mem_univ j, hlt⟩, by simp⟩
      · intro l hl; exact mem_filter.mpr ⟨mem_univ l, lt_trans (mem_filter.mp hl).2 hlt⟩
    exact (card_lt_card hsub).ne heq.symm

private lemma pos_surj (s : Fin (M + 1)) (k : ℕ) (hk : k < n) : ∃ i : Fin n, D.pos s i = k := by
  let g : Fin n → Fin n := fun i => ⟨D.pos s i, D.pos_lt s i⟩
  have hg_inj : Function.Injective g := fun i j h => D.pos_inj s (congrArg Fin.val h)
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hg_inj ⟨k, hk⟩
  exact ⟨i, congrArg Fin.val hi⟩

private lemma pos_zero (i : Fin n) : D.pos 0 i = n - 1 - i.val := by
  have hleft : ∀ a b : Fin n, a < b → D.f b (D.ξ 0) < D.f a (D.ξ 0) := by
    intro a b hab
    obtain ⟨t, hta, htb⟩ := D.hpair a b hab.ne
    have hxt : D.ξ 0 < (D.v t).1 :=
      lt_of_lt_of_le (D.ξ_lt ⟨0, D.hM⟩) (D.hv.monotone (Nat.zero_le t.val))
    have hdiff : D.f a (D.ξ 0) - D.f b (D.ξ 0) = (D.m b - D.m a) * ((D.v t).1 - D.ξ 0) := by
      dsimp only [f] at hta htb ⊢; nlinarith
    have hpos_d : 0 < (D.m b - D.m a) * ((D.v t).1 - D.ξ 0) :=
      mul_pos (sub_pos.mpr (D.hm hab)) (sub_pos.mpr hxt)
    linarith
  have hfilt : (univ.filter fun j : Fin n => D.f j (D.ξ 0) < D.f i (D.ξ 0)) =
      univ.filter fun j : Fin n => i < j := by
    ext j; simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact lt_irrefl _ h
      · exact absurd (hleft j i hlt) (not_lt.mpr h.le)
    · exact hleft i j
  dsimp only [pos]
  rw [hfilt]
  have hbij : (univ.filter fun j : Fin n => i < j).card = (Ioo i.val n).card := by
    apply Finset.card_bij (fun j _ => j.val)
    · intro j hj; rw [mem_Ioo]; exact ⟨(mem_filter.mp hj).2, j.isLt⟩
    · intro j₁ _ j₂ _ h; exact Fin.ext h
    · intro b hb; rw [mem_Ioo] at hb; exact ⟨⟨b, hb.2⟩, mem_filter.mpr ⟨mem_univ _, hb.1⟩, rfl⟩
  rw [hbij, Nat.card_Ioo]
  have := i.isLt; omega

private lemma pos_last (i : Fin n) : D.pos ⟨M, Nat.lt_succ_self M⟩ i = i.val := by
  have hright : ∀ a b : Fin n, a < b →
      D.f a (D.ξ ⟨M, Nat.lt_succ_self M⟩) < D.f b (D.ξ ⟨M, Nat.lt_succ_self M⟩) := by
    intro a b hab
    obtain ⟨t, hta, htb⟩ := D.hpair a b hab.ne
    have hxt : (D.v t).1 < D.ξ ⟨M, Nat.lt_succ_self M⟩ := by
      have h1 : (D.v t).1 ≤ (D.v ⟨M - 1, by have := D.hM; omega⟩).1 :=
        D.hv.monotone (show t ≤ ⟨M - 1, by have := D.hM; omega⟩ by simp [Fin.le_def]; omega)
      have h2 := D.lt_ξ ⟨M - 1, by have := D.hM; omega⟩
      have hM_eq : (⟨M - 1, by have := D.hM; omega⟩ : Fin M).succ = ⟨M, Nat.lt_succ_self M⟩ :=
        Fin.ext (by simp; have := D.hM; omega)
      rw [hM_eq] at h2
      linarith
    have hdiff : D.f b (D.ξ ⟨M, Nat.lt_succ_self M⟩) - D.f a (D.ξ ⟨M, Nat.lt_succ_self M⟩) =
        (D.m b - D.m a) * (D.ξ ⟨M, Nat.lt_succ_self M⟩ - (D.v t).1) := by
      dsimp only [f] at hta htb ⊢; nlinarith
    have hpos_d : 0 < (D.m b - D.m a) * (D.ξ ⟨M, Nat.lt_succ_self M⟩ - (D.v t).1) :=
      mul_pos (sub_pos.mpr (D.hm hab)) (sub_pos.mpr hxt)
    linarith
  have hfilt : (univ.filter fun j : Fin n =>
        D.f j (D.ξ ⟨M, Nat.lt_succ_self M⟩) < D.f i (D.ξ ⟨M, Nat.lt_succ_self M⟩)) =
      univ.filter fun j : Fin n => j < i := by
    ext j; simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact lt_irrefl _ h
      · exact absurd (hright i j hlt) (not_lt.mpr h.le)
    · exact hright j i
  dsimp only [pos]
  rw [hfilt]
  have hbij : (univ.filter fun j : Fin n => j < i).card = (Finset.range i.val).card := by
    apply Finset.card_bij (fun j _ => j.val)
    · intro j hj; exact mem_range.mpr (mem_filter.mp hj).2
    · intro j₁ _ j₂ _ h; exact Fin.ext h
    · intro b hb; rw [mem_range] at hb
      exact ⟨⟨b, lt_trans hb i.isLt⟩, mem_filter.mpr ⟨mem_univ _, hb⟩, rfl⟩
  rw [hbij, card_range]

private lemma pos_notI_eq (t : Fin M) (j : Fin n) (hj : j ∉ D.I t) :
    D.pos t.castSucc j = D.pos t.succ j := by
  dsimp only [pos]; congr 1; ext l; simp only [mem_filter, mem_univ, true_and]
  exact D.cross_same t j l (Or.inl hj)

private lemma pos_notI_range (t : Fin M) (j : Fin n) (hj : j ∉ D.I t) :
    D.pos t.castSucc j < D.p t ∨ D.p t + D.r t ≤ D.pos t.castSucc j := by
  have hfj_ne : D.f j (D.v t).1 ≠ (D.v t).2 := fun h => hj (mem_filter.mpr ⟨mem_univ j, h⟩)
  rcases lt_or_gt_of_ne hfj_ne with hlt | hgt
  · left
    have hsub : (univ.filter fun l : Fin n => D.f l (D.ξ t.castSucc) < D.f j (D.ξ t.castSucc)) ⊂
        (univ.filter fun l : Fin n => D.f l (D.v t).1 < (D.v t).2) := by
      rw [ssubset_iff_of_subset]
      · exact ⟨j, mem_filter.mpr ⟨mem_univ j, hlt⟩, by simp⟩
      · intro l hl
        have hlj : D.f l (D.v t).1 < D.f j (D.v t).1 :=
          (D.left_half_same t j l (Or.inl hj)).mp (mem_filter.mp hl).2
        exact mem_filter.mpr ⟨mem_univ l, lt_trans hlj hlt⟩
    exact card_lt_card hsub
  · right
    have hdisj : Disjoint (univ.filter fun l : Fin n => D.f l (D.v t).1 < (D.v t).2) (D.I t) := by
      rw [disjoint_left]; intro l h1 h2; exact (mem_filter.mp h1).2.ne (mem_filter.mp h2).2
    have hsub : (univ.filter fun l : Fin n => D.f l (D.v t).1 < (D.v t).2) ∪ D.I t ⊆
        univ.filter fun l : Fin n => D.f l (D.ξ t.castSucc) < D.f j (D.ξ t.castSucc) := by
      intro l hl
      rw [mem_filter]; refine ⟨mem_univ l, ?_⟩
      rw [D.left_half_same t j l (Or.inl hj)]
      rcases mem_union.mp hl with hl | hl
      · exact lt_trans (mem_filter.mp hl).2 hgt
      · rw [(mem_filter.mp hl).2]; exact hgt
    calc D.p t + D.r t = ((univ.filter fun l : Fin n => D.f l (D.v t).1 < (D.v t).2) ∪ D.I t).card :=
          (card_union_of_disjoint hdisj).symm
      _ ≤ D.pos t.castSucc j := card_le_card hsub

private lemma pos_I_range (t : Fin M) (i : Fin n) (hi : i ∈ D.I t) :
    (D.p t ≤ D.pos t.castSucc i ∧ D.pos t.castSucc i < D.p t + D.r t) ∧
    (D.p t ≤ D.pos t.succ i ∧ D.pos t.succ i < D.p t + D.r t) := by
  have hlo : ∀ (s : Fin (M + 1)),
      (∀ j, j ∉ D.I t → (D.f j (D.ξ s) < D.f i (D.ξ s) ↔ D.f j (D.v t).1 < (D.v t).2)) →
      D.p t ≤ D.pos s i ∧ D.pos s i < D.p t + D.r t := by
    intro s hcmp
    constructor
    · apply card_le_card
      intro j hj
      have hlt : D.f j (D.v t).1 < (D.v t).2 := (mem_filter.mp hj).2
      have hjnot : j ∉ D.I t := fun h => hlt.ne (mem_filter.mp h).2
      exact mem_filter.mpr ⟨mem_univ j, (hcmp j hjnot).mpr hlt⟩
    · have hdisj : Disjoint (univ.filter fun j : Fin n => D.f j (D.v t).1 < (D.v t).2) (D.I t) := by
        rw [disjoint_left]; intro j h1 h2; exact (mem_filter.mp h1).2.ne (mem_filter.mp h2).2
      have hsub : (univ.filter fun j : Fin n => D.f j (D.ξ s) < D.f i (D.ξ s)) ⊂
          (univ.filter fun j : Fin n => D.f j (D.v t).1 < (D.v t).2) ∪ D.I t := by
        rw [ssubset_iff_of_subset]
        · exact ⟨i, mem_union_right _ hi, by simp⟩
        · intro j hj
          by_cases hjI : j ∈ D.I t
          · exact mem_union_right _ hjI
          · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ j, (hcmp j hjI).mp (mem_filter.mp hj).2⟩)
      calc D.pos s i < ((univ.filter fun j : Fin n => D.f j (D.v t).1 < (D.v t).2) ∪ D.I t).card :=
            card_lt_card hsub
        _ = D.p t + D.r t := card_union_of_disjoint hdisj
  exact ⟨hlo t.castSucc (fun j hj => (D.notI_cmp t i j hi hj).1),
    hlo t.succ (fun j hj => (D.notI_cmp t i j hi hj).2)⟩

private lemma stay_fwd (k : ℕ) (t : Fin M) (hC : t ∉ D.C k) (hT : t ∉ D.T k)
    (i : Fin n) (hpos : D.pos t.castSucc i = k - 1 ∨ D.pos t.castSucc i = k) :
    D.pos t.succ i = D.pos t.castSucc i := by
  have hi : i ∉ D.I t := by
    intro hmem
    have hr := (D.pos_I_range t i hmem).1
    simp only [C, T, mem_filter, mem_univ, true_and] at hC hT
    rcases hpos with h | h <;> omega
  exact (D.pos_notI_eq t i hi).symm

private lemma stay_bwd (k : ℕ) (t : Fin M) (hC : t ∉ D.C k) (hT : t ∉ D.T k)
    (i : Fin n) (hpos : D.pos t.succ i = k - 1 ∨ D.pos t.succ i = k) :
    D.pos t.castSucc i = D.pos t.succ i := by
  have hi : i ∉ D.I t := by
    intro hmem
    have hr := (D.pos_I_range t i hmem).2
    simp only [C, T, mem_filter, mem_univ, true_and] at hC hT
    rcases hpos with h | h <;> omega
  exact D.pos_notI_eq t i hi

private lemma stay_interval (k a b : ℕ) (hab : a ≤ b) (hb : b ≤ M)
    (hfree : ∀ t : Fin M, a ≤ t.val → t.val < b → t ∉ D.C k ∧ t ∉ D.T k)
    (i : Fin n) (hpos : D.pos ⟨a, by omega⟩ i = k - 1 ∨ D.pos ⟨a, by omega⟩ i = k) :
    D.pos ⟨b, by omega⟩ i = D.pos ⟨a, by omega⟩ i := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hb_eq := ih (by omega) (fun t h1 h2 => hfree t h1 (by omega)) hpos
    have ht_free := hfree ⟨b, by omega⟩ hab (Nat.lt_succ_self b)
    have hstep := D.stay_fwd k ⟨b, by omega⟩ ht_free.1 ht_free.2 i (hb_eq.symm ▸ hpos)
    exact hstep.trans hb_eq

private lemma stay_interval_bwd (k a b : ℕ) (hab : a ≤ b) (hb : b ≤ M)
    (hfree : ∀ t : Fin M, a ≤ t.val → t.val < b → t ∉ D.C k ∧ t ∉ D.T k)
    (i : Fin n) (hpos : D.pos ⟨b, by omega⟩ i = k - 1 ∨ D.pos ⟨b, by omega⟩ i = k) :
    D.pos ⟨a, by omega⟩ i = D.pos ⟨b, by omega⟩ i := by
  suffices ∀ d : ℕ, ∀ (hd : d ≤ b - a),
      D.pos ⟨b - d, by omega⟩ i = D.pos ⟨b, by omega⟩ i by
    have h := this (b - a) le_rfl
    have heq : (⟨b - (b - a), by omega⟩ : Fin (M + 1)) = ⟨a, by omega⟩ := Fin.ext (by simp; omega)
    rwa [heq] at h
  intro d hd
  induction d with
  | zero => rfl
  | succ d ih =>
    have hprev := ih (by omega)
    let t : Fin M := ⟨b - (d + 1), by omega⟩
    have ht_free := hfree t (by dsimp only [t]; omega) (by dsimp only [t]; omega)
    have hsucc : t.succ = ⟨b - d, by omega⟩ := Fin.ext (by dsimp only [t]; simp; omega)
    have hstep := D.stay_bwd k t ht_free.1 ht_free.2 i (hsucc.symm ▸ hprev.symm ▸ hpos)
    exact hstep.trans (hsucc ▸ hprev)

private lemma mem_I_of_C (k : ℕ) (t : Fin M) (htC : t ∈ D.C k) :
    (∀ i : Fin n, (D.pos t.castSucc i = k - 1 ∨ D.pos t.castSucc i = k) → i ∈ D.I t) ∧
    (∀ i : Fin n, (D.pos t.succ i = k - 1 ∨ D.pos t.succ i = k) → i ∈ D.I t) := by
  have ⟨h1, h2⟩ := (mem_filter.mp htC).2
  constructor
  · intro i hi; by_contra hnot
    have hr := D.pos_notI_range t i hnot
    rcases hi with h | h <;> omega
  · intro i hi; by_contra hnot
    have hr := D.pos_notI_range t i hnot
    rw [D.pos_notI_eq t i hnot] at hr
    rcases hi with h | h <;> omega

private lemma C_nonempty (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) : (D.C k).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have hpres : ∀ (s : ℕ) (hs : s ≤ M) (i : Fin n),
      D.pos ⟨s, by omega⟩ i < k ↔ D.pos 0 i < k := by
    intro s hs i
    induction s with
    | zero => rfl
    | succ s ih =>
      have hstep : D.pos ⟨s + 1, by omega⟩ i < k ↔ D.pos ⟨s, by omega⟩ i < k := by
        let t : Fin M := ⟨s, by omega⟩
        have htC : t ∉ D.C k := by rw [hemp]; simp
        simp only [C, mem_filter, mem_univ, true_and] at htC
        by_cases hiI : i ∈ D.I t
        · have hr1 := (D.pos_I_range t i hiI).1
          have hr2 := (D.pos_I_range t i hiI).2
          change D.pos t.succ i < k ↔ D.pos t.castSucc i < k
          omega
        · have heq := D.pos_notI_eq t i hiI
          change D.pos t.succ i < k ↔ D.pos t.castSucc i < k
          rw [heq]
      exact hstep.trans (ih (by omega))
  let i₀ : Fin n := ⟨n - 1, by omega⟩
  have h0 := hpres M le_rfl i₀
  rw [D.pos_last, D.pos_zero] at h0
  dsimp only [i₀] at h0
  omega

private lemma gap_bounded (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1)
    (t₁ t₂ : Fin M) (ht1 : t₁ ∈ D.C k) (ht2 : t₂ ∈ D.C k) (hlt : t₁ < t₂)
    (hnoC : ∀ t : Fin M, t₁ < t → t < t₂ → t ∉ D.C k) :
    ∃ t : Fin M, t ∈ D.T k ∧ t₁ < t ∧ t < t₂ := by
  by_contra hnoT
  push Not at hnoT
  have hfree : ∀ t : Fin M, t₁.val + 1 ≤ t.val → t.val < t₂.val → t ∉ D.C k ∧ t ∉ D.T k := by
    intro t h1 h2
    have ht1' : t₁ < t := Fin.lt_def.mpr (by omega)
    have ht2' : t < t₂ := Fin.lt_def.mpr (by omega)
    exact ⟨hnoC t ht1' ht2', fun hT => (not_lt.mpr (hnoT t hT ht1')) ht2'⟩
  obtain ⟨i₁, hi₁⟩ := D.pos_surj t₁.succ (k - 1) (by omega)
  obtain ⟨i₂, hi₂⟩ := D.pos_surj t₁.succ k (by omega)
  have hne : i₁ ≠ i₂ := fun h => by subst h; omega
  have hi1_t1 : i₁ ∈ D.I t₁ := (D.mem_I_of_C k t₁ ht1).2 i₁ (Or.inl hi₁)
  have hi2_t1 : i₂ ∈ D.I t₁ := (D.mem_I_of_C k t₁ ht1).2 i₂ (Or.inr hi₂)
  have hi1_eq : D.pos t₂.castSucc i₁ = k - 1 := by
    have h := D.stay_interval k (t₁.val + 1) t₂.val (by exact hlt) (by omega) hfree i₁ (Or.inl hi₁)
    exact h.trans hi₁
  have hi2_eq : D.pos t₂.castSucc i₂ = k := by
    have h := D.stay_interval k (t₁.val + 1) t₂.val (by exact hlt) (by omega) hfree i₂ (Or.inr hi₂)
    exact h.trans hi₂
  have hi1_t2 : i₁ ∈ D.I t₂ := (D.mem_I_of_C k t₂ ht2).1 i₁ (Or.inl hi1_eq)
  have hi2_t2 : i₂ ∈ D.I t₂ := (D.mem_I_of_C k t₂ ht2).1 i₂ (Or.inr hi2_eq)
  exact hlt.ne (D.pair_uniq hne hi1_t1 hi2_t1 hi1_t2 hi2_t2)

private lemma gap_unbounded (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    (∃ t : Fin M, t ∈ D.T k ∧ t < (D.C k).min' (D.C_nonempty k hk1 hk2)) ∨
    (∃ t : Fin M, t ∈ D.T (n - k) ∧
      (D.C (n - k)).max' (D.C_nonempty (n - k) (by omega) (by omega)) < t) := by
  by_contra hneither
  push Not at hneither
  obtain ⟨hnoLeft, hnoRight⟩ := hneither
  let t₁ := (D.C k).min' (D.C_nonempty k hk1 hk2)
  let t₂ := (D.C (n - k)).max' (D.C_nonempty (n - k) (by omega) (by omega))
  have ht1C : t₁ ∈ D.C k := min'_mem _ _
  have ht2C : t₂ ∈ D.C (n - k) := max'_mem _ _
  have hfreeL : ∀ t : Fin M, 0 ≤ t.val → t.val < t₁.val → t ∉ D.C k ∧ t ∉ D.T k := by
    intro t _ hlt
    exact ⟨fun hC => (not_lt.mpr (min'_le _ t hC)) hlt,
      fun hT => (not_lt.mpr (hnoLeft t hT)) hlt⟩
  have hfreeR : ∀ t : Fin M, t₂.val + 1 ≤ t.val → t.val < M → t ∉ D.C (n - k) ∧ t ∉ D.T (n - k) := by
    intro t hgt _
    have ht_gt : t₂ < t := Fin.lt_def.mpr (by omega)
    exact ⟨fun hC => (not_lt.mpr (le_max' _ t hC)) ht_gt,
      fun hT => (not_lt.mpr (hnoRight t hT)) ht_gt⟩
  let i₁ : Fin n := ⟨n - k, by omega⟩
  let i₂ : Fin n := ⟨n - 1 - k, by omega⟩
  have hne : i₁ ≠ i₂ := fun h => by have := congrArg Fin.val h; dsimp only [i₁, i₂] at this; omega
  have hi1_0 : D.pos 0 i₁ = k - 1 := by rw [D.pos_zero]; dsimp only [i₁]; omega
  have hi2_0 : D.pos 0 i₂ = k := by rw [D.pos_zero]; dsimp only [i₂]; omega
  have hi1_t1_pos : D.pos t₁.castSucc i₁ = k - 1 := by
    have h := D.stay_interval k 0 t₁.val (Nat.zero_le _) t₁.isLt.le hfreeL i₁ (Or.inl hi1_0)
    exact h.trans hi1_0
  have hi2_t1_pos : D.pos t₁.castSucc i₂ = k := by
    have h := D.stay_interval k 0 t₁.val (Nat.zero_le _) t₁.isLt.le hfreeL i₂ (Or.inr hi2_0)
    exact h.trans hi2_0
  have hi1_t1 : i₁ ∈ D.I t₁ := (D.mem_I_of_C k t₁ ht1C).1 i₁ (Or.inl hi1_t1_pos)
  have hi2_t1 : i₂ ∈ D.I t₁ := (D.mem_I_of_C k t₁ ht1C).1 i₂ (Or.inr hi2_t1_pos)
  have hi1_M : D.pos ⟨M, Nat.lt_succ_self M⟩ i₁ = n - k := by rw [D.pos_last]
  have hi2_M : D.pos ⟨M, Nat.lt_succ_self M⟩ i₂ = (n - k) - 1 := by
    rw [D.pos_last]; dsimp only [i₂]; omega
  have hi1_t2_pos : D.pos t₂.succ i₁ = n - k := by
    have h := D.stay_interval_bwd (n - k) (t₂.val + 1) M t₂.isLt le_rfl hfreeR i₁ (Or.inr hi1_M)
    exact h.trans hi1_M
  have hi2_t2_pos : D.pos t₂.succ i₂ = (n - k) - 1 := by
    have h := D.stay_interval_bwd (n - k) (t₂.val + 1) M t₂.isLt le_rfl hfreeR i₂ (Or.inl hi2_M)
    exact h.trans hi2_M
  have hi1_t2 : i₁ ∈ D.I t₂ := (D.mem_I_of_C (n - k) t₂ ht2C).2 i₁ (Or.inr hi1_t2_pos)
  have hi2_t2 : i₂ ∈ D.I t₂ := (D.mem_I_of_C (n - k) t₂ ht2C).2 i₂ (Or.inl hi2_t2_pos)
  have ht12 : t₁ = t₂ := D.pair_uniq hne hi1_t1 hi2_t1 hi1_t2 hi2_t2
  have hex_j : ∃ j : Fin n, j ∉ D.I t₁ := by
    by_contra hall; push Not at hall
    have hcard : (D.I t₁).card = n := by
      rw [show D.I t₁ = univ by ext x; simp [hall x], card_univ, Fintype.card_fin]
    exact (D.hnc t₁).ne hcard
  obtain ⟨j, hj⟩ := hex_j
  have hji1 : j ≠ i₁ := fun h => hj (h ▸ hi1_t1)
  obtain ⟨t_j, htj_j, htj_i1⟩ := D.hpair j i₁ hji1
  have hti1_mem : i₁ ∈ D.I t_j := mem_filter.mpr ⟨mem_univ i₁, htj_i1⟩
  have htjne : t_j ≠ t₁ := fun h => hj (h ▸ mem_filter.mpr ⟨mem_univ j, htj_j⟩)
  rcases lt_or_gt_of_ne htjne with hlt | hgt
  · have hi1_tj_pos : D.pos t_j.castSucc i₁ = k - 1 := by
      have hfree' : ∀ t : Fin M, 0 ≤ t.val → t.val < t_j.val → t ∉ D.C k ∧ t ∉ D.T k :=
        fun t h1 h2 => hfreeL t h1 (lt_trans h2 hlt)
      have h := D.stay_interval k 0 t_j.val (Nat.zero_le _) t_j.isLt.le hfree' i₁ (Or.inl hi1_0)
      exact h.trans hi1_0
    have hr := (D.pos_I_range t_j i₁ hti1_mem).1
    rw [hi1_tj_pos] at hr
    have ⟨hnotC, hnotT⟩ := hfreeL t_j (Nat.zero_le _) hlt
    simp only [C, T, mem_filter, mem_univ, true_and] at hnotC hnotT
    omega
  · have hgt2 : t₂ < t_j := ht12 ▸ hgt
    have hi1_tj_pos : D.pos t_j.succ i₁ = n - k := by
      have hfree' : ∀ t : Fin M, t_j.val + 1 ≤ t.val → t.val < M → t ∉ D.C (n - k) ∧ t ∉ D.T (n - k) :=
        fun t h1 h2 => hfreeR t (by omega) h2
      have h := D.stay_interval_bwd (n - k) (t_j.val + 1) M t_j.isLt le_rfl hfree' i₁ (Or.inr hi1_M)
      exact h.trans hi1_M
    have hr := (D.pos_I_range t_j i₁ hti1_mem).2
    rw [hi1_tj_pos] at hr
    have ⟨hnotC, hnotT⟩ := hfreeR t_j (by exact hgt2) t_j.isLt
    simp only [C, T, mem_filter, mem_univ, true_and] at hnotC hnotT
    omega

private lemma sum_r_le_three_M : (∑ t : Fin M, D.r t) ≤ 3 * M := by
  have hpr_le : ∀ t : Fin M, D.p t + D.r t ≤ n := by
    intro t
    have hdisj : Disjoint (univ.filter fun j : Fin n => D.f j (D.v t).1 < (D.v t).2) (D.I t) := by
      rw [disjoint_left]; intro j h1 h2; exact (mem_filter.mp h1).2.ne (mem_filter.mp h2).2
    calc D.p t + D.r t = ((univ.filter fun j : Fin n => D.f j (D.v t).1 < (D.v t).2) ∪ D.I t).card :=
          (card_union_of_disjoint hdisj).symm
      _ ≤ (univ : Finset (Fin n)).card := card_le_card (subset_univ _)
      _ = n := by simp
  have hsum_T : (∑ k ∈ Icc 1 (n - 1), (D.T k).card) ≤ 2 * M := by
    have hle : (∑ k ∈ Icc 1 (n - 1), (D.T k).card) ≤ ∑ k ∈ range (n + 1), (D.T k).card := by
      apply sum_le_sum_of_subset
      intro k hk; rw [mem_Icc] at hk; rw [mem_range]; omega
    calc (∑ k ∈ Icc 1 (n - 1), (D.T k).card)
        ≤ ∑ k ∈ range (n + 1), (D.T k).card := hle
      _ = ∑ t : Fin M, ((range (n + 1)).filter fun k => k = D.p t ∨ k = D.p t + D.r t).card := by
          simp only [T, card_filter]; rw [Finset.sum_comm]
      _ ≤ ∑ _t : Fin M, 2 := by
          apply sum_le_sum; intro t _
          have hsub : ((range (n + 1)).filter fun k => k = D.p t ∨ k = D.p t + D.r t) ⊆
              {D.p t, D.p t + D.r t} := by
            intro k hk; rcases (mem_filter.mp hk).2 with rfl | rfl <;> simp
          exact (card_le_card hsub).trans card_le_two
      _ = 2 * M := by simp [mul_comm]
  have hsum_C : (∑ k ∈ Icc 1 (n - 1), (D.C k).card) = ∑ t : Fin M, (D.r t - 1) := by
    simp only [C, card_filter]
    rw [Finset.sum_comm]
    apply sum_congr rfl; intro t _
    have hfilt : (Icc 1 (n - 1)).filter (fun k => D.p t + 1 ≤ k ∧ k + 1 ≤ D.p t + D.r t) =
        Icc (D.p t + 1) (D.p t + D.r t - 1) := by
      ext k; simp only [mem_filter, mem_Icc]; have := hpr_le t; omega
    rw [← card_filter, hfilt, Nat.card_Icc]; omega
  have hmid_ge : ∀ k : ℕ, ∀ (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1),
      (D.C k).card - 1 ≤
        ((D.T k).filter fun t =>
          (D.C k).min' (D.C_nonempty k hk1 hk2) < t ∧ t < (D.C k).max' (D.C_nonempty k hk1 hk2)).card := by
    intro k hk1 hk2
    let cmax := (D.C k).max' (D.C_nonempty k hk1 hk2)
    let cmin := (D.C k).min' (D.C_nonempty k hk1 hk2)
    let S := (D.C k).erase cmax
    have hcardS : S.card = (D.C k).card - 1 := card_erase_of_mem (max'_mem (D.C k) (D.C_nonempty k hk1 hk2))
    rw [← hcardS]
    have hnxt_ne : ∀ c ∈ S, ((D.C k).filter (c < ·)).Nonempty := fun c hc =>
      ⟨cmax, mem_filter.mpr ⟨max'_mem _ _,
        lt_of_le_of_ne (le_max' _ c (mem_of_mem_erase hc)) (ne_of_mem_erase hc)⟩⟩
    have hex_g : ∀ c, ∀ (hc : c ∈ S), ∃ t ∈ D.T k, c < t ∧ t < ((D.C k).filter (c < ·)).min' (hnxt_ne c hc) := by
      intro c hc
      let c' := ((D.C k).filter (c < ·)).min' (hnxt_ne c hc)
      have hc'mem := min'_mem ((D.C k).filter (c < ·)) (hnxt_ne c hc)
      have hnoC : ∀ t : Fin M, c < t → t < c' → t ∉ D.C k := fun t h1 h2 hC =>
        (not_lt.mpr (min'_le _ t (mem_filter.mpr ⟨hC, h1⟩))) h2
      exact D.gap_bounded k hk1 hk2 c c' (mem_of_mem_erase hc) (mem_filter.mp hc'mem).1
        (mem_filter.mp hc'mem).2 hnoC
    let g : Fin M → Fin M := fun c => if hc : c ∈ S then Classical.choose (hex_g c hc) else c
    refine card_le_card_of_injOn g (fun c hc => ?_) (fun a ha b hb hab => ?_)
    · have hc' : c ∈ S := mem_coe.mp hc
      dsimp only [g]; rw [dif_pos hc']
      obtain ⟨htT, h1, h2⟩ := Classical.choose_spec (hex_g c hc')
      have hcmin : cmin ≤ c := min'_le _ c (mem_of_mem_erase hc')
      have hc'le : ((D.C k).filter (c < ·)).min' (hnxt_ne c hc') ≤ cmax :=
        le_max' _ _ (mem_filter.mp (min'_mem _ (hnxt_ne c hc'))).1
      exact mem_coe.mpr (mem_filter.mpr ⟨htT, lt_of_le_of_lt hcmin h1, lt_of_lt_of_le h2 hc'le⟩)
    · by_contra hne
      wlog hlt : a < b generalizing a b
      · exact this b hb a ha hab.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
      have ha' : a ∈ S := mem_coe.mp ha
      have hb' : b ∈ S := mem_coe.mp hb
      dsimp only [g] at hab; rw [dif_pos ha', dif_pos hb'] at hab
      obtain ⟨_, _, ha2⟩ := Classical.choose_spec (hex_g a ha')
      obtain ⟨_, hb1, _⟩ := Classical.choose_spec (hex_g b hb')
      have hble : ((D.C k).filter (a < ·)).min' (hnxt_ne a ha') ≤ b :=
        min'_le _ b (mem_filter.mpr ⟨mem_of_mem_erase hb', hlt⟩)
      rw [hab] at ha2
      exact (lt_trans hb1 (lt_of_lt_of_le ha2 hble)).false
  have hT_split : ∀ k : ℕ, ∀ (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1),
      ((D.T k).filter fun t => t < (D.C k).min' (D.C_nonempty k hk1 hk2)).card +
      ((D.T k).filter fun t => (D.C k).min' (D.C_nonempty k hk1 hk2) < t ∧
        t < (D.C k).max' (D.C_nonempty k hk1 hk2)).card +
      ((D.T k).filter fun t => (D.C k).max' (D.C_nonempty k hk1 hk2) < t).card ≤ (D.T k).card := by
    intro k hk1 hk2
    let cmin := (D.C k).min' (D.C_nonempty k hk1 hk2)
    let cmax := (D.C k).max' (D.C_nonempty k hk1 hk2)
    let A := (D.T k).filter fun t => t < cmin
    let B := (D.T k).filter fun t => cmin < t ∧ t < cmax
    let E := (D.T k).filter fun t => cmax < t
    have hAB : Disjoint A B := by
      rw [disjoint_left]; intro t h1 h2
      exact lt_asymm (mem_filter.mp h1).2 (mem_filter.mp h2).2.1
    have hABE : Disjoint (A ∪ B) E := by
      rw [disjoint_left]; intro t h1 h2
      have hcmm : cmin ≤ cmax := le_max' _ _ (min'_mem _ _)
      rcases mem_union.mp h1 with h1 | h1
      · exact lt_asymm (lt_of_lt_of_le (mem_filter.mp h1).2 hcmm) (mem_filter.mp h2).2
      · exact lt_asymm (mem_filter.mp h1).2.2 (mem_filter.mp h2).2
    have hsub : A ∪ B ∪ E ⊆ D.T k := by
      intro t ht
      rcases mem_union.mp ht with h | h
      · rcases mem_union.mp h with h | h <;> exact (mem_filter.mp h).1
      · exact (mem_filter.mp h).1
    calc A.card + B.card + E.card
        = (A ∪ B).card + E.card := by rw [card_union_of_disjoint hAB]
      _ = (A ∪ B ∪ E).card := (card_union_of_disjoint hABE).symm
      _ ≤ (D.T k).card := card_le_card hsub
  let Lcard : ℕ → ℕ := fun k =>
    if h : 1 ≤ k ∧ k ≤ n - 1 then
      ((D.T k).filter fun t => t < (D.C k).min' (D.C_nonempty k h.1 h.2)).card
    else 0
  let Mcard : ℕ → ℕ := fun k =>
    if h : 1 ≤ k ∧ k ≤ n - 1 then
      ((D.T k).filter fun t => (D.C k).min' (D.C_nonempty k h.1 h.2) < t ∧
        t < (D.C k).max' (D.C_nonempty k h.1 h.2)).card
    else 0
  let Rcard : ℕ → ℕ := fun k =>
    if h : 1 ≤ k ∧ k ≤ n - 1 then
      ((D.T k).filter fun t => (D.C k).max' (D.C_nonempty k h.1 h.2) < t).card
    else 0
  have hsum_R_rev : ∑ k ∈ Icc 1 (n - 1), Rcard (n - k) = ∑ k ∈ Icc 1 (n - 1), Rcard k := by
    apply Finset.sum_bij (fun k _ => n - k)
    · intro k hk; rw [mem_Icc] at hk ⊢; omega
    · intro k₁ hk₁ k₂ hk₂ h; rw [mem_Icc] at hk₁ hk₂; omega
    · intro k hk; rw [mem_Icc] at hk; exact ⟨n - k, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro _ _; rfl
  have hC_le_T : ∑ k ∈ Icc 1 (n - 1), (D.C k).card ≤ ∑ k ∈ Icc 1 (n - 1), (D.T k).card := by
    have hstep1 : ∑ k ∈ Icc 1 (n - 1), (D.C k).card ≤
        ∑ k ∈ Icc 1 (n - 1), (Mcard k + (Lcard k + Rcard (n - k))) := by
      apply sum_le_sum; intro k hk; rw [mem_Icc] at hk
      have h1 : (D.C k).card - 1 ≤ Mcard k := by
        dsimp only [Mcard]; rw [dif_pos hk]; exact hmid_ge k hk.1 hk.2
      have h2 : 1 ≤ Lcard k + Rcard (n - k) := by
        dsimp only [Lcard, Rcard]
        rw [dif_pos hk, dif_pos (show 1 ≤ n - k ∧ n - k ≤ n - 1 by omega)]
        rcases D.gap_unbounded k hk.1 hk.2 with ⟨t, htT, hlt⟩ | ⟨t, htT, hgt⟩
        · have hpos : 0 < ((D.T k).filter fun t => t < (D.C k).min' (D.C_nonempty k hk.1 hk.2)).card :=
            Finset.card_pos.mpr ⟨t, mem_filter.mpr ⟨htT, hlt⟩⟩
          omega
        · have hpos : 0 < ((D.T (n - k)).filter fun t =>
              (D.C (n - k)).max' (D.C_nonempty (n - k) (by omega) (by omega)) < t).card :=
            Finset.card_pos.mpr ⟨t, mem_filter.mpr ⟨htT, hgt⟩⟩
          omega
      have hCpos : 1 ≤ (D.C k).card := Finset.card_pos.mpr (D.C_nonempty k hk.1 hk.2)
      omega
    calc ∑ k ∈ Icc 1 (n - 1), (D.C k).card
        ≤ ∑ k ∈ Icc 1 (n - 1), (Mcard k + (Lcard k + Rcard (n - k))) := hstep1
      _ = (∑ k ∈ Icc 1 (n - 1), Mcard k) + (∑ k ∈ Icc 1 (n - 1), Lcard k) +
          (∑ k ∈ Icc 1 (n - 1), Rcard (n - k)) := by simp only [Finset.sum_add_distrib]; ring
      _ = ∑ k ∈ Icc 1 (n - 1), (Lcard k + Mcard k + Rcard k) := by
          rw [hsum_R_rev]; simp only [Finset.sum_add_distrib]; ring
      _ ≤ ∑ k ∈ Icc 1 (n - 1), (D.T k).card := by
          apply sum_le_sum; intro k hk; rw [mem_Icc] at hk
          dsimp only [Lcard, Mcard, Rcard]; simp only [dif_pos hk]; exact hT_split k hk.1 hk.2
  have hfin : ∑ t : Fin M, (D.r t - 1) ≤ 2 * M := by
    rw [← hsum_C]; exact hC_le_T.trans hsum_T
  have hr_sum : ∑ t : Fin M, D.r t ≤ (∑ t : Fin M, (D.r t - 1)) + M := by
    have hle : ∑ t : Fin M, D.r t ≤ ∑ t : Fin M, ((D.r t - 1) + 1) :=
      sum_le_sum fun t _ => by omega
    simpa [Finset.sum_add_distrib] using hle
  omega

end SweepData

/- ### Part 2: Duality from `s : Finset ℝ²` to the sweep-line configuration -/

/-- A finite collection of lines in `ℝ²` does not cover `ℝ²`. -/
private lemma exists_not_mem_lines (ℒ : Finset (AffineSubspace ℝ ℝ²))
    (hL : ∀ L ∈ ℒ, IsLine L) : ∃ p₀ : ℝ², ∀ L ∈ ℒ, p₀ ∉ L := by
  let vec : ℝ → ℝ² := fun μ => WithLp.toLp 2 ![1, μ]
  let badSlope : Finset ℝ :=
    ℒ.biUnion fun L =>
      if h : ∃ μ : ℝ, vec μ ∈ L.direction then {Classical.choose h} else ∅
  obtain ⟨μ, hμ⟩ := Infinite.exists_notMem_finset badSlope
  have hu_not : ∀ L ∈ ℒ, vec μ ∉ L.direction := by
    intro L hLin huin
    have hex : ∃ μ' : ℝ, vec μ' ∈ L.direction := ⟨μ, huin⟩
    let μ' := Classical.choose hex
    have hμ'_in : vec μ' ∈ L.direction := Classical.choose_spec hex
    have hμ'_mem : μ' ∈ badSlope := by
      refine mem_biUnion.mpr ⟨L, hLin, ?_⟩
      rw [dif_pos hex]; exact mem_singleton_self _
    have hne : μ ≠ μ' := fun h => hμ (h ▸ hμ'_mem)
    have hdim : Module.finrank ℝ L.direction = 1 := hL L hLin
    let v : Fin 2 → L.direction := ![⟨vec μ, huin⟩, ⟨vec μ', hμ'_in⟩]
    have hv_li : LinearIndependent ℝ v := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have h0 : g 0 * 1 + g 1 * 1 = 0 := by
        have := congrFun (congrArg (fun x : L.direction => (x : ℝ²).ofLp) hg) 0
        simpa [v, vec, Fin.sum_univ_two] using this
      have h1 : g 0 * μ + g 1 * μ' = 0 := by
        have := congrFun (congrArg (fun x : L.direction => (x : ℝ²).ofLp) hg) 1
        simpa [v, vec, Fin.sum_univ_two] using this
      have hmul : g 1 * (μ' - μ) = 0 := by linear_combination h1 - μ * h0
      have hg1 : g 1 = 0 := (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hne.symm)
      have hg0 : g 0 = 0 := by linarith
      intro i; fin_cases i <;> assumption
    have hle : 2 ≤ Module.finrank ℝ L.direction := by
      simpa using hv_li.fintype_card_le_finrank
    omega
  let badT : Finset ℝ :=
    ℒ.biUnion fun L =>
      if h : ∃ t : ℝ, t • vec μ ∈ L then {Classical.choose h} else ∅
  obtain ⟨t₀, ht₀⟩ := Infinite.exists_notMem_finset badT
  refine ⟨t₀ • vec μ, fun L hLin ht₀in => ?_⟩
  have hex : ∃ t : ℝ, t • vec μ ∈ L := ⟨t₀, ht₀in⟩
  let t₁ := Classical.choose hex
  have ht1_in : t₁ • vec μ ∈ L := Classical.choose_spec hex
  have ht1_mem : t₁ ∈ badT := by
    refine mem_biUnion.mpr ⟨L, hLin, ?_⟩
    rw [dif_pos hex]; exact mem_singleton_self _
  have hne : t₀ ≠ t₁ := fun h => ht₀ (h ▸ ht1_mem)
  have hvsub : (t₀ - t₁) • vec μ ∈ L.direction := by
    have := AffineSubspace.vsub_mem_direction ht₀in ht1_in
    rwa [vsub_eq_sub, ← sub_smul] at this
  have hu_in : vec μ ∈ L.direction := by
    have := L.direction.smul_mem (t₀ - t₁)⁻¹ hvsub
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at this
  exact hu_not L hLin hu_in

/-- Every line `L ∈ determinedLines s` is indeed a line (`IsLine L`). -/
private lemma isLine_of_mem_determinedLines {s : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ determinedLines s) : IsLine L := by
  rw [determinedLines, mem_image] at hL
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hL
  have hne : p ≠ q := (mem_offDiag.mp hpq).2.2
  rw [IsLine, direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr hne)

/-- Main theorem: Melchior's inequality `∑ L ∈ determinedLines s, |s ∩ L| ≤ 3 * |determinedLines s|`. -/
theorem melchior_mean_multiplicity (s : Finset ℝ²) (hs : 2 ≤ s.card)
    (hnc : ∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card < s.card) :
    (∑ L ∈ determinedLines s, ((s.filter fun p => p ∈ L).card : ℝ)) ≤
      3 * ((determinedLines s).card : ℝ) := by
  obtain ⟨p₀, hp₀⟩ := exists_not_mem_lines (determinedLines s)
    (fun L hL => isLine_of_mem_determinedLines hL)
  let s₁ : Finset ℝ² := s.image (fun p => p - p₀)
  have hs₁_card : s₁.card = s.card :=
    card_image_of_injective s (fun a b h => sub_left_injective h)
  let tr : ℝ² ≃ᵃ[ℝ] ℝ² := AffineEquiv.constVAdd ℝ ℝ² (-p₀)
  have htr_apply : ∀ p : ℝ², tr p = p - p₀ := fun p => by simp [tr, sub_eq_add_neg, add_comm]
  have hs₁_eq : s₁ = s.image tr := by ext x; simp [s₁, htr_apply]
  have hlines_eq : determinedLines s₁ = (determinedLines s).image (AffineSubspace.map tr.toAffineMap) := by
    ext L
    simp only [determinedLines, hs₁_eq, mem_image, mem_offDiag]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩, hab⟩, rfl⟩
      have hpq : p ≠ q := fun h => hab (h ▸ rfl)
      refine ⟨line[ℝ, p, q], ⟨(p, q), ⟨hp, hq, hpq⟩, rfl⟩, ?_⟩
      simp [AffineSubspace.map_span, Set.image_pair]
    · rintro ⟨L₀, ⟨⟨p, q⟩, ⟨hp, hq, hpq⟩, rfl⟩, rfl⟩
      refine ⟨(tr p, tr q), ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩, tr.injective.ne hpq⟩, ?_⟩
      simp [AffineSubspace.map_span, Set.image_pair]
  have hmap_inj : Function.Injective (AffineSubspace.map tr.toAffineMap) := by
    intro L₁ L₂ h
    ext x
    have := congrArg (fun M : AffineSubspace ℝ ℝ² => tr x ∈ M) h
    simpa [AffineSubspace.mem_map_iff_mem_of_injective (f := tr.toAffineMap) tr.injective] using this
  have hcard_lines : (determinedLines s₁).card = (determinedLines s).card := by
    rw [hlines_eq, card_image_of_injective _ hmap_inj]
  have hsum_lines : (∑ L ∈ determinedLines s₁, (s₁.filter fun p => p ∈ L).card) =
      ∑ L ∈ determinedLines s, (s.filter fun p => p ∈ L).card := by
    rw [hlines_eq, sum_image (fun _ _ _ _ h => hmap_inj h)]
    apply sum_congr rfl; intro L _
    rw [hs₁_eq]
    have hfilt : (s.image tr).filter (fun p => p ∈ L.map tr.toAffineMap) =
        (s.filter fun p => p ∈ L).image tr := by
      ext y; simp only [mem_filter, mem_image]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hy⟩
        exact ⟨x, ⟨hx, (AffineSubspace.mem_map_iff_mem_of_injective (f := tr.toAffineMap) tr.injective).mp hy⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hxL⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, AffineSubspace.mem_map_of_mem _ hxL⟩
    rw [hfilt, card_image_of_injective _ tr.injective]
  suffices hnat : (∑ L ∈ determinedLines s₁, (s₁.filter fun p => p ∈ L).card) ≤
      3 * (determinedLines s₁).card by
    rw [hsum_lines, hcard_lines] at hnat
    exact_mod_cast hnat
  have hzero_not_mem : ∀ L ∈ determinedLines s₁, (0 : ℝ²) ∉ L := by
    intro L hL h0
    rw [hlines_eq, mem_image] at hL
    obtain ⟨L₀, hL₀, rfl⟩ := hL
    have htrp₀ : tr.toAffineMap p₀ = 0 := by change tr p₀ = 0; rw [htr_apply, sub_self]
    rw [← htrp₀, AffineSubspace.mem_map_iff_mem_of_injective (f := tr.toAffineMap) tr.injective] at h0
    exact hp₀ L₀ hL₀ h0
  have hnc₁ : ∀ L : AffineSubspace ℝ ℝ², IsLine L → (s₁.filter fun p => p ∈ L).card < s₁.card := by
    intro L hL
    let L₀ := L.map tr.symm.toAffineMap
    have hL₀ : IsLine L₀ := by
      rw [IsLine, AffineSubspace.map_direction]
      exact (Submodule.equivMapOfInjective tr.symm.linear.toLinearMap tr.symm.linear.injective L.direction).symm.finrank_eq.trans hL
    have hfilt : (s₁.filter fun p => p ∈ L).card = (s.filter fun p => p ∈ L₀).card := by
      rw [hs₁_eq]
      have : (s.image tr).filter (fun p => p ∈ L) = (s.filter fun p => p ∈ L₀).image tr := by
        ext y; simp only [mem_filter, mem_image]
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, hy⟩
          exact ⟨x, ⟨hx, ⟨tr x, hy, by simp⟩⟩, rfl⟩
        · rintro ⟨x, ⟨hx, hxL₀⟩, rfl⟩
          obtain ⟨z, hz, hzx⟩ := hxL₀
          have : tr x = z := by rw [← hzx]; simp
          exact ⟨⟨x, hx, rfl⟩, this.symm ▸ hz⟩
      rw [this, card_image_of_injective _ tr.injective]
    rw [hfilt, hs₁_card]
    exact hnc L₀ hL₀
  have hdet_ne : ∀ p ∈ s₁, ∀ q ∈ s₁, p ≠ q → p 0 * q 1 - p 1 * q 0 ≠ 0 := by
    intro p hp q hq hpq hdet
    have hLmem : line[ℝ, p, q] ∈ determinedLines s₁ :=
      mem_image.mpr ⟨(p, q), mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩
    have h0not := hzero_not_mem _ hLmem
    have hp0 : p ≠ 0 := fun h => h0not (h ▸ left_mem_affineSpan_pair ℝ p q)
    have hcomb : ∃ α : ℝ, (1 - α) • p + α • q = 0 := by
      by_cases hp00 : p 0 = 0
      · have hp1 : p 1 ≠ 0 := fun h => hp0 (by ext i; fin_cases i <;> simp [hp00, h])
        have hq00 : q 0 = 0 := by rw [hp00, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at hdet; exact hdet.resolve_left hp1
        have hqp : q 1 - p 1 ≠ 0 := fun h => hpq (by
          have hq1 : q 1 = p 1 := sub_eq_zero.mp h
          ext i; fin_cases i
          · simp [hp00, hq00]
          · simp [hq1])
        refine ⟨-p 1 / (q 1 - p 1), ?_⟩
        ext i; fin_cases i
        · simp [hp00, hq00]
        · change (1 - -p 1 / (q 1 - p 1)) * p 1 + (-p 1 / (q 1 - p 1)) * q 1 = 0
          apply mul_right_cancel₀ hqp
          have hmul : -p 1 / (q 1 - p 1) * (q 1 - p 1) = -p 1 := div_mul_cancel₀ _ hqp
          linear_combination (q 1 - p 1) * hmul
      · have hqp : q 0 - p 0 ≠ 0 := by
          intro h
          have hq0eq : q 0 = p 0 := by linarith
          have hq1eq : q 1 = p 1 := by
            have hmul : p 0 * (q 1 - p 1) = 0 := by linear_combination hdet + p 1 * hq0eq
            exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hp00)
          exact hpq (by
            ext i; fin_cases i
            · simp [hq0eq]
            · simp [hq1eq])
        refine ⟨-p 0 / (q 0 - p 0), ?_⟩
        ext i; fin_cases i
        · change (1 - -p 0 / (q 0 - p 0)) * p 0 + (-p 0 / (q 0 - p 0)) * q 0 = 0
          field_simp [hqp]; ring
        · change (1 - -p 0 / (q 0 - p 0)) * p 1 + (-p 0 / (q 0 - p 0)) * q 1 = 0
          field_simp [hqp]; nlinarith
    obtain ⟨α, hα⟩ := hcomb
    have h0in : (0 : ℝ²) ∈ line[ℝ, p, q] := by
      rw [← hα]
      have h1 : (1 - α) • p + α • q = AffineMap.lineMap p q α := by
        simp [AffineMap.lineMap_apply_module]
      rw [h1]
      exact AffineMap.lineMap_mem_affineSpan_pair α p q
    exact h0not h0in
  have hex_dual : ∀ L ∈ determinedLines s₁, ∃ v : ℝ²,
      ∀ x : ℝ², x ∈ L ↔ x 0 * v 0 + x 1 * v 1 = 1 := by
    intro L hL
    rw [determinedLines, mem_image] at hL
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hL
    obtain ⟨hp, hq, hne⟩ := mem_offDiag.mp hpq
    have hdet : p 0 * q 1 - p 1 * q 0 ≠ 0 := hdet_ne p hp q hq hne
    let v : ℝ² := WithLp.toLp 2 ![(q 1 - p 1) / (p 0 * q 1 - p 1 * q 0), (p 0 - q 0) / (p 0 * q 1 - p 1 * q 0)]
    have hv0 : v 0 = (q 1 - p 1) / (p 0 * q 1 - p 1 * q 0) := rfl
    have hv1 : v 1 = (p 0 - q 0) / (p 0 * q 1 - p 1 * q 0) := rfl
    have hpv : p 0 * v 0 + p 1 * v 1 = 1 := by
      rw [hv0, hv1, mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hdet]; ring
    have hqv : q 0 * v 0 + q 1 * v 1 = 1 := by
      rw [hv0, hv1, mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hdet]; ring
    refine ⟨v, fun x => ?_⟩
    constructor
    · intro hx
      have hvs := AffineSubspace.vsub_mem_direction hx (left_mem_affineSpan_pair ℝ p q)
      rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_span_singleton] at hvs
      obtain ⟨t, ht⟩ := hvs
      have hx0 : x 0 - p 0 = t * (p 0 - q 0) := by
        have := congrArg (fun z : ℝ² => z 0) ht; simpa [vsub_eq_sub] using this.symm
      have hx1 : x 1 - p 1 = t * (p 1 - q 1) := by
        have := congrArg (fun z : ℝ² => z 1) ht; simpa [vsub_eq_sub] using this.symm
      linear_combination v 0 * hx0 + v 1 * hx1 + (1 + t) * hpv - t * hqv
    · intro hxv
      let t := (x 0 * p 1 - x 1 * p 0) / (q 0 * p 1 - q 1 * p 0)
      have hdet' : q 0 * p 1 - q 1 * p 0 ≠ 0 := by intro h; exact hdet (by linarith)
      have hrel : x 0 * (q 1 - p 1) + x 1 * (p 0 - q 0) = p 0 * q 1 - p 1 * q 0 := by
        rw [hv0, hv1, mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hdet] at hxv
        linarith
      have ht_mul : t * (q 0 * p 1 - q 1 * p 0) = x 0 * p 1 - x 1 * p 0 :=
        div_mul_cancel₀ _ hdet'
      have hx_eq : AffineMap.lineMap p q t = x := by
        rw [AffineMap.lineMap_apply_module]
        ext i; fin_cases i
        · change (1 - t) * p 0 + t * q 0 = x 0
          apply mul_right_cancel₀ hdet'
          linear_combination (q 0 - p 0) * ht_mul + p 0 * hrel
        · change (1 - t) * p 1 + t * q 1 = x 1
          apply mul_right_cancel₀ hdet'
          linear_combination (q 1 - p 1) * ht_mul + p 1 * hrel
      rw [← hx_eq]
      exact AffineMap.lineMap_mem_affineSpan_pair t p q
  let dualV : AffineSubspace ℝ ℝ² → ℝ² := fun L =>
    if h : L ∈ determinedLines s₁ then Classical.choose (hex_dual L h) else 0
  have hdual_spec : ∀ L ∈ determinedLines s₁, ∀ x : ℝ²,
      x ∈ L ↔ x 0 * (dualV L) 0 + x 1 * (dualV L) 1 = 1 := by
    intro L hL x; dsimp only [dualV]; rw [dif_pos hL]
    exact Classical.choose_spec (hex_dual L hL) x
  have hdual_inj : Set.InjOn dualV (determinedLines s₁ : Set (AffineSubspace ℝ ℝ²)) := by
    intro L₁ hL₁ L₂ hL₂ heq; ext x
    rw [hdual_spec L₁ hL₁ x, hdual_spec L₂ hL₂ x, heq]
  let bad1 : Finset ℝ := s₁.image fun p => p 1 / p 0
  let bad2 : Finset ℝ := (determinedLines s₁).offDiag.image fun P =>
    ((dualV P.1) 0 - (dualV P.2) 0) / ((dualV P.2) 1 - (dualV P.1) 1)
  obtain ⟨lam, hlam⟩ := Infinite.exists_notMem_finset (bad1 ∪ bad2)
  have hlam1 : ∀ p ∈ s₁, p 1 - lam * p 0 ≠ 0 := by
    intro p hp h0
    by_cases hp0 : p 0 = 0
    · have hp1 : p 1 = 0 := by rw [hp0, mul_zero, sub_zero] at h0; exact h0
      have : p = 0 := by
        ext i; fin_cases i
        · simp [hp0]
        · simp [hp1]
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s₁.card)
      obtain ⟨q, hq, hpq⟩ : ∃ q ∈ s₁, p ≠ q :=
        if hpa : p = a then ⟨b, hb, fun h => hab (hpa.symm.trans h)⟩
        else ⟨a, ha, hpa⟩
      have hLm : line[ℝ, p, q] ∈ determinedLines s₁ :=
        mem_image.mpr ⟨(p, q), mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩
      exact hzero_not_mem _ hLm (this ▸ left_mem_affineSpan_pair ℝ p q)
    · have hlameq : lam = p 1 / p 0 := by field_simp [hp0]; linarith
      exact hlam (mem_union_left _ (mem_image.mpr ⟨p, hp, hlameq.symm⟩))
  have hlam2 : ∀ L₁ ∈ determinedLines s₁, ∀ L₂ ∈ determinedLines s₁, L₁ ≠ L₂ →
      (dualV L₁) 0 + lam * (dualV L₁) 1 ≠ (dualV L₂) 0 + lam * (dualV L₂) 1 := by
    intro L₁ hL₁ L₂ hL₂ hne heq
    by_cases hy : (dualV L₂) 1 - (dualV L₁) 1 = 0
    · have hy' : (dualV L₁) 1 = (dualV L₂) 1 := by linarith
      have hx' : (dualV L₁) 0 = (dualV L₂) 0 := by rw [hy'] at heq; linarith
      have hv_eq : dualV L₁ = dualV L₂ := by
        ext i; fin_cases i
        · simp [hx']
        · simp [hy']
      exact hne (hdual_inj hL₁ hL₂ hv_eq)
    · have hlameq : lam = ((dualV L₁) 0 - (dualV L₂) 0) / ((dualV L₂) 1 - (dualV L₁) 1) := by
        field_simp [hy]; linarith
      exact hlam (mem_union_right _ (mem_image.mpr ⟨(L₁, L₂), mem_offDiag.mpr ⟨hL₁, hL₂, hne⟩, hlameq.symm⟩))
  let slope : ℝ² → ℝ := fun p => -p 0 / (p 1 - lam * p 0)
  let yint : ℝ² → ℝ := fun p => 1 / (p 1 - lam * p 0)
  let vx : AffineSubspace ℝ ℝ² → ℝ := fun L => (dualV L) 0 + lam * (dualV L) 1
  let vy : AffineSubspace ℝ ℝ² → ℝ := fun L => (dualV L) 1
  have hinc_iff : ∀ p ∈ s₁, ∀ L ∈ determinedLines s₁,
      p ∈ L ↔ slope p * vx L + yint p = vy L := by
    intro p hp L hL
    rw [hdual_spec L hL p]
    have hden : p 1 - lam * p 0 ≠ 0 := hlam1 p hp
    dsimp only [slope, yint, vx, vy]
    rw [div_mul_eq_mul_div, ← add_div, div_eq_iff hden]
    constructor <;> intro h <;> linear_combination -h
  have hslope_inj : Set.InjOn slope (s₁ : Set ℝ²) := by
    intro p hp q hq heq
    by_contra hne
    have hdp : p 1 - lam * p 0 ≠ 0 := hlam1 p hp
    have hdq : q 1 - lam * q 0 ≠ 0 := hlam1 q hq
    dsimp only [slope] at heq
    rw [div_eq_div_iff hdp hdq] at heq
    exact hdet_ne p hp q hq hne (by linear_combination -heq)
  let n := s₁.card
  let M := (determinedLines s₁).card
  have hM_pos : 0 < M := by
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < s₁.card)
    exact Finset.card_pos.mpr ⟨line[ℝ, p, q], mem_image.mpr ⟨(p, q), mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩⟩
  let eS : Fin n ≃o (s₁.image slope) :=
    (s₁.image slope).orderIsoOfFin (card_image_of_injOn hslope_inj)
  have hvx_inj : Set.InjOn vx (determinedLines s₁ : Set (AffineSubspace ℝ ℝ²)) :=
    fun L₁ hL₁ L₂ hL₂ h => by_contra fun hne => hlam2 L₁ hL₁ L₂ hL₂ hne h
  let eL : Fin M ≃o ((determinedLines s₁).image vx) :=
    ((determinedLines s₁).image vx).orderIsoOfFin (card_image_of_injOn hvx_inj)
  let pt : Fin n → ℝ² := fun i => Classical.choose (mem_image.mp (eS i).2)
  have hpt_mem : ∀ i : Fin n, pt i ∈ s₁ := fun i => (Classical.choose_spec (mem_image.mp (eS i).2)).1
  have hpt_slope : ∀ i : Fin n, slope (pt i) = (eS i).1 := fun i =>
    (Classical.choose_spec (mem_image.mp (eS i).2)).2
  have hpt_inj : Function.Injective pt := fun i j h => by
    apply eS.injective; apply Subtype.ext; rw [← hpt_slope i, ← hpt_slope j, h]
  have hpt_surj : ∀ p ∈ s₁, ∃ i : Fin n, pt i = p := by
    intro p hp
    let i := eS.symm ⟨slope p, mem_image_of_mem slope hp⟩
    refine ⟨i, hslope_inj (hpt_mem i) hp ?_⟩
    rw [hpt_slope i]; simp [i]
  let ln : Fin M → AffineSubspace ℝ ℝ² := fun t => Classical.choose (mem_image.mp (eL t).2)
  have hln_mem : ∀ t : Fin M, ln t ∈ determinedLines s₁ := fun t =>
    (Classical.choose_spec (mem_image.mp (eL t).2)).1
  have hln_vx : ∀ t : Fin M, vx (ln t) = (eL t).1 := fun t =>
    (Classical.choose_spec (mem_image.mp (eL t).2)).2
  have hln_inj : Function.Injective ln := fun t₁ t₂ h => by
    apply eL.injective; apply Subtype.ext; rw [← hln_vx t₁, ← hln_vx t₂, h]
  have hln_surj : ∀ L ∈ determinedLines s₁, ∃ t : Fin M, ln t = L := by
    intro L hL
    let t := eL.symm ⟨vx L, mem_image_of_mem vx hL⟩
    refine ⟨t, hvx_inj (hln_mem t) hL ?_⟩
    rw [hln_vx t]; simp [t]
  let D : SweepData n M := {
    m := fun i => slope (pt i)
    c := fun i => yint (pt i)
    hm := fun i j hij => by dsimp only; rw [hpt_slope i, hpt_slope j]; exact eS.strictMono hij
    v := fun t => (vx (ln t), vy (ln t))
    hv := fun t₁ t₂ hlt => by dsimp only; rw [hln_vx t₁, hln_vx t₂]; exact eL.strictMono hlt
    hM := hM_pos
    hpair := fun i j hij => by
      have hne : pt i ≠ pt j := hpt_inj.ne hij
      have hLm : line[ℝ, pt i, pt j] ∈ determinedLines s₁ :=
        mem_image.mpr ⟨(pt i, pt j), mem_offDiag.mpr ⟨hpt_mem i, hpt_mem j, hne⟩, rfl⟩
      obtain ⟨t, ht⟩ := hln_surj _ hLm
      refine ⟨t, ?_, ?_⟩
      · exact (hinc_iff (pt i) (hpt_mem i) (ln t) (hln_mem t)).mp
          (ht.symm ▸ left_mem_affineSpan_pair ℝ (pt i) (pt j))
      · exact (hinc_iff (pt j) (hpt_mem j) (ln t) (hln_mem t)).mp
          (ht.symm ▸ right_mem_affineSpan_pair ℝ (pt i) (pt j))
    hnc := fun t => by
      have hcard_eq : (univ.filter fun i : Fin n => slope (pt i) * vx (ln t) + yint (pt i) = vy (ln t)).card =
          (s₁.filter fun p => p ∈ ln t).card := by
        apply Finset.card_bij (fun i _ => pt i)
        · intro i hi
          exact mem_filter.mpr ⟨hpt_mem i,
            (hinc_iff (pt i) (hpt_mem i) (ln t) (hln_mem t)).mpr (mem_filter.mp hi).2⟩
        · intro i _ j _ h; exact hpt_inj h
        · intro p hp
          obtain ⟨i, rfl⟩ := hpt_surj p (mem_filter.mp hp).1
          exact ⟨i, mem_filter.mpr ⟨mem_univ i,
            (hinc_iff (pt i) (hpt_mem i) (ln t) (hln_mem t)).mp (mem_filter.mp hp).2⟩, rfl⟩
      rw [hcard_eq]
      exact hnc₁ (ln t) (isLine_of_mem_determinedLines (hln_mem t))
  }
  have hsum_eq : (∑ L ∈ determinedLines s₁, (s₁.filter fun p => p ∈ L).card) =
      ∑ t : Fin M, D.r t := by
    symm
    apply Finset.sum_bij (fun t _ => ln t)
    · intro t _; exact hln_mem t
    · intro t₁ _ t₂ _ h; exact hln_inj h
    · intro L hL; obtain ⟨t, rfl⟩ := hln_surj L hL; exact ⟨t, mem_univ t, rfl⟩
    · intro t _
      apply Finset.card_bij (fun i _ => pt i)
      · intro i hi
        exact mem_filter.mpr ⟨hpt_mem i,
          (hinc_iff (pt i) (hpt_mem i) (ln t) (hln_mem t)).mpr (mem_filter.mp hi).2⟩
      · intro i _ j _ h; exact hpt_inj h
      · intro p hp
        obtain ⟨i, rfl⟩ := hpt_surj p (mem_filter.mp hp).1
        exact ⟨i, mem_filter.mpr ⟨mem_univ i,
          (hinc_iff (pt i) (hpt_mem i) (ln t) (hln_mem t)).mp (mem_filter.mp hp).2⟩, rfl⟩
  rw [hsum_eq]
  exact D.sum_r_le_three_M

end

end OMA.MelchiorSweep

theorem OMA.solution : OMA.R_Erdos211_erdos_211_variants_one_sixth_R1.H2 :=
  OMA.MelchiorSweep.melchior_mean_multiplicity