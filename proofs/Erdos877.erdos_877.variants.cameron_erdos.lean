import FormalConjectures.ErdosProblems.«877»

-- Problem: Erdős Problem 877 — cameron erdos
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/877.lean:83 (declaration Erdos877.erdos_877.variants.cameron_erdos)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

namespace OMA.W15
open Erdos877

def base (e : ℕ) (T : Finset ℕ) : Finset ℕ :=
  insert (2 * e) ((T.image fun i => 2 * i + 1) ∪
    (((Finset.range (e / 2)) \ T).image fun i => 2 * e - (2 * i + 1)))

lemma mem_base {e : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range (e / 2)) {y : ℕ} :
    y ∈ base e T ↔ y = 2 * e ∨ (∃ i, i < e / 2 ∧ i ∈ T ∧ 2 * i + 1 = y) ∨
      (∃ i, i < e / 2 ∧ i ∉ T ∧ 2 * e - (2 * i + 1) = y) := by
  simp only [base, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff,
    Finset.mem_range]
  constructor
  · rintro (h | ⟨i, hi, h⟩ | ⟨i, ⟨hi, hiT⟩, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, Finset.mem_range.1 (hT hi), hi, h⟩)
    · exact Or.inr (Or.inr ⟨i, hi, hiT, h⟩)
  · rintro (h | ⟨i, -, hi, h⟩ | ⟨i, hi, hiT, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, hi, h⟩)
    · exact Or.inr (Or.inr ⟨i, ⟨hi, hiT⟩, h⟩)

lemma base_sumFree {e : ℕ} (he : 1 ≤ e) {T : Finset ℕ} (hT : T ⊆ Finset.range (e / 2)) :
    IsSumFree (base e T : Set ℕ) := by
  rw [isSumFree_iff]
  intro x hx y hy hxy
  simp only [Finset.mem_coe, mem_base hT] at hx hy hxy
  rcases hx with rfl | ⟨i, hi, hiT, rfl⟩ | ⟨i, hi, hiT, rfl⟩ <;>
  rcases hy with rfl | ⟨j, hj, hjT, rfl⟩ | ⟨j, hj, hjT, rfl⟩ <;>
  rcases hxy with h | ⟨k, hk, hkT, h⟩ | ⟨k, hk, hkT, h⟩ <;>
  first
  | omega
  | (obtain rfl : i = j := by omega
     contradiction)

lemma base_sub {n e : ℕ} (he : 1 ≤ e) (hn : 2 * e ≤ n) {T : Finset ℕ}
    (hT : T ⊆ Finset.range (e / 2)) : base e T ⊆ Finset.Icc 1 n := by
  intro y hy
  rw [mem_base hT] at hy
  rw [Finset.mem_Icc]
  rcases hy with rfl | ⟨i, hi, -, rfl⟩ | ⟨i, hi, -, rfl⟩ <;> omega

lemma exists_max (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hs : IsSumFree (A : Set ℕ)) : ∃ M, IsMaximalSumFree n M ∧ A ⊆ M := by
  classical
  let F := (Finset.Icc 1 n).powerset.filter fun B : Finset ℕ => IsSumFree (B : Set ℕ) ∧ A ⊆ B
  have hne : F.Nonempty := ⟨A, by simp [F, hA, hs]⟩
  obtain ⟨M, hMF, hmax⟩ := F.exists_max_image Finset.card hne
  simp only [F, Finset.mem_filter, Finset.mem_powerset] at hMF
  refine ⟨M, ⟨hMF.1, hMF.2.1, fun B hB hBs hMB => ?_⟩, hMF.2.2⟩
  have hBF : B ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hB, hBs, hMF.2.2.trans hMB⟩
  exact Finset.eq_of_subset_of_card_le hMB (hmax B hBF)

open Classical in
noncomputable def ext (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  if h : A ⊆ Finset.Icc 1 n ∧ IsSumFree (A : Set ℕ) then
    Classical.choose (exists_max n A h.1 h.2) else A

lemma ext_spec {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n)
    (hs : IsSumFree (A : Set ℕ)) : IsMaximalSumFree n (ext n A) ∧ A ⊆ ext n A := by
  rw [ext, dif_pos ⟨hA, hs⟩]
  exact Classical.choose_spec (exists_max n A hA hs)

/-- recovering the choice -/
lemma recover {e : ℕ} {T M : Finset ℕ} (hT : T ⊆ Finset.range (e / 2)) (hM : base e T ⊆ M)
    (hs : IsSumFree (M : Set ℕ)) {i : ℕ} (hi : i < e / 2) : 2 * i + 1 ∈ M ↔ i ∈ T := by
  constructor
  · intro h
    by_contra hiT
    have h2 : 2 * e - (2 * i + 1) ∈ M := hM ((mem_base hT).2 (Or.inr (Or.inr ⟨i, hi, hiT, rfl⟩)))
    have h3 : 2 * e ∈ M := hM ((mem_base hT).2 (Or.inl rfl))
    have := (isSumFree_iff.1 hs) _ h _ h2
    rw [show 2 * i + 1 + (2 * e - (2 * i + 1)) = 2 * e by omega] at this
    exact this h3
  · intro h
    exact hM ((mem_base hT).2 (Or.inr (Or.inl ⟨i, hi, h, rfl⟩)))

noncomputable def fam (n e : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (e / 2)).powerset.image fun T => ext n (base e T)

lemma fam_sub {n e : ℕ} (he : 1 ≤ e) (hn : 2 * e ≤ n) {M : Finset ℕ} (hM : M ∈ fam n e) :
    IsMaximalSumFree n M := by
  simp only [fam, Finset.mem_image, Finset.mem_powerset] at hM
  obtain ⟨T, hT, rfl⟩ := hM
  exact (ext_spec (base_sub he hn hT) (base_sumFree he hT)).1

lemma card_fam {n e : ℕ} (he : 1 ≤ e) (hn : 2 * e ≤ n) : (fam n e).card = 2 ^ (e / 2) := by
  rw [fam, Finset.card_image_of_injOn, Finset.card_powerset, Finset.card_range]
  intro T hT T' hT' hTT
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset] at hT hT'
  simp only at hTT
  have h1 := ext_spec (base_sub he hn hT) (base_sumFree he hT)
  have h2 := ext_spec (base_sub he hn hT') (base_sumFree he hT')
  ext i
  by_cases hi : i < e / 2
  · rw [← recover hT h1.2 h1.1.2.1 hi, ← recover hT' h2.2 h2.1.2.1 hi, hTT]
  · constructor
    · intro h; exact absurd (Finset.mem_range.1 (hT h)) hi
    · intro h; exact absurd (Finset.mem_range.1 (hT' h)) hi

lemma upset_eq {p : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range p)
    (hup : ∀ i < p, i ∉ T → i - 1 ∉ T) :
    ∃ k ∈ Finset.range (p + 1), T = Finset.Ico k p := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨p, Finset.mem_range.2 (Nat.lt_succ_self p), by simp⟩
  · refine ⟨T.min' hne, ?_, ?_⟩
    · have := Finset.mem_range.1 (hT (T.min'_mem hne)); exact Finset.mem_range.2 (by omega)
    · ext j
      rw [Finset.mem_Ico]
      constructor
      · intro hj
        exact ⟨T.min'_le j hj, Finset.mem_range.1 (hT hj)⟩
      · rintro ⟨h1, h2⟩
        by_contra hj
        have key : ∀ d, j - d ∉ T := by
          intro d
          induction d with
          | zero => simpa using hj
          | succ d ih =>
            have := hup (j - d) (by omega) ih
            rwa [show j - d - 1 = j - (d + 1) by omega] at this
        have := key (j - T.min' hne)
        rw [show j - (j - T.min' hne) = T.min' hne by omega] at this
        exact this (T.min'_mem hne)

lemma overlap {n e : ℕ} (he : 2 ≤ e) (hn : 2 * e ≤ n) :
    fam n e ∩ fam n (e - 1) ⊆
      ((Finset.range (e / 2 + 1)).image fun k => Finset.Ico k (e / 2)).image
        fun T => ext n (base e T) := by
  intro M hM
  rw [Finset.mem_inter] at hM
  obtain ⟨hA, hB⟩ := hM
  simp only [fam, Finset.mem_image, Finset.mem_powerset] at hA hB
  obtain ⟨T, hT, rfl⟩ := hA
  obtain ⟨T', hT', hTT'⟩ := hB
  have h1 := ext_spec (base_sub (by omega) hn hT) (base_sumFree (by omega) hT)
  have h2 := ext_spec (base_sub (n := n) (e := e - 1) (by omega) (by omega) hT') (base_sumFree (by omega) hT')
  have hE2 : 2 * (e - 1) ∈ ext n (base e T) := by
    rw [← hTT']; exact h2.2 ((mem_base hT').2 (Or.inl rfl))
  have hs := h1.1.2.1
  have hup : ∀ i < e / 2, i ∉ T → i - 1 ∉ T := by
    intro i hi hiT hi1
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact hiT hi1
    have ha : 2 * e - (2 * i + 1) ∈ ext n (base e T) :=
      h1.2 ((mem_base hT).2 (Or.inr (Or.inr ⟨i, hi, hiT, rfl⟩)))
    have hb : 2 * (i - 1) + 1 ∈ ext n (base e T) :=
      h1.2 ((mem_base hT).2 (Or.inr (Or.inl ⟨i - 1, by omega, hi1, rfl⟩)))
    have := (isSumFree_iff.1 hs) _ hb _ ha
    rw [show 2 * (i - 1) + 1 + (2 * e - (2 * i + 1)) = 2 * (e - 1) by omega] at this
    exact this hE2
  obtain ⟨k, hk, rfl⟩ := upset_eq hT hup
  simp only [Finset.mem_image]
  exact ⟨Finset.Ico k (e / 2), ⟨k, hk, rfl⟩, rfl⟩

lemma count (n : ℕ) (hn : 4 ≤ n) :
    2 ^ (n / 2 / 2) + 2 ^ ((n / 2 - 1) / 2) ≤ fm n + (n / 2 / 2 + 1) := by
  classical
  set e := n / 2 with he_def
  have he : 2 ≤ e := by omega
  have hn1 : 2 * e ≤ n := by omega
  have hn2 : 2 * (e - 1) ≤ n := by omega
  have hsub : fam n e ∪ fam n (e - 1) ⊆
      (Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsMaximalSumFree n A := by
    intro M hM
    rw [Finset.mem_filter, Finset.mem_powerset]
    rcases Finset.mem_union.1 hM with h | h
    · have := fam_sub (by omega) hn1 h; exact ⟨this.1, this⟩
    · have := fam_sub (by omega) hn2 h; exact ⟨this.1, this⟩
  have hcard := Finset.card_union_add_card_inter (fam n e) (fam n (e - 1))
  rw [card_fam (by omega) hn1, card_fam (by omega) hn2] at hcard
  have hov : (fam n e ∩ fam n (e - 1)).card ≤ e / 2 + 1 := by
    refine (Finset.card_le_card (overlap he hn1)).trans ?_
    refine Finset.card_image_le.trans (Finset.card_image_le.trans ?_)
    simp
  have hfm : (fam n e ∪ fam n (e - 1)).card ≤ fm n := by
    unfold fm
    convert Finset.card_le_card hsub
  omega

lemma nat_aux1 (q : ℕ) (hq : 4 ≤ q) : 10 * (q + 2) < 6 * 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih => rw [pow_succ]; omega

lemma nat_aux2 (m : ℕ) (hm : 5 ≤ m) : 10 * (m + 1) < 3 * 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

lemma rpow_bound (n k : ℕ) (r : ℝ) (h : (n : ℝ) ≤ 4 * k + r) :
    (2 : ℝ) ^ ((n : ℝ) / 4) ≤ 2 ^ k * (2 : ℝ) ^ (r / 4) := by
  calc (2 : ℝ) ^ ((n : ℝ) / 4) ≤ (2 : ℝ) ^ ((k : ℝ) + r / 4) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 ^ k * (2 : ℝ) ^ (r / 4) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast]

lemma two_quarter : (2 : ℝ) ^ ((1 : ℝ) / 4) < 1.2 := by
  have h4 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 2 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  by_contra hc
  push Not at hc
  have := pow_le_pow_left₀ (by norm_num) hc 4
  rw [h4] at this
  norm_num at this

lemma two_three_quarter : (2 : ℝ) ^ ((3 : ℝ) / 4) < 1.7 := by
  have h4 : ((2 : ℝ) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) = 8 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
  by_contra hc
  push Not at hc
  have := pow_le_pow_left₀ (by norm_num) hc 4
  rw [h4] at this
  norm_num at this

theorem main : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) / 4) < fm n := by
  rw [eventually_atTop]
  refine ⟨40, fun n hn => ?_⟩
  have hc := count n (by omega)
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4 * m + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have hm : 10 ≤ m := by omega
  rcases (show r ≤ 1 ∨ 2 ≤ r by omega) with hr1 | hr2
  · -- e = 2m, p1 = m, p2 = m - 1
    have e1 : (4 * m + r) / 2 / 2 = m := by omega
    have e2 : ((4 * m + r) / 2 - 1) / 2 = m - 1 := by omega
    rw [e1, e2] at hc
    obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hc
    have ha := nat_aux1 q (by omega)
    have hr1' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
    have hb := rpow_bound (4 * (q + 1) + r) (q + 1) 1 (by push_cast; linarith)
    have hq := two_quarter
    have hcR : ((2 : ℝ) ^ (q + 1) + 2 ^ q) ≤ fm (4 * (q + 1) + r) + (q + 1 + 1) := by exact_mod_cast hc
    have haR : (10 : ℝ) * (q + 2) < 6 * 2 ^ q := by exact_mod_cast ha
    have hpos : (0 : ℝ) < 2 ^ (q + 1) := by positivity
    rw [pow_succ] at hcR hb hpos
    nlinarith
  · -- e = 2m + 1, p1 = m, p2 = m
    have e1 : (4 * m + r) / 2 / 2 = m := by omega
    have e2 : ((4 * m + r) / 2 - 1) / 2 = m := by omega
    rw [e1, e2] at hc
    have ha := nat_aux2 m (by omega)
    have hr3 : (r : ℝ) ≤ 3 := by exact_mod_cast (show r ≤ 3 by omega)
    have hb := rpow_bound (4 * m + r) m 3 (by push_cast; linarith)
    have hq := two_three_quarter
    have hcR : ((2 : ℝ) ^ m + 2 ^ m) ≤ fm (4 * m + r) + (m + 1) := by exact_mod_cast hc
    have haR : (10 : ℝ) * (m + 1) < 3 * 2 ^ m := by exact_mod_cast ha
    have hpos : (0 : ℝ) < 2 ^ m := by positivity
    nlinarith

end OMA.W15

theorem OMA.solution : type_of% @Erdos877.erdos_877.variants.cameron_erdos := by
  exact OMA.W15.main
