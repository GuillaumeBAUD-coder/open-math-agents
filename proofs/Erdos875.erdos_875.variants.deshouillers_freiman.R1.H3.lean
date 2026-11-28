import OMAReductions.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1

open Finset

namespace E875H3

private lemma sum_min_le_sum {B : Finset ℕ} {m r : ℕ} (hm : B.card = m) (hr : r ≤ m)
    (T : Finset ℕ) (hTB : T ⊆ B) (hTr : T.card = r) :
    let e := B.orderIsoOfFin hm
    ∑ i ∈ Finset.range r, (if h : i < m then (e ⟨i, h⟩ : ℕ) else 0) ≤ ∑ x ∈ T, x := by
  dsimp only
  set e := B.orderIsoOfFin hm
  set eT := T.orderIsoOfFin hTr
  have hle : ∀ i : Fin r, (e ⟨i.1, by omega⟩ : ℕ) ≤ (eT i : ℕ) := by
    intro i
    let f : Fin r → ℕ := fun j => (e.symm ⟨(eT j : ℕ), hTB (eT j).2⟩).1
    have hf_strict : StrictMono f := fun j₁ j₂ hj =>
      e.symm.strictMono (show (⟨(eT j₁ : ℕ), hTB (eT j₁).2⟩ : B) < ⟨(eT j₂ : ℕ), hTB (eT j₂).2⟩ from eT.strictMono hj)
    have hge_nat : ∀ k (hk : k < r), k ≤ f ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have hlt : f ⟨k, by omega⟩ < f ⟨k + 1, hk⟩ :=
          hf_strict (Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))
        have hp := ih (by omega)
        omega
    have hge : ∀ j : Fin r, j.1 ≤ f j := fun j => hge_nat j.1 j.2
    have hmo := e.monotone (show (⟨i.1, by omega⟩ : Fin m) ≤ e.symm ⟨(eT i : ℕ), hTB (eT i).2⟩ from hge i)
    rw [e.apply_symm_apply] at hmo
    exact hmo
  have hsumT : ∑ x ∈ T, x = ∑ i : Fin r, (eT i : ℕ) := by
    rw [← Finset.sum_attach T (fun x => x)]
    symm; exact Finset.sum_equiv eT.toEquiv (by simp) (by simp)
  rw [hsumT, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [show i.1 < m by omega, ↓reduceDIte]
  exact hle i

private lemma sum_le_sum_max {B : Finset ℕ} {m r : ℕ} (hm : B.card = m) (hr : r ≤ m)
    (T : Finset ℕ) (hTB : T ⊆ B) (hTr : T.card = r) :
    let e := B.orderIsoOfFin hm
    ∑ x ∈ T, x ≤ ∑ i ∈ Finset.range r, (if h : m - r + i < m then (e ⟨m - r + i, h⟩ : ℕ) else 0) := by
  dsimp only
  set e := B.orderIsoOfFin hm
  set eT := T.orderIsoOfFin hTr
  have hle : ∀ i : Fin r, (eT i : ℕ) ≤ (e ⟨m - r + i.1, by omega⟩ : ℕ) := by
    intro i
    let f : Fin r → ℕ := fun j => (e.symm ⟨(eT j : ℕ), hTB (eT j).2⟩).1
    have hf_strict : StrictMono f := fun j₁ j₂ hj =>
      e.symm.strictMono (show (⟨(eT j₁ : ℕ), hTB (eT j₁).2⟩ : B) < ⟨(eT j₂ : ℕ), hTB (eT j₂).2⟩ from eT.strictMono hj)
    have hbound : ∀ (k : ℕ) (hk : k < r), f ⟨r - 1 - k, by omega⟩ ≤ m - 1 - k := by
      intro k
      induction k with
      | zero =>
        intro hk
        have hlt := (e.symm ⟨(eT ⟨r - 1 - 0, by omega⟩ : ℕ), hTB (eT _).2⟩).2
        change f ⟨r - 1 - 0, by omega⟩ < m at hlt
        omega
      | succ k ih =>
        intro hk
        have hlt : f ⟨r - 1 - (k + 1), by omega⟩ < f ⟨r - 1 - k, by omega⟩ :=
          hf_strict (by simp [Fin.lt_def]; omega)
        have hprev := ih (by omega)
        omega
    have hfi : f i ≤ m - r + i.1 := by
      have h1 := hbound (r - 1 - i.1) (by omega)
      have heq : (⟨r - 1 - (r - 1 - i.1), by omega⟩ : Fin r) = i := by ext; dsimp; omega
      rw [heq] at h1; omega
    have hmo := e.monotone (show e.symm ⟨(eT i : ℕ), hTB (eT i).2⟩ ≤ ⟨m - r + i.1, by omega⟩ from hfi)
    rw [e.apply_symm_apply] at hmo
    exact hmo
  have hsumT : ∑ x ∈ T, x = ∑ i : Fin r, (eT i : ℕ) := by
    rw [← Finset.sum_attach T (fun x => x)]
    symm; exact Finset.sum_equiv eT.toEquiv (by simp) (by simp)
  rw [hsumT, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [show m - r + i.1 < m by omega, ↓reduceDIte]
  exact hle i

private lemma diff_ge_of_strict {m : ℕ} {b : ℕ → ℕ}
    (hstrict : ∀ i j, i < j → j < m → b i < b j) :
    ∀ i j, i ≤ j → j < m → j - i ≤ b j - b i := by
  have hadd : ∀ i j, i ≤ j → j < m → b i + (j - i) ≤ b j := by
    intro i j hij hjm
    induction j with
    | zero =>
      have hi0 : i = 0 := by omega
      subst hi0; simp
    | succ k ih =>
      rcases eq_or_lt_of_le hij with rfl | hlt
      · omega
      · have h1 := ih (by omega) (by omega)
        have h2 := hstrict k (k + 1) (Nat.lt_succ_self k) hjm
        omega
  intro i j hij hjm
  have := hadd i j hij hjm
  omega

private lemma block_diff_exists (m a₁ a₂ b₁ b₂ d : ℕ)
    (ha : a₁ < a₂) (hab : a₂ ≤ b₁) (hb : b₁ < b₂) (hb₂m : b₂ ≤ m)
    (b : ℕ → ℕ)
    (hstrict : ∀ i j, i < j → j < m → b i < b j)
    (h1 : (b (a₂ - 1) - b a₁) - (a₂ - 1 - a₁) + ((b (b₂ - 1) - b b₁) - (b₂ - 1 - b₁)) < a₂ - a₁)
    (h2 : (b (a₂ - 1) - b a₁) - (a₂ - 1 - a₁) + ((b (b₂ - 1) - b b₁) - (b₂ - 1 - b₁)) < b₂ - b₁)
    (h3 : b b₁ + ((b (a₂ - 1) - b a₁) - (a₂ - 1 - a₁)) + ((b (b₂ - 1) - b b₁) - (b₂ - 1 - b₁)) < b (a₂ - 1) + d + 1)
    (h4 : b a₁ + d + ((b (a₂ - 1) - b a₁) - (a₂ - 1 - a₁)) + ((b (b₂ - 1) - b b₁) - (b₂ - 1 - b₁)) < b (b₂ - 1) + 1) :
    ∃ i ∈ Finset.Ico a₁ a₂, ∃ j ∈ Finset.Ico b₁ b₂, b j = b i + d := by
  set gX := (b (a₂ - 1) - b a₁) - (a₂ - 1 - a₁)
  set gY := (b (b₂ - 1) - b b₁) - (b₂ - 1 - b₁)
  have hmono : ∀ i j, i ≤ j → j < m → b i ≤ b j := fun i j hij hjm =>
    (eq_or_lt_of_le hij).elim (fun h => h ▸ le_rfl) (fun h => (hstrict i j h hjm).le)
  have hXgap := diff_ge_of_strict hstrict a₁ (a₂ - 1) (by omega) (by omega)
  have hYgap := diff_ge_of_strict hstrict b₁ (b₂ - 1) (by omega) (by omega)
  set X := (Finset.Ico a₁ a₂).image b
  set Y := (Finset.Ico b₁ b₂).image b
  have hXcard : X.card = a₂ - a₁ := by
    rw [Finset.card_image_of_injOn, Nat.card_Ico]
    intro i hi j hj heq
    rw [Finset.mem_coe, Finset.mem_Ico] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact absurd heq (ne_of_lt (hstrict i j hlt (by omega)))
    · rfl
    · exact absurd heq.symm (ne_of_lt (hstrict j i hgt (by omega)))
  have hYcard : Y.card = b₂ - b₁ := by
    rw [Finset.card_image_of_injOn, Nat.card_Ico]
    intro i hi j hj heq
    rw [Finset.mem_coe, Finset.mem_Ico] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact absurd heq (ne_of_lt (hstrict i j hlt (by omega)))
    · rfl
    · exact absurd heq.symm (ne_of_lt (hstrict j i hgt (by omega)))
  set lo := max (b a₁ + d) (b b₁)
  set hi := min (b (a₂ - 1) + d) (b (b₂ - 1))
  have ha_le := hmono a₁ (a₂ - 1) (by omega) (by omega)
  have hb_le := hmono b₁ (b₂ - 1) (by omega) (by omega)
  set I := Finset.Icc lo hi
  have hI_card : gX + gY < I.card := by
    rw [Nat.card_Icc]; omega
  have hmissX : (I \ X.image (· + d)).card ≤ gX := by
    have hXsub : X ⊆ Finset.Icc (b a₁) (b (a₂ - 1)) := by
      intro x hx; obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨u, v⟩ := Finset.mem_Ico.mp hi'
      exact Finset.mem_Icc.mpr ⟨hmono a₁ i u (by omega), hmono i (a₂ - 1) (by omega) (by omega)⟩
    have hcard_holesX : (Finset.Icc (b a₁) (b (a₂ - 1)) \ X).card = gX := by
      have hs := Finset.card_sdiff_add_card_eq_card hXsub
      rw [Nat.card_Icc, hXcard] at hs; omega
    rw [← hcard_holesX]
    refine Finset.card_le_card_of_injOn (fun z => z - d) ?_ ?_
    · intro z hz
      rw [Finset.mem_coe] at hz ⊢
      obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hzI
      dsimp only
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, fun hmem =>
        hznot (Finset.mem_image.mpr ⟨z - d, hmem, by omega⟩)⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      rw [Finset.mem_coe] at hz₁ hz₂
      have u1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₁).1).1
      have u2 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₂).1).1
      dsimp only at heq; omega
  have hmissY : (I \ Y).card ≤ gY := by
    have hYsub : Y ⊆ Finset.Icc (b b₁) (b (b₂ - 1)) := by
      intro y hy; obtain ⟨j, hj', rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨u, v⟩ := Finset.mem_Ico.mp hj'
      exact Finset.mem_Icc.mpr ⟨hmono b₁ j u (by omega), hmono j (b₂ - 1) (by omega) (by omega)⟩
    have hcard_holesY : (Finset.Icc (b b₁) (b (b₂ - 1)) \ Y).card = gY := by
      have hs := Finset.card_sdiff_add_card_eq_card hYsub
      rw [Nat.card_Icc, hYcard] at hs; omega
    rw [← hcard_holesY]
    refine Finset.card_le_card fun z hz => ?_
    obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hzI
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hznot⟩
  have hex : (I \ ((I \ X.image (· + d)) ∪ (I \ Y))).Nonempty := by
    apply Finset.card_pos.mp
    have hu := Finset.card_union_le (I \ X.image (· + d)) (I \ Y)
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.union_subset Finset.sdiff_subset Finset.sdiff_subset :
      (I \ X.image (· + d)) ∪ (I \ Y) ⊆ I)
    omega
  obtain ⟨z, hz⟩ := hex
  obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz
  have hzXd : z ∈ X.image (· + d) := by
    by_contra h; exact hznot (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hzI, h⟩))
  have hzY : z ∈ Y := by
    by_contra h; exact hznot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzI, h⟩))
  obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.mp hzXd
  obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp hxX
  obtain ⟨j, hj', hjeq⟩ := Finset.mem_image.mp hzY
  exact ⟨i, hi', j, hj', hjeq⟩

/-- Clean modular lemma: every `z` with `L + g + 1 ≤ z` and `z + g + 1 ≤ M` lies in `S`. -/
private lemma mid_in_S (m r g L M : ℕ) (S : Finset ℕ) (b s : ℕ → ℕ)
    (hr10 : 10 ≤ r) (hg1 : 1 ≤ g) (h5g : 5 * g ≤ r) (hrm : 2 * r ≤ m) (hrm2 : m ≤ 2 * r + 1)
    (hstrict : ∀ i j, i < j → j < m → b i < b j)
    (hg_eq : g = (b (m - 1) - b 0) - (m - 1))
    (hs0 : s 0 = L) (hsr' : s (m - r) = M)
    (hs_step : ∀ t, t < m - r → s (t + 1) + b t = s t + b (t + r))
    (hswap_up : ∀ t i j, t ≤ m - r → i ∈ Finset.Ico t (t + r) → j < m → j ∉ Finset.Ico t (t + r) →
      b i ≤ b j → s t + (b j - b i) ∈ S)
    (hswap_down : ∀ t i j, t ≤ m - r → j ∈ Finset.Ico t (t + r) → i < m → i ∉ Finset.Ico t (t + r) →
      b i ≤ b j → s t - (b j - b i) ∈ S) :
    ∀ z, L + g + 1 ≤ z → z + g + 1 ≤ M → z ∈ S := by
  intro z hzL hzM
  set r' := m - r
  let h : ℕ → ℕ := fun i => (b i - b 0) - i
  have hmono : ∀ i j, i ≤ j → j < m → b i ≤ b j := fun i j hij hjm =>
    (eq_or_lt_of_le hij).elim (fun e => e ▸ le_rfl) (fun e => (hstrict i j e hjm).le)
  have hdiff := diff_ge_of_strict hstrict
  have hb_eq_h : ∀ i, i < m → b i = b 0 + i + h i := fun i hi => by
    have u1 := hdiff 0 i (Nat.zero_le _) hi; have u2 := hmono 0 i (Nat.zero_le _) hi
    dsimp only [h]; omega
  have hh_mono : ∀ i j, i ≤ j → j < m → h i ≤ h j := fun i j hij hjm => by
    have u0 := hmono i j hij hjm
    have u1 := hdiff i j hij hjm
    have u2 := hb_eq_h i (by omega)
    have u3 := hb_eq_h j hjm
    omega
  have hhm : h (m - 1) = g := hg_eq.symm
  have hs_mono : ∀ t₁ t₂, t₁ ≤ t₂ → t₂ ≤ r' → s t₁ ≤ s t₂ := by
    intro t₁ t₂ h12 h2r
    induction t₂ with
    | zero =>
      have ht0 : t₁ = 0 := by omega
      subst ht0; exact le_rfl
    | succ k ih =>
      rcases eq_or_lt_of_le h12 with rfl | hlt
      · exact le_rfl
      · have p := ih (by omega) (by omega); have st := hs_step k (by omega)
        have bl := hstrict k (k + r) (by omega) (by omega); omega
  by_cases hcase : z ≤ s (r' - 2 * g) + g
  · set Good := (Finset.Icc 0 (r' - 2 * g)).filter (fun t => s t + g < z)
    have h0_good : 0 ∈ Good := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩, by omega⟩
    set t := Good.max' ⟨0, h0_good⟩
    have ht_mem := Finset.mem_filter.mp (Finset.max'_mem Good ⟨0, h0_good⟩)
    have ht_le : t ≤ r' - 2 * g := (Finset.mem_Icc.mp ht_mem.1).2
    have ht_lt_z : s t + g < z := ht_mem.2
    have ht_strict : t < r' - 2 * g := by
      by_contra hge
      have hteq : t = r' - 2 * g := by omega
      rw [hteq] at ht_lt_z
      omega
    have hnext_ge : z ≤ s (t + 1) + g := by
      by_contra hlt; push Not at hlt
      have := Finset.le_max' Good (t + 1) (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, hlt⟩)
      omega
    set d := z - s t
    have hstep := hs_step t (by omega)
    have hb_gap := hdiff (t + r) (m - 1) (by omega) (by omega)
    have u1 := hb_eq_h t (by omega)
    have u2 := hb_eq_h (t + r - 1) (by omega)
    have u3 := hb_eq_h (t + r) (by omega)
    have u4 := hb_eq_h (m - 1) (by omega)
    have m1 := hh_mono t (t + r - 1) (by omega) (by omega)
    have m2 := hh_mono (t + r - 1) (t + r) (by omega) (by omega)
    have m3 := hh_mono (t + r) (m - 1) (by omega) (by omega)
    obtain ⟨i, hi, j, hj, hjeq⟩ := block_diff_exists m t (t + r) (t + r) m d
      (by omega) le_rfl (by omega) le_rfl b hstrict
      (by omega) (by omega) (by omega) (by omega)
    have hsw := hswap_up t i j (by omega) hi (Finset.mem_Ico.mp hj).2
      (by simp only [Finset.mem_Ico]; have := (Finset.mem_Ico.mp hj).1; omega) (by omega)
    have hz_eq : z = s t + (b j - b i) := by omega
    exact hz_eq ▸ hsw
  · push Not at hcase
    have h2g_lt : s (2 * g) + g < z := by
      have := hs_mono (2 * g) (r' - 2 * g) (by omega) (by omega); omega
    set Good := (Finset.Icc (2 * g) r').filter (fun t => z + g < s t)
    have hr'_good : r' ∈ Good := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, by omega⟩
    set t := Good.min' ⟨r', hr'_good⟩
    have ht_mem := Finset.mem_filter.mp (Finset.min'_mem Good ⟨r', hr'_good⟩)
    have ht_ge : 2 * g ≤ t := (Finset.mem_Icc.mp ht_mem.1).1
    have ht_le : t ≤ r' := (Finset.mem_Icc.mp ht_mem.1).2
    have ht_gt_z : z + g < s t := ht_mem.2
    have ht_strict : 2 * g < t := by
      by_contra hle
      have hteq : t = 2 * g := by omega
      rw [hteq] at ht_gt_z
      omega
    have hprev_le : s (t - 1) ≤ z + g := by
      by_contra hgt; push Not at hgt
      have := Finset.min'_le Good (t - 1) (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hgt⟩)
      omega
    set d := s t - z
    have hstep := hs_step (t - 1) (by omega)
    have hteq1 : t - 1 + 1 = t := by omega
    rw [hteq1] at hstep
    have hb_gap := hdiff 0 (t - 1) (Nat.zero_le _) (by omega)
    have u1 := hb_eq_h (t - 1) (by omega)
    have u2 := hb_eq_h t (by omega)
    have u3 := hb_eq_h (t + r - 1) (by omega)
    have u4 := hb_eq_h (m - 1) (by omega)
    have m1 := hh_mono (t - 1) t (by omega) (by omega)
    have m2 := hh_mono t (t + r - 1) (by omega) (by omega)
    have m3 := hh_mono (t + r - 1) (m - 1) (by omega) (by omega)
    have htr1 : t - 1 + r = t + r - 1 := by omega
    rw [htr1] at hstep
    obtain ⟨i, hi, j, hj, hjeq⟩ := block_diff_exists m 0 t t (t + r) d
      (by omega) le_rfl (by omega) (by omega) b hstrict
      (by omega) (by omega) (by omega) (by omega)
    have hsw := hswap_down t i j ht_le hj (by have := (Finset.mem_Ico.mp hi).2; omega)
      (by simp only [Finset.mem_Ico]; have := (Finset.mem_Ico.mp hi).2; omega) (by omega)
    have hz_eq : z = s t - (b j - b i) := by omega
    exact hz_eq ▸ hsw

/-- Clean modular lemma: bottom-end missing count `2 * |(Icc (L+1) (L+g) \ S)| ≤ g + δ`. -/
private lemma bot_missing_le (m r g L : ℕ) (S : Finset ℕ) (b : ℕ → ℕ)
    (hr10 : 10 ≤ r) (h5g : 5 * g ≤ r) (hrm : 2 * r ≤ m)
    (hstrict : ∀ i j, i < j → j < m → b i < b j)
    (hg_eq : g = (b (m - 1) - b 0) - (m - 1))
    (hswap0 : ∀ i j, i < r → r ≤ j → j < m → L + (b j - b i) ∈ S) :
    let h := fun i => (b i - b 0) - i
    2 * (Finset.Icc (L + 1) (L + g) \ S).card ≤ g + (h r - h (r - 1)) := by
  dsimp only
  let h : ℕ → ℕ := fun i => (b i - b 0) - i
  have hmono : ∀ i j, i ≤ j → j < m → b i ≤ b j := fun i j hij hjm =>
    (eq_or_lt_of_le hij).elim (fun e => e ▸ le_rfl) (fun e => (hstrict i j e hjm).le)
  have hdiff := diff_ge_of_strict hstrict
  have hb_eq_h : ∀ i, i < m → b i = b 0 + i + h i := fun i hi => by
    have u1 := hdiff 0 i (Nat.zero_le _) hi; have u2 := hmono 0 i (Nat.zero_le _) hi
    dsimp only [h]; omega
  have hh_mono : ∀ i j, i ≤ j → j < m → h i ≤ h j := fun i j hij hjm => by
    have u0 := hmono i j hij hjm
    have u1 := hdiff i j hij hjm
    have u2 := hb_eq_h i (by omega)
    have u3 := hb_eq_h j hjm
    omega
  have hb_inj : Set.InjOn b (Finset.range m : Set ℕ) := by
    intro i hi j hj heq; rw [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact absurd heq (ne_of_lt (hstrict i j hlt hj))
    · rfl
    · exact absurd heq.symm (ne_of_lt (hstrict j i hgt hi))
  set gL := h (r - 1)
  set δ := h r - h (r - 1)
  set gR := g - h r
  have h1 := hb_eq_h (r - 1) (by omega)
  have h2 := hb_eq_h r (by omega)
  have h3 := hb_eq_h (m - 1) (by omega)
  have hm1 := hh_mono (r - 1) r (by omega) (by omega)
  have hm2 := hh_mono r (m - 1) (by omega) (by omega)
  have hhm : h (m - 1) = g := hg_eq.symm
  have hsub : Finset.Icc (L + 1) (L + g) \ S ⊆
      Finset.Icc (L + 1) (L + δ) ∪ (Finset.Icc (L + δ + 1) (L + g) \ S) := by
    intro z hz; obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz; obtain ⟨z1, z2⟩ := Finset.mem_Icc.mp hzI
    by_cases c : z ≤ L + δ
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨z1, c⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, z2⟩, hznot⟩)
  have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Nat.card_Icc] at hu
  have htailR : (Finset.Icc (L + δ + 1) (L + g) \ S).card ≤ gR := by
    set Y := (Finset.Ico r m).image b
    have hYsub : Y ⊆ Finset.Icc (b r) (b (m - 1)) := by
      intro y hy; obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_Icc.mpr ⟨hmono r j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2,
        hmono j (m - 1) (by have := (Finset.mem_Ico.mp hj).2; omega) (by omega)⟩
    have hYcard : Y.card = m - r := by
      rw [Finset.card_image_of_injOn, Nat.card_Ico]
      exact hb_inj.mono fun j hj => Finset.mem_coe.mpr (Finset.mem_range.mpr (Finset.mem_Ico.mp (Finset.mem_coe.mp hj)).2)
    have hholesY : (Finset.Icc (b r) (b (m - 1)) \ Y).card = gR := by
      have hs := Finset.card_sdiff_add_card_eq_card hYsub
      rw [Nat.card_Icc, hYcard] at hs; omega
    rw [← hholesY]
    refine Finset.card_le_card_of_injOn (fun z => b (r - 1) + (z - L)) ?_ ?_
    · intro z hz; rw [Finset.mem_coe] at hz ⊢
      obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz; obtain ⟨z1, z2⟩ := Finset.mem_Icc.mp hzI
      dsimp only
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, fun hmemY => ?_⟩
      obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hmemY
      have hsw := hswap0 (r - 1) j (by omega) (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
      exact hznot ((show z = L + (b j - b (r - 1)) by omega) ▸ hsw)
    · intro z₁ hz₁ z₂ hz₂ heq; rw [Finset.mem_coe] at hz₁ hz₂
      have u1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₁).1).1
      have u2 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₂).1).1
      dsimp only at heq; omega
  have htailL : (Finset.Icc (L + δ + 1) (L + g) \ S).card ≤ gL := by
    set X := (Finset.Ico 0 r).image b
    have hXsub : X ⊆ Finset.Icc (b 0) (b (r - 1)) := by
      intro x hx; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_Icc.mpr ⟨hmono 0 i (Nat.zero_le _) (by have := (Finset.mem_Ico.mp hi).2; omega),
        hmono i (r - 1) (by have := (Finset.mem_Ico.mp hi).2; omega) (by omega)⟩
    have hXcard : X.card = r := by
      rw [Finset.card_image_of_injOn, Nat.card_Ico]; simp
      exact hb_inj.mono fun i hi => Finset.mem_coe.mpr (Finset.mem_range.mpr (by
        have := (Finset.mem_Ico.mp (Finset.mem_coe.mp hi)).2; omega))
    have hholesX : (Finset.Icc (b 0) (b (r - 1)) \ X).card = gL := by
      have hs := Finset.card_sdiff_add_card_eq_card hXsub
      rw [Nat.card_Icc, hXcard] at hs; omega
    rw [← hholesX]
    refine Finset.card_le_card_of_injOn (fun z => b r - (z - L)) ?_ ?_
    · intro z hz; rw [Finset.mem_coe] at hz ⊢
      obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz; obtain ⟨z1, z2⟩ := Finset.mem_Icc.mp hzI
      dsimp only
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, fun hmemX => ?_⟩
      obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp hmemX
      have hsw := hswap0 i r (Finset.mem_Ico.mp hi).2 le_rfl (by omega)
      exact hznot ((show z = L + (b r - b i) by omega) ▸ hsw)
    · intro z₁ hz₁ z₂ hz₂ heq; rw [Finset.mem_coe] at hz₁ hz₂
      have u1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₁).1)
      have u2 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₂).1)
      dsimp only at heq; omega
  omega

/-- Clean modular lemma: top-end missing count `2 * |(Icc (M-g) (M-1) \ S)| ≤ g + δ'`. -/
private lemma top_missing_le (m r g M : ℕ) (S : Finset ℕ) (b : ℕ → ℕ)
    (hr10 : 10 ≤ r) (h5g : 5 * g ≤ r) (hrm : 2 * r ≤ m) (hrm2 : m ≤ 2 * r + 1) (hMg : g + 1 ≤ M)
    (hstrict : ∀ i j, i < j → j < m → b i < b j)
    (hg_eq : g = (b (m - 1) - b 0) - (m - 1))
    (hswapM : ∀ i j, i < m - r → m - r ≤ j → j < m → M - (b j - b i) ∈ S) :
    let h := fun i => (b i - b 0) - i
    2 * (Finset.Icc (M - g) (M - 1) \ S).card ≤ g + (h (m - r) - h (m - r - 1)) := by
  dsimp only
  set r' := m - r
  let h : ℕ → ℕ := fun i => (b i - b 0) - i
  have hmono : ∀ i j, i ≤ j → j < m → b i ≤ b j := fun i j hij hjm =>
    (eq_or_lt_of_le hij).elim (fun e => e ▸ le_rfl) (fun e => (hstrict i j e hjm).le)
  have hdiff := diff_ge_of_strict hstrict
  have hb_eq_h : ∀ i, i < m → b i = b 0 + i + h i := fun i hi => by
    have u1 := hdiff 0 i (Nat.zero_le _) hi; have u2 := hmono 0 i (Nat.zero_le _) hi
    dsimp only [h]; omega
  have hh_mono : ∀ i j, i ≤ j → j < m → h i ≤ h j := fun i j hij hjm => by
    have u0 := hmono i j hij hjm
    have u1 := hdiff i j hij hjm
    have u2 := hb_eq_h i (by omega)
    have u3 := hb_eq_h j hjm
    omega
  have hb_inj : Set.InjOn b (Finset.range m : Set ℕ) := by
    intro i hi j hj heq; rw [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact absurd heq (ne_of_lt (hstrict i j hlt hj))
    · rfl
    · exact absurd heq.symm (ne_of_lt (hstrict j i hgt hi))
  set gL' := h (r' - 1)
  set δ' := h r' - h (r' - 1)
  set gR' := g - h r'
  have h1 := hb_eq_h (r' - 1) (by omega)
  have h2 := hb_eq_h r' (by omega)
  have h3 := hb_eq_h (m - 1) (by omega)
  have hm1 := hh_mono (r' - 1) r' (by omega) (by omega)
  have hm2 := hh_mono r' (m - 1) (by omega) (by omega)
  have hhm : h (m - 1) = g := hg_eq.symm
  have hsub : Finset.Icc (M - g) (M - 1) \ S ⊆
      Finset.Icc (M - δ') (M - 1) ∪ (Finset.Icc (M - g) (M - δ' - 1) \ S) := by
    intro z hz; obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz; obtain ⟨z1, z2⟩ := Finset.mem_Icc.mp hzI
    by_cases c : M - δ' ≤ z
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨c, z2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨z1, by omega⟩, hznot⟩)
  have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Nat.card_Icc] at hu
  have htailL : (Finset.Icc (M - g) (M - δ' - 1) \ S).card ≤ gL' := by
    set X := (Finset.Ico 0 r').image b
    have hXsub : X ⊆ Finset.Icc (b 0) (b (r' - 1)) := by
      intro x hx; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_Icc.mpr ⟨hmono 0 i (Nat.zero_le _) (by have := (Finset.mem_Ico.mp hi).2; omega),
        hmono i (r' - 1) (by have := (Finset.mem_Ico.mp hi).2; omega) (by omega)⟩
    have hXcard : X.card = r' := by
      rw [Finset.card_image_of_injOn, Nat.card_Ico]; simp
      exact hb_inj.mono fun i hi => Finset.mem_coe.mpr (Finset.mem_range.mpr (by
        have := (Finset.mem_Ico.mp (Finset.mem_coe.mp hi)).2; omega))
    have hholesX : (Finset.Icc (b 0) (b (r' - 1)) \ X).card = gL' := by
      have hs := Finset.card_sdiff_add_card_eq_card hXsub
      rw [Nat.card_Icc, hXcard] at hs; omega
    rw [← hholesX]
    refine Finset.card_le_card_of_injOn (fun z => b r' - (M - z)) ?_ ?_
    · intro z hz; rw [Finset.mem_coe] at hz ⊢
      obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz; obtain ⟨z1, z2⟩ := Finset.mem_Icc.mp hzI
      dsimp only
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, fun hmemX => ?_⟩
      obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp hmemX
      have hsw := hswapM i r' (Finset.mem_Ico.mp hi).2 le_rfl (by omega)
      exact hznot ((show z = M - (b r' - b i) by omega) ▸ hsw)
    · intro z₁ hz₁ z₂ hz₂ heq; rw [Finset.mem_coe] at hz₁ hz₂
      have u1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₁).1)
      have u2 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₂).1)
      dsimp only at heq; omega
  have htailR : (Finset.Icc (M - g) (M - δ' - 1) \ S).card ≤ gR' := by
    set Y := (Finset.Ico r' m).image b
    have hYsub : Y ⊆ Finset.Icc (b r') (b (m - 1)) := by
      intro y hy; obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_Icc.mpr ⟨hmono r' j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2,
        hmono j (m - 1) (by have := (Finset.mem_Ico.mp hj).2; omega) (by omega)⟩
    have hYcard : Y.card = r := by
      rw [Finset.card_image_of_injOn, Nat.card_Ico]; omega
      exact hb_inj.mono fun j hj => Finset.mem_coe.mpr (Finset.mem_range.mpr (Finset.mem_Ico.mp (Finset.mem_coe.mp hj)).2)
    have hholesY : (Finset.Icc (b r') (b (m - 1)) \ Y).card = gR' := by
      have hs := Finset.card_sdiff_add_card_eq_card hYsub
      rw [Nat.card_Icc, hYcard] at hs; omega
    rw [← hholesY]
    refine Finset.card_le_card_of_injOn (fun z => b (r' - 1) + (M - z)) ?_ ?_
    · intro z hz; rw [Finset.mem_coe] at hz ⊢
      obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz; obtain ⟨z1, z2⟩ := Finset.mem_Icc.mp hzI
      dsimp only
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, fun hmemY => ?_⟩
      obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hmemY
      have hsw := hswapM (r' - 1) j (by omega) (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
      exact hznot ((show z = M - (b j - b (r' - 1)) by omega) ▸ hsw)
    · intro z₁ hz₁ z₂ hz₂ heq; rw [Finset.mem_coe] at hz₁ hz₂
      have u1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₁).1)
      have u2 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hz₂).1)
      dsimp only at heq; omega
  omega

end E875H3

theorem OMA.solution : OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1.H3 := by
  intro B hB hm20 L M hLM hLex hMex hg10
  set m := B.card with hm_def
  set r := m / 2 with hr_def
  set r' := m - r with hr'_def
  have hr10 : 10 ≤ r := by omega
  set e := B.orderIsoOfFin (rfl : B.card = m)
  let b : ℕ → ℕ := fun i => if h : i < m then (e ⟨i, h⟩ : ℕ) else 0
  have hb_mem : ∀ i, i < m → b i ∈ B := fun i hi => by
    simp only [b, hi, ↓reduceDIte]; exact (e ⟨i, hi⟩).2
  have hstrict : ∀ i j, i < j → j < m → b i < b j := fun i j hij hjm => by
    simp only [b, show i < m by omega, hjm, ↓reduceDIte]
    exact e.strictMono (Fin.mk_lt_mk.mpr hij)
  have hmono : ∀ i j, i ≤ j → j < m → b i ≤ b j := fun i j hij hjm =>
    (eq_or_lt_of_le hij).elim (fun h => h ▸ le_rfl) (fun h => (hstrict i j h hjm).le)
  have hdiff := E875H3.diff_ge_of_strict hstrict
  have hb_inj : Set.InjOn b (Finset.range m : Set ℕ) := by
    intro i hi j hj heq; rw [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact absurd heq (ne_of_lt (hstrict i j hlt hj))
    · rfl
    · exact absurd heq.symm (ne_of_lt (hstrict j i hgt hi))
  have hb0_eq : b 0 = B.min' hB := by
    apply le_antisymm
    · let k := e.symm ⟨B.min' hB, Finset.min'_mem B hB⟩
      have h1 : b 0 ≤ b k.1 := hmono 0 k.1 (Nat.zero_le _) k.2
      have h2 : b k.1 = B.min' hB := by
        simp only [b, show k.1 < m from k.2, ↓reduceDIte]
        have := e.apply_symm_apply ⟨B.min' hB, Finset.min'_mem B hB⟩
        exact congrArg Subtype.val this
      omega
    · exact Finset.min'_le B (b 0) (hb_mem 0 (by omega))
  have hbm_eq : b (m - 1) = B.max' hB := by
    apply le_antisymm
    · exact Finset.le_max' B (b (m - 1)) (hb_mem (m - 1) (by omega))
    · let k := e.symm ⟨B.max' hB, Finset.max'_mem B hB⟩
      have h1 : b k.1 ≤ b (m - 1) := hmono k.1 (m - 1) (by omega) (by omega)
      have h2 : b k.1 = B.max' hB := by
        simp only [b, show k.1 < m from k.2, ↓reduceDIte]
        have := e.apply_symm_apply ⟨B.max' hB, Finset.max'_mem B hB⟩
        exact congrArg Subtype.val this
      omega
  set g := (B.max' hB - B.min' hB) - (m - 1) with hg_def
  have hg_eq : g = (b (m - 1) - b 0) - (m - 1) := by rw [hg_def, hb0_eq, hbm_eq]
  have h5g_le_r : 5 * g ≤ r := by omega
  let h : ℕ → ℕ := fun i => (b i - b 0) - i
  have hh0 : h 0 = 0 := by simp [h]
  have hhm : h (m - 1) = g := hg_eq.symm
  have hb_eq_h : ∀ i, i < m → b i = b 0 + i + h i := fun i hi => by
    have u1 := hdiff 0 i (Nat.zero_le _) hi; have u2 := hmono 0 i (Nat.zero_le _) hi
    dsimp only [h]; omega
  have hh_mono : ∀ i j, i ≤ j → j < m → h i ≤ h j := fun i j hij hjm => by
    have u0 := hmono i j hij hjm
    have u1 := hdiff i j hij hjm
    have u2 := hb_eq_h i (by omega)
    have u3 := hb_eq_h j hjm
    omega
  set S := (B.powersetCard r).image (fun T => ∑ x ∈ T, x)
  let W : ℕ → Finset ℕ := fun t => (Finset.Ico t (t + r)).image b
  let s : ℕ → ℕ := fun t => ∑ i ∈ Finset.Ico t (t + r), b i
  have hW_mem : ∀ t, t ≤ r' → W t ∈ B.powersetCard r := by
    intro t ht
    refine Finset.mem_powersetCard.mpr ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hb_mem i (by have := (Finset.mem_Ico.mp hi).2; omega)
    · rw [Finset.card_image_of_injOn, Nat.card_Ico]; omega
      exact hb_inj.mono fun i hi => Finset.mem_coe.mpr (Finset.mem_range.mpr (by
        have := (Finset.mem_Ico.mp (Finset.mem_coe.mp hi)).2; omega))
  have hs_eq : ∀ t, t ≤ r' → ∑ x ∈ W t, x = s t := fun t ht =>
    Finset.sum_image (hb_inj.mono fun i hi => Finset.mem_coe.mpr (Finset.mem_range.mpr (by
      have := (Finset.mem_Ico.mp (Finset.mem_coe.mp hi)).2; omega)))
  have hs_mem : ∀ t, t ≤ r' → s t ∈ S := fun t ht =>
    Finset.mem_image.mpr ⟨W t, hW_mem t ht, hs_eq t ht⟩
  have hs_step : ∀ t, t < r' → s (t + 1) + b t = s t + b (t + r) := by
    intro t ht
    have h1 : Finset.Ico t (t + r + 1) = insert t (Finset.Ico (t + 1) (t + r + 1)) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have h2 : Finset.Ico t (t + r + 1) = insert (t + r) (Finset.Ico t (t + r)) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have eq1 : ∑ i ∈ Finset.Ico t (t + r + 1), b i = b t + s (t + 1) := by
      have hI : Finset.Ico (t + 1) (t + r + 1) = Finset.Ico (t + 1) (t + 1 + r) := by congr 1; omega
      rw [h1, Finset.sum_insert (by simp), hI]
    have eq2 : ∑ i ∈ Finset.Ico t (t + r + 1), b i = b (t + r) + s t := by
      rw [h2, Finset.sum_insert (by simp)]
    omega
  have hs0_eq : s 0 = L := by
    apply le_antisymm
    · obtain ⟨T, hT, hTL⟩ := hLex; rw [← hTL]
      have h1 := E875H3.sum_min_le_sum (rfl : B.card = m) (by omega : r ≤ m) T
        (Finset.mem_powersetCard.mp hT).1 (Finset.mem_powersetCard.mp hT).2
      have h2 : s 0 = ∑ i ∈ Finset.range r, b i := by
        dsimp only [s]; rw [Nat.Ico_zero_eq_range, zero_add]
      rw [h2]; exact h1
    · rw [← hs_eq 0 (Nat.zero_le _)]; exact (hLM (W 0) (hW_mem 0 (Nat.zero_le _))).1
  have hsr'_eq : s r' = M := by
    apply le_antisymm
    · rw [← hs_eq r' le_rfl]; exact (hLM (W r') (hW_mem r' le_rfl)).2
    · obtain ⟨T, hT, hTM⟩ := hMex; rw [← hTM]
      have h1 := E875H3.sum_le_sum_max (rfl : B.card = m) (by omega : r ≤ m) T
        (Finset.mem_powersetCard.mp hT).1 (Finset.mem_powersetCard.mp hT).2
      have h2 : s r' = ∑ i ∈ Finset.range r, b (r' + i) := by
        dsimp only [s]
        have hIco : Finset.Ico r' (r' + r) = (Finset.range r).image (fun i => r' + i) := by
          ext j; simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
          exact ⟨fun hj => ⟨j - r', by omega, by omega⟩, fun ⟨i, hi, e⟩ => by omega⟩
        rw [hIco, Finset.sum_image (fun _ _ _ _ h => by omega)]
      rw [h2]; exact h1
  have hswap_up : ∀ t i j, t ≤ r' → i ∈ Finset.Ico t (t + r) → j < m → j ∉ Finset.Ico t (t + r) →
      b i ≤ b j → s t + (b j - b i) ∈ S := by
    intro t i j ht hi hjm hjnot hle
    have hbi_in : b i ∈ W t := Finset.mem_image_of_mem b hi
    have hbj_not : b j ∉ W t := fun hmem => by
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hmem
      have hkeq : k = j := hb_inj (Finset.mem_coe.mpr (Finset.mem_range.mpr (by
        have := (Finset.mem_Ico.mp hk).2; omega))) (Finset.mem_coe.mpr (Finset.mem_range.mpr hjm)) heq
      exact hjnot (hkeq ▸ hk)
    have hbj_not_er : b j ∉ (W t).erase (b i) := fun h => hbj_not (Finset.mem_of_mem_erase h)
    refine Finset.mem_image.mpr ⟨insert (b j) ((W t).erase (b i)), Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.insert_subset (hb_mem j hjm) ((Finset.erase_subset _ _).trans (Finset.mem_powersetCard.mp (hW_mem t ht)).1)
    · rw [Finset.card_insert_of_notMem hbj_not_er, Finset.card_erase_of_mem hbi_in,
          (Finset.mem_powersetCard.mp (hW_mem t ht)).2]; omega
    · rw [Finset.sum_insert hbj_not_er]
      have hsum := Finset.add_sum_erase (W t) (fun x => x) hbi_in
      rw [hs_eq t ht] at hsum; omega
  have hswap_down : ∀ t i j, t ≤ r' → j ∈ Finset.Ico t (t + r) → i < m → i ∉ Finset.Ico t (t + r) →
      b i ≤ b j → s t - (b j - b i) ∈ S := by
    intro t i j ht hj him hinot hle
    have hbj_in : b j ∈ W t := Finset.mem_image_of_mem b hj
    have hbi_not : b i ∉ W t := fun hmem => by
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hmem
      have hkeq : k = i := hb_inj (Finset.mem_coe.mpr (Finset.mem_range.mpr (by
        have := (Finset.mem_Ico.mp hk).2; omega))) (Finset.mem_coe.mpr (Finset.mem_range.mpr him)) heq
      exact hinot (hkeq ▸ hk)
    have hbi_not_er : b i ∉ (W t).erase (b j) := fun h => hbi_not (Finset.mem_of_mem_erase h)
    refine Finset.mem_image.mpr ⟨insert (b i) ((W t).erase (b j)), Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.insert_subset (hb_mem i him) ((Finset.erase_subset _ _).trans (Finset.mem_powersetCard.mp (hW_mem t ht)).1)
    · rw [Finset.card_insert_of_notMem hbi_not_er, Finset.card_erase_of_mem hbj_in,
          (Finset.mem_powersetCard.mp (hW_mem t ht)).2]; omega
    · rw [Finset.sum_insert hbi_not_er]
      have hsum := Finset.add_sum_erase (W t) (fun x => x) hbj_in
      rw [hs_eq t ht] at hsum; omega
  have hS_sub : S ⊆ Finset.Icc L M := fun x hx => by
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx; exact Finset.mem_Icc.mpr (hLM T hT)
  have hL_le_M : L ≤ M := by obtain ⟨T, hT, hTL⟩ := hLex; exact hTL ▸ (hLM T hT).2
  have hmiss_eq : (M - L + 1) - S.card = (Finset.Icc L M \ S).card := by
    have hs := Finset.card_sdiff_add_card_eq_card hS_sub; rw [Nat.card_Icc] at hs; omega
  have hML_decomp : M - L = r * r' + ∑ i ∈ Finset.range r, (h (r' + i) - h i) := by
    have hM_sum : M = ∑ i ∈ Finset.range r, b (r' + i) := by
      rw [← hsr'_eq]; dsimp only [s]
      have hIco : Finset.Ico r' (r' + r) = (Finset.range r).image (fun i => r' + i) := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
        exact ⟨fun hj => ⟨j - r', by omega, by omega⟩, fun ⟨i, hi, e⟩ => by omega⟩
      rw [hIco, Finset.sum_image (fun _ _ _ _ h => by omega)]
    have hL_sum : L = ∑ i ∈ Finset.range r, b i := by
      rw [← hs0_eq]; dsimp only [s]; rw [Nat.Ico_zero_eq_range, zero_add]
    have hadd : L + ∑ i ∈ Finset.range r, (b (r' + i) - b i) = M := by
      rw [hL_sum, hM_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => Nat.add_sub_of_le (hmono i (r' + i) (by omega) (by rw [Finset.mem_range] at hi; omega))
    have hpt : ∀ i ∈ Finset.range r, b (r' + i) - b i = r' + (h (r' + i) - h i) := fun i hi => by
      rw [Finset.mem_range] at hi
      have u1 := hb_eq_h (r' + i) (by omega); have u2 := hb_eq_h i (by omega)
      have u3 := hh_mono i (r' + i) (by omega) (by omega); omega
    have hsum_eq : ∑ i ∈ Finset.range r, (b (r' + i) - b i) =
        r * r' + ∑ i ∈ Finset.range r, (h (r' + i) - h i) := by
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  by_cases hg0 : g = 0
  · have hb_consec : ∀ i, i < m → b i = b 0 + i := fun i hi => by
      have u1 := hb_eq_h i hi; have u2 := hh_mono i (m - 1) (by omega) (by omega); omega
    have hs_consec : ∀ t, t ≤ r' → s t = L + t * r := by
      intro t ht; induction t with
      | zero => simp [hs0_eq]
      | succ k ih =>
        have hstep := hs_step k (by omega); have u1 := hb_consec k (by omega)
        have u2 := hb_consec (k + r) (by omega); have p := ih (by omega)
        have hm' : (k + 1) * r = k * r + r := by ring
        omega
    have hall : Finset.Icc L M ⊆ S := by
      intro z hz; obtain ⟨z1, z2⟩ := Finset.mem_Icc.mp hz
      by_cases hzM : z = M
      · exact hzM ▸ hsr'_eq ▸ hs_mem r' le_rfl
      · set q := (z - L) / r; set rem := (z - L) % r
        have hM_val : M = L + r' * r := by rw [← hsr'_eq, hs_consec r' le_rfl]
        have hdiv : q * r + rem = z - L := by
          have := Nat.div_add_mod (z - L) r; rw [Nat.mul_comm] at this; exact this
        have hrem_lt : rem < r := Nat.mod_lt _ (by omega)
        have hq_lt : q < r' := by
          by_contra hge; push Not at hge
          have : r' * r ≤ q * r := Nat.mul_le_mul_right r hge; omega
        by_cases hrem0 : rem = 0
        · exact (show z = s q by rw [hs_consec q (by omega)]; omega) ▸ hs_mem q (by omega)
        · have hqr_lt : q + r < m := Nat.add_lt_of_lt_sub hq_lt
          have hrem_pos : 0 < rem := Nat.pos_of_ne_zero hrem0
          have hq_le_qrr : q ≤ q + r - rem := Nat.le_sub_of_add_le (Nat.add_le_add_left hrem_lt.le q)
          have hqrr_lt : q + r - rem < q + r := Nat.sub_lt (Nat.add_pos_right q (by omega)) hrem_pos
          have hqrr_lt_m : q + r - rem < m := lt_trans hqrr_lt hqr_lt
          have h1 := hswap_up q (q + r - rem) (q + r) (le_of_lt hq_lt)
            (Finset.mem_Ico.mpr ⟨hq_le_qrr, hqrr_lt⟩) hqr_lt
            (by simp only [Finset.mem_Ico]; exact fun h => lt_irrefl _ h.2)
            (hmono _ _ (le_of_lt hqrr_lt) hqr_lt)
          have u1 := hb_consec (q + r - rem) hqrr_lt_m
          have u2 := hb_consec (q + r) hqr_lt
          have hsq := hs_consec q (le_of_lt hq_lt)
          have hdiff_eq : b (q + r) - b (q + r - rem) = rem := by
            rw [u1, u2, Nat.add_sub_add_left,
              Nat.sub_sub_self (le_trans hrem_lt.le (Nat.le_add_left r q))]
          have hz_eq : z = s q + (b (q + r) - b (q + r - rem)) := by
            rw [hsq, hdiff_eq, add_assoc, hdiv, Nat.add_sub_of_le z1]
          exact hz_eq ▸ h1
    have hmiss0 : (Finset.Icc L M \ S).card = 0 := by
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]; exact hall
    rw [hmiss_eq, hmiss0]; omega
  -- `1 ≤ g`
  have hmid := E875H3.mid_in_S m r g L M S b s hr10 (by omega) h5g_le_r (by omega) (by omega)
    hstrict hg_eq hs0_eq hsr'_eq hs_step hswap_up hswap_down
  have hmiss_sub : Finset.Icc L M \ S ⊆
      (Finset.Icc (L + 1) (L + g) \ S) ∪ (Finset.Icc (M - g) (M - 1) \ S) := by
    intro z hz; obtain ⟨hzI, hznot⟩ := Finset.mem_sdiff.mp hz; obtain ⟨z1, z2⟩ := Finset.mem_Icc.mp hzI
    have hneL : z ≠ L := fun e => hznot (e ▸ hs0_eq ▸ hs_mem 0 (Nat.zero_le _))
    have hneM : z ≠ M := fun e => hznot (e ▸ hsr'_eq ▸ hs_mem r' le_rfl)
    by_cases hlo : z ≤ L + g
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hlo⟩, hznot⟩)
    · by_cases hhi : M - g ≤ z
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hhi, by omega⟩, hznot⟩)
      · exact absurd (hmid z (by omega) (by omega)) hznot
  have h2bot := E875H3.bot_missing_le m r g L S b hr10 h5g_le_r (by omega) hstrict hg_eq
    (fun i j hi hj hjm => hs0_eq ▸ hswap_up 0 i j (Nat.zero_le _)
      (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩) hjm (by simp only [Finset.mem_Ico]; omega)
      (hmono i j (by omega) hjm))
  have h2top := E875H3.top_missing_le m r g M S b hr10 h5g_le_r (by omega) (by omega)
    (by
      have := hML_decomp
      have hr'1 : 0 < r' := by omega
      have h1 : r ≤ r * r' := Nat.le_mul_of_pos_right r hr'1
      omega) hstrict hg_eq
    (fun i j hi hj hjm => hsr'_eq ▸ hswap_down r' i j le_rfl
      (Finset.mem_Ico.mpr ⟨hj, by omega⟩) (by omega) (by simp only [Finset.mem_Ico]; omega)
      (hmono i j (by omega) hjm))
  have hsum_lb : g + (r - 1) * (h r' - h (r - 1)) ≤ ∑ i ∈ Finset.range r, (h (r' + i) - h i) := by
    have hsplit : ∑ i ∈ Finset.range r, (h (r' + i) - h i) =
        (h r' - h 0) + (h (r' + (r - 1)) - h (r - 1)) +
        ∑ i ∈ Finset.Ioo 0 (r - 1), (h (r' + i) - h i) := by
      have hset : Finset.range r = insert 0 (insert (r - 1) (Finset.Ioo 0 (r - 1))) := by
        ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]; omega
      rw [hset, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ioo]; omega),
          Finset.sum_insert (by simp only [Finset.mem_Ioo]; omega)]
      simp only [add_zero]; ring
    have hmid_lb : (r - 2) * (h r' - h (r - 1)) ≤ ∑ i ∈ Finset.Ioo 0 (r - 1), (h (r' + i) - h i) := by
      calc (r - 2) * (h r' - h (r - 1))
          = ∑ _i ∈ Finset.Ioo 0 (r - 1), (h r' - h (r - 1)) := by
            rw [Finset.sum_const, Nat.card_Ioo, smul_eq_mul, show r - 1 - 0 - 1 = r - 2 by omega]
        _ ≤ ∑ i ∈ Finset.Ioo 0 (r - 1), (h (r' + i) - h i) := Finset.sum_le_sum fun i hi => by
            obtain ⟨_, hi2⟩ := Finset.mem_Ioo.mp hi
            have u1 := hh_mono r' (r' + i) (by omega) (by omega)
            have u2 := hh_mono i (r - 1) (by omega) (by omega); omega
    have htop_idx : r' + (r - 1) = m - 1 := by omega
    rw [hsplit, hh0, htop_idx, hhm]
    have u1 := hh_mono (r - 1) r' (by omega) (by omega)
    have u2 := hh_mono r' (m - 1) (by omega) (by omega); rw [hhm] at u2
    have hmul : (r - 1) * (h r' - h (r - 1)) = (h r' - h (r - 1)) + (r - 2) * (h r' - h (r - 1)) := by
      have : r - 1 = 1 + (r - 2) := by omega
      rw [this, Nat.add_mul, one_mul]
    omega
  have hmiss_card : (Finset.Icc L M \ S).card ≤
      (Finset.Icc (L + 1) (L + g) \ S).card + (Finset.Icc (M - g) (M - 1) \ S).card :=
    (Finset.card_le_card hmiss_sub).trans (Finset.card_union_le _ _)
  have hδ_le : (h r - h (r - 1)) + (h r' - h (r' - 1)) ≤ 2 * (h r' - h (r - 1)) := by
    by_cases hrr : r' = r
    · rw [hrr]; omega
    · have : r' = r + 1 := by omega
      have u1 := hh_mono (r - 1) r (by omega) (by omega)
      have u2 := hh_mono r (r + 1) (by omega) (by omega)
      rw [this]; simp only [Nat.add_sub_cancel]; omega
  have hr_ge3 : 2 * (h r' - h (r - 1)) ≤ (r - 1) * (h r' - h (r - 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  change 2 * (Finset.Icc (L + 1) (L + g) \ S).card ≤ g + (h r - h (r - 1)) at h2bot
  change 2 * (Finset.Icc (M - g) (M - 1) \ S).card ≤ g + (h r' - h (r' - 1)) at h2top
  rw [hmiss_eq]; omega
