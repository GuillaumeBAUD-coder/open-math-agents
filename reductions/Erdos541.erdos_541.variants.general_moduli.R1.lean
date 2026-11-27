import FormalConjectures.ErdosProblems.«541»

namespace OMA.R_Erdos541_erdos_541_variants_general_moduli_R1

/-- Savchev--Chen (2007), normalized form: a zero-sum free sequence over `ZMod n` of length
greater than `n / 2` becomes, after multiplication by a suitable unit, a sequence whose
representatives in `[0, n)` have total sum less than `n`. -/
def H1 : Prop := ∀ (n : ℕ) (ι : Type) (U : Finset ι) (x : ι → ZMod n), 0 < n →
    (∀ W ⊆ U, W.Nonempty → ∑ i ∈ W, x i ≠ 0) → n < 2 * U.card →
    ∃ u : ZMod n, IsUnit u ∧ ∑ i ∈ U, (u * x i).val < n

/-- The central case `2 r = n` of the common zero-sum length. -/
def H2 : Prop := ∀ (n : ℕ) (a : Fin n → ZMod n) (r : ℕ),
    (∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, a i = 0 → S.card = r) →
    2 * r = n → (Set.range a).ncard ≤ 2

lemma sum_ge_card {ι : Type*} (s : Finset ι) (w : ι → ℕ) (h : ∀ i ∈ s, 1 ≤ w i) :
    s.card ≤ ∑ i ∈ s, w i := by
  simpa using Finset.card_nsmul_le_sum s w 1 h

lemma all_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℕ) (h : ∀ i ∈ s, 1 ≤ w i)
    (hs : ∑ i ∈ s, w i ≤ s.card) : ∀ i ∈ s, w i = 1 := by
  intro i hi
  by_contra hne
  have h2 : 2 ≤ w i := by have := h i hi; omega
  have e := Finset.add_sum_erase s w hi
  have hg := sum_ge_card (s.erase i) w (fun j hj => h j (Finset.mem_of_mem_erase hj))
  rw [Finset.card_erase_of_mem hi] at hg
  have : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
  omega

lemma exists_one {ι : Type*} (s : Finset ι) (w : ι → ℕ) (h : ∀ i ∈ s, 1 ≤ w i)
    (hs : ∑ i ∈ s, w i < 2 * s.card) : ∃ i ∈ s, w i = 1 := by
  by_contra hcon
  push Not at hcon
  have h2 : ∀ i ∈ s, 2 ≤ w i := fun i hi => by have := h i hi; have := hcon i hi; omega
  have h3 : 2 * s.card ≤ ∑ i ∈ s, w i := by
    simpa [mul_comm] using Finset.card_nsmul_le_sum s w 2 h2
  omega

lemma realize {ι : Type*} [DecidableEq ι] (w : ι → ℕ) : ∀ (N : ℕ) (s : Finset ι), s.card = N →
    (∀ i ∈ s, 1 ≤ w i) → ∑ i ∈ s, w i < 2 * s.card →
    ∀ k ≤ ∑ i ∈ s, w i, ∃ V ⊆ s, ∑ i ∈ V, w i = k := by
  intro N
  induction N with
  | zero =>
    intro s hs _ _ k hk
    rw [Finset.card_eq_zero] at hs
    subst hs
    simp at hk
    exact ⟨∅, by simp, by simp [hk]⟩
  | succ N ih =>
    intro s hs hpos hlt k hk
    have hne : s.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image s w hne
    by_cases hx1 : w x ≤ 1
    · have h1 : ∀ i ∈ s, w i = 1 := fun i hi => le_antisymm ((hmax i hi).trans hx1) (hpos i hi)
      have hsum : ∑ i ∈ s, w i = s.card := by rw [Finset.sum_congr rfl h1]; simp
      obtain ⟨V, hVs, hVc⟩ := Finset.exists_subset_card_eq (s := s) (n := k) (by omega)
      refine ⟨V, hVs, ?_⟩
      rw [Finset.sum_congr rfl (fun i hi => h1 i (hVs hi))]
      simp [hVc]
    · push Not at hx1
      have hsplit := Finset.add_sum_erase s w hx
      have hcard : (s.erase x).card = N := by rw [Finset.card_erase_of_mem hx]; omega
      have hpos' : ∀ i ∈ s.erase x, 1 ≤ w i := fun i hi => hpos i (Finset.mem_of_mem_erase hi)
      have hge := sum_ge_card (s.erase x) w hpos'
      have hlt' : ∑ i ∈ s.erase x, w i < 2 * (s.erase x).card := by omega
      by_cases hkle : k ≤ ∑ i ∈ s.erase x, w i
      · obtain ⟨V, hV, hVs⟩ := ih (s.erase x) hcard hpos' hlt' k hkle
        exact ⟨V, hV.trans (Finset.erase_subset x s), hVs⟩
      · obtain ⟨V, hV, hVs⟩ := ih (s.erase x) hcard hpos' hlt' (k - w x) (by omega)
        refine ⟨insert x V, Finset.insert_subset hx (hV.trans (Finset.erase_subset x s)), ?_⟩
        have hxV : x ∉ V := fun h => by simpa using hV h
        rw [Finset.sum_insert hxV]
        omega

section
variable {n : ℕ}

lemma cast_sum_val [NeZero n] (b : Fin n → ZMod n) (W : Finset (Fin n)) :
    ((∑ i ∈ W, (b i).val : ℕ) : ZMod n) = ∑ i ∈ W, b i := by
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => ZMod.natCast_zmod_val _)

lemma exch (b : Fin n → ZMod n) (r : ℕ)
    (hZ : ∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, b i = 0 → S.card = r)
    (T : Finset (Fin n)) (hT0 : ∑ i ∈ T, b i = 0) (hTc : T.card = r)
    (V W : Finset (Fin n)) (hV : V ⊆ T) (hW : W ⊆ Tᶜ)
    (hs : ∑ i ∈ V, b i = ∑ i ∈ W, b i) (hne : ((T \ V) ∪ W).Nonempty) :
    W.card = V.card := by
  have hdisj : Disjoint (T \ V) W := by
    rw [Finset.disjoint_left]
    intro i hi hiW
    exact (Finset.mem_compl.mp (hW hiW)) (Finset.mem_sdiff.mp hi).1
  have hsum : ∑ i ∈ (T \ V) ∪ W, b i = 0 := by
    rw [Finset.sum_union hdisj, Finset.sum_sdiff_eq_sub hV, hT0, hs]
    ring
  have h := hZ _ (Finset.nonempty_iff_ne_empty.mp hne) hsum
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hV] at h
  have := Finset.card_le_card hV
  omega

lemma free_compl (b : Fin n → ZMod n) (r : ℕ)
    (hZ : ∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, b i = 0 → S.card = r)
    (T : Finset (Fin n)) (hT0 : ∑ i ∈ T, b i = 0) (hTc : T.card = r) (hr : 1 ≤ r) :
    ∀ W ⊆ Tᶜ, W.Nonempty → ∑ i ∈ W, b i ≠ 0 := by
  intro W hW hWne h0
  have hd : Disjoint T W := by
    rw [Finset.disjoint_left]
    intro i hiT hiW
    exact (Finset.mem_compl.mp (hW hiW)) hiT
  have h1 := hZ W (Finset.nonempty_iff_ne_empty.mp hWne) h0
  have h2 := hZ (T ∪ W)
    (Finset.nonempty_iff_ne_empty.mp (hWne.mono Finset.subset_union_right))
    (by rw [Finset.sum_union hd, hT0, h0, add_zero])
  rw [Finset.card_union_of_disjoint hd] at h2
  omega

lemma free_erase (b : Fin n → ZMod n) (r : ℕ)
    (hZ : ∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, b i = 0 → S.card = r)
    (T : Finset (Fin n)) (hTc : T.card = r) (t : Fin n) (ht : t ∈ T) :
    ∀ W ⊆ T.erase t, W.Nonempty → ∑ i ∈ W, b i ≠ 0 := by
  intro W hW hWne h0
  have h1 := hZ W (Finset.nonempty_iff_ne_empty.mp hWne) h0
  have h2 := Finset.card_le_card hW
  rw [Finset.card_erase_of_mem ht] at h2
  have := Finset.card_pos.mpr hWne
  omega

lemma exists_zero_sum [NeZero n] (a : Fin n → ZMod n) :
    ∃ T : Finset (Fin n), T.Nonempty ∧ ∑ i ∈ T, a i = 0 := by
  let f : ℕ → ZMod n := fun k => ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i
  have hc : (Finset.univ : Finset (ZMod n)).card < (Finset.range (n + 1)).card := by
    simp [ZMod.card]
  obtain ⟨k1, hk1, k2, hk2, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc (f := f) (fun _ _ => Finset.mem_univ _)
  have key : ∀ k1 k2 : ℕ, k1 < k2 → k2 ≤ n → f k1 = f k2 →
      ∃ T : Finset (Fin n), T.Nonempty ∧ ∑ i ∈ T, a i = 0 := by
    intro k1 k2 hlt hle hf
    refine ⟨Finset.univ.filter (fun i : Fin n => k1 ≤ i.val ∧ i.val < k2), ⟨⟨k1, by omega⟩, by
      simp [hlt]⟩, ?_⟩
    have : ∑ i ∈ Finset.univ.filter (fun i : Fin n => k1 ≤ i.val ∧ i.val < k2), a i
        = f k2 - f k1 := by
      simp only [f, Finset.sum_filter]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> (try simp) <;> omega
    rw [this, hf, sub_self]
  simp only [Finset.mem_range] at hk1 hk2
  rcases lt_or_gt_of_ne hne with h | h
  · exact key k1 k2 h (by omega) heq
  · exact key k2 k1 h (by omega) heq.symm

lemma case1 [NeZero n] (b : Fin n → ZMod n) (r : ℕ)
    (hZ : ∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, b i = 0 → S.card = r)
    (T : Finset (Fin n)) (hT0 : ∑ i ∈ T, b i = 0) (hTc : T.card = r) (hr1 : 1 ≤ r)
    (hrn : 2 * r < n) (hU : ∑ i ∈ Tᶜ, (b i).val < n) :
    ∃ c1 c2 : ZMod n, ∀ i, b i = c1 ∨ b i = c2 := by
  have hfree := free_compl b r hZ T hT0 hTc hr1
  have hcardU : (Tᶜ).card = n - r := by rw [Finset.card_compl, Fintype.card_fin, hTc]
  have hpos : ∀ i ∈ Tᶜ, 1 ≤ (b i).val := by
    intro i hi
    have := hfree {i} (by simpa using hi) (by simp)
    rw [Finset.sum_singleton] at this
    exact ZMod.val_pos.mpr this
  have hge := sum_ge_card Tᶜ _ hpos
  have hval : ∀ i, (((b i).val : ℕ) : ZMod n) = b i := fun i => ZMod.natCast_zmod_val _
  have hUone : ∑ i ∈ Tᶜ, (b i).val ≤ n - r → ∀ i ∈ Tᶜ, b i = 1 := by
    intro h i hi
    have := all_one Tᶜ _ hpos (by omega) i hi
    rw [← hval i, this, Nat.cast_one]
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · have hr : r = 1 := by omega
    obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp (hTc.trans hr)
    refine ⟨1, b t, fun i => ?_⟩
    by_cases hi : i = t
    · right; rw [hi]
    · left; exact hUone (by omega) i (by simp [hi])
  · have hnz : ∀ i, b i ≠ 0 := by
      intro i h
      have := hZ {i} (by simp) (by simp [h])
      simp at this
      omega
    obtain ⟨o, hoU, ho1⟩ := exists_one Tᶜ _ hpos (by omega)
    have hreal := realize (fun i => (b i).val) _ Tᶜ rfl hpos (by omega)
    have hpos' : ∀ i ∈ Tᶜ.erase o, 1 ≤ (b i).val :=
      fun i hi => hpos i (Finset.mem_of_mem_erase hi)
    have hsplit := Finset.add_sum_erase Tᶜ (fun i => (b i).val) hoU
    try simp only at hsplit
    have hreal' := realize (fun i => (b i).val) _ (Tᶜ.erase o) rfl hpos'
      (by rw [Finset.card_erase_of_mem hoU]; omega)
    have hT : ∀ t ∈ T, (b t).val = 1 ∨ ∑ i ∈ Tᶜ, (b i).val < (b t).val := by
      intro t ht
      by_contra hcon
      push Not at hcon
      obtain ⟨hne1, hle⟩ := hcon
      have hy1 : 1 ≤ (b t).val := ZMod.val_pos.mpr (hnz t)
      obtain ⟨W', hW', hW's⟩ := hreal' ((b t).val - 1) (by omega)
      try simp only at hW's
      have hoW' : o ∉ W' := fun h => by simpa using hW' h
      have hW'ne : W'.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp at hW's
        omega
      have hWU : insert o W' ⊆ Tᶜ :=
        Finset.insert_subset hoU (hW'.trans (Finset.erase_subset _ _))
      have hs : ∑ i ∈ ({t} : Finset (Fin n)), b i = ∑ i ∈ insert o W', b i := by
        rw [Finset.sum_singleton, ← cast_sum_val b (insert o W'), Finset.sum_insert hoW', ho1,
          hW's, show 1 + ((b t).val - 1) = (b t).val by omega, hval]
      have hc := exch b r hZ T hT0 hTc {t} (insert o W') (by simpa using ht) hWU hs
        ⟨o, Finset.mem_union_right _ (Finset.mem_insert_self _ _)⟩
      rw [Finset.card_insert_of_notMem hoW', Finset.card_singleton] at hc
      have := Finset.card_pos.mpr hW'ne
      omega
    by_cases hbig : ∃ t ∈ T, ∑ i ∈ Tᶜ, (b i).val < (b t).val
    · have hkey : ∀ t ∈ T, ∑ i ∈ Tᶜ, (b i).val < (b t).val →
          (b t).val = n - r + 1 ∧ ∑ i ∈ Tᶜ, (b i).val ≤ n - r := by
        intro t ht hlt
        have hyn : (b t).val < n := ZMod.val_lt _
        obtain ⟨W, hWU, hWs⟩ := hreal (n - (b t).val) (by omega)
        try simp only at hWs
        have htW : t ∉ W := fun h => by
          have := hWU h
          rw [Finset.mem_compl] at this
          exact this ht
        have hz : ∑ i ∈ insert t W, b i = 0 := by
          rw [Finset.sum_insert htW, ← cast_sum_val b W, hWs]
          have : (((b t).val : ℕ) : ZMod n) + ((n - (b t).val : ℕ) : ZMod n) = 0 := by
            rw [← Nat.cast_add, Nat.add_sub_cancel' hyn.le, ZMod.natCast_self]
          rwa [hval] at this
        have hc := hZ _ (Finset.insert_ne_empty _ _) hz
        rw [Finset.card_insert_of_notMem htW] at hc
        have hWge := sum_ge_card W _ (fun i hi => hpos i (hWU hi))
        omega
      obtain ⟨t0, ht0, hlt0⟩ := hbig
      have hUle := (hkey t0 ht0 hlt0).2
      refine ⟨1, ((n - r + 1 : ℕ) : ZMod n), fun i => ?_⟩
      by_cases hiT : i ∈ T
      · rcases hT i hiT with h | h
        · left; rw [← hval i, h, Nat.cast_one]
        · right; rw [← hval i, (hkey i hiT h).1]
      · left; exact hUone hUle i (by simpa using hiT)
    · push Not at hbig
      exfalso
      have hall : ∀ t ∈ T, (b t).val = 1 :=
        fun t ht => (hT t ht).resolve_right (not_lt.mpr (hbig t ht))
      have hsumT : ∑ i ∈ T, (b i).val = r := by
        rw [Finset.sum_congr rfl hall]; simp [hTc]
      have h0 : ((r : ℕ) : ZMod n) = 0 := by rw [← hsumT, cast_sum_val, hT0]
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := Nat.le_of_dvd (by omega) h0
      omega

lemma case2 [NeZero n] (b : Fin n → ZMod n) (r : ℕ)
    (hZ : ∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, b i = 0 → S.card = r)
    (T : Finset (Fin n)) (hT0 : ∑ i ∈ T, b i = 0) (hTc : T.card = r)
    (t0 : Fin n) (ht0 : t0 ∈ T)
    (hrn : n + 1 < 2 * r) (hT' : ∑ i ∈ T.erase t0, (b i).val < n) :
    ∃ c1 c2 : ZMod n, ∀ i, b i = c1 ∨ b i = c2 := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hrle : r ≤ n := by
    rw [← hTc]; simpa using Finset.card_le_univ T
  have hval : ∀ i, (((b i).val : ℕ) : ZMod n) = b i := fun i => ZMod.natCast_zmod_val _
  have hnz : ∀ i, b i ≠ 0 := by
    intro i h
    have := hZ {i} (by simp) (by simp [h])
    simp at this
    omega
  have hpos : ∀ i, 1 ≤ (b i).val := fun i => ZMod.val_pos.mpr (hnz i)
  have hsplit0 := Finset.add_sum_erase T (fun i => (b i).val) ht0
  try simp only at hsplit0
  have hsumT : ∑ i ∈ T, (b i).val = n := by
    have hd : n ∣ ∑ i ∈ T, (b i).val := by
      rw [← ZMod.natCast_eq_zero_iff, cast_sum_val, hT0]
    have hlt : ∑ i ∈ T, (b i).val < 2 * n := by have := ZMod.val_lt (b t0); omega
    have hp : 0 < ∑ i ∈ T, (b i).val := by have := hpos t0; omega
    obtain ⟨k, hk⟩ := hd
    have hk2 : k < 2 := by
      by_contra hcon
      push Not at hcon
      have := Nat.mul_le_mul_left n hcon
      omega
    interval_cases k
    · omega
    · omega
  obtain ⟨o, hoT, ho1⟩ := exists_one T _ (fun i _ => hpos i) (by omega)
  have hsplit := Finset.add_sum_erase T (fun i => (b i).val) hoT
  try simp only at hsplit
  have hreal' := realize (fun i => (b i).val) _ (T.erase o) rfl (fun i _ => hpos i)
    (by rw [Finset.card_erase_of_mem hoT]; omega)
  have hUone : ∀ i ∈ Tᶜ, (b i).val = 1 := by
    intro i hi
    by_contra hne
    have h2 : 2 ≤ (b i).val := by have := hpos i; omega
    have hlt := ZMod.val_lt (b i)
    obtain ⟨V', hV', hV's⟩ := hreal' ((b i).val - 1) (by omega)
    try simp only at hV's
    have hoV' : o ∉ V' := fun h => by simpa using hV' h
    have hV'ne : V'.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hV's
      omega
    have hVT : insert o V' ⊆ T :=
      Finset.insert_subset hoT (hV'.trans (Finset.erase_subset _ _))
    have hs : ∑ j ∈ insert o V', b j = ∑ j ∈ ({i} : Finset (Fin n)), b j := by
      rw [Finset.sum_singleton, ← cast_sum_val b (insert o V'), Finset.sum_insert hoV', ho1,
        hV's, show 1 + ((b i).val - 1) = (b i).val by omega, hval]
    have hc := exch b r hZ T hT0 hTc (insert o V') {i} hVT (by simpa using hi) hs
      ⟨i, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
    rw [Finset.card_insert_of_notMem hoV', Finset.card_singleton] at hc
    have := Finset.card_pos.mpr hV'ne
    omega
  by_cases hrn' : r = n
  · have hTu : T = Finset.univ := Finset.eq_univ_of_card T (by rw [hTc, hrn', Fintype.card_fin])
    have h1 := all_one T (fun i => (b i).val) (fun i _ => hpos i) (by omega)
    refine ⟨1, 1, fun i => Or.inl ?_⟩
    rw [← hval i, h1 i (by rw [hTu]; exact Finset.mem_univ _), Nat.cast_one]
  · have hrlt : r < n := lt_of_le_of_ne hrle hrn'
    have hTbig : ∀ x ∈ T, (b x).val = 1 ∨ n - r + 1 ≤ (b x).val := by
      intro x hx
      by_contra hcon
      push Not at hcon
      obtain ⟨hne1, hle⟩ := hcon
      have h2 : 2 ≤ (b x).val := by have := hpos x; omega
      obtain ⟨W, hW, hWc⟩ := Finset.exists_subset_card_eq (s := Tᶜ) (n := (b x).val)
        (by rw [Finset.card_compl, Fintype.card_fin, hTc]; omega)
      have hWs : ∑ i ∈ W, (b i).val = (b x).val := by
        rw [Finset.sum_congr rfl (fun i hi => hUone i (hW hi))]
        simp [hWc]
      have hs : ∑ i ∈ ({x} : Finset (Fin n)), b i = ∑ i ∈ W, b i := by
        rw [Finset.sum_singleton, ← cast_sum_val b W, hWs, hval]
      have hWne : W.Nonempty := by rw [← Finset.card_pos]; omega
      obtain ⟨w, hw⟩ := hWne
      have hc := exch b r hZ T hT0 hTc {x} W (by simpa using hx) hW hs
        ⟨w, Finset.mem_union_right _ hw⟩
      rw [Finset.card_singleton] at hc
      omega
    by_cases hex : ∃ x ∈ T, (b x).val ≠ 1
    · obtain ⟨x, hx, hx1⟩ := hex
      have huniq : ∀ y ∈ T, y ≠ x → (b y).val = 1 := by
        intro y hy hyx
        by_contra hy1
        have hxb := (hTbig x hx).resolve_left hx1
        have hyb := (hTbig y hy).resolve_left hy1
        have e1 := Finset.add_sum_erase T (fun i => (b i).val) hx
        have hyE : y ∈ T.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
        have e2 := Finset.add_sum_erase (T.erase x) (fun i => (b i).val) hyE
        try simp only at e1 e2
        have hge := sum_ge_card ((T.erase x).erase y) (fun i => (b i).val) (fun i _ => hpos i)
        rw [Finset.card_erase_of_mem hyE, Finset.card_erase_of_mem hx] at hge
        omega
      refine ⟨1, b x, fun i => ?_⟩
      by_cases hi : i = x
      · right; rw [hi]
      · left
        by_cases hiT : i ∈ T
        · rw [← hval i, huniq i hiT hi, Nat.cast_one]
        · rw [← hval i, hUone i (by simpa using hiT), Nat.cast_one]
    · push Not at hex
      refine ⟨1, 1, fun i => Or.inl ?_⟩
      by_cases hiT : i ∈ T
      · rw [← hval i, hex i hiT, Nat.cast_one]
      · rw [← hval i, hUone i (by simpa using hiT), Nat.cast_one]

lemma free_swap (b : Fin n → ZMod n) (r : ℕ)
    (hZ : ∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, b i = 0 → S.card = r)
    (T : Finset (Fin n)) (hT0 : ∑ i ∈ T, b i = 0) (hTc : T.card = r)
    (t : Fin n) (ht : t ∈ T) (x : Fin n) (hx : x ∈ Tᶜ) (hne : b x ≠ b t) :
    ∀ W ⊆ insert x (T.erase t), W.Nonempty → ∑ i ∈ W, b i ≠ 0 := by
  intro W hW hWne h0
  have hxT : x ∉ T.erase t := fun h => (Finset.mem_compl.mp hx) (Finset.mem_of_mem_erase h)
  by_cases hxW : x ∈ W
  · have hc := hZ W (Finset.nonempty_iff_ne_empty.mp hWne) h0
    have hcX : (insert x (T.erase t)).card = r := by
      rw [Finset.card_insert_of_notMem hxT, Finset.card_erase_of_mem ht]
      have := Finset.card_pos.mpr ⟨t, ht⟩
      omega
    have hWX : W = insert x (T.erase t) := Finset.eq_of_subset_of_card_le hW (by omega)
    rw [hWX, Finset.sum_insert hxT, Finset.sum_erase_eq_sub ht, hT0] at h0
    apply hne
    have : b x - b t = 0 := by rw [← h0]; ring
    exact sub_eq_zero.mp this
  · have hW' : W ⊆ T.erase t := by
      intro i hi
      have := hW hi
      rw [Finset.mem_insert] at this
      rcases this with h | h
      · exact absurd (h ▸ hi) hxW
      · exact h
    exact free_erase b r hZ T hTc t ht W hW' hWne h0

lemma free_add (b : Fin n → ZMod n) (r : ℕ)
    (hZ : ∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, b i = 0 → S.card = r)
    (T : Finset (Fin n)) (hT0 : ∑ i ∈ T, b i = 0) (hTc : T.card = r) (hr1 : 1 ≤ r)
    (hcard : (Tᶜ).card + 1 = r)
    (t : Fin n) (ht : t ∈ T) (hne : b t + ∑ i ∈ Tᶜ, b i ≠ 0) :
    ∀ W ⊆ insert t Tᶜ, W.Nonempty → ∑ i ∈ W, b i ≠ 0 := by
  intro W hW hWne h0
  have htU : t ∉ Tᶜ := fun h => (Finset.mem_compl.mp h) ht
  by_cases htW : t ∈ W
  · have hc := hZ W (Finset.nonempty_iff_ne_empty.mp hWne) h0
    have hcX : (insert t Tᶜ).card = r := by rw [Finset.card_insert_of_notMem htU]; omega
    have hWX : W = insert t Tᶜ := Finset.eq_of_subset_of_card_le hW (by omega)
    rw [hWX, Finset.sum_insert htU] at h0
    exact hne h0
  · have hW' : W ⊆ Tᶜ := by
      intro i hi
      have := hW hi
      rw [Finset.mem_insert] at this
      rcases this with h | h
      · exact absurd (h ▸ hi) htW
      · exact h
    exact free_compl b r hZ T hT0 hTc hr1 W hW' hWne h0

lemma case3 [NeZero n] (b : Fin n → ZMod n) (r : ℕ)
    (hZ : ∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, b i = 0 → S.card = r)
    (T : Finset (Fin n)) (hT0 : ∑ i ∈ T, b i = 0) (hTc : T.card = r)
    (hr : 2 * r = n + 1) (hr2 : 2 ≤ r) (t : Fin n) (ht : t ∈ T)
    (hW : ∑ i ∈ insert t Tᶜ, (b i).val < n) :
    ∃ c1 c2 : ZMod n, ∀ i, b i = c1 ∨ b i = c2 := by
  have hval : ∀ i, (((b i).val : ℕ) : ZMod n) = b i := fun i => ZMod.natCast_zmod_val _
  have hnz : ∀ i, b i ≠ 0 := by
    intro i h
    have := hZ {i} (by simp) (by simp [h])
    simp at this
    omega
  have hpos : ∀ i, 1 ≤ (b i).val := fun i => ZMod.val_pos.mpr (hnz i)
  have htU : t ∉ Tᶜ := fun h => (Finset.mem_compl.mp h) ht
  rw [Finset.sum_insert htU] at hW
  have hvt := hpos t
  have hcardU : (Tᶜ).card = r - 1 := by rw [Finset.card_compl, Fintype.card_fin, hTc]; omega
  have hge := sum_ge_card Tᶜ _ (fun i _ => hpos i)
  have hreal := realize (fun i => (b i).val) _ Tᶜ rfl (fun i _ => hpos i) (by omega)
  -- (a) every element of `T` is at most `n - Σ_U`
  have ha : ∀ x ∈ T, (b x).val + ∑ i ∈ Tᶜ, (b i).val ≤ n := by
    intro x hx
    by_contra hcon
    have hyn : (b x).val < n := ZMod.val_lt _
    obtain ⟨W, hWU, hWs⟩ := hreal (n - (b x).val) (by omega)
    have hxW : x ∉ W := fun h => (Finset.mem_compl.mp (hWU h)) hx
    have hz : ∑ i ∈ insert x W, b i = 0 := by
      rw [Finset.sum_insert hxW, ← cast_sum_val b W, hWs]
      have : (((b x).val : ℕ) : ZMod n) + ((n - (b x).val : ℕ) : ZMod n) = 0 := by
        rw [← Nat.cast_add, Nat.add_sub_cancel' hyn.le, ZMod.natCast_self]
      rwa [hval] at this
    have hc := hZ _ (Finset.insert_ne_empty _ _) hz
    rw [Finset.card_insert_of_notMem hxW] at hc
    have hWeq : W = Tᶜ := Finset.eq_of_subset_of_card_le hWU (by omega)
    rw [hWeq] at hWs
    omega
  by_cases hsmall : ∑ i ∈ Tᶜ, (b i).val ≤ n - 3
  · obtain ⟨o, hoU, ho1⟩ := exists_one Tᶜ _ (fun i _ => hpos i) (by omega)
    have hsplit := Finset.add_sum_erase Tᶜ (fun i => (b i).val) hoU
    have hreal' := realize (fun i => (b i).val) _ (Tᶜ.erase o) rfl (fun i _ => hpos i)
      (by rw [Finset.card_erase_of_mem hoU]; omega)
    have hT : ∀ x ∈ T, (b x).val = 1 ∨ ∑ i ∈ Tᶜ, (b i).val < (b x).val := by
      intro x hx
      by_contra hcon
      push Not at hcon
      obtain ⟨hne1, hle⟩ := hcon
      have hy1 := hpos x
      obtain ⟨W', hW', hW's⟩ := hreal' ((b x).val - 1) (by omega)
      have hoW' : o ∉ W' := fun h => by simpa using hW' h
      have hW'ne : W'.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp at hW's
        omega
      have hWU : insert o W' ⊆ Tᶜ :=
        Finset.insert_subset hoU (hW'.trans (Finset.erase_subset _ _))
      have hs : ∑ i ∈ ({x} : Finset (Fin n)), b i = ∑ i ∈ insert o W', b i := by
        rw [Finset.sum_singleton, ← cast_sum_val b (insert o W'), Finset.sum_insert hoW', ho1,
          hW's, show 1 + ((b x).val - 1) = (b x).val by omega, hval]
      have hc := exch b r hZ T hT0 hTc {x} (insert o W') (by simpa using hx) hWU hs
        ⟨o, Finset.mem_union_right _ (Finset.mem_insert_self _ _)⟩
      rw [Finset.card_insert_of_notMem hoW', Finset.card_singleton] at hc
      have := Finset.card_pos.mpr hW'ne
      omega
    by_cases hbig : ∃ x ∈ T, ∑ i ∈ Tᶜ, (b i).val < (b x).val
    · obtain ⟨x0, hx0, hlt0⟩ := hbig
      have h0 := ha x0 hx0
      have hUr : ∑ i ∈ Tᶜ, (b i).val ≤ (Tᶜ).card := by omega
      have hUone := all_one Tᶜ _ (fun i _ => hpos i) hUr
      refine ⟨1, ((r : ℕ) : ZMod n), fun i => ?_⟩
      by_cases hiT : i ∈ T
      · rcases hT i hiT with h | h
        · left; rw [← hval i, h, Nat.cast_one]
        · right
          have := ha i hiT
          rw [← hval i, show (b i).val = r by omega]
      · left; rw [← hval i, hUone i (by simpa using hiT), Nat.cast_one]
    · push Not at hbig
      exfalso
      have hall : ∀ x ∈ T, (b x).val = 1 :=
        fun x hx => (hT x hx).resolve_right (not_lt.mpr (hbig x hx))
      have hsumT : ∑ i ∈ T, (b i).val = r := by
        rw [Finset.sum_congr rfl hall]; simp [hTc]
      have h0 : ((r : ℕ) : ZMod n) = 0 := by rw [← hsumT, cast_sum_val, hT0]
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := Nat.le_of_dvd (by omega) h0
      omega
  · push Not at hsmall
    have hT2 : ∀ x ∈ T, (b x).val ≤ 2 := fun x hx => by have := ha x hx; omega
    have hsumle : ∑ i ∈ T, (b i).val ≤ 2 * r := by
      have := Finset.sum_le_card_nsmul T (fun i => (b i).val) 2 hT2
      simp only [smul_eq_mul] at this
      rw [hTc] at this
      omega
    have hsumT : ∑ i ∈ T, (b i).val = n := by
      have hd : n ∣ ∑ i ∈ T, (b i).val := by
        rw [← ZMod.natCast_eq_zero_iff, cast_sum_val, hT0]
      have hp : r ≤ ∑ i ∈ T, (b i).val := by
        have := sum_ge_card T _ (fun i _ => hpos i); omega
      obtain ⟨k, hk⟩ := hd
      have hk2 : k < 2 := by
        by_contra hcon
        push Not at hcon
        have := Nat.mul_le_mul_left n hcon
        omega
      interval_cases k
      · omega
      · omega
    have hrealT := realize (fun i => (b i).val) _ T rfl (fun i _ => hpos i) (by omega)
    have hU2 : ∀ u ∈ Tᶜ, (b u).val ≤ 2 := by
      intro u hu
      by_contra hcon
      have hlt := ZMod.val_lt (b u)
      obtain ⟨V, hV, hVs⟩ := hrealT (b u).val (by omega)
      have hV2 : ∑ i ∈ V, (b i).val ≤ 2 * V.card := by
        have := Finset.sum_le_card_nsmul V (fun i => (b i).val) 2 (fun i hi => hT2 i (hV hi))
        simp only [smul_eq_mul] at this
        omega
      have hs : ∑ i ∈ V, b i = ∑ i ∈ ({u} : Finset (Fin n)), b i := by
        rw [Finset.sum_singleton, ← cast_sum_val b V, hVs, hval]
      have hc := exch b r hZ T hT0 hTc V {u} hV (by simpa using hu) hs
        ⟨u, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
      rw [Finset.card_singleton] at hc
      omega
    refine ⟨1, ((2 : ℕ) : ZMod n), fun i => ?_⟩
    have h2 : (b i).val ≤ 2 := by
      by_cases hiT : i ∈ T
      · exact hT2 i hiT
      · exact hU2 i (by simpa using hiT)
    have h1 := hpos i
    rcases (show (b i).val = 1 ∨ (b i).val = 2 by omega) with h | h
    · left; rw [← hval i, h, Nat.cast_one]
    · right; rw [← hval i, h]

lemma case3_const [NeZero n] (b : Fin n → ZMod n) (r : ℕ)
    (hZ : ∀ S : Finset (Fin n), S ≠ ∅ → ∑ i ∈ S, b i = 0 → S.card = r)
    (T : Finset (Fin n)) (hT0 : ∑ i ∈ T, b i = 0) (hTc : T.card = r)
    (hr : 2 * r = n + 1) (hr2 : 2 ≤ r) (t : Fin n) (ht : t ∈ T) (x : Fin n) (hx : x ∈ Tᶜ)
    (hX : ∑ i ∈ insert x (T.erase t), (b i).val < n) (hconst : ∀ y ∈ T, b y = b t) : False := by
  have hnz : ∀ i, b i ≠ 0 := by
    intro i h
    have := hZ {i} (by simp) (by simp [h])
    simp at this
    omega
  have hxT : x ∉ T.erase t := fun h => (Finset.mem_compl.mp hx) (Finset.mem_of_mem_erase h)
  rw [Finset.sum_insert hxT] at hX
  have hc : ∀ y ∈ T, (b y).val = (b t).val := fun y hy => by rw [hconst y hy]
  have hsT : ∑ i ∈ T, (b i).val = r * (b t).val := by
    rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, hTc]
  have hsT' : ∑ i ∈ T.erase t, (b i).val = (r - 1) * (b t).val := by
    rw [Finset.sum_congr rfl (fun y hy => hc y (Finset.mem_of_mem_erase hy)), Finset.sum_const,
      smul_eq_mul, Finset.card_erase_of_mem ht, hTc]
  have hd : n ∣ r * (b t).val := by
    rw [← hsT, ← ZMod.natCast_eq_zero_iff, cast_sum_val, hT0]
  have hw := ZMod.val_pos.mpr (hnz t)
  have hrel : (r - 1) * (b t).val + (b t).val = r * (b t).val := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  obtain ⟨k, hk⟩ := hd
  have hk2 : k < 2 := by
    by_contra hcon
    push Not at hcon
    have := Nat.mul_le_mul_left n hcon
    have := ZMod.val_lt (b t)
    omega
  interval_cases k
  · omega
  · rcases Nat.lt_or_ge (b t).val 2 with h | h
    · have h1 : (b t).val = 1 := by omega
      rw [h1, mul_one] at hk
      omega
    · have := Nat.mul_le_mul_left r h
      omega

end

theorem main : H1 → H2 → type_of% @Erdos541.erdos_541.variants.general_moduli := by
  intro h1 h2 p a ⟨r, hZ⟩
  by_cases hp : p ≤ 2
  · calc (Set.range a).ncard = (Finset.univ.image a).card := by
          rw [← Set.ncard_coe_finset]; simp
      _ ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_image_le
      _ ≤ 2 := by simpa using hp
  · push Not at hp
    have : NeZero p := ⟨by omega⟩
    obtain ⟨T, hTne, hT0⟩ := exists_zero_sum a
    have hTc := hZ T (Finset.nonempty_iff_ne_empty.mp hTne) hT0
    have hr1 : 1 ≤ r := hTc ▸ Finset.card_pos.mpr hTne
    obtain ⟨t0, ht0⟩ := hTne
    have fin : ∀ u : ZMod p, IsUnit u →
        (∃ c1 c2 : ZMod p, ∀ i, u * a i = c1 ∨ u * a i = c2) → (Set.range a).ncard ≤ 2 := by
      intro u hu ⟨c1, c2, hc⟩
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      have hsub : Set.range a ⊆ {v * c1, v * c2} := by
        rintro _ ⟨i, rfl⟩
        have e : a i = v * (u * a i) := by rw [← mul_assoc, hv, one_mul]
        rcases hc i with h | h
        · rw [e, h]; exact Set.mem_insert _ _
        · rw [e, h]; exact Set.mem_insert_of_mem _ rfl
      calc (Set.range a).ncard ≤ ({v * c1, v * c2} : Set (ZMod p)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({v * c2} : Set (ZMod p)).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have hZb : ∀ u : ZMod p, IsUnit u →
        ∀ S : Finset (Fin p), S ≠ ∅ → ∑ i ∈ S, u * a i = 0 → S.card = r := by
      intro u hu S hS h
      rw [← Finset.mul_sum] at h
      exact hZ S hS ((hu.mul_right_eq_zero).mp h)
    have hT0b : ∀ u : ZMod p, ∑ i ∈ T, u * a i = 0 := by
      intro u; rw [← Finset.mul_sum, hT0, mul_zero]
    have hrle : r ≤ p := by rw [← hTc]; simpa using Finset.card_le_univ T
    have hconst : (∀ x ∈ Tᶜ, ∀ t ∈ T, a x = a t) → (∀ t ∈ T, a t = a t0) →
        (Set.range a).ncard ≤ 2 := by
      intro hUT hTT
      refine fin 1 isUnit_one ⟨a t0, a t0, fun i => Or.inl ?_⟩
      rw [one_mul]
      by_cases hiT : i ∈ T
      · exact hTT i hiT
      · rw [hUT i (by simpa using hiT) t0 ht0]
    rcases lt_or_ge (2 * r) p with h | h
    · obtain ⟨u, hu, hsum⟩ := h1 p (Fin p) Tᶜ a (by omega)
        (free_compl a r hZ T hT0 hTc hr1)
        (by rw [Finset.card_compl, Fintype.card_fin]; omega)
      exact fin u hu (case1 (fun i => u * a i) r (hZb u hu) T (hT0b u) hTc hr1 h hsum)
    · rcases lt_or_ge (p + 2) (2 * r) with h' | h'
      · obtain ⟨u, hu, hsum⟩ := h1 p (Fin p) (T.erase t0) a (by omega)
          (free_erase a r hZ T hTc t0 ht0)
          (by rw [Finset.card_erase_of_mem ht0]; omega)
        exact fin u hu (case2 (fun i => u * a i) r (hZb u hu) T (hT0b u) hTc t0 ht0
          (by omega) hsum)
      · rcases (show 2 * r = p ∨ 2 * r = p + 1 ∨ 2 * r = p + 2 by omega) with he | he | he
        · exact h2 p a r hZ he
        · -- `2 r = p + 1`
          by_cases hex : ∃ t ∈ T, a t + ∑ i ∈ Tᶜ, a i ≠ 0
          · obtain ⟨t, ht, hne⟩ := hex
            have hcU : (Tᶜ).card + 1 = r := by
              rw [Finset.card_compl, Fintype.card_fin]; omega
            have htU : t ∉ Tᶜ := fun h => (Finset.mem_compl.mp h) ht
            obtain ⟨u, hu, hsum⟩ := h1 p (Fin p) (insert t Tᶜ) a (by omega)
              (free_add a r hZ T hT0 hTc hr1 hcU t ht hne)
              (by rw [Finset.card_insert_of_notMem htU]; omega)
            exact fin u hu (case3 (fun i => u * a i) r (hZb u hu) T (hT0b u) hTc he
              (by omega) t ht hsum)
          · push Not at hex
            have hTT : ∀ t ∈ T, a t = a t0 := by
              intro t ht
              have e1 := hex t ht
              have e2 := hex t0 ht0
              rw [← sub_eq_zero]
              calc a t - a t0 = (a t + ∑ i ∈ Tᶜ, a i) - (a t0 + ∑ i ∈ Tᶜ, a i) := by ring
                _ = 0 := by rw [e1, e2, sub_zero]
            by_cases hex2 : ∃ x ∈ Tᶜ, a x ≠ a t0
            · exfalso
              obtain ⟨x, hx, hxne⟩ := hex2
              have hxT : x ∉ T.erase t0 :=
                fun h => (Finset.mem_compl.mp hx) (Finset.mem_of_mem_erase h)
              obtain ⟨u, hu, hsum⟩ := h1 p (Fin p) (insert x (T.erase t0)) a (by omega)
                (free_swap a r hZ T hT0 hTc t0 ht0 x hx hxne)
                (by rw [Finset.card_insert_of_notMem hxT, Finset.card_erase_of_mem ht0]; omega)
              exact case3_const (fun i => u * a i) r (hZb u hu) T (hT0b u) hTc he (by omega)
                t0 ht0 x hx hsum (fun y hy => by show u * a y = u * a t0; rw [hTT y hy])
            · push Not at hex2
              exact hconst (fun x hx t ht => by rw [hex2 x hx, hTT t ht]) hTT
        · -- `2 r = p + 2`
          by_cases hex2 : ∃ x ∈ Tᶜ, ∃ t ∈ T, a x ≠ a t
          · obtain ⟨x, hx, t, ht, hxne⟩ := hex2
            have hxT : x ∉ T.erase t :=
              fun h => (Finset.mem_compl.mp hx) (Finset.mem_of_mem_erase h)
            obtain ⟨u, hu, hsum⟩ := h1 p (Fin p) (insert x (T.erase t)) a (by omega)
              (free_swap a r hZ T hT0 hTc t ht x hx hxne)
              (by rw [Finset.card_insert_of_notMem hxT, Finset.card_erase_of_mem ht]; omega)
            have hsum' : ∑ i ∈ T.erase t, (u * a i).val < p := by
              rw [Finset.sum_insert hxT] at hsum
              omega
            exact fin u hu (case2 (fun i => u * a i) r (hZb u hu) T (hT0b u) hTc t ht
              (by omega) hsum')
          · push Not at hex2
            have hUne : (Tᶜ).Nonempty := by
              rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]; omega
            obtain ⟨x0, hx0⟩ := hUne
            exact hconst hex2 (fun t ht => by rw [← hex2 x0 hx0 t ht, hex2 x0 hx0 t0 ht0])

end OMA.R_Erdos541_erdos_541_variants_general_moduli_R1
