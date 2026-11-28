import OMAStatements.S_oeis_a381636

namespace OeisA381636

open OMA.S_oeis_a381636

-- ============================================================================
-- Section 1: Basic Helpers on Prime Indices, Constant Blocks, and Runs
-- ============================================================================

private lemma primeIndices_pos {n v : ℕ} (hv : v ∈ primeIndices n) : 1 ≤ v := by
  rw [primeIndices, Multiset.mem_coe, primeIndexList, List.mem_map] at hv
  obtain ⟨p, hp_mem, rfl⟩ := hv
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactorsList hp_mem
  have h2 : 2 ≤ p := hp.two_le
  have hmono : Nat.primeCounting 2 ≤ Nat.primeCounting p := Nat.monotone_primeCounting h2
  have hpc2 : Nat.primeCounting 2 = 1 := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    decide
  omega

private lemma mem_A382876_pos_iff (n : ℕ) :
    0 < A382876 n ↔ ∃ l : List ℕ, l.Perm (primeIndexList n) ∧ (runSums l).Nodup := by
  unfold A382876
  rw [Finset.card_pos]
  constructor
  · rintro ⟨l, hl⟩
    rw [Finset.mem_filter, List.mem_toFinset, List.mem_permutations] at hl
    exact ⟨l, hl.1, hl.2⟩
  · rintro ⟨l, hperm, hnodup⟩
    exact ⟨l, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_permutations.mpr hperm), hnodup⟩⟩

private lemma list_eq_replicate_of_isChain_beq :
    ∀ (r : List ℕ), r ≠ [] → (r.IsChain fun x y => (x == y) = true) →
      ∃ v : ℕ, r = List.replicate r.length v
  | [], hne, _ => absurd rfl hne
  | [a], _, _ => ⟨a, rfl⟩
  | a :: b :: t, _, hc => by
    rw [List.isChain_cons_cons] at hc
    have hab : a = b := beq_iff_eq.mp hc.1
    obtain ⟨v, hv⟩ := list_eq_replicate_of_isChain_beq (b :: t) (List.cons_ne_nil b t) hc.2
    have hbv : b = v := by
      have hhd := congrArg List.head? hv
      simp [List.replicate_succ] at hhd
      exact hhd
    subst hab
    subst hbv
    refine ⟨a, ?_⟩
    simp only [List.length_cons, List.replicate_succ]
    exact congrArg (List.cons a) hv

private lemma multiset_sum_coe_map (R : List (List ℕ)) :
    (Multiset.ofList (R.map Multiset.ofList)).sum = Multiset.ofList R.flatten := by
  induction R with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.flatten_cons]
    change (Multiset.ofList r ::ₘ Multiset.ofList (rs.map Multiset.ofList)).sum =
      Multiset.ofList (r ++ rs.flatten)
    rw [Multiset.sum_cons, ih]
    exact (Multiset.coe_add r rs.flatten).symm

private def blockColor (b : Multiset ℕ) : ℕ :=
  b.sum / Multiset.card b

private lemma blockColor_replicate {k v : ℕ} (hk : k ≠ 0) :
    blockColor (Multiset.replicate k v) = v := by
  unfold blockColor
  rw [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    Nat.mul_div_cancel_left v (Nat.pos_of_ne_zero hk)]

private lemma block_eq_replicate_blockColor {b : Multiset ℕ}
    (h : b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) :
    b = Multiset.replicate (Multiset.card b) (blockColor b) := by
  obtain ⟨hne, v, hv⟩ := h
  have hc : Multiset.card b ≠ 0 := by
    intro h0
    exact hne (Multiset.card_eq_zero.mp h0)
  have hcol : blockColor b = v := by
    conv_lhs => rw [hv]
    exact blockColor_replicate hc
  rw [hcol]
  exact hv

private lemma block_sum_eq {b : Multiset ℕ}
    (h : b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) :
    b.sum = Multiset.card b * blockColor b := by
  conv_lhs => rw [block_eq_replicate_blockColor h]
  rw [Multiset.sum_replicate, smul_eq_mul]

private lemma blockColor_mem {b : Multiset ℕ}
    (h : b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) :
    blockColor b ∈ b := by
  have hc : Multiset.card b ≠ 0 := fun h0 => h.1 (Multiset.card_eq_zero.mp h0)
  have hb := block_eq_replicate_blockColor h
  set c := blockColor b
  rw [hb, Multiset.mem_replicate]
  exact ⟨hc, rfl⟩

private lemma list_isChain_replicate_beq (k v : ℕ) :
    (List.replicate k v).IsChain fun x y => (x == y) = true := by
  induction k with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simp
    | succ k' =>
      rw [List.replicate_succ, List.replicate_succ, List.isChain_cons_cons]
      exact ⟨by simp, ih⟩

private lemma list_head_replicate {k v : ℕ} (hk : List.replicate k v ≠ []) :
    (List.replicate k v).head hk = v := by
  cases k with
  | zero => exact absurd rfl hk
  | succ k' => simp

private lemma list_getLast_replicate {k v : ℕ} (hk : List.replicate k v ≠ []) :
    (List.replicate k v).getLast hk = v := by
  cases k with
  | zero => exact absurd rfl hk
  | succ k' => simp

-- ============================================================================
-- Section 2: Backward Direction (0 < A382876 n -> HasConstBlockPartition)
-- ============================================================================

private lemma backward_dir {n : ℕ} (hpos : 0 < A382876 n) :
    HasConstBlockPartition (primeIndices n) := by
  obtain ⟨l, hl_perm, hl_nodup⟩ := (mem_A382876_pos_iff n).mp hpos
  let R : List (List ℕ) := l.splitBy (· == ·)
  let P : Multiset (Multiset ℕ) := Multiset.ofList (R.map Multiset.ofList)
  refine ⟨P, ?_, ?_, ?_⟩
  · show P.sum = primeIndices n
    rw [multiset_sum_coe_map, List.flatten_splitBy]
    exact Multiset.coe_eq_coe.mpr hl_perm
  · intro b hb
    rw [Multiset.mem_coe, List.mem_map] at hb
    obtain ⟨r, hrR, rfl⟩ := hb
    have hr_ne : r ≠ [] := List.ne_nil_of_mem_splitBy hrR
    have hr_chain : r.IsChain fun x y => (x == y) = true := List.isChain_of_mem_splitBy hrR
    obtain ⟨v, hrv⟩ := list_eq_replicate_of_isChain_beq r hr_ne hr_chain
    refine ⟨?_, v, ?_⟩
    · intro h0
      exact hr_ne (by simpa using h0)
    · rw [Multiset.coe_card, ← Multiset.coe_replicate]
      exact congrArg Multiset.ofList hrv
  · have hmap : P.map Multiset.sum = Multiset.ofList (runSums l) := by
      have hlist : (R.map Multiset.ofList).map Multiset.sum = runSums l := by
        simp only [runSums, R, List.map_map]
        refine List.map_congr_left fun r _ => ?_
        simp
      rw [← hlist]
      exact Multiset.map_coe Multiset.sum (R.map Multiset.ofList)
    rw [hmap]
    exact Multiset.coe_nodup.mpr hl_nodup

-- ============================================================================
-- Section 3: Minimum-Block Pigeonhole Merge Lemma
-- ============================================================================

private def IsValidPart (M : Multiset ℕ) (P : Multiset (Multiset ℕ)) : Prop :=
  P.sum = M ∧
    (∀ b ∈ P, b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) ∧
    (P.map Multiset.sum).Nodup

private lemma multiset_exists_notMem_of_nodup_card_lt {α : Type*} [DecidableEq α]
    {S U : Multiset α} (hS : S.Nodup) (hlt : Multiset.card U < Multiset.card S) :
    ∃ y ∈ S, y ∉ U := by
  by_contra hnone
  push Not at hnone
  have hsub : S.toFinset ⊆ U.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset] at hy ⊢
    exact hnone y hy
  have h1 : Multiset.card S = S.toFinset.card := (Multiset.toFinset_card_of_nodup hS).symm
  have h2 : S.toFinset.card ≤ U.toFinset.card := Finset.card_le_card hsub
  have h3 : U.toFinset.card ≤ Multiset.card U := Multiset.toFinset_card_le U
  omega

private lemma exists_minimal_validPart {M : Multiset ℕ} (hM : ∀ v ∈ M, 1 ≤ v)
    (h : HasConstBlockPartition M) :
    ∃ P : Multiset (Multiset ℕ), IsValidPart M P ∧
      ∀ v : ℕ, 2 * Multiset.card (P.filter fun b => blockColor b = v) ≤ Multiset.card P + 1 := by
  classical
  have hex : ∃ k : ℕ, ∃ P : Multiset (Multiset ℕ), IsValidPart M P ∧ Multiset.card P = k := by
    rcases h with ⟨P, h1, h2, h3⟩
    exact ⟨Multiset.card P, P, ⟨h1, h2, h3⟩, rfl⟩
  obtain ⟨P, hP, hPcard⟩ := Nat.find_spec hex
  have hmin : ∀ P' : Multiset (Multiset ℕ), IsValidPart M P' → Multiset.card P ≤ Multiset.card P' := by
    intro P' hP'
    rw [hPcard]
    exact Nat.find_min' hex ⟨P', hP', rfl⟩
  refine ⟨P, hP, ?_⟩
  intro v
  set Pv : Multiset (Multiset ℕ) := P.filter fun b => blockColor b = v
  set Qv : Multiset (Multiset ℕ) := P.filter fun b => blockColor b ≠ v
  have hsplit : Pv + Qv = P := Multiset.filter_add_not (fun b => blockColor b = v) P
  have hcard_split : Multiset.card Pv + Multiset.card Qv = Multiset.card P := by
    rw [← Multiset.card_add, hsplit]
  by_contra hgt
  have hge : Multiset.card Qv + 2 ≤ Multiset.card Pv := by omega
  have hPv_ne : Pv ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hge
    omega
  have hPv_toFinset_ne : Pv.toFinset.Nonempty := by
    obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hPv_ne
    exact ⟨b, Multiset.mem_toFinset.mpr hb⟩
  obtain ⟨bmax, hbmax_fin, hbmax_ge⟩ := Finset.exists_max_image Pv.toFinset Multiset.card hPv_toFinset_ne
  have hbmax_Pv : bmax ∈ Pv := Multiset.mem_toFinset.mp hbmax_fin
  have hbmax_P : bmax ∈ P := (Multiset.mem_filter.mp hbmax_Pv).1
  have hbmax_col : blockColor bmax = v := (Multiset.mem_filter.mp hbmax_Pv).2
  have hv_pos : 1 ≤ v := by
    have hv_in_bmax : v ∈ bmax := hbmax_col ▸ blockColor_mem (hP.2.1 bmax hbmax_P)
    have hle : bmax ≤ P.sum := Multiset.le_sum_of_mem hbmax_P
    exact hM v (hP.1 ▸ Multiset.mem_of_le hle hv_in_bmax)
  set smax : ℕ := Multiset.card bmax
  set Pv' : Multiset (Multiset ℕ) := Pv.erase bmax
  have hPv'_card : Multiset.card Pv' = Multiset.card Pv - 1 := Multiset.card_erase_of_mem hbmax_Pv
  have hPv'_le_P : Pv' ≤ P := le_trans (Multiset.erase_le bmax Pv) (Multiset.filter_le _ P)
  have hPv'_sum_nodup : (Pv'.map Multiset.sum).Nodup :=
    Multiset.nodup_of_le (Multiset.map_le_map hPv'_le_P) hP.2.2
  set S : Multiset ℕ := (Pv'.map Multiset.sum).map (fun x => smax * v + x)
  set U : Multiset ℕ := Qv.map Multiset.sum
  have hS_nodup : S.Nodup :=
    Multiset.Nodup.map (fun _ _ heq => by omega) hPv'_sum_nodup
  have hS_card : Multiset.card S = Multiset.card Pv - 1 := by
    simp [S, hPv'_card]
  have hU_card : Multiset.card U = Multiset.card Qv := by
    simp [U]
  obtain ⟨y, hyS, hyU⟩ := multiset_exists_notMem_of_nodup_card_lt hS_nodup (by omega : Multiset.card U < Multiset.card S)
  rw [Multiset.mem_map] at hyS
  obtain ⟨x0, hx0, rfl⟩ := hyS
  rw [Multiset.mem_map] at hx0
  obtain ⟨b0, hb0_Pv', rfl⟩ := hx0
  have hb0_Pv : b0 ∈ Pv := Multiset.mem_of_mem_erase hb0_Pv'
  have hb0_P : b0 ∈ P := (Multiset.mem_filter.mp hb0_Pv).1
  have hb0_col : blockColor b0 = v := (Multiset.mem_filter.mp hb0_Pv).2
  have hb0_card_pos : 1 ≤ Multiset.card b0 := by
    have hne := (hP.2.1 b0 hb0_P).1
    have hc : Multiset.card b0 ≠ 0 := fun h0 => hne (Multiset.card_eq_zero.mp h0)
    omega
  have hb0_in_Per : b0 ∈ P.erase bmax := by
    have hle : Pv.erase bmax ≤ P.erase bmax := Multiset.erase_le_erase bmax (Multiset.filter_le _ P)
    exact Multiset.mem_of_le hle hb0_Pv'
  set bnew : Multiset ℕ := bmax + b0
  set Prest : Multiset (Multiset ℕ) := (P.erase bmax).erase b0
  set P' : Multiset (Multiset ℕ) := bnew ::ₘ Prest
  have hP'_card : Multiset.card P' = Multiset.card P - 1 := by
    have hc1 : Multiset.card (P.erase bmax) = Multiset.card P - 1 := Multiset.card_erase_of_mem hbmax_P
    have hc2 : Multiset.card Prest = Multiset.card (P.erase bmax) - 1 := Multiset.card_erase_of_mem hb0_in_Per
    have hcP : 2 ≤ Multiset.card P := by omega
    simp only [P', Multiset.card_cons]
    omega
  have hP'_valid : IsValidPart M P' := by
    refine ⟨?_, ?_, ?_⟩
    · calc P'.sum = bmax + b0 + Prest.sum := by simp [P', bnew, Multiset.sum_cons]
        _ = bmax + (b0 + Prest.sum) := by rw [add_assoc]
        _ = bmax + (P.erase bmax).sum := by
            rw [← Multiset.sum_cons, Multiset.cons_erase hb0_in_Per]
        _ = P.sum := by
            rw [← Multiset.sum_cons, Multiset.cons_erase hbmax_P]
        _ = M := hP.1
    · intro b hb
      rw [Multiset.mem_cons] at hb
      rcases hb with rfl | hb_rest
      · refine ⟨?_, v, ?_⟩
        · intro h0
          have hc : Multiset.card bnew = 0 := by rw [h0, Multiset.card_zero]
          have hcb : Multiset.card bnew = Multiset.card bmax + Multiset.card b0 := Multiset.card_add bmax b0
          omega
        · have h1 : bmax = Multiset.replicate (Multiset.card bmax) v :=
            hbmax_col ▸ block_eq_replicate_blockColor (hP.2.1 bmax hbmax_P)
          have h2 : b0 = Multiset.replicate (Multiset.card b0) v :=
            hb0_col ▸ block_eq_replicate_blockColor (hP.2.1 b0 hb0_P)
          rw [Multiset.card_add]
          calc bnew = bmax + b0 := rfl
            _ = Multiset.replicate (Multiset.card bmax) v + Multiset.replicate (Multiset.card b0) v := by
                rw [← h1, ← h2]
            _ = Multiset.replicate (Multiset.card bmax + Multiset.card b0) v :=
                (Multiset.replicate_add (Multiset.card bmax) (Multiset.card b0) v).symm
      · exact hP.2.1 b (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hb_rest))
    · simp only [P', Multiset.map_cons, Multiset.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hmem
        rw [Multiset.mem_map] at hmem
        obtain ⟨b, hb_rest, hsum_eq⟩ := hmem
        have hb_P : b ∈ P := Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hb_rest)
        have hbnew_sum : bnew.sum = smax * v + b0.sum := by
          simp only [bnew, Multiset.sum_add]
          have hbm : bmax.sum = smax * v := hbmax_col ▸ block_sum_eq (hP.2.1 bmax hbmax_P)
          rw [hbm]
        by_cases hcol : blockColor b = v
        · have hb_Pv : b ∈ Pv := Multiset.mem_filter.mpr ⟨hb_P, hcol⟩
          have hb_le : Multiset.card b ≤ smax := hbmax_ge b (Multiset.mem_toFinset.mpr hb_Pv)
          have hb_sum : b.sum = Multiset.card b * v := hcol ▸ block_sum_eq (hP.2.1 b hb_P)
          have hb0_sum : b0.sum = Multiset.card b0 * v := hb0_col ▸ block_sum_eq (hP.2.1 b0 hb0_P)
          have hlt1 : Multiset.card b * v ≤ smax * v := Nat.mul_le_mul_right v hb_le
          have hpos0 : 1 ≤ Multiset.card b0 * v := Nat.mul_pos hb0_card_pos hv_pos
          omega
        · have hb_Qv : b ∈ Qv := Multiset.mem_filter.mpr ⟨hb_P, hcol⟩
          have hb_U : b.sum ∈ U := Multiset.mem_map.mpr ⟨b, hb_Qv, rfl⟩
          rw [hsum_eq, hbnew_sum] at hb_U
          exact hyU hb_U
      · have hle : Prest ≤ P := le_trans (Multiset.erase_le b0 _) (Multiset.erase_le bmax P)
        exact Multiset.nodup_of_le (Multiset.map_le_map hle) hP.2.2
  have hle_min := hmin P' hP'_valid
  have hcP : 2 ≤ Multiset.card P := by omega
  omega

-- ============================================================================
-- Section 4: Greedy Interlacing Lemma for Colored Multisets
-- ============================================================================

private lemma card_filter_add_card_filter_le {α : Type*} [DecidableEq α] (col : α → ℕ)
    (S : Multiset α) {c₁ c₂ : ℕ} (hne : c₁ ≠ c₂) :
    Multiset.card (S.filter fun x => col x = c₁) +
      Multiset.card (S.filter fun x => col x = c₂) ≤ Multiset.card S := by
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.filter_cons, Multiset.card_cons]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) hne
    · simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero]; omega
    · simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero]; omega
    · simp only [Multiset.card_add, Multiset.card_zero]; omega

private lemma card_filter_erase_eq_sub {α : Type*} [DecidableEq α] (col : α → ℕ)
    {S : Multiset α} {x : α} (hx : x ∈ S) :
    Multiset.card ((S.erase x).filter fun y => col y = col x) =
      Multiset.card (S.filter fun y => col y = col x) - 1 := by
  have hcons := Multiset.cons_erase hx
  have hf : S.filter (fun y => col y = col x) =
      x ::ₘ ((S.erase x).filter fun y => col y = col x) := by
    conv_lhs => rw [← hcons]
    simp
  rw [hf, Multiset.card_cons]
  omega

private lemma card_filter_erase_ne {α : Type*} [DecidableEq α] (col : α → ℕ)
    {S : Multiset α} {x : α} (hx : x ∈ S) {c : ℕ} (hne : col x ≠ c) :
    Multiset.card ((S.erase x).filter fun y => col y = c) =
      Multiset.card (S.filter fun y => col y = c) := by
  have hcons := Multiset.cons_erase hx
  have hf : S.filter (fun y => col y = c) = (S.erase x).filter fun y => col y = c := by
    conv_lhs => rw [← hcons]
    simp [hne]
  rw [hf]

private lemma greedy_interlace {α : Type*} [DecidableEq α] (col : α → ℕ) :
    ∀ k : ℕ, ∀ (S : Multiset α) (f : Option ℕ),
      Multiset.card S = k →
      (∀ c : ℕ, 2 * Multiset.card (S.filter fun x => col x = c) ≤ k + 1) →
      (∀ c0 : ℕ, f = some c0 → 2 * Multiset.card (S.filter fun x => col x = c0) ≤ k) →
      ∃ B : List α, (B : Multiset α) = S ∧
        B.IsChain (fun x y => col x ≠ col y) ∧
        (∀ c0 : ℕ, f = some c0 → ∀ x ∈ B.head?, col x ≠ c0) := by
  classical
  intro k
  induction k with
  | zero =>
    intro S f hcard _ _
    have hS : S = 0 := Multiset.card_eq_zero.mp hcard
    refine ⟨[], ?_, by simp, by simp⟩
    simp [hS]
  | succ k ih =>
    intro S f hcard hbound hforb
    let allowed : α → Prop := fun x => ∀ c0 : ℕ, f = some c0 → col x ≠ c0
    set A : Multiset α := S.filter allowed
    have hA_ne : A ≠ 0 := by
      cases hf : f with
      | none =>
        have hAS : A = S := by
          simp only [A, allowed, hf]
          exact Multiset.filter_eq_self.mpr (fun _ _ _ h => by cases h)
        rw [hAS]
        intro h0
        rw [h0, Multiset.card_zero] at hcard
        omega
      | some c0 =>
        have hcompl : Multiset.card (S.filter fun x => col x = c0) + Multiset.card A = Multiset.card S := by
          have hAeq : A = S.filter (fun x => ¬ col x = c0) := by
            refine Multiset.filter_congr fun x _ => ?_
            simp [allowed, hf]
          rw [hAeq, ← Multiset.card_add, Multiset.filter_add_not]
        have hfc0 := hforb c0 hf
        intro h0
        rw [h0, Multiset.card_zero] at hcompl
        omega
    have hA_fin_ne : A.toFinset.Nonempty := by
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hA_ne
      exact ⟨x, Multiset.mem_toFinset.mpr hx⟩
    obtain ⟨xstar, hxstar_fin, hxstar_max⟩ :=
      Finset.exists_max_image A.toFinset (fun x => Multiset.card (S.filter fun y => col y = col x)) hA_fin_ne
    have hxstar_A : xstar ∈ A := Multiset.mem_toFinset.mp hxstar_fin
    have hxstar_S : xstar ∈ S := (Multiset.mem_filter.mp hxstar_A).1
    have hxstar_all : allowed xstar := (Multiset.mem_filter.mp hxstar_A).2
    set cstar : ℕ := col xstar
    set S' : Multiset α := S.erase xstar
    have hS'_card : Multiset.card S' = k := by
      rw [Multiset.card_erase_of_mem hxstar_S, hcard]
      rfl
    have hS'_forb : ∀ c0 : ℕ, some cstar = some c0 →
        2 * Multiset.card (S'.filter fun x => col x = c0) ≤ k := by
      intro c0 hc0
      cases hc0
      rw [card_filter_erase_eq_sub col hxstar_S]
      have hb := hbound (col xstar)
      have hpos : 1 ≤ Multiset.card (S.filter fun x => col x = col xstar) := by
        have hmem : xstar ∈ S.filter (fun x => col x = col xstar) :=
          Multiset.mem_filter.mpr ⟨hxstar_S, rfl⟩
        exact Multiset.card_pos.mpr (fun h0 => by rw [h0] at hmem; exact Multiset.notMem_zero _ hmem)
      omega
    have hS'_bound : ∀ c : ℕ, 2 * Multiset.card (S'.filter fun x => col x = c) ≤ k + 1 := by
      intro c
      by_cases hcc : c = cstar
      · subst hcc
        have := hS'_forb cstar rfl
        omega
      · rw [card_filter_erase_ne col hxstar_S (Ne.symm hcc)]
        by_cases hfc : f = some c
        · exact hforb c hfc
        · by_cases hzero : Multiset.card (S.filter fun x => col x = c) = 0
          · omega
          · have hne_flt : (S.filter fun x => col x = c) ≠ 0 :=
              fun h0 => hzero (by rw [h0, Multiset.card_zero])
            obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne_flt
            have hyS : y ∈ S := (Multiset.mem_filter.mp hy).1
            have hycol : col y = c := (Multiset.mem_filter.mp hy).2
            have hy_all : allowed y := by
              intro c0 hc0
              rw [hycol]
              intro heq
              subst heq
              exact hfc hc0
            have hyA : y ∈ A := Multiset.mem_filter.mpr ⟨hyS, hy_all⟩
            have hle_max := hxstar_max y (Multiset.mem_toFinset.mpr hyA)
            rw [hycol] at hle_max
            have hdisj := card_filter_add_card_filter_le col S hcc
            omega
    obtain ⟨B', hB'_eq, hB'_chain, hB'_head⟩ := ih S' (some cstar) hS'_card hS'_bound hS'_forb
    refine ⟨xstar :: B', ?_, ?_, ?_⟩
    · rw [← Multiset.cons_coe, hB'_eq, Multiset.cons_erase hxstar_S]
    · rw [List.isChain_cons]
      refine ⟨?_, hB'_chain⟩
      intro y hy
      exact Ne.symm (hB'_head cstar rfl y hy)
    · intro c0 hc0 x hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hxstar_all c0 hc0

-- ============================================================================
-- Section 5: Forward Direction (HasConstBlockPartition -> 0 < A382876 n) & Main
-- ============================================================================

private lemma isChain_toRun_of_isChain {B : List (Multiset ℕ)}
    (hB : ∀ b ∈ B, b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v)
    (hchain : B.IsChain fun a b => blockColor a ≠ blockColor b) :
    (B.map fun b => List.replicate (Multiset.card b) (blockColor b)).IsChain
      fun a b => ∃ ha hb, (a.getLast ha == b.head hb) = false := by
  induction B with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b ts =>
      rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
      rw [List.isChain_cons_cons] at hchain
      refine ⟨?_, ih (fun x hx => hB x (List.mem_cons_of_mem a hx)) hchain.2⟩
      have ha_ne : List.replicate (Multiset.card a) (blockColor a) ≠ [] := by
        have ha0 := (hB a List.mem_cons_self).1
        have hca : Multiset.card a ≠ 0 := fun h0 => ha0 (Multiset.card_eq_zero.mp h0)
        simp [hca]
      have hb_ne : List.replicate (Multiset.card b) (blockColor b) ≠ [] := by
        have hb0 := (hB b (List.mem_cons_of_mem a List.mem_cons_self)).1
        have hcb : Multiset.card b ≠ 0 := fun h0 => hb0 (Multiset.card_eq_zero.mp h0)
        simp [hcb]
      refine ⟨ha_ne, hb_ne, ?_⟩
      rw [list_getLast_replicate ha_ne, list_head_replicate hb_ne, beq_eq_false_iff_ne]
      exact hchain.1

private lemma forward_dir {n : ℕ} (hpart : HasConstBlockPartition (primeIndices n)) :
    0 < A382876 n := by
  obtain ⟨P, hP, hPbal⟩ := exists_minimal_validPart (fun _ hv => primeIndices_pos hv) hpart
  obtain ⟨B, hB_eq, hB_chain, _⟩ := greedy_interlace blockColor (Multiset.card P) P none rfl hPbal
    (fun _ h => by cases h)
  have hB_valid : ∀ b ∈ B, b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v := by
    intro b hb
    exact hP.2.1 b (hB_eq ▸ Multiset.mem_coe.mpr hb)
  let toRun : Multiset ℕ → List ℕ := fun b => List.replicate (Multiset.card b) (blockColor b)
  let Lruns : List (List ℕ) := B.map toRun
  let l : List ℕ := Lruns.flatten
  rw [mem_A382876_pos_iff]
  refine ⟨l, ?_, ?_⟩
  · have hcoe : Multiset.ofList l = primeIndices n := by
      have hmap : Lruns.map Multiset.ofList = B := by
        simp only [Lruns, List.map_map]
        conv_rhs => rw [← List.map_id B]
        refine List.map_congr_left fun b hb => ?_
        simp only [Function.comp_apply, id_eq, toRun, Multiset.coe_replicate]
        exact (block_eq_replicate_blockColor (hB_valid b hb)).symm
      rw [← multiset_sum_coe_map Lruns, hmap, hB_eq, hP.1]
    exact Multiset.coe_eq_coe.mp hcoe
  · have hsplit : l.splitBy (· == ·) = Lruns := by
      apply List.splitBy_flatten
      · intro hnil
        rw [List.mem_map] at hnil
        obtain ⟨b, hbB, hbeq⟩ := hnil
        have hb0 := (hB_valid b hbB).1
        have hcb : Multiset.card b ≠ 0 := fun h0 => hb0 (Multiset.card_eq_zero.mp h0)
        simp [toRun, hcb] at hbeq
      · intro m hm
        rw [List.mem_map] at hm
        obtain ⟨b, _, rfl⟩ := hm
        exact list_isChain_replicate_beq (Multiset.card b) (blockColor b)
      · exact isChain_toRun_of_isChain hB_valid hB_chain
    have hrun_eq : runSums l = B.map Multiset.sum := by
      simp only [runSums, hsplit, Lruns, List.map_map]
      refine List.map_congr_left fun b hb => ?_
      simp only [Function.comp_apply, toRun, List.sum_replicate, smul_eq_mul]
      exact (block_sum_eq (hB_valid b hb)).symm
    rw [hrun_eq, ← Multiset.coe_nodup, ← Multiset.map_coe, hB_eq]
    exact hP.2.2

theorem main_proof : ∀ n : ℕ, 1 ≤ n → (InA381636 n ↔ A382876 n = 0) := by
  intro n _
  unfold InA381636
  constructor
  · intro hnot
    by_contra hne
    exact hnot (backward_dir (Nat.pos_of_ne_zero hne))
  · intro h0 hpart
    have hpos := forward_dir hpart
    omega

end OeisA381636

theorem OMA.solution : type_of% @OMA.S_oeis_a381636.main :=
  OeisA381636.main_proof
