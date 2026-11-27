import OMAReductions.R_Erdos360_erdos_360_R1

-- Step Erdos360.erdos_360.R1.H1: hypothesis H1 of reduction Erdos360.erdos_360.R1
-- Credit: @OrangeHeadz
-- H1 := ∀ n r d : ℕ, ∀ S : Finset ℕ, 2 ≤ n → 1 ≤ d →     (∀ p ∈ S, p.Prime ∧ ¬ p ∣ n) →     Nat.Coprime d n →     (∀ p : ℕ, p.Prime → p ∣ d → p ∈ S) →     let R' := (Finset.Icc 1 (n / d)).filter (fun t ↦ ∀ p ∈ S, ¬ p ∣ t)     Erdos360.f n ≤ r / 2 + S.card + 2 * d.totient + (R'.card / d + 1)

/-!
Informal plan (the upper bound colouring of Conlon, Fox and Pham, arXiv:2104.14766, Section 5).

Colour each t in {1, ..., n - 1} as follows.

1. If some p in S divides t, give t the colour p (the least such p). Every subset sum of
   this class is a multiple of p, and p does not divide n.
2. Otherwise t is coprime to d, because every prime factor of d lies in S.
   If t ≤ n / d then t lies in R'. List R' in increasing order and cut it into consecutive
   blocks of d elements; the colour of t is the index of its block. A block has at most d
   elements, each at most n / d, so a subset sum is at most d * (n / d) ≤ n. Equality forces
   d ∣ n, hence d = 1, and then the subset is a single element t = n, which is out of range.
3. If t > n / d, the colour is the pair (t mod d, side). A subset B of one residue class a
   with sum n has fewer than d elements, and |B| * a ≡ n (mod d). As a is a unit mod d, this
   pins |B| to a single value j. The side records whether j * t < n. On the low side
   j * n = Σ j * t < j * n. On the high side every j * t = n, so B has one element t = n.

The number of colours is |S| + (|R'| / d + 1) + 2 φ(d). The parameter r is not needed.
Mathlib supplies Finpartition.ofErase, Nat.totient_eq_card_coprime, Finset.sum_nat_mod and
Nat.ModEq.cancel_right_of_coprime; everything else is elementary.
-/

open Finset

namespace OMA.E360

/-- A colouring with colours in `T` and no monochromatic subset summing to `n` bounds `f n`. -/
lemma f_le_of_coloring {γ : Type} [DecidableEq γ] (n : ℕ) (c : ℕ → γ) (T : Finset γ)
    (hT : ∀ t ∈ Icc 1 (n - 1), c t ∈ T)
    (hc : ∀ B : Finset ℕ, B ⊆ Icc 1 (n - 1) → (∀ t ∈ B, ∀ u ∈ B, c t = c u) →
      ∑ t ∈ B, t ≠ n) :
    Erdos360.f n ≤ T.card := by
  classical
  have hindep : (T.image (fun k => (Icc 1 (n - 1)).filter (fun t => c t = k))).SupIndep id := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hAB
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hA)
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hB)
    show Disjoint ((Icc 1 (n - 1)).filter (fun t => c t = k))
      ((Icc 1 (n - 1)).filter (fun t => c t = l))
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    apply hAB
    rw [← (mem_filter.mp ht1).2, ← (mem_filter.mp ht2).2]
  have hsup : (T.image (fun k => (Icc 1 (n - 1)).filter (fun t => c t = k))).sup id
      = Icc 1 (n - 1) := by
    ext t
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨A, hA, ht⟩
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hA
      exact (mem_filter.mp ht).1
    · intro ht
      exact ⟨_, Finset.mem_image.mpr ⟨c t, hT t ht, rfl⟩, mem_filter.mpr ⟨ht, rfl⟩⟩
  have hcard : (Finpartition.ofErase _ hindep hsup).parts.card ≤ T.card :=
    (Finset.card_erase_le).trans Finset.card_image_le
  refine le_trans (Nat.sInf_le ⟨Finpartition.ofErase _ hindep hsup, rfl, ?_⟩) hcard
  intro A hA hn
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hA)
  obtain ⟨B, hB, hsum⟩ := hn
  have hmem : ∀ t ∈ B, t ∈ (Icc 1 (n - 1)).filter (fun t => c t = k) :=
    fun t ht => Finset.mem_coe.mp (hB (Finset.mem_coe.mpr ht))
  exact hc B (fun t ht => (mem_filter.mp (hmem t ht)).1)
    (fun t ht u hu => ((mem_filter.mp (hmem t ht)).2).trans ((mem_filter.mp (hmem u hu)).2).symm)
    hsum.symm

/-- The colouring. -/
def col (n d : ℕ) (S R : Finset ℕ) (t : ℕ) : ℕ ⊕ (ℕ ⊕ (ℕ × Bool)) :=
  if h : ∃ p, p ∈ S ∧ p ∣ t then Sum.inl (Nat.find h)
  else if t ≤ n / d then Sum.inr (Sum.inl ((R.filter (· < t)).card / d))
  else Sum.inr (Sum.inr (t % d, decide (∃ j, j < d ∧ (j * t) % d = n % d ∧ j * t < n)))

/-- The set of colours. -/
def T (d : ℕ) (S R : Finset ℕ) : Finset (ℕ ⊕ (ℕ ⊕ (ℕ × Bool))) :=
  S.disjSum ((range (R.card / d + 1)).disjSum
    (((range d).filter (fun a => d.Coprime a)) ×ˢ (Finset.univ : Finset Bool)))

lemma T_card (d : ℕ) (S R : Finset ℕ) :
    (T d S R).card = S.card + ((R.card / d + 1) + d.totient * 2) := by
  unfold T
  rw [Finset.card_disjSum, Finset.card_disjSum, Finset.card_product, Finset.card_range,
    Nat.totient_eq_card_coprime]
  simp

lemma col_inl {n d : ℕ} {S R : Finset ℕ} {t p : ℕ} (h : col n d S R t = Sum.inl p) :
    p ∈ S ∧ p ∣ t := by
  unfold col at h
  split_ifs at h with h1 h2
  have h3 := Sum.inl.inj h
  subst h3
  exact Nat.find_spec h1

lemma col_mid {n d : ℕ} {S R : Finset ℕ} {t i : ℕ}
    (h : col n d S R t = Sum.inr (Sum.inl i)) :
    (∀ p ∈ S, ¬ p ∣ t) ∧ t ≤ n / d ∧ (R.filter (· < t)).card / d = i := by
  unfold col at h
  split_ifs at h with h1 h2
  all_goals first
    | exact ⟨fun p hp hpt => h1 ⟨p, hp, hpt⟩, h2, Sum.inl.inj (Sum.inr.inj h)⟩
    | cases h

lemma col_big {n d : ℕ} {S R : Finset ℕ} {t a : ℕ} {s : Bool}
    (h : col n d S R t = Sum.inr (Sum.inr (a, s))) :
    (∀ p ∈ S, ¬ p ∣ t) ∧ n / d < t ∧ t % d = a ∧
      (s = true ↔ ∃ j, j < d ∧ (j * t) % d = n % d ∧ j * t < n) := by
  unfold col at h
  split_ifs at h with h1 h2
  all_goals first
    | (obtain ⟨ha, hs⟩ := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))
       refine ⟨fun p hp hpt => h1 ⟨p, hp, hpt⟩, by omega, ha, ?_⟩
       rw [← hs]
       exact decide_eq_true_iff)
    | cases h

lemma rank_lt (R : Finset ℕ) {t u : ℕ} (ht : t ∈ R) (h : t < u) :
    (R.filter (· < t)).card < (R.filter (· < u)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨t, mem_filter.mpr ⟨ht, h⟩, fun h' => lt_irrefl _ (mem_filter.mp h').2⟩
  · intro x hx
    rw [mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩

lemma col_mem {n d : ℕ} {S R : Finset ℕ} (hd : 1 ≤ d)
    (hdS : ∀ p : ℕ, p.Prime → p ∣ d → p ∈ S)
    (hR : R = (Icc 1 (n / d)).filter (fun t => ∀ p ∈ S, ¬ p ∣ t)) {t : ℕ} (ht : 1 ≤ t) :
    col n d S R t ∈ T d S R := by
  unfold col T
  split_ifs with h1 h2
  · exact Finset.inl_mem_disjSum.mpr (Nat.find_spec h1).1
  · refine Finset.inr_mem_disjSum.mpr (Finset.inl_mem_disjSum.mpr ?_)
    rw [mem_range]
    have htR : t ∈ R := by
      rw [hR, mem_filter, mem_Icc]
      exact ⟨⟨ht, h2⟩, fun p hp hpt => h1 ⟨p, hp, hpt⟩⟩
    have hlt : (R.filter (· < t)).card < R.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨t, htR, fun h' => lt_irrefl _ (mem_filter.mp h').2⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (le_of_lt hlt))
  · refine Finset.inr_mem_disjSum.mpr (Finset.inr_mem_disjSum.mpr ?_)
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    have hcop : Nat.Coprime d t :=
      Nat.coprime_of_dvd (fun k hk hkd hkt => h1 ⟨k, hdS k hk hkd, hkt⟩)
    rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]
    exact hcop

/-- Blocks of `d` consecutive elements of `R`, all at most `n / d`. -/
lemma case_mid {n d i : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hdn : Nat.Coprime d n)
    (R B : Finset ℕ) (hB : B ⊆ Icc 1 (n - 1))
    (h : ∀ t ∈ B, t ∈ R ∧ t ≤ n / d ∧ (R.filter (· < t)).card / d = i) :
    ∑ t ∈ B, t ≠ n := by
  intro hsum
  have hcard : B.card ≤ d := by
    have hle : B.card ≤ (Ico (i * d) (i * d + d)).card := by
      apply Finset.card_le_card_of_injOn (fun t => (R.filter (· < t)).card)
      · intro t ht
        obtain ⟨-, -, h3⟩ := h t ht
        have h6 : (R.filter (· < t)).card ∈ Ico (i * d) (i * d + d) := by
          rw [mem_Ico, ← h3]
          exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add (by omega)⟩
        simpa using h6
      · intro t ht u hu htu
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · exact absurd htu (ne_of_lt (rank_lt R (h t ht).1 hlt))
        · exact absurd htu.symm (ne_of_lt (rank_lt R (h u hu).1 hlt))
    simpa using hle
  have hle : ∑ t ∈ B, t ≤ B.card * (n / d) := by
    simpa [smul_eq_mul] using
      Finset.sum_le_card_nsmul B (fun t => t) (n / d) (fun t ht => (h t ht).2.1)
  have h1 : d * (n / d) ≤ n := Nat.mul_div_le n d
  have h2 : B.card * (n / d) ≤ d * (n / d) := Nat.mul_le_mul_right _ hcard
  have h3 : d * (n / d) = n := by omega
  have hd1 : d = 1 := Nat.Coprime.eq_one_of_dvd hdn (Dvd.intro _ h3)
  subst hd1
  have hle' : ∑ t ∈ B, t ≤ B.card * (n - 1) := by
    simpa [smul_eq_mul] using
      Finset.sum_le_card_nsmul B (fun t => t) (n - 1) (fun t ht => (mem_Icc.mp (hB ht)).2)
  have h4 : B.card * (n - 1) ≤ 1 * (n - 1) := Nat.mul_le_mul_right _ hcard
  omega

/-- One residue class mod `d` above `n / d`, split by the side of `n / j`. -/
lemma case_big {n d a : ℕ} {s : Bool} (hn : 2 ≤ n) (hd : 1 ≤ d) (B : Finset ℕ)
    (hB : B ⊆ Icc 1 (n - 1))
    (h : ∀ t ∈ B, Nat.Coprime d t ∧ n / d < t ∧ t % d = a ∧
      (s = true ↔ ∃ j, j < d ∧ (j * t) % d = n % d ∧ j * t < n)) :
    ∑ t ∈ B, t ≠ n := by
  intro hsum
  have hne : B.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hsum
    omega
  have hlow : B.card * (n / d + 1) ≤ ∑ t ∈ B, t := by
    simpa [smul_eq_mul] using
      Finset.card_nsmul_le_sum B (fun t => t) (n / d + 1) (fun t ht => (h t ht).2.1)
  have hlt : B.card < d := by
    by_contra hge'
    have hge := not_lt.mp hge'
    have h1 : d * (n / d + 1) ≤ B.card * (n / d + 1) := Nat.mul_le_mul_right _ hge
    have h2 : n < d * (n / d + 1) := Nat.lt_mul_div_succ n (by omega)
    omega
  have hmod : ∀ t ∈ B, (B.card * t) % d = n % d := by
    intro t ht
    have e1 : n % d = (B.card * a) % d := by
      rw [← hsum, Finset.sum_nat_mod, Finset.sum_congr rfl (fun u hu => (h u hu).2.2.1)]
      simp [Finset.sum_const, smul_eq_mul]
    have e2 : t ≡ a [MOD d] := by
      unfold Nat.ModEq
      rw [← (h t ht).2.2.1, Nat.mod_mod]
    rw [e1]
    exact Nat.ModEq.mul_left _ e2
  have hsumj : ∑ t ∈ B, B.card * t = B.card * n := by rw [← Finset.mul_sum, hsum]
  cases s with
  | true =>
    have hall : ∀ t ∈ B, B.card * t < n := by
      intro t ht
      obtain ⟨hcop, -, -, hs⟩ := h t ht
      obtain ⟨j, hjd, hjmod, hjlt⟩ := hs.mp rfl
      have hj : j = B.card := by
        have hme : j * t ≡ B.card * t [MOD d] := by
          unfold Nat.ModEq
          rw [hjmod, hmod t ht]
        have hme' := Nat.ModEq.cancel_right_of_coprime hcop hme
        unfold Nat.ModEq at hme'
        rwa [Nat.mod_eq_of_lt hjd, Nat.mod_eq_of_lt hlt] at hme'
      rw [← hj]
      exact hjlt
    have hlt' : ∑ t ∈ B, B.card * t < ∑ _t ∈ B, n := Finset.sum_lt_sum_of_nonempty hne hall
    rw [hsumj, Finset.sum_const, smul_eq_mul] at hlt'
    exact lt_irrefl _ hlt'
  | false =>
    have hall : ∀ t ∈ B, n ≤ B.card * t := by
      intro t ht
      obtain ⟨-, -, -, hs⟩ := h t ht
      by_contra hlt'
      exact Bool.false_ne_true (hs.mpr ⟨B.card, hlt, hmod t ht, not_le.mp hlt'⟩)
    have heq : ∀ t ∈ B, B.card * t = n := by
      intro t ht
      by_contra hne'
      have hlt' : n < B.card * t := lt_of_le_of_ne (hall t ht) (Ne.symm hne')
      have hlt'' : ∑ _u ∈ B, n < ∑ u ∈ B, B.card * u := Finset.sum_lt_sum hall ⟨t, ht, hlt'⟩
      rw [hsumj, Finset.sum_const, smul_eq_mul] at hlt''
      exact lt_irrefl _ hlt''
    obtain ⟨t0, ht0⟩ := hne
    have ht0n : t0 ≤ n - 1 := (mem_Icc.mp (hB ht0)).2
    have hc2 : 1 < B.card := by
      by_contra hle'
      have hle := not_lt.mp hle'
      have h0 := heq t0 ht0
      have h1 : B.card * t0 ≤ 1 * t0 := Nat.mul_le_mul_right _ hle
      omega
    obtain ⟨t1, ht1, hne1⟩ := Finset.exists_mem_ne hc2 t0
    have h2 := (heq t1 ht1).trans (heq t0 ht0).symm
    exact hne1 (Nat.eq_of_mul_eq_mul_left (by omega) h2)

end OMA.E360

theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1.H1 := by
  unfold OMA.R_Erdos360_erdos_360_R1.H1
  intro n r d S hn hd hS hdn hdS R'
  have hR : R' = (Finset.Icc 1 (n / d)).filter (fun t ↦ ∀ p ∈ S, ¬ p ∣ t) := rfl
  clear_value R'
  have key : Erdos360.f n ≤ (OMA.E360.T d S R').card := by
    apply OMA.E360.f_le_of_coloring n (OMA.E360.col n d S R')
    · intro t ht
      exact OMA.E360.col_mem hd hdS hR (Finset.mem_Icc.mp ht).1
    · intro B hB hmono
      rcases B.eq_empty_or_nonempty with rfl | ⟨t0, ht0⟩
      · simp
        omega
      · rcases hc0 : OMA.E360.col n d S R' t0 with p | i | ⟨a, s⟩
        · have hall : ∀ t ∈ B, p ∣ t :=
            fun t ht => (OMA.E360.col_inl ((hmono t ht t0 ht0).trans hc0)).2
          have hp := (OMA.E360.col_inl hc0).1
          intro hsum
          exact (hS p hp).2 (hsum ▸ Finset.dvd_sum hall)
        · apply OMA.E360.case_mid hn hd hdn R' B hB (i := i)
          intro t ht
          obtain ⟨h1, h2, h3⟩ := OMA.E360.col_mid ((hmono t ht t0 ht0).trans hc0)
          refine ⟨?_, h2, h3⟩
          rw [hR, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨(Finset.mem_Icc.mp (hB ht)).1, h2⟩, h1⟩
        · apply OMA.E360.case_big hn hd B hB (a := a) (s := s)
          intro t ht
          obtain ⟨h1, h2, h3, h4⟩ := OMA.E360.col_big ((hmono t ht t0 ht0).trans hc0)
          exact ⟨Nat.coprime_of_dvd (fun k hk hkd hkt => h1 k (hdS k hk hkd) hkt), h2, h3, h4⟩
  rw [OMA.E360.T_card] at key
  omega
