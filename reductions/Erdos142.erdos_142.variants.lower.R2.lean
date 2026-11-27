import FormalConjectures.ErdosProblems.«142»

/-!
# From reciprocal progressions to the logarithmic upper bound

A divergent sum of normalized extremal cardinalities would give a set of divergent
reciprocal sum by placing extremizers in separated blocks. The two hypotheses express
the reciprocal-progression theorem restricted to those blocks and the preservation
of progression freeness in this construction. The former follows from Erdős problem 3,
formalized by OAI in OAI.Combinatorics.Progressions.Results.Conclusions.
The equivalence with summability of the extremal densities on dyadic scales is
recorded by Green and Tao in New bounds for Szemerédi's theorem, III, referring
to Tao and Vu, Additive Combinatorics, Exercise 10.0.6. We use powers of four.
The elementary length-two argument below is from reduction R1 of this problem.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2

open Asymptotics Erdos142 Filter Real
open scoped Topology

/-- The reciprocal-progression theorem restricted to the union of the block intervals. -/
def H1 : Prop :=
  ∀ A : Set ℕ, (∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
    ¬ Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)) →
    ∀ k : ℕ, 3 ≤ k → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- Packing each progression-free block preserves the absence of a progression. -/
def H2 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (B : ℕ → Finset ℕ), (∀ j, B j ⊆ Finset.Icc 1 (4 ^ j)) →
    (∀ j, ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ B j) →
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, ∃ j b, b ∈ B j ∧ a + i * d = 4 * 4 ^ j + b

lemma card_bound_two (N : ℕ) : r 2 N ≤ 1 := by
  unfold r Set.IsAPOfLengthFree.maxCard
  apply csSup_le
  · refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro A hA hAP
    have hEmpty : A = ∅ := Set.subset_empty_iff.mp (by simpa using hA)
    exact (Set.not_isAPOfLength_empty (by decide) (hEmpty ▸ hAP)).elim
  · rintro m ⟨A, _, hA, rfl⟩
    by_contra! hLarge
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hLarge
    have hf (x y : ℕ) (hx : x ∈ A) (hy : y ∈ A) (hxy : x < y) : False := by
      have hSub : ({x, y} : Set ℕ) ⊆ (A : Set ℕ) := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      have hTwo := hA _ hSub (Nat.isAPOfLength_pair hxy)
      exact (by decide : ¬ ((2 : ℕ) : ℕ∞) ≤ 1) hTwo
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact hf a b ha hb hlt
    · exact hf b a hb ha hgt

lemma two_littleO :
    (fun N ↦ (r 2 N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ) / log (N : ℝ)) := by
  have hT : Tendsto (fun N : ℕ ↦ log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [hT.eventually (gt_mem_nhds hc), eventually_gt_atTop (1 : ℕ)] with N hN hLarge
  have hOne : 1 < (N : ℝ) := by exact_mod_cast hLarge
  have hPos : 0 < log (N : ℝ) := log_pos hOne
  have hNat : 0 < (N : ℝ) := zero_lt_one.trans hOne
  have hcard : (r 2 N : ℝ) ≤ 1 := by exact_mod_cast card_bound_two N
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  apply hcard.trans
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hPos).mpr
  simpa using ((div_lt_iff₀ hNat).mp hN).le

theorem card_le_maxCard {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : (S : Set ℕ).IsAPOfLengthFree k) :
    S.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  unfold Set.IsAPOfLengthFree.maxCard
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro _ ⟨U, hU, _, rfl⟩
    exact (Finset.card_mono hU).trans_eq (Nat.card_Icc 1 N)
  · exact ⟨S, hS, hfree, rfl⟩

theorem maxCard_monotone (k : ℕ) : Monotone (Set.IsAPOfLengthFree.maxCard k) := by
  intro M N hMN
  apply csSup_le'
  rintro _ ⟨S, hS, hfree, rfl⟩
  exact card_le_maxCard (hS.trans (Finset.Icc_subset_Icc_right hMN)) hfree

theorem isAPOfLength_translate {t : Set ℕ} {k : ℕ} (ht : t.IsAPOfLength k) (M : ℕ) :
    ((fun x : ℕ ↦ M + x) '' t).IsAPOfLength k := by
  obtain ⟨a, d, hc, ht⟩ := ht
  refine ⟨M + a, d, ?_, ?_⟩
  · have hi : Function.Injective (fun x : ℕ ↦ M + x) := fun _ _ h ↦ Nat.add_left_cancel h
    simpa only [ENat.card_coe_set_eq, hi.encard_image] using hc
  · rw [ht]
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, by simp [Nat.add_assoc]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨a + i • d, ⟨i, hi, rfl⟩, by simp [Nat.add_assoc]⟩

theorem maxCard_add_le (k M N : ℕ) :
    Set.IsAPOfLengthFree.maxCard k (M + N) ≤
      Set.IsAPOfLengthFree.maxCard k M + Set.IsAPOfLengthFree.maxCard k N := by
  classical
  apply csSup_le'
  rintro _ ⟨S, hS, hfree, rfl⟩
  let L := S.filter fun x ↦ x ≤ M
  let R := S.filter fun x ↦ ¬ x ≤ M
  let T := R.image fun x ↦ x - M
  have hL : L.card ≤ Set.IsAPOfLengthFree.maxCard k M := by
    apply card_le_maxCard
    · intro x hx
      obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hS hxS)).1, hxM⟩
    · intro t ht h
      apply hfree t _ h
      exact ht.trans (fun _ hx ↦ (Finset.mem_filter.mp hx).1)
  have hT : T.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
    apply card_le_maxCard
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyS, hyM⟩ := Finset.mem_filter.mp hy
      have hyMN := (Finset.mem_Icc.mp (hS hyS)).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro t ht h
      apply hfree ((fun x : ℕ ↦ M + x) '' t) _ (isAPOfLength_translate h M)
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (ht hx)
      obtain ⟨hyS, hyM⟩ := Finset.mem_filter.mp hy
      change M + (y - M) ∈ S
      rwa [Nat.add_sub_of_le (by omega : M ≤ y)]
  have hRT : T.card = R.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy h
    have hxM := (Finset.mem_filter.mp hx).2
    have hyM := (Finset.mem_filter.mp hy).2
    change x - M = y - M at h
    omega
  have hLR : L.card + R.card = S.card := Finset.card_filter_add_card_filter_not _
  omega

theorem maxCard_double_le (k N : ℕ) :
    Set.IsAPOfLengthFree.maxCard k (2 * N) ≤ 2 * Set.IsAPOfLengthFree.maxCard k N := by
  simpa only [two_mul] using maxCard_add_le k N N

theorem dyadic_density_antitone (k : ℕ) :
    Antitone (fun j : ℕ ↦ (Set.IsAPOfLengthFree.maxCard k (2 ^ j) : ℝ) / (2 : ℝ) ^ j) := by
  apply antitone_nat_of_succ_le
  intro j
  have hnat := maxCard_double_le k (2 ^ j)
  have h : (Set.IsAPOfLengthFree.maxCard k (2 * 2 ^ j) : ℝ) ≤
      2 * (Set.IsAPOfLengthFree.maxCard k (2 ^ j) : ℝ) := by exact_mod_cast hnat
  simp only [pow_succ']
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (2 : ℝ) ^ j)]

/-- Disjoint translates of finite sets capture a constant fraction of their normalized
cardinalities in the reciprocal sum of the ambient set. -/
theorem summable_card_div_pow_four_of_reciprocals
    (B : ℕ → Finset ℕ) (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j))
    (A : Set ℕ) (hA : ∀ j b, b ∈ B j → 4 * 4 ^ j + b ∈ A)
    (hsum : Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹))) :
    Summable (fun j : ℕ ↦ ((B j).card : ℝ) / (4 : ℝ) ^ j) := by
  classical
  let encode (p : (j : ℕ) × ↥(B j)) : ℕ := 4 * 4 ^ p.1 + p.2.1
  have ordered {i j : ℕ} (hij : i < j) (a : B i) (b : B j) :
      encode ⟨i, a⟩ < encode ⟨j, b⟩ := by
    have ha := (Finset.mem_Icc.mp (hB i a.property)).2
    have hp : (4 : ℕ) ^ (i + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by decide) hij
    rw [pow_succ] at hp
    have hpos : 0 < (4 : ℕ) ^ i := by positivity
    dsimp [encode]
    omega
  have hinj : Function.Injective encode := by
    rintro ⟨i, a⟩ ⟨j, b⟩ heq
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact ((ordered hij a b).ne heq).elim
    · have hval : a.val = b.val := by simpa [encode] using heq
      rw [Subtype.ext hval]
    · exact ((ordered hji b a).ne heq.symm).elim
  have hscale : Summable (fun p : (j : ℕ) × ↥(B j) ↦ ((4 : ℝ)^p.1)⁻¹) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _
      ((hsum.comp_injective hinj).mul_left 5)
    rintro ⟨j, b⟩
    change ((4 : ℝ)^j)⁻¹ ≤ 5 * A.indicator _ (encode ⟨j, b⟩)
    rw [Set.indicator_of_mem (hA j b b.property)]
    have hb := (Finset.mem_Icc.mp (hB j b.property)).2
    have hupper : (encode ⟨j, b⟩ : ℝ) ≤ 5 * (4 : ℝ)^j := by
      exact_mod_cast (show encode ⟨j, b⟩ ≤ 5 * 4 ^ j by dsimp [encode]; omega)
    have hencode : 0 < (encode ⟨j, b⟩ : ℝ) := by
      exact_mod_cast (show 0 < encode ⟨j, b⟩ by dsimp [encode]; positivity)
    have hfrac : 1 / (4 : ℝ)^j ≤ 5 / (encode ⟨j, b⟩ : ℝ) :=
      (div_le_div_iff₀ (by positivity) hencode).mpr (by simpa using hupper)
    simpa [div_eq_mul_inv, encode] using hfrac
  have hfiber := hscale.sigma
  simpa [tsum_fintype, div_eq_mul_inv] using hfiber

/-- A summable decreasing density has decay strictly faster than reciprocal scale. -/
theorem tendsto_nat_mul_of_antitone_summable {d : ℕ → ℝ}
    (hanti : Antitone d) (hpos : ∀ n, 0 ≤ d n) (hsum : Summable d) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * d n) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun n : ℕ ↦ n / 2) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun m ↦ ⟨2 * m, fun n hn ↦ ?_⟩
    omega
  have hblock : Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.Ico (n / 2) n, d i) atTop (𝓝 0) := by
    have h := hsum.tendsto_sum_tsum_nat
    simpa [Function.comp_def, Finset.sum_Ico_eq_sub d (Nat.div_le_self _ _)]
      using h.sub (h.comp hhalf)
  apply squeeze_zero (fun n ↦ mul_nonneg (Nat.cast_nonneg _) (hpos _))
    (fun n ↦ ?_) (by simpa using hblock.const_mul 2)
  have hcard : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * (n - n / 2) by omega)
  calc
    (n : ℝ) * d n ≤ (2 * ((n - n / 2 : ℕ) : ℝ)) * d n :=
      mul_le_mul_of_nonneg_right hcard (hpos _)
    _ = 2 * (∑ _i ∈ Finset.Ico (n / 2) n, d n) := by simp [Nat.card_Ico, mul_assoc]
    _ ≤ 2 * (∑ i ∈ Finset.Ico (n / 2) n, d i) := by
      gcongr with i hi
      exact hanti (Finset.mem_Ico.mp hi).2.le

/-- A logarithmically weighted estimate along powers of four controls every interval length. -/
theorem littleO_of_powers_of_four (f : ℕ → ℕ) (hmono : Monotone f)
    (hd : Tendsto (fun j : ℕ ↦ (j : ℝ) * ((f (4^j) : ℝ) / 4^j)) atTop (𝓝 0)) :
    (fun N ↦ (f N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ) / log N) := by
  rw [isLittleO_iff]
  intro ε hε
  have hlog : 0 < log 4 := log_pos (by norm_num)
  have hconst : 0 < ε / (4 * log 4) := by positivity
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hd.eventually (gt_mem_nhds hconst))
  filter_upwards [eventually_ge_atTop (4^J), eventually_gt_atTop (1 : ℕ)] with N hlarge hN
  let m := Nat.log 4 N + 1
  have hm : J ≤ m := (Nat.le_log_of_pow_le (by decide) hlarge).trans (Nat.le_succ _)
  have hdy := (hJ m hm).le
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNlog : 0 < log N := log_pos (by exact_mod_cast hN)
  have hupper : N ≤ 4^m := (Nat.lt_pow_succ_log_self (by decide : 1 < 4) N).le
  have hupperR : (N : ℝ) ≤ (4 : ℝ)^m := by exact_mod_cast hupper
  have hceil : (4 : ℝ)^m ≤ 4 * N := by
    have hfloor := Nat.pow_log_le_self 4 (by omega : N ≠ 0)
    dsimp [m]
    rw [pow_succ, mul_comm]
    gcongr
    exact_mod_cast hfloor
  have hfn : (f N : ℝ) ≤ (f (4^m) : ℝ) := by exact_mod_cast hmono hupper
  have hlogN : log N ≤ (m : ℝ) * log 4 := by
    simpa only [log_pow] using log_le_log hNpos hupperR
  have hpos : 0 < (4 : ℝ)^m := by positivity
  have hscale : 0 < 4 * log 4 := by positivity
  change (m : ℝ) * ((f (4^m) : ℝ) / 4^m) ≤ ε / (4 * log 4) at hdy
  rw [← mul_div_assoc] at hdy
  have hproduct := (div_le_div_iff₀ hpos hscale).mp hdy
  have hcap : (f (4^m) : ℝ) * ((m : ℝ) * log 4) ≤ ε * N := by
    nlinarith only [hproduct, mul_le_mul_of_nonneg_left hceil hε.le]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), ← mul_div_assoc]
  apply (le_div_iff₀ hNlog).mpr
  calc
    (f N : ℝ) * log N ≤ (f (4^m) : ℝ) * ((m : ℝ) * log 4) := by gcongr
    _ ≤ ε * N := hcap

lemma no_positive_step {A : Set ℕ} {k : ℕ} (hk : 1 < k) (hfree : A.IsAPOfLengthFree k) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  rintro ⟨a, d, hd, hmem⟩
  let T := (Finset.range k).image fun i => a + i * d
  have hcard : T.card = k := by
    have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
      intro x y h
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
    simp [T, Finset.card_image_of_injective _ hinj]
  have hsub : (T : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (Finset.mem_range.mp hi)
  have hap' : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, by simp [hcard], ?_⟩
    ext x
    simp [T]
  have hle := hfree (T : Set ℕ) hsub hap'
  exact (not_le_of_gt hk) (by exact_mod_cast hle)

/-- The natural-number supremum defining the extremal cardinality is attained. -/
lemma extremizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      S.card = r k N := by
  let c : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hnon : c.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro t ht hprogression
    have ht' : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    have hpos : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    exact (Set.not_isAPOfLength_empty hpos (ht' ▸ hprogression)).elim
  have hbound : BddAbove c := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hs, _, rfl⟩
    exact (Finset.card_mono hs).trans_eq (Nat.card_Icc 1 N)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hnon hbound
  exact ⟨S, hS, hfree, hcard⟩

theorem main : H1 → H2 → type_of% @Erdos142.erdos_142.variants.lower := by
  intro hrec hpack k hk
  by_cases htwo : k = 2
  · subst k
    exact two_littleO
  have hthree : 3 ≤ k := by omega
  choose B hB hfree hcard using fun j : ℕ ↦ extremizer hk (4 ^ j)
  let A : Set ℕ := {x | ∃ j b, b ∈ B j ∧ x = 4 * 4 ^ j + b}
  have hsupport (x : ℕ) (hx : x ∈ A) : ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j := by
    obtain ⟨j, b, hb, rfl⟩ := hx
    have h := Finset.mem_Icc.mp (hB j hb)
    exact ⟨j, by omega, by omega⟩
  have hnoAP := hpack k hthree B hB (fun j ↦ no_positive_step hk (hfree j))
  have hsum : Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)) := by
    by_contra h
    exact hnoAP (hrec A hsupport h k hthree)
  have hden : Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ)^j) := by
    simpa only [hcard] using summable_card_div_pow_four_of_reciprocals
      B hB A (fun j b hb ↦ ⟨j, b, hb, rfl⟩) hsum
  have hmono : Antitone (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ)^j) := by
    intro i j hij
    have hd := dyadic_density_antitone k (show 2 * i ≤ 2 * j by omega)
    simpa only [pow_mul, Nat.reducePow, show (2 : ℝ)^2 = 4 by norm_num] using hd
  exact littleO_of_powers_of_four (r k) (maxCard_monotone k)
    (tendsto_nat_mul_of_antitone_summable hmono (fun _ ↦ by positivity) hden)

end OMA.R_Erdos142_erdos_142_variants_lower_R2
