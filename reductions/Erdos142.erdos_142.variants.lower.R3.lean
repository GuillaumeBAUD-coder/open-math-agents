import FormalConjectures.ErdosProblems.«142»

/-!
# The logarithmic little-o bound from sparse prime cyclic groups

Test cyclic groups of prime order at a scale comparable to `2^(2^j)`.
An interval of length at most half the modulus embeds without creating
progressions. Subadditivity gives antitone extremal density along dyadic
scales, so the sampled little-o bound controls all interval lengths.
The two-term argument is from reduction R1. The dyadic subadditivity and
extremizer lemmas are from reduction R2.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R3

open Asymptotics Erdos142 Filter Real
open scoped Topology

/-- The logarithmic little-o bound for progression-free sets in sparse prime cyclic groups. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
    ∃ p : ℕ, p.Prime ∧ 2 * 2 ^ (2 ^ j) ≤ p ∧ p ≤ 4 * 2 ^ (2 ^ j) ∧
      ∀ S : Finset ℕ, S ⊆ Finset.range p →
        (¬ ∃ a d : ℕ, a < p ∧ 0 < d ∧ d < p ∧ ∀ i < k, (a + i * d) % p ∈ S) →
        (S.card : ℝ) / (p : ℝ) ≤ ε / (2 : ℝ) ^ j

/-- Reducing an interval of length at most half the modulus preserves progression freeness.
The original representatives already lie in the cyclic range, so the cardinality is preserved. -/
def H2 : Prop :=
  ∀ k L p : ℕ, 3 ≤ k → 2 * L ≤ p → p.Prime →
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 L → (S : Set ℕ).IsAPOfLengthFree k →
      S ⊆ Finset.range p ∧
        ¬ ∃ a d : ℕ, a < p ∧ 0 < d ∧ d < p ∧ ∀ i < k, (a + i * d) % p ∈ S

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

/-- A little-o estimate for the density on doubly exponential scales suffices at every length. -/
lemma littleO_of_sparse (k : ℕ)
    (hs : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      (r k (2 ^ (2 ^ j)) : ℝ) / (2 : ℝ) ^ ((2 : ℕ) ^ j) ≤ ε / (2 : ℝ) ^ j) :
    (fun N ↦ (r k N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ) / log (N : ℝ)) := by
  rw [isLittleO_iff]
  intro c hc
  let ε := c / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hs ε hε)
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ J) : ℕ), eventually_gt_atTop (1 : ℕ)]
    with N hN hNlarge
  let m := Nat.log 2 N + 1
  let j := Nat.log 2 m
  let t : ℕ := 2 ^ j
  have hmpos : 0 < m := Nat.succ_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmJ : 2 ^ J ≤ m :=
    (Nat.le_log_of_pow_le (by decide) hN).trans (Nat.le_succ _)
  have hjJ : J ≤ j := Nat.le_log_of_pow_le (by decide) hmJ
  have htm : t ≤ m := Nat.pow_log_le_self 2 hmpos.ne'
  have hmt : m ≤ 2 * t := by
    have h := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) m).le
    simpa [t, j, pow_succ'] using h
  have hNm : N ≤ 2 ^ m := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).le
  have hmN : 2 ^ m ≤ 2 * N := by
    rw [show m = Nat.log 2 N + 1 by rfl, pow_succ']
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  have hNmR : (N : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast hNm
  have hmNR : (2 : ℝ) ^ m ≤ 2 * (N : ℝ) := by exact_mod_cast hmN
  have htR : (t : ℝ) = (2 : ℝ) ^ j := by exact_mod_cast (show t = (2 : ℕ)^j by rfl)
  have htpos : (0 : ℝ) < t := by rw [htR]; positivity
  have hlogpos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hNlarge)
  have hlogle : log (N : ℝ) ≤ 2 * (t : ℝ) := by
    have hlog2 : log 2 ≤ 1 := by
      calc
        log 2 ≤ 2 - 1 := log_le_sub_one_of_pos (by norm_num)
        _ = 1 := by norm_num
    have hmtR : (m : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hmt
    calc
      log (N : ℝ) ≤ log ((2 : ℝ) ^ m) := log_le_log hNpos hNmR
      _ = (m : ℝ) * log 2 := log_pow 2 m
      _ ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ ≤ 2 * (t : ℝ) := by simpa using hmtR
  have hdensity : (r k (2 ^ m) : ℝ) / (2 : ℝ) ^ m ≤ ε / (t : ℝ) := by
    rw [htR]
    exact (dyadic_density_antitone k htm).trans (hJ j hjJ)
  have hrNm : (r k N : ℝ) ≤ (r k (2 ^ m) : ℝ) := by
    exact_mod_cast maxCard_monotone k hNm
  have hrN : (r k N : ℝ) * (t : ℝ) ≤ ε * (2 * (N : ℝ)) := by
    calc
      (r k N : ℝ) * (t : ℝ) ≤ (r k (2 ^ m) : ℝ) * (t : ℝ) :=
        mul_le_mul_of_nonneg_right hrNm htpos.le
      _ ≤ ε * (2 : ℝ) ^ m := (div_le_div_iff₀ (by positivity) htpos).mp hdensity
      _ ≤ ε * (2 * (N : ℝ)) := mul_le_mul_of_nonneg_left hmNR hε.le
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  rw [← mul_div_assoc, le_div_iff₀ hlogpos]
  calc
    (r k N : ℝ) * log (N : ℝ) ≤ (r k N : ℝ) * (2 * (t : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogle (Nat.cast_nonneg _)
    _ = 2 * ((r k N : ℝ) * (t : ℝ)) := by ring
    _ ≤ 2 * (ε * (2 * (N : ℝ))) := mul_le_mul_of_nonneg_left hrN (by norm_num)
    _ = c * (N : ℝ) := by dsimp [ε]; ring

theorem main : H1 → H2 → type_of% @Erdos142.erdos_142.variants.lower := by
  intro hCyclic hEmbed k hk
  by_cases hTwo : k = 2
  · subst k
    exact two_littleO
  have hk3 : 3 ≤ k := by omega
  apply littleO_of_sparse k
  intro ε hε
  filter_upwards [hCyclic k hk3 (ε / 4) (by positivity)] with j hj
  let L : ℕ := 2 ^ (2 ^ j)
  obtain ⟨p, hp, hpLo, hpHi, hbound⟩ := hj
  obtain ⟨S, hS, hfree, hcard⟩ := extremizer hk L
  obtain ⟨hRange, hNoAP⟩ := hEmbed k L p hk3 hpLo hp S hS hfree
  have hd := hbound S hRange hNoAP
  rw [hcard] at hd
  have hLpos : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℕ) ^ j) := by positivity
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have htpos : 0 < (2 : ℝ) ^ j := by positivity
  have hpHiR : (p : ℝ) ≤ 4 * (2 : ℝ) ^ ((2 : ℕ) ^ j) := by exact_mod_cast hpHi
  apply (div_le_div_iff₀ hLpos htpos).mpr
  calc
    (r k L : ℝ) * (2 : ℝ) ^ j ≤ (ε / 4) * (p : ℝ) :=
      (div_le_div_iff₀ hppos htpos).mp hd
    _ ≤ (ε / 4) * (4 * (2 : ℝ) ^ ((2 : ℕ) ^ j)) :=
      mul_le_mul_of_nonneg_left hpHiR (by positivity)
    _ = ε * (2 : ℝ) ^ ((2 : ℕ) ^ j) := by ring

theorem card_le_maxCard_of_cyclic_free {k p : ℕ} {S : Finset ℕ} (hk : 1 < k)
    (hS : S ⊆ Finset.range p)
    (hfree : ¬ ∃ a d : ℕ, a < p ∧ 0 < d ∧ d < p ∧
      ∀ i < k, (a + i * d) % p ∈ S) :
    S.card ≤ r k p := by
  let T := S.image (fun x => x + 1)
  have hcard : T.card = S.card :=
    Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)
  rw [← hcard]
  apply card_le_maxCard
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr ⟨Nat.succ_pos _, Finset.mem_range.mp (hS hy)⟩
  · rintro A hA ⟨a, d, hc, heq⟩
    exfalso
    apply hfree
    have hpoint (i : ℕ) (hi : i < k) : ∃ x ∈ S, x + 1 = a + i * d := by
      apply Finset.mem_image.mp
      apply hA
      rw [heq]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    obtain ⟨x, hx, hxa⟩ := hpoint 0 (by omega)
    simp only [zero_mul, add_zero] at hxa
    have hd : 0 < d := by
      by_contra! hd
      have hd0 : d = 0 := by omega
      have hsing : A ⊆ ({a} : Set ℕ) := by
        rw [heq]
        rintro _ ⟨i, hi, rfl⟩
        simp [hd0]
      have hle := Set.encard_mono hsing
      rw [← ENat.card_coe_set_eq, hc, Set.encard_singleton] at hle
      exact (not_le_of_gt hk) (by exact_mod_cast hle)
    obtain ⟨y, hy, hya⟩ := hpoint 1 hk
    have hyp := Finset.mem_range.mp (hS hy)
    have hxp := Finset.mem_range.mp (hS hx)
    simp only [one_mul] at hya
    refine ⟨x, d, hxp, hd, by omega, ?_⟩
    intro i hi
    obtain ⟨w, hw, hwa⟩ := hpoint i hi
    have hwp := Finset.mem_range.mp (hS hw)
    have he : x + i * d = w := by omega
    simpa only [he, Nat.mod_eq_of_lt hwp] using hw

/-- Translate cyclic representatives into the interval and apply the little-o estimate. -/
theorem sparse_prime_of_interval_littleO
    (hAll : ∀ k : ℕ, 1 < k →
      (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)) : H1 := by
  intro k hk ε hε
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hBound := isLittleO_iff.mp (hAll k (by omega)) (mul_pos hε hlog2)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hBound
  filter_upwards [eventually_ge_atTop J] with j hj
  let L : ℕ := 2 ^ (2 ^ j)
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨p, hp, hpLo, hpHi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * L) (by omega)
  refine ⟨p, hp, hpLo.le, by simpa only [← Nat.mul_assoc] using hpHi,
    fun S hS hfree => ?_⟩
  have hjL : j ≤ L :=
    (Nat.lt_two_pow_self (n := j)).le.trans (Nat.lt_two_pow_self (n := 2 ^ j)).le
  have hJp : J ≤ p := hj.trans (hjL.trans (by omega))
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hLogPos : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hLcast : (L : ℝ) = (2 : ℝ) ^ ((2 : ℕ) ^ j) := by
    exact_mod_cast (show L = 2 ^ ((2 : ℕ) ^ j) by rfl)
  have hLp : (L : ℝ) ≤ p := by exact_mod_cast (show L ≤ p by omega)
  have hLog : (2 : ℝ) ^ j * log 2 ≤ log (p : ℝ) := by
    calc
      (2 : ℝ) ^ j * log 2 = log (L : ℝ) := by rw [hLcast, log_pow]; norm_cast
      _ ≤ log (p : ℝ) := log_le_log (by exact_mod_cast hL) hLp
  have hBoundAtP : (r k p : ℝ) ≤ (ε * log 2) * ((p : ℝ) / log (p : ℝ)) := by
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (div_nonneg hpPos.le hLogPos.le)] using hJ p hJp
  have hcard : (S.card : ℝ) ≤ (r k p : ℝ) := by
    exact_mod_cast card_le_maxCard_of_cyclic_free (show 1 < k by omega) hS hfree
  calc
    (S.card : ℝ) / (p : ℝ) ≤ ((ε * log 2) * ((p : ℝ) / log (p : ℝ))) / (p : ℝ) :=
      div_le_div_of_nonneg_right (hcard.trans hBoundAtP) hpPos.le
    _ = (ε * log 2) / log (p : ℝ) := by field_simp
    _ ≤ (ε * log 2) / ((2 : ℝ) ^ j * log 2) :=
      div_le_div_of_nonneg_left (mul_pos hε hlog2).le (by positivity) hLog
    _ = ε / (2 : ℝ) ^ j := by field_simp

end OMA.R_Erdos142_erdos_142_variants_lower_R3
