import FormalConjectures.ErdosProblems.«168»

/-!
The Graham–Spencer–Witsenhausen decomposition groups each integer by its
factor coprime to six. Truncating the powers of two and three gives a
uniformly accurate sequence of finite approximations to the extremal density.
-/

open Finset Filter
open scoped Classical Topology BigOperators

namespace OMA.Erdos168Proof

open Erdos168

noncomputable def optimum (U : Finset ℕ) : ℕ :=
  (U.powerset.filter NonTernary).sup Finset.card

theorem le_optimum {U S : Finset ℕ} (hS : S ⊆ U) (h : NonTernary S) :
    S.card ≤ optimum U :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, h⟩)

theorem optimum_attained (U : Finset ℕ) :
    ∃ S ⊆ U, NonTernary S ∧ S.card = optimum U := by
  have hn : (U.powerset.filter NonTernary).Nonempty := ⟨∅, by simp [NonTernary]⟩
  obtain ⟨S, hS, he⟩ := Finset.exists_mem_eq_sup _ hn Finset.card
  obtain ⟨hSU, h⟩ := Finset.mem_filter.mp hS
  exact ⟨S, Finset.mem_powerset.mp hSU, h, he.symm⟩

theorem F_eq_optimum (N : ℕ) : F N = optimum (Icc 1 N) := by
  have h : IntervalNonTernarySets N = (Icc 1 N).powerset.filter NonTernary := by
    ext S
    simp [mem_IntervalNonTernarySets_iff, and_comm]
  simp only [F, optimum, h]

def cores (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun c => c.Coprime 6)

def factors (Q m : ℕ) : Finset ℕ := Q.divisors.filter (· ≤ m)

noncomputable def profile (Q m : ℕ) : ℕ := optimum (factors Q m)

noncomputable def approximation (k N : ℕ) : ℕ :=
  ∑ c ∈ cores N, profile (6 ^ k) (N / c)

theorem core_unique {c c' d d' t : ℕ}
    (hc : c.Coprime 6) (hc' : c'.Coprime 6)
    (hd : d ∣ 6 ^ t) (hd' : d' ∣ 6 ^ t) (h : c * d = c' * d') : c = c' := by
  apply Nat.dvd_antisymm
  · exact ((hc.pow_right t).of_dvd_right hd').dvd_of_dvd_mul_right
      (h ▸ dvd_mul_right c d)
  · exact ((hc'.pow_right t).of_dvd_right hd).dvd_of_dvd_mul_right
      (h.symm ▸ dvd_mul_right c' d')

theorem extract_core (n : ℕ) (hn : 0 < n) :
    ∃ c a b : ℕ, c.Coprime 6 ∧ n = c * (2 ^ a * 3 ^ b) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h₂ : 2 ∣ n
    · obtain ⟨m, hm⟩ := h₂
      obtain ⟨c, a, b, hc, h⟩ := ih m (by omega) (by omega)
      exact ⟨c, a + 1, b, hc, by rw [hm, h, pow_succ]; ring⟩
    by_cases h₃ : 3 ∣ n
    · obtain ⟨m, hm⟩ := h₃
      obtain ⟨c, a, b, hc, h⟩ := ih m (by omega) (by omega)
      exact ⟨c, a, b + 1, hc, by rw [hm, h, pow_succ]; ring⟩
    refine ⟨n, 0, 0, ?_, by simp⟩
    change n.Coprime (2 * 3)
    exact Nat.coprime_mul_iff_right.mpr
      ⟨(Nat.prime_two.coprime_iff_not_dvd.mpr h₂).symm,
        (Nat.prime_three.coprime_iff_not_dvd.mpr h₃).symm⟩

theorem extract_bounded_core {k n : ℕ} (hn : 0 < n)
    (h₂ : ¬ 2 ^ (k + 1) ∣ n) (h₃ : ¬ 3 ^ (k + 1) ∣ n) :
    ∃ c d, c.Coprime 6 ∧ d ∣ 6 ^ k ∧ n = c * d := by
  obtain ⟨c, a, b, hc, h⟩ := extract_core n hn
  have ha : a ≤ k := by
    by_contra! ha
    exact h₂ (h ▸ dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (pow_dvd_pow 2 ha) _) _)
  have hb : b ≤ k := by
    by_contra! hb
    exact h₃ (h ▸ dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right (pow_dvd_pow 3 hb) _) _)
  refine ⟨c, 2 ^ a * 3 ^ b, hc, ?_, h⟩
  change 2 ^ a * 3 ^ b ∣ (2 * 3) ^ k
  rw [mul_pow]
  exact Nat.mul_dvd_mul (pow_dvd_pow 2 ha) (pow_dvd_pow 3 hb)

theorem approximation_le (k N : ℕ) : approximation k N ≤ F N := by
  have hex (c : ℕ) := optimum_attained (factors (6 ^ k) (N / c))
  choose choice hsub hnt hcard using hex
  let S := (cores N).biUnion (fun c => (choice c).image (c * ·))
  have hmem {n : ℕ} : n ∈ S ↔
      ∃ c ∈ cores N, ∃ d ∈ choice c, c * d = n := by simp [S]
  have hdvd {c d : ℕ} (hd : d ∈ choice c) : d ∣ 6 ^ k :=
    (Nat.mem_divisors.mp (Finset.mem_filter.mp (hsub c hd)).1).1
  have hcpos {c : ℕ} (hc : c ∈ cores N) : 0 < c :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
  have hcop {c : ℕ} (hc : c ∈ cores N) : c.Coprime 6 := (Finset.mem_filter.mp hc).2
  have hSI : S ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨c, hc, d, hd, rfl⟩ := hmem.mp hn
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (hdvd hd) (by positivity)
    have hdb := (Finset.mem_filter.mp (hsub c hd)).2
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (hcpos hc) hdpos, by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (hcpos hc)).mp hdb⟩
  have hSN : NonTernary S := by
    intro n
    by_contra! hbad
    obtain ⟨c, hc, d, hd, hdn⟩ := hmem.mp hbad.1
    obtain ⟨c₂, hc₂, d₂, hd₂, hdn₂⟩ := hmem.mp hbad.2.1
    obtain ⟨c₃, hc₃, d₃, hd₃, hdn₃⟩ := hmem.mp hbad.2.2
    have hdouble : c * (2 * d) = c₂ * d₂ := by rw [hdn₂, ← hdn]; ring
    have htriple : c * (3 * d) = c₃ * d₃ := by rw [hdn₃, ← hdn]; ring
    have hstep {a : ℕ} (ha : a ∣ 6) : a * d ∣ 6 ^ (k + 1) := by
      rw [pow_succ']
      exact Nat.mul_dvd_mul ha (hdvd hd)
    have hincl : 6 ^ k ∣ 6 ^ (k + 1) := pow_dvd_pow 6 (by omega)
    have hsame₂ := core_unique (hcop hc) (hcop hc₂) (hstep (by decide : 2 ∣ 6))
      ((hdvd hd₂).trans hincl) hdouble
    have hsame₃ := core_unique (hcop hc) (hcop hc₃) (hstep (by decide : 3 ∣ 6))
      ((hdvd hd₃).trans hincl) htriple
    subst c₂
    subst c₃
    have he₂ : 2 * d = d₂ := Nat.eq_of_mul_eq_mul_left (hcpos hc) hdouble
    have he₃ : 3 * d = d₃ := Nat.eq_of_mul_eq_mul_left (hcpos hc) htriple
    rcases hnt c d with h | h | h
    · exact h hd
    · exact h (he₂ ▸ hd₂)
    · exact h (he₃ ▸ hd₃)
  have hdis : (cores N : Set ℕ).PairwiseDisjoint
      (fun c => (choice c).image (c * ·)) := by
    intro c hc c' hc' hne
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    obtain ⟨d, hd, h⟩ := Finset.mem_image.mp hn
    obtain ⟨d', hd', h'⟩ := Finset.mem_image.mp hn'
    exact hne (core_unique (hcop hc) (hcop hc') (hdvd hd) (hdvd hd') (h.trans h'.symm))
  have hSC : S.card = approximation k N := by
    rw [show S.card = ∑ c ∈ cores N, ((choice c).image (c * ·)).card from
      Finset.card_biUnion hdis, approximation]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.card_image_of_injective _ (fun _ _ h =>
      Nat.eq_of_mul_eq_mul_left (hcpos hc) h), hcard c]
    rfl
  rw [← hSC, F_eq_optimum]
  exact le_optimum hSI hSN

def multiples (D N : ℕ) : Finset ℕ :=
  (range (N / D)).image (fun i => D * (i + 1))

theorem mem_multiples {D N n : ℕ} (hD : 0 < D) (hn : 0 < n) (hN : n ≤ N)
    (h : D ∣ n) : n ∈ multiples D N := by
  obtain ⟨i, rfl⟩ := h
  have hi : 0 < i := by by_contra! hi; simp [show i = 0 by omega] at hn
  apply Finset.mem_image.mpr
  refine ⟨i - 1, Finset.mem_range.mpr ?_, by congr 1; omega⟩
  have hbound : i ≤ N / D := (Nat.le_div_iff_mul_le hD).mpr (by simpa [Nat.mul_comm] using hN)
  omega

theorem F_le_approximation_add (k N : ℕ) :
    F N ≤ approximation k N + (N / 2 ^ (k + 1) + N / 3 ^ (k + 1)) := by
  obtain ⟨S, hS, hSN, hSC⟩ := optimum_attained (Icc 1 N)
  rw [← F_eq_optimum] at hSC
  let chosen (c : ℕ) := (factors (6 ^ k) (N / c)).filter (fun d => c * d ∈ S)
  let covered := (cores N).biUnion (fun c => (chosen c).image (c * ·))
  have hCS : covered.card ≤ approximation k N := by
    calc
      covered.card ≤ ∑ c ∈ cores N, ((chosen c).image (c * ·)).card :=
        Finset.card_biUnion_le
      _ ≤ approximation k N := by
        apply Finset.sum_le_sum
        intro c _
        refine Finset.card_image_le.trans (le_optimum (Finset.filter_subset _ _) ?_)
        intro u
        by_contra! hbad
        have h₁ := (Finset.mem_filter.mp hbad.1).2
        have h₂ := (Finset.mem_filter.mp hbad.2.1).2
        have h₃ := (Finset.mem_filter.mp hbad.2.2).2
        rw [show c * (2 * u) = 2 * (c * u) by ring] at h₂
        rw [show c * (3 * u) = 3 * (c * u) by ring] at h₃
        rcases hSN (c * u) with h | h | h
        · exact h h₁
        · exact h h₂
        · exact h h₃
  have hs : S ⊆ covered ∪ (multiples (2 ^ (k + 1)) N ∪ multiples (3 ^ (k + 1)) N) := by
    intro n hn
    obtain ⟨hnpos, hN⟩ := Finset.mem_Icc.mp (hS hn)
    by_cases h₂ : 2 ^ (k + 1) ∣ n
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (mem_multiples (by positivity) hnpos hN h₂))
    by_cases h₃ : 3 ^ (k + 1) ∣ n
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (mem_multiples (by positivity) hnpos hN h₃))
    obtain ⟨c, d, hc, hd, hnEq⟩ := extract_bounded_core hnpos h₂ h₃
    have hcpos : 0 < c := by
      by_contra! h
      simp [show c = 0 by omega] at hnEq
      omega
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by positivity)
    have hcN : c ≤ N := by
      calc
        c ≤ c * d := Nat.le_mul_of_pos_right _ hdpos
        _ ≤ N := hnEq ▸ hN
    have hdc : d ≤ N / c := (Nat.le_div_iff_mul_le hcpos).mpr (by
      rw [Nat.mul_comm, ← hnEq]
      exact hN)
    refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨c, ?_, Finset.mem_image.mpr ⟨d, ?_, hnEq.symm⟩⟩)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hcpos, hcN⟩, hc⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hd, by positivity⟩, hdc⟩, hnEq ▸ hn⟩
  rw [← hSC]
  exact (Finset.card_le_card hs).trans
    (Finset.card_union_le _ _ |>.trans
      (Nat.add_le_add hCS (Finset.card_union_le _ _ |>.trans
        (Nat.add_le_add (Finset.card_image_le.trans (by simp))
          (Finset.card_image_le.trans (by simp))))))


theorem profile_zero (Q : ℕ) : profile Q 0 = 0 := by
  have hz : factors Q 0 = ∅ := by
    ext d
    simp only [factors, Finset.mem_filter, Nat.mem_divisors, Nat.le_zero,
      Finset.notMem_empty, iff_false]
    rintro ⟨⟨hd, hQ⟩, rfl⟩
    exact hQ (Nat.zero_dvd.mp hd)
  obtain ⟨S, hS, _, hcard⟩ := optimum_attained (factors Q 0)
  rw [hz, Finset.subset_empty] at hS
  simpa [profile, hS] using hcard.symm

theorem profile_mono (Q : ℕ) : Monotone (profile Q) := by
  intro a b hab
  obtain ⟨S, hS, hnt, hcard⟩ := optimum_attained (factors Q a)
  rw [profile, ← hcard]
  refine le_optimum (hS.trans ?_) hnt
  intro d hd
  obtain ⟨hdQ, hda⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hdQ, hda.trans hab⟩

theorem profile_min {Q : ℕ} (hQ : 0 < Q) (m : ℕ) :
    profile Q (min m Q) = profile Q m := by
  have he : factors Q (min m Q) = factors Q m := by
    ext d
    simp only [factors, Finset.mem_filter, le_min_iff]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h =>
      ⟨h.1, h.2, Nat.le_of_dvd hQ (Nat.mem_divisors.mp h.1).1⟩⟩
  rw [profile, he, profile]

theorem step_sum (g : ℕ → ℕ) (h₀ : g 0 = 0) (hg : Monotone g) (n q : ℕ) :
    g (min n q) = ∑ i ∈ range q, if i + 1 ≤ n then g (i + 1) - g i else 0 := by
  induction q with
  | zero => simpa using h₀
  | succ q ih =>
    rw [Finset.sum_range_succ, ← ih]
    by_cases h : q + 1 ≤ n
    · rw [if_pos h, min_eq_right h, min_eq_right (show q ≤ n by omega)]
      have hh := hg (show q ≤ q + 1 by omega)
      omega
    · rw [if_neg h, Nat.add_zero, min_eq_left (show n ≤ q + 1 by omega),
        min_eq_left (show n ≤ q by omega)]
      simp

theorem core_threshold (N i : ℕ) :
    (cores N).filter (fun c => i + 1 ≤ N / c) = cores (N / (i + 1)) := by
  ext c
  simp only [cores, Finset.mem_filter, Finset.mem_Icc]
  have hi : 0 < i + 1 := by omega
  constructor
  · rintro ⟨⟨⟨hc, _⟩, hco⟩, hb⟩
    have hmul := (Nat.le_div_iff_mul_le (show 0 < c by omega)).mp hb
    exact ⟨⟨hc, (Nat.le_div_iff_mul_le hi).mpr (by simpa [Nat.mul_comm] using hmul)⟩, hco⟩
  · rintro ⟨⟨hc, hb⟩, hco⟩
    have hmul := (Nat.le_div_iff_mul_le hi).mp hb
    refine ⟨⟨⟨hc, hb.trans (Nat.div_le_self _ _)⟩, hco⟩, ?_⟩
    exact (Nat.le_div_iff_mul_le (show 0 < c by omega)).mpr (by simpa [Nat.mul_comm] using hmul)

theorem approximation_sum (k N : ℕ) :
    approximation k N =
      ∑ i ∈ range (6 ^ k), (cores (N / (i + 1))).card *
        (profile (6 ^ k) (i + 1) - profile (6 ^ k) i) := by
  calc
    approximation k N =
        ∑ c ∈ cores N, ∑ i ∈ range (6 ^ k),
          if i + 1 ≤ N / c then profile (6 ^ k) (i + 1) - profile (6 ^ k) i else 0 := by
      unfold approximation
      apply Finset.sum_congr rfl
      intro c _
      rw [← profile_min (by positivity : 0 < (6 : ℕ) ^ k) (N / c)]
      exact step_sum _ (profile_zero _) (profile_mono _) _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter, core_threshold]
      simp

theorem coprime_six_iff (c : ℕ) : c.Coprime 6 ↔ c % 6 = 1 ∨ c % 6 = 5 := by
  have h₂ : c.Coprime 2 ↔ ¬ 2 ∣ c := Nat.coprime_comm.trans Nat.prime_two.coprime_iff_not_dvd
  have h₃ : c.Coprime 3 ↔ ¬ 3 ∣ c := Nat.coprime_comm.trans Nat.prime_three.coprime_iff_not_dvd
  change c.Coprime (2 * 3) ↔ _
  rw [Nat.coprime_mul_iff_right, h₂, h₃]
  simp only [Nat.dvd_iff_mod_eq_zero]
  rw [← Nat.mod_mod_of_dvd c (by decide : 2 ∣ 6),
    ← Nat.mod_mod_of_dvd c (by decide : 3 ∣ 6)]
  omega

def residue (M r : ℕ) : Finset ℕ := (Icc 1 M).filter (fun c => c % 6 = r)

theorem residue_count (M r : ℕ) (hr₀ : 0 < r) (hr₆ : r < 6) :
    (residue M r).card = (M + (6 - r)) / 6 := by
  have he : residue M r = (range ((M + (6 - r)) / 6)).image (fun i => 6 * i + r) := by
    ext c
    simp only [residue, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨hc₀, hcM⟩, hcr⟩
      exact ⟨c / 6, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [he, Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]

theorem cores_count (M : ℕ) : (cores M).card = (M + 5) / 6 + (M + 1) / 6 := by
  have he : cores M = residue M 1 ∪ residue M 5 := by
    ext c
    simp only [cores, residue, Finset.mem_union, Finset.mem_filter, coprime_six_iff]
    tauto
  have hd : Disjoint (residue M 1) (residue M 5) := by
    apply Finset.disjoint_left.mpr
    intro c h₁ h₅
    have hr₁ := (Finset.mem_filter.mp h₁).2
    have hr₅ := (Finset.mem_filter.mp h₅).2
    omega
  rw [he, Finset.card_union_of_disjoint hd, residue_count M 1 (by decide) (by decide),
    residue_count M 5 (by decide) (by decide)]

theorem one_div_nat_tendsto : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem cores_ratio_tendsto (t : ℕ) (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((cores (N / t)).card : ℝ) / N) atTop (𝓝 (1 / (3 * (t : ℝ)))) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hq : 0 < 6 * t := by omega
  have herr (N : ℕ) (hN : 0 < N) :
      dist (((cores (N / t)).card : ℝ) / N) (1 / (3 * (t : ℝ))) ≤ 2 / (N : ℝ) := by
    have hf : N / (6 * t) = (N / t) / 6 := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm 6]
    have hlow : 2 * (N / (6 * t)) ≤ (cores (N / t)).card := by
      rw [hf, cores_count]
      omega
    have hhigh : (cores (N / t)).card ≤ 2 * (N / (6 * t)) + 2 := by
      rw [hf, cores_count]
      omega
    have hlow' : (2 : ℝ) * ((N / (6 * t) : ℕ) : ℝ) ≤ (cores (N / t)).card := by exact_mod_cast hlow
    have hhigh' : ((cores (N / t)).card : ℝ) ≤ 2 * ((N / (6 * t) : ℕ) : ℝ) + 2 := by
      exact_mod_cast hhigh
    have hrem : ((N % (6 * t) : ℕ) : ℝ) < 6 * (t : ℝ) := by exact_mod_cast Nat.mod_lt N hq
    have heq : ((N % (6 * t) : ℕ) : ℝ) + 6 * (t : ℝ) * ((N / (6 * t) : ℕ) : ℝ) = N := by
      exact_mod_cast Nat.mod_add_div N (6 * t)
    have hrem₀ : (0 : ℝ) ≤ ((N % (6 * t) : ℕ) : ℝ) := by positivity
    have ht₃ : (0 : ℝ) < 3 * (t : ℝ) := by positivity
    have hlo : (N : ℝ) / (3 * (t : ℝ)) - 2 ≤ (cores (N / t)).card := by
      rw [sub_le_iff_le_add, div_le_iff₀ ht₃]
      nlinarith [mul_le_mul_of_nonneg_right hlow' ht₃.le]
    have hhi : ((cores (N / t)).card : ℝ) - 2 ≤ (N : ℝ) / (3 * (t : ℝ)) := by
      rw [le_div_iff₀ ht₃]
      nlinarith [mul_le_mul_of_nonneg_right hhigh' ht₃.le]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.dist_eq]
    have hrewrite : ((cores (N / t)).card : ℝ) / N - 1 / (3 * (t : ℝ)) =
        (((cores (N / t)).card : ℝ) - (N : ℝ) / (3 * (t : ℝ))) / N := by
      field_simp
    rw [hrewrite, abs_div, abs_of_pos hN']
    apply div_le_div_of_nonneg_right _ hN'.le
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hinv := (tendsto_const_nhds (x := (2 : ℝ))).div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hinv ε hε
  refine ⟨max M 1, fun N hN => (herr N (by omega)).trans_lt ?_⟩
  simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) / N)] using
    hM N ((le_max_left _ _).trans hN)

theorem approximation_ratio_tendsto (k : ℕ) :
    ∃ x : ℝ, Tendsto (fun N : ℕ => (approximation k N : ℝ) / N) atTop (𝓝 x) := by
  let gain (i : ℕ) : ℕ := profile (6 ^ k) (i + 1) - profile (6 ^ k) i
  let weight (i : ℕ) : ℝ := 1 / (3 * ((i + 1 : ℕ) : ℝ))
  refine ⟨∑ i ∈ range (6 ^ k), weight i * (gain i : ℝ), ?_⟩
  have h : Tendsto
      (fun N : ℕ => ∑ i ∈ range (6 ^ k),
        (((cores (N / (i + 1))).card : ℝ) / N) * (gain i : ℝ)) atTop
      (𝓝 (∑ i ∈ range (6 ^ k), weight i * (gain i : ℝ))) :=
    tendsto_finsetSum _ (fun i _ => (cores_ratio_tendsto (i + 1) (by omega)).mul tendsto_const_nhds)
  convert h using 1
  ext N
  rw [approximation_sum]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change ((cores (N / (i + 1))).card : ℝ) * (gain i : ℝ) / N =
    ((cores (N / (i + 1))).card : ℝ) / N * (gain i : ℝ)
  ring

theorem approximation_error (k N : ℕ) :
    dist ((F N : ℝ) / N) ((approximation k N : ℝ) / N) ≤
      (1 / 2 : ℝ) ^ (k + 1) + (1 / 3 : ℝ) ^ (k + 1) := by
  by_cases hN : N = 0
  · subst N
    simp
    positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hmin : ((approximation k N : ℕ) : ℝ) ≤ F N := by exact_mod_cast approximation_le k N
  have hmax : (F N : ℝ) ≤ (approximation k N : ℝ) +
      ((N / 2 ^ (k + 1) : ℕ) : ℝ) + ((N / 3 ^ (k + 1) : ℕ) : ℝ) := by
    rw [add_assoc]
    exact_mod_cast F_le_approximation_add k N
  have hdiv (d : ℕ) (hd : 0 < d) : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
    rw [le_div_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast Nat.div_mul_le_self N d
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (div_le_div_of_nonneg_right hmin hN'.le)),
    ← sub_div]
  simp only [div_pow, one_pow]
  rw [div_le_iff₀ hN']
  have h₂ := hdiv (2 ^ (k + 1)) (by positivity)
  have h₃ := hdiv (3 ^ (k + 1)) (by positivity)
  push_cast at h₂ h₃
  rw [add_mul, one_div_mul_eq_div, one_div_mul_eq_div]
  linarith

theorem limit_exists : ∃ x : ℝ, Tendsto (fun N : ℕ => (F N : ℝ) / N) atTop (𝓝 x) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have h₂ : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h₃ : Tendsto (fun k : ℕ => (1 / 3 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hz : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k + (1 / 3 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using h₂.add h₃
  obtain ⟨k, hk⟩ := (eventually_atTop.mp (hz.eventually (gt_mem_nhds (show 0 < ε / 3 by positivity))))
  have hclose (N : ℕ) : dist ((F N : ℝ) / N) ((approximation k N : ℝ) / N) < ε / 3 :=
    (approximation_error k N).trans_lt (hk (k + 1) (by omega))
  obtain ⟨x, hx⟩ := approximation_ratio_tendsto k
  have hc : CauchySeq (fun N : ℕ => (approximation k N : ℝ) / N) := hx.cauchySeq
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hc (ε / 3) (by positivity)
  refine ⟨M, fun m hm n hn => ?_⟩
  have hb := dist_triangle ((F m : ℝ) / m) ((approximation k m : ℝ) / m) ((F n : ℝ) / n)
  have hb' := dist_triangle ((approximation k m : ℝ) / m)
    ((approximation k n : ℝ) / n) ((F n : ℝ) / n)
  have hn' := hclose n
  rw [dist_comm] at hn'
  linarith [hclose m, hM m hm n hn]

end OMA.Erdos168Proof

theorem OMA.solution : type_of% @Erdos168.erdos_168.variants.limit_exists :=
  OMA.Erdos168Proof.limit_exists
