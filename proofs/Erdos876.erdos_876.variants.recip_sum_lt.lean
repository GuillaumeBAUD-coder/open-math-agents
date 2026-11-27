import FormalConjectures.ErdosProblems.«876»

-- Problem: Erdős Problem 876, reciprocal sum of a sum-free sequence is below 103
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/876.lean (declaration Erdos876.erdos_876.variants.recip_sum_lt)
-- Reference: P. Erdős, Some remarks on number theory III (Hungarian), Mat. Lapok 13 (1962), Theorem II.

/-!
# Erdős 876: the reciprocal sum of a sum-free set is less than 103

Following Erdős (1962). For an initial segment `B` of `A` with `k` elements and sum `S`, the
`k + 1` translates `S_c + {a ∈ A : a > c}` are pairwise disjoint (a collision would write an
element of `A` as a sum of distinct smaller elements), which gives
`(k + 1) A(x) ≤ x + (k + 1)(S + k)`. Split the dyadic blocks `(2^j, 2^(j+1)]` into those holding
at most `2^j / j^2` elements (total contribution at most `2`) and the others. The `r`-th block of
the second kind with `r ≥ 100` contributes less than `4 / r^2`, by the inequality above applied
with an earlier large block; the first `99` contribute at most `1` each.
-/

open Finset

namespace OMAE876
open Erdos876 Classical

noncomputable def F (A : Set ℕ) (x : ℕ) : Finset ℕ := (Icc 1 x).filter (· ∈ A)

lemma mem_F {A : Set ℕ} {x a : ℕ} : a ∈ F A x ↔ 1 ≤ a ∧ a ≤ x ∧ a ∈ A := by
  simp [F, and_assoc]

lemma F_mono (A : Set ℕ) {x y : ℕ} (h : x ≤ y) : F A x ⊆ F A y := by
  intro a ha; rw [mem_F] at ha ⊢; exact ⟨ha.1, by omega, ha.2.2⟩

/-- Erdős's inequality (4). -/
lemma key (A : Set ℕ) (hs : IsSubsetSumFree A) (y x : ℕ) :
    ((F A y).card + 1) * (F A x).card ≤
      x + ((F A y).card + 1) * ((∑ a ∈ F A y, a) + (F A y).card) := by
  set k := (F A y).card
  set S := ∑ a ∈ F A y, a
  let I : Finset ℕ := insert 0 (F A y)
  have h0 : (0 : ℕ) ∉ F A y := by simp [mem_F]
  have hI : I.card = k + 1 := by simp [I, card_insert_of_notMem h0, k]
  let G : ℕ → Finset ℕ := fun c =>
    ((F A x).filter (fun a => c < a ∧ a + ∑ b ∈ F A c, b ≤ x)).image (· + ∑ b ∈ F A c, b)
  -- each G c lies in Icc 1 x
  have hGsub : ∀ c ∈ I, G c ⊆ Icc 1 x := by
    intro c _ z hz
    simp only [G, mem_image, mem_filter, mem_F] at hz
    obtain ⟨a, ⟨⟨ha1, _, _⟩, _, hax⟩, rfl⟩ := hz
    simp only [mem_Icc]; omega
  -- disjointness
  have hdisj : (I : Set ℕ).PairwiseDisjoint G := by
    have main : ∀ c ∈ I, ∀ c' ∈ I, c < c' → Disjoint (G c) (G c') := by
      intro c hc c' hc' hlt
      rw [Finset.disjoint_left]
      intro z hz hz'
      simp only [G, mem_image, mem_filter] at hz hz'
      obtain ⟨a, ⟨haF, hca, _⟩, rfl⟩ := hz
      obtain ⟨b, ⟨hbF, hcb, _⟩, hab⟩ := hz'
      have hc'F : c' ∈ F A y := by
        rcases mem_insert.1 hc' with h | h
        · omega
        · exact h
      have hsub : F A c ⊆ F A c' := F_mono A hlt.le
      have hc'mem : c' ∈ F A c' \ F A c := by
        rw [mem_F] at hc'F
        exact mem_sdiff.2 ⟨mem_F.2 ⟨hc'F.1, le_rfl, hc'F.2.2⟩, fun h => by rw [mem_F] at h; omega⟩
      have hsd : ∑ i ∈ F A c' \ F A c, i + ∑ i ∈ F A c, i = ∑ i ∈ F A c', i := sum_sdiff hsub
      have hpos : 0 < ∑ i ∈ F A c' \ F A c, i := by
        apply Finset.sum_pos' (fun i _ => Nat.zero_le i) ⟨c', hc'mem, by omega⟩
      rw [mem_F] at haF hbF
      have hb_notin : b ∉ F A c' \ F A c := by
        intro h; rw [mem_sdiff, mem_F] at h; omega
      apply (hs a haF.2.2).2
      refine ⟨insert b (F A c' \ F A c), ?_, ?_⟩
      · intro w hw
        simp only [coe_insert, Set.mem_insert_iff, mem_coe, mem_sdiff, mem_F] at hw
        refine ⟨?_, ?_⟩
        · rcases hw with rfl | hw
          · exact hbF.2.2
          · exact hw.1.2.2
        · show w < a
          rcases hw with rfl | hw <;> omega
      · rw [sum_insert hb_notin]; omega
    intro c hc c' hc' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact main c hc c' hc' h
    · exact (main c' hc' c hc h).symm
  -- lower bound on each G c
  have hGcard : ∀ c ∈ I, (F A x).card ≤ (G c).card + S + k := by
    intro c hc
    have hcy : c ≤ y := by
      rcases mem_insert.1 hc with h | h
      · omega
      · exact (mem_F.1 h).2.1
    have hTsub : F A c ⊆ F A y := F_mono A hcy
    have hSc : ∑ b ∈ F A c, b ≤ S := sum_le_sum_of_subset hTsub
    have hkc : (F A c).card ≤ k := card_le_card hTsub
    set Sc := ∑ b ∈ F A c, b
    have hinj : (G c).card = ((F A x).filter (fun a => c < a ∧ a + Sc ≤ x)).card :=
      card_image_of_injective _ (add_left_injective Sc)
    -- complement is covered by F A c and Ioc (x - Sc) x
    have hcov : (F A x) ⊆ ((F A x).filter (fun a => c < a ∧ a + Sc ≤ x)) ∪
        (F A c ∪ Ioc (x - Sc) x) := by
      intro a ha
      rw [mem_F] at ha
      by_cases h1 : c < a ∧ a + Sc ≤ x
      · exact mem_union_left _ (mem_filter.2 ⟨mem_F.2 ha, h1⟩)
      · apply mem_union_right
        rcases not_and_or.1 h1 with h | h
        · exact mem_union_left _ (mem_F.2 ⟨ha.1, by omega, ha.2.2⟩)
        · exact mem_union_right _ (by rw [mem_Ioc]; omega)
    have := card_le_card hcov
    have h2 := card_union_le ((F A x).filter (fun a => c < a ∧ a + Sc ≤ x)) (F A c ∪ Ioc (x - Sc) x)
    have h3 := card_union_le (F A c) (Ioc (x - Sc) x)
    simp only [Nat.card_Ioc] at h3
    omega
  have hsum : ∑ c ∈ I, (G c).card ≤ x := by
    rw [← card_biUnion hdisj]
    calc (I.biUnion G).card ≤ (Icc 1 x).card := card_le_card (biUnion_subset.2 hGsub)
      _ = x := by simp
  have : ∑ c ∈ I, (F A x).card ≤ ∑ c ∈ I, ((G c).card + S + k) := sum_le_sum hGcard
  simp only [sum_const, smul_eq_mul, hI, sum_add_distrib] at this
  nlinarith [this, hsum]


lemma card_F_succ (A : Set ℕ) (z : ℕ) : (F A (z + 1)).card ≤ (F A z).card + 1 := by
  have : F A (z + 1) ⊆ insert (z + 1) (F A z) := by
    intro a ha; rw [mem_F] at ha
    rcases Nat.lt_or_ge a (z + 1) with h | h
    · exact mem_insert_of_mem (mem_F.2 ⟨ha.1, by omega, ha.2.2⟩)
    · rw [show a = z + 1 by omega]; exact mem_insert_self _ _
  exact (card_le_card this).trans (card_insert_le _ _)

lemma ivt (A : Set ℕ) (z m : ℕ) (hm : m ≤ (F A z).card) : ∃ y ≤ z, (F A y).card = m := by
  induction z with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    have : F A 0 = ∅ := by ext a; simp [mem_F]; omega
    rw [this] at hm ⊢; simp at hm ⊢; omega
  | succ z ih =>
    rcases Nat.lt_or_ge (F A z).card m with h | h
    · have := card_F_succ A z
      exact ⟨z + 1, le_rfl, by omega⟩
    · obtain ⟨y, hy, hy'⟩ := ih h
      exact ⟨y, by omega, hy'⟩

/-- Corollary of `key`. -/
lemma cor (A : Set ℕ) (hs : IsSubsetSumFree A) (K t j : ℕ) (hK : K ≤ (F A (2 ^ (t + 1))).card)
    (htj : t ≤ j) (hpow : 2 * (K + 1) ^ 2 ≤ 2 ^ (j - t)) :
    (K + 1) * (F A (2 ^ (j + 1))).card ≤ 2 ^ (j + 2) := by
  obtain ⟨y, hy, hyK⟩ := ivt A _ K hK
  have h := key A hs y (2 ^ (j + 1))
  rw [hyK] at h
  have hS : ∑ a ∈ F A y, a ≤ K * 2 ^ (t + 1) := by
    calc ∑ a ∈ F A y, a ≤ (F A y).card • y := sum_le_card_nsmul _ _ _ (fun a ha => (mem_F.1 ha).2.1)
      _ ≤ K * 2 ^ (t + 1) := by rw [hyK, smul_eq_mul]; exact Nat.mul_le_mul_left _ hy
  have hpj : 2 ^ (j + 1) = 2 ^ (j - t) * 2 ^ (t + 1) := by
    rw [← pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ (t + 1) := Nat.one_le_two_pow
  have h2 : (K + 1) * (∑ a ∈ F A y, a + K) ≤ 2 ^ (j + 1) := by
    calc (K + 1) * (∑ a ∈ F A y, a + K) ≤ (K + 1) * (K * 2 ^ (t + 1) + K * 2 ^ (t + 1)) := by
          apply Nat.mul_le_mul_left; nlinarith
      _ = 2 * (K + 1) * K * 2 ^ (t + 1) := by ring
      _ ≤ 2 * (K + 1) ^ 2 * 2 ^ (t + 1) := by
          apply Nat.mul_le_mul_right; nlinarith
      _ ≤ 2 ^ (j - t) * 2 ^ (t + 1) := Nat.mul_le_mul_right _ hpow
      _ = 2 ^ (j + 1) := hpj.symm
  rw [pow_succ 2 (j + 1)]
  omega

lemma num1 (t : ℕ) (ht : 30 ≤ t) : 32 * (t + 2) ^ 4 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    have hn' : (32 : ℕ) ≤ n + 2 := by omega
    have : (n + 1 + 2) ^ 4 ≤ 2 * (n + 2) ^ 4 := by
      have e : n + 1 + 2 = (n + 2) + 1 := by ring
      rw [e]
      set u := n + 2
      nlinarith [pow_le_pow_left₀ (Nat.zero_le _) hn' 2, pow_le_pow_left₀ (Nat.zero_le _) hn' 3,
        Nat.mul_le_mul_right (u ^ 3) hn']
    nlinarith

noncomputable def β (A : Set ℕ) (j : ℕ) : ℝ := ∑ a ∈ F A (2 ^ (j + 1)) \ F A (2 ^ j), (1 : ℝ) / a

noncomputable def D (A : Set ℕ) (j : ℕ) : ℕ := (F A (2 ^ (j + 1)) \ F A (2 ^ j)).card

lemma β_le (A : Set ℕ) (j : ℕ) : β A j ≤ (D A j : ℝ) / 2 ^ j := by
  unfold β D
  rw [div_eq_mul_one_div, mul_comm]
  have := sum_le_card_nsmul (F A (2 ^ (j + 1)) \ F A (2 ^ j)) (fun a : ℕ => (1 : ℝ) / a)
    ((1 : ℝ) / 2 ^ j) (by
      intro a ha
      rw [mem_sdiff, mem_F, mem_F] at ha
      have : 2 ^ j < a := by
        by_contra hc; exact ha.2 ⟨ha.1.1, by omega, ha.1.2.2⟩
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast this.le)
  simpa [nsmul_eq_mul, mul_comm] using this

lemma D_le (A : Set ℕ) (j : ℕ) : D A j ≤ 2 ^ j := by
  unfold D
  have : F A (2 ^ (j + 1)) \ F A (2 ^ j) ⊆ Ioc (2 ^ j) (2 ^ (j + 1)) := by
    intro a ha
    rw [mem_sdiff, mem_F, mem_F] at ha
    rw [mem_Ioc]
    by_contra hc; apply ha.2; refine ⟨ha.1.1, ?_, ha.1.2.2⟩; omega
  have h := card_le_card this
  rw [Nat.card_Ioc] at h
  have h2 : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
  omega

lemma D_le_F (A : Set ℕ) (j : ℕ) : D A j ≤ (F A (2 ^ (j + 1))).card :=
  card_le_card sdiff_subset

lemma β_le_one (A : Set ℕ) (j : ℕ) : β A j ≤ 1 := by
  refine (β_le A j).trans ?_
  rw [div_le_one (by positivity)]
  exact_mod_cast D_le A j

lemma total (A : Set ℕ) (J : ℕ) :
    ∑ a ∈ F A (2 ^ (J + 1)), (1 : ℝ) / a = ∑ a ∈ F A 2, (1 : ℝ) / a + ∑ j ∈ Icc 1 J, β A j := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_Icc_succ_top (by omega), ← add_assoc, ← ih, β]
    have hsub : F A (2 ^ (J + 1)) ⊆ F A (2 ^ (J + 1 + 1)) := F_mono A (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [← sum_sdiff hsub]; ring

lemma small (A : Set ℕ) : ∑ a ∈ F A 2, (1 : ℝ) / a ≤ 3 / 2 := by
  have : F A 2 ⊆ {1, 2} := by
    intro a ha; rw [mem_F] at ha; simp; omega
  calc ∑ a ∈ F A 2, (1 : ℝ) / a ≤ ∑ a ∈ ({1, 2} : Finset ℕ), (1 : ℝ) / a :=
        sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => by positivity)
    _ = 3 / 2 := by norm_num

noncomputable def C (A : Set ℕ) (J : ℕ) : Finset ℕ := (Icc 1 J).filter (fun j => 2 ^ j < j ^ 2 * D A j)

noncomputable def rk (A : Set ℕ) (J j : ℕ) : ℕ := ((C A J).filter (· ≤ j)).card

lemma first_class (A : Set ℕ) (J j : ℕ) (hj : j ∈ Icc 1 J) (hC : j ∉ C A J) :
    β A j ≤ ((j : ℝ) ^ 2)⁻¹ := by
  have h1 : 1 ≤ j := (mem_Icc.1 hj).1
  have hle : j ^ 2 * D A j ≤ 2 ^ j := by
    simp only [C, mem_filter, not_and, not_lt] at hC; exact hC hj
  refine (β_le A j).trans ?_
  have hj0 : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ hj0]
  have : ((j ^ 2 * D A j : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at this; linarith

lemma rk_le (A : Set ℕ) (J c : ℕ) : rk A J c ≤ c := by
  unfold rk
  have : (C A J).filter (· ≤ c) ⊆ Icc 1 c := by
    intro a ha; simp only [C, mem_filter, mem_Icc] at ha; rw [mem_Icc]; omega
  simpa using card_le_card this

lemma rk_pos (A : Set ℕ) (J c : ℕ) (hc : c ∈ C A J) : 1 ≤ rk A J c := by
  unfold rk; apply card_pos.2; exact ⟨c, mem_filter.2 ⟨hc, le_rfl⟩⟩

lemma rk_lt (A : Set ℕ) (J c c' : ℕ) (hc' : c' ∈ C A J) (h : c < c') : rk A J c < rk A J c' := by
  unfold rk
  apply card_lt_card
  refine ⟨fun a ha => ?_, fun hsub => ?_⟩
  · simp only [mem_filter] at ha ⊢; exact ⟨ha.1, by omega⟩
  · have := hsub (mem_filter.2 ⟨hc', le_rfl⟩); simp only [mem_filter] at this; omega

lemma rk_injOn (A : Set ℕ) (J : ℕ) : Set.InjOn (rk A J) (C A J) := by
  intro c hc c' hc' h
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact absurd h (rk_lt A J c c' hc' h').ne
  · exact absurd h (rk_lt A J c' c hc h').ne'

lemma rk_exists (A : Set ℕ) (J j m : ℕ) (hj : j ∈ C A J) (hm1 : 1 ≤ m) (hm : m ≤ rk A J j) :
    ∃ t ∈ C A J, t ≤ j ∧ rk A J t = m := by
  set Cj := (C A J).filter (· ≤ j)
  have hsub : Cj.image (rk A J) ⊆ Icc 1 (rk A J j) := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hi
    rw [mem_filter] at hc
    rw [mem_Icc]; refine ⟨rk_pos A J c hc.1, ?_⟩
    rcases Nat.lt_or_ge c j with h | h
    · exact (rk_lt A J c j hj h).le
    · rw [show c = j by omega]
  have hcard : (Icc 1 (rk A J j)).card ≤ (Cj.image (rk A J)).card := by
    rw [card_image_of_injOn ((rk_injOn A J).mono (by intro x hx; exact (mem_filter.1 hx).1))]
    simp [Cj, rk]
  have heq := eq_of_subset_of_card_le hsub hcard
  have : m ∈ Cj.image (rk A J) := by rw [heq, mem_Icc]; exact ⟨hm1, hm⟩
  obtain ⟨t, ht, htm⟩ := mem_image.1 this
  rw [mem_filter] at ht
  exact ⟨t, ht.1, ht.2, htm⟩

lemma rk_gap (A : Set ℕ) (J t j : ℕ) (htj : t ≤ j) : rk A J j - rk A J t ≤ j - t := by
  unfold rk
  have hsub : (C A J).filter (· ≤ t) ⊆ (C A J).filter (· ≤ j) := by
    intro a ha; simp only [mem_filter] at ha ⊢; exact ⟨ha.1, by omega⟩
  have : (C A J).filter (· ≤ j) \ (C A J).filter (· ≤ t) ⊆ Ioc t j := by
    intro a ha; simp only [mem_sdiff, mem_filter, not_and, not_le] at ha; rw [mem_Ioc]
    exact ⟨ha.2 ha.1.1, ha.1.2⟩
  have h := card_le_card this
  rw [card_sdiff_of_subset hsub, Nat.card_Ioc] at h
  exact h

lemma second_class (A : Set ℕ) (hs : IsSubsetSumFree A) (J j : ℕ) (hj : j ∈ C A J)
    (hr : 100 ≤ rk A J j) : β A j ≤ 4 / ((rk A J j : ℝ) ^ 2) := by
  set r := rk A J j with hr_def
  set m := (r + 1) / 2 with hm_def
  obtain ⟨t, htC, htj, htm⟩ := rk_exists A J j m hj (by omega) (by omega)
  have hmt : m ≤ t := htm ▸ rk_le A J t
  have hgap := rk_gap A J t j htj
  rw [htm] at hgap
  set q := r - m with hq_def
  have hq50 : 50 ≤ q := by omega
  have hrq : r ≤ 2 * q + 1 := by omega
  have hr2t : r ≤ 2 * t := by omega
  -- the block at t is large
  have htC' : 2 ^ t < t ^ 2 * D A t := (mem_filter.1 htC).2
  have hn1 := num1 t (by omega)
  have hDt : r ^ 2 ≤ D A t := by
    by_contra hcon
    push Not at hcon
    have e1 : t ^ 2 * D A t ≤ t ^ 2 * r ^ 2 := Nat.mul_le_mul_left _ hcon.le
    have e2 : t ^ 2 * r ^ 2 ≤ t ^ 2 * (2 * t) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr2t 2)
    have e3 : t ^ 2 * (2 * t) ^ 2 ≤ 32 * (t + 2) ^ 4 := by
      have : t ^ 2 * (2 * t) ^ 2 = 4 * t ^ 4 := by ring
      rw [this]; have := Nat.pow_le_pow_left (show t ≤ t + 2 by omega) 4; omega
    omega
  have hK : r ^ 2 ≤ (F A (2 ^ (t + 1))).card := hDt.trans (D_le_F A t)
  have hpow : 2 * (r ^ 2 + 1) ^ 2 ≤ 2 ^ (j - t) := by
    have hq1 := num1 q (by omega)
    have a1 : r ^ 2 + 1 ≤ 4 * (q + 2) ^ 2 := by nlinarith
    have a2 : (r ^ 2 + 1) ^ 2 ≤ (4 * (q + 2) ^ 2) ^ 2 := Nat.pow_le_pow_left a1 2
    have a3 : 2 ^ q ≤ 2 ^ (j - t) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a4 : (4 * (q + 2) ^ 2) ^ 2 = 16 * (q + 2) ^ 4 := by ring
    omega
  have hc := cor A hs (r ^ 2) t j hK htj hpow
  -- conclude
  refine (β_le A j).trans ?_
  have hDj : (D A j : ℝ) ≤ (F A (2 ^ (j + 1))).card := by exact_mod_cast D_le_F A j
  have hc' : ((r : ℝ) ^ 2 + 1) * ((F A (2 ^ (j + 1))).card : ℝ) ≤ (2 : ℝ) ^ (j + 2) := by
    exact_mod_cast hc
  have h4 : (2 : ℝ) ^ (j + 2) = 2 ^ j * 4 := by ring
  have hr100 : (100 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hr0]
  have hF0 : (0 : ℝ) ≤ ((F A (2 ^ (j + 1))).card : ℝ) := by positivity
  calc (D A j : ℝ) * (r : ℝ) ^ 2 ≤ ((F A (2 ^ (j + 1))).card : ℝ) * (r : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hDj hr0.le
    _ ≤ ((r : ℝ) ^ 2 + 1) * ((F A (2 ^ (j + 1))).card : ℝ) := by nlinarith
    _ ≤ 4 * 2 ^ j := by linarith

lemma second_sum (A : Set ℕ) (hs : IsSubsetSumFree A) (J : ℕ) :
    ∑ j ∈ C A J, β A j ≤ 99 + 8 / 100 := by
  rw [← sum_filter_add_sum_filter_not (C A J) (fun j => rk A J j < 100)]
  have hinj := rk_injOn A J
  have p1 : ∑ j ∈ (C A J).filter (fun j => rk A J j < 100), β A j ≤ 99 := by
    calc _ ≤ ∑ j ∈ (C A J).filter (fun j => rk A J j < 100), (1 : ℝ) := sum_le_sum (fun j _ => β_le_one A j)
      _ = ((C A J).filter (fun j => rk A J j < 100)).card := by simp
      _ ≤ 99 := by
        have : ((C A J).filter (fun j => rk A J j < 100)).card ≤ (Icc 1 99).card := by
          apply card_le_card_of_injOn (rk A J)
          · intro c hc; simp only [coe_filter, Set.mem_ofPred_eq] at hc
            simp only [coe_Icc, Set.mem_Icc]; exact ⟨rk_pos A J c hc.1, by omega⟩
          · exact hinj.mono (by intro x hx; simp only [coe_filter, Set.mem_ofPred_eq] at hx; exact hx.1)
        simp at this; exact_mod_cast this
  have p2 : ∑ j ∈ (C A J).filter (fun j => ¬ rk A J j < 100), β A j ≤ 8 / 100 := by
    set C' := (C A J).filter (fun j => ¬ rk A J j < 100)
    have hinj' : Set.InjOn (rk A J) C' := hinj.mono (by intro x hx; simp only [C', coe_filter, Set.mem_ofPred_eq] at hx; exact hx.1)
    calc _ ≤ ∑ j ∈ C', 4 * (((rk A J j : ℕ) : ℝ) ^ 2)⁻¹ := by
          apply sum_le_sum; intro j hj
          simp only [C', mem_filter, not_lt] at hj
          rw [← div_eq_mul_inv]; exact second_class A hs J j hj.1 hj.2
      _ = ∑ i ∈ C'.image (rk A J), 4 * (((i : ℕ) : ℝ) ^ 2)⁻¹ := by rw [sum_image hinj']
      _ ≤ ∑ i ∈ Ioo 99 (J + 1), 4 * (((i : ℕ) : ℝ) ^ 2)⁻¹ := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro i hi
            obtain ⟨c, hc, rfl⟩ := mem_image.1 hi
            have hc1 := (mem_filter.1 hc).1
            have hc2 := (mem_filter.1 hc).2
            have hc3 := mem_Icc.1 (mem_filter.1 hc1).1
            have := rk_le A J c
            rw [mem_Ioo]; omega
          · intro _ _ _; positivity
      _ = 4 * ∑ i ∈ Ioo 99 (J + 1), (((i : ℕ) : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
      _ ≤ 4 * (2 / ((99 : ℕ) + 1)) := by
          apply mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le 99 (J + 1)) (by norm_num)
      _ = 8 / 100 := by norm_num
  linarith

lemma first_sum (A : Set ℕ) (J : ℕ) :
    ∑ j ∈ Icc 1 J \ C A J, β A j ≤ 2 := by
  calc _ ≤ ∑ j ∈ Icc 1 J \ C A J, (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum; intro j hj; rw [mem_sdiff] at hj; exact first_class A J j hj.1 hj.2
    _ ≤ ∑ j ∈ Ioo 0 (J + 1), (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj; rw [mem_sdiff, mem_Icc] at hj; rw [mem_Ioo]; omega
        · intro _ _ _; positivity
    _ ≤ 2 / ((0 : ℕ) + 1) := sum_Ioo_inv_sq_le 0 (J + 1)
    _ = 2 := by norm_num

lemma bound (A : Set ℕ) (hs : IsSubsetSumFree A) (J : ℕ) :
    ∑ a ∈ F A (2 ^ (J + 1)), (1 : ℝ) / a ≤ 3 / 2 + 2 + (99 + 8 / 100) := by
  rw [total]
  have hC : C A J ⊆ Icc 1 J := filter_subset _ _
  rw [← sum_sdiff hC]
  have := small A; have := first_sum A J; have := second_sum A hs J
  linarith

lemma finset_bound (A : Set ℕ) (hs : IsSubsetSumFree A) (u : Finset A) :
    ∑ a ∈ u, (1 : ℝ) / ((a : ℕ) : ℝ) ≤ 3 / 2 + 2 + (99 + 8 / 100) := by
  set J := ∑ a ∈ u, (a : ℕ)
  have hsub : u.map (Function.Embedding.subtype _) ⊆ F A (2 ^ (J + 1)) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hx
    rw [mem_F]
    have hpos := (hs a a.2).1
    have h1 : (a : ℕ) ≤ J := single_le_sum (f := fun a : A => (a : ℕ)) (fun _ _ => Nat.zero_le _) ha
    have h2 : J < 2 ^ J := Nat.lt_two_pow_self
    have h3 : 2 ^ J ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨hpos, by simp; omega, a.2⟩
  calc ∑ a ∈ u, (1 : ℝ) / ((a : ℕ) : ℝ) = ∑ x ∈ u.map (Function.Embedding.subtype _), (1 : ℝ) / x := by
        rw [sum_map]; rfl
    _ ≤ ∑ x ∈ F A (2 ^ (J + 1)), (1 : ℝ) / x :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := bound A hs J

end OMAE876

open OMAE876 in
theorem OMA.solution : type_of% @Erdos876.erdos_876.variants.recip_sum_lt := by
  intro A _ hs
  have hnn : (0 : A → ℝ) ≤ fun a : A ↦ (1 : ℝ) / (a : ℕ) := fun a => by positivity
  have hsum : Summable (fun a : A ↦ (1 : ℝ) / (a : ℕ)) :=
    summable_of_sum_le hnn (finset_bound A hs)
  refine ⟨∑' a : A, (1 : ℝ) / (a : ℕ), ?_, hsum.hasSum⟩
  have : ∑' a : A, (1 : ℝ) / (a : ℕ) ≤ 3 / 2 + 2 + (99 + 8 / 100) :=
    tsum_le_of_sum_le' (by norm_num) (finset_bound A hs)
  linarith

