import FormalConjectures.Other.SuffixPrefixAvoidance

-- Problem: Suffix-prefix avoidance bound
-- Upstream: formal-conjectures FormalConjectures/Other/SuffixPrefixAvoidance.lean:76 (declaration SuffixPrefixAvoidance.suffix_prefix_avoidance_bound)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Proof outline (after D. Zakharov, arXiv:2602.20143, rearranged so that it formalises directly).

Words are handled as lists. For a set `A` of words of length `n` put
* `S A m`: the suffixes of length `m` of the words of `A`,
* `T A m`: the words of length `m` that are not in `S A m` but whose tail is in `S A (m - 1)`,
* `G A j`: the words of length `j` none of whose nonempty initial segments lies in some `S A i`.

If `(A, B)` is suffix-prefix avoiding then every word of `B` lies in `G A n`. Cutting a word of
`G A (j + 1)` just before its shortest final segment that is not a suffix of `A` gives the renewal
inequality `|G (j + 1)| ≤ ∑ i ≤ j, |G i| * |T (j + 1 - i)|`. Normalising by powers of `q`, with
`γ j = |G j| / q ^ j`, `a m = |S m| / q ^ m`, `d m = a m - a (m + 1) ≥ |T (m + 1)| / q ^ (m + 1)` and
`α = |A| / q ^ n`, we get `γ (j + 1) ≤ ∑ i ≤ j, γ i * d (j - i)` and `∑ m < n, d m = 1 - α`.

`key_bound` is the purely real-variable part: choose `ρ ≥ 1` with `∑ m < n, d m * ρ ^ (m + 1) = 1`
(intermediate value theorem), show by induction that the potential
`∑ i ≤ j, ρ ^ i * γ i * (1 - P (j - i))` never exceeds `1`, where `P k = ∑ m < k, d m * ρ ^ (m + 1)`,
and evaluate it at `j = n` to get `α * γ n * ρ ^ (n + 1) ≤ ρ - 1`. Finally
`(ρ - 1) * (e * n) ≤ ρ ^ (n + 1)` for all `ρ ≥ 1` (`exp_bound`).
-/

open SuffixPrefixAvoidance

namespace OMAAux

variable {n q : ℕ}

/-- All words of length `m`, as lists. -/
def W (q m : ℕ) : Finset (List (Fin q)) :=
  (Finset.univ : Finset (Fin m → Fin q)).image List.ofFn

lemma mem_W {m : ℕ} {l : List (Fin q)} : l ∈ W q m ↔ l.length = m := by
  unfold W
  constructor
  · intro h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp h
    simp
  · intro h
    subst h
    exact Finset.mem_image.mpr ⟨fun i => l.get i, Finset.mem_univ _, List.ofFn_get l⟩

/-- `S A m`: the suffixes of length `m` of the words of `A`. -/
def S (A : Finset (Fin n → Fin q)) (m : ℕ) : Finset (List (Fin q)) :=
  A.image (fun a => (List.ofFn a).drop (n - m))

/-- `G A j`: the words of length `j` none of whose nonempty initial segments is a suffix of a
word of `A`. -/
def G (A : Finset (Fin n → Fin q)) (j : ℕ) : Finset (List (Fin q)) :=
  (W q j).filter (fun w => ∀ i ∈ Finset.range j, w.take (i + 1) ∉ S A (i + 1))

/-- `T A m`: the words of length `m` that are not suffixes of words of `A`, but whose tail is. -/
def T (A : Finset (Fin n → Fin q)) (m : ℕ) : Finset (List (Fin q)) :=
  (W q m).filter (fun v => v.tail ∈ S A (m - 1) ∧ v ∉ S A m)

lemma mem_G {A : Finset (Fin n → Fin q)} {j : ℕ} {w : List (Fin q)} :
    w ∈ G A j ↔ w.length = j ∧ ∀ i, i < j → w.take (i + 1) ∉ S A (i + 1) := by
  unfold G
  rw [Finset.mem_filter, mem_W]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => h2 i (Finset.mem_range.mpr hi)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => h2 i (Finset.mem_range.mp hi)⟩

lemma S_length {A : Finset (Fin n → Fin q)} {m : ℕ} (hm : m ≤ n) {l : List (Fin q)}
    (hl : l ∈ S A m) : l.length = m := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hl
  simp
  omega

lemma S_zero {A : Finset (Fin n → Fin q)} (hA : A.Nonempty) : S A 0 = {[]} := by
  ext l
  simp only [S, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨a, -, rfl⟩
    simp
  · rintro rfl
    obtain ⟨a, ha⟩ := hA
    exact ⟨a, ha, by simp⟩

lemma S_tail {A : Finset (Fin n → Fin q)} {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ n)
    {l : List (Fin q)} (hl : l ∈ S A m) : l.tail ∈ S A (m - 1) := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
  refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
  rw [List.tail_drop]
  congr 1
  omega

lemma card_S_n (A : Finset (Fin n → Fin q)) : (S A n).card = A.card := by
  unfold S
  rw [Finset.card_image_of_injective]
  intro a b hab
  simp only [Nat.sub_self, List.drop_zero] at hab
  exact List.ofFn_injective hab

lemma card_T_add_card_S_le {A : Finset (Fin n → Fin q)} {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ n) :
    (T A m).card + (S A m).card ≤ q * (S A (m - 1)).card := by
  have hdisj : Disjoint (T A m) (S A m) :=
    Finset.disjoint_left.mpr (fun v hvT hvS => (Finset.mem_filter.mp hvT).2.2 hvS)
  rw [← Finset.card_union_of_disjoint hdisj]
  have hsub : T A m ∪ S A m ⊆
      ((Finset.univ : Finset (Fin q)) ×ˢ S A (m - 1)).image (fun p => p.1 :: p.2) := by
    intro v hv
    have hlen : v.length = m ∧ v.tail ∈ S A (m - 1) := by
      rcases Finset.mem_union.mp hv with h | h
      · exact ⟨mem_W.mp (Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2.1⟩
      · exact ⟨S_length hm h, S_tail hm1 hm h⟩
    obtain ⟨hl, ht⟩ := hlen
    cases v with
    | nil =>
      simp at hl
      omega
    | cons c t =>
      exact Finset.mem_image.mpr
        ⟨(c, t), Finset.mem_product.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩
  calc (T A m ∪ S A m).card
      ≤ (((Finset.univ : Finset (Fin q)) ×ˢ S A (m - 1)).image (fun p => p.1 :: p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin q)) ×ˢ S A (m - 1)).card := Finset.card_image_le
    _ = q * (S A (m - 1)).card := by
        rw [Finset.card_product]
        simp

lemma card_G_zero (A : Finset (Fin n → Fin q)) : (G A 0).card = 1 := by
  have h : G A 0 = {[]} := by
    ext w
    rw [mem_G, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, -⟩
      exact List.length_eq_zero_iff.mp h1
    · rintro rfl
      exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  rw [h, Finset.card_singleton]

lemma card_G_succ_le (A : Finset (Fin n → Fin q)) (j : ℕ) :
    (G A (j + 1)).card ≤ q * (G A j).card := by
  have hsub : G A (j + 1) ⊆
      ((G A j) ×ˢ (Finset.univ : Finset (Fin q))).image (fun p => p.1 ++ [p.2]) := by
    intro w hw
    obtain ⟨hl, hw'⟩ := mem_G.mp hw
    rcases List.eq_nil_or_concat w with rfl | ⟨u, c, hwe⟩
    · simp at hl
    · rw [List.concat_eq_append] at hwe
      subst hwe
      have hul : u.length = j := by
        simp at hl
        omega
      refine Finset.mem_image.mpr
        ⟨(u, c), Finset.mem_product.mpr ⟨mem_G.mpr ⟨hul, ?_⟩, Finset.mem_univ _⟩, rfl⟩
      intro i hi
      have h := hw' i (by omega)
      rwa [List.take_append_of_le_length (by omega)] at h
  calc (G A (j + 1)).card
      ≤ (((G A j) ×ˢ (Finset.univ : Finset (Fin q))).image (fun p => p.1 ++ [p.2])).card :=
        Finset.card_le_card hsub
    _ ≤ ((G A j) ×ˢ (Finset.univ : Finset (Fin q))).card := Finset.card_image_le
    _ = q * (G A j).card := by
        rw [Finset.card_product]
        simp [mul_comm]

lemma card_G_le_sum {A : Finset (Fin n → Fin q)} (hA : A.Nonempty) (j : ℕ) :
    (G A (j + 1)).card ≤
      ∑ i ∈ Finset.range (j + 1), (G A i).card * (T A (j + 1 - i)).card := by
  have hsub : G A (j + 1) ⊆ (Finset.range (j + 1)).biUnion
      (fun i => ((G A i) ×ˢ (T A (j + 1 - i))).image (fun p => p.1 ++ p.2)) := by
    intro w hw
    obtain ⟨hl, hw'⟩ := mem_G.mp hw
    have hex : ∃ m, 1 ≤ m ∧ w.drop (j + 1 - m) ∉ S A m := by
      refine ⟨j + 1, by omega, ?_⟩
      have h := hw' j (by omega)
      rw [List.take_of_length_le (by omega)] at h
      simpa using h
    classical
    have hm := Nat.find_spec hex
    have hmin : ∀ m', m' < Nat.find hex → ¬ (1 ≤ m' ∧ w.drop (j + 1 - m') ∉ S A m') :=
      fun m' h => Nat.find_min hex h
    have hmle : Nat.find hex ≤ j + 1 := by
      apply Nat.find_min' hex
      refine ⟨by omega, ?_⟩
      have h := hw' j (by omega)
      rw [List.take_of_length_le (by omega)] at h
      simpa using h
    generalize Nat.find hex = m at hm hmin hmle
    obtain ⟨hm1, hm2⟩ := hm
    refine Finset.mem_biUnion.mpr ⟨j + 1 - m, Finset.mem_range.mpr (by omega),
      Finset.mem_image.mpr ⟨(w.take (j + 1 - m), w.drop (j + 1 - m)),
        Finset.mem_product.mpr ⟨?_, ?_⟩, List.take_append_drop _ _⟩⟩
    · refine mem_G.mpr ⟨?_, fun i hi => ?_⟩
      · simp [hl]
      · have h := hw' i (by omega)
        rw [List.take_take]
        rwa [min_eq_left (by omega)]
    · have hidx : j + 1 - (j + 1 - m) = m := by omega
      show w.drop (j + 1 - m) ∈ T A (j + 1 - (j + 1 - m))
      rw [hidx]
      refine Finset.mem_filter.mpr ⟨mem_W.mpr ?_, ?_, hm2⟩
      · simp [hl]
        omega
      · rw [List.tail_drop]
        by_cases h1 : m = 1
        · subst h1
          rw [S_zero hA, Finset.mem_singleton]
          apply List.drop_eq_nil_of_le
          omega
        · have h2 := hmin (m - 1) (by omega)
          have h3 : w.drop (j + 1 - (m - 1)) ∈ S A (m - 1) := by
            by_contra hcon
            exact h2 ⟨by omega, hcon⟩
          have hidx2 : j + 1 - m + 1 = j + 1 - (m - 1) := by omega
          rw [hidx2]
          exact h3
  calc (G A (j + 1)).card
      ≤ ((Finset.range (j + 1)).biUnion
          (fun i => ((G A i) ×ˢ (T A (j + 1 - i))).image (fun p => p.1 ++ p.2))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (j + 1),
          (((G A i) ×ˢ (T A (j + 1 - i))).image (fun p => p.1 ++ p.2)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.range (j + 1), (G A i).card * (T A (j + 1 - i)).card := by
        apply Finset.sum_le_sum
        intro i _
        calc (((G A i) ×ˢ (T A (j + 1 - i))).image (fun p => p.1 ++ p.2)).card
            ≤ ((G A i) ×ˢ (T A (j + 1 - i))).card := Finset.card_image_le
          _ = (G A i).card * (T A (j + 1 - i)).card := Finset.card_product _ _

lemma ofFn_mem_G {A B : Finset (Fin n → Fin q)} (h : IsSuffixPrefixAvoiding A B)
    {b : Fin n → Fin q} (hb : b ∈ B) : List.ofFn b ∈ G A n := by
  refine mem_G.mpr ⟨List.length_ofFn, fun i hi hmem => ?_⟩
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hmem
  apply h a ha b hb ⟨i, hi⟩
  funext t
  have ht : (t : ℕ) < i + 1 := t.isLt
  have h1 := congrArg (fun l => l[(t : ℕ)]?) heq
  simp only [List.getElem?_drop, List.getElem?_take, List.getElem?_ofFn] at h1
  have hlt1 : n - (i + 1) + (t : ℕ) < n := by omega
  have hlt2 : (t : ℕ) < n := by omega
  rw [dif_pos hlt1, if_pos ht, dif_pos hlt2] at h1
  have h2 := Option.some.inj h1
  unfold wordSuffix wordPrefix
  convert h2 using 2
  apply Fin.ext
  show n - i - 1 + (t : ℕ) = n - (i + 1) + (t : ℕ)
  omega

/-- For `ρ ≥ 1`: `(ρ - 1) * (e * n) ≤ ρ ^ (n + 1)`. -/
lemma exp_bound {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℕ) :
    (ρ - 1) * (Real.exp 1 * n) ≤ ρ ^ (n + 1) := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : 1 - ρ⁻¹ ≤ Real.log ρ := Real.one_sub_inv_le_log_of_pos hρ0
  have h2 : ρ - 1 ≤ ρ * Real.log ρ := by
    have h3 : ρ * (1 - ρ⁻¹) ≤ ρ * Real.log ρ := mul_le_mul_of_nonneg_left h1 hρ0.le
    have h4 : ρ * (1 - ρ⁻¹) = ρ - 1 := by
      field_simp
    linarith
  have h5 : Real.exp 1 * ((n : ℝ) * Real.log ρ) ≤ ρ ^ n := by
    have h6 := Real.add_one_le_exp ((n : ℝ) * Real.log ρ - 1)
    have h7 : Real.exp ((n : ℝ) * Real.log ρ - 1) = ρ ^ n / Real.exp 1 := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hρ0]
    rw [h7] at h6
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    rw [le_div_iff₀ he] at h6
    linarith
  calc (ρ - 1) * (Real.exp 1 * n) ≤ (ρ * Real.log ρ) * (Real.exp 1 * n) := by
        apply mul_le_mul_of_nonneg_right h2
        positivity
    _ = ρ * (Real.exp 1 * ((n : ℝ) * Real.log ρ)) := by ring
    _ ≤ ρ * ρ ^ n := mul_le_mul_of_nonneg_left h5 hρ0.le
    _ = ρ ^ (n + 1) := by ring

/-- The real-variable core: a renewal inequality with total weight `1 - α` forces
`α * γ n ≤ 1 / (e * n)`. -/
lemma key_bound (n : ℕ) (hn : 0 < n) (α : ℝ) (γ d : ℕ → ℝ)
    (hγ0 : γ 0 = 1) (hγmono : ∀ j, γ (j + 1) ≤ γ j)
    (hd : ∀ m, m < n → 0 ≤ d m) (hsum : ∑ m ∈ Finset.range n, d m = 1 - α) (hα : 0 ≤ α)
    (hren : ∀ j, j < n → γ (j + 1) ≤ ∑ i ∈ Finset.range (j + 1), γ i * d (j - i)) :
    α * γ n ≤ 1 / (Real.exp 1 * n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hen : 0 < Real.exp 1 * n := by positivity
  have hanti : Antitone γ := antitone_nat_of_succ_le hγmono
  by_cases hex : ∃ m, m < n ∧ 0 < d m
  swap
  · have hd0 : ∀ m, m < n → d m = 0 := by
      intro m hm
      have h1 := hd m hm
      have h2 : ¬ 0 < d m := fun h => hex ⟨m, hm, h⟩
      linarith
    have h3 := hren (n - 1) (by omega)
    have h4 : n - 1 + 1 = n := by omega
    rw [h4] at h3
    have h5 : ∑ i ∈ Finset.range n, γ i * d (n - 1 - i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hd0 (n - 1 - i) (by omega), mul_zero]
    rw [h5] at h3
    have h6 : α * γ n ≤ 0 := by nlinarith
    exact h6.trans (by positivity)
  · obtain ⟨m₀, hm₀, hdm₀⟩ := hex
    have hFc : Continuous (fun x : ℝ => ∑ m ∈ Finset.range n, d m * x ^ (m + 1)) := by
      apply continuous_finsetSum
      intro m _
      exact continuous_const.mul (continuous_pow _)
    have hF1 : (fun x : ℝ => ∑ m ∈ Finset.range n, d m * x ^ (m + 1)) 1 ≤ 1 := by
      simp only [one_pow, mul_one]
      rw [hsum]
      linarith
    have hR1 : (1 : ℝ) ≤ 1 + 1 / d m₀ := by
      have : 0 ≤ 1 / d m₀ := by positivity
      linarith
    have hFR : 1 ≤ (fun x : ℝ => ∑ m ∈ Finset.range n, d m * x ^ (m + 1)) (1 + 1 / d m₀) := by
      have h1 : d m₀ * (1 + 1 / d m₀) ^ (m₀ + 1) ≤
          ∑ m ∈ Finset.range n, d m * (1 + 1 / d m₀) ^ (m + 1) := by
        apply Finset.single_le_sum (f := fun m => d m * (1 + 1 / d m₀) ^ (m + 1)) _
          (Finset.mem_range.mpr hm₀)
        intro m hm
        exact mul_nonneg (hd m (Finset.mem_range.mp hm)) (by positivity)
      have h2 : 1 + 1 / d m₀ ≤ (1 + 1 / d m₀) ^ (m₀ + 1) := le_self_pow₀ hR1 (by omega)
      have h3 : d m₀ * (1 + 1 / d m₀) = d m₀ + 1 := by
        field_simp
      have h4 : d m₀ * (1 + 1 / d m₀) ≤ d m₀ * (1 + 1 / d m₀) ^ (m₀ + 1) :=
        mul_le_mul_of_nonneg_left h2 hdm₀.le
      show 1 ≤ ∑ m ∈ Finset.range n, d m * (1 + 1 / d m₀) ^ (m + 1)
      linarith
    obtain ⟨ρ, ⟨hρ1, -⟩, hρ⟩ := intermediate_value_Icc hR1 hFc.continuousOn ⟨hF1, hFR⟩
    have hρ0 : 0 < ρ := by linarith
    obtain ⟨P, hP⟩ : ∃ P : ℕ → ℝ, ∀ k, P k = ∑ m ∈ Finset.range k, d m * ρ ^ (m + 1) :=
      ⟨_, fun _ => rfl⟩
    have hP0 : P 0 = 0 := by rw [hP]; simp
    have hPs : ∀ k, P (k + 1) = P k + d k * ρ ^ (k + 1) := by
      intro k
      rw [hP, hP, Finset.sum_range_succ]
    have hPn : P n = 1 := by rw [hP]; exact hρ
    have hPle : ∀ k, k ≤ n → P k ≤ 1 := by
      intro k hk
      rw [← hPn, hP, hP]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_subset_range.mpr hk
      · intro m hm _
        exact mul_nonneg (hd m (Finset.mem_range.mp hm)) (by positivity)
    have hΦ : ∀ j, j ≤ n →
        ∑ i ∈ Finset.range (j + 1), ρ ^ i * γ i * (1 - P (j - i)) ≤ 1 := by
      intro j
      induction j with
      | zero =>
        intro _
        simp [hP0, hγ0]
      | succ j ih =>
        intro hj
        have ih' := ih (by omega)
        have hr := hren j (by omega)
        rw [Finset.sum_range_succ]
        have h1 : ∑ i ∈ Finset.range (j + 1), ρ ^ i * γ i * (1 - P (j + 1 - i))
            = ∑ i ∈ Finset.range (j + 1), ρ ^ i * γ i * (1 - P (j - i))
              - ρ ^ (j + 1) * ∑ i ∈ Finset.range (j + 1), γ i * d (j - i) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i ≤ j := by
            have := Finset.mem_range.mp hi
            omega
          have h2 : j + 1 - i = (j - i) + 1 := by omega
          rw [h2, hPs]
          have h3 : ρ ^ (j + 1) = ρ ^ i * ρ ^ (j - i + 1) := by
            rw [← pow_add]
            congr 1
            omega
          rw [h3]
          ring
        rw [h1]
        have h4 : j + 1 - (j + 1) = 0 := by omega
        rw [h4, hP0]
        have hρpos : 0 < ρ ^ (j + 1) := by positivity
        have h5 := mul_le_mul_of_nonneg_left hr hρpos.le
        simp only [sub_zero, mul_one]
        linarith
    have hΦn := hΦ n le_rfl
    obtain ⟨H, hH⟩ : ∃ H : ℕ → ℝ, ∀ j,
        H j = ∑ i ∈ Finset.range (j + 1), ρ ^ i * (1 - P (j - i)) := ⟨_, fun _ => rfl⟩
    have hH0 : H 0 = 1 := by
      rw [hH]
      simp [hP0]
    have hHs : ∀ j, H (j + 1) = (1 - P (j + 1)) + ρ * H j := by
      intro j
      rw [hH, hH, Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, one_mul, Nat.sub_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have : j + 1 - (i + 1) = j - i := by omega
      rw [this]
      ring
    obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ j, D j = ∑ m ∈ Finset.range j, d m := ⟨_, fun _ => rfl⟩
    have hD0 : D 0 = 0 := by
      rw [hD]
      simp
    have hDs : ∀ j, D (j + 1) = D j + d j := by
      intro j
      rw [hD, hD, Finset.sum_range_succ]
    have hclosed : ∀ j, (ρ - 1) * H j = ρ ^ (j + 1) * (1 - D j) - (1 - P j) := by
      intro j
      induction j with
      | zero =>
        rw [hH0, hD0, hP0]
        ring
      | succ j ih =>
        rw [hHs, hDs, hPs]
        have e : (ρ - 1) * (1 - (P j + d j * ρ ^ (j + 1)) + ρ * H j)
            = (ρ - 1) * (1 - (P j + d j * ρ ^ (j + 1))) + ρ * ((ρ - 1) * H j) := by ring
        rw [e, ih]
        ring
    have hHn : (ρ - 1) * H n = α * ρ ^ (n + 1) := by
      rw [hclosed, hD, hsum, hPn]
      ring
    have hlow : γ n * H n ≤ 1 := by
      refine le_trans ?_ hΦn
      rw [hH, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := by
        have := Finset.mem_range.mp hi
        omega
      have hQ : 0 ≤ 1 - P (n - i) := by linarith [hPle (n - i) (by omega)]
      have hγi : γ n ≤ γ i := hanti hi'
      have hρi : 0 ≤ ρ ^ i := by positivity
      calc γ n * (ρ ^ i * (1 - P (n - i)))
          ≤ γ i * (ρ ^ i * (1 - P (n - i))) :=
            mul_le_mul_of_nonneg_right hγi (mul_nonneg hρi hQ)
        _ = ρ ^ i * γ i * (1 - P (n - i)) := by ring
    have hfin : α * γ n * ρ ^ (n + 1) ≤ ρ - 1 := by
      have e : α * γ n * ρ ^ (n + 1) = (ρ - 1) * (γ n * H n) := by
        linear_combination (-(γ n)) * hHn
      rw [e]
      calc (ρ - 1) * (γ n * H n) ≤ (ρ - 1) * 1 :=
            mul_le_mul_of_nonneg_left hlow (by linarith)
        _ = ρ - 1 := mul_one _
    have hexp := exp_bound hρ1 n
    rw [le_div_iff₀ hen]
    have hρpow : 0 < ρ ^ (n + 1) := by positivity
    have h8 : α * γ n * (Real.exp 1 * n) * ρ ^ (n + 1) ≤ 1 * ρ ^ (n + 1) := by
      calc α * γ n * (Real.exp 1 * n) * ρ ^ (n + 1)
          = (α * γ n * ρ ^ (n + 1)) * (Real.exp 1 * n) := by ring
        _ ≤ (ρ - 1) * (Real.exp 1 * n) := mul_le_mul_of_nonneg_right hfin hen.le
        _ ≤ ρ ^ (n + 1) := hexp
        _ = 1 * ρ ^ (n + 1) := (one_mul _).symm
    exact le_of_mul_le_mul_right h8 hρpow

/-- The normalised form of the theorem: `(|A| / q ^ n) * (|G A n| / q ^ n) ≤ 1 / (e * n)`. -/
lemma main_real {A : Finset (Fin n → Fin q)} (hq : 0 < q) (hn : 0 < n) (hA : A.Nonempty) :
    ((A.card : ℝ) / (q : ℝ) ^ n) * (((G A n).card : ℝ) / (q : ℝ) ^ n) ≤
      1 / (Real.exp 1 * n) := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hq0 : (q : ℝ) ≠ 0 := hq'.ne'
  have hqpow : ∀ m : ℕ, (0 : ℝ) < (q : ℝ) ^ m := fun m => pow_pos hq' m
  have hT : ∀ m, m < n → ((T A (m + 1)).card : ℝ) / (q : ℝ) ^ (m + 1) ≤
      ((S A m).card : ℝ) / (q : ℝ) ^ m - ((S A (m + 1)).card : ℝ) / (q : ℝ) ^ (m + 1) := by
    intro m hm
    have h1 := card_T_add_card_S_le (A := A) (m := m + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at h1
    have h2 : ((T A (m + 1)).card : ℝ) + ((S A (m + 1)).card : ℝ) ≤
        (q : ℝ) * ((S A m).card : ℝ) := by
      exact_mod_cast h1
    have h3 : ((S A m).card : ℝ) / (q : ℝ) ^ m =
        (q : ℝ) * ((S A m).card : ℝ) / (q : ℝ) ^ (m + 1) := by
      rw [pow_succ, mul_comm (q : ℝ) _, mul_div_mul_right _ _ hq0]
    rw [h3, ← sub_div]
    apply div_le_div_of_nonneg_right _ (hqpow _).le
    linarith
  apply key_bound n hn ((A.card : ℝ) / (q : ℝ) ^ n) (fun j => ((G A j).card : ℝ) / (q : ℝ) ^ j)
    (fun m => ((S A m).card : ℝ) / (q : ℝ) ^ m - ((S A (m + 1)).card : ℝ) / (q : ℝ) ^ (m + 1))
  · simp [card_G_zero]
  · intro j
    have h1 := card_G_succ_le A j
    have h2 : ((G A (j + 1)).card : ℝ) ≤ (q : ℝ) * ((G A j).card : ℝ) := by exact_mod_cast h1
    show ((G A (j + 1)).card : ℝ) / (q : ℝ) ^ (j + 1) ≤ ((G A j).card : ℝ) / (q : ℝ) ^ j
    rw [div_le_div_iff₀ (hqpow _) (hqpow _), pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right h2 (hqpow j).le]
  · intro m hm
    have h1 := hT m hm
    have h0 : (0 : ℝ) ≤ ((T A (m + 1)).card : ℝ) / (q : ℝ) ^ (m + 1) := by positivity
    show (0 : ℝ) ≤
      ((S A m).card : ℝ) / (q : ℝ) ^ m - ((S A (m + 1)).card : ℝ) / (q : ℝ) ^ (m + 1)
    linarith
  · have h1 := Finset.sum_range_sub' (fun m => ((S A m).card : ℝ) / (q : ℝ) ^ m) n
    refine h1.trans ?_
    simp [S_zero hA, card_S_n]
  · positivity
  · intro j hj
    have h1 := card_G_le_sum hA j
    have h2 : ((G A (j + 1)).card : ℝ) ≤
        ∑ i ∈ Finset.range (j + 1), ((G A i).card : ℝ) * ((T A (j + 1 - i)).card : ℝ) := by
      exact_mod_cast h1
    have h3 : ((G A (j + 1)).card : ℝ) / (q : ℝ) ^ (j + 1) ≤
        (∑ i ∈ Finset.range (j + 1), ((G A i).card : ℝ) * ((T A (j + 1 - i)).card : ℝ)) /
          (q : ℝ) ^ (j + 1) := div_le_div_of_nonneg_right h2 (hqpow _).le
    refine h3.trans ?_
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ j := by
      have := Finset.mem_range.mp hi
      omega
    have e1 : j + 1 - i = j - i + 1 := by omega
    have e2 : (q : ℝ) ^ (j + 1) = (q : ℝ) ^ i * (q : ℝ) ^ (j - i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have h4 := hT (j - i) (by omega)
    have h5 : ((G A i).card : ℝ) * ((T A (j + 1 - i)).card : ℝ) / (q : ℝ) ^ (j + 1) =
        ((G A i).card : ℝ) / (q : ℝ) ^ i *
          (((T A (j - i + 1)).card : ℝ) / (q : ℝ) ^ (j - i + 1)) := by
      rw [e1, e2, mul_div_mul_comm]
    rw [h5]
    apply mul_le_mul_of_nonneg_left h4
    positivity

end OMAAux

theorem OMA.solution : type_of% @SuffixPrefixAvoidance.suffix_prefix_avoidance_bound := by
  intro n q A B hq hn h
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  · have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hqn : (0 : ℝ) < (q : ℝ) ^ n := pow_pos hq' n
    have hB : B.card ≤ (OMAAux.G A n).card := by
      have hsub : B.image List.ofFn ⊆ OMAAux.G A n := by
        intro l hl
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
        exact OMAAux.ofFn_mem_G h hb
      calc B.card = (B.image List.ofFn).card :=
            (Finset.card_image_of_injective _ List.ofFn_injective).symm
        _ ≤ (OMAAux.G A n).card := Finset.card_le_card hsub
    have hB' : (B.card : ℝ) ≤ ((OMAAux.G A n).card : ℝ) := by exact_mod_cast hB
    have hmain := OMAAux.main_real (A := A) hq hn hA
    have h2 : (q : ℝ) ^ (2 * n) = (q : ℝ) ^ n * (q : ℝ) ^ n := by rw [two_mul, pow_add]
    rw [h2]
    calc (A.card : ℝ) * (B.card : ℝ) ≤ (A.card : ℝ) * ((OMAAux.G A n).card : ℝ) :=
          mul_le_mul_of_nonneg_left hB' (Nat.cast_nonneg _)
      _ = ((A.card : ℝ) / (q : ℝ) ^ n) * (((OMAAux.G A n).card : ℝ) / (q : ℝ) ^ n) *
            ((q : ℝ) ^ n * (q : ℝ) ^ n) := by
          field_simp
      _ ≤ 1 / (Real.exp 1 * n) * ((q : ℝ) ^ n * (q : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_right hmain (by positivity)
      _ = (q : ℝ) ^ n * (q : ℝ) ^ n / (Real.exp 1 * n) := by ring
