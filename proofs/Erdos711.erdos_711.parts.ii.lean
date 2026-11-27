import FormalConjectures.ErdosProblems.«711»
import Mathlib

-- Problem: Erdős Problem 711 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/711.lean:67 (declaration Erdos711.erdos_711.parts.ii)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős Problem 711, part ii

Write `f(n, m)` for the least `L` such that the open interval `(m, m + L)` contains distinct
integers `a_1, ..., a_n` with `k ∣ a_k`. We prove `f(n, 4n) - f(n, n) → ∞`.

The proof has three steps.

* `halve`: a tuple for `n` in `(4n, 4n + L)` yields a tuple for `n` in `(n, 2n + (L + 1) / 2)`.
  The indices `j > n / 2` take the value `2j`, and an index `j ≤ n / 2` takes half of the value
  at index `2j`. This is the case `k = 2` of the lemma of van Doorn
  (W. van Doorn, *On the length of an interval that contains distinct multiples of the first
  `n` positive integers*, arXiv:2601.16972, Lemma 2), composed with halving the even indices.
  It gives `f(n, 4n) - f(n, n) ≥ f(n, n) - 2n - 1`.
* `scale`: a tuple for `n` in `(n, 3n + B)` restricts along the multiples of `d = n / n₀` to a
  tuple for `n₀` in `(n₀, 3n₀ + 1)`, as soon as `n ≥ n₀ (3n₀ + B)`. So `f(n, n) - 2n → ∞` follows
  from the single inequality `f(n₀, n₀) > 2n₀ + 1` for one value `n₀`.
* `cert`: for `n₀ = 12800` there is no tuple in `(n₀, 3n₀ + 1)`. This is a failure of the
  marriage condition: the 272 indices in `certK` have only 271 multiples in `(n₀, 3n₀]`,
  listed in `certN`. The kernel checks this.

This replaces the Erdős–Pomerance bounds on `f(n, n)` used by van Doorn with a finite
computation; it gives the qualitative statement only, not his bound `≫ n log n / log log n`.
-/

namespace OMA711

open Erdos711 Filter

/-- The tuple property is monotone in the interval length. -/
lemma hasTuple_mono {n m L L' : ℕ} (h : HasDivisibleDistinctTuple n m L) (hL : L ≤ L') :
    HasDivisibleDistinctTuple n m L' := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨a, ha, fun i => ⟨(hb i).1, lt_of_lt_of_le (hb i).2.1 (by omega), (hb i).2.2⟩⟩

/-- Some interval length always works. -/
lemma hasTuple_exists (n m : ℕ) : ∃ L, HasDivisibleDistinctTuple n m L := by
  refine ⟨(n + 1) * (m + 1) + 1, fun i => (i.val + 1) * (m + 1), ?_, ?_⟩
  · intro i j hij
    have h := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) hij
    exact Fin.ext (by omega)
  · intro i
    have h1 : 1 * (m + 1) ≤ (i.val + 1) * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (i.val + 1) * (m + 1) ≤ (n + 1) * (m + 1) :=
      Nat.mul_le_mul_right _ (by have := i.2; omega)
    refine ⟨?_, ?_, Dvd.intro _ rfl⟩
    · change m < (i.val + 1) * (m + 1)
      omega
    · change (i.val + 1) * (m + 1) < m + ((n + 1) * (m + 1) + 1)
      omega

/-- The minimal interval length exists. -/
lemma exists_minimal (n m : ℕ) : ∃ L, IsMinimalIntervalLength n m L := by
  classical
  have h := hasTuple_exists n m
  exact ⟨Nat.find h, Nat.find_spec h, fun L' hL' => Nat.find_min' h hL'⟩

/-- van Doorn's lemma for `k = 2`, combined with halving the even indices: a tuple in
`(4n, 4n + L)` gives a tuple in `(n, 2n + (L + 1) / 2)`. -/
lemma halve {n L : ℕ} (h : HasDivisibleDistinctTuple n (4 * n) L) :
    HasDivisibleDistinctTuple n n (n + (L + 1) / 2) := by
  obtain ⟨c, hc, hb⟩ := h
  have hidx : ∀ j : Fin n, 2 * (j.val + 1) ≤ n → 2 * (j.val + 1) - 1 < n := fun j h => by omega
  have key : ∀ (j : Fin n) (h2 : 2 * (j.val + 1) ≤ n),
      ∃ v, c ⟨2 * (j.val + 1) - 1, hidx j h2⟩ = 2 * v ∧ (j.val + 1) ∣ v ∧
        4 * n < 2 * v ∧ 2 * v < 4 * n + L := by
    intro j h2
    obtain ⟨hlo, hhi, hdvd⟩ := hb ⟨2 * (j.val + 1) - 1, hidx j h2⟩
    have he : 2 * (j.val + 1) - 1 + 1 = 2 * (j.val + 1) := by omega
    simp only [he] at hdvd
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨(j.val + 1) * t, ?_, Dvd.intro _ rfl, ?_, ?_⟩
    · rw [ht]; ring
    · have : 2 * ((j.val + 1) * t) = 2 * (j.val + 1) * t := by ring
      omega
    · have : 2 * ((j.val + 1) * t) = 2 * (j.val + 1) * t := by ring
      omega
  refine ⟨fun j => if h2 : 2 * (j.val + 1) ≤ n
      then c ⟨2 * (j.val + 1) - 1, hidx j h2⟩ / 2 else 2 * (j.val + 1), ?_, ?_⟩
  · intro j j' hjj
    simp only at hjj
    by_cases h2 : 2 * (j.val + 1) ≤ n <;> by_cases h2' : 2 * (j'.val + 1) ≤ n
    · rw [dif_pos h2, dif_pos h2'] at hjj
      obtain ⟨v, hv, -, -, -⟩ := key j h2
      obtain ⟨v', hv', -, -, -⟩ := key j' h2'
      have hcc : c ⟨2 * (j.val + 1) - 1, hidx j h2⟩ = c ⟨2 * (j'.val + 1) - 1, hidx j' h2'⟩ := by
        omega
      have h3 := Fin.mk.inj (hc hcc)
      exact Fin.ext (by omega)
    · rw [dif_pos h2, dif_neg h2'] at hjj
      obtain ⟨v, hv, -, hlo, -⟩ := key j h2
      have := j'.2
      omega
    · rw [dif_neg h2, dif_pos h2'] at hjj
      obtain ⟨v', hv', -, hlo, -⟩ := key j' h2'
      have := j.2
      omega
    · rw [dif_neg h2, dif_neg h2'] at hjj
      exact Fin.ext (by omega)
  · intro j
    by_cases h2 : 2 * (j.val + 1) ≤ n
    · simp only [dif_pos h2]
      obtain ⟨v, hv, hdv, hlo, hhi⟩ := key j h2
      have hv2 : c ⟨2 * (j.val + 1) - 1, hidx j h2⟩ / 2 = v := by omega
      rw [hv2]
      exact ⟨by omega, by omega, hdv⟩
    · simp only [dif_neg h2]
      obtain ⟨hlo, hhi, -⟩ := hb j
      have := j.2
      exact ⟨by omega, by omega, Dvd.intro_left _ rfl⟩

/-- Scaling: a tuple for `n` in `(n, 3n + B)` restricts, along the multiples of `d = n / n₀`,
to a tuple for `n₀` in `(n₀, 3n₀ + 1)`. -/
lemma scale {n₀ n B : ℕ} (hn₀ : 0 < n₀) (hn : n₀ * (3 * n₀ + B) ≤ n)
    (h : HasDivisibleDistinctTuple n n (2 * n + B)) :
    HasDivisibleDistinctTuple n₀ n₀ (2 * n₀ + 1) := by
  obtain ⟨a, ha, hb⟩ := h
  have hd1 : 3 * n₀ + B ≤ n / n₀ :=
    (Nat.le_div_iff_mul_le hn₀).2 (by rw [Nat.mul_comm]; exact hn)
  have hdn : n / n₀ * n₀ ≤ n := Nat.div_mul_le_self n n₀
  have hnd : n < n / n₀ * n₀ + n₀ := by
    have := Nat.lt_div_mul_add (a := n) hn₀
    omega
  generalize n / n₀ = d at hd1 hdn hnd
  have hdpos : 0 < d := by omega
  have hidx : ∀ j : Fin n₀, d * (j.val + 1) - 1 < n := by
    intro j
    have h1 : d * (j.val + 1) ≤ d * n₀ := Nat.mul_le_mul_left _ j.2
    have h2 : 0 < d * (j.val + 1) := Nat.mul_pos hdpos (Nat.succ_pos _)
    have h3 : d * n₀ = d * n₀ := rfl
    rw [Nat.mul_comm d n₀] at h1
    rw [Nat.mul_comm d n₀] at hdn
    omega
  have key : ∀ j : Fin n₀, ∃ u, a ⟨d * (j.val + 1) - 1, hidx j⟩ = d * u ∧ (j.val + 1) ∣ u ∧
      n₀ < u ∧ u < n₀ + (2 * n₀ + 1) := by
    intro j
    obtain ⟨hlo, hhi, hdvd⟩ := hb ⟨d * (j.val + 1) - 1, hidx j⟩
    have h2 : 0 < d * (j.val + 1) := Nat.mul_pos hdpos (Nat.succ_pos _)
    have he : d * (j.val + 1) - 1 + 1 = d * (j.val + 1) := by omega
    simp only [he] at hdvd
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨(j.val + 1) * t, by rw [ht]; ring, Dvd.intro _ rfl, ?_, ?_⟩
    · have h3 : d * n₀ < d * ((j.val + 1) * t) := by
        have : d * ((j.val + 1) * t) = d * (j.val + 1) * t := by ring
        omega
      exact Nat.lt_of_mul_lt_mul_left h3
    · have h3 : d * ((j.val + 1) * t) < d * (n₀ + (2 * n₀ + 1)) := by
        have h4 : d * ((j.val + 1) * t) = d * (j.val + 1) * t := by ring
        have h5 : d * (n₀ + (2 * n₀ + 1)) = 3 * (d * n₀) + d := by ring
        omega
      exact Nat.lt_of_mul_lt_mul_left h3
  refine ⟨fun j => a ⟨d * (j.val + 1) - 1, hidx j⟩ / d, ?_, ?_⟩
  · intro j j' hjj
    simp only at hjj
    obtain ⟨u, hu, -, -, -⟩ := key j
    obtain ⟨u', hu', -, -, -⟩ := key j'
    rw [hu, hu', Nat.mul_div_cancel_left _ hdpos, Nat.mul_div_cancel_left _ hdpos] at hjj
    have hcc : a ⟨d * (j.val + 1) - 1, hidx j⟩ = a ⟨d * (j'.val + 1) - 1, hidx j'⟩ := by
      rw [hu, hu', hjj]
    have h3 := Fin.mk.inj (ha hcc)
    have h4 : 0 < d * (j.val + 1) := Nat.mul_pos hdpos (Nat.succ_pos _)
    have h5 : 0 < d * (j'.val + 1) := Nat.mul_pos hdpos (Nat.succ_pos _)
    have h6 : d * (j.val + 1) = d * (j'.val + 1) := by omega
    have h7 := Nat.eq_of_mul_eq_mul_left hdpos h6
    exact Fin.ext (by omega)
  · intro j
    obtain ⟨u, hu, hdv, hlo, hhi⟩ := key j
    simp only [hu, Nat.mul_div_cancel_left _ hdpos]
    exact ⟨hlo, hhi, hdv⟩

/-- A Hall-violation certificate: a list `K` of indices all of whose multiples in `(n₀, 3n₀]`
lie in a shorter list `N`. -/
lemma no_tuple_of_cert (n₀ : ℕ) (K N : List ℕ) (hK : K.Nodup)
    (hc : ∀ i ∈ K, 1 ≤ i ∧ i ≤ n₀ ∧
      ∀ q ∈ List.range (3 * n₀ / i + 1), n₀ < i * q → i * q ∈ N)
    (hlen : N.length < K.length) : ¬ HasDivisibleDistinctTuple n₀ n₀ (2 * n₀ + 1) := by
  rintro ⟨a, ha, hb⟩
  have hgN : ∀ i ∈ K, ∀ hlt : i - 1 < n₀, a ⟨i - 1, hlt⟩ ∈ N := by
    intro i hi hlt
    obtain ⟨h1, h2, h3⟩ := hc i hi
    obtain ⟨hlo, hhi, hdvd⟩ := hb ⟨i - 1, hlt⟩
    have he : i - 1 + 1 = i := by omega
    simp only [he] at hdvd
    obtain ⟨q, hq⟩ := hdvd
    rw [hq]
    refine h3 q ?_ (by omega)
    rw [List.mem_range]
    refine Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by omega)).2 ?_)
    rw [Nat.mul_comm]
    omega
  have hinj : Set.InjOn (fun i : ℕ => if hlt : i - 1 < n₀ then a ⟨i - 1, hlt⟩ else 0)
      (K.toFinset : Set ℕ) := by
    intro i hi j hj hij
    have hi' := hc i (List.mem_toFinset.1 hi)
    have hj' := hc j (List.mem_toFinset.1 hj)
    have hlti : i - 1 < n₀ := by omega
    have hltj : j - 1 < n₀ := by omega
    simp only [dif_pos hlti, dif_pos hltj] at hij
    have h3 := Fin.mk.inj (ha hij)
    omega
  have hsub : K.toFinset.image (fun i : ℕ => if hlt : i - 1 < n₀ then a ⟨i - 1, hlt⟩ else 0)
      ⊆ N.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    have hi' := hc i (List.mem_toFinset.1 hi)
    have hlti : i - 1 < n₀ := by omega
    simp only [dif_pos hlti]
    exact List.mem_toFinset.2 (hgN i (List.mem_toFinset.1 hi) hlti)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup hK] at hcard
  have := List.toFinset_card_le N
  omega

/-- The main reduction: one certificate value `n₀` settles the problem. -/
theorem main_of_cert (n₀ : ℕ) (hn₀ : 0 < n₀)
    (hcert : ¬ HasDivisibleDistinctTuple n₀ n₀ (2 * n₀ + 1)) :
    ∀ B : ℕ, ∀ᶠ n in atTop, ∃ m Lm Ln : ℕ, IsMinimalIntervalLength n m Lm ∧
      IsMinimalIntervalLength n n Ln ∧ B ≤ Lm - Ln := by
  intro B
  filter_upwards [eventually_ge_atTop (n₀ * (3 * n₀ + (B + 1)))] with n hn
  obtain ⟨Lm, hLm⟩ := exists_minimal n (4 * n)
  obtain ⟨Ln, hLn⟩ := exists_minimal n n
  refine ⟨4 * n, Lm, Ln, hLm, hLn, ?_⟩
  have h1 : Ln ≤ n + (Lm + 1) / 2 := hLn.2 _ (halve hLm.1)
  have h2 : 2 * n + (B + 1) < Ln := by
    by_contra hcon
    exact hcert (scale hn₀ hn (hasTuple_mono hLn.1 (not_lt.1 hcon)))
  omega

/-- The indices of the Hall violator for `n₀ = 12800`. -/
def certK : List ℕ := [
  2268, 2304, 2352, 2430, 2520, 2560, 2592, 2640, 2646, 2673, 2688, 2700, 2744, 2772, 2800, 2835,
  2880, 2916, 2940, 2970, 3000, 3024, 3072, 3080, 3120, 3136, 3150, 3159, 3168, 3200, 3240, 3276,
  3300, 3360, 3375, 3402, 3456, 3500, 3510, 3520, 3528, 3564, 3600, 3640, 3645, 3696, 3744, 3750,
  3780, 3840, 3888, 3900, 3920, 3960, 3969, 4000, 4032, 4050, 4116, 4158, 4160, 4200, 4212, 4224,
  4312, 4320, 4356, 4368, 4400, 4410, 4455, 4480, 4500, 4536, 4608, 4620, 4680, 4704, 4725, 4752,
  4800, 4840, 4860, 4900, 4914, 4928, 4950, 4992, 5000, 5040, 5096, 5120, 5184, 5250, 5265, 5280,
  5292, 5346, 5376, 5400, 5460, 5488, 5544, 5600, 5616, 5625, 5632, 5670, 5760, 5808, 5824, 5832,
  5850, 5880, 5940, 6000, 6048, 6075, 6144, 6160, 6174, 6237, 6240, 6272, 6300, 6318, 6336, 6400,
  6468, 6480, 6534, 6552, 6600, 6615, 6720, 6750, 6804, 6860, 6912, 6930, 7000, 7020, 7040, 7056,
  7128, 7200, 7260, 7280, 7290, 7350, 7371, 7392, 7425, 7488, 7500, 7560, 7644, 7680, 7700, 7776,
  7800, 7840, 7875, 7920, 7938, 8000, 8019, 8064, 8100, 8190, 8232, 8250, 8316, 8320, 8400, 8424,
  8448, 8505, 8624, 8640, 8712, 8736, 8748, 8750, 8775, 8800, 8820, 8910, 8960, 9000, 9072, 9100,
  9216, 9240, 9261, 9360, 9375, 9408, 9450, 9477, 9504, 9600, 9604, 9680, 9702, 9720, 9750, 9800,
  9801, 9828, 9856, 9900, 9984, 10000, 10080, 10125, 10192, 10206, 10240, 10290, 10368, 10395,
  10400, 10500, 10530, 10560, 10584, 10692, 10752, 10780, 10800, 10890, 10920, 10935, 10976,
  11000, 11025, 11088, 11200, 11232, 11250, 11264, 11340, 11466, 11520, 11550, 11616, 11648,
  11664, 11700, 11760, 11880, 11907, 12000, 12096, 12100, 12150, 12250, 12285, 12288, 12320,
  12348, 12375, 12474, 12480, 12500, 12544, 12600, 12636, 12672, 12740, 12800]

/-- The multiples in `(12800, 38400]` of the indices in `certK`. -/
def certN : List ℕ := [
  12936, 12960, 13068, 13104, 13200, 13230, 13365, 13440, 13500, 13608, 13720, 13824, 13860,
  14000, 14040, 14080, 14112, 14175, 14256, 14400, 14520, 14560, 14580, 14700, 14742, 14784,
  14850, 14976, 15000, 15120, 15288, 15360, 15400, 15552, 15600, 15680, 15750, 15795, 15840,
  15876, 16000, 16038, 16128, 16200, 16380, 16464, 16500, 16632, 16640, 16800, 16848, 16875,
  16896, 17010, 17248, 17280, 17424, 17472, 17496, 17500, 17550, 17600, 17640, 17820, 17920,
  18000, 18144, 18200, 18225, 18432, 18480, 18522, 18711, 18720, 18750, 18816, 18900, 18954,
  19008, 19200, 19208, 19360, 19404, 19440, 19500, 19600, 19602, 19656, 19712, 19800, 19845,
  19968, 20000, 20160, 20250, 20384, 20412, 20480, 20580, 20736, 20790, 20800, 21000, 21060,
  21120, 21168, 21384, 21504, 21560, 21600, 21780, 21840, 21870, 21952, 22000, 22050, 22113,
  22176, 22275, 22400, 22464, 22500, 22528, 22680, 22932, 23040, 23100, 23232, 23296, 23328,
  23400, 23520, 23625, 23760, 23814, 24000, 24057, 24192, 24200, 24300, 24500, 24570, 24576,
  24640, 24696, 24750, 24948, 24960, 25000, 25088, 25200, 25272, 25344, 25480, 25515, 25600,
  25872, 25920, 26136, 26208, 26244, 26250, 26325, 26400, 26460, 26730, 26880, 27000, 27216,
  27300, 27440, 27648, 27720, 27783, 28000, 28080, 28125, 28160, 28224, 28350, 28431, 28512,
  28800, 28812, 29040, 29106, 29120, 29160, 29250, 29400, 29403, 29484, 29568, 29700, 29952,
  30000, 30184, 30240, 30375, 30492, 30576, 30618, 30720, 30800, 30870, 31104, 31185, 31200,
  31360, 31500, 31590, 31680, 31752, 32000, 32076, 32256, 32340, 32400, 32670, 32760, 32805,
  32928, 33000, 33075, 33264, 33280, 33600, 33696, 33750, 33792, 33880, 34020, 34300, 34320,
  34398, 34496, 34560, 34650, 34749, 34848, 34944, 34992, 35000, 35100, 35200, 35280, 35640,
  35672, 35721, 35840, 36000, 36036, 36288, 36300, 36400, 36450, 36750, 36855, 36864, 36960,
  37044, 37125, 37422, 37440, 37500, 37632, 37800, 37908, 38016, 38220, 38400]

lemma certK_nodup : certK.Nodup := by decide +kernel

lemma cert_len : certN.length < certK.length := by decide +kernel

lemma cert_check : ∀ i ∈ certK, 1 ≤ i ∧ i ≤ 12800 ∧
    ∀ q ∈ List.range (3 * 12800 / i + 1), 12800 < i * q → i * q ∈ certN := by
  decide +kernel

lemma cert : ¬ HasDivisibleDistinctTuple 12800 12800 (2 * 12800 + 1) :=
  no_tuple_of_cert 12800 certK certN certK_nodup cert_check cert_len

end OMA711

theorem OMA.solution : type_of% @Erdos711.erdos_711.parts.ii := by
  exact OMA711.main_of_cert 12800 (by norm_num) OMA711.cert
