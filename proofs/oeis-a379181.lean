import OMAStatements.S_oeis_a379181

/-!
# An exponential upper bound for words with integral mean digit

A decimal word with integral mean has mean at least five, or its digitwise
complement has mean at least five. Exponential weights with base 17/16
bound the number of either kind by (99/10)^n. This excludes a limiting
ratio of ten, independently of the uniqueness condition on the mode.
-/

namespace IntegralDigitMean

open OMA.S_oeis_a379181 Finset Filter

abbrev Word (n : ℕ) := Fin n → Fin 10

def side (n : ℕ) : Finset (Word n) :=
  univ.filter fun w => 5 * n ≤ ∑ i, (w i).val ∨ 5 * n ≤ ∑ i, (9 - (w i).val)

def decode {n : ℕ} (w : Word n) : ℕ :=
  Nat.ofDigits 10 (List.ofFn fun i => (w i).val).reverse

lemma decode_digitWord (k : ℕ) : Nat.ofDigits 10 (digitWord k).reverse = k := by
  by_cases hk : k = 0
  · simp [digitWord, hk]
  · simp [digitWord, hk, Nat.ofDigits_digits]

lemma digit_bound (k d : ℕ) (hd : d ∈ digitWord k) : d < 10 := by
  by_cases hk : k = 0
  · simp [digitWord, hk] at hd
    omega
  · exact Nat.digits_lt_base (by decide) (by simpa [digitWord, hk] using hd)

lemma represent {l : List ℕ} {n : ℕ} (hlen : l.length = n)
    (hd : ∀ d ∈ l, d < 10) :
    ∃ w : Word n, (List.ofFn fun i => (w i).val) = l := by
  subst n
  exact ⟨fun i => ⟨l.get i, hd _ (l.get_mem i)⟩, List.ofFn_get l⟩

lemma complement_sum {n : ℕ} (w : Word n) :
    (∑ i, (w i).val) + (∑ i, (9 - (w i).val)) = 9 * n := by
  rw [← sum_add_distrib]
  have hd (i : Fin n) : (w i).val + (9 - (w i).val) = 9 := by
    have := (w i).isLt
    omega
  simp [hd, Nat.mul_comm]

lemma count_le (n : ℕ) : term n ≤ (side n).card := by
  unfold term
  apply card_le_card_of_surjOn decode
  intro k hk
  obtain ⟨_, hlen, hq⟩ := mem_filter.mp hk
  obtain ⟨m, _, hm⟩ := List.any_eq_true.mp hq
  have heq : (digitWord k).sum = m * (digitWord k).length := by
    simpa using (Bool.and_eq_true_iff.mp hm).2
  obtain ⟨w, hw⟩ := represent hlen (digit_bound k)
  refine ⟨w, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
  · have hs : ∑ i, (w i).val = m * n := by
      rw [← Fin.sum_ofFn, hw, heq, hlen]
    by_cases hm5 : 5 ≤ m
    · left
      rw [hs]
      exact Nat.mul_le_mul_right n hm5
    · right
      have h4 := Nat.mul_le_mul_right n (show m ≤ 4 by omega)
      have := complement_sum w
      omega
  · simpa [decode, hw] using decode_digitWord k

noncomputable def weight (d : ℕ) : ℝ := (17 / 16 : ℝ) ^ d / (17 / 16 : ℝ) ^ 5

lemma weight_nonneg (d : ℕ) : 0 ≤ weight d := by
  unfold weight
  positivity

lemma heavy {n : ℕ} (d : Fin n → ℕ) (hd : 5 * n ≤ ∑ i, d i) :
    1 ≤ ∏ i, weight (d i) := by
  simp only [weight, prod_div_distrib, prod_const, card_univ, Fintype.card_fin,
    prod_pow_eq_pow_sum, ← pow_mul]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa using (pow_le_pow_right₀ (by norm_num : 1 ≤ (17 / 16 : ℝ)) hd)

lemma total_weights (n : ℕ) (f : Fin 10 → ℕ) :
    (∑ w : Word n, ∏ i, weight (f (w i))) = (∑ j : Fin 10, weight (f j)) ^ n := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) (j : Fin 10) => weight (f j))]
  simp

lemma weight_bounds :
    (∑ j : Fin 10, weight j.val) ≤ 99 / 10 ∧
    (∑ j : Fin 10, weight (9 - j.val)) ≤ 99 / 10 := by
  norm_num [weight, Fin.sum_univ_succ]

lemma exponential_bound (n : ℕ) : (term n : ℝ) ≤ 2 * (99 / 10 : ℝ) ^ n := by
  let cost (w : Word n) := (∏ i, weight (w i).val) + ∏ i, weight (9 - (w i).val)
  have hmajor (w : Word n) (hw : w ∈ side n) : 1 ≤ cost w := by
    have ha : 0 ≤ ∏ i, weight (w i).val := prod_nonneg fun i _ => weight_nonneg _
    have hb : 0 ≤ ∏ i, weight (9 - (w i).val) := prod_nonneg fun i _ => weight_nonneg _
    rcases (mem_filter.mp hw).2 with h | h
    · exact (heavy _ h).trans (le_add_of_nonneg_right hb)
    · exact (heavy _ h).trans (le_add_of_nonneg_left ha)
  calc
    (term n : ℝ) ≤ ((side n).card : ℝ) := by exact_mod_cast count_le n
    _ = ∑ _w ∈ side n, (1 : ℝ) := by simp
    _ ≤ ∑ w ∈ side n, cost w := sum_le_sum hmajor
    _ ≤ ∑ w, cost w := sum_le_univ_sum_of_nonneg fun w => add_nonneg
      (prod_nonneg fun i _ => weight_nonneg _) (prod_nonneg fun i _ => weight_nonneg _)
    _ = (∑ j : Fin 10, weight j.val) ^ n + (∑ j : Fin 10, weight (9 - j.val)) ^ n := by
      dsimp only [cost]
      rw [sum_add_distrib, total_weights n (fun j => j.val), total_weights n (fun j => 9 - j.val)]
    _ ≤ 2 * (99 / 10 : ℝ) ^ n := by
      rw [two_mul]
      exact add_le_add (pow_le_pow_left₀ (sum_nonneg fun _ _ => weight_nonneg _) weight_bounds.1 n)
        (pow_le_pow_left₀ (sum_nonneg fun _ _ => weight_nonneg _) weight_bounds.2 n)

lemma excludes_ratio (a : ℕ → ℕ) (ha : ∀ n, (a n : ℝ) ≤ 2 * (99 / 10 : ℝ) ^ n) :
    ¬ Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (nhds 10) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (lt_mem_nhds
    (show (199 / 20 : ℝ) < 10 by norm_num)))
  have hpos (n : ℕ) (hn : N ≤ n) : 0 < (a n : ℝ) := by
    by_contra! hz
    have hzero : (a n : ℝ) = 0 := le_antisymm hz (by positivity)
    have hr := hN n hn
    change 199 / 20 < (a (n + 1) : ℝ) / (a n : ℝ) at hr
    rw [hzero, div_zero] at hr
    norm_num at hr
  have lower (k : ℕ) : (199 / 20 : ℝ) ^ k * (a N : ℝ) ≤ (a (N + k) : ℝ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hr := hN (N + k) (by omega)
      have hnext := ((lt_div_iff₀ (hpos (N + k) (by omega))).mp hr).le
      calc
        _ = 199 / 20 * ((199 / 20 : ℝ) ^ k * (a N : ℝ)) := by rw [pow_succ]; ring
        _ ≤ 199 / 20 * (a (N + k) : ℝ) := by gcongr
        _ ≤ _ := hnext
  have hb (k : ℕ) : (a N : ℝ) ≤ (2 * (99 / 10 : ℝ) ^ N) * ((99 / 10) / (199 / 20) : ℝ) ^ k := by
    have hk := (lower k).trans (ha (N + k))
    rw [pow_add] at hk
    rw [div_pow (99 / 10 : ℝ) (199 / 20) k, ← mul_div_assoc]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hk
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ ((99 / 10) / (199 / 20) : ℝ) by norm_num)
    (show ((99 / 10) / (199 / 20) : ℝ) < 1 by norm_num)
  have hz := le_of_tendsto_of_tendsto tendsto_const_nhds
    (hlim.const_mul (2 * (99 / 10 : ℝ) ^ N)) (Eventually.of_forall hb)
  have hp := hpos N le_rfl
  exact (not_le_of_gt hp) (by simpa using hz)

end IntegralDigitMean

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a379181.main) := by
  exact IntegralDigitMean.excludes_ratio _ IntegralDigitMean.exponential_bound
