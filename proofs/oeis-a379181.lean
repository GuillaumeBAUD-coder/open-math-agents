import OMAStatements.S_oeis_a379181
import Mathlib

/-!
Disproof of the OEIS A379181 consecutive-term growth conjecture:
  Filter.Tendsto (fun n => (term (n + 1) : ℝ) / (term n : ℝ)) Filter.atTop (nhds 10).

For any qualifying n-digit integer (n >= 2), the digit mean equals its unique mode m in
{0, ..., 9}, so the sum of its n decimal digits is m * n, which is either <= 4n or >= 5n.
Because the uniform digit mean is 4.5, a Cramer/exponential-tilt Markov bound with t = 9/10
gives #{w in {0..9}^n : sum w <= 4n} <= (t^(-4) * sum_{d=0}^9 t^d)^n <= (993/100)^n, and the
digit-complement involution d -> 9 - d yields the same bound for sum w >= 5n. Hence
term n <= 2 * (993/100)^n for all n >= 2. If term(n + 1) / term(n) converged to 10, then
term(n) would eventually grow at rate at least 995/100 per step, contradicting the upper bound.
-/

namespace OMA.OeisA379181Disproof

open OMA.S_oeis_a379181 Filter Topology

private lemma qualifies_sum_le_or_ge {w : List ℕ} {n : ℕ}
    (hlen : w.length = n) (hq : qualifies w = true) :
    w.sum ≤ 4 * n ∨ 5 * n ≤ w.sum := by
  unfold qualifies at hq
  rw [List.any_eq_true] at hq
  rcases hq with ⟨m, hm_mem, hm_eq⟩
  rw [List.mem_range] at hm_mem
  simp only [Bool.and_eq_true, beq_iff_eq] at hm_eq
  have hsum : w.sum = m * n := by simpa [hlen] using hm_eq.2
  by_cases hm4 : m ≤ 4
  · left
    rw [hsum]
    exact Nat.mul_le_mul_right n hm4
  · right
    rw [hsum]
    exact Nat.mul_le_mul_right n (by omega)

private lemma digitWord_mem_lt_ten (k d : ℕ) (hd : d ∈ digitWord k) : d < 10 := by
  unfold digitWord at hd
  split_ifs at hd with hk
  · simp only [List.mem_singleton] at hd
    omega
  · rw [List.mem_reverse] at hd
    exact Nat.digits_lt_base (by norm_num) hd

private lemma digitWord_getD_lt_ten (k i : ℕ) : (digitWord k).getD i 0 < 10 := by
  by_cases hi : i < (digitWord k).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact digitWord_mem_lt_ten k _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    omega

private def toVec (n : ℕ) (k : ℕ) : Fin n → Fin 10 :=
  fun i => ⟨(digitWord k).getD i.val 0, digitWord_getD_lt_ten k i.val⟩

private lemma list_sum_eq_fin_sum : ∀ (l : List ℕ),
    ∑ i : Fin l.length, l.getD i.val 0 = l.sum
  | [] => by simp
  | a :: tl => by
    rw [List.length_cons, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ, List.sum_cons]
    congr 1
    exact list_sum_eq_fin_sum tl

private lemma sum_toVec {n k : ℕ} (hlen : (digitWord k).length = n) :
    ∑ i : Fin n, (toVec n k i).val = (digitWord k).sum := by
  subst hlen
  exact list_sum_eq_fin_sum (digitWord k)

private lemma toVec_inj {n k₁ k₂ : ℕ} (hn : 2 ≤ n)
    (h1 : (digitWord k₁).length = n) (h2 : (digitWord k₂).length = n)
    (heq : toVec n k₁ = toVec n k₂) : k₁ = k₂ := by
  have hw : digitWord k₁ = digitWord k₂ := by
    apply List.ext_getElem (h1.trans h2.symm)
    intro i hi1 hi2
    have hi : i < n := by omega
    have hfun := congrArg (fun f => (f ⟨i, hi⟩).val) heq
    simp only [toVec] at hfun
    rwa [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at hfun
  have hk1 : k₁ ≠ 0 := by
    intro h0
    subst h0
    simp [digitWord] at h1
    omega
  have hk2 : k₂ ≠ 0 := by
    intro h0
    subst h0
    simp [digitWord] at h2
    omega
  simp only [digitWord, if_neg hk1, if_neg hk2] at hw
  have hdig : Nat.digits 10 k₁ = Nat.digits 10 k₂ := List.reverse_injective hw
  have := congrArg (Nat.ofDigits 10) hdig
  rwa [Nat.ofDigits_digits, Nat.ofDigits_digits] at this

private def Low (n : ℕ) : Finset (Fin n → Fin 10) :=
  Finset.univ.filter fun w => ∑ i : Fin n, (w i).val ≤ 4 * n

private def High (n : ℕ) : Finset (Fin n → Fin 10) :=
  Finset.univ.filter fun w => 5 * n ≤ ∑ i : Fin n, (w i).val

private def flipVec {n : ℕ} (w : Fin n → Fin 10) : Fin n → Fin 10 :=
  fun i => ⟨9 - (w i).val, by omega⟩

private lemma flipVec_sum {n : ℕ} (w : Fin n → Fin 10) :
    ∑ i : Fin n, (flipVec w i).val + ∑ i : Fin n, (w i).val = 9 * n := by
  rw [← Finset.sum_add_distrib]
  have h9 : ∀ i : Fin n, (flipVec w i).val + (w i).val = 9 := by
    intro i
    simp only [flipVec]
    have hi : (w i).val < 10 := (w i).isLt
    omega
  simp [h9, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

private lemma flipVec_involutive {n : ℕ} (w : Fin n → Fin 10) :
    flipVec (flipVec w) = w := by
  ext i
  simp only [flipVec]
  have hi : (w i).val < 10 := (w i).isLt
  omega

private lemma card_high_eq_card_low (n : ℕ) : (High n).card = (Low n).card := by
  refine Finset.card_nbij flipVec ?_ ?_ ?_
  · intro w hw
    simp only [High, Low, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have hsum := flipVec_sum w
    omega
  · intro w₁ _ w₂ _ h
    have := congrArg flipVec h
    rwa [flipVec_involutive, flipVec_involutive] at this
  · intro w hw
    refine ⟨flipVec w, ?_, flipVec_involutive w⟩
    simp only [High, Low, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have hsum := flipVec_sum w
    omega

private lemma term_le_two_card_low {n : ℕ} (hn : 2 ≤ n) :
    term n ≤ 2 * (Low n).card := by
  set S : Finset ℕ := (Finset.range (10 ^ n)).filter fun k =>
    (digitWord k).length = n ∧ qualifies (digitWord k) = true
  change S.card ≤ 2 * (Low n).card
  have hinj : Set.InjOn (toVec n) S := by
    intro k₁ hk₁ k₂ hk₂ heq
    simp only [S, Finset.mem_coe, Finset.mem_filter] at hk₁ hk₂
    exact toVec_inj hn hk₁.2.1 hk₂.2.1 heq
  have hsub : S.image (toVec n) ⊆ Low n ∪ High n := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨k, hk, rfl⟩
    simp only [S, Finset.mem_filter] at hk
    have hle_or := qualifies_sum_le_or_ge hk.2.1 hk.2.2
    rw [← sum_toVec hk.2.1] at hle_or
    rcases hle_or with hlo | hhi
    · exact Finset.mem_union_left _ (by simp [Low, hlo])
    · exact Finset.mem_union_right _ (by simp [High, hhi])
  calc S.card = (S.image (toVec n)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Low n ∪ High n).card := Finset.card_le_card hsub
    _ ≤ (Low n).card + (High n).card := Finset.card_union_le _ _
    _ = 2 * (Low n).card := by rw [card_high_eq_card_low]; ring

private lemma sum_fin10_tilt_le :
    (∑ d : Fin 10, (9 / 10 : ℝ) ^ d.val) / (9 / 10 : ℝ) ^ 4 ≤ 993 / 100 := by
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero]
  norm_num

private lemma card_low_le_pow (n : ℕ) :
    ((Low n).card : ℝ) ≤ (993 / 100 : ℝ) ^ n := by
  set t : ℝ := 9 / 10
  have ht_pos : 0 < t := by positivity
  have ht_le1 : t ≤ 1 := by norm_num [t]
  have hterm : ∀ w ∈ Low n, t ^ (4 * n) ≤ ∏ i : Fin n, t ^ (w i).val := by
    intro w hw
    simp only [Low, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [Finset.prod_pow_eq_pow_sum]
    exact pow_le_pow_of_le_one ht_pos.le ht_le1 hw
  have hsum1 : ((Low n).card : ℝ) * t ^ (4 * n) ≤
      ∑ w ∈ Low n, ∏ i : Fin n, t ^ (w i).val := by
    calc ((Low n).card : ℝ) * t ^ (4 * n)
        = ∑ _w ∈ Low n, t ^ (4 * n) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ Low n, ∏ i : Fin n, t ^ (w i).val := Finset.sum_le_sum hterm
  have hsum2 : ∑ w ∈ Low n, ∏ i : Fin n, t ^ (w i).val ≤
      ∑ w : Fin n → Fin 10, ∏ i : Fin n, t ^ (w i).val := by
    refine Finset.sum_le_univ_sum_of_nonneg ?_
    intro w
    exact Finset.prod_nonneg fun i _ => pow_nonneg ht_pos.le _
  have hprod : ∑ w : Fin n → Fin 10, ∏ i : Fin n, t ^ (w i).val =
      (∑ d : Fin 10, t ^ d.val) ^ n := by
    rw [← Fintype.prod_sum (fun (_ : Fin n) (d : Fin 10) => t ^ d.val)]
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpow_pos : (0 : ℝ) < (t ^ 4) ^ n := by positivity
  have hmain : ((Low n).card : ℝ) * (t ^ 4) ^ n ≤ (∑ d : Fin 10, t ^ d.val) ^ n := by
    have h4 : t ^ (4 * n) = (t ^ 4) ^ n := by rw [pow_mul]
    rw [← h4, ← hprod]
    exact hsum1.trans hsum2
  calc ((Low n).card : ℝ)
      ≤ (∑ d : Fin 10, t ^ d.val) ^ n / (t ^ 4) ^ n := (le_div_iff₀ hpow_pos).mpr hmain
    _ = ((∑ d : Fin 10, t ^ d.val) / t ^ 4) ^ n := (div_pow _ _ n).symm
    _ ≤ (993 / 100 : ℝ) ^ n := by
      refine pow_le_pow_left₀ ?_ sum_fin10_tilt_le n
      exact div_nonneg (Finset.sum_nonneg fun d _ => pow_nonneg ht_pos.le _) (by positivity)

private lemma term_upper_bound {n : ℕ} (hn : 2 ≤ n) :
    (term n : ℝ) ≤ 2 * (993 / 100 : ℝ) ^ n := by
  have h1 : (term n : ℝ) ≤ (2 * (Low n).card : ℕ) := Nat.cast_le.mpr (term_le_two_card_low hn)
  push_cast at h1
  linarith [card_low_le_pow n]

theorem main_disproof :
    ¬ Filter.Tendsto (fun n : ℕ => (term (n + 1) : ℝ) / (term n : ℝ))
        Filter.atTop (nhds 10) := by
  intro hLim
  have hEv : ∀ᶠ n in Filter.atTop, (995 / 100 : ℝ) < (term (n + 1) : ℝ) / (term n : ℝ) :=
    hLim.eventually (Ioi_mem_nhds (by norm_num))
  rw [Filter.eventually_atTop] at hEv
  rcases hEv with ⟨N₀, hN₀⟩
  set N : ℕ := max N₀ 2
  have hN_ge_N0 : N₀ ≤ N := le_max_left _ _
  have hN_ge_2 : 2 ≤ N := le_max_right _ _
  have hstep : ∀ n, N ≤ n →
      0 < (term n : ℝ) ∧ (995 / 100 : ℝ) * (term n : ℝ) ≤ (term (n + 1) : ℝ) := by
    intro n hn
    have hgt : (995 / 100 : ℝ) < (term (n + 1) : ℝ) / (term n : ℝ) := hN₀ n (hN_ge_N0.trans hn)
    have hpos : 0 < (term n : ℝ) := by
      by_contra hle
      have h0 : (term n : ℝ) = 0 := le_antisymm (not_lt.mp hle) (Nat.cast_nonneg _)
      rw [h0, div_zero] at hgt
      linarith
    exact ⟨hpos, le_of_lt ((lt_div_iff₀ hpos).mp hgt)⟩
  have hposN : 0 < (term N : ℝ) := (hstep N le_rfl).1
  have hlower : ∀ k : ℕ, (995 / 100 : ℝ) ^ k * (term N : ℝ) ≤ (term (N + k) : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstepk := (hstep (N + k) (Nat.le_add_right N k)).2
      calc (995 / 100 : ℝ) ^ (k + 1) * (term N : ℝ)
          = (995 / 100 : ℝ) * ((995 / 100 : ℝ) ^ k * (term N : ℝ)) := by ring
        _ ≤ (995 / 100 : ℝ) * (term (N + k) : ℝ) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ (term (N + k + 1) : ℝ) := hstepk
  have hratio_bdd : ∀ k : ℕ,
      (995 / 993 : ℝ) ^ k ≤ 2 * (993 / 100 : ℝ) ^ N / (term N : ℝ) := by
    intro k
    have hlow := hlower k
    have hup := term_upper_bound (n := N + k) (by omega)
    have hcomb : (995 / 100 : ℝ) ^ k * (term N : ℝ) ≤ 2 * (993 / 100 : ℝ) ^ (N + k) :=
      hlow.trans hup
    rw [pow_add] at hcomb
    have hrw : (995 / 993 : ℝ) ^ k = (995 / 100 : ℝ) ^ k / (993 / 100 : ℝ) ^ k := by
      rw [← div_pow]
      congr 1
      norm_num
    rw [hrw]
    rw [div_le_div_iff₀ (by positivity) hposN]
    calc (995 / 100 : ℝ) ^ k * (term N : ℝ)
        ≤ 2 * ((993 / 100 : ℝ) ^ N * (993 / 100 : ℝ) ^ k) := hcomb
      _ = 2 * (993 / 100 : ℝ) ^ N * (993 / 100 : ℝ) ^ k := by ring
  have htend : Filter.Tendsto (fun k : ℕ => (995 / 993 : ℝ) ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hbig : ∀ᶠ k in Filter.atTop,
      2 * (993 / 100 : ℝ) ^ N / (term N : ℝ) < (995 / 993 : ℝ) ^ k :=
    htend.eventually_gt_atTop _
  rcases hbig.exists with ⟨k, hk⟩
  linarith [hratio_bdd k]

end OMA.OeisA379181Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a379181.main) :=
  OMA.OeisA379181Disproof.main_disproof
