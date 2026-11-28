import OMAStatements.S_mo_472052
import Mathlib

namespace OMA.S_mo_472052_Proof

open OMA.S_mo_472052 Filter Topology

/-! ### Part 1: General properties of `continuations` and `count` -/

private lemma continuations_pos (s t n : ℕ) (h : ℕ → Bool) :
    0 < continuations s t n h := by
  induction n generalizing h with
  | zero => simp [continuations]
  | succ n ih =>
    unfold continuations
    have := ih (push true h)
    omega

private lemma continuations_le_two_pow (s t n : ℕ) (h : ℕ → Bool) :
    continuations s t n h ≤ 2 ^ n := by
  induction n generalizing h with
  | zero => simp [continuations]
  | succ n ih =>
    unfold continuations
    have h1 := ih (push true h)
    have h2 := ih (push false h)
    rw [pow_succ']
    split_ifs <;> omega

private lemma continuations_congr {s t : ℕ} (hs : 0 < s) (n : ℕ) (h₁ h₂ : ℕ → Bool)
    (hagree : ∀ i < max t s + s, h₁ i = h₂ i) :
    continuations s t n h₁ = continuations s t n h₂ := by
  induction n generalizing h₁ h₂ with
  | zero => rfl
  | succ n ih =>
    have ha : allowZero s t h₁ = allowZero s t h₂ := by
      unfold allowZero
      have h1 : t + s - 1 < max t s + s := by omega
      have h2 : s + s - 1 < max t s + s := by omega
      have h3 : s - 1 < max t s + s := by omega
      rw [hagree _ h1, hagree _ h2, hagree _ h3]
    have hpush : ∀ b : Bool, ∀ i < max t s + s, push b h₁ i = push b h₂ i := by
      intro b i hi
      cases i with
      | zero => rfl
      | succ i => exact hagree i (by omega)
    unfold continuations
    rw [ha, ih _ _ (hpush true), ih _ _ (hpush false)]

private lemma continuations_le_of_ones_after {s t : ℕ} (hs : 0 < s) (n k : ℕ)
    (h₁ h₂ : ℕ → Bool) (hagree : ∀ i < k, h₁ i = h₂ i) (hones : ∀ i, k ≤ i → h₂ i = true) :
    continuations s t n h₁ ≤ continuations s t n h₂ := by
  induction n generalizing k h₁ h₂ with
  | zero => exact le_refl 1
  | succ n ih =>
    have hpush_agree : ∀ b : Bool, ∀ i < k + 1, push b h₁ i = push b h₂ i := by
      intro b i hi
      cases i with
      | zero => rfl
      | succ i => exact hagree i (by omega)
    have hpush_ones : ∀ b : Bool, ∀ i, k + 1 ≤ i → push b h₂ i = true := by
      intro b i hi
      cases i with
      | zero => omega
      | succ i => exact hones i (by omega)
    have hallow : allowZero s t h₁ = true → allowZero s t h₂ = true := by
      intro ha1
      unfold allowZero at ha1 ⊢
      by_cases hts : k ≤ t + s - 1
      · rw [hones _ hts]; simp
      · by_cases hss : k ≤ s + s - 1
        · rw [hones _ hss]; simp
        · have h1 : t + s - 1 < k := by omega
          have h2 : s + s - 1 < k := by omega
          have h3 : s - 1 < k := by omega
          rw [← hagree _ h1, ← hagree _ h2, ← hagree _ h3]
          exact ha1
    unfold continuations
    have htrue := ih (k + 1) _ _ (hpush_agree true) (hpush_ones true)
    have hfalse := ih (k + 1) _ _ (hpush_agree false) (hpush_ones false)
    by_cases ha1 : allowZero s t h₁ = true
    · rw [if_pos ha1, if_pos (hallow ha1)]
      omega
    · rw [if_neg ha1]
      split_ifs <;> omega

private lemma continuations_le_count {s t : ℕ} (hs : 0 < s) (n : ℕ) (h : ℕ → Bool) :
    continuations s t n h ≤ count s t n :=
  continuations_le_of_ones_after hs n 0 h (fun _ => true) (by omega) (fun _ _ => rfl)

private lemma continuations_submul {s t : ℕ} (hs : 0 < s) (m n : ℕ) (h : ℕ → Bool) :
    continuations s t (m + n) h ≤ continuations s t m h * count s t n := by
  induction m generalizing h with
  | zero =>
    simpa [continuations] using continuations_le_count hs n h
  | succ m ih =>
    have hEq : m + 1 + n = (m + n) + 1 := by omega
    rw [hEq]
    unfold continuations
    have h1 := ih (push true h)
    have h2 := ih (push false h)
    split_ifs <;> nlinarith

private lemma count_submul {s t : ℕ} (hs : 0 < s) (m n : ℕ) :
    count s t (m + n) ≤ count s t m * count s t n :=
  continuations_submul hs m n (fun _ => true)

private lemma continuations_ge_pushOnes (s t L n : ℕ) (h : ℕ → Bool) :
    continuations s t n ((push true)^[L] h) ≤ continuations s t (L + n) h := by
  induction L generalizing h with
  | zero => simp
  | succ L ih =>
    rw [Function.iterate_succ_apply, show L + 1 + n = (L + n) + 1 by omega]
    conv_rhs => unfold continuations
    have h1 := ih (push true h)
    omega

private lemma pushOnes_true (L : ℕ) (h : ℕ → Bool) (i : ℕ) (hi : i < L) :
    ((push true)^[L] h) i = true := by
  induction L generalizing i h with
  | zero => omega
  | succ L ih =>
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => rfl
    | succ i => exact ih h i (by omega)

private lemma continuations_supermul {s t : ℕ} (hs : 0 < s) (m n : ℕ) (h : ℕ → Bool) :
    continuations s t m h * count s t n ≤ continuations s t (m + (max t s + s + n)) h := by
  induction m generalizing h with
  | zero =>
    simp only [continuations, one_mul, zero_add]
    have hcongr : continuations s t n ((push true)^[max t s + s] h) = count s t n :=
      continuations_congr hs n _ _ (fun i hi => pushOnes_true _ h i hi)
    rw [← hcongr]
    exact continuations_ge_pushOnes s t (max t s + s) n h
  | succ m ih =>
    have hEq : m + 1 + (max t s + s + n) = (m + (max t s + s + n)) + 1 := by omega
    rw [hEq]
    unfold continuations
    have h1 := ih (push true h)
    have h2 := ih (push false h)
    split_ifs <;> nlinarith

private lemma count_supermul {s t : ℕ} (hs : 0 < s) (m n : ℕ) :
    count s t m * count s t n ≤ count s t (m + (max t s + s + n)) :=
  continuations_supermul hs m n (fun _ => true)

private lemma count_mono (s t : ℕ) : Monotone (count s t) := by
  refine monotone_nat_of_le_succ fun n => ?_
  suffices ∀ m h, continuations s t m h ≤ continuations s t (m + 1) h from this n (fun _ => true)
  intro m
  induction m with
  | zero => intro h; simp only [continuations]; split_ifs <;> omega
  | succ m ih =>
    intro h
    unfold continuations
    have h1 := ih (push true h)
    have h2 := ih (push false h)
    split_ifs <;> omega

/-! ### Part 2: Lower bound `(7/4)^n ≤ count s t n` via 3-state product weight -/

private def wt : Bool → Bool → ℝ
  | _, false => 21
  | false, true => 16
  | true, true => 28

private lemma wt_le_28 (a b : Bool) : wt a b ≤ 28 := by
  cases a <;> cases b <;> norm_num [wt]

private lemma wt_nonneg (a b : Bool) : 0 ≤ wt a b := by
  cases a <;> cases b <;> norm_num [wt]

private def W (s : ℕ) (h : ℕ → Bool) : ℝ :=
  ∏ r ∈ Finset.range s, wt (h (r + s)) (h r)

private lemma W_nonneg (s : ℕ) (h : ℕ → Bool) : 0 ≤ W s h :=
  Finset.prod_nonneg fun _ _ => wt_nonneg _ _

private lemma W_le (s : ℕ) (h : ℕ → Bool) : W s h ≤ (28 : ℝ) ^ s := by
  unfold W
  calc ∏ r ∈ Finset.range s, wt (h (r + s)) (h r)
      ≤ ∏ _r ∈ Finset.range s, (28 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => wt_nonneg _ _) (fun _ _ => wt_le_28 _ _)
    _ = (28 : ℝ) ^ s := by simp

private lemma W_push {s : ℕ} (hs : 0 < s) (b : Bool) (h : ℕ → Bool) :
    W s (push b h) = wt (h (s - 1)) b * ∏ r ∈ Finset.range (s - 1), wt (h (r + s)) (h r) := by
  unfold W
  have hsplit : Finset.range s = insert 0 ((Finset.range (s - 1)).image Nat.succ) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro hx
      cases x with
      | zero => left; rfl
      | succ x => right; exact ⟨x, by omega, rfl⟩
    · rintro (rfl | ⟨x, hx, rfl⟩) <;> omega
  have hnot : (0 : ℕ) ∉ (Finset.range (s - 1)).image Nat.succ := by simp
  rw [hsplit, Finset.prod_insert hnot, Finset.prod_image (fun _ _ _ _ h => Nat.succ.inj h)]
  congr 1
  · have h0 : 0 + s = (s - 1) + 1 := by omega
    rw [h0]
    rfl
  · refine Finset.prod_congr rfl fun r _ => ?_
    have h1 : r + 1 + s = (r + s) + 1 := by omega
    rw [h1]
    rfl

private lemma W_split_last {s : ℕ} (hs : 0 < s) (h : ℕ → Bool) :
    W s h = wt (h (s + s - 1)) (h (s - 1)) * ∏ r ∈ Finset.range (s - 1), wt (h (r + s)) (h r) := by
  unfold W
  have hs_eq : s = (s - 1) + 1 := by omega
  conv_lhs => arg 1; rw [hs_eq]
  rw [Finset.prod_range_succ, mul_comm]
  congr 1
  have hidx : s - 1 + s = s + s - 1 := by omega
  rw [hidx]

private lemma continuations_ge_W {s t : ℕ} (hs : 0 < s) (n : ℕ) (h : ℕ → Bool) :
    (7 / 4 : ℝ) ^ n * (W s h / (28 : ℝ) ^ s) ≤ (continuations s t n h : ℝ) := by
  induction n generalizing h with
  | zero =>
    simp only [pow_zero, one_mul, continuations, Nat.cast_one]
    rw [div_le_one (by positivity : (0 : ℝ) < (28 : ℝ) ^ s)]
    exact W_le s h
  | succ n ih =>
    unfold continuations
    have h1 := ih (push true h)
    have h2 := ih (push false h)
    have hP_nn : 0 ≤ ∏ r ∈ Finset.range (s - 1), wt (h (r + s)) (h r) :=
      Finset.prod_nonneg fun _ _ => wt_nonneg _ _
    have hstep_W : (7 / 4 : ℝ) * W s h ≤
        W s (push true h) + (if allowZero s t h = true then W s (push false h) else 0) := by
      rw [W_split_last hs h, W_push hs true h, W_push hs false h]
      cases h_s1 : h (s - 1) <;> cases h_s2 : h (s + s - 1)
      · have ha : allowZero s t h = true := by unfold allowZero; rw [h_s1]; simp
        rw [if_pos ha]
        simp only [wt] at hP_nn ⊢; nlinarith
      · have ha : allowZero s t h = true := by unfold allowZero; rw [h_s1]; simp
        rw [if_pos ha]
        simp only [wt] at hP_nn ⊢; nlinarith
      · split_ifs
        · simp only [wt] at hP_nn ⊢; nlinarith
        · simp only [wt] at hP_nn ⊢; nlinarith
      · have ha : allowZero s t h = true := by unfold allowZero; rw [h_s2]; simp
        rw [if_pos ha]
        simp only [wt] at hP_nn ⊢; nlinarith
    have hpow_nn : (0 : ℝ) ≤ (7 / 4 : ℝ) ^ n := by positivity
    have h28_pos : (0 : ℝ) < (28 : ℝ) ^ s := by positivity
    by_cases ha : allowZero s t h = true
    · rw [if_pos ha] at hstep_W ⊢
      push_cast
      have hdiv : (7 / 4 : ℝ) * (W s h / (28 : ℝ) ^ s) ≤
          W s (push true h) / (28 : ℝ) ^ s + W s (push false h) / (28 : ℝ) ^ s := by
        rw [← add_div, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right hstep_W (le_of_lt h28_pos)
      rw [pow_succ']
      nlinarith
    · rw [if_neg ha] at hstep_W ⊢
      simp only [add_zero] at hstep_W ⊢
      have hdiv : (7 / 4 : ℝ) * (W s h / (28 : ℝ) ^ s) ≤
          W s (push true h) / (28 : ℝ) ^ s := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right hstep_W (le_of_lt h28_pos)
      rw [pow_succ']
      nlinarith

private lemma seven_fourths_pow_le_count {s t : ℕ} (hs : 0 < s) (n : ℕ) :
    (7 / 4 : ℝ) ^ n ≤ (count s t n : ℝ) := by
  have h := continuations_ge_W (t := t) hs n (fun _ => true)
  have hW : W s (fun _ => true) = (28 : ℝ) ^ s := by
    unfold W
    simp [wt]
  rw [hW, div_self (by positivity : (28 : ℝ) ^ s ≠ 0), mul_one] at h
  exact h

/-! ### Part 3: Strict upper bound `count s t (L + 1) < 2 ^ (L + 1)` -/

private def pushList (bs : List Bool) (h : ℕ → Bool) : ℕ → Bool :=
  bs.foldl (fun acc b => push b acc) h

private def ValidPath (s t : ℕ) : List Bool → (ℕ → Bool) → Prop
  | [], _ => True
  | b :: bs, h => (b = false → allowZero s t h = true) ∧ ValidPath s t bs (push b h)

private lemma continuations_lt_two_pow_of_path {s t : ℕ} :
    ∀ (bs : List Bool) (h : ℕ → Bool), ValidPath s t bs h →
      allowZero s t (pushList bs h) = false →
      continuations s t (bs.length + 1) h < 2 ^ (bs.length + 1) := by
  intro bs
  induction bs with
  | nil =>
    intro h _ hfa
    simp only [List.length_nil, zero_add, pow_one, pushList, List.foldl_nil] at hfa ⊢
    unfold continuations
    rw [if_neg (by rw [hfa]; decide)]
    simp [continuations]
  | cons b bs ih =>
    intro h ⟨hb, hvp⟩ hfa
    have hlt := ih (push b h) hvp hfa
    simp only [List.length_cons, Nat.succ_add]
    unfold continuations
    cases b
    · have ha : allowZero s t h = true := hb rfl
      rw [if_pos ha]
      have h1 := continuations_le_two_pow s t (bs.length + 1) (push true h)
      rw [pow_succ']
      omega
    · have h2 := continuations_le_two_pow s t (bs.length + 1) (push false h)
      rw [pow_succ']
      split_ifs <;> omega

private lemma pushList_get {bs : List Bool} {h : ℕ → Bool} {i : ℕ} :
    pushList bs h i =
      if hlt : i < bs.length then bs.reverse.get ⟨i, by simpa using hlt⟩
      else h (i - bs.length) := by
  induction bs generalizing h i with
  | nil => simp [pushList]
  | cons b bs ih =>
    have hstep : pushList (b :: bs) h i = pushList bs (push b h) i := rfl
    rw [hstep, ih]
    by_cases hlt : i < bs.length
    · have hlt2 : i < (b :: bs).length := by simp; omega
      rw [dif_pos hlt, dif_pos hlt2]
      simp only [List.get_eq_getElem, List.reverse_cons]
      rw [List.getElem_append_left (by simpa using hlt)]
    · by_cases heq : i = bs.length
      · subst heq
        have hlt2 : bs.length < (b :: bs).length := by simp
        rw [dif_neg (by omega), dif_pos hlt2, Nat.sub_self]
        simp only [push, List.get_eq_getElem, List.reverse_cons]
        rw [List.getElem_append_right (by simp)]
        simp
      · have hlt2 : ¬ i < (b :: bs).length := by simp; omega
        rw [dif_neg hlt, dif_neg hlt2]
        have hsub : i - bs.length = (i - (b :: bs).length) + 1 := by simp; omega
        rw [hsub]
        rfl

private lemma count_lt_two_pow {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    count s t (max t s + s + 1) < 2 ^ (max t s + s + 1) := by
  let L := max t s + s
  let idx1 := L - (t + s)
  let idx2 := L - (s + s)
  let bit : ℕ → Bool := fun j => decide (j ≠ idx1 ∧ j ≠ idx2)
  let bs : List Bool := (List.range L).map bit
  have hbs_len : bs.length = L := by simp [bs]
  -- Helper: prefix `bs.take k` pushed onto `fun _ => true` has value at index `i`
  have hprefix_val : ∀ (k i : ℕ), k ≤ L →
      pushList (bs.take k) (fun _ => true) i =
        if i < k then bit (k - 1 - i) else true := by
    intro k i hk
    rw [pushList_get]
    have hlen : (bs.take k).length = k := by simp [bs, Nat.min_eq_left hk]
    split_ifs with h1 h2
    · rw [List.get_eq_getElem, List.getElem_reverse]
      have hidx_lt : (bs.take k).length - 1 - i < (bs.take k).length := by omega
      have hget : (bs.take k)[(bs.take k).length - 1 - i]'hidx_lt = bit (k - 1 - i) := by
        simp [bs, hlen]
      simpa [hlen] using hget
    · omega
    · omega
    · rfl
  -- Prove ValidPath on every suffix `bs.drop k` starting from `pushList (bs.take k) (fun _ => true)`
  have hvalid : ∀ k : ℕ, k ≤ L →
      ValidPath s t (bs.drop k) (pushList (bs.take k) (fun _ => true)) := by
    intro k hk
    have hrem : ∃ r, L - k = r := ⟨L - k, rfl⟩
    obtain ⟨r, hr⟩ := hrem
    induction r generalizing k with
    | zero =>
      have hkL : k = L := by omega
      subst hkL
      have hdrop : bs.drop L = [] := List.drop_eq_nil_iff.mpr (by rw [hbs_len])
      rw [hdrop]; trivial
    | succ r ih =>
      have hk_lt : k < L := by omega
      have hdrop : bs.drop k = bit k :: bs.drop (k + 1) := by
        have hlt : k < bs.length := by rw [hbs_len]; exact hk_lt
        rw [← List.cons_getElem_drop_succ (h := hlt)]
        simp [bs]
      have htake : push (bit k) (pushList (bs.take k) (fun _ => true)) =
          pushList (bs.take (k + 1)) (fun _ => true) := by
        have ht1 : bs.take (k + 1) = bs.take k ++ [bit k] := by
          have hlt : k < bs.length := by rw [hbs_len]; exact hk_lt
          rw [List.take_succ_eq_append_getElem hlt]
          simp [bs]
        rw [ht1]
        simp [pushList]
      rw [hdrop]
      refine ⟨?_, ?_⟩
      · intro hbit_false
        unfold allowZero
        rw [hprefix_val k (t + s - 1) hk, hprefix_val k (s + s - 1) hk]
        -- Since bit k = false, k = idx1 or k = idx2
        have hk_eq : k = idx1 ∨ k = idx2 := by
          dsimp [bit] at hbit_false
          by_contra hnot
          push Not at hnot
          simp [hnot.1, hnot.2] at hbit_false
        -- In either case, k - 1 - (t + s - 1) and k - 1 - (s + s - 1) cannot both be in {idx1, idx2}
        -- In fact, k ≤ max(idx1, idx2) = max t s - min t s < t + s or < s + s!
        by_cases hts : t + s - 1 < k
        · by_cases hss : s + s - 1 < k
          · exfalso
            -- Impossible: k = idx1 or idx2, and both idx1, idx2 ≤ max t s - s? No, idx1 = L - (t+s), idx2 = L - 2s.
            -- If t ≤ s: L = 2s, idx1 = s - t < s < 2s - 1, idx2 = 0. So k < 2s - 1, contradicting hss!
            -- If s < t: L = t + s, idx1 = 0, idx2 = t - s < t + s - 1. So k < t + s - 1, contradicting hts!
            dsimp [idx1, idx2, L] at hk_eq
            omega
          · simp [hss]
        · simp [hts]
      · rw [htake]
        exact ih (k + 1) (by omega) (by omega)
  have hvp0 : ValidPath s t bs (fun _ => true) := by
    have := hvalid 0 (Nat.zero_le L)
    simpa [pushList] using this
  have hfa : allowZero s t (pushList bs (fun _ => true)) = false := by
    have htakeL : bs.take L = bs := List.take_of_length_le (by rw [hbs_len])
    unfold allowZero
    rw [← htakeL, hprefix_val L (t + s - 1) (le_refl L),
        hprefix_val L (s + s - 1) (le_refl L),
        hprefix_val L (s - 1) (le_refl L)]
    have h1 : t + s - 1 < L := by dsimp [L]; omega
    have h2 : s + s - 1 < L := by dsimp [L]; omega
    have h3 : s - 1 < L := by dsimp [L]; omega
    have heq1 : L - 1 - (t + s - 1) = idx1 := by dsimp [idx1, L]; omega
    have heq2 : L - 1 - (s + s - 1) = idx2 := by dsimp [idx2, L]; omega
    have hne3a : L - 1 - (s - 1) ≠ idx1 := by dsimp [idx1, L]; omega
    have hne3b : L - 1 - (s - 1) ≠ idx2 := by dsimp [idx2, L]; omega
    rw [if_pos h1, if_pos h2, if_pos h3, heq1, heq2]
    simp [bit, hne3a, hne3b]
  have hlt := continuations_lt_two_pow_of_path bs (fun _ => true) hvp0 hfa
  simpa [hbs_len, L, count] using hlt

/-! ### Part 4: Fekete limit `c` and general bounds -/

private lemma exists_general_c {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    ∃ c : ℝ, 7 / 4 ≤ c ∧ c < 2 ∧
      (∀ n : ℕ, c ^ n ≤ (count s t n : ℝ) ∧ (count s t n : ℝ) ≤ c ^ (n + max t s + s)) := by
  let u : ℕ → ℝ := fun n => Real.log (count s t n : ℝ)
  have hpos_r : ∀ n : ℕ, (0 : ℝ) < (count s t n : ℝ) := fun n =>
    Nat.cast_pos.mpr (continuations_pos s t n _)
  have hsub : Subadditive u := by
    intro m n
    dsimp only [u]
    rw [← Real.log_mul (ne_of_gt (hpos_r m)) (ne_of_gt (hpos_r n))]
    refine Real.log_le_log (hpos_r (m + n)) ?_
    exact_mod_cast count_submul hs m n
  have hbdd : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : (1 : ℝ) ≤ (count s t n : ℝ) := by
      exact_mod_cast continuations_pos s t n (fun _ => true)
    exact div_nonneg (Real.log_nonneg h1) (Nat.cast_nonneg n)
  let c : ℝ := Real.exp hsub.lim
  have hc_pos : 0 < c := Real.exp_pos _
  have hlim_tendsto : Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (nhds hsub.lim) :=
    hsub.tendsto_lim hbdd
  have hlower : ∀ n : ℕ, c ^ n ≤ (count s t n : ℝ) := by
    intro n
    cases n with
    | zero => simp [count, continuations]
    | succ n =>
      have hdiv := hsub.lim_le_div hbdd (Nat.succ_ne_zero n)
      have hn_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hmul : ((n + 1 : ℕ) : ℝ) * hsub.lim ≤ u (n + 1) := by
        rwa [le_div_iff₀ hn_pos, mul_comm] at hdiv
      have hexp := Real.exp_le_exp.mpr hmul
      rw [Real.exp_nat_mul] at hexp
      rwa [Real.exp_log (hpos_r (n + 1))] at hexp
  have hupper : ∀ n : ℕ, (count s t n : ℝ) ≤ c ^ (n + max t s + s) := by
    intro n
    let L := max t s + s
    have hpow_le : ∀ k : ℕ, 1 ≤ k → (count s t n) ^ k ≤ count s t (k * (n + L)) := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hkpos
        · simp only [zero_add, pow_one, one_mul]
          exact count_mono s t (by omega)
        · calc (count s t n) ^ (k + 1)
              = (count s t n) ^ k * count s t n := pow_succ _ _
            _ ≤ count s t (k * (n + L)) * count s t n := Nat.mul_le_mul_right _ (ih hkpos)
            _ ≤ count s t (k * (n + L) + (L + n)) := count_supermul hs _ _
            _ = count s t ((k + 1) * (n + L)) := by congr 1; ring
    have hlog_le : u n / ((n + L : ℕ) : ℝ) ≤ hsub.lim := by
      have hnL_pos : 0 < n + L := by dsimp [L]; omega
      have hcomp : Tendsto (fun k : ℕ => u (k * (n + L)) / ((k * (n + L) : ℕ) : ℝ))
          atTop (nhds hsub.lim) := by
        refine hlim_tendsto.comp ?_
        rw [tendsto_atTop_atTop]
        intro b
        refine ⟨b, fun k hk => ?_⟩
        nlinarith
      refine ge_of_tendsto hcomp ?_
      rw [eventually_atTop]
      refine ⟨1, fun k hk => ?_⟩
      have hkr : (0 : ℝ) < (k : ℝ) := by positivity
      have hnLr : (0 : ℝ) < ((n + L : ℕ) : ℝ) := by positivity
      have h1 : (k : ℝ) * u n ≤ u (k * (n + L)) := by
        dsimp only [u]
        rw [← Real.log_pow]
        refine Real.log_le_log (pow_pos (hpos_r n) k) ?_
        exact_mod_cast hpow_le k hk
      rw [Nat.cast_mul, div_le_div_iff₀ hnLr (mul_pos hkr hnLr)]
      nlinarith
    have hnL_pos : (0 : ℝ) < ((n + L : ℕ) : ℝ) := by dsimp [L]; positivity
    have hmul : u n ≤ ((n + L : ℕ) : ℝ) * hsub.lim := by
      rwa [div_le_iff₀ hnL_pos, mul_comm] at hlog_le
    have hexp := Real.exp_le_exp.mpr hmul
    rw [Real.exp_log (hpos_r n), Real.exp_nat_mul] at hexp
    have hadd : n + max t s + s = n + L := by dsimp [L]; omega
    rwa [hadd]
  have hc_ge : 7 / 4 ≤ c := by
    have hlog : Real.log (7 / 4) ≤ hsub.lim := by
      refine ge_of_tendsto hlim_tendsto ?_
      rw [eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      rw [le_div_iff₀ hn_pos]
      have h1 := Real.log_le_log (by positivity : (0 : ℝ) < (7 / 4 : ℝ) ^ n)
        (seven_fourths_pow_le_count (t := t) hs n)
      rw [Real.log_pow] at h1
      linarith
    have := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 7 / 4)] at this
  have hc_lt : c < 2 := by
    let L := max t s + s
    have h1 := hlower (L + 1)
    have h2 : (count s t (L + 1) : ℝ) < (2 : ℝ) ^ (L + 1) := by
      exact_mod_cast count_lt_two_pow hs ht
    have hpow : c ^ (L + 1) < (2 : ℝ) ^ (L + 1) := lt_of_le_of_lt h1 h2
    by_contra hge
    push Not at hge
    have : (2 : ℝ) ^ (L + 1) ≤ c ^ (L + 1) := pow_le_pow_left₀ (by norm_num) hge _
    linarith
  exact ⟨c, hc_ge, hc_lt, fun n => ⟨hlower n, hupper n⟩⟩

/-! ### Part 5: Exact transfer-matrix eigenvector for `(s, t) = (2, 3)` -/

private def stateCode (h : ℕ → Bool) : Fin 32 :=
  ⟨(if h 0 then 1 else 0) + (if h 1 then 2 else 0) + (if h 2 then 4 else 0) +
    (if h 3 then 8 else 0) + (if h 4 then 16 else 0), by
    split_ifs <;> omega⟩

private def clsOf (st : Fin 32) : Fin 9 :=
  match st.val with
  | 0 | 8 | 16 | 24 => 0
  | 1 | 17 => 1
  | 2 | 6 | 7 => 2
  | 3 => 3
  | 4 | 12 | 20 | 28 => 4
  | 5 | 11 | 13 | 15 | 21 | 23 | 27 | 29 | 31 => 5
  | 9 | 25 => 6
  | 10 | 14 | 18 | 22 | 26 | 30 => 7
  | _ => 8

private def eigW (r : ℝ) : Fin 9 → ℝ
  | 0 => -60 - 8*r + 37*r^2 - 3*r^3 - 10*r^4 - 32*r^5 + 19*r^6
  | 1 => 41 + 5*r - 26*r^2 + 2*r^3 + 7*r^4 + 22*r^5 - 13*r^6
  | 2 => 3 + r - 2*r^2 + 2*r^5 - r^6
  | 3 => 10 + r - 6*r^2 + 2*r^4 + 5*r^5 - 3*r^6
  | 4 => -1 - r + r^2
  | 5 => 1
  | 6 => 60 + 7*r - 38*r^2 + 4*r^3 + 10*r^4 + 32*r^5 - 19*r^6
  | 7 => -1 + r
  | 8 => 20 + 2*r - 12*r^2 + 4*r^4 + 10*r^5 - 6*r^6

private def pushState (b : Bool) (st : Fin 32) : Fin 32 :=
  ⟨((st.val * 2) % 32) + if b then 1 else 0, by
    have := Nat.mod_lt (st.val * 2) (by norm_num : 0 < 32)
    have : (st.val * 2) % 32 % 2 = 0 := by omega
    split_ifs <;> omega⟩

private def allowZeroState (st : Fin 32) : Bool :=
  (st.val / 16 % 2 == 1) || (st.val / 8 % 2 == 1) || !(st.val / 2 % 2 == 1)

private lemma stateCode_push_aux (b b0 b1 b2 b3 b4 : Bool) :
    ((if b then 1 else 0) + (if b0 then 2 else 0) + (if b1 then 4 else 0) +
      (if b2 then 8 else 0) + (if b3 then 16 else 0)) =
    ((((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
      (if b3 then 8 else 0) + (if b4 then 16 else 0)) * 2) % 32) +
    (if b then 1 else 0) := by
  cases b <;> cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

private lemma stateCode_push (b : Bool) (h : ℕ → Bool) :
    stateCode (push b h) = pushState b (stateCode h) := by
  ext
  exact stateCode_push_aux b (h 0) (h 1) (h 2) (h 3) (h 4)

private lemma allowZero_eq_state_aux (b0 b1 b2 b3 b4 : Bool) :
    let v := (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
      (if b3 then 8 else 0) + (if b4 then 16 else 0)
    (b4 || b3 || !b1) = ((v / 16 % 2 == 1) || (v / 8 % 2 == 1) || !(v / 2 % 2 == 1)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

private lemma allowZero_eq_state (h : ℕ → Bool) :
    allowZero 2 3 h = allowZeroState (stateCode h) := by
  exact allowZero_eq_state_aux (h 0) (h 1) (h 2) (h 3) (h 4)

private lemma eig_step_finite (r : ℝ) (hr : r ^ 7 - 2 * r ^ 6 + 2 * r ^ 3 - r ^ 2 - 3 * r + 1 = 0)
    (st : Fin 32) :
    r * eigW r (clsOf st) =
      eigW r (clsOf (pushState true st)) +
        if allowZeroState st = true then eigW r (clsOf (pushState false st)) else 0 := by
  fin_cases st <;> simp [clsOf, pushState, allowZeroState, eigW] <;>
    (first
      | linear_combination 19 * hr
      | linear_combination (-13) * hr
      | linear_combination (-1) * hr
      | linear_combination (-3) * hr
      | linear_combination (-19) * hr
      | linear_combination (-6) * hr
      | ring)

private lemma eigW_bounds (r : ℝ) (hlo : 1884337 / 1000000 < r) (hhi : r < 1884338 / 1000000)
    (i : Fin 9) : 1 / 10 ≤ eigW r i ∧ eigW r i ≤ 2 := by
  have hr2_lo : (1884337 / 1000000 : ℝ) ^ 2 < r ^ 2 := by nlinarith
  have hr2_hi : r ^ 2 < (1884338 / 1000000 : ℝ) ^ 2 := by nlinarith
  have hr3_lo : (1884337 / 1000000 : ℝ) ^ 3 < r ^ 3 := by nlinarith
  have hr3_hi : r ^ 3 < (1884338 / 1000000 : ℝ) ^ 3 := by nlinarith
  have hr4_lo : (1884337 / 1000000 : ℝ) ^ 4 < r ^ 4 := by nlinarith
  have hr4_hi : r ^ 4 < (1884338 / 1000000 : ℝ) ^ 4 := by nlinarith
  have hr5_lo : (1884337 / 1000000 : ℝ) ^ 5 < r ^ 5 := by nlinarith
  have hr5_hi : r ^ 5 < (1884338 / 1000000 : ℝ) ^ 5 := by nlinarith
  have hr6_lo : (1884337 / 1000000 : ℝ) ^ 6 < r ^ 6 := by nlinarith
  have hr6_hi : r ^ 6 < (1884338 / 1000000 : ℝ) ^ 6 := by nlinarith
  fin_cases i <;> simp only [eigW] <;> constructor <;> linarith

private lemma exists_root_23 :
    ∃ r : ℝ, 1884337 / 1000000 < r ∧ r < 1884338 / 1000000 ∧
      r ^ 7 - 2 * r ^ 6 + 2 * r ^ 3 - r ^ 2 - 3 * r + 1 = 0 := by
  let f : ℝ → ℝ := fun x => x ^ 7 - 2 * x ^ 6 + 2 * x ^ 3 - x ^ 2 - 3 * x + 1
  have hcont : ContinuousOn f (Set.Icc (1884337 / 1000000) (1884338 / 1000000)) := by
    fun_prop
  have hfa : f (1884337 / 1000000) < 0 := by dsimp [f]; norm_num
  have hfb : 0 < f (1884338 / 1000000) := by dsimp [f]; norm_num
  have h0_mem : (0 : ℝ) ∈ Set.Icc (f (1884337 / 1000000)) (f (1884338 / 1000000)) :=
    ⟨le_of_lt hfa, le_of_lt hfb⟩
  obtain ⟨r, ⟨hr1, hr2⟩, hfr⟩ :=
    intermediate_value_Icc (by norm_num : (1884337 / 1000000 : ℝ) ≤ 1884338 / 1000000) hcont h0_mem
  have hr1_lt : 1884337 / 1000000 < r := lt_of_le_of_ne hr1 (fun h => by rw [← h] at hfr; linarith)
  have hr2_lt : r < 1884338 / 1000000 := lt_of_le_of_ne hr2 (fun h => by rw [h] at hfr; linarith)
  exact ⟨r, hr1_lt, hr2_lt, hfr⟩

private lemma continuations_23_sandwiched (r : ℝ)
    (hlo : 1884337 / 1000000 < r) (hhi : r < 1884338 / 1000000)
    (hr : r ^ 7 - 2 * r ^ 6 + 2 * r ^ 3 - r ^ 2 - 3 * r + 1 = 0)
    (n : ℕ) (h : ℕ → Bool) :
    (1 / 2 : ℝ) * eigW r (clsOf (stateCode h)) * r ^ n ≤ (continuations 2 3 n h : ℝ) ∧
    (continuations 2 3 n h : ℝ) ≤ 10 * eigW r (clsOf (stateCode h)) * r ^ n := by
  induction n generalizing h with
  | zero =>
    simp only [pow_zero, mul_one, continuations, Nat.cast_one]
    have hb := eigW_bounds r hlo hhi (clsOf (stateCode h))
    constructor <;> linarith
  | succ n ih =>
    unfold continuations
    have h1 := ih (push true h)
    have h2 := ih (push false h)
    have heig := eig_step_finite r hr (stateCode h)
    rw [← stateCode_push true h, ← stateCode_push false h, ← allowZero_eq_state h] at heig
    have hrn_nn : (0 : ℝ) ≤ r ^ n := by positivity
    rw [pow_succ']
    by_cases ha : allowZero 2 3 h = true
    · rw [if_pos ha] at heig ⊢
      push_cast
      constructor <;> nlinarith
    · rw [if_neg ha] at heig ⊢
      simp only [add_zero] at heig ⊢
      constructor <;> nlinarith

theorem main_proof : ∀ s t : ℕ, 0 < s → 0 < t → ∃ c : ℝ,
    7 / 4 ≤ c ∧ c < 2 ∧
    (∀ n : ℕ, c ^ n ≤ (count s t n : ℝ) ∧ (count s t n : ℝ) ≤ c ^ (n + max t s + s)) ∧
    (s = 2 → t = 3 →
      1884337 / 1000000 < c ∧ c < 1884338 / 1000000 ∧
      c ^ 7 - 2 * c ^ 6 + 2 * c ^ 3 - c ^ 2 - 3 * c + 1 = 0) := by
  intro s t hs ht
  obtain ⟨c, hc1, hc2, hbounds⟩ := exists_general_c hs ht
  refine ⟨c, hc1, hc2, hbounds, ?_⟩
  rintro rfl rfl
  obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ := exists_root_23
  have hcr : c = r := by
    have hsand : ∀ n : ℕ, (1 / 2 : ℝ) * r ^ n ≤ (count 2 3 n : ℝ) ∧
        (count 2 3 n : ℝ) ≤ 10 * r ^ n := by
      intro n
      have h := continuations_23_sandwiched r hr_lo hr_hi hr_eq n (fun _ => true)
      have hcls : clsOf (stateCode (fun _ => true)) = 5 := by decide
      rw [hcls] at h
      simpa [count, eigW] using h
    have hc_pos : 0 < c := by linarith
    have hr_pos : 0 < r := by linarith
    have hle : c ≤ r := by
      by_contra hgt
      push Not at hgt
      have hratio : 1 < c / r := (one_lt_div hr_pos).mpr hgt
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (10 : ℝ) hratio
      have h1 := (hbounds n).1
      have h2 := (hsand n).2
      have h3 : (c / r) ^ n ≤ 10 := by
        rw [div_pow, div_le_iff₀ (pow_pos hr_pos n)]
        linarith
      linarith
    have hge : r ≤ c := by
      by_contra hlt
      push Not at hlt
      have hratio : 1 < r / c := (one_lt_div hc_pos).mpr hlt
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * c ^ 5) hratio
      have h1 := (hbounds n).2
      have h2 := (hsand n).1
      have h5 : n + max 3 2 + 2 = n + 5 := by omega
      rw [h5, pow_add] at h1
      have h3 : (r / c) ^ n ≤ 2 * c ^ 5 := by
        rw [div_pow, div_le_iff₀ (pow_pos hc_pos n)]
        linarith
      linarith
    linarith
  rw [hcr]
  exact ⟨hr_lo, hr_hi, hr_eq⟩

end OMA.S_mo_472052_Proof

theorem OMA.solution : type_of% @OMA.S_mo_472052.main :=
  OMA.S_mo_472052_Proof.main_proof
