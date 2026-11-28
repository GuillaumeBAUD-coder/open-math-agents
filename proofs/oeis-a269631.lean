import OMAStatements.S_oeis_a269631
import Mathlib

namespace OMA.S_oeis_a269631_Proof

open OMA.S_oeis_a269631

private lemma digits_ne_nil (n : ℕ) : digits n ≠ [] := by
  unfold digits
  split_ifs with h
  · simp
  · exact Nat.digits_ne_nil_iff_ne_zero.mpr h

private lemma digits_length_pos (n : ℕ) : 1 ≤ (digits n).length := by
  have h := digits_ne_nil n
  cases hlen : (digits n) with
  | nil => exact (h hlen).elim
  | cons _ _ => simp

private lemma digits_length_le_of_lt_pow {n m : ℕ} (hm : 1 ≤ m) (hlt : n < 10 ^ m) :
    (digits n).length ≤ m := by
  unfold digits
  split_ifs with h0
  · simpa using hm
  · rw [Nat.length_digits 10 n (by norm_num) h0]
    have hlog : Nat.log 10 n < m := Nat.log_lt_of_lt_pow h0 hlt
    omega

private lemma pow_le_of_digits_length {n : ℕ} (hn : 1 ≤ n) :
    10 ^ ((digits n).length - 1) ≤ n := by
  unfold digits
  rw [if_neg (by omega)]
  have hlen : (Nat.digits 10 n).length = Nat.log 10 n + 1 :=
    Nat.length_digits 10 n (by norm_num) (by omega)
  rw [hlen, Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 10 (by omega)

private lemma digits_length_eq_of_bounds {n m : ℕ} (hm : 1 ≤ m)
    (hlo : 10 ^ (m - 1) ≤ n) (hhi : n < 10 ^ m) : (digits n).length = m := by
  have hn0 : n ≠ 0 := by
    have hpos : 1 ≤ 10 ^ (m - 1) := Nat.one_le_pow _ _ (by omega)
    omega
  unfold digits
  rw [if_neg hn0, Nat.length_digits 10 n (by norm_num) hn0]
  have h1 : m - 1 ≤ Nat.log 10 n := Nat.le_log_of_pow_le (by norm_num) hlo
  have h2 : Nat.log 10 n < m := Nat.log_lt_of_lt_pow hn0 hhi
  omega

private lemma digits_append_pow (k d t : ℕ) (hk : 1 ≤ k) (ht : t < 10 ^ d) :
    (digits k).IsInfix (digits (k * 10 ^ d + t)) := by
  have hne : k * 10 ^ d + t ≠ 0 := by
    have : 1 ≤ 10 ^ d := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hk0 : k ≠ 0 := by omega
  unfold digits
  rw [if_neg hk0, if_neg hne]
  clear hne
  suffices h : ∃ l : List ℕ, Nat.digits 10 (k * 10 ^ d + t) = l ++ Nat.digits 10 k by
    rcases h with ⟨l, hl⟩
    exact ⟨l, [], by simp [hl]⟩
  induction d generalizing t with
  | zero =>
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    exact ⟨[], by simp⟩
  | succ d ih =>
    have hlt_d : t / 10 < 10 ^ d := by
      rw [pow_succ'] at ht
      omega
    have hmul : k * 10 ^ (d + 1) + t = 10 * (k * 10 ^ d) + t := by
      rw [pow_succ]; ring
    have hdiv : (k * 10 ^ (d + 1) + t) / 10 = k * 10 ^ d + t / 10 := by
      rw [hmul, Nat.mul_add_div (by omega : 0 < 10)]
    have hmod : (k * 10 ^ (d + 1) + t) % 10 = t % 10 := by
      rw [hmul, Nat.mul_add_mod]
    have hpos : k * 10 ^ (d + 1) + t ≠ 0 := by
      have : 1 ≤ 10 ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
      nlinarith
    rw [Nat.digits_def' (by norm_num : 1 < 10) (Nat.pos_of_ne_zero hpos), hmod, hdiv]
    obtain ⟨l, hl⟩ := ih (t / 10) hlt_d
    exact ⟨(t % 10) :: l, by simp [hl]⟩

private lemma exists_eligible (seen : Finset ℕ) (prev : ℕ) :
    ∃ x : ℕ, eligible seen prev x := by
  let k := (digits prev).length
  have hk1 : 1 ≤ k := digits_length_pos prev
  let B := seen.sup id + 1
  let d := Nat.log 10 B + 1
  have hB_lt : B < 10 ^ d := Nat.lt_pow_succ_log_self (by norm_num) B
  let x := k * 10 ^ d
  have hx_notin : x ∉ seen := by
    intro hx
    have hle : x ≤ seen.sup id := Finset.le_sup (f := id) hx
    have h1 : 10 ^ d ≤ x := Nat.le_mul_of_pos_left _ hk1
    omega
  refine ⟨x, hx_notin, ?_⟩
  simpa using digits_append_pow k d 0 hk1 (by positivity)

private lemma state_snd_eq_image :
    ∀ n : ℕ, (state n).2 = (Finset.range (n + 1)).image a := by
  intro n
  induction n with
  | zero =>
    simp [state, a]
  | succ n ih =>
    have h1 : (state (n + 1)).2 = insert (a (n + 1)) (state n).2 := by
      simp [state, a]
    rw [h1, ih]
    conv_rhs => rw [Finset.range_add_one, Finset.image_insert]

private lemma a_succ_eq_next (n : ℕ) :
    a (n + 1) = next (state n).2 (state n).1 := by
  simp [a, state]

private lemma a_succ_eligible (n : ℕ) :
    eligible (state n).2 (state n).1 (a (n + 1)) := by
  classical
  rw [a_succ_eq_next]
  unfold next
  have hex := exists_eligible (state n).2 (state n).1
  rw [dif_pos hex]
  exact Nat.find_spec hex

private lemma a_succ_le_of_eligible (n x : ℕ)
    (hx : eligible (state n).2 (state n).1 x) : a (n + 1) ≤ x := by
  classical
  rw [a_succ_eq_next]
  unfold next
  have hex := exists_eligible (state n).2 (state n).1
  rw [dif_pos hex]
  exact Nat.find_min' hex hx

private lemma a_injective : Function.Injective a := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : a i ∈ (state (j - 1)).2 := by
      rw [state_snd_eq_image]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
    have hnot : a j ∉ (state (j - 1)).2 := by
      have hEq : j = (j - 1) + 1 := by omega
      have hel := a_succ_eligible (j - 1)
      rw [← hEq] at hel
      exact hel.1
    rw [hij] at hmem
    exact hnot hmem
  · have hmem : a j ∈ (state (i - 1)).2 := by
      rw [state_snd_eq_image]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
    have hnot : a i ∉ (state (i - 1)).2 := by
      have hEq : i = (i - 1) + 1 := by omega
      have hel := a_succ_eligible (i - 1)
      rw [← hEq] at hel
      exact hel.1
    rw [← hij] at hmem
    exact hnot hmem

private lemma exists_ge_pow (M : ℕ) : ∃ n : ℕ, M ≤ a n := by
  by_contra hall
  push Not at hall
  have hsub : (Finset.range (M + 1)).image a ⊆ Finset.range M := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨n, _, rfl⟩
    exact Finset.mem_range.mpr (hall n)
  have hcard : ((Finset.range (M + 1)).image a).card ≤ (Finset.range M).card :=
    Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ a_injective, Finset.card_range, Finset.card_range] at hcard
  omega

private lemma mul_succ_lt_ten_pow_pred : ∀ m : ℕ, 2 ≤ m → m * (m + 1) < 10 ^ (m - 1) := by
  intro m hm
  induction m with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le (show 1 ≤ k by omega) with rfl | hk2
    · norm_num
    · have hih := ih hk2
      have hexp : k + 1 - 1 = (k - 1) + 1 := by omega
      rw [hexp, pow_succ]
      nlinarith

private lemma a_surjective : Function.Surjective a := by
  intro m
  rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm_pos
  · exact ⟨0, rfl⟩
  by_contra hnot
  push Not at hnot
  -- Find the least index n₁ with 10^m ≤ a n₁
  have hex : ∃ n : ℕ, 10 ^ m ≤ a n := exists_ge_pow (10 ^ m)
  classical
  let n₁ := Nat.find hex
  have hn₁_ge : 10 ^ m ≤ a n₁ := Nat.find_spec hex
  have hn₁_pos : 1 ≤ n₁ := by
    by_contra h0
    have hz : n₁ = 0 := by omega
    have ha0 : a 0 = 0 := rfl
    rw [hz, ha0] at hn₁_ge
    have : 1 ≤ 10 ^ m := Nat.one_le_pow _ _ (by omega)
    omega
  let n₀ := n₁ - 1
  have hn₁_eq : n₁ = n₀ + 1 := by omega
  have hn₀_lt : a n₀ < 10 ^ m := by
    have hlt : n₀ < n₁ := by omega
    have := Nat.find_min hex hlt
    omega
  let k := (digits (a n₀)).length
  have hk1 : 1 ≤ k := digits_length_pos (a n₀)
  have hkm : k ≤ m := digits_length_le_of_lt_pow hm_pos hn₀_lt
  -- Every x < 10^m containing digits k must already be in (state n₀).2
  have hin_seen : ∀ x : ℕ, x < 10 ^ m → (digits k).IsInfix (digits x) → x ∈ (state n₀).2 := by
    intro x hx_lt hx_inf
    by_contra hx_not
    have hel : eligible (state n₀).2 (state n₀).1 x := ⟨hx_not, hx_inf⟩
    have hle : a (n₀ + 1) ≤ x := a_succ_le_of_eligible n₀ x hel
    rw [← hn₁_eq] at hle
    omega
  have hm1 : 1 ≤ m := hm_pos
  rcases eq_or_lt_of_le hm1 with rfl | hm2
  · -- Case m = 1: k = 1, x = 1 must be in seen
    have hk_eq : k = 1 := by omega
    have h1_mem : 1 ∈ (state n₀).2 := hin_seen 1 (by norm_num) (by rw [hk_eq])
    rw [state_snd_eq_image] at h1_mem
    rcases Finset.mem_image.mp h1_mem with ⟨i, _, hi⟩
    exact hnot i hi
  · -- Case m ≥ 2: count m-digit numbers in (state n₀).2 containing digits k
    let r := (digits k).length
    have hr1 : 1 ≤ r := digits_length_pos k
    have hpow_r : 10 ^ (r - 1) ≤ k := pow_le_of_digits_length hk1
    have hrm : r < m := by
      have hm_lt : m < 10 ^ (m - 1) := by
        have := mul_succ_lt_ten_pow_pred m hm2
        nlinarith
      have h1 : 10 ^ (r - 1) < 10 ^ (m - 1) := lt_of_le_of_lt (le_trans hpow_r hkm) hm_lt
      have h2 : r - 1 < m - 1 := (Nat.pow_lt_pow_iff_right (by omega : 1 < 10)).mp h1
      omega
    -- Construct 10^(m - r) distinct m-digit numbers in (state n₀).2
    let f : ℕ → ℕ := fun t => k * 10 ^ (m - r) + t
    let T : Finset ℕ := (Finset.range (10 ^ (m - r))).image f
    have hT_card : T.card = 10 ^ (m - r) := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro t₁ t₂ h; dsimp [f] at h; omega
    have hT_sub : T ⊆ (state n₀).2.filter (fun x => (digits x).length = m) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
      have ht_lt : t < 10 ^ (m - r) := Finset.mem_range.mp ht
      have hk_lt : k < 10 ^ r := by
        have hlen : Nat.log 10 k + 1 = r := by
          dsimp [r]; unfold digits; rw [if_neg (by omega), Nat.length_digits 10 k (by norm_num) (by omega)]
        rw [← hlen]
        exact Nat.lt_pow_succ_log_self (by norm_num) k
      have hfx_lo : 10 ^ (m - 1) ≤ f t := by
        dsimp [f]
        have h1 : 10 ^ (m - 1) = 10 ^ (r - 1) * 10 ^ (m - r) := by
          rw [← pow_add]; congr 1; omega
        rw [h1]
        exact le_trans (Nat.mul_le_mul_right _ hpow_r) (Nat.le_add_right _ _)
      have hfx_hi : f t < 10 ^ m := by
        dsimp [f]
        have h1 : 10 ^ m = 10 ^ r * 10 ^ (m - r) := by
          rw [← pow_add]; congr 1; omega
        rw [h1]
        have h2 : k + 1 ≤ 10 ^ r := hk_lt
        have h3 : (k + 1) * 10 ^ (m - r) ≤ 10 ^ r * 10 ^ (m - r) := Nat.mul_le_mul_right _ h2
        linarith [add_mul k 1 (10 ^ (m - r))]
      refine Finset.mem_filter.mpr ⟨hin_seen (f t) hfx_hi (digits_append_pow k (m - r) t hk1 ht_lt), ?_⟩
      exact digits_length_eq_of_bounds (by omega) hfx_lo hfx_hi
    -- On the other hand, at most m + 1 elements in (state n₀).2 can have length m
    have hupper : ((state n₀).2.filter (fun x => (digits x).length = m)).card ≤ m + 1 := by
      rw [state_snd_eq_image]
      let S_idx := (Finset.range (n₀ + 1)).filter (fun i => (digits (a i)).length = m)
      have hcard_eq : (((Finset.range (n₀ + 1)).image a).filter (fun x => (digits x).length = m)).card =
          S_idx.card := by
        rw [Finset.filter_image, Finset.card_image_of_injective _ a_injective]
      rw [hcard_eq]
      have hmap_sub : (S_idx.image (fun i => a (i + 1))) ⊆ Finset.range (m + 1) := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
        have hlen : (digits (a i)).length = m := (Finset.mem_filter.mp hi).2
        have hm_not_seen : m ∉ (state i).2 := by
          rw [state_snd_eq_image]
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
          exact hnot j hj
        have hm_elig : eligible (state i).2 (state i).1 m := by
          refine ⟨hm_not_seen, ?_⟩
          have hs : (state i).1 = a i := rfl
          rw [hs, hlen]
        have hle := a_succ_le_of_eligible i m hm_elig
        exact Finset.mem_range.mpr (by omega)
      have hinj : Function.Injective (fun i => a (i + 1)) := fun i j h => by
        have := a_injective h; omega
      calc S_idx.card = (S_idx.image (fun i => a (i + 1))).card :=
            (Finset.card_image_of_injective _ hinj).symm
        _ ≤ (Finset.range (m + 1)).card := Finset.card_le_card hmap_sub
        _ = m + 1 := Finset.card_range _
    have hle_cards : 10 ^ (m - r) ≤ m + 1 := by
      rw [← hT_card]
      exact le_trans (Finset.card_le_card hT_sub) hupper
    -- Contradict 10^(m - r) > m + 1
    have hmul_lt : (m + 1) * 10 ^ r < 10 ^ m := by
      have h10r : 10 ^ r ≤ 10 * m := by
        have h1 : 10 ^ r = 10 * 10 ^ (r - 1) := by
          have : r = (r - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
        rw [h1]
        exact Nat.mul_le_mul_left 10 (le_trans hpow_r hkm)
      have hpow_m : 10 ^ m = 10 * 10 ^ (m - 1) := by
        have : m = (m - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ']
      have hstep := mul_succ_lt_ten_pow_pred m hm2
      rw [hpow_m]
      nlinarith
    have hpow_split : 10 ^ (m - r) * 10 ^ r = 10 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt hrm)]
    have hmul_le : 10 ^ m ≤ (m + 1) * 10 ^ r := by
      rw [← hpow_split]
      exact Nat.mul_le_mul_right _ hle_cards
    omega

theorem main_proof : Function.Bijective a :=
  ⟨a_injective, a_surjective⟩

end OMA.S_oeis_a269631_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a269631.main :=
  OMA.S_oeis_a269631_Proof.main_proof
