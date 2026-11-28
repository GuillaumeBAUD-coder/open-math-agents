import OMAStatements.S_oeis_a083942
import Mathlib

open OMA.S_oeis_a083942

namespace A083942Proof

open DyckStep

def bit : DyckStep → ℕ
  | U => 1
  | D => 0

def unbit (d : ℕ) : DyckStep := if d = 0 then D else U

lemma bit_injective : Function.Injective bit := by
  intro s t h
  cases s <;> cases t <;> first | rfl | (simp [bit] at h)

lemma bit_lt (s : DyckStep) : bit s < 2 := by cases s <;> simp [bit]

lemma unbit_bit (s : DyckStep) : unbit (bit s) = s := by cases s <;> simp [bit, unbit]

lemma map_bit_unbit (l : List ℕ) (hl : ∀ x ∈ l, x < 2) : (l.map unbit).map bit = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  have := hl x hx
  unfold unbit
  simp only [Function.comp_apply, id]
  split_ifs with h
  · simp [bit, h]
  · simp [bit]; omega

lemma count_bit_U (l : List DyckStep) : l.count U = (l.map bit).count 1 := by
  rw [show (1 : ℕ) = bit U from rfl, List.count_map_of_injective _ _ bit_injective]

lemma count_bit_D (l : List DyckStep) : l.count D = (l.map bit).count 0 := by
  rw [show (0 : ℕ) = bit D from rfl, List.count_map_of_injective _ _ bit_injective]

/-- The binary number of a Dyck word (`U = 1`, `D = 0`, first step = most significant bit). -/
def enc (p : DyckWord) : ℕ := Nat.ofDigits 2 (p.toList.map bit).reverse

lemma digits_enc (p : DyckWord) : Nat.digits 2 (enc p) = (p.toList.map bit).reverse := by
  unfold enc
  apply Nat.digits_ofDigits 2 (by norm_num)
  · intro l hl
    rw [List.mem_reverse, List.mem_map] at hl
    obtain ⟨s, _, rfl⟩ := hl
    exact bit_lt s
  · intro h
    have hp : p.toList ≠ [] := by
      intro h'
      apply h
      simp [h']
    rw [List.getLast_reverse, List.head_map, DyckWord.head_eq_U p hp]
    simp [bit]

lemma TB_enc (p : DyckWord) : TB (enc p) := by
  unfold TB
  rw [digits_enc, List.reverse_reverse]
  refine ⟨?_, fun i _ => ?_⟩
  · rw [← count_bit_U, ← count_bit_D]
    exact p.count_U_eq_count_D.symm
  · rw [← List.map_take, ← count_bit_U, ← count_bit_D]
    exact p.count_D_le_count_U i

lemma enc_injective : Function.Injective enc := by
  intro p q h
  have h1 := congrArg (Nat.digits 2) h
  rw [digits_enc, digits_enc, List.reverse_inj] at h1
  exact DyckWord.ext (List.map_injective_iff.mpr bit_injective h1)

lemma length_digits_enc (p : DyckWord) :
    (Nat.digits 2 (enc p)).length = 2 * p.semilength := by
  rw [digits_enc, List.length_reverse, List.length_map, DyckWord.two_mul_semilength_eq_length]

lemma digits_lt_two (x : ℕ) : ∀ d ∈ (Nat.digits 2 x).reverse, d < 2 := by
  intro d hd
  rw [List.mem_reverse] at hd
  exact Nat.digits_lt_base (by norm_num) hd

/-- The Dyck word of a totally balanced number. -/
def ofTB (x : ℕ) (hx : TB x) : DyckWord where
  toList := (Nat.digits 2 x).reverse.map unbit
  count_U_eq_count_D := by
    rw [count_bit_U, count_bit_D, map_bit_unbit _ (digits_lt_two x)]
    exact hx.1.symm
  count_D_le_count_U i := by
    rw [count_bit_U, count_bit_D, ← List.map_take, map_bit_unbit _
      (fun d hd => digits_lt_two x d (List.mem_of_mem_take hd))]
    rcases Nat.lt_or_ge i (Nat.digits 2 x).length with h | h
    · exact hx.2 i h.le
    · have hx2 := hx.2 (Nat.digits 2 x).length le_rfl
      have e1 : ((Nat.digits 2 x).reverse.take i) = (Nat.digits 2 x).reverse :=
        List.take_of_length_le (by rw [List.length_reverse]; exact h)
      have e2 : ((Nat.digits 2 x).reverse.take (Nat.digits 2 x).length) =
          (Nat.digits 2 x).reverse :=
        List.take_of_length_le (by rw [List.length_reverse])
      rw [e1]
      rw [e2] at hx2
      exact hx2

lemma enc_ofTB (x : ℕ) (hx : TB x) : enc (ofTB x hx) = x := by
  unfold enc ofTB
  simp only
  rw [map_bit_unbit _ (digits_lt_two x), List.reverse_reverse, Nat.ofDigits_digits]

lemma card_TB_below (m : ℕ) :
    ((Finset.range (2 ^ (2 * m))).filter TB).card = ∑ k ∈ Finset.range (m + 1), catalan k := by
  set S := (Finset.range (m + 1)).sigma
    (fun k => (Finset.univ : Finset {p : DyckWord // p.semilength = k}))
  have hS : S.card = ∑ k ∈ Finset.range (m + 1), catalan k := by
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.card_univ, DyckWord.card_dyckWord_semilength_eq_catalan]
  rw [← hS]
  have himg : S.image (fun x => enc x.2.1) = (Finset.range (2 ^ (2 * m))).filter TB := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, S, Finset.mem_sigma,
      Finset.mem_univ, and_true]
    constructor
    · rintro ⟨⟨k, ⟨p, hp⟩⟩, hk, rfl⟩
      refine ⟨?_, TB_enc p⟩
      rw [← Nat.digits_length_le_iff (by norm_num), length_digits_enc, hp]
      simp only at hk
      omega
    · rintro ⟨hx, htb⟩
      refine ⟨⟨(ofTB x htb).semilength, ⟨ofTB x htb, rfl⟩⟩, ?_, enc_ofTB x htb⟩
      have h1 := length_digits_enc (ofTB x htb)
      rw [enc_ofTB] at h1
      have h2 := (Nat.digits_length_le_iff (b := 2) (k := 2 * m) (by norm_num) x).mpr hx
      simp only
      omega
  rw [← himg, Finset.card_image_of_injOn]
  rintro ⟨k, ⟨p, hp⟩⟩ _ ⟨k', ⟨q, hq⟩⟩ _ h
  simp only at h
  have := enc_injective h
  subst this
  subst hp
  subst hq
  rfl

lemma count01 (l : List ℕ) (hl : ∀ x ∈ l, x < 2) : l.count 0 + l.count 1 = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := hl a (List.mem_cons_self)
    have ht := ih (fun x hx => hl x (List.mem_cons_of_mem a hx))
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
      simp [List.count_cons] <;> omega

lemma digits_two_pow_sub_one (m : ℕ) : Nat.digits 2 (2 ^ m - 1) = List.replicate m 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 ^ (m + 1) - 1 = 1 + 2 * (2 ^ m - 1) := by
      have := Nat.one_le_two_pow (n := m)
      rw [pow_succ]; omega
    rw [h1, Nat.digits_def' (by norm_num) (by omega), List.replicate_succ]
    congr 1
    · omega
    · rw [← ih]; congr 1; omega

lemma digits_cj (m j : ℕ) (hj : j < 2 ^ m) :
    Nat.digits 2 (2 ^ (2 * m) - 2 ^ m + j) =
      Nat.digits 2 j ++ List.replicate (m - (Nat.digits 2 j).length) 0 ++ List.replicate m 1 := by
  have hl : (Nat.digits 2 j).length ≤ m := (Nat.digits_length_le_iff (by norm_num) j).mpr hj
  have hpos : 0 < 2 ^ m - 1 ∨ m = 0 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact Or.inr h
    · left; have := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp h); omega
  rcases hpos with hpos | hm0
  · rw [← digits_two_pow_sub_one m, Nat.digits_append_zeroes_append_digits (by norm_num) hpos]
    congr 1
    rw [show (Nat.digits 2 j).length + (m - (Nat.digits 2 j).length) = m by omega,
      Nat.mul_sub_one, ← pow_add, ← two_mul]
    have : 2 ^ m ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · subst hm0
    have : j = 0 := by simpa using hj
    subst this
    simp

lemma rev_cj (m j : ℕ) (hj : j < 2 ^ m) :
    (Nat.digits 2 (2 ^ (2 * m) - 2 ^ m + j)).reverse =
      List.replicate m 1 ++ (List.replicate (m - (Nat.digits 2 j).length) 0 ++
        (Nat.digits 2 j).reverse) := by
  rw [digits_cj m j hj]
  simp [List.reverse_append, List.reverse_replicate]

lemma TB_c (m : ℕ) : TB (2 ^ (2 * m) - 2 ^ m) := by
  have h := rev_cj m 0 (by positivity)
  simp only [add_zero, Nat.digits_zero, List.length_nil, Nat.sub_zero, List.reverse_nil,
    List.append_nil] at h
  unfold TB
  rw [h]
  refine ⟨by simp [List.count_replicate], fun i _ => ?_⟩
  rw [List.take_append, List.take_replicate, List.take_replicate]
  simp [List.count_replicate]

lemma not_TB_cj (m j : ℕ) (hj : j < 2 ^ m) (hj0 : 0 < j) : ¬ TB (2 ^ (2 * m) - 2 ^ m + j) := by
  intro htb
  have h1 := htb.1
  rw [rev_cj m j hj] at h1
  have hl : (Nat.digits 2 j).length ≤ m := (Nat.digits_length_le_iff (by norm_num) j).mpr hj
  have h01 := count01 (Nat.digits 2 j) (fun d hd => Nat.digits_lt_base (by norm_num) hd)
  have hc1 : 0 < (Nat.digits 2 j).count 1 := by
    have hne : Nat.digits 2 j ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have hlast := Nat.getLast_digit_ne_zero 2 (m := j) (by omega)
    have hlt := Nat.digits_lt_base (b := 2) (m := j) (by norm_num) (List.getLast_mem hne)
    have h1mem : 1 ∈ Nat.digits 2 j := by
      have : (Nat.digits 2 j).getLast hne = 1 := by omega
      rw [← this]; exact List.getLast_mem hne
    exact List.count_pos_iff.mpr h1mem
  simp [List.count_append, List.count_replicate, List.count_reverse] at h1
  omega

end A083942Proof

open A083942Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a083942.main := by
  intro n hn
  set m := 2 ^ n - 1 with hm
  have hn2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hm1 : 1 ≤ m := by omega
  have hc : c n = 2 ^ (2 * m) - 2 ^ m := by
    unfold c
    rw [show 2 ^ (n + 1) - 2 = 2 * m by rw [pow_succ]; omega]
  have hle : 2 ^ m ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ha : a n = Nat.count TB (2 ^ (2 * m) - 2 ^ m) := by
    unfold a A080300
    rw [hc, if_pos (TB_c m)]
  have hkey : Nat.count TB (2 ^ (2 * m)) = Nat.count TB (2 ^ (2 * m) - 2 ^ m) + 1 := by
    have e : 2 ^ (2 * m) = (2 ^ (2 * m) - 2 ^ m) + 2 ^ m := by omega
    conv_lhs => rw [e]
    rw [Nat.count_add]
    congr 1
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, htb⟩
      by_contra h0
      exact not_TB_cj m j hj (by omega) htb
    · rintro rfl
      exact ⟨by positivity, by simpa using TB_c m⟩
  have htot : Nat.count TB (2 ^ (2 * m)) = ∑ k ∈ Finset.range (m + 1), catalan k := by
    rw [Nat.count_eq_card_filter_range, card_TB_below]
  have hsum : ∑ k ∈ Finset.range (m + 1), catalan k =
      catalan 0 + ∑ k ∈ Finset.Icc 1 m, catalan k := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.Ico_add_one_right_eq_Icc]
  rw [catalan_zero] at hsum
  rw [ha]
  omega
