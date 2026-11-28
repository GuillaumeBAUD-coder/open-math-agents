import OMAStatements.S_oeis_a011558
import Mathlib

/-!
# A011558: selections of distinct parts from 1, 2, 5, 10, 20, ...

Only the parts `1` and `2` are not divisible by 5, so `weight 5 p` determines the two flags
`p.one`, `p.two` from the residue modulo 5.  The remaining part of the weight is
`5 * (sum of distinct powers of two)`, i.e. the binary representation of `weight / 5`, which
exists and is unique.
-/

namespace OMA

open OMA.S_oeis_a011558

/-! ### The weight -/

private lemma weight_eq (p : Selection) :
    weight 5 p = p.one.toNat + 2 * p.two.toNat + 5 * ∑ j ∈ p.exponents, 2 ^ j := by
  simp only [weight]
  rw [← Finset.mul_sum]

private lemma small (p : Selection) : p.one.toNat + 2 * p.two.toNat ≤ 3 := by
  cases p.one <;> cases p.two <;> simp [Bool.toNat]

private lemma weight_mod_five (p : Selection) :
    weight 5 p % 5 = (p.one.toNat + 2 * p.two.toNat) % 5 := by
  rw [weight_eq]
  have hm : 5 * ∑ j ∈ p.exponents, 2 ^ j = (∑ j ∈ p.exponents, 2 ^ j) * 5 := by ring
  rw [hm]
  exact Nat.add_mul_mod_self_right _ _ _

private lemma flags_eq {p q : Selection} (h : weight 5 p = weight 5 q) :
    p.one = q.one ∧ p.two = q.two := by
  have hm : (p.one.toNat + 2 * p.two.toNat) % 5 = (q.one.toNat + 2 * q.two.toNat) % 5 := by
    rw [← weight_mod_five, ← weight_mod_five, h]
  have hp := small p
  have hq := small q
  rw [Nat.mod_eq_of_lt (by omega : p.one.toNat + 2 * p.two.toNat < 5),
      Nat.mod_eq_of_lt (by omega : q.one.toNat + 2 * q.two.toNat < 5)] at hm
  revert hm
  cases p.one <;> cases p.two <;> cases q.one <;> cases q.two <;>
    simp [Bool.toNat]

/-! ### Sums of distinct powers of two -/

/-- Shifting all exponents up by one doubles the sum. -/
private lemma sum_two_pow_shift (S : Finset ℕ) :
    ∑ j ∈ S.image Nat.succ, 2 ^ j = 2 * ∑ j ∈ S, 2 ^ j := by
  rw [Finset.sum_image (f := fun j => 2 ^ j) (g := Nat.succ)
    (fun a _ b _ h => by omega)]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [Nat.pow_succ]; ring)

/-- If no exponent is zero, the sum is twice the sum of the shifted-down exponents. -/
private lemma sum_two_pow_even (S : Finset ℕ) (h : ∀ j ∈ S, j ≠ 0) :
    ∑ j ∈ S, 2 ^ j = 2 * ∑ j ∈ S, 2 ^ (j - 1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj0 : j ≠ 0 := h j hj
  calc 2 ^ j = 2 ^ ((j - 1) + 1) := by rw [Nat.sub_one_add_one hj0]
    _ = 2 ^ (j - 1) * 2 := by rw [Nat.pow_succ]
    _ = 2 * 2 ^ (j - 1) := by ring

/-- The parity of the sum records whether the exponent zero is used. -/
private lemma sum_two_pow_mod_two (S : Finset ℕ) :
    (∑ j ∈ S, 2 ^ j) % 2 = if 0 ∈ S then 1 else 0 := by
  by_cases h0 : 0 ∈ S
  · have hsum := Finset.sum_erase_add S (fun j => 2 ^ j) h0
    have heven : ∑ j ∈ S.erase 0, 2 ^ j = 2 * ∑ j ∈ S.erase 0, 2 ^ (j - 1) :=
      sum_two_pow_even _ (fun j hj => Finset.ne_of_mem_erase hj)
    rw [if_pos h0, ← hsum, heven]
    simp only [pow_zero]
    omega
  · have heven : ∑ j ∈ S, 2 ^ j = 2 * ∑ j ∈ S, 2 ^ (j - 1) :=
      sum_two_pow_even _ (fun j hj hz => h0 (hz ▸ hj))
    rw [if_neg h0, heven, Nat.mul_mod_right]

/-- Deleting the exponent zero and shifting everything down by one. -/
private def predSet (S : Finset ℕ) : Finset ℕ := (S.erase 0).image (fun k => k - 1)

private lemma sum_two_pow_div_two (S : Finset ℕ) :
    (∑ j ∈ S, 2 ^ j) / 2 = ∑ j ∈ predSet S, 2 ^ j := by
  rw [predSet, Finset.sum_image (f := fun j => 2 ^ j) (g := fun k => k - 1)
    (fun a ha b hb hab => by
      have ha' : a ≠ 0 := Finset.ne_of_mem_erase ha
      have hb' : b ≠ 0 := Finset.ne_of_mem_erase hb
      have hab' : a - 1 = b - 1 := hab
      omega)]
  by_cases h0 : 0 ∈ S
  · have hsum := Finset.sum_erase_add S (fun j => 2 ^ j) h0
    have heven : ∑ j ∈ S.erase 0, 2 ^ j = 2 * ∑ j ∈ S.erase 0, 2 ^ (j - 1) :=
      sum_two_pow_even _ (fun j hj => Finset.ne_of_mem_erase hj)
    rw [← hsum, heven]
    simp only [pow_zero]
    omega
  · have herase : S.erase 0 = S := by
      ext x
      simp only [Finset.mem_erase]
      constructor
      · exact fun h => h.2
      · intro hx
        exact ⟨by rintro rfl; exact h0 hx, hx⟩
    have heven : ∑ j ∈ S, 2 ^ j = 2 * ∑ j ∈ S, 2 ^ (j - 1) :=
      sum_two_pow_even _ (fun j hj hz => h0 (hz ▸ hj))
    rw [herase, heven]
    omega

/-- `predSet` is inverted by `Nat.succ`. -/
private lemma succ_predSet (S : Finset ℕ) : (predSet S).image Nat.succ = S.erase 0 := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨k, hk, hk1⟩
    rw [Finset.mem_erase] at hk ⊢
    obtain ⟨hk0, hkS⟩ := hk
    have hky : Nat.succ y = k := by
      rw [← hk1]
      exact Nat.sub_one_add_one hk0
    rw [hky]
    exact ⟨hk0, hkS⟩
  · intro hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hx0, hxS⟩ := hx
    refine Finset.mem_image.mpr ⟨x - 1, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx0, hxS⟩, rfl⟩
    · exact Nat.sub_one_add_one hx0

/-! ### Existence and uniqueness of binary representations -/

private lemma eq_empty_of_sum_zero {S : Finset ℕ} (h : ∑ j ∈ S, 2 ^ j = 0) : S = ∅ := by
  by_contra hne
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hle := Finset.single_le_sum (f := fun j => 2 ^ j) (fun i _ => Nat.zero_le _) ha
  have hpos : 0 < 2 ^ a := pow_pos (by norm_num) a
  omega

private lemma exists_sum_two_pow : ∀ m : ℕ, ∃ S : Finset ℕ, ∑ j ∈ S, 2 ^ j = m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · exact ⟨∅, by simp [hm0]⟩
    · obtain ⟨S, hS⟩ := ih (m / 2) (Nat.div_lt_self hmpos (by norm_num))
      have hshift : ∑ j ∈ S.image Nat.succ, 2 ^ j = 2 * (m / 2) := by
        rw [sum_two_pow_shift, hS]
      by_cases hodd : m % 2 = 1
      · refine ⟨insert 0 (S.image Nat.succ), ?_⟩
        have hnot : (0 : ℕ) ∉ S.image Nat.succ := by
          intro h
          rcases Finset.mem_image.mp h with ⟨k, _, hk⟩
          omega
        rw [Finset.sum_insert hnot, hshift]
        simp only [pow_zero]
        omega
      · refine ⟨S.image Nat.succ, ?_⟩
        rw [hshift]
        omega

private lemma sum_two_pow_inj_aux : ∀ m : ℕ, ∀ S T : Finset ℕ,
    ∑ j ∈ S, 2 ^ j = m → ∑ j ∈ T, 2 ^ j = m → S = T := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S T hS hT
    have hpar : (if 0 ∈ S then 1 else 0) = (if 0 ∈ T then 1 else 0) := by
      rw [← sum_two_pow_mod_two S, ← sum_two_pow_mod_two T, hS, hT]
    have hmem : (0 ∈ S) ↔ (0 ∈ T) := by
      constructor
      · intro h1
        by_contra h2
        rw [if_pos h1, if_neg h2] at hpar
        omega
      · intro h2
        by_contra h1
        rw [if_neg h1, if_pos h2] at hpar
        omega
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hS0 : S = ∅ := eq_empty_of_sum_zero (by rw [hS, hm0])
      have hT0 : T = ∅ := eq_empty_of_sum_zero (by rw [hT, hm0])
      rw [hS0, hT0]
    · have hlt : m / 2 < m := Nat.div_lt_self hmpos (by norm_num)
      have hpred : predSet S = predSet T := by
        refine ih (m / 2) hlt (predSet S) (predSet T) ?_ ?_
        · rw [← sum_two_pow_div_two, hS]
        · rw [← sum_two_pow_div_two, hT]
      have herase : S.erase 0 = T.erase 0 := by
        rw [← succ_predSet S, ← succ_predSet T, hpred]
      ext x
      by_cases hx : x = 0
      · subst hx
        exact hmem
      · have h' : x ∈ S.erase 0 ↔ x ∈ T.erase 0 := by rw [herase]
        simpa [Finset.mem_erase, hx] using h'

private lemma sum_two_pow_inj (S T : Finset ℕ)
    (h : ∑ j ∈ S, 2 ^ j = ∑ j ∈ T, 2 ^ j) : S = T :=
  sum_two_pow_inj_aux (∑ j ∈ S, 2 ^ j) S T rfl h.symm

/-! ### The weight determines the selection -/

private lemma weight_inj {p q : Selection} (h : weight 5 p = weight 5 q) : p = q := by
  obtain ⟨h1, h2⟩ := flags_eq h
  have hsum : ∑ j ∈ p.exponents, 2 ^ j = ∑ j ∈ q.exponents, 2 ^ j := by
    have hp := weight_eq p
    have hq := weight_eq q
    rw [hp, hq, h1, h2] at h
    have h5 : 5 * ∑ j ∈ p.exponents, 2 ^ j = 5 * ∑ j ∈ q.exponents, 2 ^ j := by omega
    exact Nat.mul_left_cancel (by norm_num : 0 < 5) h5
  have hexp := sum_two_pow_inj p.exponents q.exponents hsum
  cases p with
  | mk p1 p2 pe =>
    cases q with
    | mk q1 q2 qe =>
      simp only at h1 h2 hexp
      subst h1
      subst h2
      subst hexp
      rfl

private lemma flags_toNat (c : ℕ) (hc : c ≤ 3) :
    (decide (c % 2 = 1)).toNat + 2 * (decide (2 ≤ c)).toNat = c := by
  interval_cases c <;> decide

/-! ### The statement -/

private theorem key : ∀ n : ℕ, a (n + 1) = ({p : Selection | weight 5 p = n} : Set Selection).ncard := by
  intro n
  obtain ⟨S, hS⟩ := exists_sum_two_pow (n / 5)
  have hmod : n % 5 + 5 * (n / 5) = n := Nat.mod_add_div n 5
  have hr : n % 5 < 5 := Nat.mod_lt n (by norm_num)
  have ha : a (n + 1) = (if (n + 1) % 5 = 0 then 0 else 1) := rfl
  by_cases h4 : n % 5 = 4
  · have hempty : {p : Selection | weight 5 p = n} = (∅ : Set Selection) := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hp
      have hm := weight_mod_five p
      rw [hp, h4] at hm
      have hle := small p
      rw [Nat.mod_eq_of_lt (by omega : p.one.toNat + 2 * p.two.toNat < 5)] at hm
      omega
    have hz : (n + 1) % 5 = 0 := by omega
    rw [ha, if_pos hz, hempty, Set.ncard_empty]
  · have hflags : (decide (n % 5 % 2 = 1)).toNat + 2 * (decide (2 ≤ n % 5)).toNat = n % 5 :=
      flags_toNat (n % 5) (by omega)
    have hmem : weight 5 (⟨decide (n % 5 % 2 = 1), decide (2 ≤ n % 5), S⟩ : Selection) = n := by
      have hw : weight 5 (⟨decide (n % 5 % 2 = 1), decide (2 ≤ n % 5), S⟩ : Selection)
          = (decide (n % 5 % 2 = 1)).toNat + 2 * (decide (2 ≤ n % 5)).toNat
            + 5 * ∑ j ∈ S, 2 ^ j := weight_eq _
      rw [hw, hS]
      omega
    have hsub : ∀ p q : Selection, weight 5 p = n → weight 5 q = n → p = q := by
      intro p q hp hq
      exact weight_inj (by rw [hp, hq])
    have hset : {p : Selection | weight 5 p = n}
        = {⟨decide (n % 5 % 2 = 1), decide (2 ≤ n % 5), S⟩} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hp
        exact hsub p _ hp hmem
      · intro hp
        rw [hp]
        exact hmem
    have hnz : ¬ (n + 1) % 5 = 0 := by omega
    rw [ha, if_neg hnz, hset, Set.ncard_singleton]

end OMA

theorem OMA.solution : type_of% @OMA.S_oeis_a011558.main := OMA.key
