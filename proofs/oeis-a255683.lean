import OMAStatements.S_oeis_a255683

-- Problem: A255683: Sum of the binary numbers whose digits are cyclic permutations of the binary expansion of n.
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a255683.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a255683

open OMA.S_oeis_a255683

private lemma sum_pow_two_range (L : ℕ) :
    ∑ j ∈ Finset.range L, 2 ^ j = 2 ^ L - 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h1 : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by norm_num)
    omega

private lemma list_sum_eq_fin_sum (l : List ℕ) :
    l.sum = ∑ k : Fin l.length, l[k] := by
  induction l with
  | nil => simp
  | cons d t ih =>
    rw [List.sum_cons, ih]
    simp only [List.length_cons, Fin.sum_univ_succ]
    rfl

private lemma ofDigits_two_eq_sum (m : List ℕ) :
    Nat.ofDigits 2 m = ∑ j : Fin m.length, m[j] * 2 ^ (j : ℕ) := by
  induction m with
  | nil => simp [Nat.ofDigits]
  | cons d t ih =>
    rw [Nat.ofDigits_cons, ih]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
      List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    change 2 * (t[j.1] * 2 ^ j.1) = t[j.1] * 2 ^ (j.1 + 1)
    rw [pow_succ']
    ring

private lemma sum_ofDigits_rotate (l : List ℕ) :
    ∑ r ∈ Finset.range l.length, Nat.ofDigits 2 (l.rotate r) = (2 ^ l.length - 1) * l.sum := by
  by_cases hlen : l.length = 0
  · have hl : l = [] := List.eq_nil_of_length_eq_zero hlen
    subst hl
    simp
  · have hLpos : 0 < l.length := Nat.pos_of_ne_zero hlen
    haveI : NeZero l.length := ⟨hlen⟩
    rw [← Fin.sum_univ_eq_sum_range (fun r => Nat.ofDigits 2 (l.rotate r))]
    have hrot : ∀ r : Fin l.length,
        Nat.ofDigits 2 (l.rotate r) =
          ∑ j : Fin l.length, l[(j + r : Fin l.length).val] * 2 ^ (j : ℕ) := by
      intro r
      rw [ofDigits_two_eq_sum]
      refine Finset.sum_bij (fun (j : Fin (l.rotate r).length) _ =>
          (⟨j.1, by simpa using j.2⟩ : Fin l.length)) ?_ ?_ ?_ ?_
      · intro j _; exact Finset.mem_univ _
      · intro j₁ _ j₂ _ h
        exact Fin.ext (by simpa using congrArg Fin.val h)
      · intro j _
        exact ⟨⟨j.1, by simpa using j.2⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro j _
        change (l.rotate r.1)[j.1]'(j.2) * 2 ^ j.1 =
          l[(j.1 + r.1) % l.length]'(Nat.mod_lt _ hLpos) * 2 ^ j.1
        rw [List.getElem_rotate]
    simp_rw [hrot]
    rw [Finset.sum_comm]
    have hinner : ∀ j : Fin l.length,
        (∑ r : Fin l.length, l[(j + r : Fin l.length).val] * 2 ^ (j : ℕ)) =
          l.sum * 2 ^ (j : ℕ) := by
      intro j
      rw [← Finset.sum_mul, list_sum_eq_fin_sum]
      congr 1
      exact Equiv.sum_comp (Equiv.addLeft j) (fun k : Fin l.length => l[k.val])
    simp_rw [hinner]
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => 2 ^ j), sum_pow_two_range, mul_comm]

private lemma digits_two_pow_sub_one_sum (k : ℕ) :
    (Nat.digits 2 (2 ^ k - 1)).sum = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 2 ^ (k + 1) - 1 := by
      have : 2 ≤ 2 ^ (k + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have hmod : (2 ^ (k + 1) - 1) % 2 = 1 := by
      rw [pow_succ]
      omega
    have hdiv : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by
      rw [pow_succ]
      omega
    rw [Nat.digits_def' (by norm_num) hpos, hmod, hdiv, List.sum_cons, ih]
    omega

private lemma digits_two_add_pow_sum :
    ∀ k j : ℕ, j < 2 ^ k → (Nat.digits 2 (2 ^ k + j)).sum = 1 + (Nat.digits 2 j).sum := by
  intro k
  induction k with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    norm_num
  | succ k ih =>
    intro j hj
    have hpos : 0 < 2 ^ (k + 1) + j := by positivity
    have hmod : (2 ^ (k + 1) + j) % 2 = j % 2 := by
      rw [pow_succ]
      omega
    have hdiv : (2 ^ (k + 1) + j) / 2 = 2 ^ k + j / 2 := by
      rw [pow_succ]
      omega
    have hjdiv : j / 2 < 2 ^ k := by
      rw [pow_succ] at hj
      omega
    rw [Nat.digits_def' (by norm_num) hpos, hmod, hdiv, List.sum_cons, ih (j / 2) hjdiv]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp
    · rw [Nat.digits_def' (by norm_num) hjpos, List.sum_cons]
      omega

private lemma b_eq_succ_digits_sum (m : ℕ) (hm : 1 ≤ m) :
    b m = 1 + (Nat.digits 2 (m - 1)).sum := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hm0 : m ≠ 0 := by omega
    rw [b]
    simp only [hm0, ↓reduceDIte]
    set k := Nat.log 2 m with hk_def
    have hle : 2 ^ k ≤ m := Nat.pow_log_le_self 2 hm0
    have hlt : m < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    by_cases heq : m = 2 ^ k
    · simp only [heq, ↓reduceIte]
      rw [digits_two_pow_sub_one_sum]
      omega
    · simp only [heq, ↓reduceIte]
      set r := m - 2 ^ k with hr_def
      have hr_pos : 1 ≤ r := by omega
      have hr_lt_m : r < m := by
        have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
        omega
      have hr_lt_pow : r - 1 < 2 ^ k := by
        rw [pow_succ] at hlt
        omega
      rw [ih r hr_lt_m hr_pos]
      have hm1 : m - 1 = 2 ^ k + (r - 1) := by omega
      rw [hm1, digits_two_add_pow_sum k (r - 1) hr_lt_pow]

private lemma digits_two_length_pow_add (n i : ℕ) (hi : i ≤ 2 ^ n - 1) :
    (Nat.digits 2 (2 ^ n + i)).length = n + 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hne : 2 ^ n + i ≠ 0 := by omega
  rw [Nat.digits_len 2 (2 ^ n + i) (by norm_num) hne]
  have hlog : Nat.log 2 (2 ^ n + i) = n := by
    rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, hne⟩)]
    constructor
    · omega
    · rw [pow_succ]
      omega
  rw [hlog]

theorem main_proof : ∀ n i : ℕ, i ≤ 2 ^ n - 1 → a (2 ^ n + i) = (2 ^ (n + 1) - 1) * b (i + 1) := by
  intro n i hi
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hi_lt : i < 2 ^ n := by omega
  unfold a
  rw [sum_ofDigits_rotate, digits_two_length_pow_add n i hi,
    digits_two_add_pow_sum n i hi_lt, b_eq_succ_digits_sum (i + 1) (by omega)]
  simp

end OMA.Proof_oeis_a255683

theorem OMA.solution : type_of% @OMA.S_oeis_a255683.main :=
  OMA.Proof_oeis_a255683.main_proof
