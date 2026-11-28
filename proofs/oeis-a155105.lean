import OMAStatements.S_oeis_a155105
import Mathlib

namespace OMA.P_oeis_a155105

open OMA.S_oeis_a155105

/-- The closed form of the nonzero entries. -/
def P (j : ℕ) : ℤ := ∏ i ∈ Finset.range j, ((3 : ℤ) * 2 ^ i + 1)

lemma P_succ (j : ℕ) : P (j + 1) = P j * (3 * 2 ^ j + 1) := by
  unfold P; rw [Finset.prod_range_succ]

lemma P_pos (j : ℕ) : 0 < P j := by
  unfold P; apply Finset.prod_pos; intro i _; positivity

/-- Column 3 for rows that are odd or below 6. -/
lemma B_three_of_not (n : ℕ) (h : ¬ (2 ∣ n ∧ 6 ≤ n)) :
    B n 3 = if n = 3 then 1 else 0 := by
  rw [B]
  have : ∑ k : Fin n, (if 3 ≤ (k : ℕ) then T n k * B k 3 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk := k.isLt
    split_ifs with h3
    · have : T n k = 0 := by
        unfold T
        rw [if_neg (by omega), if_neg]
        intro h2
        apply h
        constructor
        · exact ⟨k, h2⟩
        · omega
      rw [this, zero_mul]
    · rfl
  rw [this, sub_zero]

/-- Column 3 for even rows 2*m with m ≥ 3. -/
lemma B_three_double (m : ℕ) (hm : 3 ≤ m) :
    B (2 * m) 3 = ((m : ℤ) + 1) * B m 3 := by
  rw [B]
  have : ∑ k : Fin (2 * m), (if 3 ≤ (k : ℕ) then T (2 * m) k * B k 3 else 0)
      = -((m : ℤ) + 1) * B m 3 := by
    rw [Finset.sum_eq_single (⟨m, by omega⟩ : Fin (2 * m))]
    · simp only
      rw [if_pos hm]
      unfold T
      rw [if_neg (by omega), if_pos rfl]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ m := fun h => hk (Fin.ext h)
      have hlt := k.isLt
      split_ifs with h3
      · have : T (2 * m) k = 0 := by
          unfold T
          rw [if_neg (by omega), if_neg (by omega)]
        rw [this, zero_mul]
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [this, if_neg (by omega)]
  ring

lemma B_three_pow (j : ℕ) : B (3 * 2 ^ j) 3 = P j := by
  induction j with
  | zero =>
    rw [B_three_of_not _ (by norm_num)]
    simp [P]
  | succ j ih =>
    have h1 : 3 * 2 ^ (j + 1) = 2 * (3 * 2 ^ j) := by ring
    have h2 : 3 ≤ 3 * 2 ^ j := by
      have := Nat.one_le_two_pow (n := j); omega
    rw [h1, B_three_double _ h2, ih, P_succ]
    push_cast
    ring

lemma B_three_zero (n : ℕ) (h : ∀ j, n ≠ 3 * 2 ^ j) : B n 3 = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hc : 2 ∣ n ∧ 6 ≤ n
    · obtain ⟨⟨m, rfl⟩, h6⟩ := hc
      rw [B_three_double m (by omega), ih m (by omega), mul_zero]
      intro j hj
      apply h (j + 1)
      rw [hj]; ring
    · rw [B_three_of_not n hc, if_neg]
      intro h3
      exact h 0 (by simpa using h3)

lemma pos_iff (r : ℕ) : 0 < B r 3 ↔ r ∈ Set.range (fun j : ℕ => 3 * 2 ^ j) := by
  constructor
  · intro hr
    by_contra hn
    have : B r 3 = 0 := B_three_zero r (fun j hj => hn ⟨j, hj.symm⟩)
    omega
  · rintro ⟨j, rfl⟩
    simp only
    rw [B_three_pow]; exact P_pos j

lemma strictMono_f : StrictMono (fun j : ℕ => 3 * 2 ^ j) := by
  intro x y hxy
  have : 2 ^ x < 2 ^ y := Nat.pow_lt_pow_right (by norm_num) hxy
  simp only
  omega

lemma nth_eq (n : ℕ) : Nat.nth (fun r => 0 < B r 3) n = 3 * 2 ^ n := by
  have hinf : (Set.ofPred (fun r => 0 < B r 3)).Infinite := by
    have : Set.ofPred (fun r => 0 < B r 3) = Set.range (fun j : ℕ => 3 * 2 ^ j) := by
      ext r; exact pos_iff r
    rw [this]
    exact Set.infinite_range_of_injective strictMono_f.injective
  have key := Nat.nth_comp_of_strictMono (p := fun r => 0 < B r 3) (n := n) strictMono_f
    (fun k hk => (pos_iff k).1 hk) (fun hfi => absurd hfi hinf)
  rw [← key]
  have : (fun i : ℕ => 0 < B ((fun j : ℕ => 3 * 2 ^ j) i) 3) = fun _ => True := by
    funext i
    simp only [eq_iff_iff, iff_true]
    rw [B_three_pow]; exact P_pos i
  rw [this, Nat.nth_of_forall (fun _ _ => trivial)]

lemma a_eq (n : ℕ) : a n = P (n - 1) := by
  unfold a
  rw [nth_eq, B_three_pow]

lemma prod_eq (n : ℕ) :
    ∏ k ∈ Finset.Icc 1 n, ((1 : ℤ) + 3 * 2 ^ (k - 1)) = P n := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, P_succ]
    simp only [Nat.add_sub_cancel]
    ring

end OMA.P_oeis_a155105

theorem OMA.solution : type_of% @OMA.S_oeis_a155105.main := by
  open OMA.S_oeis_a155105 OMA.P_oeis_a155105 in
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [a_eq]; simp [P]
  · intro n hn
    rw [a_eq, a_eq]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have h1 : m + 2 - 1 = m + 1 := by omega
    have h2 : m + 1 - 1 = m := by omega
    have h3 : m + 2 - 2 = m := by omega
    rw [h1, h2, h3, P_succ]
    ring
  · intro n _
    rw [a_eq, prod_eq]
