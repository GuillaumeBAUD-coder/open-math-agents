import OMAStatements.S_oeis_a265283
import Mathlib

namespace R265283
open OMA.S_oeis_a265283

theorem rule94_eq (l c r : Bool) : rule94 l c r = ((l || c || r) && !(l && r)) := by
  cases l <;> cases c <;> cases r <;> first | rfl | decide | simp [rule94]

theorem rule_iff (x y z : Bool) (A B C : Prop) (hx : x = true ↔ A) (hy : y = true ↔ B)
    (hz : z = true ↔ C) : rule94 x y z = true ↔ ((A ∨ B ∨ C) ∧ ¬(A ∧ C)) := by
  rw [rule94_eq, ← hx, ← hy, ← hz]
  cases x <;> cases y <;> cases z <;> first | decide | simp

/-- Closed form of generation `N`: `|i| ≤ N` and (`|i| ≥ N - 1` or `i` odd). -/
def Q (N i : ℤ) : Prop := -N ≤ i ∧ i ≤ N ∧ (N - 1 ≤ i ∨ i ≤ 1 - N ∨ i % 2 = 1)

set_option maxHeartbeats 2000000 in
theorem fwdA (N i : ℤ) (hN : 0 ≤ N) (hA : Q N (i - 1)) (hC : ¬Q N (i + 1)) :
    Q (N + 1) i := by
  unfold Q at hA hC ⊢
  omega

set_option maxHeartbeats 2000000 in
theorem fwdB1 (N i : ℤ) (hN : 0 ≤ N) (hB : Q N i) (hA : ¬Q N (i - 1)) : Q (N + 1) i := by
  unfold Q at hA hB ⊢
  omega

set_option maxHeartbeats 2000000 in
theorem fwdB2 (N i : ℤ) (hN : 0 ≤ N) (hB : Q N i) (hC : ¬Q N (i + 1)) : Q (N + 1) i := by
  unfold Q at hB hC ⊢
  omega

set_option maxHeartbeats 2000000 in
theorem fwdC (N i : ℤ) (hN : 0 ≤ N) (hC : Q N (i + 1)) (hA : ¬Q N (i - 1)) :
    Q (N + 1) i := by
  unfold Q at hA hC ⊢
  omega

set_option maxHeartbeats 2000000 in
theorem bwd1 (N i : ℤ) (hN : 0 ≤ N) (hD : Q (N + 1) i) :
    Q N (i - 1) ∨ Q N i ∨ Q N (i + 1) := by
  unfold Q at hD ⊢
  omega

set_option maxHeartbeats 2000000 in
theorem bwd2 (N i : ℤ) (hN : 0 ≤ N) (hD : Q (N + 1) i) (hA : Q N (i - 1))
    (hC : Q N (i + 1)) : False := by
  unfold Q at hD hA hC
  omega

theorem step_prop (N i : ℤ) (hN : 0 ≤ N) :
    ((Q N (i - 1) ∨ Q N i ∨ Q N (i + 1)) ∧ ¬(Q N (i - 1) ∧ Q N (i + 1))) ↔ Q (N + 1) i := by
  constructor
  · rintro ⟨hA | hB | hC, h⟩
    · exact fwdA N i hN hA (fun hC => h ⟨hA, hC⟩)
    · by_cases hA : Q N (i - 1)
      · exact fwdB2 N i hN hB (fun hC => h ⟨hA, hC⟩)
      · exact fwdB1 N i hN hB hA
    · exact fwdC N i hN hC (fun hA => h ⟨hA, hC⟩)
  · intro hD
    exact ⟨bwd1 N i hN hD, fun hAC => bwd2 N i hN hD hAC.1 hAC.2⟩

theorem ca_iff (n : ℕ) : ∀ i : ℤ, ca n i = true ↔ Q (n : ℤ) i := by
  induction n with
  | zero =>
    intro i
    show decide (i = 0) = true ↔ Q 0 i
    rw [decide_eq_true_iff]
    unfold Q
    omega
  | succ n ih =>
    intro i
    show rule94 (ca n (i - 1)) (ca n i) (ca n (i + 1)) = true ↔ Q ((n + 1 : ℕ) : ℤ) i
    rw [rule_iff _ _ _ _ _ _ (ih (i - 1)) (ih i) (ih (i + 1)), Nat.cast_add_one]
    exact step_prop (n : ℤ) i (by omega)

/-- Number of ON cells among the first `m` positions `k - n`, `k < m`. -/
def S (n m : ℕ) : ℕ :=
  (Finset.range m).sum (fun k => if ca n ((k : ℤ) - (n : ℤ)) = true then 1 else 0)

theorem S_zero (n : ℕ) : S n 0 = 0 := by
  simp [S]

theorem S_succ (n m : ℕ) :
    S n (m + 1) = S n m + (if ca n ((m : ℤ) - (n : ℤ)) = true then 1 else 0) := by
  unfold S
  exact Finset.sum_range_succ _ _

theorem S_formula (n : ℕ) (hn : 2 ≤ n) :
    ∀ m, m ≤ 2 * n - 1 → S n m = (m + n % 2) / 2 + min (m - n % 2) 1 := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [S_zero]
    omega
  | succ m ih =>
    intro hm
    rw [S_succ, ih (by omega)]
    split_ifs with h
    · rw [ca_iff] at h
      unfold Q at h
      omega
    · first | rw [ca_iff] at h | rw [← Bool.not_eq_true, ca_iff] at h
      unfold Q at h
      omega

theorem a_val (n : ℕ) (hn : 2 ≤ n) : a n = n + 2 + n % 2 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega⟩
  have h1 : a n = S n (2 * n + 1) := by
    unfold a S
    exact Finset.card_filter _ _
  have h2 : 2 * n + 1 = k + 1 + 1 := by omega
  rw [h1, h2, S_succ, S_succ, S_formula n hn k (by omega)]
  split_ifs <;> simp only [ca_iff, Q] at * <;> omega

end R265283

theorem OMA.solution : type_of% @OMA.S_oeis_a265283.main := by
  intro n hn
  have ha := R265283.a_val n (by omega)
  rcases Nat.even_or_odd n with he | ho
  · rw [Even.neg_one_pow he, ha]
    obtain ⟨r, hr⟩ := he
    push_cast
    omega
  · rw [Odd.neg_one_pow ho, ha]
    obtain ⟨r, hr⟩ := ho
    push_cast
    omega
