import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3
import Mathlib

/-!
# Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H1.R3

First crossing of a dyadic density threshold. Write R = r 3. Since 1 <= R N <= N, put
m = log_2 (N / R N), so that 2^m R N <= N < 2^(m+1) R N. Let n be the least positive integer with
2^m R n <= n; then n <= N and every smaller positive j has j < 2^m R j. Equality 2^m R n = n holds
because either n = 1, or n - 1 < 2^m R (n - 1) <= 2^m R n by monotonicity. The last inequality
n r k N <= 2 N r k n is interpolation from subadditivity: N <= q n <= 2 N for q = N / n + 1 and
r k (q n) <= q r k n. Monotonicity, subadditivity and card_le_maxCard are taken from reduction R2.
-/

namespace FirstCross

open OMA.R_Erdos142_erdos_142_variants_lower_R2

lemma maxCard_le (k N : ℕ) : Set.IsAPOfLengthFree.maxCard k N ≤ N := by
  unfold Set.IsAPOfLengthFree.maxCard
  apply csSup_le'
  rintro _ ⟨S, hS, _, rfl⟩
  simpa using Finset.card_le_card hS

lemma one_le_maxCard_three {N : ℕ} (hN : 0 < N) : 1 ≤ Set.IsAPOfLengthFree.maxCard 3 N := by
  have hsub : ({1} : Finset ℕ) ⊆ Finset.Icc 1 N := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hfree : ((({1} : Finset ℕ) : Set ℕ)).IsAPOfLengthFree ((3 : ℕ) : ℕ∞) := by
    intro t ht hAP
    have hle : t.encard ≤ 1 := (Set.encard_mono ht).trans (by simp)
    rw [← hAP.card]
    exact hle
  simpa using card_le_maxCard hsub hfree

lemma mul_le (k M : ℕ) : ∀ q : ℕ, 1 ≤ q →
    Set.IsAPOfLengthFree.maxCard k (q * M) ≤ q * Set.IsAPOfLengthFree.maxCard k M := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ q _ ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact (maxCard_add_le k (q * M) M).trans (Nat.add_le_add_right ih _)

lemma interp (k : ℕ) {M X : ℕ} (hM : 0 < M) (hMX : M ≤ X) :
    M * Set.IsAPOfLengthFree.maxCard k X ≤ 2 * X * Set.IsAPOfLengthFree.maxCard k M := by
  have hXq : X ≤ (X / M + 1) * M := by
    have := Nat.lt_div_mul_add (a := X) hM
    rw [add_mul, one_mul]
    omega
  have hqM : (X / M + 1) * M ≤ 2 * X := by
    have := Nat.div_mul_le_self X M
    rw [add_mul, one_mul]
    omega
  have h1 := (maxCard_monotone k hXq).trans (mul_le k M (X / M + 1) (Nat.le_add_left 1 _))
  calc M * Set.IsAPOfLengthFree.maxCard k X
      ≤ M * ((X / M + 1) * Set.IsAPOfLengthFree.maxCard k M) := Nat.mul_le_mul_left _ h1
    _ = ((X / M + 1) * M) * Set.IsAPOfLengthFree.maxCard k M := by ring
    _ ≤ 2 * X * Set.IsAPOfLengthFree.maxCard k M := Nat.mul_le_mul_right _ hqM

theorem first_crossing (k N : ℕ) (hN : 0 < N) : ∃ m n : ℕ, 0 < n ∧ n ≤ N ∧
    2 ^ m * Set.IsAPOfLengthFree.maxCard 3 n = n ∧
    (∀ j, 0 < j → j < n → j < 2 ^ m * Set.IsAPOfLengthFree.maxCard 3 j) ∧
    N < 2 ^ (m + 1) * Set.IsAPOfLengthFree.maxCard 3 N ∧
    n * Set.IsAPOfLengthFree.maxCard k N ≤ 2 * N * Set.IsAPOfLengthFree.maxCard k n := by
  classical
  have hR1 : 1 ≤ Set.IsAPOfLengthFree.maxCard 3 N := one_le_maxCard_three hN
  have hRN : Set.IsAPOfLengthFree.maxCard 3 N ≤ N := maxCard_le 3 N
  have hdiv : 0 < N / Set.IsAPOfLengthFree.maxCard 3 N := Nat.div_pos hRN (by omega)
  have hlow : 2 ^ Nat.log 2 (N / Set.IsAPOfLengthFree.maxCard 3 N) *
      Set.IsAPOfLengthFree.maxCard 3 N ≤ N :=
    (Nat.le_div_iff_mul_le (by omega)).mp (Nat.pow_log_le_self 2 hdiv.ne')
  have hup : N < 2 ^ (Nat.log 2 (N / Set.IsAPOfLengthFree.maxCard 3 N) + 1) *
      Set.IsAPOfLengthFree.maxCard 3 N :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_pow_succ_log_self (by norm_num) _)
  have hex : ∃ n, 0 < n ∧ 2 ^ Nat.log 2 (N / Set.IsAPOfLengthFree.maxCard 3 N) *
      Set.IsAPOfLengthFree.maxCard 3 n ≤ n := ⟨N, hN, hlow⟩
  have hnN : Nat.find hex ≤ N := Nat.find_min' hex ⟨hN, hlow⟩
  have hpos := (Nat.find_spec hex).1
  refine ⟨_, Nat.find hex, hpos, hnN, ?_, ?_, hup, interp k hpos hnN⟩
  · apply le_antisymm (Nat.find_spec hex).2
    by_cases h1 : Nat.find hex = 1
    · rw [h1]
      have h3 := one_le_maxCard_three (N := 1) one_pos
      have h4 : 1 ≤ 2 ^ Nat.log 2 (N / Set.IsAPOfLengthFree.maxCard 3 N) := Nat.one_le_two_pow
      nlinarith
    · have hj := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      have hlt : Nat.find hex - 1 < 2 ^ Nat.log 2 (N / Set.IsAPOfLengthFree.maxCard 3 N) *
          Set.IsAPOfLengthFree.maxCard 3 (Nat.find hex - 1) := by
        by_contra h
        exact hj ⟨by omega, not_lt.mp h⟩
      have hmono := Nat.mul_le_mul_left (2 ^ Nat.log 2 (N / Set.IsAPOfLengthFree.maxCard 3 N))
        (maxCard_monotone 3 (Nat.sub_le (Nat.find hex) 1))
      omega
  · intro j hj0 hjn
    by_contra h
    exact Nat.find_min hex hjn ⟨hj0, not_lt.mp h⟩

end FirstCross

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3.H2 :=
  fun k N hN => FirstCross.first_crossing k N hN
