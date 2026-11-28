import OMAStatements.S_oeis_a238806
import Mathlib

open OMA.S_oeis_a238806 PowerSeries Finset

namespace P238806

def gC (c : Fin 2 → Fin 3) {n : ℕ} (x : Fin n → Fin 2 → Fin 3) : Prop :=
  ∀ i j, (x i j : ℕ) ≠ (1 + leftSum x i j) % 3 ∧ (x i j : ℕ) ≠ (1 + (c j : ℕ) + aboveSum x i j) % 3

instance (c : Fin 2 → Fin 3) (n : ℕ) : DecidablePred (@gC c n) := fun x => by
  unfold gC; infer_instance

def rowok (c r : Fin 2 → Fin 3) : Prop :=
  ∀ j, (r j : ℕ) ≠ (1 + ∑ j' ∈ univ.filter (· < j), (r j' : ℕ)) % 3 ∧ (r j : ℕ) ≠ (1 + (c j : ℕ)) % 3

instance (c r : Fin 2 → Fin 3) : Decidable (rowok c r) := by unfold rowok; infer_instance

lemma L1 {n : ℕ} (r : Fin 2 → Fin 3) (x : Fin n → Fin 2 → Fin 3) (j : Fin 2) :
    leftSum (Fin.cons r x : Fin (n + 1) → Fin 2 → Fin 3) 0 j = ∑ j' ∈ univ.filter (· < j), (r j' : ℕ) := by
  simp only [leftSum, Fin.cons_zero]

lemma L2 {n : ℕ} (r : Fin 2 → Fin 3) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) :
    leftSum (Fin.cons r x : Fin (n + 1) → Fin 2 → Fin 3) i.succ j = leftSum x i j := by
  simp only [leftSum, Fin.cons_succ]

lemma L3 {n : ℕ} (r : Fin 2 → Fin 3) (x : Fin n → Fin 2 → Fin 3) (j : Fin 2) :
    aboveSum (Fin.cons r x : Fin (n + 1) → Fin 2 → Fin 3) 0 j = 0 := by
  simp [aboveSum]

lemma L4 {n : ℕ} (r : Fin 2 → Fin 3) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) :
    aboveSum (Fin.cons r x : Fin (n + 1) → Fin 2 → Fin 3) i.succ j = (r j : ℕ) + aboveSum x i j := by
  unfold aboveSum
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp [Fin.succ_lt_succ_iff, Fin.succ_pos]

lemma L5 {n : ℕ} (c r : Fin 2 → Fin 3) (x : Fin n → Fin 2 → Fin 3) :
    gC c (Fin.cons r x : Fin (n + 1) → Fin 2 → Fin 3) ↔ rowok c r ∧ gC (c + r) x := by
  have key : ∀ j (s : ℕ), (1 + (((c + r) j : Fin 3) : ℕ) + s) % 3 = (1 + (c j : ℕ) + ((r j : ℕ) + s)) % 3 := by
    intro j s; rw [Pi.add_apply, Fin.val_add]; omega
  unfold gC rowok
  rw [Fin.forall_fin_succ]
  simp only [L1, L2, L3, L4, Fin.cons_zero, Fin.cons_succ, add_zero, key]

def K (n : ℕ) (c : Fin 2 → Fin 3) : ℕ := ((univ : Finset (Fin n → Fin 2 → Fin 3)).filter (gC c)).card

lemma sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 2 → Fin 3) → ℕ) :
    ∑ y, F y = ∑ v : Fin 2 → Fin 3, ∑ z : Fin n → Fin 2 → Fin 3, F (Fin.cons v z) := by
  rw [← (Fin.consEquiv (fun _ => Fin 2 → Fin 3)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma K_succ (n : ℕ) (c : Fin 2 → Fin 3) :
    K (n + 1) c = ∑ r : Fin 2 → Fin 3, if rowok c r then K n (c + r) else 0 := by
  rw [K, Finset.card_filter, sum_cons]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : rowok c r
  · rw [if_pos hr, K, Finset.card_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [L5, hr, true_and]
  · rw [if_neg hr]
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [L5, hr]

lemma K_zero (c : Fin 2 → Fin 3) : K 0 c = 1 := by
  rw [K, Finset.card_eq_one]
  refine ⟨fun i => i.elim0, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro _; funext i; exact i.elim0
  · intro _ i; exact i.elim0

def K2 (n : ℕ) (a b : Fin 3) : ℕ := K n ![a, b]

lemma sumC (g : (Fin 2 → Fin 3) → ℕ) : ∑ s, g s = ∑ a : Fin 3, ∑ b : Fin 3, g ![a, b] := by
  have e : ∀ a b : Fin 3, (piFinTwoEquiv fun _ => Fin 3).symm (a, b) = ![a, b] := by
    intro a b; funext i; fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp, Fintype.sum_prod_type]
  simp only [e]

lemma vadd (a b c d : Fin 3) : (![a, b] + ![c, d] : Fin 2 → Fin 3) = ![a + c, b + d] := by
  funext i; fin_cases i <;> rfl

lemma K2_succ (n : ℕ) (a b : Fin 3) :
    K2 (n + 1) a b = ∑ c : Fin 3, ∑ d : Fin 3, if rowok ![a, b] ![c, d] then K2 n (a + c) (b + d) else 0 := by
  rw [K2, K_succ, sumC]
  simp only [vadd, K2]

lemma R00 (n : ℕ) : K2 (n + 1) 0 0 = K2 n 0 0 + K2 n 0 2 + K2 n 2 2 := by
  rw [K2_succ]
  simp [Fin.sum_univ_three, rowok, Finset.sum_filter, Fin.sum_univ_two]

lemma R01 (n : ℕ) : K2 (n + 1) 0 1 = K2 n 0 1 + K2 n 2 2 := by
  rw [K2_succ]
  simp [Fin.sum_univ_three, rowok, Finset.sum_filter, Fin.sum_univ_two]

lemma R02 (n : ℕ) : K2 (n + 1) 0 2 = K2 n 0 1 + K2 n 2 0 + K2 n 2 1 := by
  rw [K2_succ]
  simp [Fin.sum_univ_three, rowok, Finset.sum_filter, Fin.sum_univ_two, add_assoc]

lemma R10 (n : ℕ) : K2 (n + 1) 1 0 = K2 n 1 0 + K2 n 1 2 := by
  rw [K2_succ]
  simp [Fin.sum_univ_three, rowok, Finset.sum_filter, Fin.sum_univ_two]

lemma R11 (n : ℕ) : K2 (n + 1) 1 1 = K2 n 1 1 := by
  rw [K2_succ]
  simp [Fin.sum_univ_three, rowok, Finset.sum_filter, Fin.sum_univ_two]

lemma R12 (n : ℕ) : K2 (n + 1) 1 2 = K2 n 1 1 := by
  rw [K2_succ]
  simp [Fin.sum_univ_three, rowok, Finset.sum_filter, Fin.sum_univ_two]

lemma R20 (n : ℕ) : K2 (n + 1) 2 0 = K2 n 1 2 := by
  rw [K2_succ]
  simp [Fin.sum_univ_three, rowok, Finset.sum_filter, Fin.sum_univ_two]

lemma R21 (n : ℕ) : K2 (n + 1) 2 1 = K2 n 1 2 := by
  rw [K2_succ]
  simp [Fin.sum_univ_three, rowok, Finset.sum_filter, Fin.sum_univ_two]

lemma R22 (n : ℕ) : K2 (n + 1) 2 2 = K2 n 1 0 + K2 n 1 1 := by
  rw [K2_succ]
  simp [Fin.sum_univ_three, rowok, Finset.sum_filter, Fin.sum_univ_two]

lemma C1 (n : ℕ) : K2 n 1 1 = 1 ∧ K2 n 1 2 = 1 ∧ K2 n 2 0 = 1 ∧ K2 n 2 1 = 1 := by
  induction n with
  | zero => simp [K2, K_zero]
  | succ n ih => rw [R11, R12, R20, R21]; exact ⟨ih.1, ih.1, ih.2.1, ih.2.1⟩

lemma C2 (n : ℕ) : K2 n 1 0 = n + 1 ∧ K2 n 2 2 = n + 1 := by
  induction n with
  | zero => simp [K2, K_zero]
  | succ n ih => rw [R10, R22, ih.1, (C1 n).2.1, (C1 n).1]; omega

lemma C3 (n : ℕ) : (K2 n 0 1 : ℚ) = 1 + n * (n + 1) / 2 := by
  induction n with
  | zero => simp [K2, K_zero]
  | succ n ih => rw [R01]; push_cast; rw [ih, (C2 n).2]; push_cast; ring

lemma C4 (m : ℕ) : (K2 (m + 1) 0 2 : ℚ) = 3 + m * (m + 1) / 2 := by
  rw [R02]; push_cast; rw [C3, (C1 m).2.2.1, (C1 m).2.2.2]; push_cast; ring

lemma C5 (m : ℕ) : (K2 (m + 1) 0 0 : ℚ) = 3 + 5 * m + m * (m - 1) / 2 + (m - 1) * m * (m + 1) / 6 := by
  induction m with
  | zero => rw [R00]; simp [K2, K_zero]
  | succ m ih =>
    rw [R00]; push_cast; rw [ih, C4, (C2 (m + 1)).2]; push_cast; ring

lemma a_eq (n : ℕ) : a n = K2 n 0 0 := by
  have h0 : (![0, 0] : Fin 2 → Fin 3) = 0 := by funext i; fin_cases i <;> rfl
  rw [K2, K, h0, a]
  congr 1

end P238806

open P238806 in
theorem OMA.solution : type_of% @OMA.S_oeis_a238806.main := by
  have hA : ∀ m : ℕ, (a (m + 1) : ℚ) = 3 + 5 * m + m * (m - 1) / 2 + (m - 1) * m * (m + 1) / 6 := by
    intro m; rw [a_eq, C5]
  refine ⟨?_, ?_⟩
  · have hq : ∀ F : PowerSeries ℚ, F * (1 - X) ^ 4 = F - F * X ^ 1 * C 4 + F * X ^ 2 * C 6 - F * X ^ 3 * C 4 + F * X ^ 4 := by
      intro F; simp only [map_ofNat, pow_one]; ring
    have hr : (3 - 4 * X + X ^ 2 + X ^ 3 : PowerSeries ℚ) = C 3 - X ^ 1 * C 4 + X ^ 2 + X ^ 3 := by
      simp only [map_ofNat, pow_one]; ring
    rw [hq, hr]
    ext n
    simp only [map_add, map_sub, coeff_mul_C, coeff_mul_X_pow', coeff_mk, coeff_C, coeff_X_pow]
    by_cases hn : n < 4
    · interval_cases n <;> simp [hA] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
        show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega, show 1 ≤ k + 4 by omega,
        show 2 ≤ k + 4 by omega, show 3 ≤ k + 4 by omega, show 4 ≤ k + 4 by omega,
        show k + 4 ≠ 0 by omega, show k + 4 ≠ 1 by omega, show k + 4 ≠ 2 by omega,
        show k + 4 ≠ 3 by omega, if_true, if_false, hA]
      push_cast
      ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    have : ((a (k + 4 + 1) : ℤ) : ℚ) = 4 * ((a (k + 3 + 1) : ℤ) : ℚ) - 6 * ((a (k + 2 + 1) : ℤ) : ℚ)
        + 4 * ((a (k + 1 + 1) : ℤ) : ℚ) - ((a (k + 0 + 1) : ℤ) : ℚ) := by
      push_cast
      rw [hA, hA, hA, hA, hA]
      push_cast
      ring
    rw [show k + 5 - 1 = k + 3 + 1 by omega, show k + 5 - 2 = k + 2 + 1 by omega,
      show k + 5 - 3 = k + 1 + 1 by omega, show k + 5 - 4 = k + 0 + 1 by omega,
      show k + 5 = k + 4 + 1 by omega]
    exact_mod_cast this
