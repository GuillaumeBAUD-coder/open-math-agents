import OMAReductions.R_OeisA2426_conjecture_R1
import Mathlib.Tactic

/-!
# Proof of OeisA2426 H1

Every prime `p > 3` satisfies `OeisA2426.a p ≡ 1 [MOD p ^ 2]`.
-/

open Polynomial BigOperators

private lemma coeff_one_sub_X_pow (n i : ℕ) :
    ((1 - X : ℤ[X]) ^ n).coeff i = (-1) ^ i * (n.choose i : ℤ) := by
  rw [sub_eq_add_neg, add_comm, add_pow]
  simp only [one_pow, mul_one, finsetSum_coeff]
  have hterm : ∀ m ∈ Finset.range (n + 1),
      ((-X : ℤ[X]) ^ m * (n.choose m : ℤ[X])).coeff i =
        if i = m then (-1) ^ m * (n.choose m : ℤ) else 0 := by
    intro m _
    have hneg : (-X : ℤ[X]) ^ m = C ((-1 : ℤ) ^ m) * X ^ m := by
      rw [← neg_one_mul, mul_pow, C_pow, C_neg, C_1]
    have hcast : (n.choose m : ℤ[X]) = C (n.choose m : ℤ) := (map_natCast C (n.choose m)).symm
    rw [hneg, hcast, mul_assoc, mul_comm (X ^ m : ℤ[X]), ← mul_assoc, ← C_mul,
      coeff_C_mul, coeff_X_pow]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with hi
  · rfl
  · simp only [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt hi]
    simp

private lemma coeff_one_sub_X3_pow_of_not_dvd (n i : ℕ) (h3 : ¬ 3 ∣ i) :
    ((1 - X ^ 3 : ℤ[X]) ^ n).coeff i = 0 := by
  rw [sub_eq_add_neg, add_comm, add_pow]
  simp only [one_pow, mul_one, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro m _
  have hneg : (-X ^ 3 : ℤ[X]) ^ m = C ((-1 : ℤ) ^ m) * X ^ (3 * m) := by
    rw [← neg_one_mul, mul_pow, ← pow_mul, C_pow, C_neg, C_1]
  have hcast : (n.choose m : ℤ[X]) = C (n.choose m : ℤ) := (map_natCast C (n.choose m)).symm
  rw [hneg, hcast, mul_assoc, mul_comm (X ^ (3 * m) : ℤ[X]), ← mul_assoc, ← C_mul,
    coeff_C_mul, coeff_X_pow]
  split_ifs with hmi
  · exfalso; exact h3 ⟨m, hmi⟩
  · ring

private lemma coeff_one_add_X2_pow (m d : ℕ) :
    ((1 + X ^ 2 : ℤ[X]) ^ m).coeff d =
      ∑ l ∈ Finset.range (m + 1), if d = 2 * l then (m.choose l : ℤ) else 0 := by
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro l _
  have hcast : (m.choose l : ℤ[X]) = C (m.choose l : ℤ) := (map_natCast C (m.choose l)).symm
  rw [← pow_mul, hcast, mul_comm, coeff_C_mul, coeff_X_pow]
  split_ifs <;> ring

private lemma coeff_one_add_X2_pow_two_mul (k : ℕ) :
    ((1 + X ^ 2 : ℤ[X]) ^ (2 * k)).coeff (2 * k) = ((2 * k).choose k : ℤ) := by
  rw [coeff_one_add_X2_pow]
  have hcongr : ∀ l ∈ Finset.range (2 * k + 1),
      (if 2 * k = 2 * l then ((2 * k).choose l : ℤ) else 0) =
        if l = k then ((2 * k).choose k : ℤ) else 0 := by
    intro l _
    split_ifs with h1 h2 h2
    · subst h2; rfl
    · omega
    · omega
    · rfl
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
  have hk : k ∈ Finset.range (2 * k + 1) := by
    rw [Finset.mem_range]; omega
  simp [hk]

private lemma coeff_one_add_X2_pow_odd (m : ℕ) (hm : Odd m) :
    ((1 + X ^ 2 : ℤ[X]) ^ m).coeff m = 0 := by
  rw [coeff_one_add_X2_pow]
  apply Finset.sum_eq_zero
  intro l _
  split_ifs with hl
  · exfalso
    rcases hm with ⟨k, rfl⟩
    omega
  · rfl

private lemma sum_range_even (f : ℕ → ℤ) (hf : ∀ m, Odd m → f m = 0) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), f m = ∑ k ∈ Finset.range (n / 2 + 1), f (2 * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd (n + 1) with ⟨k, hk⟩ | hodd
    · have hdiv : (n + 1) / 2 = n / 2 + 1 := by omega
      have hmul : 2 * (n / 2 + 1) = n + 1 := by omega
      rw [hdiv]
      symm
      rw [Finset.sum_range_succ, hmul]
    · have hdiv : (n + 1) / 2 = n / 2 := by
        rcases hodd with ⟨k, hk⟩
        omega
      rw [hdiv, hf (n + 1) hodd, add_zero]

private lemma coeff_trinomial_middle (n : ℕ) :
    ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff n = (OeisA2426.a n : ℤ) := by
  have hrew : (1 + X + X ^ 2 : ℤ[X]) = (1 + X ^ 2) + X := by ring
  rw [hrew, add_pow]
  simp only [finsetSum_coeff]
  have hterm : ∀ m ∈ Finset.range (n + 1),
      (((1 + X ^ 2 : ℤ[X]) ^ m * X ^ (n - m) * (n.choose m : ℤ[X])).coeff n) =
        (n.choose m : ℤ) * ((1 + X ^ 2 : ℤ[X]) ^ m).coeff m := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hcast : (n.choose m : ℤ[X]) = C (n.choose m : ℤ) := (map_natCast C (n.choose m)).symm
    rw [hcast, mul_comm _ (C _), coeff_C_mul]
    have hc : ((1 + X ^ 2 : ℤ[X]) ^ m * X ^ (n - m)).coeff (m + (n - m)) =
        ((1 + X ^ 2 : ℤ[X]) ^ m).coeff m := by
      rw [coeff_mul_X_pow]
    have hnm : m + (n - m) = n := by omega
    rw [hnm] at hc
    rw [hc]
  rw [Finset.sum_congr rfl hterm]
  rw [sum_range_even (fun m => (n.choose m : ℤ) * ((1 + X ^ 2 : ℤ[X]) ^ m).coeff m) (by
    intro m hm
    rw [coeff_one_add_X2_pow_odd m hm, mul_zero])]
  unfold OeisA2426.a
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_one_add_X2_pow_two_mul]

private lemma dvd_coeff_one_add_X2_pow (p d : ℕ) (hp : p.Prime) (hd0 : 0 < d) (hdp : d < p) :
    (p : ℤ) ∣ ((1 + X ^ 2 : ℤ[X]) ^ p).coeff d := by
  rw [coeff_one_add_X2_pow]
  apply Finset.dvd_sum
  intro l _
  split_ifs with hld
  · exact Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self (by omega) (by omega))
  · exact dvd_zero _

private lemma dvd_coeff_trinomial (p d : ℕ) (hp : p.Prime) (hd0 : 0 < d) (hdp : d < p) :
    (p : ℤ) ∣ ((1 + X + X ^ 2 : ℤ[X]) ^ p).coeff d := by
  have hrew : (1 + X + X ^ 2 : ℤ[X]) = (1 + X ^ 2) + X := by ring
  rw [hrew, add_pow, finsetSum_coeff]
  apply Finset.dvd_sum
  intro m hm
  rw [Finset.mem_range] at hm
  have hcast : (p.choose m : ℤ[X]) = C (p.choose m : ℤ) := (map_natCast C (p.choose m)).symm
  rw [hcast, mul_comm _ (C _), coeff_C_mul]
  by_cases hm0 : m = 0
  · rw [hm0]
    simp only [pow_zero, one_mul, Nat.sub_zero, coeff_X_pow]
    have hdp_ne : d ≠ p := by omega
    simp [hdp_ne]
  · by_cases hmp : m = p
    · rw [hmp]
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one]
      exact dvd_coeff_one_add_X2_pow p d hp hd0 hdp
    · have hdvd : (p : ℤ) ∣ (p.choose m : ℤ) :=
        Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self hm0 (by omega))
      exact dvd_mul_of_dvd_left hdvd _

private lemma sum_range_split_first (f : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), f i = f 0 + ∑ j ∈ Finset.range m, f (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]

theorem prove_OeisA2426_H1 :
    ∀ p : ℕ, 3 < p → p.Prime → OeisA2426.a p ≡ 1 [MOD p ^ 2] := by
  intro p hp3 hp
  have h3 : ¬ 3 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h1 | h2 <;> omega
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  let P : ℤ[X] := (1 - X) ^ p
  let Q : ℤ[X] := (1 + X + X ^ 2) ^ p
  have hPQ : P * Q = (1 - X ^ 3 : ℤ[X]) ^ p := by
    dsimp [P, Q]
    rw [← mul_pow]
    congr 1
    ring
  have hcoeff0 : (P * Q).coeff p = 0 := by
    rw [hPQ]
    exact coeff_one_sub_X3_pow_of_not_dvd p p h3
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j) p] at hcoeff0
  rw [Finset.sum_range_succ] at hcoeff0
  have hfirst := sum_range_split_first (fun i => P.coeff i * Q.coeff (p - i)) (p - 1)
  have hp_pred : p - 1 + 1 = p := by omega
  rw [hp_pred, Nat.sub_zero] at hfirst
  rw [hfirst] at hcoeff0
  have hP0 : P.coeff 0 = 1 := by
    dsimp [P]
    rw [coeff_one_sub_X_pow]
    simp
  have hPp : P.coeff p = -1 := by
    dsimp [P]
    rw [coeff_one_sub_X_pow, hp_odd.neg_one_pow, Nat.choose_self]
    simp
  have hQ0 : Q.coeff 0 = 1 := by
    dsimp [Q]
    rw [coeff_zero_eq_eval_zero]
    simp
  have hQp : Q.coeff p = (OeisA2426.a p : ℤ) := coeff_trinomial_middle p
  rw [Nat.sub_self, hP0, hPp, hQ0, hQp] at hcoeff0
  have hS_dvd : ((p : ℤ) ^ 2) ∣
      ∑ j ∈ Finset.range (p - 1), P.coeff (j + 1) * Q.coeff (p - (j + 1)) := by
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hP_dvd : (p : ℤ) ∣ P.coeff (j + 1) := by
      dsimp [P]
      rw [coeff_one_sub_X_pow]
      have hdvd : (p : ℤ) ∣ (p.choose (j + 1) : ℤ) :=
        Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self (by omega) (by omega))
      exact dvd_mul_of_dvd_right hdvd _
    have hQ_dvd : (p : ℤ) ∣ Q.coeff (p - (j + 1)) :=
      dvd_coeff_trinomial p (p - (j + 1)) hp (by omega) (by omega)
    rw [sq]
    exact mul_dvd_mul hP_dvd hQ_dvd
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
  push_cast
  have heq : (1 : ℤ) - (OeisA2426.a p : ℤ) =
      ∑ j ∈ Finset.range (p - 1), P.coeff (j + 1) * Q.coeff (p - (j + 1)) := by
    linarith
  rw [heq]
  exact hS_dvd

theorem OMA.solution : OMA.R_OeisA2426_conjecture_R1.H1 :=
  prove_OeisA2426_H1
