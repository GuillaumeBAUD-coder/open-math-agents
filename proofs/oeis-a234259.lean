import OMAStatements.S_oeis_a234259
import Mathlib.Tactic

namespace OMA.P_oeis_a234259

open OMA.S_oeis_a234259

private def adj (r1 r2 : Fin 3 × Fin 3) : Bool :=
  decide (validBlock r1.1 r1.2 r2.1 r2.2)

private def stepVec (v : Fin 3 × Fin 3 → ℤ) (r2 : Fin 3 × Fin 3) : ℤ :=
  ∑ r1 : Fin 3 × Fin 3, if adj r1 r2 then v r1 else 0

private lemma stepVec_add (u v : Fin 3 × Fin 3 → ℤ) (r : Fin 3 × Fin 3) :
    stepVec (fun x => u x + v x) r = stepVec u r + stepVec v r := by
  unfold stepVec
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_sub (u v : Fin 3 × Fin 3 → ℤ) (r : Fin 3 × Fin 3) :
    stepVec (fun x => u x - v x) r = stepVec u r - stepVec v r := by
  unfold stepVec
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_smul (c : ℤ) (v : Fin 3 × Fin 3 → ℤ) (r : Fin 3 × Fin 3) :
    stepVec (fun x => c * v x) r = c * stepVec v r := by
  unfold stepVec
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private def isValidArr (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 3) : Prop :=
  ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
    (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))

private instance (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 3) : Decidable (isValidArr n A) := by
  unfold isValidArr; infer_instance

private def rowCount (n : ℕ) (r : Fin 3 × Fin 3) : ℤ :=
  ∑ A : Fin (n + 1) × Fin 2 → Fin 3,
    if isValidArr n A ∧ (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1)) = r
    then 1 else 0

private lemma A234259_eq_sum_rowCount (n : ℕ) :
    (A234259 n : ℤ) = ∑ r : Fin 3 × Fin 3, rowCount n r := by
  unfold A234259 rowCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (n + 1) × Fin 2 → Fin 3),
      (S.card : ℤ) = ∑ A : Fin (n + 1) × Fin 2 → Fin 3, if A ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isValidArr]
  by_cases hA : ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))
  · rw [if_pos hA]
    rw [Finset.sum_eq_single (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1))]
    · simp [hA]
    · intro r _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  · rw [if_neg hA]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    simp [hA]

private lemma rowCount_zero (r : Fin 3 × Fin 3) : rowCount 0 r = 1 := by
  unfold rowCount isValidArr
  let A0 : Fin 1 × Fin 2 → Fin 3 := fun p => if p.2 = 0 then r.1 else r.2
  rw [Finset.sum_eq_single A0]
  · simp [A0]
  · intro A _ hne
    rw [if_neg]
    rintro ⟨_, hr⟩
    apply hne
    funext ⟨i, j⟩
    fin_cases i; fin_cases j
    · exact congrArg Prod.fst hr
    · exact congrArg Prod.snd hr
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma rowCount_succ (n : ℕ) (r : Fin 3 × Fin 3) :
    rowCount (n + 1) r = stepVec (rowCount n) r := by
  let e : (Fin (n + 2) × Fin 2 → Fin 3) ≃ ((Fin (n + 1) × Fin 2 → Fin 3) × (Fin 3 × Fin 3)) :=
    { toFun := fun A =>
        (fun p => A (⟨p.1.1, by omega⟩, p.2),
         (A (⟨n + 1, Nat.lt_succ_self _⟩, 0), A (⟨n + 1, Nat.lt_succ_self _⟩, 1)))
      invFun := fun ⟨A', r'⟩ p =>
        if h : p.1.1 < n + 1 then A' (⟨p.1.1, h⟩, p.2)
        else if p.2 = 0 then r'.1 else r'.2
      left_inv := fun A => by
        funext ⟨i, j⟩
        by_cases h : i.1 < n + 1
        · simp [h]
        · have hi : i = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
          subst hi; fin_cases j <;> simp
      right_inv := fun ⟨A', r'⟩ => by
        apply Prod.ext
        · funext ⟨i, j⟩; simp [i.isLt]
        · simp }
  have hiff : ∀ A : Fin (n + 2) × Fin 2 → Fin 3,
      (isValidArr (n + 1) A ∧
       (A (⟨n + 1, Nat.lt_succ_self _⟩, 0), A (⟨n + 1, Nat.lt_succ_self _⟩, 1)) = r) ↔
      (isValidArr n (e A).1 ∧
       adj ((e A).1 (⟨n, Nat.lt_succ_self n⟩, 0), (e A).1 (⟨n, Nat.lt_succ_self n⟩, 1)) (e A).2 = true ∧
       (e A).2 = r) := by
    intro A
    simp only [e, Equiv.coe_fn_mk, isValidArr, adj, decide_eq_true_eq]
    constructor
    · rintro ⟨hA, hr⟩
      refine ⟨fun i => hA ⟨i.1, by omega⟩, hA ⟨n, Nat.lt_succ_self n⟩, hr⟩
    · rintro ⟨hA', hlast, hr⟩
      refine ⟨fun i => ?_, hr⟩
      by_cases hi : i.1 < n
      · exact hA' ⟨i.1, hi⟩
      · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
        subst hieq; exact hlast
  unfold rowCount stepVec
  rw [Fintype.sum_equiv e _ (fun p =>
      if isValidArr n p.1 ∧
         adj (p.1 (⟨n, Nat.lt_succ_self n⟩, 0), p.1 (⟨n, Nat.lt_succ_self n⟩, 1)) p.2 = true ∧
         p.2 = r then (1 : ℤ) else 0)
      (fun A => by simp only [hiff A])]
  rw [Fintype.sum_prod_type]
  have hr_sum : ∀ A' : Fin (n + 1) × Fin 2 → Fin 3,
      (∑ r' : Fin 3 × Fin 3,
        if isValidArr n A' ∧
           adj (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1)) r' = true ∧
           r' = r then (1 : ℤ) else 0) =
      if isValidArr n A' ∧
         adj (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1)) r = true
      then (1 : ℤ) else 0 := by
    intro A'
    rw [Finset.sum_eq_single r]
    · simp
    · intro r' _ hne; simp [hne]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  simp_rw [hr_sum]
  symm
  trans ∑ r1 : Fin 3 × Fin 3, ∑ A' : Fin (n + 1) × Fin 2 → Fin 3,
      if isValidArr n A' ∧
         (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1)) = r1 ∧
         adj r1 r = true then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun r1 _ => ?_
    by_cases hadj : adj r1 r = true
    · simp [hadj]
    · simp [hadj]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A' _ => ?_
    rw [Finset.sum_eq_single (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1))]
    · simp
    · intro r1 _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma rowCount_zero_fun : rowCount 0 = fun _ => 1 := funext rowCount_zero
private lemma rowCount_succ_fun (n : ℕ) : rowCount (n + 1) = stepVec (rowCount n) :=
  funext (rowCount_succ n)

private lemma rowCount_rec_base :
    rowCount 3 = fun r => 2 * rowCount 2 r + 6 * rowCount 1 r - 12 * rowCount 0 r := by
  funext r
  simp only [rowCount_succ_fun, rowCount_zero_fun]
  revert r; decide

private lemma rowCount_rec (m : ℕ) :
    rowCount (m + 3) = fun r => 2 * rowCount (m + 2) r + 6 * rowCount (m + 1) r - 12 * rowCount m r := by
  induction m with
  | zero => exact rowCount_rec_base
  | succ m ih =>
    funext r
    conv_lhs =>
      rw [rowCount_succ (m + 3) r, ih, stepVec_sub, stepVec_add, stepVec_smul, stepVec_smul,
        stepVec_smul, ← rowCount_succ (m + 2) r, ← rowCount_succ (m + 1) r, ← rowCount_succ m r]

private lemma A234259_rec (m : ℕ) :
    (A234259 (m + 4) : ℤ) = 2 * A234259 (m + 3) + 6 * A234259 (m + 2) - 12 * A234259 (m + 1) := by
  simp only [A234259_eq_sum_rowCount]
  rw [show m + 4 = (m + 1) + 3 by omega, show m + 3 = (m + 1) + 2 by omega,
    show m + 2 = (m + 1) + 1 by omega, rowCount_rec (m + 1),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

private lemma A234259_small : A234259 1 = 20 ∧ A234259 2 = 46 ∧ A234259 3 = 104 := by
  have h1 : (A234259 1 : ℤ) = 20 := by
    rw [A234259_eq_sum_rowCount, rowCount_succ_fun, rowCount_zero_fun]; decide
  have h2 : (A234259 2 : ℤ) = 46 := by
    rw [A234259_eq_sum_rowCount, rowCount_succ_fun, rowCount_succ_fun, rowCount_zero_fun]; decide
  have h3 : (A234259 3 : ℤ) = 104 := by
    rw [A234259_eq_sum_rowCount, rowCount_succ_fun, rowCount_succ_fun, rowCount_succ_fun,
      rowCount_zero_fun]; decide
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

private lemma coeff_X_pow_mul_eq (k : ℕ) (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k * f) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with hk
  · rw [Finset.sum_eq_single (k, n - k)]
    · rw [PowerSeries.coeff_X_pow, if_pos rfl, one_mul]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have hne1 : p.1 ≠ k := fun h => hne (Prod.ext h (by omega))
      rw [PowerSeries.coeff_X_pow, if_neg hne1, zero_mul]
    · intro hnot; exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega
  · apply Finset.sum_eq_zero
    intro p hp; rw [Finset.mem_antidiagonal] at hp
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

private lemma A234259_gf :
    (1 - 2 * PowerSeries.X) * (1 - 6 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234259 n : ℤ)) =
      2 * PowerSeries.X * (10 + 3 * PowerSeries.X - 54 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234259 n : ℤ))
  have hlhs : (1 - 2 * PowerSeries.X) * (1 - 6 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 2 * (PowerSeries.X ^ 1 * F) -
        PowerSeries.C 6 * (PowerSeries.X ^ 2 * F) + PowerSeries.C 12 * (PowerSeries.X ^ 3 * F) := by
    have h2 : PowerSeries.C (2 : ℤ) = (2 : PowerSeries ℤ) := rfl
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h12 : PowerSeries.C (12 : ℤ) = (12 : PowerSeries ℤ) := rfl
    rw [h2, h6, h12, pow_one]; ring
  have hrhs : 2 * (PowerSeries.X : PowerSeries ℤ) *
        (10 + 3 * PowerSeries.X - 54 * PowerSeries.X ^ 2) =
      PowerSeries.C 20 * PowerSeries.X + PowerSeries.C 6 * PowerSeries.X ^ 2 -
      PowerSeries.C 108 * PowerSeries.X ^ 3 := by
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h20 : PowerSeries.C (20 : ℤ) = (20 : PowerSeries ℤ) := rfl
    have h108 : PowerSeries.C (108 : ℤ) = (108 : PowerSeries ℤ) := rfl
    rw [h6, h20, h108]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3⟩ := A234259_small
  by_cases hn3 : n ≤ 3
  · interval_cases n <;> simp [F, h1, h2, h3]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec := A234259_rec (n - 4)
    simp only [show n - 4 + 4 = n by omega, show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 2 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega] at hrec
    linarith

private lemma A234259_closed (n : ℕ) (hn : 1 ≤ n) :
    A234259 n =
      if Even n then 2 ^ (2 + n) + 5 * 6 ^ (n / 2)
      else 2 ^ (2 + n) + 12 * 6 ^ ((n - 1) / 2) := by
  suffices h : ∀ k : ℕ,
      (A234259 (k + 1) : ℤ) =
        if Even (k + 1) then (2 : ℤ) ^ (k + 3) + 5 * (6 : ℤ) ^ ((k + 1) / 2)
        else (2 : ℤ) ^ (k + 3) + 12 * (6 : ℤ) ^ (k / 2) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hk := h k
    rw [show 2 + (k + 1) = k + 3 by omega, Nat.add_sub_cancel]
    by_cases hev : Even (k + 1)
    · rw [if_pos hev] at hk ⊢; exact_mod_cast hk
    · rw [if_neg hev] at hk ⊢; exact_mod_cast hk
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2, h3⟩ := A234259_small
    rcases k with _ | _ | _ | m
    · simp [h1]
    · simp [h2]
    · have ho3 : ¬ Even 3 := by decide
      simp [h3, ho3]
    · have hrec := A234259_rec m
      have ih2 := ih (m + 2) (by omega)
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      rw [show m + 3 + 1 = m + 4 by omega, hrec]
      by_cases hev : Even (m + 4)
      · have h3o : ¬ Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2e : Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1o : ¬ Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_pos hev]
        rw [show m + 2 + 1 = m + 3 by omega, if_neg h3o] at ih2
        rw [show m + 1 + 1 = m + 2 by omega, if_pos h2e] at ih1
        rw [if_neg h1o] at ih0
        have hp3 : (2 : ℤ) ^ (m + 3 + 3) = 8 * (2 : ℤ) ^ (m + 3) := by
          rw [show m + 3 + 3 = (m + 3) + 3 by omega, pow_add]; ring
        have hp2 : (2 : ℤ) ^ (m + 2 + 3) = 4 * (2 : ℤ) ^ (m + 3) := by
          rw [show m + 2 + 3 = (m + 3) + 2 by omega, pow_add]; ring
        have hp1 : (2 : ℤ) ^ (m + 1 + 3) = 2 * (2 : ℤ) ^ (m + 3) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, pow_add]; ring
        have h6_4 : (6 : ℤ) ^ ((m + 4) / 2) = 36 * (6 : ℤ) ^ (m / 2) := by
          rw [show (m + 4) / 2 = m / 2 + 2 by omega, pow_add]; ring
        have h6_2 : (6 : ℤ) ^ ((m + 2) / 2) = 6 * (6 : ℤ) ^ (m / 2) := by
          rw [show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ]; ring
        rw [hp3, h6_4]; rw [hp2, h6_2] at ih2; rw [hp1, h6_2] at ih1
        linarith
      · have h3e : Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2o : ¬ Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1e : Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_neg hev]
        rw [show m + 2 + 1 = m + 3 by omega, if_pos h3e] at ih2
        rw [show m + 1 + 1 = m + 2 by omega, if_neg h2o] at ih1
        rw [if_pos h1e] at ih0
        have hp3 : (2 : ℤ) ^ (m + 3 + 3) = 8 * (2 : ℤ) ^ (m + 3) := by
          rw [show m + 3 + 3 = (m + 3) + 3 by omega, pow_add]; ring
        have hp2 : (2 : ℤ) ^ (m + 2 + 3) = 4 * (2 : ℤ) ^ (m + 3) := by
          rw [show m + 2 + 3 = (m + 3) + 2 by omega, pow_add]; ring
        have hp1 : (2 : ℤ) ^ (m + 1 + 3) = 2 * (2 : ℤ) ^ (m + 3) := by
          rw [show m + 1 + 3 = (m + 3) + 1 by omega, pow_add]; ring
        have h6_3 : (6 : ℤ) ^ ((m + 3) / 2) = 6 * (6 : ℤ) ^ ((m + 1) / 2) := by
          rw [show (m + 3) / 2 = (m + 1) / 2 + 1 by omega, pow_succ]; ring
        rw [hp3, h6_3]; rw [hp2, h6_3] at ih2; rw [hp1] at ih1
        linarith

end OMA.P_oeis_a234259

theorem OMA.solution : type_of% @OMA.S_oeis_a234259.main :=
  ⟨OMA.P_oeis_a234259.A234259_gf, OMA.P_oeis_a234259.A234259_closed⟩
