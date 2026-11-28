import OMAStatements.S_oeis_a245990

-- Credit: @Dariusthedoggie
-- Proof: two-state transfer matrix on the first two entries of length-(n+2) arrays (equal vs distinct valid pairs).

namespace OMA.P245990

open OMA.S_oeis_a245990 PowerSeries

abbrev D := Fin 4

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → D) → ℕ) :
    ∑ x, f x = ∑ u : D, ∑ y : Fin m → D, f (Fin.cons u y) := by
  rw [← (Fin.consEquiv (fun _ => D)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma valid_two (u v : D) :
    isValid 2 (Fin.cons u (fun _ : Fin 1 => v)) ↔ (u : ℕ) + (v : ℕ) ≠ 3 := by
  constructor
  · intro h
    simpa using h 0 1 (by decide) (by decide)
  · intro h i j hij _
    fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · simpa using h
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)

lemma valid_cons (m : ℕ) (u : D) (y : Fin (m + 2) → D) :
    isValid (m + 3) (Fin.cons u y) ↔
      (u : ℕ) + (y 0 : ℕ) ≠ 3 ∧ (u : ℕ) + (y 1 : ℕ) ≠ 3 ∧ isValid (m + 2) y := by
  have hv1 : ((1 : Fin (m + 2)) : ℕ) = 1 := by
    change 1 % (m + 2) = 1; exact Nat.mod_eq_of_lt (by omega)
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h 0 (Fin.succ 0) (Fin.lt_def.mpr (by simp)) (by simp)
      simpa using this
    · have h2 := h 0 (Fin.succ (1 : Fin (m + 2)))
        (Fin.lt_def.mpr (by simp only [Fin.val_zero, Fin.val_succ, hv1]; omega))
        (by simp only [Fin.val_zero, Fin.val_succ, hv1]; omega)
      rw [Fin.cons_zero, Fin.cons_succ] at h2
      exact h2
    · intro i j hij hle
      have := h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) (by simp only [Fin.val_succ]; omega)
      simpa using this
  · rintro ⟨h01, h02, hy⟩ i j hij hle
    revert hij hle
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro hij _; exact absurd hij (lt_irrefl 0)
      · intro _ hle
        have hj : (j' : ℕ) = 0 ∨ (j' : ℕ) = 1 := by
          simp only [Fin.val_zero, Fin.val_succ] at hle
          omega
        rcases hj with hj | hj
        · have : j' = 0 := Fin.ext hj
          subst this; simpa using h01
        · have : j' = 1 := Fin.ext (by rw [hv1]; exact hj)
          subst this; rw [Fin.cons_zero, Fin.cons_succ]; exact h02
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro hij _; exact absurd hij (Fin.not_lt_zero _)
      · intro hij hle
        have hij' : i' < j' := Fin.succ_lt_succ_iff.mp hij
        have hle' : (j' : ℕ) - (i' : ℕ) ≤ 2 := by simp only [Fin.val_succ] at hle; omega
        simpa using hy i' j' hij' hle'

/-- Number of valid length `m + 2` arrays starting with `(u, v)`. -/
def N (m : ℕ) (u v : D) : ℕ :=
  ∑ y : Fin (m + 2) → D, if y 0 = u ∧ y 1 = v ∧ isValid (m + 2) y then 1 else 0

lemma fiber2 (m : ℕ) (g : (Fin (m + 2) → D) → ℕ) :
    ∑ y, g y = ∑ u : D, ∑ v : D,
      ∑ y : Fin (m + 2) → D, if y 0 = u ∧ y 1 = v then g y else 0 := by
  trans (∑ y : Fin (m + 2) → D, ∑ u : D, ∑ v : D, if y 0 = u ∧ y 1 = v then g y else 0)
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (y 0)]
    · rw [Finset.sum_eq_single (y 1)]
      · simp
      · intro v _ hv; simp [Ne.symm hv]
      · simp
    · intro u _ hu
      apply Finset.sum_eq_zero
      intro v _
      simp [Ne.symm hu]
    · simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]

lemma N_zero (u v : D) : N 0 u v = if (u : ℕ) + (v : ℕ) ≠ 3 then 1 else 0 := by
  unfold N
  rw [sum_cons]
  rw [Finset.sum_eq_single u]
  · rw [← (Equiv.funUnique (Fin 1) D).symm.sum_comp]
    rw [Finset.sum_eq_single v]
    · have hu : (Equiv.funUnique (Fin 1) D).symm v = fun _ : Fin 1 => v := funext fun _ => rfl
      rw [hu]
      simp only [Fin.cons_zero, Fin.cons_one, true_and]
      exact if_congr (valid_two u v) rfl rfl
    · intro b _ hb
      simp [hb]
    · simp
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro y _
    simp [ha']
  · simp

lemma N_succ (m : ℕ) (u v : D) :
    N (m + 1) u v =
      ∑ w : D, if (u : ℕ) + (v : ℕ) ≠ 3 ∧ (u : ℕ) + (w : ℕ) ≠ 3 then N m v w else 0 := by
  unfold N
  rw [sum_cons]
  rw [Finset.sum_eq_single u]
  · simp only [Fin.cons_zero, Fin.cons_one, true_and]
    rw [fiber2]
    rw [Finset.sum_eq_single v]
    · apply Finset.sum_congr rfl
      intro w _
      by_cases hc : (u : ℕ) + (v : ℕ) ≠ 3 ∧ (u : ℕ) + (w : ℕ) ≠ 3
      · rw [if_pos hc]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y 0 = v ∧ y 1 = w
        · rcases hy with ⟨hy0, hy1⟩
          rw [if_pos ⟨hy0, hy1⟩]
          have hvc := valid_cons m u y
          rw [hy0, hy1] at hvc
          exact if_congr (by simp [hy0, hy1, hvc, hc]) rfl rfl
        · rw [if_neg hy]
          by_cases hy0 : y 0 = v
          · have hy1 : y 1 ≠ w := fun h => hy ⟨hy0, h⟩
            simp [hy0, hy1]
          · simp [hy0]
      · rw [if_neg hc]
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : y 0 = v ∧ y 1 = w
        · rcases hy with ⟨hy0, hy1⟩
          rw [if_pos ⟨hy0, hy1⟩]
          have hvc := valid_cons m u y
          rw [hy0, hy1] at hvc
          rw [if_neg]
          intro ⟨_, hv⟩
          rw [hvc] at hv
          exact hc ⟨hv.1, hv.2.1⟩
        · rw [if_neg hy]
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro w _
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy0 : y 0 = b <;> simp [hy0, hb]
    · simp
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro y _
    simp [ha']
  · simp

/-- State counts: `E m` for equal starting pairs `u = v`, `E.D_ m` for distinct valid pairs. -/
def E : ℕ → ℕ
  | 0 => 1
  | m + 1 => E m + 2 * D_ m
where
  D_ : ℕ → ℕ
  | 0 => 1
  | m + 1 => E m + 1 * D_ m

lemma cnt_EE : ∀ u v : D,
    (∑ w : D, if (u : ℕ) + (v : ℕ) ≠ 3 ∧ (u : ℕ) + (w : ℕ) ≠ 3 ∧
      (v : ℕ) + (w : ℕ) ≠ 3 ∧ v = w then 1 else 0) =
    if (u : ℕ) + (v : ℕ) ≠ 3 then 1 else 0 := by
  decide

lemma cnt_ED : ∀ u v : D,
    (∑ w : D, if (u : ℕ) + (v : ℕ) ≠ 3 ∧ (u : ℕ) + (w : ℕ) ≠ 3 ∧
      (v : ℕ) + (w : ℕ) ≠ 3 ∧ v ≠ w then 1 else 0) =
    if (u : ℕ) + (v : ℕ) = 3 then 0 else if u = v then 2 else 1 := by
  decide

lemma cnt_pairs :
    (∑ u : D, ∑ v : D, if (u : ℕ) + (v : ℕ) ≠ 3 ∧ u = v then 1 else 0) = 4 ∧
    (∑ u : D, ∑ v : D, if (u : ℕ) + (v : ℕ) ≠ 3 ∧ u ≠ v then 1 else 0) = 8 := by
  decide

lemma N_eq (m : ℕ) (u v : D) :
    N m u v = if (u : ℕ) + (v : ℕ) = 3 then 0 else if u = v then E m else E.D_ m := by
  induction m generalizing u v with
  | zero =>
    rw [N_zero]
    split_ifs <;> simp_all [E, E.D_]
  | succ m ih =>
    rw [N_succ]
    have e : ∀ w : D,
        (if (u : ℕ) + (v : ℕ) ≠ 3 ∧ (u : ℕ) + (w : ℕ) ≠ 3 then N m v w else 0) =
        E m * (if (u : ℕ) + (v : ℕ) ≠ 3 ∧ (u : ℕ) + (w : ℕ) ≠ 3 ∧
          (v : ℕ) + (w : ℕ) ≠ 3 ∧ v = w then 1 else 0) +
        E.D_ m * (if (u : ℕ) + (v : ℕ) ≠ 3 ∧ (u : ℕ) + (w : ℕ) ≠ 3 ∧
          (v : ℕ) + (w : ℕ) ≠ 3 ∧ v ≠ w then 1 else 0) := by
      intro w
      rw [ih v w]
      by_cases h1 : (u : ℕ) + (v : ℕ) ≠ 3
      · by_cases h2 : (u : ℕ) + (w : ℕ) ≠ 3
        · by_cases h3 : (v : ℕ) + (w : ℕ) = 3
          · simp [h1, h2, h3]
          · by_cases h4 : v = w <;> simp [h1, h2, h3, h4]
        · simp [h1, h2]
      · simp [h1]
    rw [Finset.sum_congr rfl (fun w _ => e w), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, cnt_EE, cnt_ED]
    by_cases h1 : (u : ℕ) + (v : ℕ) = 3
    · simp [h1]
    · by_cases h2 : u = v <;> simp [h1, h2, E, E.D_] <;> split_ifs <;> ring

lemma a_succ (m : ℕ) : a (m + 1) = 4 * E (m + 1) + 8 * E.D_ (m + 1) := by
  have e : a (m + 1) = ∑ u : D, ∑ v : D, N (m + 1) u v := by
    show (Finset.univ.filter (fun x : Fin (m + 3) → D => isValid (m + 3) x)).card = _
    unfold N
    rw [Finset.card_filter, fiber2]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = u ∧ y 1 = v
    · rcases hy with ⟨hy0, hy1⟩
      simp [hy0, hy1]
    · rw [if_neg hy]
      by_cases hy0 : y 0 = u
      · have hy1 : y 1 ≠ v := fun h => hy ⟨hy0, h⟩
        simp [hy0, hy1]
      · simp [hy0]
  rw [e]
  have e2 : ∀ u v : D, N (m + 1) u v =
      E (m + 1) * (if (u : ℕ) + (v : ℕ) ≠ 3 ∧ u = v then 1 else 0) +
      E.D_ (m + 1) * (if (u : ℕ) + (v : ℕ) ≠ 3 ∧ u ≠ v then 1 else 0) := by
    intro u v
    rw [N_eq]
    by_cases h1 : (u : ℕ) + (v : ℕ) = 3
    · simp [h1]
    · by_cases h2 : u = v <;> simp [h1, h2]
  simp_rw [e2, Finset.sum_add_distrib, ← Finset.mul_sum, cnt_pairs.1, cnt_pairs.2]
  ring

lemma step_rec (m : ℕ) :
    E (m + 2) = 2 * E (m + 1) + E m ∧
    E.D_ (m + 2) = 2 * E.D_ (m + 1) + E.D_ m := by
  simp only [E, E.D_]
  constructor <;> ring

lemma a_rec (n : ℕ) (hn : 3 ≤ n) : a n = 2 * a (n - 1) + a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
  rw [a_succ (m + 2), a_succ (m + 1), a_succ m]
  have h := step_rec (m + 1)
  rw [h.1, h.2]
  ring

lemma a_zero : a 0 = 0 := rfl
lemma a_one : a 1 = 28 := by rw [a_succ 0]; simp [E, E.D_]
lemma a_two : a 2 = 68 := by rw [a_succ 1]; simp [E, E.D_]

noncomputable def binet (n : ℕ) : ℝ :=
  Real.sqrt 2 *
    ((1 - Real.sqrt 2) ^ n * (-4 + 3 * Real.sqrt 2) +
     (1 + Real.sqrt 2) ^ n * (4 + 3 * Real.sqrt 2))

lemma binet_rec (n : ℕ) : binet (n + 2) = 2 * binet (n + 1) + binet n := by
  unfold binet
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (1 - Real.sqrt 2) ^ (n + 2) =
      2 * (1 - Real.sqrt 2) ^ (n + 1) + (1 - Real.sqrt 2) ^ n := by
    have : (1 - Real.sqrt 2) ^ 2 = 2 * (1 - Real.sqrt 2) + 1 := by nlinarith [hs]
    calc (1 - Real.sqrt 2) ^ (n + 2)
        = (1 - Real.sqrt 2) ^ n * (1 - Real.sqrt 2) ^ 2 := by ring
      _ = (1 - Real.sqrt 2) ^ n * (2 * (1 - Real.sqrt 2) + 1) := by rw [this]
      _ = 2 * (1 - Real.sqrt 2) ^ (n + 1) + (1 - Real.sqrt 2) ^ n := by ring
  have h2 : (1 + Real.sqrt 2) ^ (n + 2) =
      2 * (1 + Real.sqrt 2) ^ (n + 1) + (1 + Real.sqrt 2) ^ n := by
    have : (1 + Real.sqrt 2) ^ 2 = 2 * (1 + Real.sqrt 2) + 1 := by nlinarith [hs]
    calc (1 + Real.sqrt 2) ^ (n + 2)
        = (1 + Real.sqrt 2) ^ n * (1 + Real.sqrt 2) ^ 2 := by ring
      _ = (1 + Real.sqrt 2) ^ n * (2 * (1 + Real.sqrt 2) + 1) := by rw [this]
      _ = 2 * (1 + Real.sqrt 2) ^ (n + 1) + (1 + Real.sqrt 2) ^ n := by ring
  rw [h1, h2]
  ring

lemma binet_one : binet 1 = 28 := by
  unfold binet
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination 14 * hs

lemma binet_two : binet 2 = 68 := by
  unfold binet
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination (34 + 6 * Real.sqrt 2 ^ 2) * hs

lemma a_eq_binet (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = binet n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | k
    · simp [a_one, binet_one]
    · simp [a_two, binet_two]
    · have hrec := a_rec (k + 3) (by omega)
      have h1 : (a (k + 2) : ℝ) = binet (k + 2) := ih (k + 1) (by omega)
      have h0 : (a (k + 1) : ℝ) = binet (k + 1) := ih k (by omega)
      have hr : (a (k + 3) : ℝ) = 2 * (a (k + 2) : ℝ) + (a (k + 1) : ℝ) := by
        exact_mod_cast hrec
      rw [hr, h1, h0, ← binet_rec (k + 1)]

theorem main_proof :
    (∀ n : ℕ, 3 ≤ n → a n = 2 * a (n - 1) + a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 2 * X - X ^ 2) = 4 * X * (7 + 3 * X)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = Real.sqrt 2 *
        ((1 - Real.sqrt 2) ^ n * (-4 + 3 * Real.sqrt 2) +
         (1 + Real.sqrt 2) ^ n * (4 + 3 * Real.sqrt 2))) := by
  refine ⟨a_rec, ?_, a_eq_binet⟩
  have hl : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 2 * X - X ^ 2) =
      PowerSeries.mk (fun n => (a n : ℚ)) -
        C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) -
        PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2 := by
    simp only [map_ofNat]; ring
  have hr : (4 * X * (7 + 3 * X) : PowerSeries ℚ) =
      C (28 : ℚ) * X ^ 1 + C (12 : ℚ) * X ^ 2 := by
    simp only [map_ofNat]; ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [a_zero, a_one, a_two] <;> norm_num
  · have hq : (a n : ℚ) = 2 * a (n - 1) + a (n - 2) := by exact_mod_cast a_rec n hn
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    simp only [c1, c2, e1, e2, coeff_C, if_true, if_false]
    rw [hq]; ring

end OMA.P245990

theorem OMA.solution : type_of% @OMA.S_oeis_a245990.main := OMA.P245990.main_proof
