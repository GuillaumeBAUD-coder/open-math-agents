import OMAStatements.S_oeis_a222955

namespace OMA.S_oeis_a222955.Pf
open OMA.S_oeis_a222955

lemma posSum_eq {n : ℕ} (w : Fin n → Fin 2) :
    posSum w = ∑ i : Fin n, ((i : ℕ) + 1) * (w i : ℕ) := by
  unfold posSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  generalize w i = x
  fin_cases x <;> simp

lemma rev_sum {n : ℕ} (f : Fin n → ℕ) : ∑ i : Fin n, f (Fin.rev i) = ∑ i : Fin n, f i :=
  Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)

lemma posSum_rev {n : ℕ} (w : Fin n → Fin 2) :
    posSum (reverse w) = ∑ i : Fin n, (n - (i : ℕ)) * (w i : ℕ) := by
  rw [posSum_eq]
  unfold reverse
  rw [← rev_sum (fun i => (n - (i : ℕ)) * (w i : ℕ))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_rev]
  have := i.isLt
  congr 1
  omega

lemma psSum_eq {n : ℕ} (w : Fin n → Fin 2) :
    psSum w = ∑ i : Fin n, (n - (i : ℕ)) * (w i : ℕ) := by
  unfold psSum
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  congr 1
  have : (Finset.univ.filter (fun j : Fin n => i ≤ j)) = Finset.Ici i := by
    ext j; simp
  rw [this, Fin.card_Ici]

lemma psSum_rev {n : ℕ} (w : Fin n → Fin 2) :
    psSum (reverse w) = ∑ i : Fin n, ((i : ℕ) + 1) * (w i : ℕ) := by
  rw [psSum_eq]
  unfold reverse
  rw [← rev_sum (fun i => ((i : ℕ) + 1) * (w i : ℕ))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_rev]
  have := i.isLt
  congr 1
  omega

lemma sum_lin (n : ℕ) : ∑ i : Fin n, (((i : ℕ) : ℚ) + 1) = (n : ℚ) * (n + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℚ) + 1)) n]
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_sq (n : ℕ) : ∑ i : Fin n, (((i : ℕ) : ℚ) + 1) ^ 2 = (n : ℚ) * (n + 1) * (2 * n + 1) / 6 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℚ) + 1) ^ 2) n]
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

end OMA.S_oeis_a222955.Pf

open OMA.S_oeis_a222955 OMA.S_oeis_a222955.Pf in
theorem OMA.solution : type_of% @OMA.S_oeis_a222955.main := by
  intro n hn w
  set P := ∑ i : Fin n, ((i : ℕ) + 1) * (w i : ℕ) with hP
  set R := ∑ i : Fin n, (n - (i : ℕ)) * (w i : ℕ) with hR
  set S := ∑ i : Fin n, (w i : ℕ) with hS
  have hPR : P + R = (n + 1) * S := by
    rw [hP, hR, hS, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have := i.isLt
    rw [← add_mul]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [posSum_eq, posSum_rev, ← hP, ← hR]
    have hrows : ∀ i : Fin n, ZeroSlope (fun j : Fin 1 => ((((fun i (_ : Fin 1) => w i) i j : Fin 2) : ℕ) : ℚ)) :=
      fun _ => Or.inl rfl
    unfold Good
    simp only [hrows, implies_true, true_and]
    -- the single column
    rw [Fin.forall_fin_one]
    unfold ZeroSlope lsSlope
    rw [sum_lin, sum_sq]
    have hPq : ∑ i : Fin n, (((i : ℕ) : ℚ) + 1) * (((w i : Fin 2) : ℕ) : ℚ) = (P : ℚ) := by
      rw [hP]; push_cast; rfl
    have hSq : ∑ i : Fin n, (((w i : Fin 2) : ℕ) : ℚ) = (S : ℚ) := by
      rw [hS]; push_cast; rfl
    rw [hPq, hSq]
    have hPRq : (P : ℚ) + R = (n + 1) * S := by exact_mod_cast hPR
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      have : P = R := by
        rw [hP, hR]; apply Finset.sum_congr rfl; intro i _; have := i.isLt; congr 1; omega
      simp [hn1, this]
    · have hn1 : n ≠ 1 := by omega
      have hnq : (n : ℚ) ≥ 2 := by exact_mod_cast h2
      have hD : (n : ℚ) * ((n : ℚ) * (n + 1) * (2 * n + 1) / 6) - ((n : ℚ) * (n + 1) / 2) ^ 2 ≠ 0 := by
        have : (n : ℚ) * ((n : ℚ) * (n + 1) * (2 * n + 1) / 6) - ((n : ℚ) * (n + 1) / 2) ^ 2
            = (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) / 12 := by ring
        rw [this]
        have h3 : (0:ℚ) < (n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) / 12 := by
          apply div_pos _ (by norm_num)
          apply mul_pos <;> nlinarith
        exact h3.ne'
      simp only [hn1, false_or]
      rw [div_eq_zero_iff, or_iff_left hD]
      constructor
      · intro h
        have hn0 : (n : ℚ) ≠ 0 := by positivity
        have h2P : 2 * (P : ℚ) = (n + 1) * S := by
          have : (n : ℚ) * (2 * P - (n + 1) * S) = 0 := by linear_combination 2 * h
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hn0
          · linarith
        have : (P : ℚ) = R := by linarith
        exact_mod_cast this
      · intro h
        have : (P : ℚ) = R := by exact_mod_cast h
        have h2P : 2 * (P : ℚ) = (n + 1) * S := by linarith
        linear_combination (n : ℚ) / 2 * h2P
  · rw [posSum_eq, posSum_rev, psSum_eq, psSum_rev]
    exact eq_comm
