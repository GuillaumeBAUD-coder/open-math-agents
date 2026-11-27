import OMAStatements.S_oeis_a273400

private lemma catalan_succ_eq (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 : (n + 2) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 : (n + 1) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom :=
    Nat.succ_mul_centralBinom_succ n
  have h3 : (n + 1) * catalan n = n.centralBinom :=
    succ_mul_catalan_eq_centralBinom n
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
  calc
    (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (n + 1).centralBinom := by rw [h1]
    _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := by rw [h2, h3]
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by ring

private lemma catalan_mono : Monotone catalan := by
  refine monotone_nat_of_le_succ fun n => ?_
  have h := catalan_succ_eq n
  have hle : (n + 2) * catalan n ≤ (n + 2) * catalan (n + 1) := by
    rw [h]
    exact Nat.mul_le_mul_right _ (by omega)
  exact Nat.le_of_mul_le_mul_left hle (by omega)

private lemma two_mul_catalan_le_succ {n : ℕ} (hn : 1 ≤ n) :
    2 * catalan n ≤ catalan (n + 1) := by
  have h := catalan_succ_eq n
  have hle : (n + 2) * (2 * catalan n) ≤ (n + 2) * catalan (n + 1) := by
    rw [h]
    calc
      (n + 2) * (2 * catalan n) = 2 * (n + 2) * catalan n := by ring
      _ ≤ 2 * (2 * n + 1) * catalan n := Nat.mul_le_mul_right _ (by omega)
  exact Nat.le_of_mul_le_mul_left hle (by omega)

private lemma two_pow_pred_le_catalan : ∀ k : ℕ, 1 ≤ k → 2 ^ (k - 1) ≤ catalan k
  | 0, hk => by omega
  | 1, _ => by simp
  | k + 2, _ => by
    have ih := two_pow_pred_le_catalan (k + 1) (by omega)
    have hstep := two_mul_catalan_le_succ (n := k + 1) (by omega)
    calc
      2 ^ (k + 2 - 1) = 2 * 2 ^ (k + 1 - 1) := by rw [show k + 2 - 1 = (k + 1 - 1) + 1 by omega, pow_succ']
      _ ≤ 2 * catalan (k + 1) := Nat.mul_le_mul_left 2 ih
      _ ≤ catalan (k + 2) := hstep

private lemma catalan_five : catalan 5 = 42 := by
  have h3 : 5 * catalan 4 = 2 * (2 * 3 + 1) * catalan 3 := catalan_succ_eq 3
  have h4 : 6 * catalan 5 = 2 * (2 * 4 + 1) * catalan 4 := catalan_succ_eq 4
  rw [catalan_three] at h3
  omega

private lemma four_mul_add_one_le_catalan (m : ℕ) (hm : 5 ≤ m) :
    4 * m + 1 ≤ catalan m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hm
  induction d with
  | zero => simp [catalan_five]
  | succ d ih =>
    have hstep := two_mul_catalan_le_succ (n := d + 5) (by omega)
    have ih' := ih (by omega)
    rw [show d + 1 + 5 = d + 5 + 1 by omega]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a273400.main := by
  refine (Set.finite_lt_nat 3).subset fun n hn => ?_
  change (Nat.digits 10 (OMA.S_oeis_a273400.a n)).length < catalan n at hn
  change n < 3
  by_contra hge
  have hn3 : 3 ≤ n := by omega
  have hm5 : 5 ≤ catalan n := by
    calc
      5 = catalan 3 := catalan_three.symm
      _ ≤ catalan n := catalan_mono hn3
  have hlin : 4 * catalan n + 1 ≤ catalan (catalan n) :=
    four_mul_add_one_le_catalan (catalan n) hm5
  have h10 : 10 ^ catalan n ≤ OMA.S_oeis_a273400.a n := by
    calc
      10 ^ catalan n ≤ (2 ^ 4) ^ catalan n := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (4 * catalan n) := by rw [← pow_mul]
      _ ≤ 2 ^ (catalan (catalan n) - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ catalan (catalan (catalan n)) := two_pow_pred_le_catalan _ (by omega)
  have hdig : OMA.S_oeis_a273400.a n < 10 ^ (Nat.digits 10 (OMA.S_oeis_a273400.a n)).length :=
    Nat.lt_base_pow_length_digits (by omega)
  have hpow : 10 ^ (Nat.digits 10 (OMA.S_oeis_a273400.a n)).length ≤ 10 ^ catalan n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega
