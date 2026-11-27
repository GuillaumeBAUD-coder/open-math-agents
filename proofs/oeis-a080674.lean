import OMAStatements.S_oeis_a080674

namespace OMA.P_oeis_a080674

def P (m : ℕ) : Prop := m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, d ∉ ({0, 1, 2, 3, 4, 5} : Finset ℕ)

instance (m : ℕ) : Decidable (P m) := by unfold P; infer_instance

def T (n : ℕ) : Finset ℕ := (Finset.range (10 ^ n)).filter P

def D : Finset ℕ := {6, 7, 8, 9}

lemma digits_split (q d : ℕ) (hd : d ∈ D) : Nat.digits 10 (d + 10 * q) = d :: Nat.digits 10 q := by
  have h1 : d < 10 := by simp [D] at hd; omega
  have h2 : d ≠ 0 := by simp [D] at hd; omega
  exact Nat.digits_add 10 (by norm_num) d q h1 (Or.inl h2)

lemma T_succ (n : ℕ) :
    T (n + 1) = ((insert 0 (T n)) ×ˢ D).image (fun p : ℕ × ℕ => p.2 + 10 * p.1) := by
  ext m
  simp only [T, P, Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product,
    Finset.mem_insert, Prod.exists]
  constructor
  · rintro ⟨hlt, hm0, hdig⟩
    have hdm : Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
      Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hm0)
    rw [hdm] at hdig
    have hr : m % 10 ∈ D := by
      have := hdig (m % 10) (List.mem_cons_self ..)
      have h10 : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
      simp only [D, Finset.mem_insert, Finset.mem_singleton] at this ⊢
      omega
    refine ⟨m / 10, m % 10, ⟨?_, hr⟩, by omega⟩
    by_cases hq : m / 10 = 0
    · exact Or.inl hq
    · refine Or.inr ⟨?_, hq, fun d hd => hdig d (List.mem_cons_of_mem _ hd)⟩
      rw [pow_succ] at hlt
      omega
  · rintro ⟨q, d, ⟨hq, hd⟩, rfl⟩
    have hd' : 6 ≤ d ∧ d ≤ 9 := by simp [D] at hd; omega
    rw [digits_split q d hd]
    rcases hq with rfl | ⟨hqlt, hq0, hqd⟩
    · refine ⟨?_, by omega, ?_⟩
      · have : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
        rw [pow_succ]; omega
      · intro x hx
        simp only [Nat.digits_zero, List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    · refine ⟨?_, by omega, ?_⟩
      · rw [pow_succ]; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        · exact hqd x hx

lemma card_T_succ (n : ℕ) : (T (n + 1)).card = 4 * ((T n).card + 1) := by
  rw [T_succ, Finset.card_image_of_injOn]
  · rw [Finset.card_product, Finset.card_insert_of_notMem]
    · simp [D]; ring
    · simp [T, P]
  · rintro ⟨q1, d1⟩ h1 ⟨q2, d2⟩ h2 heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, D, Finset.mem_insert,
      Finset.mem_singleton] at h1 h2
    simp only at heq
    have : d1 = d2 := by omega
    subst this
    have : q1 = q2 := by omega
    subst this
    rfl

lemma card_T (n : ℕ) : 3 * (T n).card + 4 = 4 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih => rw [card_T_succ, pow_succ]; omega

end OMA.P_oeis_a080674

theorem OMA.solution : type_of% @OMA.S_oeis_a080674.main := by
  intro n
  have h := OMA.P_oeis_a080674.card_T n
  change (OMA.P_oeis_a080674.T n).card = _
  have h4 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  rw [pow_succ] at h
  symm
  apply Nat.div_eq_of_eq_mul_left (by norm_num)
  rw [Nat.mul_sub, mul_one]
  omega
