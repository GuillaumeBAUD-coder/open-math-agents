import OMAStatements.S_oeis_a083451

-- Problem: A083451, n concatenated n times exceeds n^n for n > 1.
-- Credit: @bnb9001

namespace OMA_A083451_Proof

lemma ofDigits_rep (n k : ℕ) :
    Nat.ofDigits 10 (List.flatten (List.replicate (k + 1) (Nat.digits 10 n))) =
      n + 10 ^ (Nat.digits 10 n).length *
        Nat.ofDigits 10 (List.flatten (List.replicate k (Nat.digits 10 n))) := by
  rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, Nat.ofDigits_digits]

lemma ofDigits_rep_ge (n k : ℕ) :
    n * 10 ^ ((Nat.digits 10 n).length * k) ≤
      Nat.ofDigits 10 (List.flatten (List.replicate (k + 1) (Nat.digits 10 n))) := by
  induction k with
  | zero => rw [ofDigits_rep]; simp
  | succ k ih =>
    rw [ofDigits_rep]
    calc n * 10 ^ ((Nat.digits 10 n).length * (k + 1))
        = 10 ^ (Nat.digits 10 n).length * (n * 10 ^ ((Nat.digits 10 n).length * k)) := by ring
      _ ≤ 10 ^ (Nat.digits 10 n).length *
            Nat.ofDigits 10 (List.flatten (List.replicate (k + 1) (Nat.digits 10 n))) :=
          Nat.mul_le_mul_left _ ih
      _ ≤ _ := Nat.le_add_left _ _

end OMA_A083451_Proof

open OMA_A083451_Proof OMA.S_oeis_a083451 in
theorem OMA.solution : type_of% @OMA.S_oeis_a083451.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : k ≠ 0 := by omega
  have hlt : k + 1 < 10 ^ (Nat.digits 10 (k + 1)).length :=
    Nat.lt_base_pow_length_digits (by norm_num)
  have h1 : (k + 1) ^ k < (10 ^ (Nat.digits 10 (k + 1)).length) ^ k :=
    Nat.pow_lt_pow_left hlt hk
  have h2 := ofDigits_rep_ge (k + 1) k
  have key : (k + 1) ^ (k + 1) < concatRep (k + 1) := by
    unfold concatRep
    calc (k + 1) ^ (k + 1) = (k + 1) * (k + 1) ^ k := by ring
      _ < (k + 1) * (10 ^ (Nat.digits 10 (k + 1)).length) ^ k :=
          Nat.mul_lt_mul_of_pos_left h1 (by omega)
      _ = (k + 1) * 10 ^ ((Nat.digits 10 (k + 1)).length * k) := by rw [← pow_mul]
      _ ≤ _ := h2
  have : ((k + 1) ^ (k + 1) : ℕ) < (concatRep (k + 1) : ℕ) := key
  have h3 : (((k + 1) ^ (k + 1) : ℕ) : ℤ) < ((concatRep (k + 1) : ℕ) : ℤ) := by exact_mod_cast this
  push_cast at h3 ⊢
  linarith
