import OMAStatements.S_oeis_a242191

-- Problem: A242191, closed form for 6^n times the expected highest of n dice.
-- Credit: @bnb9001

namespace OMA_A242191_Proof

open OMA.S_oeis_a242191

lemma highest_le {n : ℕ} (f : Fin n → Fin 6) : highest f ≤ 6 := by
  unfold highest
  apply Finset.sup_le
  intro i _
  have := (f i).isLt
  omega

lemma eq_sum_indicator (m : ℕ) (hm : m ≤ 6) :
    m = ∑ k ∈ Finset.range 6, (if k < m then 1 else 0) := by
  rw [Finset.sum_boole, Nat.cast_id]
  have : (Finset.range 6).filter (· < m) = Finset.range m := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

lemma highest_le_iff {n : ℕ} (f : Fin n → Fin 6) (k : ℕ) :
    highest f ≤ k ↔ ∀ i, (f i : ℕ) < k := by
  unfold highest
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_univ, true_implies]
  constructor <;> intro h i <;> have := h i <;> omega

lemma card_le (n k : ℕ) (hk : k < 6) :
    (Finset.univ.filter (fun f : Fin n → Fin 6 => highest f ≤ k)).card = k ^ n := by
  have e : Finset.univ.filter (fun f : Fin n → Fin 6 => highest f ≤ k) =
      Fintype.piFinset (fun _ => Finset.univ.filter (fun j : Fin 6 => (j : ℕ) < k)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, highest_le_iff]
  rw [e, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  interval_cases k <;> decide

lemma card_gt (n k : ℕ) (hk : k < 6) :
    (Finset.univ.filter (fun f : Fin n → Fin 6 => k < highest f)).card = 6 ^ n - k ^ n := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → Fin 6))) (p := fun f => highest f ≤ k)
  rw [card_le n k hk, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  have e : Finset.univ.filter (fun f : Fin n → Fin 6 => ¬ highest f ≤ k) =
      Finset.univ.filter (fun f : Fin n → Fin 6 => k < highest f) := by
    ext f; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  rw [e] at h
  omega

end OMA_A242191_Proof

open OMA_A242191_Proof OMA.S_oeis_a242191 in
theorem OMA.solution : type_of% @OMA.S_oeis_a242191.main := by
  intro n hn
  have h1 : a n = ∑ k ∈ Finset.range 6, (6 ^ n - k ^ n) := by
    unfold a
    calc ∑ f : Fin n → Fin 6, highest f
        = ∑ f : Fin n → Fin 6, ∑ k ∈ Finset.range 6, (if k < highest f then 1 else 0) :=
          Finset.sum_congr rfl fun f _ => eq_sum_indicator _ (highest_le f)
      _ = ∑ k ∈ Finset.range 6, ∑ f : Fin n → Fin 6, (if k < highest f then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.range 6, (6 ^ n - k ^ n) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.sum_boole, Nat.cast_id, card_gt n k (Finset.mem_range.1 hk)]
  rw [h1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have hz : (0 : ℕ) ^ n = 0 := zero_pow (by omega)
  have p1 : 1 ^ n ≤ 6 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have p2 : 2 ^ n ≤ 6 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have p3 : 3 ^ n ≤ 6 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have p4 : 4 ^ n ≤ 6 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have p5 : 5 ^ n ≤ 6 ^ n := Nat.pow_le_pow_left (by norm_num) n
  rw [hz, one_pow] at *
  simp only [Nat.sub_zero]
  push_cast [Nat.cast_sub p1, Nat.cast_sub p2, Nat.cast_sub p3, Nat.cast_sub p4, Nat.cast_sub p5]
  ring
