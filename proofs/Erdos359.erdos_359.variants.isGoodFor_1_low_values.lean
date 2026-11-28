import FormalConjectures.ErdosProblems.«359»

namespace OMA359

def B (i : ℕ) : ℕ := [1, 2, 4, 5, 8, 10, 14, 15].getD i 0

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
lemma P : ∀ j < 7, B j < B (j + 1) ∧ (∀ a ≤ j, ∀ b ≤ j, a ≤ b → B (j + 1) ≠ ∑ i ∈ Finset.Icc a b, B i) ∧
    ∀ m < B (j + 1), B j < m → ∃ a ≤ j, ∃ b ≤ j, a ≤ b ∧ m = ∑ i ∈ Finset.Icc a b, B i := by decide

lemma step (A : ℕ → ℕ) (hA : ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i} (A (j + 1)))
    (j : ℕ) (hj : j < 7) (h : ∀ i ≤ j, A i = B i) : A (j + 1) = B (j + 1) := by
  obtain ⟨h1, h2, h3⟩ := P j hj
  have k : ∀ a b, b ≤ j → ∑ i ∈ Finset.Icc a b, A i = ∑ i ∈ Finset.Icc a b, B i :=
    fun a b hb => Finset.sum_congr rfl fun i hi => h i ((Finset.mem_Icc.1 hi).2.trans hb)
  refine (hA j).unique ⟨⟨h j le_rfl ▸ h1, fun a b s => ?_⟩, fun m ⟨hm, s⟩ => not_lt.1 fun l => ?_⟩
  · rcases le_or_gt a b with hab | hab
    · have hb : b ≤ j := by simpa using s (Finset.mem_Icc.2 ⟨hab, le_rfl⟩)
      rw [k a b hb]; exact h2 a (by omega) b hb hab
    · simp [Finset.Icc_eq_empty_of_lt hab]; omega
  · obtain ⟨a, -, b, hb, -, e⟩ := h3 m l (h j le_rfl ▸ hm)
    exact s a b (fun x hx => by simp at hx ⊢; omega) (by rw [k a b hb]; exact e)

end OMA359

open OMA359 in
theorem OMA.solution : type_of% @Erdos359.erdos_359.variants.isGoodFor_1_low_values := by
  rintro A ⟨h0, -, hL⟩
  have e : ∀ j ≤ 7, ∀ i ≤ j, A i = B i := by
    intro j; induction j with
    | zero => intro _ i hi; rw [Nat.le_zero.1 hi]; exact h0
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      exacts [ih (by omega) i (by omega), step A hL j (by omega) (ih (by omega))]
  rw [Set.image_congr (s := Set.Iic 7) (e 7 le_rfl), show Set.Iic 7 = {0, 1, 2, 3, 4, 5, 6, 7} by ext; simp; omega]
  simp [Set.image_insert_eq, B]
