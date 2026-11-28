import OMAStatements.S_oeis_a008934
import Mathlib

open OMA.S_oeis_a008934

namespace P8934

/-- Explicit finset of tournament-type sequences of length `m + 1` starting at `v`. -/
def F : (m : ℕ) → ℕ → Finset (Fin (m + 1) → ℕ)
  | 0, v => {fun _ => v}
  | m + 1, v => (Finset.Icc 1 v).biUnion
      (fun i => (F m (v + i)).image (fun g => (Fin.cons v g : Fin (m + 2) → ℕ)))

theorem mem_F (m : ℕ) : ∀ (v : ℕ) (a : Fin (m + 1) → ℕ), a ∈ F m v ↔
    (a 0 = v ∧ ∀ i : Fin m, a i.castSucc < a i.succ ∧ a i.succ ≤ 2 * a i.castSucc) := by
  induction m with
  | zero =>
    intro v a
    simp only [F, Finset.mem_singleton, IsEmpty.forall_iff, and_true]
    constructor
    · rintro rfl; rfl
    · intro h; funext x; fin_cases x; exact h
  | succ m ih =>
    intro v a
    simp only [F, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨i, ⟨hi1, hi2⟩, g, hg, rfl⟩
      rw [ih] at hg
      obtain ⟨hg0, hg⟩ := hg
      refine ⟨by simp, ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one, hg0]
        omega
      · rw [← Fin.succ_castSucc]
        simp only [Fin.cons_succ]
        exact hg j
    · rintro ⟨h0, h⟩
      have h1 := h 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, h0] at h1
      refine ⟨a 1 - v, ⟨by omega, by omega⟩, Fin.tail a, ?_, ?_⟩
      · rw [ih]
        refine ⟨?_, ?_⟩
        · simp only [Fin.tail]
          rw [show (Fin.succ (0 : Fin (m + 1))) = 1 from rfl]
          omega
        · intro j
          have := h j.succ
          simp only [Fin.tail]
          rw [Fin.succ_castSucc]
          exact this
      · rw [← h0]
        exact Fin.cons_self_tail a

theorem card_F (m : ℕ) : ∀ v : ℕ, (F m v).card = nest m v := by
  induction m with
  | zero => intro v; simp [F, nest]
  | succ m ih =>
    intro v
    rw [F, nest, Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.card_image_of_injective _ (Fin.cons_right_injective (α := fun _ => ℕ) v), ih]
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_image] at ha hb
      obtain ⟨g, hg, rfl⟩ := ha
      obtain ⟨g', hg', heq⟩ := hb
      have e1 := ((mem_F m _ g).mp hg).1
      have e2 := ((mem_F m _ g').mp hg').1
      have := congrArg (fun f => f 1) heq
      simp only [Fin.cons_one] at this
      apply hij
      omega

theorem A_eq (n : ℕ) : A n = nest n 1 := by
  have : tournamentSeqs n = ↑(F n 1) := by
    ext a
    rw [Finset.mem_coe, mem_F]
    rfl
  rw [A, this, Set.ncard_coe_finset, card_F]

theorem solve : ∀ n : ℕ, 2 ≤ n → A n = nest (n - 1) 2 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [A_eq, nest]
  simp

end P8934

theorem OMA.solution : type_of% @OMA.S_oeis_a008934.main := P8934.solve
