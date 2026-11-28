import OMAStatements.S_oeis_a222945
import Mathlib

namespace A222945Proof
open OMA.S_oeis_a222945

lemma nth_eq (R : ℕ → Prop) (f : ℕ → ℕ) (hf : StrictMono f) (h1 : ∀ n, R (f n))
    (h2 : ∀ b, R b → ∃ n, f n = b) : Nat.nth R = f := by
  have hinf : (Set.ofPred R).Infinite := Set.infinite_of_injective_forall_mem hf.injective h1
  have hr : Set.range (Nat.nth R) = Set.range f := by
    rw [Nat.range_nth_of_infinite hinf]
    ext b
    constructor
    · intro hb
      exact h2 b hb
    · rintro ⟨n, rfl⟩
      exact h1 n
  exact ((Nat.nth_strictMono hinf).range_inj hf).mp hr

lemma ends_iff (m : ℕ) : endsIn01 m ↔ (m % 4 = 1 ∧ 5 ≤ m) := by
  unfold endsIn01
  rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | h
  · simp
  · norm_num
  · rw [Nat.digits_def' (by norm_num) (by omega),
      Nat.digits_def' (by norm_num) (by omega : 0 < m / 2)]
    show [m % 2, m / 2 % 2] = [1, 0] ↔ _
    simp only [List.cons.injEq, and_true]
    omega

lemma nth_ends (k : ℕ) : Nat.nth endsIn01 k = 4 * k + 5 := by
  have h := nth_eq endsIn01 (fun k => 4 * k + 5)
    (by
      intro a b hab
      show 4 * a + 5 < 4 * b + 5
      omega)
    (fun n => (ends_iff _).mpr ⟨by omega, by omega⟩)
    (fun b hb => by
      obtain ⟨h1, h2⟩ := (ends_iff b).mp hb
      refine ⟨(b - 5) / 4, ?_⟩
      show 4 * ((b - 5) / 4) + 5 = b
      omega)
  rw [h]

lemma bound (i j k N : ℤ) (hN : 2 ≤ N) (hi1 : -N ≤ i) (hi2 : i ≤ N) (hj1 : -N ≤ j)
    (hj2 : j ≤ N) (hk1 : -N ≤ k) (hk2 : k ≤ N) (hprod : |i * j * k| ≤ N) :
    -2 * N ≤ i + j + k ∧ i + j + k ≤ 2 * N := by
  by_cases hi0 : i = 0
  · subst hi0
    constructor <;> linarith
  by_cases hj0 : j = 0
  · subst hj0
    constructor <;> linarith
  by_cases hk0 : k = 0
  · subst hk0
    constructor <;> linarith
  have hx : 1 ≤ |i| := Int.one_le_abs hi0
  have hy : 1 ≤ |j| := Int.one_le_abs hj0
  have hz : 1 ≤ |k| := Int.one_le_abs hk0
  have hxyz : |i| * |j| * |k| ≤ N := by
    rw [← abs_mul, ← abs_mul]
    exact hprod
  have ha : 0 ≤ (|i| - 1) * (|j| - 1) := mul_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ (|i| * |j| - 1) * (|k| - 1) := mul_nonneg (by nlinarith) (by linarith)
  have h1 : |i| + |j| + |k| ≤ N + 2 := by nlinarith
  constructor <;>
    linarith [neg_abs_le i, le_abs_self i, neg_abs_le j, le_abs_self j, neg_abs_le k,
      le_abs_self k]

lemma sums_eq (n : ℕ) (hn : 2 ≤ n) : sums n = Finset.Icc (-2 * (n : ℤ)) (2 * n) := by
  have hn' : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  ext s
  unfold sums
  constructor
  · intro hs
    rw [Finset.mem_image] at hs
    obtain ⟨⟨i, j, k⟩, hmem, rfl⟩ := hs
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem
    obtain ⟨⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩, hk1, hk2⟩, hprod⟩ := hmem
    rw [Finset.mem_Icc]
    exact bound i j k n hn' hi1 hi2 hj1 hj2 hk1 hk2 hprod
  · intro hs
    rw [Finset.mem_Icc] at hs
    rw [Finset.mem_image]
    have key : ∀ j k : ℤ, -(n : ℤ) ≤ j → j ≤ n → -(n : ℤ) ≤ k → k ≤ n → j + k = s →
        ∃ a ∈ Finset.filter (fun t : ℤ × ℤ × ℤ => |t.1 * t.2.1 * t.2.2| ≤ (n : ℤ))
          (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n),
          a.1 + a.2.1 + a.2.2 = s := by
      intro j k hj1 hj2 hk1 hk2 hjk
      refine ⟨(0, j, k), ?_, by simpa using hjk⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨by omega, by omega⟩, ⟨hj1, hj2⟩, hk1, hk2⟩, by simp⟩
    rcases (show s < -(n : ℤ) ∨ (-(n : ℤ) ≤ s ∧ s ≤ n) ∨ (n : ℤ) < s by omega) with h | h | h
    · exact key (-(n : ℤ)) (s + n) (by omega) (by omega) (by omega) (by omega) (by ring)
    · exact key s 0 h.1 h.2 (by omega) (by omega) (by ring)
    · exact key (n : ℤ) (s - n) (by omega) (by omega) (by omega) (by omega) (by ring)

end A222945Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a222945.main := by
  intro n hn
  unfold OMA.S_oeis_a222945.a OMA.S_oeis_a222945.A004766
  rw [A222945Proof.sums_eq n hn, Int.card_Icc, A222945Proof.nth_ends]
  omega
