import OMAStatements.S_oeis_a115801
import Mathlib

namespace OMA.S_oeis_a115801

def A (m b c h k : ℕ) : Prop := m * k + c = (clmul b k) ^^^ h

def okS (m b c h e : ℕ) : Prop := (m * e + c) % 2 = ((b * e) ^^^ h) % 2
def nxS (m b c h e : ℕ) : ℕ × ℕ := ((m * e + c) / 2, ((b * e) ^^^ h) / 2)

instance (m b c h e : ℕ) : Decidable (okS m b c h e) := by unfold okS; infer_instance

theorem clmul_zero (b : ℕ) : clmul b 0 = 0 := by
  unfold clmul; simp

theorem clmul_two (b k e : ℕ) (he : e < 2) : clmul b (2 * k + e) = (b * e) ^^^ (2 * clmul b k) := by
  have hh : e = 0 ∨ e = 1 := by omega
  rcases hh with h | h
  · subst h
    by_cases hk : k = 0
    · subst hk; simp [clmul_zero]
    · conv_lhs => unfold clmul
      have : ¬ (2 * k + 0 = 0) := by omega
      simp [this, hk]
  · subst h
    conv_lhs => unfold clmul
    have : ¬ (2 * k + 1 = 0) := by omega
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    simp [this, h1, h2]

theorem xor_two (x C : ℕ) : x ^^^ (2 * C) = x % 2 + 2 * ((x / 2) ^^^ C) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases i with _ | i
  · rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    have h1 : (2 * C) % 2 = 0 := by omega
    have h2 : (x % 2 + 2 * ((x / 2) ^^^ C)) % 2 = x % 2 := by omega
    simp [h1, h2]
  · rw [Nat.testBit_xor]
    have h2 : (x % 2 + 2 * ((x / 2) ^^^ C)) / 2 = (x / 2) ^^^ C := by omega
    have h3 : 2 * C / 2 = C := by omega
    simp only [Nat.testBit_succ]
    rw [h2, h3, Nat.testBit_xor]

theorem A_step (m b c h k e : ℕ) (he : e < 2) :
    A m b c h (2 * k + e) ↔ okS m b c h e ∧ A m b (nxS m b c h e).1 (nxS m b c h e).2 k := by
  unfold A okS nxS
  rw [clmul_two b k e he, Nat.xor_right_comm, xor_two, Nat.xor_comm (_ / 2)]
  have hm : m * (2 * k + e) = 2 * (m * k) + m * e := by ring
  rw [hm]
  generalize m * k = a
  generalize m * e = d
  generalize (b * e ^^^ h) = x
  generalize (clmul b k) = C
  simp only
  constructor
  · intro H; refine ⟨by omega, by omega⟩
  · rintro ⟨H1, H2⟩; omega

theorem A_zero (m b c h : ℕ) : A m b c h 0 ↔ c = h := by
  unfold A; simp [clmul_zero]

theorem empty_lemma (m b : ℕ) (E : List (ℕ × ℕ))
    (hE : ∀ s ∈ E, s.1 ≠ s.2 ∧ ∀ e ∈ [0, 1], ¬ okS m b s.1 s.2 e ∨ nxS m b s.1 s.2 e ∈ E) :
    ∀ k (s : ℕ × ℕ), s ∈ E → ¬ A m b s.1 s.2 k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hm
    obtain ⟨h1, h2⟩ := hE _ hm
    by_cases hk : k = 0
    · subst hk; rw [A_zero]; exact h1
    · have hk' : k = 2 * (k / 2) + k % 2 := by omega
      have he : k % 2 < 2 := by omega
      rw [hk', A_step _ _ _ _ _ _ he]
      rintro ⟨hok, hA⟩
      have := h2 (k % 2) (by simp; omega)
      rcases this with n | n
      · exact n hok
      · exact ih (k / 2) (by omega) _ n hA

def condS (m1 b1 m2 b2 : ℕ) (E1 E2 : List (ℕ × ℕ)) (T : List (ℕ × ℕ × ℕ × ℕ))
    (p : ℕ × ℕ × ℕ × ℕ) : Prop :=
  (p.1 = p.2.1 ↔ p.2.2.1 = p.2.2.2) ∧ ∀ e ∈ [0, 1],
    (okS m1 b1 p.1 p.2.1 e ∧ okS m2 b2 p.2.2.1 p.2.2.2 e ∧
      ((nxS m1 b1 p.1 p.2.1 e).1, (nxS m1 b1 p.1 p.2.1 e).2,
        (nxS m2 b2 p.2.2.1 p.2.2.2 e).1, (nxS m2 b2 p.2.2.1 p.2.2.2 e).2) ∈ T) ∨
    (¬ okS m1 b1 p.1 p.2.1 e ∧ ¬ okS m2 b2 p.2.2.1 p.2.2.2 e) ∨
    (¬ okS m1 b1 p.1 p.2.1 e ∧ okS m2 b2 p.2.2.1 p.2.2.2 e ∧ nxS m2 b2 p.2.2.1 p.2.2.2 e ∈ E2) ∨
    (okS m1 b1 p.1 p.2.1 e ∧ ¬ okS m2 b2 p.2.2.1 p.2.2.2 e ∧ nxS m1 b1 p.1 p.2.1 e ∈ E1)

instance (m1 b1 m2 b2 : ℕ) (E1 E2 : List (ℕ × ℕ)) (T : List (ℕ × ℕ × ℕ × ℕ))
    (p : ℕ × ℕ × ℕ × ℕ) : Decidable (condS m1 b1 m2 b2 E1 E2 T p) := by
  unfold condS; infer_instance

theorem bisim (m1 b1 m2 b2 : ℕ) (E1 E2 : List (ℕ × ℕ)) (T : List (ℕ × ℕ × ℕ × ℕ))
    (hE1 : ∀ s ∈ E1, s.1 ≠ s.2 ∧ ∀ e ∈ [0, 1], ¬ okS m1 b1 s.1 s.2 e ∨ nxS m1 b1 s.1 s.2 e ∈ E1)
    (hE2 : ∀ s ∈ E2, s.1 ≠ s.2 ∧ ∀ e ∈ [0, 1], ¬ okS m2 b2 s.1 s.2 e ∨ nxS m2 b2 s.1 s.2 e ∈ E2)
    (hT : ∀ p ∈ T, condS m1 b1 m2 b2 E1 E2 T p) :
    ∀ k c h c2 h2, (c, h, c2, h2) ∈ T → (A m1 b1 c h k ↔ A m2 b2 c2 h2 k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro c h c2 h2 hm
    obtain ⟨h0, hs⟩ := hT _ hm
    simp only at h0 hs
    by_cases hk : k = 0
    · subst hk; rw [A_zero, A_zero]; exact h0
    · have hk' : k = 2 * (k / 2) + k % 2 := by omega
      have he : k % 2 < 2 := by omega
      rw [hk', A_step _ _ _ _ _ _ he, A_step _ _ _ _ _ _ he]
      have := hs (k % 2) (by simp; omega)
      rcases this with ⟨o1, o2, n⟩ | ⟨o1, o2⟩ | ⟨o1, o2, n⟩ | ⟨o1, o2, n⟩
      · simp only [o1, o2, true_and]
        exact ih (k / 2) (by omega) _ _ _ _ n
      · simp only [o1, o2, false_and]
      · have := empty_lemma m2 b2 E2 hE2 (k / 2) _ n
        simp only [o1, o2, false_and, true_and]
        simp [this]
      · have := empty_lemma m1 b1 E1 hE1 (k / 2) _ n
        simp only [o1, o2, false_and, true_and]
        simp [this]

theorem equiv_all : ∀ k : ℕ, 9 * k = clmul 25 k ↔ 15 * k = clmul 19 k := by
  have h := bisim 9 25 15 19 [(0,1), (1,2), (1,3), (2,6), (2,7), (3,4), (3,5), (3,7), (5,12), (5,13), (5,15), (6,14), (6,15), (7,10), (7,11), (8,9)] [(3,4), (5,6), (6,7), (8,9), (9,8), (11,10)] [(0,0,0,0), (1,1,1,1), (2,2,3,3), (2,6,3,4), (3,4,6,7), (3,5,5,6), (4,4,7,7), (4,12,7,9), (5,12,8,9), (5,13,9,8), (6,10,11,13), (6,14,11,10), (7,9,13,15), (8,8,14,14)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro k
  have := h k 0 0 0 0 (by decide +kernel)
  simpa [A] using this

end OMA.S_oeis_a115801

theorem OMA.solution : type_of% @OMA.S_oeis_a115801.main := OMA.S_oeis_a115801.equiv_all

