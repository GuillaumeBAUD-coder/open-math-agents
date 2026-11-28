import OMAStatements.S_oeis_a106252
import Mathlib.Tactic

-- Credit: @erood (Lean proof with Codex)

namespace OMA.A106252Proof

open Finset OMA.S_oeis_a106252

/-- A positive multiple of d that is at most 2d has only two possibilities. -/
private theorem small_multiple {d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (h : d ∣ k) (bound : k ≤ 2 * d) : k = d ∨ k = 2 * d := by
  obtain ⟨q, rfl⟩ := h
  have hq : q ≤ 2 := Nat.le_of_mul_le_mul_left (by simpa [Nat.mul_comm] using bound) hd
  have hn : q ≠ 0 := by rintro rfl; simp at hk
  rcases (show q = 1 ∨ q = 2 by omega) with rfl | rfl <;> simp [Nat.mul_comm]

private theorem classify {x y z : ℕ} (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hy : y ∣ x + z) (hz : z ∣ x + y) :
    (y = x ∧ z = x) ∨ (y = x ∧ z = 2 * x) ∨ (y = 2 * x ∧ z = 3 * x) := by
  rcases small_multiple (by omega) (by omega) hz (by omega) with heq | heq
  · have hdiv : y ∣ 2 * x := by
      rwa [show x + z = 2 * x + y by omega, Nat.dvd_add_self_right] at hy
    rcases small_multiple (by omega) (by omega) hdiv (by omega) with h | h <;> omega
  · omega

/-- Each shape is parametrized by its first coordinate. -/
private def diagonal : ℕ ↪ ℕ × ℕ × ℕ :=
  ⟨fun x => (x, x, x), fun _ _ h => congrArg Prod.fst h⟩

private def doubleLast : ℕ ↪ ℕ × ℕ × ℕ :=
  ⟨fun x => (x, x, 2 * x), fun _ _ h => congrArg Prod.fst h⟩

private def staircase : ℕ ↪ ℕ × ℕ × ℕ :=
  ⟨fun x => (x, 2 * x, 3 * x), fun _ _ h => congrArg Prod.fst h⟩

private theorem diagonal_apply (x : ℕ) : diagonal x = (x, x, x) := rfl
private theorem doubleLast_apply (x : ℕ) : doubleLast x = (x, x, 2 * x) := rfl
private theorem staircase_apply (x : ℕ) : staircase x = (x, 2 * x, 3 * x) := rfl

private theorem triples_eq (n : ℕ) :
    triples n = ((Icc 1 n).map diagonal ∪ (Icc 1 (n / 2)).map doubleLast) ∪
      (Icc 1 (n / 3)).map staircase := by
  ext ⟨x, y, z⟩
  simp only [triples, mem_filter, mem_product, mem_Icc, mem_union, mem_map,
    diagonal_apply, doubleLast_apply, staircase_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hx, _⟩, ⟨_, _⟩, _, hzn⟩, hxy, hyz, _, hy, hz⟩
    rcases classify hx hxy hyz hy hz with ⟨hy', hz'⟩ | ⟨hy', hz'⟩ | ⟨hy', hz'⟩
    · exact Or.inl (Or.inl ⟨x, ⟨hx, by omega⟩, rfl, hy'.symm, hz'.symm⟩)
    · exact Or.inl (Or.inr ⟨x, ⟨hx, by omega⟩, rfl, hy'.symm, hz'.symm⟩)
    · exact Or.inr ⟨x, ⟨hx, by omega⟩, rfl, hy'.symm, hz'.symm⟩
  · rintro ((⟨k, ⟨hk, hn⟩, rfl, rfl, rfl⟩ | ⟨k, ⟨hk, hn⟩, rfl, rfl, rfl⟩) |
      ⟨k, ⟨hk, hn⟩, rfl, rfl, rfl⟩)
    · exact ⟨by omega, by omega, by omega, ⟨2, by omega⟩, ⟨2, by omega⟩, ⟨2, by omega⟩⟩
    · exact ⟨by omega, by omega, by omega, ⟨3, by omega⟩, ⟨3, by omega⟩, ⟨1, by omega⟩⟩
    · exact ⟨by omega, by omega, by omega, ⟨5, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩⟩

/-- Kimberling's formula follows by counting the three disjoint shapes. -/
private theorem count (n : ℕ) : a n = n + n / 2 + n / 3 := by
  have disj₁ : Disjoint ((Icc 1 n).map diagonal) ((Icc 1 (n / 2)).map doubleLast) := by
    rw [Finset.disjoint_left]
    rintro _ ha hb
    obtain ⟨x, hx, rfl⟩ := mem_map.mp ha
    obtain ⟨y, hy, h⟩ := mem_map.mp hb
    simp only [doubleLast_apply, diagonal_apply, Prod.mk.injEq] at h
    have := (mem_Icc.mp hx).1
    omega
  have disj₂ : Disjoint ((Icc 1 n).map diagonal ∪ (Icc 1 (n / 2)).map doubleLast)
      ((Icc 1 (n / 3)).map staircase) := by
    rw [Finset.disjoint_left]
    rintro _ ha hb
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hb
    have := (mem_Icc.mp hx).1
    rcases mem_union.mp ha with ha | ha <;> obtain ⟨y, _, h⟩ := mem_map.mp ha <;>
      simp only [diagonal_apply, doubleLast_apply, staircase_apply, Prod.mk.injEq] at h <;>
      omega
  rw [a, triples_eq, card_union_of_disjoint disj₂, card_union_of_disjoint disj₁]
  simp [Nat.card_Icc]

end OMA.A106252Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a106252.main := by
  intro n
  simp only [OMA.A106252Proof.count]
  omega
