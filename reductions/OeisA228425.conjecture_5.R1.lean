import FormalConjectures.OEIS.«228425»

/-!
Sun's proposed list has 31 pairs. For every other pair in the specified range,
the table gives an integer between 2 and 39 with no prime polygonal split.
The kernel checks every split of each witness. The remaining hypotheses
concern positive representations for the triangular and nontriangular families.
-/

open OeisA228425

namespace OMA.R_OeisA228425_conjecture_5_R1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem row3 : ∀ m : Fin 101, 3 < m.val →
    (3, m.val) ∈ sunPolygonalPairs ∨
      ∃ n : ℕ, 1 < n ∧ ∀ x : Fin n, 0 < x.val →
        ¬ Nat.Prime (Nat.polygonalNumber 3 x.val + Nat.polygonalNumber m.val (n - x.val)) := by
  let witnesses : Array ℕ := #[0, 0, 0, 0, 0, 3, 0, 3, 3, 3, 6, 3, 14, 3, 3, 3, 6, 3, 14, 3,
        3, 3, 39, 3, 3, 3, 3, 3, 0, 3, 6, 3, 3, 3, 3, 3, 7, 3, 3, 3,
        6, 3, 6, 3, 3, 3, 0, 3, 3, 3, 3, 3, 0, 3, 3, 3, 3, 3, 6, 3,
        6, 3, 3, 3, 3, 3, 6, 3, 3, 3, 6, 3, 6, 3, 3, 3, 3, 3, 14, 3,
        3, 3, 0, 3, 3, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 3, 7, 3, 3, 3,
        6]
  have checked : ∀ m : Fin 101, 3 < m.val →
      (3, m.val) ∈ sunPolygonalPairs ∨
        (1 < witnesses[m.val]! ∧ ∀ x : Fin witnesses[m.val]!, 0 < x.val →
          ¬ Nat.Prime (Nat.polygonalNumber 3 x.val +
            Nat.polygonalNumber m.val (witnesses[m.val]! - x.val))) := by
    dsimp only [witnesses]
    decide +kernel
  intro m hm
  rcases checked m hm with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem row4 : ∀ m : Fin 101, 4 < m.val →
    (4, m.val) ∈ sunPolygonalPairs ∨
      ∃ n : ℕ, 1 < n ∧ ∀ x : Fin n, 0 < x.val →
        ¬ Nat.Prime (Nat.polygonalNumber 4 x.val + Nat.polygonalNumber m.val (n - x.val)) := by
  let witnesses : Array ℕ := #[0, 0, 0, 0, 0, 6, 4, 0, 4, 6, 4, 6, 4, 10, 4, 0, 4, 4, 4, 6,
        4, 8, 4, 6, 4, 0, 4, 0, 4, 4, 4, 4, 4, 6, 4, 6, 4, 0, 4, 6,
        4, 4, 4, 0, 4, 4, 4, 6, 4, 6, 4, 8, 4, 6, 4, 8, 4, 14, 4, 4,
        4, 6, 4, 0, 4, 6, 4, 0, 4, 6, 4, 6, 4, 4, 4, 6, 4, 6, 4, 6,
        4, 10, 4, 4, 4, 12, 4, 4, 4, 4, 4, 10, 4, 8, 4, 6, 4, 0, 4, 6,
        4]
  have checked : ∀ m : Fin 101, 4 < m.val →
      (4, m.val) ∈ sunPolygonalPairs ∨
        (1 < witnesses[m.val]! ∧ ∀ x : Fin witnesses[m.val]!, 0 < x.val →
          ¬ Nat.Prime (Nat.polygonalNumber 4 x.val +
            Nat.polygonalNumber m.val (witnesses[m.val]! - x.val))) := by
    dsimp only [witnesses]
    decide +kernel
  intro m hm
  rcases checked m hm with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem row5 : ∀ m : Fin 101, 5 < m.val →
    (5, m.val) ∈ sunPolygonalPairs ∨
      ∃ n : ℕ, 1 < n ∧ ∀ x : Fin n, 0 < x.val →
        ¬ Nat.Prime (Nat.polygonalNumber 5 x.val + Nat.polygonalNumber m.val (n - x.val)) := by
  let witnesses : Array ℕ := #[0, 0, 0, 0, 0, 0, 6, 3, 3, 3, 6, 3, 6, 3, 3, 3, 6, 3, 6, 3,
        3, 3, 6, 3, 3, 3, 3, 3, 6, 3, 6, 3, 3, 3, 3, 3, 6, 3, 3, 3,
        6, 3, 6, 3, 3, 3, 6, 3, 3, 3, 3, 3, 6, 3, 3, 3, 3, 3, 6, 3,
        6, 3, 3, 3, 3, 3, 6, 3, 3, 3, 6, 3, 6, 3, 3, 3, 3, 3, 6, 3,
        3, 3, 6, 3, 3, 3, 3, 3, 6, 3, 3, 3, 3, 3, 3, 3, 6, 3, 3, 3,
        6]
  have checked : ∀ m : Fin 101, 5 < m.val →
      (5, m.val) ∈ sunPolygonalPairs ∨
        (1 < witnesses[m.val]! ∧ ∀ x : Fin witnesses[m.val]!, 0 < x.val →
          ¬ Nat.Prime (Nat.polygonalNumber 5 x.val +
            Nat.polygonalNumber m.val (witnesses[m.val]! - x.val))) := by
    dsimp only [witnesses]
    decide +kernel
  intro m hm
  rcases checked m hm with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem row6 : ∀ m : Fin 101, 6 < m.val →
    (6, m.val) ∈ sunPolygonalPairs ∨
      ∃ n : ℕ, 1 < n ∧ ∀ x : Fin n, 0 < x.val →
        ¬ Nat.Prime (Nat.polygonalNumber 6 x.val + Nat.polygonalNumber m.val (n - x.val)) := by
  let witnesses : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 6, 4, 4, 4, 6, 4, 17, 4, 14, 4, 6, 4, 4,
        4, 6, 4, 6, 4, 0, 4, 6, 4, 4, 4, 28, 4, 18, 4, 6, 4, 6, 4, 4,
        4, 6, 4, 0, 4, 4, 4, 6, 4, 4, 4, 8, 4, 6, 4, 8, 4, 4, 4, 4,
        4, 9, 4, 4, 4, 6, 4, 6, 4, 4, 4, 6, 4, 0, 4, 8, 4, 6, 4, 4,
        4, 20, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 4, 6, 4, 6, 4, 4,
        4]
  have checked : ∀ m : Fin 101, 6 < m.val →
      (6, m.val) ∈ sunPolygonalPairs ∨
        (1 < witnesses[m.val]! ∧ ∀ x : Fin witnesses[m.val]!, 0 < x.val →
          ¬ Nat.Prime (Nat.polygonalNumber 6 x.val +
            Nat.polygonalNumber m.val (witnesses[m.val]! - x.val))) := by
    dsimp only [witnesses]
    decide +kernel
  intro m hm
  rcases checked m hm with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem row7 : ∀ m : Fin 101, 7 < m.val →
    (7, m.val) ∈ sunPolygonalPairs ∨
      ∃ n : ℕ, 1 < n ∧ ∀ x : Fin n, 0 < x.val →
        ¬ Nat.Prime (Nat.polygonalNumber 7 x.val + Nat.polygonalNumber m.val (n - x.val)) := by
  let witnesses : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 3, 5, 3, 3, 3, 6, 3, 0, 3,
        3, 3, 5, 3, 3, 3, 3, 3, 5, 3, 7, 3, 3, 3, 3, 3, 5, 3, 3, 3,
        12, 3, 5, 3, 3, 3, 6, 3, 3, 3, 3, 3, 5, 3, 3, 3, 3, 3, 5, 3,
        12, 3, 3, 3, 3, 3, 6, 3, 3, 3, 5, 3, 5, 3, 3, 3, 3, 3, 7, 3,
        3, 3, 5, 3, 3, 3, 3, 3, 6, 3, 3, 3, 3, 3, 3, 3, 6, 3, 3, 3,
        0]
  have checked : ∀ m : Fin 101, 7 < m.val →
      (7, m.val) ∈ sunPolygonalPairs ∨
        (1 < witnesses[m.val]! ∧ ∀ x : Fin witnesses[m.val]!, 0 < x.val →
          ¬ Nat.Prime (Nat.polygonalNumber 7 x.val +
            Nat.polygonalNumber m.val (witnesses[m.val]! - x.val))) := by
    dsimp only [witnesses]
    decide +kernel
  intro m hm
  rcases checked m hm with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem row8 : ∀ m : Fin 101, 8 < m.val →
    (8, m.val) ∈ sunPolygonalPairs ∨
      ∃ n : ℕ, 1 < n ∧ ∀ x : Fin n, 0 < x.val →
        ¬ Nat.Prime (Nat.polygonalNumber 8 x.val + Nat.polygonalNumber m.val (n - x.val)) := by
  let witnesses : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 3, 4, 3, 3, 3, 4, 3, 4, 3,
        3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3,
        4, 3, 4, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 3,
        4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 4, 3, 4, 3, 3, 3, 3, 3, 4, 3,
        3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 3, 3, 4, 3, 3, 3,
        4]
  have checked : ∀ m : Fin 101, 8 < m.val →
      (8, m.val) ∈ sunPolygonalPairs ∨
        (1 < witnesses[m.val]! ∧ ∀ x : Fin witnesses[m.val]!, 0 < x.val →
          ¬ Nat.Prime (Nat.polygonalNumber 8 x.val +
            Nat.polygonalNumber m.val (witnesses[m.val]! - x.val))) := by
    dsimp only [witnesses]
    decide +kernel
  intro m hm
  rcases checked m hm with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem row9 : ∀ m : Fin 101, 9 < m.val →
    (9, m.val) ∈ sunPolygonalPairs ∨
      ∃ n : ℕ, 1 < n ∧ ∀ x : Fin n, 0 < x.val →
        ¬ Nat.Prime (Nat.polygonalNumber 9 x.val + Nat.polygonalNumber m.val (n - x.val)) := by
  let witnesses : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 3, 4, 3, 3, 3, 4, 3, 4, 3,
        3, 3, 6, 3, 3, 3, 3, 3, 6, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3,
        4, 3, 4, 3, 3, 3, 4, 3, 3, 3, 3, 3, 14, 3, 3, 3, 3, 3, 7, 3,
        4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 7, 3, 4, 3, 3, 3, 3, 3, 4, 3,
        3, 3, 4, 3, 3, 3, 3, 3, 6, 3, 3, 3, 3, 3, 3, 3, 4, 3, 3, 3,
        7]
  have checked : ∀ m : Fin 101, 9 < m.val →
      (9, m.val) ∈ sunPolygonalPairs ∨
        (1 < witnesses[m.val]! ∧ ∀ x : Fin witnesses[m.val]!, 0 < x.val →
          ¬ Nat.Prime (Nat.polygonalNumber 9 x.val +
            Nat.polygonalNumber m.val (witnesses[m.val]! - x.val))) := by
    dsimp only [witnesses]
    decide +kernel
  intro m hm
  rcases checked m hm with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem row10 : ∀ m : Fin 101, 10 < m.val →
    (10, m.val) ∈ sunPolygonalPairs ∨
      ∃ n : ℕ, 1 < n ∧ ∀ x : Fin n, 0 < x.val →
        ¬ Nat.Prime (Nat.polygonalNumber 10 x.val + Nat.polygonalNumber m.val (n - x.val)) := by
  let witnesses : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 6, 4, 0, 4, 4, 4, 0,
        4, 8, 4, 6, 4, 6, 4, 0, 4, 4, 4, 18, 4, 6, 4, 6, 4, 0, 4, 4,
        4, 4, 4, 6, 4, 4, 4, 6, 4, 14, 4, 22, 4, 6, 4, 0, 4, 25, 4, 4,
        4, 8, 4, 6, 4, 6, 4, 6, 4, 6, 4, 6, 4, 6, 4, 0, 4, 6, 4, 0,
        4, 6, 4, 4, 4, 4, 4, 0, 4, 4, 4, 6, 4, 6, 4, 6, 4, 11, 4, 0,
        4]
  have checked : ∀ m : Fin 101, 10 < m.val →
      (10, m.val) ∈ sunPolygonalPairs ∨
        (1 < witnesses[m.val]! ∧ ∀ x : Fin witnesses[m.val]!, 0 < x.val →
          ¬ Nat.Prime (Nat.polygonalNumber 10 x.val +
            Nat.polygonalNumber m.val (witnesses[m.val]! - x.val))) := by
    dsimp only [witnesses]
    decide +kernel
  intro m hm
  rcases checked m hm with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, h⟩

def H1 : Prop := ∀ m : ℕ, (3, m) ∈ sunPolygonalPairs →
  ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    Nat.Prime (Nat.polygonalNumber 3 x + Nat.polygonalNumber m y)

def H2 : Prop := ∀ k m : ℕ, 4 ≤ k → (k, m) ∈ sunPolygonalPairs →
  ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    Nat.Prime (Nat.polygonalNumber k x + Nat.polygonalNumber m y)

theorem main : H1 → H2 → type_of% @OeisA228425.conjecture_5 := by
  intro triangular others k m hk hlo hkm hm
  constructor
  · intro represents
    let j : Fin 101 := ⟨m, by omega⟩
    have cert : (k, j.val) ∈ sunPolygonalPairs ∨
        ∃ n : ℕ, 1 < n ∧ ∀ x : Fin n, 0 < x.val →
          ¬ Nat.Prime (Nat.polygonalNumber k x.val + Nat.polygonalNumber j.val (n - x.val)) := by
      interval_cases k <;> first
        | exact row3 j hkm
        | exact row4 j hkm
        | exact row5 j hkm
        | exact row6 j hkm
        | exact row7 j hkm
        | exact row8 j hkm
        | exact row9 j hkm
        | exact row10 j hkm
    rcases cert with listed | ⟨n, hn, blocks⟩
    · exact listed
    · obtain ⟨x, y, hx, hy, sum, prime⟩ := represents n hn
      have no := blocks ⟨x, by omega⟩ hx
      have hsub : n - x = y := by omega
      exact False.elim (no (by simpa only [j, hsub] using prime))
  · intro listed
    by_cases hk3 : k = 3
    · subst k
      exact triangular m listed
    · exact others k m (by omega) listed

end OMA.R_OeisA228425_conjecture_5_R1
