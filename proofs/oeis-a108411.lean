import OMAStatements.S_oeis_a108411
import Mathlib

/-!
Credit: @ivillar
Proof: let G(n) be the set of subsets S of {0, ..., n} with n not in S + S. For S in G(n+2), the
elements 1, ..., n+1 of S shifted down by one form a set in G(n) (pairs adding up to n + 2 among
1, ..., n+1 become pairs adding up to n), and S contains at most one of 0 and n + 2 (and none of
them can pair with an element of {1, ..., n+1}). Conversely each T in G(n) and each of the three
choices (neither, 0, n + 2) gives a set in G(n+2). This bijection between G(n+2) and
{0, 1, 2} x G(n) gives |G(n+2)| = 3 |G(n)|, and |G(0)| = 1, |G(1)| = 3 are computed directly,
so |G(n)| = 3^floor((n+1)/2) = a(n+1).
-/

namespace OMAA108411Helpers
open Pointwise OMA.S_oeis_a108411

theorem mem_good (n : ℕ) (S : Finset ℕ) :
    S ∈ good n ↔ (∀ x ∈ S, x ≤ n) ∧ ∀ x ∈ S, ∀ y ∈ S, x + y ≠ n := by
  unfold good
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_add, not_exists, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => h2 x hx y hy hxy⟩
    have := Finset.mem_range.mp (h1 hx)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x hx y hy hxy => h2 x hx y hy hxy⟩
    intro x hx
    have := h1 x hx
    exact Finset.mem_range.mpr (by omega)

/-- The elements 1, ..., n+1 of S, shifted down by one. -/
def un (n : ℕ) (S : Finset ℕ) : Finset ℕ := (Finset.range (n + 1)).filter (fun y => y + 1 ∈ S)

/-- Which of 0 (tag 1) and n + 2 (tag 2) lies in S (tag 0: neither). -/
def tg (n : ℕ) (S : Finset ℕ) : ℕ := if 0 ∈ S then 1 else if n + 2 ∈ S then 2 else 0

/-- The inverse map: shift T up by one and add 0 or n + 2 according to the tag. -/
def up (n : ℕ) (p : ℕ × Finset ℕ) : Finset ℕ :=
  (Finset.range (n + 3)).filter
    (fun x => (x = 0 ∧ p.1 = 1) ∨ (x = n + 2 ∧ p.1 = 2) ∨ (1 ≤ x ∧ x ≤ n + 1 ∧ x - 1 ∈ p.2))

theorem mem_un (n : ℕ) (S : Finset ℕ) (y : ℕ) : y ∈ un n S ↔ y ≤ n ∧ y + 1 ∈ S := by
  unfold un
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem mem_up (n t : ℕ) (T : Finset ℕ) (x : ℕ) : x ∈ up n (t, T) ↔
    x < n + 3 ∧ ((x = 0 ∧ t = 1) ∨ (x = n + 2 ∧ t = 2) ∨ (1 ≤ x ∧ x ≤ n + 1 ∧ x - 1 ∈ T)) := by
  unfold up
  simp only [Finset.mem_filter, Finset.mem_range]

theorem tg_lt (n : ℕ) (S : Finset ℕ) : tg n S < 3 := by
  unfold tg
  split_ifs <;> omega

theorem tg_one (n : ℕ) (S : Finset ℕ) : tg n S = 1 ↔ 0 ∈ S := by
  unfold tg
  split_ifs with h1 h2 <;> simp_all

theorem tg_two (n : ℕ) (S : Finset ℕ) (h : ¬ (0 ∈ S ∧ n + 2 ∈ S)) :
    tg n S = 2 ↔ n + 2 ∈ S := by
  unfold tg
  split_ifs with h1 h2 <;> simp_all

theorem step (n : ℕ) : (good (n + 2)).card = 3 * (good n).card := by
  have hc : (Finset.range 3 ×ˢ good n).card = 3 * (good n).card := by
    rw [Finset.card_product, Finset.card_range]
  rw [← hc]
  refine Finset.card_bij' (fun S _ => (tg n S, un n S)) (fun p _ => up n p) ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_good] at hS
    simp only [Finset.mem_product, Finset.mem_range, mem_good]
    refine ⟨tg_lt n S, ?_, ?_⟩
    · intro y hy
      exact ((mem_un n S y).mp hy).1
    · intro x hx y hy hxy
      have hx' := ((mem_un n S x).mp hx).2
      have hy' := ((mem_un n S y).mp hy).2
      exact hS.2 _ hx' _ hy' (by omega)
  · rintro ⟨t, T⟩ hp
    simp only [Finset.mem_product, Finset.mem_range, mem_good] at hp
    obtain ⟨-, -, hT2⟩ := hp
    rw [mem_good]
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · have := ((mem_up n t T x).mp hx).1
      omega
    · rw [mem_up] at hx hy
      obtain ⟨-, hx⟩ := hx
      obtain ⟨-, hy⟩ := hy
      rcases hx with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨hx1, hx2, hx3⟩ <;>
        rcases hy with ⟨rfl, hy⟩ | ⟨rfl, hy⟩ | ⟨hy1, hy2, hy3⟩ <;>
        first | omega | exact fun h => hT2 _ hx3 _ hy3 (by omega)
  · intro S hS
    rw [mem_good] at hS
    have hne : ¬ (0 ∈ S ∧ n + 2 ∈ S) := fun h => hS.2 0 h.1 (n + 2) h.2 (by omega)
    ext x
    rw [mem_up, tg_one, tg_two n S hne]
    constructor
    · rintro ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h1, -, h3⟩⟩
      · exact h
      · exact h
      · have := ((mem_un n S _).mp h3).2
        rwa [Nat.sub_add_cancel h1] at this
    · intro hx
      have hb := hS.1 x hx
      refine ⟨by omega, ?_⟩
      rcases (by omega : x = 0 ∨ x = n + 2 ∨ (1 ≤ x ∧ x ≤ n + 1)) with rfl | rfl | ⟨h1, h2⟩
      · exact Or.inl ⟨rfl, hx⟩
      · exact Or.inr (Or.inl ⟨rfl, hx⟩)
      · refine Or.inr (Or.inr ⟨h1, h2, ?_⟩)
        rw [mem_un, Nat.sub_add_cancel h1]
        exact ⟨by omega, hx⟩
  · rintro ⟨t, T⟩ hp
    simp only [Finset.mem_product, Finset.mem_range, mem_good] at hp
    obtain ⟨ht, hT1, -⟩ := hp
    have h0 : 0 ∈ up n (t, T) ↔ t = 1 := by
      rw [mem_up]
      constructor
      · rintro ⟨-, ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ <;> omega
      · intro h
        exact ⟨by omega, Or.inl ⟨rfl, h⟩⟩
    have h2 : n + 2 ∈ up n (t, T) ↔ t = 2 := by
      rw [mem_up]
      constructor
      · rintro ⟨-, ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩⟩ <;> omega
      · intro h
        exact ⟨by omega, Or.inr (Or.inl ⟨rfl, h⟩)⟩
    have htg : tg n (up n (t, T)) = t := by
      unfold tg
      split_ifs with c1 c2
      · exact (h0.mp c1).symm
      · exact (h2.mp c2).symm
      · have := mt h0.mpr c1
        have := mt h2.mpr c2
        omega
    have hun : un n (up n (t, T)) = T := by
      ext y
      rw [mem_un, mem_up]
      constructor
      · rintro ⟨hy, -, ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩⟩
        · omega
        · omega
        · simpa using h
      · intro hy
        have := hT1 y hy
        exact ⟨this, by omega, Or.inr (Or.inr ⟨by omega, by omega, by simpa using hy⟩)⟩
    rw [htg, hun]

theorem card_good (n : ℕ) : (good n).card = 3 ^ ((n + 1) / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · decide
    · decide
    · show (good (n + 2)).card = 3 ^ ((n + 2 + 1) / 2)
      rw [step n, ih n (by omega), show (n + 2 + 1) / 2 = (n + 1) / 2 + 1 by omega, pow_succ]
      ring

end OMAA108411Helpers

open OMAA108411Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a108411.main := by
  intro n
  exact (card_good n).symm
