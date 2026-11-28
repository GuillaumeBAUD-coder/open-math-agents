import FormalConjectures.Paper.LatinSquare
import Mathlib

namespace OMA.R_LatinSquare_oddOrderLatinSquareTransversal_R1
open LatinSquare

/-- Ryser's conjecture in orders at most nine, for the squares not isotopic to the Cayley table
of a group nor to a symmetric Latin square (known by exhaustive computation). -/
def H1 : Prop := ∀ (n : ℕ), Odd n → n ≤ 9 → ∀ L : LatinSquare n,
  (¬ ∃ (G : Type) (_ : Group G) (e : Fin n ≃ G) (α β γ : Equiv.Perm (Fin n)),
      ∀ i j, L.mat i j = γ (e.symm (e (α i) * e (β j)))) →
  (¬ ∃ (S : LatinSquare n), (∀ i j, S.mat i j = S.mat j i) ∧
      ∃ (α β γ : Equiv.Perm (Fin n)), ∀ i j, L.mat i j = γ (S.mat (α i) (β j))) →
  ∃ σ, IsTransversal L σ

/-- Ryser's conjecture in odd orders at least eleven, for the squares not isotopic to the Cayley
table of a group nor to a symmetric Latin square (the open part). -/
def H2 : Prop := ∀ (n : ℕ), Odd n → 11 ≤ n → ∀ L : LatinSquare n,
  (¬ ∃ (G : Type) (_ : Group G) (e : Fin n ≃ G) (α β γ : Equiv.Perm (Fin n)),
      ∀ i j, L.mat i j = γ (e.symm (e (α i) * e (β j)))) →
  (¬ ∃ (S : LatinSquare n), (∀ i j, S.mat i j = S.mat j i) ∧
      ∃ (α β γ : Equiv.Perm (Fin n)), ∀ i j, L.mat i j = γ (S.mat (α i) (β j))) →
  ∃ σ, IsTransversal L σ

/-- In a finite group of odd order, squaring is injective. -/
theorem sq_injective_of_odd {G : Type} [Group G] [Fintype G] (h : Odd (Fintype.card G)) :
    Function.Injective (fun x : G => x * x) := by
  obtain ⟨k, hk⟩ := h
  have key : ∀ x : G, x = (x * x) ^ (k + 1) := by
    intro x
    have h1 : x ^ Fintype.card G = 1 := pow_card_eq_one
    rw [← pow_two, ← pow_mul]
    calc x = x ^ (Fintype.card G + 1) := by rw [pow_succ, h1, one_mul]
      _ = x ^ (2 * (k + 1)) := by congr 1; omega
  intro x y hxy
  rw [key x, key y]
  exact congrArg (fun z => z ^ (k + 1)) hxy

/-- Odd-order Latin squares isotopic to a group table have a transversal: `σ = β⁻¹ ∘ α`. -/
theorem groupBased_transversal {n : ℕ} (hn : Odd n) (L : LatinSquare n)
    (hL : ∃ (G : Type) (_ : Group G) (e : Fin n ≃ G) (α β γ : Equiv.Perm (Fin n)),
      ∀ i j, L.mat i j = γ (e.symm (e (α i) * e (β j)))) : ∃ σ, IsTransversal L σ := by
  obtain ⟨G, _, e, α, β, γ, hmat⟩ := hL
  let _ : Fintype G := Fintype.ofEquiv (Fin n) e
  have hcard : Fintype.card G = n := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hsq := sq_injective_of_odd (G := G) (hcard ▸ hn)
  refine ⟨fun i => β.symm (α i), ?_, ?_⟩
  · intro i j hij
    exact α.injective (β.symm.injective hij)
  · intro i j hij
    simp only [hmat, Equiv.apply_symm_apply] at hij
    exact α.injective (e.injective (hsq (e.symm.injective (γ.injective hij))))

/-- In a symmetric Latin square of odd order, the main diagonal hits every symbol
(each symbol's off-diagonal cells pair up under transposition). -/
theorem symm_diag_surjective {n : ℕ} (hn : Odd n) (S : LatinSquare n)
    (hS : ∀ i j, S.mat i j = S.mat j i) : Function.Surjective (fun i => S.mat i i) := by
  intro s
  have hsurj : ∀ i, Function.Surjective (S.mat i) := fun i =>
    Finite.injective_iff_surjective.mp (S.row_injective i)
  let c : Fin n → Fin n := fun i => Classical.choose (hsurj i s)
  have hc : ∀ i, S.mat i (c i) = s := fun i => Classical.choose_spec (hsurj i s)
  have hinv : Function.Involutive c := by
    intro i
    apply S.row_injective (c i)
    rw [hc (c i), hS, hc i]
  let τ : Equiv.Perm (Fin n) := hinv.toPerm c
  have hτ : τ ^ 2 ^ 1 = 1 := by
    ext i
    simp [τ, sq, hinv i]
  have h2 : ¬ 2 ∣ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    exact Nat.odd_iff.mp hn |> fun h => by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime h2 hτ
  refine ⟨a, ?_⟩
  have : c a = a := ha
  have h := hc a
  rw [this] at h
  exact h

/-- Odd-order Latin squares isotopic to a symmetric Latin square have a transversal. -/
theorem symmetricBased_transversal {n : ℕ} (hn : Odd n) (L : LatinSquare n)
    (hL : ∃ (S : LatinSquare n), (∀ i j, S.mat i j = S.mat j i) ∧
      ∃ (α β γ : Equiv.Perm (Fin n)), ∀ i j, L.mat i j = γ (S.mat (α i) (β j))) :
    ∃ σ, IsTransversal L σ := by
  obtain ⟨S, hS, α, β, γ, hmat⟩ := hL
  have hd : Function.Injective (fun i => S.mat i i) :=
    Finite.injective_iff_surjective.mpr (symm_diag_surjective hn S hS)
  refine ⟨fun i => β.symm (α i), ?_, ?_⟩
  · intro i j hij
    exact α.injective (β.symm.injective hij)
  · intro i j hij
    simp only [hmat, Equiv.apply_symm_apply] at hij
    exact α.injective (hd (γ.injective hij))

theorem main : H1 → H2 → type_of% @LatinSquare.oddOrderLatinSquareTransversal := by
  intro h1 h2 n hn L
  by_cases hg : ∃ (G : Type) (_ : Group G) (e : Fin n ≃ G) (α β γ : Equiv.Perm (Fin n)),
      ∀ i j, L.mat i j = γ (e.symm (e (α i) * e (β j)))
  · exact groupBased_transversal hn L hg
  by_cases hs : ∃ (S : LatinSquare n), (∀ i j, S.mat i j = S.mat j i) ∧
      ∃ (α β γ : Equiv.Perm (Fin n)), ∀ i j, L.mat i j = γ (S.mat (α i) (β j))
  · exact symmetricBased_transversal hn L hs
  by_cases hle : n ≤ 9
  · exact h1 n hn hle L hg hs
  · have h11 : 11 ≤ n := by
      obtain ⟨k, hk⟩ := hn
      omega
    exact h2 n hn h11 L hg hs

end OMA.R_LatinSquare_oddOrderLatinSquareTransversal_R1
