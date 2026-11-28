import OMAStatements.S_mo_107600
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
An elementary scalar-coset argument disproves the proposed density-one limit.
For a pairwise noncommuting set S, scalar translation embeds S x R into the
matrix ring, giving |S|*|R| <= |M_n(R)|. Over ZMod p, the maximum density is
therefore at most 1/p. The final contradiction uses matrices of size 2.
-/

open OMA.S_mo_107600

namespace MO107600Proof

lemma scalar_translate_injective {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [CommRing R] (S : Finset (Matrix ι ι R))
    (hS : (S : Set (Matrix ι ι R)).Pairwise fun A B => ¬ Commute A B) :
    Function.Injective (fun x : S × R => x.1.val + Matrix.scalar ι x.2) := by
  rintro ⟨⟨A, hA⟩, a⟩ ⟨⟨B, hB⟩, b⟩ hab
  change A + Matrix.scalar ι a = B + Matrix.scalar ι b at hab
  have hBA : B = A + Matrix.scalar ι (a - b) := by
    rw [map_sub]
    calc
      B = B + Matrix.scalar ι b - Matrix.scalar ι b := by abel
      _ = A + Matrix.scalar ι a - Matrix.scalar ι b := by rw [hab]
      _ = A + (Matrix.scalar ι a - Matrix.scalar ι b) := by abel
  have hcomm : Commute A B := by
    rw [hBA]
    exact (Commute.refl A).add_right
      (Matrix.scalar_commute (a - b) (Commute.all _) A).symm
  have hAB : A = B := by
    by_contra hne
    exact hS hA hB hne hcomm
  rw [← hAB] at hab
  have hab' : a = b := Matrix.scalar_inj.mp (add_left_cancel hab)
  exact Prod.ext (Subtype.ext hAB) hab'

lemma card_mul_le {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [CommRing R] [Fintype R] (S : Finset (Matrix ι ι R))
    (hS : (S : Set (Matrix ι ι R)).Pairwise fun A B => ¬ Commute A B) :
    S.card * Fintype.card R ≤ Fintype.card (Matrix ι ι R) := by
  simpa using Fintype.card_le_of_injective _ (scalar_translate_injective S hS)

lemma matrix_card_bound {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (S : Finset (Matrix (Fin n) (Fin n) (ZMod p)))
    (hS : (S : Set (Matrix (Fin n) (Fin n) (ZMod p))).Pairwise
      (fun A B => ¬ Commute A B)) :
    S.card * p ≤ p ^ (n * n) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hcard : Fintype.card (Matrix (Fin n) (Fin n) (ZMod p)) = p ^ (n * n) := by
    change Fintype.card (Fin n → Fin n → ZMod p) = _
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul]
  simpa only [ZMod.card, hcard] using card_mul_le S hS

lemma attainable_nonempty (n p : ℕ) : (attainableSizes n p).Nonempty := by
  refine ⟨0, ∅, ?_, rfl⟩
  simp

lemma attainable_bounded (n : ℕ) {p : ℕ} (hp : 0 < p) :
    BddAbove (attainableSizes n p) := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  refine ⟨Fintype.card (Matrix (Fin n) (Fin n) (ZMod p)), ?_⟩
  rintro k ⟨S, _, rfl⟩
  exact Finset.card_le_univ S

lemma max_attained (n : ℕ) {p : ℕ} (hp : 0 < p) :
    maxNoncommuting n p ∈ attainableSizes n p :=
  Nat.sSup_mem (attainable_nonempty n p) (attainable_bounded n hp)

lemma max_mul_le {n p : ℕ} (hn : 0 < n) (hp : 0 < p) :
    maxNoncommuting n p * p ≤ p ^ (n * n) := by
  obtain ⟨S, hS, hcard⟩ := max_attained n hp
  rw [← hcard]
  exact matrix_card_bound hn hp S hS

lemma density_le_reciprocal {n p : ℕ} (hn : 0 < n) (hp : 0 < p) :
    (maxNoncommuting n p : ℝ) / (p : ℝ) ^ (n * n) ≤ 1 / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hbound : (maxNoncommuting n p : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ (n * n) := by
    exact_mod_cast max_mul_le hn hp
  apply (div_le_div_iff₀ (pow_pos hpR _) hpR).2
  simpa only [one_mul] using hbound

end MO107600Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_107600.main) := by
  intro h
  obtain ⟨N, hN⟩ := h 2 (by decide) (1 / 2) (by norm_num)
  obtain ⟨p, hpge, hprime⟩ := Nat.exists_infinite_primes (max N 3)
  have hpN : N ≤ p := le_trans (le_max_left N 3) hpge
  have hp3 : 3 ≤ p := le_trans (le_max_right N 3) hpge
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hprime.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hsmall : (1 : ℝ) / p < 1 / 2 := by
    apply (div_lt_div_iff₀ hpR (by norm_num : (0 : ℝ) < 2)).2
    linarith
  have hbound := MO107600Proof.density_le_reciprocal
    (n := 2) (by decide) hprime.pos
  have hlimit := (abs_lt.mp (hN p hprime hpN)).1
  linarith
