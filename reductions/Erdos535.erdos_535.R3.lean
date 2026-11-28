import FormalConjectures.ErdosProblems.«535»

/-!
# Erdős Problem 535: a three-step reduction

`f r N` is the largest size of a set `A ⊆ {1,…,N}` in which no `r`-element subset
has all its pairwise gcds equal.  Erdős conjectured `f r N ≤ N ^ (c / log log N)`.

The difficulty is put in three places.

* `H1` (the deep core, a bound for a single prime-factor layer).  A good set whose
  elements all have at most `k` prime factors *counted with multiplicity* has at
  most `C ^ k` elements.  This is the multiplicity-sensitive strengthening that
  Abbott pointed out (see Erdős [Er73]) and it is what the sunflower method
  proves with an extra `k !`.  The version for exactly `k` prime factors implies
  this one: splitting by the value of `Ω` and summing the geometric series costs
  only a factor `k + 1`, which is absorbed by `C`.

* `H2` (organisation of `{1,…,N}`).  Write every `a` as `s · b`, where `s`
  carries the prime factors at most `y` and `b` the prime factors larger than
  `y`.  If `N < 2 ^ L` then every exponent in `s` is smaller than `L`, so `s`
  takes at most `(L + 1) ^ y` values; if `N < y ^ (K + 1)` then the rough part
  satisfies `Ω b ≤ K`.  Hence one fibre of the small part (cut down to one value
  of `Ω b`) carries at least `A.card / ((L + 1) ^ y * (K + 1))` elements, and its
  quotients have all prime factors larger than `y` and at most `K` of them.

* `H3` (the numerical choice of the cutoffs).  For a fixed `C ≥ 1` one can pick
  `y ≈ log N / (log log N) ^ 2`, `L ≈ log N / log 2` and `K ≈ log N / log y` so
  that the counting loss `((L + 1) ^ y * (K + 1)) * C ^ K` is at most
  `N ^ (c / log log N)` for a constant `c > 0`.

Main then scales the good condition back along `b ↦ s * b` (no coprimality is
needed, the forbidden configuration is preserved by a common factor) and reads
off the bound for `f` from the bound for every good set.
-/

namespace OMA.R_Erdos535_erdos_535_R3

open Erdos535 Filter Real
open ArithmeticFunction
open scoped Omega

/-- A good set whose elements all have at most `k` prime factors, counted with
multiplicity, has at most `C ^ k` elements. -/
def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (k : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 1 ≤ a ∧ Ω a ≤ k) →
      NoConstantPairwiseGcdCoprimeSubsets r A →
      (A.card : ℝ) ≤ C ^ k

/-- Separating the small prime factors of the elements of `A ⊆ {1,…,N}` leaves a
fibre (up to the layer of `Ω`) whose quotients use only primes larger than `y`
and have at most `K` prime factors. -/
def H2 : Prop :=
  ∀ (N y L K : ℕ), 2 ≤ y → N < 2 ^ L → N < y ^ (K + 1) →
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      ∃ (s k : ℕ) (B : Finset ℕ),
        0 < s ∧ k ≤ K ∧ (∀ b ∈ B, 1 ≤ b ∧ Ω b ≤ k) ∧
          A.card ≤ (L + 1) ^ y * (K + 1) * B.card ∧
            ∀ b ∈ B, s * b ∈ A

/-- For every `C ≥ 1` the cutoffs can be chosen so that the counting loss
`((L + 1) ^ y * (K + 1)) * C ^ K` is `N ^ (c / log log N)`. -/
def H3 : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ (N : ℕ) in atTop,
      ∃ (y L K : ℕ), 2 ≤ y ∧ N < 2 ^ L ∧ N < y ^ (K + 1) ∧
        (((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * C ^ K ≤
          (N : ℝ) ^ (c / log (log (N : ℝ)))

/-- The forbidden configuration is preserved when a good set is scaled by a
common positive factor: a constant-gcd `r`-subset of the quotients lifts to a
constant-gcd `r`-subset of the original set. -/
lemma noConstant_of_scaled {r s : ℕ} (hs : 0 < s) {A B : Finset ℕ}
    (hA : ∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d)))
    (hBA : ∀ b ∈ B, s * b ∈ A) :
    NoConstantPairwiseGcdCoprimeSubsets r B := by
  classical
  intro S hSB hSr
  rintro ⟨d, -, hpair, -⟩
  have hinj : Function.Injective (fun b : ℕ => s * b) :=
    fun b c h => Nat.eq_of_mul_eq_mul_left hs h
  refine hA (S.image fun b => s * b) ?_ ?_ ⟨s * d, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact hBA b (hSB hb)
  · rw [Finset.card_image_of_injective _ hinj, hSr]
  · intro x hx z hz hxz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    have hbc : b ≠ c := fun h => hxz (by rw [h])
    rw [Nat.gcd_mul_left, hpair hb hc hbc]

/-- One good set, split by `H2` and bounded by `H1` on the resulting fibre. -/
lemma card_le_of_split (hSplit : H2) {r : ℕ} {C : ℝ} (hC : 1 ≤ C)
    (hLayer : ∀ (k : ℕ) (B : Finset ℕ), (∀ b ∈ B, 1 ≤ b ∧ Ω b ≤ k) →
      NoConstantPairwiseGcdCoprimeSubsets r B → (B.card : ℝ) ≤ C ^ k)
    {N y L K : ℕ} (hy : 2 ≤ y) (hL : N < 2 ^ L) (hK : N < y ^ (K + 1))
    {A : Finset ℕ} (hAN : A ⊆ Finset.Icc 1 N)
    (hA : ∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d))) :
    (A.card : ℝ) ≤ (((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * C ^ K := by
  obtain ⟨s, k, B, hs, hk, hB, hsize, hBA⟩ := hSplit N y L K hy hL hK A hAN
  have hfree : NoConstantPairwiseGcdCoprimeSubsets r B :=
    noConstant_of_scaled hs hA hBA
  have hBcard : (B.card : ℝ) ≤ C ^ k := hLayer k B hB hfree
  have hBle : (B.card : ℝ) ≤ C ^ K := hBcard.trans (pow_le_pow_right₀ hC hk)
  have hsizeR : (A.card : ℝ) ≤ (((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * (B.card : ℝ) := by
    exact_mod_cast hsize
  exact hsizeR.trans (mul_le_mul_of_nonneg_left hBle (by positivity))

/-- `f r N` is bounded by any bound that holds for every good subset of `{1,…,N}`. -/
lemma card_f_le {r N : ℕ} {Bnd : ℝ} (_hr : 0 < r) (hBnd : 0 ≤ Bnd)
    (h : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      (∀ S ⊆ A, S.card = r →
        ¬ (∃ d, (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d))) →
      (A.card : ℝ) ≤ Bnd) :
    (f r N : ℝ) ≤ Bnd := by
  have hle : f r N ≤ Nat.floor Bnd := by
    refine csSup_le' (a := Nat.floor Bnd) ?_
    rintro k ⟨A, hAN, hA, hk⟩
    refine (Nat.le_floor_iff hBnd).mpr ?_
    rw [← hk]
    exact h A hAN hA
  exact (Nat.cast_le.mpr hle).trans (Nat.floor_le hBnd)

theorem main : H1 → H2 → H3 → type_of% @Erdos535.erdos_535 := by
  intro hCore hSplit hCut r hr
  obtain ⟨C, hC, hLayer⟩ := hCore r hr
  obtain ⟨c, hc, hev⟩ := hCut C hC
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev] with N hN
  obtain ⟨y, L, K, hy, hL, hK, hbound⟩ := hN
  refine (card_f_le (r := r) (by omega) (by positivity) ?_).trans hbound
  exact fun A hAN hA => card_le_of_split hSplit hC hLayer hy hL hK hAN hA

end OMA.R_Erdos535_erdos_535_R3
