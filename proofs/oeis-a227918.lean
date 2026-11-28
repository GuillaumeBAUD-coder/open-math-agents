import OMAStatements.S_oeis_a227918
import Mathlib

/-!
# Proof of OEIS A227918 Recurrence (R. J. Mathar's Conjecture)

We prove the stronger two-term recurrence for all `n >= 3`:
  `weightedCount n - n * weightedCount (n - 1) = 1 + 4 * (-1)^n`
from which the four-term recurrence for all `n >= 5` follows immediately by subtracting
the `n - 2` instance from the `n` instance.

The proof evaluates a finite double sum over pairs `(p, c)` where `p : Equiv.Perm (Fin n)`
and `c : Fin (n - 1) -> Bool` dominates the ascent vector of `p` (so `p` is strictly
decreasing on every false-run of `c`), weighted by `blockWeight (runLens c)`:
- Summing over `c` first (Way 1) collapses each maximal decreasing run via 1D composition
  identities to `weightedCount n + (3 - n)`.
- Summing over `p` first (Way 2) counts permutations compatible with `c` by the multinomial
  coefficient `multinomial (runLens c)`, and evaluates the resulting sum in terms of the
  derangement sequence `D(n)` and a telescoping sum `U(n)`.
-/

namespace A227918Proof

open Finset OMA.S_oeis_a227918

/-! ### Section 1: Run lengths, weights, and multinomials on lists -/

def fW (m : ℕ) : ℤ := (m : ℤ) - 1
def gW (m : ℕ) : ℤ := 2 - (m : ℤ)

def runLensAux : ℕ → List Bool → List ℕ
  | r, [] => [r]
  | r, true :: rest => r :: runLensAux 1 rest
  | r, false :: rest => runLensAux (r + 1) rest

def runLens (l : List Bool) : List ℕ := runLensAux 1 l

def intProd : List ℕ → ℤ
  | [] => 1
  | m :: rest => fW m * intProd rest

def headWeight : List ℕ → ℤ
  | [] => 0
  | m :: rest => gW m * intProd rest

def tailWeight : List ℕ → ℤ
  | [] => 0
  | [m] => gW m
  | m :: rest => fW m * tailWeight rest

def blockWeight : List ℕ → ℤ
  | [] => 0
  | m :: rest => gW m * tailWeight rest

def multinomial : List ℕ → ℕ
  | [] => 1
  | m :: rest => (m + rest.sum).choose m * multinomial rest

lemma runLensAux_ne_nil (r : ℕ) (l : List Bool) : runLensAux r l ≠ [] := by
  induction l generalizing r with
  | nil => simp [runLensAux]
  | cons b rest ih =>
    cases b
    · exact ih (r + 1)
    · simp [runLensAux]

lemma runLens_ne_nil (l : List Bool) : runLens l ≠ [] := runLensAux_ne_nil 1 l

lemma runLensAux_sum (r : ℕ) (l : List Bool) : (runLensAux r l).sum = r + l.length := by
  induction l generalizing r with
  | nil => simp [runLensAux]
  | cons b rest ih =>
    cases b
    · simp only [runLensAux, ih, List.length_cons]; omega
    · simp only [runLensAux, List.sum_cons, ih, List.length_cons]; omega

lemma runLens_sum (l : List Bool) : (runLens l).sum = l.length + 1 := by
  simpa [runLens, add_comm] using runLensAux_sum 1 l

lemma runLensAux_replicate_false (r k : ℕ) :
    runLensAux r (List.replicate k false) = [r + k] := by
  induction k generalizing r with
  | zero => simp [runLensAux]
  | succ k ih =>
    simp only [List.replicate_succ, runLensAux, ih]
    congr 1; omega

lemma runLens_replicate_false (k : ℕ) : runLens (List.replicate k false) = [k + 1] := by
  simpa [runLens, add_comm] using runLensAux_replicate_false 1 k

lemma runLensAux_append_true (r : ℕ) (l1 l2 : List Bool) :
    runLensAux r (l1 ++ true :: l2) = runLensAux r l1 ++ runLens l2 := by
  induction l1 generalizing r with
  | nil => simp [runLensAux, runLens]
  | cons b rest ih =>
    cases b
    · simp only [List.cons_append, runLensAux, ih]
    · simp only [List.cons_append, runLensAux, ih, List.cons_append]

lemma runLens_append_true (l1 l2 : List Bool) :
    runLens (l1 ++ true :: l2) = runLens l1 ++ runLens l2 :=
  runLensAux_append_true 1 l1 l2

lemma eq_replicate_false_of_not_mem_true {l : List Bool} (h : true ∉ l) :
    l = List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
    cases b
    · simp only [List.length_cons, List.replicate_succ]
      congr 1
      exact ih (fun hm => h (List.mem_cons_of_mem _ hm))
    · exact absurd List.mem_cons_self h

lemma exists_first_true {l : List Bool} (h : true ∈ l) :
    ∃ k rest, l = List.replicate k false ++ true :: rest := by
  induction l with
  | nil => simp at h
  | cons b rest ih =>
    cases b
    · have hmem : true ∈ rest := by
        rcases List.mem_cons.1 h with hfalse | hm
        · exact absurd hfalse (by decide)
        · exact hm
      rcases ih hmem with ⟨k, r, hr⟩
      exact ⟨k + 1, r, by rw [List.replicate_succ, List.cons_append, hr]⟩
    · exact ⟨0, rest, rfl⟩

lemma runLens_reverse (l : List Bool) : runLens l.reverse = (runLens l).reverse := by
  have hstrong : ∀ n (l : List Bool), l.length = n → runLens l.reverse = (runLens l).reverse := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hl
      by_cases hmem : true ∈ l
      · rcases exists_first_true hmem with ⟨k, rest, rfl⟩
        have hlen : rest.length < n := by simp at hl; omega
        rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
          runLens_append_true, runLens_append_true, List.reverse_append,
          ih rest.length hlen rest rfl, List.reverse_replicate, runLens_replicate_false,
          List.reverse_singleton]
      · have hrep := eq_replicate_false_of_not_mem_true hmem
        rw [hrep, List.reverse_replicate, runLens_replicate_false, List.reverse_singleton]
  exact hstrong l.length l rfl

lemma intProd_append (a b : List ℕ) : intProd (a ++ b) = intProd a * intProd b := by
  induction a with
  | nil => simp [intProd]
  | cons m rest ih => simp [intProd, ih, mul_assoc]

lemma tailWeight_append (a b : List ℕ) (hb : b ≠ []) :
    tailWeight (a ++ b) = intProd a * tailWeight b := by
  induction a with
  | nil => simp [intProd]
  | cons m rest ih =>
    cases h : rest ++ b with
    | nil => exact absurd (List.append_eq_nil_iff.1 h).2 hb
    | cons x xs =>
      simp only [List.cons_append, intProd]
      rw [show tailWeight (m :: (rest ++ b)) = fW m * tailWeight (rest ++ b) by rw [h]; rfl]
      rw [ih, mul_assoc]

lemma blockWeight_append (a b : List ℕ) (ha : a ≠ []) (hb : b ≠ []) :
    blockWeight (a ++ b) = headWeight a * tailWeight b := by
  cases a with
  | nil => exact absurd rfl ha
  | cons m rest =>
    simp only [List.cons_append, blockWeight, headWeight, tailWeight_append rest b hb, mul_assoc]

lemma intProd_reverse (a : List ℕ) : intProd a.reverse = intProd a := by
  induction a with
  | nil => simp [intProd]
  | cons m rest ih =>
    simp only [List.reverse_cons, intProd_append, ih, intProd, mul_one, mul_comm]

lemma tailWeight_reverse (a : List ℕ) : tailWeight a.reverse = headWeight a := by
  cases a with
  | nil => simp [tailWeight, headWeight]
  | cons m rest =>
    simp only [List.reverse_cons, tailWeight_append rest.reverse [m] (List.cons_ne_nil _ _),
      intProd_reverse, tailWeight, headWeight, mul_comm]

lemma multinomial_mul_prod_factorial (a : List ℕ) :
    multinomial a * (a.map Nat.factorial).prod = a.sum.factorial := by
  induction a with
  | nil => simp [multinomial]
  | cons m rest ih =>
    simp only [multinomial, List.map_cons, List.prod_cons, List.sum_cons]
    calc (m + rest.sum).choose m * multinomial rest * (m.factorial * (rest.map Nat.factorial).prod)
        = (m + rest.sum).choose m * m.factorial * (multinomial rest * (rest.map Nat.factorial).prod) := by ring
      _ = (m + rest.sum).choose m * m.factorial * rest.sum.factorial := by rw [ih]
      _ = (m + rest.sum).factorial := by
          have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m rest.sum)
          simpa [Nat.add_sub_cancel_left] using this

lemma multinomial_reverse (a : List ℕ) : multinomial a.reverse = multinomial a := by
  have hpos : 0 < (a.map Nat.factorial).prod := by
    induction a with
    | nil => simp
    | cons m rest ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_pos (Nat.factorial_pos m) ih
  apply Nat.eq_of_mul_eq_mul_right hpos
  have h1 := multinomial_mul_prod_factorial a.reverse
  rw [List.map_reverse, List.prod_reverse, List.sum_reverse] at h1
  rw [h1, multinomial_mul_prod_factorial]

/-! ### Section 2: `superLists` and Way 1 identities -/

def superLists : List Bool → List (List Bool)
  | [] => [[]]
  | true :: rest => (superLists rest).map (true :: ·)
  | false :: rest => (superLists rest).map (false :: ·) ++ (superLists rest).map (true :: ·)

lemma superLists_map_sum_append_true (l1 l2 : List Bool) (F : List Bool → ℤ) :
    ((superLists (l1 ++ true :: l2)).map F).sum =
      ((superLists l1).map (fun c1 =>
        ((superLists l2).map (fun c2 => F (c1 ++ true :: c2))).sum)).sum := by
  induction l1 generalizing F with
  | nil => simp [superLists, List.map_map, Function.comp_def]
  | cons b rest ih =>
    cases b
    · simp only [List.cons_append, superLists, List.map_append, List.sum_append,
        List.map_map, Function.comp_def]
      rw [ih (fun x => F (false :: x)), ih (fun x => F (true :: x))]
    · simp only [List.cons_append, superLists, List.map_map, Function.comp_def]
      rw [ih (fun x => F (true :: x))]

lemma sum_superLists_replicate_false (k : ℕ) (F : List Bool → ℤ) :
    ((superLists (List.replicate k false)).map F).sum =
      F (List.replicate k false) +
        ∑ j ∈ range k, ((superLists (List.replicate (k - 1 - j) false)).map
          (fun c => F (List.replicate j false ++ true :: c))).sum := by
  induction k generalizing F with
  | zero => simp [superLists]
  | succ k ih =>
    simp only [List.replicate_succ, superLists, List.map_append, List.sum_append,
      List.map_map, Function.comp_def]
    rw [ih (fun x => F (false :: x)), Finset.sum_range_succ']
    simp only [Nat.succ_sub_one, Nat.sub_zero, List.replicate_zero, List.nil_append]
    have hcongr : ∑ j ∈ range k,
        ((superLists (List.replicate (k - 1 - j) false)).map
          (fun c => F (false :: (List.replicate j false ++ true :: c)))).sum =
        ∑ j ∈ range k,
        ((superLists (List.replicate (k - (j + 1)) false)).map
          (fun c => F (List.replicate (j + 1) false ++ true :: c))).sum := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show k - (j + 1) = k - 1 - j by omega]
      simp only [List.replicate_succ, List.cons_append]
    rw [hcongr]
    ring

def sumInt (l : List Bool) : ℤ := ((superLists l).map (fun c => intProd (runLens c))).sum
def sumHead (l : List Bool) : ℤ := ((superLists l).map (fun c => headWeight (runLens c))).sum
def sumTail (l : List Bool) : ℤ := ((superLists l).map (fun c => tailWeight (runLens c))).sum
def sumBlock (l : List Bool) : ℤ := ((superLists l).map (fun c => blockWeight (runLens c))).sum

lemma sumTail_append_true (l1 l2 : List Bool) :
    sumTail (l1 ++ true :: l2) = sumInt l1 * sumTail l2 := by
  unfold sumTail sumInt
  rw [superLists_map_sum_append_true]
  have hmap : (superLists l1).map (fun c1 =>
      ((superLists l2).map (fun c2 => tailWeight (runLens (c1 ++ true :: c2)))).sum) =
      (superLists l1).map (fun c1 =>
        intProd (runLens c1) * ((superLists l2).map (fun c2 => tailWeight (runLens c2))).sum) := by
    refine List.map_congr_left fun c1 _ => ?_
    have hinner : (superLists l2).map (fun c2 => tailWeight (runLens (c1 ++ true :: c2))) =
        (superLists l2).map (fun c2 => intProd (runLens c1) * tailWeight (runLens c2)) := by
      refine List.map_congr_left fun c2 _ => ?_
      rw [runLens_append_true, tailWeight_append _ _ (runLens_ne_nil c2)]
    rw [hinner, ← List.sum_map_mul_left]
  rw [hmap, List.sum_map_mul_right]

lemma sumBlock_append_true (l1 l2 : List Bool) :
    sumBlock (l1 ++ true :: l2) = sumHead l1 * sumTail l2 := by
  unfold sumBlock sumHead sumTail
  rw [superLists_map_sum_append_true]
  have hmap : (superLists l1).map (fun c1 =>
      ((superLists l2).map (fun c2 => blockWeight (runLens (c1 ++ true :: c2)))).sum) =
      (superLists l1).map (fun c1 =>
        headWeight (runLens c1) * ((superLists l2).map (fun c2 => tailWeight (runLens c2))).sum) := by
    refine List.map_congr_left fun c1 _ => ?_
    have hinner : (superLists l2).map (fun c2 => blockWeight (runLens (c1 ++ true :: c2))) =
        (superLists l2).map (fun c2 => headWeight (runLens c1) * tailWeight (runLens c2)) := by
      refine List.map_congr_left fun c2 _ => ?_
      rw [runLens_append_true, blockWeight_append _ _ (runLens_ne_nil c1) (runLens_ne_nil c2)]
    rw [hinner, ← List.sum_map_mul_left]
  rw [hmap, List.sum_map_mul_right]

lemma sum_lin_pow2 (k : ℕ) :
    ∑ i ∈ range (k + 1), ((k - i : ℕ) : ℤ) * (2 : ℤ) ^ i =
      (2 : ℤ) ^ (k + 1) - ((k : ℤ) + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, pow_zero, mul_one]
    have hshift : ∑ i ∈ range (k + 1), ((k + 1 - (i + 1) : ℕ) : ℤ) * (2 : ℤ) ^ (i + 1) =
        2 * ∑ i ∈ range (k + 1), ((k - i : ℕ) : ℤ) * (2 : ℤ) ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show k + 1 - (i + 1) = k - i by omega, pow_succ]
      ring
    rw [hshift, ih]
    push_cast
    rw [pow_succ (2 : ℤ) (k + 1)]
    ring

lemma sum_pow2_int (r : ℕ) :
    ∑ i ∈ range r, (2 : ℤ) ^ i = (2 : ℤ) ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

lemma sumInt_replicate_false (k : ℕ) :
    sumInt (List.replicate k false) = if k = 0 then 0 else (2 : ℤ) ^ (k - 1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    unfold sumInt
    rw [sum_superLists_replicate_false, runLens_replicate_false]
    simp only [intProd, mul_one]
    have hterm : ∀ j ∈ range k,
        ((superLists (List.replicate (k - 1 - j) false)).map
          (fun c => intProd (runLens (List.replicate j false ++ true :: c)))).sum =
        fW (j + 1) * sumInt (List.replicate (k - 1 - j) false) := by
      intro j _
      unfold sumInt
      have hm : (superLists (List.replicate (k - 1 - j) false)).map
          (fun c => intProd (runLens (List.replicate j false ++ true :: c))) =
          (superLists (List.replicate (k - 1 - j) false)).map
            (fun c => fW (j + 1) * intProd (runLens c)) := by
        refine List.map_congr_left fun c _ => ?_
        rw [runLens_append_true, runLens_replicate_false, List.singleton_append, intProd]
      rw [hm, ← List.sum_map_mul_left]
    rw [Finset.sum_congr rfl hterm]
    match k with
    | 0 => simp [fW]
    | 1 => simp [fW, sumInt, superLists, runLens, runLensAux, intProd]
    | k + 2 =>
      simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte]
      have hsub : ∀ j, k + 2 - 1 - j = k + 1 - j := fun j => by omega
      simp_rw [hsub]
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self]
      rw [ih 0 (by omega)]
      simp only [↓reduceIte, mul_zero, add_zero]
      have hbody : ∑ j ∈ range (k + 1), fW (j + 1) * sumInt (List.replicate (k + 1 - j) false) =
          ∑ i ∈ range (k + 1), ((k - i : ℕ) : ℤ) * (2 : ℤ) ^ i := by
        rw [← Finset.sum_range_reflect (fun i => ((k - i : ℕ) : ℤ) * (2 : ℤ) ^ i) (k + 1)]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ k := Nat.le_of_lt_succ (mem_range.1 hj)
        rw [ih (k + 1 - j) (by omega)]
        have hne : k + 1 - j ≠ 0 := by omega
        simp only [hne, ↓reduceIte, fW]
        rw [show k - (k + 1 - 1 - j) = j by omega,
          show k + 1 - j - 1 = k - j by omega,
          show k + 1 - 1 - j = k - j by omega]
        push_cast; ring
      rw [hbody, sum_lin_pow2]
      simp only [fW]; push_cast; ring

lemma sumHead_replicate_false (k : ℕ) :
    sumHead (List.replicate k false) = if k = 0 then 1 else 0 := by
  unfold sumHead
  rw [sum_superLists_replicate_false, runLens_replicate_false]
  have hterm : ∀ j ∈ range k,
      ((superLists (List.replicate (k - 1 - j) false)).map
        (fun c => headWeight (runLens (List.replicate j false ++ true :: c)))).sum =
      gW (j + 1) * sumInt (List.replicate (k - 1 - j) false) := by
    intro j _
    unfold sumInt
    have hm : (superLists (List.replicate (k - 1 - j) false)).map
        (fun c => headWeight (runLens (List.replicate j false ++ true :: c))) =
        (superLists (List.replicate (k - 1 - j) false)).map
          (fun c => gW (j + 1) * intProd (runLens c)) := by
      refine List.map_congr_left fun c _ => ?_
      rw [runLens_append_true, runLens_replicate_false, List.singleton_append, headWeight]
    rw [hm, ← List.sum_map_mul_left]
  rw [Finset.sum_congr rfl hterm]
  simp only [headWeight, intProd, mul_one]
  match k with
  | 0 => simp [gW]
  | 1 => simp [gW, sumInt, superLists, runLens, runLensAux, intProd, fW]
  | k + 2 =>
    simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte]
    have hsub : ∀ j, k + 2 - 1 - j = k + 1 - j := fun j => by omega
    simp_rw [hsub]
    rw [Finset.sum_range_succ, Nat.sub_self]
    have h0 : sumInt (List.replicate 0 false) = 0 := sumInt_replicate_false 0
    rw [h0, mul_zero, add_zero]
    have hsplit : ∑ j ∈ range (k + 1), gW (j + 1) * sumInt (List.replicate (k + 1 - j) false) =
        (∑ j ∈ range (k + 1), sumInt (List.replicate (k + 1 - j) false)) -
        (∑ j ∈ range (k + 1), fW (j + 1) * sumInt (List.replicate (k + 1 - j) false)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [gW, fW]; push_cast; ring
    rw [hsplit]
    have hs1 : ∑ j ∈ range (k + 1), sumInt (List.replicate (k + 1 - j) false) =
        (2 : ℤ) ^ (k + 1) - 1 := by
      rw [← sum_pow2_int (k + 1), ← Finset.sum_range_reflect (fun i => (2 : ℤ) ^ i) (k + 1)]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ k := Nat.le_of_lt_succ (mem_range.1 hj)
      rw [sumInt_replicate_false]
      have hne : k + 1 - j ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      rw [show k + 1 - j - 1 = k + 1 - 1 - j by omega]
    have hs2 : ∑ j ∈ range (k + 1), fW (j + 1) * sumInt (List.replicate (k + 1 - j) false) =
        (2 : ℤ) ^ (k + 1) - ((k : ℤ) + 2) := by
      rw [← sum_lin_pow2 k, ← Finset.sum_range_reflect (fun i => ((k - i : ℕ) : ℤ) * (2 : ℤ) ^ i) (k + 1)]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ k := Nat.le_of_lt_succ (mem_range.1 hj)
      rw [sumInt_replicate_false]
      have hne : k + 1 - j ≠ 0 := by omega
      simp only [hne, ↓reduceIte, fW]
      rw [show k - (k + 1 - 1 - j) = j by omega,
        show k + 1 - j - 1 = k - j by omega,
        show k + 1 - 1 - j = k - j by omega]
      push_cast; ring
    rw [hs1, hs2]
    simp only [gW]; push_cast; ring

lemma sumTail_replicate_false (k : ℕ) :
    sumTail (List.replicate k false) = if k = 0 then 1 else 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    unfold sumTail
    rw [sum_superLists_replicate_false, runLens_replicate_false]
    simp only [tailWeight]
    have hterm : ∀ j ∈ range k,
        ((superLists (List.replicate (k - 1 - j) false)).map
          (fun c => tailWeight (runLens (List.replicate j false ++ true :: c)))).sum =
        fW (j + 1) * sumTail (List.replicate (k - 1 - j) false) := by
      intro j _
      unfold sumTail
      have hm : (superLists (List.replicate (k - 1 - j) false)).map
          (fun c => tailWeight (runLens (List.replicate j false ++ true :: c))) =
          (superLists (List.replicate (k - 1 - j) false)).map
            (fun c => fW (j + 1) * tailWeight (runLens c)) := by
        refine List.map_congr_left fun c _ => ?_
        rw [runLens_append_true, runLens_replicate_false,
          tailWeight_append _ _ (runLens_ne_nil c)]
        simp only [intProd, mul_one]
      rw [hm, ← List.sum_map_mul_left]
    rw [Finset.sum_congr rfl hterm]
    match k with
    | 0 => simp [gW]
    | k + 1 =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self]
      rw [ih 0 (by omega)]
      simp only [↓reduceIte, mul_one]
      have hzero : ∑ j ∈ range k, fW (j + 1) * sumTail (List.replicate (k - j) false) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj' : j < k := mem_range.1 hj
        rw [ih (k - j) (by omega)]
        have hne : k - j ≠ 0 := by omega
        simp [hne]
      rw [hzero, zero_add]
      simp only [gW, fW]; push_cast; ring

lemma sumBlock_replicate_false (k : ℕ) :
    sumBlock (List.replicate k false) = if k = 0 then 0 else 2 - (k : ℤ) := by
  unfold sumBlock
  rw [sum_superLists_replicate_false, runLens_replicate_false]
  have hterm : ∀ j ∈ range k,
      ((superLists (List.replicate (k - 1 - j) false)).map
        (fun c => blockWeight (runLens (List.replicate j false ++ true :: c)))).sum =
      gW (j + 1) * sumTail (List.replicate (k - 1 - j) false) := by
    intro j _
    unfold sumTail
    have hm : (superLists (List.replicate (k - 1 - j) false)).map
        (fun c => blockWeight (runLens (List.replicate j false ++ true :: c))) =
        (superLists (List.replicate (k - 1 - j) false)).map
          (fun c => gW (j + 1) * tailWeight (runLens c)) := by
      refine List.map_congr_left fun c _ => ?_
      rw [runLens_append_true, runLens_replicate_false, List.singleton_append, blockWeight]
    rw [hm, ← List.sum_map_mul_left]
  rw [Finset.sum_congr rfl hterm]
  simp only [blockWeight, tailWeight, mul_zero, zero_add]
  match k with
  | 0 => simp
  | k + 1 =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self]
    have h0 : sumTail (List.replicate 0 false) = 1 := sumTail_replicate_false 0
    rw [h0, mul_one]
    have hzero : ∑ j ∈ range k, gW (j + 1) * sumTail (List.replicate (k - j) false) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' : j < k := mem_range.1 hj
      rw [sumTail_replicate_false]
      have hne : k - j ≠ 0 := by omega
      simp [hne]
    rw [hzero, zero_add]
    rfl

def hasDoubleTrue : List Bool → Bool
  | true :: true :: _ => true
  | _ :: rest => hasDoubleTrue rest
  | [] => false

def countDoubleFalse : List Bool → ℕ
  | false :: false :: rest => 1 + countDoubleFalse (false :: rest)
  | _ :: rest => countDoubleFalse rest
  | [] => 0

lemma hasDoubleTrue_false_rep_true (k : ℕ) (rest : List Bool) :
    hasDoubleTrue (false :: List.replicate k false ++ true :: rest) = hasDoubleTrue (true :: rest) := by
  induction k with
  | zero => simp [hasDoubleTrue]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append] at ih ⊢
    exact ih

lemma countDoubleFalse_false_rep_true (k : ℕ) (rest : List Bool) :
    countDoubleFalse (false :: List.replicate k false ++ true :: rest) =
      k + countDoubleFalse (true :: rest) := by
  induction k with
  | zero => simp [countDoubleFalse]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append] at ih ⊢
    change 1 + countDoubleFalse (false :: (List.replicate k false ++ true :: rest)) = _
    rw [ih]; omega

lemma sumTail_eq_list_weight (rest : List Bool) :
    sumTail rest =
      if (true :: rest).getLast (List.cons_ne_nil _ _) && !hasDoubleTrue (true :: rest) then
        (2 : ℤ) ^ countDoubleFalse (true :: rest)
      else 0 := by
  have hstrong : ∀ n (rest : List Bool), rest.length = n →
      sumTail rest =
        if (true :: rest).getLast (List.cons_ne_nil _ _) && !hasDoubleTrue (true :: rest) then
          (2 : ℤ) ^ countDoubleFalse (true :: rest)
        else 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro rest hlen
      by_cases hmem : true ∈ rest
      · rcases exists_first_true hmem with ⟨k, rest', rfl⟩
        rw [sumTail_append_true, sumInt_replicate_false]
        cases k with
        | zero =>
          simp [hasDoubleTrue]
        | succ k =>
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
          have hlt : rest'.length < n := by simp at hlen; omega
          rw [ih rest'.length hlt rest' rfl]
          have hlast : (true :: (List.replicate (k + 1) false ++ true :: rest')).getLast
              (List.cons_ne_nil _ _) =
              (true :: rest').getLast (List.cons_ne_nil _ _) := by
            change ((true :: List.replicate (k + 1) false) ++ (true :: rest')).getLast _ = _
            exact List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _)
          have hdt : hasDoubleTrue (true :: (List.replicate (k + 1) false ++ true :: rest')) =
              hasDoubleTrue (true :: rest') := by
            rw [List.replicate_succ, List.cons_append]
            exact hasDoubleTrue_false_rep_true k rest'
          have hdf : countDoubleFalse (true :: (List.replicate (k + 1) false ++ true :: rest')) =
              k + countDoubleFalse (true :: rest') := by
            rw [List.replicate_succ, List.cons_append]
            exact countDoubleFalse_false_rep_true k rest'
          rw [hlast, hdt, hdf, pow_add]
          split_ifs <;> ring
      · have hrep := eq_replicate_false_of_not_mem_true hmem
        rw [hrep, sumTail_replicate_false]
        cases hlen' : rest.length with
        | zero => simp [hasDoubleTrue, countDoubleFalse]
        | succ k =>
          have hlast : (true :: List.replicate (k + 1) false).getLast (List.cons_ne_nil _ _) = false := by
            change ([true] ++ List.replicate (k + 1) false).getLast _ = false
            rw [List.getLast_append_of_ne_nil _ (by simp)]
            simp
          simp [hlast]
  exact hstrong rest.length rest rfl

lemma sumBlock_eq_list_weight (l : List Bool) (hl : l ≠ []) :
    sumBlock l =
      (if l.head hl && l.getLast hl && !hasDoubleTrue l then
        (2 : ℤ) ^ countDoubleFalse l
      else 0) +
      if true ∈ l then 0 else 2 - (l.length : ℤ) := by
  by_cases hmem : true ∈ l
  · rcases exists_first_true hmem with ⟨k, rest, rfl⟩
    rw [if_pos hmem, add_zero, sumBlock_append_true, sumHead_replicate_false]
    cases k with
    | zero =>
      simp only [↓reduceIte, one_mul, List.replicate_zero, List.nil_append, List.head_cons,
        Bool.true_and]
      exact sumTail_eq_list_weight rest
    | succ k =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_mul,
        List.replicate_succ, List.cons_append, List.head_cons, Bool.false_and, Bool.false_eq_true]
  · have hrep := eq_replicate_false_of_not_mem_true hmem
    have hpos : 0 < l.length := List.length_pos_of_ne_nil hl
    rw [if_neg hmem]
    conv_lhs => rw [hrep]
    rw [sumBlock_replicate_false, if_neg (by omega)]
    have hhead : l.head hl = false := by
      cases l with
      | nil => exact absurd rfl hl
      | cons b rest =>
        cases b
        · rfl
        · exact absurd List.mem_cons_self hmem
    simp [hhead]

lemma sum_filter_dom_eq_superLists {m : ℕ} (v : Fin m → Bool) (F : List Bool → ℤ) :
    ∑ c ∈ univ.filter (fun c : Fin m → Bool => ∀ i, v i = true → c i = true), F (List.ofFn c) =
      ((superLists (List.ofFn v)).map F).sum := by
  induction m generalizing F with
  | zero =>
    simp only [List.ofFn_zero, superLists, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [Finset.sum_filter]
    have hcard : (univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext f; simp only [mem_univ, mem_singleton, true_iff]; funext i; exact Fin.elim0 i
    rw [hcard, Finset.sum_singleton]
    simp
  | succ m ih =>
    rw [List.ofFn_succ, Finset.sum_filter]
    let e : Bool × (Fin m → Bool) ≃ (Fin (m + 1) → Bool) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun c => (c 0, c ∘ Fin.succ)
        left_inv := fun ⟨b, c'⟩ => by
          refine Prod.ext (by simp) ?_
          funext i; simp
        right_inv := fun c => by
          funext i
          refine Fin.cases (by simp) (fun j => by simp) i }
    rw [← Fintype.sum_equiv e (fun p =>
      if ∀ i : Fin (m + 1), v i = true → e p i = true then F (List.ofFn (e p)) else 0) _ (fun _ => rfl)]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    have hofFn : ∀ (b : Bool) (c' : Fin m → Bool),
        List.ofFn (e (b, c')) = b :: List.ofFn c' := by
      intro b c'
      rw [List.ofFn_succ]
      simp [e, Function.comp_def]
    have hcond : ∀ (b : Bool) (c' : Fin m → Bool),
        (∀ i : Fin (m + 1), v i = true → e (b, c') i = true) ↔
        ((v 0 = true → b = true) ∧ ∀ j : Fin m, v j.succ = true → c' j = true) := by
      intro b c'
      constructor
      · intro h
        exact ⟨h 0, fun j => h j.succ⟩
      · rintro ⟨h0, hs⟩ i
        exact Fin.cases h0 hs i
    simp_rw [hofFn, hcond]
    cases hv0 : v 0
    · simp only [Bool.false_eq_true, false_implies, true_and, superLists, List.map_append,
        List.sum_append, List.map_map, Function.comp_def]
      rw [← Finset.sum_filter, ← Finset.sum_filter,
        ih (fun j => v j.succ) (fun x => F (true :: x)),
        ih (fun j => v j.succ) (fun x => F (false :: x)), add_comm]
    · simp only [true_implies, Bool.false_eq_true, false_and, ↓reduceIte, Finset.sum_const_zero,
        add_zero, true_and, superLists, List.map_map, Function.comp_def]
      rw [← Finset.sum_filter, ih (fun j => v j.succ) (fun x => F (true :: x))]

lemma hasDoubleTrue_ofFn {n : ℕ} (v : Fin (n + 1) → Bool) :
    hasDoubleTrue (List.ofFn v) = decide (∃ i : Fin n, v i.castSucc = true ∧ v i.succ = true) := by
  induction n with
  | zero =>
    simp [List.ofFn_succ, List.ofFn_zero, hasDoubleTrue]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    have hih := ih (fun i : Fin (n + 1) => v i.succ)
    rw [List.ofFn_succ] at hih
    cases hv0 : v 0
    · cases hv1 : v (Fin.succ 0)
      · change hasDoubleTrue (false :: List.ofFn (fun i : Fin n => v i.succ.succ)) = _
        have hstep : hasDoubleTrue (false :: List.ofFn (fun i : Fin n => v i.succ.succ)) =
            hasDoubleTrue (v (Fin.succ 0) :: List.ofFn (fun i : Fin n => v i.succ.succ)) := by
          rw [hv1]
        rw [hstep, hih]
        apply Bool.eq_iff_iff.2
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨i, h1, h2⟩; exact ⟨i.succ, h1, h2⟩
        · rintro ⟨i, h1, h2⟩
          refine Fin.cases ?_ (fun j h1' h2' => ⟨j, h1', h2'⟩) i h1 h2
          intro h1' _; simp [hv0] at h1'
      · change hasDoubleTrue (true :: List.ofFn (fun i : Fin n => v i.succ.succ)) = _
        have hstep : hasDoubleTrue (true :: List.ofFn (fun i : Fin n => v i.succ.succ)) =
            hasDoubleTrue (v (Fin.succ 0) :: List.ofFn (fun i : Fin n => v i.succ.succ)) := by
          rw [hv1]
        rw [hstep, hih]
        apply Bool.eq_iff_iff.2
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨i, h1, h2⟩; exact ⟨i.succ, h1, h2⟩
        · rintro ⟨i, h1, h2⟩
          refine Fin.cases ?_ (fun j h1' h2' => ⟨j, h1', h2'⟩) i h1 h2
          intro h1' _; simp [hv0] at h1'
    · cases hv1 : v (Fin.succ 0)
      · change hasDoubleTrue (false :: List.ofFn (fun i : Fin n => v i.succ.succ)) = _
        have hstep : hasDoubleTrue (false :: List.ofFn (fun i : Fin n => v i.succ.succ)) =
            hasDoubleTrue (v (Fin.succ 0) :: List.ofFn (fun i : Fin n => v i.succ.succ)) := by
          rw [hv1]
        rw [hstep, hih]
        apply Bool.eq_iff_iff.2
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨i, h1, h2⟩; exact ⟨i.succ, h1, h2⟩
        · rintro ⟨i, h1, h2⟩
          refine Fin.cases ?_ (fun j h1' h2' => ⟨j, h1', h2'⟩) i h1 h2
          intro _ h2'
          rw [hv1] at h2'
          exact absurd h2' Bool.false_ne_true
      · simp only [hasDoubleTrue]
        symm
        rw [decide_eq_true_eq]
        exact ⟨0, hv0, hv1⟩

lemma countDoubleFalse_ofFn {n : ℕ} (v : Fin (n + 1) → Bool) :
    countDoubleFalse (List.ofFn v) =
      (univ.filter (fun i : Fin n => !v i.castSucc && !v i.succ)).card := by
  induction n with
  | zero =>
    simp [List.ofFn_succ, List.ofFn_zero, countDoubleFalse]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Finset.card_filter, Fin.sum_univ_succ]
    have hih := ih (fun i : Fin (n + 1) => v i.succ)
    rw [List.ofFn_succ, Finset.card_filter] at hih
    change countDoubleFalse (v 0 :: v (Fin.succ 0) :: List.ofFn (fun i : Fin n => v i.succ.succ)) = _
    cases hv0 : v 0 <;> cases hv1 : v (Fin.succ 0)
    · change 1 + countDoubleFalse (false :: List.ofFn (fun i : Fin n => v i.succ.succ)) = _
      have hstep : countDoubleFalse (false :: List.ofFn (fun i : Fin n => v i.succ.succ)) =
          countDoubleFalse (v (Fin.succ 0) :: List.ofFn (fun i : Fin n => v i.succ.succ)) := by
        rw [hv1]
      rw [hstep, hih]
      simp [hv0]
    · change countDoubleFalse (true :: List.ofFn (fun i : Fin n => v i.succ.succ)) = _
      have hstep : countDoubleFalse (true :: List.ofFn (fun i : Fin n => v i.succ.succ)) =
          countDoubleFalse (v (Fin.succ 0) :: List.ofFn (fun i : Fin n => v i.succ.succ)) := by
        rw [hv1]
      rw [hstep, hih]
      simp [hv0]
    · change countDoubleFalse (false :: List.ofFn (fun i : Fin n => v i.succ.succ)) = _
      have hstep : countDoubleFalse (false :: List.ofFn (fun i : Fin n => v i.succ.succ)) =
          countDoubleFalse (v (Fin.succ 0) :: List.ofFn (fun i : Fin n => v i.succ.succ)) := by
        rw [hv1]
      rw [hstep, hih]
      simp [hv0]
    · change countDoubleFalse (true :: List.ofFn (fun i : Fin n => v i.succ.succ)) = _
      have hstep : countDoubleFalse (true :: List.ofFn (fun i : Fin n => v i.succ.succ)) =
          countDoubleFalse (v (Fin.succ 0) :: List.ofFn (fun i : Fin n => v i.succ.succ)) := by
        rw [hv1]
      rw [hstep, hih]
      simp [hv0]

/-! ### Section 3: Way 2 permutation counts (`decPerms`) -/

def revPerm (k : ℕ) : Equiv.Perm (Fin k) :=
  { toFun := Fin.rev
    invFun := Fin.rev
    left_inv := Fin.rev_rev
    right_inv := Fin.rev_rev }

lemma fin_le_of_strictMono {k : ℕ} {f : Fin k → Fin k} (hf : StrictMono f) (i : Fin k) :
    i ≤ f i := by
  rcases i with ⟨v, hv⟩
  induction v with
  | zero => exact Nat.zero_le _
  | succ v ih =>
    have hprev := ih (Nat.lt_of_succ_lt hv)
    have hlt : f ⟨v, Nat.lt_of_succ_lt hv⟩ < f ⟨v + 1, hv⟩ :=
      hf (by change v < v + 1; omega)
    change v + 1 ≤ (f ⟨v + 1, hv⟩).val
    have h1 : v ≤ (f ⟨v, Nat.lt_of_succ_lt hv⟩).val := hprev
    have h2 : (f ⟨v, Nat.lt_of_succ_lt hv⟩).val < (f ⟨v + 1, hv⟩).val := hlt
    omega

lemma strictMono_perm_eq_one {k : ℕ} (q : Equiv.Perm (Fin k)) (hq : StrictMono q) : q = 1 := by
  have hsymm : StrictMono q.symm := by
    intro a b hab
    by_contra hle
    have hba : q.symm b ≤ q.symm a := le_of_not_gt hle
    have := hq.monotone hba
    rw [q.apply_symm_apply, q.apply_symm_apply] at this
    exact not_lt_of_ge this hab
  ext i
  exact le_antisymm (by simpa using fin_le_of_strictMono hsymm (q i)) (fin_le_of_strictMono hq i)

lemma strictAnti_perm_eq_rev {k : ℕ} (p : Equiv.Perm (Fin k)) (hp : StrictAnti p) :
    p = revPerm k := by
  have hq : StrictMono (p.trans (revPerm k)) := by
    intro a b hab
    exact Fin.rev_lt_rev.2 (hp hab)
  have h1 := strictMono_perm_eq_one (p.trans (revPerm k)) hq
  ext i
  have := Equiv.congr_fun h1 i
  simp only [Equiv.trans_apply, Equiv.Perm.one_apply, revPerm, Equiv.coe_fn_mk] at this ⊢
  rw [← Fin.rev_rev (p i), this]

lemma strictAnti_of_adj {m n : ℕ} {f : Fin (m + 1) → Fin n}
    (h : ∀ i : Fin m, f i.succ < f i.castSucc) : StrictAnti f := by
  intro a b hab
  have hstep : ∀ d (a b : Fin (m + 1)), b.val = a.val + d + 1 → f b < f a := by
    intro d
    induction d with
    | zero =>
      intro a b hEq
      have ha : a.val < m := by omega
      have h1 := h ⟨a.val, ha⟩
      have hcast : (⟨a.val, ha⟩ : Fin m).castSucc = a := Fin.ext rfl
      have hsucc : (⟨a.val, ha⟩ : Fin m).succ = b := Fin.ext (by simp; omega)
      rwa [hcast, hsucc] at h1
    | succ d ih =>
      intro a b hEq
      have hmid_lt : a.val + d + 1 < m + 1 := by omega
      let mid : Fin (m + 1) := ⟨a.val + d + 1, hmid_lt⟩
      have h1 : f mid < f a := ih a mid rfl
      have hm_lt : mid.val < m := by dsimp only [mid]; omega
      have h2 := h ⟨mid.val, hm_lt⟩
      have hcast : (⟨mid.val, hm_lt⟩ : Fin m).castSucc = mid := Fin.ext rfl
      have hsucc : (⟨mid.val, hm_lt⟩ : Fin m).succ = b := Fin.ext (by simp [mid]; omega)
      rw [hcast, hsucc] at h2
      exact lt_trans h2 h1
  have hab' : a.val < b.val := hab
  exact hstep (b.val - a.val - 1) a b (by omega)

lemma strictAnti_eq_orderIso_rev {k n : ℕ} {S : Finset (Fin n)} (hS : S.card = k)
    (f : Fin k → Fin n) (hf_anti : StrictAnti f) (hf_mem : ∀ i, f i ∈ S) :
    ∀ i : Fin k, f i = (S.orderIsoOfFin hS (Fin.rev i)).val := by
  let g : Fin k → Fin k := fun i => (S.orderIsoOfFin hS).symm ⟨f (Fin.rev i), hf_mem _⟩
  have hg_mono : StrictMono g := by
    intro a b hab
    have hlt : f (Fin.rev a) < f (Fin.rev b) := hf_anti (Fin.rev_lt_rev.2 hab)
    exact (S.orderIsoOfFin hS).symm.strictMono (by exact hlt)
  have hg_bij : Function.Bijective g := Finite.injective_iff_bijective.1 hg_mono.injective
  have hgid : Equiv.ofBijective g hg_bij = 1 :=
    strictMono_perm_eq_one (Equiv.ofBijective g hg_bij) hg_mono
  intro i
  have hgi : g (Fin.rev i) = Fin.rev i := by
    have := Equiv.congr_fun hgid (Fin.rev i)
    simpa using this
  have happ := congr_arg (fun x => (S.orderIsoOfFin hS x).val) hgi
  simpa [g, Fin.rev_rev] using happ

def decPerms {m : ℕ} (c : Fin m → Bool) : Finset (Equiv.Perm (Fin (m + 1))) :=
  univ.filter (fun p => ∀ i : Fin m, c i = false → p i.succ < p i.castSucc)

lemma decPerms_iff_ascends {m : ℕ} (c : Fin m → Bool) (p : Equiv.Perm (Fin (m + 1))) :
    p ∈ decPerms c ↔ ∀ i : Fin m, ascends p i = true → c i = true := by
  simp only [decPerms, mem_filter, mem_univ, true_and, ascends, decide_eq_true_eq]
  constructor
  · intro h i hlt
    by_contra hne
    have hcf : c i = false := Bool.eq_false_iff.2 hne
    exact not_lt_of_gt (h i hcf) hlt
  · intro h i hcf
    have hnot : ¬ (p i.castSucc < p i.succ) := fun hlt => by
      have := h i hlt; rw [hcf] at this; exact Bool.false_ne_true this
    have hne : p i.succ ≠ p i.castSucc := fun heq => by
      have := p.injective heq
      have h1 : i.succ.val = i.castSucc.val := congr_arg Fin.val this
      simp at h1
    exact lt_of_le_of_ne (le_of_not_gt hnot) hne

lemma card_decPerms (m : ℕ) (c : Fin m → Bool) :
    (decPerms c).card = multinomial (runLens (List.ofFn c)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hall : ∀ i : Fin m, c i = false
    · have hlist : List.ofFn c = List.replicate m false := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp [hall ⟨i, by simpa using h1⟩]
      rw [hlist, runLens_replicate_false]
      simp only [multinomial, List.sum_nil, add_zero, Nat.choose_self, mul_one]
      have hsing : decPerms c = {revPerm (m + 1)} := by
        ext p
        simp only [decPerms, mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hp
          exact strictAnti_perm_eq_rev p (strictAnti_of_adj fun i => hp i (hall i))
        · rintro rfl i _
          simp only [revPerm, Equiv.coe_fn_mk]
          exact Fin.rev_lt_rev.2 Fin.castSucc_lt_succ
      rw [hsing, card_singleton]
    · push Not at hall
      have hex : ∃ k : ℕ, ∃ hk : k < m, c ⟨k, hk⟩ = true := by
        rcases hall with ⟨i, hi⟩
        exact ⟨i.val, i.isLt, Bool.eq_true_of_not_eq_false hi⟩
      classical
      let k := Nat.find hex
      have hk_spec : ∃ hk : k < m, c ⟨k, hk⟩ = true := Nat.find_spec hex
      rcases hk_spec with ⟨hk_lt, hck⟩
      have hlt_false : ∀ j : ℕ, j < k → ∀ hj : j < m, c ⟨j, hj⟩ = false := by
        intro j hjk hj
        by_contra hne
        exact Nat.find_min hex hjk ⟨hj, Bool.eq_true_of_not_eq_false hne⟩
      let m' := m - 1 - k
      have hm_eq : m = k + 1 + m' := by omega
      let c' : Fin m' → Bool := fun j => c ⟨k + 1 + j.val, by omega⟩
      have hlist : List.ofFn c = List.replicate k false ++ true :: List.ofFn c' := by
        apply List.ext_getElem
        · simp [m']; omega
        · intro i h1 h2
          have hi_lt : i < m := by simpa using h1
          rw [List.getElem_ofFn]
          by_cases h1' : i < k
          · rw [List.getElem_append_left (by simp [h1']), List.getElem_replicate]
            exact hlt_false i h1' hi_lt
          · rw [List.getElem_append_right (by simp; omega)]
            simp only [List.length_replicate]
            by_cases h2' : i = k
            · subst h2'; simp [hck]
            · have hi_gt : k < i := by omega
              have hidx : (true :: List.ofFn c')[i - k]'(by simp [m']; omega) =
                  (true :: List.ofFn c')[(i - k - 1) + 1]'(by simp [m']; omega) := by
                congr 1; omega
              rw [hidx, List.getElem_cons_succ, List.getElem_ofFn]
              dsimp only [c']
              congr 1; ext; dsimp; omega
      rw [hlist, runLens_append_true, runLens_replicate_false, List.singleton_append, multinomial,
        runLens_sum, List.length_ofFn, show (k + 1) + (m' + 1) = m + 1 by omega, ← ih m' (by omega) c']
      let RHS := powersetCard (k + 1) (univ : Finset (Fin (m + 1))) ×ˢ decPerms c'
      have hRHS : RHS.card = (m + 1).choose (k + 1) * (decPerms c').card := by
        rw [card_product, card_powersetCard, card_univ, Fintype.card_fin]
      rw [← hRHS]
      -- Forward map from p ∈ decPerms c to (S, q) ∈ RHS
      let getS (p : Equiv.Perm (Fin (m + 1))) : Finset (Fin (m + 1)) :=
        (univ : Finset (Fin (k + 1))).image (fun j => p ⟨j.val, by omega⟩)
      have hgetS_card : ∀ p : Equiv.Perm (Fin (m + 1)), (getS p).card = k + 1 := by
        intro p
        rw [card_image_of_injective _ (fun a b h => by
          have h1 := p.injective h
          have h2 : a.val = b.val := congr_arg (Fin.val : Fin (m + 1) → ℕ) h1
          exact Fin.ext h2), card_univ, Fintype.card_fin]
      have hcompl_card : ∀ S : Finset (Fin (m + 1)), S.card = k + 1 →
          (univ \ S).card = m' + 1 := by
        intro S hSc
        rw [card_sdiff, inter_eq_left.2 (subset_univ _), card_univ, Fintype.card_fin, hSc]; omega
      let getQ (p : Equiv.Perm (Fin (m + 1))) : Equiv.Perm (Fin (m' + 1)) :=
        let iso := (univ \ getS p).orderIsoOfFin (hcompl_card (getS p) (hgetS_card p))
        let f : Fin (m' + 1) → Fin (m' + 1) := fun j =>
          iso.symm ⟨p ⟨k + 1 + j.val, by omega⟩, by
            rw [mem_sdiff]; refine ⟨mem_univ _, ?_⟩
            intro hm
            rcases mem_image.1 hm with ⟨a, _, ha⟩
            have hval := congr_arg Fin.val (p.injective ha)
            dsimp at hval; omega⟩
        have hfinj : Function.Injective f := by
          intro j1 j2 h
          have h1 := congr_arg Subtype.val (iso.symm.injective h)
          have h2 := congr_arg Fin.val (p.injective h1)
          ext; dsimp at h2; omega
        Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
      refine Finset.card_bij (fun p _ => (getS p, getQ p)) ?_ ?_ ?_
      · intro p hp
        rw [mem_product, mem_powersetCard]
        refine ⟨⟨subset_univ _, hgetS_card p⟩, ?_⟩
        simp only [decPerms, mem_filter, mem_univ, true_and] at hp ⊢
        intro j hcj
        let iso := (univ \ getS p).orderIsoOfFin (hcompl_card (getS p) (hgetS_card p))
        change iso.symm ⟨p ⟨k + 1 + j.succ.val, _⟩, _⟩ < iso.symm ⟨p ⟨k + 1 + j.castSucc.val, _⟩, _⟩
        apply iso.symm.strictMono
        change p ⟨k + 1 + j.succ.val, _⟩ < p ⟨k + 1 + j.castSucc.val, _⟩
        have h1 := hp ⟨k + 1 + j.val, by omega⟩ hcj
        have hcast : (⟨k + 1 + j.val, by omega⟩ : Fin m).castSucc = ⟨k + 1 + j.castSucc.val, by omega⟩ :=
          Fin.ext rfl
        have hsucc : (⟨k + 1 + j.val, by omega⟩ : Fin m).succ = ⟨k + 1 + j.succ.val, by omega⟩ :=
          Fin.ext (by simp; omega)
        rwa [hcast, hsucc] at h1
      · intro p1 hp1 p2 hp2 hEq
        simp only [Prod.mk.injEq] at hEq
        rcases hEq with ⟨hS, hQ⟩
        simp only [decPerms, mem_filter, mem_univ, true_and] at hp1 hp2
        have hanti1 : StrictAnti (fun j : Fin (k + 1) => p1 ⟨j.val, by omega⟩) :=
          strictAnti_of_adj fun j => by
            have h1 := hp1 ⟨j.val, by omega⟩ (hlt_false j.val j.isLt (by omega))
            have hcast : (⟨j.val, by omega⟩ : Fin m).castSucc = ⟨j.castSucc.val, by omega⟩ := Fin.ext rfl
            have hsucc : (⟨j.val, by omega⟩ : Fin m).succ = ⟨j.succ.val, by omega⟩ := Fin.ext (by simp)
            rwa [hcast, hsucc] at h1
        have hanti2 : StrictAnti (fun j : Fin (k + 1) => p2 ⟨j.val, by omega⟩) :=
          strictAnti_of_adj fun j => by
            have h1 := hp2 ⟨j.val, by omega⟩ (hlt_false j.val j.isLt (by omega))
            have hcast : (⟨j.val, by omega⟩ : Fin m).castSucc = ⟨j.castSucc.val, by omega⟩ := Fin.ext rfl
            have hsucc : (⟨j.val, by omega⟩ : Fin m).succ = ⟨j.succ.val, by omega⟩ := Fin.ext (by simp)
            rwa [hcast, hsucc] at h1
        ext i
        by_cases hi : i.val < k + 1
        · let j : Fin (k + 1) := ⟨i.val, hi⟩
          have h1 := strictAnti_eq_orderIso_rev (hgetS_card p1) (fun j : Fin (k + 1) => p1 ⟨j.val, by omega⟩)
            hanti1 (fun j => mem_image.2 ⟨j, mem_univ _, rfl⟩) j
          have h2 := strictAnti_eq_orderIso_rev (hgetS_card p1) (fun j : Fin (k + 1) => p2 ⟨j.val, by omega⟩)
            hanti2 (fun j => by rw [hS]; exact mem_image.2 ⟨j, mem_univ _, rfl⟩) j
          have h1' : p1 i = ( (getS p1).orderIsoOfFin (hgetS_card p1) (Fin.rev j) ).val := h1
          have h2' : p2 i = ( (getS p1).orderIsoOfFin (hgetS_card p1) (Fin.rev j) ).val := h2
          rw [h1', h2']
        · let j : Fin (m' + 1) := ⟨i.val - (k + 1), by omega⟩
          have hqj := Equiv.congr_fun hQ j
          have hi_eq : (⟨k + 1 + j.val, by omega⟩ : Fin (m + 1)) = i := Fin.ext (by dsimp [j]; omega)
          have hval1 : p1 ⟨k + 1 + j.val, by omega⟩ =
              ((univ \ getS p1).orderIsoOfFin (hcompl_card (getS p1) (hgetS_card p1)) (getQ p1 j)).val := by
            simp [getQ]
          have hval2 : p2 ⟨k + 1 + j.val, by omega⟩ =
              ((univ \ getS p2).orderIsoOfFin (hcompl_card (getS p2) (hgetS_card p2)) (getQ p2 j)).val := by
            simp [getQ]
          rw [← hi_eq, hval1, hval2]
          have hS' : univ \ getS p1 = univ \ getS p2 := by rw [hS]
          have hcast : ∀ (A B : Finset (Fin (m + 1))) (hAB : A = B) (hA : A.card = m' + 1)
              (hB : B.card = m' + 1) (x y : Fin (m' + 1)) (hxy : x = y),
              (A.orderIsoOfFin hA x).val = (B.orderIsoOfFin hB y).val := by
            rintro A _ rfl hA hB x _ rfl; rfl
          exact congr_arg Fin.val (hcast _ _ hS' _ _ _ _ hqj)
      · rintro ⟨S, q⟩ hSq
        rw [mem_product, mem_powersetCard] at hSq
        rcases hSq with ⟨⟨_, hSc⟩, hq⟩
        dsimp only at hSc hq
        let isoS := S.orderIsoOfFin hSc
        let isoC := (univ \ S).orderIsoOfFin (hcompl_card S hSc)
        let pf : Fin (m + 1) → Fin (m + 1) := fun i =>
          if hi : i.val < k + 1 then (isoS (Fin.rev ⟨i.val, hi⟩)).val
          else (isoC (q ⟨i.val - (k + 1), by omega⟩)).val
        have hpfinj : Function.Injective pf := by
          intro i1 i2 h
          by_cases h1 : i1.val < k + 1 <;> by_cases h2 : i2.val < k + 1
          · simp only [pf, h1, h2, ↓reduceDIte] at h
            have h3 := Fin.rev_injective (isoS.injective (Subtype.ext h))
            have h4 : i1.val = i2.val := congr_arg (Fin.val : Fin (k + 1) → ℕ) h3
            exact Fin.ext h4
          · simp only [pf, h1, h2, ↓reduceDIte] at h
            exfalso
            have hm1 : (isoS (Fin.rev ⟨i1.val, h1⟩)).val ∈ S := (isoS _).property
            have hm2 : (isoC (q ⟨i2.val - (k + 1), by omega⟩)).val ∈ univ \ S := (isoC _).property
            rw [h] at hm1
            exact (mem_sdiff.1 hm2).2 hm1
          · simp only [pf, h1, h2, ↓reduceDIte] at h
            exfalso
            have hm1 : (isoC (q ⟨i1.val - (k + 1), by omega⟩)).val ∈ univ \ S := (isoC _).property
            have hm2 : (isoS (Fin.rev ⟨i2.val, h2⟩)).val ∈ S := (isoS _).property
            rw [h] at hm1
            exact (mem_sdiff.1 hm1).2 hm2
          · simp only [pf, h1, h2, ↓reduceDIte] at h
            have h3 := q.injective (isoC.injective (Subtype.ext h))
            have h4 := congr_arg Fin.val h3
            dsimp at h4; ext; omega
        let p : Equiv.Perm (Fin (m + 1)) := Equiv.ofBijective pf (Finite.injective_iff_bijective.1 hpfinj)
        have hp_mem : p ∈ decPerms c := by
          simp only [decPerms, mem_filter, mem_univ, true_and] at hq ⊢
          intro i hci
          have hne_k : i.val ≠ k := fun h => by
            have : c ⟨k, hk_lt⟩ = false := by convert hci using 2; ext; exact h.symm
            rw [hck] at this; exact Bool.false_ne_true this.symm
          by_cases hi : i.val < k
          · have h1 : i.castSucc.val < k + 1 := by simp; omega
            have h2 : i.succ.val < k + 1 := by simp; omega
            change pf i.succ < pf i.castSucc
            simp only [pf, h1, h2, ↓reduceDIte]
            exact isoS.strictMono (Fin.rev_lt_rev.2 (by change i.castSucc.val < i.succ.val; simp))
          · have h1 : ¬ (i.castSucc.val < k + 1) := by simp; omega
            have h2 : ¬ (i.succ.val < k + 1) := by simp; omega
            change pf i.succ < pf i.castSucc
            simp only [pf, h1, h2, ↓reduceDIte]
            apply isoC.strictMono
            let j : Fin m' := ⟨i.val - (k + 1), by omega⟩
            have hcj : c' j = false := by
              dsimp only [c', j]; convert hci using 2; ext; dsimp; omega
            have hqj := hq j hcj
            have hcast : (⟨i.castSucc.val - (k + 1), by omega⟩ : Fin (m' + 1)) = j.castSucc :=
              Fin.ext (by simp [j])
            have hsucc : (⟨i.succ.val - (k + 1), by omega⟩ : Fin (m' + 1)) = j.succ :=
              Fin.ext (by simp [j]; omega)
            rwa [hcast, hsucc]
        have hgetS_eq : getS p = S := by
          ext x
          simp only [getS, mem_image, mem_univ, true_and]
          constructor
          · rintro ⟨j, rfl⟩
            change pf ⟨j.val, _⟩ ∈ S
            simp only [pf, j.isLt, ↓reduceDIte]
            exact (isoS _).property
          · intro hx
            refine ⟨Fin.rev (isoS.symm ⟨x, hx⟩), ?_⟩
            change pf ⟨(Fin.rev (isoS.symm ⟨x, hx⟩)).val, _⟩ = x
            simp only [pf, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.rev_rev]
            exact congr_arg Subtype.val (isoS.apply_symm_apply ⟨x, hx⟩)
        refine ⟨p, hp_mem, Prod.ext hgetS_eq ?_⟩
        ext j
        have hnot : ¬ (k + 1 + j.val < k + 1) := by omega
        have hval : p ⟨k + 1 + j.val, by omega⟩ = (isoC (q j)).val := by
          change pf ⟨k + 1 + j.val, by omega⟩ = _
          simp only [pf, hnot, ↓reduceDIte]
          congr 2; ext; simp
        have hcast_iso : ∀ (A B : Finset (Fin (m + 1))) (hAB : A = B) (hA : A.card = m' + 1)
            (hB : B.card = m' + 1) (x : A) (y : B) (hxy : x.val = y.val),
            (A.orderIsoOfFin hA).symm x = (B.orderIsoOfFin hB).symm y := by
          rintro A _ rfl hA hB x y hxy
          have : x = y := Subtype.ext hxy
          subst this; rfl
        have hqval : getQ p j =
            ((univ \ getS p).orderIsoOfFin (hcompl_card (getS p) (hgetS_card p))).symm
              ⟨p ⟨k + 1 + j.val, by omega⟩, by
                rw [mem_sdiff]; refine ⟨mem_univ _, ?_⟩
                intro hm; rcases mem_image.1 hm with ⟨a, _, ha⟩
                have := congr_arg Fin.val (p.injective ha); dsimp at this; omega⟩ := rfl
        rw [hqval]
        have heq := hcast_iso (univ \ getS p) (univ \ S) (by rw [hgetS_eq])
          (hcompl_card (getS p) (hgetS_card p)) (hcompl_card S hSc)
          ⟨p ⟨k + 1 + j.val, by omega⟩, by
            rw [mem_sdiff]; refine ⟨mem_univ _, ?_⟩
            intro hm; rcases mem_image.1 hm with ⟨a, _, ha⟩
            have := congr_arg Fin.val (p.injective ha); dsimp at this; omega⟩
          (isoC (q j)) hval
        rw [heq]
        exact congr_arg Fin.val (isoC.symm_apply_apply (q j))

/-! ### Section 4: Derangement identities and Way 2 sum evaluation -/

def D : ℕ → ℤ
  | 0 => 1
  | n + 1 => (n + 1 : ℤ) * D n + (-1 : ℤ) ^ (n + 1)

lemma sum_choose_neg_one (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (-1 : ℤ) ^ k = 0 := by
  have h := add_pow (-1 : ℤ) 1 n
  rw [show (-1 : ℤ) + 1 = 0 by ring, zero_pow (by omega : n ≠ 0)] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_comm]

lemma sum_choose_D (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℤ) * D k = (n.factorial : ℤ) := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, D, one_mul]
    have hsplit : ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℤ) * ((k + 1 : ℤ) * D k + (-1 : ℤ) ^ (k + 1)) =
        (n + 1 : ℤ) * (∑ k ∈ range (n + 1), (n.choose k : ℤ) * D k) +
        (∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℤ) * (-1 : ℤ) ^ (k + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hch : (n + 1).choose (k + 1) * (k + 1) = (n + 1) * n.choose k := by
        have := Nat.add_one_mul_choose_eq n k
        linarith
      have hch' : ((n + 1).choose (k + 1) : ℤ) * (k + 1 : ℤ) = (n + 1 : ℤ) * (n.choose k : ℤ) := by
        exact_mod_cast hch
      calc ((n + 1).choose (k + 1) : ℤ) * ((k + 1 : ℤ) * D k + (-1 : ℤ) ^ (k + 1))
          = ((n + 1).choose (k + 1) : ℤ) * (k + 1 : ℤ) * D k +
            ((n + 1).choose (k + 1) : ℤ) * (-1 : ℤ) ^ (k + 1) := by ring
        _ = (n + 1 : ℤ) * ((n.choose k : ℤ) * D k) +
            ((n + 1).choose (k + 1) : ℤ) * (-1 : ℤ) ^ (k + 1) := by rw [hch']; ring
    rw [hsplit, ih]
    have hneg := sum_choose_neg_one (n + 1) (by omega)
    rw [Finset.sum_range_succ'] at hneg
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at hneg
    rw [Nat.factorial_succ]
    push_cast
    linarith

lemma sum_choose_mul_D_rev (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℤ) * D (n - k) = (n.factorial : ℤ) := by
  rw [← sum_choose_D n, ← Finset.sum_range_reflect (fun k => (n.choose k : ℤ) * D k) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.le_of_lt_succ (mem_range.1 hk)
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm hk']

lemma sum_choose_mul_id_D_rev (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (k : ℤ) * D (n - k) = (n.factorial : ℤ) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have hstep : ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ) * D (n + 1 - (k + 1)) =
        (n + 1 : ℤ) * ∑ k ∈ range (n + 1), (n.choose k : ℤ) * D (n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hch : (n + 1).choose (k + 1) * (k + 1) = (n + 1) * n.choose k := by
        have := Nat.add_one_mul_choose_eq n k
        linarith
      have hch' : ((n + 1).choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ) = (n + 1 : ℤ) * (n.choose k : ℤ) := by
        exact_mod_cast hch
      rw [show n + 1 - (k + 1) = n - k by omega, hch', mul_assoc]
    rw [hstep, sum_choose_mul_D_rev, Nat.factorial_succ]
    push_cast; ring

lemma D_eq_sum_fW (n : ℕ) (hn : 1 ≤ n) :
    D n = ∑ j ∈ range n, (n.choose (j + 1) : ℤ) * fW (j + 1) * D (n - 1 - j) := by
  have h1 := sum_choose_mul_id_D_rev n hn
  have h2 := sum_choose_mul_D_rev n
  have hsub : ∑ k ∈ range (n + 1), (n.choose k : ℤ) * fW k * D (n - k) = 0 := by
    calc ∑ k ∈ range (n + 1), (n.choose k : ℤ) * fW k * D (n - k)
        = (∑ k ∈ range (n + 1), (n.choose k : ℤ) * (k : ℤ) * D (n - k)) -
          (∑ k ∈ range (n + 1), (n.choose k : ℤ) * D (n - k)) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun k _ => by simp only [fW]; ring
      _ = (n.factorial : ℤ) - (n.factorial : ℤ) := by rw [h1, h2]
      _ = 0 := sub_self _
  rw [Finset.sum_range_succ'] at hsub
  simp only [Nat.choose_zero_right, Nat.cast_one, fW, Nat.cast_zero, zero_sub, mul_neg, mul_one,
    Nat.sub_zero, neg_mul, one_mul] at hsub
  have hcongr : ∑ j ∈ range n, (n.choose (j + 1) : ℤ) * ((j + 1 : ℕ) - 1 : ℤ) * D (n - (j + 1)) =
      ∑ j ∈ range n, (n.choose (j + 1) : ℤ) * fW (j + 1) * D (n - 1 - j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [fW, show n - (j + 1) = n - 1 - j by omega]
  rw [hcongr] at hsub
  linarith

lemma sum_choose_gW_D (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ range n, (n.choose (j + 1) : ℤ) * gW (j + 1) * D (n - 1 - j) =
      (n.factorial : ℤ) - 2 * D n := by
  have h1 := sum_choose_mul_id_D_rev n hn
  have h2 := sum_choose_mul_D_rev n
  have hcomb : ∑ k ∈ range (n + 1), (n.choose k : ℤ) * gW k * D (n - k) = (n.factorial : ℤ) := by
    calc ∑ k ∈ range (n + 1), (n.choose k : ℤ) * gW k * D (n - k)
        = 2 * (∑ k ∈ range (n + 1), (n.choose k : ℤ) * D (n - k)) -
          (∑ k ∈ range (n + 1), (n.choose k : ℤ) * (k : ℤ) * D (n - k)) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun k _ => by simp only [gW]; ring
      _ = 2 * (n.factorial : ℤ) - (n.factorial : ℤ) := by rw [h1, h2]
      _ = (n.factorial : ℤ) := by ring
  rw [Finset.sum_range_succ'] at hcomb
  simp only [Nat.choose_zero_right, Nat.cast_one, gW, Nat.cast_zero, sub_zero, one_mul,
    Nat.sub_zero] at hcomb
  have hcongr : ∑ j ∈ range n, (n.choose (j + 1) : ℤ) * (2 - ((j + 1 : ℕ) : ℤ)) * D (n - (j + 1)) =
      ∑ j ∈ range n, (n.choose (j + 1) : ℤ) * gW (j + 1) * D (n - 1 - j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [gW, show n - (j + 1) = n - 1 - j by omega]
  rw [hcongr] at hcomb
  linarith

def U (n : ℕ) : ℤ :=
  ∑ j ∈ range (n - 1), (n.choose (j + 1) : ℤ) * gW (j + 1) * ((n - 1 - j).factorial : ℤ)

lemma choose_mul_fact_step {n a : ℕ} (ha : a ≤ n) :
    (n + 1).choose a * (n + 1 - a).factorial = (n + 1) * (n.choose a * (n - a).factorial) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos a)
  have h1 : (n + 1).choose a * (n + 1 - a).factorial * a.factorial = (n + 1).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_succ_of_le ha)
    linarith
  have h2 : n.choose a * (n - a).factorial * a.factorial = n.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial ha
    linarith
  rw [h1, mul_assoc, h2, Nat.factorial_succ]

lemma U_step (n : ℕ) (hn : 2 ≤ n) :
    U (n + 1) - ((n + 1 : ℕ) : ℤ) * U n = ((n + 1 : ℕ) : ℤ) * (2 - (n : ℤ)) := by
  unfold U
  rw [show n + 1 - 1 = (n - 1) + 1 by omega, Finset.sum_range_succ]
  have hlast : ((n + 1).choose (n - 1 + 1) : ℤ) * gW (n - 1 + 1) * ((n - 1 + 1 - (n - 1)).factorial : ℤ) =
      ((n + 1 : ℕ) : ℤ) * (2 - (n : ℤ)) := by
    rw [show n - 1 + 1 = n by omega, show n - (n - 1) = 1 by omega,
      Nat.choose_succ_self_right, Nat.factorial_one]
    simp only [gW, Nat.cast_one, mul_one]
  have hhead : ∑ j ∈ range (n - 1),
      ((n + 1).choose (j + 1) : ℤ) * gW (j + 1) * ((n - 1 + 1 - j).factorial : ℤ) =
      ((n + 1 : ℕ) : ℤ) * ∑ j ∈ range (n - 1),
        (n.choose (j + 1) : ℤ) * gW (j + 1) * ((n - 1 - j).factorial : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 ≤ n := by have := mem_range.1 hj; omega
    have hnat := choose_mul_fact_step hj'
    have hint : ((n + 1).choose (j + 1) : ℤ) * ((n + 1 - (j + 1)).factorial : ℤ) =
        ((n + 1 : ℕ) : ℤ) * ((n.choose (j + 1) : ℤ) * ((n - (j + 1)).factorial : ℤ)) := by
      exact_mod_cast hnat
    rw [show n - 1 + 1 - j = n + 1 - (j + 1) by omega, show n - 1 - j = n - (j + 1) by omega]
    calc ((n + 1).choose (j + 1) : ℤ) * gW (j + 1) * ((n + 1 - (j + 1)).factorial : ℤ)
        = gW (j + 1) * (((n + 1).choose (j + 1) : ℤ) * ((n + 1 - (j + 1)).factorial : ℤ)) := by ring
      _ = gW (j + 1) * (((n + 1 : ℕ) : ℤ) * ((n.choose (j + 1) : ℤ) * ((n - (j + 1)).factorial : ℤ))) := by
            rw [hint]
      _ = ((n + 1 : ℕ) : ℤ) * ((n.choose (j + 1) : ℤ) * gW (j + 1) * ((n - (j + 1)).factorial : ℤ)) := by ring
  rw [hlast, hhead]; ring

def sumAllInt (m : ℕ) : ℤ :=
  ((superLists (List.replicate m false)).map
    (fun c => (multinomial (runLens c) : ℤ) * intProd (runLens c))).sum

def sumAllHead (m : ℕ) : ℤ :=
  ((superLists (List.replicate m false)).map
    (fun c => (multinomial (runLens c) : ℤ) * headWeight (runLens c))).sum

def sumAllTail (m : ℕ) : ℤ :=
  ((superLists (List.replicate m false)).map
    (fun c => (multinomial (runLens c) : ℤ) * tailWeight (runLens c))).sum

def sumAllBlock (m : ℕ) : ℤ :=
  ((superLists (List.replicate m false)).map
    (fun c => (multinomial (runLens c) : ℤ) * blockWeight (runLens c))).sum

lemma sum_univ_bool_eq_superLists {m : ℕ} (F : List Bool → ℤ) :
    ∑ c : Fin m → Bool, F (List.ofFn c) =
      ((superLists (List.replicate m false)).map F).sum := by
  have h := sum_filter_dom_eq_superLists (fun _ : Fin m => false) F
  have hrep : List.ofFn (fun _ : Fin m => false) = List.replicate m false := by
    apply List.ext_getElem <;> simp
  rw [hrep] at h
  simpa using h

lemma sumAllInt_eq_D (m : ℕ) : sumAllInt m = D (m + 1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    unfold sumAllInt
    rw [sum_superLists_replicate_false, runLens_replicate_false]
    simp only [multinomial, List.sum_nil, add_zero, Nat.choose_self, mul_one, Nat.cast_one,
      intProd, one_mul]
    have hterm : ∀ j ∈ range m,
        ((superLists (List.replicate (m - 1 - j) false)).map
          (fun c => (multinomial (runLens (List.replicate j false ++ true :: c)) : ℤ) *
            intProd (runLens (List.replicate j false ++ true :: c)))).sum =
        ((m + 1).choose (j + 1) : ℤ) * fW (j + 1) * D (m - j) := by
      intro j hj
      have hj' : j < m := mem_range.1 hj
      have hm : (superLists (List.replicate (m - 1 - j) false)).map
          (fun c => (multinomial (runLens (List.replicate j false ++ true :: c)) : ℤ) *
            intProd (runLens (List.replicate j false ++ true :: c))) =
          (superLists (List.replicate (m - 1 - j) false)).map
            (fun c => (((m + 1).choose (j + 1) : ℤ) * fW (j + 1)) *
              ((multinomial (runLens c) : ℤ) * intProd (runLens c))) := by
        refine List.map_congr_left fun c hc => ?_
        have hclen : c.length = m - 1 - j := by
          have hlen_sl : ∀ (l : List Bool) (x : List Bool), x ∈ superLists l → x.length = l.length := by
            intro l
            induction l with
            | nil => intro x hx; simp [superLists] at hx; simp [hx]
            | cons b r ihr =>
              intro x hx
              cases b
              · simp only [superLists, List.mem_append, List.mem_map] at hx
                rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;> simp [ihr y hy]
              · simp only [superLists, List.mem_map] at hx
                rcases hx with ⟨y, hy, rfl⟩; simp [ihr y hy]
          simpa using hlen_sl _ _ hc
        rw [runLens_append_true, runLens_replicate_false, List.singleton_append, multinomial,
          runLens_sum, hclen, show (j + 1) + (m - 1 - j + 1) = m + 1 by omega, intProd]
        push_cast; ring
      rw [hm, List.sum_map_mul_left]
      have hsub : sumAllInt (m - 1 - j) = D (m - j) := by
        have := ih (m - 1 - j) (by omega)
        rwa [show m - 1 - j + 1 = m - j by omega] at this
      exact congr_arg (((m + 1).choose (j + 1) : ℤ) * fW (j + 1) * ·) hsub
    rw [Finset.sum_congr rfl hterm, D_eq_sum_fW (m + 1) (by omega), Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.add_sub_cancel, Nat.sub_self, D, mul_one]
    exact add_comm _ _

lemma sumAllHead_eq (m : ℕ) : sumAllHead m = ((m + 1).factorial : ℤ) - 2 * D (m + 1) := by
  unfold sumAllHead
  rw [sum_superLists_replicate_false, runLens_replicate_false]
  have hterm : ∀ j ∈ range m,
      ((superLists (List.replicate (m - 1 - j) false)).map
        (fun c => (multinomial (runLens (List.replicate j false ++ true :: c)) : ℤ) *
          headWeight (runLens (List.replicate j false ++ true :: c)))).sum =
      ((m + 1).choose (j + 1) : ℤ) * gW (j + 1) * D (m - j) := by
    intro j hj
    have hj' : j < m := mem_range.1 hj
    have hm : (superLists (List.replicate (m - 1 - j) false)).map
        (fun c => (multinomial (runLens (List.replicate j false ++ true :: c)) : ℤ) *
          headWeight (runLens (List.replicate j false ++ true :: c))) =
        (superLists (List.replicate (m - 1 - j) false)).map
          (fun c => (((m + 1).choose (j + 1) : ℤ) * gW (j + 1)) *
            ((multinomial (runLens c) : ℤ) * intProd (runLens c))) := by
      refine List.map_congr_left fun c hc => ?_
      have hclen : c.length = m - 1 - j := by
        have hlen_sl : ∀ (l : List Bool) (x : List Bool), x ∈ superLists l → x.length = l.length := by
          intro l
          induction l with
          | nil => intro x hx; simp [superLists] at hx; simp [hx]
          | cons b r ihr =>
            intro x hx
            cases b
            · simp only [superLists, List.mem_append, List.mem_map] at hx
              rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;> simp [ihr y hy]
            · simp only [superLists, List.mem_map] at hx
              rcases hx with ⟨y, hy, rfl⟩; simp [ihr y hy]
        simpa using hlen_sl _ _ hc
      rw [runLens_append_true, runLens_replicate_false, List.singleton_append, multinomial,
        runLens_sum, hclen, show (j + 1) + (m - 1 - j + 1) = m + 1 by omega, headWeight]
      push_cast; ring
    rw [hm, List.sum_map_mul_left]
    have hsub : sumAllInt (m - 1 - j) = D (m - j) := by
      have := sumAllInt_eq_D (m - 1 - j)
      rwa [show m - 1 - j + 1 = m - j by omega] at this
    exact congr_arg (((m + 1).choose (j + 1) : ℤ) * gW (j + 1) * ·) hsub
  rw [Finset.sum_congr rfl hterm, ← sum_choose_gW_D (m + 1) (by omega), Finset.sum_range_succ]
  simp only [multinomial, List.sum_nil, add_zero, Nat.choose_self, mul_one, Nat.cast_one,
    headWeight, intProd, one_mul, Nat.add_sub_cancel, Nat.sub_self, D]
  exact add_comm _ _

lemma sumAllTail_eq_sumAllHead (m : ℕ) : sumAllTail m = sumAllHead m := by
  unfold sumAllTail sumAllHead
  rw [← sum_univ_bool_eq_superLists, ← sum_univ_bool_eq_superLists]
  let e : (Fin m → Bool) ≃ (Fin m → Bool) :=
    { toFun := fun c => c ∘ Fin.rev
      invFun := fun c => c ∘ Fin.rev
      left_inv := fun c => by funext i; simp [Fin.rev_rev]
      right_inv := fun c => by funext i; simp [Fin.rev_rev] }
  refine Fintype.sum_equiv e _ _ fun c => ?_
  have hrev : List.ofFn (e c) = (List.ofFn c).reverse := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : i < m := by simpa using h1
      rw [List.getElem_ofFn, List.getElem_reverse, List.getElem_ofFn]
      dsimp only [e, Equiv.coe_fn_mk, Function.comp_def]
      congr 1; ext; simp [Fin.rev]; omega
  rw [hrev, runLens_reverse, multinomial_reverse, ← tailWeight_reverse, List.reverse_reverse]

lemma sumAllBlock_eq (m : ℕ) (hm : 1 ≤ m) :
    sumAllBlock m = U (m + 1) - 2 * ((m + 1).factorial : ℤ) + 4 * D (m + 1) +
      2 * (2 - ((m + 1 : ℕ) : ℤ)) := by
  unfold sumAllBlock
  rw [sum_superLists_replicate_false, runLens_replicate_false]
  have hterm : ∀ j ∈ range m,
      ((superLists (List.replicate (m - 1 - j) false)).map
        (fun c => (multinomial (runLens (List.replicate j false ++ true :: c)) : ℤ) *
          blockWeight (runLens (List.replicate j false ++ true :: c)))).sum =
      ((m + 1).choose (j + 1) : ℤ) * gW (j + 1) * (((m - j).factorial : ℤ) - 2 * D (m - j)) := by
    intro j hj
    have hj' : j < m := mem_range.1 hj
    have hmap : (superLists (List.replicate (m - 1 - j) false)).map
        (fun c => (multinomial (runLens (List.replicate j false ++ true :: c)) : ℤ) *
          blockWeight (runLens (List.replicate j false ++ true :: c))) =
        (superLists (List.replicate (m - 1 - j) false)).map
          (fun c => (((m + 1).choose (j + 1) : ℤ) * gW (j + 1)) *
            ((multinomial (runLens c) : ℤ) * tailWeight (runLens c))) := by
      refine List.map_congr_left fun c hc => ?_
      have hclen : c.length = m - 1 - j := by
        have hlen_sl : ∀ (l : List Bool) (x : List Bool), x ∈ superLists l → x.length = l.length := by
          intro l
          induction l with
          | nil => intro x hx; simp [superLists] at hx; simp [hx]
          | cons b r ihr =>
            intro x hx
            cases b
            · simp only [superLists, List.mem_append, List.mem_map] at hx
              rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;> simp [ihr y hy]
            · simp only [superLists, List.mem_map] at hx
              rcases hx with ⟨y, hy, rfl⟩; simp [ihr y hy]
        simpa using hlen_sl _ _ hc
      rw [runLens_append_true, runLens_replicate_false, List.singleton_append, multinomial,
        runLens_sum, hclen, show (j + 1) + (m - 1 - j + 1) = m + 1 by omega, blockWeight]
      push_cast; ring
    rw [hmap, List.sum_map_mul_left]
    have hsub : sumAllTail (m - 1 - j) = ((m - j).factorial : ℤ) - 2 * D (m - j) := by
      rw [sumAllTail_eq_sumAllHead, sumAllHead_eq, show m - 1 - j + 1 = m - j by omega]
    exact congr_arg (((m + 1).choose (j + 1) : ℤ) * gW (j + 1) * ·) hsub
  rw [Finset.sum_congr rfl hterm]
  simp only [blockWeight, tailWeight, mul_zero, zero_add]
  have hsplit : ∑ j ∈ range m,
      ((m + 1).choose (j + 1) : ℤ) * gW (j + 1) * (((m - j).factorial : ℤ) - 2 * D (m - j)) =
      U (m + 1) - 2 * ∑ j ∈ range m, ((m + 1).choose (j + 1) : ℤ) * gW (j + 1) * D (m - j) := by
    unfold U
    rw [Nat.add_sub_cancel, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  have hE := sum_choose_gW_D (m + 1) (by omega)
  rw [Finset.sum_range_succ] at hE
  have hD0 : D 0 = 1 := rfl
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.add_sub_cancel, Nat.sub_self, hD0, mul_one] at hE
  have hgW : gW (m + 1) = 2 - ((m + 1 : ℕ) : ℤ) := rfl
  linarith

/-! ### Section 5: Double sum, two-term recurrence, and main theorem -/

lemma weightedCount_formula (m : ℕ) :
    weightedCount (m + 2) + (3 - ((m + 2 : ℕ) : ℤ)) =
      U (m + 2) - 2 * ((m + 2).factorial : ℤ) + 4 * D (m + 2) + 2 * (2 - ((m + 2 : ℕ) : ℤ)) := by
  let S : ℤ :=
    ∑ p : Equiv.Perm (Fin (m + 2)),
      ∑ c : Fin (m + 1) → Bool,
        if ∀ i : Fin (m + 1), ascends p i = true → c i = true then
          blockWeight (runLens (List.ofFn c))
        else 0
  have hWay1 : S = weightedCount (m + 2) + (3 - ((m + 2 : ℕ) : ℤ)) := by
    dsimp only [S]
    have hinner : ∀ p : Equiv.Perm (Fin (m + 2)),
        (∑ c : Fin (m + 1) → Bool,
          if ∀ i : Fin (m + 1), ascends p i = true → c i = true then
            blockWeight (runLens (List.ofFn c))
          else 0) =
        (if ascends p 0 && ascends p (Fin.last m) &&
            ((univ.filter fun i : Fin m => ascends p i.castSucc && ascends p i.succ).card == 0) then
          (2 : ℤ) ^ (univ.filter fun i : Fin m => !ascends p i.castSucc && !ascends p i.succ).card
        else 0) +
        if p = revPerm (m + 2) then 3 - ((m + 2 : ℕ) : ℤ) else 0 := by
      intro p
      rw [← Finset.sum_filter, sum_filter_dom_eq_superLists (fun i => ascends p i)
        (fun c => blockWeight (runLens c))]
      change sumBlock (List.ofFn (fun i : Fin (m + 1) => ascends p i)) = _
      have hne : List.ofFn (fun i : Fin (m + 1) => ascends p i) ≠ [] := by simp
      rw [sumBlock_eq_list_weight _ hne]
      have hhead : (List.ofFn (fun i : Fin (m + 1) => ascends p i)).head hne = ascends p 0 := by
        rw [List.head_eq_getElem]; simp
      have hlast : (List.ofFn (fun i : Fin (m + 1) => ascends p i)).getLast hne = ascends p (Fin.last m) := by
        rw [List.getLast_eq_getElem]
        simp only [List.length_ofFn, Nat.add_sub_cancel, List.getElem_ofFn]
        rfl
      have hdt : (!hasDoubleTrue (List.ofFn (fun i : Fin (m + 1) => ascends p i))) =
          ((univ.filter fun i : Fin m => ascends p i.castSucc && ascends p i.succ).card == 0) := by
        rw [hasDoubleTrue_ofFn]
        apply Bool.eq_iff_iff.2
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff, mem_univ, true_implies, Bool.and_eq_true, not_exists]
      have hdf : countDoubleFalse (List.ofFn (fun i : Fin (m + 1) => ascends p i)) =
          (univ.filter fun i : Fin m => !ascends p i.castSucc && !ascends p i.succ).card :=
        countDoubleFalse_ofFn (fun i : Fin (m + 1) => ascends p i)
      have hrev_iff : true ∉ List.ofFn (fun i : Fin (m + 1) => ascends p i) ↔ p = revPerm (m + 2) := by
        rw [List.mem_ofFn]
        simp only [not_exists]
        constructor
        · intro hall
          have hdec : p ∈ decPerms (fun _ : Fin (m + 1) => false) := by
            rw [decPerms_iff_ascends]
            intro i hi
            exact absurd hi (hall i)
          simp only [decPerms, mem_filter, mem_univ, true_and, true_implies] at hdec
          exact strictAnti_perm_eq_rev p (strictAnti_of_adj hdec)
        · rintro rfl i hi
          have hlt : (revPerm (m + 2)) i.castSucc < (revPerm (m + 2)) i.succ := of_decide_eq_true hi
          exact not_lt_of_gt (Fin.rev_lt_rev.2 Fin.castSucc_lt_succ) hlt
      rw [hhead, hlast, hdt, hdf]
      congr 1
      by_cases hp : p = revPerm (m + 2)
      · have hnot : true ∉ List.ofFn (fun i : Fin (m + 1) => ascends p i) := hrev_iff.2 hp
        rw [if_neg hnot, if_pos hp, List.length_ofFn]
        push_cast; ring
      · have hmem : true ∈ List.ofFn (fun i : Fin (m + 1) => ascends p i) := by
          by_contra hnot; exact hp (hrev_iff.1 hnot)
        rw [if_pos hmem, if_neg hp]
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [mem_univ, ↓reduceIte]
    rfl
  have hWay2 : S = U (m + 2) - 2 * ((m + 2).factorial : ℤ) + 4 * D (m + 2) +
      2 * (2 - ((m + 2 : ℕ) : ℤ)) := by
    dsimp only [S]
    rw [Finset.sum_comm]
    have hinner : ∀ c : Fin (m + 1) → Bool,
        (∑ p : Equiv.Perm (Fin (m + 2)),
          if ∀ i : Fin (m + 1), ascends p i = true → c i = true then
            blockWeight (runLens (List.ofFn c))
          else 0) =
        (multinomial (runLens (List.ofFn c)) : ℤ) * blockWeight (runLens (List.ofFn c)) := by
      intro c
      have hcongr : ∑ p : Equiv.Perm (Fin (m + 2)),
          (if ∀ i : Fin (m + 1), ascends p i = true → c i = true then
            blockWeight (runLens (List.ofFn c))
          else 0) =
          ∑ p ∈ decPerms c, blockWeight (runLens (List.ofFn c)) := by
        unfold decPerms
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        have hiff := decPerms_iff_ascends c p
        simp only [decPerms, mem_filter, mem_univ, true_and] at hiff
        by_cases h : ∀ i : Fin (m + 1), ascends p i = true → c i = true
        · rw [if_pos h, if_pos (hiff.2 h)]
        · rw [if_neg h, if_neg (fun hp => h (hiff.1 hp))]
      rw [hcongr, Finset.sum_const, nsmul_eq_mul, card_decPerms]
    simp_rw [hinner]
    rw [sum_univ_bool_eq_superLists (fun c => (multinomial (runLens c) : ℤ) * blockWeight (runLens c))]
    exact sumAllBlock_eq (m + 1) (by omega)
  rw [← hWay1, hWay2]

lemma weightedCount_two_term (n : ℕ) (hn : 3 ≤ n) :
    weightedCount n - (n : ℤ) * weightedCount (n - 1) = 1 + 4 * (-1 : ℤ) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h1 := weightedCount_formula (k + 1)
  have h0 := weightedCount_formula k
  have hU := U_step (k + 2) (by omega)
  have hD : D (k + 3) = ((k + 3 : ℕ) : ℤ) * D (k + 2) + (-1 : ℤ) ^ (k + 3) := by
    simp only [D]; push_cast; ring
  have hF : ((k + 3).factorial : ℤ) = ((k + 3 : ℕ) : ℤ) * ((k + 2).factorial : ℤ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [show k + 3 - 1 = k + 2 by omega]
  have h1' : weightedCount (k + 3) + (3 - ((k + 3 : ℕ) : ℤ)) =
      U (k + 3) - 2 * ((k + 3).factorial : ℤ) + 4 * D (k + 3) + 2 * (2 - ((k + 3 : ℕ) : ℤ)) := h1
  have h0' : weightedCount (k + 2) + (3 - ((k + 2 : ℕ) : ℤ)) =
      U (k + 2) - 2 * ((k + 2).factorial : ℤ) + 4 * D (k + 2) + 2 * (2 - ((k + 2 : ℕ) : ℤ)) := h0
  rw [hF, hD] at h1'
  push_cast at h1' h0' hU ⊢
  nlinarith

end A227918Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a227918.main := by
  intro n hn
  have h1 := A227918Proof.weightedCount_two_term n (by omega)
  have h2 := A227918Proof.weightedCount_two_term (n - 2) (by omega)
  rw [show n - 2 - 1 = n - 3 by omega] at h2
  have hpow : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n - 2) := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
    ring
  have hcast : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  rw [hcast] at h2
  linarith
