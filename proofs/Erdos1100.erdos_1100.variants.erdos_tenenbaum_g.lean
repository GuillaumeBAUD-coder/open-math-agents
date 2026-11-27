import FormalConjectures.ErdosProblems.«1100»

/-! The squarefree case of the consecutive-divisor bound of Erdős and Tenenbaum (1989).
For a coprime pair of consecutive divisors, split the primes into those in the left
divisor, those in the right divisor, and the rest. Each of these three sets
determines the index when its role is specified. The divisor indexing follows the
upstream proof of the elementary lower bound by the number of prime factors. -/

open Finset Erdos1100
open scoped ArithmeticFunction.omega

namespace OMA.ConsecutiveDivisors

private def smallParts (P : Finset ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter fun T => 3 * T.card ≤ P.card

private lemma smallParts_bound (P : Finset ℕ) :
    ((smallParts P).card : ℝ) ≤ (3 / (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ P.card := by
  let D := (2 : ℝ) ^ ((2 : ℝ) / 3)
  have hD : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  rw [div_pow, le_div_iff₀ (pow_pos hD _)]
  change _ * D ^ P.card ≤ _
  have hterm (T : Finset ℕ) (hT : T ∈ smallParts P) :
      D ^ P.card ≤ (2 : ℝ) ^ (P.card - T.card) := by
    obtain ⟨hsub, hsize⟩ := mem_filter.mp hT
    have hle := card_le_card (mem_powerset.mp hsub)
    dsimp [D]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast (2 : ℝ) (P.card - T.card)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [Nat.cast_sub hle]
    have h' : (3 : ℝ) * T.card ≤ P.card := by exact_mod_cast hsize
    linarith
  calc
    _ = ∑ _T ∈ smallParts P, D ^ P.card := by simp
    _ ≤ ∑ T ∈ smallParts P, (2 : ℝ) ^ (P.card - T.card) := sum_le_sum hterm
    _ ≤ ∑ T ∈ P.powerset, (2 : ℝ) ^ (P.card - T.card) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = 3 ^ P.card := by
      simpa [show (1 : ℝ) + 2 = 3 by norm_num] using sum_pow_mul_eq_add_pow (1 : ℝ) 2 P

private lemma three_encodings {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (L : Finset (Finset ℕ)) (a b c : ι → Finset ℕ)
    (ha : (S : Set ι).InjOn a) (hb : (S : Set ι).InjOn b) (hc : (S : Set ι).InjOn c)
    (hcover : ∀ i ∈ S, a i ∈ L ∨ b i ∈ L ∨ c i ∈ L) :
    S.card ≤ 3 * L.card := by
  classical
  let part (f : ι → Finset ℕ) := S.filter fun i => f i ∈ L
  have hbound (f : ι → Finset ℕ) (hf : (S : Set ι).InjOn f) :
      (part f).card ≤ L.card :=
    card_le_card_of_injOn f (fun _ hi => (mem_filter.mp hi).2)
      (hf.mono (fun _ hi => (mem_filter.mp hi).1))
  have hsub : S ⊆ part a ∪ part b ∪ part c := by
    intro i hi
    rcases hcover i hi with h | h | h <;> simp [part, hi, h]
  calc
    S.card ≤ (part a ∪ part b ∪ part c).card := card_le_card hsub
    _ ≤ (part a ∪ part b).card + (part c).card := card_union_le _ _
    _ ≤ ((part a).card + (part b).card) + (part c).card :=
      Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ (L.card + L.card) + L.card :=
      Nat.add_le_add (Nat.add_le_add (hbound a ha) (hbound b hb)) (hbound c hc)
    _ = 3 * L.card := by omega

private lemma count_pairs {n : ℕ} (hsq : Squarefree n) :
    tauPerp n ≤ 3 * (smallParts n.primeFactors).card := by
  classical
  have hn : n ≠ 0 := hsq.ne_zero
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn]
  let d := Nat.nth (· ∣ n)
  let I := Fin (n.divisors.card - 1)
  let a (i : I) := d i.val
  let b (i : I) := d (i.val + 1)
  have hidx (i : I) : i.val + 1 < hf.toFinset.card := by
    have := i.isLt
    omega
  have haD (i : I) : a i ∣ n := Nat.nth_mem_of_lt_card hf (by have := hidx i; omega)
  have hbD (i : I) : b i ∣ n := Nat.nth_mem_of_lt_card hf (hidx i)
  have haM : StrictMono a := fun i j hij =>
    Nat.nth_lt_nth_of_lt_card hf hij (by have := hidx j; omega)
  have hbM : StrictMono b := fun i j hij =>
    Nat.nth_lt_nth_of_lt_card hf (Nat.add_lt_add_right hij 1) (hidx j)
  have habM : StrictMono (fun i => a i * b i) := fun _ _ hij =>
    Nat.mul_lt_mul_of_lt_of_lt (haM hij) (hbM hij)
  let S := univ.filter fun i : I => (a i).Coprime (b i)
  let A (i : I) := (a i).primeFactors
  let B (i : I) := (b i).primeFactors
  let P := n.primeFactors
  let C (i : I) := P \ (A i ∪ B i)
  have hA (i : I) : A i ⊆ P := Nat.primeFactors_mono (haD i) hn
  have hB (i : I) : B i ⊆ P := Nat.primeFactors_mono (hbD i) hn
  have hU (i : I) : A i ∪ B i ⊆ P := union_subset (hA i) (hB i)
  have prodA (i : I) : ∏ p ∈ A i, p = a i :=
    Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd (haD i))
  have prodB (i : I) : ∏ p ∈ B i, p = b i :=
    Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd (hbD i))
  have hdis (i : I) (hi : i ∈ S) : Disjoint (A i) (B i) :=
    (show (a i).Coprime (b i) from (mem_filter.mp hi).2).disjoint_primeFactors
  change S.card ≤ 3 * (smallParts P).card
  apply three_encodings S _ A B C
  · intro i _ j _ e
    apply haM.injective
    rw [← prodA i, ← prodA j, e]
  · intro i _ j _ e
    apply hbM.injective
    rw [← prodB i, ← prodB j, e]
  · intro i hi j hj e
    have eu : A i ∪ B i = A j ∪ B j := by
      simpa only [C, Finset.sdiff_sdiff_eq_self (hU i), Finset.sdiff_sdiff_eq_self (hU j)]
        using congrArg (fun T => P \ T) e
    apply habM.injective
    change a i * b i = a j * b j
    rw [← prodA i, ← prodB i, ← prodA j, ← prodB j,
      ← prod_union (hdis i hi), ← prod_union (hdis j hj), eu]
  · intro i hi
    have hcardU := card_union_of_disjoint (hdis i hi)
    have hcardC : (C i).card = P.card - (A i ∪ B i).card := card_sdiff_of_subset (hU i)
    have hle := card_le_card (hU i)
    have hs : 3 * (A i).card ≤ P.card ∨ 3 * (B i).card ≤ P.card ∨
        3 * (C i).card ≤ P.card := by omega
    simpa [smallParts, hA i, hB i, show C i ⊆ P from sdiff_subset] using hs

end OMA.ConsecutiveDivisors

open OMA.ConsecutiveDivisors in
theorem OMA.solution : type_of% @Erdos1100.erdos_1100.variants.erdos_tenenbaum_g := by
  intro k
  let bound := 3 * (3 / (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ k
  have hpos : 0 ≤ bound := by dsimp [bound]; positivity
  suffices g k ≤ ⌊bound⌋₊ by exact (Nat.cast_le.mpr this).trans (Nat.floor_le hpos)
  apply csSup_le'
  rintro t ⟨n, hsq, hk, rfl⟩
  apply Nat.le_floor
  have hω : ω n = n.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
    rfl
  have hcount : (tauPerp n : ℝ) ≤ 3 * ((smallParts n.primeFactors).card : ℝ) := by
    exact_mod_cast count_pairs hsq
  exact hcount.trans (by
    dsimp [bound]
    rw [← hk, hω]
    exact mul_le_mul_of_nonneg_left (smallParts_bound _) (by norm_num))
