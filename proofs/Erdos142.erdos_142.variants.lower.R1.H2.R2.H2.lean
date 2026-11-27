import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Covering an interval by translates

For each uncovered x in [N+1,2N], exactly |S| shifts t in [0,2N) have x in t+S.
Averaging picks a shift that removes at least |S|/(2N) of the remaining points.
After q choices the number left is at most N exp(-q|S|/(2N)), which is less
than one under the stated logarithmic hypothesis. Fox and Hunter use a random-shifts
version of this cover in Three-color van der Waerden numbers grow super-exponentially
(2026), page 2.
-/

open Finset

namespace Erdos142TranslateCover

open scoped Classical

private def hit (S : Finset ℕ) (t x : ℕ) : Prop :=
  ∃ a ∈ S, x = t + a

private theorem hit_count (N : ℕ) (S U : Finset ℕ)
    (hS : S ⊆ Icc 1 N) (hU : U ⊆ Icc (N + 1) (2 * N)) :
    ∑ t ∈ range (2 * N), (U.filter (hit S t)).card = U.card * S.card := by
  classical
  have hrow (x : ℕ) (hx : x ∈ U) :
      ((range (2 * N)).filter (fun t ↦ hit S t x)).card = S.card := by
    obtain ⟨hxlo, hxhi⟩ := mem_Icc.mp (hU hx)
    have himage : (range (2 * N)).filter (fun t ↦ hit S t x) =
        S.image (fun a ↦ x - a) := by
      apply Finset.ext
      intro t
      constructor
      · intro ht
        obtain ⟨_, a, ha, heq⟩ := mem_filter.mp ht
        exact mem_image.mpr ⟨a, ha, by omega⟩
      · intro ht
        obtain ⟨a, ha, rfl⟩ := mem_image.mp ht
        obtain ⟨halo, hahi⟩ := mem_Icc.mp (hS ha)
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), a, ha, by omega⟩
    rw [himage]
    apply card_image_of_injOn
    intro a ha b hb hab
    have hal := (mem_Icc.mp (hS ha)).2
    have hbl := (mem_Icc.mp (hS hb)).2
    dsimp at hab
    omega
  calc
    _ = ∑ t ∈ range (2 * N), ∑ x ∈ U, if hit S t x then 1 else 0 := by
      simp only [card_filter]
    _ = ∑ x ∈ U, ∑ t ∈ range (2 * N), if hit S t x then 1 else 0 := sum_comm
    _ = ∑ x ∈ U, S.card := by
      apply sum_congr rfl
      intro x hx
      rw [← card_filter]
      exact hrow x hx
    _ = U.card * S.card := by simp

private theorem greedy_step (N : ℕ) (hN : 0 < N) (S U : Finset ℕ)
    (hS : S ⊆ Icc 1 N) (hU : U ⊆ Icc (N + 1) (2 * N)) :
    ∃ t : ℕ, ((U.filter fun x ↦ ¬ hit S t x).card : ℝ) ≤
      (U.card : ℝ) * (1 - (S.card : ℝ) / (2 * (N : ℝ))) := by
  classical
  let p : ℝ := (S.card : ℝ) / (2 * (N : ℝ))
  have hD : 0 < (2 : ℝ) * (N : ℝ) := by positivity
  have hshifts : (range (2 * N)).Nonempty := by
    exact ⟨0, mem_range.mpr (by omega)⟩
  have hsum : ∑ t ∈ range (2 * N), ((U.filter (hit S t)).card : ℝ) =
      (U.card : ℝ) * (S.card : ℝ) := by exact_mod_cast hit_count N S U hS hU
  have hconst : (∑ _t ∈ range (2 * N), (U.card : ℝ) * p) =
      (U.card : ℝ) * (S.card : ℝ) := by
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [p]
    field_simp
  obtain ⟨t, _, havg⟩ :
      ∃ t ∈ range (2 * N), (U.card : ℝ) * p ≤ ((U.filter (hit S t)).card : ℝ) :=
    exists_le_of_sum_le hshifts (le_of_eq (hconst.trans hsum.symm))
  have hparts : ((U.filter (hit S t)).card : ℝ) +
      ((U.filter fun x ↦ ¬ hit S t x).card : ℝ) = (U.card : ℝ) := by
    exact_mod_cast (card_filter_add_card_filter_not (s := U) (hit S t))
  refine ⟨t, ?_⟩
  change ((U.filter fun x ↦ ¬ hit S t x).card : ℝ) ≤ (U.card : ℝ) * (1 - p)
  rw [mul_sub, mul_one]
  linarith

/-- Sufficiently many translates of a dense finite set cover a central interval. -/
theorem translate_cover (N q : ℕ) (S : Finset ℕ) (hN : 0 < N) (_hq : 0 < q)
    (hS : S ⊆ Icc 1 N) (hbound : 2 * (N : ℝ) * Real.log (N : ℝ) <
      (q : ℝ) * (S.card : ℝ)) :
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Icc 1 N,
      ∃ t : Fin q, ∃ a ∈ S, x + N = shifts t + a := by
  classical
  let U := Icc (N+1) (2*N)
  let p : ℝ := (S.card : ℝ) / (2 * (N : ℝ))
  let missed {m : ℕ} (f : Fin m → ℕ) := U.filter (fun x ↦ ¬ ∃ t, hit S (f t) x)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hD : 0 < (2 : ℝ) * (N : ℝ) := by positivity
  have hcard : S.card ≤ N := (card_le_card hS).trans_eq (Nat.card_Icc 1 N)
  have hcardU : U.card = N := by
    rw [Nat.card_Icc]
    omega
  have hbase : 0 ≤ 1 - p := by
    have hS' : (S.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
    apply sub_nonneg.mpr
    dsimp [p]
    apply (div_le_iff₀ hD).mpr
    linarith
  have hiter (m : ℕ) : ∃ f : Fin m → ℕ, ((missed f).card : ℝ) ≤ (N : ℝ) * (1 - p)^m := by
    induction m with
    | zero =>
      use Fin.elim0
      simp [missed, hcardU]
    | succ m ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨t, ht⟩ := greedy_step N hN S (missed f) hS (filter_subset _ _)
      use Fin.cons t f
      have hsub : missed (Fin.cons t f) ⊆ (missed f).filter (fun x ↦ ¬ hit S t x) := by
        intro x hx
        obtain ⟨hxU, hh⟩ := mem_filter.mp hx
        apply mem_filter.mpr
        constructor
        · apply mem_filter.mpr
          refine ⟨hxU, ?_⟩
          rintro ⟨i, hi⟩
          exact hh ⟨i.succ, by simpa using hi⟩
        · intro hi
          exact hh ⟨0, by simpa using hi⟩
      have hstep : ((missed (Fin.cons t f)).card : ℝ) ≤
          (((missed f).filter fun x ↦ ¬ hit S t x).card : ℝ) := by
        exact_mod_cast card_le_card hsub
      calc
        _ ≤ _ := hstep
        _ ≤ ((missed f).card : ℝ) * (1 - p) := ht
        _ ≤ (N : ℝ) * (1 - p)^m * (1 - p) := mul_le_mul_of_nonneg_right hf hbase
        _ = _ := by rw [pow_succ, mul_assoc]
  have hmass : Real.log (N : ℝ) < (q : ℝ) * p := by
    dsimp [p]
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hD).mpr
    linarith only [hbound]
  have hpow : (1 - p)^q ≤ Real.exp (-(q : ℝ) * p) := by
    have hb : 1 - p ≤ Real.exp (-p) := by linarith only [Real.add_one_le_exp (-p)]
    calc
      _ ≤ (Real.exp (-p))^q := pow_le_pow_left₀ hbase hb _
      _ = _ := by rw [← Real.exp_nat_mul, mul_neg, neg_mul]
  have hsmall : (N : ℝ) * (1 - p)^q < 1 := by
    calc
      _ ≤ (N : ℝ) * Real.exp (-(q : ℝ) * p) := mul_le_mul_of_nonneg_left hpow hNp.le
      _ = Real.exp (Real.log (N : ℝ) + -(q : ℝ) * p) := by
        rw [Real.exp_add, Real.exp_log hNp]
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith only [hmass])
      _ = 1 := Real.exp_zero
  obtain ⟨f, hf⟩ := hiter q
  have hsmallCard : (missed f).card < 1 := by exact_mod_cast hf.trans_lt hsmall
  have hempty : missed f = ∅ := card_eq_zero.mp (by omega)
  refine ⟨f, ?_⟩
  intro x hx
  change ∃ t, hit S (f t) (x + N)
  by_contra h
  obtain ⟨hxlo, hxhi⟩ := mem_Icc.mp hx
  have hm : x + N ∈ missed f :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h⟩
  simp [hempty] at hm

end Erdos142TranslateCover

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 :=
  Erdos142TranslateCover.translate_cover
