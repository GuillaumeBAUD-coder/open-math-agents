import FormalConjectures.Paper.BurningNumberConjecture
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat

/-! The burning number of a path, by covering it with intervals. -/

open SimpleGraph BurningNumberConjecture
open scoped BigOperators

theorem OMA.solution : type_of% @BurningNumberConjecture.burning_number_conjecture.variants.path := by
  intro n hn
  have hreach := pathGraph_preconnected n
  have hwalk {a b : Fin n} (p : (pathGraph n).Walk a b) :
      a.val ≤ b.val + p.length ∧ b.val ≤ a.val + p.length := by
    induction p with
    | nil => simp
    | @cons a u b hadj p ih =>
      have h := pathGraph_adj.mp hadj
      simp only [Walk.length_cons]
      omega
  have hdistLower (a b : Fin n) :
      a.val ≤ b.val + (pathGraph n).dist a b ∧
        b.val ≤ a.val + (pathGraph n).dist a b := by
    obtain ⟨p, hp⟩ := (hreach a b).exists_walk_length_eq_dist
    rw [← hp]
    exact hwalk p
  have hdistIncreasing (a : Fin n) : ∀ (d : ℕ) (b : Fin n), b.val = a.val + d →
      (pathGraph n).dist a b ≤ d := by
    intro d
    induction d with
    | zero =>
      intro b hb
      have hab : a = b := Fin.ext (by omega)
      simp [hab]
    | succ d ih =>
      intro b hb
      let u : Fin n := ⟨a.val + d, by have := b.isLt; omega⟩
      have hadj : (pathGraph n).Adj u b := pathGraph_adj.mpr
        (Or.inl (by change a.val + d + 1 = b.val; omega))
      have hstep : (pathGraph n).dist u b = 1 := dist_eq_one_iff_adj.mpr hadj
      have hu := ih u rfl
      have htriangle := hadj.reachable.dist_triangle_right a
      omega
  have hdistUpper (a b : Fin n) (r : ℕ) (ha : a.val ≤ b.val + r)
      (hb : b.val ≤ a.val + r) : (pathGraph n).dist a b ≤ r := by
    by_cases hab : a.val ≤ b.val
    · exact (hdistIncreasing a (b.val - a.val) b (by omega)).trans (by omega)
    · rw [dist_comm]
      exact (hdistIncreasing b (a.val - b.val) a (by omega)).trans (by omega)
  have hceil (k : ℕ) : ⌈Real.sqrt n⌉₊ ≤ k ↔ n ≤ k ^ 2 := by
    rw [Nat.ceil_le, Real.sqrt_le_left (by positivity), ← Nat.cast_pow, Nat.cast_le]
  let k := ⌈Real.sqrt n⌉₊
  have hnk : n ≤ k ^ 2 := (hceil k).mp le_rfl
  have hcover : ∃ x : Fin k → Fin n, IsBurningSequence (pathGraph n) x := by
    -- The radius-r fire covers the block starting at r², truncated by the end of the path.
    let center (i : Fin k) : Fin n :=
      ⟨min (i.rev.val ^ 2 + i.rev.val) (n - 1),
        (min_le_right _ _).trans_lt (by omega)⟩
    refine ⟨center, fun v => ?_⟩
    let r : Fin k := ⟨Nat.sqrt v.val, Nat.sqrt_lt'.mpr (v.isLt.trans_le hnk)⟩
    refine ⟨r.rev, hreach _ _, ?_⟩
    have hrlo : r.val ^ 2 ≤ v.val := Nat.sqrt_le' _
    have hrhi : v.val < (r.val + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have hrhi' : v.val ≤ r.val ^ 2 + 2 * r.val := by nlinarith
    have hc : (center r.rev).val = min (r.val ^ 2 + r.val) (n - 1) := by
      simp [center]
    have hv := v.isLt
    have hd := hdistUpper (center r.rev) v r.val (by omega) (by omega)
    have hr := r.isLt
    have hrev := Fin.val_rev r
    omega
  refine le_antisymm (Nat.sInf_le hcover) ?_
  have hfeasible : {j | ∃ y : Fin j → Fin n, IsBurningSequence (pathGraph n) y}.Nonempty :=
    ⟨k, hcover⟩
  have hminimal := Nat.sInf_mem hfeasible
  change ∃ x : Fin (burningNumber (pathGraph n)) → Fin n,
    IsBurningSequence (pathGraph n) x at hminimal
  obtain ⟨x, hx⟩ := hminimal
  let m := burningNumber (pathGraph n)
  apply (hceil m).mpr
  let interval (r : Fin m) :=
    Finset.Icc ((x r.rev).val - r.val) ((x r.rev).val + r.val)
  have hcard : n ≤ ((Finset.univ : Finset (Fin m)).biUnion interval).card := by
    have hmap : Set.MapsTo (fun v : Fin n => v.val)
        (Finset.univ : Finset (Fin n)) ((Finset.univ : Finset (Fin m)).biUnion interval) := by
      intro v _
      obtain ⟨i, _, hi⟩ := hx v
      have hd := hdistLower (x i) v
      have hrev := Fin.val_rev i
      refine Finset.mem_biUnion.mpr ⟨i.rev, Finset.mem_univ _, ?_⟩
      simp only [interval, Fin.rev_rev, Finset.mem_Icc]
      omega
    simpa using Finset.card_le_card_of_injOn _ hmap Fin.val_injective.injOn
  have hsum : ∀ t : ℕ, (∑ j ∈ Finset.range t, (2 * j + 1)) = t ^ 2 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  calc
    n ≤ ((Finset.univ : Finset (Fin m)).biUnion interval).card := hcard
    _ ≤ ∑ r : Fin m, (interval r).card := Finset.card_biUnion_le
    _ ≤ ∑ r : Fin m, (2 * r.val + 1) := by
      apply Finset.sum_le_sum
      intro r _
      simp only [interval, Nat.card_Icc]
      omega
    _ = m ^ 2 := (Fin.sum_univ_eq_sum_range (fun j : ℕ => 2 * j + 1) m).trans (hsum m)