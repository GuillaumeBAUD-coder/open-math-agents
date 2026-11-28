import OMAStatements.S_oeis_a365383
import Mathlib

namespace OMA.A365383Aux

open OMA.S_oeis_a365383

/-- Adding all parts of `p` (which sum to `n`) to a representation of `k` represents `k + n`. -/
lemma rep_add {n : ℕ} (p : Nat.Partition n) (k : ℕ) (h : Represents p k) :
    Represents p (k + n) := by
  obtain ⟨xs, hx, hs⟩ := h
  refine ⟨xs + p.parts, ?_, ?_⟩
  · intro x hxm
    rcases Multiset.mem_add.mp hxm with h1 | h1
    · exact hx x h1
    · exact h1
  · rw [Multiset.sum_add, hs, p.parts_sum]

lemma rep_add_mul {n : ℕ} (p : Nat.Partition n) (k j : ℕ) (h : Represents p k) :
    Represents p (k + n * j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have := rep_add p _ ih
    rw [show k + n * (j + 1) = k + n * j + n by ring]
    exact this

lemma rep_zero {n : ℕ} (p : Nat.Partition n) : Represents p 0 :=
  ⟨0, fun x hx => absurd hx (Multiset.notMem_zero x), Multiset.sum_zero⟩

/-- Every partition of `n` represents every multiple of `n`. -/
lemma rep_mul {n : ℕ} (p : Nat.Partition n) (j : ℕ) : Represents p (n * j) := by
  simpa using rep_add_mul p 0 j (rep_zero p)

/-- In a residue class mod `n`, representability propagates upward. -/
lemma rep_up {n : ℕ} (p : Nat.Partition n) (a b : ℕ) (hab : a < b) (hmod : a % n = b % n)
    (ha : Represents p (a + n)) : Represents p b := by
  obtain ⟨c, hc⟩ : n ∣ b - a := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
  have hb : b = a + n * c := by rw [← hc]; omega
  cases c with
  | zero => simp at hb; omega
  | succ c =>
    have := rep_add_mul p (a + n) c ha
    rw [hb, show a + n * (c + 1) = a + n + n * c by ring]
    exact this

/-- For a fixed partition, the bad indices (where `k + n` is represented but `k` is not) form a
finite set: at most one per residue class mod `n`. -/
lemma bad_finite {n : ℕ} (hn : 0 < n) (p : Nat.Partition n) :
    {k : ℕ | Represents p (k + n) ∧ ¬ Represents p k}.Finite := by
  apply Set.Finite.of_finite_image (f := fun k => k % n)
  · apply (Set.finite_lt_nat n).subset
    rintro _ ⟨k, -, rfl⟩
    exact Nat.mod_lt k hn
  · intro a ha b hb hab
    simp only [Set.mem_ofPred_eq] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hb.2 (rep_up p a b h hab ha.1)
    · exact ha.2 (rep_up p b a h hab.symm hb.1)

/-- The partition `[n]` only represents multiples of `n`. -/
lemma indiscrete_dvd {n : ℕ} (hn : n ≠ 0) (k : ℕ) (h : Represents (Nat.Partition.indiscrete n) k) :
    n ∣ k := by
  obtain ⟨xs, hx, hs⟩ := h
  rw [← hs]
  apply Multiset.dvd_sum
  intro a ha
  have := hx a ha
  rw [Nat.Partition.indiscrete_parts hn, Multiset.mem_singleton] at this
  rw [this]

end OMA.A365383Aux

open OMA.S_oeis_a365383 OMA.A365383Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a365383.main := by
  refine ⟨?_, ?_⟩
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun k _ => by simp⟩
    · have hfin : {k : ℕ | ∃ p : Nat.Partition n, Represents p (k + n) ∧ ¬ Represents p k}.Finite := by
        have e : {k : ℕ | ∃ p : Nat.Partition n, Represents p (k + n) ∧ ¬ Represents p k} =
            ⋃ p : Nat.Partition n, {k : ℕ | Represents p (k + n) ∧ ¬ Represents p k} := by
          ext k
          simp
        rw [e]
        exact Set.finite_iUnion (fun p => bad_finite hn p)
      obtain ⟨B, hB⟩ := hfin.bddAbove
      refine ⟨B + 1, fun k hk => ?_⟩
      unfold row
      classical
      congr 1
      apply Finset.filter_congr
      intro p _
      constructor
      · intro h
        by_contra h'
        have : k ≤ B := hB (show k ∈ {k : ℕ | ∃ p : Nat.Partition n,
          Represents p (k + n) ∧ ¬ Represents p k} from ⟨p, h, h'⟩)
        omega
      · exact rep_add p k
  · intro n t hn hK
    obtain ⟨K, hK⟩ := hK
    have hk : K ≤ n * K := Nat.le_mul_of_pos_left K hn
    have h1 := hK (n * K) hk
    unfold row at h1
    classical
    have hall : (Finset.univ.filter (fun p : Nat.Partition n => Represents p (n * K))) =
        Finset.univ := Finset.filter_true_of_mem (fun p _ => rep_mul p K)
    have hsub := Finset.filter_subset (fun p : Nat.Partition n => Represents p (n * K + t))
      Finset.univ
    have hcard : (Finset.univ : Finset (Nat.Partition n)).card ≤
        (Finset.univ.filter (fun p : Nat.Partition n => Represents p (n * K + t))).card := by
      have h2 : (Finset.univ.filter (fun p : Nat.Partition n => Represents p (n * K + t))).card =
          (Finset.univ.filter (fun p : Nat.Partition n => Represents p (n * K))).card := by
        convert h1
      rw [h2, hall]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : Nat.Partition.indiscrete n ∈
        Finset.univ.filter (fun p : Nat.Partition n => Represents p (n * K + t)) := by
      rw [heq]
      exact Finset.mem_univ _
    have hd := indiscrete_dvd (Nat.pos_iff_ne_zero.mp hn) _ (Finset.mem_filter.mp hmem).2
    exact (Nat.dvd_add_right (dvd_mul_right n K)).mp hd

