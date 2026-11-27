import FormalConjectures.ErdosProblems.«46»

/-!
For a finite coloring, some color carries at least the average reciprocal weight
on each interval. Bloom's quantitative unit-fraction theorem then gives a
monochromatic solution beyond any prescribed cutoff. Increasing the cutoffs
past the previous denominators produces pairwise disjoint solutions.

Reference: Thomas F. Bloom, *On a density conjecture about unit fractions*,
Theorem 3, https://arxiv.org/abs/2112.03726.
-/

namespace OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1

open Finset

/-- The harmonic mass above any fixed cutoff exceeds any fixed multiple of
Bloom's threshold along arbitrarily large endpoints. -/
def H1 : Prop :=
  ∀ (B N₀ : ℕ) (K : ℝ), ∃ N ≥ N₀,
    K * (Real.log (Real.log (Real.log N)) / Real.log (Real.log N) * Real.log N) <
      ∑ n ∈ Ioc B N, (1 / (n : ℝ))

/-- Bloom's finite extraction theorem, restricted to sufficiently large endpoints. -/
def H2 : Prop :=
  ∃ C > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ, A ⊆ Icc 1 N →
    C * (Real.log (Real.log (Real.log N)) / Real.log (Real.log N) * Real.log N) ≤
      ∑ n ∈ A, (1 / (n : ℝ)) →
    ∃ S ⊆ A, ∑ n ∈ S, (1 / (n : ℚ)) = 1

theorem main : H1 → H2 → type_of% @Erdos46.erdos_46.variants.infinitely_many_disjoint := by
  classical
  intro tail extract c hc
  obtain ⟨C, _, N₀, extract⟩ := extract
  let colors := hc.toFinset
  have fresh (B : ℕ) : ∃ S : Finset ℕ, (∀ n ∈ S, max B 1 < n) ∧
      ∑ n ∈ S, (1 / (n : ℚ)) = 1 ∧ (c '' (S : Set ℕ)).Subsingleton := by
    obtain ⟨N, hN, hsum⟩ := tail (max B 1) N₀ (colors.card * C)
    let threshold := C * (Real.log (Real.log (Real.log N)) / Real.log (Real.log N) * Real.log N)
    have mass : colors.card • threshold < ∑ n ∈ Ioc (max B 1) N, (1 / (n : ℝ)) := by
      simpa only [threshold, nsmul_eq_mul, mul_assoc] using hsum
    have maps (n : ℕ) (_ : n ∈ Ioc (max B 1) N) : c n ∈ colors :=
      hc.mem_toFinset.mpr ⟨n, rfl⟩
    obtain ⟨j, _, hj⟩ := exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum maps mass
    let A := (Ioc (max B 1) N).filter (fun n => c n = j)
    have hA : A ⊆ Icc 1 N := by
      intro n hn
      have h := mem_Ioc.mp (mem_filter.mp hn).1
      exact mem_Icc.mpr ⟨by omega, h.2⟩
    obtain ⟨S, hS, hunit⟩ := extract N hN A hA hj.le
    refine ⟨S, fun n hn => (mem_Ioc.mp (mem_filter.mp (hS hn)).1).1, hunit, ?_⟩
    rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩
    exact (mem_filter.mp (hS hn)).2.trans (mem_filter.mp (hS hm)).2.symm
  choose block lower unit monoColor using fresh
  let cutoff : ℕ → ℕ := Nat.rec 0 (fun _ b => max b ((block b).sup id))
  have increasing : Monotone cutoff :=
    monotone_nat_of_le_succ fun i => le_max_left (cutoff i) _
  have separated {i j : ℕ} (hij : i < j) :
      Disjoint (block (cutoff i)) (block (cutoff j)) := by
    apply disjoint_left.mpr
    intro n hi hj
    have hn : n ≤ (block (cutoff i)).sup id := le_sup (f := id) hi
    have hnext : (block (cutoff i)).sup id ≤ cutoff (i + 1) :=
      le_max_right (cutoff i) _
    have hle := hn.trans (hnext.trans (increasing (Nat.succ_le_of_lt hij)))
    have hlt := lower (cutoff j) n hj
    omega
  refine ⟨fun i => block (cutoff i), ?_, ?_⟩
  · intro i j h
    rcases lt_or_gt_of_ne h with hij | hji
    · exact separated hij
    · exact (separated hji).symm
  · intro i
    refine ⟨?_, unit (cutoff i), monoColor (cutoff i)⟩
    intro n hn
    have h := lower (cutoff i) n hn
    omega

end OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1
