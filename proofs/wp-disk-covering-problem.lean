import OMAStatements.S_wp_disk_covering_problem
import Mathlib

/-!
# The optimal radius in the disk covering problem is attained

The disk covering problem asks for the least common radius `r n` of `n` closed disks covering the
closed unit disk. Its open part is the numerical value of `r n`. What the statement below asks is
that `r` exists, i.e. that for every `n >= 1` the set `S n` of covering radii has a least element;
this is a compactness statement and the values are not needed.

Three facts are used.

* `S n` is upward closed: the same centres with a larger radius still cover.
* Every covering radius is nonnegative: the centre of the unit disk lies in some disk of the
  cover, so its distance to that centre is `<= R` while distances are `>= 0`.
* `S n` contains its infimum. A covering configuration may be assumed to have all centres within
  distance `1 + R` of the origin, since a centre farther than that covers no point of the unit
  disk and can be replaced by the origin. The set of pairs (configuration, radius) that cover the
  unit disk is closed, because covering means that for every point `x` of the unit disk some index
  `i` has `dist x (c i) <= R`, a finite union of closed conditions. Hence a sequence of covering
  radii decreasing to the infimum, with centres clamped into a fixed compact ball, has a
  convergent subsequence whose limit is a covering configuration at the infimum.
-/

open Set Metric
open scoped Topology

namespace DCP

/-- The plane of the statement. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The set of radii for which the closed unit disk is covered by `n` closed disks. -/
def S (n : ℕ) : Set ℝ := {radius : ℝ | OMA.S_wp_disk_covering_problem.IsCoveringRadius n radius}

/-- The covering relation on pairs (centres, radius). -/
def Cover (n : ℕ) : Set ((Fin n → Plane) × ℝ) :=
  {p | Metric.closedBall (0 : Plane) 1 ⊆ ⋃ i, Metric.closedBall (p.1 i) p.2}

/-- `S n` is upward closed. -/
lemma S_mono {n : ℕ} {R R' : ℝ} (h : R ∈ S n) (hRR' : R ≤ R') : R' ∈ S n := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, Subset.trans hc (iUnion_mono fun i => closedBall_subset_closedBall hRR')⟩

/-- Every covering radius is nonnegative. -/
lemma S_nonneg {n : ℕ} {R : ℝ} (h : R ∈ S n) : 0 ≤ R := by
  obtain ⟨c, hc⟩ := h
  have h0 : (0 : Plane) ∈ closedBall (0 : Plane) 1 := by simp
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hc h0)
  have hd : dist (0 : Plane) (c i) ≤ R := mem_closedBall.1 hi
  have hd0 : (0 : ℝ) ≤ dist (0 : Plane) (c i) := dist_nonneg
  linarith

/-- `S n` is nonempty for `n >= 1`: the disk of radius `2` about the origin covers the unit disk. -/
lemma S_nonempty {n : ℕ} (hn : 0 < n) : (S n).Nonempty := by
  refine ⟨2, fun _ => 0, ?_⟩
  intro x hx
  exact mem_iUnion.2 ⟨⟨0, hn⟩, closedBall_subset_closedBall (by norm_num) hx⟩

/-- The set of covering pairs (configuration, radius) is closed. -/
lemma isClosed_cover (n : ℕ) : IsClosed (Cover n) := by
  have h : Cover n = ⋂ (x : Plane), ⋂ (_ : x ∈ closedBall (0 : Plane) 1),
      ⋃ i : Fin n, {p : (Fin n → Plane) × ℝ | x ∈ closedBall (p.1 i) p.2} := by
    ext p
    simp only [Cover, subset_def, mem_iInter, mem_iUnion, mem_ofPred_eq]
  rw [h]
  refine isClosed_iInter fun x => isClosed_iInter fun hx => isClosed_iUnion_of_finite fun i => ?_
  have hcont : Continuous fun p : (Fin n → Plane) × ℝ => dist x (p.1 i) :=
    continuous_const.dist ((continuous_apply i).comp continuous_fst)
  have hset : {p : (Fin n → Plane) × ℝ | x ∈ closedBall (p.1 i) p.2} =
      {p : (Fin n → Plane) × ℝ | dist x (p.1 i) ≤ p.2} := by
    ext p
    simp only [mem_ofPred_eq, mem_closedBall]
  rw [hset]
  exact isClosed_le hcont continuous_snd

/-- The infimum of the set of covering radii is itself a covering radius. -/
lemma sInf_mem {n : ℕ} (hn : 0 < n) : sInf (S n) ∈ S n := by
  have hne : (S n).Nonempty := S_nonempty hn
  have hbdd : BddBelow (S n) := ⟨0, fun r hr => S_nonneg hr⟩
  have hm0 : 0 ≤ sInf (S n) := le_csInf hne fun b hb => S_nonneg hb
  -- radii slightly above the infimum are covering radii
  have hRmem : ∀ k : ℕ, (sInf (S n) + 1 / ((k : ℝ) + 1)) ∈ S n := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hlt : sInf (S n) < sInf (S n) + 1 / ((k : ℝ) + 1) := lt_add_of_pos_right _ hpos
    obtain ⟨b, hb, hblt⟩ := exists_lt_of_csInf_lt hne hlt
    exact S_mono hb hblt.le
  choose c hc using hRmem
  -- a uniform bound on the auxiliary radii
  have hrec : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := by
    intro k
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    calc 1 / ((k : ℝ) + 1) ≤ 1 / 1 := one_div_le_one_div_of_le (by norm_num) hk
      _ = 1 := by norm_num
  -- centres farther than 1 + R from the origin cover nothing and are moved to the origin
  let cl : ℕ → Fin n → Plane := fun k i =>
    if dist (0 : Plane) (c k i) ≤ 1 + (sInf (S n) + 1 / ((k : ℝ) + 1)) then c k i else 0
  have hcl_cover : ∀ k, closedBall (0 : Plane) 1 ⊆
      ⋃ i, closedBall (cl k i) (sInf (S n) + 1 / ((k : ℝ) + 1)) := by
    intro k x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hc k hx)
    have hd : dist x (c k i) ≤ sInf (S n) + 1 / ((k : ℝ) + 1) := mem_closedBall.1 hi
    have hd0 : dist (0 : Plane) (c k i) ≤ 1 + (sInf (S n) + 1 / ((k : ℝ) + 1)) := by
      have h1 : dist (0 : Plane) x ≤ 1 := mem_closedBall'.1 hx
      calc dist (0 : Plane) (c k i) ≤ dist (0 : Plane) x + dist x (c k i) := dist_triangle _ _ _
        _ ≤ 1 + (sInf (S n) + 1 / ((k : ℝ) + 1)) := by linarith
    have hcl : cl k i = c k i := by
      simp only [cl, if_pos hd0]
    refine mem_iUnion.2 ⟨i, ?_⟩
    rw [hcl]
    exact mem_closedBall.2 hd
  have hcl_bound : ∀ k i, dist (0 : Plane) (cl k i) ≤ sInf (S n) + 2 := by
    intro k i
    have h1 := hrec k
    by_cases hcond : dist (0 : Plane) (c k i) ≤ 1 + (sInf (S n) + 1 / ((k : ℝ) + 1))
    · have hcl : cl k i = c k i := by simp only [cl, if_pos hcond]
      rw [hcl]
      linarith
    · have hcl : cl k i = 0 := by simp only [cl, if_neg hcond]
      rw [hcl, dist_self]
      linarith
  set m := sInf (S n) with hm
  -- the pairs (clamped configuration, radius) lie in a fixed compact ball
  let q : ℕ → (Fin n → Plane) × ℝ := fun k => (cl k, m + 1 / ((k : ℝ) + 1))
  have hqT : ∀ k, q k ∈ Cover n := by
    intro k
    have h := hcl_cover k
    simpa [q, hm, Cover] using h
  have hqK : ∀ k, q k ∈ closedBall ((0 : Fin n → Plane), (0 : ℝ)) (m + 3) := by
    intro k
    rw [← closedBall_prod_same (0 : Fin n → Plane) (0 : ℝ) (m + 3)]
    constructor
    · rw [mem_closedBall, dist_pi_le_iff (by linarith)]
      intro i
      have h := hcl_bound k i
      rw [dist_zero_left] at h
      simp only [q, Pi.zero_apply, dist_zero_right]
      linarith
    · rw [mem_closedBall, Real.dist_eq]
      have h1 := hrec k
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have habs : |m + 1 / ((k : ℝ) + 1) - 0| = m + 1 / ((k : ℝ) + 1) := by
        rw [sub_zero]
        exact abs_of_pos (by linarith)
      rw [habs]
      linarith
  have hK : IsCompact (closedBall ((0 : Fin n → Plane), (0 : ℝ)) (m + 3)) :=
    isCompact_closedBall _ _
  obtain ⟨a, _haK, φ, hφ, htend⟩ := hK.tendsto_subseq hqK
  have haT : a ∈ Cover n :=
    (isClosed_cover n).mem_of_tendsto htend (Filter.Eventually.of_forall fun j => hqT (φ j))
  have h2a : Filter.Tendsto (fun j => (q (φ j)).2) Filter.atTop (𝓝 a.2) :=
    (continuous_snd.tendsto a).comp htend
  have hdiv : Filter.Tendsto (fun j => 1 / (((φ j : ℕ) : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have h2b : Filter.Tendsto (fun j => (q (φ j)).2) Filter.atTop (𝓝 m) := by
    have hsum : Filter.Tendsto (fun j => m + 1 / (((φ j : ℕ) : ℝ) + 1)) Filter.atTop (𝓝 (m + 0)) :=
      tendsto_const_nhds.add hdiv
    simpa [q] using hsum
  have ha2 : a.2 = m := tendsto_nhds_unique h2a h2b
  have haT' : closedBall (0 : Plane) 1 ⊆ ⋃ i, closedBall (a.1 i) a.2 := haT
  rw [ha2] at haT'
  exact ⟨a.1, haT'⟩

/-- The optimal covering radius is attained for every `n >= 1`. -/
theorem main : ∃ r : ℕ → ℝ, ∀ n : ℕ, 0 < n → IsLeast (S n) (r n) := by
  refine ⟨fun n => sInf (S n), fun n hn => ?_⟩
  have hbdd : BddBelow (S n) := ⟨0, fun r hr => S_nonneg hr⟩
  exact ⟨sInf_mem hn, fun b hb => csInf_le hbdd hb⟩

end DCP

theorem OMA.solution : type_of% @OMA.S_wp_disk_covering_problem.main := DCP.main
