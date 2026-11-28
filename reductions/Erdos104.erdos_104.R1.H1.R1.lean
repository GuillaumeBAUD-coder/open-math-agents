import OMAReductions.R_Erdos104_erdos_104_R1
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card

-- Reduction Erdos104.erdos_104.R1.H1.R1 of step H1 of reduction R1 of Erdos Problem 104
-- Credit: @MBimrose
-- Splits "unit circles with exactly three contacts and no diametral pair are o(n^2)" by whether
-- the centre of the circle lies in the convex hull of its three contacts.

/-! The three contacts of a unit circle span a triangle whose circumcentre is the centre of the
circle; with no diametral pair of contacts that triangle is neither right nor degenerate, so the
centre lies either inside it (the contacts surround the centre, H1) or outside it (the contacts
fit in an open semicircle, H2).  The two families are disjoint, their union is the whole family of
R1's H1, and each is a strictly smaller obligation: H1 implies each of them, not conversely. -/

open EuclideanGeometry Finset
open scoped EuclideanGeometry

namespace OMA.R_Erdos104_erdos_104_R1_H1_R1

-- The centre of the circle lies in the convex hull of its contacts.
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : Finset ℝ², P.card ≤ n →
    (({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard = 3 ∧
        s.center ∈ convexHull ℝ {p ∈ (P : Set ℝ²) | p ∈ s} ∧
        ¬ ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}.ncard : ℝ) ≤ ε * (n : ℝ) ^ 2)

-- The centre of the circle does not lie in the convex hull of its contacts.
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : Finset ℝ², P.card ≤ n →
    (({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard = 3 ∧
        s.center ∉ convexHull ℝ {p ∈ (P : Set ℝ²) | p ∈ s} ∧
        ¬ ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}.ncard : ℝ) ≤ ε * (n : ℝ) ^ 2)

-- At most two unit circles pass through two distinct points.
private theorem pair_circles_finite {a b : ℝ²} (hab : a ≠ b) :
    ({s : Sphere ℝ² | s.radius = 1 ∧ a ∈ s ∧ b ∈ s} : Set (Sphere ℝ²)).Finite := by
  classical
  set Q : Set (Sphere ℝ²) := {s : Sphere ℝ² | s.radius = 1 ∧ a ∈ s ∧ b ∈ s} with hQ
  let A : Sphere ℝ² := ⟨a, 1⟩
  let B : Sphere ℝ² := ⟨b, 1⟩
  have hAB : A ≠ B := fun h => hab (congrArg Sphere.center h)
  have ha (s : Sphere ℝ²) (hs : s ∈ Q) : s.center ∈ A := by
    obtain ⟨hsr, has, -⟩ := hs
    exact mem_sphere'.mpr ((mem_sphere.mp has).trans hsr)
  have hb (s : Sphere ℝ²) (hs : s ∈ Q) : s.center ∈ B := by
    obtain ⟨hsr, -, hbs⟩ := hs
    exact mem_sphere'.mpr ((mem_sphere.mp hbs).trans hsr)
  have byCentre (s t : Sphere ℝ²) (hs : s ∈ Q) (ht : t ∈ Q) (h : s.center = t.center) : s = t := by
    obtain ⟨hsr, -, -⟩ := hs
    obtain ⟨htr, -, -⟩ := ht
    rw [← Sphere.mk_center_radius s, ← Sphere.mk_center_radius t, h, hsr, htr]
  by_cases hsub : Q.Subsingleton
  · exact hsub.finite
  obtain ⟨s, hs, t, ht, hst⟩ := Set.not_subsingleton_iff.mp hsub
  have hstc : s.center ≠ t.center := fun h => hst (byCentre s t hs ht h)
  have hsubset : Q ⊆ ({s, t} : Set (Sphere ℝ²)) := by
    intro u hu
    rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := ℝ²) (by simp) hAB hstc (ha s hs) (ha t ht) (ha u hu) (hb s hs) (hb t ht) (hb u hu)
      with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl (byCentre u s hu hs h))
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (byCentre u t hu ht h)))
  exact (Set.toFinite ({s, t} : Set (Sphere ℝ²))).subset hsubset

set_option maxHeartbeats 2000000 in
theorem main : H1 → H2 → OMA.R_Erdos104_erdos_104_R1.H1 := by
  intro h1 h2 ε hε
  obtain ⟨N1, hN1⟩ := h1 (ε / 2) (by positivity)
  obtain ⟨N2, hN2⟩ := h2 (ε / 2) (by positivity)
  refine ⟨max N1 N2, ?_⟩
  intro n hn P hP
  classical
  set A : Set (Sphere ℝ²) := {s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard = 3 ∧
      s.center ∈ convexHull ℝ {p ∈ (P : Set ℝ²) | p ∈ s} ∧
      ¬ ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s} with hAdef
  set B : Set (Sphere ℝ²) := {s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard = 3 ∧
      s.center ∉ convexHull ℝ {p ∈ (P : Set ℝ²) | p ∈ s} ∧
      ¬ ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s} with hBdef
  have hA : (A.ncard : ℝ) ≤ (ε / 2) * (n : ℝ) ^ 2 := by
    have := hN1 n ((le_max_left N1 N2).trans hn) P hP
    rwa [hAdef]
  have hB : (B.ncard : ℝ) ≤ (ε / 2) * (n : ℝ) ^ 2 := by
    have := hN2 n ((le_max_right N1 N2).trans hn) P hP
    rwa [hBdef]
  -- the family of R1's H1 is contained in the union of the two cases
  have hsub : ({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard = 3} \
      {s : Sphere ℝ² | s.radius = 1 ∧
        ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}) ⊆ A ∪ B := by
    rintro s ⟨⟨hsr, hs3⟩, hdiam⟩
    have hnd : ¬ ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s :=
      fun hex => hdiam ⟨hsr, hex⟩
    by_cases hc : s.center ∈ convexHull ℝ {p ∈ (P : Set ℝ²) | p ∈ s}
    · refine Or.inl ?_
      rw [hAdef]
      exact ⟨hsr, hs3, hc, hnd⟩
    · refine Or.inr ?_
      rw [hBdef]
      exact ⟨hsr, hs3, hc, hnd⟩
  -- every unit circle with three distinct contacts is a unit circle through a pair of them
  have hthreefin : ({s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard} :
      Set (Sphere ℝ²)).Finite := by
    classical
    let block (p : ℝ² × ℝ²) : Finset (Sphere ℝ²) :=
      if h : p.1 ≠ p.2 then (pair_circles_finite h).toFinset else ∅
    refine (P.offDiag.biUnion block).finite_toSet.subset ?_
    intro s hs
    obtain ⟨hsr, hs3⟩ := hs
    have hPfin : {p ∈ (P : Set ℝ²) | p ∈ s}.Finite := P.finite_toSet.subset fun x hx => hx.1
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (Set.one_lt_ncard hPfin).mp (by omega : 1 < {p ∈ (P : Set ℝ²) | p ∈ s}.ncard)
    refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha.1, hb.1, hab⟩, ?_⟩
    have hpair : s ∈ ({s : Sphere ℝ² | s.radius = 1 ∧ a ∈ s ∧ b ∈ s} : Set (Sphere ℝ²)) :=
      ⟨hsr, ha.2, hb.2⟩
    simpa only [block, dif_pos hab, Set.Finite.mem_toFinset] using hpair
  have hfinAB : (A ∪ B).Finite := by
    refine hthreefin.subset ?_
    rintro s (hs | hs)
    · rw [hAdef] at hs
      exact ⟨hs.1, by have := hs.2.1; omega⟩
    · rw [hBdef] at hs
      exact ⟨hs.1, by have := hs.2.1; omega⟩
  calc (({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard = 3} \
      {s : Sphere ℝ² | s.radius = 1 ∧
        ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}).ncard : ℝ)
      ≤ ((A ∪ B).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfinAB
    _ ≤ (A.ncard : ℝ) + (B.ncard : ℝ) := by
        exact_mod_cast Set.ncard_union_le A B
    _ ≤ ε * (n : ℝ) ^ 2 := by linarith

end OMA.R_Erdos104_erdos_104_R1_H1_R1
