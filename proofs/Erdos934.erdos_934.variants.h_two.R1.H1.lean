import OMAReductions.R_Erdos934_erdos_934_variants_h_two_R1

/-! # The blow-up of the 5-cycle

On `Fin (5 * r)` join `u` and `v` when their residues modulo `5` are consecutive. Each residue
class has `r` elements, so every degree is at most `2 * r`, there are `5 * r ^ 2` edges, and
since the `5`-cycle has no induced `2K₂`, any two edges have adjacent endpoints.
-/

namespace OMA934

/-- The blow-up of the `5`-cycle with `r` vertices in each class. -/
def G5 (r : ℕ) : SimpleGraph (Fin (5 * r)) :=
  SimpleGraph.fromRel (fun u v : Fin (5 * r) => (u.val + 1) % 5 = v.val % 5)

lemma adj_iff (r : ℕ) (u v : Fin (5 * r)) :
    (G5 r).Adj u v ↔ ((u.val + 1) % 5 = v.val % 5 ∨ (v.val + 1) % 5 = u.val % 5) := by
  unfold G5
  rw [SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    omega

lemma class_ncard_le (r c : ℕ) : {w : Fin (5 * r) | w.val % 5 = c}.ncard ≤ r := by
  have hlt : ∀ w : Fin (5 * r), w.val / 5 < r := by
    intro w
    have := w.isLt
    omega
  have h := Set.ncard_le_ncard_of_injOn (s := {w : Fin (5 * r) | w.val % 5 = c})
    (t := (Set.univ : Set (Fin r))) (fun w => (⟨w.val / 5, hlt w⟩ : Fin r))
    (fun _ _ => Set.mem_univ _)
    (by
      intro x hx y hy hxy
      simp only [Set.mem_setOf_eq] at hx hy
      have h1 : x.val / 5 = y.val / 5 := congrArg Fin.val hxy
      apply Fin.ext
      omega)
    (Set.toFinite _)
  simpa using h

lemma degree_le (r : ℕ) (v : Fin (5 * r)) : ((G5 r).neighborSet v).ncard ≤ r + r := by
  have hsub : (G5 r).neighborSet v ⊆
      {w : Fin (5 * r) | w.val % 5 = (v.val + 1) % 5} ∪
        {w : Fin (5 * r) | w.val % 5 = (v.val + 4) % 5} := by
    intro w hw
    have hw' : (G5 r).Adj v w := hw
    rw [adj_iff] at hw'
    rcases hw' with h | h
    · left
      exact h.symm
    · right
      show w.val % 5 = (v.val + 4) % 5
      omega
  calc ((G5 r).neighborSet v).ncard
      ≤ ({w : Fin (5 * r) | w.val % 5 = (v.val + 1) % 5} ∪
        {w : Fin (5 * r) | w.val % 5 = (v.val + 4) % 5}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ {w : Fin (5 * r) | w.val % 5 = (v.val + 1) % 5}.ncard +
        {w : Fin (5 * r) | w.val % 5 = (v.val + 4) % 5}.ncard := Set.ncard_union_le _ _
    _ ≤ r + r := Nat.add_le_add (class_ncard_le r _) (class_ncard_le r _)

lemma edges_ge (r : ℕ) : 5 * (r * r) ≤ (G5 r).edgeSet.ncard := by
  have hb1 : ∀ x : Fin 5 × Fin r × Fin r, 5 * x.2.1.val + x.1.val < 5 * r := by
    intro x
    have h1 := x.2.1.isLt
    have h2 := x.1.isLt
    omega
  have hb2 : ∀ x : Fin 5 × Fin r × Fin r, 5 * x.2.2.val + (x.1.val + 1) % 5 < 5 * r := by
    intro x
    have h1 := x.2.2.isLt
    have h2 := x.1.isLt
    omega
  let f : Fin 5 × Fin r × Fin r → Sym2 (Fin (5 * r)) := fun x =>
    s(⟨5 * x.2.1.val + x.1.val, hb1 x⟩, ⟨5 * x.2.2.val + (x.1.val + 1) % 5, hb2 x⟩)
  have hinj : Function.Injective f := by
    rintro ⟨i, a, b⟩ ⟨j, c, d⟩ h
    have hi := i.isLt
    have hj := j.isLt
    simp only [f, Sym2.eq_iff, Fin.mk.injEq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hij : i.val = j.val := by omega
      have hac : a.val = c.val := by omega
      have hbd : b.val = d.val := by omega
      simp only [Prod.mk.injEq]
      exact ⟨Fin.ext hij, Fin.ext hac, Fin.ext hbd⟩
    · exfalso
      omega
  have hsub : f '' Set.univ ⊆ (G5 r).edgeSet := by
    rintro _ ⟨x, -, rfl⟩
    show s(_, _) ∈ (G5 r).edgeSet
    rw [SimpleGraph.mem_edgeSet, adj_iff]
    left
    show (5 * x.2.1.val + x.1.val + 1) % 5 = (5 * x.2.2.val + (x.1.val + 1) % 5) % 5
    omega
  have hcard : (f '' Set.univ).ncard = 5 * (r * r) := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    simp
  rw [← hcard]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

lemma no_far_edges (r : ℕ) : ¬ Erdos934.HasFarEdges (G5 r) 2 := by
  rintro ⟨u, v, w, x, huv, hwx, hfar⟩
  rw [adj_iff] at huv hwx
  have key : (G5 r).Adj u w ∨ (G5 r).Adj u x ∨ (G5 r).Adj v w ∨ (G5 r).Adj v x := by
    simp only [adj_iff]
    omega
  have hcontra : ∀ a b : Fin (5 * r), (G5 r).Adj a b → ((2 : ℕ) : ℕ∞) ≤ (G5 r).edist a b →
      False := by
    intro a b hab hle
    rw [SimpleGraph.edist_eq_one_iff_adj.2 hab] at hle
    have : (2 : ℕ) ≤ 1 := by exact_mod_cast hle
    omega
  rcases key with h | h | h | h
  · exact hcontra u w h (hfar u (by simp) w (by simp))
  · exact hcontra u x h (hfar u (by simp) x (by simp))
  · exact hcontra v w h (hfar v (by simp) w (by simp))
  · exact hcontra v x h (hfar v (by simp) x (by simp))

end OMA934

theorem OMA.solution : OMA.R_Erdos934_erdos_934_variants_h_two_R1.H1 := by
  intro d hd
  obtain ⟨r, rfl⟩ := hd
  refine ⟨5 * r, OMA934.G5 r, OMA934.degree_le r, ?_, OMA934.no_far_edges r⟩
  have h : 5 * (r + r) ^ 2 = 4 * (5 * (r * r)) := by ring
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  exact OMA934.edges_ge r
