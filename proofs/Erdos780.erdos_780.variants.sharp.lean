import FormalConjectures.ErdosProblems.«780»

-- Problem: Erdős Problem 780 — sharp
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/780.lean:61 (declaration Erdos780.erdos_780.variants.sharp)
-- Credit: @snoozingnewt (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Construction: vertices below k * r - 1 form the big block X (colour 0); the remaining
-- (t - 1) * (k - 1) vertices are cut into t - 1 consecutive blocks of size k - 1, the block
-- with index q getting colour q + 1. An edge gets the colour of its largest vertex.
-- Colour 0 edges lie inside X, and k disjoint ones would need k * r > k * r - 1 vertices.
-- An edge of colour q + 1 has its largest vertex in block q, and k disjoint such edges
-- would give k distinct vertices in a block of size k - 1.

namespace OMA.E780

-- The colour of a single vertex.
def g (k r t : ℕ) (ht : 1 ≤ t) (v : Fin (k * r - 1 + (t - 1) * (k - 1))) : Fin t :=
  if h : (v : ℕ) < k * r - 1 then ⟨0, ht⟩
  else ⟨((v : ℕ) - (k * r - 1)) / (k - 1) + 1, by
    have hv := v.isLt
    rcases Nat.eq_zero_or_pos (k - 1) with h0 | h0
    · have h1 : (t - 1) * (k - 1) = 0 := by rw [h0, Nat.mul_zero]
      omega
    · have : ((v : ℕ) - (k * r - 1)) / (k - 1) < t - 1 := by
        rw [Nat.div_lt_iff_lt_mul h0]
        omega
      omega⟩

theorem g_val (k r t : ℕ) (ht : 1 ≤ t) (v : Fin (k * r - 1 + (t - 1) * (k - 1))) :
    ((g k r t ht v : Fin t) : ℕ) =
      if (v : ℕ) < k * r - 1 then 0 else ((v : ℕ) - (k * r - 1)) / (k - 1) + 1 := by
  unfold g
  split_ifs <;> rfl

end OMA.E780

theorem OMA.solution : type_of% @Erdos780.erdos_780.variants.sharp := by
  intro k r t hk hr ht
  have hne : ∀ e : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r},
      e.1.Nonempty := by
    intro e
    apply Finset.card_pos.mp
    have h : e.1.card = r := e.2
    omega
  refine ⟨fun e => OMA.E780.g k r t ht (e.1.max' (hne e)), ?_⟩
  rintro ⟨i, e, hc, hdisj⟩
  obtain ⟨x, hxmem, hxle, hxg⟩ : ∃ x : Fin k → Fin (k * r - 1 + (t - 1) * (k - 1)),
      (∀ j, x j ∈ (e j).1) ∧ (∀ j, ∀ v ∈ (e j).1, v ≤ x j) ∧
      ∀ j, ((OMA.E780.g k r t ht (x j) : Fin t) : ℕ) = (i : ℕ) :=
    ⟨fun j => (e j).1.max' (hne (e j)), fun j => Finset.max'_mem _ _,
      fun j v hv => Finset.le_max' _ v hv, fun j => congrArg Fin.val (hc j)⟩
  simp only [OMA.E780.g_val] at hxg
  by_cases hi : (i : ℕ) = 0
  · -- all edges lie in the big block, which is too small for k disjoint edges
    have hsmall : ∀ j, ∀ v ∈ (e j).1, (v : ℕ) < k * r - 1 := by
      intro j v hv
      have h1 := hxg j
      have h2 : (v : ℕ) ≤ (x j : ℕ) := Fin.le_iff_val_le_val.mp (hxle j v hv)
      by_cases h3 : (x j : ℕ) < k * r - 1
      · omega
      · rw [if_neg h3] at h1
        generalize ((x j : ℕ) - (k * r - 1)) / (k - 1) = q at h1
        omega
    have hce : ∀ j ∈ (Finset.univ : Finset (Fin k)), (e j).1.card = r := fun j _ => (e j).2
    have hcard : (Finset.univ.biUnion fun j => (e j).1).card = k * r := by
      rw [Finset.card_biUnion (by intro a _ b _ hab; exact hdisj hab), Finset.sum_const_nat hce]
      simp
    have hle : (Finset.univ.biUnion fun j => (e j).1).card ≤ (Finset.range (k * r - 1)).card := by
      refine Finset.card_le_card_of_injOn
        (fun v : Fin (k * r - 1 + (t - 1) * (k - 1)) => (v : ℕ)) ?_ ?_
      · intro v hv
        simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
          Set.mem_iUnion, Finset.mem_coe] at hv
        obtain ⟨j, hj⟩ := hv
        simpa using hsmall j v hj
      · intro a _ b _ hab
        exact Fin.ext hab
    rw [hcard, Finset.card_range] at hle
    have : 0 < k * r := Nat.mul_pos (by omega) (by omega)
    omega
  · -- every edge has its largest vertex in the same small block of size k - 1
    have hbig : ∀ j, ¬ (x j : ℕ) < k * r - 1 ∧
        ((x j : ℕ) - (k * r - 1)) / (k - 1) + 1 = (i : ℕ) := by
      intro j
      have h1 := hxg j
      by_cases h3 : (x j : ℕ) < k * r - 1
      · rw [if_pos h3] at h1
        omega
      · rw [if_neg h3] at h1
        exact ⟨h3, h1⟩
    have j0 : Fin k := ⟨0, by omega⟩
    have hk1 : 0 < k - 1 := by
      rcases Nat.eq_zero_or_pos (k - 1) with h0 | h0
      · have hv := (x j0).isLt
        have h1 : (t - 1) * (k - 1) = 0 := by rw [h0, Nat.mul_zero]
        have := (hbig j0).1
        omega
      · exact h0
    obtain ⟨a, b, hab, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun j => (⟨((x j : ℕ) - (k * r - 1)) % (k - 1), Nat.mod_lt _ hk1⟩ : Fin (k - 1)))
      (by simp only [Fintype.card_fin]; omega)
    have hmod : ((x a : ℕ) - (k * r - 1)) % (k - 1) = ((x b : ℕ) - (k * r - 1)) % (k - 1) :=
      congrArg Fin.val hφ
    have hq : ((x a : ℕ) - (k * r - 1)) / (k - 1) = ((x b : ℕ) - (k * r - 1)) / (k - 1) := by
      have ha := (hbig a).2
      have hb := (hbig b).2
      generalize ((x a : ℕ) - (k * r - 1)) / (k - 1) = qa at ha ⊢
      generalize ((x b : ℕ) - (k * r - 1)) / (k - 1) = qb at hb ⊢
      omega
    have ha := Nat.div_add_mod ((x a : ℕ) - (k * r - 1)) (k - 1)
    have hb := Nat.div_add_mod ((x b : ℕ) - (k * r - 1)) (k - 1)
    rw [hq] at ha
    have hxab : x a = x b := by
      apply Fin.ext
      have := (hbig a).1
      have := (hbig b).1
      generalize (k - 1) * (((x b : ℕ) - (k * r - 1)) / (k - 1)) = P at ha hb
      generalize ((x a : ℕ) - (k * r - 1)) % (k - 1) = ra at ha hmod
      generalize ((x b : ℕ) - (k * r - 1)) % (k - 1) = rb at hb hmod
      omega
    exact Finset.disjoint_left.mp (hdisj hab) (hxmem a) (by rw [hxab]; exact hxmem b)
