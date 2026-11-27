import FormalConjectures.ErdosProblems.«1010»
open SimpleGraph Finset

namespace OMAE1010

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- pairs at a fixed vertex -/
theorem pairs_le (v : Fin n) (S : Finset (Fin n × Fin n))
    (hS : ∀ p ∈ S, G.Adj v p.1 ∧ G.Adj v p.2 ∧ G.Adj p.1 p.2)
    (hanti : ∀ y z, (y, z) ∈ S → (z, y) ∉ S) :
    S.card ≤ (G.cliqueFinset 3).card := by
  refine card_le_card_of_injOn (fun p => ({v, p.1, p.2} : Finset (Fin n))) ?_ ?_
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hS p hp
    simp only [coe_cliqueFinset, Set.mem_setOf_eq]
    exact (is3Clique_triple_iff).2 ⟨h1, h2, h3⟩
  · rintro ⟨y, z⟩ hp ⟨y', z'⟩ hp' heq
    simp only at heq
    obtain ⟨a1, a2, a3⟩ := hS _ hp
    obtain ⟨b1, b2, b3⟩ := hS _ hp'
    simp only at a1 a2 a3 b1 b2 b3
    have hy : y ∈ ({v, y', z'} : Finset (Fin n)) := heq ▸ (by simp)
    have hz : z ∈ ({v, y', z'} : Finset (Fin n)) := heq ▸ (by simp)
    have hy' : y' ∈ ({v, y, z} : Finset (Fin n)) := heq.symm ▸ (by simp)
    simp only [mem_insert, mem_singleton] at hy hz hy'
    have nvy : y ≠ v := fun h => a1.ne h.symm
    have nvz : z ≠ v := fun h => a2.ne h.symm
    have nvy' : y' ≠ v := fun h => b1.ne h.symm
    have nyz : y ≠ z := a3.ne
    have nyz' : y' ≠ z' := b3.ne
    rcases hy with h | h | h
    · exact absurd h nvy
    · subst h
      rcases hz with h | h | h
      · exact absurd h nvz
      · exact absurd h.symm nyz
      · subst h; rfl
    · subst h
      rcases hz with h | h | h
      · exact absurd h nvz
      · subst h; exact absurd hp' (hanti _ _ hp)
      · exact absurd h.symm nyz

/-- mixed triangles -/
theorem triples_le (σ : Fin n → Bool) (S : Finset (Fin n × Fin n × Fin n))
    (hS : ∀ p ∈ S, G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2 ∧ p.1 < p.2.1 ∧
      σ p.1 = σ p.2.1 ∧ σ p.2.2 ≠ σ p.1) :
    S.card ≤ (G.cliqueFinset 3).card := by
  refine card_le_card_of_injOn (fun p => ({p.1, p.2.1, p.2.2} : Finset (Fin n))) ?_ ?_
  · intro p hp
    obtain ⟨h1, h2, h3, -⟩ := hS p hp
    simp only [coe_cliqueFinset, Set.mem_setOf_eq]
    exact (is3Clique_triple_iff).2 ⟨h1, h2, h3⟩
  · rintro ⟨x, y, z⟩ hp ⟨x', y', z'⟩ hp' heq
    simp only at heq
    obtain ⟨-, -, -, lt, s1, s2⟩ := hS _ hp
    obtain ⟨-, -, -, lt', s1', s2'⟩ := hS _ hp'
    simp only at lt s1 s2 lt' s1' s2'
    have hx : x ∈ ({x', y', z'} : Finset (Fin n)) := heq ▸ (by simp)
    have hy : y ∈ ({x', y', z'} : Finset (Fin n)) := heq ▸ (by simp)
    have hz : z ∈ ({x', y', z'} : Finset (Fin n)) := heq ▸ (by simp)
    have hx' : x' ∈ ({x, y, z} : Finset (Fin n)) := heq.symm ▸ (by simp)
    have hy' : y' ∈ ({x, y, z} : Finset (Fin n)) := heq.symm ▸ (by simp)
    simp only [mem_insert, mem_singleton] at hx hy hz hx' hy'
    have hxy : x ≠ y := ne_of_lt lt
    have hxy' : x' ≠ y' := ne_of_lt lt'
    have hzz : z = z' := by
      rcases hz with h | h | h
      · subst h
        rcases hx with h | h | h
        · subst h; exact absurd s1' (by simp_all)
        · subst h; exact absurd s1' (by simp_all)
        · rcases hy with h' | h' | h'
          · subst h'; exact absurd s1' (by simp_all)
          · subst h'; exact absurd s1' (by simp_all)
          · exact absurd (h.trans h'.symm) hxy
      · subst h
        rcases hx with h | h | h
        · subst h; exact absurd s1' (by simp_all)
        · subst h; exact absurd s1' (by simp_all)
        · rcases hy with h' | h' | h'
          · subst h'; exact absurd s1' (by simp_all)
          · subst h'; exact absurd s1' (by simp_all)
          · exact absurd (h.trans h'.symm) hxy
      · exact h
    subst hzz
    have nxz : x ≠ z := fun h => s2 (h ▸ rfl)
    have nyz : y ≠ z := fun h => s2 (by rw [← h, s1])
    rcases hx with h | h | h
    · subst h
      rcases hy with h | h | h
      · exact absurd h.symm hxy
      · subst h; rfl
      · exact absurd h nyz
    · subst h
      rcases hy with h | h | h
      · subst h; exact absurd (lt_trans lt lt') (lt_irrefl _)
      · exact absurd h.symm hxy
      · exact absurd h nyz
    · exact absurd h nxz


/-- symmetric sums -/
theorem sum_sym (f : Fin n → Fin n → ℤ) (hs : ∀ x y, f x y = f y x) (hd : ∀ x, f x x = 0) :
    ∑ x, ∑ y, f x y = 2 * ∑ x, ∑ y, if x < y then f x y else 0 := by
  have h1 : ∀ x y, f x y = (if x < y then f x y else 0) + (if y < x then f x y else 0) := by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, not_lt.2 h.le]
    · subst h; simp [hd]
    · simp [h, not_lt.2 h.le]
  have h2 : ∑ x, ∑ y, (if y < x then f x y else 0) = ∑ x, ∑ y, (if x < y then f x y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hs]
  calc ∑ x, ∑ y, f x y
      = ∑ x, ∑ y, ((if x < y then f x y else 0) + (if y < x then f x y else 0)) := by
        simp_rw [← h1]
    _ = _ := by simp_rw [Finset.sum_add_distrib]; rw [h2]; ring

/-- degree as a sum -/
theorem degree_eq_sum (x : Fin n) : (G.degree x : ℤ) = ∑ y, if G.Adj x y then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]
  push_cast; rfl

theorem two_e (e : ℕ) (he : G.edgeFinset.card = e) :
    ∑ x, ∑ y, (if G.Adj x y then (1:ℤ) else 0) = 2 * e := by
  rw [← he]
  have := G.sum_degrees_eq_twice_card_edges
  have h2 : ((∑ v, G.degree v : ℕ) : ℤ) = ((2 * G.edgeFinset.card : ℕ) : ℤ) := by rw [this]
  push_cast at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun x _ => (degree_eq_sum G x).symm


noncomputable section
variable (σ : Fin n → Bool)

def dOwn (x : Fin n) : ℤ := ∑ y, if G.Adj x y ∧ σ x = σ y then 1 else 0
def dOth (x : Fin n) : ℤ := ∑ y, if G.Adj x y ∧ σ x ≠ σ y then 1 else 0
def oth (x : Fin n) : ℤ := ∑ y, if σ x ≠ σ y then 1 else 0
def mu (x : Fin n) : ℤ := oth σ x - dOth G σ x
def II : ℤ := ∑ x, dOwn G σ x
def CC : ℤ := ∑ x, dOth G σ x

theorem II_add_CC (e : ℕ) (he : G.edgeFinset.card = e) : II G σ + CC G σ = 2 * e := by
  rw [← two_e G e he, II, CC, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dOwn, dOth, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : G.Adj x y <;> by_cases h' : σ x = σ y <;> simp [h, h']

theorem mu_nonneg (x : Fin n) : 0 ≤ mu G σ x := by
  rw [mu, oth, dOth, sub_nonneg]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases h : G.Adj x y <;> by_cases h' : σ x = σ y <;> simp [h, h']

theorem triple_card_eq (P : Fin n → Fin n → Fin n → Prop) [∀ x y z, Decidable (P x y z)] :
    (((univ : Finset (Fin n × Fin n × Fin n)).filter (fun p => P p.1 p.2.1 p.2.2)).card : ℤ) =
      ∑ x, ∑ y, ∑ z, if P x y z then 1 else 0 := by
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]

theorem caseS (α : ℤ) (hS : ∀ x, 2 * dOwn G σ x ≤ α) (hα : ∀ x, α ≤ oth σ x) :
    α * (II G σ - ∑ x, mu G σ x) ≤ 2 * (G.cliqueFinset 3).card := by
  set g : Fin n → Fin n → Fin n → ℤ := fun x y z =>
    if (G.Adj x y ∧ σ x = σ y) ∧ (σ z ≠ σ x ∧ G.Adj x z ∧ G.Adj y z) then 1 else 0 with hg
  -- upper bound
  have hup : ∑ x, ∑ y, ∑ z, g x y z ≤ 2 * (G.cliqueFinset 3).card := by
    rw [sum_sym (fun x y => ∑ z, g x y z)]
    · have : ∑ x, ∑ y, (if x < y then ∑ z, g x y z else 0) =
          (((univ : Finset (Fin n × Fin n × Fin n)).filter (fun p =>
            p.1 < p.2.1 ∧ ((G.Adj p.1 p.2.1 ∧ σ p.1 = σ p.2.1) ∧
              (σ p.2.2 ≠ σ p.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2)))).card : ℤ) := by
        rw [triple_card_eq (fun x y z => x < y ∧ ((G.Adj x y ∧ σ x = σ y) ∧
              (σ z ≠ σ x ∧ G.Adj x z ∧ G.Adj y z)))]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        by_cases h : x < y
        · simp only [h, if_true, true_and, hg]
        · simp [h]
      rw [this]
      have := triples_le G σ ((univ : Finset (Fin n × Fin n × Fin n)).filter (fun p =>
            p.1 < p.2.1 ∧ ((G.Adj p.1 p.2.1 ∧ σ p.1 = σ p.2.1) ∧
              (σ p.2.2 ≠ σ p.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2)))) (by
        intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp
        exact ⟨hp.2.1.1, hp.2.2.2.1, hp.2.2.2.2, hp.1, hp.2.1.2, hp.2.2.1⟩)
      omega
    · intro x y
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [hg]
      by_cases h1 : G.Adj x y
      · have h1' : G.Adj y x := h1.symm
        by_cases h2 : σ x = σ y
        · simp only [h1, h1', h2, true_and]
          by_cases h3 : σ z ≠ σ y <;> by_cases h4 : G.Adj x z <;> by_cases h5 : G.Adj y z <;>
            simp [h3, h4, h5]
        · have h2' : ¬ σ y = σ x := fun h => h2 h.symm
          simp [h2, h2']
      · have h1' : ¬ G.Adj y x := fun h => h1 h.symm
        simp [h1, h1']
    · intro x; simp [hg]
  -- lower bound
  have hin : ∀ x y, (if G.Adj x y ∧ σ x = σ y then 1 else 0) * (α - mu G σ x - mu G σ y) ≤
      ∑ z, g x y z := by
    intro x y
    by_cases h : G.Adj x y ∧ σ x = σ y
    · rw [if_pos h, one_mul]
      have hz : ∀ z, (if G.Adj x z ∧ σ x ≠ σ z then (1:ℤ) else 0) +
          (if G.Adj y z ∧ σ y ≠ σ z then 1 else 0) - (if σ x ≠ σ z then 1 else 0) ≤ g x y z := by
        intro z
        simp only [hg, h, true_and]
        rw [← h.2]
        by_cases h3 : σ x = σ z <;> by_cases h4 : G.Adj x z <;> by_cases h5 : G.Adj y z <;>
          simp [h3, h4, h5, Ne.symm, eq_comm]
      have := Finset.sum_le_sum fun z (_ : z ∈ univ) => hz z
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at this
      have ho : oth σ y = oth σ x := by rw [oth, oth, h.2]
      have := hα x
      simp only [mu, dOth, oth] at *
      linarith
    · rw [if_neg h, zero_mul]
      exact Finset.sum_nonneg fun z _ => by simp only [hg]; split_ifs <;> norm_num
  have hlow : ∑ x, ∑ y, (if G.Adj x y ∧ σ x = σ y then 1 else 0) * (α - mu G σ x - mu G σ y) ≤
      ∑ x, ∑ y, ∑ z, g x y z :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hin x y
  have hexp : ∑ x, ∑ y, (if G.Adj x y ∧ σ x = σ y then (1:ℤ) else 0) * (α - mu G σ x - mu G σ y) =
      α * II G σ - ∑ x, dOwn G σ x * mu G σ x - ∑ x, dOwn G σ x * mu G σ x := by
    have hsw : ∑ x, ∑ y, (if G.Adj x y ∧ σ x = σ y then (1:ℤ) else 0) * mu G σ y =
        ∑ x, dOwn G σ x * mu G σ x := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [dOwn, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      have e1 : (G.Adj x y ∧ σ x = σ y) ↔ (G.Adj y x ∧ σ y = σ x) :=
        ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
      simp only [e1]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsw, II, Finset.mul_sum]
    congr 1
    congr 1
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [dOwn, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [dOwn, Finset.sum_mul]
  have hfin : 2 * ∑ x, dOwn G σ x * mu G σ x ≤ α * ∑ x, mu G σ x := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have := mu_nonneg G σ x
    have := hS x
    nlinarith
  linarith


theorem sum_mu_eq : ∑ x, mu G σ x = ∑ x, ∑ y, if σ x ≠ σ y ∧ ¬ G.Adj x y then (1:ℤ) else 0 := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mu, oth, dOth, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : G.Adj x y <;> by_cases h' : σ x = σ y <;> simp [h, h']

theorem caseN (x : Fin n) :
    2 * (dOwn G σ x * dOth G σ x) - ∑ y, mu G σ y ≤ 2 * (G.cliqueFinset 3).card := by
  set S := (univ : Finset (Fin n × Fin n)).filter (fun p =>
    (G.Adj x p.1 ∧ σ x = σ p.1) ∧ (G.Adj x p.2 ∧ σ x ≠ σ p.2) ∧ G.Adj p.1 p.2) with hSdef
  have hS : S.card ≤ (G.cliqueFinset 3).card := by
    refine pairs_le G x S ?_ ?_
    · intro p hp
      simp only [hSdef, mem_filter, mem_univ, true_and] at hp
      exact ⟨hp.1.1, hp.2.1.1, hp.2.2⟩
    · intro y z hyz hzy
      simp only [hSdef, mem_filter, mem_univ, true_and] at hyz hzy
      exact hzy.2.1.2 hyz.1.2
  have hcard : (S.card : ℤ) = ∑ y, ∑ z, if (G.Adj x y ∧ σ x = σ y) ∧ (G.Adj x z ∧ σ x ≠ σ z) ∧
      G.Adj y z then 1 else 0 := by
    rw [hSdef, Finset.card_filter]; push_cast; rw [Fintype.sum_prod_type]
  set Mx : ℤ := ∑ y, ∑ z, if σ y = σ x ∧ σ z ≠ σ x ∧ ¬ G.Adj y z then 1 else 0 with hMx
  have hpt : ∀ y z, (if G.Adj x y ∧ σ x = σ y then (1:ℤ) else 0) *
      (if G.Adj x z ∧ σ x ≠ σ z then 1 else 0) -
      (if σ y = σ x ∧ σ z ≠ σ x ∧ ¬ G.Adj y z then 1 else 0) ≤
      if (G.Adj x y ∧ σ x = σ y) ∧ (G.Adj x z ∧ σ x ≠ σ z) ∧ G.Adj y z then 1 else 0 := by
    intro y z
    generalize σ x = a; generalize σ y = b; generalize σ z = c
    by_cases h1 : G.Adj x y <;> by_cases h3 : G.Adj x z <;> by_cases h5 : G.Adj y z <;>
      cases a <;> cases b <;> cases c <;> simp [h1, h3, h5]
  have h1 : dOwn G σ x * dOth G σ x - Mx ≤ S.card := by
    rw [hcard, dOwn, dOth, Finset.sum_mul_sum, hMx, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun z _ => hpt y z
  have h2 : ∑ y, mu G σ y = 2 * Mx := by
    rw [sum_mu_eq]
    have hsplit : ∀ y z, (if σ y ≠ σ z ∧ ¬ G.Adj y z then (1:ℤ) else 0) =
        (if σ y = σ x ∧ σ z ≠ σ x ∧ ¬ G.Adj y z then 1 else 0) +
        (if σ z = σ x ∧ σ y ≠ σ x ∧ ¬ G.Adj y z then 1 else 0) := by
      intro y z
      generalize σ x = a; generalize σ y = b; generalize σ z = c
      by_cases h : G.Adj y z <;> cases a <;> cases b <;> cases c <;> simp [h]
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [hMx, two_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    by_cases h : G.Adj y z
    · have h' : G.Adj z y := h.symm
      simp [h, h']
    · have h' : ¬ G.Adj z y := fun h' => h h'.symm
      simp only [h, h', not_false_eq_true, and_true]
  linarith

theorem CC_update (x : Fin n) :
    CC G (Function.update σ x (!σ x)) = CC G σ + 2 * (dOwn G σ x - dOth G σ x) := by
  set F : Fin n → ℤ := fun z => (if G.Adj x z ∧ σ x = σ z then 1 else 0) -
      (if G.Adj x z ∧ σ x ≠ σ z then 1 else 0) with hF
  have hpt : ∀ y z, (if G.Adj y z ∧ Function.update σ x (!σ x) y ≠ Function.update σ x (!σ x) z
      then (1:ℤ) else 0) = (if G.Adj y z ∧ σ y ≠ σ z then 1 else 0) +
      (if y = x then F z else 0) + (if z = x then F y else 0) := by
    intro y z
    simp only [hF]
    by_cases hy : y = x <;> by_cases hz : z = x
    · subst hy; subst hz; simp
    · subst hy
      simp only [Function.update_self, Function.update_of_ne hz, if_true, hz, if_false]
      cases h : σ y <;> cases h' : σ z <;> by_cases ha : G.Adj y z <;> simp [ha]
    · subst hz
      simp only [Function.update_self, Function.update_of_ne hy, if_true, hy, if_false]
      by_cases ha : G.Adj y z
      · have hb : G.Adj z y := ha.symm
        cases h : σ y <;> cases h' : σ z <;> simp [ha, hb]
      · have hb : ¬ G.Adj z y := fun h => ha h.symm
        cases h : σ y <;> cases h' : σ z <;> simp [ha, hb]
    · simp [Function.update_of_ne hy, Function.update_of_ne hz, hy, hz]
  have key : CC G (Function.update σ x (!σ x)) = ∑ y, ∑ z, ((if G.Adj y z ∧ σ y ≠ σ z then (1:ℤ)
      else 0) + (if y = x then F z else 0) + (if z = x then F y else 0)) := by
    unfold CC dOth
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => hpt y z
  have hB : ∑ y, ∑ z, (if y = x then F z else 0) = ∑ z, F z := by
    rw [Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hC : ∑ y, ∑ z, (if z = x then F y else 0) = ∑ y, F y := by
    simp [Finset.sum_ite_eq']
  have hFs : ∑ z, F z = dOwn G σ x - dOth G σ x := by
    simp only [hF, Finset.sum_sub_distrib, dOwn, dOth]
  rw [key]
  simp only [Finset.sum_add_distrib]
  rw [hB, hC, hFs]
  unfold CC dOth
  ring

theorem local_opt (hmax : ∀ τ, CC G τ ≤ CC G σ) (x : Fin n) : dOwn G σ x ≤ dOth G σ x := by
  have := hmax (Function.update σ x (!σ x))
  rw [CC_update] at this
  linarith


theorem furedi (v : Fin n) (hv : ∀ w, G.degree w ≤ G.degree v) (e : ℕ)
    (he : G.edgeFinset.card = e) :
    II G (fun y => decide (G.Adj v y)) ≤
      4 * (G.cliqueFinset 3).card + 2 * (((n : ℤ) - G.degree v) * G.degree v) - 2 * e := by
  set Pin : ℤ := ∑ x, ∑ y, if G.Adj x y ∧ G.Adj v x ∧ G.Adj v y then 1 else 0 with hPin
  set Pout : ℤ := ∑ x, ∑ y, if G.Adj x y ∧ ¬ G.Adj v x ∧ ¬ G.Adj v y then 1 else 0 with hPout
  set Pc : ℤ := ∑ x, ∑ y, if G.Adj x y ∧ ¬ G.Adj v x ∧ G.Adj v y then 1 else 0 with hPc
  set Pc' : ℤ := ∑ x, ∑ y, if G.Adj x y ∧ G.Adj v x ∧ ¬ G.Adj v y then 1 else 0 with hPc'
  set Dout : ℤ := ∑ x, ∑ y, if ¬ G.Adj v x ∧ G.Adj x y then 1 else 0 with hDout
  have h1 : II G (fun y => decide (G.Adj v y)) = Pin + Pout := by
    rw [II, hPin, hPout, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [dOwn, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases a : G.Adj x y <;> by_cases b : G.Adj v x <;> by_cases c : G.Adj v y <;> simp [a, b, c]
  have h2 : Pin + Pout + Pc + Pc' = 2 * e := by
    rw [← two_e G e he, hPin, hPout, hPc, hPc', ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases a : G.Adj x y <;> by_cases b : G.Adj v x <;> by_cases c : G.Adj v y <;> simp [a, b, c]
  have h3 : Pc' = Pc := by
    rw [hPc', hPc, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases a : G.Adj x y
    · have a' : G.Adj y x := a.symm
      by_cases b : G.Adj v x <;> by_cases c : G.Adj v y <;> simp [a, a', b, c]
    · have a' : ¬ G.Adj y x := fun h => a h.symm
      simp [a, a']
  have h4 : Dout = Pout + Pc := by
    rw [hDout, hPout, hPc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases a : G.Adj x y <;> by_cases b : G.Adj v x <;> by_cases c : G.Adj v y <;> simp [a, b, c]
  have h5 : Dout ≤ ((n : ℤ) - G.degree v) * G.degree v := by
    have hD : Dout = ∑ x, (if ¬ G.Adj v x then (1:ℤ) else 0) * G.degree x := by
      rw [hDout]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [degree_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases b : G.Adj v x <;> by_cases a : G.Adj x y <;> simp [a, b]
    have hcnt : ∑ x, (if ¬ G.Adj v x then (1:ℤ) else 0) = n - G.degree v := by
      rw [degree_eq_sum]
      have : ∑ x, ((if ¬ G.Adj v x then (1:ℤ) else 0) + (if G.Adj v x then 1 else 0)) = n := by
        have : ∀ x, ((if ¬ G.Adj v x then (1:ℤ) else 0) + (if G.Adj v x then 1 else 0)) = 1 := by
          intro x; by_cases b : G.Adj v x <;> simp [b]
        rw [Finset.sum_congr rfl fun x _ => this x]
        simp
      rw [Finset.sum_add_distrib] at this
      linarith
    rw [hD, ← hcnt, Finset.sum_mul]
    refine Finset.sum_le_sum fun x _ => ?_
    have := hv x
    by_cases b : G.Adj v x
    · simp [b]
    · simp only [b, not_false_eq_true, if_true, one_mul]; exact_mod_cast this
  have h6 : Pin ≤ 2 * (G.cliqueFinset 3).card := by
    rw [hPin, sum_sym (fun x y => if G.Adj x y ∧ G.Adj v x ∧ G.Adj v y then (1:ℤ) else 0)]
    · set S := (univ : Finset (Fin n × Fin n)).filter
        (fun p => p.1 < p.2 ∧ (G.Adj p.1 p.2 ∧ G.Adj v p.1 ∧ G.Adj v p.2)) with hSdef
      have hS : S.card ≤ (G.cliqueFinset 3).card := by
        refine pairs_le G v S ?_ ?_
        · intro p hp
          simp only [hSdef, mem_filter, mem_univ, true_and] at hp
          exact ⟨hp.2.2.1, hp.2.2.2, hp.2.1⟩
        · intro y z hyz hzy
          simp only [hSdef, mem_filter, mem_univ, true_and] at hyz hzy
          exact absurd (lt_trans hyz.1 hzy.1) (lt_irrefl _)
      have hc : (S.card : ℤ) = ∑ x, ∑ y, if x < y then
          (if G.Adj x y ∧ G.Adj v x ∧ G.Adj v y then (1:ℤ) else 0) else 0 := by
        rw [hSdef, Finset.card_filter]; push_cast; rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        by_cases h : x < y <;> simp [h]
      rw [← hc]; omega
    · intro x y
      by_cases a : G.Adj x y
      · have a' : G.Adj y x := a.symm
        simp only [a, a', true_and]
        by_cases b : G.Adj v x <;> by_cases c : G.Adj v y <;> simp [b, c]
      · have a' : ¬ G.Adj y x := fun h => a h.symm
        simp [a, a']
    · intro x; simp
  linarith


theorem oth_facts : ∃ p q : ℤ, 0 ≤ p ∧ 0 ≤ q ∧ p + q = n ∧ (∀ x, oth σ x = p ∨ oth σ x = q) ∧
    ∑ x, oth σ x = 2 * p * q := by
  refine ⟨∑ x, if σ x = true then (1:ℤ) else 0, ∑ x, if σ x = false then (1:ℤ) else 0,
    Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num,
    Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num, ?_, ?_, ?_⟩
  · rw [← Finset.sum_add_distrib]
    have : ∀ x, ((if σ x = true then (1:ℤ) else 0) + if σ x = false then 1 else 0) = 1 := by
      intro x; cases σ x <;> simp
    rw [Finset.sum_congr rfl fun x _ => this x]; simp
  · intro x
    rw [oth]
    cases hx : σ x
    · left; refine Finset.sum_congr rfl fun y _ => ?_; cases σ y <;> simp
    · right; refine Finset.sum_congr rfl fun y _ => ?_; cases σ y <;> simp
  · have : ∀ x, oth σ x = (if σ x = true then (1:ℤ) else 0) * ∑ y, (if σ y = false then 1 else 0) +
        (if σ x = false then (1:ℤ) else 0) * ∑ y, (if σ y = true then 1 else 0) := by
      intro x; rw [oth]; cases σ x <;> simp
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul]
    ring

theorem sq_div4 (n : ℕ) : ((n ^ 2 / 4 : ℕ) : ℤ) = (n / 2 : ℕ) * (n / 2 : ℕ) + (n % 2 : ℕ) * (n / 2 : ℕ) := by
  have h1 := Nat.div_add_mod n 2
  have hq : n ^ 2 / 4 = (n / 2) * (n / 2) + (n % 2) * (n / 2) := by
    apply Nat.div_eq_of_lt_le
    · rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] at h1 ⊢ <;> nlinarith
    · rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] at h1 ⊢ <;> nlinarith
  rw [hq]; push_cast; ring

theorem ar_four_e (n h r t e : ℤ) (hn : n = 2 * h + r) (hr : r = 0 ∨ r = 1)
    (he : e = h * h + r * h + t) : n ^ 2 ≤ 4 * e - 4 * t + 1 := by
  rcases hr with hr | hr <;> subst hr <;> subst hn <;> subst he <;> nlinarith

theorem ar_alpha (n α e T t h : ℤ) (h4 : n ^ 2 ≤ 4 * e - 4 * t + 1) (hpq : e - 2 * T ≤ α * (n - α))
    (hT : T < t * h) (ht : 100 * t < n) (ht1 : 1 ≤ t) (hh : 2 * h ≤ n) (hα0 : 0 ≤ α) :
    n ≤ 4 * α := by
  by_contra hc
  push_neg at hc
  have h1 : 16 * (α * (n - α)) ≤ 3 * n ^ 2 := by nlinarith
  have h2 : 2 * T < t * n := by nlinarith
  have h3 : 100 * (t * n) < n * n := by nlinarith
  nlinarith

theorem ar_caseN (n α d T t h : ℤ) (hd : α < 2 * d) (hα : n ≤ 4 * α) (h6 : 2 * (d * d) ≤ 6 * T)
    (hT : T < t * h) (ht : 100 * t < n) (hh : 2 * h ≤ n) (hα0 : 0 ≤ α) (ht0 : 0 ≤ t) : False := by
  have h1 : n < 8 * d := by linarith
  have hn0 : 0 ≤ n := by linarith
  have h2 : n * n < 64 * (d * d) := by nlinarith
  have h3 : 2 * T < t * n := by nlinarith
  have h4 : 100 * (t * n) < n * n := by nlinarith
  nlinarith

theorem ar_caseS (n h r t e α T : ℤ) (hn : n = 2 * h + r) (hr : r = 0 ∨ r = 1)
    (he : e = h * h + r * h + t) (hαn : 2 * α ≤ n) (hαt : t ≤ α) (hα0 : 0 ≤ α)
    (key : α * (e - α * (n - α)) ≤ T) (hT : T < t * h) : False := by
  have hk0 : 0 ≤ h - α := by rcases hr with h0 | h0 <;> subst h0 <;> linarith
  have hid : α * (e - α * (n - α)) - t * h = (h - α) * (α * ((h - α) + r) - t) := by
    subst hn; subst he; ring
  have : 0 ≤ (h - α) * (α * ((h - α) + r) - t) := by
    rcases (eq_or_lt_of_le hk0) with h0 | h0
    · rw [← h0]; simp
    · apply mul_nonneg hk0
      have hr0 : 0 ≤ r := by rcases hr with h1 | h1 <;> rw [h1] <;> norm_num
      have : α * 1 ≤ α * (h - α + r) := mul_le_mul_of_nonneg_left (by linarith) hα0
      linarith
  linarith

theorem main (n t : ℕ) (ht : 100 * t < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : G.edgeFinset.card = n ^ 2 / 4 + t) : t * (n / 2) ≤ (G.cliqueFinset 3).card := by
  by_contra hT
  push_neg at hT
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; simp at hT
    · exact h
  have hn : 0 < n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨v, hv⟩ := Finite.exists_max (fun w => G.degree w)
  obtain ⟨σ, hσ⟩ := Finite.exists_max (fun τ : Fin n → Bool => CC G τ)
  have F0 := II_add_CC G σ _ he
  have F0' := II_add_CC G (fun y => decide (G.Adj v y)) _ he
  have F0'' := hσ (fun y => decide (G.Adj v y))
  have F1 := furedi G v hv _ he
  have F2 : 4 * (((n : ℤ) - G.degree v) * G.degree v) ≤ (n : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℤ) - 2 * G.degree v)]
  have F3 : (((n ^ 2 / 4 + t : ℕ)) : ℤ) = (n / 2 : ℕ) * (n / 2 : ℕ) + (n % 2 : ℕ) * (n / 2 : ℕ) + t := by
    rw [Nat.cast_add, sq_div4]
  have hn2 : (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) + ((n % 2 : ℕ) : ℤ) := by omega
  have hr : ((n % 2 : ℕ) : ℤ) = 0 ∨ ((n % 2 : ℕ) : ℤ) = 1 := by omega
  have hT' : ((G.cliqueFinset 3).card : ℤ) < t * ((n / 2 : ℕ) : ℤ) := by exact_mod_cast hT
  have ht' : 100 * (t : ℤ) < n := by exact_mod_cast ht
  have ht1' : (1 : ℤ) ≤ t := by exact_mod_cast ht1
  have hh2 : 2 * ((n / 2 : ℕ) : ℤ) ≤ n := by omega
  generalize ((n ^ 2 / 4 + t : ℕ) : ℤ) = e at F0 F0' F1 F3
  generalize hTc : ((G.cliqueFinset 3).card : ℤ) = T at F1 hT'
  have h4 := ar_four_e _ _ _ _ _ hn2 hr F3
  have hII : II G σ ≤ 4 * T := by linarith
  obtain ⟨p, q, hp0, hq0, hpq, hoth, hsum⟩ := oth_facts σ
  have hmu : ∑ x, mu G σ x = 2 * p * q - CC G σ := by
    simp only [mu, Finset.sum_sub_distrib, hsum, CC]
  have hmu0 : 0 ≤ ∑ x, mu G σ x := Finset.sum_nonneg fun x _ => mu_nonneg G σ x
  obtain ⟨x0⟩ := (inferInstance : Nonempty (Fin n))
  have hoth0 : ∀ x, 0 ≤ oth σ x := fun x => Finset.sum_nonneg fun y _ => by
    split_ifs <;> norm_num
  have hPQ : 4 * (p * q) ≤ (n : ℤ) ^ 2 := by rw [← hpq]; nlinarith [sq_nonneg (p - q)]
  have hmuII : ∑ x, mu G σ x ≤ II G σ := by
    have : p * q < e := by linarith
    linarith
  have hαpq : ∃ α, α ≤ p ∧ α ≤ q ∧ 0 ≤ α ∧ p * q = α * (n - α) ∧ (α = p ∨ α = q) := by
    rcases le_total p q with h' | h'
    · exact ⟨p, le_refl _, h', hp0, by rw [← hpq]; ring, Or.inl rfl⟩
    · exact ⟨q, h', le_refl _, hq0, by rw [← hpq]; ring, Or.inr rfl⟩
  obtain ⟨α, hα1, hα2, hα0, hαpq, -⟩ := hαpq
  have hαn : 2 * α ≤ n := by linarith
  have hα4 : (n : ℤ) ≤ 4 * α :=
    ar_alpha _ _ _ _ _ _ h4 (by rw [← hαpq]; linarith) hT' ht' ht1' hh2 hα0
  by_cases hcase : ∃ x, α < 2 * dOwn G σ x
  · obtain ⟨x, hx⟩ := hcase
    have hN := caseN G σ x
    rw [hTc] at hN
    have hlo := local_opt G σ hσ x
    have hd0 : 0 ≤ dOwn G σ x := Finset.sum_nonneg fun y _ => by split_ifs <;> norm_num
    have h6 : 2 * (dOwn G σ x * dOwn G σ x) ≤ 6 * T := by
      have : dOwn G σ x * dOwn G σ x ≤ dOwn G σ x * dOth G σ x := mul_le_mul_of_nonneg_left hlo hd0
      linarith
    exact ar_caseN _ _ _ _ _ _ hx hα4 h6 hT' ht' hh2 hα0 (by linarith)
  · push_neg at hcase
    have hS := caseS G σ α hcase (fun x => by rcases hoth x with h' | h' <;> rw [h'] <;> assumption)
    rw [hTc] at hS
    have key : α * (e - α * (n - α)) ≤ T := by
      rw [← hαpq]
      have : II G σ - ∑ x, mu G σ x = 2 * (e - p * q) := by linarith
      rw [this] at hS
      linarith
    exact ar_caseS _ _ _ _ _ _ _ hn2 hr F3 hαn (by linarith) hα0 key hT'

end
end OMAE1010

theorem OMA.solution : type_of% @Erdos1010.erdos_1010.variants.erdos := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro n t ht G he
  classical
  have ht' : 100 * t < n := by
    have : (100 : ℝ) * t < n := by linarith
    exact_mod_cast this
  have := OMAE1010.main n t ht' G (by convert he)
  convert this
