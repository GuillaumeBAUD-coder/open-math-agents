import FormalConjectures.ErdosProblems.«723»

namespace OMA.R_Erdos723_erdos_723_variants_eq_12_R1

open Configuration

-- Find an intersecting partial plane, fourteen lines short of a full plane.
def H1 : Prop :=
  ∃ S : Finset (Finset (Fin 157)), S.card = 143 ∧ (∀ b ∈ S, b.card = 13) ∧
    ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

-- One-line extension, a consequence of Metsch's embedding bound n² − n/6.
def H2 : Prop :=
  ∀ S : Finset (Finset (Fin 157)), 143 ≤ S.card → S.card < 157 →
    (∀ b ∈ S, b.card = 13) → (∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) →
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = S.card + 1 ∧
      (∀ b ∈ T, b.card = 13) ∧ ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

lemma third_point (s : Finset (Fin 157)) (hs : s.card = 13) (a b : Fin 157) :
    ∃ x ∈ s, x ≠ a ∧ x ≠ b := by
  classical
  by_contra hn
  have sub : s ⊆ {a, b} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra! h
    exact hn ⟨x, hx, h⟩
  have hle := Finset.card_le_card sub
  have hpair : ({a, b} : Finset (Fin 157)).card ≤ 2 := by
    by_cases h : a = b <;> simp [h]
  omega

lemma plane_of_blocks (B : Fin 157 → Finset (Fin 157)) (size : ∀ i, (B i).card = 13)
    (meet : ∀ i j, i ≠ j → ∃! x, x ∈ B i ∧ x ∈ B j) :
    type_of% @Erdos723.erdos_723.variants.eq_12 := by
  classical
  letI : Membership (Fin 157) (Fin 157) := ⟨fun l p => p ∈ B l⟩
  have outside (i j : Fin 157) : ∃ p, p ∉ B i ∧ p ∉ B j := by
    by_contra hn
    have sub : Finset.univ ⊆ B i ∪ B j := by
      intro p _
      simp only [Finset.mem_union]
      by_contra! hh
      exact hn ⟨p, hh⟩
    have hle := Finset.card_le_card sub
    have hu := Finset.card_union_le (B i) (B j)
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    rw [size, size] at hu
    omega
  have misses (p : Fin 157) : ∃ i, p ∉ B i := by
    by_contra! hall
    choose f hf using fun i => third_point (B i) (size i) p p
    have inj : Function.Injective f := by
      intro i j h
      by_contra hij
      exact (hf i).2.1 ((meet i j hij).unique ⟨(hf i).1, h ▸ (hf j).1⟩ ⟨hall i, hall j⟩)
    obtain ⟨i, hi⟩ := (Finite.surjective_of_injective inj) p
    exact (hf i).2.1 hi
  letI : HasPoints (Fin 157) (Fin 157) := {
    exists_point := fun l => (outside l l).imp fun _ h => h.1
    exists_line := misses
    eq_or_eq := by
      intro p q l m hpl hql hpm hqm
      by_cases h : l = m
      · exact Or.inr h
      · exact Or.inl ((meet l m h).unique ⟨hpl, hpm⟩ ⟨hql, hqm⟩)
    mkPoint := fun {l m} h => (meet l m h).choose
    mkPoint_ax := fun {l m} h => (meet l m h).choose_spec.1 }
  letI := HasPoints.hasLines (P := Fin 157) (L := Fin 157) rfl
  obtain ⟨p, hp, _⟩ := meet 0 1 (by decide)
  obtain ⟨l, hl⟩ := misses p
  have hl0 : l ≠ 0 := by rintro rfl; exact hl hp.1
  obtain ⟨z, hz, _⟩ := meet l 0 hl0
  obtain ⟨q, hq, hqz, hqp⟩ := third_point (B 0) (size 0) z p
  obtain ⟨u, hu⟩ := outside 0 1
  letI pp : ProjectivePlane (Fin 157) (Fin 157) :=
    { (inferInstance : HasPoints (Fin 157) (Fin 157)),
      (inferInstance : HasLines (Fin 157) (Fin 157)) with
      exists_config := ⟨u, p, q, l, 0, 1, hu.1, hu.2, hl, hp.1, hp.2,
        fun h => hqz ((meet l 0 hl0).unique ⟨h, hq⟩ hz), hq,
        fun h => hqp ((meet 0 1 (by decide)).unique ⟨hq, h⟩ hp)⟩ }
  refine ⟨Fin 157, Fin 157, inferInstance, inferInstance, inferInstance, pp, ?_⟩
  have hc := ProjectivePlane.pointCount_eq (Fin 157) (0 : Fin 157)
  have hk : pointCount (Fin 157) (0 : Fin 157) = 13 := by
    change Nat.card {p : Fin 157 // p ∈ B 0} = 13
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using size 0
  change ProjectivePlane.order (Fin 157) (Fin 157) = 12
  omega

theorem main : H1 → H2 → type_of% @Erdos723.erdos_723.variants.eq_12 := by
  classical
  intro seed extend
  have grow (k : ℕ) (hk : k ≤ 14) : ∃ S : Finset (Finset (Fin 157)),
      S.card = 143 + k ∧ (∀ b ∈ S, b.card = 13) ∧
        ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c := by
    induction k with
    | zero => exact seed
    | succ k ih =>
      obtain ⟨S, hn, hs, hm⟩ := ih (by omega)
      obtain ⟨T, _, ht, hs', hm'⟩ := extend S (by omega) (by omega) hs hm
      exact ⟨T, by omega, hs', hm'⟩
  obtain ⟨S, hn, hs, hm⟩ := grow 14 (by decide)
  let e := (Fintype.equivFinOfCardEq (show Fintype.card S = 157 by simpa using hn)).symm
  apply plane_of_blocks (fun i => (e i).val) (fun i => hs _ (e i).property)
  intro i j hij
  exact hm _ (e i).property _ (e j).property (fun h => hij (e.injective (Subtype.ext h)))

end OMA.R_Erdos723_erdos_723_variants_eq_12_R1
