import OMAStatements.S_oeis_a008484

theorem bc_sum_add_two (s : Multiset ℕ) :
    (s.map (fun i => i + 2)).sum = s.sum + 2 * Multiset.card s := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro a s ih
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    ring

theorem bc_map_sub_add (s : Multiset ℕ) (h : ∀ i ∈ s, 2 ≤ i) :
    (s.map (fun i => i - 2)).map (fun i => i + 2) = s := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id s]
  exact Multiset.map_congr rfl (fun i hi => by have := h i hi; show i - 2 + 2 = i; omega)

theorem bc_map_add_sub (s : Multiset ℕ) :
    (s.map (fun i => i + 2)).map (fun i => i - 2) = s := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id s]
  exact Multiset.map_congr rfl (fun i _ => by show i + 2 - 2 = i; omega)

theorem bc_part_ext {n : ℕ} {p q : Nat.Partition n} (h : p.parts = q.parts) : p = q := by
  first
  | exact Nat.Partition.ext h
  | (cases p; cases q; simp only at h; subst h; rfl)

def bcF {n : ℕ} (p : Nat.Partition n) (hp : ∀ i ∈ p.parts, 4 ≤ i) : Nat.Partition n where
  parts := p.parts.map (fun i => i - 2) + Multiset.replicate (2 * Multiset.card p.parts) 1
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.1 hi with h | h
    · obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 h
      have := hp j hj
      show 0 < j - 2
      omega
    · rw [Multiset.eq_of_mem_replicate h]
      exact Nat.one_pos
  parts_sum := by
    have h2 : ∀ i ∈ p.parts, 2 ≤ i := fun i hi => by have := hp i hi; omega
    have key := bc_sum_add_two (p.parts.map (fun i => i - 2))
    rw [bc_map_sub_add p.parts h2, Multiset.card_map] at key
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one, ← key]
    exact p.parts_sum

def bcG {n : ℕ} (q : Nat.Partition n) (hq : 3 * q.parts.count 1 = 2 * Multiset.card q.parts) :
    Nat.Partition n where
  parts := (q.parts.filter (fun a => ¬ a = 1)).map (fun i => i + 2)
  parts_pos := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hi
    show 0 < j + 2
    omega
  parts_sum := by
    have hs : q.parts.filter (fun a => a = 1) + q.parts.filter (fun a => ¬ a = 1) = q.parts := by
      first
      | exact Multiset.filter_add_not _ _
      | exact Multiset.filter_add_not _
    have he : q.parts.filter (fun a => a = 1) = Multiset.replicate (q.parts.count 1) 1 := by
      first
      | exact Multiset.filter_eq' _ _
      | exact Multiset.filter_eq' q.parts 1
    have hsum := congrArg Multiset.sum hs
    have hcard := congrArg Multiset.card hs
    rw [Multiset.sum_add, he, Multiset.sum_replicate, smul_eq_mul, mul_one, q.parts_sum] at hsum
    rw [Multiset.card_add, he, Multiset.card_replicate] at hcard
    rw [bc_sum_add_two]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a008484.main := by
  intro n
  refine Finset.card_bij' (fun p hp => bcF p (Finset.mem_filter.1 hp).2)
    (fun q hq => bcG q (Finset.mem_filter.1 hq).2) ?_ ?_ ?_ ?_
  · intro p hp
    have h4 := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show 3 * Multiset.count 1 (p.parts.map (fun i => i - 2) +
        Multiset.replicate (2 * Multiset.card p.parts) 1) =
      2 * Multiset.card (p.parts.map (fun i => i - 2) +
        Multiset.replicate (2 * Multiset.card p.parts) 1)
    have e0 : Multiset.count 1 (p.parts.map (fun i => i - 2)) = 0 :=
      Multiset.count_eq_zero.2 (fun h => by
        obtain ⟨j, hj, hj1⟩ := Multiset.mem_map.1 h
        have := h4 j hj
        omega)
    rw [Multiset.count_add, Multiset.count_replicate_self, Multiset.card_add, Multiset.card_map,
      Multiset.card_replicate, e0]
    ring
  · intro q hq
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    intro i hi
    change i ∈ (q.parts.filter (fun a => ¬ a = 1)).map (fun i => i + 2) at hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hi
    have hj' := Multiset.mem_filter.1 hj
    have := q.parts_pos hj'.1
    show 4 ≤ j + 2
    omega
  · intro p hp
    have h4 := (Finset.mem_filter.1 hp).2
    apply bc_part_ext
    show ((p.parts.map (fun i => i - 2) + Multiset.replicate (2 * Multiset.card p.parts) 1).filter
      (fun a => ¬ a = 1)).map (fun i => i + 2) = p.parts
    have e1 : (p.parts.map (fun i => i - 2)).filter (fun a => ¬ a = 1) =
        p.parts.map (fun i => i - 2) :=
      Multiset.filter_eq_self.2 (fun a ha => by
        obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 ha
        have := h4 j hj
        show ¬ (j - 2 = 1)
        omega)
    have e2 : (Multiset.replicate (2 * Multiset.card p.parts) 1).filter (fun a => ¬ a = 1) = 0 :=
      Multiset.filter_eq_nil.2 (fun a ha => by
        rw [Multiset.eq_of_mem_replicate ha]
        simp)
    rw [Multiset.filter_add, e1, e2, add_zero]
    exact bc_map_sub_add p.parts (fun i hi => by have := h4 i hi; omega)
  · intro q hq
    have h3 := (Finset.mem_filter.1 hq).2
    apply bc_part_ext
    show ((q.parts.filter (fun a => ¬ a = 1)).map (fun i => i + 2)).map (fun i => i - 2) +
      Multiset.replicate (2 * Multiset.card ((q.parts.filter (fun a => ¬ a = 1)).map
        (fun i => i + 2))) 1 = q.parts
    rw [bc_map_add_sub, Multiset.card_map]
    have hs : q.parts.filter (fun a => a = 1) + q.parts.filter (fun a => ¬ a = 1) = q.parts := by
      first
      | exact Multiset.filter_add_not _ _
      | exact Multiset.filter_add_not _
    have he : q.parts.filter (fun a => a = 1) = Multiset.replicate (q.parts.count 1) 1 := by
      first
      | exact Multiset.filter_eq' _ _
      | exact Multiset.filter_eq' q.parts 1
    have hcard := congrArg Multiset.card hs
    rw [Multiset.card_add, he, Multiset.card_replicate] at hcard
    have h2 : 2 * Multiset.card (q.parts.filter (fun a => ¬ a = 1)) = q.parts.count 1 := by
      omega
    rw [h2]
    conv_rhs => rw [← hs, he]
    exact add_comm _ _
