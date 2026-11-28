import OMAStatements.S_mo_387203


open OMA.S_mo_387203

theorem PP_mem_sums (l : List Vec) (x : Vec) :
    x ∈ sums l ↔ ∃ s : List Vec, s.Sublist l ∧ s.sum = x := by
  induction l generalizing x with
  | nil => simp [sums, eq_comm]
  | cons a l ih =>
    simp only [sums, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (⟨s, hs, rfl⟩ | ⟨y, ⟨s, hs, rfl⟩, rfl⟩)
      · exact ⟨s, hs.cons a, rfl⟩
      · exact ⟨a :: s, hs.cons_cons a, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      cases hs with
      | cons _ h => exact Or.inl ⟨_, h, rfl⟩
      | cons_cons _ h => exact Or.inr ⟨_, ⟨_, h, rfl⟩, by simp⟩

theorem PP_length_sums (l : List Vec) : (sums l).length = 2 ^ l.length := by
  induction l with
  | nil => simp [sums]
  | cons a l ih => simp [sums, ih, pow_succ]; omega

theorem PP_reaches_append (l₁ l₂ : List Vec) (c : Vec) :
    reaches (l₁ ++ l₂) c ↔ ∃ a ∈ sums l₁, ∃ b ∈ sums l₂, a + b = c := by
  unfold reaches
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨s₁, s₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hs
    exact ⟨s₁.sum, (PP_mem_sums _ _).2 ⟨s₁, h₁, rfl⟩, s₂.sum,
      (PP_mem_sums _ _).2 ⟨s₂, h₂, rfl⟩, by simp⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨s₁, h₁, rfl⟩ := (PP_mem_sums _ _).1 ha
    obtain ⟨s₂, h₂, rfl⟩ := (PP_mem_sums _ _).1 hb
    exact ⟨s₁ ++ s₂, List.Sublist.append h₁ h₂, by simp⟩

instance PP_trans : Std.TransCmp (lexOrd.compare : Vec → Vec → Ordering) :=
  inferInstanceAs <| Std.TransCmp (compareLex (compareOn (fun p : Vec => p.1)) (compareOn (fun p : Vec => p.2)))

instance PP_lawful : Std.LawfulBEqCmp (lexOrd.compare : Vec → Vec → Ordering) where
  compare_eq_iff_beq {a b} := by
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp

theorem partP1 : ∀ (v : List Vec) (c : Vec), query v c = true ↔ reaches v c := by
  intro v c
  have h := PP_reaches_append (v.take (v.length / 2)) (v.drop (v.length / 2)) c
  rw [List.take_append_drop] at h
  rw [h]
  simp only [query, List.any_eq_true, Std.TreeSet.contains_ofList, List.contains_iff_mem]
  constructor
  · rintro ⟨y, hy, hc⟩
    exact ⟨c - y, hc, y, hy, by abel⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, by simpa using ha⟩

theorem partP2 : ∀ v : List Vec, (sums (v.take (v.length/2))).length = 2^(v.length/2) ∧
    (sums (v.drop (v.length/2))).length = 2^(v.length-v.length/2) := by
  intro v
  rw [PP_length_sums, PP_length_sums, List.length_take, List.length_drop]
  refine ⟨?_, rfl⟩
  congr 1
  omega

theorem PQ_compl {G : Type*} [AddCommMonoid G] {s l : List G} (h : s.Sublist l) :
    ∃ s' : List G, s'.Sublist l ∧ s.sum + s'.sum = l.sum := by
  induction h with
  | slnil => exact ⟨[], List.Sublist.slnil, by simp⟩
  | cons a _ ih =>
    obtain ⟨s', hs', e⟩ := ih
    refine ⟨a :: s', hs'.cons_cons a, ?_⟩
    rw [List.sum_cons, List.sum_cons, ← e]
    abel
  | cons_cons a _ ih =>
    obtain ⟨s', hs', e⟩ := ih
    refine ⟨s', hs'.cons a, ?_⟩
    rw [List.sum_cons, List.sum_cons, ← e]
    abel

theorem PQ_reaches_compl_mp {G : Type*} [AddCommGroup G] (l : List G) (c : G)
    (h : reaches l c) : reaches l (l.sum - c) := by
  obtain ⟨s, hs, rfl⟩ := h
  obtain ⟨s', hs', e⟩ := PQ_compl hs
  refine ⟨s', hs', ?_⟩
  rw [← e]
  abel

theorem PQ_reaches_compl {G : Type*} [AddCommGroup G] (l : List G) (c : G) :
    reaches l c ↔ reaches l (l.sum - c) := by
  constructor
  · exact PQ_reaches_compl_mp l c
  · intro h
    have h2 := PQ_reaches_compl_mp l _ h
    rwa [sub_sub_cancel] at h2

theorem PQ_horiz_eq (v : List Vec) : horiz v = v.sum - vert v := by
  apply Prod.ext <;> simp [vert, horiz]

theorem partQ1 : ∀ v : List Vec, reaches v (vert v) ↔ reaches v (horiz v) := by
  intro v
  rw [PQ_horiz_eq]
  exact PQ_reaches_compl v (vert v)

theorem PQ_map_sum (v : List ℤ) :
    (v.map (fun x => ((x, 0) : Vec))).sum = (v.sum, 0) := by
  induction v with
  | nil => rfl
  | cons a v ih => rw [List.map_cons, List.sum_cons, List.sum_cons, ih]; simp

theorem PQ_vert_encode (v : List ℤ) (t : ℤ) : vert (encode v t) = (0, 1) := by
  simp [vert, encode, PQ_map_sum]

theorem PQ_vert_iff (v : List ℤ) (t : ℤ) :
    reaches v t ↔ reaches (encode v t) (0, 1) := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(-s.sum, 1) :: s.map (fun x => ((x, 0) : Vec)),
      (hs.map _).cons_cons _, ?_⟩
    rw [List.sum_cons, PQ_map_sum]
    simp
  · rintro ⟨s, hs, hsum⟩
    unfold encode at hs
    cases hs with
    | cons _ h =>
      obtain ⟨s', _, rfl⟩ := List.sublist_map_iff.1 h
      rw [PQ_map_sum] at hsum
      have := congrArg Prod.snd hsum
      simp at this
    | cons_cons _ h =>
      obtain ⟨s', hs', rfl⟩ := List.sublist_map_iff.1 h
      rw [List.sum_cons, PQ_map_sum] at hsum
      have h1 := congrArg Prod.fst hsum
      simp at h1
      exact ⟨s', hs', by linarith⟩

theorem partQ2 : ∀ (v : List ℤ) (t : ℤ), (v.Nodup → (encode v t).Nodup) ∧
    (reaches v t ↔ reaches (encode v t) (vert (encode v t))) ∧
    (reaches v t ↔ reaches (encode v t) (horiz (encode v t))) := by
  intro v t
  have hv : reaches v t ↔ reaches (encode v t) (vert (encode v t)) := by
    rw [PQ_vert_encode]; exact PQ_vert_iff v t
  refine ⟨?_, hv, hv.trans (partQ1 _)⟩
  intro hn
  unfold encode
  rw [List.nodup_cons]
  refine ⟨?_, hn.map (fun a b h => (Prod.mk.inj h).1)⟩
  intro hm
  obtain ⟨x, _, hx⟩ := List.mem_map.1 hm
  have := congrArg Prod.snd hx
  simp at this

theorem OMA.solution : type_of% @OMA.S_mo_387203.main :=
  ⟨partP1, partP2, partQ1, partQ2⟩
