import OMAStatements.S_opg_s_s_f_s_f_for_reloids

-- Problem: S(S(f)) = S(f) for reloids
-- Credit: @JamesSlash (agent: Claude Code, model claude-opus-5-5)
--
-- Disproof by an explicit endo-reloid on the natural numbers.
-- Let f be the filter on N x N whose sets contain the shift relation b = a + 1 and some tail
-- {(a, b) | k <= a}. Every power of f contains each shift relation b = a + n, and f^1 = f,
-- so every set of S(f) contains a relation Y k = {(a, b) | a <= b or k <= a}. Composing two
-- such relations gives the full relation (go up to max a k, then jump anywhere), so
-- S(f) o S(f) is the top filter and S(S(f)) is top. But S(f) is not top: the set
-- {(a, b) | a <= b or 2 <= a} lies in every f^n (f^n is contained in the principal filter of
-- {(a, b) | b = a + n or k < a + n} for every k; take k = n + 1), and it misses (1, 0).

namespace OMA.P24Reloid

open OMA.S_opg_s_s_f_s_f_for_reloids Filter

/-- The counterexample reloid: sets containing the successor relation and a tail. -/
def f0 : Filter (ℕ × ℕ) :=
  Filter.principal {p : ℕ × ℕ | p.2 = p.1 + 1} ⊔ Filter.comap Prod.fst Filter.atTop

/-- Lower envelope of the sets of S(f0). -/
def Y (k : ℕ) : Set (ℕ × ℕ) := {p | p.1 ≤ p.2 ∨ k ≤ p.1}

lemma mem_f0 {X : Set (ℕ × ℕ)} :
    X ∈ f0 ↔ {p : ℕ × ℕ | p.2 = p.1 + 1} ⊆ X ∧ ∃ k : ℕ, ∀ p : ℕ × ℕ, k ≤ p.1 → p ∈ X := by
  unfold f0
  rw [Filter.mem_sup, Filter.mem_principal, Filter.mem_comap]
  constructor
  · rintro ⟨h1, t, ht, hsub⟩
    refine ⟨h1, ?_⟩
    obtain ⟨k, hk⟩ := Filter.mem_atTop_sets.mp ht
    exact ⟨k, fun p hp => hsub (hk p.1 hp)⟩
  · rintro ⟨h1, k, hk⟩
    refine ⟨h1, Set.Ici k, Filter.Ici_mem_atTop k, ?_⟩
    intro p hp
    exact hk p hp

/-- Composing with the identity reloid loses nothing. -/
lemma le_comp_id {A : Type} (g : Filter (A × A)) : g ≤ rldComp g (rldId A) := by
  unfold rldComp
  rw [Filter.le_generate_iff]
  rintro K ⟨F, hF, G, hG, rfl⟩
  show relComp G F ∈ g
  refine Filter.mem_of_superset hG ?_
  intro p hp
  refine ⟨p.1, ?_, hp⟩
  have hF' : {q : A × A | q.1 = q.2} ⊆ F := Filter.mem_principal.mp hF
  exact hF' (by simp)

/-- A relation contained in every set of `f` and one contained in every set of `g` compose to a
relation contained in every set of `rldComp g f`. -/
lemma sub_comp {A : Type} {f g : Filter (A × A)} {P Q : Set (A × A)}
    (hf : ∀ F ∈ f, P ⊆ F) (hg : ∀ G ∈ g, Q ⊆ G) :
    ∀ X ∈ rldComp g f, relComp Q P ⊆ X := by
  intro X hX
  unfold rldComp at hX
  rw [Filter.mem_generate_iff] at hX
  obtain ⟨t, ht, -, hsub⟩ := hX
  refine subset_trans ?_ hsub
  intro p hp
  rw [Set.mem_sInter]
  intro K hK
  obtain ⟨F, hF, G, hG, rfl⟩ := ht hK
  obtain ⟨b, h1, h2⟩ := hp
  exact ⟨b, hf F hF h1, hg G hG h2⟩

/-- Every set of every power of `f0` contains the shift by `n`. -/
lemma shift_sub (n : ℕ) : ∀ X ∈ rldPow f0 n, {p : ℕ × ℕ | p.2 = p.1 + n} ⊆ X := by
  induction n with
  | zero =>
    intro X hX p hp
    have hX' : {q : ℕ × ℕ | q.1 = q.2} ⊆ X := Filter.mem_principal.mp hX
    apply hX'
    simp only [Set.mem_setOf_eq, add_zero] at hp ⊢
    exact hp.symm
  | succ n ih =>
    intro X hX
    have key := sub_comp (P := {p : ℕ × ℕ | p.2 = p.1 + n})
      (Q := {p : ℕ × ℕ | p.2 = p.1 + 1}) ih (fun G hG => (mem_f0.mp hG).1) X hX
    intro p hp
    apply key
    refine ⟨p.1 + n, ?_, ?_⟩
    · simp
    · simp only [Set.mem_setOf_eq] at hp ⊢
      omega

/-- Every set of `S f0` contains some `Y k`. -/
lemma Y_sub {X : Set (ℕ × ℕ)} (hX : X ∈ S f0) : ∃ k, Y k ⊆ X := by
  have hall : ∀ n, X ∈ rldPow f0 n := Filter.mem_iSup.mp hX
  have h1 : X ∈ f0 := le_comp_id f0 (hall 1)
  obtain ⟨-, k, hk⟩ := mem_f0.mp h1
  refine ⟨k, ?_⟩
  rintro ⟨a, b⟩ hp
  simp only [Y, Set.mem_setOf_eq] at hp
  rcases hp with hab | hka
  · apply shift_sub (b - a) X (hall (b - a))
    simp only [Set.mem_setOf_eq]
    omega
  · exact hk (a, b) hka

/-- If every set of `f` and of `g` contains some `Y k`, then every set of `rldComp g f` is full. -/
lemma comp_full {f g : Filter (ℕ × ℕ)} (hf : ∀ F ∈ f, ∃ k, Y k ⊆ F)
    (hg : ∀ G ∈ g, ∃ k, Y k ⊆ G) : ∀ X ∈ rldComp g f, ∀ p, p ∈ X := by
  intro X hX p
  unfold rldComp at hX
  rw [Filter.mem_generate_iff] at hX
  obtain ⟨t, ht, -, hsub⟩ := hX
  apply hsub
  rw [Set.mem_sInter]
  intro K hK
  obtain ⟨F, hF, G, hG, rfl⟩ := ht hK
  obtain ⟨k1, h1⟩ := hf F hF
  obtain ⟨k2, h2⟩ := hg G hG
  refine ⟨max p.1 k2, h1 ?_, h2 ?_⟩
  · simp only [Y, Set.mem_setOf_eq]
    exact Or.inl (le_max_left _ _)
  · simp only [Y, Set.mem_setOf_eq]
    exact Or.inr (le_max_right _ _)

/-- The upper envelope of the powers of `f0`. -/
def V (k n : ℕ) : Set (ℕ × ℕ) := {p | p.2 = p.1 + n ∨ k < p.1 + n}

lemma V_mem (k n : ℕ) : V k n ∈ rldPow f0 n := by
  induction n with
  | zero =>
    show V k 0 ∈ Filter.principal {q : ℕ × ℕ | q.1 = q.2}
    rw [Filter.mem_principal]
    intro p hp
    simp only [V, Set.mem_setOf_eq] at hp ⊢
    omega
  | succ n ih =>
    have hG : {p : ℕ × ℕ | p.2 = p.1 + 1 ∨ k ≤ p.1} ∈ f0 := by
      rw [mem_f0]
      exact ⟨fun p hp => Or.inl hp, k, fun p hp => Or.inr hp⟩
    have hgen : relComp {p : ℕ × ℕ | p.2 = p.1 + 1 ∨ k ≤ p.1} (V k n) ∈ rldPow f0 (n + 1) :=
      Filter.mem_generate_of_mem ⟨V k n, ih, _, hG, rfl⟩
    refine Filter.mem_of_superset hgen ?_
    rintro ⟨a, c⟩ ⟨b, h1, h2⟩
    simp only [V, Set.mem_setOf_eq] at h1 h2 ⊢
    omega

/-- The set witnessing that `S f0` is not the top filter. -/
lemma X0_mem : Y 2 ∈ S f0 := by
  rw [S, Filter.mem_iSup]
  intro n
  refine Filter.mem_of_superset (V_mem (n + 1) n) ?_
  rintro ⟨a, b⟩ hp
  simp only [V, Y, Set.mem_setOf_eq] at hp ⊢
  omega

end OMA.P24Reloid

open OMA.S_opg_s_s_f_s_f_for_reloids OMA.P24Reloid
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_s_s_f_s_f_for_reloids.main) := by
  intro h
  have hS : S (S f0) = S f0 := h ℕ f0
  have hmem : Y 2 ∈ S (S f0) := by
    rw [hS]
    exact X0_mem
  have h2 : Y 2 ∈ rldPow (S f0) 2 := Filter.mem_iSup.mp hmem 2
  have hF : ∀ F ∈ rldComp (S f0) (rldId ℕ), ∃ k, Y k ⊆ F :=
    fun F hF => Y_sub (le_comp_id (S f0) hF)
  have hfull := comp_full hF (fun G hG => Y_sub hG) (Y 2) h2 (1, 0)
  simp [Y] at hfull
