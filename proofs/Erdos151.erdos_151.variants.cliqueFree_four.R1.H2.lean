import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1

-- Step: Erdos151.erdos_151.variants.cliqueFree_four.R1.H2
-- Credit: @SanskarX10
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- === BEGIN HELPERS ===
private abbrev OpaEdge := Fin 6 × Fin 6

private def opaEdges : List OpaEdge :=
  [(0,1), (0,2), (0,3), (0,4), (0,5),
   (1,2), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]

private def opaOK (m : Nat) (e : OpaEdge) (b : Bool) : Bool :=
  if b then !(m.testBit e.1.val && m.testBit e.2.val)
  else m.testBit e.1.val || m.testBit e.2.val

private theorem opaOK_spec (m : Nat) (e : OpaEdge) (b : Bool) :
    opaOK m e b = true ↔
      ¬ (m.testBit e.1.val = b ∧ m.testBit e.2.val = b) := by
  cases b <;> cases h₁ : m.testBit e.1.val <;>
    cases h₂ : m.testBit e.2.val <;> simp [opaOK, h₁, h₂]

private def opaColor : List OpaEdge → List Nat → Bool
  | [], ds => !ds.isEmpty
  | e :: es, ds =>
      opaColor es (ds.filter (fun m => opaOK m e false)) &&
      opaColor es (ds.filter (fun m => opaOK m e true))

private theorem opaColor_sound (C : Fin 6 → Fin 6 → Bool) (g : List OpaEdge) :
    ∀ ds, opaColor g ds = true →
      ∃ m ∈ ds, ∀ e ∈ g,
        ¬ (m.testBit e.1.val = C e.1 e.2 ∧ m.testBit e.2.val = C e.1 e.2) := by
  induction g with
  | nil =>
      intro ds h
      cases ds with
      | nil => simp [opaColor] at h
      | cons m ms => exact ⟨m, by simp, by simp⟩
  | cons e es ih =>
      intro ds h
      simp only [opaColor, Bool.and_eq_true] at h
      have hs : opaColor es (ds.filter (fun m => opaOK m e (C e.1 e.2))) = true := by
        cases hc : C e.1 e.2 with
        | false => simpa only [hc] using h.1
        | true => simpa only [hc] using h.2
      obtain ⟨m, hm, hrest⟩ := ih _ hs
      simp only [List.mem_filter] at hm
      refine ⟨m, hm.1, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (opaOK_spec _ _ _).mp hm.2
      · exact hrest p hp

private def opaAssignments : List Nat := List.range 64

private def opaBip (g : List OpaEdge) : Bool :=
  opaAssignments.any (fun m => g.all (fun e =>
    decide (m.testBit e.1.val ≠ m.testBit e.2.val)))

private def opaMeet (g : List OpaEdge) (x y : Fin 6) : Bool :=
  g.any (fun e => decide (e = (x,y) ∨ e = (y,x)))

private def opaTri (g : List OpaEdge) (e : OpaEdge) : Bool :=
  ([0,1,2,3,4,5] : List (Fin 6)).any (fun z =>
    opaMeet g e.1 z && opaMeet g e.2 z)

private def opaScan (g : List OpaEdge) : List OpaEdge → Bool
  | [] => opaBip g || opaColor g opaAssignments
  | e :: es => opaScan g es && (opaTri g e || opaScan (e :: g) es)

private theorem opaScan_step {g es : List OpaEdge} {e : OpaEdge}
    (h₀ : opaScan g es = true)
    (h₁ : opaTri g e = true ∨ opaScan (e :: g) es = true) :
    opaScan g (e :: es) = true := by
  simpa only [opaScan, Bool.and_eq_true, Bool.or_eq_true] using And.intro h₀ h₁

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem opaCertificate : opaScan [] opaEdges = true := by
  unfold opaEdges
  all_goals refine opaScan_step ?_ (Or.inr ?_)
  all_goals refine opaScan_step ?_ (Or.inr ?_)
  all_goals refine opaScan_step ?_ (Or.inr ?_)
  all_goals refine opaScan_step ?_ (Or.inr ?_)
  all_goals refine opaScan_step ?_ (Or.inr ?_)
  all_goals rfl

private theorem opaScan_sound (A : Fin 6 → Fin 6 → Prop)
    (hsym : ∀ ⦃x y⦄, A x y → A y x)
    (htri : ∀ x y z, A x y → A x z → A y z → False)
    (C : Fin 6 → Fin 6 → Bool) (es : List OpaEdge) :
    ∀ g : List OpaEdge, (∀ p ∈ g, A p.1 p.2) → opaScan g es = true →
      ∃ m : Nat, ∀ p : OpaEdge, p ∈ g ∨ (p ∈ es ∧ A p.1 p.2) →
        ¬ (m.testBit p.1.val = C p.1 p.2 ∧ m.testBit p.2.val = C p.1 p.2) := by
  classical
  have meet (g : List OpaEdge) (hg : ∀ p ∈ g, A p.1 p.2) (x y : Fin 6)
      (h : opaMeet g x y = true) : A x y := by
    simp only [opaMeet, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨p, hp, rfl | rfl⟩ := h
    · exact hg _ hp
    · exact hsym (hg _ hp)
  induction es with
  | nil =>
      intro g hg h
      simp only [opaScan, Bool.or_eq_true] at h
      rcases h with hb | hc
      · simp only [opaBip, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hb
        obtain ⟨m, _, hm⟩ := hb
        refine ⟨m, ?_⟩
        intro p hp hbad
        have hp' : p ∈ g := by simpa using hp
        exact hm p hp' (hbad.1.trans hbad.2.symm)
      · obtain ⟨m, _, hm⟩ := opaColor_sound C g _ hc
        exact ⟨m, fun p hp => hm p (by simpa using hp)⟩
  | cons e es ih =>
      intro g hg h
      simp only [opaScan, Bool.and_eq_true, Bool.or_eq_true] at h
      by_cases he : A e.1 e.2
      · have hn : opaTri g e ≠ true := by
          intro ht
          simp only [opaTri, List.any_eq_true, Bool.and_eq_true] at ht
          obtain ⟨z, _, hx, hy⟩ := ht
          exact htri e.1 e.2 z he (meet g hg _ _ hx) (meet g hg _ _ hy)
        have hg' : ∀ p ∈ e :: g, A p.1 p.2 := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact he
          · exact hg p hp
        obtain ⟨m, hm⟩ := ih (e :: g) hg' (h.2.resolve_left hn)
        refine ⟨m, fun p hp => hm p ?_⟩
        simp only [List.mem_cons] at hp ⊢
        tauto
      · obtain ⟨m, hm⟩ := ih g hg h.1
        refine ⟨m, fun p hp => hm p ?_⟩
        rcases hp with hp | ⟨hp, ha⟩
        · exact Or.inl hp
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact (he ha).elim
          · exact Or.inr ⟨hp, ha⟩

private theorem opaCover (a b : Fin 6) :
    a ≠ b → (a,b) ∈ opaEdges ∨ (b,a) ∈ opaEdges := by
  fin_cases a <;> fin_cases b <;> decide

private theorem opaNoTriangle {k : Nat} (L : SimpleGraph (Fin k))
    (hfree : L.CliqueFree 3) (x y z : Fin k)
    (hxy : L.Adj x y) (hxz : L.Adj x z) (hyz : L.Adj y z) : False := by
  have hloop (a : Fin k) : ¬ L.Adj a a := by
    apply L.loopless.irrefl
  have hxy' : x ≠ y := by
    intro h
    subst y
    exact hloop x hxy
  have hxz' : x ≠ z := by
    intro h
    subst z
    exact hloop x hxz
  have hyz' : y ≠ z := by
    intro h
    subst z
    exact hloop y hyz
  have hs : L.IsNClique 3 ({x,y,z} : Finset (Fin k)) := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      have ha' : a = x ∨ a = y ∨ a = z := by
        simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using ha
      have hb' : b = x ∨ b = y ∨ b = z := by
        simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using hb
      rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
        first | exact (hab rfl).elim | assumption | solve | apply L.symm.symm; assumption
    · have hx : x ∉ ({y,z} : Finset (Fin k)) := by simp [hxy', hxz']
      have hy : y ∉ ({z} : Finset (Fin k)) := by simp [hyz']
      rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hy,
        Finset.card_singleton]
  first | exact hfree hs | exact hfree _ hs
-- === END HELPERS ===

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1.H2 := by
  classical
  intro k L hk hfree c hc
  let f (i : Fin k) : Fin 6 := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have hf : Function.Injective f := by
    intro x y h
    have hv := congrArg (fun i : Fin 6 => i.val) h
    exact Fin.ext hv
  let A (i j : Fin 6) : Prop :=
    ∃ x y : Fin k, f x = i ∧ f y = j ∧ L.Adj x y
  have hs : ∀ ⦃i j⦄, A i j → A j i := by
    intro i j h
    obtain ⟨x, y, hx, hy, hxy⟩ := h
    refine ⟨y, x, hy, hx, ?_⟩
    apply L.symm.symm
    exact hxy
  have ht : ∀ i j l, A i j → A i l → A j l → False := by
    intro i j l hij hil hjl
    obtain ⟨x, y, rfl, rfl, hxy⟩ := hij
    obtain ⟨x', z, hxx, rfl, hxz⟩ := hil
    obtain ⟨y', z', hyy, hzz, hyz⟩ := hjl
    have ex : x' = x := hf hxx
    have ey : y' = y := hf hyy
    have ez : z' = z := hf hzz
    subst x'
    subst y'
    subst z'
    exact opaNoTriangle L hfree x y z hxy hxz hyz
  let C (i j : Fin 6) : Bool :=
    if hi : i.val < k then
      if hj : j.val < k then c ⟨i.val, hi⟩ ⟨j.val, hj⟩ else false
    else false
  have hC (x y : Fin k) : C (f x) (f y) = c x y := by
    simp [C, f, x.isLt, y.isLt]
  obtain ⟨m, hm⟩ := opaScan_sound A hs ht C opaEdges [] (by simp) opaCertificate
  refine ⟨fun x => m.testBit (f x).val, ?_⟩
  intro x y hxy
  have hne : f x ≠ f y := by
    intro h
    have he := hf h
    subst y
    have hn : ¬ L.Adj x x := by apply L.loopless.irrefl
    exact hn hxy
  have ha : A (f x) (f y) := ⟨x, y, rfl, rfl, hxy⟩
  rcases opaCover (f x) (f y) hne with hp | hp
  · have hh := hm (f x, f y) (Or.inr ⟨hp, ha⟩)
    change ¬ (m.testBit (f x).val = C (f x) (f y) ∧
      m.testBit (f y).val = C (f x) (f y)) at hh
    simpa only [hC] using hh
  · have hh := hm (f y, f x) (Or.inr ⟨hp, hs ha⟩)
    change ¬ (m.testBit (f y).val = C (f y) (f x) ∧
      m.testBit (f x).val = C (f y) (f x)) at hh
    rw [hC, hc y x] at hh
    intro hbad
    exact hh ⟨hbad.2, hbad.1⟩
