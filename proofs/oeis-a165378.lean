import OMAStatements.S_oeis_a165378

/-!
# The slanted four-colour board count

Problem: https://lefttosolve.com/p/oeis-a165378
Source: https://oeis.org/A165378 (R. H. Hardin; conjectured formula by Colin Barker).
Credit: @CubeJerry (agent: codex, model: gpt-6.2-astra).

The proof first identifies valid boards with words accepted by a finite frontier
automaton. A state records the last row, its current degrees, the connectivity
relation on its four cells, and colours whose connected component is closed.
The union-find calculation is proved equivalent to graph reachability.

An explicit family of 766 states is closed under all 256 possible next rows.
The initial, transition, and acceptance identities are checked in the Lean
kernel. Three coefficient vectors certify that the count of suffixes of length
k+3 is quadratic in k. Summing over initial states gives
9*k^2 + 76*k + 158, which is 9*n^2 + 4*n - 2 for n=k+4.
-/

/- Frontier. -/
section

namespace A165378Proof

abbrev Ix := Fin 4
abbrev Row := Ix → Fin 4
abbrev Node := Fin 8
abbrev Labels := List.Vector ℕ 8

structure State where
  row : Row
  degree : Ix → ℕ
  conn : Ix → Ix → Bool
  done : Fin 4 → Bool

theorem state_eq_iff (s t : State) : s = t ↔
    (∀ i, s.row i = t.row i) ∧ (∀ i, s.degree i = t.degree i) ∧
    (∀ i j, s.conn i j = t.conn i j) ∧ (∀ i, s.done i = t.done i) := by
  constructor
  · rintro rfl
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  · rintro ⟨hr, hd, hc, hz⟩
    cases s with
    | mk sr sd sc sz =>
      cases t with
      | mk tr td tc tz =>
        have hr' : sr = tr := funext hr
        have hd' : sd = td := funext hd
        have hc' : sc = tc := funext fun i => funext (hc i)
        have hz' : sz = tz := funext hz
        cases hr'; cases hd'; cases hc'; cases hz'
        rfl

instance instDecidableEqState : DecidableEq State := fun s t =>
  decidable_of_iff _ (state_eq_iff s t).symm

def old (i : Ix) : Node := ⟨i.val, by omega⟩
def new (i : Ix) : Node := ⟨i.val + 4, by omega⟩
def lo (i : Fin 3) : Ix := ⟨i.val, by omega⟩
def hi (i : Fin 3) : Ix := ⟨i.val + 1, by omega⟩

def mergeLabels (lab : Labels) (edge : Node × Node) : Labels :=
  if lab.get edge.1 = lab.get edge.2 then lab
  else lab.map fun x => if x = lab.get edge.2 then lab.get edge.1 else x

def closureLabels (edges : List (Node × Node)) : Labels :=
  edges.foldl mergeLabels (List.Vector.ofFn Fin.val)

def horizontalEdges (r : Row) : List (Node × Node) :=
  (List.finRange 3).filterMap fun i =>
    if r (lo i) = r (hi i) then some (new (lo i), new (hi i)) else none

def oldEdges (s : State) : List (Node × Node) :=
  (List.finRange 4).flatMap fun i => (List.finRange 4).filterMap fun j =>
    if s.conn i j then some (old i, old j) else none

def verticalEdges (s : State) (r : Row) : List (Node × Node) :=
  (List.finRange 3).filterMap fun i =>
    if s.row (hi i) = r (lo i) then some (old (hi i), new (lo i)) else none

def stepEdges (s : State) (r : Row) : List (Node × Node) :=
  oldEdges s ++ verticalEdges s r ++ horizontalEdges r

def Linked (s : State) (r : Row) (u v : Node) : Prop :=
  (closureLabels (stepEdges s r)).get u = (closureLabels (stepEdges s r)).get v

instance (s : State) (r : Row) (u v : Node) : Decidable (Linked s r u v) :=
  inferInstanceAs (Decidable (_ = _))

def horizontalDegree (r : Row) (i : Ix) : ℕ :=
  (Finset.univ.filter fun j : Ix =>
    (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ r i = r j).card

def downDegree (s : State) (r : Row) (i : Ix) : ℕ :=
  (Finset.univ.filter fun j : Ix => i.val = j.val + 1 ∧ s.row i = r j).card

def upDegree (s : State) (r : Row) (j : Ix) : ℕ :=
  (Finset.univ.filter fun i : Ix => i.val = j.val + 1 ∧ s.row i = r j).card

def newDegree (s : State) (r : Row) (i : Ix) : ℕ :=
  horizontalDegree r i + upDegree s r i

def Alive (s : State) (r : Row) (i : Ix) : Prop :=
  ∃ j : Ix, Linked s r (old i) (new j)

instance (s : State) (r : Row) (i : Ix) : Decidable (Alive s r i) :=
  inferInstanceAs (Decidable (∃ j : Ix, Linked s r (old i) (new j)))

def StepOK (s : State) (r : Row) : Prop :=
  (∀ j, s.done (r j) = false) ∧
  (∀ i, s.degree i + downDegree s r i ≤ 2) ∧
  (∀ i, newDegree s r i ≤ 2) ∧
  ∀ i, ¬ Alive s r i →
    (∀ j, s.row j = s.row i → Linked s r (old i) (old j)) ∧
    (∀ j, r j ≠ s.row i)

instance (s : State) (r : Row) : Decidable (StepOK s r) := by
  unfold StepOK
  infer_instance

def nextState (s : State) (r : Row) : State where
  row := r
  degree := newDegree s r
  conn := fun i j => decide (Linked s r (new i) (new j))
  done := fun v => s.done v || decide (∃ i, s.row i = v ∧ ¬ Alive s r i)

def step (s : State) (r : Row) : Option State :=
  if StepOK s r then some (nextState s r) else none

def initial (r : Row) : State where
  row := r
  degree := horizontalDegree r
  conn := fun i j => decide
    ((closureLabels (horizontalEdges r)).get (new i) =
     (closureLabels (horizontalEdges r)).get (new j))
  done := fun _ => false

def TopRow (r : Row) : Prop := r 0 = 0 ∧ r 3 = 1

instance (r : Row) : Decidable (TopRow r) := inferInstanceAs (Decidable (_ ∧ _))

def accept (s : State) : Bool := decide
  (s.row 0 = 2 ∧ s.row 3 = 3 ∧ ∀ i j, s.row i = s.row j → s.conn i j = true)

def runFrom (s : State) (rs : List Row) : Option State :=
  rs.foldl (fun so r => so.bind (fun t => step t r)) (some s)

def run : List Row → Option State
  | [] => none
  | r :: rs => if TopRow r then runFrom (initial r) rs else none

def GoodWord {n : ℕ} (w : Fin n → Row) : Prop :=
  (run (List.ofFn w)).any accept = true

noncomputable def wordCount (n : ℕ) : ℕ :=
  Nat.card {w : Fin n → Row // GoodWord w}

noncomputable def suffixCount (s : State) (n : ℕ) : ℕ :=
  Nat.card {w : Fin n → Row // (runFrom s (List.ofFn w)).any accept = true}

end A165378Proof

end

/- Reach. -/
section

/-!
Reachability compression for extending a graph through a finite frontier.
Old paths are replaced by edges between their boundary endpoints.
-/

namespace A165378Reach

open Relation

variable {A B I : Type*}

def Glue (R : A → A → Prop) (S : B → B → Prop)
    (e : I → A) (J : I → B → Prop) : A ⊕ B → A ⊕ B → Prop
  | .inl a, .inl a' => R a a'
  | .inl a, .inr b => ∃ i, e i = a ∧ J i b
  | .inr b, .inl a => ∃ i, e i = a ∧ J i b
  | .inr b, .inr b' => S b b'

def Compressed (R : A → A → Prop) (S : B → B → Prop)
    (e : I → A) (J : I → B → Prop) : I ⊕ B → I ⊕ B → Prop
  | .inl i, .inl j => ReflTransGen R (e i) (e j)
  | .inl i, .inr b => J i b
  | .inr b, .inl i => J i b
  | .inr b, .inr b' => S b b'

def embed (e : I → A) : I ⊕ B → A ⊕ B
  | .inl i => .inl (e i)
  | .inr b => .inr b

variable {R : A → A → Prop} {S : B → B → Prop}
    {e : I → A} {J : I → B → Prop}

theorem lift_old {a a' : A} (h : ReflTransGen R a a') :
    ReflTransGen (Glue R S e J) (.inl a) (.inl a') :=
  h.lift Sum.inl (fun _ _ h => h)

theorem lift_new {b b' : B} (h : ReflTransGen S b b') :
    ReflTransGen (Glue R S e J) (.inr b) (.inr b') :=
  h.lift Sum.inr (fun _ _ h => h)

theorem expand {x y : I ⊕ B}
    (h : ReflTransGen (Compressed R S e J) x y) :
    ReflTransGen (Glue R S e J) (embed e x) (embed e y) := by
  apply h.lift' (embed e)
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => exact lift_old hxy
    | inr b => exact .single ⟨i, rfl, hxy⟩
  | inr b =>
    cases y with
    | inl i => exact .single ⟨i, rfl, hxy⟩
    | inr b' => exact .single hxy

private def FromFrontier (x : I ⊕ B) : A ⊕ B → Prop
  | .inl a => ∃ i, ReflTransGen (Compressed R S e J) x (.inl i) ∧
      ReflTransGen R (e i) a
  | .inr b => ReflTransGen (Compressed R S e J) x (.inr b)

theorem compress_aux {x : I ⊕ B} {y : A ⊕ B}
    (h : ReflTransGen (Glue R S e J) (embed e x) y) :
    FromFrontier (R := R) (S := S) (e := e) (J := J) x y := by
  induction h with
  | refl =>
    cases x with
    | inl i => exact ⟨i, .refl, .refl⟩
    | inr b => exact .refl
  | @tail y z hy hyz ih =>
    cases y with
    | inl a =>
      obtain ⟨i, hxi, hia⟩ := ih
      cases z with
      | inl a' => exact ⟨i, hxi, hia.tail hyz⟩
      | inr b =>
        obtain ⟨j, hj, hjb⟩ := hyz
        subst a
        have hij : Compressed R S e J (.inl i) (.inl j) := hia
        exact (hxi.tail hij).tail hjb
    | inr b =>
      cases z with
      | inl a =>
        obtain ⟨i, hi, hib⟩ := hyz
        subst a
        exact ⟨i, ih.tail hib, .refl⟩
      | inr b' => exact ih.tail hyz

theorem compress {x y : I ⊕ B}
    (h : ReflTransGen (Glue R S e J) (embed e x) (embed e y)) :
    ReflTransGen (Compressed R S e J) x y := by
  have h' := compress_aux h
  cases y with
  | inl j =>
    obtain ⟨i, hxi, hij⟩ := h'
    exact hxi.tail hij
  | inr b => exact h'

theorem compression {x y : I ⊕ B} :
    ReflTransGen (Glue R S e J) (embed e x) (embed e y) ↔
      ReflTransGen (Compressed R S e J) x y :=
  ⟨compress, expand⟩

/-- A component missing the frontier cannot leave the old graph. -/
theorem stays_old {a : A}
    (ha : ¬ ∃ i, ReflTransGen R a (e i)) {z : A ⊕ B}
    (h : ReflTransGen (Glue R S e J) (.inl a) z) :
    ∃ a', z = .inl a' ∧ ReflTransGen R a a' := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | @tail y z hy hyz ih =>
    obtain ⟨a', rfl, haa'⟩ := ih
    cases z with
    | inl a'' => exact ⟨a'', rfl, haa'.tail hyz⟩
    | inr b =>
      obtain ⟨i, hi, _⟩ := hyz
      exact (ha ⟨i, hi ▸ haa'⟩).elim

end A165378Reach

end

/- Components. -/
section

namespace A165378Reach

open Relation

variable {A B I C : Type*}

def Touches (R : A → A → Prop) (e : I → A) (a : A) : Prop :=
  ∃ i, ReflTransGen R a (e i)

/-- Every component missing the frontier is the whole of its color. -/
def FrontierValid (R : A → A → Prop) (color : A → C) (e : I → A) : Prop :=
  ∀ a b, color a = color b → ¬ Touches R e a → ReflTransGen R a b

theorem reach_symm {R : A → A → Prop} (hR : ∀ ⦃a b⦄, R a b → R b a) {a b : A}
    (h : ReflTransGen R a b) : ReflTransGen R b a := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih => exact .head (hR hbc) ih

theorem reach_color {R : A → A → Prop} {color : A → C}
    (hc : ∀ a b, R a b → color a = color b) {a b : A}
    (h : ReflTransGen R a b) : color a = color b := by
  induction h with
  | refl => rfl
  | tail hab hbc ih => exact ih.trans (hc _ _ hbc)

variable {R : A → A → Prop} {S : B → B → Prop}
    {e : I → A} {J : I → B → Prop}
    {ca : A → C} {cb : B → C}

theorem not_touches_glue {a : A} (ha : ¬ Touches R e a) :
    ¬ Touches (Glue R S e J) Sum.inr (.inl a) := by
  rintro ⟨b, hb⟩
  obtain ⟨a', he, _⟩ := stays_old ha hb
  cases he

theorem touches_compression (x : I ⊕ B) :
    Touches (Glue R S e J) Sum.inr (embed e x) ↔
      Touches (Compressed R S e J) Sum.inr x := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, compress (y := .inr b) hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, expand hb⟩

theorem frontier_valid_old
    (h : FrontierValid (Glue R S e J) (Sum.elim ca cb) Sum.inr) :
    FrontierValid R ca e := by
  intro a b hc ha
  have hab := h (.inl a) (.inl b) hc (not_touches_glue ha)
  obtain ⟨b', he, hp⟩ := stays_old ha hab
  have hbb : b = b' := Sum.inl.inj he
  simpa only [hbb] using hp

theorem no_resurrection
    (h : FrontierValid (Glue R S e J) (Sum.elim ca cb) Sum.inr) :
    ∀ a, ¬ Touches R e a → ∀ b, ca a ≠ cb b := by
  intro a ha b hc
  have hab := h (.inl a) (.inr b) hc (not_touches_glue ha)
  obtain ⟨b', he, _⟩ := stays_old ha hab
  cases he

theorem frontier_valid_compressed
    (h : FrontierValid (Glue R S e J) (Sum.elim ca cb) Sum.inr) :
    FrontierValid (Compressed R S e J) (Sum.elim (ca ∘ e) cb) Sum.inr := by
  intro x y hc hx
  have hcx : Sum.elim ca cb (embed e x) = Sum.elim ca cb (embed e y) := by
    cases x <;> cases y <;> exact hc
  have hnot : ¬ Touches (Glue R S e J) Sum.inr (embed e x) := by
    intro ht
    exact hx ((touches_compression x).mp ht)
  exact compress (h (embed e x) (embed e y) hcx hnot)

theorem frontier_valid_glue
    (hR : ∀ ⦃a b⦄, R a b → R b a)
    (hcolor : ∀ a b, R a b → ca a = ca b)
    (hold : FrontierValid R ca e)
    (hclosed : ∀ a, ¬ Touches R e a → ∀ b, ca a ≠ cb b)
    (hsmall : FrontierValid (Compressed R S e J) (Sum.elim (ca ∘ e) cb) Sum.inr) :
    FrontierValid (Glue R S e J) (Sum.elim ca cb) Sum.inr := by
  intro x y hc hx
  cases x with
  | inr b => exact (hx ⟨b, .refl⟩).elim
  | inl a =>
    by_cases ha : Touches R e a
    · obtain ⟨i, hai⟩ := ha
      have hci : ca a = ca (e i) := reach_color hcolor hai
      have hi : ¬ Touches (Compressed R S e J) Sum.inr (.inl i) := by
        rintro ⟨b, hib⟩
        exact hx ⟨b, (lift_old hai).trans (expand hib)⟩
      cases y with
      | inl b =>
        by_cases hb : Touches R e b
        · obtain ⟨j, hbj⟩ := hb
          have hcj : ca b = ca (e j) := reach_color hcolor hbj
          have hij := hsmall (.inl i) (.inl j) (hci.symm.trans (hc.trans hcj)) hi
          exact (lift_old hai).trans ((expand hij).trans (lift_old (reach_symm hR hbj)))
        · have hba := hold b a hc.symm hb
          exact (hb ⟨i, hba.trans hai⟩).elim
      | inr b =>
        have hib := hsmall (.inl i) (.inr b) (hci.symm.trans hc) hi
        exact (lift_old hai).trans (expand hib)
    · cases y with
      | inl b => exact lift_old (hold a b hc ha)
      | inr b => exact (hclosed a ha b hc).elim

/-- The connectivity invariant has an exact one-row transition rule. -/
theorem frontier_valid_glue_iff
    (hR : ∀ ⦃a b⦄, R a b → R b a) (hcolor : ∀ a b, R a b → ca a = ca b) :
    FrontierValid (Glue R S e J) (Sum.elim ca cb) Sum.inr ↔
      FrontierValid R ca e ∧
      (∀ a, ¬ Touches R e a → ∀ b, ca a ≠ cb b) ∧
      FrontierValid (Compressed R S e J) (Sum.elim (ca ∘ e) cb) Sum.inr := by
  constructor
  · intro h
    exact ⟨frontier_valid_old h, no_resurrection h, frontier_valid_compressed h⟩
  · rintro ⟨hold, hclosed, hsmall⟩
    exact frontier_valid_glue hR hcolor hold hclosed hsmall

/-- Under the prefix invariant, a closed color is exactly a used color absent
from the frontier. This is the finite state's `done` bit. -/
theorem closed_color_iff (h : FrontierValid R ca e)
    (hcolor : ∀ a b, R a b → ca a = ca b) (v : C) :
    (∃ a, ca a = v ∧ ¬ Touches R e a) ↔
      (∃ a, ca a = v) ∧ ∀ i, ca (e i) ≠ v := by
  constructor
  · rintro ⟨a, ha, hclosed⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    intro i hi
    exact hclosed ⟨i, h a (e i) (ha.trans hi.symm) hclosed⟩
  · rintro ⟨⟨a, ha⟩, hnone⟩
    refine ⟨a, ha, ?_⟩
    rintro ⟨i, hai⟩
    exact hnone i ((reach_color hcolor hai).symm.trans ha)

/-- The `done` update: a color was already closed, or an old frontier
component of that color loses its last contact with the new frontier. -/
theorem closed_color_glue_iff
    (hcolor : ∀ a b, R a b → ca a = ca b) (v : C) :
    (∃ x, Sum.elim ca cb x = v ∧
      ¬ Touches (Glue R S e J) Sum.inr x) ↔
      (∃ a, ca a = v ∧ ¬ Touches R e a) ∨
      ∃ i, ca (e i) = v ∧ ¬ Touches (Compressed R S e J) Sum.inr (.inl i) := by
  constructor
  · rintro ⟨x, hx, hclosed⟩
    cases x with
    | inr b => exact (hclosed ⟨b, .refl⟩).elim
    | inl a =>
      by_cases ha : Touches R e a
      · obtain ⟨i, hai⟩ := ha
        refine Or.inr ⟨i, (reach_color hcolor hai).symm.trans hx, ?_⟩
        rintro ⟨b, hib⟩
        exact hclosed ⟨b, (lift_old hai).trans (expand hib)⟩
      · exact Or.inl ⟨a, hx, ha⟩
  · rintro (⟨a, ha, hclosed⟩ | ⟨i, hi, hclosed⟩)
    · exact ⟨.inl a, ha, not_touches_glue hclosed⟩
    · refine ⟨.inl (e i), hi, ?_⟩
      intro ht
      exact hclosed ((touches_compression (.inl i)).mp ht)

theorem no_resurrection_iff :
    (∀ a, ¬ Touches R e a → ∀ b, ca a ≠ cb b) ↔
      ∀ b, ¬ ∃ a, ca a = cb b ∧ ¬ Touches R e a := by
  constructor
  · rintro h b ⟨a, ha, hclosed⟩
    exact h a hclosed b ha
  · intro h a hclosed b heq
    exact h b ⟨a, heq, hclosed⟩

/-- On the eight-node graph, only an old node can miss the new frontier.
The invariant is exactly the explicit closed-component condition in StepOK. -/
theorem frontier_valid_sum_iff {T : I ⊕ B → I ⊕ B → Prop} {ci : I → C} :
    FrontierValid T (Sum.elim ci cb) Sum.inr ↔
      ∀ i, ¬ Touches T Sum.inr (.inl i) →
        (∀ j, ci j = ci i → ReflTransGen T (.inl i) (.inl j)) ∧
        (∀ b, cb b ≠ ci i) := by
  constructor
  · intro h i hi
    refine ⟨fun j hj => h (.inl i) (.inl j) hj.symm hi, ?_⟩
    intro b hb
    exact hi ⟨b, h (.inl i) (.inr b) hb.symm hi⟩
  · intro h x y hc hx
    cases x with
    | inr b => exact (hx ⟨b, .refl⟩).elim
    | inl i =>
      cases y with
      | inl j => exact (h i hx).1 j hc.symm
      | inr b => exact ((h i hx).2 b hc.symm).elim

/-- At the final row, the remaining components must be connected by color. -/
theorem all_connected_iff_frontier
    (hR : ∀ ⦃a b⦄, R a b → R b a) (hcolor : ∀ a b, R a b → ca a = ca b) :
    (∀ a b, ca a = ca b → ReflTransGen R a b) ↔
      FrontierValid R ca e ∧
      (∀ i j, ca (e i) = ca (e j) → ReflTransGen R (e i) (e j)) := by
  constructor
  · intro h
    exact ⟨fun a b hc _ => h a b hc, fun i j hc => h (e i) (e j) hc⟩
  · rintro ⟨h, he⟩ a b hc
    by_cases ha : Touches R e a
    · obtain ⟨i, hai⟩ := ha
      by_cases hb : Touches R e b
      · obtain ⟨j, hbj⟩ := hb
        have hij := he i j ((reach_color hcolor hai).symm.trans
          (hc.trans (reach_color hcolor hbj)))
        exact hai.trans (hij.trans (reach_symm hR hbj))
      · exact reach_symm hR (h b a hc.symm hb)
    · exact h a b hc ha

end A165378Reach

end

/- Transport. -/
section

namespace A165378Reach

open Relation

variable {A B I C : Type*}

theorem reachable_equiv (E : A ≃ B) {R : A → A → Prop} {S : B → B → Prop}
    (hrel : ∀ a b, R a b ↔ S (E a) (E b)) (a b : A) :
    ReflTransGen R a b ↔ ReflTransGen S (E a) (E b) := by
  constructor
  · intro h
    exact h.lift E (fun u v huv => (hrel u v).mp huv)
  · intro h
    have hm := h.lift E.symm (fun u v huv => by
      apply (hrel (E.symm u) (E.symm v)).mpr
      simpa only [E.apply_symm_apply] using huv)
    simpa only [Function.onFun, E.symm_apply_apply] using hm

theorem touches_equiv (E : A ≃ B) {R : A → A → Prop} {S : B → B → Prop}
    {e : I → A} {f : I → B}
    (hrel : ∀ a b, R a b ↔ S (E a) (E b))
    (hfront : ∀ i, E (e i) = f i) (a : A) :
    Touches R e a ↔ Touches S f (E a) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← hfront i]
    exact (reachable_equiv E hrel a (e i)).mp hi
  · rintro ⟨i, hi⟩
    refine ⟨i, (reachable_equiv E hrel a (e i)).mpr ?_⟩
    simpa only [hfront i] using hi

theorem frontier_valid_equiv (E : A ≃ B)
    {R : A → A → Prop} {S : B → B → Prop}
    {ca : A → C} {cb : B → C} {e : I → A} {f : I → B}
    (hrel : ∀ a b, R a b ↔ S (E a) (E b))
    (hcolor : ∀ a, cb (E a) = ca a)
    (hfront : ∀ i, E (e i) = f i) :
    FrontierValid R ca e ↔ FrontierValid S cb f := by
  constructor
  · intro h u v hc hu
    obtain ⟨a, rfl⟩ := E.surjective u
    obtain ⟨b, rfl⟩ := E.surjective v
    apply (reachable_equiv E hrel a b).mp
    apply h a b
    · simpa only [hcolor] using hc
    · intro ht
      exact hu ((touches_equiv E hrel hfront a).mp ht)
  · intro h a b hc ha
    apply (reachable_equiv E hrel a b).mpr
    apply h (E a) (E b)
    · simpa only [hcolor] using hc
    · intro ht
      exact ha ((touches_equiv E hrel hfront a).mpr ht)

theorem closed_color_equiv (E : A ≃ B)
    {R : A → A → Prop} {S : B → B → Prop}
    {ca : A → C} {cb : B → C} {e : I → A} {f : I → B}
    (hrel : ∀ a b, R a b ↔ S (E a) (E b))
    (hcolor : ∀ a, cb (E a) = ca a)
    (hfront : ∀ i, E (e i) = f i) (v : C) :
    (∃ a, ca a = v ∧ ¬ Touches R e a) ↔
      ∃ b, cb b = v ∧ ¬ Touches S f b := by
  constructor
  · rintro ⟨a, ha, hclosed⟩
    refine ⟨E a, (hcolor a).trans ha, ?_⟩
    intro ht
    exact hclosed ((touches_equiv E hrel hfront a).mpr ht)
  · rintro ⟨b, hb, hclosed⟩
    obtain ⟨a, rfl⟩ := E.surjective b
    refine ⟨a, (hcolor a).symm.trans hb, ?_⟩
    intro ht
    exact hclosed ((touches_equiv E hrel hfront a).mp ht)

end A165378Reach

end

/- Union. -/
section

namespace A165378Proof
@[simp] theorem get_mergeLabels (lab : Labels) (edge : Node × Node) (i : Node) :
    (mergeLabels lab edge).get i =
      if lab.get i = lab.get edge.2 then lab.get edge.1 else lab.get i := by
  by_cases h : lab.get edge.1 = lab.get edge.2
  · simp only [mergeLabels, if_pos h]
    by_cases hi : lab.get i = lab.get edge.2
    · simp only [if_pos hi]
      exact hi.trans h.symm
    · simp only [if_neg hi]
  · simp only [mergeLabels, if_neg h, List.Vector.get_map]
theorem merge_preserves (lab : Labels) (e : Node × Node) {u v : Node}
    (h : lab.get u = lab.get v) :
    (mergeLabels lab e).get u = (mergeLabels lab e).get v := by
  simp only [get_mergeLabels, h]
theorem merge_connects (lab : Labels) (e : Node × Node) :
    (mergeLabels lab e).get e.1 = (mergeLabels lab e).get e.2 := by
  by_cases h : lab.get e.1 = lab.get e.2
  · simp only [get_mergeLabels, h, if_true]
  · simp only [get_mergeLabels, h, if_false, if_true]
theorem fold_preserves (lab : Labels) (es : List (Node × Node)) {u v : Node}
    (h : lab.get u = lab.get v) :
    (es.foldl mergeLabels lab).get u = (es.foldl mergeLabels lab).get v := by
  induction es generalizing lab with
  | nil => exact h
  | cons e es ih => exact ih _ (merge_preserves lab e h)
theorem fold_connects (lab : Labels) (es : List (Node × Node))
    {e : Node × Node} (he : e ∈ es) :
    (es.foldl mergeLabels lab).get e.1 = (es.foldl mergeLabels lab).get e.2 := by
  induction es generalizing lab with
  | nil => simp at he
  | cons f es ih =>
      rcases List.mem_cons.mp he with rfl | he
      · exact fold_preserves (mergeLabels lab e) es (merge_connects lab e)
      · exact ih (mergeLabels lab f) he
theorem merge_sound (R : Node → Node → Prop) (hR : Equivalence R)
    (lab : Labels) (e : Node × Node)
    (hlab : ∀ u v, lab.get u = lab.get v → R u v) (he : R e.1 e.2)
    {u v : Node} (h : (mergeLabels lab e).get u = (mergeLabels lab e).get v) : R u v := by
  simp only [get_mergeLabels] at h
  by_cases hu : lab.get u = lab.get e.2
  · by_cases hv : lab.get v = lab.get e.2
    · exact hR.trans (hlab _ _ hu) (hR.symm (hlab _ _ hv))
    · simp only [if_pos hu, if_neg hv] at h
      exact hR.trans (hlab _ _ hu) (hR.trans (hR.symm he) (hlab _ _ h))
  · by_cases hv : lab.get v = lab.get e.2
    · simp only [if_neg hu, if_pos hv] at h
      exact hR.trans (hlab _ _ h) (hR.trans he (hR.symm (hlab _ _ hv)))
    · simp only [if_neg hu, if_neg hv] at h
      exact hlab _ _ h
theorem fold_sound (R : Node → Node → Prop) (hR : Equivalence R)
    (lab : Labels) (es : List (Node × Node))
    (hlab : ∀ u v, lab.get u = lab.get v → R u v)
    (hes : ∀ e ∈ es, R e.1 e.2)
    {u v : Node} (h : (es.foldl mergeLabels lab).get u =
      (es.foldl mergeLabels lab).get v) : R u v := by
  induction es generalizing lab with
  | nil => exact hlab _ _ h
  | cons e es ih =>
      exact ih (mergeLabels lab e)
        (fun _ _ h => merge_sound R hR lab e hlab (hes e (by simp)) h)
        (fun e he => hes e (by simp [he])) h
def EdgeRel (es : List (Node × Node)) (u v : Node) : Prop :=
  (u, v) ∈ es ∨ (v, u) ∈ es
theorem closure_labels_eq_iff (es : List (Node × Node)) (u v : Node) :
    (closureLabels es).get u = (closureLabels es).get v ↔
      Relation.EqvGen (fun a b => (a, b) ∈ es) u v := by
  constructor
  · intro h
    apply fold_sound _ (Relation.EqvGen.is_equivalence _) _ es ?_ ?_ h
    · intro a b hab
      simp only [List.Vector.get_ofFn] at hab
      have : a = b := Fin.ext hab
      subst b
      exact .refl _
    · intro e he
      exact .rel _ _ he
  · intro h
    induction h with
    | rel a b hab => exact fold_connects _ es hab
    | refl => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
theorem closure_labels_iff_reachable (es : List (Node × Node)) (u v : Node) :
    (closureLabels es).get u = (closureLabels es).get v ↔
      Relation.ReflTransGen (EdgeRel es) u v := by
  rw [closure_labels_eq_iff, ← Relation.EqvGen.reflTransGen_symmGen]
  rfl
theorem linked_iff_reachable (s : State) (r : Row) (u v : Node) :
    Linked s r u v ↔ Relation.ReflTransGen (EdgeRel (stepEdges s r)) u v :=
  closure_labels_iff_reachable _ _ _
end A165378Proof

end

/- Adapter. -/
section

namespace A165378Proof

open Relation A165378Reach

def nodeEquiv : Ix ⊕ Ix ≃ Node := finSumFinEquiv

@[simp] theorem nodeEquiv_old (i : Ix) : nodeEquiv (.inl i) = old i := rfl

@[simp] theorem nodeEquiv_new (i : Ix) : nodeEquiv (.inr i) = new i := by
  apply Fin.ext
  change 4 + i.val = i.val + 4
  omega

@[simp] theorem old_inj (i j : Ix) : old i = old j ↔ i = j := by
  simp [old, Fin.ext_iff]

@[simp] theorem new_inj (i j : Ix) : new i = new j ↔ i = j := by
  simp [new, Fin.ext_iff]

@[simp] theorem old_ne_new (i j : Ix) : old i ≠ new j := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [old, new] at hval
  omega

@[simp] theorem new_ne_old (i j : Ix) : new i ≠ old j :=
  (old_ne_new j i).symm

def rowAdj (r : Row) (i j : Ix) : Prop :=
  (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ r i = r j

def crossAdj (s : State) (r : Row) (i j : Ix) : Prop :=
  i.val = j.val + 1 ∧ s.row i = r j

def LocalRel (s : State) (r : Row) : Ix ⊕ Ix → Ix ⊕ Ix → Prop
  | .inl i, .inl j => s.conn i j = true ∨ s.conn j i = true
  | .inl i, .inr j => crossAdj s r i j
  | .inr j, .inl i => crossAdj s r i j
  | .inr i, .inr j => rowAdj r i j

theorem mem_oldEdges (s : State) (u v : Node) :
    (u, v) ∈ oldEdges s ↔
      ∃ i j : Ix, s.conn i j = true ∧ old i = u ∧ old j = v := by
  simp [oldEdges, List.mem_flatMap, List.mem_filterMap]

theorem mem_horizontalEdges (r : Row) (u v : Node) :
    (u, v) ∈ horizontalEdges r ↔
      ∃ k : Fin 3, r (lo k) = r (hi k) ∧ new (lo k) = u ∧ new (hi k) = v := by
  simp [horizontalEdges, List.mem_filterMap]

theorem mem_verticalEdges (s : State) (r : Row) (u v : Node) :
    (u, v) ∈ verticalEdges s r ↔
      ∃ k : Fin 3, s.row (hi k) = r (lo k) ∧ old (hi k) = u ∧ new (lo k) = v := by
  simp [verticalEdges, List.mem_filterMap]

theorem horizontal_new_new (r : Row) (i j : Ix) :
    (new i, new j) ∈ horizontalEdges r ↔ i.val + 1 = j.val ∧ r i = r j := by
  rw [mem_horizontalEdges]
  simp only [new_inj]
  constructor
  · rintro ⟨k, hc, rfl, rfl⟩
    exact ⟨rfl, hc⟩
  · rintro ⟨hij, hc⟩
    have hik : i.val < 3 := by omega
    let k : Fin 3 := ⟨i.val, hik⟩
    have hlo : lo k = i := by apply Fin.ext; rfl
    have hhi : hi k = j := by apply Fin.ext; exact hij
    exact ⟨k, by simpa only [hlo, hhi] using hc, hlo, hhi⟩

theorem vertical_old_new (s : State) (r : Row) (i j : Ix) :
    (old i, new j) ∈ verticalEdges s r ↔ crossAdj s r i j := by
  rw [mem_verticalEdges]
  simp only [old_inj, new_inj]
  constructor
  · rintro ⟨k, hc, rfl, rfl⟩
    exact ⟨rfl, hc⟩
  · rintro ⟨hij, hc⟩
    have hjk : j.val < 3 := by omega
    let k : Fin 3 := ⟨j.val, hjk⟩
    have hlo : lo k = j := by apply Fin.ext; rfl
    have hhi : hi k = i := by apply Fin.ext; exact hij.symm
    exact ⟨k, by simpa only [hlo, hhi] using hc, hhi, hlo⟩

theorem edgeRel_nodeEquiv (s : State) (r : Row) (x y : Ix ⊕ Ix) :
    EdgeRel (stepEdges s r) (nodeEquiv x) (nodeEquiv y) ↔ LocalRel s r x y := by
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      simp [EdgeRel, stepEdges, LocalRel, mem_oldEdges, mem_verticalEdges, mem_horizontalEdges]
    | inr j =>
      simp [EdgeRel, stepEdges, LocalRel, mem_oldEdges,
        mem_horizontalEdges, mem_verticalEdges]
      simpa only [mem_verticalEdges, old_inj, new_inj] using vertical_old_new s r i j
  | inr i =>
    cases y with
    | inl j =>
      simp [EdgeRel, stepEdges, LocalRel, mem_oldEdges,
        mem_horizontalEdges, mem_verticalEdges]
      simpa only [mem_verticalEdges, old_inj, new_inj] using vertical_old_new s r j i
    | inr j =>
      simp [EdgeRel, stepEdges, LocalRel, mem_oldEdges, mem_verticalEdges,
        horizontal_new_new, rowAdj]
      constructor
      · rintro (⟨hij, hc⟩ | ⟨hji, hc⟩)
        · exact ⟨Or.inl hij, hc⟩
        · exact ⟨Or.inr hji, hc.symm⟩
      · rintro ⟨hij | hji, hc⟩
        · exact Or.inl ⟨hij, hc⟩
        · exact Or.inr ⟨hji, hc.symm⟩

theorem linked_iff_local (s : State) (r : Row) (x y : Ix ⊕ Ix) :
    Linked s r (nodeEquiv x) (nodeEquiv y) ↔ ReflTransGen (LocalRel s r) x y := by
  rw [linked_iff_reachable]
  constructor
  · intro h
    have hm := h.lift nodeEquiv.symm (fun u v huv => by
      have he := (edgeRel_nodeEquiv s r (nodeEquiv.symm u) (nodeEquiv.symm v)).mp
        (by simpa using huv)
      exact he)
    simpa only [Function.onFun, Equiv.symm_apply_apply] using hm
  · intro h
    exact h.lift nodeEquiv (fun u v huv => (edgeRel_nodeEquiv s r u v).mpr huv)

theorem linked_iff_compressed {A : Type*} (R : A → A → Prop) (e : Ix → A)
    (s : State) (r : Row)
    (hR : ∀ ⦃a b⦄, R a b → R b a)
    (hconn : ∀ i j, s.conn i j = true ↔ ReflTransGen R (e i) (e j))
    (x y : Ix ⊕ Ix) :
    Linked s r (nodeEquiv x) (nodeEquiv y) ↔
      ReflTransGen (Compressed R (rowAdj r) e (crossAdj s r)) x y := by
  rw [linked_iff_local]
  have hrel : LocalRel s r = Compressed R (rowAdj r) e (crossAdj s r) := by
    funext u v
    apply propext
    cases u with
    | inl i =>
      cases v with
      | inl j =>
        change (s.conn i j = true ∨ s.conn j i = true) ↔ _
        constructor
        · rintro (h | h)
          · exact (hconn i j).mp h
          · exact reach_symm hR ((hconn j i).mp h)
        · intro h
          exact Or.inl ((hconn i j).mpr h)
      | inr j => rfl
    | inr i => cases v <;> rfl
  rw [hrel]

def projectNode (u : Node) : Ix := ⟨u.val % 4, Nat.mod_lt _ (by decide)⟩

@[simp] theorem project_new (i : Ix) : projectNode (new i) = i := by
  apply Fin.ext
  dsimp [projectNode, new]
  omega

theorem horizontal_edge_project (r : Row) {u v : Node}
    (h : EdgeRel (horizontalEdges r) u v) : rowAdj r (projectNode u) (projectNode v) := by
  rcases h with h | h
  · obtain ⟨k, hc, hu, hv⟩ := (mem_horizontalEdges r u v).mp h
    rw [← hu, ← hv, project_new, project_new]
    exact ⟨Or.inl rfl, hc⟩
  · obtain ⟨k, hc, hv, hu⟩ := (mem_horizontalEdges r v u).mp h
    rw [← hu, ← hv, project_new, project_new]
    exact ⟨Or.inr rfl, hc.symm⟩

theorem horizontal_edge_lift (r : Row) {i j : Ix} (h : rowAdj r i j) :
    EdgeRel (horizontalEdges r) (new i) (new j) := by
  rcases h with ⟨hij | hji, hc⟩
  · exact Or.inl ((horizontal_new_new r i j).mpr ⟨hij, hc⟩)
  · exact Or.inr ((horizontal_new_new r j i).mpr ⟨hji, hc.symm⟩)

theorem initial_conn_correct (r : Row) (i j : Ix) :
    (initial r).conn i j = true ↔ ReflTransGen (rowAdj r) i j := by
  simp only [initial, decide_eq_true_eq]
  rw [closure_labels_iff_reachable]
  constructor
  · intro h
    have hp := h.lift projectNode (fun _ _ huv => horizontal_edge_project r huv)
    simpa only [Function.onFun, project_new] using hp
  · intro h
    exact h.lift new (fun _ _ hij => horizontal_edge_lift r hij)

end A165378Proof

end

/- PackCore. -/
section

namespace A165378Proof

/-- Eight base-eight labels, with the zeroth label in the lowest digit. -/
def packLabels (lab : Labels) : ℕ :=
  lab.get 0 + 8 * (lab.get 1 + 8 * (lab.get 2 + 8 * (lab.get 3 +
    8 * (lab.get 4 + 8 * (lab.get 5 + 8 * (lab.get 6 + 8 * lab.get 7))))))

def unpack (code : ℕ) (i : Node) : ℕ := code / 8 ^ i.val % 8

theorem unpack_lt (code : ℕ) (i : Node) : unpack code i < 8 :=
  Nat.mod_lt _ (by decide)

theorem digit8_succ (a b k : ℕ) (ha : a < 8) :
    (a + 8 * b) / 8 ^ (k + 1) % 8 = b / 8 ^ k % 8 := by
  rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem unpack_pack (lab : Labels) (h : ∀ i, lab.get i < 8) (i : Node) :
    unpack (packLabels lab) i = lab.get i := by
  fin_cases i
  · change packLabels lab / 8 ^ 0 % 8 = lab.get 0
    unfold packLabels
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0)]
  · change packLabels lab / 8 ^ 1 % 8 = lab.get 1
    unfold packLabels
    rw [digit8_succ _ _ 0 (h 0)]
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 1)]
  · change packLabels lab / 8 ^ 2 % 8 = lab.get 2
    unfold packLabels
    rw [digit8_succ _ _ 1 (h 0), digit8_succ _ _ 0 (h 1)]
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 2)]
  · change packLabels lab / 8 ^ 3 % 8 = lab.get 3
    unfold packLabels
    rw [digit8_succ _ _ 2 (h 0), digit8_succ _ _ 1 (h 1), digit8_succ _ _ 0 (h 2)]
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 3)]
  · change packLabels lab / 8 ^ 4 % 8 = lab.get 4
    unfold packLabels
    rw [digit8_succ _ _ 3 (h 0), digit8_succ _ _ 2 (h 1), digit8_succ _ _ 1 (h 2), digit8_succ _ _ 0 (h 3)]
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 4)]
  · change packLabels lab / 8 ^ 5 % 8 = lab.get 5
    unfold packLabels
    rw [digit8_succ _ _ 4 (h 0), digit8_succ _ _ 3 (h 1), digit8_succ _ _ 2 (h 2), digit8_succ _ _ 1 (h 3), digit8_succ _ _ 0 (h 4)]
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 5)]
  · change packLabels lab / 8 ^ 6 % 8 = lab.get 6
    unfold packLabels
    rw [digit8_succ _ _ 5 (h 0), digit8_succ _ _ 4 (h 1), digit8_succ _ _ 3 (h 2), digit8_succ _ _ 2 (h 3), digit8_succ _ _ 1 (h 4), digit8_succ _ _ 0 (h 5)]
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 6)]
  · change packLabels lab / 8 ^ 7 % 8 = lab.get 7
    unfold packLabels
    rw [digit8_succ _ _ 6 (h 0), digit8_succ _ _ 5 (h 1), digit8_succ _ _ 4 (h 2), digit8_succ _ _ 3 (h 3), digit8_succ _ _ 2 (h 4), digit8_succ _ _ 1 (h 5), digit8_succ _ _ 0 (h 6)]
    simp only [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt (h 7)]

theorem packLabels_lt (lab : Labels) (h : ∀ i, lab.get i < 8) :
    packLabels lab < 8 ^ 8 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  change lab.get 0 + 8 * (lab.get 1 + 8 * (lab.get 2 + 8 * (lab.get 3 +
    8 * (lab.get 4 + 8 * (lab.get 5 + 8 * (lab.get 6 + 8 * lab.get 7)))))) < 16777216
  omega

theorem merge_labels_lt (lab : Labels) (e : Node × Node)
    (h : ∀ i, lab.get i < 8) : ∀ i, (mergeLabels lab e).get i < 8 := by
  intro i
  rw [get_mergeLabels]
  split <;> apply h

theorem fold_labels_lt (es : List (Node × Node)) (lab : Labels)
    (h : ∀ i, lab.get i < 8) : ∀ i, (es.foldl mergeLabels lab).get i < 8 := by
  induction es generalizing lab with
  | nil => exact h
  | cons e es ih => exact ih (mergeLabels lab e) (merge_labels_lt lab e h)

theorem closure_labels_lt (es : List (Node × Node)) (i : Node) :
    (closureLabels es).get i < 8 := by
  apply fold_labels_lt es _ _ i
  intro j
  simpa only [List.Vector.get_ofFn] using j.isLt

end A165378Proof

end

/- Packed. -/
section

namespace A165378Proof

def mergedLabels (code : ℕ) (e : Node × Node) : Labels :=
  List.Vector.ofFn fun i =>
    if unpack code i = unpack code e.2 then unpack code e.1 else unpack code i

lemma mergedLabels_bounded (code : ℕ) (e : Node × Node) :
    ∀ i, (mergedLabels code e).get i < 8 := by
  intro i
  simp only [mergedLabels, List.Vector.get_ofFn]
  split <;> exact unpack_lt _ _

/-- Merge two labels and materialize the result as one base-eight integer. -/
def mergeCode (code : ℕ) (e : Node × Node) : ℕ :=
  if unpack code e.1 = unpack code e.2 then code
  else packLabels (mergedLabels code e)

lemma unpack_mergeCode (code : ℕ) (e : Node × Node) (i : Node) :
    unpack (mergeCode code e) i =
      if unpack code i = unpack code e.2 then unpack code e.1 else unpack code i := by
  by_cases h : unpack code e.1 = unpack code e.2
  · rw [mergeCode, if_pos h]
    by_cases hi : unpack code i = unpack code e.2
    · rw [if_pos hi]
      exact hi.trans h.symm
    · rw [if_neg hi]
  · rw [mergeCode, if_neg h, unpack_pack _ (mergedLabels_bounded code e) i]
    exact List.Vector.get_ofFn _ _

lemma mergeCode_correct (code : ℕ) (lab : Labels) (e : Node × Node)
    (hrep : ∀ i, unpack code i = lab.get i) (i : Node) :
    unpack (mergeCode code e) i = (mergeLabels lab e).get i := by
  rw [unpack_mergeCode, get_mergeLabels, hrep i, hrep e.1, hrep e.2]

lemma foldCode_correct (es : List (Node × Node)) (code : ℕ) (lab : Labels)
    (hrep : ∀ i, unpack code i = lab.get i) :
    ∀ i, unpack (es.foldl mergeCode code) i = (es.foldl mergeLabels lab).get i := by
  induction es generalizing code lab with
  | nil => exact hrep
  | cons e es ih =>
    exact ih (mergeCode code e) (mergeLabels lab e)
      (mergeCode_correct code lab e hrep)

def packedClosure (es : List (Node × Node)) : ℕ :=
  es.foldl mergeCode (packLabels (List.Vector.ofFn Fin.val))

theorem packedClosure_correct (es : List (Node × Node)) (i : Node) :
    unpack (packedClosure es) i = (closureLabels es).get i := by
  unfold packedClosure closureLabels
  apply foldCode_correct
  intro j
  apply unpack_pack
  intro k
  simpa only [List.Vector.get_ofFn] using k.isLt

end A165378Proof

end

/- LabelStep. -/
section

namespace A165378Proof

abbrev LabelFn := Node → ℕ

def labelAlive (lab : LabelFn) (i : Ix) : Prop :=
  ∃ j : Ix, lab (old i) = lab (new j)
instance (lab : LabelFn) (i : Ix) : Decidable (labelAlive lab i) :=
  inferInstanceAs (Decidable (∃ j : Ix, lab (old i) = lab (new j)))

def cheapOK (s : State) (r : Row) : Prop :=
  (∀ j, s.done (r j) = false) ∧
  (∀ i, s.degree i + downDegree s r i ≤ 2) ∧
  (∀ i, newDegree s r i ≤ 2)
instance (s : State) (r : Row) : Decidable (cheapOK s r) := by
  unfold cheapOK
  infer_instance

def labelStepOK (s : State) (r : Row) (lab : LabelFn) : Prop :=
  (∀ j, s.done (r j) = false) ∧
  (∀ i, s.degree i + downDegree s r i ≤ 2) ∧
  (∀ i, newDegree s r i ≤ 2) ∧
  ∀ i, ¬ labelAlive lab i →
    (∀ j, s.row j = s.row i → lab (old i) = lab (old j)) ∧
    (∀ j, r j ≠ s.row i)
instance (s : State) (r : Row) (lab : LabelFn) : Decidable (labelStepOK s r lab) := by
  unfold labelStepOK
  infer_instance

def labelNext (s : State) (r : Row) (lab : LabelFn) : State where
  row := r
  degree := newDegree s r
  conn := fun i j => decide (lab (new i) = lab (new j))
  done := fun v => s.done v || decide (∃ i, s.row i = v ∧ ¬ labelAlive lab i)

def labelStep (s : State) (r : Row) (lab : LabelFn) : Option State :=
  if labelStepOK s r lab then some (labelNext s r lab) else none

theorem labelStep_eq_step (s : State) (r : Row) :
    labelStep s r (fun i => (closureLabels (stepEdges s r)).get i) = step s r := by
  rfl

theorem step_none_of_not_cheapOK (s : State) (r : Row) (h : ¬ cheapOK s r) :
    step s r = none := by
  have hn : ¬ StepOK s r := fun hs => h ⟨hs.1, hs.2.1, hs.2.2.1⟩
  simp [step, hn]

def forceNat {α : Type*} (f : ℕ → α) : ℕ → α
  | 0 => f 0
  | n + 1 => f (n + 1)

theorem forceNat_eq {α : Type*} (f : ℕ → α) (n : ℕ) : forceNat f n = f n := by
  cases n <;> rfl

def codedStep (encode : List (Node × Node) → ℕ) (decode : ℕ → LabelFn)
    (s : State) (r : Row) : Option State :=
  if cheapOK s r then
    forceNat (fun code => labelStep s r (decode code)) (encode (stepEdges s r))
  else none

theorem codedStep_eq_step (encode : List (Node × Node) → ℕ) (decode : ℕ → LabelFn)
    (hcode : ∀ es i, decode (encode es) i = (closureLabels es).get i)
    (s : State) (r : Row) : codedStep encode decode s r = step s r := by
  unfold codedStep
  by_cases h : cheapOK s r
  · rw [if_pos h, forceNat_eq]
    have hl : decode (encode (stepEdges s r)) =
        fun i => (closureLabels (stepEdges s r)).get i := funext (hcode _)
    rw [hl, labelStep_eq_step]
  · rw [if_neg h, step_none_of_not_cheapOK s r h]

end A165378Proof

end

/- Fast. -/
section

namespace A165378Proof

def fastStep (s : State) (r : Row) : Option State :=
  codedStep packedClosure unpack s r

theorem fastStep_eq_step (s : State) (r : Row) : fastStep s r = step s r :=
  codedStep_eq_step packedClosure unpack packedClosure_correct s r

end A165378Proof

end

/- Bounds. -/
section

namespace A165378Proof

theorem horizontalDegree_le_two (r : Row) (i : Ix) : horizontalDegree r i ≤ 2 := by
  have bound : ∀ k : Ix,
      (Finset.univ.filter fun j : Ix => k.val + 1 = j.val ∨ j.val + 1 = k.val).card ≤ 2 := by
    decide
  calc
    horizontalDegree r i ≤
        (Finset.univ.filter fun j : Ix => i.val + 1 = j.val ∨ j.val + 1 = i.val).card := by
      apply Finset.card_le_card
      intro j hj
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2.1⟩
    _ ≤ 2 := bound i

end A165378Proof

end

/- StateSemantics. -/
section

namespace A165378Proof

open Relation A165378Reach

variable {A : Type*} {R : A → A → Prop} {e : Ix → A}
    {ca : A → Fin 4} {s : State} {r : Row}

theorem alive_iff_touches
    (hR : ∀ ⦃a b⦄, R a b → R b a)
    (hconn : ∀ i j, s.conn i j = true ↔ ReflTransGen R (e i) (e j)) (i : Ix) :
    Alive s r i ↔ Touches (Compressed R (rowAdj r) e (crossAdj s r)) Sum.inr (.inl i) := by
  unfold Alive Touches
  apply exists_congr
  intro j
  simpa only [nodeEquiv_old, nodeEquiv_new] using
    linked_iff_compressed R e s r hR hconn (.inl i) (.inr j)

theorem next_conn_correct
    (hR : ∀ ⦃a b⦄, R a b → R b a)
    (hconn : ∀ i j, s.conn i j = true ↔ ReflTransGen R (e i) (e j)) (i j : Ix) :
    (nextState s r).conn i j = true ↔
      ReflTransGen (Glue R (rowAdj r) e (crossAdj s r)) (.inr i) (.inr j) := by
  calc
    (nextState s r).conn i j = true ↔ Linked s r (new i) (new j) := by
      simp only [nextState, decide_eq_true_eq]
    _ ↔ ReflTransGen (Compressed R (rowAdj r) e (crossAdj s r)) (.inr i) (.inr j) := by
      simpa only [nodeEquiv_new] using
        linked_iff_compressed R e s r hR hconn (.inr i) (.inr j)
    _ ↔ _ := compression.symm

theorem next_done_correct
    (hR : ∀ ⦃a b⦄, R a b → R b a)
    (hcolor : ∀ a b, R a b → ca a = ca b)
    (hrow : ∀ i, s.row i = ca (e i))
    (hconn : ∀ i j, s.conn i j = true ↔ ReflTransGen R (e i) (e j))
    (hdone : ∀ v, s.done v = true ↔ ∃ a, ca a = v ∧ ¬ Touches R e a) (v : Fin 4) :
    (nextState s r).done v = true ↔
      ∃ x, Sum.elim ca r x = v ∧
        ¬ Touches (Glue R (rowAdj r) e (crossAdj s r)) Sum.inr x := by
  simp only [nextState, Bool.or_eq_true, decide_eq_true_eq]
  rw [hdone v, closed_color_glue_iff hcolor v]
  apply or_congr Iff.rfl
  apply exists_congr
  intro i
  rw [hrow i, alive_iff_touches hR hconn i]

theorem stepOK_iff_frontier
    (hR : ∀ ⦃a b⦄, R a b → R b a)
    (hcolor : ∀ a b, R a b → ca a = ca b)
    (hold : FrontierValid R ca e)
    (hrow : ∀ i, s.row i = ca (e i))
    (hconn : ∀ i j, s.conn i j = true ↔ ReflTransGen R (e i) (e j))
    (hdone : ∀ v, s.done v = true ↔ ∃ a, ca a = v ∧ ¬ Touches R e a) :
    StepOK s r ↔
      (∀ i, s.degree i + downDegree s r i ≤ 2) ∧
      (∀ i, newDegree s r i ≤ 2) ∧
      FrontierValid (Glue R (rowAdj r) e (crossAdj s r)) (Sum.elim ca r) Sum.inr := by
  constructor
  · rintro ⟨hres, hdeg, hnew, hclose⟩
    refine ⟨hdeg, hnew, frontier_valid_glue hR hcolor hold ?_ ?_⟩
    · intro a ha j hj
      have ht : s.done (r j) = true := (hdone (r j)).mpr ⟨a, hj, ha⟩
      rw [hres j] at ht
      cases ht
    · apply frontier_valid_sum_iff.mpr
      intro i hi
      have hni : ¬ Alive s r i := by rwa [alive_iff_touches hR hconn i]
      obtain ⟨hc, hn⟩ := hclose i hni
      constructor
      · intro j hj
        have hp := hc j (by rw [hrow j, hrow i]; exact hj)
        exact (linked_iff_compressed R e s r hR hconn (.inl i) (.inl j)).mp
          (by simpa only [nodeEquiv_old] using hp)
      · intro j hj
        exact hn j (by rw [hrow i]; exact hj)
  · rintro ⟨hdeg, hnew, hfull⟩
    refine ⟨?_, hdeg, hnew, ?_⟩
    · intro j
      cases hv : s.done (r j) with
      | false => rfl
      | true =>
        obtain ⟨a, ha, hclosed⟩ := (hdone (r j)).mp hv
        exact (no_resurrection hfull a hclosed j ha).elim
    · intro i hi
      have hni : ¬ Touches (Compressed R (rowAdj r) e (crossAdj s r))
          Sum.inr (.inl i) := by rwa [← alive_iff_touches hR hconn i]
      obtain ⟨hc, hn⟩ := frontier_valid_sum_iff.mp (frontier_valid_compressed hfull) i hni
      constructor
      · intro j hj
        apply (linked_iff_compressed R e s r hR hconn (.inl i) (.inl j)).mpr
        exact hc j (by simpa only [Function.comp_apply, hrow i, hrow j] using hj)
      · intro j hj
        exact hn j (by simpa only [Function.comp_apply, hrow i] using hj)

theorem accept_iff_connected
    (hR : ∀ ⦃a b⦄, R a b → R b a)
    (hcolor : ∀ a b, R a b → ca a = ca b)
    (hold : FrontierValid R ca e)
    (hrow : ∀ i, s.row i = ca (e i))
    (hconn : ∀ i j, s.conn i j = true ↔ ReflTransGen R (e i) (e j)) :
    accept s = true ↔ s.row 0 = 2 ∧ s.row 3 = 3 ∧
      ∀ a b, ca a = ca b → ReflTransGen R a b := by
  simp only [accept, decide_eq_true_eq]
  constructor
  · rintro ⟨hleft, hright, hc⟩
    refine ⟨hleft, hright, (all_connected_iff_frontier hR hcolor).mpr ⟨hold, ?_⟩⟩
    intro i j hij
    exact (hconn i j).mp (hc i j (by rw [hrow i, hrow j]; exact hij))
  · rintro ⟨hleft, hright, hc⟩
    refine ⟨hleft, hright, ?_⟩
    intro i j hij
    exact (hconn i j).mpr (hc (e i) (e j) (by simpa only [hrow i, hrow j] using hij))

end A165378Proof

end

/- Board. -/
section

namespace A165378Board

open OMA.S_oeis_a165378 A165378Proof

def oldCell {n : ℕ} (c : Cell n) : Cell (n + 1) := (c.1.castSucc, c.2)

def lastCell {n : ℕ} (j : Ix) : Cell (n + 1) := (Fin.last n, j)

def append {n : ℕ} (f : Cell n → Fin 4) (r : Row) (c : Cell (n + 1)) : Fin 4 :=
  Fin.lastCases (r c.2) (fun i => f (i, c.2)) c.1

def cellEquiv (n : ℕ) : Cell n ⊕ Ix ≃ Cell (n + 1) where
  toFun := Sum.elim oldCell lastCell
  invFun := fun c => Fin.lastCases (.inr c.2) (fun i => .inl (i, c.2)) c.1
  left_inv := by
    intro c
    cases c <;> simp [oldCell, lastCell]
  right_inv := by
    rintro ⟨i, j⟩
    cases i using Fin.lastCases <;> simp [oldCell, lastCell]

def toWord {n : ℕ} (f : Cell n → Fin 4) : Fin n → Row := fun i j => f (i, j)

def fromWord {n : ℕ} (w : Fin n → Row) : Cell n → Fin 4 := fun c => w c.1 c.2

@[simp] theorem fromWord_toWord {n : ℕ} (f : Cell n → Fin 4) :
    fromWord (toWord f) = f := rfl

@[simp] theorem toWord_fromWord {n : ℕ} (w : Fin n → Row) :
    toWord (fromWord w) = w := rfl

def boardWordEquiv (n : ℕ) : (Cell n → Fin 4) ≃ (Fin n → Row) where
  toFun := toWord
  invFun := fromWord
  left_inv := fromWord_toWord
  right_inv := toWord_fromWord

@[simp] theorem append_old {n : ℕ} (f : Cell n → Fin 4) (r : Row) (c : Cell n) :
    append f r (oldCell c) = f c := by
  simp [append, oldCell]

@[simp] theorem append_last {n : ℕ} (f : Cell n → Fin 4) (r : Row) (j : Ix) :
    append f r (lastCell j) = r j := by
  simp [append, lastCell]

theorem neighbors_old {n : ℕ} (c d : Cell n) :
    neighbors (oldCell c) (oldCell d) ↔ neighbors c d := by
  simp [neighbors, absCol, oldCell]

theorem neighbors_last {n : ℕ} (i j : Ix) :
    neighbors (lastCell (n := n) i) (lastCell j) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp [neighbors, absCol, lastCell]

theorem neighbors_old_last {n : ℕ} (c : Cell n) (j : Ix) :
    neighbors (oldCell c) (lastCell j) ↔
      c.1.val + 1 = n ∧ c.2.val = j.val + 1 := by
  have hc := c.1.isLt
  simp only [neighbors, oldCell, lastCell, absCol, Fin.val_castSucc, Fin.val_last,
    Fin.ext_iff]
  omega

theorem neighbors_last_old {n : ℕ} (c : Cell n) (j : Ix) :
    neighbors (lastCell j) (oldCell c) ↔
      c.1.val + 1 = n ∧ c.2.val = j.val + 1 := by
  have hc := c.1.isLt
  simp only [neighbors, oldCell, lastCell, absCol, Fin.val_castSucc, Fin.val_last,
    Fin.ext_iff]
  omega

theorem card_filter_cells {n : ℕ} (P : Cell (n + 1) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter fun c : Cell n => P (oldCell c)).card +
      (Finset.univ.filter fun j : Ix => P (lastCell j)).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]
  rfl

theorem neighborSame_append_old {n : ℕ} (f : Cell n → Fin 4) (r : Row) (c : Cell n) :
    neighborSame (append f r) (oldCell c) = neighborSame f c +
      (Finset.univ.filter fun j : Ix =>
        c.1.val + 1 = n ∧ c.2.val = j.val + 1 ∧ f c = r j).card := by
  classical
  unfold neighborSame
  rw [card_filter_cells]
  congr 1
  · congr 1
    ext d
    simp [neighbors_old]
  · congr 1
    ext j
    simp [neighbors_old_last, and_assoc, eq_comm]

def lastRow {n : ℕ} (f : Cell (n + 1) → Fin 4) : Row := fun j => f (lastCell j)

theorem cell_eq_last {n : ℕ} (c : Cell (n + 1)) (hc : c.1.val = n) :
    c = lastCell c.2 := by
  exact Prod.ext (Fin.ext hc) rfl

theorem neighborSame_append_frontier {n : ℕ} (f : Cell (n + 1) → Fin 4)
    (r : Row) (s : State) (hrow : s.row = lastRow f) (i : Ix) :
    neighborSame (append f r) (oldCell (lastCell i)) =
      neighborSame f (lastCell i) + downDegree s r i := by
  classical
  rw [neighborSame_append_old]
  congr 1
  unfold downDegree
  congr 1
  ext j
  simp [lastCell, hrow, lastRow]

theorem neighborSame_append_interior {n : ℕ} (f : Cell n → Fin 4)
    (r : Row) (c : Cell n) (hc : c.1.val + 1 ≠ n) :
    neighborSame (append f r) (oldCell c) = neighborSame f c := by
  classical
  rw [neighborSame_append_old]
  simp [hc]

theorem neighborSame_le_append {n : ℕ} (f : Cell n → Fin 4)
    (r : Row) (c : Cell n) :
    neighborSame f c ≤ neighborSame (append f r) (oldCell c) := by
  rw [neighborSame_append_old]
  omega

theorem card_filter_last {n : ℕ} (P : Ix → Prop) [DecidablePred P] :
    (Finset.univ.filter fun c : Cell (n + 1) => c.1.val = n ∧ P c.2).card =
      (Finset.univ.filter P).card := by
  rw [card_filter_cells]
  have hzero : ∀ c : Cell n, ¬ (c.1.val = n ∧ P c.2) := by
    intro c h
    exact (Nat.ne_of_lt c.1.isLt) h.1
  simp [oldCell, lastCell, hzero]

theorem neighborSame_append_new {n : ℕ} (f : Cell (n + 1) → Fin 4)
    (r : Row) (s : State) (hrow : s.row = lastRow f) (i : Ix) :
    neighborSame (append f r) (lastCell i) = newDegree s r i := by
  classical
  unfold neighborSame
  rw [card_filter_cells]
  have hold : (Finset.univ.filter fun c : Cell (n + 1) =>
      neighbors (lastCell i) (oldCell c) ∧ append f r (oldCell c) =
        append f r (lastCell i)).card = upDegree s r i := by
    have he : (Finset.univ.filter fun c : Cell (n + 1) =>
        neighbors (lastCell i) (oldCell c) ∧ append f r (oldCell c) =
          append f r (lastCell i)) =
        Finset.univ.filter (fun c : Cell (n + 1) =>
          c.1.val = n ∧ (c.2.val = i.val + 1 ∧ s.row c.2 = r i)) := by
      apply Finset.filter_congr
      intro c hc
      rw [neighbors_last_old, append_old, append_last]
      constructor
      · rintro ⟨⟨hcrow, hcol⟩, hcolor⟩
        have hec := cell_eq_last c (show c.1.val = n by omega)
        refine ⟨by omega, hcol, ?_⟩
        simpa [hrow, lastRow, ← hec] using hcolor
      · rintro ⟨hcrow, hcol, hcolor⟩
        refine ⟨⟨by omega, hcol⟩, ?_⟩
        have hec := cell_eq_last c hcrow
        simpa [hrow, lastRow, ← hec] using hcolor
    rw [he]
    exact card_filter_last (n := n) (fun j : Ix => j.val = i.val + 1 ∧ s.row j = r i)
  have hnew : (Finset.univ.filter fun j : Ix =>
      neighbors (lastCell (n := n + 1) i) (lastCell j) ∧ append f r (lastCell j) =
        append f r (lastCell i)).card = horizontalDegree r i := by
    unfold horizontalDegree
    congr 1
    ext j
    simp [neighbors_last, eq_comm]
  rw [hold, hnew, newDegree]
  omega

theorem card_eq_wordCount {n : ℕ}
    (h : ∀ f : Cell n → Fin 4, Valid n f ↔ GoodWord (toWord f)) :
    Nat.card {f : Cell n → Fin 4 // Valid n f} = wordCount n := by
  let e : {f : Cell n → Fin 4 // Valid n f} ≃
      {w : Fin n → Row // GoodWord w} :=
    { toFun := fun f => ⟨toWord f.val, (h f.val).mp f.property⟩
      invFun := fun w => ⟨fromWord w.val, (h _).mpr (by simpa using w.property)⟩
      left_inv := by intro f; apply Subtype.ext; rfl
      right_inv := by intro w; apply Subtype.ext; rfl }
  exact Nat.card_congr e

end A165378Board

end

/- BoardGraph. -/
section

namespace A165378Board

open OMA.S_oeis_a165378 A165378Proof A165378Reach Relation

@[simp] theorem cellEquiv_inl {n : ℕ} (c : Cell n) :
    cellEquiv n (.inl c) = oldCell c := rfl

@[simp] theorem cellEquiv_inr {n : ℕ} (j : Ix) :
    cellEquiv n (.inr j) = lastCell j := rfl

theorem neighbors_symm {n : ℕ} {c d : Cell n} (h : neighbors c d) : neighbors d c := by
  rcases h with ⟨hr, hc⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩
  · exact Or.inl ⟨hr.symm, hc.symm⟩
  · exact Or.inr (Or.inr ⟨hr, hc.symm⟩)
  · exact Or.inr (Or.inl ⟨hr, hc.symm⟩)

theorem sameAdj_symm {n : ℕ} (f : Cell n → Fin 4) {c d : Cell n}
    (h : sameAdj f c d) : sameAdj f d c :=
  ⟨neighbors_symm h.1, h.2.symm⟩

theorem append_cellEquiv {n : ℕ} (f : Cell n → Fin 4) (r : Row) (x : Cell n ⊕ Ix) :
    append f r (cellEquiv n x) = Sum.elim f r x := by
  cases x <;> simp

theorem sameAdj_append_glue {n : ℕ} (f : Cell (n + 1) → Fin 4)
    (r : Row) (s : State) (hrow : s.row = lastRow f)
    (x y : Cell (n + 1) ⊕ Ix) :
    sameAdj (append f r) (cellEquiv (n + 1) x) (cellEquiv (n + 1) y) ↔
      Glue (sameAdj f) (rowAdj r) lastCell (crossAdj s r) x y := by
  cases x with
  | inl c =>
    cases y with
    | inl d => simp [Glue, sameAdj, neighbors_old]
    | inr j =>
      simp only [cellEquiv_inl, cellEquiv_inr, sameAdj, neighbors_old_last,
        append_old, append_last, Glue]
      constructor
      · rintro ⟨⟨hc, hj⟩, hcolor⟩
        have he : c = lastCell c.2 := cell_eq_last c (by omega)
        refine ⟨c.2, he.symm, hj, ?_⟩
        simpa [hrow, lastRow, ← he] using hcolor
      · rintro ⟨i, he, hi, hcolor⟩
        subst c
        refine ⟨⟨by simp [lastCell], hi⟩, ?_⟩
        simpa [hrow, lastRow] using hcolor
  | inr i =>
    cases y with
    | inl c =>
      simp only [cellEquiv_inl, cellEquiv_inr, sameAdj, neighbors_last_old,
        append_old, append_last, Glue]
      constructor
      · rintro ⟨⟨hc, hj⟩, hcolor⟩
        have he : c = lastCell c.2 := cell_eq_last c (by omega)
        refine ⟨c.2, he.symm, hj, ?_⟩
        simpa [hrow, lastRow, ← he] using hcolor.symm
      · rintro ⟨j, he, hj, hcolor⟩
        subst c
        refine ⟨⟨by simp [lastCell], hj⟩, ?_⟩
        simpa [hrow, lastRow] using hcolor.symm
    | inr j => simp [Glue, sameAdj, neighbors_last, rowAdj]

def single (r : Row) : Cell 1 → Fin 4 := fun c => r c.2

def singleEquiv : Ix ≃ Cell 1 where
  toFun := lastCell
  invFun := Prod.snd
  left_inv := fun _ => rfl
  right_inv := by
    intro c
    apply Prod.ext
    · apply Fin.ext
      have hc := c.1.isLt
      dsimp [lastCell]
      omega
    · rfl

@[simp] theorem singleEquiv_apply (i : Ix) : singleEquiv i = lastCell i := rfl

@[simp] theorem lastRow_single (r : Row) : lastRow (single r) = r := rfl

@[simp] theorem single_apply (r : Row) (i : Ix) : single r (singleEquiv i) = r i := rfl

theorem sameAdj_single (r : Row) (i j : Ix) :
    sameAdj (single r) (singleEquiv i) (singleEquiv j) ↔ rowAdj r i j := by
  simp [sameAdj, neighbors, absCol, single, rowAdj, lastCell]

theorem neighborSame_single (r : Row) (i : Ix) :
    neighborSame (single r) (lastCell i) = horizontalDegree r i := by
  classical
  unfold neighborSame
  rw [card_filter_cells (n := 0)]
  simp [single, horizontalDegree, neighbors, absCol, eq_comm, lastCell]

@[simp] theorem lastRow_append {n : ℕ} (f : Cell n → Fin 4) (r : Row) :
    lastRow (append f r) = r := by
  funext i
  simp [lastRow]

theorem ofFn_toWord_single (r : Row) : List.ofFn (toWord (single r)) = [r] := by
  change List.ofFn (fun _ : Fin 1 => r) = [r]
  simp

theorem ofFn_toWord_append {n : ℕ} (f : Cell n → Fin 4) (r : Row) :
    List.ofFn (toWord (append f r)) = List.ofFn (toWord f) ++ [r] := by
  rw [List.ofFn_succ_last]
  have hfirst : (fun i : Fin n => toWord (append f r) i.castSucc) = toWord f := by
    funext i j
    exact append_old f r (i, j)
  have hlast : toWord (append f r) (Fin.last n) = r := by
    funext j
    exact append_last f r j
  rw [hfirst, hlast]

theorem append_restrict {n : ℕ} (f : Cell (n + 1) → Fin 4) :
    append (fun c => f (oldCell c)) (lastRow f) = f := by
  funext c
  rcases c with ⟨i, j⟩
  cases i using Fin.lastCases <;> simp [append, oldCell, lastCell, lastRow]

theorem firstRow_append {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row) :
    toWord (append f r) 0 = toWord f 0 := by
  funext j
  simpa [toWord, oldCell] using append_old f r ((0 : Fin (n + 1)), j)

theorem degrees_append_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (s : State) (hrow : s.row = lastRow f)
    (hdegree : ∀ i, s.degree i = neighborSame f (lastCell i)) :
    (∀ c, neighborSame (append f r) c ≤ 2) ↔
      (∀ c, neighborSame f c ≤ 2) ∧
      (∀ i, s.degree i + downDegree s r i ≤ 2) ∧
      (∀ i, newDegree s r i ≤ 2) := by
  constructor
  · intro h
    refine ⟨fun c => le_trans (neighborSame_le_append f r c) (h _), ?_, ?_⟩
    · intro i
      simpa only [neighborSame_append_frontier f r s hrow, hdegree i] using
        h (oldCell (lastCell i))
    · intro i
      simpa only [neighborSame_append_new f r s hrow] using h (lastCell i)
  · rintro ⟨hold, hfront, hnew⟩ c
    obtain ⟨x, rfl⟩ := (cellEquiv (n + 1)).surjective c
    cases x with
    | inl c =>
      change neighborSame (append f r) (oldCell c) ≤ 2
      by_cases hc : c.1.val = n
      · rw [cell_eq_last c hc, neighborSame_append_frontier f r s hrow]
        simpa only [hdegree c.2] using hfront c.2
      · rw [neighborSame_append_interior f r c (by omega)]
        exact hold c
    | inr i =>
      change neighborSame (append f r) (lastCell i) ≤ 2
      rw [neighborSame_append_new f r s hrow]
      exact hnew i

theorem valid_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) :
    Valid (n + 1) f ↔ TopRow (toWord f 0) ∧
      lastRow f 0 = 2 ∧ lastRow f 3 = 3 ∧
      (∀ a b, f a = f b → ReflTransGen (sameAdj f) a b) ∧
      ∀ c, neighborSame f c ≤ 2 := by
  constructor
  · rintro ⟨hn, h00, h03, hn0, hn3, hconn, hdeg⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, hdeg⟩
    · simpa [toWord] using h00
    · simpa [toWord] using h03
    · simpa [lastRow, lastCell, Fin.last] using hn0
    · simpa [lastRow, lastCell, Fin.last] using hn3
    · intro a b hab
      exact hconn (f a) a b rfl hab.symm
  · rintro ⟨⟨h00, h03⟩, hn0, hn3, hconn, hdeg⟩
    refine ⟨Nat.succ_pos n, ?_, ?_, ?_, ?_, ?_, hdeg⟩
    · simpa [toWord] using h00
    · simpa [toWord] using h03
    · simpa [lastRow, lastCell, Fin.last] using hn0
    · simpa [lastRow, lastCell, Fin.last] using hn3
    · intro v a b ha hb
      exact hconn a b (ha.trans hb.symm)

end A165378Board

end

/- RunCorrect. -/
section

namespace A165378Run

open OMA.S_oeis_a165378 A165378Proof A165378Board A165378Reach Relation

structure Tracks {n : ℕ} (f : Cell (n + 1) → Fin 4) (s : State) : Prop where
  row_eq : s.row = lastRow f
  degree_eq : ∀ i, s.degree i = neighborSame f (lastCell i)
  conn_eq : ∀ i j, s.conn i j = true ↔
    ReflTransGen (sameAdj f) (lastCell i) (lastCell j)
  done_eq : ∀ v, s.done v = true ↔
    ∃ c, f c = v ∧ ¬ Touches (sameAdj f) lastCell c

def PrefixGood {n : ℕ} (f : Cell (n + 1) → Fin 4) : Prop :=
  TopRow (toWord f 0) ∧ (∀ c, neighborSame f c ≤ 2) ∧
    FrontierValid (sameAdj f) f lastCell

theorem adj_color {n : ℕ} (f : Cell n → Fin 4) (c d : Cell n) (h : sameAdj f c d) :
    f c = f d := h.2

theorem runFrom_snoc (s : State) (rs : List Row) (r : Row) :
    runFrom s (rs ++ [r]) = (runFrom s rs).bind (fun t => step t r) := by
  simp [runFrom, List.foldl_append]

theorem run_snoc (rs : List Row) (hne : rs ≠ []) (r : Row) :
    run (rs ++ [r]) = (run rs).bind (fun t => step t r) := by
  cases rs with
  | nil => exact (hne rfl).elim
  | cons q qs =>
    by_cases hq : TopRow q <;> simp [run, hq, runFrom_snoc]

theorem word_nonempty {n : ℕ} (f : Cell (n + 1) → Fin 4) :
    List.ofFn (toWord f) ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp at hl

theorem glue_frontier_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (s : State) (hrow : s.row = lastRow f) :
    FrontierValid (Glue (sameAdj f) (rowAdj r) lastCell (crossAdj s r))
      (Sum.elim f r) Sum.inr ↔
      FrontierValid (sameAdj (append f r)) (append f r) lastCell := by
  exact frontier_valid_equiv (cellEquiv (n + 1))
    (fun x y => (sameAdj_append_glue f r s hrow x y).symm)
    (append_cellEquiv f r) (fun _ => rfl)

theorem prefix_restrict {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (h : PrefixGood (append f r)) : PrefixGood f := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [firstRow_append] using h.1
  · intro c
    exact le_trans (neighborSame_le_append f r c) (h.2.1 _)
  · have hfull := (glue_frontier_iff f r (initial (lastRow f)) rfl).mpr h.2.2
    exact frontier_valid_old hfull

theorem prefix_append_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (s : State) (hgood : PrefixGood f) (ht : Tracks f s) :
    PrefixGood (append f r) ↔ StepOK s r := by
  have hstep := stepOK_iff_frontier (r := r) (fun {_ _} h => sameAdj_symm f h) (adj_color f) hgood.2.2
    (fun i => congrFun ht.row_eq i) ht.conn_eq ht.done_eq
  constructor
  · intro h
    obtain ⟨_, hfront, hnew⟩ := (degrees_append_iff f r s ht.row_eq ht.degree_eq).mp h.2.1
    exact hstep.mpr ⟨hfront, hnew, (glue_frontier_iff f r s ht.row_eq).mpr h.2.2⟩
  · intro h
    obtain ⟨hfront, hnew, hfull⟩ := hstep.mp h
    refine ⟨?_, ?_, (glue_frontier_iff f r s ht.row_eq).mp hfull⟩
    · simpa only [firstRow_append] using hgood.1
    · exact (degrees_append_iff f r s ht.row_eq ht.degree_eq).mpr ⟨hgood.2.1, hfront, hnew⟩

theorem tracks_next {n : ℕ} (f : Cell (n + 1) → Fin 4) (r : Row)
    (s : State) (ht : Tracks f s) : Tracks (append f r) (nextState s r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [nextState, lastRow_append]
  · intro i
    exact (neighborSame_append_new f r s ht.row_eq i).symm
  · intro i j
    calc
      (nextState s r).conn i j = true ↔
          ReflTransGen (Glue (sameAdj f) (rowAdj r) lastCell (crossAdj s r))
            (.inr i) (.inr j) := next_conn_correct (fun {_ _} h => sameAdj_symm f h) ht.conn_eq i j
      _ ↔ _ := by
        simpa only [cellEquiv_inr] using reachable_equiv (cellEquiv (n + 1))
          (fun x y => (sameAdj_append_glue f r s ht.row_eq x y).symm)
          (.inr i) (.inr j)
  · intro v
    calc
      (nextState s r).done v = true ↔
          ∃ x, Sum.elim f r x = v ∧
            ¬ Touches (Glue (sameAdj f) (rowAdj r) lastCell (crossAdj s r)) Sum.inr x :=
        next_done_correct (fun {_ _} h => sameAdj_symm f h) (adj_color f)
          (fun i => congrFun ht.row_eq i) ht.conn_eq ht.done_eq v
      _ ↔ _ := closed_color_equiv (cellEquiv (n + 1))
        (fun x y => (sameAdj_append_glue f r s ht.row_eq x y).symm)
        (append_cellEquiv f r) (fun _ => rfl) v

theorem single_lastRow (f : Cell 1 → Fin 4) : single (lastRow f) = f := by
  funext c
  obtain ⟨i, rfl⟩ := singleEquiv.surjective c
  rfl

theorem initial_tracks (r : Row) : Tracks (single r) (initial r) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i
    exact (neighborSame_single r i).symm
  · intro i j
    calc
      (initial r).conn i j = true ↔ ReflTransGen (rowAdj r) i j := initial_conn_correct r i j
      _ ↔ _ := reachable_equiv singleEquiv (fun a b => (sameAdj_single r a b).symm) i j
  · intro v
    change (false = true) ↔ _
    constructor
    · intro h; cases h
    · rintro ⟨c, _, hc⟩
      obtain ⟨i, rfl⟩ := singleEquiv.surjective c
      exact (hc ⟨i, .refl⟩).elim

theorem prefix_single (r : Row) : PrefixGood (single r) ↔ TopRow r := by
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, ?_, ?_⟩
    · intro c
      obtain ⟨i, rfl⟩ := singleEquiv.surjective c
      rw [singleEquiv_apply, neighborSame_single]
      exact horizontalDegree_le_two r i
    · intro c d _ hc
      obtain ⟨i, rfl⟩ := singleEquiv.surjective c
      exact (hc ⟨i, .refl⟩).elim

theorem run_spec : ∀ (n : ℕ) (f : Cell (n + 1) → Fin 4),
    match run (List.ofFn (toWord f)) with
    | none => ¬ PrefixGood f
    | some s => PrefixGood f ∧ Tracks f s := by
  intro n
  induction n with
  | zero =>
    intro f
    rw [← single_lastRow f, ofFn_toWord_single]
    by_cases h : TopRow (lastRow f)
    · simp only [run, if_pos h, runFrom, List.foldl_nil]
      exact ⟨(prefix_single _).mpr h, initial_tracks _⟩
    · simp only [run, if_neg h]
      exact fun hp => h ((prefix_single _).mp hp)
  | succ n ih =>
    intro f
    let g : Cell (n + 1) → Fin 4 := fun c => f (oldCell c)
    let r := lastRow f
    have hf : append g r = f := append_restrict f
    rw [← hf, ofFn_toWord_append, run_snoc _ (word_nonempty g) r]
    have hg := ih g
    cases hrun : run (List.ofFn (toWord g)) with
    | none =>
      simp only [Option.bind_none]
      have hnot : ¬ PrefixGood g := by simpa only [hrun] using hg
      exact fun hp => hnot (prefix_restrict g r hp)
    | some s =>
      simp only [Option.bind_some]
      obtain ⟨hgood, ht⟩ : PrefixGood g ∧ Tracks g s := by simpa only [hrun] using hg
      by_cases hstep : StepOK s r
      · simp only [step, if_pos hstep]
        exact ⟨(prefix_append_iff g r s hgood ht).mpr hstep, tracks_next g r s ht⟩
      · simp only [step, if_neg hstep]
        exact fun hp => hstep ((prefix_append_iff g r s hgood ht).mp hp)

theorem run_tracks {n : ℕ} (f : Cell (n + 1) → Fin 4) (s : State)
    (h : run (List.ofFn (toWord f)) = some s) : PrefixGood f ∧ Tracks f s := by
  simpa only [h] using run_spec n f

theorem run_success_iff {n : ℕ} (f : Cell (n + 1) → Fin 4) :
    (∃ s, run (List.ofFn (toWord f)) = some s) ↔ PrefixGood f := by
  constructor
  · rintro ⟨s, hs⟩
    exact (run_tracks f s hs).1
  · intro hp
    cases hrun : run (List.ofFn (toWord f)) with
    | none =>
      have hnot : ¬ PrefixGood f := by simpa only [hrun] using run_spec n f
      exact (hnot hp).elim
    | some s => exact ⟨s, rfl⟩

theorem valid_prefix {n : ℕ} (f : Cell (n + 1) → Fin 4) (h : Valid (n + 1) f) :
    PrefixGood f := by
  obtain ⟨htop, _, _, hc, hdeg⟩ := (valid_iff f).mp h
  exact ⟨htop, hdeg, ((all_connected_iff_frontier (e := lastCell)
    (fun {_ _} h => sameAdj_symm f h) (adj_color f)).mp hc).1⟩

theorem goodWord_iff_valid {n : ℕ} (f : Cell (n + 1) → Fin 4) :
    GoodWord (toWord f) ↔ Valid (n + 1) f := by
  cases hrun : run (List.ofFn (toWord f)) with
  | none =>
    have hnot : ¬ PrefixGood f := by simpa only [hrun] using run_spec n f
    constructor
    · intro h
      simp only [GoodWord, hrun, Option.any_none, Bool.false_eq_true] at h
    · intro hv
      exact (hnot (valid_prefix f hv)).elim
  | some s =>
    obtain ⟨hp, ht⟩ := run_tracks f s hrun
    have ha := accept_iff_connected (fun {_ _} h => sameAdj_symm f h) (adj_color f) hp.2.2
      (fun i => congrFun ht.row_eq i) ht.conn_eq
    constructor
    · intro h
      have hacc : accept s = true := by simpa only [GoodWord, hrun, Option.any_some] using h
      obtain ⟨hl, hr, hc⟩ := ha.mp hacc
      exact (valid_iff f).mpr ⟨hp.1, by simpa only [ht.row_eq] using hl,
        by simpa only [ht.row_eq] using hr, hc, hp.2.1⟩
    · intro hv
      obtain ⟨_, hl, hr, hc, _⟩ := (valid_iff f).mp hv
      have hacc : accept s = true := ha.mpr ⟨by simpa only [ht.row_eq] using hl,
        by simpa only [ht.row_eq] using hr, hc⟩
      simpa only [GoodWord, hrun, Option.any_some] using hacc

end A165378Run

end

/- Count. -/
section

namespace A165378Count

variable {S : Type*}

def paths (succ : S → List S) (accept : S → ℕ) : ℕ → S → ℕ
  | 0, s => accept s
  | n + 1, s => ((succ s).map (paths succ accept n)).sum

theorem paths_three_of_vectors (succ : S → List S) (accept v1 v2 c : S → ℕ)
    (h1 : ∀ s, ((succ s).map accept).sum = v1 s)
    (h2 : ∀ s, ((succ s).map v1).sum = v2 s)
    (h3 : ∀ s, ((succ s).map v2).sum = c s) (s : S) :
    paths succ accept 3 s = c s := by
  have hp1 : paths succ accept 1 = v1 := funext h1
  have hp2 : paths succ accept 2 = v2 := by
    funext t
    change ((succ t).map (paths succ accept 1)).sum = v2 t
    rw [hp1, h2]
  change ((succ s).map (paths succ accept 2)).sum = c s
  rw [hp2, h3]

theorem sum_quadratic (L : List S) (q l c : S → ℕ) (n : ℕ) :
    (L.map (fun s => q s * n ^ 2 + l s * n + c s)).sum =
      (L.map q).sum * n ^ 2 + (L.map l).sum * n + (L.map c).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem paths_quadratic (succ : S → List S) (accept q l c : S → ℕ)
    (hbase : ∀ s, paths succ accept 3 s = c s)
    (hq : ∀ s, ((succ s).map q).sum = q s)
    (hl : ∀ s, ((succ s).map l).sum = l s + 2 * q s)
    (hc : ∀ s, ((succ s).map c).sum = c s + l s + q s) :
    ∀ n s, paths succ accept (n + 3) s = q s * n ^ 2 + l s * n + c s := by
  intro n
  induction n with
  | zero => intro s; simpa using hbase s
  | succ n ih =>
    intro s
    change ((succ s).map (paths succ accept (n + 3))).sum = _
    rw [show paths succ accept (n + 3) =
      (fun t => q t * n ^ 2 + l t * n + c t) from funext ih]
    rw [sum_quadratic, hq, hl, hc]
    ring

theorem initial_quadratic (succ : S → List S) (accept q l c : S → ℕ)
    (initial : List S)
    (hbase : ∀ s, paths succ accept 3 s = c s)
    (hq : ∀ s, ((succ s).map q).sum = q s)
    (hl : ∀ s, ((succ s).map l).sum = l s + 2 * q s)
    (hc : ∀ s, ((succ s).map c).sum = c s + l s + q s)
    (hiq : (initial.map q).sum = 9)
    (hil : (initial.map l).sum = 76)
    (hic : (initial.map c).sum = 158) (n : ℕ) :
    (initial.map (paths succ accept (n + 3))).sum =
      9 * (n + 4) ^ 2 + 4 * (n + 4) - 2 := by
  rw [show paths succ accept (n + 3) =
    (fun s => q s * n ^ 2 + l s * n + c s) from
      funext (paths_quadratic succ accept q l c hbase hq hl hc n)]
  rw [sum_quadratic, hiq, hil, hic]
  have heq : 9 * (n + 4) ^ 2 + 4 * (n + 4) =
      9 * n ^ 2 + 76 * n + 158 + 2 := by ring
  omega

end A165378Count

end

/- Words. -/
section

namespace A165378Proof

open scoped BigOperators

theorem card_words_succ {A : Type*} [Fintype A] (n : ℕ)
    (P : (Fin (n + 1) → A) → Prop) :
    Nat.card {w : Fin (n + 1) → A // P w} =
      ∑ a : A, Nat.card {v : Fin n → A // P (Fin.cons a v)} := by
  classical
  calc
    _ = Nat.card {p : A × (Fin n → A) // P (Fin.cons p.1 p.2)} :=
      Nat.card_congr ((Fin.consEquiv (fun _ : Fin (n + 1) => A)).symm.subtypeEquiv
        (by intro w; simp [Fin.consEquiv]))
    _ = Nat.card (Σ a : A, {v : Fin n → A // P (Fin.cons a v)}) :=
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a v => P (Fin.cons a v)))
    _ = _ := Nat.card_sigma

lemma run_fold_none (rs : List Row) :
    rs.foldl (fun so r => so.bind (fun s => step s r)) none = none := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simpa only [List.foldl_cons, Option.bind_none] using ih

lemma runFrom_cons (s : State) (r : Row) (rs : List Row) :
    runFrom s (r :: rs) = (step s r).bind (fun t => runFrom t rs) := by
  cases h : step s r with
  | none => simp [runFrom, h, run_fold_none]
  | some t => simp [runFrom, h]

lemma suffixCount_zero (s : State) :
    suffixCount s 0 = if accept s then 1 else 0 := by
  cases h : accept s <;> simp [suffixCount, runFrom, h, Nat.card_eq_fintype_card]

lemma suffixCount_succ (s : State) (n : ℕ) :
    suffixCount s (n + 1) =
      ∑ r : Row, (step s r).elim 0 (fun t => suffixCount t n) := by
  classical
  unfold suffixCount
  rw [card_words_succ]
  apply Finset.sum_congr rfl
  intro r _
  cases h : step s r with
  | none => simp [runFrom_cons, h, Nat.card_eq_fintype_card]
  | some t => simp [runFrom_cons, h]

lemma wordCount_succ (n : ℕ) :
    wordCount (n + 1) =
      ∑ r : Row, if TopRow r then suffixCount (initial r) n else 0 := by
  classical
  unfold wordCount
  rw [card_words_succ]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : TopRow r
  · simp [GoodWord, run, hr, suffixCount]
  · simp [GoodWord, run, hr, Nat.card_eq_fintype_card]

theorem sum_rows_of_equiv (e : Fin 256 ≃ Row) (f : Row → ℕ) :
    (((List.finRange 256).map e).map f).sum = ∑ r : Row, f r := by
  rw [List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  exact e.sum_comp f

lemma sum_filterMap {A B : Type*} (L : List A) (f : A → Option B) (g : B → ℕ) :
    ((L.filterMap f).map g).sum = (L.map (fun a => (f a).elim 0 g)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h : f a <;> simp [h, ih]

lemma sum_filter {A : Type*} (L : List A) (P : A → Prop) [DecidablePred P] (g : A → ℕ) :
    ((L.filter (fun a => decide (P a))).map g).sum =
      (L.map (fun a => if P a then g a else 0)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => by_cases h : P a <;> simp [h, ih]

variable {I : Type*}

theorem suffixCount_eq_paths (rows : List Row)
    (hrows : ∀ f : Row → ℕ, (rows.map f).sum = ∑ r : Row, f r)
    (state : I → State) (succ : I → List I) (accepted : I → ℕ)
    (hstep : ∀ i, rows.filterMap (step (state i)) = (succ i).map state)
    (haccept : ∀ i, (if accept (state i) then 1 else 0) = accepted i) :
    ∀ n i, suffixCount (state i) n = A165378Count.paths succ accepted n i := by
  intro n
  induction n with
  | zero => intro i; exact (suffixCount_zero _).trans (haccept i)
  | succ n ih =>
    intro i
    rw [suffixCount_succ, ← hrows, ← sum_filterMap, hstep, List.map_map]
    change ((succ i).map (fun j => suffixCount (state j) n)).sum = _
    rw [show (fun j => suffixCount (state j) n) =
        A165378Count.paths succ accepted n from funext ih]
    rfl

theorem wordCount_eq_paths (rows : List Row)
    (hrows : ∀ f : Row → ℕ, (rows.map f).sum = ∑ r : Row, f r)
    (state : I → State) (succ : I → List I) (accepted : I → ℕ) (starts : List I)
    (hstep : ∀ i, rows.filterMap (step (state i)) = (succ i).map state)
    (haccept : ∀ i, (if accept (state i) then 1 else 0) = accepted i)
    (hstart : ((rows.filter (fun r => decide (TopRow r))).map initial) =
      starts.map state) (n : ℕ) :
    wordCount (n + 1) = (starts.map (A165378Count.paths succ accepted n)).sum := by
  rw [wordCount_succ, ← hrows, ← sum_filter]
  change ((rows.filter (fun r => decide (TopRow r))).map
    ((fun t : State => suffixCount t n) ∘ initial)).sum = _
  rw [← List.map_map, hstart, List.map_map]
  change (starts.map (fun i => suffixCount (state i) n)).sum = _
  rw [show (fun i => suffixCount (state i) n) =
      A165378Count.paths succ accepted n from
    funext (suffixCount_eq_paths rows hrows state succ accepted hstep haccept n)]

end A165378Proof

end

/- Rows. -/
section

namespace A165378Proof

def rowOfCode (c : Fin 256) : Row :=
  ![⟨c.val / 64, by omega⟩,
    ⟨c.val / 16 % 4, Nat.mod_lt _ (by omega)⟩,
    ⟨c.val / 4 % 4, Nat.mod_lt _ (by omega)⟩,
    ⟨c.val % 4, Nat.mod_lt _ (by omega)⟩]

def rowCode (r : Row) : Fin 256 :=
  ⟨64 * (r 0).val + 16 * (r 1).val + 4 * (r 2).val + (r 3).val, by
    have h₀ := (r 0).isLt
    have h₁ := (r 1).isLt
    have h₂ := (r 2).isLt
    have h₃ := (r 3).isLt
    omega⟩

def rowEquiv : Fin 256 ≃ Row where
  toFun := rowOfCode
  invFun := rowCode
  left_inv := by
    intro c
    apply Fin.ext
    change 64 * (c.val / 64) + 16 * (c.val / 16 % 4) +
      4 * (c.val / 4 % 4) + c.val % 4 = c.val
    omega
  right_inv := by
    intro r
    have h₀ := (r 0).isLt
    have h₁ := (r 1).isLt
    have h₂ := (r 2).isLt
    have h₃ := (r 3).isLt
    funext i
    fin_cases i <;> apply Fin.ext <;> dsimp [rowOfCode, rowCode] <;> omega

def allRows : List Row := (List.finRange 256).map rowEquiv

theorem mem_allRows (r : Row) : r ∈ allRows := by
  exact List.mem_map.mpr ⟨rowEquiv.symm r, by simp, rowEquiv.apply_symm_apply r⟩

theorem allRows_nodup : allRows.Nodup := by
  exact (List.nodup_finRange 256).map rowEquiv.injective

end A165378Proof

end

/- Table. -/
section

namespace A165378Table

/-- A finite frontier state, decoded from four short natural-number codes. -/
def decode (r d p z : ℕ) : A165378Proof.State where
  row := fun i => ⟨r / 4 ^ i.val % 4, Nat.mod_lt _ (by decide)⟩
  degree := fun i => d / 3 ^ i.val % 3
  conn := fun i j => decide (p / 4 ^ i.val % 4 = p / 4 ^ j.val % 4)
  done := fun c => decide (z / 2 ^ c.val % 2 = 1)

/-- A closed family of 766 frontiers containing all permitted first rows.
Balanced comparisons avoid long array reductions during kernel checking. -/
def codes (i : ℕ) : ℕ × ℕ × ℕ × ℕ := (if i < 383 then (if i < 191 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then (0, 53, 0, 2) else (0, 53, 0, 6)) else (if i < 3 then (0, 53, 0, 10) else (if i < 4 then (0, 53, 0, 14) else (64, 16, 64, 0)))) else (if i < 8 then (if i < 6 then (128, 17, 64, 2) else (if i < 7 then (128, 17, 64, 10) else (128, 26, 64, 2))) else (if i < 9 then (128, 26, 64, 10) else (if i < 10 then (192, 17, 64, 2) else (192, 17, 64, 6))))) else (if i < 17 then (if i < 14 then (if i < 12 then (192, 26, 64, 2) else (if i < 13 then (192, 26, 64, 6) else (16, 14, 144, 0))) else (if i < 15 then (16, 14, 144, 4) else (if i < 16 then (16, 14, 144, 8) else (80, 40, 80, 0)))) else (if i < 20 then (if i < 18 then (80, 50, 80, 0) else (if i < 19 then (80, 50, 80, 4) else (80, 50, 80, 8))) else (if i < 21 then (144, 14, 144, 0) else (if i < 22 then (144, 14, 144, 8) else (208, 14, 144, 0)))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then (208, 14, 144, 4) else (if i < 25 then (32, 16, 144, 10) else (32, 5, 144, 2))) else (if i < 27 then (32, 5, 144, 10) else (if i < 28 then (32, 14, 144, 2) else (32, 14, 144, 10)))) else (if i < 32 then (if i < 30 then (96, 4, 144, 0) else (if i < 31 then (160, 52, 80, 10) else (160, 41, 80, 2))) else (if i < 33 then (160, 41, 80, 10) else (if i < 34 then (160, 50, 80, 2) else (160, 50, 80, 10))))) else (if i < 41 then (if i < 38 then (if i < 36 then (224, 5, 144, 2) else (if i < 37 then (224, 14, 144, 2) else (48, 16, 144, 6))) else (if i < 39 then (48, 5, 144, 2) else (if i < 40 then (48, 5, 144, 6) else (48, 14, 144, 2)))) else (if i < 44 then (if i < 42 then (48, 14, 144, 6) else (if i < 43 then (112, 4, 144, 0) else (176, 5, 144, 2))) else (if i < 45 then (176, 14, 144, 2) else (if i < 46 then (240, 52, 80, 6) else (240, 41, 80, 2))))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then (240, 41, 80, 6) else (if i < 49 then (240, 50, 80, 2) else (240, 50, 80, 6))) else (if i < 51 then (4, 40, 164, 0) else (if i < 52 then (4, 40, 164, 4) else (4, 40, 164, 8)))) else (if i < 56 then (if i < 54 then (4, 40, 164, 12) else (if i < 55 then (4, 49, 164, 0) else (4, 49, 164, 4))) else (if i < 57 then (4, 49, 164, 8) else (if i < 58 then (68, 0, 228, 0) else (68, 4, 228, 0))))) else (if i < 65 then (if i < 62 then (if i < 60 then (68, 4, 228, 4) else (if i < 61 then (68, 4, 228, 8) else (68, 4, 228, 12))) else (if i < 63 then (68, 13, 228, 0) else (if i < 64 then (68, 13, 228, 4) else (68, 13, 228, 8)))) else (if i < 68 then (if i < 66 then (132, 4, 228, 0) else (if i < 67 then (132, 4, 228, 8) else (132, 13, 228, 0))) else (if i < 69 then (132, 13, 228, 8) else (if i < 70 then (196, 4, 228, 0) else (196, 4, 228, 4)))))) else (if i < 83 then (if i < 77 then (if i < 74 then (if i < 72 then (196, 13, 228, 0) else (if i < 73 then (196, 13, 228, 4) else (20, 22, 148, 4))) else (if i < 75 then (20, 22, 148, 8) else (if i < 76 then (20, 16, 148, 4) else (20, 16, 148, 8)))) else (if i < 80 then (if i < 78 then (20, 16, 148, 12) else (if i < 79 then (20, 25, 148, 0) else (84, 48, 84, 0))) else (if i < 81 then (84, 52, 84, 4) else (if i < 82 then (84, 52, 84, 8) else (84, 52, 84, 12))))) else (if i < 89 then (if i < 86 then (if i < 84 then (148, 22, 148, 8) else (if i < 85 then (148, 16, 148, 8) else (148, 25, 148, 0))) else (if i < 87 then (212, 22, 148, 4) else (if i < 88 then (212, 16, 148, 4) else (212, 25, 148, 0)))) else (if i < 92 then (if i < 90 then (36, 4, 228, 0) else (if i < 91 then (36, 4, 228, 8) else (36, 13, 228, 0))) else (if i < 93 then (36, 13, 228, 8) else (if i < 94 then (100, 0, 228, 0) else (100, 4, 228, 0)))))))) else (if i < 143 then (if i < 119 then (if i < 107 then (if i < 101 then (if i < 98 then (if i < 96 then (100, 4, 228, 8) else (if i < 97 then (100, 13, 228, 0) else (100, 13, 228, 8))) else (if i < 99 then (164, 40, 164, 0) else (if i < 100 then (164, 40, 164, 8) else (164, 49, 164, 0)))) else (if i < 104 then (if i < 102 then (164, 49, 164, 8) else (if i < 103 then (228, 4, 228, 0) else (228, 13, 228, 0))) else (if i < 105 then (52, 4, 228, 0) else (if i < 106 then (52, 4, 228, 4) else (52, 13, 228, 0))))) else (if i < 113 then (if i < 110 then (if i < 108 then (52, 13, 228, 4) else (if i < 109 then (116, 0, 228, 0) else (116, 4, 228, 0))) else (if i < 111 then (116, 4, 228, 4) else (if i < 112 then (116, 13, 228, 0) else (116, 13, 228, 4)))) else (if i < 116 then (if i < 114 then (180, 4, 228, 0) else (if i < 115 then (180, 13, 228, 0) else (244, 40, 164, 0))) else (if i < 117 then (244, 40, 164, 4) else (if i < 118 then (244, 49, 164, 0) else (244, 49, 164, 4)))))) else (if i < 131 then (if i < 125 then (if i < 122 then (if i < 120 then (8, 45, 164, 10) else (if i < 121 then (8, 37, 164, 2) else (8, 37, 164, 10))) else (if i < 123 then (8, 46, 164, 2) else (if i < 124 then (8, 46, 164, 10) else (8, 40, 164, 2)))) else (if i < 128 then (if i < 126 then (8, 40, 164, 10) else (if i < 127 then (8, 49, 164, 2) else (8, 49, 164, 10))) else (if i < 129 then (72, 0, 228, 0) else (if i < 130 then (136, 9, 228, 10) else (136, 1, 228, 2))))) else (if i < 137 then (if i < 134 then (if i < 132 then (136, 1, 228, 10) else (if i < 133 then (136, 10, 228, 2) else (136, 10, 228, 10))) else (if i < 135 then (136, 4, 228, 2) else (if i < 136 then (136, 4, 228, 10) else (136, 13, 228, 2)))) else (if i < 140 then (if i < 138 then (136, 13, 228, 10) else (if i < 139 then (200, 1, 228, 2) else (200, 10, 228, 2))) else (if i < 141 then (200, 4, 228, 2) else (if i < 142 then (200, 13, 228, 2) else (24, 10, 228, 0))))))) else (if i < 167 then (if i < 155 then (if i < 149 then (if i < 146 then (if i < 144 then (24, 10, 228, 8) else (if i < 145 then (24, 13, 228, 0) else (88, 36, 164, 0))) else (if i < 147 then (88, 46, 164, 0) else (if i < 148 then (88, 46, 164, 8) else (88, 49, 164, 0)))) else (if i < 152 then (if i < 150 then (152, 10, 228, 0) else (if i < 151 then (152, 10, 228, 8) else (152, 13, 228, 0))) else (if i < 153 then (216, 10, 228, 0) else (if i < 154 then (216, 13, 228, 0) else (40, 13, 148, 2))))) else (if i < 161 then (if i < 158 then (if i < 156 then (40, 13, 148, 10) else (if i < 157 then (40, 22, 148, 2) else (40, 22, 148, 10))) else (if i < 159 then (40, 16, 148, 2) else (if i < 160 then (40, 16, 148, 10) else (40, 25, 148, 2)))) else (if i < 164 then (if i < 162 then (40, 25, 148, 10) else (if i < 163 then (104, 12, 148, 0) else (168, 49, 84, 2))) else (if i < 165 then (168, 49, 84, 10) else (if i < 166 then (168, 52, 84, 2) else (168, 52, 84, 10)))))) else (if i < 179 then (if i < 173 then (if i < 170 then (if i < 168 then (232, 13, 148, 2) else (if i < 169 then (232, 22, 148, 2) else (232, 16, 148, 2))) else (if i < 171 then (232, 25, 148, 2) else (if i < 172 then (56, 1, 228, 2) else (56, 10, 228, 2)))) else (if i < 176 then (if i < 174 then (56, 4, 228, 2) else (if i < 175 then (56, 13, 228, 2) else (120, 0, 228, 0))) else (if i < 177 then (184, 1, 228, 2) else (if i < 178 then (184, 10, 228, 2) else (184, 4, 228, 2))))) else (if i < 185 then (if i < 182 then (if i < 180 then (184, 13, 228, 2) else (if i < 181 then (248, 37, 164, 2) else (248, 46, 164, 2))) else (if i < 183 then (248, 40, 164, 2) else (if i < 184 then (248, 49, 164, 2) else (12, 45, 164, 6)))) else (if i < 188 then (if i < 186 then (12, 37, 164, 2) else (if i < 187 then (12, 37, 164, 6) else (12, 46, 164, 2))) else (if i < 189 then (12, 46, 164, 6) else (if i < 190 then (12, 40, 164, 2) else (12, 40, 164, 6))))))))) else (if i < 287 then (if i < 239 then (if i < 215 then (if i < 203 then (if i < 197 then (if i < 194 then (if i < 192 then (12, 49, 164, 2) else (if i < 193 then (12, 49, 164, 6) else (76, 0, 228, 0))) else (if i < 195 then (140, 1, 228, 2) else (if i < 196 then (140, 10, 228, 2) else (140, 4, 228, 2)))) else (if i < 200 then (if i < 198 then (140, 13, 228, 2) else (if i < 199 then (204, 9, 228, 6) else (204, 1, 228, 2))) else (if i < 201 then (204, 1, 228, 6) else (if i < 202 then (204, 10, 228, 2) else (204, 10, 228, 6))))) else (if i < 209 then (if i < 206 then (if i < 204 then (204, 4, 228, 2) else (if i < 205 then (204, 4, 228, 6) else (204, 13, 228, 2))) else (if i < 207 then (204, 13, 228, 6) else (if i < 208 then (28, 10, 228, 0) else (28, 10, 228, 4)))) else (if i < 212 then (if i < 210 then (28, 13, 228, 0) else (if i < 211 then (92, 36, 164, 0) else (92, 46, 164, 0))) else (if i < 213 then (92, 46, 164, 4) else (if i < 214 then (92, 49, 164, 0) else (156, 10, 228, 0)))))) else (if i < 227 then (if i < 221 then (if i < 218 then (if i < 216 then (156, 13, 228, 0) else (if i < 217 then (220, 10, 228, 0) else (220, 10, 228, 4))) else (if i < 219 then (220, 13, 228, 0) else (if i < 220 then (44, 1, 228, 2) else (44, 10, 228, 2)))) else (if i < 224 then (if i < 222 then (44, 4, 228, 2) else (if i < 223 then (44, 13, 228, 2) else (108, 0, 228, 0))) else (if i < 225 then (172, 37, 164, 2) else (if i < 226 then (172, 46, 164, 2) else (172, 40, 164, 2))))) else (if i < 233 then (if i < 230 then (if i < 228 then (172, 49, 164, 2) else (if i < 229 then (236, 1, 228, 2) else (236, 10, 228, 2))) else (if i < 231 then (236, 4, 228, 2) else (if i < 232 then (236, 13, 228, 2) else (60, 13, 148, 2)))) else (if i < 236 then (if i < 234 then (60, 13, 148, 6) else (if i < 235 then (60, 22, 148, 2) else (60, 22, 148, 6))) else (if i < 237 then (60, 16, 148, 2) else (if i < 238 then (60, 16, 148, 6) else (60, 25, 148, 2))))))) else (if i < 263 then (if i < 251 then (if i < 245 then (if i < 242 then (if i < 240 then (60, 25, 148, 6) else (if i < 241 then (124, 12, 148, 0) else (188, 13, 148, 2))) else (if i < 243 then (188, 22, 148, 2) else (if i < 244 then (188, 16, 148, 2) else (188, 25, 148, 2)))) else (if i < 248 then (if i < 246 then (252, 49, 84, 2) else (if i < 247 then (252, 49, 84, 6) else (252, 52, 84, 2))) else (if i < 249 then (252, 52, 84, 6) else (if i < 250 then (17, 12, 228, 0) else (81, 48, 164, 0))))) else (if i < 257 then (if i < 254 then (if i < 252 then (145, 12, 228, 0) else (if i < 253 then (209, 12, 228, 0) else (85, 53, 0, 5))) else (if i < 255 then (85, 53, 0, 9) else (if i < 256 then (85, 53, 0, 13) else (149, 25, 64, 1)))) else (if i < 260 then (if i < 258 then (149, 25, 64, 9) else (if i < 259 then (149, 17, 64, 9) else (149, 26, 64, 9))) else (if i < 261 then (213, 25, 64, 1) else (if i < 262 then (213, 25, 64, 5) else (213, 17, 64, 5)))))) else (if i < 275 then (if i < 269 then (if i < 266 then (if i < 264 then (213, 26, 64, 5) else (if i < 265 then (101, 7, 144, 1) else (101, 7, 144, 9))) else (if i < 267 then (101, 16, 144, 1) else (if i < 268 then (101, 16, 144, 9) else (101, 5, 144, 9)))) else (if i < 272 then (if i < 270 then (101, 14, 144, 1) else (if i < 271 then (101, 14, 144, 9) else (165, 43, 80, 1))) else (if i < 273 then (165, 43, 80, 9) else (if i < 274 then (165, 52, 80, 1) else (165, 52, 80, 9))))) else (if i < 281 then (if i < 278 then (if i < 276 then (165, 41, 80, 9) else (if i < 277 then (165, 50, 80, 1) else (165, 50, 80, 9))) else (if i < 279 then (229, 7, 144, 1) else (if i < 280 then (229, 16, 144, 1) else (229, 14, 144, 1)))) else (if i < 284 then (if i < 282 then (117, 7, 144, 1) else (if i < 283 then (117, 7, 144, 5) else (117, 16, 144, 1))) else (if i < 285 then (117, 16, 144, 5) else (if i < 286 then (117, 5, 144, 5) else (117, 14, 144, 1)))))))) else (if i < 335 then (if i < 311 then (if i < 299 then (if i < 293 then (if i < 290 then (if i < 288 then (117, 14, 144, 5) else (if i < 289 then (181, 7, 144, 1) else (181, 16, 144, 1))) else (if i < 291 then (181, 14, 144, 1) else (if i < 292 then (245, 43, 80, 1) else (245, 43, 80, 5)))) else (if i < 296 then (if i < 294 then (245, 52, 80, 1) else (if i < 295 then (245, 52, 80, 5) else (245, 41, 80, 5))) else (if i < 297 then (245, 50, 80, 1) else (if i < 298 then (245, 50, 80, 5) else (89, 45, 164, 1))))) else (if i < 305 then (if i < 302 then (if i < 300 then (89, 45, 164, 9) else (if i < 301 then (89, 48, 164, 1) else (89, 48, 164, 9))) else (if i < 303 then (89, 37, 164, 9) else (if i < 304 then (89, 46, 4, 1) else (89, 46, 164, 9)))) else (if i < 308 then (if i < 306 then (89, 40, 164, 1) else (if i < 307 then (89, 40, 164, 9) else (89, 49, 164, 1))) else (if i < 309 then (89, 49, 164, 9) else (if i < 310 then (153, 9, 228, 1) else (153, 9, 228, 9)))))) else (if i < 323 then (if i < 317 then (if i < 314 then (if i < 312 then (153, 12, 228, 1) else (if i < 313 then (153, 12, 228, 9) else (153, 1, 228, 9))) else (if i < 315 then (153, 10, 132, 1) else (if i < 316 then (153, 10, 228, 9) else (153, 4, 228, 1)))) else (if i < 320 then (if i < 318 then (153, 4, 228, 9) else (if i < 319 then (153, 13, 228, 1) else (153, 13, 228, 9))) else (if i < 321 then (217, 9, 228, 1) else (if i < 322 then (217, 12, 228, 1) else (217, 10, 132, 1))))) else (if i < 329 then (if i < 326 then (if i < 324 then (217, 4, 228, 1) else (if i < 325 then (217, 13, 228, 1) else (105, 13, 148, 1))) else (if i < 327 then (105, 13, 148, 9) else (if i < 328 then (105, 22, 148, 9) else (105, 16, 148, 9)))) else (if i < 332 then (if i < 330 then (105, 25, 148, 1) else (if i < 331 then (105, 25, 148, 9) else (169, 49, 84, 1))) else (if i < 333 then (169, 49, 84, 9) else (if i < 334 then (169, 52, 84, 9) else (233, 13, 148, 1))))))) else (if i < 359 then (if i < 347 then (if i < 341 then (if i < 338 then (if i < 336 then (233, 25, 148, 1) else (if i < 337 then (121, 1, 228, 1) else (121, 10, 228, 1))) else (if i < 339 then (121, 4, 228, 1) else (if i < 340 then (121, 13, 228, 1) else (185, 1, 228, 1)))) else (if i < 344 then (if i < 342 then (185, 10, 228, 1) else (if i < 343 then (185, 4, 228, 1) else (185, 13, 228, 1))) else (if i < 345 then (249, 37, 164, 1) else (if i < 346 then (249, 46, 164, 1) else (249, 40, 164, 1))))) else (if i < 353 then (if i < 350 then (if i < 348 then (249, 49, 164, 1) else (if i < 349 then (93, 45, 164, 1) else (93, 45, 164, 5))) else (if i < 351 then (93, 48, 164, 1) else (if i < 352 then (93, 48, 164, 5) else (93, 37, 164, 5)))) else (if i < 356 then (if i < 354 then (93, 46, 4, 1) else (if i < 355 then (93, 46, 164, 5) else (93, 40, 164, 1))) else (if i < 357 then (93, 40, 164, 5) else (if i < 358 then (93, 49, 164, 1) else (93, 49, 164, 5)))))) else (if i < 371 then (if i < 365 then (if i < 362 then (if i < 360 then (157, 9, 228, 1) else (if i < 361 then (157, 12, 228, 1) else (157, 10, 132, 1))) else (if i < 363 then (157, 4, 228, 1) else (if i < 364 then (157, 13, 228, 1) else (221, 9, 228, 1)))) else (if i < 368 then (if i < 366 then (221, 9, 228, 5) else (if i < 367 then (221, 12, 228, 1) else (221, 12, 228, 5))) else (if i < 369 then (221, 1, 228, 5) else (if i < 370 then (221, 10, 132, 1) else (221, 10, 228, 5))))) else (if i < 377 then (if i < 374 then (if i < 372 then (221, 4, 228, 1) else (if i < 373 then (221, 4, 228, 5) else (221, 13, 228, 1))) else (if i < 375 then (221, 13, 228, 5) else (if i < 376 then (109, 1, 228, 1) else (109, 10, 228, 1)))) else (if i < 380 then (if i < 378 then (109, 4, 228, 1) else (if i < 379 then (109, 13, 228, 1) else (173, 37, 164, 1))) else (if i < 381 then (173, 46, 164, 1) else (if i < 382 then (173, 40, 164, 1) else (173, 49, 164, 1)))))))))) else (if i < 574 then (if i < 478 then (if i < 430 then (if i < 406 then (if i < 394 then (if i < 388 then (if i < 385 then (if i < 384 then (237, 1, 228, 1) else (237, 10, 228, 1)) else (if i < 386 then (237, 4, 228, 1) else (if i < 387 then (237, 13, 228, 1) else (125, 13, 148, 1)))) else (if i < 391 then (if i < 389 then (125, 13, 148, 5) else (if i < 390 then (125, 22, 148, 5) else (125, 16, 148, 5))) else (if i < 392 then (125, 25, 148, 1) else (if i < 393 then (125, 25, 148, 5) else (189, 13, 148, 1))))) else (if i < 400 then (if i < 397 then (if i < 395 then (189, 25, 148, 1) else (if i < 396 then (253, 49, 84, 1) else (253, 49, 84, 5))) else (if i < 398 then (253, 52, 84, 5) else (if i < 399 then (2, 51, 84, 2) else (2, 51, 84, 10)))) else (if i < 403 then (if i < 401 then (2, 52, 84, 10) else (if i < 402 then (130, 15, 148, 2) else (130, 15, 148, 10))) else (if i < 404 then (130, 16, 148, 10) else (if i < 405 then (194, 15, 148, 2) else (18, 12, 228, 0)))))) else (if i < 418 then (if i < 412 then (if i < 409 then (if i < 407 then (82, 48, 164, 0) else (if i < 408 then (146, 12, 228, 0) else (210, 12, 228, 0))) else (if i < 410 then (34, 3, 228, 2) else (if i < 411 then (34, 3, 228, 10) else (34, 12, 228, 2)))) else (if i < 415 then (if i < 413 then (34, 12, 228, 10) else (if i < 414 then (34, 4, 228, 10) else (34, 13, 228, 2))) else (if i < 416 then (34, 13, 228, 10) else (if i < 417 then (162, 39, 164, 2) else (162, 39, 164, 10))))) else (if i < 424 then (if i < 421 then (if i < 419 then (162, 48, 164, 2) else (if i < 420 then (162, 48, 164, 10) else (162, 40, 164, 10))) else (if i < 422 then (162, 49, 164, 2) else (if i < 423 then (162, 49, 164, 10) else (226, 3, 228, 2)))) else (if i < 427 then (if i < 425 then (226, 12, 228, 2) else (if i < 426 then (226, 13, 228, 2) else (50, 3, 228, 2))) else (if i < 428 then (50, 12, 228, 2) else (if i < 429 then (50, 13, 228, 2) else (178, 3, 228, 2))))))) else (if i < 454 then (if i < 442 then (if i < 436 then (if i < 433 then (if i < 431 then (178, 12, 228, 2) else (if i < 432 then (178, 13, 228, 2) else (242, 39, 164, 2))) else (if i < 434 then (242, 48, 164, 2) else (if i < 435 then (242, 49, 164, 2) else (86, 51, 84, 9)))) else (if i < 439 then (if i < 437 then (86, 52, 84, 9) else (if i < 438 then (150, 21, 148, 1) else (150, 21, 148, 9))) else (if i < 440 then (150, 15, 148, 9) else (if i < 441 then (150, 24, 148, 1) else (150, 24, 148, 9))))) else (if i < 448 then (if i < 445 then (if i < 443 then (150, 22, 148, 1) else (if i < 444 then (150, 22, 148, 9) else (150, 16, 148, 9))) else (if i < 446 then (150, 25, 148, 1) else (if i < 447 then (214, 21, 148, 1) else (214, 24, 148, 1)))) else (if i < 451 then (if i < 449 then (214, 22, 148, 1) else (if i < 450 then (214, 25, 148, 1) else (102, 3, 228, 1))) else (if i < 452 then (102, 3, 228, 9) else (if i < 453 then (102, 12, 228, 1) else (102, 12, 228, 9)))))) else (if i < 466 then (if i < 460 then (if i < 457 then (if i < 455 then (102, 4, 228, 1) else (if i < 456 then (102, 4, 228, 9) else (102, 13, 228, 1))) else (if i < 458 then (102, 13, 228, 9) else (if i < 459 then (166, 39, 164, 1) else (166, 39, 164, 9)))) else (if i < 463 then (if i < 461 then (166, 48, 164, 1) else (if i < 462 then (166, 48, 164, 9) else (166, 40, 164, 1))) else (if i < 464 then (166, 40, 164, 9) else (if i < 465 then (166, 49, 164, 1) else (166, 49, 164, 9))))) else (if i < 472 then (if i < 469 then (if i < 467 then (230, 3, 228, 1) else (if i < 468 then (230, 12, 228, 1) else (230, 4, 228, 1))) else (if i < 470 then (230, 13, 228, 1) else (if i < 471 then (118, 3, 228, 1) else (118, 12, 228, 1)))) else (if i < 475 then (if i < 473 then (118, 4, 228, 1) else (if i < 474 then (118, 13, 228, 1) else (182, 3, 228, 1))) else (if i < 476 then (182, 12, 228, 1) else (if i < 477 then (182, 4, 228, 1) else (182, 13, 228, 1)))))))) else (if i < 526 then (if i < 502 then (if i < 490 then (if i < 484 then (if i < 481 then (if i < 479 then (246, 39, 164, 1) else (if i < 480 then (246, 48, 164, 1) else (246, 40, 164, 1))) else (if i < 482 then (246, 49, 164, 1) else (if i < 483 then (10, 49, 80, 2) else (10, 49, 80, 10)))) else (if i < 487 then (if i < 485 then (10, 50, 80, 2) else (if i < 486 then (10, 50, 80, 10) else (138, 13, 144, 2))) else (if i < 488 then (138, 13, 144, 10) else (if i < 489 then (138, 14, 144, 2) else (138, 14, 144, 10))))) else (if i < 496 then (if i < 493 then (if i < 491 then (202, 13, 144, 2) else (if i < 492 then (202, 14, 144, 2) else (90, 49, 80, 1))) else (if i < 494 then (90, 49, 80, 9) else (if i < 495 then (90, 52, 80, 1) else (90, 52, 80, 9)))) else (if i < 499 then (if i < 497 then (90, 50, 80, 1) else (if i < 498 then (90, 50, 80, 9) else (90, 53, 80, 1))) else (if i < 500 then (154, 13, 144, 1) else (if i < 501 then (154, 13, 144, 9) else (154, 16, 144, 1)))))) else (if i < 514 then (if i < 508 then (if i < 505 then (if i < 503 then (154, 16, 144, 9) else (if i < 504 then (154, 14, 144, 1) else (154, 14, 144, 9))) else (if i < 506 then (154, 17, 144, 1) else (if i < 507 then (218, 13, 144, 1) else (218, 16, 144, 1)))) else (if i < 511 then (if i < 509 then (218, 14, 144, 1) else (if i < 510 then (218, 17, 144, 1) else (170, 52, 0, 3))) else (if i < 512 then (170, 52, 0, 11) else (if i < 513 then (170, 53, 0, 3) else (170, 53, 0, 11))))) else (if i < 520 then (if i < 517 then (if i < 515 then (234, 16, 64, 3) else (if i < 516 then (234, 25, 64, 3) else (234, 17, 64, 3))) else (if i < 518 then (234, 26, 64, 3) else (if i < 519 then (186, 4, 144, 3) else (186, 13, 144, 3)))) else (if i < 523 then (if i < 521 then (186, 7, 144, 3) else (if i < 522 then (186, 16, 144, 3) else (186, 5, 144, 3))) else (if i < 524 then (186, 14, 144, 3) else (if i < 525 then (186, 8, 144, 3) else (186, 17, 144, 3))))))) else (if i < 550 then (if i < 538 then (if i < 532 then (if i < 529 then (if i < 527 then (250, 40, 80, 3) else (if i < 528 then (250, 49, 80, 3) else (250, 43, 80, 3))) else (if i < 530 then (250, 52, 80, 3) else (if i < 531 then (250, 41, 80, 3) else (250, 50, 80, 3)))) else (if i < 535 then (if i < 533 then (250, 44, 80, 3) else (if i < 534 then (250, 53, 80, 3) else (14, 45, 164, 2))) else (if i < 536 then (14, 46, 164, 2) else (if i < 537 then (142, 9, 228, 2) else (142, 10, 228, 2))))) else (if i < 544 then (if i < 541 then (if i < 539 then (206, 9, 228, 2) else (if i < 540 then (206, 10, 228, 2) else (94, 45, 164, 1))) else (if i < 542 then (94, 48, 164, 1) else (if i < 543 then (94, 46, 164, 1) else (94, 49, 164, 1)))) else (if i < 547 then (if i < 545 then (158, 9, 228, 1) else (if i < 546 then (158, 12, 228, 1) else (158, 10, 228, 1))) else (if i < 548 then (158, 13, 228, 1) else (if i < 549 then (222, 9, 228, 1) else (222, 12, 228, 1)))))) else (if i < 562 then (if i < 556 then (if i < 553 then (if i < 551 then (222, 10, 228, 1) else (if i < 552 then (222, 13, 228, 1) else (174, 36, 164, 3))) else (if i < 554 then (174, 45, 164, 3) else (if i < 555 then (174, 39, 164, 3) else (174, 48, 164, 3)))) else (if i < 559 then (if i < 557 then (174, 37, 164, 3) else (if i < 558 then (174, 46, 4, 3) else (174, 46, 164, 3))) else (if i < 560 then (174, 40, 164, 3) else (if i < 561 then (174, 49, 164, 3) else (238, 0, 228, 3))))) else (if i < 568 then (if i < 565 then (if i < 563 then (238, 9, 228, 3) else (if i < 564 then (238, 3, 228, 3) else (238, 12, 228, 3))) else (if i < 566 then (238, 1, 228, 3) else (if i < 567 then (238, 10, 132, 3) else (238, 10, 228, 3)))) else (if i < 571 then (if i < 569 then (238, 4, 228, 3) else (if i < 570 then (238, 13, 228, 3) else (190, 12, 148, 3))) else (if i < 572 then (190, 21, 148, 3) else (if i < 573 then (190, 15, 148, 3) else (190, 24, 148, 3))))))))) else (if i < 670 then (if i < 622 then (if i < 598 then (if i < 586 then (if i < 580 then (if i < 577 then (if i < 575 then (190, 13, 148, 3) else (if i < 576 then (190, 22, 148, 3) else (190, 16, 148, 3))) else (if i < 578 then (190, 25, 148, 3) else (if i < 579 then (254, 48, 84, 3) else (254, 51, 84, 3)))) else (if i < 583 then (if i < 581 then (254, 49, 84, 3) else (if i < 582 then (254, 52, 84, 3) else (3, 51, 84, 2))) else (if i < 584 then (3, 51, 84, 6) else (if i < 585 then (3, 52, 84, 6) else (131, 15, 148, 2))))) else (if i < 592 then (if i < 589 then (if i < 587 then (195, 15, 148, 2) else (if i < 588 then (195, 15, 148, 6) else (195, 16, 148, 6))) else (if i < 590 then (19, 12, 228, 0) else (if i < 591 then (83, 48, 164, 0) else (147, 12, 228, 0)))) else (if i < 595 then (if i < 593 then (211, 12, 228, 0) else (if i < 594 then (35, 3, 228, 2) else (35, 12, 228, 2))) else (if i < 596 then (35, 13, 228, 2) else (if i < 597 then (163, 39, 164, 2) else (163, 48, 164, 2)))))) else (if i < 610 then (if i < 604 then (if i < 601 then (if i < 599 then (163, 49, 164, 2) else (if i < 600 then (227, 3, 228, 2) else (227, 12, 228, 2))) else (if i < 602 then (227, 13, 228, 2) else (if i < 603 then (51, 3, 228, 2) else (51, 3, 228, 6)))) else (if i < 607 then (if i < 605 then (51, 12, 228, 2) else (if i < 606 then (51, 12, 228, 6) else (51, 4, 228, 6))) else (if i < 608 then (51, 13, 228, 2) else (if i < 609 then (51, 13, 228, 6) else (179, 3, 228, 2))))) else (if i < 616 then (if i < 613 then (if i < 611 then (179, 12, 228, 2) else (if i < 612 then (179, 13, 228, 2) else (243, 39, 164, 2))) else (if i < 614 then (243, 39, 164, 6) else (if i < 615 then (243, 48, 164, 2) else (243, 48, 164, 6)))) else (if i < 619 then (if i < 617 then (243, 40, 164, 6) else (if i < 618 then (243, 49, 164, 2) else (243, 49, 164, 6))) else (if i < 620 then (87, 51, 84, 5) else (if i < 621 then (87, 52, 84, 5) else (151, 21, 148, 1))))))) else (if i < 646 then (if i < 634 then (if i < 628 then (if i < 625 then (if i < 623 then (151, 24, 148, 1) else (if i < 624 then (151, 22, 148, 1) else (151, 25, 148, 1))) else (if i < 626 then (215, 21, 148, 1) else (if i < 627 then (215, 21, 148, 5) else (215, 15, 148, 5)))) else (if i < 631 then (if i < 629 then (215, 24, 148, 1) else (if i < 630 then (215, 24, 148, 5) else (215, 22, 148, 1))) else (if i < 632 then (215, 22, 148, 5) else (if i < 633 then (215, 16, 148, 5) else (215, 25, 148, 1))))) else (if i < 640 then (if i < 637 then (if i < 635 then (103, 3, 228, 1) else (if i < 636 then (103, 12, 228, 1) else (103, 4, 228, 1))) else (if i < 638 then (103, 13, 228, 1) else (if i < 639 then (167, 39, 164, 1) else (167, 48, 164, 1)))) else (if i < 643 then (if i < 641 then (167, 40, 164, 1) else (if i < 642 then (167, 49, 164, 1) else (231, 3, 228, 1))) else (if i < 644 then (231, 12, 228, 1) else (if i < 645 then (231, 4, 228, 1) else (231, 13, 228, 1)))))) else (if i < 658 then (if i < 652 then (if i < 649 then (if i < 647 then (119, 3, 228, 1) else (if i < 648 then (119, 3, 228, 5) else (119, 12, 228, 1))) else (if i < 650 then (119, 12, 228, 5) else (if i < 651 then (119, 4, 228, 1) else (119, 4, 228, 5)))) else (if i < 655 then (if i < 653 then (119, 13, 228, 1) else (if i < 654 then (119, 13, 228, 5) else (183, 3, 228, 1))) else (if i < 656 then (183, 12, 228, 1) else (if i < 657 then (183, 4, 228, 1) else (183, 13, 228, 1))))) else (if i < 664 then (if i < 661 then (if i < 659 then (247, 39, 164, 1) else (if i < 660 then (247, 39, 164, 5) else (247, 48, 164, 1))) else (if i < 662 then (247, 48, 164, 5) else (if i < 663 then (247, 40, 164, 1) else (247, 40, 164, 5)))) else (if i < 667 then (if i < 665 then (247, 49, 164, 1) else (if i < 666 then (247, 49, 164, 5) else (11, 45, 164, 2))) else (if i < 668 then (11, 46, 164, 2) else (if i < 669 then (139, 9, 228, 2) else (139, 10, 228, 2)))))))) else (if i < 718 then (if i < 694 then (if i < 682 then (if i < 676 then (if i < 673 then (if i < 671 then (203, 9, 228, 2) else (if i < 672 then (203, 10, 228, 2) else (91, 45, 164, 1))) else (if i < 674 then (91, 48, 164, 1) else (if i < 675 then (91, 46, 164, 1) else (91, 49, 164, 1)))) else (if i < 679 then (if i < 677 then (155, 9, 228, 1) else (if i < 678 then (155, 12, 228, 1) else (155, 10, 228, 1))) else (if i < 680 then (155, 13, 228, 1) else (if i < 681 then (219, 9, 228, 1) else (219, 12, 228, 1))))) else (if i < 688 then (if i < 685 then (if i < 683 then (219, 10, 228, 1) else (if i < 684 then (219, 13, 228, 1) else (171, 48, 84, 3))) else (if i < 686 then (171, 51, 84, 3) else (if i < 687 then (171, 49, 84, 3) else (171, 52, 84, 3)))) else (if i < 691 then (if i < 689 then (235, 12, 148, 3) else (if i < 690 then (235, 21, 148, 3) else (235, 15, 148, 3))) else (if i < 692 then (235, 24, 148, 3) else (if i < 693 then (235, 13, 148, 3) else (235, 22, 148, 3)))))) else (if i < 706 then (if i < 700 then (if i < 697 then (if i < 695 then (235, 16, 148, 3) else (if i < 696 then (235, 25, 148, 3) else (187, 0, 228, 3))) else (if i < 698 then (187, 9, 228, 3) else (if i < 699 then (187, 3, 228, 3) else (187, 12, 228, 3)))) else (if i < 703 then (if i < 701 then (187, 1, 228, 3) else (if i < 702 then (187, 10, 132, 3) else (187, 10, 228, 3))) else (if i < 704 then (187, 4, 228, 3) else (if i < 705 then (187, 13, 228, 3) else (251, 36, 164, 3))))) else (if i < 712 then (if i < 709 then (if i < 707 then (251, 45, 164, 3) else (if i < 708 then (251, 39, 164, 3) else (251, 48, 164, 3))) else (if i < 710 then (251, 37, 164, 3) else (if i < 711 then (251, 46, 4, 3) else (251, 46, 164, 3)))) else (if i < 715 then (if i < 713 then (251, 40, 164, 3) else (if i < 714 then (251, 49, 164, 3) else (15, 49, 80, 2))) else (if i < 716 then (15, 49, 80, 6) else (if i < 717 then (15, 50, 80, 2) else (15, 50, 80, 6))))))) else (if i < 742 then (if i < 730 then (if i < 724 then (if i < 721 then (if i < 719 then (143, 13, 144, 2) else (if i < 720 then (143, 14, 144, 2) else (207, 13, 144, 2))) else (if i < 722 then (207, 13, 144, 6) else (if i < 723 then (207, 14, 144, 2) else (207, 14, 144, 6)))) else (if i < 727 then (if i < 725 then (95, 49, 80, 1) else (if i < 726 then (95, 49, 80, 5) else (95, 52, 80, 1))) else (if i < 728 then (95, 52, 80, 5) else (if i < 729 then (95, 50, 80, 1) else (95, 50, 80, 5))))) else (if i < 736 then (if i < 733 then (if i < 731 then (95, 53, 80, 1) else (if i < 732 then (159, 13, 144, 1) else (159, 16, 144, 1))) else (if i < 734 then (159, 14, 144, 1) else (if i < 735 then (159, 17, 144, 1) else (223, 13, 144, 1)))) else (if i < 739 then (if i < 737 then (223, 13, 144, 5) else (if i < 738 then (223, 16, 144, 1) else (223, 16, 144, 5))) else (if i < 740 then (223, 14, 144, 1) else (if i < 741 then (223, 14, 144, 5) else (223, 17, 144, 1)))))) else (if i < 754 then (if i < 748 then (if i < 745 then (if i < 743 then (175, 40, 80, 3) else (if i < 744 then (175, 49, 80, 3) else (175, 43, 80, 3))) else (if i < 746 then (175, 52, 80, 3) else (if i < 747 then (175, 41, 80, 3) else (175, 50, 80, 3)))) else (if i < 751 then (if i < 749 then (175, 44, 80, 3) else (if i < 750 then (175, 53, 80, 3) else (239, 4, 144, 3))) else (if i < 752 then (239, 13, 144, 3) else (if i < 753 then (239, 7, 144, 3) else (239, 16, 144, 3))))) else (if i < 760 then (if i < 757 then (if i < 755 then (239, 5, 144, 3) else (if i < 756 then (239, 14, 144, 3) else (239, 8, 144, 3))) else (if i < 758 then (239, 17, 144, 3) else (if i < 759 then (191, 16, 64, 3) else (191, 25, 64, 3)))) else (if i < 763 then (if i < 761 then (191, 17, 64, 3) else (if i < 762 then (191, 26, 64, 3) else (255, 52, 0, 3))) else (if i < 764 then (255, 52, 0, 7) else (if i < 765 then (255, 53, 0, 3) else (255, 53, 0, 7)))))))))))

def state (i : Fin 766) : A165378Proof.State :=
  let (r, d, p, z) := codes i.val
  decode r d p z

/-- Successors in lexicographic order of the new row. -/
def successors (i : ℕ) : List (Fin 766) := (if i < 383 then (if i < 191 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then [482, 486, 490, 510, 514, 518, 526, 534, 536, 538, 552, 561, 570, 578, 666, 668, 670, 684, 688, 696, 705, 714, 718, 720, 742, 750, 758, 762] else [715, 721, 763]) else (if i < 3 then [483, 487, 511] else (if i < 4 then [] else [249, 250, 251, 252, 256, 260, 298, 309, 320, 348, 359, 364, 398, 401, 404, 405, 406, 407, 408, 409, 416, 423, 426, 429, 432, 437, 446, 492, 499, 506, 510, 514, 518, 526, 540, 544, 548, 552, 561, 570, 578, 582, 585, 586, 589, 590, 591, 592, 593, 596, 599, 602, 609, 612, 621, 625, 672, 676, 680, 684, 688, 696, 705, 724, 731, 735, 742, 750, 758, 762]))) else (if i < 8 then (if i < 6 then [411, 418, 424, 515, 553, 562, 583, 587, 594, 597, 600, 603, 613, 689, 743, 751, 763] else (if i < 7 then [412, 419] else [515, 553, 562, 689, 743, 751, 763])) else (if i < 9 then [] else (if i < 10 then [399, 402, 410, 417, 427, 430, 433, 511, 519, 527, 571, 604, 610, 614, 697, 706, 759] else [605, 615])))) else (if i < 17 then (if i < 14 then (if i < 12 then [511, 519, 527, 571, 697, 706, 759] else (if i < 13 then [] else [7, 11, 54, 62, 67, 71, 122, 132, 139, 187, 195, 201])) else (if i < 15 then [12, 55, 63, 72, 188, 202] else (if i < 16 then [8, 56, 64, 68, 123, 133] else [0, 5, 9, 13, 17, 20, 22, 25, 31, 35, 38, 43, 46, 50, 58, 65, 69, 78, 85, 88, 89, 94, 98, 102, 104, 109, 113, 115, 120, 130, 138, 142, 146, 149, 152, 154, 163, 167, 171, 176, 180, 185, 194, 199, 207, 211, 214, 216, 219, 224, 228, 232, 241, 245, 264, 271, 278, 281, 288, 291, 298, 309, 320, 348, 359, 364, 440, 447, 450, 458, 466, 470, 474, 478, 492, 499, 506, 510, 514, 518, 526, 540, 544, 548, 552, 561, 570, 578, 622, 628, 634, 638, 642, 646, 654, 658, 672, 676, 680, 684, 688, 696, 705, 724, 731, 735, 742, 750, 758, 762]))) else (if i < 20 then (if i < 18 then [0, 5, 9, 13, 17, 20, 22, 25, 31, 35, 38, 43, 46, 120, 130, 138, 142, 146, 149, 152, 154, 163, 167, 171, 176, 180, 185, 194, 199, 207, 211, 214, 216, 219, 224, 228, 232, 241, 245, 298, 309, 320, 348, 359, 364, 492, 499, 506, 510, 514, 518, 526, 540, 544, 548, 552, 561, 570, 578, 672, 676, 680, 684, 688, 696, 705, 724, 731, 735, 742, 750, 758, 762] else (if i < 19 then [1, 10, 14, 18, 23, 39, 47, 186, 200, 208, 212, 217, 233, 246, 349, 365, 725, 736, 763] else [2, 6, 15, 19, 21, 26, 32, 121, 131, 143, 147, 150, 155, 164, 299, 310, 493, 500, 511])) else (if i < 21 then [1, 10, 27, 33, 36, 39, 47, 51, 59, 70, 75, 80, 87, 91, 96, 100, 103, 105, 110, 116, 156, 168, 186, 200, 220, 225, 229, 233, 246, 266, 273, 279, 282, 292, 452, 460, 467, 515, 553, 562, 619, 627, 635, 639, 643, 647, 659, 689, 743, 751, 763] else (if i < 22 then [3, 28, 34, 53, 61, 77, 82, 92, 97, 101, 157, 267, 274, 453, 461] else [2, 6, 26, 32, 40, 44, 48, 52, 60, 66, 76, 81, 84, 90, 95, 99, 106, 111, 114, 117, 121, 131, 155, 164, 172, 177, 181, 234, 242, 265, 272, 283, 289, 293, 435, 439, 451, 459, 471, 475, 479, 511, 519, 527, 571, 648, 655, 660, 697, 706, 759]))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then [3, 41, 49, 53, 61, 77, 82, 107, 112, 118, 235, 284, 294, 649, 661] else (if i < 25 then [] else [12, 126, 136, 141, 188, 202])) else (if i < 27 then [127, 137] else (if i < 28 then [12, 126, 136, 141, 188, 202] else [127, 137]))) else (if i < 32 then (if i < 30 then [1, 10, 14, 18, 23, 39, 47, 73, 86, 124, 134, 140, 144, 148, 151, 153, 158, 165, 169, 173, 178, 182, 186, 200, 208, 212, 217, 233, 246, 261, 300, 311, 321, 349, 365, 494, 501, 507, 520, 528, 626, 673, 677, 681, 685, 690, 698, 707, 725, 736, 763] else (if i < 31 then [] else [1, 10, 27, 33, 36, 39, 47, 124, 134, 140, 160, 170, 173, 178, 182, 186, 200, 220, 225, 229, 233, 246, 520, 528, 553, 562, 691, 698, 707, 743, 751, 763])) else (if i < 33 then [3, 28, 34, 125, 135, 161] else (if i < 34 then [1, 10, 27, 33, 36, 39, 47, 186, 200, 220, 225, 229, 233, 246, 553, 562, 743, 751, 763] else [3, 28, 34])))) else (if i < 41 then (if i < 38 then (if i < 36 then [3, 41, 49, 125, 135, 159, 166, 174, 179, 183, 235, 521, 529, 699, 708] else (if i < 37 then [3, 41, 49, 125, 135, 159, 166, 174, 179, 183, 235, 521, 529, 699, 708] else [])) else (if i < 39 then [8, 123, 133, 191, 197, 205] else (if i < 40 then [192, 206] else [8, 123, 133, 191, 197, 205]))) else (if i < 44 then (if i < 42 then [192, 206] else (if i < 43 then [2, 6, 15, 19, 21, 26, 32, 74, 83, 121, 131, 143, 147, 150, 155, 164, 189, 196, 203, 209, 213, 215, 218, 221, 226, 230, 236, 243, 247, 257, 299, 310, 350, 360, 366, 438, 493, 500, 511, 541, 545, 549, 554, 563, 572, 579, 726, 732, 737, 744, 752] else [3, 28, 34, 157, 190, 204, 222, 227, 231, 237, 248, 555, 564, 745, 753])) else (if i < 45 then [3, 28, 34, 157, 190, 204, 222, 227, 231, 237, 248, 555, 564, 745, 753] else (if i < 46 then [] else [2, 6, 26, 32, 40, 44, 48, 121, 131, 155, 164, 172, 177, 181, 189, 196, 203, 221, 226, 230, 238, 244, 511, 519, 527, 554, 563, 573, 697, 706, 744, 752])))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then [3, 41, 49, 190, 204, 239] else (if i < 49 then [2, 6, 26, 32, 40, 44, 48, 121, 131, 155, 164, 172, 177, 181, 511, 519, 527, 697, 706] else [3, 41, 49])) else []) else []) else []) else (if i < 83 then (if i < 77 then [] else (if i < 80 then (if i < 78 then [] else (if i < 79 then [] else [303, 314, 322, 325, 331, 334, 336, 340, 344, 353, 361, 369, 375, 379, 383, 387, 393, 395, 492, 499, 506, 510, 514, 518, 526, 540, 544, 548, 552, 561, 570, 578, 672, 676, 680, 684, 688, 696, 705, 724, 731, 735, 742, 750, 758, 762])) else (if i < 81 then [725, 736, 763] else (if i < 82 then [493, 500, 511] else [])))) else (if i < 89 then (if i < 86 then (if i < 84 then [327] else (if i < 85 then [453, 461] else [515, 553, 562, 689, 743, 751, 763])) else (if i < 87 then [389] else (if i < 88 then [649, 661] else [511, 519, 527, 571, 697, 706, 759]))) else (if i < 92 then [] else (if i < 93 then [] else [263, 307, 318, 324, 354, 370])))))) else (if i < 143 then (if i < 119 then (if i < 107 then (if i < 101 then (if i < 98 then (if i < 96 then [308, 319] else (if i < 97 then [263, 307, 318, 324, 354, 370] else [308, 319])) else (if i < 99 then [253, 262, 269, 276, 280, 285, 295, 305, 316, 323, 329, 335, 338, 342, 346, 352, 368, 376, 380, 384, 388, 396, 520, 528, 553, 562, 691, 698, 707, 743, 751, 763] else (if i < 100 then [255, 270, 277, 306, 317, 330] else [253, 262, 269, 276, 280, 285, 295, 352, 368, 376, 380, 384, 388, 396, 553, 562, 743, 751, 763]))) else (if i < 104 then (if i < 102 then [255, 270, 277] else [255, 287, 297, 306, 317, 328, 333, 339, 343, 347, 389, 521, 529, 699, 708]) else [])) else (if i < 113 then (if i < 110 then (if i < 108 then [] else [259, 304, 315, 357, 363, 373]) else (if i < 111 then [358, 374] else (if i < 112 then [259, 304, 315, 357, 363, 373] else [358, 374]))) else (if i < 116 then (if i < 114 then [255, 270, 277, 327, 356, 372, 378, 382, 386, 390, 397, 555, 564, 745, 753] else (if i < 115 then [255, 270, 277, 327, 356, 372, 378, 382, 386, 390, 397, 555, 564, 745, 753] else [254, 258, 268, 275, 286, 290, 296, 302, 313, 326, 332, 337, 341, 345, 355, 362, 371, 377, 381, 385, 391, 394, 511, 519, 527, 554, 563, 573, 697, 706, 744, 752])) else (if i < 117 then [255, 287, 297, 356, 372, 392] else (if i < 118 then [254, 258, 268, 275, 286, 290, 296, 302, 313, 326, 332, 337, 341, 345, 511, 519, 527, 697, 706] else [255, 287, 297]))))) else []) else (if i < 167 then (if i < 155 then (if i < 149 then (if i < 146 then (if i < 144 then [] else (if i < 145 then [] else [282, 292, 349, 365, 445, 449, 454, 462, 468, 472, 476, 480, 496, 503, 508, 512, 516, 522, 530, 542, 546, 550, 556, 565, 574, 580, 629, 647, 659, 725, 736, 763])) else (if i < 147 then [349, 365, 496, 503, 508, 512, 516, 522, 530, 542, 546, 550, 556, 565, 574, 580, 725, 736, 763] else (if i < 148 then [497, 504, 513] else [349, 365, 496, 503, 508, 512, 516, 522, 530, 542, 546, 550, 556, 565, 574, 580, 725, 736, 763]))) else (if i < 152 then (if i < 150 then [456, 464, 469, 517, 558, 567] else (if i < 151 then [457, 465] else [456, 464, 469, 517, 558, 567])) else (if i < 153 then [284, 294, 436, 444, 455, 463, 473, 477, 481, 513, 523, 531, 575, 649, 661] else (if i < 154 then [284, 294, 436, 444, 455, 463, 473, 477, 481, 513, 523, 531, 575, 649, 661] else [])))) else (if i < 161 then [] else (if i < 164 then (if i < 162 then [] else (if i < 163 then [261, 300, 311, 321, 349, 365, 442, 448, 498, 505, 509, 524, 532, 542, 546, 550, 556, 565, 574, 580, 626, 673, 677, 681, 685, 690, 698, 707, 725, 736, 763] else [557, 566, 574, 580, 743, 751, 763])) else (if i < 165 then [] else (if i < 166 then [743, 751, 763] else []))))) else (if i < 179 then (if i < 173 then (if i < 170 then (if i < 168 then [525, 533, 575, 699, 708] else (if i < 169 then [575] else [699, 708])) else []) else (if i < 176 then (if i < 174 then [] else (if i < 175 then [] else [351, 367, 443, 497, 504, 513, 543, 547, 551, 559, 568, 576, 581, 727, 738])) else [560, 569])) else (if i < 185 then (if i < 182 then (if i < 180 then [560, 569] else (if i < 181 then [513, 523, 531, 559, 568, 577] else [513, 523, 531])) else (if i < 183 then [513, 523, 531, 559, 568, 577] else (if i < 184 then [513, 523, 531] else []))) else []))))) else (if i < 287 then (if i < 239 then (if i < 215 then (if i < 203 then [] else (if i < 209 then [] else (if i < 212 then (if i < 210 then [] else (if i < 211 then [265, 272, 299, 310, 441, 451, 459, 493, 500, 511, 624, 633, 636, 640, 644, 650, 656, 662, 674, 678, 682, 686, 692, 700, 709, 728, 733, 739, 746, 754, 760, 764] else [299, 310, 493, 500, 511, 674, 678, 682, 686, 692, 700, 709, 728, 733, 739, 746, 754, 760, 764])) else (if i < 213 then [729, 740, 765] else (if i < 214 then [299, 310, 493, 500, 511, 674, 678, 682, 686, 692, 700, 709, 728, 733, 739, 746, 754, 760, 764] else [267, 274, 453, 461, 620, 632, 637, 641, 645, 651, 663, 693, 747, 755, 765]))))) else (if i < 227 then (if i < 221 then (if i < 218 then (if i < 216 then [267, 274, 453, 461, 620, 632, 637, 641, 645, 651, 663, 693, 747, 755, 765] else (if i < 217 then [652, 657, 664, 702, 711, 761] else [653, 665])) else (if i < 219 then [652, 657, 664, 702, 711, 761] else [])) else (if i < 224 then (if i < 222 then [] else (if i < 223 then [] else [301, 312, 495, 502, 631, 675, 679, 683, 687, 694, 703, 712, 729, 740, 765])) else (if i < 225 then [695, 703, 712, 747, 755, 765] else (if i < 226 then [747, 755, 765] else [695, 703, 712, 747, 755, 765])))) else (if i < 233 then (if i < 230 then (if i < 228 then [747, 755, 765] else [704, 713]) else (if i < 231 then [704, 713] else (if i < 232 then [704, 713] else []))) else []))) else (if i < 263 then (if i < 251 then (if i < 245 then (if i < 242 then (if i < 240 then [] else (if i < 241 then [257, 299, 310, 350, 360, 366, 438, 493, 500, 511, 541, 545, 549, 554, 563, 572, 579, 623, 630, 674, 678, 682, 686, 692, 700, 709, 730, 734, 741, 748, 756] else [555, 564, 693, 749, 757])) else (if i < 243 then [693] else (if i < 244 then [555, 564] else []))) else (if i < 248 then (if i < 246 then [511, 519, 527, 686, 692, 701, 710] else (if i < 247 then [] else [511, 519, 527])) else [])) else (if i < 257 then (if i < 254 then (if i < 252 then [] else (if i < 253 then [] else [725, 736, 763])) else (if i < 255 then [493, 500, 511] else (if i < 256 then [] else [515, 553, 562, 689, 743, 751, 763]))) else (if i < 260 then (if i < 258 then [] else (if i < 259 then [453, 461] else [])) else (if i < 261 then [511, 519, 527, 571, 697, 706, 759] else (if i < 262 then [] else [649, 661]))))) else (if i < 275 then (if i < 269 then (if i < 266 then [] else (if i < 267 then [] else (if i < 268 then [] else [308, 319]))) else (if i < 272 then (if i < 270 then [263, 307, 318, 324, 354, 370] else (if i < 271 then [308, 319] else [520, 528, 553, 562, 691, 698, 707, 743, 751, 763])) else (if i < 273 then [] else (if i < 274 then [553, 562, 743, 751, 763] else [])))) else (if i < 281 then (if i < 278 then (if i < 276 then [255, 270, 277, 306, 317, 330] else (if i < 277 then [253, 262, 269, 276, 280, 285, 295, 352, 368, 376, 380, 384, 388, 396, 553, 562, 743, 751, 763] else [255, 270, 277])) else (if i < 279 then [521, 529, 699, 708] else (if i < 280 then [521, 529, 699, 708] else [255, 287, 297, 306, 317, 328, 333, 339, 343, 347, 389, 521, 529, 699, 708]))) else (if i < 284 then [] else (if i < 285 then [] else (if i < 286 then [358, 374] else [259, 304, 315, 357, 363, 373]))))))) else (if i < 335 then (if i < 311 then (if i < 299 then (if i < 293 then (if i < 290 then (if i < 288 then [358, 374] else [555, 564, 745, 753]) else (if i < 291 then [255, 270, 277, 327, 356, 372, 378, 382, 386, 390, 397, 555, 564, 745, 753] else (if i < 292 then [511, 519, 527, 554, 563, 573, 697, 706, 744, 752] else []))) else (if i < 296 then (if i < 294 then [511, 519, 527, 697, 706] else (if i < 295 then [] else [255, 287, 297, 356, 372, 392])) else (if i < 297 then [254, 258, 268, 275, 286, 290, 296, 302, 313, 326, 332, 337, 341, 345, 511, 519, 527, 697, 706] else (if i < 298 then [255, 287, 297] else [])))) else (if i < 305 then (if i < 302 then [] else (if i < 303 then [] else (if i < 304 then [349, 365, 496, 503, 508, 512, 516, 522, 530, 542, 546, 550, 556, 565, 574, 580, 725, 736, 763] else []))) else [])) else (if i < 323 then (if i < 317 then (if i < 314 then [] else (if i < 315 then [456, 464, 469, 517, 558, 567] else [])) else (if i < 320 then [] else (if i < 321 then [] else (if i < 322 then [] else [284, 294, 436, 444, 455, 463, 473, 477, 481, 513, 523, 531, 575, 649, 661])))) else (if i < 329 then [] else (if i < 332 then (if i < 330 then [] else (if i < 331 then [] else [557, 566, 574, 580, 743, 751, 763])) else (if i < 333 then [] else (if i < 334 then [] else [525, 533, 575, 699, 708])))))) else (if i < 359 then (if i < 347 then (if i < 341 then (if i < 338 then [] else (if i < 339 then [] else (if i < 340 then [] else [560, 569]))) else (if i < 344 then [560, 569] else (if i < 345 then [513, 523, 531, 559, 568, 577] else (if i < 346 then [513, 523, 531] else [513, 523, 531, 559, 568, 577])))) else (if i < 353 then (if i < 350 then (if i < 348 then [513, 523, 531] else []) else []) else (if i < 356 then (if i < 354 then [299, 310, 493, 500, 511, 674, 678, 682, 686, 692, 700, 709, 728, 733, 739, 746, 754, 760, 764] else []) else []))) else (if i < 371 then (if i < 365 then (if i < 362 then (if i < 360 then [] else (if i < 361 then [] else [267, 274, 453, 461, 620, 632, 637, 641, 645, 651, 663, 693, 747, 755, 765])) else []) else (if i < 368 then [] else (if i < 369 then [] else (if i < 370 then [652, 657, 664, 702, 711, 761] else [])))) else (if i < 377 then [] else (if i < 380 then (if i < 378 then [] else (if i < 379 then [] else [695, 703, 712, 747, 755, 765])) else (if i < 381 then [747, 755, 765] else (if i < 382 then [695, 703, 712, 747, 755, 765] else [747, 755, 765]))))))))) else (if i < 574 then (if i < 478 then (if i < 430 then (if i < 406 then (if i < 394 then (if i < 388 then (if i < 385 then [704, 713] else (if i < 386 then [704, 713] else (if i < 387 then [704, 713] else []))) else (if i < 391 then [] else (if i < 392 then [] else (if i < 393 then [] else [555, 564, 693, 749, 757])))) else (if i < 400 then (if i < 397 then (if i < 395 then [] else (if i < 396 then [511, 519, 527, 686, 692, 701, 710] else [])) else (if i < 398 then [] else (if i < 399 then [715, 721, 763] else []))) else (if i < 403 then [] else (if i < 404 then [] else (if i < 405 then [605, 615] else [12, 55, 63, 72, 188, 202]))))) else (if i < 418 then (if i < 412 then (if i < 409 then (if i < 407 then [1, 10, 14, 18, 23, 39, 47, 186, 200, 208, 212, 217, 233, 246, 349, 365, 725, 736, 763] else (if i < 408 then [] else [3, 41, 49, 53, 61, 77, 82, 107, 112, 118, 235, 284, 294, 649, 661])) else []) else []) else (if i < 424 then [] else (if i < 427 then (if i < 425 then [] else (if i < 426 then [] else [192, 206])) else (if i < 428 then [192, 206] else (if i < 429 then [192, 206] else [])))))) else (if i < 454 then (if i < 442 then (if i < 436 then (if i < 433 then (if i < 431 then [] else (if i < 432 then [] else [3, 41, 49, 190, 204, 239])) else (if i < 434 then [3, 41, 49] else (if i < 435 then [3, 41, 49] else []))) else []) else (if i < 448 then (if i < 445 then [] else (if i < 446 then [] else (if i < 447 then [389] else []))) else (if i < 451 then (if i < 449 then [389] else []) else []))) else (if i < 466 then [] else (if i < 472 then (if i < 469 then [] else (if i < 470 then [] else [358, 374])) else (if i < 475 then (if i < 473 then [358, 374] else (if i < 474 then [358, 374] else [])) else []))))) else (if i < 526 then (if i < 502 then (if i < 490 then (if i < 484 then (if i < 481 then (if i < 479 then [255, 287, 297, 356, 372, 392] else (if i < 480 then [255, 287, 297] else [255, 287, 297, 356, 372, 392])) else (if i < 482 then [255, 287, 297] else (if i < 483 then [184, 198, 484, 488, 491, 512, 516, 522, 530, 535, 537, 539, 556, 565, 574, 580, 715, 721, 763] else [485, 489, 513]))) else (if i < 487 then (if i < 485 then [184, 198, 484, 488, 491, 512, 516, 522, 530, 535, 537, 539, 556, 565, 574, 580, 715, 721, 763] else (if i < 486 then [485, 489, 513] else [414, 421, 425, 517, 558, 567])) else (if i < 488 then [415, 422] else (if i < 489 then [414, 421, 425, 517, 558, 567] else [415, 422])))) else (if i < 496 then (if i < 493 then (if i < 491 then [37, 45, 400, 403, 413, 420, 428, 431, 434, 513, 523, 531, 575, 605, 615] else (if i < 492 then [37, 45, 400, 403, 413, 420, 428, 431, 434, 513, 523, 531, 575, 605, 615] else [349, 365, 496, 503, 508, 512, 516, 522, 530, 542, 546, 550, 556, 565, 574, 580, 725, 736, 763])) else (if i < 494 then [497, 504, 513] else (if i < 495 then [349, 365, 725, 736, 763] else []))) else (if i < 499 then (if i < 497 then [349, 365, 496, 503, 508, 512, 516, 522, 530, 542, 546, 550, 556, 565, 574, 580, 725, 736, 763] else (if i < 498 then [497, 504, 513] else [349, 365, 725, 736, 763])) else (if i < 500 then [456, 464, 469, 517, 558, 567] else (if i < 501 then [457, 465] else []))))) else (if i < 514 then (if i < 508 then (if i < 505 then (if i < 503 then [] else (if i < 504 then [456, 464, 469, 517, 558, 567] else [457, 465])) else (if i < 506 then [] else (if i < 507 then [284, 294, 436, 444, 455, 463, 473, 477, 481, 513, 523, 531, 575, 649, 661] else [284, 294, 649, 661]))) else (if i < 511 then (if i < 509 then [284, 294, 436, 444, 455, 463, 473, 477, 481, 513, 523, 531, 575, 649, 661] else (if i < 510 then [284, 294, 649, 661] else [743, 751, 763])) else (if i < 512 then [] else (if i < 513 then [743, 751, 763] else [])))) else (if i < 520 then (if i < 517 then (if i < 515 then [699, 708] else (if i < 516 then [] else [699, 708])) else (if i < 518 then [] else [560, 569])) else (if i < 523 then (if i < 521 then [] else (if i < 522 then [] else [560, 569])) else (if i < 524 then [560, 569] else []))))) else (if i < 550 then (if i < 538 then (if i < 532 then (if i < 529 then (if i < 527 then [513, 523, 531, 559, 568, 577] else (if i < 528 then [513, 523, 531] else [])) else (if i < 530 then [] else (if i < 531 then [513, 523, 531, 559, 568, 577] else [513, 523, 531]))) else (if i < 535 then (if i < 533 then [] else (if i < 534 then [] else [717, 723, 765])) else (if i < 536 then [717, 723, 765] else []))) else (if i < 544 then (if i < 541 then (if i < 539 then [608, 618] else (if i < 540 then [608, 618] else [729, 740, 765])) else [729, 740, 765]) else (if i < 547 then [] else (if i < 548 then [] else [653, 665])))) else (if i < 562 then (if i < 556 then (if i < 553 then (if i < 551 then [653, 665] else (if i < 552 then [653, 665] else [])) else []) else (if i < 559 then (if i < 557 then [] else (if i < 558 then [747, 755, 765] else [])) else [])) else (if i < 568 then (if i < 565 then [] else (if i < 566 then [] else (if i < 567 then [704, 713] else []))) else []))))) else (if i < 670 then (if i < 622 then (if i < 598 then (if i < 586 then (if i < 580 then [] else (if i < 583 then (if i < 581 then [] else (if i < 582 then [] else [483, 487, 511])) else (if i < 584 then [] else (if i < 585 then [] else [412, 419])))) else (if i < 592 then (if i < 589 then [] else (if i < 590 then [8, 56, 64, 68, 123, 133] else (if i < 591 then [2, 6, 15, 19, 21, 26, 32, 121, 131, 143, 147, 150, 155, 164, 299, 310, 493, 500, 511] else [3, 28, 34, 53, 61, 77, 82, 92, 97, 101, 157, 267, 274, 453, 461]))) else (if i < 595 then (if i < 593 then [] else [127, 137]) else (if i < 596 then [127, 137] else (if i < 597 then [3, 28, 34, 125, 135, 161] else [3, 28, 34]))))) else (if i < 610 then (if i < 604 then (if i < 601 then (if i < 599 then [3, 28, 34] else []) else []) else []) else (if i < 616 then [] else (if i < 619 then [] else (if i < 620 then [] else (if i < 621 then [] else [327])))))) else (if i < 646 then (if i < 634 then (if i < 628 then (if i < 625 then (if i < 623 then [] else (if i < 624 then [327] else [])) else []) else []) else (if i < 640 then (if i < 637 then [308, 319] else (if i < 638 then [308, 319] else (if i < 639 then [255, 270, 277, 306, 317, 330] else [255, 270, 277]))) else (if i < 643 then (if i < 641 then [255, 270, 277, 306, 317, 330] else (if i < 642 then [255, 270, 277] else [])) else []))) else (if i < 658 then [] else (if i < 664 then [] else (if i < 667 then (if i < 665 then [] else (if i < 666 then [] else [485, 489, 513])) else (if i < 668 then [485, 489, 513] else [415, 422])))))) else (if i < 718 then (if i < 694 then (if i < 682 then (if i < 676 then (if i < 673 then (if i < 671 then [] else (if i < 672 then [] else [497, 504, 513])) else [497, 504, 513]) else (if i < 679 then [457, 465] else (if i < 680 then [457, 465] else []))) else []) else (if i < 706 then (if i < 700 then [] else (if i < 703 then (if i < 701 then [] else (if i < 702 then [560, 569] else [])) else [])) else (if i < 712 then (if i < 709 then [] else (if i < 710 then [] else (if i < 711 then [513, 523, 531] else []))) else (if i < 715 then (if i < 713 then [] else (if i < 714 then [] else [119, 129, 483, 487, 511, 667, 669, 671, 686, 692, 700, 709, 716, 719, 722, 746, 754, 760, 764])) else (if i < 716 then [717, 723, 765] else (if i < 717 then [119, 129, 483, 487, 511, 667, 669, 671, 686, 692, 700, 709, 716, 719, 722, 746, 754, 760, 764] else [717, 723, 765])))))) else (if i < 742 then (if i < 730 then (if i < 724 then (if i < 721 then (if i < 719 then [24, 30, 412, 419, 584, 588, 595, 598, 601, 606, 616, 693, 747, 755, 765] else (if i < 720 then [24, 30, 412, 419, 584, 588, 595, 598, 601, 606, 616, 693, 747, 755, 765] else [607, 611, 617, 702, 711, 761])) else (if i < 722 then [608, 618] else (if i < 723 then [607, 611, 617, 702, 711, 761] else [608, 618]))) else (if i < 727 then (if i < 725 then [299, 310, 493, 500, 511, 674, 678, 682, 686, 692, 700, 709, 728, 733, 739, 746, 754, 760, 764] else (if i < 726 then [729, 740, 765] else [299, 310, 493, 500, 511])) else (if i < 728 then [] else (if i < 729 then [299, 310, 493, 500, 511, 674, 678, 682, 686, 692, 700, 709, 728, 733, 739, 746, 754, 760, 764] else [729, 740, 765])))) else (if i < 736 then (if i < 733 then (if i < 731 then [299, 310, 493, 500, 511] else (if i < 732 then [267, 274, 453, 461, 620, 632, 637, 641, 645, 651, 663, 693, 747, 755, 765] else [267, 274, 453, 461])) else (if i < 734 then [267, 274, 453, 461, 620, 632, 637, 641, 645, 651, 663, 693, 747, 755, 765] else (if i < 735 then [267, 274, 453, 461] else [652, 657, 664, 702, 711, 761]))) else (if i < 739 then (if i < 737 then [653, 665] else []) else (if i < 740 then [652, 657, 664, 702, 711, 761] else (if i < 741 then [653, 665] else []))))) else (if i < 754 then (if i < 748 then (if i < 745 then (if i < 743 then [695, 703, 712, 747, 755, 765] else (if i < 744 then [747, 755, 765] else [])) else (if i < 746 then [] else (if i < 747 then [695, 703, 712, 747, 755, 765] else [747, 755, 765]))) else (if i < 751 then (if i < 749 then [] else (if i < 750 then [] else [704, 713])) else (if i < 752 then [704, 713] else []))) else (if i < 760 then (if i < 757 then (if i < 755 then [704, 713] else (if i < 756 then [704, 713] else [])) else (if i < 758 then [] else (if i < 759 then [555, 564] else []))) else (if i < 763 then (if i < 761 then [555, 564] else (if i < 762 then [] else [511, 519, 527])) else (if i < 764 then [] else (if i < 765 then [511, 519, 527] else []))))))))))

def succ (i : Fin 766) : List (Fin 766) := successors i.val

def initial : List (Fin 766) := [4, 16, 29, 42, 57, 79, 93, 108, 128, 145, 162, 175, 193, 210, 223, 240]

def accepting : List (Fin 766) := [404, 408, 432, 433, 434, 446, 447, 448, 449, 478, 479, 480, 481, 490, 491, 506, 507, 508, 509, 514, 515, 516, 517, 526, 527, 528, 529, 530, 531, 532, 533, 578, 579, 580, 581]

def acceptedValues (i : ℕ) : ℕ := (if i < 383 then 0 else (if i < 574 then (if i < 478 then (if i < 430 then (if i < 406 then (if i < 394 then 0 else (if i < 400 then 0 else (if i < 403 then 0 else (if i < 404 then 0 else (if i < 405 then 1 else 0))))) else (if i < 418 then (if i < 412 then (if i < 409 then (if i < 407 then 0 else (if i < 408 then 0 else 1)) else 0) else 0) else 0)) else (if i < 454 then (if i < 442 then (if i < 436 then (if i < 433 then (if i < 431 then 0 else (if i < 432 then 0 else 1)) else (if i < 434 then 1 else (if i < 435 then 1 else 0))) else 0) else (if i < 448 then (if i < 445 then 0 else (if i < 446 then 0 else 1)) else (if i < 451 then (if i < 449 then 1 else (if i < 450 then 1 else 0)) else 0))) else 0)) else (if i < 526 then (if i < 502 then (if i < 490 then (if i < 484 then (if i < 481 then 1 else (if i < 482 then 1 else 0)) else 0) else (if i < 496 then (if i < 493 then (if i < 491 then 1 else (if i < 492 then 1 else 0)) else 0) else 0)) else (if i < 514 then (if i < 508 then (if i < 505 then 0 else (if i < 506 then 0 else 1)) else (if i < 511 then (if i < 509 then 1 else (if i < 510 then 1 else 0)) else 0)) else (if i < 520 then (if i < 517 then 1 else (if i < 518 then 1 else 0)) else 0))) else (if i < 550 then (if i < 538 then (if i < 532 then 1 else (if i < 535 then (if i < 533 then 1 else (if i < 534 then 1 else 0)) else 0)) else 0) else 0))) else (if i < 670 then (if i < 622 then (if i < 598 then (if i < 586 then (if i < 580 then (if i < 577 then 0 else (if i < 578 then 0 else 1)) else (if i < 583 then (if i < 581 then 1 else (if i < 582 then 1 else 0)) else 0)) else 0) else 0) else 0) else 0)))

def accepted (i : Fin 766) : ℕ := acceptedValues i.val

def qValues (i : ℕ) : ℕ := (if i < 383 then (if i < 191 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then 0 else (if i < 17 then (if i < 14 then 0 else (if i < 15 then 0 else (if i < 16 then 0 else 9))) else (if i < 20 then (if i < 18 then 9 else 0) else 0))) else 0) else 0) else 0) else 0) else 0)

def q (i : Fin 766) : ℕ := qValues i.val

def lValues (i : ℕ) : ℕ := (if i < 383 then (if i < 191 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 3 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 3))) else 0) else (if i < 17 then (if i < 14 then 0 else (if i < 15 then 0 else (if i < 16 then 0 else 61))) else (if i < 20 then (if i < 18 then 58 else 0) else (if i < 21 then 2 else (if i < 22 then 0 else 4))))) else (if i < 35 then (if i < 29 then 0 else (if i < 32 then (if i < 30 then 2 else (if i < 31 then 0 else 1)) else (if i < 33 then 0 else (if i < 34 then 1 else 0)))) else (if i < 41 then 0 else (if i < 44 then (if i < 42 then 0 else (if i < 43 then 1 else 0)) else (if i < 45 then 0 else (if i < 46 then 0 else 2)))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then 0 else (if i < 49 then 2 else 0)) else 0) else 0) else 0) else (if i < 83 then (if i < 77 then 0 else (if i < 80 then (if i < 78 then 0 else (if i < 79 then 0 else 6)) else 0)) else 0))) else (if i < 143 then (if i < 119 then (if i < 107 then (if i < 101 then (if i < 98 then 0 else (if i < 99 then 1 else (if i < 100 then 0 else 1))) else 0) else (if i < 113 then 0 else (if i < 116 then (if i < 114 then 0 else (if i < 115 then 0 else 2)) else (if i < 117 then 0 else (if i < 118 then 2 else 0))))) else 0) else (if i < 167 then (if i < 155 then (if i < 149 then (if i < 146 then (if i < 144 then 0 else (if i < 145 then 0 else 2)) else (if i < 147 then 2 else (if i < 148 then 0 else 2))) else 0) else 0) else 0))) else (if i < 287 then (if i < 239 then (if i < 215 then (if i < 203 then 0 else (if i < 209 then 0 else (if i < 212 then (if i < 210 then 0 else 1) else (if i < 213 then 0 else (if i < 214 then 1 else 0))))) else 0) else (if i < 263 then 0 else (if i < 275 then 0 else (if i < 281 then (if i < 278 then (if i < 276 then 0 else (if i < 277 then 1 else 0)) else 0) else 0)))) else (if i < 335 then (if i < 311 then (if i < 299 then (if i < 293 then 0 else (if i < 296 then 0 else (if i < 297 then 2 else 0))) else (if i < 305 then (if i < 302 then 0 else (if i < 303 then 0 else (if i < 304 then 2 else 0))) else 0)) else 0) else (if i < 359 then (if i < 347 then 0 else (if i < 353 then 0 else (if i < 356 then (if i < 354 then 1 else 0) else 0))) else 0)))) else (if i < 574 then (if i < 478 then 0 else (if i < 526 then (if i < 502 then (if i < 490 then (if i < 484 then (if i < 481 then 0 else (if i < 482 then 0 else (if i < 483 then 2 else 0))) else (if i < 487 then (if i < 485 then 2 else 0) else 0)) else (if i < 496 then (if i < 493 then (if i < 491 then 0 else (if i < 492 then 0 else 2)) else 0) else (if i < 499 then (if i < 497 then 2 else 0) else 0))) else 0) else 0)) else (if i < 670 then 0 else (if i < 718 then (if i < 694 then 0 else (if i < 706 then 0 else (if i < 712 then 0 else (if i < 715 then (if i < 713 then 0 else (if i < 714 then 0 else 1)) else (if i < 716 then 0 else (if i < 717 then 1 else 0)))))) else (if i < 742 then (if i < 730 then (if i < 724 then 0 else (if i < 727 then (if i < 725 then 1 else 0) else (if i < 728 then 0 else (if i < 729 then 1 else 0)))) else 0) else 0)))))

def l (i : Fin 766) : ℕ := lValues i.val

def cValues (i : ℕ) : ℕ := (if i < 383 then (if i < 191 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 12 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 13))) else (if i < 8 then 0 else (if i < 9 then 0 else (if i < 10 then 1 else 0)))) else (if i < 17 then (if i < 14 then (if i < 12 then 1 else (if i < 13 then 0 else 1)) else (if i < 15 then 0 else (if i < 16 then 0 else 96))) else (if i < 20 then (if i < 18 then 88 else 0) else (if i < 21 then 4 else (if i < 22 then 0 else 9))))) else (if i < 35 then (if i < 29 then 0 else (if i < 32 then (if i < 30 then 10 else (if i < 31 then 0 else 3)) else (if i < 33 then 0 else (if i < 34 then 2 else 0)))) else (if i < 41 then (if i < 38 then (if i < 36 then 1 else (if i < 37 then 1 else 0)) else 0) else (if i < 44 then (if i < 42 then 0 else (if i < 43 then 2 else 0)) else (if i < 45 then 0 else (if i < 46 then 0 else 5)))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then 0 else (if i < 49 then 5 else 0)) else 0) else 0) else 0) else (if i < 83 then (if i < 77 then 0 else (if i < 80 then (if i < 78 then 0 else (if i < 79 then 0 else 25)) else 0)) else (if i < 89 then (if i < 86 then 0 else (if i < 87 then 0 else (if i < 88 then 0 else 1))) else 0)))) else (if i < 143 then (if i < 119 then (if i < 107 then (if i < 101 then (if i < 98 then 0 else (if i < 99 then 3 else (if i < 100 then 0 else 2))) else (if i < 104 then (if i < 102 then 0 else 1) else 0)) else (if i < 113 then 0 else (if i < 116 then (if i < 114 then 0 else (if i < 115 then 0 else 5)) else (if i < 117 then 0 else (if i < 118 then 5 else 0))))) else 0) else (if i < 167 then (if i < 155 then (if i < 149 then (if i < 146 then (if i < 144 then 0 else (if i < 145 then 0 else 10)) else (if i < 147 then 10 else (if i < 148 then 0 else 10))) else (if i < 152 then 0 else (if i < 153 then 1 else (if i < 154 then 1 else 0)))) else 0) else (if i < 179 then 0 else (if i < 185 then (if i < 182 then (if i < 180 then 0 else 1) else (if i < 183 then 1 else (if i < 184 then 1 else 0))) else 0))))) else (if i < 287 then (if i < 239 then (if i < 215 then (if i < 203 then 0 else (if i < 209 then 0 else (if i < 212 then (if i < 210 then 0 else 2) else (if i < 213 then 0 else (if i < 214 then 2 else 0))))) else 0) else (if i < 263 then (if i < 251 then (if i < 245 then 0 else (if i < 248 then (if i < 246 then 2 else (if i < 247 then 0 else 1)) else 0)) else (if i < 257 then 0 else (if i < 260 then 0 else (if i < 261 then 1 else 0)))) else (if i < 275 then 0 else (if i < 281 then (if i < 278 then (if i < 276 then 0 else (if i < 277 then 2 else 0)) else (if i < 279 then 0 else (if i < 280 then 0 else 1))) else 0)))) else (if i < 335 then (if i < 311 then (if i < 299 then (if i < 293 then (if i < 290 then 0 else (if i < 291 then 0 else (if i < 292 then 1 else 0))) else (if i < 296 then (if i < 294 then 1 else 0) else (if i < 297 then 5 else 0))) else (if i < 305 then (if i < 302 then 0 else (if i < 303 then 0 else (if i < 304 then 10 else 0))) else 0)) else (if i < 323 then (if i < 317 then 0 else (if i < 320 then 0 else (if i < 321 then 0 else (if i < 322 then 0 else 1)))) else 0)) else (if i < 359 then (if i < 347 then (if i < 341 then 0 else (if i < 344 then 0 else 1)) else (if i < 353 then (if i < 350 then (if i < 348 then 1 else 0) else 0) else (if i < 356 then (if i < 354 then 2 else 0) else 0))) else 0)))) else (if i < 574 then (if i < 478 then (if i < 430 then (if i < 406 then (if i < 394 then 0 else (if i < 400 then (if i < 397 then (if i < 395 then 0 else (if i < 396 then 2 else 0)) else 0) else 0)) else 0) else 0) else (if i < 526 then (if i < 502 then (if i < 490 then (if i < 484 then (if i < 481 then 0 else (if i < 482 then 0 else (if i < 483 then 10 else 0))) else (if i < 487 then (if i < 485 then 10 else 0) else 0)) else (if i < 496 then (if i < 493 then (if i < 491 then 1 else (if i < 492 then 1 else 10)) else 0) else (if i < 499 then (if i < 497 then 10 else 0) else 0))) else (if i < 514 then (if i < 508 then (if i < 505 then 0 else (if i < 506 then 0 else (if i < 507 then 1 else 0))) else (if i < 511 then (if i < 509 then 1 else 0) else 0)) else 0)) else (if i < 550 then (if i < 538 then (if i < 532 then (if i < 529 then (if i < 527 then 1 else (if i < 528 then 1 else 0)) else (if i < 530 then 0 else 1)) else 0) else 0) else 0))) else (if i < 670 then 0 else (if i < 718 then (if i < 694 then 0 else (if i < 706 then 0 else (if i < 712 then (if i < 709 then 0 else (if i < 710 then 0 else (if i < 711 then 1 else 0))) else (if i < 715 then (if i < 713 then 0 else (if i < 714 then 0 else 2)) else (if i < 716 then 0 else (if i < 717 then 2 else 0)))))) else (if i < 742 then (if i < 730 then (if i < 724 then 0 else (if i < 727 then (if i < 725 then 2 else 0) else (if i < 728 then 0 else (if i < 729 then 2 else 0)))) else 0) else (if i < 754 then 0 else (if i < 760 then 0 else (if i < 763 then (if i < 761 then 0 else (if i < 762 then 0 else 1)) else (if i < 764 then 0 else (if i < 765 then 1 else 0))))))))))

def c (i : Fin 766) : ℕ := cValues i.val

def v1Values (i : ℕ) : ℕ := (if i < 383 then (if i < 191 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 4 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 8))) else (if i < 8 then (if i < 6 then 1 else (if i < 7 then 0 else 1)) else (if i < 9 then 0 else (if i < 10 then 2 else 0)))) else (if i < 17 then (if i < 14 then (if i < 12 then 1 else 0) else (if i < 15 then 0 else (if i < 16 then 0 else 6))) else (if i < 20 then (if i < 18 then 4 else 0) else (if i < 21 then 1 else (if i < 22 then 0 else 2))))) else (if i < 35 then (if i < 29 then 0 else (if i < 32 then (if i < 30 then 2 else (if i < 31 then 0 else 1)) else 0)) else (if i < 41 then (if i < 38 then (if i < 36 then 1 else (if i < 37 then 1 else 0)) else 0) else (if i < 44 then (if i < 42 then 0 else (if i < 43 then 1 else 0)) else (if i < 45 then 0 else (if i < 46 then 0 else 1)))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then 0 else (if i < 49 then 1 else 0)) else 0) else 0) else 0) else (if i < 83 then (if i < 77 then 0 else (if i < 80 then (if i < 78 then 0 else (if i < 79 then 0 else 4)) else 0)) else (if i < 89 then (if i < 86 then (if i < 84 then 0 else (if i < 85 then 0 else 1)) else (if i < 87 then 0 else (if i < 88 then 0 else 1))) else 0)))) else (if i < 143 then (if i < 119 then (if i < 107 then (if i < 101 then (if i < 98 then 0 else (if i < 99 then 1 else 0)) else (if i < 104 then (if i < 102 then 0 else 1) else 0)) else (if i < 113 then 0 else (if i < 116 then (if i < 114 then 0 else (if i < 115 then 0 else 1)) else (if i < 117 then 0 else (if i < 118 then 1 else 0))))) else 0) else (if i < 167 then (if i < 155 then (if i < 149 then (if i < 146 then (if i < 144 then 0 else (if i < 145 then 0 else 6)) else (if i < 147 then 4 else (if i < 148 then 0 else 4))) else (if i < 152 then (if i < 150 then 1 else (if i < 151 then 0 else 1)) else (if i < 153 then 2 else (if i < 154 then 2 else 0)))) else (if i < 161 then 0 else (if i < 164 then (if i < 162 then 0 else (if i < 163 then 4 else 1)) else 0))) else (if i < 179 then (if i < 173 then (if i < 170 then (if i < 168 then 1 else 0) else 0) else (if i < 176 then (if i < 174 then 0 else (if i < 175 then 0 else 1)) else 0)) else (if i < 185 then (if i < 182 then (if i < 180 then 0 else 1) else (if i < 183 then 1 else (if i < 184 then 1 else 0))) else 0))))) else (if i < 287 then (if i < 239 then 0 else (if i < 263 then (if i < 251 then (if i < 245 then (if i < 242 then (if i < 240 then 0 else (if i < 241 then 1 else 0)) else 0) else (if i < 248 then (if i < 246 then 1 else (if i < 247 then 0 else 1)) else 0)) else (if i < 257 then (if i < 254 then 0 else (if i < 255 then 0 else (if i < 256 then 0 else 1))) else (if i < 260 then 0 else (if i < 261 then 1 else 0)))) else (if i < 275 then (if i < 269 then 0 else (if i < 272 then (if i < 270 then 0 else (if i < 271 then 0 else 1)) else 0)) else (if i < 281 then (if i < 278 then 0 else 1) else 0)))) else (if i < 335 then (if i < 311 then (if i < 299 then (if i < 293 then (if i < 290 then 0 else (if i < 291 then 0 else (if i < 292 then 1 else 0))) else (if i < 296 then (if i < 294 then 1 else 0) else (if i < 297 then 1 else 0))) else (if i < 305 then (if i < 302 then 0 else (if i < 303 then 0 else (if i < 304 then 4 else 0))) else 0)) else (if i < 323 then (if i < 317 then (if i < 314 then 0 else (if i < 315 then 1 else 0)) else (if i < 320 then 0 else (if i < 321 then 0 else (if i < 322 then 0 else 2)))) else (if i < 329 then 0 else (if i < 332 then (if i < 330 then 0 else (if i < 331 then 0 else 1)) else (if i < 333 then 0 else (if i < 334 then 0 else 1)))))) else (if i < 359 then (if i < 347 then (if i < 341 then 0 else (if i < 344 then 0 else 1)) else (if i < 353 then (if i < 350 then (if i < 348 then 1 else 0) else 0) else 0)) else 0)))) else (if i < 574 then (if i < 478 then (if i < 430 then (if i < 406 then (if i < 394 then 0 else (if i < 400 then (if i < 397 then (if i < 395 then 0 else (if i < 396 then 1 else 0)) else 0) else 0)) else 0) else 0) else (if i < 526 then (if i < 502 then (if i < 490 then (if i < 484 then (if i < 481 then 0 else (if i < 482 then 0 else (if i < 483 then 4 else 0))) else (if i < 487 then (if i < 485 then 4 else (if i < 486 then 0 else 1)) else (if i < 488 then 0 else (if i < 489 then 1 else 0)))) else (if i < 496 then (if i < 493 then (if i < 491 then 2 else (if i < 492 then 2 else 4)) else 0) else (if i < 499 then (if i < 497 then 4 else 0) else (if i < 500 then 1 else 0)))) else (if i < 514 then (if i < 508 then (if i < 505 then (if i < 503 then 0 else (if i < 504 then 1 else 0)) else (if i < 506 then 0 else (if i < 507 then 2 else 0))) else (if i < 511 then (if i < 509 then 2 else 0) else 0)) else 0)) else (if i < 550 then (if i < 538 then (if i < 532 then (if i < 529 then (if i < 527 then 1 else (if i < 528 then 1 else 0)) else (if i < 530 then 0 else 1)) else 0) else 0) else 0))) else (if i < 670 then 0 else (if i < 718 then (if i < 694 then 0 else (if i < 706 then 0 else (if i < 712 then (if i < 709 then 0 else (if i < 710 then 0 else (if i < 711 then 1 else 0))) else 0))) else (if i < 742 then 0 else (if i < 754 then 0 else (if i < 760 then 0 else (if i < 763 then (if i < 761 then 0 else (if i < 762 then 0 else 1)) else (if i < 764 then 0 else (if i < 765 then 1 else 0))))))))))

def v1 (i : Fin 766) : ℕ := v1Values i.val

def v2Values (i : ℕ) : ℕ := (if i < 383 then (if i < 191 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 9 else 0) else (if i < 3 then 0 else (if i < 4 then 0 else 11))) else (if i < 8 then 0 else (if i < 9 then 0 else (if i < 10 then 1 else 0)))) else (if i < 17 then (if i < 14 then (if i < 12 then 1 else (if i < 13 then 0 else 2)) else (if i < 15 then 0 else (if i < 16 then 0 else 45))) else (if i < 20 then (if i < 18 then 37 else 0) else (if i < 21 then 3 else (if i < 22 then 0 else 5))))) else (if i < 35 then (if i < 29 then 0 else (if i < 32 then (if i < 30 then 8 else (if i < 31 then 0 else 2)) else (if i < 33 then 0 else (if i < 34 then 1 else 0)))) else (if i < 41 then (if i < 38 then (if i < 36 then 1 else (if i < 37 then 1 else 0)) else 0) else (if i < 44 then (if i < 42 then 0 else (if i < 43 then 1 else 0)) else (if i < 45 then 0 else (if i < 46 then 0 else 3)))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then 0 else (if i < 49 then 3 else 0)) else 0) else 0) else 0) else (if i < 83 then (if i < 77 then 0 else (if i < 80 then (if i < 78 then 0 else (if i < 79 then 0 else 20)) else 0)) else (if i < 89 then (if i < 86 then 0 else (if i < 87 then 0 else (if i < 88 then 0 else 1))) else 0)))) else (if i < 143 then (if i < 119 then (if i < 107 then (if i < 101 then (if i < 98 then 0 else (if i < 99 then 2 else (if i < 100 then 0 else 1))) else (if i < 104 then (if i < 102 then 0 else 1) else 0)) else (if i < 113 then 0 else (if i < 116 then (if i < 114 then 0 else (if i < 115 then 0 else 3)) else (if i < 117 then 0 else (if i < 118 then 3 else 0))))) else 0) else (if i < 167 then (if i < 155 then (if i < 149 then (if i < 146 then (if i < 144 then 0 else (if i < 145 then 0 else 8)) else (if i < 147 then 8 else (if i < 148 then 0 else 8))) else (if i < 152 then 0 else (if i < 153 then 1 else (if i < 154 then 1 else 0)))) else 0) else (if i < 179 then 0 else (if i < 185 then (if i < 182 then (if i < 180 then 0 else 1) else (if i < 183 then 1 else (if i < 184 then 1 else 0))) else 0))))) else (if i < 287 then (if i < 239 then (if i < 215 then (if i < 203 then 0 else (if i < 209 then 0 else (if i < 212 then (if i < 210 then 0 else 1) else (if i < 213 then 0 else (if i < 214 then 1 else 0))))) else 0) else (if i < 263 then (if i < 251 then (if i < 245 then 0 else (if i < 248 then (if i < 246 then 2 else (if i < 247 then 0 else 1)) else 0)) else (if i < 257 then 0 else (if i < 260 then 0 else (if i < 261 then 1 else 0)))) else (if i < 275 then 0 else (if i < 281 then (if i < 278 then (if i < 276 then 0 else (if i < 277 then 1 else 0)) else (if i < 279 then 0 else (if i < 280 then 0 else 1))) else 0)))) else (if i < 335 then (if i < 311 then (if i < 299 then (if i < 293 then (if i < 290 then 0 else (if i < 291 then 0 else (if i < 292 then 1 else 0))) else (if i < 296 then (if i < 294 then 1 else 0) else (if i < 297 then 3 else 0))) else (if i < 305 then (if i < 302 then 0 else (if i < 303 then 0 else (if i < 304 then 8 else 0))) else 0)) else (if i < 323 then (if i < 317 then 0 else (if i < 320 then 0 else (if i < 321 then 0 else (if i < 322 then 0 else 1)))) else 0)) else (if i < 359 then (if i < 347 then (if i < 341 then 0 else (if i < 344 then 0 else 1)) else (if i < 353 then (if i < 350 then (if i < 348 then 1 else 0) else 0) else (if i < 356 then (if i < 354 then 1 else 0) else 0))) else 0)))) else (if i < 574 then (if i < 478 then (if i < 430 then (if i < 406 then (if i < 394 then 0 else (if i < 400 then (if i < 397 then (if i < 395 then 0 else (if i < 396 then 2 else 0)) else 0) else 0)) else 0) else 0) else (if i < 526 then (if i < 502 then (if i < 490 then (if i < 484 then (if i < 481 then 0 else (if i < 482 then 0 else (if i < 483 then 8 else 0))) else (if i < 487 then (if i < 485 then 8 else 0) else 0)) else (if i < 496 then (if i < 493 then (if i < 491 then 1 else (if i < 492 then 1 else 8)) else 0) else (if i < 499 then (if i < 497 then 8 else 0) else 0))) else (if i < 514 then (if i < 508 then (if i < 505 then 0 else (if i < 506 then 0 else (if i < 507 then 1 else 0))) else (if i < 511 then (if i < 509 then 1 else 0) else 0)) else 0)) else (if i < 550 then (if i < 538 then (if i < 532 then (if i < 529 then (if i < 527 then 1 else (if i < 528 then 1 else 0)) else (if i < 530 then 0 else 1)) else 0) else 0) else 0))) else (if i < 670 then 0 else (if i < 718 then (if i < 694 then 0 else (if i < 706 then 0 else (if i < 712 then (if i < 709 then 0 else (if i < 710 then 0 else (if i < 711 then 1 else 0))) else (if i < 715 then (if i < 713 then 0 else (if i < 714 then 0 else 1)) else (if i < 716 then 0 else (if i < 717 then 1 else 0)))))) else (if i < 742 then (if i < 730 then (if i < 724 then 0 else (if i < 727 then (if i < 725 then 1 else 0) else (if i < 728 then 0 else (if i < 729 then 1 else 0)))) else 0) else (if i < 754 then 0 else (if i < 760 then 0 else (if i < 763 then (if i < 761 then 0 else (if i < 762 then 0 else 1)) else (if i < 764 then 0 else (if i < 765 then 1 else 0))))))))))

def v2 (i : Fin 766) : ℕ := v2Values i.val

end A165378Table

end

/- Local. -/
section

namespace A165378Proof

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
lemma initial_table :
    ((allRows.filter (fun r => decide (TopRow r))).map initial) =
      A165378Table.initial.map A165378Table.state := by
  decide +kernel

def LocalCheck (i : Fin 766) : Prop :=
  (if accept (A165378Table.state i) then 1 else 0) = A165378Table.accepted i ∧
  allRows.filterMap (step (A165378Table.state i)) =
    (A165378Table.succ i).map A165378Table.state

def FastLocalCheck (i : Fin 766) : Prop :=
  (if accept (A165378Table.state i) then 1 else 0) = A165378Table.accepted i ∧
  allRows.filterMap (fastStep (A165378Table.state i)) =
    (A165378Table.succ i).map A165378Table.state

def CheckAt (k : ℕ) : Prop :=
  if h : k < 766 then FastLocalCheck ⟨k, h⟩ else True

instance (i : Fin 766) : Decidable (LocalCheck i) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (i : Fin 766) : Decidable (FastLocalCheck i) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (k : ℕ) : Decidable (CheckAt k) := by
  unfold CheckAt
  infer_instance

/- Each small finite computation is checked separately by the kernel.  Keeping
these checks within one proof bounds memory without changing elaborator options. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem local_check_table (i : Fin 766) : LocalCheck i := by
  have h0 : ∀ j : Fin 8, CheckAt (8 * 0 + j.val) := by decide +kernel
  have h1 : ∀ j : Fin 8, CheckAt (8 * 1 + j.val) := by decide +kernel
  have h2 : ∀ j : Fin 8, CheckAt (8 * 2 + j.val) := by decide +kernel
  have h3 : ∀ j : Fin 8, CheckAt (8 * 3 + j.val) := by decide +kernel
  have h4 : ∀ j : Fin 8, CheckAt (8 * 4 + j.val) := by decide +kernel
  have h5 : ∀ j : Fin 8, CheckAt (8 * 5 + j.val) := by decide +kernel
  have h6 : ∀ j : Fin 8, CheckAt (8 * 6 + j.val) := by decide +kernel
  have h7 : ∀ j : Fin 8, CheckAt (8 * 7 + j.val) := by decide +kernel
  have h8 : ∀ j : Fin 8, CheckAt (8 * 8 + j.val) := by decide +kernel
  have h9 : ∀ j : Fin 8, CheckAt (8 * 9 + j.val) := by decide +kernel
  have h10 : ∀ j : Fin 8, CheckAt (8 * 10 + j.val) := by decide +kernel
  have h11 : ∀ j : Fin 8, CheckAt (8 * 11 + j.val) := by decide +kernel
  have h12 : ∀ j : Fin 8, CheckAt (8 * 12 + j.val) := by decide +kernel
  have h13 : ∀ j : Fin 8, CheckAt (8 * 13 + j.val) := by decide +kernel
  have h14 : ∀ j : Fin 8, CheckAt (8 * 14 + j.val) := by decide +kernel
  have h15 : ∀ j : Fin 8, CheckAt (8 * 15 + j.val) := by decide +kernel
  have h16 : ∀ j : Fin 8, CheckAt (8 * 16 + j.val) := by decide +kernel
  have h17 : ∀ j : Fin 8, CheckAt (8 * 17 + j.val) := by decide +kernel
  have h18 : ∀ j : Fin 8, CheckAt (8 * 18 + j.val) := by decide +kernel
  have h19 : ∀ j : Fin 8, CheckAt (8 * 19 + j.val) := by decide +kernel
  have h20 : ∀ j : Fin 8, CheckAt (8 * 20 + j.val) := by decide +kernel
  have h21 : ∀ j : Fin 8, CheckAt (8 * 21 + j.val) := by decide +kernel
  have h22 : ∀ j : Fin 8, CheckAt (8 * 22 + j.val) := by decide +kernel
  have h23 : ∀ j : Fin 8, CheckAt (8 * 23 + j.val) := by decide +kernel
  have h24 : ∀ j : Fin 8, CheckAt (8 * 24 + j.val) := by decide +kernel
  have h25 : ∀ j : Fin 8, CheckAt (8 * 25 + j.val) := by decide +kernel
  have h26 : ∀ j : Fin 8, CheckAt (8 * 26 + j.val) := by decide +kernel
  have h27 : ∀ j : Fin 8, CheckAt (8 * 27 + j.val) := by decide +kernel
  have h28 : ∀ j : Fin 8, CheckAt (8 * 28 + j.val) := by decide +kernel
  have h29 : ∀ j : Fin 8, CheckAt (8 * 29 + j.val) := by decide +kernel
  have h30 : ∀ j : Fin 8, CheckAt (8 * 30 + j.val) := by decide +kernel
  have h31 : ∀ j : Fin 8, CheckAt (8 * 31 + j.val) := by decide +kernel
  have h32 : ∀ j : Fin 8, CheckAt (8 * 32 + j.val) := by decide +kernel
  have h33 : ∀ j : Fin 8, CheckAt (8 * 33 + j.val) := by decide +kernel
  have h34 : ∀ j : Fin 8, CheckAt (8 * 34 + j.val) := by decide +kernel
  have h35 : ∀ j : Fin 8, CheckAt (8 * 35 + j.val) := by decide +kernel
  have h36 : ∀ j : Fin 8, CheckAt (8 * 36 + j.val) := by decide +kernel
  have h37 : ∀ j : Fin 8, CheckAt (8 * 37 + j.val) := by decide +kernel
  have h38 : ∀ j : Fin 8, CheckAt (8 * 38 + j.val) := by decide +kernel
  have h39 : ∀ j : Fin 8, CheckAt (8 * 39 + j.val) := by decide +kernel
  have h40 : ∀ j : Fin 8, CheckAt (8 * 40 + j.val) := by decide +kernel
  have h41 : ∀ j : Fin 8, CheckAt (8 * 41 + j.val) := by decide +kernel
  have h42 : ∀ j : Fin 8, CheckAt (8 * 42 + j.val) := by decide +kernel
  have h43 : ∀ j : Fin 8, CheckAt (8 * 43 + j.val) := by decide +kernel
  have h44 : ∀ j : Fin 8, CheckAt (8 * 44 + j.val) := by decide +kernel
  have h45 : ∀ j : Fin 8, CheckAt (8 * 45 + j.val) := by decide +kernel
  have h46 : ∀ j : Fin 8, CheckAt (8 * 46 + j.val) := by decide +kernel
  have h47 : ∀ j : Fin 8, CheckAt (8 * 47 + j.val) := by decide +kernel
  have h48 : ∀ j : Fin 8, CheckAt (8 * 48 + j.val) := by decide +kernel
  have h49 : ∀ j : Fin 8, CheckAt (8 * 49 + j.val) := by decide +kernel
  have h50 : ∀ j : Fin 8, CheckAt (8 * 50 + j.val) := by decide +kernel
  have h51 : ∀ j : Fin 8, CheckAt (8 * 51 + j.val) := by decide +kernel
  have h52 : ∀ j : Fin 8, CheckAt (8 * 52 + j.val) := by decide +kernel
  have h53 : ∀ j : Fin 8, CheckAt (8 * 53 + j.val) := by decide +kernel
  have h54 : ∀ j : Fin 8, CheckAt (8 * 54 + j.val) := by decide +kernel
  have h55 : ∀ j : Fin 8, CheckAt (8 * 55 + j.val) := by decide +kernel
  have h56 : ∀ j : Fin 8, CheckAt (8 * 56 + j.val) := by decide +kernel
  have h57 : ∀ j : Fin 8, CheckAt (8 * 57 + j.val) := by decide +kernel
  have h58 : ∀ j : Fin 8, CheckAt (8 * 58 + j.val) := by decide +kernel
  have h59 : ∀ j : Fin 8, CheckAt (8 * 59 + j.val) := by decide +kernel
  have h60 : ∀ j : Fin 8, CheckAt (8 * 60 + j.val) := by decide +kernel
  have h61 : ∀ j : Fin 8, CheckAt (8 * 61 + j.val) := by decide +kernel
  have h62 : ∀ j : Fin 8, CheckAt (8 * 62 + j.val) := by decide +kernel
  have h63 : ∀ j : Fin 8, CheckAt (8 * 63 + j.val) := by decide +kernel
  have h64 : ∀ j : Fin 8, CheckAt (8 * 64 + j.val) := by decide +kernel
  have h65 : ∀ j : Fin 8, CheckAt (8 * 65 + j.val) := by decide +kernel
  have h66 : ∀ j : Fin 8, CheckAt (8 * 66 + j.val) := by decide +kernel
  have h67 : ∀ j : Fin 8, CheckAt (8 * 67 + j.val) := by decide +kernel
  have h68 : ∀ j : Fin 8, CheckAt (8 * 68 + j.val) := by decide +kernel
  have h69 : ∀ j : Fin 8, CheckAt (8 * 69 + j.val) := by decide +kernel
  have h70 : ∀ j : Fin 8, CheckAt (8 * 70 + j.val) := by decide +kernel
  have h71 : ∀ j : Fin 8, CheckAt (8 * 71 + j.val) := by decide +kernel
  have h72 : ∀ j : Fin 8, CheckAt (8 * 72 + j.val) := by decide +kernel
  have h73 : ∀ j : Fin 8, CheckAt (8 * 73 + j.val) := by decide +kernel
  have h74 : ∀ j : Fin 8, CheckAt (8 * 74 + j.val) := by decide +kernel
  have h75 : ∀ j : Fin 8, CheckAt (8 * 75 + j.val) := by decide +kernel
  have h76 : ∀ j : Fin 8, CheckAt (8 * 76 + j.val) := by decide +kernel
  have h77 : ∀ j : Fin 8, CheckAt (8 * 77 + j.val) := by decide +kernel
  have h78 : ∀ j : Fin 8, CheckAt (8 * 78 + j.val) := by decide +kernel
  have h79 : ∀ j : Fin 8, CheckAt (8 * 79 + j.val) := by decide +kernel
  have h80 : ∀ j : Fin 8, CheckAt (8 * 80 + j.val) := by decide +kernel
  have h81 : ∀ j : Fin 8, CheckAt (8 * 81 + j.val) := by decide +kernel
  have h82 : ∀ j : Fin 8, CheckAt (8 * 82 + j.val) := by decide +kernel
  have h83 : ∀ j : Fin 8, CheckAt (8 * 83 + j.val) := by decide +kernel
  have h84 : ∀ j : Fin 8, CheckAt (8 * 84 + j.val) := by decide +kernel
  have h85 : ∀ j : Fin 8, CheckAt (8 * 85 + j.val) := by decide +kernel
  have h86 : ∀ j : Fin 8, CheckAt (8 * 86 + j.val) := by decide +kernel
  have h87 : ∀ j : Fin 8, CheckAt (8 * 87 + j.val) := by decide +kernel
  have h88 : ∀ j : Fin 8, CheckAt (8 * 88 + j.val) := by decide +kernel
  have h89 : ∀ j : Fin 8, CheckAt (8 * 89 + j.val) := by decide +kernel
  have h90 : ∀ j : Fin 8, CheckAt (8 * 90 + j.val) := by decide +kernel
  have h91 : ∀ j : Fin 8, CheckAt (8 * 91 + j.val) := by decide +kernel
  have h92 : ∀ j : Fin 8, CheckAt (8 * 92 + j.val) := by decide +kernel
  have h93 : ∀ j : Fin 8, CheckAt (8 * 93 + j.val) := by decide +kernel
  have h94 : ∀ j : Fin 8, CheckAt (8 * 94 + j.val) := by decide +kernel
  have h95 : ∀ j : Fin 8, CheckAt (8 * 95 + j.val) := by decide +kernel
  have blocks (b : Fin 96) : ∀ j : Fin 8, CheckAt (8 * b.val + j.val) := by
    fin_cases b
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14
    · exact h15
    · exact h16
    · exact h17
    · exact h18
    · exact h19
    · exact h20
    · exact h21
    · exact h22
    · exact h23
    · exact h24
    · exact h25
    · exact h26
    · exact h27
    · exact h28
    · exact h29
    · exact h30
    · exact h31
    · exact h32
    · exact h33
    · exact h34
    · exact h35
    · exact h36
    · exact h37
    · exact h38
    · exact h39
    · exact h40
    · exact h41
    · exact h42
    · exact h43
    · exact h44
    · exact h45
    · exact h46
    · exact h47
    · exact h48
    · exact h49
    · exact h50
    · exact h51
    · exact h52
    · exact h53
    · exact h54
    · exact h55
    · exact h56
    · exact h57
    · exact h58
    · exact h59
    · exact h60
    · exact h61
    · exact h62
    · exact h63
    · exact h64
    · exact h65
    · exact h66
    · exact h67
    · exact h68
    · exact h69
    · exact h70
    · exact h71
    · exact h72
    · exact h73
    · exact h74
    · exact h75
    · exact h76
    · exact h77
    · exact h78
    · exact h79
    · exact h80
    · exact h81
    · exact h82
    · exact h83
    · exact h84
    · exact h85
    · exact h86
    · exact h87
    · exact h88
    · exact h89
    · exact h90
    · exact h91
    · exact h92
    · exact h93
    · exact h94
    · exact h95
  have h := blocks ⟨i.val / 8, by omega⟩ ⟨i.val % 8, Nat.mod_lt _ (by omega)⟩
  have he : 8 * (i.val / 8) + i.val % 8 = i.val := by omega
  rw [he] at h
  have hf : FastLocalCheck i := by
    simpa only [CheckAt, dif_pos i.isLt] using h
  refine ⟨hf.1, ?_⟩
  have heq : fastStep (A165378Table.state i) = step (A165378Table.state i) :=
    funext (fastStep_eq_step _)
  simpa only [heq] using hf.2

theorem accept_table (i : Fin 766) :
    (if accept (A165378Table.state i) then 1 else 0) = A165378Table.accepted i :=
  (local_check_table i).1

theorem step_table (i : Fin 766) :
    allRows.filterMap (step (A165378Table.state i)) =
      (A165378Table.succ i).map A165378Table.state :=
  (local_check_table i).2

end A165378Proof

end

/- Certificate. -/
section

namespace A165378Table

abbrev QuadraticAt (i : Fin 766) : Prop :=
    ((succ i).map accepted).sum = v1 i ∧
    ((succ i).map v1).sum = v2 i ∧
    ((succ i).map v2).sum = c i ∧
    ((succ i).map q).sum = q i ∧
    ((succ i).map l).sum = l i + 2 * q i ∧
    ((succ i).map c).sum = c i + l i + q i

def tableIndex (n : ℕ) : Fin 766 := ⟨n % 766, Nat.mod_lt _ (by decide)⟩

def QuadraticBlock (k : ℕ) : Prop :=
  ∀ j : Fin 8, QuadraticAt (tableIndex (8 * k + j.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 32000000 in
lemma quadratic_blocks (k : Fin 96) : QuadraticBlock k.val := by
  have block_0 : QuadraticBlock 0 := by
    unfold QuadraticBlock
    decide +kernel
  have block_1 : QuadraticBlock 1 := by
    unfold QuadraticBlock
    decide +kernel
  have block_2 : QuadraticBlock 2 := by
    unfold QuadraticBlock
    decide +kernel
  have block_3 : QuadraticBlock 3 := by
    unfold QuadraticBlock
    decide +kernel
  have block_4 : QuadraticBlock 4 := by
    unfold QuadraticBlock
    decide +kernel
  have block_5 : QuadraticBlock 5 := by
    unfold QuadraticBlock
    decide +kernel
  have block_6 : QuadraticBlock 6 := by
    unfold QuadraticBlock
    decide +kernel
  have block_7 : QuadraticBlock 7 := by
    unfold QuadraticBlock
    decide +kernel
  have block_8 : QuadraticBlock 8 := by
    unfold QuadraticBlock
    decide +kernel
  have block_9 : QuadraticBlock 9 := by
    unfold QuadraticBlock
    decide +kernel
  have block_10 : QuadraticBlock 10 := by
    unfold QuadraticBlock
    decide +kernel
  have block_11 : QuadraticBlock 11 := by
    unfold QuadraticBlock
    decide +kernel
  have block_12 : QuadraticBlock 12 := by
    unfold QuadraticBlock
    decide +kernel
  have block_13 : QuadraticBlock 13 := by
    unfold QuadraticBlock
    decide +kernel
  have block_14 : QuadraticBlock 14 := by
    unfold QuadraticBlock
    decide +kernel
  have block_15 : QuadraticBlock 15 := by
    unfold QuadraticBlock
    decide +kernel
  have block_16 : QuadraticBlock 16 := by
    unfold QuadraticBlock
    decide +kernel
  have block_17 : QuadraticBlock 17 := by
    unfold QuadraticBlock
    decide +kernel
  have block_18 : QuadraticBlock 18 := by
    unfold QuadraticBlock
    decide +kernel
  have block_19 : QuadraticBlock 19 := by
    unfold QuadraticBlock
    decide +kernel
  have block_20 : QuadraticBlock 20 := by
    unfold QuadraticBlock
    decide +kernel
  have block_21 : QuadraticBlock 21 := by
    unfold QuadraticBlock
    decide +kernel
  have block_22 : QuadraticBlock 22 := by
    unfold QuadraticBlock
    decide +kernel
  have block_23 : QuadraticBlock 23 := by
    unfold QuadraticBlock
    decide +kernel
  have block_24 : QuadraticBlock 24 := by
    unfold QuadraticBlock
    decide +kernel
  have block_25 : QuadraticBlock 25 := by
    unfold QuadraticBlock
    decide +kernel
  have block_26 : QuadraticBlock 26 := by
    unfold QuadraticBlock
    decide +kernel
  have block_27 : QuadraticBlock 27 := by
    unfold QuadraticBlock
    decide +kernel
  have block_28 : QuadraticBlock 28 := by
    unfold QuadraticBlock
    decide +kernel
  have block_29 : QuadraticBlock 29 := by
    unfold QuadraticBlock
    decide +kernel
  have block_30 : QuadraticBlock 30 := by
    unfold QuadraticBlock
    decide +kernel
  have block_31 : QuadraticBlock 31 := by
    unfold QuadraticBlock
    decide +kernel
  have block_32 : QuadraticBlock 32 := by
    unfold QuadraticBlock
    decide +kernel
  have block_33 : QuadraticBlock 33 := by
    unfold QuadraticBlock
    decide +kernel
  have block_34 : QuadraticBlock 34 := by
    unfold QuadraticBlock
    decide +kernel
  have block_35 : QuadraticBlock 35 := by
    unfold QuadraticBlock
    decide +kernel
  have block_36 : QuadraticBlock 36 := by
    unfold QuadraticBlock
    decide +kernel
  have block_37 : QuadraticBlock 37 := by
    unfold QuadraticBlock
    decide +kernel
  have block_38 : QuadraticBlock 38 := by
    unfold QuadraticBlock
    decide +kernel
  have block_39 : QuadraticBlock 39 := by
    unfold QuadraticBlock
    decide +kernel
  have block_40 : QuadraticBlock 40 := by
    unfold QuadraticBlock
    decide +kernel
  have block_41 : QuadraticBlock 41 := by
    unfold QuadraticBlock
    decide +kernel
  have block_42 : QuadraticBlock 42 := by
    unfold QuadraticBlock
    decide +kernel
  have block_43 : QuadraticBlock 43 := by
    unfold QuadraticBlock
    decide +kernel
  have block_44 : QuadraticBlock 44 := by
    unfold QuadraticBlock
    decide +kernel
  have block_45 : QuadraticBlock 45 := by
    unfold QuadraticBlock
    decide +kernel
  have block_46 : QuadraticBlock 46 := by
    unfold QuadraticBlock
    decide +kernel
  have block_47 : QuadraticBlock 47 := by
    unfold QuadraticBlock
    decide +kernel
  have block_48 : QuadraticBlock 48 := by
    unfold QuadraticBlock
    decide +kernel
  have block_49 : QuadraticBlock 49 := by
    unfold QuadraticBlock
    decide +kernel
  have block_50 : QuadraticBlock 50 := by
    unfold QuadraticBlock
    decide +kernel
  have block_51 : QuadraticBlock 51 := by
    unfold QuadraticBlock
    decide +kernel
  have block_52 : QuadraticBlock 52 := by
    unfold QuadraticBlock
    decide +kernel
  have block_53 : QuadraticBlock 53 := by
    unfold QuadraticBlock
    decide +kernel
  have block_54 : QuadraticBlock 54 := by
    unfold QuadraticBlock
    decide +kernel
  have block_55 : QuadraticBlock 55 := by
    unfold QuadraticBlock
    decide +kernel
  have block_56 : QuadraticBlock 56 := by
    unfold QuadraticBlock
    decide +kernel
  have block_57 : QuadraticBlock 57 := by
    unfold QuadraticBlock
    decide +kernel
  have block_58 : QuadraticBlock 58 := by
    unfold QuadraticBlock
    decide +kernel
  have block_59 : QuadraticBlock 59 := by
    unfold QuadraticBlock
    decide +kernel
  have block_60 : QuadraticBlock 60 := by
    unfold QuadraticBlock
    decide +kernel
  have block_61 : QuadraticBlock 61 := by
    unfold QuadraticBlock
    decide +kernel
  have block_62 : QuadraticBlock 62 := by
    unfold QuadraticBlock
    decide +kernel
  have block_63 : QuadraticBlock 63 := by
    unfold QuadraticBlock
    decide +kernel
  have block_64 : QuadraticBlock 64 := by
    unfold QuadraticBlock
    decide +kernel
  have block_65 : QuadraticBlock 65 := by
    unfold QuadraticBlock
    decide +kernel
  have block_66 : QuadraticBlock 66 := by
    unfold QuadraticBlock
    decide +kernel
  have block_67 : QuadraticBlock 67 := by
    unfold QuadraticBlock
    decide +kernel
  have block_68 : QuadraticBlock 68 := by
    unfold QuadraticBlock
    decide +kernel
  have block_69 : QuadraticBlock 69 := by
    unfold QuadraticBlock
    decide +kernel
  have block_70 : QuadraticBlock 70 := by
    unfold QuadraticBlock
    decide +kernel
  have block_71 : QuadraticBlock 71 := by
    unfold QuadraticBlock
    decide +kernel
  have block_72 : QuadraticBlock 72 := by
    unfold QuadraticBlock
    decide +kernel
  have block_73 : QuadraticBlock 73 := by
    unfold QuadraticBlock
    decide +kernel
  have block_74 : QuadraticBlock 74 := by
    unfold QuadraticBlock
    decide +kernel
  have block_75 : QuadraticBlock 75 := by
    unfold QuadraticBlock
    decide +kernel
  have block_76 : QuadraticBlock 76 := by
    unfold QuadraticBlock
    decide +kernel
  have block_77 : QuadraticBlock 77 := by
    unfold QuadraticBlock
    decide +kernel
  have block_78 : QuadraticBlock 78 := by
    unfold QuadraticBlock
    decide +kernel
  have block_79 : QuadraticBlock 79 := by
    unfold QuadraticBlock
    decide +kernel
  have block_80 : QuadraticBlock 80 := by
    unfold QuadraticBlock
    decide +kernel
  have block_81 : QuadraticBlock 81 := by
    unfold QuadraticBlock
    decide +kernel
  have block_82 : QuadraticBlock 82 := by
    unfold QuadraticBlock
    decide +kernel
  have block_83 : QuadraticBlock 83 := by
    unfold QuadraticBlock
    decide +kernel
  have block_84 : QuadraticBlock 84 := by
    unfold QuadraticBlock
    decide +kernel
  have block_85 : QuadraticBlock 85 := by
    unfold QuadraticBlock
    decide +kernel
  have block_86 : QuadraticBlock 86 := by
    unfold QuadraticBlock
    decide +kernel
  have block_87 : QuadraticBlock 87 := by
    unfold QuadraticBlock
    decide +kernel
  have block_88 : QuadraticBlock 88 := by
    unfold QuadraticBlock
    decide +kernel
  have block_89 : QuadraticBlock 89 := by
    unfold QuadraticBlock
    decide +kernel
  have block_90 : QuadraticBlock 90 := by
    unfold QuadraticBlock
    decide +kernel
  have block_91 : QuadraticBlock 91 := by
    unfold QuadraticBlock
    decide +kernel
  have block_92 : QuadraticBlock 92 := by
    unfold QuadraticBlock
    decide +kernel
  have block_93 : QuadraticBlock 93 := by
    unfold QuadraticBlock
    decide +kernel
  have block_94 : QuadraticBlock 94 := by
    unfold QuadraticBlock
    decide +kernel
  have block_95 : QuadraticBlock 95 := by
    unfold QuadraticBlock
    decide +kernel
  fin_cases k
  · exact block_0
  · exact block_1
  · exact block_2
  · exact block_3
  · exact block_4
  · exact block_5
  · exact block_6
  · exact block_7
  · exact block_8
  · exact block_9
  · exact block_10
  · exact block_11
  · exact block_12
  · exact block_13
  · exact block_14
  · exact block_15
  · exact block_16
  · exact block_17
  · exact block_18
  · exact block_19
  · exact block_20
  · exact block_21
  · exact block_22
  · exact block_23
  · exact block_24
  · exact block_25
  · exact block_26
  · exact block_27
  · exact block_28
  · exact block_29
  · exact block_30
  · exact block_31
  · exact block_32
  · exact block_33
  · exact block_34
  · exact block_35
  · exact block_36
  · exact block_37
  · exact block_38
  · exact block_39
  · exact block_40
  · exact block_41
  · exact block_42
  · exact block_43
  · exact block_44
  · exact block_45
  · exact block_46
  · exact block_47
  · exact block_48
  · exact block_49
  · exact block_50
  · exact block_51
  · exact block_52
  · exact block_53
  · exact block_54
  · exact block_55
  · exact block_56
  · exact block_57
  · exact block_58
  · exact block_59
  · exact block_60
  · exact block_61
  · exact block_62
  · exact block_63
  · exact block_64
  · exact block_65
  · exact block_66
  · exact block_67
  · exact block_68
  · exact block_69
  · exact block_70
  · exact block_71
  · exact block_72
  · exact block_73
  · exact block_74
  · exact block_75
  · exact block_76
  · exact block_77
  · exact block_78
  · exact block_79
  · exact block_80
  · exact block_81
  · exact block_82
  · exact block_83
  · exact block_84
  · exact block_85
  · exact block_86
  · exact block_87
  · exact block_88
  · exact block_89
  · exact block_90
  · exact block_91
  · exact block_92
  · exact block_93
  · exact block_94
  · exact block_95

lemma quadratic_certificate (i : Fin 766) : QuadraticAt i := by
  have hk : i.val / 8 < 96 := by omega
  have hj : i.val % 8 < 8 := Nat.mod_lt _ (by decide)
  have h := quadratic_blocks ⟨i.val / 8, hk⟩ ⟨i.val % 8, hj⟩
  have he : tableIndex (8 * (i.val / 8) + i.val % 8) = i := by
    apply Fin.ext
    have hi := i.isLt
    dsimp [tableIndex]
    omega
  simpa only [he] using h

lemma base_three (i : Fin 766) : A165378Count.paths succ accepted 3 i = c i :=
  A165378Count.paths_three_of_vectors succ accepted v1 v2 c
    (fun i => (quadratic_certificate i).1)
    (fun i => (quadratic_certificate i).2.1)
    (fun i => (quadratic_certificate i).2.2.1) i

lemma initial_q : (initial.map q).sum = 9 := by decide +kernel
lemma initial_l : (initial.map l).sum = 76 := by decide +kernel
lemma initial_c : (initial.map c).sum = 158 := by decide +kernel

/-- Number of accepting paths for a board of height `n+4`. -/
theorem indexed_count (n : ℕ) :
    (initial.map (A165378Count.paths succ accepted (n + 3))).sum =
      9 * (n + 4) ^ 2 + 4 * (n + 4) - 2 :=
  A165378Count.initial_quadratic succ accepted q l c initial
    base_three
    (fun i => (quadratic_certificate i).2.2.2.1)
    (fun i => (quadratic_certificate i).2.2.2.2.1)
    (fun i => (quadratic_certificate i).2.2.2.2.2)
    initial_q initial_l initial_c n

end A165378Table

end

/- Enumerate. -/
section

namespace A165378Proof

theorem wordCount_closed (n : ℕ) :
    wordCount (n + 4) = 9 * (n + 4) ^ 2 + 4 * (n + 4) - 2 := by
  calc
    wordCount (n + 4) =
        (A165378Table.initial.map
          (A165378Count.paths A165378Table.succ A165378Table.accepted (n + 3))).sum :=
      wordCount_eq_paths allRows (sum_rows_of_equiv rowEquiv)
        A165378Table.state A165378Table.succ A165378Table.accepted A165378Table.initial
        step_table accept_table initial_table (n + 3)
    _ = _ := A165378Table.indexed_count n

theorem wordCount_formula (n : ℕ) (hn : 3 < n) :
    wordCount n = 9 * n ^ 2 + 4 * n - 2 := by
  have he : n - 4 + 4 = n := by omega
  simpa only [he] using wordCount_closed (n - 4)

end A165378Proof

end

theorem OMA.solution : type_of% @OMA.S_oeis_a165378.main := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    calc
      Nat.card {f : OMA.S_oeis_a165378.Cell (n + 1) → Fin 4 //
          OMA.S_oeis_a165378.Valid (n + 1) f} = A165378Proof.wordCount (n + 1) :=
        A165378Board.card_eq_wordCount
          (fun f => (A165378Run.goodWord_iff_valid f).symm)
      _ = _ := A165378Proof.wordCount_formula (n + 1) hn
