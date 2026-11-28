import OMAStatements.S_arxiv_2607_03584

/- Adapted from OpenAI, The dyadic case of the Erdős similarity conjecture, Apache-2.0.
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MeasureTheory/DyadicAvoidance
Port and statement bridge: @my-other-github-account. -/

-- OpenAI source module: WindowRecursion
section

namespace OAI

namespace Problem310.WindowRecursion

/-- Total span occupied by the windows in a complete tree of the given height.
At a bottom-level child there is no following subtree gap; at higher levels the
incoming window is followed by one gap and the complete child subtree. -/
def span (M g r₀ : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 =>
      M * (max r₀ (g + span M g r₀ h) +
        if h = 0 then 0 else g + span M g r₀ h) + (M - 1) * g

/-- Length of an incoming window whose parent has height `h + 1`.
The value at height zero is unused and is set equal to the threshold. -/
def length (M g r₀ : ℕ) : ℕ → ℕ
  | 0 => r₀
  | h + 1 => max r₀ (g + span M g r₀ h)

/-- Span of one incoming-edge window and the subtree beneath that edge. -/
def childSpan (M g r₀ h : ℕ) : ℕ :=
  length M g r₀ (h + 1) + if h = 0 then 0 else g + span M g r₀ h

@[simp] theorem span_zero (M g r₀ : ℕ) : span M g r₀ 0 = 0 := rfl

@[simp] theorem length_zero (M g r₀ : ℕ) : length M g r₀ 0 = r₀ := rfl

@[simp] theorem length_succ (M g r₀ h : ℕ) :
    length M g r₀ (h + 1) = max r₀ (g + span M g r₀ h) := rfl

theorem span_succ (M g r₀ h : ℕ) :
    span M g r₀ (h + 1) = M * childSpan M g r₀ h + (M - 1) * g := rfl

@[simp] theorem childSpan_zero (M g r₀ : ℕ) :
    childSpan M g r₀ 0 = length M g r₀ 1 := by
  simp [childSpan]

@[simp] theorem span_one (M g r₀ : ℕ) :
    span M g r₀ 1 = M * length M g r₀ 1 + (M - 1) * g := by
  rw [span_succ, childSpan_zero]

theorem childSpan_succ (M g r₀ h : ℕ) :
    childSpan M g r₀ (h + 1) =
      length M g r₀ (h + 2) + g + span M g r₀ (h + 1) := by
  simp [childSpan, Nat.add_assoc]

theorem threshold_le_length (M g r₀ h : ℕ) : r₀ ≤ length M g r₀ h := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact le_max_left _ _

theorem gap_add_span_le_length (M g r₀ h : ℕ) :
    g + span M g r₀ h ≤ length M g r₀ (h + 1) := le_max_right _ _

theorem length_pos (M g r₀ h : ℕ) (hr₀ : 0 < r₀) :
    0 < length M g r₀ h := hr₀.trans_le (threshold_le_length _ _ _ _)

/-- The key padding estimate: an entire child block occupies no more than twice
its incoming window length, independently of the size of the complete tree. -/
theorem childSpan_le_twice_length (M g r₀ h : ℕ) :
    childSpan M g r₀ h ≤ 2 * length M g r₀ (h + 1) := by
  have hp := gap_add_span_le_length M g r₀ h
  dsimp [childSpan]
  split_ifs <;> omega

end Problem310.WindowRecursion

end OAI

end

-- OpenAI source module: AddressInjectivity
section

namespace OAI

universe u_A u_I u_X u_K

noncomputable section

namespace Problem310.AddressInjectivity

/-- Two descendants of different children cannot be the same leaf. -/
theorem child_eq_of_common_descendant {A : Type u_A} {U L : List A} {i j : A}
    (hi : U ++ [i] <+: L) (hj : U ++ [j] <+: L) : i = j := by
  have hi' := List.prefix_iff_eq_take.mp hi
  have hj' := List.prefix_iff_eq_take.mp hj
  have heq : U ++ [i] = U ++ [j] := by
    rw [hi', hj']
    simp
  simpa using List.append_cancel_left heq

/-- A pointwise-selected terminal leaf still gives distinct terminal table addresses.
The selected leaf may depend arbitrarily on the selector outcome: only its child
subtree and the refinement of its terminal grid matter. -/
theorem terminalAddress_injective {I : Type u_I} {A : Type u_A} {X : Type u_X} {K : Type u_K}
    (U : List A) (child : I → A) (point : I → X)
    (leaf : I → List A) (base : A → ℕ) (level : List A → ℕ)
    (key : ℕ → X → K)
    (hprefix : ∀ i, U ++ [child i] <+: leaf i)
    (hlevel : ∀ i, base (child i) ≤ level (leaf i))
    (hrefine : ∀ {b B : ℕ} {x y : X}, b ≤ B →
      key B x = key B y → key b x = key b y)
    (hseparate : ∀ {i j : I}, child i = child j → i ≠ j →
      key (base (child i)) (point i) ≠ key (base (child i)) (point j)) :
    Function.Injective (fun i => (leaf i, key (level (leaf i)) (point i))) := by
  intro i j hij
  have hleaf : leaf i = leaf j := congrArg Prod.fst hij
  have hchild : child i = child j :=
    child_eq_of_common_descendant (hprefix i) (hleaf.symm ▸ hprefix j)
  have hkey : key (level (leaf i)) (point i) = key (level (leaf i)) (point j) := by
    have h := congrArg Prod.snd hij
    simpa only [hleaf] using h
  by_contra hne
  exact hseparate hchild hne (hrefine (hlevel i) hkey)

end Problem310.AddressInjectivity

end

end OAI

end

-- OpenAI source module: TreePreorder
section

namespace OAI

noncomputable section

namespace Problem310.TreePreorder

/-- Edge paths in the complete ordered `q`-ary tree, in depth-first preorder. -/
def edgePaths (q : ℕ) : ℕ → List (List (Fin q))
  | 0 => []
  | d + 1 => (List.finRange q).flatMap fun i =>
      [i] :: (edgePaths q d).map (List.cons i)

/-- Number of edges in the complete tree. -/
def edgeCount (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => q * (1 + edgeCount q d)

@[simp] theorem edgePaths_zero (q : ℕ) : edgePaths q 0 = [] := rfl

@[simp] theorem edgePaths_succ (q d : ℕ) :
    edgePaths q (d + 1) = (List.finRange q).flatMap (fun i =>
      [i] :: (edgePaths q d).map (List.cons i)) := rfl

/-- Exactly the nonempty paths of length at most the tree depth occur. -/
theorem mem_edgePaths_iff (q d : ℕ) (p : List (Fin q)) :
    p ∈ edgePaths q d ↔ p ≠ [] ∧ p.length ≤ d := by
  induction d generalizing p with
  | zero => simp [edgePaths]
  | succ d ih =>
      cases p with
      | nil => simp [edgePaths]
      | cons i p =>
          simp only [edgePaths, List.mem_flatMap, List.mem_finRange, true_and,
            List.mem_cons, List.cons.injEq, List.mem_map, List.length_cons,
            ]
          constructor
          · rintro ⟨j, h | ⟨p', hp', h⟩⟩
            · rcases h with ⟨rfl, rfl⟩
              simp
            · rcases h with ⟨rfl, rfl⟩
              have hlen := (ih p').mp hp'
              exact ⟨by simp, Nat.succ_le_succ hlen.2⟩
          · intro hp
            by_cases he : p = []
            · subst p
              exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩
            · exact ⟨i, Or.inr ⟨p, (ih p).mpr ⟨he, by omega⟩, ⟨rfl, rfl⟩⟩⟩

@[simp] theorem length_edgePaths (q d : ℕ) :
    (edgePaths q d).length = edgeCount q d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [edgePaths, edgeCount, List.length_flatMap, ih, add_comm]

/-- Each child block consists entirely of paths with that child as first entry. -/
theorem mem_childBlock_prefix (q d : ℕ) (i : Fin q) (p : List (Fin q))
    (hp : p ∈ [i] :: (edgePaths q d).map (List.cons i)) :
    ∃ s, p = i :: s := by
  rcases List.mem_cons.mp hp with h | h
  · exact ⟨[], h⟩
  · obtain ⟨s, hs, h⟩ := List.mem_map.mp h
    exact ⟨s, h.symm⟩

/-- The preorder contains no duplicate edge path. -/
theorem nodup_edgePaths (q d : ℕ) : (edgePaths q d).Nodup := by
  induction d with
  | zero => simp [edgePaths]
  | succ d ih =>
      rw [edgePaths_succ, List.nodup_flatMap]
      constructor
      · intro i hi
        rw [List.nodup_cons]
        constructor
        · intro hm
          obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
          have hp0 : p = [] := (List.cons.inj heq).2
          subst p
          simp [mem_edgePaths_iff] at hp
        · exact ih.map (by intro a b h; exact (List.cons.inj h).2)
      · apply (List.nodup_finRange q).imp
        intro i j hij p hp hq
        obtain ⟨s, rfl⟩ := mem_childBlock_prefix q d i p hp
        obtain ⟨t, heq⟩ := mem_childBlock_prefix q d j (i :: s) hq
        exact hij (List.cons.inj heq).1

/-- The finite type of tree edges, represented by nonempty bounded-depth paths. -/
def Edge (q d : ℕ) := {p : List (Fin q) // p ∈ edgePaths q d}

instance (q d : ℕ) : Fintype (Edge q d) := by
  classical
  unfold Edge
  exact Fintype.ofFinset (edgePaths q d).toFinset (by intro p; exact List.mem_toFinset)

@[simp] theorem edge_nonempty {q d : ℕ} (e : Edge q d) : e.val ≠ [] :=
  ((mem_edgePaths_iff q d e.val).mp e.property).1

/-- Convert a nonempty bounded path into the finite edge type. -/
def mkEdge {q d : ℕ} (p : List (Fin q)) (hne : p ≠ []) (hlen : p.length ≤ d) :
    Edge q d := ⟨p, (mem_edgePaths_iff q d p).mpr ⟨hne, hlen⟩⟩

@[simp] theorem mkEdge_val {q d : ℕ} (p : List (Fin q))
    (hne : p ≠ []) (hlen : p.length ≤ d) :
    (mkEdge p hne hlen).val = p := rfl

/-- The preorder gives the canonical enumeration of finite tree edges. -/
def edgeEquivFin (q d : ℕ) : Edge q d ≃ Fin (edgeCount q d) :=
  (List.Nodup.getEquiv (edgePaths q d) (nodup_edgePaths q d)).symm.trans
    (finCongr (length_edgePaths q d))

@[simp] theorem card_Edge (q d : ℕ) : Fintype.card (Edge q d) = edgeCount q d := by
  rw [Fintype.card_congr (edgeEquivFin q d), Fintype.card_fin]

/-- Edges corresponding to appending a child at a strict internal node. -/
def childEdge {q d : ℕ} (P : List (Fin q)) (hP : P.length < d) (i : Fin q) :
    Edge q d := mkEdge (P ++ [i]) (by simp) (by simp; omega)

@[simp] theorem childEdge_val {q d : ℕ} (P : List (Fin q))
    (hP : P.length < d) (i : Fin q) : (childEdge P hP i).val = P ++ [i] := rfl

end Problem310.TreePreorder

end

end OAI

end

-- OpenAI source module: TreePreorderRank
section

namespace OAI

namespace Problem310.TreePreorderRank

/-- Number of nodes, including the root, in the complete `K`-ary tree of depth `d`. -/
def size (K : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + K * size K d

/-- Preorder rank of a path. On paths of length at most `d`, this is the usual
zero-based root-first rank in the complete tree. -/
def rank {K : ℕ} : ℕ → List (Fin K) → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | d + 1, i :: p => 1 + i.val * size K d + rank d p

@[simp] theorem size_zero (K : ℕ) : size K 0 = 1 := rfl
@[simp] theorem size_succ (K d : ℕ) : size K (d + 1) = 1 + K * size K d := rfl
@[simp] theorem rank_nil {K : ℕ} (d : ℕ) : rank d ([] : List (Fin K)) = 0 := by
  cases d <;> rfl
@[simp] theorem rank_cons {K : ℕ} (d : ℕ) (i : Fin K) (p : List (Fin K)) :
    rank (d + 1) (i :: p) = 1 + i.val * size K d + rank d p := rfl

/-- Every valid node has rank strictly below the total number of nodes. -/
theorem rank_lt_size {K d : ℕ} {p : List (Fin K)} (hp : p.length ≤ d) :
    rank d p < size K d := by
  induction d generalizing p with
  | zero => simp [rank, size]
  | succ d ih =>
    cases p with
    | nil => simp [rank, size]
    | cons i p =>
      have hp' : p.length ≤ d := by simpa using hp
      have hr := ih hp'
      have hi : i.val + 1 ≤ K := i.isLt
      have hm := Nat.mul_le_mul_right (size K d) hi
      simp only [rank_cons, size_succ]
      nlinarith

/-- A nonroot valid node has positive rank. -/
theorem rank_pos {K d : ℕ} {p : List (Fin K)}
    (hp : p.length ≤ d) (hne : p ≠ []) : 0 < rank d p := by
  cases p with
  | nil => exact (hne rfl).elim
  | cons i p =>
    cases d with
    | zero => simp at hp
    | succ d => simp [rank]

/-- Descending into a node adds the local preorder rank in that node's subtree. -/
theorem rank_append {K d : ℕ} {p : List (Fin K)} (hp : p.length ≤ d)
    (q : List (Fin K)) :
    rank d (p ++ q) = rank d p + rank (d - p.length) q := by
  induction p generalizing d with
  | nil => simp
  | cons i p ih =>
    cases d with
    | zero => simp at hp
    | succ d =>
      have hp' : p.length ≤ d := by simpa using hp
      simp only [List.cons_append, rank_cons, List.length_cons, Nat.add_sub_add_right]
      rw [ih hp']
      omega

/-- A subtree occupies one contiguous interval of the preorder ranks. -/
theorem rank_append_bounds {K d : ℕ} {p q : List (Fin K)}
    (hpq : (p ++ q).length ≤ d) :
    rank d p ≤ rank d (p ++ q) ∧
      rank d (p ++ q) < rank d p + size K (d - p.length) := by
  have hp : p.length ≤ d := by simp only [List.length_append] at hpq; omega
  have hq : q.length ≤ d - p.length := by simp only [List.length_append] at hpq; omega
  rw [rank_append hp]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (rank_lt_size hq) _⟩

/-- The entire subtree of an earlier child precedes the entire subtree of a later child. -/
theorem rank_cons_lt_rank_cons {K d : ℕ} {i j : Fin K} {p q : List (Fin K)}
    (hij : i < j) (hp : p.length ≤ d) (_hq : q.length ≤ d) :
    rank (d + 1) (i :: p) < rank (d + 1) (j :: q) := by
  have hr := rank_lt_size hp
  have hi : i.val + 1 ≤ j.val := hij
  have hm := Nat.mul_le_mul_right (size K d) hi
  simp only [rank_cons]
  nlinarith

/-- Ordered sibling subtrees remain ordered after any common ancestral prefix. -/
theorem rank_sibling_descendants_lt {K d : ℕ} {P p q : List (Fin K)} {i j : Fin K}
    (hij : i < j) (hp : (P ++ i :: p).length ≤ d)
    (hq : (P ++ j :: q).length ≤ d) :
    rank d (P ++ i :: p) < rank d (P ++ j :: q) := by
  have hP : P.length ≤ d := by simp only [List.length_append, List.length_cons] at hp; omega
  rw [rank_append hP, rank_append hP]
  cases heq : d - P.length with
  | zero => simp only [List.length_append, List.length_cons] at hp; omega
  | succ k =>
    have hp' : p.length ≤ k := by simp only [List.length_append, List.length_cons] at hp; omega
    have hq' : q.length ≤ k := by simp only [List.length_append, List.length_cons] at hq; omega
    exact Nat.add_lt_add_left (rank_cons_lt_rank_cons hij hp' hq') _

/-- Preorder ranks distinguish every two valid paths. -/
theorem rank_injective_on {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (heq : rank d p = rank d q) : p = q := by
  induction d generalizing p q with
  | zero =>
    have hp0 : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
    have hq0 : q = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hq)
    exact hp0.trans hq0.symm
  | succ d ih =>
    cases p with
    | nil =>
      cases q with
      | nil => rfl
      | cons j q => simp only [rank_nil, rank_cons] at heq; omega
    | cons i p =>
      cases q with
      | nil => simp [rank] at heq
      | cons j q =>
        have hp' : p.length ≤ d := by simpa using hp
        have hq' : q.length ≤ d := by simpa using hq
        have hij : i = j := by
          rcases lt_trichotomy i j with h | h | h
          · exact False.elim ((rank_cons_lt_rank_cons h hp' hq').ne heq)
          · exact h
          · exact False.elim ((rank_cons_lt_rank_cons h hq' hp').ne heq.symm)
        subst j
        have heq' : rank d p = rank d q := by simpa only [rank_cons, Nat.add_left_cancel_iff] using heq
        exact congrArg (List.cons i) (ih hp' hq' heq')

/-- The interval occupied by a subtree is contained in the whole tree's interval. -/
theorem subtree_end_le_size {K d : ℕ} {p : List (Fin K)} (hp : p.length ≤ d) :
    rank d p + size K (d - p.length) ≤ size K d := by
  induction d generalizing p with
  | zero => simp [rank, size]
  | succ d ih =>
    cases p with
    | nil => simp
    | cons i p =>
      have hp' : p.length ≤ d := by simpa using hp
      have he := ih hp'
      have hi : i.val + 1 ≤ K := i.isLt
      have hm := Nat.mul_le_mul_right (size K d) hi
      simp only [rank_cons, List.length_cons, Nat.add_sub_add_right, size_succ]
      nlinarith

/-- The descendants of a path are exactly a contiguous half-open interval of ranks. -/
theorem isPrefix_iff_rank_bounds {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) :
    List.IsPrefix p q ↔ rank d p ≤ rank d q ∧
      rank d q < rank d p + size K (d - p.length) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact rank_append_bounds hq
  · intro h
    induction d generalizing p q with
    | zero =>
      have hp0 : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
      subst p
      exact List.nil_prefix
    | succ d ih =>
      cases p with
      | nil => exact List.nil_prefix
      | cons i p =>
        cases q with
        | nil =>
          have hpos := rank_pos hp (by simp)
          simp only [rank_nil] at h
          omega
        | cons j q =>
          have hp' : p.length ≤ d := by simpa using hp
          have hq' : q.length ≤ d := by simpa using hq
          have hpEnd := subtree_end_le_size hp'
          have hrq := rank_lt_size hq'
          simp only [rank_cons, List.length_cons, Nat.add_sub_add_right] at h
          have hij : i = j := by
            rcases lt_trichotomy i j with hij | hij | hji
            · have hi : i.val + 1 ≤ j.val := hij
              have hm := Nat.mul_le_mul_right (size K d) hi
              exfalso
              nlinarith [h.2]
            · exact hij
            · have hi : j.val + 1 ≤ i.val := hji
              have hm := Nat.mul_le_mul_right (size K d) hi
              exfalso
              nlinarith [h.1]
          subst j
          apply List.cons_prefix_cons.mpr
          refine ⟨rfl, ih hp' hq' ?_⟩
          omega

/-- Zero-based rank among edges, obtained by removing the root's rank. -/
def edgeRank {K : ℕ} (d : ℕ) (p : List (Fin K)) : ℕ := rank d p - 1

theorem edgeRank_add_one {K d : ℕ} {p : List (Fin K)}
    (hp : p.length ≤ d) (hne : p ≠ []) : edgeRank d p + 1 = rank d p := by
  have := rank_pos hp hne
  unfold edgeRank
  omega

theorem edgeRank_injective_on {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (hp0 : p ≠ []) (hq0 : q ≠ [])
    (heq : edgeRank d p = edgeRank d q) : p = q := by
  apply rank_injective_on hp hq
  rw [← edgeRank_add_one hp hp0, ← edgeRank_add_one hq hq0, heq]

theorem edgeRank_sibling_descendants_lt {K d : ℕ} {P p q : List (Fin K)} {i j : Fin K}
    (hij : i < j) (hp : (P ++ i :: p).length ≤ d)
    (hq : (P ++ j :: q).length ≤ d) :
    edgeRank d (P ++ i :: p) < edgeRank d (P ++ j :: q) := by
  have hlt := rank_sibling_descendants_lt hij hp hq
  have hpos := rank_pos hp (by simp)
  unfold edgeRank
  omega

/-- Edge ranks give the same exact contiguous-subtree characterization without the root slot. -/
theorem isPrefix_iff_edgeRank_bounds {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (hp0 : p ≠ []) (hq0 : q ≠ []) :
    List.IsPrefix p q ↔ edgeRank d p ≤ edgeRank d q ∧
      edgeRank d q < edgeRank d p + size K (d - p.length) := by
  rw [isPrefix_iff_rank_bounds hp hq]
  have hpR := edgeRank_add_one hp hp0
  have hqR := edgeRank_add_one hq hq0
  omega

end Problem310.TreePreorderRank

end OAI

end

-- OpenAI source module: WindowData
section

namespace OAI

noncomputable section

namespace Problem310

/-- An edge is identified with the nonempty path to its child. -/
def ValidWindowEdge {q : ℕ} (d : ℕ) (P : List (Fin q)) : Prop :=
  P ≠ [] ∧ P.length ≤ d

/-- Deterministic window interface shared by the finite router and its
geometric/probabilistic estimates. `q` is the TOTAL number of children.
Only the two ordering comparisons actually used by routing are required;
a preorder construction can supply them from its general rank gap bound. -/
structure WindowData (q d g r₀ : ℕ) where
  r : ℕ → ℕ
  a : List (Fin q) → ℕ
  b : List (Fin q) → ℕ
  bstar : List (Fin q) → ℕ
  length_pos : ∀ P : List (Fin q), ValidWindowEdge d P → 1 ≤ r (d + 1 - P.length)
  length_threshold : ∀ P : List (Fin q), ValidWindowEdge d P → r₀ ≤ r (d + 1 - P.length)
  start_three : ∀ P, ValidWindowEdge d P → 3 ≤ a P
  endpoint : ∀ P, ValidWindowEdge d P →
    b P + 1 = a P + r (d + 1 - P.length)
  gap_prefix : ∀ P Q, ValidWindowEdge d P → ValidWindowEdge d Q →
    P.IsPrefix Q → P ≠ Q → b P + g < a Q
  gap_sibling : ∀ (P : List (Fin q)) (i j : Fin q) (tail : List (Fin q)),
    i < j → ValidWindowEdge d (P ++ [i]) → ValidWindowEdge d (P ++ j :: tail) →
      b (P ++ [i]) + g < a (P ++ j :: tail)
  descendant_bounds : ∀ P Q, ValidWindowEdge d P → ValidWindowEdge d Q →
    P.IsPrefix Q → b P ≤ b Q ∧ b Q ≤ bstar P
  padding : ∀ P, ValidWindowEdge d P →
    bstar P + 1 ≤ a P + 2 * r (d + 1 - P.length)

namespace WindowData

variable {q d g r₀ : ℕ} (W : WindowData q d g r₀)

abbrev length (P : List (Fin q)) : ℕ := W.r (d + 1 - P.length)

def window (P : List (Fin q)) : Finset ℕ := Finset.Icc (W.a P) (W.b P)

lemma card_window (P : List (Fin q)) (hP : ValidWindowEdge d P) :
    (W.window P).card = W.length P := by
  rw [window, Nat.card_Icc]
  have hend := W.endpoint P hP
  dsimp [length]
  omega

end WindowData
end Problem310

end

end OAI

end

-- OpenAI source module: GridGeometry
section

namespace OAI

noncomputable section
namespace Problem310

/-- The integer label of the half-open periodic grid cell containing a point. -/
def periodicGridKey (q x : ℝ) : ℤ := ⌊q * Int.fract x⌋

/-- The periodic label is the residue of the label on the real-line grid. -/
theorem periodicGridKey_eq_emod (q : ℕ) (hq : 0 < q) (x : ℝ) :
    periodicGridKey q x = ⌊(q : ℝ) * x⌋ % (q : ℤ) := by
  unfold periodicGridKey Int.fract
  rw [mul_sub]
  have hc : (q : ℝ) * (⌊x⌋ : ℝ) = (((q : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hc, Int.floor_sub_intCast, Int.emod_def]
  have hf := Int.natCast_mul_floor_div_cancel (R := ℝ) (Nat.ne_of_gt hq) x
  rw [hf]

/-- Absence of a real-line grid boundary between ordered points preserves keys.
The interval is open at its left end, so a center on a boundary is allowed. -/
theorem periodicGridKey_eq_of_no_crossing (q : ℕ) (hq : 0 < q) {x y : ℝ}
    (hxy : x ≤ y) (hcross : ∀ k : ℤ, (k : ℝ) / q ∉ Set.Ioc x y) :
    periodicGridKey q x = periodicGridKey q y := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hmono : ⌊(q : ℝ) * x⌋ ≤ ⌊(q : ℝ) * y⌋ :=
    Int.floor_mono (mul_le_mul_of_nonneg_left hxy hqpos.le)
  have hfloors : ⌊(q : ℝ) * x⌋ = ⌊(q : ℝ) * y⌋ := by
    by_contra hne
    have hlt : ⌊(q : ℝ) * x⌋ + 1 ≤ ⌊(q : ℝ) * y⌋ := by omega
    apply hcross (⌊(q : ℝ) * x⌋ + 1)
    constructor
    · apply (lt_div_iff₀ hqpos).mpr
      have h := Int.lt_floor_add_one ((q : ℝ) * x)
      push_cast
      nlinarith
    · apply (div_le_iff₀ hqpos).mpr
      have hcast : ((⌊(q : ℝ) * x⌋ + 1 : ℤ) : ℝ) ≤
          (⌊(q : ℝ) * y⌋ : ℝ) := by exact_mod_cast hlt
      have h := Int.floor_le ((q : ℝ) * y)
      nlinarith
  rw [periodicGridKey_eq_emod q hq, periodicGridKey_eq_emod q hq, hfloors]

/-- Periodic cells used for a dyadic window with last index `b`. -/
def dyadicGridKey (b : ℕ) (x : ℝ) : ℤ := periodicGridKey ((2 : ℝ) ^ (b + 2)) x

@[simp] theorem dyadicGridKey_add_one (b : ℕ) (x : ℝ) :
    dyadicGridKey b (x + 1) = dyadicGridKey b x := by
  simp [dyadicGridKey, periodicGridKey, Int.fract_add_one]

/-- Fine dyadic grid labels determine all coarser labels by integer division. -/
theorem dyadicGridKey_nested {b B : ℕ} (hb : b ≤ B) (x : ℝ) :
    dyadicGridKey B x / (2 : ℤ) ^ (B - b) = dyadicGridKey b x := by
  have hp : (2 : ℝ) ^ (B + 2) = ((2 : ℕ) ^ (B - b) : ℝ) * (2 : ℝ) ^ (b + 2) := by
    push_cast
    rw [← pow_add]
    congr 1
    omega
  unfold dyadicGridKey periodicGridKey
  rw [hp, mul_assoc]
  have h := Int.natCast_mul_floor_div_cancel (R := ℝ)
    (n := (2 : ℕ) ^ (B - b)) (by positivity) ((2 : ℝ) ^ (b + 2) * Int.fract x)
  simpa using h

private theorem half_pow_antitone : Antitone (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) :=
  pow_right_anti₀ (by norm_num) (by norm_num)

/-- The no-crossing stability condition for a later window preserves an earlier key. -/
theorem dyadicGridKey_eq_of_stable {a b n : ℕ} {x t : ℝ}
    (han : a ≤ n) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (hstable : ∀ k : ℤ, (k : ℝ) / (2 : ℝ) ^ (b + 2) ∉
      Set.Ioc x (x + 2 * ((2 : ℝ)⁻¹) ^ a)) :
    dyadicGridKey b (x + t * ((2 : ℝ)⁻¹) ^ n) = dyadicGridKey b x := by
  have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ n := by positivity
  have hp' : 0 ≤ ((2 : ℝ)⁻¹) ^ a := by positivity
  have hn := half_pow_antitone han
  have hstep : 0 ≤ t * ((2 : ℝ)⁻¹) ^ n :=
    mul_nonneg (by linarith [ht.1]) hp
  have hbound : t * ((2 : ℝ)⁻¹) ^ n ≤ 2 * ((2 : ℝ)⁻¹) ^ a := by
    nlinarith [ht.2]
  have hkey := periodicGridKey_eq_of_no_crossing ((2 : ℕ) ^ (b + 2))
    (by positivity) (show x ≤ x + t * ((2 : ℝ)⁻¹) ^ n by linarith)
    (fun k hk ↦ hstable k ⟨by simpa using hk.1, by
      have hk' : (k : ℝ) / (2 : ℝ) ^ (b + 2) ≤ x + t * ((2 : ℝ)⁻¹) ^ n := by
        simpa using hk.2
      linarith⟩)
  simpa [dyadicGridKey] using hkey.symm

end Problem310

end

end OAI

end

-- OpenAI source module: GridSeparation
section

namespace OAI

universe u_α

noncomputable section

namespace Problem310.GridSeparation

/-- The periodic key of a real point in a grid of mesh `1 / q`. -/
def periodicKey (q x : ℝ) : ℤ := ⌊q * Int.fract x⌋

lemma periodicKey_add_one (q x : ℝ) :
    periodicKey q (x + 1) = periodicKey q x := by
  simp [periodicKey]

/-- Points separated by at least one grid mesh in both circular directions
cannot have the same periodic key. This includes points on cell boundaries. -/
lemma periodicKey_ne_of_separated {q x y : ℝ} (hq : 0 < q)
    (hlo : 1 ≤ q * (y - x)) (hhi : q * (y - x) ≤ q - 1) :
    periodicKey q x ≠ periodicKey q y := by
  intro heq
  have hxlo := Int.floor_le (q * Int.fract x)
  have hxhi := Int.lt_floor_add_one (q * Int.fract x)
  have hylo := Int.floor_le (q * Int.fract y)
  have hyhi := Int.lt_floor_add_one (q * Int.fract y)
  change ⌊q * Int.fract x⌋ = ⌊q * Int.fract y⌋ at heq
  have hcast : (⌊q * Int.fract x⌋ : ℝ) = (⌊q * Int.fract y⌋ : ℝ) :=
    congrArg (fun n : ℤ => (n : ℝ)) heq
  have hdifflo : -1 < q * (Int.fract y - Int.fract x) := by nlinarith
  have hdiffhi : q * (Int.fract y - Int.fract x) < 1 := by nlinarith
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  let k : ℤ := ⌊y⌋ - ⌊x⌋
  have hk : (k : ℝ) = y - x - (Int.fract y - Int.fract x) := by
    simp only [k, Int.cast_sub]
    linarith
  have hkpos : 0 < (k : ℝ) := by nlinarith
  have hklt : (k : ℝ) < 1 := by nlinarith
  have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hklt' : k < (1 : ℤ) := by exact_mod_cast hklt
  omega

lemma periodicKey_ne_of_small_shift {q x d : ℝ} (hq : 4 ≤ q)
    (hlo : 1 ≤ q * d) (hhi : d ≤ 1 / 4) :
    periodicKey q x ≠ periodicKey q (x + d) := by
  apply periodicKey_ne_of_separated (by linarith)
  · simpa using hlo
  · have hmul := mul_le_mul_of_nonneg_left hhi (show 0 ≤ q by linarith)
    have : q * d ≤ q - 1 := by nlinarith
    simpa using this

lemma mesh_mul_dyadic (b : ℕ) :
    (2 : ℝ) ^ (b + 2) * (2 : ℝ)⁻¹ ^ b = 4 := by
  rw [pow_add, inv_pow]
  have hb : (2 : ℝ) ^ b ≠ 0 := by positivity
  field_simp
  ring

lemma mesh_ge_four (b : ℕ) : 4 ≤ (2 : ℝ) ^ (b + 2) := by
  have hb : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  nlinarith

lemma dyadic_shift_le_quarter {n : ℕ} {t : ℝ} (hn : 3 ≤ n)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) : t * (2 : ℝ)⁻¹ ^ n ≤ 1 / 4 := by
  have hp : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  norm_num at hp
  have hnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  nlinarith

lemma mesh_mul_shift_ge_four {b n : ℕ} {t : ℝ}
    (hn : n ≤ b) (ht : 1 ≤ t) :
    4 ≤ (2 : ℝ) ^ (b + 2) * (t * (2 : ℝ)⁻¹ ^ n) := by
  have hp : (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hpos : 0 < (2 : ℝ) ^ (b + 2) := by positivity
  have hpnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have hshift : (2 : ℝ)⁻¹ ^ b ≤ t * (2 : ℝ)⁻¹ ^ n := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hshift hpos.le
  rw [mesh_mul_dyadic] at hmul
  exact hmul

/-- Every tested dyadic translate uses a key different from the center's key. -/
lemma periodicKey_dyadic_ne_center {b n : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnhi : n ≤ b) (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x ≠
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n) := by
  apply periodicKey_ne_of_small_shift (mesh_ge_four b)
  · have := mesh_mul_shift_ge_four hnhi htlo
    linarith
  · exact dyadic_shift_le_quarter hnlo htlo hthi

lemma dyadic_gap_ge_smaller {n m : ℕ} (hnm : n < m) :
    (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ n - (2 : ℝ)⁻¹ ^ m := by
  have hp : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ (n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [pow_succ] at hp
  norm_num at hp
  linarith

/-- Different indices in one window use different periodic keys, uniformly in
all normalized scales. No exclusion of grid-boundary centers is needed. -/
lemma periodicKey_dyadic_ne_of_lt {b n m : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnm : n < m) (hmhi : m ≤ b)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n) ≠
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ m) := by
  have hgap := dyadic_gap_ge_smaller hnm
  have hmon : (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmhi
  have hmpos : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  have hqpos : 0 < (2 : ℝ) ^ (b + 2) := by positivity
  have hdiff : (2 : ℝ)⁻¹ ^ b ≤
      t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m := by
    have hprod := mul_nonneg (sub_nonneg.mpr htlo)
      (show 0 ≤ (2 : ℝ)⁻¹ ^ n - (2 : ℝ)⁻¹ ^ m by linarith)
    nlinarith
  have hlow := mul_le_mul_of_nonneg_left hdiff hqpos.le
  rw [mesh_mul_dyadic] at hlow
  have hsmall : t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m ≤ 1 / 4 := by
    have := dyadic_shift_le_quarter hnlo htlo hthi
    have hprod : 0 ≤ t * (2 : ℝ)⁻¹ ^ m := mul_nonneg (by linarith) hmpos.le
    linarith
  have hne := periodicKey_ne_of_small_shift
    (x := x + t * (2 : ℝ)⁻¹ ^ m) (mesh_ge_four b)
    (show 1 ≤ (2 : ℝ) ^ (b + 2) *
      (t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m) by linarith) hsmall
  have heq : x + t * (2 : ℝ)⁻¹ ^ m +
      (t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m) =
      x + t * (2 : ℝ)⁻¹ ^ n := by ring
  rw [heq] at hne
  exact hne.symm

lemma periodicKey_dyadic_injOn {a b : ℕ} {x t : ℝ} (ha : 3 ≤ a)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    Set.InjOn (fun n : ℕ =>
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n))
      (Set.Icc a b) := by
  intro n hn m hm heq
  rcases lt_trichotomy n m with hlt | heq' | hgt
  · exact False.elim ((periodicKey_dyadic_ne_of_lt
      (le_trans ha hn.1) hlt hm.2 htlo hthi) heq)
  · exact heq'
  · exact False.elim ((periodicKey_dyadic_ne_of_lt
      (le_trans ha hm.1) hgt hn.2 htlo hthi) heq.symm)

/-- The nesting identity for the periodic dyadic grids. -/
lemma periodicKey_dyadic_refine {b B : ℕ} (hb : b ≤ B) (x : ℝ) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x =
      periodicKey ((2 : ℝ) ^ (B + 2)) x / (2 : ℤ) ^ (B - b) := by
  have heq : (2 : ℝ) ^ (B + 2) * Int.fract x =
      ((2 : ℝ) ^ (b + 2) * Int.fract x) * ((2 ^ (B - b) : ℕ) : ℝ) := by
    push_cast
    rw [mul_right_comm, ← pow_add]
    congr 1
    congr 1
    omega
  unfold periodicKey
  rw [heq]
  simpa using (Int.mul_natCast_floor_div_cancel
    (n := 2 ^ (B - b)) (by positivity)
    ((2 : ℝ) ^ (b + 2) * Int.fract x)).symm

lemma periodicKey_dyadic_eq_of_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (heq : periodicKey ((2 : ℝ) ^ (B + 2)) x =
      periodicKey ((2 : ℝ) ^ (B + 2)) y) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x =
      periodicKey ((2 : ℝ) ^ (b + 2)) y := by
  rw [periodicKey_dyadic_refine hb x, periodicKey_dyadic_refine hb y, heq]

lemma periodicKey_nonneg {q : ℝ} (hq : 0 ≤ q) (x : ℝ) :
    0 ≤ periodicKey q x := by
  exact Int.floor_nonneg.mpr (mul_nonneg hq (Int.fract_nonneg x))

lemma periodicKey_lt (q : ℕ) (hq : 0 < q) (x : ℝ) :
    periodicKey (q : ℝ) x < (q : ℤ) := by
  apply Int.floor_lt.mpr
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have := mul_lt_mul_of_pos_left (Int.fract_lt_one x) hq'
  simpa using this

/-- A finite-table address for the periodic dyadic grid. -/
def dyadicKey (b : ℕ) (x : ℝ) : Fin (2 ^ (b + 2)) :=
  ⟨(periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x).toNat,
    (Int.toNat_lt (periodicKey_nonneg (by positivity) x)).mpr
      (periodicKey_lt _ (by positivity) x)⟩

lemma dyadicKey_eq_iff (b : ℕ) (x y : ℝ) :
    dyadicKey b x = dyadicKey b y ↔
      periodicKey ((2 : ℝ) ^ (b + 2)) x =
        periodicKey ((2 : ℝ) ^ (b + 2)) y := by
  constructor
  · intro h
    have hv := congrArg (fun k : Fin (2 ^ (b + 2)) => (k.val : ℤ)) h
    dsimp [dyadicKey] at hv
    rw [Int.toNat_of_nonneg (periodicKey_nonneg (by positivity) x),
      Int.toNat_of_nonneg (periodicKey_nonneg (by positivity) y)] at hv
    simpa using hv
  · intro h
    apply Fin.ext
    dsimp [dyadicKey]
    have h' : periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x =
        periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) y := by simpa using h
    rw [h']

lemma dyadicKey_ne_center {b n : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnhi : n ≤ b) (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    dyadicKey b x ≠ dyadicKey b (x + t * (2 : ℝ)⁻¹ ^ n) := by
  rw [ne_eq, dyadicKey_eq_iff]
  exact periodicKey_dyadic_ne_center hnlo hnhi htlo hthi

lemma dyadicKey_injOn {a b : ℕ} {x t : ℝ} (ha : 3 ≤ a)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    Set.InjOn (fun n : ℕ => dyadicKey b (x + t * (2 : ℝ)⁻¹ ^ n))
      (Set.Icc a b) := by
  intro n hn m hm heq
  apply periodicKey_dyadic_injOn ha htlo hthi hn hm
  exact (dyadicKey_eq_iff b _ _).mp heq

lemma dyadicKey_eq_of_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (heq : dyadicKey B x = dyadicKey B y) : dyadicKey b x = dyadicKey b y := by
  apply (dyadicKey_eq_iff b x y).mpr
  exact periodicKey_dyadic_eq_of_refine hb ((dyadicKey_eq_iff B x y).mp heq)

lemma dyadicKey_add_one (b : ℕ) (x : ℝ) : dyadicKey b (x + 1) = dyadicKey b x := by
  rw [dyadicKey_eq_iff]
  exact periodicKey_add_one _ _

lemma measurable_periodicKey (q : ℝ) : Measurable (periodicKey q) := by
  have hfract : Measurable (Int.fract : ℝ → ℝ) :=
    measurable_id.sub ((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
      Int.measurable_floor)
  exact Int.measurable_floor.comp (measurable_const.mul hfract)

lemma measurable_dyadicKey (b : ℕ) : Measurable (dyadicKey b) := by
  let lift : ℤ → Fin (2 ^ (b + 2)) := fun k =>
    if h : k.toNat < 2 ^ (b + 2) then ⟨k.toNat, h⟩ else ⟨0, by positivity⟩
  have hlift : Measurable lift := measurable_of_countable _
  have h := hlift.comp (measurable_periodicKey ((2 ^ (b + 2) : ℕ) : ℝ))
  have heq : (fun x => lift (periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x)) =
      dyadicKey b := by
    funext x
    have hlt : (periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x).toNat < 2 ^ (b + 2) :=
      (dyadicKey b x).isLt
    simp only [lift, dif_pos hlt, dyadicKey]
  simpa only [Function.comp_def, heq] using h

end Problem310.GridSeparation

end

end OAI

end

-- OpenAI source module: ConcreteLabelMeasures
section

namespace OAI

universe u_S u_T

noncomputable section

namespace Problem310.ConcreteLabels

open MeasureTheory ProbabilityTheory

/-- The actual terminal-bit law used at parameter `p`. -/
def bitLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure Bool :=
  bernoulliMeasure true false ⟨p, hp0, hp1⟩

instance bitLaw_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bitLaw p hp0 hp1) := by
  unfold bitLaw
  infer_instance

@[simp] theorem bitLaw_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bitLaw p hp0 hp1 {true} = ENNReal.ofReal p := by
  simp [bitLaw, unitInterval.toNNReal, ENNReal.ofReal, Real.toNNReal_of_nonneg hp0]
  rfl

@[simp] theorem bitLaw_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bitLaw p hp0 hp1 {false} = ENNReal.ofReal (1 - p) := by
  simp [bitLaw, unitInterval.toNNReal, ENNReal.ofReal,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1)]
  rfl

/-- The actual fair law for selector table entries. -/
def fairLaw : Measure Bool := bitLaw (1 / 2) (by norm_num) (by norm_num)

instance fairLaw_probability : IsProbabilityMeasure fairLaw := by
  unfold fairLaw
  infer_instance

@[simp] theorem fairLaw_singleton (b : Bool) : fairLaw {b} = (2 : ENNReal)⁻¹ := by
  have hh : ENNReal.ofReal ((1 : ℝ) / 2) = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  cases b <;> norm_num [fairLaw] <;> exact hh

/-- A finite table of independent fair selectors. -/
def selectorLaw (S : Type u_S) [Fintype S] : Measure (S → Bool) :=
  Measure.pi fun _ => fairLaw

instance selectorLaw_probability (S : Type u_S) [Fintype S] :
    IsProbabilityMeasure (selectorLaw S) := by
  unfold selectorLaw
  infer_instance

/-- A finite table of independent Bernoulli terminal entries. -/
def terminalLaw (T : Type u_T) [Fintype T] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measure (T → Bool) := Measure.pi fun _ => bitLaw p hp0 hp1

instance terminalLaw_probability (T : Type u_T) [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (terminalLaw T p hp0 hp1) := by
  unfold terminalLaw
  infer_instance

/-- Complete finite selector/terminal outcome law, with independent tables. -/
def outcomeLaw (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure ((S → Bool) × (T → Bool)) :=
  (selectorLaw S).prod (terminalLaw T p hp0 hp1)

instance outcomeLaw_probability (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (outcomeLaw S T p hp0 hp1) := by
  unfold outcomeLaw
  infer_instance

@[simp] theorem selectorLaw_singleton (S : Type u_S) [Fintype S] (ω : S → Bool) :
    selectorLaw S {ω} = ((2 : ENNReal)⁻¹) ^ Fintype.card S := by
  simp [selectorLaw, Measure.pi_singleton]

@[simp] theorem terminalLaw_singleton (T : Type u_T) [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : T → Bool) :
    terminalLaw T p hp0 hp1 {ω} =
      ∏ t, ENNReal.ofReal (if ω t then p else 1 - p) := by
  rw [terminalLaw, Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro t _
  cases h : ω t <;> simp

@[simp] theorem outcomeLaw_singleton (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : (S → Bool) × (T → Bool)) :
    outcomeLaw S T p hp0 hp1 {ω} =
      selectorLaw S {ω.1} * terminalLaw T p hp0 hp1 {ω.2} := by
  cases ω with
  | mk s t =>
    rw [outcomeLaw, ← Set.singleton_prod_singleton, Measure.prod_prod]

end Problem310.ConcreteLabels

end

end OAI

end

-- OpenAI source module: ExceptionalCenters
section

namespace OAI

noncomputable section

open Set Filter Topology

namespace Problem310.Auxiliary

section

/-- Centers at which some normalized scale avoids all the selected tests. -/
def exceptionalCenters (B : Set ℝ) (N : Set ℕ) (a : ℕ → ℝ) : Set ℝ :=
  {x | ∃ t ∈ Icc (1 : ℝ) 2, ∀ n ∈ N, x + t * a n ∉ B}

/-- Compactness of the normalized scale interval makes the exceptional centers closed. -/
theorem isClosed_exceptionalCenters (B : Set ℝ) (hB : IsOpen B)
    (N : Set ℕ) (a : ℕ → ℝ) : IsClosed (exceptionalCenters B N a) := by
  let K := Icc (1 : ℝ) 2
  let S : Set (ℝ × K) := {z | ∀ n ∈ N, z.1 + (z.2 : ℝ) * a n ∉ B}
  have hS : IsClosed S := by
    have heq : S = ⋂ n ∈ N, {z : ℝ × K | z.1 + (z.2 : ℝ) * a n ∉ B} := by
      ext z
      simp [S]
    rw [heq]
    refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
    exact hB.isClosed_compl.preimage (continuous_fst.add
      ((continuous_subtype_val.comp continuous_snd).mul_const (a n)))
  have hK : IsCompact K := isCompact_Icc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hproj : IsClosed (Prod.fst '' S) := isClosedMap_fst_of_compactSpace S hS
  convert hproj using 1
  ext x
  simp only [exceptionalCenters, S, K, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨(x, ⟨t, ht⟩), h, rfl⟩
  · rintro ⟨⟨y, t, ht⟩, h, rfl⟩
    exact ⟨t, ht, h⟩

/-- Periodicity passes from the selected set to its exceptional centers. -/
theorem exceptionalCenters_periodic (B : Set ℝ)
    (hB : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B) (N : Set ℕ) (a : ℕ → ℝ) :
    ∀ x : ℝ, x + 1 ∈ exceptionalCenters B N a ↔
      x ∈ exceptionalCenters B N a := by
  intro x
  simp only [exceptionalCenters, mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, fun n hn hm => h n hn ?_⟩
    rw [show x + 1 + t * a n = (x + t * a n) + 1 by ring]
    exact (hB _).mpr hm
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, fun n hn hm => h n hn ?_⟩
    apply (hB _).mp
    convert hm using 1; ring

/-- An open neighborhood of a limit point meets every tail of a converging sequence. -/
theorem exists_tail_mem_of_tendsto (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (V : Set ℝ) (hV : IsOpen V) (x : ℝ) (hx : x ∈ V) (t : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ V := by
  have hlim : Tendsto (fun n => x + t * a n) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul ha)
  have hev : ∀ᶠ n in atTop, x + t * a n ∈ V := hlim.eventually (hV.mem_nhds hx)
  obtain ⟨n, hn, hmem⟩ := (eventually_ge_atTop 1 |>.and hev).exists
  exact ⟨n, hn, hmem⟩

/-- Open-neighborhood repair turns tests away from exceptional centers into hits everywhere. -/
theorem exceptionalCenters_repair (B V : Set ℝ) (N : Set ℕ) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hN : ∀ n ∈ N, 1 ≤ n)
    (hV : IsOpen V) (hcover : exceptionalCenters B N a ⊆ V) :
    ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
      ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ B ∪ V := by
  intro x t ht
  by_cases hx : x ∈ exceptionalCenters B N a
  · obtain ⟨n, hn, hmem⟩ := exists_tail_mem_of_tendsto a ha V hV x (hcover hx) t
    exact ⟨n, hn, Or.inr hmem⟩
  · have htest : ∃ n ∈ N, x + t * a n ∈ B := by
      by_contra! h
      exact hx ⟨t, ht, h⟩
    obtain ⟨n, hn, hmem⟩ := htest
    exact ⟨n, hN n hn, Or.inl hmem⟩

open Set Filter Topology MeasureTheory Metric

/-- Thickening preserves one-periodicity. -/
theorem thickening_periodic (R : Set ℝ)
    (hR : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) :
    ∀ x : ℝ, x + 1 ∈ thickening ε R ↔ x ∈ thickening ε R := by
  intro x
  simp only [mem_thickening_iff]
  constructor
  · rintro ⟨z, hz, hdist⟩
    refine ⟨z - 1, ?_, ?_⟩
    · apply (hR (z - 1)).mp
      simpa using hz
    · simpa [Real.dist_eq, sub_sub] using hdist
  · rintro ⟨z, hz, hdist⟩
    refine ⟨z + 1, (hR z).mpr hz, ?_⟩
    simpa using hdist

/-- A closed periodic set admits an open periodic neighborhood with arbitrarily
small increase of its measure in one period. -/
theorem exists_open_periodic_superset (R : Set ℝ) (hRc : IsClosed R)
    (hRp : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set ℝ, IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧ R ⊆ V ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤
        volume (R ∩ Icc (0 : ℝ) 1) + ENNReal.ofReal ε := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  let := hfinite
  have hlim : Tendsto (fun r => μ (thickening r R)) (𝓝[>] 0) (𝓝 (μ R)) :=
    tendsto_measure_thickening_of_isClosed ⟨1, zero_lt_one, measure_ne_top μ _⟩ hRc
  have hlt : μ R < μ R + ENNReal.ofReal ε :=
    ENNReal.lt_add_right (measure_ne_top μ R) (by positivity)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (thickening r R) < μ R + ENNReal.ofReal ε :=
    hlim.eventually (eventually_lt_nhds hlt)
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hbound⟩ := (hpos.and hev).exists
  refine ⟨thickening r R, isOpen_thickening, thickening_periodic R hRp r,
    self_subset_thickening hr R, ?_⟩
  simpa [μ, Measure.restrict_apply, isOpen_thickening.measurableSet,
    hRc.measurableSet] using hbound.le

end

open Set Filter Topology MeasureTheory

/-- Deterministic completion of the probabilistic construction: once the density of
an open test set plus its exceptional centers is small, a genuinely hitting open
periodic set is available at arbitrarily small additional density cost. -/
theorem repair_open_periodic_hitting
    (B : Set ℝ) (hBo : IsOpen B)
    (hBp : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (c : ENNReal)
    (hbound : volume (B ∩ Icc (0 : ℝ) 1) +
      volume (exceptionalCenters B N a ∩ Icc (0 : ℝ) 1) ≤ c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ c + ENNReal.ofReal ε ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ H := by
  obtain ⟨V, hVo, hVp, hRV, hVm⟩ := exists_open_periodic_superset
    (exceptionalCenters B N a) (isClosed_exceptionalCenters B hBo N a)
    (exceptionalCenters_periodic B hBp N a) ε hε
  refine ⟨B ∪ V, hBo.union hVo, ?_, ?_,
    exceptionalCenters_repair B V N a ha hN hVo hRV⟩
  · intro x
    simp only [mem_union, hBp, hVp]
  · calc
      volume ((B ∪ V) ∩ Icc (0 : ℝ) 1)
          ≤ volume (B ∩ Icc (0 : ℝ) 1) + volume (V ∩ Icc (0 : ℝ) 1) := by
            rw [union_inter_distrib_right]
            exact measure_union_le _ _
      _ ≤ volume (B ∩ Icc (0 : ℝ) 1) +
          (volume (exceptionalCenters B N a ∩ Icc (0 : ℝ) 1) +
            ENNReal.ofReal ε) := add_le_add le_rfl hVm
      _ ≤ c + ENNReal.ofReal ε := by
        rw [← add_assoc]
        exact add_le_add hbound le_rfl

/-- The dyadic sequence converges to zero. -/
theorem dyadic_tendsto_zero :
    Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem periodic_hitting_of_small_exceptional
    (p : ℝ) (hp : 0 < p) (B : Set ℝ) (hBo : IsOpen B)
    (hBp : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (hbound : volume (B ∩ Icc (0 : ℝ) 1) +
      volume (exceptionalCenters B N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1)
        ≤ ENNReal.ofReal (5 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  obtain ⟨H, hHo, hHp, hHm, hHit⟩ := repair_open_periodic_hitting
    B hBo hBp N hN (fun n => (2 : ℝ)⁻¹ ^ n) dyadic_tendsto_zero
    (ENNReal.ofReal (5 * p)) hbound p hp
  refine ⟨H, hHo, hHp, ?_, hHit⟩
  convert hHm using 1
  rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hp)]
  congr 1
  ring

end Problem310.Auxiliary

end

end OAI

end

-- OpenAI source module: FirstDefault
section

namespace OAI

universe u_Ω

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.FirstDefault

abbrev Address (M : ℕ) := List (Fin (M + 1)) × Fin M
abbrev Path (M d : ℕ) := Fin d → Fin M
abbrev Tests {M d : ℕ} (f : Path M d) := (k : Fin d) × Fin ((f k).val + 1)

/-- The node immediately before the `k`th decision along a nondefault path. -/
def pathPrefix {M d : ℕ} (f : Path M d) (k : Fin d) : List (Fin (M + 1)) :=
  List.ofFn fun j : Fin k.val => (f ⟨j.val, lt_trans j.isLt k.isLt⟩).castSucc

lemma pathPrefix_eq_take_ofFn {M d : ℕ} (f : Path M d) (k : Fin d) :
    pathPrefix f k = (List.ofFn fun j => (f j).castSucc).take k.val := by
  exact Fin.ofFn_take_eq_take_ofFn k.isLt.le (fun j => (f j).castSucc)

/-- Every earlier rejected selector and the selected selector are tested. -/
def address {M d : ℕ} (f : Path M d) (i : Tests f) : Address M :=
  (pathPrefix f i.1, ⟨i.2.val, lt_of_lt_of_le i.2.isLt (Nat.succ_le_of_lt (f i.1).isLt)⟩)

def requiredBit {M d : ℕ} (f : Path M d) (i : Tests f) : Bool :=
  decide (i.2.val = (f i.1).val)

/-- The selector cylinder expressing that a prescribed path is followed. -/
def cylinder {M d : ℕ} {Ω : Type u_Ω} (S : Address M → Ω → Bool)
    (f : Path M d) : Set Ω :=
  {ω | ∀ i : Tests f, S (address f i) ω = requiredBit f i}

lemma address_injective {M d : ℕ} (f : Path M d) :
    Function.Injective (address f) := by
  rintro ⟨k, i⟩ ⟨l, j⟩ h
  have hlen := congrArg (fun a : Address M => a.1.length) h
  simp only [address, pathPrefix, List.length_ofFn] at hlen
  have hkl : k = l := Fin.ext hlen
  subst l
  have hij := congrArg (fun a : Address M => a.2.val) h
  simp only [address] at hij
  have : i = j := Fin.ext hij
  subst j
  rfl

lemma measure_cylinder_of_local {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Address M → Ω → Bool) (f : Path M d)
    (hi : iIndepFun (fun i : Tests f => S (address f i)) μ)
    (hfair : ∀ i : Tests f, ∀ b, μ (S (address f i) ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (cylinder S f) = ∏ k : Fin d, ((2 : ENNReal)⁻¹) ^ ((f k).val + 1) := by
  classical
  have h := hi.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : Tests f => {requiredBit f i}) (by intro i _; exact measurableSet_singleton _)
  have heq : (⋂ i : Tests f, ⋂ (_ : i ∈ Finset.univ),
      S (address f i) ⁻¹' {requiredBit f i}) = cylinder S f := by
    ext ω
    simp [cylinder]
  rw [heq] at h
  rw [h]
  simp only [hfair]
  rw [Fintype.prod_sigma]
  simp

lemma cylinder_disjoint_of_prefix {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (f g : Path M d) (k : Fin d)
    (hprefix : pathPrefix f k = pathPrefix g k) (hlt : f k < g k) :
    Disjoint (cylinder S f) (cylinder S g) := by
  apply Set.disjoint_left.mpr
  intro ω hf hg
  have h1 := hf ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩
  have h2 := hg ⟨k, ⟨(f k).val, lt_trans hlt (Nat.lt_succ_self _)⟩⟩
  have ha : (address f ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩) =
      address g ⟨k, ⟨(f k).val, lt_trans hlt (Nat.lt_succ_self _)⟩⟩ := by
    simp only [address, hprefix]
  have hb1 : requiredBit f ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩ = true := by
    simp [requiredBit]
  have hb2 : requiredBit g
      ⟨k, ⟨(f k).val, lt_trans hlt (Nat.lt_succ_self _)⟩⟩ = false := by
    have hne : (f k).val ≠ (g k).val := Nat.ne_of_lt hlt
    simp [requiredBit, hne]
  rw [hb1, ha] at h1
  rw [hb2, h1] at h2
  cases h2

lemma cylinders_pairwiseDisjoint {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) : Pairwise (fun f g : Path M d => Disjoint (cylinder S f) (cylinder S g)) := by
  classical
  intro f g hfg
  have hex : ∃ k, f k ≠ g k := by
    by_contra! h
    exact hfg (funext h)
  let T : Finset (Fin d) := Finset.univ.filter fun k => f k ≠ g k
  have hT : T.Nonempty := by
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, by simp [T, hk]⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image T (fun i => i) hT
  have hkne : f k ≠ g k := (Finset.mem_filter.mp hk).2
  have hearlier : ∀ j : Fin d, j < k → f j = g j := by
    intro j hj
    by_contra hne
    exact (not_le_of_gt hj) (hmin j (by simp [T, hne]))
  have hprefix : pathPrefix f k = pathPrefix g k := by
    unfold pathPrefix
    congr 1
    funext j
    rw [hearlier ⟨j.val, lt_trans j.isLt k.isLt⟩ j.isLt]
  rcases lt_or_gt_of_ne hkne with hlt | hgt
  · exact cylinder_disjoint_of_prefix S f g k hprefix hlt
  · exact (cylinder_disjoint_of_prefix S g f k hprefix.symm hgt).symm

lemma measurableSet_cylinder {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (S : Address M → Ω → Bool) (hS : ∀ a, Measurable (S a)) (f : Path M d) :
    MeasurableSet (cylinder S f) := by
  simp only [cylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => (hS _) (measurableSet_singleton _)

lemma sum_geometric_weights (M : ℕ) :
    (∑ i : Fin M, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) =
      1 - ((2 : ENNReal)⁻¹) ^ M := by
  have hadd (n : ℕ) :
      (∑ i : Fin n, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) +
        ((2 : ENNReal)⁻¹) ^ n = 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hq : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1 := ENNReal.inv_two_add_inv_two
      calc
        (∑ i : Fin n, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) +
            ((2 : ENNReal)⁻¹) ^ (n + 1) + ((2 : ENNReal)⁻¹) ^ (n + 1) =
          (∑ i : Fin n, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) +
            ((2 : ENNReal)⁻¹) ^ n * ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹) := by
              rw [pow_succ]
              ring
        _ = 1 := by rw [hq, mul_one]; exact ih
  exact ENNReal.eq_sub_of_add_eq (by finiteness) (hadd M)

/-- Local independence suffices: only the finitely many addresses on each
prescribed path are required to be independent and fair. -/
theorem measure_no_default_of_local {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Address M → Ω → Bool)
    (hS : ∀ a, Measurable (S a))
    (hIndep : ∀ f : Path M d, iIndepFun (fun i : Tests f => S (address f i)) μ)
    (hfair : ∀ f : Path M d, ∀ i : Tests f, ∀ b,
      μ (S (address f i) ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (⋃ f : Path M d, cylinder S f) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  classical
  rw [measure_iUnion (cylinders_pairwiseDisjoint S) (measurableSet_cylinder S hS),
    tsum_fintype]
  simp_rw [measure_cylinder_of_local μ S _ (hIndep _) (hfair _)]
  calc
    _ = (∑ i : Fin M, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) ^ d :=
      (Fintype.sum_pow (fun i : Fin M => ((2 : ENNReal)⁻¹) ^ (i.val + 1)) d).symm
    _ = _ := by rw [sum_geometric_weights]

abbrev BoundedAddress (M d : ℕ) := {a : Address M // a.1.length < d}

lemma address_length_lt {M d : ℕ} (f : Path M d) (i : Tests f) :
    (address f i).1.length < d := by
  simpa only [address, pathPrefix, List.length_ofFn] using i.1.isLt

def boundedAddress {M d : ℕ} (f : Path M d) (i : Tests f) : BoundedAddress M d :=
  ⟨address f i, address_length_lt f i⟩

lemma boundedAddress_injective {M d : ℕ} (f : Path M d) :
    Function.Injective (boundedAddress f) := by
  intro i j h
  exact address_injective f (congrArg Subtype.val h)

/-- Finite-tree version: no randomness outside nodes of depth less than `d`
is assumed. This is the interface for the actual finite table model. -/
theorem measure_no_default_bounded {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : BoundedAddress M d → Ω → Bool)
    (hS : ∀ a, Measurable (S a)) (hIndep : iIndepFun S μ)
    (hfair : ∀ a b, μ (S a ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (⋃ f : Path M d,
      {ω | ∀ i : Tests f, S (boundedAddress f i) ω = requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  classical
  let S' : Address M → Ω → Bool := fun a ω =>
    if h : a.1.length < d then S ⟨a, h⟩ ω else false
  have heval (f : Path M d) (i : Tests f) :
      S' (address f i) = S (boundedAddress f i) := by
    funext ω
    simp only [S', dif_pos (address_length_lt f i), boundedAddress]
  have hS' : ∀ a, Measurable (S' a) := by
    intro a
    dsimp only [S']
    split
    · exact hS _
    · exact measurable_const
  have hi : ∀ f : Path M d, iIndepFun (fun i : Tests f => S' (address f i)) μ := by
    intro f
    simp_rw [heval]
    exact hIndep.precomp (boundedAddress_injective f)
  have hf : ∀ f : Path M d, ∀ i : Tests f, ∀ b,
      μ (S' (address f i) ⁻¹' {b}) = (2 : ENNReal)⁻¹ := by
    intro f i b
    rw [heval]
    exact hfair _ b
  have h := measure_no_default_of_local μ S' hS' hi hf
  simpa only [cylinder, heval] using h

end Problem310.FirstDefault

end

end OAI

end

-- OpenAI source module: OrderedRouting
section

namespace OAI

namespace Problem310.OrderedRouting

/-- The first successful nondefault selector, or the final (default) child. -/
def chooseChild {M : ℕ} (S : Fin M → Bool) : Fin (M + 1) :=
  Fin.find (fun i => Fin.lastCases true S i = true) ⟨Fin.last M, by simp⟩

variable {M : ℕ}

theorem chooseChild_eq_nondefault_iff (S : Fin M → Bool) (i : Fin M) :
    chooseChild S = i.castSucc ↔ S i = true ∧ ∀ j < i, S j = false := by
  rw [chooseChild, Fin.find_eq_iff]
  simp only [Fin.lastCases_castSucc]
  constructor
  · rintro ⟨hi, hmin⟩
    refine ⟨hi, fun j hj => ?_⟩
    have h := hmin j.castSucc (by simpa using hj)
    simpa using h
  · rintro ⟨hi, hmin⟩
    refine ⟨hi, fun j hj => ?_⟩
    induction j using Fin.lastCases with
    | last => exact ((not_lt_of_ge (Fin.le_last _)) hj).elim
    | cast j =>
      have h := hmin j (by simpa using hj)
      simp [h]

theorem chooseChild_eq_default_iff (S : Fin M → Bool) :
    chooseChild S = Fin.last M ↔ ∀ i, S i = false := by
  rw [chooseChild, Fin.find_eq_iff]
  simp only [Fin.lastCases_last, true_and]
  constructor
  · intro h i
    have hi := h i.castSucc (Fin.castSucc_lt_last i)
    simpa using hi
  · intro h j hj
    induction j using Fin.lastCases with
    | last => exact ((lt_irrefl _) hj).elim
    | cast i => simp [h i]

/-- Routing to a nondefault child depends only on selector entries up to it. -/
theorem chooseChild_preserved (S T : Fin M → Bool) (i : Fin M)
    (hS : chooseChild S = i.castSucc) (heq : ∀ j ≤ i, S j = T j) :
    chooseChild T = i.castSucc := by
  obtain ⟨hi, hmin⟩ := (chooseChild_eq_nondefault_iff S i).mp hS
  apply (chooseChild_eq_nondefault_iff T i).mpr
  constructor
  · rw [← heq i le_rfl]
    exact hi
  · intro j hj
    rw [← heq j (le_of_lt hj)]
    exact hmin j hj

/-- Rejected earlier children and a successful current selector determine a hit. -/
theorem chooseChild_of_local_success (S : Fin M → Bool) (i : Fin M)
    (hprev : ∀ j < i, S j = false) (hi : S i = true) :
    chooseChild S = i.castSucc :=
  (chooseChild_eq_nondefault_iff S i).mpr ⟨hi, hprev⟩

/-- Pointwise equality of selectors preserves the complete child choice. -/
theorem chooseChild_congr (S T : Fin M → Bool) (h : ∀ i, S i = T i) :
    chooseChild S = chooseChild T := by
  congr 1
  exact funext h

end Problem310.OrderedRouting

end OAI

end

-- OpenAI source module: RoutingPath
section

namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- Route from a node by appending the locally selected child at each step.
The choice rule is abstract: a first-success/default selector can be supplied. -/
def routeFrom (choose : List ι → X → ι) : ℕ → List ι → X → List ι
  | 0, P, _ => P
  | n + 1, P, x =>
      let Q := routeFrom choose n P x
      Q ++ [choose Q x]

@[simp] theorem routeFrom_zero (choose : List ι → X → ι) (P : List ι) (x : X) :
    routeFrom choose 0 P x = P := rfl

@[simp] theorem routeFrom_succ (choose : List ι → X → ι) (n : ℕ) (P : List ι) (x : X) :
    routeFrom choose (n + 1) P x =
      routeFrom choose n P x ++ [choose (routeFrom choose n P x) x] := rfl

@[simp] theorem length_routeFrom (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x : X) :
    (routeFrom choose n P x).length = P.length + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.add_assoc]

/-- A route can be resumed at any intermediate node. -/
theorem routeFrom_add (choose : List ι → X → ι)
    (n m : ℕ) (P : List ι) (x : X) :
    routeFrom choose (n + m) P x =
      routeFrom choose m (routeFrom choose n P x) x := by
  induction m with
  | zero => simp
  | succ m ih => simp only [Nat.add_succ, routeFrom_succ, ih]

/-- Every routed node extends the starting node. -/
theorem prefix_routeFrom (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x : X) : P.IsPrefix (routeFrom choose n P x) := by
  induction n with
  | zero => exact List.prefix_refl _
  | succ n ih =>
      exact ih.trans (List.prefix_append _ _)

/-- Earlier decisions along one path suffice to preserve the full common prefix.
No restriction is imposed on decisions off that path. -/
theorem routeFrom_eq_of_choices_eq (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x y : X)
    (hchoice : ∀ k < n,
      choose (routeFrom choose k P x) y = choose (routeFrom choose k P x) x) :
    routeFrom choose n P y = routeFrom choose n P x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp := ih (fun k hk => hchoice k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      simp only [routeFrom_succ, hp, hchoice n (Nat.lt_succ_self n)]

/-- Preservation through an ancestor prefix followed by one specified local child
identifies the actual terminal leaf with the locally routed leaf. -/
theorem routeFrom_eq_local_route (choose : List ι → X → ι)
    (k r : ℕ) (P U : List ι) (x y : X) (i : ι)
    (hU : routeFrom choose k P x = U)
    (hchoice : ∀ l < k,
      choose (routeFrom choose l P x) y = choose (routeFrom choose l P x) x)
    (hi : choose U y = i) :
    routeFrom choose (k + 1 + r) P y = routeFrom choose r (U ++ [i]) y := by
  have hp := routeFrom_eq_of_choices_eq choose k P x y hchoice
  rw [hU] at hp
  rw [routeFrom_add, routeFrom_succ, hp, hi]

/-- Every earlier routed node is a prefix of every later routed node. -/
theorem routeFrom_prefix_of_le (choose : List ι → X → ι)
    (P : List ι) (x : X) {k d : ℕ} (hkd : k ≤ d) :
    (routeFrom choose k P x).IsPrefix (routeFrom choose d P x) := by
  have h := prefix_routeFrom choose (d - k) (routeFrom choose k P x) x
  rw [← routeFrom_add, Nat.add_sub_of_le hkd] at h
  exact h

/-- Truncating a routed leaf recovers the intermediate routed node. -/
theorem take_routeFrom (choose : List ι → X → ι)
    (P : List ι) (x : X) {k d : ℕ} (hkd : k ≤ d) :
    (routeFrom choose d P x).take (P.length + k) = routeFrom choose k P x := by
  obtain ⟨suffix, heq⟩ := routeFrom_prefix_of_le choose P x hkd
  rw [← heq]
  have h : (routeFrom choose k P x ++ suffix).take
      (routeFrom choose k P x).length = routeFrom choose k P x := by simp
  simpa only [length_routeFrom] using h

/-- Prescribed decisions on all initial segments determine a route. -/
theorem routeFrom_eq_take_of_choices (choose : List ι → X → ι)
    (L : List ι) (x : X)
    (hchoice : ∀ (k : ℕ) (hk : k < L.length), choose (L.take k) x = L[k])
    {n : ℕ} (hn : n ≤ L.length) : routeFrom choose n [] x = L.take n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnl : n < L.length := by omega
      rw [routeFrom_succ, ih (by omega), hchoice n hnl,
        List.take_succ_eq_append_getElem hnl]

/-- Path-cylinder characterization: a terminal route equals a prescribed list
exactly when each successive decision follows that list. -/
theorem routeFrom_eq_iff_choices (choose : List ι → X → ι) (L : List ι) (x : X) :
    routeFrom choose L.length [] x = L ↔
      ∀ (k : ℕ) (hk : k < L.length), choose (L.take k) x = L[k] := by
  constructor
  · intro hroute k hk
    have hk0 := take_routeFrom choose [] x (Nat.le_of_lt hk)
    have hk1 := take_routeFrom choose [] x (Nat.succ_le_of_lt hk)
    rw [hroute] at hk0 hk1
    simp only [List.length_nil, Nat.zero_add] at hk0 hk1
    rw [routeFrom_succ, ← hk0, List.take_succ_eq_append_getElem hk] at hk1
    have h := List.append_cancel_left hk1
    simpa only [List.singleton_inj] using h.symm
  · intro hchoice
    simpa using routeFrom_eq_take_of_choices choose L x hchoice (le_refl L.length)

/-- Avoiding a default at every decision is the same as avoiding it in the
terminal path (for a route starting at the root). -/
theorem noDefault_iff_not_mem (choose : List ι → X → ι)
    (default : ι) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ default) ↔
      default ∉ routeFrom choose d [] x := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [routeFrom_succ, List.mem_append, List.mem_singleton, not_or]
      constructor
      · intro h
        refine ⟨ih.mp (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self d))), ?_⟩
        exact (h d (Nat.lt_succ_self d)).symm
      · rintro ⟨hprev, hlast⟩ k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkd | rfl
        · exact ih.mpr hprev k hkd
        · intro heq
          exact hlast heq.symm

/-- A route with no default child is represented by a vector of nondefault
children. This is the deterministic event equality needed for path-cylinder
probability estimates. -/
theorem noDefault_iff_exists_path {M : ℕ}
    (choose : List (Fin (M + 1)) → X → Fin (M + 1)) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ Fin.last M) ↔
      ∃ f : Fin d → Fin M,
        routeFrom choose d [] x = List.ofFn (fun i => (f i).castSucc) := by
  rw [noDefault_iff_not_mem]
  constructor
  · intro h
    let L := routeFrom choose d [] x
    have hL : L.length = d := by simp [L]
    have hentry : ∀ i : Fin d, L[i.val]'(by rw [hL]; exact i.isLt) ≠ Fin.last M := by
      intro i heq
      apply h
      rw [← heq]
      exact List.getElem_mem _
    let f : Fin d → Fin M := fun i =>
      (L[i.val]'(by rw [hL]; exact i.isLt)).castPred (hentry i)
    refine ⟨f, ?_⟩
    change L = _
    apply List.ext_getElem
    · simp [hL]
    · intro i hi hi'
      simp only [List.getElem_ofFn]
      simp only [f, Fin.castSucc_castPred]
  · rintro ⟨f, hf⟩
    rw [hf]
    simp only [List.mem_ofFn]
    rintro ⟨i, hi⟩
    exact Fin.castSucc_ne_last (f i) hi

/-- The no-default event is a union of the prescribed nondefault path cylinders. -/
theorem noDefault_iff_exists_choices {M : ℕ}
    (choose : List (Fin (M + 1)) → X → Fin (M + 1)) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ Fin.last M) ↔
      ∃ f : Fin d → Fin M, ∀ (k : ℕ) (hk : k < d),
        choose ((List.ofFn (fun i => (f i).castSucc)).take k) x =
          (f ⟨k, hk⟩).castSucc := by
  rw [noDefault_iff_exists_path]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    have hc := (routeFrom_eq_iff_choices choose
      (List.ofFn (fun i => (f i).castSucc)) x).mp (by simpa using hf)
    simpa only [List.length_ofFn, List.getElem_ofFn] using hc
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    have hc := (routeFrom_eq_iff_choices choose
      (List.ofFn (fun i => (f i).castSucc)) x).mpr (by
        simpa only [List.length_ofFn, List.getElem_ofFn] using hf)
    simpa only [List.length_ofFn] using hc

/-- A first default on a finite route has a well-defined first occurrence. -/
theorem exists_first_default (choose : List ι → X → ι)
    (d : ℕ) (P : List ι) (x : X) (default : ι)
    (h : ∃ k < d, choose (routeFrom choose k P x) x = default) :
    ∃ k < d, choose (routeFrom choose k P x) x = default ∧
      ∀ l < k, choose (routeFrom choose l P x) x ≠ default := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
  intro l hl hdefault
  exact Nat.find_min h hl ⟨Nat.lt_trans hl (Nat.find_spec h).1, hdefault⟩

/-- Periodic node choices give periodic routed leaves. -/
theorem routeFrom_periodic (choose : List ι → ℝ → ι)
    (hchoose : ∀ P x, choose P (x + 1) = choose P x)
    (n : ℕ) (P : List ι) (x : ℝ) :
    routeFrom choose n P (x + 1) = routeFrom choose n P x := by
  apply routeFrom_eq_of_choices_eq
  intro k hk
  exact hchoose _ x

/-- Measurability of the finite router over a countable discrete child alphabet.
The joint node-choice map is the only input required from the table model. -/
theorem measurable_routeFrom [Countable ι]
    [MeasurableSpace X] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace (List ι)] [MeasurableSingletonClass (List ι)]
    (choose : List ι → X → ι)
    (hchoose : Measurable (Function.uncurry choose)) (n : ℕ) (P : List ι) :
    Measurable (routeFrom choose n P) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hnext : Measurable (fun x => choose (routeFrom choose n P x) x) :=
        hchoose.comp (ih.prodMk measurable_id)
      exact (measurable_of_countable (fun z : List ι × ι => z.1 ++ [z.2])).comp
        (ih.prodMk hnext)

end Problem310.RoutingPath

end

end OAI

end

-- OpenAI source module: Model
section

namespace OAI

noncomputable section

namespace Problem310

def dyadicPoint (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n

end Problem310

end

end OAI

end

-- OpenAI source module: AdaptiveLabels
section

namespace OAI

universe u_I u_K u_B u_A

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.AdaptiveLabels

/-- Distinct table addresses read independent labels, including when some
addresses in the table are unused. -/
theorem measure_injective_constraints
    {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype I] [Fintype K] [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (addr : I → K) (hinj : Function.Injective addr)
    (s : I → Set B) (hs : ∀ i, MeasurableSet (s i)) :
    (Measure.pi (fun _ : K => ν)) {ω | ∀ i, ω (addr i) ∈ s i} =
      ∏ i, ν (s i) := by
  classical
  have hind : iIndepFun (fun k (ω : K → B) => ω k)
      (Measure.pi (fun _ : K => ν)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := (hind.precomp hinj).measure_inter_preimage_eq_mul
    Finset.univ (fun i _ => hs i)
  simp only [Finset.mem_univ, Set.iInter_true] at h
  rw [show {ω : K → B | ∀ i, ω (addr i) ∈ s i} =
    (⋂ i, (fun ω : K → B => ω (addr i)) ⁻¹' s i) by ext ω; simp]
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  exact (measurePreserving_eval (fun _ : K => ν) (addr i)).measure_preimage
    (hs i).nullMeasurableSet

/-- An address choice may depend arbitrarily on a separate selector outcome.
After fixing that outcome, injectivity is the only required terminal-table fact. -/
theorem measure_adaptive_constraints
    {A : Type u_A} {I : Type u_I} {K : Type u_K} {B : Type u_B} [MeasurableSpace A] [Fintype I] [Fintype K]
    [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure ν]
    (addr : A → I → K) (hinj : ∀ a, Function.Injective (addr a))
    (s : A → I → Set B) (hs : ∀ a i, MeasurableSet (s a i))
    (hmeas : MeasurableSet {z : A × (K → B) |
      ∀ i, z.2 (addr z.1 i) ∈ s z.1 i}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → B) | ∀ i, z.2 (addr z.1 i) ∈ s z.1 i} =
      ∫⁻ a, ∏ i, ν (s a i) ∂μ := by
  rw [Measure.prod_apply hmeas]
  apply lintegral_congr
  intro a
  exact measure_injective_constraints ν (addr a) (hinj a) (s a) (hs a)

/-- The conditional failure probability of adaptively addressed Boolean tests.
Only active tests impose a zero label; distinct active addresses suffice here
because we assume the stronger, routing-friendly injectivity of all addresses. -/
theorem measure_adaptive_failures
    {A : Type u_A} {I : Type u_I} {K : Type u_K} [MeasurableSpace A] [Fintype I] [Fintype K]
    (μ : Measure A) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → I → K) (hinj : ∀ a, Function.Injective (addr a))
    (active : A → I → Prop) [∀ a i, Decidable (active a i)]
    (hmeas : MeasurableSet {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → Bool) | ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      ∫⁻ a, (ν {false}) ^ (Finset.univ.filter (active a)).card ∂μ := by
  classical
  let s : A → I → Set Bool := fun a i => if active a i then {false} else Set.univ
  have hset : {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      {z : A × (K → Bool) | ∀ i, z.2 (addr z.1 i) ∈ s z.1 i} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    apply forall_congr'
    intro i
    by_cases h : active z.1 i <;> simp [s, h]
  rw [hset] at hmeas ⊢
  rw [measure_adaptive_constraints μ ν addr hinj s
    (fun _ _ => MeasurableSet.of_discrete) hmeas]
  apply lintegral_congr
  intro a
  simp only [s, apply_ite, measure_univ]
  simp [Finset.prod_ite]

end Problem310.AdaptiveLabels

end OAI

end

-- OpenAI source module: WindowPlacement
section

namespace OAI

universe u_α

open scoped BigOperators

namespace Problem310.WindowPlacement

/-- Place windows in preorder, reserving `g` unused indices after each window. -/
def start (len : ℕ → ℕ) (g : ℕ) : ℕ → ℕ
  | 0 => 3
  | i + 1 => start len g i + len i + g

def finish (len : ℕ → ℕ) (g i : ℕ) : ℕ := start len g i + len i - 1

def window (len : ℕ → ℕ) (g i : ℕ) : Finset ℕ :=
  Finset.Icc (start len g i) (finish len g i)

/-- Extract a window length from a finite preorder list, using zero outside the list. -/
def lengthAt (L : List ℕ) (i : ℕ) : ℕ := L[i]?.getD 0

theorem lengthAt_map_of_getElem? {α : Type u_α} (f : α → ℕ)
    {L : List α} {i : ℕ} {x : α} (h : L[i]? = some x) :
    lengthAt (L.map f) i = f x := by
  simp only [lengthAt, List.getElem?_map, h, Option.map_some, Option.getD_some]

theorem lengthAt_map_idxOf {α : Type u_α} [BEq α] [LawfulBEq α]
    (f : α → ℕ) {L : List α} {x : α} (hx : x ∈ L) :
    lengthAt (L.map f) (L.idxOf x) = f x :=
  lengthAt_map_of_getElem? f (List.getElem?_idxOf hx)

theorem sum_lengthAt (L : List ℕ) :
    (∑ i ∈ Finset.range L.length, lengthAt L i) = L.sum := by
  induction L with
  | nil => simp [lengthAt]
  | cons a L ih =>
      simp only [List.length_cons, Finset.sum_range_succ', lengthAt,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
        List.sum_cons]
      change (∑ i ∈ Finset.range L.length, lengthAt L i) + a = a + L.sum
      rw [ih, Nat.add_comm]

theorem lengthAt_segment (pre block post : List ℕ) {k : ℕ} (hk : k < block.length) :
    lengthAt (pre ++ block ++ post) (pre.length + k) = lengthAt block k := by
  simp only [lengthAt, List.append_assoc, List.getElem?_append]
  rw [if_neg (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [if_pos hk]

/-- Translate a consecutive preorder block's list sum into the prefix-sum
interface used by the endpoint and resolution lemmas. -/
theorem sum_lengthAt_segment (pre block post : List ℕ) (g : ℕ) :
    (∑ k ∈ Finset.range block.length,
      (lengthAt (pre ++ block ++ post) (pre.length + k) + g)) =
      (block.map (fun r => r + g)).sum := by
  calc
    _ = ∑ k ∈ Finset.range block.length, (lengthAt block k + g) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [lengthAt_segment pre block post (Finset.mem_range.mp hk)]
    _ = block.sum + block.length * g := by
      rw [Finset.sum_add_distrib, sum_lengthAt]
      simp
    _ = _ := by
      induction block with
      | nil => simp
      | cons a block ih =>
          simp only [List.sum_cons, List.length_cons, List.map_cons]
          rw [← ih]
          simp only [Nat.add_mul, Nat.one_mul]
          omega

@[simp] theorem start_zero (len : ℕ → ℕ) (g : ℕ) : start len g 0 = 3 := rfl

@[simp] theorem start_succ (len : ℕ → ℕ) (g i : ℕ) :
    start len g (i + 1) = start len g i + len i + g := rfl

theorem start_mono (len : ℕ → ℕ) (g : ℕ) : Monotone (start len g) := by
  apply monotone_nat_of_le_succ
  intro i
  simp only [start_succ]
  omega

theorem three_le_start (len : ℕ → ℕ) (g i : ℕ) : 3 ≤ start len g i := by
  simpa using start_mono len g (Nat.zero_le i)

theorem finish_add_one (len : ℕ → ℕ) (g i : ℕ) :
    finish len g i + 1 = start len g i + len i := by
  have := three_le_start len g i
  unfold finish
  omega

/-- Endpoints are nondecreasing even if some windows have length zero. -/
theorem finish_mono (len : ℕ → ℕ) (g : ℕ) : Monotone (finish len g) := by
  apply monotone_nat_of_le_succ
  intro i
  have hi := finish_add_one len g i
  have hj := finish_add_one len g (i + 1)
  rw [start_succ] at hj
  omega

theorem consecutive_gap (len : ℕ → ℕ) (g i : ℕ) :
    start len g (i + 1) = finish len g i + g + 1 := by
  rw [start_succ]
  have := finish_add_one len g i
  omega

/-- Every later window starts strictly beyond the earlier endpoint and its gap. -/
theorem gap_of_lt (len : ℕ → ℕ) (g : ℕ) {i j : ℕ} (hij : i < j) :
    finish len g i + g < start len g j := by
  have hm := start_mono len g (Nat.succ_le_of_lt hij)
  rw [consecutive_gap] at hm
  omega

@[simp] theorem mem_window {len : ℕ → ℕ} {g i n : ℕ} :
    n ∈ window len g i ↔ start len g i ≤ n ∧ n ≤ finish len g i :=
  Finset.mem_Icc

@[simp] theorem card_window (len : ℕ → ℕ) (g i : ℕ) :
    (window len g i).card = len i := by
  rw [window, Nat.card_Icc]
  have := finish_add_one len g i
  omega

/-- Prefix-sum formula relative to any incoming edge. -/
theorem start_add (len : ℕ → ℕ) (g i m : ℕ) :
    start len g (i + m) = start len g i +
      ∑ k ∈ Finset.range m, (len (i + k) + g) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, start_succ, ih, Finset.sum_range_succ]
      omega

/-- A consecutive child block's endpoint is exactly its total window and gap budget. -/
theorem block_endpoint (len : ℕ → ℕ) (g i m : ℕ) :
    finish len g (i + m) + g + 1 = start len g i +
      ∑ k ∈ Finset.range (m + 1), (len (i + k) + g) := by
  rw [← consecutive_gap]
  simpa only [Nat.add_assoc] using start_add len g i (m + 1)

theorem block_endpoint_le {len : ℕ → ℕ} {g i m r : ℕ}
    (hbudget : (∑ k ∈ Finset.range (m + 1), (len (i + k) + g)) ≤ 2 * r + g) :
    finish len g (i + m) + 1 ≤ start len g i + 2 * r := by
  have := block_endpoint len g i m
  omega

end Problem310.WindowPlacement

end OAI

end

-- OpenAI source module: WindowBudgets
section

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem310.WindowBudget

/-- A polynomial factor times a decaying exponential tends to zero along natural arguments. -/
lemma tendsto_nat_mul_exp_neg (a : ℝ) (ha : 0 < a) :
    Tendsto (fun r : ℕ => (r : ℝ) * Real.exp (-a * (r : ℝ))) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) a ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The entropy factor appearing in the finite scale discretization is dominated by
its exponential saving. This uses exactly the numerical coefficient. -/
lemma entropy_tendsto_zero (M a : ℝ) (ha : 10 ≤ a) :
    Tendsto (fun r : ℕ => 20 * M * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
      Real.exp (-a * (r : ℝ))) atTop (𝓝 0) := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < a - 2 * Real.log 2 := by linarith
  have h1 := (tendsto_nat_mul_exp_neg a ha0).const_mul (20 * M)
  have h2 := (tendsto_nat_mul_exp_neg (a - 2 * Real.log 2) hb0).const_mul (80 * M)
  have hsum := h1.add h2
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [] with r
  have hpow : (2 : ℝ) ^ (2 * r + 2) =
      Real.exp (((2 * r + 2 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hfour : Real.exp (2 * Real.log 2) = 4 := by
    rw [show (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  have hprod : (2 : ℝ) ^ (2 * r + 2) * Real.exp (-a * (r : ℝ)) =
      4 * Real.exp (-(a - 2 * Real.log 2) * (r : ℝ)) := by
    rw [hpow, ← Real.exp_add, ← hfour, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc
    20 * M * ((r : ℝ) * Real.exp (-a * (r : ℝ))) +
        80 * M * ((r : ℝ) * Real.exp (-(a - 2 * Real.log 2) * (r : ℝ))) =
        20 * M * (r : ℝ) * Real.exp (-a * (r : ℝ)) +
        20 * M * (r : ℝ) * ((2 : ℝ) ^ (2 * r + 2) * Real.exp (-a * (r : ℝ))) := by
          rw [hprod]
          ring
    _ = _ := by ring

/-- A single lower bound on the window length works for every larger window. -/
lemma exists_entropy_threshold (p M a : ℝ) (hp : 0 < p) (ha : 10 ≤ a) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      20 * M * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
        Real.exp (-a * (r : ℝ)) < p := by
  have h := (entropy_tendsto_zero M a ha).eventually_lt_const hp
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp h
  refine ⟨max 1 r₀, le_max_left _ _, ?_⟩
  intro r hr
  exact hr₀ r ((le_max_right _ _).trans hr)

/-- Choose the branching number with the required exponential margin. -/
lemma exists_branching_number (p : ℝ) (hp : 0 < p) :
    ∃ M : ℕ, 2 ≤ M ∧ 10 ≤ p * ((M : ℝ) - 1) / 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (20 / p)
  have hprod : 20 < (N : ℝ) * p := (div_lt_iff₀ hp).mp hN
  refine ⟨N + 2, by omega, ?_⟩
  push_cast
  nlinarith

/-- A geometric probability can be made arbitrarily small at a positive depth. -/
lemma exists_positive_depth (p q : ℝ) (hp : 0 < p) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ d : ℕ, 1 ≤ d ∧ q ^ d < p := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually_lt_const hp
  obtain ⟨d, hd⟩ := eventually_atTop.mp h
  exact ⟨max 1 d, le_max_left _ _, hd _ (le_max_right _ _)⟩

/-- The branching factor and tree depth can be chosen in the prescribed order. -/
lemma exists_tree_parameters (p : ℝ) (hp : 0 < p) :
    ∃ M d : ℕ, 2 ≤ M ∧ 1 ≤ d ∧
      10 ≤ p * ((M : ℝ) - 1) / 2 ∧
      (1 - ((2 : ℝ)⁻¹) ^ (M - 1)) ^ d < p := by
  obtain ⟨M, hM, hmargin⟩ := exists_branching_number p hp
  have hpowpos : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ (M - 1) := by positivity
  have hpowle : ((2 : ℝ)⁻¹) ^ (M - 1) ≤ (1 : ℝ) := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨d, hd, hsmall⟩ := exists_positive_depth p
    (1 - ((2 : ℝ)⁻¹) ^ (M - 1)) hp (by linarith) (by linarith)
  exact ⟨M, d, hM, hd, hmargin, hsmall⟩

/-- The elementary Bernoulli miss probability is bounded by an exponential. -/
lemma one_sub_pow_le_exp (u : ℝ) (hu : u ≤ 1) (N : ℕ) :
    (1 - u) ^ N ≤ Real.exp (-u * (N : ℝ)) := by
  have hbase : 1 - u ≤ Real.exp (-u) := by
    have h := Real.add_one_le_exp (-u)
    linarith
  calc
    (1 - u) ^ N ≤ Real.exp (-u) ^ N :=
      pow_le_pow_left₀ (by linarith) hbase N
    _ = Real.exp (-u * (N : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The window threshold also bounds the actual fixed-scale failure probability
multiplied by the number of scale representatives. -/
lemma exists_probability_threshold (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (M : ℕ) (hM : 2 ≤ M) (hmargin : 10 ≤ p * ((M : ℝ) - 1) / 2) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      20 * (M : ℝ) * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
        (1 - p / 2) ^ ((M - 1) * r) < p := by
  obtain ⟨r₀, hr₀, hsmall⟩ :=
    exists_entropy_threshold p M (p * ((M : ℝ) - 1) / 2) hp hmargin
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  have hpow := one_sub_pow_le_exp (p / 2) (by linarith) ((M - 1) * r)
  have hexp : -(p / 2) * (((M - 1) * r : ℕ) : ℝ) =
      -(p * ((M : ℝ) - 1) / 2) * (r : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ M)]
    push_cast
    ring
  rw [hexp] at hpow
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hpow (by positivity)) (hsmall r hr)

end Problem310.WindowBudget

end

end OAI

end

-- OpenAI source module: SelectorMoment
section

namespace OAI

universe u_I u_Ω u_K

noncomputable section

namespace Problem310.SelectorMoment

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

lemma product_eq_pow_active {I : Type u_I} [Fintype I] [DecidableEq I]
    (a : I → Bool) (q : ℝ≥0∞) :
    (∏ i, if a i then q else 1) = q ^ Fintype.card {i // a i = true} := by
  simp [Finset.prod_ite, Fintype.card_subtype]

/-- Exponential moment of the number of active independent Boolean trials. -/
theorem independent_boolean_moment
    {Ω : Type u_Ω} {I : Type u_I} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Bool)
    (X : I → Ω → Bool) (hX : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (hmap : ∀ i, μ.map (X i) = ν)
    (q : ℝ≥0∞) :
    (∫⁻ ω, q ^ Fintype.card {i // X i ω = true} ∂μ) =
      (ν {false} + q * ν {true}) ^ Fintype.card I := by
  classical
  let g : Bool → ℝ≥0∞ := fun b => if b then q else 1
  have hg : Measurable g := measurable_of_countable g
  have hind : iIndepFun (fun i => g ∘ X i) μ := hX.comp (fun _ => g) (fun _ => hg)
  have hsingle (i : I) : (∫⁻ ω, g (X i ω) ∂μ) = ν {false} + q * ν {true} := by
    rw [← lintegral_map hg (hXm i), hmap i, lintegral_fintype]
    simp [g, add_comm]
  calc
    (∫⁻ ω, q ^ Fintype.card {i // X i ω = true} ∂μ) =
        ∫⁻ ω, ∏ i, g (X i ω) ∂μ := by
      apply lintegral_congr
      intro ω
      exact (product_eq_pow_active (fun i => X i ω) q).symm
    _ = ∏ i, ∫⁻ ω, g (X i ω) ∂μ := by
      exact lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
        (fun i => g ∘ X i) hind (fun i => hg.comp (hXm i))
    _ = (ν {false} + q * ν {true}) ^ Fintype.card I := by simp_rw [hsingle]; simp

/-- The same moment for injective coordinate lookups in a larger product table. -/
theorem lookup_boolean_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : I → K) (hinj : Function.Injective addr) (q : ℝ≥0∞) :
    (∫⁻ ω : K → Bool, q ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (ν {false} + q * ν {true}) ^ Fintype.card I := by
  apply independent_boolean_moment
  · exact iIndepFun.precomp hinj
      (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id))
  · intro i
    exact measurable_pi_apply (addr i)
  · intro i
    exact (measurePreserving_eval (fun _ : K => ν) (addr i)).map_eq

/-- Fair fresh selector entries, with an arbitrary nonnegative failure factor. -/
theorem lookup_fair_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfalse : ν {false} = 1 / 2) (htrue : ν {true} = 1 / 2)
    (addr : I → K) (hinj : Function.Injective addr) (q : ℝ≥0∞) :
    (∫⁻ ω : K → Bool, q ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (1 / 2 + q / 2) ^ Fintype.card I := by
  rw [lookup_boolean_moment ν addr hinj q, hfalse, htrue]
  simp [div_eq_mul_inv]

/-- The exact fixed-scale base, with real parameter p. -/
theorem lookup_fair_failure_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfalse : ν {false} = 1 / 2) (htrue : ν {true} = 1 / 2)
    (addr : I → K) (hinj : Function.Injective addr)
    (p : ℝ) (hp : p ≤ 1) :
    (∫⁻ ω : K → Bool, (ENNReal.ofReal (1 - p)) ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by
  rw [lookup_fair_moment ν hfalse htrue addr hinj]
  congr 1
  have hdiv (a : ℝ) : ENNReal.ofReal (a / 2) = ENNReal.ofReal a / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [hdiv]
    norm_num
  rw [hhalf, ← hdiv]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (div_nonneg (sub_nonneg.mpr hp) (by norm_num))]
  congr 1
  ring

end Problem310.SelectorMoment

end

end OAI

end

-- OpenAI source module: PeriodicMeasure
section

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- Iterating a period-one membership equivalence. -/
theorem periodic_mem_nat {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) (x : ℝ) :
    x + (n : ℝ) ∈ H ↔ x ∈ H := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using
      (hH (x + (n : ℝ))).trans ih

/-- Integer translates of a unit cell have the same occupied volume. -/
theorem periodic_unit_volume_nat {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) :
    volume (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) =
      volume (H ∩ Icc (0 : ℝ) 1) := by
  have hset : (fun x : ℝ => x + (n : ℝ)) ⁻¹'
      (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) = H ∩ Icc (0 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_Icc, periodic_mem_nat hH]
    constructor
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
  simpa only [hset] using
    (measure_preimage_add_right volume (n : ℝ)
      (H ∩ Icc (n : ℝ) ((n : ℝ) + 1))).symm

/-- A period-one set occupies at most `n` times its unit-cell volume in `n` cells.
No measurability assumption is needed for this upper bound. -/
theorem periodic_nat_interval_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) :
    volume (H ∩ Icc (0 : ℝ) (n : ℝ)) ≤
      (n : ENNReal) * volume (H ∩ Icc (0 : ℝ) 1) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, Icc_self, zero_mul, nonpos_iff_eq_zero]
    exact measure_mono_null inter_subset_right (measure_singleton 0)
  | succ n ih =>
    have hsplit : H ∩ Icc (0 : ℝ) ((n : ℝ) + 1) =
        (H ∩ Icc (0 : ℝ) (n : ℝ)) ∪
          (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) := by
      rw [← inter_union_distrib_left,
        Icc_union_Icc_eq_Icc (by positivity : (0 : ℝ) ≤ n) (by linarith)]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hsplit, add_mul, one_mul]
    exact (measure_union_le _ _).trans
      (add_le_add ih (le_of_eq (periodic_unit_volume_nat hH n)))

/-- Pulling a period-one set back by a positive integer dilation cannot
increase the volume occupied inside the unit interval. -/
theorem periodic_dilate_unit_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) {n : ℕ} (hn : 0 < n) :
    volume ({x : ℝ | (n : ℝ) * x ∈ H} ∩ Icc (0 : ℝ) 1) ≤
      volume (H ∩ Icc (0 : ℝ) 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hset : {x : ℝ | (n : ℝ) * x ∈ H} ∩ Icc (0 : ℝ) 1 =
      (fun x : ℝ => (n : ℝ) * x) ⁻¹' (H ∩ Icc (0 : ℝ) (n : ℝ)) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage]
    constructor
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, mul_nonneg hnR.le h₀, by nlinarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by nlinarith, by nlinarith⟩
  rw [hset, Real.volume_preimage_mul_left hnR.ne', abs_of_pos (inv_pos.mpr hnR)]
  have hbound := mul_le_mul_right (periodic_nat_interval_volume_le hH n)
    (ENNReal.ofReal ((n : ℝ)⁻¹))
  refine hbound.trans_eq ?_
  rw [ENNReal.ofReal_inv_of_pos hnR, ENNReal.ofReal_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp), one_mul]

/-- Reflection preserves period-one membership. -/
theorem periodic_reflect {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) :
    ∀ x : ℝ, x + 1 ∈ {y : ℝ | -y ∈ H} ↔ x ∈ {y : ℝ | -y ∈ H} := by
  intro x
  change -(x + 1) ∈ H ↔ -x ∈ H
  have heq : -(x + 1) + 1 = -x := by ring
  simpa only [heq] using (hH (-(x + 1))).symm

/-- Reflection preserves the occupied volume in a unit period. -/
theorem periodic_reflect_unit_volume {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) :
    volume ({x : ℝ | -x ∈ H} ∩ Icc (0 : ℝ) 1) =
      volume (H ∩ Icc (0 : ℝ) 1) := by
  have hset : {x : ℝ | -x ∈ H} ∩ Icc (0 : ℝ) 1 =
      (fun x : ℝ => -x) ⁻¹' ((fun y : ℝ => 1 + y) ⁻¹'
        (H ∩ Icc (0 : ℝ) 1)) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage]
    have hmem : 1 + -x ∈ H ↔ -x ∈ H := by simpa only [add_comm] using hH (-x)
    rw [hmem]
    constructor
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
  rw [hset, Measure.measure_preimage_neg, measure_preimage_add]

/-- The reflected version of the integer-dilation volume estimate. -/
theorem periodic_neg_dilate_unit_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) {n : ℕ} (hn : 0 < n) :
    volume ({x : ℝ | -((n : ℝ) * x) ∈ H} ∩ Icc (0 : ℝ) 1) ≤
      volume (H ∩ Icc (0 : ℝ) 1) := by
  exact (periodic_dilate_unit_volume_le (periodic_reflect hH) hn).trans_eq
    (periodic_reflect_unit_volume hH)

end Problem310Support

end

end OAI

end

-- OpenAI source module: ExposureMoments
section

namespace OAI

universe u_A u_V

open MeasureTheory

namespace Problem310.ExposureMoments

end Problem310.ExposureMoments

end OAI

end

-- OpenAI source module: ExceptionalExpectation
section

namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- For a finite random family of measurable sets, averaging their densities is
identical to integrating pointwise membership probabilities. -/
theorem expected_density_eq_pointwise_probability
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Set ℝ) (hR : ∀ ω, MeasurableSet (R ω)) :
    (∫⁻ ω, volume (R ω ∩ Icc (0 : ℝ) 1) ∂μ) =
      ∫⁻ x in Icc (0 : ℝ) 1, μ {ω | x ∈ R ω} := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let S : Set (Ω × ℝ) := {z | z.2 ∈ R z.1}
  have hS : MeasurableSet S := by
    have heq : S = ⋃ ω, ({ω} : Set Ω) ×ˢ R ω := by
      ext ⟨ω, x⟩
      simp [S]
    rw [heq]
    exact MeasurableSet.iUnion fun ω => (measurableSet_singleton ω).prod (hR ω)
  have heq := (Measure.prod_apply (μ := μ) (ν := ν) hS).symm.trans
    (Measure.prod_apply_symm (μ := μ) (ν := ν) hS)
  change (∫⁻ ω, ν (R ω) ∂μ) = ∫⁻ x, μ {ω | x ∈ R ω} ∂ν at heq
  simpa only [ν, Measure.restrict_apply (hR _)] using heq

/-- A uniform bound outside a small exceptional set of centers controls the
expected density. This is the integration step in the repair argument. -/
theorem expected_density_le_of_pointwise_bound
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Set ℝ) (hR : ∀ ω, MeasurableSet (R ω))
    (G : Set ℝ) (hG : MeasurableSet G) (a : ENNReal)
    (hgood : ∀ x ∈ G, μ {ω | x ∈ R ω} ≤ a) :
    (∫⁻ ω, volume (R ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤
      a + volume (Gᶜ ∩ Icc (0 : ℝ) 1) := by
  rw [expected_density_eq_pointwise_probability μ R hR]
  calc
    (∫⁻ x in Icc (0 : ℝ) 1, μ {ω | x ∈ R ω}) ≤
        ∫⁻ x in Icc (0 : ℝ) 1, a + Gᶜ.indicator (fun _ => (1 : ENNReal)) x := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ G
      · simpa [hx] using hgood x hx
      · simp only [mem_compl_iff, hx, not_false_eq_true, indicator_of_mem]
        exact (prob_le_one).trans (le_add_self)
    _ = a + volume (Gᶜ ∩ Icc (0 : ℝ) 1) := by
      rw [lintegral_add_left measurable_const]
      simp [lintegral_indicator hG.compl, Measure.restrict_apply hG.compl]

end Problem310.Auxiliary

end

end OAI

end

-- OpenAI source module: ExposureUnionBound
section

namespace OAI

universe u_Ω u_A u_I

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem310.ExposureUnionBound

/-- Averaging conditional bounds over a finite exposure does not introduce a
factor for the number of possible exposure values. The event itself need not
be measurable, since the proof uses only outer-measure subadditivity. -/
theorem measure_le_of_finite_exposure
    {Ω : Type u_Ω} {A : Type u_A} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → A) (hf : ∀ a, MeasurableSet {ω | f ω = a})
    (E : Set Ω) (good : Set A) (badBound goodBound : ENNReal)
    (hbad : μ {ω | f ω ∉ good} ≤ badBound)
    (hgood : ∀ a ∈ good,
      μ (E ∩ {ω | f ω = a}) ≤ goodBound * μ {ω | f ω = a}) :
    μ E ≤ badBound + goodBound := by
  classical
  let localEvent : A → Set Ω := fun a =>
    if a ∈ good then E ∩ {ω | f ω = a} else ∅
  have hcover : E ⊆ {ω | f ω ∉ good} ∪ ⋃ a, localEvent a := by
    intro ω hω
    by_cases hg : f ω ∈ good
    · right
      exact Set.mem_iUnion.mpr ⟨f ω, by simp [localEvent, hg, hω]⟩
    · exact Or.inl hg
  have hlocal (a : A) : μ (localEvent a) ≤ goodBound * μ {ω | f ω = a} := by
    by_cases ha : a ∈ good
    · simpa [localEvent, ha] using hgood a ha
    · simp [localEvent, ha]
  have hmass : (∑ a : A, μ {ω | f ω = a}) = 1 := by
    have h := sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset A)
      (f := f) (fun a _ => hf a)
    simpa [Set.preimage] using h
  calc
    μ E ≤ μ ({ω | f ω ∉ good} ∪ ⋃ a, localEvent a) := measure_mono hcover
    _ ≤ μ {ω | f ω ∉ good} + μ (⋃ a, localEvent a) := measure_union_le _ _
    _ ≤ badBound + ∑ a : A, μ (localEvent a) :=
      add_le_add hbad (measure_iUnion_fintype_le μ localEvent)
    _ ≤ badBound + ∑ a : A, goodBound * μ {ω | f ω = a} :=
      add_le_add le_rfl (Finset.sum_le_sum fun a _ => hlocal a)
    _ = badBound + goodBound := by rw [← Finset.mul_sum, hmass, mul_one]

end Problem310.ExposureUnionBound

end

end OAI

end

-- OpenAI source module: GridMeasure
section

namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

/-- Centers whose positive displacement of length `δ` crosses a boundary
of the periodic grid with `q` cells. -/
def gridBadCenters (q : ℕ) (δ : ℝ) : Set ℝ :=
  ⋃ k : ℤ, Ico ((k : ℝ) / q - δ) ((k : ℝ) / q)

theorem mem_gridBadCenters_iff (q : ℕ) (δ x : ℝ) :
    x ∈ gridBadCenters q δ ↔ ∃ k : ℤ, (k : ℝ) / q ∈ Ioc x (x + δ) := by
  simp only [gridBadCenters, mem_iUnion, mem_Ico, mem_Ioc]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.1], by linarith [hk.2]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.2], by linarith [hk.1]⟩

theorem measurableSet_gridBadCenters (q : ℕ) (δ : ℝ) :
    MeasurableSet (gridBadCenters q δ) := by
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_Ico

theorem gridBadCenters_add_one (q : ℕ) (hq : 0 < q) (δ x : ℝ) :
    x + 1 ∈ gridBadCenters q δ ↔ x ∈ gridBadCenters q δ := by
  rw [mem_gridBadCenters_iff, mem_gridBadCenters_iff]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - q, ?_⟩
    have he : ((k - q : ℤ) : ℝ) / q = (k : ℝ) / q - 1 := by
      push_cast
      field_simp
    rw [he]
    exact ⟨by linarith [hk.1], by linarith [hk.2]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k + q, ?_⟩
    have he : ((k + q : ℤ) : ℝ) / q = (k : ℝ) / q + 1 := by
      push_cast
      field_simp
    rw [he]
    exact ⟨by linarith [hk.1], by linarith [hk.2]⟩

/-- Inside a half-open period the bad centers are covered by exactly `q`
intervals of length `δ`, provided `δ` is at most one cell width. -/
theorem gridBadCenters_period_subset (q : ℕ) (hq : 0 < q) {δ : ℝ}
    (hδ : δ ≤ (q : ℝ)⁻¹) :
    gridBadCenters q δ ∩ Ico (0 : ℝ) 1 ⊆
      ⋃ i : Fin q, Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
        (((i.val + 1 : ℕ) : ℝ) / q) := by
  intro x hx
  obtain ⟨k, hk⟩ := (mem_gridBadCenters_iff q δ x).mp hx.1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hkpos : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) / q := lt_of_le_of_lt hx.2.1 hk.1
    have := (div_pos_iff.mp this)
    exact_mod_cast (by rcases this with h | h; exact h.1; linarith [h.2] : (0 : ℝ) < k)
  have hklt : k < (q : ℤ) + 1 := by
    have hstep : (k : ℝ) / q < 1 + (q : ℝ)⁻¹ := by linarith [hx.2.2, hk.2]
    have hmul := (div_lt_iff₀ hqpos).mp hstep
    have hi : (q : ℝ)⁻¹ * q = 1 := inv_mul_cancel₀ hqpos.ne'
    have : (k : ℝ) < q + 1 := by nlinarith
    exact_mod_cast this
  have hkq : k.toNat ≤ q := by omega
  have hkn : 0 < k.toNat := by omega
  let i : Fin q := ⟨k.toNat - 1, by omega⟩
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  have hki : ((i.val + 1 : ℕ) : ℝ) = (k : ℝ) := by
    have : i.val + 1 = k.toNat := by dsimp [i]; omega
    rw [this]
    exact_mod_cast (Int.toNat_of_nonneg hkpos.le)
  rw [hki]
  exact ⟨by linarith [hk.2], hk.1⟩

theorem volume_gridBadCenters_period_le (q : ℕ) (hq : 0 < q) {δ : ℝ}
    (_hδ0 : 0 ≤ δ) (hδ : δ ≤ (q : ℝ)⁻¹) :
    volume (gridBadCenters q δ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal ((q : ℝ) * δ) := by
  have hae : (gridBadCenters q δ ∩ Icc (0 : ℝ) 1 : Set ℝ) =ᵐ[volume]
      (gridBadCenters q δ ∩ Ico (0 : ℝ) 1 : Set ℝ) := by
    filter_upwards [(Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)).symm] with x hx
    exact propext (and_congr_right (fun _ => Iff.of_eq hx))
  rw [measure_congr hae]
  calc
    volume (gridBadCenters q δ ∩ Ico (0 : ℝ) 1)
      ≤ volume (⋃ i : Fin q, Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
          (((i.val + 1 : ℕ) : ℝ) / q)) :=
        measure_mono (gridBadCenters_period_subset q hq hδ)
    _ ≤ ∑ i : Fin q, volume (Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
          (((i.val + 1 : ℕ) : ℝ) / q)) := measure_iUnion_fintype_le _ _
    _ = ENNReal.ofReal ((q : ℝ) * δ) := by
      simp only [Real.volume_Ico, sub_sub_cancel]
      simp [ENNReal.ofReal_mul]

/-- The exceptional density for any finite family of stability requirements
is bounded by the sum of its grid-width budgets. -/
theorem volume_iUnion_gridBadCenters_period_le {ι : Type u_ι} [Fintype ι]
    (q : ι → ℕ) (δ : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hδ0 : ∀ i, 0 ≤ δ i) (hδ : ∀ i, δ i ≤ (q i : ℝ)⁻¹) :
    volume ((⋃ i, gridBadCenters (q i) (δ i)) ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (∑ i, (q i : ℝ) * δ i) := by
  classical
  rw [iUnion_inter]
  calc
    volume (⋃ i, gridBadCenters (q i) (δ i) ∩ Icc (0 : ℝ) 1)
      ≤ ∑ i, volume (gridBadCenters (q i) (δ i) ∩ Icc (0 : ℝ) 1) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal ((q i : ℝ) * δ i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact volume_gridBadCenters_period_le (q i) (hq i) (hδ0 i) (hδ i)
    _ = ENNReal.ofReal (∑ i, (q i : ℝ) * δ i) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i hi
      exact mul_nonneg (Nat.cast_nonneg _) (hδ0 i)

end Problem310

end

end OAI

end

-- OpenAI source module: MonotoneRepresentatives
section

namespace OAI

universe u_α u_ι

noncomputable section

open scoped BigOperators

namespace Problem310.ScaleDiscretization

/-- On a chain of integer vectors, the sum of the coordinates determines the vector. -/
lemma vector_eq_of_sum_eq {α : Type u_α} {ι : Type u_ι} [LinearOrder α] [Fintype ι]
    {s : Set α} {f : α → ι → ℤ} (hf : MonotoneOn f s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hs : (∑ i, f x i) = ∑ i, f y i) : f x = f y := by
  classical
  rcases le_total x y with hxy | hyx
  · funext i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hf hx hy hxy i)).mp hs i
      (Finset.mem_univ i)
  · funext i
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => hf hy hx hyx i)).mp hs.symm i
      (Finset.mem_univ i)).symm

/-- A monotone family of finitely many integer-valued functions has a small common
representative set. Unlike a breakpoint construction, this also handles every boundary
value without a separate endpoint convention. -/
theorem exists_monotone_representatives {α : Type u_α} {ι : Type u_ι} [LinearOrder α] [Fintype ι]
    (a b : α) (hab : a ≤ b) (f : α → ι → ℤ)
    (hf : MonotoneOn f (Set.Icc a b)) :
    ∃ R : Finset α,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ ((∑ i, f b i) + 1 - ∑ i, f a i).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R, f t' = f t := by
  classical
  let rank : α → ℤ := fun t => ∑ i, f t i
  let rep : ℤ → α := fun k =>
    if h : ∃ t, t ∈ Set.Icc a b ∧ rank t = k then Classical.choose h else a
  have rep_mem (k : ℤ) : rep k ∈ Set.Icc a b := by
    dsimp [rep]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact ⟨le_rfl, hab⟩
  have rep_rank {k : ℤ} (h : ∃ t, t ∈ Set.Icc a b ∧ rank t = k) :
      rank (rep k) = k := by
    dsimp [rep]
    rw [dif_pos h]
    exact (Classical.choose_spec h).2
  refine ⟨(Finset.Icc (rank a) (rank b)).image rep, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    exact rep_mem k
  · exact (Finset.card_image_le).trans_eq (Int.card_Icc _ _)
  · intro t ht
    have hlow : rank a ≤ rank t := by
      exact Finset.sum_le_sum fun i _ => hf ⟨le_rfl, hab⟩ ht ht.1 i
    have hhigh : rank t ≤ rank b := by
      exact Finset.sum_le_sum fun i _ => hf ht ⟨hab, le_rfl⟩ ht.2 i
    refine ⟨rep (rank t), Finset.mem_image.mpr ⟨rank t, ?_, rfl⟩, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hlow, hhigh⟩
    · exact vector_eq_of_sum_eq hf (rep_mem _) ht (rep_rank ⟨t, ht, rfl⟩)

/-- An integer floor can increase by at most the ceiling of the displacement. -/
lemma floor_sub_floor_le_ceil (x y : ℝ) : ⌊y⌋ - ⌊x⌋ ≤ ⌈y - x⌉ := by
  have hy := Int.floor_le y
  have hx := Int.lt_floor_add_one x
  have hc := Int.le_ceil (y - x)
  have h : ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) < (⌈y - x⌉ : ℝ) + 1 := by
    push_cast
    linarith
  have hi : ⌊y⌋ - ⌊x⌋ < ⌈y - x⌉ + 1 := by exact_mod_cast h
  omega

/-- Simultaneous floor keys on an affine path admit at most one plus the sum of
their (rounded-up) displacements many representatives. -/
theorem exists_affine_floor_representatives {ι : Type u_ι} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (u v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ (1 + ∑ i, ⌈v i * (b - a)⌉).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R,
        ∀ i, ⌊u i + v i * t'⌋ = ⌊u i + v i * t⌋ := by
  classical
  let f : ℝ → ι → ℤ := fun t i => ⌊u i + v i * t⌋
  have hf : MonotoneOn f (Set.Icc a b) := by
    intro x hx y hy hxy i
    apply Int.floor_le_floor
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy (hv i))
  obtain ⟨R, hR, hcard, hrep⟩ := exists_monotone_representatives a b hab f hf
  refine ⟨R, hR, hcard.trans ?_, ?_⟩
  · apply Int.toNat_le_toNat
    have hi (i : ι) : f b i - f a i ≤ ⌈v i * (b - a)⌉ := by
      have h := floor_sub_floor_le_ceil (u i + v i * a) (u i + v i * b)
      convert h using 1
      congr 1
      ring
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_sub_distrib] at hs
    linarith
  · intro t ht
    obtain ⟨t', ht', heq⟩ := hrep t ht
    exact ⟨t', ht', fun i => congrFun heq i⟩

/-- A uniform displacement bound gives a particularly convenient natural-valued
cardinality estimate for the normalized scale interval. -/
theorem exists_unit_affine_floor_representatives {ι : Type u_ι} [Fintype ι]
    (u v : ι → ℝ) (D : ℕ) (hv : ∀ i, 0 ≤ v i) (hD : ∀ i, v i ≤ (D : ℝ)) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * D ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊u i + v i * t'⌋ = ⌊u i + v i * t⌋ := by
  classical
  obtain ⟨R, hR, hcard, hrep⟩ :=
    exists_affine_floor_representatives 1 2 (by norm_num) u v hv
  refine ⟨R, hR, hcard.trans ?_, hrep⟩
  have hi (i : ι) : ⌈v i * (2 - 1)⌉ ≤ (D : ℤ) := by
    apply Int.ceil_le.mpr
    norm_num
    exact hD i
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hsum : 1 + ∑ i, ⌈v i * (2 - 1)⌉ ≤ (1 + Fintype.card ι * D : ℕ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    push_cast
    linarith
  exact (Int.toNat_le_toNat hsum).trans_eq (Int.toNat_natCast _)

/-- The padding bound controls the scale-parameter slope of each finest grid key. -/
lemma dyadic_grid_slope_le (B n L : ℕ) (h : B ≤ n + L) :
    (2 : ℝ) ^ B * ((2 : ℝ)⁻¹) ^ n ≤ (2 : ℝ) ^ L := by
  rw [inv_pow, ← div_eq_mul_inv]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

/-- Simultaneous representatives for the finest dyadic grid keys in a family of
local routing tests. Only the padding inequalities are needed. -/
theorem exists_dyadic_grid_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊(2 : ℝ) ^ B i * (x + t' * ((2 : ℝ)⁻¹) ^ n i)⌋ =
          ⌊(2 : ℝ) ^ B i * (x + t * ((2 : ℝ)⁻¹) ^ n i)⌋ := by
  let u : ι → ℝ := fun i => (2 : ℝ) ^ B i * x
  let v : ι → ℝ := fun i => (2 : ℝ) ^ B i * ((2 : ℝ)⁻¹) ^ n i
  have hv (i : ι) : 0 ≤ v i := by dsimp [v]; positivity
  have hD (i : ι) : v i ≤ ((2 ^ L : ℕ) : ℝ) := by
    simpa [v] using dyadic_grid_slope_le (B i) (n i) L (hspan i)
  obtain ⟨R, hR, hcard, hrep⟩ :=
    exists_unit_affine_floor_representatives u v (2 ^ L) hv hD
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', heq⟩ := hrep t ht
  refine ⟨t', ht', ?_⟩
  intro i
  convert heq i using 1 <;> congr 1 <;> dsimp [u, v] <;> ring

/-- Passing from a real-line dyadic cell to its periodic key loses no information. -/
lemma periodic_floor_eq_of_floor_eq (q : ℕ) {y z : ℝ}
    (h : ⌊(2 : ℝ) ^ q * y⌋ = ⌊(2 : ℝ) ^ q * z⌋) :
    ⌊(2 : ℝ) ^ q * Int.fract y⌋ = ⌊(2 : ℝ) ^ q * Int.fract z⌋ := by
  have hcancel (w : ℝ) : ⌊(2 : ℝ) ^ q * w⌋ / (2 : ℤ) ^ q = ⌊w⌋ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      Int.natCast_mul_floor_div_cancel (n := 2 ^ q) (by positivity) w
  have hfloor : ⌊y⌋ = ⌊z⌋ := by
    rw [← hcancel y, ← hcancel z, h]
  have hkey (w : ℝ) : ⌊(2 : ℝ) ^ q * Int.fract w⌋ =
      ⌊(2 : ℝ) ^ q * w⌋ - (2 : ℤ) ^ q * ⌊w⌋ := by
    rw [Int.fract]
    have heq : (2 : ℝ) ^ q * (w - (⌊w⌋ : ℝ)) =
        (2 : ℝ) ^ q * w - (((2 : ℤ) ^ q * ⌊w⌋ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [heq, Int.floor_sub_intCast]
  rw [hkey, hkey, h, hfloor]

/-- Periodic versions of all finest keys agree at one of the same representatives. -/
theorem exists_periodic_dyadic_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊(2 : ℝ) ^ B i * Int.fract (x + t' * ((2 : ℝ)⁻¹) ^ n i)⌋ =
          ⌊(2 : ℝ) ^ B i * Int.fract (x + t * ((2 : ℝ)⁻¹) ^ n i)⌋ := by
  obtain ⟨R, hR, hcard, hrep⟩ := exists_dyadic_grid_representatives x B n L hspan
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', heq⟩ := hrep t ht
  exact ⟨t', ht', fun i => periodic_floor_eq_of_floor_eq (B i) (heq i)⟩

/-- Deterministic representatives simultaneously work for every assignment of local
predicates that factors through the indicated periodic keys. In particular the
representatives do not depend on the random selector or terminal tables. -/
theorem exists_local_predicate_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : ι → ℝ → Bool,
          (∀ i y z, ⌊(2 : ℝ) ^ B i * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ B i * Int.fract z⌋ → Q i y = Q i z) →
          ∀ i, Q i (x + t' * ((2 : ℝ)⁻¹) ^ n i) =
            Q i (x + t * ((2 : ℝ)⁻¹) ^ n i) := by
  obtain ⟨R, hR, hcard, hrep⟩ := exists_periodic_dyadic_representatives x B n L hspan
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', heq⟩ := hrep t ht
  exact ⟨t', ht', fun Q hQ i => hQ i _ _ (heq i)⟩

/-- The stronger monotone-key estimate is within the entropy budget. -/
lemma representative_card_budget (M r D : ℕ) (hM : 1 ≤ M) (hr : 1 ≤ r) :
    1 + (M - 1) * r * D ≤ 20 * M * r * (1 + D) := by
  have hMr : 1 ≤ M * r := by nlinarith
  calc
    1 + (M - 1) * r * D ≤ M * r + M * r * D := by
      exact Nat.add_le_add hMr
        (Nat.mul_le_mul_right D (Nat.mul_le_mul_right r (Nat.sub_le M 1)))
    _ = M * r * (1 + D) := by ring
    _ ≤ 20 * M * r * (1 + D) := by nlinarith

end Problem310.ScaleDiscretization

end

end OAI

end

-- OpenAI source module: PeriodicEnvelope
section

namespace OAI

noncomputable section

namespace Problem310.Aux
open Set MeasureTheory

/-- Integer-periodization of a subset of the line. -/
def integerPeriodize (U : Set ℝ) : Set ℝ :=
  ⋃ k : ℤ, (fun x : ℝ => x + (k : ℝ)) ⁻¹' U

theorem isOpen_integerPeriodize (U : Set ℝ) (hU : IsOpen U) :
    IsOpen (integerPeriodize U) := by
  exact isOpen_iUnion fun k => hU.preimage (continuous_id.add continuous_const)

theorem integerPeriodize_onePeriodic (U : Set ℝ) :
    ∀ x : ℝ, x + 1 ∈ integerPeriodize U ↔ x ∈ integerPeriodize U := by
  intro x
  simp only [integerPeriodize, mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    convert hk using 1
    push_cast
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    convert hk using 1
    push_cast
    ring

/-- Periodization cannot increase the measure within a fundamental interval
beyond the measure of the original subset. -/
theorem volume_integerPeriodize_le (U : Set ℝ) (hU : MeasurableSet U) :
    volume (integerPeriodize U ∩ Icc (0 : ℝ) 1) ≤ volume U := by
  have hae : (integerPeriodize U ∩ Icc (0 : ℝ) 1 : Set ℝ) =ᵐ[volume]
      (integerPeriodize U ∩ Ico (0 : ℝ) 1 : Set ℝ) := by
    filter_upwards [(Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)).symm] with x hx
    exact propext (and_congr_right (fun _ => Iff.of_eq hx))
  rw [measure_congr hae]
  have hpiece (k : ℤ) :
      volume (((fun x : ℝ => x + (k : ℝ)) ⁻¹' U) ∩ Ico (0 : ℝ) 1) =
        volume (U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) := by
    have hI : (fun x : ℝ => x + (k : ℝ)) ⁻¹' Ico (k : ℝ) ((k : ℝ) + 1) =
        Ico (0 : ℝ) 1 := by
      ext x
      simp only [mem_preimage, mem_Ico]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [← hI, ← preimage_inter]
    exact measure_preimage_add_right volume (k : ℝ) _
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun k : ℤ => U ∩ Ico (k : ℝ) ((k : ℝ) + 1))) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro x hx hy
    rcases lt_or_gt_of_ne hij with h | h
    · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (show i + 1 ≤ j by omega)
      linarith [hx.2.2, hy.2.1]
    · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by
        exact_mod_cast (show j + 1 ≤ i by omega)
      linarith [hy.2.2, hx.2.1]
  have hunion : (⋃ k : ℤ, U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) = U := by
    rw [← inter_iUnion, iUnion_Ico_intCast, inter_univ]
  calc
    volume (integerPeriodize U ∩ Ico (0 : ℝ) 1)
        = volume (⋃ k : ℤ, ((fun x : ℝ => x + (k : ℝ)) ⁻¹' U) ∩ Ico (0 : ℝ) 1) := by
          rw [integerPeriodize, iUnion_inter]
    _ ≤ ∑' k : ℤ, volume (((fun x : ℝ => x + (k : ℝ)) ⁻¹' U) ∩ Ico (0 : ℝ) 1) :=
      measure_iUnion_le _
    _ = ∑' k : ℤ, volume (U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) := tsum_congr hpiece
    _ = volume (⋃ k : ℤ, U ∩ Ico (k : ℝ) ((k : ℝ) + 1)) :=
      (measure_iUnion hdisj (fun k => hU.inter measurableSet_Ico)).symm
    _ = volume U := congrArg volume hunion

/-- An arbitrarily small open periodic enlargement of a periodic set. -/
theorem exists_open_periodic_envelope (R : Set ℝ)
    (hR : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ENNReal) (hε : ε ≠ 0) :
    ∃ V : Set ℝ, R ⊆ V ∧ IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤ volume (R ∩ Icc (0 : ℝ) 1) + ε := by
  obtain ⟨U, hRU, hU, hμU⟩ :=
    (R ∩ Icc (0 : ℝ) 1).exists_isOpen_le_add volume hε
  refine ⟨integerPeriodize U, ?_, isOpen_integerPeriodize U hU,
    integerPeriodize_onePeriodic U, (volume_integerPeriodize_le U hU.measurableSet).trans hμU⟩
  intro x hx
  have hper : Function.Periodic (fun y : ℝ => y ∈ R) 1 := fun y => propext (hR y)
  have hmem : x - (⌊x⌋ : ℝ) ∈ R := by
    have heq := hper.sub_int_mul_eq (x := x) ⌊x⌋
    simpa using heq.mpr hx
  have hfrac : x - (⌊x⌋ : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le x)
    · have h := Int.lt_floor_add_one x
      linarith
  apply mem_iUnion.2
  refine ⟨-⌊x⌋, ?_⟩
  simpa only [mem_preimage, Int.cast_neg, ← sub_eq_add_neg] using hRU ⟨hmem, hfrac⟩

end Problem310.Aux

end

end OAI

end

-- OpenAI source module: RepresentativeFailure
section

namespace OAI

universe u_Ω u_T u_I u_J

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Problem310.RepresentativeFailure

end Problem310.RepresentativeFailure

end

end OAI

end

-- OpenAI source module: SelectedCoordinateLaw
section

namespace OAI

universe u_I u_K u_B

open MeasureTheory ProbabilityTheory

namespace Problem310.SelectedCoordinateLaw

end Problem310.SelectedCoordinateLaw

end OAI

end

-- OpenAI source module: PackedWindowSpan
section

namespace OAI

namespace Problem310.WindowRecursion

/-- Length of a list of windows packed with a fixed gap between consecutive
windows, with no leading or trailing gap. -/
def packedSpan (g : ℕ) (L : List ℕ) : ℕ := L.sum + (L.length - 1) * g

@[simp] theorem packedSpan_nil (g : ℕ) : packedSpan g [] = 0 := by
  simp [packedSpan]

@[simp] theorem packedSpan_singleton (g r : ℕ) : packedSpan g [r] = r := by
  simp [packedSpan]

/-- The deterministic list of incoming-window lengths in full preorder. -/
def preorderLengths (M g r₀ : ℕ) : ℕ → List ℕ
  | 0 => []
  | h + 1 => (List.replicate M (length M g r₀ (h + 1) :: preorderLengths M g r₀ h)).flatten

@[simp] theorem preorderLengths_zero (M g r₀ : ℕ) : preorderLengths M g r₀ 0 = [] := rfl

end Problem310.WindowRecursion

end OAI

end

-- OpenAI source module: PreorderIndex
section

namespace OAI

universe u_α u_β

namespace Problem310.PreorderIndex

private theorem idxOf_map_injective {α : Type u_α} {β : Type u_β} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (a : α) (l : List α) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  classical
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : b = a
    · subst b
      simp
    · have hfba : f b ≠ f a := fun he => h (hf he)
      simp only [List.map_cons, List.idxOf_cons_ne _ hfba, List.idxOf_cons_ne _ h, ih]

private theorem idxOf_flatMap_uniform {α : Type u_α} {β : Type u_β} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (l : List α) (f : α → List β) (R : ℕ) (hlen : ∀ a, (f a).length = R)
    (a : α) (b : β) (ha : a ∈ l) (hb : b ∈ f a)
    (hdisjoint : ∀ c, c ≠ a → b ∉ f c) :
    (l.flatMap f).idxOf b = l.idxOf a * R + (f a).idxOf b := by
  classical
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    by_cases hca : c = a
    · subst c
      rw [List.flatMap_cons, List.idxOf_append_of_mem hb]
      simp
    · have ha' : a ∈ l := by simpa [Ne.symm hca] using ha
      rw [List.flatMap_cons, List.idxOf_append_of_notMem (hdisjoint c hca),
        hlen c, ih ha', List.idxOf_cons_ne _ hca]
      simp only [Nat.succ_eq_add_one]
      ring

theorem size_eq_one_add_edgeCount (K d : ℕ) :
    TreePreorderRank.size K d = 1 + TreePreorder.edgeCount K d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [TreePreorderRank.size, TreePreorder.edgeCount, ih]

/-- The arithmetic preorder rank agrees with the actual list enumeration.
The root is omitted from `edgePaths`, hence the offset by one. -/
theorem rank_eq_idxOf_add_one {K d : ℕ} {p : List (Fin K)}
    (hp : p ∈ TreePreorder.edgePaths K d) :
    TreePreorderRank.rank d p = (TreePreorder.edgePaths K d).idxOf p + 1 := by
  induction d generalizing p with
  | zero => simp at hp
  | succ d ih =>
    cases p with
    | nil => simp [TreePreorder.mem_edgePaths_iff] at hp
    | cons i p =>
      have hplen : p.length ≤ d := by
        have h := (TreePreorder.mem_edgePaths_iff K (d + 1) (i :: p)).mp hp
        simpa using h.2
      let block : Fin K → List (List (Fin K)) := fun j =>
        [j] :: (TreePreorder.edgePaths K d).map (List.cons j)
      have hlen (j : Fin K) : (block j).length = 1 + TreePreorder.edgeCount K d := by
        simp [block, Nat.add_comm]
      have hmem : i :: p ∈ block i := by
        by_cases hp0 : p = []
        · subst p
          simp [block]
        · apply List.mem_cons.mpr
          right
          apply List.mem_map.mpr
          exact ⟨p, (TreePreorder.mem_edgePaths_iff K d p).mpr ⟨hp0, hplen⟩, rfl⟩
      have hdisjoint (j : Fin K) (hji : j ≠ i) : i :: p ∉ block j := by
        intro hm
        obtain ⟨s, he⟩ := TreePreorder.mem_childBlock_prefix K d j (i :: p) hm
        exact hji (List.cons.inj he).1.symm
      have hindex := idxOf_flatMap_uniform (List.finRange K) block
        (1 + TreePreorder.edgeCount K d) hlen i (i :: p)
        (List.mem_finRange i) hmem hdisjoint
      simp only [List.idxOf_finRange] at hindex
      change (TreePreorder.edgePaths K (d + 1)).idxOf (i :: p) =
        i.val * (1 + TreePreorder.edgeCount K d) + (block i).idxOf (i :: p) at hindex
      rw [TreePreorderRank.rank_cons, hindex, size_eq_one_add_edgeCount]
      by_cases hp0 : p = []
      · subst p
        simp [block]
        omega
      · have hpedge := (TreePreorder.mem_edgePaths_iff K d p).mpr ⟨hp0, hplen⟩
        have hneq : [i] ≠ i :: p := by
          intro h
          exact hp0 (List.cons.inj h).2.symm
        have hbi : (block i).idxOf (i :: p) =
            (TreePreorder.edgePaths K d).idxOf p + 1 := by
          dsimp only [block]
          rw [List.idxOf_cons_ne _ hneq, idxOf_map_injective (List.cons i)
            (by intro a b h; exact (List.cons.inj h).2)]
        rw [hbi, ih hpedge]
        omega

theorem edgeRank_eq_idxOf {K d : ℕ} {p : List (Fin K)}
    (hp : p ∈ TreePreorder.edgePaths K d) :
    TreePreorderRank.edgeRank d p = (TreePreorder.edgePaths K d).idxOf p := by
  rw [TreePreorderRank.edgeRank, rank_eq_idxOf_add_one hp]
  omega

end Problem310.PreorderIndex

end OAI

end

-- OpenAI source module: TrialAddresses
section

namespace OAI

universe u_E u_I u_C u_L

noncomputable section

namespace Problem310.TrialAddresses

open GridSeparation

/-- Coordinates of a finite family of dyadic tables. Different table names
are different coordinates even when their numeric cell keys coincide. -/
abbrev GridAddress {E : Type u_E} (b : E → ℕ) := Σ e : E, Fin (2 ^ (b e + 2))

def centerAddress {E : Type u_E} (b : E → ℕ) (x : ℝ) (e : E) : GridAddress b :=
  ⟨e, dyadicKey (b e) x⟩

/-- Refinement preserves all equalities needed to recover a coarse key. -/
theorem dyadicKey_eq_of_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (h : dyadicKey B x = dyadicKey B y) : dyadicKey b x = dyadicKey b y := by
  rw [dyadicKey_eq_iff]
  exact periodicKey_dyadic_eq_of_refine hb ((dyadicKey_eq_iff B x y).mp h)

def trialAddress {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (i : I) : GridAddress b :=
  ⟨edge i, dyadicKey (b (edge i)) (x + t * (2 : ℝ)⁻¹ ^ n i)⟩

/-- A tested coordinate is distinct from every center-exposed coordinate. -/
theorem trialAddress_ne_center {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (edge i)) (i : I) (e : E) :
    trialAddress b edge n x t i ≠ centerAddress b x e := by
  intro h
  have he : edge i = e := congrArg Sigma.fst h
  subst e
  have hv := congrArg (fun z : GridAddress b => z.2.val) h
  have hk : dyadicKey (b (edge i)) (x + t * (2 : ℝ)⁻¹ ^ n i) =
      dyadicKey (b (edge i)) x := Fin.ext hv
  exact (dyadicKey_ne_center (hnlo i) (hnhi i) htlo hthi) hk.symm

/-- Distinct table/index pairs give distinct fresh selector coordinates. -/
theorem trialAddress_injective {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (edge i))
    (hpair : Function.Injective (fun i => (edge i, n i))) :
    Function.Injective (trialAddress b edge n x t) := by
  intro i j h
  have he : edge i = edge j := congrArg Sigma.fst h
  have hv := congrArg (fun z : GridAddress b => z.2.val) h
  change (dyadicKey (b (edge i)) _).val = (dyadicKey (b (edge j)) _).val at hv
  rw [he] at hv
  have hk : dyadicKey (b (edge j)) (x + t * (2 : ℝ)⁻¹ ^ n i) =
      dyadicKey (b (edge j)) (x + t * (2 : ℝ)⁻¹ ^ n j) := Fin.ext hv
  have hi : n i ≤ b (edge j) := he ▸ hnhi i
  have hn : n i = n j :=
    dyadicKey_injOn (a := 3) (by omega) htlo hthi
      ⟨hnlo i, hi⟩ ⟨hnlo j, hnhi j⟩ hk
  exact hpair (Prod.ext he hn)

/-- Adaptive terminal addresses are injective whenever equal leaves force
the same child subtree, and each terminal resolution refines that child's
incoming grid. The leaf selection may otherwise depend arbitrarily on all
selector tables. -/
theorem terminalAddress_injective {I : Type u_I} {C : Type u_C} {L : Type u_L}
    (child : I → C) (n : I → ℕ) (leaf : I → L)
    (b : C → ℕ) (B : L → ℕ) (x t : ℝ)
    (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (child i))
    (hrefine : ∀ i, b (child i) ≤ B (leaf i))
    (hbranch : ∀ i j, leaf i = leaf j → child i = child j)
    (hpair : Function.Injective (fun i => (child i, n i))) :
    Function.Injective (trialAddress B leaf n x t) := by
  intro i j h
  have hl : leaf i = leaf j := congrArg Sigma.fst h
  have hc : child i = child j := hbranch i j hl
  have hv := congrArg (fun z : GridAddress B => z.2.val) h
  change (dyadicKey (B (leaf i)) _).val = (dyadicKey (B (leaf j)) _).val at hv
  rw [hl] at hv
  have hk : dyadicKey (B (leaf j)) (x + t * (2 : ℝ)⁻¹ ^ n i) =
      dyadicKey (B (leaf j)) (x + t * (2 : ℝ)⁻¹ ^ n j) := Fin.ext hv
  have hcoarse := dyadicKey_eq_of_refine (hrefine j) hk
  have hi : n i ≤ b (child j) := hc ▸ hnhi i
  have hn : n i = n j :=
    dyadicKey_injOn (a := 3) (by omega) htlo hthi
      ⟨hnlo i, hi⟩ ⟨hnlo j, hnhi j⟩ hcoarse
  exact hpair (Prod.ext hc hn)

/-- A uniform block of `r` indices for each of `M` nondefault children.
This finite trial type has exactly the exponent used in the miss formula. -/
abbrev WindowTrial (M r : ℕ) := Fin M × Fin r

def windowTrialIndex {M r : ℕ} (a : Fin M → ℕ) (i : WindowTrial M r) : ℕ :=
  a i.1 + i.2.val

@[simp] theorem card_windowTrial (M r : ℕ) :
    Fintype.card (WindowTrial M r) = M * r := by simp [WindowTrial]

theorem windowTrial_pair_injective {M r : ℕ} {E : Type u_E}
    (a : Fin M → ℕ) (edge : Fin M → E) (hedge : Function.Injective edge) :
    Function.Injective (fun i : WindowTrial M r =>
      (edge i.1, windowTrialIndex a i)) := by
  intro i j h
  have hc : i.1 = j.1 := hedge (congrArg Prod.fst h)
  have hn : windowTrialIndex a i = windowTrialIndex a j := congrArg Prod.snd h
  have ho : i.2 = j.2 := by
    apply Fin.ext
    dsimp [windowTrialIndex] at hn
    rw [hc] at hn
    omega
  exact Prod.ext hc ho

end Problem310.TrialAddresses

end

end OAI

end

-- OpenAI source module: FiniteTableModel
section

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.FiniteTableModel

/-- Child `M` is default and the other `M` children have selectors. -/
abbrev Child (M : ℕ) := Fin (M + 1)

/-- Nodes at which a depth-`d` router still makes a decision. -/
abbrev Node (M d : ℕ) := {P : List (Child M) // P.length < d}

/-- A terminal path. This is definitionally a list with the required length. -/
abbrev Leaf (M d : ℕ) := List.Vector (Child M) d

instance nodeFintype (M d : ℕ) : Fintype (Node M d) := by
  classical
  let f : (Σ k : Fin d, List.Vector (Child M) k.val) → Node M d :=
    fun p => ⟨p.2.val, by simpa only [p.2.property] using p.1.isLt⟩
  apply Fintype.ofSurjective f
  intro P
  exact ⟨⟨⟨P.val.length, P.property⟩, ⟨P.val, rfl⟩⟩, rfl⟩

instance nodeMeasurableSpace (M d : ℕ) : MeasurableSpace (Node M d) := ⊤
instance nodeDiscreteMeasurableSpace (M d : ℕ) : DiscreteMeasurableSpace (Node M d) := by constructor; intro s; trivial
instance leafMeasurableSpace (M d : ℕ) : MeasurableSpace (Leaf M d) := ⊤
instance leafDiscreteMeasurableSpace (M d : ℕ) : DiscreteMeasurableSpace (Leaf M d) := by constructor; intro s; trivial

/-- Finite selector-table addresses include the table name as well as its key. -/
abbrev SelectorAddress {M d : ℕ} (b : Node M d → Fin M → ℕ) :=
  Σ e : Node M d × Fin M, Fin (2 ^ (b e.1 e.2 + 2))

/-- Terminal addresses include the leaf name, preventing collisions between tables. -/
abbrev TerminalAddress {M d : ℕ} (b : Leaf M d → ℕ) :=
  Σ L : Leaf M d, Fin (2 ^ (b L + 2))

instance selectorAddressMeasurableSpace {M d : ℕ} (b : Node M d → Fin M → ℕ) :
    MeasurableSpace (SelectorAddress b) := ⊤
instance selectorAddressDiscreteMeasurableSpace {M d : ℕ} (b : Node M d → Fin M → ℕ) :
    DiscreteMeasurableSpace (SelectorAddress b) := by constructor; intro s; trivial
instance terminalAddressMeasurableSpace {M d : ℕ} (b : Leaf M d → ℕ) :
    MeasurableSpace (TerminalAddress b) := ⊤
instance terminalAddressDiscreteMeasurableSpace {M d : ℕ} (b : Leaf M d → ℕ) :
    DiscreteMeasurableSpace (TerminalAddress b) := by constructor; intro s; trivial

abbrev SelectorTable {M d : ℕ} (b : Node M d → Fin M → ℕ) := SelectorAddress b → Bool
abbrev TerminalTable {M d : ℕ} (b : Leaf M d → ℕ) := TerminalAddress b → Bool

/-- The center exposure consults exactly one deterministic coordinate per selector table. -/
def selectorAddress {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) (x : ℝ) : SelectorAddress b :=
  ⟨(P, i), GridSeparation.dyadicKey (b P i) x⟩

/-- The terminal coordinate read along the selected leaf. -/
def terminalAddress {M d : ℕ} (b : Leaf M d → ℕ)
    (L : Leaf M d) (x : ℝ) : TerminalAddress b :=
  ⟨L, GridSeparation.dyadicKey (b L) x⟩

/-- Selector values are extended to all lists; routing uses only valid nodes. -/
def selectorValue {M d : ℕ} (b : Node M d → Fin M → ℕ) (ω : SelectorTable b)
    (P : List (Child M)) (i : Fin M) (x : ℝ) : Bool :=
  if h : P.length < d then ω (selectorAddress b ⟨P, h⟩ i x) else false

@[simp] theorem selectorValue_valid {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : Node M d) (i : Fin M) (x : ℝ) :
    selectorValue b ω P.val i x = ω (selectorAddress b P i x) := by
  simp [selectorValue, P.property]

lemma measurable_dyadicKey (b : ℕ) : Measurable (GridSeparation.dyadicKey b) := by
  apply measurable_to_countable
  intro y
  have hm : Measurable (GridSeparation.periodicKey ((2 : ℝ) ^ (b + 2))) := by
    exact (measurable_const.mul measurable_fract).floor
  convert (measurableSet_singleton (GridSeparation.periodicKey ((2 : ℝ) ^ (b + 2)) y)).preimage hm using 1
  ext x
  exact GridSeparation.dyadicKey_eq_iff b x y

lemma dyadicKey_add_one (b : ℕ) (x : ℝ) :
    GridSeparation.dyadicKey b (x + 1) = GridSeparation.dyadicKey b x := by
  apply (GridSeparation.dyadicKey_eq_iff _ _ _).mpr
  exact GridSeparation.periodicKey_add_one _ _

lemma measurable_selectorAddress {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) : Measurable (selectorAddress b P i) := by
  exact (measurable_of_finite (fun k => (⟨(P, i), k⟩ : SelectorAddress b))).comp
    (measurable_dyadicKey (b P i))

lemma measurable_terminalAddress {M d : ℕ} (b : Leaf M d → ℕ)
    (L : Leaf M d) : Measurable (terminalAddress b L) := by
  exact (measurable_of_finite (fun k => (⟨L, k⟩ : TerminalAddress b))).comp
    (measurable_dyadicKey (b L))

lemma measurable_selectorValue {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (i : Fin M) :
    Measurable (selectorValue b ω P i) := by
  change Measurable (fun x : ℝ => if h : P.length < d then
    ω (selectorAddress b ⟨P, h⟩ i x) else false)
  by_cases h : P.length < d
  · simp only [dif_pos h]
    exact (measurable_of_finite ω).comp (measurable_selectorAddress b ⟨P, h⟩ i)
  · simpa only [dif_neg h] using (measurable_const : Measurable (fun _ : ℝ => false))

@[simp] lemma selectorAddress_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) (x : ℝ) :
    selectorAddress b P i (x + 1) = selectorAddress b P i x := by
  simp [selectorAddress, dyadicKey_add_one]

@[simp] lemma terminalAddress_add_one {M d : ℕ} (b : Leaf M d → ℕ)
    (L : Leaf M d) (x : ℝ) :
    terminalAddress b L (x + 1) = terminalAddress b L x := by
  simp [terminalAddress, dyadicKey_add_one]

@[simp] lemma selectorValue_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (i : Fin M) (x : ℝ) :
    selectorValue b ω P i (x + 1) = selectorValue b ω P i x := by
  by_cases h : P.length < d <;> simp [selectorValue, h]

/-- Exposing the center reads distinct coordinates because table names are retained. -/
lemma center_selectorAddress_injective {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (x : ℝ) : Function.Injective (fun e : Node M d × Fin M => selectorAddress b e.1 e.2 x) := by
  intro e f h
  exact congrArg Sigma.fst h

lemma dyadicKey_eq_of_refine {b B : ℕ} (hb : b ≤ B) {x y : ℝ}
    (hkey : GridSeparation.dyadicKey B x = GridSeparation.dyadicKey B y) :
    GridSeparation.dyadicKey b x = GridSeparation.dyadicKey b y := by
  apply (GridSeparation.dyadicKey_eq_iff b x y).mpr
  exact GridSeparation.periodicKey_dyadic_eq_of_refine hb
    ((GridSeparation.dyadicKey_eq_iff B x y).mp hkey)

end Problem310.FiniteTableModel

end

end OAI

end

-- OpenAI source module: PeriodicEnlargement
section

namespace OAI

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- Enlarging the test set can only remove exceptional centers. -/
theorem exceptionalCenters_antitone {B V : Set ℝ} (hBV : B ⊆ V)
    (N : Set ℕ) (a : ℕ → ℝ) :
    exceptionalCenters V N a ⊆ exceptionalCenters B N a := by
  rintro x ⟨t, ht, h⟩
  exact ⟨t, ht, fun n hn hm => h n hn (hBV hm)⟩

end Problem310.Auxiliary

end

end OAI

end

-- OpenAI source module: FiniteTableFirstDefault
section

namespace OAI

universe u_K

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem310.FirstDefault

/-- Transport of the finite-depth survival law to actual finite spatial
selector tables. The center lookup need only select distinct coordinates;
unused table entries are integrated out automatically. -/
theorem measure_no_default_finite_table {M d : ℕ} {K : Type u_K} [Fintype K]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ b, ν {b} = (2 : ENNReal)⁻¹)
    (center : BoundedAddress M d → K) (hinj : Function.Injective center) :
    (Measure.pi (fun _ : K => ν))
        (⋃ f : Path M d, {ω | ∀ i : Tests f,
          ω (center (boundedAddress f i)) = requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  apply measure_no_default_bounded
    (Measure.pi (fun _ : K => ν)) (fun a ω => ω (center a))
  · intro a
    exact measurable_pi_apply _
  · have hi : iIndepFun (fun k (ω : K → Bool) => ω k)
        (Measure.pi (fun _ : K => ν)) :=
      iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    exact hi.precomp hinj
  · intro a b
    rw [(measurePreserving_eval (fun _ : K => ν) (center a)).measure_preimage
      (measurableSet_singleton b).nullMeasurableSet]
    exact hfair b

end Problem310.FirstDefault

end

end OAI

end

-- OpenAI source module: ChildDistribution
section

namespace OAI

open MeasureTheory Set
open scoped BigOperators

namespace Problem310.OrderedRouting

variable {M : ℕ} (ν : Measure Bool) [IsProbabilityMeasure ν]

end Problem310.OrderedRouting

end OAI

end

-- OpenAI source module: FirstDefaultSelection
section

namespace OAI

universe u_Ω u_ι u_X u_Y

noncomputable section

namespace Problem310.FirstDefault

/-- A path cylinder is exactly the event that first-success routing selects
its prescribed child at each of its prescribed nodes. -/
theorem cylinder_iff_chooseChild {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (f : Path M d) (ω : Ω) :
    ω ∈ cylinder S f ↔ ∀ k : Fin d,
      OrderedRouting.chooseChild (fun j => S (pathPrefix f k, j) ω) = (f k).castSucc := by
  constructor
  · intro h k
    apply (OrderedRouting.chooseChild_eq_nondefault_iff _ _).mpr
    constructor
    · have hi := h ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩
      simpa only [address, requiredBit, decide_true] using hi
    · intro j hj
      have hi := h ⟨k, ⟨j.val, lt_trans hj (Nat.lt_succ_self _)⟩⟩
      have hne : j.val ≠ (f k).val := Nat.ne_of_lt hj
      simpa only [address, requiredBit, hne, decide_false] using hi
  · intro h i
    obtain ⟨k, j⟩ := i
    obtain ⟨hsuccess, hprev⟩ :=
      (OrderedRouting.chooseChild_eq_nondefault_iff _ _).mp (h k)
    by_cases heq : j.val = (f k).val
    · have ha : address f ⟨k, j⟩ = (pathPrefix f k, f k) := by
        apply Prod.ext
        · rfl
        · exact Fin.ext heq
      change S (address f ⟨k, j⟩) ω = requiredBit f ⟨k, j⟩
      simpa only [ha, requiredBit, heq, decide_true] using hsuccess
    · have hlt : j.val < (f k).val := by omega
      have hj := hprev ⟨j.val, lt_trans hlt (f k).isLt⟩ hlt
      change S (address f ⟨k, j⟩) ω = requiredBit f ⟨k, j⟩
      simpa only [address, requiredBit, heq, decide_false] using hj

/-- Canonical child choice from a family of selector bits at tree addresses. -/
def centerChoice {M : ℕ} {Ω : Type u_Ω} (S : Address M → Ω → Bool)
    (P : List (Fin (M + 1))) (ω : Ω) : Fin (M + 1) :=
  OrderedRouting.chooseChild (fun j => S (P, j) ω)

/-- The actual routed center avoids the default exactly on the finite union
of the path cylinders used by the exact first-default probability law. -/
theorem noDefault_iff_mem_cylinders {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (ω : Ω) :
    (∀ k < d, centerChoice S (RoutingPath.routeFrom (centerChoice S) k [] ω) ω ≠
      Fin.last M) ↔ ω ∈ ⋃ f : Path M d, cylinder S f := by
  rw [RoutingPath.noDefault_iff_exists_choices]
  simp only [Set.mem_iUnion, cylinder_iff_chooseChild]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, fun k => ?_⟩
    simpa only [centerChoice, pathPrefix_eq_take_ofFn] using hf k.val k.isLt
  · rintro ⟨f, hf⟩
    refine ⟨f, fun k hk => ?_⟩
    simpa only [centerChoice, pathPrefix_eq_take_ofFn] using hf ⟨k, hk⟩

/-- Change the auxiliary parameter space without changing any node choices. -/
theorem routeFrom_change_parameter {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (f : List ι → X → ι) (g : List ι → Y → ι) (x : X) (y : Y)
    (h : ∀ P, f P x = g P y) (n : ℕ) (P : List ι) :
    RoutingPath.routeFrom f n P x = RoutingPath.routeFrom g n P y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [RoutingPath.routeFrom_succ, ih, h]

/-- Equivalent leaf-membership formulation, convenient for concrete routers. -/
theorem default_not_mem_iff_mem_cylinders {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (ω : Ω) :
    Fin.last M ∉ RoutingPath.routeFrom (centerChoice S) d [] ω ↔
      ω ∈ ⋃ f : Path M d, cylinder S f := by
  rw [← RoutingPath.noDefault_iff_not_mem]
  exact noDefault_iff_mem_cylinders S ω

/-- Spatially parametrized selectors have the same no-default event as the
cylinders at a fixed center. This is directly usable with `selectorValue`. -/
theorem spatial_default_not_mem_iff {M d : ℕ} {Ω : Type u_Ω} {X : Type u_X}
    (S : Ω → List (Fin (M + 1)) → Fin M → X → Bool) (ω : Ω) (x : X) :
    Fin.last M ∉ RoutingPath.routeFrom
      (fun P y => OrderedRouting.chooseChild (fun j => S ω P j y)) d [] x ↔
      ω ∈ ⋃ f : Path M d,
        cylinder (fun a ω' => S ω' a.1 a.2 x) f := by
  have hr := routeFrom_change_parameter
    (centerChoice (fun a ω' => S ω' a.1 a.2 x))
    (fun P y => OrderedRouting.chooseChild (fun j => S ω P j y)) ω x
    (fun _ => rfl) d []
  rw [← hr]
  exact default_not_mem_iff_mem_cylinders _ ω

end Problem310.FirstDefault

end

end OAI

end

-- OpenAI source module: StableRoutingBridge
section

namespace OAI

universe u_X

noncomputable section

namespace Problem310.StableRouting

open OrderedRouting RoutingPath

variable {M : ℕ} {X : Type u_X}

/-- Ordered routing associated to the spatial selector values. -/
def select (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (P : List (Fin (M + 1))) (x : X) : Fin (M + 1) :=
  chooseChild (fun i => S P i x)

/-- A nondefault decision is unchanged if all selectors up to that decision agree. -/
theorem select_eq_of_earlier_agreement
    (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (P : List (Fin (M + 1))) (x y : X)
    (hnd : select S P x ≠ Fin.last M)
    (hagree : ∀ j : Fin M, j.castSucc ≤ select S P x → S P j x = S P j y) :
    select S P y = select S P x := by
  generalize hc : select S P x = c at *
  induction c using Fin.lastCases with
  | last => exact (hnd rfl).elim
  | cast i =>
    exact chooseChild_preserved (fun j => S P j x) (fun j => S P j y) i hc
      (fun j hj => hagree j (Fin.castSucc_le_castSucc_iff.mpr hj))

/-- At a center's default node, preserving the earlier selectors rejects those children. -/
theorem rejects_earlier_at_default
    (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (U : List (Fin (M + 1))) (x y : X) (i : Fin M)
    (hdefault : select S U x = Fin.last M)
    (hagree : ∀ j < i, S U j x = S U j y) :
    ∀ j < i, S U j y = false := by
  intro j hj
  rw [← hagree j hj]
  exact (chooseChild_eq_default_iff (fun j => S U j x)).mp hdefault j

end Problem310.StableRouting

end

end OAI

end

-- OpenAI source module: LocalPredicateFactor
section

namespace OAI

universe u_ι u_X u_K u_V u_J

noncomputable section

namespace Problem310.LocalPredicateFactor

open RoutingPath GridSeparation

variable {ι : Type u_ι} {X : Type u_X} {K : Type u_K} {V : Type u_V}

/-- Routing through a subtree only uses its strict-descendant choices.
If those choices factor through one key, the terminal leaf does too. -/
theorem route_eq_of_key_eq (choose : List ι → X → ι)
    (key : X → K) (r : ℕ) (P : List ι)
    (hchoice : ∀ Q : List ι, P.IsPrefix Q → Q.length < P.length + r →
      ∀ x y : X, key x = key y → choose Q x = choose Q y)
    {x y : X} (hxy : key x = key y) :
    routeFrom choose r P x = routeFrom choose r P y := by
  apply routeFrom_eq_of_choices_eq choose r P y x
  intro k hk
  apply hchoice (routeFrom choose k P y) (prefix_routeFrom choose k P y)
  · rw [length_routeFrom]
    omega
  · exact hxy

/-- A single table evaluated at any coarser grid is a function of the finest key. -/
theorem table_eq_of_finest_key {b B : ℕ} (hb : b ≤ B)
    (table : Fin (2 ^ (b + 2)) → V) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    table (dyadicKey b x) = table (dyadicKey b y) := by
  apply congrArg table
  apply (dyadicKey_eq_iff b x y).mpr
  exact periodicKey_dyadic_eq_of_refine hb hxy

variable {J : Type u_J}

end Problem310.LocalPredicateFactor

end

end OAI

end

-- OpenAI source module: RoutedAddressInjectivity
section

namespace OAI

universe u_I u_A u_X u_K

noncomputable section

namespace Problem310.AddressInjectivity

end Problem310.AddressInjectivity

end

end OAI

end

-- OpenAI source module: OrderedRoutePreservation
section

namespace OAI

universe u_X

noncomputable section

namespace Problem310.OrderedRoutePreservation

open OrderedRouting RoutingPath

variable {M : ℕ} {X : Type u_X}

end Problem310.OrderedRoutePreservation

end

end OAI

end

-- OpenAI source module: PeriodicBasic
section

namespace OAI

noncomputable section

namespace Problem310

def OnePeriodic (H : Set ℝ) : Prop :=
  ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H

def periodDensity (H : Set ℝ) : ENNReal :=
  MeasureTheory.volume (H ∩ Set.Icc (0 : ℝ) 1)

end Problem310

end

end OAI

end

-- OpenAI source module: CenterExposure
section

namespace OAI

universe u_C u_I u_K u_B

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Problem310.CenterExposure

/-- Center constraints do not alter the product law of distinct fresh
coordinates. This unnormalized identity avoids all conditional-expectation
bookkeeping and applies to arbitrary coordinate label spaces. -/
theorem measure_center_and_fresh
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K]
    [MeasurableSpace B] (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh))
    (s : C → Set B) (t : I → Set B)
    (hs : ∀ c, MeasurableSet (s c)) (ht : ∀ i, MeasurableSet (t i)) :
    (Measure.pi (fun _ : K => ν))
      {ω | (∀ c, ω (center c) ∈ s c) ∧ (∀ i, ω (fresh i) ∈ t i)} =
      (∏ c, ν (s c)) * ∏ i, ν (t i) := by
  have h := AdaptiveLabels.measure_injective_constraints ν
    (Sum.elim center fresh) hinj (Sum.elim s t) (by
      intro k
      cases k with
      | inl c => exact hs c
      | inr i => exact ht i)
  simpa only [Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Fintype.prod_sum_type] using h

/-- Specialization to an atom specifying all exposed center entries. -/
theorem measure_center_atom_and_fresh
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh))
    (value : C → B) (t : I → Set B)
    (ht : ∀ i, MeasurableSet (t i)) :
    (Measure.pi (fun _ : K => ν))
      {ω | (∀ c, ω (center c) = value c) ∧ (∀ i, ω (fresh i) ∈ t i)} =
      (∏ c, ν {value c}) * ∏ i, ν (t i) := by
  simpa only [Set.mem_singleton_iff] using
    measure_center_and_fresh ν center fresh hinj (fun c => {value c}) t
      (fun c => measurableSet_singleton (value c)) ht

/-- The whole fresh coordinate vector has its original product law after
restricting to a center atom, multiplied only by the atom's mass. This
form permits arbitrary fresh-vector events and moments, not just cylinders. -/
theorem map_fresh_restrict_center_atom
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K] [Countable B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → B) :
    Measure.map (fun ω : K → B => fun i => ω (fresh i))
      ((Measure.pi (fun _ : K => ν)).restrict
        {ω | ∀ c, ω (center c) = value c}) =
      (∏ c, ν {value c}) • Measure.pi (fun _ : I => ν) := by
  have hg : Measurable (fun ω : K → B => fun i => ω (fresh i)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (fresh i))
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply hg (measurableSet_singleton v),
    Measure.restrict_apply (hg (measurableSet_singleton v))]
  have heq :
      (fun ω : K → B => fun i => ω (fresh i)) ⁻¹' {v} ∩
        {ω | ∀ c, ω (center c) = value c} =
      {ω : K → B | (∀ c, ω (center c) = value c) ∧
        (∀ i, ω (fresh i) ∈ ({v i} : Set B))} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, funext_iff]
    exact and_comm
  rw [heq, measure_center_atom_and_fresh ν center fresh hinj value
    (fun i => {v i}) (fun i => measurableSet_singleton (v i))]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_singleton]

/-- Any nonnegative measurable function of the fresh vector has the same
moment on a center atom, up to multiplication by the atom mass. -/
theorem lintegral_fresh_restrict_center_atom
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K] [Countable B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → B)
    (F : (I → B) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (fun i => ω (fresh i)) ∂
      ((Measure.pi (fun _ : K => ν)).restrict
        {ω | ∀ c, ω (center c) = value c})) =
      (∏ c, ν {value c}) * ∫⁻ v, F v ∂Measure.pi (fun _ : I => ν) := by
  have hg : Measurable (fun ω : K → B => fun i => ω (fresh i)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (fresh i))
  rw [← lintegral_map hF hg, map_fresh_restrict_center_atom ν center fresh hinj value,
    lintegral_smul_measure, smul_eq_mul]

end Problem310.CenterExposure

end

end OAI

end

-- OpenAI source module: WindowSpanSum
section

namespace OAI

namespace Problem310.WindowSpanSum

open WindowRecursion

/-- The window lengths in edge preorder; the first length is that of the
incoming edge, followed by its complete descendant block. -/
def preorderLengths (M g r₀ : ℕ) : ℕ → List ℕ
  | 0 => []
  | h + 1 => (List.replicate M
      (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h)).flatten

/-- Charge a gap after every entry, including the final entry. -/
def paddedSum (g : ℕ) (L : List ℕ) : ℕ := (L.map (fun r => r + g)).sum

@[simp] theorem paddedSum_nil (g : ℕ) : paddedSum g [] = 0 := rfl

@[simp] theorem paddedSum_cons (g r : ℕ) (L : List ℕ) :
    paddedSum g (r :: L) = r + g + paddedSum g L := rfl

@[simp] theorem paddedSum_append (g : ℕ) (L K : List ℕ) :
    paddedSum g (L ++ K) = paddedSum g L + paddedSum g K := by
  simp [paddedSum]

@[simp] theorem paddedSum_flatten_replicate (g M : ℕ) (L : List ℕ) :
    paddedSum g (List.replicate M L).flatten = M * paddedSum g L := by
  induction M with
  | zero => simp [paddedSum]
  | succ M ih =>
      simp only [List.replicate_succ, List.flatten_cons, paddedSum_append, ih]
      ring

private theorem last_gap (M g : ℕ) (hM : 1 ≤ M) : (M - 1) * g + g = M * g := by
  simpa [Nat.add_mul] using congrArg (fun n => n * g) (Nat.sub_add_cancel hM)

/-- The exact recursive span is the preorder padded sum with the final gap removed. -/
theorem paddedSum_preorderLengths (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    paddedSum g (preorderLengths M g r₀ h) =
      if h = 0 then 0 else span M g r₀ h + g := by
  induction h with
  | zero => rfl
  | succ h ih =>
      rw [preorderLengths, paddedSum_flatten_replicate, paddedSum_cons, ih]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      rw [span_succ]
      have hg := last_gap M g hM
      cases h with
      | zero =>
          simp only [ite_true, childSpan_zero, Nat.add_zero, Nat.zero_add]
          nlinarith
      | succ h =>
          simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
          rw [childSpan_succ]
          nlinarith

/-- A child block has its precise geometric span plus one terminal gap. -/
theorem paddedSum_childBlock (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    paddedSum g (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h) =
      childSpan M g r₀ h + g := by
  rw [paddedSum_cons, paddedSum_preorderLengths M g r₀ h hM]
  cases h with
  | zero => simp
  | succ h => simp [childSpan_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- This is exactly the padded-length budget consumed by `WindowPlacement.block_padding`. -/
theorem childBlock_budget (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    paddedSum g (WindowRecursion.length M g r₀ (h + 1) :: preorderLengths M g r₀ h) ≤
      2 * WindowRecursion.length M g r₀ (h + 1) + g := by
  rw [paddedSum_childBlock M g r₀ h hM]
  exact Nat.add_le_add_right (childSpan_le_twice_length M g r₀ h) g

end Problem310.WindowSpanSum

end OAI

end

-- OpenAI source module: WindowMetadata
section

namespace OAI

noncomputable section

namespace Problem310.WindowMetadata

open TreePreorder

/-- The canonical preorder index of an edge. -/
def edgeIndex {q d : ℕ} (e : Edge q d) : ℕ := (edgePaths q d).idxOf e.val

/-- Numeric incoming-window height for an edge path. -/
def edgeHeight {q d : ℕ} (e : Edge q d) : ℕ := d + 1 - e.val.length

/-- Window lengths in precisely the canonical tree-edge preorder. -/
def lengths (q d g r₀ : ℕ) : List ℕ :=
  (edgePaths q d).map (fun P => WindowRecursion.length q g r₀ (d + 1 - P.length))

/-- The length function consumed by the canonical numeric placement API. -/
def lengthAt (q d g r₀ : ℕ) : ℕ → ℕ :=
  WindowPlacement.lengthAt (lengths q d g r₀)

def start {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : ℕ :=
  WindowPlacement.start (lengthAt q d g r₀) g (edgeIndex e)

def finish {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : ℕ :=
  WindowPlacement.finish (lengthAt q d g r₀) g (edgeIndex e)

def window {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : Finset ℕ :=
  WindowPlacement.window (lengthAt q d g r₀) g (edgeIndex e)

@[simp] theorem lengthAt_edgeIndex {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) :
    lengthAt q d g r₀ (edgeIndex e) = WindowRecursion.length q g r₀ (edgeHeight e) := by
  simp only [lengthAt, lengths, WindowPlacement.lengthAt, edgeIndex,
    List.getElem?_map, List.getElem?_idxOf e.property, Option.map_some, Option.getD_some,
    edgeHeight]

@[simp] theorem card_window {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) :
    (window g r₀ e).card = WindowRecursion.length q g r₀ (edgeHeight e) := by
  simp only [window, WindowPlacement.card_window, lengthAt_edgeIndex]

theorem three_le_start {q d : ℕ} (g r₀ : ℕ) (e : Edge q d) : 3 ≤ start g r₀ e :=
  WindowPlacement.three_le_start _ _ _

@[simp] theorem mem_window {q d : ℕ} {g r₀ n : ℕ} {e : Edge q d} :
    n ∈ window g r₀ e ↔ start g r₀ e ≤ n ∧ n ≤ finish g r₀ e :=
  WindowPlacement.mem_window

@[simp] theorem child_height {q d : ℕ} (P : List (Fin q)) (hP : P.length < d)
    (i : Fin q) : edgeHeight (childEdge P hP i) = d - P.length := by
  simp [edgeHeight, childEdge, mkEdge]

@[simp] theorem child_window_card {q d : ℕ} (g r₀ : ℕ)
    (P : List (Fin q)) (hP : P.length < d) (i : Fin q) :
    (window g r₀ (childEdge P hP i)).card =
      WindowRecursion.length q g r₀ (d - P.length) := by
  rw [card_window, child_height]

end Problem310.WindowMetadata

end

end OAI

end

-- OpenAI source module: GlobalFromPeriodic
section

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- A small open deletion from the unit interval leaves a compact set
whose volume is strictly greater than the requested threshold. -/
theorem compact_complement_volume {C : Set ℝ} (hC : IsOpen C)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hsmall : volume (C ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (η / 2)) :
    IsCompact (Icc (0 : ℝ) 1 \ C) ∧
      ENNReal.ofReal (1 - η) < volume (Icc (0 : ℝ) 1 \ C) := by
  refine ⟨isCompact_Icc.diff hC, ?_⟩
  have hfinite : volume (C ∩ Icc (0 : ℝ) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hdiff : Icc (0 : ℝ) 1 \ C =
      Icc (0 : ℝ) 1 \ (C ∩ Icc (0 : ℝ) 1) := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hdiff, measure_sdiff inter_subset_right
    (hC.measurableSet.inter measurableSet_Icc).nullMeasurableSet hfinite,
    Real.volume_Icc]
  norm_num only [sub_zero, ENNReal.ofReal_one]
  have hstrict : ENNReal.ofReal (1 - η) < ENNReal.ofReal (1 - η / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  refine hstrict.trans_le ?_
  rw [ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one]
  exact tsub_le_tsub_left hsmall 1

/-- Every positive scale can be moved into `[1,2]` by a natural power
of two followed by passage to a dyadic tail. -/
theorem positive_scale_normalization {s : ℝ} (hs : 0 < s) :
    ∃ j m : ℕ, (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) ∈ Icc (1 : ℝ) 2 := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / s) (by norm_num : (1 : ℝ) < 2)
  have hlarge : 1 ≤ s * (2 : ℝ) ^ j := by
    have := (div_lt_iff₀ hs).mp hj
    nlinarith
  obtain ⟨m, hm₀, hm₁⟩ := exists_nat_pow_near hlarge (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, m, ?_, ?_⟩
  · rw [inv_pow]
    exact (le_mul_inv_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).mpr (by simpa using hm₀)
  · rw [inv_pow]
    apply (mul_inv_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).mpr
    rw [pow_succ] at hm₁
    nlinarith

/-- The paired pullbacks used to cover all signed scales. -/
def signedDyadicUnion (H : ℕ → Set ℝ) : Set ℝ :=
  ⋃ j : ℕ, ({x : ℝ | (2 : ℝ) ^ j * x ∈ H j} ∪
    {x : ℝ | -((2 : ℝ) ^ j * x) ∈ H j})

theorem signedDyadicUnion_open {H : ℕ → Set ℝ} (hH : ∀ j, IsOpen (H j)) :
    IsOpen (signedDyadicUnion H) := by
  apply isOpen_iUnion
  intro j
  exact ((hH j).preimage (continuous_const.mul continuous_id)).union
    ((hH j).preimage (continuous_const.mul continuous_id).neg)

theorem signedDyadicUnion_neg {H : ℕ → Set ℝ} {x : ℝ}
    (hx : x ∈ signedDyadicUnion H) : -x ∈ signedDyadicUnion H := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  rcases hj with hj | hj
  · right
    simpa only [mem_ofPred_eq, mul_neg, neg_neg] using hj
  · left
    simpa only [mem_ofPred_eq, mul_neg] using hj

/-- The full signed-scale hitting property is a purely algebraic consequence
of a normalized hitting set at every dyadic magnification. -/
theorem signedDyadicUnion_hits {H : ℕ → Set ℝ}
    (hH : ∀ j (x t : ℝ), t ∈ Icc (1 : ℝ) 2 →
      ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H j) :
    ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
      x + s * ((2 : ℝ)⁻¹ ^ n) ∈ signedDyadicUnion H := by
  have hpos : ∀ x s : ℝ, 0 < s → ∃ n : ℕ, 1 ≤ n ∧
      x + s * ((2 : ℝ)⁻¹ ^ n) ∈ signedDyadicUnion H := by
    intro x s hs
    obtain ⟨j, m, hscale⟩ := positive_scale_normalization hs
    obtain ⟨n, hn, hhit⟩ := hH j ((2 : ℝ) ^ j * x)
      (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) hscale
    refine ⟨m + n, by omega, mem_iUnion.mpr ⟨j, Or.inl ?_⟩⟩
    change (2 : ℝ) ^ j * (x + s * ((2 : ℝ)⁻¹ ^ (m + n))) ∈ H j
    have heq : (2 : ℝ) ^ j * (x + s * ((2 : ℝ)⁻¹ ^ (m + n))) =
        (2 : ℝ) ^ j * x +
          (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) * ((2 : ℝ)⁻¹ ^ n) := by
      rw [pow_add]
      ring
    rwa [heq]
  intro x s hs
  rcases lt_or_gt_of_ne hs with hs | hs
  · obtain ⟨n, hn, hhit⟩ := hpos (-x) (-s) (neg_pos.mpr hs)
    refine ⟨n, hn, ?_⟩
    have := signedDyadicUnion_neg hhit
    simpa only [neg_add, neg_neg, neg_mul] using this
  · exact hpos x s hs

/-- The cost of pairing and summing the dyadic pullbacks is at most
 twice the sum of the original period densities. -/
theorem signedDyadicUnion_volume_le {H : ℕ → Set ℝ}
    (hH : ∀ j, ∀ x : ℝ, x + 1 ∈ H j ↔ x ∈ H j) :
    volume (signedDyadicUnion H ∩ Icc (0 : ℝ) 1) ≤
      ∑' j : ℕ, 2 * volume (H j ∩ Icc (0 : ℝ) 1) := by
  rw [signedDyadicUnion, iUnion_inter]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
  rw [union_inter_distrib_right, two_mul]
  refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      periodic_dilate_unit_volume_le (hH j) (n := 2 ^ j) (by positivity)
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      periodic_neg_dilate_unit_volume_le (hH j) (n := 2 ^ j) (by positivity)

theorem dyadic_density_budget {η : ℝ} (hη : 0 ≤ η) :
    (∑' j : ℕ, (2 : ENNReal) *
      ENNReal.ofReal (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j)))) =
        ENNReal.ofReal (η / 2) := by
  have hterm (j : ℕ) : (2 : ENNReal) *
      ENNReal.ofReal (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j))) =
        ENNReal.ofReal (η / 4) * ((2 : ENNReal)⁻¹ ^ j) := by
    calc
      (2 : ENNReal) * ENNReal.ofReal (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j))) =
          ENNReal.ofReal (2 * (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j)))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ = ENNReal.ofReal (η / 4 * ((2 : ℝ)⁻¹ ^ j)) := by
        congr 1
        ring
      _ = ENNReal.ofReal (η / 4) * ((2 : ENNReal)⁻¹ ^ j) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
  calc
    ENNReal.ofReal (η / 4) * 2 = ENNReal.ofReal ((η / 4) * 2) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num
    _ = ENNReal.ofReal (η / 2) := by congr 1; ring

/-- The global compact avoidance theorem follows from the periodic hitting
lemma. All measure estimates, signed scales, and strict volume loss are
included in this implication. -/
theorem avoidance_of_periodic_hitting
    (hperiodic : ∀ p : ℝ, 0 < p → p < 1 → ∃ H : Set ℝ,
      IsOpen H ∧ (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧
        x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H) :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      E ⊆ Icc (0 : ℝ) 1 ∧ IsCompact E ∧
      volume E > ENNReal.ofReal (1 - η) ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
        x + s * ((2 : ℝ)⁻¹ ^ n) ∉ E := by
  intro η hη hη1
  let p : ℕ → ℝ := fun j => η / 48 * ((2 : ℝ)⁻¹ ^ j)
  have hp₀ (j : ℕ) : 0 < p j := by dsimp [p]; positivity
  have hp₁ (j : ℕ) : p j < 1 := by
    have hpow : (2 : ℝ)⁻¹ ^ j ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hcoef : 0 ≤ η / 48 := by positivity
    have hp_le : p j ≤ η / 48 := by
      dsimp [p]
      exact mul_le_of_le_one_right hcoef hpow
    linarith
  choose H hOpen hPer hDensity hHit using fun j => hperiodic (p j) (hp₀ j) (hp₁ j)
  have hsmall : volume (signedDyadicUnion H ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (η / 2) := by
    refine (signedDyadicUnion_volume_le hPer).trans ?_
    calc
      (∑' j : ℕ, (2 : ENNReal) * volume (H j ∩ Icc (0 : ℝ) 1)) ≤
          ∑' j : ℕ, (2 : ENNReal) * ENNReal.ofReal (6 * p j) :=
        ENNReal.tsum_le_tsum fun j => mul_le_mul_right (hDensity j) 2
      _ = ENNReal.ofReal (η / 2) := dyadic_density_budget hη.le
  have hcompact := compact_complement_volume (signedDyadicUnion_open hOpen) hη hη1 hsmall
  refine ⟨Icc (0 : ℝ) 1 \ signedDyadicUnion H, sdiff_subset, hcompact.1, hcompact.2, ?_⟩
  intro x s hs
  obtain ⟨n, hn, hhit⟩ := signedDyadicUnion_hits hHit x s hs
  exact ⟨n, hn, fun hx => hx.2 hhit⟩

end Problem310Support

end

end OAI

end

-- OpenAI source module: ExpectedRepair
section

namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set Filter Topology MeasureTheory

/-- First-moment selection followed by deterministic open-neighborhood repair. -/
theorem periodic_hitting_of_expected_exceptional
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBo : ∀ ω, IsOpen (B ω))
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal (2 * p))
    (hRmean : (∫⁻ ω, volume
      (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1) ∂μ)
        ≤ ENNReal.ofReal (3 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  let f : Ω → ENNReal := fun ω => volume (B ω ∩ Icc (0 : ℝ) 1)
  let g : Ω → ENNReal := fun ω => volume
    (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1)
  have hf : Measurable f := measurable_of_countable f
  have hg : Measurable g := measurable_of_countable g
  obtain ⟨ω, hω⟩ := exists_le_lintegral (μ := μ) (hf.add hg).aemeasurable
  apply periodic_hitting_of_small_exceptional p hp (B ω) (hBo ω) (hBp ω) N hN
  calc
    f ω + g ω ≤ ∫⁻ ω, f ω + g ω ∂μ := hω
    _ = (∫⁻ ω, f ω ∂μ) + ∫⁻ ω, g ω ∂μ := lintegral_add_left hf _
    _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal (3 * p) := add_le_add hBmean hRmean
    _ = ENNReal.ofReal (5 * p) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Full analytic repair interface from pointwise failure probabilities on stable centers. -/
theorem periodic_hitting_of_pointwise_failure_bound
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBo : ∀ ω, IsOpen (B ω))
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal (2 * p))
    (hgood : ∀ x ∈ G,
      μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  apply periodic_hitting_of_expected_exceptional μ p hp B hBo hBp N hN hBmean
  have hRm : ∀ ω, MeasurableSet
      (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)) :=
    fun ω => (isClosed_exceptionalCenters (B ω) (hBo ω) N _).measurableSet
  calc
    (∫⁻ ω, volume
        (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1) ∂μ)
        ≤ ENNReal.ofReal (2 * p) + volume (Gᶜ ∩ Icc (0 : ℝ) 1) :=
      expected_density_le_of_pointwise_bound μ _ hRm G hG _ hgood
    _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal p := add_le_add le_rfl hbad
    _ = ENNReal.ofReal (3 * p) := by
      rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hp)]
      congr 1
      ring

end Problem310.Auxiliary

end

end OAI

end

-- OpenAI source module: RandomSetDensity
section

namespace OAI

universe u_A u_K

noncomputable section

open MeasureTheory

namespace Problem310.RandomSetDensity

/-- A selector outcome chooses the terminal address read at each point. -/
def selectedSet {A : Type u_A} {K : Type u_K} (addr : A → ℝ → K) (z : A × (K → Bool)) : Set ℝ :=
  {x | z.2 (addr z.1 x) = true}

/-- Finite terminal tables preserve spatial measurability of the address map. -/
theorem measurableSet_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (addr : A → ℝ → K) (haddr : ∀ a, Measurable (addr a))
    (z : A × (K → Bool)) : MeasurableSet (selectedSet addr z) := by
  exact ((measurable_of_countable z.2).comp (haddr z.1)) (measurableSet_singleton true)

/-- Periodicity of terminal addresses gives periodicity of every realization. -/
theorem periodic_selectedSet
    {A : Type u_A} {K : Type u_K} (addr : A → ℝ → K)
    (haddr : ∀ a x, addr a (x + 1) = addr a x) (z : A × (K → Bool)) :
    ∀ x : ℝ, x + 1 ∈ selectedSet addr z ↔ x ∈ selectedSet addr z := by
  intro x
  simp only [selectedSet, Set.mem_ofPred_eq, haddr]

/-- Independence of terminal labels from selectors gives the same membership
probability at every spatial point, even with adaptively selected addresses. -/
theorem pointwise_probability_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype K] (P : Measure A) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → ℝ → K) (x : ℝ) :
    (P.prod (Measure.pi (fun _ : K => ν))) {z | x ∈ selectedSet addr z} =
      ν {true} := by
  classical
  have hmeas : MeasurableSet {z : A × (K → Bool) | x ∈ selectedSet addr z} :=
    (Set.toFinite _).measurableSet
  rw [Measure.prod_apply hmeas]
  have hsection (a : A) :
      (Measure.pi (fun _ : K => ν)) {ω : K → Bool | ω (addr a x) = true} = ν {true} := by
    exact (measurePreserving_eval (fun _ : K => ν) (addr a x)).measure_preimage
      (measurableSet_singleton true).nullMeasurableSet
  change (∫⁻ a, (Measure.pi (fun _ : K => ν))
    {ω : K → Bool | ω (addr a x) = true} ∂P) = ν {true}
  simp only [hsection]
  simp

/-- Exact first-moment density identity for the random routed set. -/
theorem expected_density_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (P : Measure A) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → ℝ → K) (haddr : ∀ a, Measurable (addr a)) :
    (∫⁻ z, volume (selectedSet addr z ∩ Set.Icc (0 : ℝ) 1)
      ∂(P.prod (Measure.pi (fun _ : K => ν)))) = ν {true} := by
  classical
  rw [Problem310.Auxiliary.expected_density_eq_pointwise_probability
    (P.prod (Measure.pi (fun _ : K => ν))) (selectedSet addr)
    (measurableSet_selectedSet addr haddr)]
  simp only [pointwise_probability_selectedSet P ν addr]
  simp

end Problem310.RandomSetDensity

end

end OAI

end

-- OpenAI source module: GridStability
section

namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

/-- Simultaneous stable centers for a finite list of earlier-grid/later-window pairs. -/
def gridStableCenters {ι : Type u_ι} (a b : ι → ℕ) : Set ℝ :=
  (⋃ i, gridBadCenters ((2 : ℕ) ^ (b i + 2)) (2 * ((2 : ℝ)⁻¹) ^ (a i)))ᶜ

theorem measurableSet_gridStableCenters {ι : Type u_ι} [Countable ι] (a b : ι → ℕ) :
    MeasurableSet (gridStableCenters a b) := by
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_gridBadCenters _ _

theorem gridStableCenters_add_one {ι : Type u_ι} (a b : ι → ℕ) (x : ℝ) :
    x + 1 ∈ gridStableCenters a b ↔ x ∈ gridStableCenters a b := by
  simp only [gridStableCenters, mem_compl_iff, mem_iUnion, not_exists]
  apply forall_congr'
  intro i
  exact not_congr (gridBadCenters_add_one _ (by positivity) _ _)

/-- Stability at a grid also preserves every coarser grid at a later-window trial. -/
theorem gridStableCenters_preserves {ι : Type u_ι} {a b : ι → ℕ} {x t : ℝ}
    (hx : x ∈ gridStableCenters a b) (i : ι) {c n : ℕ}
    (hc : c ≤ b i) (hn : a i ≤ n) (ht : t ∈ Icc (1 : ℝ) 2) :
    dyadicGridKey c (x + t * ((2 : ℝ)⁻¹) ^ n) = dyadicGridKey c x := by
  have hxnot : x ∉ gridBadCenters ((2 : ℕ) ^ (b i + 2))
      (2 * ((2 : ℝ)⁻¹) ^ (a i)) := by
    intro hi
    exact hx (mem_iUnion.mpr ⟨i, hi⟩)
  have hkey := dyadicGridKey_eq_of_stable hn ht (fun k hk ↦ by
    apply hxnot
    apply (mem_gridBadCenters_iff _ _ _).mpr
    exact ⟨k, by simpa using hk⟩)
  rw [← dyadicGridKey_nested hc, ← dyadicGridKey_nested hc, hkey]

private theorem grid_window_width_le {a b : ℕ} (hgap : b + 3 ≤ a) :
    2 * ((2 : ℝ)⁻¹) ^ a ≤ (((2 : ℕ) ^ (b + 2) : ℕ) : ℝ)⁻¹ := by
  have h := pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hgap
  change (2 : ℝ)⁻¹ ^ a ≤ (2 : ℝ)⁻¹ ^ (b + 3) at h
  have hp : ((2 : ℝ)⁻¹) ^ (b + 3) = ((2 : ℝ)⁻¹) ^ (b + 2) * 2⁻¹ := by
    rw [show b + 3 = (b + 2) + 1 by omega, pow_succ]
  rw [hp] at h
  have h2 : 2 * ((2 : ℝ)⁻¹) ^ a ≤ ((2 : ℝ)⁻¹) ^ (b + 2) := by
    norm_num at h ⊢
    linarith
  simpa only [Nat.cast_pow, Nat.cast_ofNat, inv_pow] using h2

/-- A quantitative simultaneous stability estimate, with no tree assumptions. -/
theorem volume_gridStableCenters_compl_period_le {ι : Type u_ι} [Fintype ι]
    (a b : ι → ℕ) (hgap : ∀ i, b i + 3 ≤ a i) :
    volume ((gridStableCenters a b)ᶜ ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (∑ i, (2 : ℝ) ^ (b i + 2) * (2 * ((2 : ℝ)⁻¹) ^ (a i))) := by
  simp only [gridStableCenters, compl_compl]
  simpa using volume_iUnion_gridBadCenters_period_le
    (fun i ↦ (2 : ℕ) ^ (b i + 2)) (fun i ↦ 2 * ((2 : ℝ)⁻¹) ^ (a i))
    (fun i ↦ by positivity) (fun i ↦ by positivity)
    (fun i ↦ grid_window_width_le (hgap i))

/-- The density cost of a gap depends only on its length, not on the grid resolution. -/
theorem dyadic_grid_gap_budget (b g : ℕ) :
    (2 : ℝ) ^ (b + 2) * (2 * ((2 : ℝ)⁻¹) ^ (b + g + 1)) =
      4 * ((2 : ℝ)⁻¹) ^ g := by
  have hcancel : (2 : ℝ) ^ b * ((2 : ℝ)⁻¹) ^ b = 1 := by
    rw [inv_pow]
    exact mul_inv_cancel₀ (by positivity)
  calc
    (2 : ℝ) ^ (b + 2) * (2 * ((2 : ℝ)⁻¹) ^ (b + g + 1))
      = 4 * ((2 : ℝ) ^ b * ((2 : ℝ)⁻¹) ^ b) * ((2 : ℝ)⁻¹) ^ g := by
        simp only [pow_add, pow_one]
        norm_num
        ring
    _ = 4 * ((2 : ℝ)⁻¹) ^ g := by rw [hcancel]; ring

theorem volume_gridStableCenters_compl_gap_le {ι : Type u_ι} [Fintype ι]
    (a b : ι → ℕ) (g : ℕ) (hg : 2 ≤ g)
    (ha : ∀ i, a i = b i + g + 1) :
    volume ((gridStableCenters a b)ᶜ ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g)) := by
  have h := volume_gridStableCenters_compl_period_le a b (fun i ↦ by rw [ha i]; omega)
  have heq : (∑ i, (2 : ℝ) ^ (b i + 2) * (2 * ((2 : ℝ)⁻¹) ^ (a i))) =
      (Fintype.card ι : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g) := by
    simp only [ha, dyadic_grid_gap_budget, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rwa [heq] at h

/-- Any prescribed finite number of stability conditions has arbitrarily small
exceptional density once the unused gap is sufficiently long. -/
theorem exists_dyadic_gap_budget (K : ℕ) {p : ℝ} (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ (K : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g) < p := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < p / (4 * (K + 1 : ℝ)) by positivity)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨n + 2, by omega, ?_⟩
  have hpow := pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1) (show n ≤ n + 2 by omega)
  change (2 : ℝ)⁻¹ ^ (n + 2) ≤ (2 : ℝ)⁻¹ ^ n at hpow
  have hden : 0 < 4 * (K + 1 : ℝ) := by positivity
  have hlt := (lt_div_iff₀ hden).mp hn
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hnonneg : 0 ≤ ((2 : ℝ)⁻¹) ^ (n + 2) := by positivity
  nlinarith

end Problem310

end

end OAI

end

-- OpenAI source module: RoutingBudget
section

namespace OAI

noncomputable section

namespace Problem310.RoutingBudget

/-- Transfer a real finite-union estimate to the extended-nonnegative probability scale. -/
lemma ennreal_card_mul_pow_lt {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q)
    (N k : ℕ) (h : (N : ℝ) * q ^ k < p) :
    (N : ENNReal) * (ENNReal.ofReal q) ^ k < ENNReal.ofReal p := by
  have he := (ENNReal.ofReal_lt_ofReal_iff hp).2 h
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow hq] using he

/-- Choose parameters in the router convention: `M` is the number of nondefault
children, so there are `M + 1` children altogether. The last estimate is ready for
an `ENNReal` finite union bound over the monotone-key representatives. -/
theorem exists_nondefault_parameters (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ M d R : ℕ, 1 ≤ M ∧ 1 ≤ d ∧ 1 ≤ R ∧
      10 ≤ p * (M : ℝ) / 2 ∧
      (1 - ((2 : ℝ)⁻¹) ^ M) ^ d < p ∧
      ∀ r : ℕ, R ≤ r → ∀ N : ℕ,
        N ≤ 1 + M * r * 2 ^ (2 * r + 2) →
        (N : ENNReal) * (ENNReal.ofReal (1 - p / 2)) ^ (M * r) <
          ENNReal.ofReal p := by
  obtain ⟨T, d, hT, hd, hmargin, hdepth⟩ :=
    WindowBudget.exists_tree_parameters p hp
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  obtain ⟨R, hR, hsmall⟩ :=
    WindowBudget.exists_probability_threshold p hp hp1 (M + 1) hT hmargin
  have hM : 1 ≤ M := by omega
  have hmargin' : 10 ≤ p * (M : ℝ) / 2 := by
    simpa only [Nat.cast_succ, add_sub_cancel_right] using hmargin
  simp only [Nat.add_sub_cancel] at hdepth hsmall
  refine ⟨M, d, R, hM, hd, hR, hmargin', hdepth, ?_⟩
  intro r hr N hN
  have hrpos : 1 ≤ r := hR.trans hr
  have hcard := ScaleDiscretization.representative_card_budget
    (M + 1) r (2 ^ (2 * r + 2)) (by omega) hrpos
  simp only [Nat.add_sub_cancel] at hcard
  have hNbig : N ≤ 20 * (M + 1) * r * (1 + 2 ^ (2 * r + 2)) :=
    hN.trans hcard
  have hNreal : (N : ℝ) ≤ 20 * ((M + 1 : ℕ) : ℝ) * (r : ℝ) *
      (1 + (2 : ℝ) ^ (2 * r + 2)) := by
    exact_mod_cast hNbig
  apply ennreal_card_mul_pow_lt hp (by linarith) N (M * r)
  exact (mul_le_mul_of_nonneg_right hNreal (pow_nonneg (by linarith) _)).trans_lt
    (hsmall r hr)

/-- The real survival estimate has exactly the expected truncated-subtraction
form for the product probability measure. -/
lemma ennreal_survival_lt {p : ℝ} (hp : 0 < p) (M d : ℕ)
    (h : (1 - ((2 : ℝ)⁻¹) ^ M) ^ d < p) :
    (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d < ENNReal.ofReal p := by
  have hbase0 : 0 ≤ 1 - ((2 : ℝ)⁻¹) ^ M := by
    have hpow : ((2 : ℝ)⁻¹) ^ M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hbase : ENNReal.ofReal (1 - ((2 : ℝ)⁻¹) ^ M) =
      1 - ((2 : ENNReal)⁻¹) ^ M := by
    rw [ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have he := (ENNReal.ofReal_lt_ofReal_iff hp).2 h
  rwa [ENNReal.ofReal_pow hbase0, hbase] at he

end Problem310.RoutingBudget

end

end OAI

end

-- OpenAI source module: DyadicRoutedAddresses
section

namespace OAI

universe u_I u_A u_L

noncomputable section

namespace Problem310.AddressInjectivity

end Problem310.AddressInjectivity

end

end OAI

end

-- OpenAI source module: WindowTableModel
section

namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

variable {M d g r₀ : ℕ}

/-- The nondefault child edge used by a selector table. -/
def selectorEdge (P : Node M d) (i : Fin M) : List (Child M) :=
  P.val ++ [i.castSucc]

lemma selectorEdge_valid (P : Node M d) (i : Fin M) :
    ValidWindowEdge d (selectorEdge P i) := by
  constructor
  · simp [selectorEdge]
  · have hP := P.property
    simp only [selectorEdge, List.length_append, List.length_singleton]
    omega

lemma leaf_valid (hd : 0 < d) (L : Leaf M d) : ValidWindowEdge d L.val := by
  constructor
  · intro h
    have hL := L.property
    rw [h] at hL
    simp only [List.length_nil] at hL
    omega
  · exact le_of_eq L.property

/-- Canonical selector resolutions are the incoming window endpoints. -/
def selectorEndpoints (W : WindowData (M + 1) d g r₀) : Node M d → Fin M → ℕ :=
  fun P i => W.b (selectorEdge P i)

/-- Each terminal table uses its leaf's incoming-edge endpoint. -/
def terminalEndpoints (W : WindowData (M + 1) d g r₀) : Leaf M d → ℕ :=
  fun L => W.b L.val

lemma incoming_le_terminalEndpoints
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) (L : Leaf M d)
    (hprefix : (selectorEdge P i).IsPrefix L.val) :
    selectorEndpoints W P i ≤ terminalEndpoints W L := by
  have hd : 0 < d := by have := P.property; omega
  exact (W.descendant_bounds (selectorEdge P i) L.val
    (selectorEdge_valid P i) (leaf_valid hd L) hprefix).1

lemma selector_window_endpoint
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) :
    selectorEndpoints W P i + 1 = W.a (selectorEdge P i) + W.r (d - P.val.length) := by
  have h := W.endpoint (selectorEdge P i) (selectorEdge_valid P i)
  simpa [selectorEndpoints, selectorEdge] using h

end Problem310.FiniteTableModel

end

end OAI

end

-- OpenAI source module: CenterRouteExposure
section

namespace OAI

universe u_ι u_X u_Y

noncomputable section

namespace Problem310.CenterRouteExposure
open Problem310.RoutingPath

/-- Equality of all node decisions at two samples identifies their entire routes,
even when the two decision functions have different parameter spaces. -/
theorem routeFrom_congr_at {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (n : ℕ) (P : List ι) :
    routeFrom chooseX n P x = routeFrom chooseY n P y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [routeFrom_succ, ih, h]

/-- The decision at every stage is also fixed by the node-decision data. -/
theorem route_decision_congr_at {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (n : ℕ) (P : List ι) :
    chooseX (routeFrom chooseX n P x) x =
      chooseY (routeFrom chooseY n P y) y := by
  rw [routeFrom_congr_at chooseX chooseY x y h]
  exact h _

/-- The event that the first default occurs at a specified stage. -/
def FirstDefaultAt {ι : Type u_ι} {X : Type u_X} (choose : List ι → X → ι)
    (default : ι) (d k : ℕ) (P : List ι) (x : X) : Prop :=
  k < d ∧ choose (routeFrom choose k P x) x = default ∧
    ∀ l < k, choose (routeFrom choose l P x) x ≠ default

/-- Full center exposure fixes whether a given stage is the first default. -/
theorem firstDefaultAt_congr {ι : Type u_ι} {X : Type u_X} {Y : Type u_Y}
    (chooseX : List ι → X → ι) (chooseY : List ι → Y → ι)
    (x : X) (y : Y) (h : ∀ P, chooseX P x = chooseY P y)
    (default : ι) (d k : ℕ) (P : List ι) :
    FirstDefaultAt chooseX default d k P x ↔
      FirstDefaultAt chooseY default d k P y := by
  simp only [FirstDefaultAt, route_decision_congr_at chooseX chooseY x y h]

open Problem310.FiniteTableModel Problem310.OrderedRouting

/-- The full deterministic center exposure: one bit for every selector table. -/
def centerExposure {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (ω : SelectorTable b) : Node M d × Fin M → Bool :=
  fun e => ω (selectorAddress b e.1 e.2 x)

/-- Complete any exposure assignment by setting all unexposed bits to false.
This is only a deterministic representative of an atom, not a probability law. -/
def centerCompletion {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool) : SelectorTable b :=
  Function.extend (fun e : Node M d × Fin M => selectorAddress b e.1 e.2 x)
    ξ (fun _ => false)

@[simp] theorem centerExposure_completion {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool) :
    centerExposure b x (centerCompletion b x ξ) = ξ := by
  funext e
  exact (center_selectorAddress_injective b x).extend_apply ξ (fun _ => false) e

/-- Even the extended selector function is fixed by center exposure: invalid
nodes use the same constant false value in both outcomes. -/
theorem selectorValue_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (P : List (Child M)) (i : Fin M) :
    selectorValue b ω P i x = selectorValue b ω' P i x := by
  by_cases hP : P.length < d
  · have he := congrFun h (⟨P, hP⟩, i)
    simpa only [centerExposure, selectorValue, dif_pos hP] using he
  · simp only [selectorValue, dif_neg hP]

/-- The actual first-success choice made by a selector table at a fixed center. -/
def centerChoice {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (P : List (Child M)) (ω : SelectorTable b) : Child M :=
  chooseChild (fun i => selectorValue b ω P i x)

theorem centerChoice_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω') (P : List (Child M)) :
    centerChoice b x P ω = centerChoice b x P ω' := by
  exact chooseChild_congr _ _ (selectorValue_eq_of_centerExposure_eq b x h P)

/-- Every center route is constant on each full exposure atom. -/
theorem centerRoute_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (n : ℕ) (P : List (Child M)) :
    routeFrom (centerChoice b x) n P ω = routeFrom (centerChoice b x) n P ω' :=
  routeFrom_congr_at _ _ ω ω' (centerChoice_eq_of_centerExposure_eq b x h) n P

/-- The decision made at every center-route stage is constant on the atom. -/
theorem centerRoute_decision_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω')
    (n : ℕ) (P : List (Child M)) :
    centerChoice b x (routeFrom (centerChoice b x) n P ω) ω =
      centerChoice b x (routeFrom (centerChoice b x) n P ω') ω' :=
  route_decision_congr_at _ _ ω ω' (centerChoice_eq_of_centerExposure_eq b x h) n P

/-- A good exposure atom has one fixed first-default stage and node, uniformly
for every completion of all unexposed selector coordinates. -/
theorem firstDefaultData_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : ∃ k < d, centerChoice b x
      (routeFrom (centerChoice b x) k [] (centerCompletion b x ξ))
        (centerCompletion b x ξ) = Fin.last M) :
    ∃ k : ℕ, ∃ U : List (Child M), k < d ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (centerChoice b x) k [] ω = U ∧
        FirstDefaultAt (centerChoice b x) (Fin.last M) d k [] ω := by
  obtain ⟨k, hk, hdefault, hprior⟩ :=
    exists_first_default (centerChoice b x) d [] (centerCompletion b x ξ) (Fin.last M) hgood
  refine ⟨k, routeFrom (centerChoice b x) k [] (centerCompletion b x ξ), hk, ?_⟩
  intro ω hω
  have he : centerExposure b x ω = centerExposure b x (centerCompletion b x ξ) := by
    simpa only [centerExposure_completion] using hω
  refine ⟨centerRoute_eq_of_centerExposure_eq b x he k [], ?_⟩
  apply (firstDefaultAt_congr _ _ ω (centerCompletion b x ξ)
    (centerChoice_eq_of_centerExposure_eq b x he) (Fin.last M) d k []).mpr
  exact ⟨hk, hdefault, hprior⟩

/-- Version of the atomwise first-default witness with the actual bounded node
and stage types required to index the finite selector tables and window data. -/
theorem firstDefaultNode_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : ∃ k < d, centerChoice b x
      (routeFrom (centerChoice b x) k [] (centerCompletion b x ξ))
        (centerCompletion b x ξ) = Fin.last M) :
    ∃ k : Fin d, ∃ U : Node M d, U.val.length = k.val ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (centerChoice b x) k.val [] ω = U.val ∧
        FirstDefaultAt (centerChoice b x) (Fin.last M) d k.val [] ω := by
  obtain ⟨k, U, hk, hU⟩ := firstDefaultData_on_atom b x ξ hgood
  have hroute := (hU (centerCompletion b x ξ) (centerExposure_completion b x ξ)).1
  have hlen : U.length = k := by
    rw [← hroute, length_routeFrom]
    simp
  exact ⟨⟨k, hk⟩, ⟨U, by simpa only [hlen] using hk⟩, hlen, hU⟩

/-- The good atoms are those whose (equivalently, every) center route has a default. -/
def GoodExposure {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool) : Prop :=
  ∃ k < d, centerChoice b x
    (routeFrom (centerChoice b x) k [] (centerCompletion b x ξ))
      (centerCompletion b x ξ) = Fin.last M

/-- The finite-atom good predicate is exactly the actual center-path default event. -/
theorem goodExposure_centerExposure_iff {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ω : SelectorTable b) :
    GoodExposure b x (centerExposure b x ω) ↔
      ∃ k < d, centerChoice b x (routeFrom (centerChoice b x) k [] ω) ω = Fin.last M := by
  have he : centerExposure b x ω = centerExposure b x
      (centerCompletion b x (centerExposure b x ω)) := by simp
  constructor
  · rintro ⟨k, hk, hd⟩
    exact ⟨k, hk, (centerRoute_decision_eq_of_centerExposure_eq b x he k []).trans hd⟩
  · rintro ⟨k, hk, hd⟩
    exact ⟨k, hk, (centerRoute_decision_eq_of_centerExposure_eq b x he k []).symm.trans hd⟩

/-- This is the event identity used to transport the no-default probability
estimate to the bad atoms of the full center-exposure partition. -/
theorem badExposure_centerExposure_iff {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ω : SelectorTable b) :
    ¬ GoodExposure b x (centerExposure b x ω) ↔
      ∀ k < d, centerChoice b x (routeFrom (centerChoice b x) k [] ω) ω ≠ Fin.last M := by
  rw [goodExposure_centerExposure_iff]
  simp only [not_exists, not_and, ne_eq]

end Problem310.CenterRouteExposure

end

end OAI

end

-- OpenAI source module: CenterFirstDefault
section

namespace OAI

universe u_T

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem310.FiniteTableModel

/-- Center-table coordinate in the bounded-address convention used by the
first-default probability theorem. -/
def centerTableAddress {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (a : FirstDefault.BoundedAddress M d) : SelectorAddress b :=
  selectorAddress b ⟨a.1.1, a.2⟩ a.1.2 x

lemma centerTableAddress_injective {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ) :
    Function.Injective (centerTableAddress b x) := by
  intro a c h
  have hp := congrArg Sigma.fst h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Node M d × Fin M => z.1.val) hp
  · exact congrArg (fun z : Node M d × Fin M => z.2) hp

/-- Exact no-default probability for the canonical spatial selector tables,
at every real center and every choice of deterministic grid resolutions. -/
theorem measure_center_no_default {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ bit, ν {bit} = (2 : ENNReal)⁻¹) (x : ℝ) :
    (Measure.pi (fun _ : SelectorAddress b => ν))
      (⋃ f : FirstDefault.Path M d, {ω | ∀ i : FirstDefault.Tests f,
        selectorValue b ω (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  have h := FirstDefault.measure_no_default_finite_table ν hfair
    (centerTableAddress b x) (centerTableAddress_injective b x)
  simpa only [centerTableAddress, FirstDefault.boundedAddress,
    selectorValue, dif_pos (FirstDefault.address_length_lt _ _)] using h

/-- Adding the independent terminal tables does not change the center-path
survival probability. This is the full outcome-space form used by repair. -/
theorem measure_center_no_default_prod {M d : ℕ}
    {T : Type u_T} [MeasurableSpace T] (τ : Measure T) [IsProbabilityMeasure τ]
    (b : Node M d → Fin M → ℕ)
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ bit, ν {bit} = (2 : ENNReal)⁻¹) (x : ℝ) :
    ((Measure.pi (fun _ : SelectorAddress b => ν)).prod τ)
      (⋃ f : FirstDefault.Path M d, {ω : SelectorTable b × T |
        ∀ i : FirstDefault.Tests f,
        selectorValue b ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  let E : Set (SelectorTable b) := ⋃ f : FirstDefault.Path M d,
    {ω | ∀ i : FirstDefault.Tests f,
      selectorValue b ω (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
        FirstDefault.requiredBit f i}
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  have heq : (⋃ f : FirstDefault.Path M d, {ω : SelectorTable b × T |
        ∀ i : FirstDefault.Tests f,
        selectorValue b ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) = Prod.fst ⁻¹' E := by
    ext ω
    simp only [E, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [heq, measurePreserving_fst.measure_preimage hE.nullMeasurableSet]
  exact measure_center_no_default b ν hfair x

/-- The survival estimate with all probability measures instantiated, including
the Bernoulli terminal labels in the canonical complete outcome space. -/
theorem outcomeLaw_center_no_default {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      (⋃ f : FirstDefault.Path M d, {ω : SelectorTable bS × TerminalTable bT |
        ∀ i : FirstDefault.Tests f,
        selectorValue bS ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  exact measure_center_no_default_prod
    (ConcreteLabels.terminalLaw (TerminalAddress bT) p hp0 hp1)
    bS ConcreteLabels.fairLaw ConcreteLabels.fairLaw_singleton x

end Problem310.FiniteTableModel

end

end OAI

end

-- OpenAI source module: WindowLocalHit
section

namespace OAI

universe u_X

noncomputable section

namespace Problem310.WindowLocalHit

open RoutingPath StableRouting GridSeparation

variable {q d g r₀ : ℕ} {X : Type u_X}

/-- Every selector used at an earlier routed node precedes an incoming edge
below that route, provided its child index is no later than the chosen child. -/
theorem ancestor_selector_gap (W : WindowData q d g r₀)
    (choose : List (Fin q) → X → Fin q) (x : X)
    {k l : ℕ} (hkl : k < l) (hld : l < d) (i j : Fin q)
    (hj : j ≤ choose (routeFrom choose k [] x) x) :
    W.b (routeFrom choose k [] x ++ [j]) + g <
      W.a (routeFrom choose l [] x ++ [i]) := by
  have hvalid (n : ℕ) (hn : n < d) (c : Fin q) :
      ValidWindowEdge d (routeFrom choose n [] x ++ [c]) := by
    constructor
    · simp
    · simp only [List.length_append, length_routeFrom, List.length_nil,
        List.length_singleton, zero_add]
      omega
  have hpre : (routeFrom choose (k + 1) [] x).IsPrefix (routeFrom choose l [] x) := by
    have h := prefix_routeFrom choose (l - (k + 1)) (routeFrom choose (k + 1) [] x) x
    rw [← routeFrom_add, Nat.add_sub_of_le (by omega : k + 1 ≤ l)] at h
    exact h
  have hwhole : (routeFrom choose k [] x ++ [choose (routeFrom choose k [] x) x]).IsPrefix
      (routeFrom choose l [] x ++ [i]) :=
    hpre.trans (List.prefix_append _ _)
  rcases lt_or_eq_of_le hj with hj | rfl
  · obtain ⟨tail, htail⟩ := hwhole
    have heq : routeFrom choose k [] x ++ choose (routeFrom choose k [] x) x :: tail =
        routeFrom choose l [] x ++ [i] := by
      simpa only [List.append_assoc, List.singleton_append] using htail
    have hgap := W.gap_sibling (routeFrom choose k [] x) j
      (choose (routeFrom choose k [] x) x) tail hj
      (hvalid k (hkl.trans hld) j) (by rw [heq]; exact hvalid l hld i)
    rwa [heq] at hgap
  · apply W.gap_prefix _ _ (hvalid k (hkl.trans hld) _) (hvalid l hld i) hwhole
    intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_append, length_routeFrom, List.length_nil,
      List.length_singleton, zero_add] at hlen
    omega

variable {M : ℕ}

end Problem310.WindowLocalHit

end

end OAI

end

-- OpenAI source module: StableKeyRouting
section

namespace OAI

noncomputable section
namespace Problem310.StableKeyRouting

open FiniteTableModel StableRouting RoutingPath

variable {M d : ℕ}

end Problem310.StableKeyRouting

end

end OAI

end

-- OpenAI source module: FiniteLocalPredicate
section

namespace OAI

noncomputable section

namespace Problem310.FiniteLocalPredicate

open RoutingPath GridSeparation LocalPredicateFactor FiniteTableModel

variable {M d : ℕ}

/-- The leaf reached from a local child, with its ambient-depth proof retained. -/
def localLeaf (choose : List (Child M) → ℝ → Child M)
    (r : ℕ) (P : List (Child M)) (hdepth : P.length + r = d) (x : ℝ) : Leaf M d :=
  ⟨routeFrom choose r P x, (length_routeFrom choose r P x).trans hdepth⟩

/-- Table lookup at a valid node depends only on a finer common grid. -/
theorem selector_lookup_eq {b : Node M d → Fin M → ℕ} (ω : SelectorTable b)
    (Q : Node M d) (i : Fin M) {B : ℕ} (hb : b Q i ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    ω (selectorAddress b Q i x) = ω (selectorAddress b Q i y) := by
  exact table_eq_of_finest_key hb (fun k => ω ⟨(Q, i), k⟩) hxy

/-- The analogous statement for an actual dependent terminal-table address. -/
theorem terminal_lookup_eq {b : Leaf M d → ℕ} (ω : TerminalTable b)
    (L : Leaf M d) {B : ℕ} (hb : b L ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    ω (terminalAddress b L x) = ω (terminalAddress b L y) := by
  exact table_eq_of_finest_key hb (fun k => ω ⟨L, k⟩) hxy

/-- Concrete local terminal predicates in the finite table model factor through
the largest resolution in the child subtree. `rule` may be the canonical
first-success/default rule; no assumptions on that rule are needed. -/
theorem finite_local_predicate_factors
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (choose : List (Child M) → ℝ → Child M)
    (rule : List (Child M) → (Fin M → Bool) → Child M)
    (hchoose : ∀ Q x, choose Q x = rule Q (fun i => selectorValue bS ωS Q i x))
    (r : ℕ) (P : List (Child M)) (hdepth : P.length + r = d)
    (U : Node M d) (i : Fin M) (B : ℕ)
    (hbS : ∀ Q : Node M d, P.IsPrefix Q.val → ∀ j, bS Q j ≤ B)
    (hbT : ∀ L : Leaf M d, P.IsPrefix L.val → bT L ≤ B)
    (hIn : bS U i ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    (ωS (selectorAddress bS U i x) &&
      ωT (terminalAddress bT (localLeaf choose r P hdepth x) x)) =
    (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT (localLeaf choose r P hdepth y) y)) := by
  have hchoice : ∀ Q : List (Child M), P.IsPrefix Q → Q.length < P.length + r →
      ∀ u v : ℝ, ⌊(2 : ℝ) ^ (B + 2) * Int.fract u⌋ =
        ⌊(2 : ℝ) ^ (B + 2) * Int.fract v⌋ → choose Q u = choose Q v := by
    intro Q hPQ hlen u v huv
    have hQ : Q.length < d := hlen.trans_eq hdepth
    rw [hchoose Q u, hchoose Q v]
    apply congrArg (rule Q)
    funext j
    have hlook := selector_lookup_eq ωS (⟨Q, hQ⟩ : Node M d) j
      (hbS ⟨Q, hQ⟩ hPQ j) huv
    simpa only [selectorValue, dif_pos hQ] using hlook
  have hroute := route_eq_of_key_eq choose
    (fun z : ℝ => ⌊(2 : ℝ) ^ (B + 2) * Int.fract z⌋) r P hchoice hxy
  have hleaf : localLeaf choose r P hdepth x = localLeaf choose r P hdepth y :=
    Subtype.ext hroute
  have hprefix : P.IsPrefix (localLeaf choose r P hdepth y).val :=
    prefix_routeFrom choose r P y
  rw [selector_lookup_eq ωS U i hIn hxy, hleaf,
    terminal_lookup_eq ωT (localLeaf choose r P hdepth y) (hbT _ hprefix) hxy]

end Problem310.FiniteLocalPredicate

end

end OAI

end

-- OpenAI source module: FixedScaleProbability
section

namespace OAI

universe u_A u_I u_K u_C u_S u_T

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.FixedScaleProbability

/-- Exposing selector coordinates does not change the adaptive terminal-label
calculation: first restrict the selector measure, then integrate out terminals. -/
theorem measure_exposed_adaptive_failures_eq_lintegral
    {A : Type u_A} {I : Type u_I} {K : Type u_K} [MeasurableSpace A] [Fintype I] [Fintype K]
    (μ : Measure A) [SFinite μ] (ν : Measure Bool) [IsProbabilityMeasure ν]
    (E : Set A) (addr : A → I → K)
    (hinj : ∀ a, Function.Injective (addr a))
    (active : A → I → Prop) [∀ a i, Decidable (active a i)]
    (hmeas : MeasurableSet {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → Bool) | z.1 ∈ E ∧
        ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      ∫⁻ a in E, (ν {false}) ^ (Finset.univ.filter (active a)).card ∂μ := by
  have h := AdaptiveLabels.measure_adaptive_failures (μ.restrict E) ν
    addr hinj active hmeas
  rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply hmeas] at h
  convert h using 1
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod,
    Set.mem_univ, and_true]
  exact and_comm

/-- Exact fixed-scale miss probability on a center-exposure atom. Selector
lookups are fair, fresh and pairwise distinct. Terminal addresses may depend
on all selectors, but their injectivity must hold for every selector outcome.
This is the finite-product version of the conditional estimate. -/
theorem measure_fixed_scale_on_center_atom
    {C : Type u_C} {I : Type u_I} {S : Type u_S} {T : Type u_T} [Fintype C] [Fintype I] [Fintype S] [Fintype T]
    (νs νt : Measure Bool) [IsProbabilityMeasure νs] [IsProbabilityMeasure νt]
    (hfalse : νs {false} = 1 / 2) (htrue : νs {true} = 1 / 2)
    (center : C → S) (fresh : I → S)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → Bool)
    (addr : (S → Bool) → I → T) (haddr : ∀ a, Function.Injective (addr a))
    (p : ℝ) (hp : p ≤ 1) (hterminal : νt {false} = ENNReal.ofReal (1 - p)) :
    ((Measure.pi (fun _ : S => νs)).prod (Measure.pi (fun _ : T => νt)))
      {z : (S → Bool) × (T → Bool) |
        (∀ c, z.1 (center c) = value c) ∧
        ∀ i, z.1 (fresh i) = true → z.2 (addr z.1 i) = false} =
      (∏ c, νs {value c}) * (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by
  classical
  have hcalc := measure_exposed_adaptive_failures_eq_lintegral
    (Measure.pi (fun _ : S => νs)) νt
    {a | ∀ c, a (center c) = value c} addr haddr
    (fun a i => a (fresh i) = true) MeasurableSet.of_discrete
  simp only [Set.mem_ofPred_eq] at hcalc
  rw [hcalc]
  have hmoment := CenterExposure.lintegral_fresh_restrict_center_atom
    νs center fresh hinj value
    (fun v => (νt {false}) ^ (Finset.univ.filter (fun i => v i = true)).card)
    (measurable_of_countable _)
  rw [hmoment]
  congr 1
  rw [hterminal]
  simpa only [Fintype.card_subtype, id_eq] using
    SelectorMoment.lookup_fair_failure_moment νs hfalse htrue
      (id : I → I) Function.injective_id p hp

/-- The preceding identity with the actual center-atom mass as coefficient,
ready for summation over center exposure values. -/
theorem measure_fixed_scale_eq_atom_mass
    {C : Type u_C} {I : Type u_I} {S : Type u_S} {T : Type u_T} [Fintype C] [Fintype I] [Fintype S] [Fintype T]
    (νs νt : Measure Bool) [IsProbabilityMeasure νs] [IsProbabilityMeasure νt]
    (hfalse : νs {false} = 1 / 2) (htrue : νs {true} = 1 / 2)
    (center : C → S) (fresh : I → S)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → Bool)
    (addr : (S → Bool) → I → T) (haddr : ∀ a, Function.Injective (addr a))
    (p : ℝ) (hp : p ≤ 1) (hterminal : νt {false} = ENNReal.ofReal (1 - p)) :
    ((Measure.pi (fun _ : S => νs)).prod (Measure.pi (fun _ : T => νt)))
      {z : (S → Bool) × (T → Bool) |
        (∀ c, z.1 (center c) = value c) ∧
        ∀ i, z.1 (fresh i) = true → z.2 (addr z.1 i) = false} =
      (Measure.pi (fun _ : S => νs)) {a | ∀ c, a (center c) = value c} *
        (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by
  rw [measure_fixed_scale_on_center_atom νs νt hfalse htrue
    center fresh hinj value addr haddr p hp hterminal]
  congr 1
  have hcenter : Function.Injective center := by
    intro c d h
    exact Sum.inl.inj (hinj (show Sum.elim center fresh (Sum.inl c) =
      Sum.elim center fresh (Sum.inl d) from h))
  symm
  simpa only [Set.mem_singleton_iff] using
    AdaptiveLabels.measure_injective_constraints νs center hcenter
      (fun c => {value c}) (fun c => measurableSet_singleton (value c))

end Problem310.FixedScaleProbability

end OAI

end

-- OpenAI source module: TreeSpanBridge
section

namespace OAI

universe u_α

namespace Problem310.TreeSpanBridge

open TreePreorder

/-- Incoming-window lengths listed in the tree's edge preorder. -/
def weights (q d : ℕ) (r : ℕ → ℕ) : List ℕ :=
  (edgePaths q d).map fun p => r (d + 1 - p.length)

@[simp] theorem weights_zero (q : ℕ) (r : ℕ → ℕ) : weights q 0 r = [] := rfl

/-- Each child contributes its incoming length followed by the weights of a
complete subtree of one smaller height. This is independent of the child label. -/
theorem weights_succ (q d : ℕ) (r : ℕ → ℕ) :
    weights q (d + 1) r =
      (List.finRange q).flatMap (fun _ => r (d + 1) :: weights q d r) := by
  simp only [weights, edgePaths, List.map_flatMap, List.map_cons,
    List.length_cons, List.map_map, Function.comp_def]
  congr 2
  funext i
  congr 1
  apply List.map_congr_left
  intro p hp
  congr 1
  omega


/-- An edge and all descendants under it, in their contiguous preorder block. -/
def subtreeBlock (q d : ℕ) (p : List (Fin q)) : List (List (Fin q)) :=
  p :: (edgePaths q (d - p.length)).map (fun v => p ++ v)

theorem childBlock_infix (q d : ℕ) (i : Fin q) :
    ([i] :: (edgePaths q d).map (List.cons i)) <:+: edgePaths q (d + 1) := by
  have hi : [i] <:+: List.finRange q := (List.singleton_infix_iff i (List.finRange q)).mpr (by simp)
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, edgePaths] using
    hi.flatMap (fun j => [j] :: (edgePaths q d).map (List.cons j))

/-- Every rooted descendant block is contiguous in the global edge preorder. -/
theorem subtreeBlock_infix (q d : ℕ) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    subtreeBlock q d p <:+: edgePaths q d := by
  induction p generalizing d with
  | nil => exact (hp rfl).elim
  | cons i p ih =>
    cases d with
    | zero => simp at hlen
    | succ d =>
      cases p with
      | nil =>
        simpa [subtreeBlock] using childBlock_infix q d i
      | cons j p =>
        have hlen' : (j :: p).length ≤ d := by simpa using hlen
        have hsub := (ih d (by simp) hlen').map (List.cons i)
        have htail : (edgePaths q d).map (List.cons i) <:+:
            [i] :: (edgePaths q d).map (List.cons i) :=
          ⟨[[i]], [], by simp⟩
        have hfull := hsub.trans (htail.trans (childBlock_infix q d i))
        simpa [subtreeBlock, List.map_map, Function.comp_def] using hfull

/-- Global-depth weights on one descendant block are exactly the incoming
length followed by the weights of the complete residual-height subtree. -/
theorem map_weights_subtreeBlock (q d : ℕ) (r : ℕ → ℕ) (p : List (Fin q))
    (hlen : p.length ≤ d) :
    (subtreeBlock q d p).map (fun v => r (d + 1 - v.length)) =
      r (d + 1 - p.length) :: weights q (d - p.length) r := by
  simp only [subtreeBlock, List.map_cons, List.map_map, Function.comp_def,
    List.length_append, weights]
  congr 1
  apply List.map_congr_left
  intro v hv
  congr 1
  omega

/-- The path-dependent weight list is exactly the numerical preorder list. -/
theorem weights_eq_preorderLengths (q g r₀ d : ℕ) :
    weights q d (WindowRecursion.length q g r₀) =
      WindowSpanSum.preorderLengths q g r₀ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [weights_succ, WindowSpanSum.preorderLengths, ih]
    simp [List.flatMap]

/-- Full-list decomposition at the genuine edge index. This is the direct
interface for constructing separated windows from the weighted preorder. -/
theorem weighted_child_decomposition (q g r₀ d : ℕ) (p : List (Fin q))
    (hp : p ≠ []) (hlen : p.length ≤ d) :
    ∃ pre post : List ℕ,
      weights q d (WindowRecursion.length q g r₀) =
        pre ++ (WindowRecursion.length q g r₀ (d + 1 - p.length) ::
          WindowSpanSum.preorderLengths q g r₀ (d - p.length)) ++ post ∧
      pre.length = (edgePaths q d).idxOf p := by
  obtain ⟨s, t, hst⟩ := subtreeBlock_infix q d p hp hlen
  let f : List (Fin q) → ℕ := fun v => WindowRecursion.length q g r₀ (d + 1 - v.length)
  refine ⟨s.map f, t.map f, ?_, ?_⟩
  · change (edgePaths q d).map f = _
    rw [← hst, List.map_append, List.map_append]
    change s.map f ++ (subtreeBlock q d p).map
      (fun v => WindowRecursion.length q g r₀ (d + 1 - v.length)) ++ t.map f = _
    rw [map_weights_subtreeBlock q d _ p hlen, weights_eq_preorderLengths]
  · rw [List.length_map]
    have hnodup : (s ++ (subtreeBlock q d p ++ t)).Nodup := by
      rw [← List.append_assoc, hst]
      exact nodup_edgePaths q d
    have hnot : p ∉ s := by
      intro hps
      exact (List.nodup_append.mp hnodup).2.2 p hps p (by simp [subtreeBlock]) rfl
    rw [← hst, List.append_assoc, List.idxOf_append_of_notMem hnot]
    simp [subtreeBlock]

end Problem310.TreeSpanBridge

end OAI

end

-- OpenAI source module: RawRepair
section

namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- Complete analytic passage from a finite random periodic grid construction to
an open periodic hitting set. The hypotheses are precisely the density, stability,
and raw-failure estimates supplied by the combinatorial construction. -/
theorem periodic_hitting_of_raw_construction
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal p)
    (hgood : ∀ x ∈ G,
      μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  classical
  choose V hBV hVo hVp hVm using fun ω =>
    Problem310.Aux.exists_open_periodic_envelope (B ω) (hBp ω)
      (ENNReal.ofReal p) (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
  apply periodic_hitting_of_pointwise_failure_bound μ p hp V hVo hVp N hN G hG hbad
  · calc
      (∫⁻ ω, volume (V ω ∩ Icc (0 : ℝ) 1) ∂μ)
          ≤ ∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) + ENNReal.ofReal p ∂μ :=
        lintegral_mono hVm
      _ = (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) + ENNReal.ofReal p := by
        rw [lintegral_add_left (measurable_of_countable _)]
        simp
      _ ≤ ENNReal.ofReal p + ENNReal.ofReal p := add_le_add hBmean le_rfl
      _ = ENNReal.ofReal (2 * p) := by
        rw [← ENNReal.ofReal_add (le_of_lt hp) (le_of_lt hp)]
        congr 1
        ring
  · intro x hx
    calc
      μ {ω | x ∈ exceptionalCenters (V ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
          ≤ μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} := by
        apply measure_mono
        intro ω hω
        exact exceptionalCenters_antitone (hBV ω) N _ hω
      _ ≤ ENNReal.ofReal (2 * p) := hgood x hx

end Problem310.Auxiliary

end

end OAI

end

-- OpenAI source module: RoutedSetDensity
section

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.RoutedSetDensity

open FiniteTableModel

/-- The actual first-success/default child choice made by the finite selector tables. -/
def selectorChoice {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (x : ℝ) : Child M :=
  OrderedRouting.chooseChild (fun i => selectorValue b ω P i x)

/-- The leaf reached by the root router, as an element of the finite leaf type. -/
def routedLeaf {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (x : ℝ) : Leaf M d :=
  ⟨RoutingPath.routeFrom (selectorChoice b ω) d [] x, by simp⟩

/-- The terminal table coordinate consulted by the complete finite router. -/
def routedAddress {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ω : SelectorTable bS) (x : ℝ) : TerminalAddress bT :=
  terminalAddress bT (routedLeaf bS ω x) x

/-- The raw random periodic set, with both selector and terminal tables explicit. -/
def routedSet {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ω : SelectorTable bS × TerminalTable bT) : Set ℝ :=
  RandomSetDensity.selectedSet (routedAddress bS bT) ω

lemma measurable_selectorChoice {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) : Measurable (selectorChoice b ω P) := by
  classical
  exact (measurable_of_finite (OrderedRouting.chooseChild (M := M))).comp
    (measurable_pi_iff.mpr fun i => measurable_selectorValue b ω P i)

@[simp] lemma selectorChoice_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (x : ℝ) :
    selectorChoice b ω P (x + 1) = selectorChoice b ω P x := by
  apply OrderedRouting.chooseChild_congr
  intro i
  exact selectorValue_add_one b ω P i x

lemma measurable_routedLeaf {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) : Measurable (routedLeaf b ω) := by
  let : MeasurableSpace (List (Child M)) := ⊤
  let : DiscreteMeasurableSpace (List (Child M)) := ⟨fun _ => trivial⟩
  have hchoose : Measurable (Function.uncurry (selectorChoice b ω)) :=
    measurable_from_prod_countable_right (measurable_selectorChoice b ω)
  have hroute := RoutingPath.measurable_routeFrom (selectorChoice b ω) hchoose d []
  apply measurable_to_countable
  intro y
  convert (measurableSet_singleton
    (RoutingPath.routeFrom (selectorChoice b ω) d [] y)).preimage hroute using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, routedLeaf]
  exact List.Vector.toList_injective.eq_iff.symm

@[simp] lemma routedLeaf_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (x : ℝ) : routedLeaf b ω (x + 1) = routedLeaf b ω x := by
  apply Subtype.ext
  exact RoutingPath.routeFrom_periodic (selectorChoice b ω) (selectorChoice_add_one b ω) d [] x

lemma measurable_routedAddress {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS) : Measurable (routedAddress bS bT ω) := by
  have hterminal : Measurable (fun z : Leaf M d × ℝ => terminalAddress bT z.1 z.2) :=
    measurable_from_prod_countable_right (measurable_terminalAddress bT)
  exact hterminal.comp ((measurable_routedLeaf bS ω).prodMk measurable_id)

@[simp] lemma routedAddress_add_one {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS) (x : ℝ) :
    routedAddress bS bT ω (x + 1) = routedAddress bS bT ω x := by
  simp [routedAddress]

lemma routedSet_periodic {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS × TerminalTable bT) (x : ℝ) :
    x + 1 ∈ routedSet bS bT ω ↔ x ∈ routedSet bS bT ω :=
  RandomSetDensity.periodic_selectedSet _ (routedAddress_add_one bS bT) ω x

/-- Exact density of the concrete raw routed blocker, with no spatial regularity hypotheses. -/
theorem expected_routedSet_density {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (P : Measure (SelectorTable bS)) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν] :
    (∫⁻ ω, volume (routedSet bS bT ω ∩ Set.Icc (0 : ℝ) 1)
      ∂(P.prod (Measure.pi (fun _ : TerminalAddress bT => ν)))) = ν {true} := by
  classical
  exact RandomSetDensity.expected_density_selectedSet P ν _ (measurable_routedAddress bS bT)

end Problem310.RoutedSetDensity

end

end OAI

end

-- OpenAI source module: GridStabilityFin
section

namespace OAI

universe u_ι

noncomputable section
namespace Problem310

/-- Bridge from quantitative stability to the canonical finite selector addresses. -/
theorem gridStableCenters_preserves_fin {ι : Type u_ι} {a b : ι → ℕ} {x t : ℝ}
    (hx : x ∈ gridStableCenters a b) (i : ι) {c n : ℕ}
    (hc : c ≤ b i) (hn : a i ≤ n) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    GridSeparation.dyadicKey c (x + t * ((2 : ℝ)⁻¹) ^ n) =
      GridSeparation.dyadicKey c x := by
  apply (GridSeparation.dyadicKey_eq_iff c _ _).mpr
  exact gridStableCenters_preserves hx i hc hn ht

/-- Choose the gap using only the finite number of grids, before their resolutions
are assigned. Every subsequent assignment has a periodic measurable stable set
with the same prescribed exceptional-density budget. -/
theorem exists_uniform_grid_stability {ι : Type u_ι} [Fintype ι]
    (p : ℝ) (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ ∀ b : ι → ℕ, ∃ G : Set ℝ,
      MeasurableSet G ∧ (∀ x : ℝ, x + 1 ∈ G ↔ x ∈ G) ∧
      MeasureTheory.volume (Gᶜ ∩ Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p ∧
      ∀ x ∈ G, ∀ i : ι, ∀ n : ℕ, b i + g + 1 ≤ n →
        ∀ t ∈ Set.Icc (1 : ℝ) 2,
          GridSeparation.dyadicKey (b i) (x + t * ((2 : ℝ)⁻¹) ^ n) =
            GridSeparation.dyadicKey (b i) x := by
  obtain ⟨g, hg, hbudget⟩ := exists_dyadic_gap_budget (Fintype.card ι) hp
  refine ⟨g, hg, fun b ↦ ?_⟩
  let a : ι → ℕ := fun i ↦ b i + g + 1
  refine ⟨gridStableCenters a b, measurableSet_gridStableCenters a b,
    gridStableCenters_add_one a b, ?_, ?_⟩
  · exact (volume_gridStableCenters_compl_gap_le a b g hg (fun i ↦ rfl)).trans
      (ENNReal.ofReal_le_ofReal hbudget.le)
  · intro x hx i n hn t ht
    exact gridStableCenters_preserves_fin hx i le_rfl hn ht

end Problem310

end

end OAI

end

-- OpenAI source module: WindowTrialAddresses
section

namespace OAI

noncomputable section

namespace Problem310.WindowTrialAddresses

open FiniteTableModel TrialAddresses

variable {M d g r₀ : ℕ}

abbrev LocalTrial (W : WindowData (M + 1) d g r₀) (P : Node M d) :=
  WindowTrial M (W.r (d - P.val.length))

def localStarts (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) : ℕ :=
  W.a (selectorEdge P i)

def localIndex (W : WindowData (M + 1) d g r₀) (P : Node M d)
    (z : LocalTrial W P) : ℕ := windowTrialIndex (localStarts W P) z

@[simp] theorem card_localTrial (W : WindowData (M + 1) d g r₀) (P : Node M d) :
    Fintype.card (LocalTrial W P) = M * W.r (d - P.val.length) := by
  simp [LocalTrial]

theorem localIndex_bounds (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (z : LocalTrial W P) :
    3 ≤ localIndex W P z ∧ localIndex W P z ≤ selectorEndpoints W P z.1 := by
  have hs := W.start_three (selectorEdge P z.1) (selectorEdge_valid P z.1)
  have he := selector_window_endpoint W P z.1
  have hk := z.2.isLt
  dsimp [localIndex, windowTrialIndex, localStarts]
  omega

/-- The actual finite-model selector coordinate read at one child-window trial. -/
def localSelectorAddress (W : WindowData (M + 1) d g r₀) (P : Node M d)
    (x t : ℝ) (z : LocalTrial W P) : SelectorAddress (selectorEndpoints W) :=
  selectorAddress (selectorEndpoints W) P z.1
    (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P z))

theorem localSelectorAddress_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    Function.Injective (localSelectorAddress W P x t) := by
  change Function.Injective (trialAddress
    (fun e : Node M d × Fin M => selectorEndpoints W e.1 e.2)
    (fun z : LocalTrial W P => (P, z.1)) (localIndex W P) x t)
  apply trialAddress_injective _ _ _ _ _ ht.1 ht.2
  · exact fun z => (localIndex_bounds W P z).1
  · exact fun z => (localIndex_bounds W P z).2
  · exact windowTrial_pair_injective (localStarts W P) (fun i => (P, i))
      (fun _ _ h => congrArg Prod.snd h)

theorem localSelectorAddress_ne_center (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (z : LocalTrial W P) (e : Node M d × Fin M) :
    localSelectorAddress W P x t z ≠
      selectorAddress (selectorEndpoints W) e.1 e.2 x := by
  exact trialAddress_ne_center
    (fun e : Node M d × Fin M => selectorEndpoints W e.1 e.2)
    (fun z : LocalTrial W P => (P, z.1)) (localIndex W P) x t ht.1 ht.2
    (fun z => (localIndex_bounds W P z).1)
    (fun z => (localIndex_bounds W P z).2) z e

/-- This is the single address-injectivity assumption needed by center
exposure: every center coordinate and every local trial coordinate are fresh. -/
theorem center_local_sum_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    Function.Injective (Sum.elim
      (fun e : Node M d × Fin M => selectorAddress (selectorEndpoints W) e.1 e.2 x)
      (localSelectorAddress W P x t)) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact congrArg Sum.inl (center_selectorAddress_injective (selectorEndpoints W) x h)
    | inr j =>
      exact False.elim ((localSelectorAddress_ne_center W P x t ht j i) h.symm)
  | inr i =>
    cases j with
    | inl j =>
      exact False.elim ((localSelectorAddress_ne_center W P x t ht i j) h)
    | inr j =>
      exact congrArg Sum.inr (localSelectorAddress_injective W P x t ht h)

/-- Once local routing stays in its chosen child subtree, all terminal
coordinates are distinct. WindowData automatically supplies the necessary
resolution refinement, so no numerical hypothesis remains. -/
theorem localTerminalAddress_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (leaf : LocalTrial W P → Leaf M d)
    (hprefix : ∀ z, (selectorEdge P z.1).IsPrefix (leaf z).val) :
    Function.Injective (fun z : LocalTrial W P =>
      terminalAddress (terminalEndpoints W) (leaf z)
        (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P z))) := by
  change Function.Injective (trialAddress (terminalEndpoints W) leaf (localIndex W P) x t)
  apply TrialAddresses.terminalAddress_injective
    (fun z : LocalTrial W P => z.1) (localIndex W P) leaf
    (selectorEndpoints W P) (terminalEndpoints W) x t ht.1 ht.2
  · exact fun z => (localIndex_bounds W P z).1
  · exact fun z => (localIndex_bounds W P z).2
  · exact fun z => incoming_le_terminalEndpoints W P z.1 (leaf z) (hprefix z)
  · intro i j hij
    have hpath : (leaf i).val = (leaf j).val := congrArg Subtype.val hij
    obtain ⟨si, hsi⟩ := hprefix i
    obtain ⟨sj, hsj⟩ := hprefix j
    have heq : P.val ++ (i.1.castSucc :: si) = P.val ++ (j.1.castSucc :: sj) := by
      simpa only [selectorEdge, List.append_assoc, List.singleton_append] using
        hsi.trans (hpath.trans hsj.symm)
    have hchild := (List.cons.inj (List.append_cancel_left heq)).1
    exact Fin.ext (congrArg (fun v : Fin (M + 1) => v.val) hchild)
  · exact windowTrial_pair_injective (localStarts W P) id (fun _ _ h => h)

end Problem310.WindowTrialAddresses

end

end OAI

end

-- OpenAI source module: CenterFailureBound
section

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310.CenterFailureBound

open FiniteTableModel CenterRouteExposure

/-- The actual full-outcome fiber of the center selector exposure. -/
def centerAtom {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (x : ℝ) (ξ : Node M d × Fin M → Bool) :
    Set (SelectorTable bS × TerminalTable bT) :=
  {ω | centerExposure bS x ω.1 = ξ}

/-- No default occurs on the actual center path. Terminal coordinates do not
enter this event, but are retained in the probability space. -/
def noDefaultEvent {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (x : ℝ) : Set (SelectorTable bS × TerminalTable bT) :=
  {ω | ∀ k < d, centerChoice bS x
    (RoutingPath.routeFrom (centerChoice bS x) k [] ω.1) ω.1 ≠ Fin.last M}

/-- Concrete assembly of the atom bounds into the raw `2p` failure estimate.
All exposure fibers, their measurability, and their total mass are discharged
here for the canonical finite selector/terminal table model. -/
theorem raw_failure_le_of_center_atoms {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (μ : Measure (SelectorTable bS × TerminalTable bT)) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 ≤ p) (B : SelectorTable bS × TerminalTable bT → Set ℝ)
    (N : Set ℕ) (x : ℝ)
    (hbad : μ (noDefaultEvent bS bT x) ≤ ENNReal.ofReal p)
    (hatom : ∀ ξ : Node M d × Fin M → Bool, GoodExposure bS x ξ →
      μ ({ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
          centerAtom bS bT x ξ) ≤
        ENNReal.ofReal p * μ (centerAtom bS bT x ξ)) :
    μ {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ≤
      ENNReal.ofReal (2 * p) := by
  classical
  let f : SelectorTable bS × TerminalTable bT → (Node M d × Fin M → Bool) :=
    fun ω => centerExposure bS x ω.1
  let good : Set (Node M d × Fin M → Bool) := {ξ | GoodExposure bS x ξ}
  have hf (ξ) : MeasurableSet {ω | f ω = ξ} := (Set.to_countable _).measurableSet
  have hbad' : μ {ω | f ω ∉ good} ≤ ENNReal.ofReal p := by
    have heq : {ω | f ω ∉ good} = noDefaultEvent bS bT x := by
      ext ω
      exact badExposure_centerExposure_iff bS x ω.1
    rwa [heq]
  have h := ExposureUnionBound.measure_le_of_finite_exposure μ f hf
    {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} good
    (ENNReal.ofReal p) (ENNReal.ofReal p) hbad' (fun ξ hξ => hatom ξ hξ)
  calc
    μ {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal p + ENNReal.ofReal p := h
    _ = ENNReal.ofReal (2 * p) := by
      rw [← ENNReal.ofReal_add hp hp]
      congr 1
      ring

end Problem310.CenterFailureBound

end

end OAI

end

-- OpenAI source module: RoutedFirstDefault
section

namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

/-- Exact no-default probability for the actual depth-`d` spatial router
under the finite selector/terminal outcome law. All randomness is instantiated. -/
theorem outcomeLaw_routed_no_default {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      {ω : SelectorTable bS × TerminalTable bT |
        Fin.last M ∉ RoutingPath.routeFrom
          (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
          d [] x} = (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  have heq : {ω : SelectorTable bS × TerminalTable bT |
        Fin.last M ∉ RoutingPath.routeFrom
          (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
          d [] x} =
      ⋃ f : FirstDefault.Path M d, {ω : SelectorTable bS × TerminalTable bT |
        ∀ i : FirstDefault.Tests f,
          selectorValue bS ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
            FirstDefault.requiredBit f i} := by
    ext ω
    exact FirstDefault.spatial_default_not_mem_iff
      (fun ω P i y => selectorValue bS ω.1 P i y) ω x
  rw [heq]
  exact outcomeLaw_center_no_default bS bT p hp0 hp1 x

/-- The same exact law stated with the step-by-step absence of a default.
This form pairs directly with first-default decomposition of the exposure atoms. -/
theorem outcomeLaw_no_default_steps {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      {ω : SelectorTable bS × TerminalTable bT |
        ∀ k < d,
          OrderedRouting.chooseChild (fun i => selectorValue bS ω.1
            (RoutingPath.routeFrom
              (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
              k [] x) i x) ≠ Fin.last M} =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  convert outcomeLaw_routed_no_default bS bT p hp0 hp1 x using 1
  congr 1
  ext ω
  exact RoutingPath.noDefault_iff_not_mem
    (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y)) (Fin.last M) d x

end Problem310.FiniteTableModel

end

end OAI

end

-- OpenAI source module: WindowLocalFactor
section

namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.WindowLocalFactor

open RoutingPath GridSeparation LocalPredicateFactor

/-- Padded equal-length child windows provide a common representative set for
all outcomes and all local predicates factoring through their subtree grids.
The representatives are selected before the outcome or predicates. -/
theorem exists_uniform_window_representatives {Ω : Type u_Ω} (M r : ℕ)
    (a B : Fin M → ℕ) (hpadding : ∀ i, B i + 1 ≤ a i + 2 * r)
    (x : ℝ) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * r * 2 ^ (2 * r + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : Ω → Fin M → ℝ → Bool,
          (∀ ω i y z, ⌊(2 : ℝ) ^ (B i + 2) * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ (B i + 2) * Int.fract z⌋ → Q ω i y = Q ω i z) →
          ∀ ω (i : Fin M) (j : Fin r),
            Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (a i + j.val)) =
              Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (a i + j.val)) := by
  have hspan (ij : Fin M × Fin r) : B ij.1 + 2 ≤
      (a ij.1 + ij.2.val) + (2 * r + 2) := by
    have h := hpadding ij.1
    omega
  obtain ⟨R, hR, hcard, hrep⟩ := ScaleDiscretization.exists_local_predicate_representatives
    x (fun ij : Fin M × Fin r => B ij.1 + 2)
    (fun ij : Fin M × Fin r => a ij.1 + ij.2.val) (2 * r + 2) hspan
  refine ⟨R, hR, ?_, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hcard
  · intro t ht
    obtain ⟨t', ht', hsame⟩ := hrep t ht
    refine ⟨t', ht', ?_⟩
    intro Q hQ ω i j
    exact hsame (fun ij z => Q ω ij.1 z) (fun ij y z h => hQ ω ij.1 y z h) (i, j)

/-- Canonical window data discharges the padding hypothesis for all nondefault
children of an internal node, whose incoming windows have the same length. -/
theorem exists_window_data_representatives {Ω : Type u_Ω} {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀) (U : FiniteTableModel.Node M d) (x : ℝ) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : Ω → Fin M → ℝ → Bool,
          (∀ ω i y z,
            ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract z⌋ →
              Q ω i y = Q ω i z) →
          ∀ ω (i : Fin M) (j : Fin (W.r (d - U.val.length))),
            Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) =
              Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) := by
  apply exists_uniform_window_representatives M (W.r (d - U.val.length))
    (fun i => W.a (U.val ++ [i.castSucc]))
    (fun i => W.bstar (U.val ++ [i.castSucc]))
  intro i
  have hP : ValidWindowEdge d (U.val ++ [i.castSucc]) := by
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt U.property
  have hpad := W.padding _ hP
  simpa only [List.length_append, List.length_singleton, Nat.add_sub_add_right] using hpad

/-- The concrete finite-table local predicate inherits its common grid from
WindowData's bound on endpoints of descendant edges. -/
theorem window_local_predicate_factors {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀)
    (bS : FiniteTableModel.Node M d → Fin M → ℕ)
    (bT : FiniteTableModel.Leaf M d → ℕ)
    (hbS : ∀ Q j, bS Q j = W.b (Q.val ++ [j.castSucc]))
    (hbT : ∀ L, bT L = W.b L.val)
    (ωS : FiniteTableModel.SelectorTable bS) (ωT : FiniteTableModel.TerminalTable bT)
    (choose : List (FiniteTableModel.Child M) → ℝ → FiniteTableModel.Child M)
    (rule : List (FiniteTableModel.Child M) → (Fin M → Bool) → FiniteTableModel.Child M)
    (hchoose : ∀ Q x, choose Q x = rule Q (fun j => FiniteTableModel.selectorValue bS ωS Q j x))
    (U : FiniteTableModel.Node M d) (i : Fin M) (r : ℕ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (W.bstar (U.val ++ [i.castSucc]) + 2) * Int.fract y⌋) :
    (ωS (FiniteTableModel.selectorAddress bS U i x) &&
      ωT (FiniteTableModel.terminalAddress bT
        (FiniteLocalPredicate.localLeaf choose r (U.val ++ [i.castSucc]) hdepth x) x)) =
    (ωS (FiniteTableModel.selectorAddress bS U i y) &&
      ωT (FiniteTableModel.terminalAddress bT
        (FiniteLocalPredicate.localLeaf choose r (U.val ++ [i.castSucc]) hdepth y) y)) := by
  have hP : ValidWindowEdge d (U.val ++ [i.castSucc]) := by
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt U.property
  apply FiniteLocalPredicate.finite_local_predicate_factors
    bS bT ωS ωT choose rule hchoose r (U.val ++ [i.castSucc]) hdepth U i
    (W.bstar (U.val ++ [i.castSucc]))
  · intro Q hPQ j
    rw [hbS]
    apply (W.descendant_bounds _ _ hP ?_ (hPQ.trans (List.prefix_append _ _))).2
    refine ⟨by simp, ?_⟩
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt Q.property
  · intro L hPL
    rw [hbT]
    apply (W.descendant_bounds _ _ hP ?_ hPL).2
    refine ⟨?_, L.property.le⟩
    intro hL
    have hD := L.property
    rw [hL] at hD
    simp only [List.length_nil] at hD
    have hU := U.property
    omega
  · rw [hbS]
    exact (W.descendant_bounds _ _ hP hP (List.prefix_refl _)).2
  · exact hxy

/-- Complete concrete representative adapter. Here `Q` is the actual local test,
with only its defining equality retained as an input for convenient rewriting.
No grid-factorization or numerical span hypotheses remain. -/
theorem exists_concrete_local_representatives {M d g r₀ : ℕ}
    (W : WindowData (M + 1) d g r₀) (U : FiniteTableModel.Node M d) (x : ℝ)
    (choose : FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) →
      List (FiniteTableModel.Child M) → ℝ → FiniteTableModel.Child M)
    (rule : List (FiniteTableModel.Child M) → (Fin M → Bool) → FiniteTableModel.Child M)
    (hchoose : ∀ ωS P y, choose ωS P y = rule P (fun j =>
      FiniteTableModel.selectorValue (FiniteTableModel.selectorEndpoints W) ωS P j y))
    (r : ℕ) (hdepth : ∀ i : Fin M, (U.val ++ [i.castSucc]).length + r = d)
    (Q : (FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) ×
      FiniteTableModel.TerminalTable (FiniteTableModel.terminalEndpoints W)) →
        Fin M → ℝ → Bool)
    (hQ : ∀ ω i y, Q ω i y =
      (ω.1 (FiniteTableModel.selectorAddress (FiniteTableModel.selectorEndpoints W) U i y) &&
        ω.2 (FiniteTableModel.terminalAddress (FiniteTableModel.terminalEndpoints W)
          (FiniteLocalPredicate.localLeaf (choose ω.1) r (U.val ++ [i.castSucc]) (hdepth i) y) y))) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ ω (i : Fin M) (j : Fin (W.r (d - U.val.length))),
          Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) =
            Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (W.a (U.val ++ [i.castSucc]) + j.val)) := by
  obtain ⟨R, hR, hcard, hrep⟩ := exists_window_data_representatives (Ω :=
    FiniteTableModel.SelectorTable (FiniteTableModel.selectorEndpoints W) ×
      FiniteTableModel.TerminalTable (FiniteTableModel.terminalEndpoints W)) W U x
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', hsame⟩ := hrep t ht
  refine ⟨t', ht', hsame Q ?_⟩
  intro ω i y z hyz
  rw [hQ ω i y, hQ ω i z]
  exact window_local_predicate_factors W
    (FiniteTableModel.selectorEndpoints W) (FiniteTableModel.terminalEndpoints W)
    (fun _ _ => rfl) (fun _ => rfl) ω.1 ω.2 (choose ω.1) rule (hchoose ω.1)
    U i r (hdepth i) hyz

end Problem310.WindowLocalFactor

end

end OAI

end

-- OpenAI source module: WindowDataExistence
section

namespace OAI

noncomputable section

namespace Problem310.WindowConstruction

open TreePreorder TreePreorderRank WindowPlacement
open scoped BigOperators

/-- Actual window lengths, in the finite tree preorder. -/
def lengths (q d g r₀ : ℕ) : List ℕ :=
  TreeSpanBridge.weights q d (WindowRecursion.length q g r₀)

def lengthAt (q d g r₀ : ℕ) : ℕ → ℕ := WindowPlacement.lengthAt (lengths q d g r₀)

lemma lengthAt_edgeRank {q d g r₀ : ℕ} {P : List (Fin q)}
    (hP : ValidWindowEdge d P) :
    lengthAt q d g r₀ (edgeRank d P) = WindowRecursion.length q g r₀ (d + 1 - P.length) := by
  have hm := (mem_edgePaths_iff q d P).mpr hP
  rw [PreorderIndex.edgeRank_eq_idxOf hm]
  exact WindowPlacement.lengthAt_map_idxOf _ hm

lemma length_preorderLengths (q g r₀ h : ℕ) :
    (WindowSpanSum.preorderLengths q g r₀ h).length = edgeCount q h := by
  rw [← TreeSpanBridge.weights_eq_preorderLengths q g r₀ h]
  simp [TreeSpanBridge.weights]

/-- Every descendant endpoint lies within twice the incoming window length. -/
theorem descendant_endpoint_bound {q d g r₀ : ℕ} (hq : 1 ≤ q)
    {P Q : List (Fin q)} (hP : ValidWindowEdge d P) (hQ : ValidWindowEdge d Q)
    (hpref : P.IsPrefix Q) :
    finish (lengthAt q d g r₀) g (edgeRank d Q) + 1 ≤
      start (lengthAt q d g r₀) g (edgeRank d P) +
        2 * WindowRecursion.length q g r₀ (d + 1 - P.length) := by
  obtain ⟨pre, post, hL, hpre⟩ :=
    TreeSpanBridge.weighted_child_decomposition q g r₀ d P hP.1 hP.2
  have hmem := (mem_edgePaths_iff q d P).mpr hP
  have hpre' : pre.length = edgeRank d P := by
    rw [PreorderIndex.edgeRank_eq_idxOf hmem]
    exact hpre
  have hheight : d + 1 - P.length = (d - P.length) + 1 := by
    have hlen := hP.2
    omega
  let block := WindowRecursion.length q g r₀ (d + 1 - P.length) ::
    WindowSpanSum.preorderLengths q g r₀ (d - P.length)
  have hcard : block.length = edgeCount q (d - P.length) + 1 := by
    simp [block, length_preorderLengths]
  have hsum := WindowPlacement.sum_lengthAt_segment pre block post g
  have hL' : lengths q d g r₀ = pre ++ block ++ post := hL
  rw [← hL', hcard, hpre'] at hsum
  have hbudget :
      (∑ k ∈ Finset.range (edgeCount q (d - P.length) + 1),
        (lengthAt q d g r₀ (edgeRank d P + k) + g)) ≤
      2 * WindowRecursion.length q g r₀ (d + 1 - P.length) + g := by
    change (∑ k ∈ Finset.range (edgeCount q (d - P.length) + 1),
      (WindowPlacement.lengthAt (lengths q d g r₀) (edgeRank d P + k) + g)) ≤ _
    rw [hsum]
    change WindowSpanSum.paddedSum g block ≤ _
    dsimp [block]
    rw [hheight]
    exact WindowSpanSum.childBlock_budget q g r₀ (d - P.length) hq
  have hend := WindowPlacement.block_endpoint_le hbudget
  have hr := (isPrefix_iff_edgeRank_bounds hP.2 hQ.2 hP.1 hQ.1).mp hpref
  rw [PreorderIndex.size_eq_one_add_edgeCount] at hr
  have hle : edgeRank d Q ≤ edgeRank d P + edgeCount q (d - P.length) := by omega
  have hm := WindowPlacement.finish_mono (lengthAt q d g r₀) g hle
  omega

/-- The complete deterministic windows exist with any prescribed positive
uniform threshold and gap. -/
def windowData (q d g r₀ : ℕ) (hq : 1 ≤ q) (hr₀ : 1 ≤ r₀) :
    WindowData q d g r₀ where
  r := WindowRecursion.length q g r₀
  a P := start (lengthAt q d g r₀) g (edgeRank d P)
  b P := finish (lengthAt q d g r₀) g (edgeRank d P)
  bstar P := start (lengthAt q d g r₀) g (edgeRank d P) +
    2 * WindowRecursion.length q g r₀ (d + 1 - P.length) - 1
  length_pos P hP := hr₀.trans (WindowRecursion.threshold_le_length _ _ _ _)
  length_threshold P hP := WindowRecursion.threshold_le_length _ _ _ _
  start_three P hP := WindowPlacement.three_le_start _ _ _
  endpoint P hP := by
    rw [WindowPlacement.finish_add_one, lengthAt_edgeRank hP]
  gap_prefix P Q hP hQ hpref hne := by
    apply WindowPlacement.gap_of_lt
    have hr := (isPrefix_iff_edgeRank_bounds hP.2 hQ.2 hP.1 hQ.1).mp hpref
    apply lt_of_le_of_ne hr.1
    intro heq
    exact hne (edgeRank_injective_on hP.2 hQ.2 hP.1 hQ.1 heq)
  gap_sibling P i j tail hij hP hQ := by
    apply WindowPlacement.gap_of_lt
    exact edgeRank_sibling_descendants_lt (p := []) hij hP.2 hQ.2
  descendant_bounds P Q hP hQ hpref := by
    constructor
    · apply WindowPlacement.finish_mono
      exact ((isPrefix_iff_edgeRank_bounds hP.2 hQ.2 hP.1 hQ.1).mp hpref).1
    · have hb := descendant_endpoint_bound (g := g) (r₀ := r₀) hq hP hQ hpref
      omega
  padding P hP := by
    have hstart := WindowPlacement.three_le_start (lengthAt q d g r₀) g (edgeRank d P)
    omega

end Problem310.WindowConstruction

end

end OAI

end

-- OpenAI source module: FiniteLocalHit
section

namespace OAI

noncomputable section
namespace Problem310.FiniteLocalHit

open FiniteTableModel StableRouting RoutingPath OrderedRouting FiniteLocalPredicate

variable {M d : ℕ}

/-- A successful concrete child-local test is a successful terminal lookup on the
actual root route. Only the earlier center-path selectors must be stable. -/
theorem local_test_implies_root_hit
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (k r : ℕ) (U : Node M d) (i : Fin M) (x y : ℝ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    (hU : routeFrom (select (selectorValue bS ωS)) k [] x = U.val)
    (hnd : ∀ l < k, select (selectorValue bS ωS)
      (routeFrom (select (selectorValue bS ωS)) l [] x) x ≠ Fin.last M)
    (hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ select (selectorValue bS ωS)
        (routeFrom (select (selectorValue bS ωS)) l [] x) x →
      selectorValue bS ωS (routeFrom (select (selectorValue bS ωS)) l [] x) j x =
      selectorValue bS ωS (routeFrom (select (selectorValue bS ωS)) l [] x) j y)
    (hdefault : select (selectorValue bS ωS) U.val x = Fin.last M)
    (hearlier : ∀ j < i, selectorValue bS ωS U.val j x = selectorValue bS ωS U.val j y)
    (hlocal : (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT
        (localLeaf (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) hdepth y) y)) = true) :
    ωT (terminalAddress bT
      (localLeaf (select (selectorValue bS ωS)) d [] (by simp) y) y) = true := by
  have hklength : k = U.val.length := by
    have h := congrArg List.length hU
    simpa using h
  have htotal : k + 1 + r = d := by
    simpa only [List.length_append, List.length_singleton, ← hklength] using hdepth
  simp only [Bool.and_eq_true] at hlocal
  obtain ⟨hselector, hterminal⟩ := hlocal
  have hi : select (selectorValue bS ωS) U.val y = i.castSucc := by
    apply chooseChild_of_local_success
    · exact rejects_earlier_at_default (selectorValue bS ωS) U.val x y i hdefault hearlier
    · simpa using hselector
  have hroute : routeFrom (select (selectorValue bS ωS)) d [] y =
      routeFrom (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) y := by
    apply (congrArg (fun n => routeFrom (select (selectorValue bS ωS)) n [] y) htotal).symm.trans
    apply routeFrom_eq_local_route _ k r [] U.val x y i.castSucc hU ?_ hi
    intro l hl
    exact select_eq_of_earlier_agreement (selectorValue bS ωS) _ x y
      (hnd l hl) (hprefix l hl)
  have hleaf : localLeaf (select (selectorValue bS ωS)) d [] (by simp) y =
      localLeaf (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) hdepth y :=
    Subtype.ext hroute
  rw [hleaf]
  exact hterminal

/-- Final canonical-set form of the local-hit implication. This uses precisely the
concrete `selectorChoice`, `localLeaf`, and `routedSet` definitions of the model. -/
theorem local_test_mem_routedSet
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (k r : ℕ) (U : Node M d) (i : Fin M) (x y : ℝ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    (hU : routeFrom (RoutedSetDensity.selectorChoice bS ωS) k [] x = U.val)
    (hnd : ∀ l < k, RoutedSetDensity.selectorChoice bS ωS
      (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) x ≠ Fin.last M)
    (hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ RoutedSetDensity.selectorChoice bS ωS
        (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) x →
      selectorValue bS ωS (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) j x =
      selectorValue bS ωS (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) j y)
    (hdefault : RoutedSetDensity.selectorChoice bS ωS U.val x = Fin.last M)
    (hearlier : ∀ j < i, selectorValue bS ωS U.val j x = selectorValue bS ωS U.val j y)
    (hlocal : (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT
        (localLeaf (RoutedSetDensity.selectorChoice bS ωS) r (U.val ++ [i.castSucc]) hdepth y) y)) = true) :
    y ∈ RoutedSetDensity.routedSet bS bT (ωS, ωT) := by
  exact local_test_implies_root_hit bS bT ωS ωT k r U i x y hdepth hU hnd
    hprefix hdefault hearlier hlocal

end Problem310.FiniteLocalHit

end

end OAI

end

-- OpenAI source module: RoutedExposure
section

namespace OAI

noncomputable section

namespace Problem310.RoutedExposure
open FiniteTableModel RoutingPath CenterRouteExposure RoutedSetDensity

@[simp] theorem selectorChoice_eq_centerChoice {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (ω : SelectorTable b)
    (P : List (Child M)) (x : ℝ) :
    selectorChoice b ω P x = centerChoice b x P ω := rfl

/-- Translate from spatial routing with tables fixed to routing the table outcome
with the center fixed. No decision or node representation is changed. -/
theorem routedPath_eq_centerRoute {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (ω : SelectorTable b) (x : ℝ)
    (n : ℕ) (P : List (Child M)) :
    routeFrom (selectorChoice b ω) n P x = routeFrom (centerChoice b x) n P ω :=
  routeFrom_congr_at _ _ x ω (fun _ => rfl) n P

/-- A good exposure supplies the actual bounded first-default node, fixed before
any remaining selector or terminal-table coordinates are revealed. -/
theorem actual_firstDefaultNode_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : GoodExposure b x ξ) :
    ∃ k : Fin d, ∃ U : Node M d, U.val.length = k.val ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (selectorChoice b ω) k.val [] x = U.val ∧
        selectorChoice b ω U.val x = Fin.last M ∧
        ∀ l < k.val,
          selectorChoice b ω (routeFrom (selectorChoice b ω) l [] x) x ≠ Fin.last M := by
  obtain ⟨k, U, hlen, hU⟩ := firstDefaultNode_on_atom b x ξ hgood
  refine ⟨k, U, hlen, ?_⟩
  intro ω hω
  obtain ⟨hroute, _, hdefault, hprior⟩ := hU ω hω
  have hactual : routeFrom (selectorChoice b ω) k.val [] x = U.val := by
    rw [routedPath_eq_centerRoute]
    exact hroute
  refine ⟨hactual, ?_, ?_⟩
  · change centerChoice b x U.val ω = Fin.last M
    rwa [hroute] at hdefault
  · intro l hl
    simpa only [routedPath_eq_centerRoute, selectorChoice_eq_centerChoice] using hprior l hl

end Problem310.RoutedExposure

end

end OAI

end

-- OpenAI source module: Construction
section

namespace OAI

noncomputable section

namespace Problem310.Construction

open Set MeasureTheory FiniteTableModel

/-- The analytic conclusion for the actual finite window-table model. All
regularity and first-moment obligations are discharged here; only the geometric
good-center set and its raw failure estimate remain as inputs. -/
theorem periodic_hitting_of_window_failure
    {M d g r₀ : ℕ} (W : WindowData (M + 1) d g r₀)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hgood : ∀ x ∈ G,
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp.le hp1.le
        {ω | x ∈ Auxiliary.exceptionalCenters
          (RoutedSetDensity.routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
          (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  classical
  apply Auxiliary.periodic_hitting_of_raw_construction
    (ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp.le hp1.le)
    p hp (RoutedSetDensity.routedSet (selectorEndpoints W) (terminalEndpoints W))
    (RoutedSetDensity.routedSet_periodic _ _) (Ici 1) (fun _ hn => hn)
    G hG hbad
  · have hmean := RoutedSetDensity.expected_routedSet_density
      (selectorEndpoints W) (terminalEndpoints W)
      (ConcreteLabels.selectorLaw (SelectorAddress (selectorEndpoints W)))
      (ConcreteLabels.bitLaw p hp.le hp1.le)
    simpa only [ConcreteLabels.outcomeLaw, ConcreteLabels.terminalLaw,
      ConcreteLabels.bitLaw_true] using hmean.le
  · exact hgood

end Problem310.Construction

end

end OAI

end

-- OpenAI source module: GridModelStability
section

namespace OAI

universe u_ι

noncomputable section
namespace Problem310.FiniteTableModel

end Problem310.FiniteTableModel

end

end OAI

end

-- OpenAI source module: WindowDataStability
section

namespace OAI

noncomputable section
namespace Problem310

open FiniteTableModel

/-- Actual selector stability for arbitrary canonical window data. The gap is
chosen before the window recursion and all its resolutions. Prefix and sibling
gap fields of `W` may be applied directly to the displayed strict cutoff. -/
theorem exists_windowData_selector_stability (M d : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ ∀ r₀ : ℕ, ∀ W : WindowData (M + 1) d g r₀,
      ∃ G : Set ℝ, MeasurableSet G ∧
        (∀ x : ℝ, x + 1 ∈ G ↔ x ∈ G) ∧
        MeasureTheory.volume (Gᶜ ∩ Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p ∧
        ∀ x ∈ G, ∀ P : Node M d, ∀ i : Fin M, ∀ n : ℕ,
          W.b (P.val ++ [i.castSucc]) + g < n →
          ∀ t ∈ Set.Icc (1 : ℝ) 2,
          ∀ ω : SelectorTable (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])),
          selectorValue (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])) ω P.val i (x + t * ((2 : ℝ)⁻¹) ^ n) =
          selectorValue (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])) ω P.val i x := by
  obtain ⟨g, hg, hgeometry⟩ :=
    exists_uniform_grid_stability (ι := Node M d × Fin M) p hp
  refine ⟨g, hg, fun r₀ W ↦ ?_⟩
  let bS : Node M d → Fin M → ℕ := fun P i => W.b (P.val ++ [i.castSucc])
  obtain ⟨G, hGm, hGp, hGbudget, hGkey⟩ := hgeometry (fun e => bS e.1 e.2)
  refine ⟨G, hGm, hGp, hGbudget, ?_⟩
  intro x hx P i n hn t ht ω
  have hk := hGkey x hx (P, i) n (by dsimp [bS]; omega) t ht
  have ha : selectorAddress bS P i (x + t * ((2 : ℝ)⁻¹) ^ n) =
      selectorAddress bS P i x := by
    unfold selectorAddress
    rw [hk]
  change selectorValue bS ω P.val i (x + t * ((2 : ℝ)⁻¹) ^ n) =
    selectorValue bS ω P.val i x
  rw [selectorValue_valid, selectorValue_valid, ha]

end Problem310

end

end OAI

end

-- OpenAI source module: GridWindowStability
section

namespace OAI

noncomputable section
namespace Problem310

end Problem310

end

end OAI

end

-- OpenAI source module: WindowFixedScale
section

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.WindowTrialAddresses

open FiniteTableModel ConcreteLabels

variable {M d g r₀ : ℕ}

/-- Exact fixed-scale failure mass for the actual W-indexed finite table
model. All fresh-selector and adaptive-terminal injectivity obligations are
discharged here; local leaves only have to stay in their selected child. -/
theorem window_fixed_scale_on_center_atom
    (W : WindowData (M + 1) d g r₀) (P : Node M d) (x t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (value : Node M d × Fin M → Bool)
    (leaf : SelectorTable (selectorEndpoints W) → LocalTrial W P → Leaf M d)
    (hprefix : ∀ a z, (selectorEdge P z.1).IsPrefix (leaf a z).val) :
    outcomeLaw (SelectorAddress (selectorEndpoints W)) (TerminalAddress (terminalEndpoints W))
      p hp0 hp1
      {z : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W) |
        (∀ c : Node M d × Fin M,
          z.1 (selectorAddress (selectorEndpoints W) c.1 c.2 x) = value c) ∧
        ∀ i : LocalTrial W P, z.1 (localSelectorAddress W P x t i) = true →
          z.2 (terminalAddress (terminalEndpoints W) (leaf z.1 i)
            (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P i))) = false} =
      selectorLaw (SelectorAddress (selectorEndpoints W))
        {a | ∀ c : Node M d × Fin M,
          a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = value c} *
      (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - P.val.length)) := by
  classical
  have h := FixedScaleProbability.measure_fixed_scale_eq_atom_mass
    fairLaw (bitLaw p hp0 hp1)
    (by simpa only [one_div] using fairLaw_singleton false)
    (by simpa only [one_div] using fairLaw_singleton true)
    (fun c : Node M d × Fin M => selectorAddress (selectorEndpoints W) c.1 c.2 x)
    (localSelectorAddress W P x t) (center_local_sum_injective W P x t ht) value
    (fun a i => terminalAddress (terminalEndpoints W) (leaf a i)
      (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P i)))
    (fun a => localTerminalAddress_injective W P x t ht (leaf a) (hprefix a))
    p hp1 (bitLaw_false p hp0 hp1)
  simpa only [outcomeLaw, selectorLaw, terminalLaw, card_localTrial] using h

end Problem310.WindowTrialAddresses

end

end OAI

end

-- OpenAI source module: WindowExceptionalTransfer
section

namespace OAI

noncomputable section
namespace Problem310.WindowExceptionalTransfer

open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate CenterRouteExposure

variable {M d g r₀ : ℕ}

lemma local_depth (U : Node M d) (i : Fin M) :
    (U.val ++ [i.castSucc]).length + (d - (U.val.length + 1)) = d := by
  have h := U.property
  simp only [List.length_append, List.length_singleton]
  omega

/-- The actual local Boolean test, using the canonical tables and subtree router. -/
def localQ (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W))
    (i : Fin M) (y : ℝ) : Bool :=
  ω.1 (selectorAddress (selectorEndpoints W) U i y) &&
    ω.2 (terminalAddress (terminalEndpoints W)
      (localLeaf (selectorChoice (selectorEndpoints W) ω.1)
        (d - (U.val.length + 1)) (U.val ++ [i.castSucc]) (local_depth U i) y) y)

/-- Stability in precisely the selector-value form supplied by the canonical
window stability construction. -/
def StableAt (W : WindowData (M + 1) d g r₀) (x : ℝ) : Prop :=
  ∀ (P : Node M d) (i : Fin M) (n : ℕ),
    W.b (P.val ++ [i.castSucc]) + g < n →
    ∀ t ∈ Set.Icc (1 : ℝ) 2, ∀ ω : SelectorTable (selectorEndpoints W),
      selectorValue (selectorEndpoints W) ω P.val i x =
        selectorValue (selectorEndpoints W) ω P.val i (x + t * (2 : ℝ)⁻¹ ^ n)

lemma localQ_mem_routedSet (W : WindowData (M + 1) d g r₀)
    (U : Node M d) (k : ℕ) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W))
    (hU : routeFrom (selectorChoice (selectorEndpoints W) ω.1) k [] x = U.val)
    (hdefault : selectorChoice (selectorEndpoints W) ω.1 U.val x = Fin.last M)
    (hprior : ∀ l < k, selectorChoice (selectorEndpoints W) ω.1
      (routeFrom (selectorChoice (selectorEndpoints W) ω.1) l [] x) x ≠ Fin.last M)
    (hstable : StableAt W x) (i : Fin M) (n : ℕ)
    (hn : W.a (U.val ++ [i.castSucc]) ≤ n)
    (hq : localQ W U ω i (x + t * (2 : ℝ)⁻¹ ^ n) = true) :
    x + t * (2 : ℝ)⁻¹ ^ n ∈ routedSet (selectorEndpoints W) (terminalEndpoints W) ω := by
  have hlen : k = U.val.length := by
    have h := congrArg List.length hU
    simpa using h
  have hk : k < d := by rw [hlen]; exact U.property
  apply FiniteLocalHit.local_test_mem_routedSet (selectorEndpoints W) (terminalEndpoints W)
    ω.1 ω.2 k (d - (U.val.length + 1)) U i x (x + t * (2 : ℝ)⁻¹ ^ n)
    (local_depth U i) hU hprior ?_ hdefault ?_ hq
  · intro l hl j hj
    have hP : (routeFrom (selectorChoice (selectorEndpoints W) ω.1) l [] x).length < d := by
      simpa using hl.trans hk
    apply hstable ⟨_, hP⟩ j n ?_ t ht ω.1
    have hgap := WindowLocalHit.ancestor_selector_gap W
      (selectorChoice (selectorEndpoints W) ω.1) x hl hk i.castSucc j.castSucc hj
    rw [hU] at hgap
    exact hgap.trans_le hn
  · intro j hj
    apply hstable U j n ?_ t ht ω.1
    have hgap := W.gap_sibling U.val j.castSucc i.castSucc []
      (by simpa using hj) (selectorEdge_valid U j) (selectorEdge_valid U i)
    exact hgap.trans_le hn

/-- Raw exceptional failure on a fixed good center atom transfers to one finite
representative scale at which every actual local Boolean trial fails. -/
theorem exists_representatives_failure_transfer
    (W : WindowData (M + 1) d g r₀) (U : Node M d) (k : ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool)
    (hfirst : ∀ ω : SelectorTable (selectorEndpoints W),
      centerExposure (selectorEndpoints W) x ω = ξ →
      routeFrom (selectorChoice (selectorEndpoints W) ω) k [] x = U.val ∧
      selectorChoice (selectorEndpoints W) ω U.val x = Fin.last M ∧
      ∀ l < k, selectorChoice (selectorEndpoints W) ω
        (routeFrom (selectorChoice (selectorEndpoints W) ω) l [] x) x ≠ Fin.last M)
    (hstable : StableAt W x) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W),
        centerExposure (selectorEndpoints W) x ω.1 = ξ →
        x ∈ Auxiliary.exceptionalCenters
          (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
          (Set.Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n) →
        ∃ t ∈ R, ∀ (i : Fin M) (j : Fin (W.r (d - U.val.length))),
          localQ W U ω i
            (x + t * (2 : ℝ)⁻¹ ^ (W.a (U.val ++ [i.castSucc]) + j.val)) = false := by
  obtain ⟨R, hR, hcard, hrep⟩ := WindowLocalFactor.exists_concrete_local_representatives
    W U x (selectorChoice (selectorEndpoints W))
    (fun _ => OrderedRouting.chooseChild) (fun _ _ _ => rfl)
    (d - (U.val.length + 1)) (local_depth U) (localQ W U) (fun _ _ _ => rfl)
  refine ⟨R, hR, hcard, ?_⟩
  intro ω hω hfail
  obtain ⟨t, ht, havoid⟩ := hfail
  obtain ⟨t', ht', heq⟩ := hrep t ht
  refine ⟨t', ht', ?_⟩
  intro i j
  rw [heq ω i j]
  obtain ⟨hU, hdefault, hprior⟩ := hfirst ω.1 hω
  have hn : 1 ≤ W.a (U.val ++ [i.castSucc]) + j.val := by
    have h : 3 ≤ W.a (U.val ++ [i.castSucc]) := W.start_three _ (selectorEdge_valid U i)
    omega
  cases hq : localQ W U ω i
      (x + t * (2 : ℝ)⁻¹ ^ (W.a (U.val ++ [i.castSucc]) + j.val)) with
  | false => rfl
  | true =>
    exact False.elim (havoid _ hn
      (localQ_mem_routedSet W U k x t ht ω hU hdefault hprior hstable i _
        (Nat.le_add_right _ _) hq))

end Problem310.WindowExceptionalTransfer

end

end OAI

end

-- OpenAI source module: CenterNoDefaultMass
section

namespace OAI

noncomputable section

namespace Problem310.CenterFailureBound

open Set MeasureTheory FiniteTableModel CenterRouteExposure RoutedSetDensity

/-- The atom-averaging bad event and the spatial router's no-default event
are identical, including their terminal-table coordinate. -/
theorem noDefaultEvent_eq_spatial {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ) (x : ℝ) :
    noDefaultEvent bS bT x =
      {ω : SelectorTable bS × TerminalTable bT | ∀ k < d,
        selectorChoice bS ω.1
          (RoutingPath.routeFrom (selectorChoice bS ω.1) k [] x) x ≠ Fin.last M} := by
  ext ω
  simp only [noDefaultEvent, Set.mem_ofPred_eq,
    RoutedExposure.routedPath_eq_centerRoute,
    RoutedExposure.selectorChoice_eq_centerChoice]

/-- Exact mass of the bad event in the concrete center-atom averaging theorem.
No probability or independence premises remain. -/
theorem outcomeLaw_noDefaultEvent {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
      (noDefaultEvent bS bT x) = (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  rw [noDefaultEvent_eq_spatial]
  exact outcomeLaw_no_default_steps bS bT p hp0 hp1 x

/-- Concrete raw-failure assembly: only the numeric depth budget and the
per-good-atom local-trial estimate are required. -/
theorem raw_failure_le_of_outcome_center_atoms {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (B : SelectorTable bS × TerminalTable bT → Set ℝ) (N : Set ℕ) (x : ℝ)
    (htail : (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d ≤ ENNReal.ofReal p)
    (hatom : ∀ ξ : Node M d × Fin M → Bool, GoodExposure bS x ξ →
      ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
        ({ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
          centerAtom bS bT x ξ) ≤
        ENNReal.ofReal p *
          ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
            (centerAtom bS bT x ξ)) :
    ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1
      {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ≤
      ENNReal.ofReal (2 * p) := by
  apply raw_failure_le_of_center_atoms bS bT
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
    p hp0 B N x _ hatom
  rw [outcomeLaw_noDefaultEvent]
  exact htail

end Problem310.CenterFailureBound

end

end OAI

end

-- OpenAI source module: ConcreteWindowAtom
section

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Problem310.ConcreteWindowAtom

open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate
open CenterRouteExposure CenterFailureBound WindowExceptionalTransfer WindowTrialAddresses

variable {M d g r₀ : ℕ}

/-- The concrete center atom together with all child-window trial misses. -/
def localMiss (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (x t : ℝ) (ξ : Node M d × Fin M → Bool) :
    Set (SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W)) :=
  {ω | centerExposure (selectorEndpoints W) x ω.1 = ξ ∧
    ∀ z : LocalTrial W U, localQ W U ω z.1
      (x + t * (2 : ℝ)⁻¹ ^ localIndex W U z) = false}

lemma centerAtom_mass (W : WindowData (M + 1) d g r₀)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ)
    (ξ : Node M d × Fin M → Bool) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1
      (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) =
    ConcreteLabels.selectorLaw (SelectorAddress (selectorEndpoints W))
      {a | ∀ c : Node M d × Fin M,
        a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = ξ c} := by
  have heq : centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ =
      ({a : SelectorTable (selectorEndpoints W) | ∀ c : Node M d × Fin M,
        a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = ξ c} ×ˢ
        (Set.univ : Set (TerminalTable (terminalEndpoints W)))) := by
    ext ω
    simp only [centerAtom, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
    exact funext_iff
  rw [heq, ConcreteLabels.outcomeLaw, Measure.prod_prod]
  simp

/-- Exact mass of the actual local Boolean failure event, with no remaining
address-injectivity or leaf-prefix obligations. -/
theorem localMiss_mass (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ξ : Node M d × Fin M → Bool) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1 (localMiss W U x t ξ) =
    (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - U.val.length)) *
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp0 hp1
        (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) := by
  let leaf : SelectorTable (selectorEndpoints W) → LocalTrial W U → Leaf M d :=
    fun a z => localLeaf (selectorChoice (selectorEndpoints W) a)
      (d - (U.val.length + 1)) (U.val ++ [z.1.castSucc]) (local_depth U z.1)
      (x + t * (2 : ℝ)⁻¹ ^ localIndex W U z)
  have hprefix : ∀ a z, (selectorEdge U z.1).IsPrefix (leaf a z).val := by
    intro a z
    exact prefix_routeFrom _ _ _ _
  have h := window_fixed_scale_on_center_atom W U x t ht p hp0 hp1 ξ leaf hprefix
  have heq : localMiss W U x t ξ =
      {ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W) |
        (∀ c : Node M d × Fin M,
          ω.1 (selectorAddress (selectorEndpoints W) c.1 c.2 x) = ξ c) ∧
        ∀ z : LocalTrial W U, ω.1 (localSelectorAddress W U x t z) = true →
          ω.2 (terminalAddress (terminalEndpoints W) (leaf ω.1 z)
            (x + t * (2 : ℝ)⁻¹ ^ localIndex W U z)) = false} := by
    ext ω
    simp only [localMiss, Set.mem_ofPred_eq, funext_iff, centerExposure,
      localQ, Bool.and_eq_false_imp, localSelectorAddress, leaf]
  rw [heq, h, centerAtom_mass]
  exact mul_comm _ _

/-- The final good-atom bound for the actual window router. The only numerical
input is precisely the uniform entropy budget returned by RoutingBudget. -/
theorem raw_failure_on_good_atom
    (W : WindowData (M + 1) d g r₀) (hM : 1 ≤ M)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbudget : ∀ r : ℕ, r₀ ≤ r → ∀ N : ℕ,
      N ≤ 1 + M * r * 2 ^ (2 * r + 2) →
      (N : ENNReal) * (ENNReal.ofReal (1 - p / 2)) ^ (M * r) ≤ ENNReal.ofReal p)
    (x : ℝ) (hstable : StableAt W x)
    (ξ : Node M d × Fin M → Bool) (hgood : GoodExposure (selectorEndpoints W) x ξ) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1
      ({ω | x ∈ Auxiliary.exceptionalCenters
        (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
        (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
        centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) ≤
    ENNReal.ofReal p *
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp0 hp1
        (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) := by
  classical
  obtain ⟨k, U, hlen, hfirst⟩ :=
    RoutedExposure.actual_firstDefaultNode_on_atom (selectorEndpoints W) x ξ hgood
  obtain ⟨R, hR, hcard, htransfer⟩ :=
    exists_representatives_failure_transfer W U k.val x ξ hfirst hstable
  let μ := ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
    (TerminalAddress (terminalEndpoints W)) p hp0 hp1
  let A := centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ
  let q := (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - U.val.length))
  have hthreshold : r₀ ≤ W.r (d - U.val.length) := by
    have h := W.length_threshold (selectorEdge U (⟨0, by omega⟩ : Fin M))
      (selectorEdge_valid U _)
    simpa [WindowData.length, selectorEdge] using h
  have hsmall : (R.card : ENNReal) * q ≤ ENNReal.ofReal p :=
    hbudget _ hthreshold _ hcard
  have hsub : ({ω | x ∈ Auxiliary.exceptionalCenters
      (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
      (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ∩ A) ⊆
      ⋃ t ∈ R, localMiss W U x t ξ := by
    rintro ω ⟨hfail, hatom⟩
    obtain ⟨t, ht, hmiss⟩ := htransfer ω hatom hfail
    refine mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, hatom, ?_⟩⟩
    intro z
    exact hmiss z.1 z.2
  change μ _ ≤ ENNReal.ofReal p * μ A
  calc
    μ _ ≤ μ (⋃ t ∈ R, localMiss W U x t ξ) := measure_mono hsub
    _ ≤ ∑ t ∈ R, μ (localMiss W U x t ξ) := measure_biUnion_finset_le _ _
    _ = ∑ _t ∈ R, q * μ A := by
      apply Finset.sum_congr rfl
      intro t ht
      exact localMiss_mass W U x t (hR t ht) p hp0 hp1 ξ
    _ = (R.card : ENNReal) * (q * μ A) := by simp [nsmul_eq_mul]
    _ = ((R.card : ENNReal) * q) * μ A := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal p * μ A := mul_le_mul hsmall le_rfl (by positivity) (by positivity)

end Problem310.ConcreteWindowAtom

end

end OAI

end

-- OpenAI source module: Main
section

namespace OAI

noncomputable section

namespace Problem310

theorem periodic_hitting_set :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧ periodDensity H ≤ ENNReal.ofReal (6 * p) ∧ ∀ x t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧ x + t * dyadicPoint n ∈ H := by
  intro p hp hp1
  obtain ⟨M, d, R, hM, hd, hR, _, hsurvival, hbudget⟩ :=
    RoutingBudget.exists_nondefault_parameters p hp hp1
  obtain ⟨g, hg, hgeo⟩ := exists_windowData_selector_stability M d p hp
  let W := WindowConstruction.windowData (M + 1) d g R (by omega) hR
  obtain ⟨G, hG, hGp, hbad, hstable⟩ := hgeo R W
  apply Construction.periodic_hitting_of_window_failure W p hp hp1 G hG hbad
  intro x hx
  apply CenterFailureBound.raw_failure_le_of_outcome_center_atoms
    (FiniteTableModel.selectorEndpoints W) (FiniteTableModel.terminalEndpoints W)
    p hp.le hp1.le
    (RoutedSetDensity.routedSet (FiniteTableModel.selectorEndpoints W)
      (FiniteTableModel.terminalEndpoints W)) (Set.Ici 1) x
    (RoutingBudget.ennreal_survival_lt hp M d hsurvival).le
  intro ξ hξ
  apply ConcreteWindowAtom.raw_failure_on_good_atom W hM p hp.le hp1.le
    (fun r hr N hN => (hbudget r hr N hN).le) x ?_ ξ hξ
  intro P i n hn t ht ω
  exact (hstable x hx P i n hn t ht ω).symm

theorem dyadic_affine_avoidance :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧ MeasureTheory.volume E > ENNReal.ofReal (1 - η) ∧ ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * dyadicPoint n ∉ E := by
  exact Problem310Support.avoidance_of_periodic_hitting periodic_hitting_set

end Problem310

end

end OAI

end

theorem OMA.solution : type_of% @OMA.S_arxiv_2607_03584.main := by
  obtain ⟨E, _, hc, hv, ha⟩ := OAI.Problem310.dyadic_affine_avoidance (1/2) (by norm_num) (by norm_num)
  refine ⟨E, hc.measurableSet, lt_trans ?_ hv, ha⟩
  exact ENNReal.ofReal_pos.mpr (by norm_num)
