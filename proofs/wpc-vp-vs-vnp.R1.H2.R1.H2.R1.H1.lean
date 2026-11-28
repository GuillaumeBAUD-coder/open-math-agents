import OMAReductions.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1
/-! Adapted from OpenAI math@3344da59991ed94f9ba711217b29c1d760badfa6, OAI/Computability/VPVNP, Apache-2.0. Copyright OpenAI. -/
namespace OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1
open OMA.S_wpc_vp_vs_vnp MvPolynomial
open scoped Classical
def H1 : Prop := ∀ (K τ : Type) [Field K] (k : ℕ) (φ : List (List (Fin k × Bool))) (w : Fin k → τ ⊕ K), 0 < k →
  let m := (k * (3 * (φ.map List.length).sum + 4) + φ.length)
  ∃ ψ : Fin m × Fin m → τ ⊕ K, (eval₂Hom C (fun i => (ψ i).elim X C)) (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin m) => 0 < m ∧ π.IsCycleOn Set.univ), ∏ i, (X (i, π i) : MvPolynomial (Fin m × Fin m) K)) = (∑ x : Fin k → Bool, if ∀ c ∈ φ, c.countP (fun l => x l.1 == l.2) = 1 then ∏ i, if x i then (w i).elim X C else 1 else 0)
def H2 : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] [Countable K]
  (p : Family K (fun n => Fin n × Bool)), IsVNP p → ∃ e M : ℕ, ∀ n ≥ M,
  ∃ (k : ℕ) (φ : List (List (Fin k × Bool))) (w : Fin k → (Fin n × Bool) ⊕ K), 0 < k ∧ n ≤ (k * (3 * (φ.map List.length).sum + 4) + φ.length) ∧ (k * (3 * (φ.map List.length).sum + 4) + φ.length) ≤ n ^ e ∧ (∑ x : Fin k → Bool, if ∀ c ∈ φ, c.countP (fun l => x l.1 == l.2) = 1 then ∏ i, if x i then (w i).elim X C else 1 else 0) = p n
theorem project {K σ τ : Type} [Field K] (ψ : σ → τ ⊕ K) {s : ℕ} {p : MvPolynomial σ K} (h : Computes s p) : Computes s ((eval₂Hom C (fun i => (ψ i).elim X C)) p) := by
  obtain ⟨v, out, gates⟩ := h
  refine ⟨fun j => (eval₂Hom C (fun i => (ψ i).elim X C)) (v j), ?_, ?_⟩
  all_goals
    let av (j : ℕ) (q : MvPolynomial τ K) := (∃ i, X i = q) ∨ (∃ a, C a = q) ∨ ∃ i : Fin s, i.val < j ∧ (eval₂Hom C (fun i => (ψ i).elim X C)) (v i) = q
    have lift (j : ℕ) (q : MvPolynomial σ K) (hq : (∃ i, X i = q) ∨ (∃ a, C a = q) ∨ ∃ i : Fin s, i.val < j ∧ v i = q) : av j ((eval₂Hom C (fun i => (ψ i).elim X C)) q) := by
      rcases hq with ⟨i,rfl⟩ | ⟨a,rfl⟩ | ⟨i,hi,rfl⟩
      · cases hi : ψ i with
        | inl t => exact Or.inl ⟨t, by simp [hi]⟩
        | inr a => exact Or.inr (Or.inl ⟨a, by simp [hi]⟩)
      · exact Or.inr (Or.inl ⟨a, by simp⟩)
      · exact Or.inr (Or.inr ⟨i,hi,rfl⟩)
  · exact lift _ _ out
  · intro i
    obtain ⟨a,b,ha,hb,hop⟩ := gates i
    refine ⟨_,_,lift _ _ ha,lift _ _ hb,?_⟩
    rcases hop with hh | hh | hh <;> simp [hh]
theorem main : H1 → H2 → OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1.H1 := by
  intro h pres K _ _ _ p hp
  obtain ⟨e,M,H⟩ := pres K p hp
  refine ⟨e,M,fun n hn => ?_⟩
  obtain ⟨k,φ,w,hk,hlo,hhi,hw⟩ := H n hn
  obtain ⟨ψ,hψ⟩ := h K _ k φ w hk
  refine ⟨(k * (3 * (φ.map List.length).sum + 4) + φ.length),hlo,hhi,fun s hs => ?_⟩
  rw [← hw, ← hψ]
  exact project ψ hs
end OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1

/-! Adapted from OpenAI math@3344da59991ed94f9ba711217b29c1d760badfa6, OAI/Computability/VPVNP, Apache-2.0. Copyright OpenAI. -/

section



/-!
# Directed Hamiltonian-cycle graph for exact-one clauses

Each variable has a track with endpoints, one pair of ports per occurrence slot, and a
buffer between successive pairs. At the slot belonging to a literal, the directed
crossing for the literal's true value passes through its clause vertex. The opposite
crossing uses the edge between the ports.
-/

namespace GadgetOAI
namespace Computability
namespace VPVNP

namespace HCGadget

/-- The Hamiltonian reduction has a track for each variable, ports for literal occurrences,
separators between tracks, and one vertex per clause. -/
inductive Vertex (k h c : ℕ) where
  | sep (i : Fin k)
  | endpoint (i : Fin k) (side : Bool)
  | buffer (i : Fin k) (j : Fin (h + 1))
  | port (i : Fin k) (j : Fin h) (side : Bool)
  | clause (a : Fin c)
  deriving DecidableEq, Fintype

variable {k h c : ℕ}

/-- Left neighbor of a buffer in the linear order on its track. -/
def prevPort (i : Fin k) (j : Fin (h + 1)) : Vertex k h c :=
  Fin.cases (.endpoint i false) (fun s => .port i s true) j

/-- Right neighbor of a buffer in the linear order on its track. -/
def nextPort (i : Fin k) (j : Fin (h + 1)) : Vertex k h c :=
  Fin.lastCases (.endpoint i true) (fun s => .port i s false) j

/-- Each port has exactly one adjacent buffer along its track. -/
def portBuffer (i : Fin k) (j : Fin h) (b : Bool) : Vertex k h c :=
  .buffer i (if b then j.succ else j.castSucc)

@[simp] theorem prevPort_zero (i : Fin k) : prevPort (h := h) (c := c) i 0 = .endpoint i false := rfl

@[simp] theorem prevPort_succ (i : Fin k) (j : Fin h) :
    prevPort (c := c) i j.succ = .port i j true := by simp [prevPort]

@[simp] theorem nextPort_last (i : Fin k) :
    nextPort (c := c) i (Fin.last h) = .endpoint i true := by simp [nextPort]

@[simp] theorem nextPort_castSucc (i : Fin k) (j : Fin h) :
    nextPort (c := c) i j.castSucc = .port i j false := by simp [nextPort]

/-- Allowed directed edges. The occurrence data give the variable, clause and
satisfying variable value of each slot. -/
inductive Allowed (occ : Fin h → Fin k × Fin c × Bool) : Vertex k h c → Vertex k h c → Prop
  | bufferPrev (i : Fin k) (j : Fin (h + 1)) : Allowed occ (.buffer i j) (prevPort i j)
  | prevBuffer (i : Fin k) (j : Fin (h + 1)) : Allowed occ (prevPort i j) (.buffer i j)
  | bufferNext (i : Fin k) (j : Fin (h + 1)) : Allowed occ (.buffer i j) (nextPort i j)
  | nextBuffer (i : Fin k) (j : Fin (h + 1)) : Allowed occ (nextPort i j) (.buffer i j)
  | enterTrack (i : Fin k) (b : Bool) : Allowed occ (.sep i) (.endpoint i b)
  | exitTrack (i : Fin k) (b : Bool) : Allowed occ (.endpoint i b) (.sep (finRotate k i))
  | cross (i : Fin k) (j : Fin h) (b : Bool) (inactive : (occ j).1 ≠ i ∨ (occ j).2.2 = b) :
      Allowed occ (.port i j b) (.port i j (!b))
  | enterClause (j : Fin h) : Allowed occ (.port (occ j).1 j (!(occ j).2.2)) (.clause (occ j).2.1)
  | exitClause (j : Fin h) : Allowed occ (.clause (occ j).2.1) (.port (occ j).1 j (occ j).2.2)

/-- The graph uses polynomially many vertices, including for empty occurrence lists. -/
theorem card_vertex (k h c : ℕ) : Fintype.card (Vertex k h c) = k * (3 * h + 4) + c := by
  rw [← Fintype.card_congr (proxy_equiv% (Vertex k h c))]
  simp
  ring


variable {occ : Fin h → Fin k × Fin c × Bool}
variable {i : Fin k} {j : Fin (h + 1)} {a : Fin c} {v : Vertex k h c}

private def isPortOrEndpoint : Vertex k h c → Bool
  | .port .. | .endpoint .. => true
  | _ => false

private theorem prevPort_kind (i : Fin k) (j : Fin (h + 1)) :
    isPortOrEndpoint (prevPort (c := c) i j) = true := by
  cases j using Fin.cases <;> simp [isPortOrEndpoint]

private theorem nextPort_kind (i : Fin k) (j : Fin (h + 1)) :
    isPortOrEndpoint (nextPort (c := c) i j) = true := by
  cases j using Fin.lastCases <;> simp [isPortOrEndpoint]

private theorem ne_prevPort_of_kind_false (u : Vertex k h c) (i : Fin k)
    (j : Fin (h + 1)) (hu : isPortOrEndpoint u = false) : u ≠ prevPort i j := by
  intro e
  have he := congrArg isPortOrEndpoint e
  simp only [hu, prevPort_kind] at he
  contradiction

private theorem ne_nextPort_of_kind_false (u : Vertex k h c) (i : Fin k)
    (j : Fin (h + 1)) (hu : isPortOrEndpoint u = false) : u ≠ nextPort i j := by
  intro e
  have he := congrArg isPortOrEndpoint e
  simp only [hu, nextPort_kind] at he
  contradiction

theorem allowed_from_buffer_iff :
    Allowed occ (.buffer i j) v ↔ v = prevPort i j ∨ v = nextPort i j := by
  constructor
  · intro e
    generalize hv : Vertex.buffer i j = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro (rfl | rfl)
    · exact .bufferPrev i j
    · exact .bufferNext i j

theorem allowed_to_buffer_iff :
    Allowed occ v (.buffer i j) ↔ v = prevPort i j ∨ v = nextPort i j := by
  constructor
  · intro e
    generalize hv : Vertex.buffer i j = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro (rfl | rfl)
    · exact .prevBuffer i j
    · exact .nextBuffer i j

theorem allowed_from_sep_iff :
    Allowed occ (.sep i) v ↔ ∃ b, v = .endpoint i b := by
  constructor
  · intro e
    generalize hv : Vertex.sep i = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro ⟨b, rfl⟩
    exact .enterTrack i b

theorem allowed_to_sep_iff :
    Allowed occ v (.sep i) ↔ ∃ b, v = .endpoint ((finRotate k).symm i) b := by
  constructor
  · intro e
    generalize hv : Vertex.sep i = u at e
    cases e <;> (try simp_all [-finRotate_apply, -finRotate_symm_apply]) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro ⟨b, rfl⟩
    simpa only [Equiv.apply_symm_apply] using Allowed.exitTrack (occ := occ) ((finRotate k).symm i) b

theorem allowed_from_clause_iff :
    Allowed occ (.clause a) v ↔ ∃ j, (occ j).2.1 = a ∧ v = .port (occ j).1 j (occ j).2.2 := by
  constructor
  · intro e
    generalize hv : Vertex.clause a = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro ⟨j, rfl, rfl⟩
    exact .exitClause j

theorem allowed_to_clause_iff :
    Allowed occ v (.clause a) ↔ ∃ j, (occ j).2.1 = a ∧ v = .port (occ j).1 j (!(occ j).2.2) := by
  constructor
  · intro e
    generalize hv : Vertex.clause a = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro ⟨j, rfl, rfl⟩
    exact .enterClause j

end HCGadget

end VPVNP
end Computability
end GadgetOAI

end

section



/-!
# Directed traversal determined by an exact-one assignment

The bit of each variable orients its entire track. At a satisfied occurrence
the traversal visits the clause vertex, then continues at the other port of
the same slot. The unique satisfied occurrence determines the outgoing arc
from each clause.
-/

namespace GadgetOAI
namespace Computability
namespace VPVNP

namespace HCGadget

open Equiv

variable {k h c : ℕ}
variable (occ : Fin h → Fin k × Fin c × Bool) (x : Fin k → Bool)

/-- Occurrences are distinct slots, including repeated literals within a clause. -/
def Exact : Prop :=
  ∀ a : Fin c, ∃! j : Fin h, (occ j).2.1 = a ∧ x (occ j).1 = (occ j).2.2

variable (hx : Exact occ x)

/-- The unique satisfied occurrence at the clause. -/
noncomputable def chosen (a : Fin c) : Fin h := (hx a).exists.choose

theorem chosen_spec (a : Fin c) :
    (occ (chosen occ x hx a)).2.1 = a ∧
      x (occ (chosen occ x hx a)).1 = (occ (chosen occ x hx a)).2.2 :=
  (hx a).exists.choose_spec

theorem chosen_eq {a : Fin c} {j : Fin h}
    (hj : (occ j).2.1 = a ∧ x (occ j).1 = (occ j).2.2) : chosen occ x hx a = j :=
  (hx a).unique (chosen_spec occ x hx a) hj

/-- The next vertex along the cycle specified by the assignment. -/
noncomputable def nextVertex : Vertex k h c → Vertex k h c
  | .sep i => .endpoint i (!x i)
  | .endpoint i b => if b = x i then .sep (finRotate k i)
      else .buffer i (if b then Fin.last h else 0)
  | .buffer i j => if x i then nextPort i j else prevPort i j
  | .port i j b => if b = x i then portBuffer i j b
      else if (occ j).1 = i ∧ (occ j).2.2 = x i then .clause (occ j).2.1
      else .port i j (x i)
  | .clause a =>
    let j := chosen occ x hx a
    .port (occ j).1 j (occ j).2.2

theorem nextVertex_prevPort {i : Fin k} (hi : x i = true) (j : Fin (h + 1)) :
    nextVertex occ x hx (prevPort i j) = .buffer i j := by
  cases j using Fin.cases <;> simp [nextVertex, hi, portBuffer]

theorem nextVertex_nextPort {i : Fin k} (hi : x i = false) (j : Fin (h + 1)) :
    nextVertex occ x hx (nextPort i j) = .buffer i j := by
  cases j using Fin.lastCases <;> simp [nextVertex, hi, portBuffer]

theorem nextVertex_ingress (i : Fin k) (j : Fin h) :
    nextVertex occ x hx (.port i j (!x i)) =
      if (occ j).1 = i ∧ (occ j).2.2 = x i then .clause (occ j).2.1 else .port i j (x i) := by
  cases hi : x i <;> simp [nextVertex, hi]

theorem nextVertex_clause_of_active {i : Fin k} {j : Fin h}
    (ha : (occ j).1 = i ∧ (occ j).2.2 = x i) :
    nextVertex occ x hx (.clause (occ j).2.1) = .port i j (x i) := by
  have hc := chosen_eq occ x hx (a := (occ j).2.1) (j := j) ⟨rfl, by rw [ha.1, ha.2]⟩
  simp [nextVertex, hc, ha.1, ha.2]

theorem nextVertex_surjective : Function.Surjective (nextVertex occ x hx) := by
  intro v
  cases v with
  | sep i =>
    let q := (finRotate k).symm i
    exact ⟨.endpoint q (x q), by simp only [nextVertex, ite_true, q, Equiv.apply_symm_apply]⟩
  | endpoint i b =>
    cases hb : b <;> cases hi : x i
    · exact ⟨.buffer i 0, by simp [nextVertex, hi]⟩
    · exact ⟨.sep i, by simp [nextVertex, hi]⟩
    · exact ⟨.sep i, by simp [nextVertex, hi]⟩
    · exact ⟨.buffer i (Fin.last h), by simp [nextVertex, hi]⟩
  | buffer i j =>
    cases hi : x i with
    | false => exact ⟨nextPort i j, nextVertex_nextPort occ x hx hi j⟩
    | true => exact ⟨prevPort i j, nextVertex_prevPort occ x hx hi j⟩
  | port i j b =>
    by_cases hb : b = x i
    · subst b
      by_cases ha : (occ j).1 = i ∧ (occ j).2.2 = x i
      · exact ⟨.clause (occ j).2.1, nextVertex_clause_of_active occ x hx ha⟩
      · exact ⟨.port i j (!x i), by rw [nextVertex_ingress, if_neg ha]⟩
    · cases b <;> cases hi : x i <;> simp [hi] at hb
      · exact ⟨.buffer i j.castSucc, by simp [nextVertex, hi]⟩
      · exact ⟨.buffer i j.succ, by simp [nextVertex, hi]⟩
  | clause a =>
    let j := chosen occ x hx a
    obtain ⟨hc, hp⟩ := chosen_spec occ x hx a
    refine ⟨.port (occ j).1 j (!x (occ j).1), ?_⟩
    rw [nextVertex_ingress, if_pos ⟨rfl, hp.symm⟩, hc]

/-- The traversal uses every vertex once as a successor. -/
noncomputable def cycleOfAssignment : Perm (Vertex k h c) :=
  Equiv.ofBijective (nextVertex occ x hx)
    ⟨Finite.injective_iff_surjective.mpr (nextVertex_surjective occ x hx),
      nextVertex_surjective occ x hx⟩

@[simp] theorem cycleOfAssignment_apply (v : Vertex k h c) :
    cycleOfAssignment occ x hx v = nextVertex occ x hx v := rfl

theorem nextVertex_allowed (v : Vertex k h c) :
    Allowed occ v (nextVertex occ x hx v) := by
  cases v with
  | sep i => exact .enterTrack _ _
  | endpoint i b =>
    by_cases hb : b = x i
    · simpa [nextVertex, hb] using Allowed.exitTrack (occ := occ) i b
    · cases b
      · simpa [nextVertex, hb] using Allowed.prevBuffer (occ := occ) i (0 : Fin (h + 1))
      · simpa [nextVertex, hb] using Allowed.nextBuffer (occ := occ) i (Fin.last h)
  | buffer i j =>
    cases hi : x i
    · simpa [nextVertex, hi] using Allowed.bufferPrev (occ := occ) i j
    · simpa [nextVertex, hi] using Allowed.bufferNext (occ := occ) i j
  | port i j b =>
    by_cases hb : b = x i
    · rw [nextVertex, if_pos hb]
      cases b
      · simpa [portBuffer] using Allowed.nextBuffer (occ := occ) i j.castSucc
      · simpa [portBuffer] using Allowed.prevBuffer (occ := occ) i j.succ
    · have hn : (!b) = x i := by cases b <;> cases hi : x i <;> simp [hi] at *
      by_cases ha : (occ j).1 = i ∧ (occ j).2.2 = x i
      · have hs : (!(occ j).2.2) = b := by rw [ha.2, ← hn]; simp
        rw [nextVertex, if_neg hb, if_pos ha]
        have he := Allowed.enterClause (occ := occ) j
        rw [ha.1, hs] at he
        exact he
      · have inactive : (occ j).1 ≠ i ∨ (occ j).2.2 = b := by
          by_cases he : (occ j).1 = i
          · right
            have hs : (occ j).2.2 ≠ x i := fun H => ha ⟨he, H⟩
            cases b <;> cases hp : (occ j).2.2 <;> cases hi : x i <;> simp [hi, hp] at *
          · exact Or.inl he
        simpa [nextVertex, hb, ha, hn] using Allowed.cross (occ := occ) i j b inactive
  | clause a =>
    have he := Allowed.exitClause (occ := occ) (chosen occ x hx a)
    rw [(chosen_spec occ x hx a).1] at he
    exact he

end HCGadget

end VPVNP
end Computability
end GadgetOAI

end

section


/-!
# Connectivity of the directed Hamiltonian-cycle gadget

If each pair of ports and each buffer belongs to the same permutation cycle as its
neighbors, the whole variable track lies in one cycle. The separators join the tracks
in cyclic order, and a single incident port suffices to attach each clause.
-/

namespace GadgetOAI
namespace Computability
namespace VPVNP

namespace HCGadget

open Equiv.Perm

variable {k h c : ℕ}

/-- The local connectivity conditions for variable tracks, separators and clause
vertices suffice to make the permutation a Hamiltonian cycle. -/
theorem isCycleOn_of_track_connections (π : Equiv.Perm (Vertex k h c)) (hk : 0 < k)
    (buffers : ∀ i j, π.SameCycle (prevPort i j) (.buffer i j) ∧
      π.SameCycle (.buffer i j) (nextPort i j))
    (pairs : ∀ i j, π.SameCycle (.port i j false) (.port i j true))
    (entries : ∀ i, ∃ b, π.SameCycle (.sep i) (.endpoint i b))
    (exits : ∀ i, ∃ b, π.SameCycle (.endpoint i b) (.sep (finRotate k i)))
    (clauses : ∀ a, ∃ i j b, π.SameCycle (.port i j b) (.clause a)) :
    π.IsCycleOn Set.univ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have toBuffer (i : Fin (k + 1)) (j : Fin (h + 1)) :
      π.SameCycle (.endpoint i false) (.buffer i j) := by
    induction j using Fin.induction with
    | zero => simpa using (buffers i 0).1
    | succ j ih =>
      have left : π.SameCycle (.buffer i j.castSucc) (.port i j false) := by
        simpa using (buffers i j.castSucc).2
      have right : π.SameCycle (.port i j true) (.buffer i j.succ) := by
        simpa using (buffers i j.succ).1
      exact ((ih.trans left).trans (pairs i j)).trans right
  have toEndpoint (i : Fin (k + 1)) (b : Bool) :
      π.SameCycle (.endpoint i false) (.endpoint i b) := by
    cases b with
    | false => exact SameCycle.rfl
    | true => simpa using (toBuffer i (Fin.last h)).trans (buffers i (Fin.last h)).2
  have fromSep (i : Fin (k + 1)) : π.SameCycle (.sep i) (.endpoint i false) := by
    obtain ⟨b, hb⟩ := entries i
    exact hb.trans (toEndpoint i b).symm
  have toSep (i : Fin (k + 1)) : π.SameCycle (.sep 0) (.sep i) := by
    induction i using Fin.induction with
    | zero => exact SameCycle.rfl
    | succ i ih =>
      obtain ⟨b, hb⟩ := exits i.castSucc
      have rot : finRotate (k + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      rw [rot] at hb
      exact ((ih.trans (fromSep i.castSucc)).trans (toEndpoint i.castSucc b)).trans hb
  have track (i : Fin (k + 1)) : π.SameCycle (.sep 0) (.endpoint i false) :=
    (toSep i).trans (fromSep i)
  have port (i : Fin (k + 1)) (j : Fin h) (b : Bool) : π.SameCycle (.sep 0) (.port i j b) := by
    have left : π.SameCycle (.buffer i j.castSucc) (.port i j false) := by
      simpa using (buffers i j.castSucc).2
    have first := ((track i).trans (toBuffer i j.castSucc)).trans left
    cases b with
    | false => exact first
    | true => exact first.trans (pairs i j)
  have all (v : Vertex (k + 1) h c) : π.SameCycle (.sep 0) v := by
    cases v with
    | sep i => exact toSep i
    | endpoint i b => exact (track i).trans (toEndpoint i b)
    | buffer i j => exact (track i).trans (toBuffer i j)
    | port i j b => exact port i j b
    | clause a =>
      obtain ⟨i, j, b, hab⟩ := clauses a
      exact (port i j b).trans hab
  exact ⟨π.bijective.bijOn_univ, fun x _ y _ => (all x).symm.trans (all y)⟩

end HCGadget

end VPVNP
end Computability
end GadgetOAI

end

section



/-! The assignment traversal connects all track and clause vertices in one directed cycle. -/

namespace GadgetOAI
namespace Computability
namespace VPVNP

namespace HCGadget

open Equiv.Perm

variable {k h c : ℕ} (occ : Fin h → Fin k × Fin c × Bool) (x : Fin k → Bool) (hx : Exact occ x)

private theorem same_of_step {a b : Vertex k h c} (e : nextVertex occ x hx a = b) :
    (cycleOfAssignment occ x hx).SameCycle a b := by
  change cycleOfAssignment occ x hx a = b at e
  rw [← e]
  exact (SameCycle.refl _ _).apply_right

theorem cycleOfAssignment_buffers (i : Fin k) (j : Fin (h+1)) :
    (cycleOfAssignment occ x hx).SameCycle (prevPort i j) (.buffer i j) ∧
      (cycleOfAssignment occ x hx).SameCycle (.buffer i j) (nextPort i j) := by
  cases hi : x i with
  | false =>
    refine ⟨(same_of_step occ x hx ?_).symm,
      (same_of_step occ x hx (nextVertex_nextPort occ x hx hi j)).symm⟩
    simp [nextVertex, hi]
  | true =>
    refine ⟨same_of_step occ x hx (nextVertex_prevPort occ x hx hi j), same_of_step occ x hx ?_⟩
    simp [nextVertex, hi]

theorem cycleOfAssignment_slots (i : Fin k) (j : Fin h) :
    (cycleOfAssignment occ x hx).SameCycle (.port i j false) (.port i j true) := by
  have cross : (cycleOfAssignment occ x hx).SameCycle (.port i j (!x i)) (.port i j (x i)) := by
    by_cases ha : (occ j).1 = i ∧ (occ j).2.2 = x i
    · have hin : nextVertex occ x hx (.port i j (!x i)) = .clause (occ j).2.1 := by
        rw [nextVertex_ingress, if_pos ha]
      exact (same_of_step occ x hx hin).trans (same_of_step occ x hx (nextVertex_clause_of_active occ x hx ha))
    · exact same_of_step occ x hx (by rw [nextVertex_ingress, if_neg ha])
  cases hi : x i
  · simpa [hi] using cross.symm
  · simpa [hi] using cross

theorem cycleOfAssignment_enter (i : Fin k) :
    ∃ b, (cycleOfAssignment occ x hx).SameCycle (.sep i) (.endpoint i b) :=
  ⟨!x i, same_of_step occ x hx rfl⟩

theorem cycleOfAssignment_exit (i : Fin k) :
    ∃ b, (cycleOfAssignment occ x hx).SameCycle (.endpoint i b) (.sep (finRotate k i)) :=
  ⟨x i, same_of_step occ x hx (by simp [nextVertex])⟩

theorem cycleOfAssignment_clauses (a : Fin c) :
    ∃ i j b, (cycleOfAssignment occ x hx).SameCycle (.port i j b) (.clause a) := by
  let j := chosen occ x hx a
  have hc := chosen_spec occ x hx a
  refine ⟨(occ j).1, j, !x (occ j).1, same_of_step occ x hx ?_⟩
  rw [nextVertex_ingress, if_pos ⟨rfl, hc.2.symm⟩, hc.1]

/-- Every exact-one assignment yields a spanning directed cycle using allowed arcs. -/
theorem cycleOfAssignment_spanning (hk : 0 < k) :
    (cycleOfAssignment occ x hx).IsCycleOn Set.univ :=
  isCycleOn_of_track_connections _ hk (cycleOfAssignment_buffers occ x hx)
    (cycleOfAssignment_slots occ x hx) (cycleOfAssignment_enter occ x hx)
    (cycleOfAssignment_exit occ x hx) (cycleOfAssignment_clauses occ x hx)

end HCGadget

end VPVNP
end Computability
end GadgetOAI

end

section


/-! # Port neighborhoods of the exact-one Hamiltonian-cycle graph -/

namespace GadgetOAI
namespace Computability
namespace VPVNP

namespace HCGadget

variable {k h c : ℕ} {occ : Fin h → Fin k × Fin c × Bool}

private theorem prevPort_buffer {i i' : Fin k} {j : Fin h} {b : Bool}
    (t : Fin (h + 1)) (he : prevPort (c := c) i' t = .port i j b) :
    .buffer i' t = portBuffer (c := c) i j b := by
  induction t using Fin.cases with
  | zero => simp at he
  | succ t => simp only [prevPort_succ, Vertex.port.injEq] at he; rcases he with ⟨rfl,rfl,rfl⟩; rfl

private theorem nextPort_buffer {i i' : Fin k} {j : Fin h} {b : Bool}
    (t : Fin (h + 1)) (he : nextPort (c := c) i' t = .port i j b) :
    .buffer i' t = portBuffer (c := c) i j b := by
  induction t using Fin.lastCases with
  | last => simp at he
  | cast t => simp only [nextPort_castSucc, Vertex.port.injEq] at he; rcases he with ⟨rfl,rfl,rfl⟩; rfl

theorem Allowed.from_port {i : Fin k} {j : Fin h} {b : Bool} {v : Vertex k h c}
    (edge : Allowed occ (.port i j b) v) :
    v = portBuffer i j b ∨ (v = .port i j (!b) ∧ ((occ j).1 ≠ i ∨ (occ j).2.2 = b)) ∨
      (v = .clause (occ j).2.1 ∧ (occ j).1 = i ∧ b = !(occ j).2.2) := by
  generalize hs : Vertex.port i j b = u at edge
  cases edge with
  | prevBuffer i' t => exact Or.inl (prevPort_buffer t hs.symm)
  | nextBuffer i' t => exact Or.inl (nextPort_buffer t hs.symm)
  | cross i' j' b' hcross => cases hs; exact Or.inr (Or.inl ⟨rfl, hcross⟩)
  | enterClause j' => cases hs; simp
  | _ => cases hs

theorem Allowed.to_port {i : Fin k} {j : Fin h} {b : Bool} {u : Vertex k h c}
    (edge : Allowed occ u (.port i j b)) :
    u = portBuffer i j b ∨ (u = .port i j (!b) ∧ ((occ j).1 ≠ i ∨ (occ j).2.2 = !b)) ∨
      (u = .clause (occ j).2.1 ∧ (occ j).1 = i ∧ b = (occ j).2.2) := by
  generalize hs : Vertex.port i j b = v at edge
  cases edge with
  | bufferPrev i' t => exact Or.inl (prevPort_buffer t hs.symm)
  | bufferNext i' t => exact Or.inl (nextPort_buffer t hs.symm)
  | cross i' j' b' hcross => cases hs; exact Or.inr (Or.inl (by simpa using hcross))
  | exitClause j' => cases hs; simp
  | _ => cases hs

/-- The buffer next to an endpoint, indexed by its side of the track. -/
def endpointBuffer (i : Fin k) (b : Bool) : Vertex k h c :=
  .buffer i (if b then Fin.last h else 0)

private theorem prevEndpoint_buffer {i i' : Fin k} {b : Bool}
    (t : Fin (h + 1)) (he : prevPort (c := c) i' t = .endpoint i b) :
    .buffer i' t = endpointBuffer (c := c) i b := by
  induction t using Fin.cases with
  | zero => simp only [prevPort_zero, Vertex.endpoint.injEq] at he; rcases he with ⟨rfl,rfl⟩; rfl
  | succ t => simp at he

private theorem nextEndpoint_buffer {i i' : Fin k} {b : Bool}
    (t : Fin (h + 1)) (he : nextPort (c := c) i' t = .endpoint i b) :
    .buffer i' t = endpointBuffer (c := c) i b := by
  induction t using Fin.lastCases with
  | last => simp only [nextPort_last, Vertex.endpoint.injEq] at he; rcases he with ⟨rfl,rfl⟩; rfl
  | cast t => simp at he

theorem Allowed.from_endpoint {i : Fin k} {b : Bool} {v : Vertex k h c}
    (edge : Allowed occ (.endpoint i b) v) :
    v = endpointBuffer i b ∨ v = .sep (finRotate k i) := by
  generalize hs : Vertex.endpoint i b = u at edge
  cases edge with
  | prevBuffer i' t => exact Or.inl (prevEndpoint_buffer t hs.symm)
  | nextBuffer i' t => exact Or.inl (nextEndpoint_buffer t hs.symm)
  | exitTrack i' b' => cases hs; exact Or.inr rfl
  | _ => cases hs

theorem Allowed.to_endpoint {i : Fin k} {b : Bool} {u : Vertex k h c}
    (edge : Allowed occ u (.endpoint i b)) : u = endpointBuffer i b ∨ u = .sep i := by
  generalize hs : Vertex.endpoint i b = v at edge
  cases edge with
  | bufferPrev i' t => exact Or.inl (prevEndpoint_buffer t hs.symm)
  | bufferNext i' t => exact Or.inl (nextEndpoint_buffer t hs.symm)
  | enterTrack i' b' => cases hs; exact Or.inr rfl
  | _ => cases hs

/-- The left and right neighbor of a buffer are distinct, including an empty track. -/
theorem prev_next_ne (i : Fin k) (t : Fin (h + 1)) :
    prevPort (c := c) i t ≠ nextPort i t := by
  suffices disjoint : ∀ l r : Fin (h + 1), prevPort (c := c) i l ≠ nextPort i r from disjoint t t
  intro l r
  induction l using Fin.cases <;> induction r using Fin.lastCases <;> simp

/-- A spanning permutation cannot contain a 2-cycle: a track has at least four vertices. -/
theorem no_two_cycle (π : Equiv.Perm (Vertex k h c)) (cycle : π.IsCycleOn Set.univ)
    (i : Fin k) (v : Vertex k h c) : π (π v) ≠ v := by
  intro hv
  have hcy : π.IsCycleOn (Finset.univ : Finset (Vertex k h c)) := by simpa using cycle
  have hdiv := (hcy.pow_apply_eq (Finset.mem_univ v) (n := 2)).mp
    (by simpa [pow_two] using hv)
  rw [Finset.card_univ, card_vertex] at hdiv
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  have hi : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hmul := Nat.le_mul_of_pos_left (3*h+4) hi
  omega

/-- A tour passes through each degree-two buffer from one side to the other. -/
theorem buffer_directions (π : Equiv.Perm (Vertex k h c)) (cycle : π.IsCycleOn Set.univ)
    (allowed : ∀ v, Allowed occ v (π v)) (i : Fin k) (t : Fin (h + 1)) :
    (π (.buffer i t) = nextPort i t ∧ π (prevPort i t) = .buffer i t) ∨
    (π (.buffer i t) = prevPort i t ∧ π (nextPort i t) = .buffer i t) := by
  obtain ⟨v, hv⟩ := π.surjective (.buffer i t)
  have he := allowed v
  rw [hv] at he
  have hin := allowed_to_buffer_iff.mp he
  have hout := allowed_from_buffer_iff.mp (allowed (.buffer i t))
  have hne := no_two_cycle π cycle i v
  rw [hv] at hne
  rcases hin with rfl | rfl
  · exact Or.inl ⟨hout.resolve_left hne, hv⟩
  · exact Or.inr ⟨hout.resolve_right hne, hv⟩

end HCGadget

end VPVNP
end Computability
end GadgetOAI

end

section



/-!
# Reading an assignment from a spanning cycle of the exact-one graph

At a buffer, the predecessor and successor must lie on opposite sides. Two
consecutive buffers must point in the same direction: otherwise both intervening
ports would have to send edges to the same clause vertex, or both would need
incoming edges from it. Thus a single bit determines the direction of each track.
-/

namespace GadgetOAI
namespace Computability
namespace VPVNP

namespace HCGadget

open Equiv

variable {k h c : ℕ} {occ : Fin h → Fin k × Fin c × Bool} {π : Perm (Vertex k h c)}

private theorem cannot_return (cyc : π.IsCycleOn Set.univ) (i : Fin k) {u v : Vertex k h c}
    (go : π u = v) : π v ≠ u := by
  simpa only [go] using no_two_cycle π cyc i u

private theorem allowed_predecessor (edge : ∀ v, Allowed occ v (π v)) (v : Vertex k h c) :
    Allowed occ (π.symm v) v := by simpa using edge (π.symm v)

private theorem no_two_incoming_buffers (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (i : Fin k) (j : Fin h)
    (arrive : ∀ b, π (portBuffer i j b) = .port i j b) : False := by
  have out (b : Bool) : π (.port i j b) = .clause (occ j).2.1 := by
    rcases (edge (.port i j b)).from_port with hb | ⟨hc, _⟩ | ⟨hcl, _⟩
    · exact (cannot_return cyc i (arrive b) hb).elim
    · have he := π.injective (hc.trans (arrive (!b)).symm)
      simp [portBuffer] at he
    · exact hcl
  have he := π.injective ((out false).trans (out true).symm)
  simp at he

private theorem no_two_outgoing_buffers (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (i : Fin k) (j : Fin h)
    (depart : ∀ b, π (.port i j b) = portBuffer i j b) : False := by
  have src (b : Bool) : π.symm (.port i j b) = .clause (occ j).2.1 := by
    rcases (allowed_predecessor edge (.port i j b)).to_port with hb | ⟨hc, _⟩ | ⟨hcl, _⟩
    · have hback := (π.symm_apply_eq.mp hb).symm
      exact (cannot_return cyc i (depart b) hback).elim
    · have he := (π.symm_apply_eq.mp hc).trans (depart (!b))
      simp [portBuffer] at he
    · exact hcl
  have he := π.symm.injective ((src false).trans (src true).symm)
  simp at he

/-- The two edges of a cycle incident to a buffer have the direction indicated
by the variable bit. -/
private def trackDirection (π : Perm (Vertex k h c)) (i : Fin k) (j : Fin (h + 1))
    (bit : Bool) : Prop :=
  if bit then π (.buffer i j) = nextPort i j ∧ π (prevPort i j) = .buffer i j
  else π (.buffer i j) = prevPort i j ∧ π (nextPort i j) = .buffer i j

private theorem trackDirection_step (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (i : Fin k) (j : Fin h) (bit : Bool)
    (here : trackDirection π i j.castSucc bit)
    (options : trackDirection π i j.succ true ∨ trackDirection π i j.succ false) :
    trackDirection π i j.succ bit := by
  cases bit with
  | false =>
    rcases options with right | left
    · have dep : ∀ b, π (.port i j b) = portBuffer i j b := by
        intro b
        cases b
        · simpa [portBuffer] using (show _ ∧ _ from here).2
        · simpa [portBuffer] using (show _ ∧ _ from right).2
      exact (no_two_outgoing_buffers cyc edge i j dep).elim
    · exact left
  | true =>
    rcases options with right | left
    · exact right
    · have arr : ∀ b, π (portBuffer i j b) = .port i j b := by
        intro b
        cases b
        · simpa [portBuffer] using (show _ ∧ _ from here).1
        · simpa [portBuffer] using (show _ ∧ _ from left).1
      exact (no_two_incoming_buffers cyc edge i j arr).elim

private theorem trackDirections (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) :
    ∃ x : Fin k → Bool, ∀ i t, trackDirection π i t (x i) := by
  classical
  have options (i : Fin k) (t : Fin (h + 1)) :
      trackDirection π i t true ∨ trackDirection π i t false :=
    buffer_directions π cyc edge i t
  let x (i : Fin k) := decide (trackDirection π i 0 true)
  refine ⟨x, fun i t => ?_⟩
  induction t using Fin.induction with
  | zero =>
    by_cases hi : trackDirection π i 0 true
    · simp [x, hi]
    · simpa [x, hi] using (options i 0).resolve_left hi
  | succ j ih =>
    exact trackDirection_step cyc edge i j (x i) ih (options i j.succ)

private theorem aligned_port_buffers {x : Fin k → Bool}
    (align : ∀ i t, trackDirection π i t (x i)) (i : Fin k) (j : Fin h) :
    π (portBuffer i j (!x i)) = .port i j (!x i) ∧
    π (.port i j (x i)) = portBuffer i j (x i) := by
  have left := align i j.castSucc
  have right := align i j.succ
  cases hx : x i <;> simp [trackDirection, hx] at left right <;> simp [portBuffer, left, right]

private theorem aligned_endpoint_buffers {x : Fin k → Bool}
    (align : ∀ i t, trackDirection π i t (x i)) (i : Fin k) :
    π (endpointBuffer i (x i)) = .endpoint i (x i) ∧
    π (.endpoint i (!x i)) = endpointBuffer i (!x i) := by
  have left := align i 0
  have right := align i (Fin.last h)
  cases hx : x i <;> simp [trackDirection, hx] at left right <;> simp [endpointBuffer, left, right]

private theorem aligned_ingress {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i))
    (i : Fin k) (j : Fin h) :
    π (.port i j (!x i)) =
      if (occ j).1 = i ∧ (occ j).2.2 = x i then .clause (occ j).2.1 else .port i j (x i) := by
  rcases (edge (.port i j (!x i))).from_port with hb | ⟨direct, hinactive⟩ | ⟨detour, hi, hb⟩
  · exact (cannot_return cyc i (aligned_port_buffers align i j).1 hb).elim
  · have h : ¬ ((occ j).1 = i ∧ (occ j).2.2 = x i) := by
      rintro ⟨hi, hb⟩
      rcases hinactive with hn | hn
      · exact hn hi
      · simp [hb] at hn
    simpa [h] using direct
  · have h : (occ j).1 = i ∧ (occ j).2.2 = x i := ⟨hi, by simpa using (congrArg Bool.not hb).symm⟩
    simpa [h] using detour

private theorem aligned_detour_exit {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i))
    (i : Fin k) (j : Fin h) (active : (occ j).1 = i ∧ (occ j).2.2 = x i) :
    π (.clause (occ j).2.1) = .port i j (x i) := by
  rcases (allowed_predecessor edge (.port i j (x i))).to_port with hb | ⟨cross, _⟩ | ⟨detour, _⟩
  · exact (cannot_return cyc i (aligned_port_buffers align i j).2
      (π.symm_apply_eq.mp hb).symm).elim
  · have depart := aligned_ingress cyc edge align i j
    rw [if_pos active] at depart
    have he := (π.symm_apply_eq.mp cross).trans depart
    cases he
  · exact (π.symm_apply_eq.mp detour).symm

private theorem aligned_track_end {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i))
    (i : Fin k) :
    π (.sep i) = .endpoint i (!x i) ∧ π (.endpoint i (x i)) = .sep (finRotate k i) := by
  obtain ⟨arrive, depart⟩ := aligned_endpoint_buffers align i
  constructor
  · rcases (allowed_predecessor edge (.endpoint i (!x i))).to_endpoint with hb | hs
    · exact (cannot_return cyc i depart (π.symm_apply_eq.mp hb).symm).elim
    · exact (π.symm_apply_eq.mp hs).symm
  · exact (edge (.endpoint i (x i))).from_endpoint.resolve_left (cannot_return cyc i arrive)

private theorem aligned_exact {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i)) :
    Exact occ x := by
  intro a
  obtain ⟨j, hcl, hpred⟩ := allowed_to_clause_iff.mp (allowed_predecessor edge (.clause a))
  have toClause := (π.symm_apply_eq.mp hpred).symm
  have active : x (occ j).1 = (occ j).2.2 := by
    by_contra h
    have he : (!(occ j).2.2) = x (occ j).1 := by
      cases ha : (occ j).2.2 <;> cases hx : x (occ j).1 <;> simp_all
    rw [he, (aligned_port_buffers align (occ j).1 j).2] at toClause
    cases toClause
  refine ⟨j, ⟨hcl, active⟩, ?_⟩
  rintro s ⟨hs, hv⟩
  have from_s := aligned_ingress cyc edge align (occ s).1 s
  rw [if_pos ⟨rfl, hv.symm⟩, hs] at from_s
  have he := π.injective (from_s.trans toClause.symm)
  exact (Vertex.port.inj he).2.1

private theorem read_aligned_cycle {x : Fin k → Bool} (cyc : π.IsCycleOn Set.univ)
    (edge : ∀ v, Allowed occ v (π v)) (align : ∀ i t, trackDirection π i t (x i))
    (exactly : Exact occ x) (v : Vertex k h c) : π v = nextVertex occ x exactly v := by
  cases v with
  | sep i => exact (aligned_track_end cyc edge align i).1
  | endpoint i b =>
    by_cases hb : b = x i
    · subst b
      simpa [nextVertex] using (aligned_track_end cyc edge align i).2
    · have he : b = !(x i) := by cases b <;> cases hx : x i <;> simp_all
      rw [nextVertex, if_neg hb, he]
      exact (aligned_endpoint_buffers align i).2
  | buffer i j =>
    have atBuffer := align i j
    cases hi : x i <;> simp [trackDirection, hi] at atBuffer <;> simp [nextVertex, hi, atBuffer]
  | port i j b =>
    by_cases hb : b = x i
    · subst b
      simpa [nextVertex] using (aligned_port_buffers align i j).2
    · have he : b = !(x i) := by cases b <;> cases hx : x i <;> simp_all
      rw [he, nextVertex_ingress]
      exact aligned_ingress cyc edge align i j
  | clause a =>
    let j := chosen occ x exactly a
    obtain ⟨hcl, hv⟩ := chosen_spec occ x exactly a
    have he := aligned_detour_exit cyc edge align (occ j).1 j ⟨rfl, hv.symm⟩
    change π (.clause a) = .port (occ j).1 j (occ j).2.2
    simpa only [j, hcl, hv] using he

/-- Every allowed spanning cycle is precisely the traversal constructed from
an assignment satisfying every exact-one constraint. -/
theorem exists_exact_assignment (cyc : π.IsCycleOn Set.univ) (edge : ∀ v, Allowed occ v (π v)) :
    ∃ (x : Fin k → Bool) (hx : Exact occ x), π = cycleOfAssignment occ x hx := by
  obtain ⟨x, align⟩ := trackDirections cyc edge
  let hx := aligned_exact cyc edge align
  exact ⟨x, hx, Equiv.ext (read_aligned_cycle cyc edge align hx)⟩

/-- The outgoing arc at each separator recovers its track bit, so distinct
satisfying assignments give distinct tours. -/
theorem cycleOfAssignment_injective (occ : Fin h → Fin k × Fin c × Bool) :
    Function.Injective (fun x : {x : Fin k → Bool // Exact occ x} =>
      cycleOfAssignment occ x.val x.property) := by
  intro x y he
  apply Subtype.ext
  funext i
  have e := Equiv.congr_fun he (.sep i)
  have hb := (Vertex.endpoint.inj (show Vertex.endpoint (h := h) (c := c) i (!(x.val i)) =
    .endpoint i (!(y.val i)) from e)).2
  simpa using congrArg Bool.not hb

end HCGadget

end VPVNP
end Computability
end GadgetOAI

end
namespace GadgetOAI.Computability.VPVNP
open MvPolynomial
noncomputable def spanningCycles (m : ℕ) : Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter (fun π => 0 < m ∧ π.IsCycleOn Set.univ)
noncomputable def hamiltonianCyclePolynomial (R : Type*) [CommSemiring R] (m : ℕ) :
    MvPolynomial (Fin m × Fin m) R :=
  ∑ π ∈ spanningCycles m, ∏ i, X (i, π i)
abbrev Projection (R σ τ : Type*) := σ → τ ⊕ R
noncomputable def Projection.hom {R σ τ : Type*} [CommSemiring R] (ψ : Projection R σ τ) : MvPolynomial σ R →+* MvPolynomial τ R :=
  eval₂Hom C (fun i => (ψ i).elim X C)
end GadgetOAI.Computability.VPVNP

section



/-!
# Weighted directed Hamiltonian cycles on a finite vertex type

Relabel the vertices by matrix indices, substitute zero on forbidden arcs, and
put the indicated variable or scalar on each allowed arc. In the resulting
formal polynomial only the permitted spanning permutations contribute.
-/

namespace GadgetOAI
namespace Computability
namespace VPVNP

open MvPolynomial
open scoped Classical

private theorem cycle_relabel {α β : Type*} (e : α ≃ β) {π : Equiv.Perm α}
    (h : π.IsCycleOn Set.univ) : (e.permCongr π).IsCycleOn Set.univ := by
  refine ⟨(e.permCongr π).bijective.bijOn_univ, fun x _ y _ => ?_⟩
  obtain ⟨i, hi⟩ := h.2 (Set.mem_univ (e.symm x)) (Set.mem_univ (e.symm y))
  refine ⟨i, ?_⟩
  change (e.permCongrHom π ^ i) x = y
  rw [← map_zpow]
  simp only [Equiv.permCongrHom_coe, Equiv.permCongr_apply, hi, Equiv.apply_symm_apply]

/-- The projected matrix has the given arc label on allowed arcs and zero elsewhere. -/
theorem hamiltonian_projection_on_allowed {V R τ : Type*} [Fintype V] [CommRing R] {m : ℕ}
    (e : Fin m ≃ V) (hm : 0 < m) (ok : V → V → Prop) (w : V → V → τ ⊕ R) :
    ∃ ψ : Projection R (Fin m × Fin m) τ, ψ.hom (hamiltonianCyclePolynomial R m) =
      ∑ π : {π : Equiv.Perm V // π.IsCycleOn Set.univ ∧ ∀ i, ok i (π i)},
        ∏ i, (w i (π.val i)).elim X C := by
  classical
  let ψ : Projection R (Fin m × Fin m) τ := fun (i,j) =>
    if ok (e i) (e j) then w (e i) (e j) else .inr 0
  let good (π : Equiv.Perm V) := π.IsCycleOn Set.univ ∧ ∀ i, ok i (π i)
  let weight (π : Equiv.Perm V) := ∏ i, (w i (π i)).elim (X (R := R)) C
  refine ⟨ψ, ?_⟩
  change ψ.hom (hamiltonianCyclePolynomial R m) = ∑ π : {π // good π}, weight π.val
  rw [← Finset.sum_subtype (Finset.univ.filter good) (by simp) weight, Finset.sum_filter,
    ← e.permCongr.sum_comp (fun π => if good π then weight π else 0)]
  simp only [hamiltonianCyclePolynomial, spanningCycles, map_sum, Finset.sum_filter,
    hm, true_and]
  apply Finset.sum_congr rfl
  intro π _
  have hc : (e.permCongr π).IsCycleOn Set.univ ↔ π.IsCycleOn Set.univ := by
    constructor
    · intro hc
      have hr := cycle_relabel e.symm hc
      change (e.permCongr.symm (e.permCongr π)).IsCycleOn Set.univ at hr
      rw [Equiv.symm_apply_apply] at hr
      exact hr
    · exact cycle_relabel e
  by_cases hcycle : π.IsCycleOn Set.univ
  · simp only [hcycle, ite_true, good, hc, true_and, map_prod]
    by_cases hok : ∀ i, ok i (e.permCongr π i)
    · rw [if_pos hok]
      dsimp only [weight]
      rw [← e.prod_comp (fun i => (w i (e.permCongr π i)).elim X C)]
      apply Finset.prod_congr rfl
      intro i _
      have hi : ok (e i) (e (π i)) := by simpa using hok (e i)
      simp [Projection.hom, ψ, hi]
    · rw [if_neg hok]
      obtain ⟨v, hv⟩ := not_forall.mp hok
      apply Finset.prod_eq_zero (Finset.mem_univ (e.symm v))
      have hi : ¬ok v (e (π (e.symm v))) := hv
      simp [Projection.hom, ψ, hi]
  · simp [hcycle, good, hc]

end VPVNP
end Computability
end GadgetOAI

end

section




/-!
# Selecting the first satisfied literal

Each literal occurrence is indexed by its position. In a satisfied clause, the
first match is unique even when the same literal occurs at several positions.
-/

namespace GadgetOAI
namespace Computability
namespace VPVNP

namespace ExactOne

variable {m : ℕ}

/-- A true bit with no earlier true bit. -/
def firstMatch (f : Fin m → Bool) (i : Fin m) : Bool :=
  decide (f i = true ∧ ∀ j < i, f j = false)

theorem firstMatch_iff (f : Fin m → Bool) (i : Fin m) :
    firstMatch f i = true ↔ f i = true ∧ ∀ j < i, f j = false := by
  simp [firstMatch]

theorem firstMatch_unique (f : Fin m → Bool) {i j : Fin m}
    (hi : firstMatch f i = true) (hj : firstMatch f j = true) : i = j := by
  rw [firstMatch_iff] at hi hj
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (by simpa [hi.1] using hj.2 i h)
  · exact h
  · exact False.elim (by simpa [hj.1] using hi.2 j h)

theorem existsUnique_firstMatch (f : Fin m → Bool) (hf : ∃ i, f i = true) :
    ∃! i, firstMatch f i = true := by
  let s := Finset.univ.filter (fun i => f i = true)
  have hs : s.Nonempty := by simpa [s, Finset.Nonempty] using hf
  let i := s.min' hs
  have hi : firstMatch f i = true := by
    rw [firstMatch_iff]
    refine ⟨by simpa [s] using s.min'_mem hs, fun j hj => ?_⟩
    cases h : f j with
    | false => rfl
    | true => exact (not_le_of_gt hj (s.min'_le j (by simp [s, h]))).elim
  exact ⟨i, hi, fun j hj => firstMatch_unique f hj hi⟩

theorem countP_finRange_eq_one (f : Fin m → Bool) :
    (List.finRange m).countP f = 1 ↔ ∃! i, f i = true := by
  have h := (List.nodup_finRange m).card_eq_countP (P := fun i => f i = true)
  simp only [Bool.decide_eq_true] at h
  rw [← h, Finset.card_eq_one_iff_existsUnique]
  simp

end ExactOne

end VPVNP
end Computability
end GadgetOAI

end
namespace GadgetOAI.Computability.VPVNP
namespace HardnessCNF
abbrev Literal (k : ℕ) := Fin k × Bool
abbrev CNF (k : ℕ) := List (List (Literal k))
def literalCount {k : ℕ} (φ : CNF k) : ℕ := (φ.map List.length).sum
end HardnessCNF
namespace ExactOne
open HardnessCNF MvPolynomial
open scoped Classical
variable {k : ℕ} {R : Type*}
def Holds (φ : CNF k) (x : Fin k → Bool) : Prop :=
  ∀ c ∈ φ, c.countP (fun l => x l.1 == l.2) = 1
abbrev Occ (φ : CNF k) := Σ c : Fin φ.length, Fin (φ[c].length)
theorem sum_lengths (φ : CNF k) : (∑ c : Fin φ.length, φ[c].length) = literalCount φ := by
  rw [← Fin.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map φ List.length)
noncomputable def weightedExactOne [CommSemiring R] (φ : CNF k) (w : Fin k → R) : R :=
  ∑ x, if Holds φ x then ∏ i, if x i then w i else 1 else 0
theorem weightedExactOne_eq_sum [CommSemiring R] (φ : CNF k) (w : Fin k → R) :
    weightedExactOne φ w =
      ∑ x : {x : Fin k → Bool // Holds φ x}, ∏ i, if x.val i then w i else 1 := by
  rw [weightedExactOne, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _
end ExactOne
end GadgetOAI.Computability.VPVNP

section



/-!
# Flattening exact-one literal occurrences for the graph reductions

The graph for Hamiltonian cycles and the graph for cycle covers have one indexed
occurrence per literal position. Each occurrence retains its variable, clause,
and polarity. Multiple occurrences of the same literal stay distinct.
-/

namespace GadgetOAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF

variable {k : ℕ}

theorem card_occ (φ : CNF k) : Fintype.card (Occ φ) = literalCount φ := by
  simp only [Occ, Fintype.card_sigma, Fintype.card_fin, sum_lengths]

/-- The graph may number occurrences by any bijection. -/
noncomputable def occurrenceIndex (φ : CNF k) : Fin (literalCount φ) ≃ Occ φ :=
  (Fintype.equivFinOfCardEq (card_occ φ)).symm

/-- The variable, clause and satisfying bit of occurrence `j`. -/
noncomputable def occurrences (φ : CNF k) (j : Fin (literalCount φ)) :
    Fin k × Fin φ.length × Bool :=
  let z := occurrenceIndex φ j
  let lit := φ[z.1][z.2]
  (lit.1, z.1, lit.2)

private theorem countP_eq_one_iff_position {A : Type*} (c : List A) (f : A → Bool) :
    c.countP f = 1 ↔ ∃! j : Fin c.length, f (c.get j) = true := by
  have hc : (List.finRange c.length).map (fun i : Fin c.length => c.get i) = c := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem
  have h := countP_finRange_eq_one (fun i : Fin c.length => f (c.get i))
  have eqCount := congrArg (List.countP f) hc
  rw [List.countP_map] at eqCount
  rw [← eqCount]
  exact h

private theorem existsUnique_occ_iff (φ : CNF k) (x : Fin k → Bool) (a : Fin φ.length) :
    (∃! z : Occ φ, z.1 = a ∧ x (φ[z.1][z.2]).1 = (φ[z.1][z.2]).2) ↔
      ∃! i : Fin φ[a].length, x (φ[a][i]).1 = (φ[a][i]).2 := by
  constructor
  · rintro ⟨⟨c, i⟩, ⟨rfl, hi⟩, hu⟩
    refine ⟨i, hi, fun j hj => ?_⟩
    exact eq_of_heq (Sigma.mk.inj_iff.mp (hu ⟨c, j⟩ ⟨rfl, hj⟩)).2
  · rintro ⟨i, hi, hu⟩
    refine ⟨⟨a, i⟩, ⟨rfl, hi⟩, ?_⟩
    rintro ⟨c, j⟩ ⟨rfl, hj⟩
    exact congrArg (Sigma.mk c) (hu j hj)

/-- Exact-one satisfaction is equivalent to one true numbered occurrence in each clause. -/
theorem holds_iff_unique_occurrence (φ : CNF k) (x : Fin k → Bool) :
    Holds φ x ↔ ∀ a : Fin φ.length, ∃! j : Fin (literalCount φ),
      (occurrences φ j).2.1 = a ∧ x (occurrences φ j).1 = (occurrences φ j).2.2 := by
  simp only [Holds, List.forall_mem_iff_get]
  apply forall_congr'
  intro a
  rw [countP_eq_one_iff_position]
  simp only [beq_iff_eq]
  exact (existsUnique_occ_iff φ x a).symm.trans
    (occurrenceIndex φ).existsUnique_congr_right.symm

/-- Any family member containing an empty clause has zero satisfying assignments. -/
theorem not_holds_of_nil_mem {φ : CNF k} (h : [] ∈ φ) (x : Fin k → Bool) : ¬ Holds φ x := by
  intro hx
  simpa using hx [] h

/-- Without empty clauses the graph's number of clause vertices is at most the literal count. -/
theorem length_le_literalCount_of_nil_notMem {φ : CNF k} (h : [] ∉ φ) :
    φ.length ≤ literalCount φ := by
  rw [← sum_lengths]
  have hpos (c : Fin φ.length) : 1 ≤ φ[c].length := by
    have hc : φ[c] ≠ [] := fun he => h (he ▸ List.getElem_mem _)
    exact List.length_pos_iff.mpr hc
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpos c)

end ExactOne

end VPVNP
end Computability
end GadgetOAI

end

section






/-!
# Exact-one generating polynomials as Hamiltonian-cycle projections

Each satisfying assignment yields one allowed spanning cycle. Its entry arcs
record the selected variable weights. Summing the weights of these cycles
therefore gives the weighted exact-one polynomial over any commutative ring.
-/

namespace GadgetOAI
namespace Computability
namespace VPVNP

namespace HCGadget

open MvPolynomial Equiv
open scoped Classical

variable {R τ : Type*} [CommSemiring R] {k h c : ℕ}
variable (occ : Fin h → Fin k × Fin c × Bool)

/-- The entering arc records a true bit by its variable or scalar weight. All
other allowed arcs carry one. -/
def arcWeight (w : Projection R (Fin k) τ) : Vertex k h c → Vertex k h c → τ ⊕ R
  | .sep i, .endpoint _ false => w i
  | _, _ => .inr 1

theorem product_cycleOfAssignment (w : Projection R (Fin k) τ) (x : Fin k → Bool)
    (hx : Exact occ x) :
    (∏ v, (arcWeight w v (cycleOfAssignment occ x hx v)).elim X C) =
      ∏ i, if x i then (w i).elim X C else 1 := by
  classical
  let S : Finset (Vertex k h c) := Finset.univ.image Vertex.sep
  have toS : (∏ v, (arcWeight w v (cycleOfAssignment occ x hx v)).elim X C) =
      ∏ v ∈ S, (arcWeight w v (cycleOfAssignment occ x hx v)).elim X C := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro v _ hv
    cases v with
    | sep i => exact False.elim (hv (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    | endpoint | buffer | port | clause => simp [arcWeight]
  rw [toS, show S = _ from rfl, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i _
    cases hi : x i <;> simp [nextVertex, hi, arcWeight]
  · exact fun _ _ _ _ he => Vertex.sep.inj he

/-- Spanning cycles in the exact-one gadget that follow an allowed directed edge at every
vertex. -/
abbrev Admissible (occ : Fin h → Fin k × Fin c × Bool) :=
  {π : Perm (Vertex k h c) // π.IsCycleOn Set.univ ∧ ∀ v, Allowed occ v (π v)}

/-- Turn an exact satisfying assignment into its directed spanning cycle through the variable
tracks and clause vertices. -/
noncomputable def toCycle (hk : 0 < k) (x : {x : Fin k → Bool // Exact occ x}) : Admissible occ :=
  ⟨cycleOfAssignment occ x x.2, cycleOfAssignment_spanning occ x x.2 hk, nextVertex_allowed occ x x.2⟩

/-- The weight-preserving encoding of exact-one assignments as allowed Hamiltonian tours. -/
noncomputable def assignmentsEquiv (hk : 0 < k) :
    {x : Fin k → Bool // Exact occ x} ≃ Admissible occ :=
  Equiv.ofBijective (toCycle occ hk) ⟨
    fun _ _ e => cycleOfAssignment_injective occ (congrArg Subtype.val e),
    fun π => by
      obtain ⟨x, hx, he⟩ := exists_exact_assignment π.2.1 π.2.2
      exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩⟩

section

variable {S : Type*} [CommRing S]

theorem weightedProjectionSlots (hk : 0 < k) (w : Projection S (Fin k) τ) :
    ∃ ψ : Projection S (Fin (k * (3 * h + 4) + c) × Fin (k * (3 * h + 4) + c)) τ,
      ψ.hom (hamiltonianCyclePolynomial S (k * (3 * h + 4) + c)) =
        ∑ x : {x : Fin k → Bool // Exact occ x}, ∏ i, if x.val i then (w i).elim X C else 1 := by
  classical
  let e := (Fintype.equivFinOfCardEq (card_vertex k h c)).symm
  have hm : 0 < k * (3 * h + 4) + c := Nat.add_pos_left (Nat.mul_pos hk (by omega)) _
  obtain ⟨ψ, he⟩ := hamiltonian_projection_on_allowed e hm (Allowed occ) (arcWeight w)
  refine ⟨ψ, he.trans ?_⟩
  symm
  let aweight (x : {x : Fin k → Bool // Exact occ x}) :=
    ∏ i, if x.val i then (w i).elim X C else 1
  let cweight (π : Admissible occ) := ∏ v, (arcWeight w v (π.val v)).elim X C
  refine @Fintype.sum_equiv _ _ _ ?_ ?_ _ (assignmentsEquiv occ hk) aweight cweight ?_
  intro x
  exact (product_cycleOfAssignment occ w x.val x.2).symm

/-- Projection from a Hamiltonian polynomial of explicit order for any positive-width
exact-one formula, allowing repeated literals and empty clauses. -/
theorem weighted_projection (φ : HardnessCNF.CNF k) (hk : 0 < k) (w : Projection S (Fin k) τ) :
    ∃ ψ : Projection S (Fin (k * (3 * HardnessCNF.literalCount φ + 4) + φ.length) ×
        Fin (k * (3 * HardnessCNF.literalCount φ + 4) + φ.length)) τ,
      ψ.hom (hamiltonianCyclePolynomial S (k * (3 * HardnessCNF.literalCount φ + 4) + φ.length)) =
        ExactOne.weightedExactOne φ (fun i => (w i).elim X C) := by
  obtain ⟨ψ, he⟩ := weightedProjectionSlots (ExactOne.occurrences φ) hk w
  refine ⟨ψ, he.trans ?_⟩
  rw [ExactOne.weightedExactOne_eq_sum]
  let e : {x : Fin k → Bool // Exact (ExactOne.occurrences φ) x} ≃
      {x : Fin k → Bool // ExactOne.Holds φ x} := Equiv.subtypeEquivRight (fun x => (ExactOne.holds_iff_unique_occurrence φ x).symm)
  let wt (x : Fin k → Bool) : MvPolynomial τ S := ∏ i, if x i then (w i).elim X C else 1
  exact Fintype.sum_equiv e (fun x => wt x.val) (fun x => wt x.val) fun _ => rfl

end

end HCGadget

end VPVNP
end Computability
end GadgetOAI

end

theorem OMA.branch1 : OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro K τ _ k φ w hk
  obtain ⟨ψ, hψ⟩ := GadgetOAI.Computability.VPVNP.HCGadget.weighted_projection φ hk w
  refine ⟨ψ, ?_⟩
  simp only [GadgetOAI.Computability.VPVNP.Projection.hom, GadgetOAI.Computability.VPVNP.hamiltonianCyclePolynomial, GadgetOAI.Computability.VPVNP.spanningCycles, GadgetOAI.Computability.VPVNP.HardnessCNF.literalCount, GadgetOAI.Computability.VPVNP.ExactOne.weightedExactOne, GadgetOAI.Computability.VPVNP.ExactOne.Holds] at hψ
  convert hψ using 1 <;> congr! 5

/-! Adapted from OpenAI/math 3344da59991ed94f9ba711217b29c1d760badfa6, lean/OAI/Computability/VPVNP, Apache-2.0. Copyright OpenAI. -/
section





/-! # Permanent completeness for exact arithmetic circuits -/

namespace OAI
namespace Computability
namespace VPVNP

namespace Valiant.Project

open scoped Classical

/-- A table of `s` binary gates computes `p`. Variables and scalars are free, and the
output and later gates may reuse any previously available value. -/
def Computes {F σ : Type*} [Field F] (s : ℕ) (p : MvPolynomial σ F) : Prop :=
  ∃ v : Fin s → MvPolynomial σ F,
    let available (k : ℕ) (x : MvPolynomial σ F) :=
      (∃ j : σ, MvPolynomial.X j = x) ∨ (∃ a : F, MvPolynomial.C a = x) ∨
        ∃ j : Fin s, j.val < k ∧ v j = x
    available s p ∧ ∀ i : Fin s, ∃ a b, available i.val a ∧ available i.val b ∧
      (v i = a + b ∨ v i = a - b ∨ v i = a * b)

/-- A polynomial bound uniform in all sufficiently large indices. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop := ∃ A d N : ℕ, ∀ n ≥ N, f n ≤ A * n ^ d

/-- At each index a family has its own finite type of indeterminates. -/
abbrev Family (F : Type*) [Field F] (σ : ℕ → Type) := (n : ℕ) → MvPolynomial (σ n) F

variable {F : Type*} [Field F] {σ τ : ℕ → Type} [∀ n, Fintype (σ n)]

/-- Arity and total degree grow at most polynomially with the index. -/
def PFamily (p : Family F σ) : Prop :=
  PolynomiallyBounded (fun n => Fintype.card (σ n)) ∧
    PolynomiallyBounded (fun n => (p n).totalDegree)

/-- VP consists of polynomial families computed by polynomial-size exact circuits. -/
def IsVP (p : Family F σ) : Prop :=
  PFamily p ∧ ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, Computes (s n) (p n)

/-- A VNP family sums a VP verifier over all Boolean assignments to its witness variables. -/
def IsVNP (p : Family F σ) : Prop :=
  PFamily p ∧ ∃ (W : ℕ → Type) (inst : ∀ n, Fintype (W n)) (g : Family F (fun n => σ n ⊕ W n)),
    PolynomiallyBounded (fun n => @Fintype.card _ (inst n)) ∧ IsVP g ∧ ∀ n,
      p n = ∑ y : W n → Bool, MvPolynomial.eval₂Hom MvPolynomial.C
        (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (if y i then 1 else 0))) (g n)

/-- A p-projection substitutes target variables or scalars at polynomially bounded indices. -/
def PProjects (target : Family F τ) (source : Family F σ) : Prop :=
  ∃ r : ℕ → ℕ, PolynomiallyBounded r ∧ ∀ n, ∃ φ : σ (r n) → τ n ⊕ F,
    MvPolynomial.eval₂Hom MvPolynomial.C (fun i => (φ i).elim MvPolynomial.X MvPolynomial.C)
      (source (r n)) = target n

/-- Membership in VNP and hardness for every VNP family over the same field. -/
def VNPComplete (p : Family F σ) : Prop :=
  IsVNP p ∧ ∀ (τ : ℕ → Type) [∀ n, Fintype (τ n)] (g : Family F τ), IsVNP g → PProjects g p

/-- The permanent of the generic square matrix of formal variables. -/
noncomputable def permanent (F : Type*) [Field F] (n : ℕ) : MvPolynomial (Fin n × Fin n) F :=
  Matrix.permanent (Matrix.of fun i j => MvPolynomial.X (i, j))

end Valiant.Project

end VPVNP
end Computability
end OAI

end

section


/-! # Exact arithmetic circuits and projections

Gates are listed in topological order. Each operand may use any earlier gate, a variable,
or any scalar in the coefficient ring. Only binary operations count toward the size.
The designated output is evaluated in the ring of formal multivariate polynomials.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- A binary addition, subtraction, or multiplication gate in an exact arithmetic circuit. -/
inductive BinOp where
  | add | sub | mul

/-- Interpret a gate's operation on its two ordered inputs in the target ring. -/
def BinOp.apply {A : Type*} [Ring A] : BinOp → A → A → A
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- A reference available after exactly `n` gates have been computed. -/
inductive Ref (R σ : Type*) (n : ℕ) where
  | var : σ → Ref R σ n
  | const : R → Ref R σ n
  | gate : Fin n → Ref R σ n

/-- A topologically ordered list of arithmetic gates. The index counts the gates already
available to subsequent operands. -/
inductive Program (R σ : Type*) : ℕ → Type _ where
  | nil : Program R σ 0
  | snoc {n : ℕ} (prev : Program R σ n) (op : BinOp) (a b : Ref R σ n) : Program R σ (n+1)

/-- An arithmetic program with one designated output. Its size index counts binary operations. -/
structure Circuit (R σ : Type*) (n : ℕ) where
  /-- The sequence of binary gates available to the output reference. -/
  program : Program R σ n
  /-- The input variable, ring constant, or previously computed gate selected as the output. -/
  output : Ref R σ n

variable {R S σ τ A B : Type*} {n : ℕ}

/-- Resolve an operand using the supplied interpretation of constants, inputs, and earlier gate
values. -/
def Ref.read (scalar : R → A) (input : σ → A) (wires : Fin n → A) : Ref R σ n → A
  | .const r => scalar r
  | .var i => input i
  | .gate i => wires i

/-- Evaluate the gates in topological order and return the value at every gate index. -/
def Program.run [Ring A] (scalar : R → A) (input : σ → A) :
    {n : ℕ} → Program R σ n → Fin n → A
  | _, .nil => Fin.elim0
  | _, .snoc p op a b =>
    let wires := p.run scalar input
    Fin.lastCases (op.apply (a.read scalar input wires) (b.read scalar input wires)) wires

/-- Read the designated output after evaluating the circuit with the supplied scalar and
variable assignments. -/
def Circuit.eval [Ring A] (c : Circuit R σ n) (scalar : R → A) (input : σ → A) : A :=
  c.output.read scalar input (c.program.run scalar input)

/-- The formal polynomial computed when each input is its corresponding indeterminate and each
scalar is a constant polynomial. -/
noncomputable def Circuit.polynomial [CommRing R] (c : Circuit R σ n) : MvPolynomial σ R :=
  c.eval MvPolynomial.C MvPolynomial.X

/-- Substitutions allowed in a projection. A variable may become a variable or a scalar. -/
abbrev Projection (R σ τ : Type*) := σ → τ ⊕ R

/-- Apply a projection to a variable operand and the supplied scalar map to a constant operand.
A gate reference keeps its index. -/
def Ref.subst (φ : Projection S σ τ) (f : R → S) : Ref R σ n → Ref S τ n
  | .var i => (φ i).elim Ref.var Ref.const
  | .const r => .const (f r)
  | .gate i => .gate i

/-- Project the variable operands and map the constants of every gate in the program. -/
def Program.subst (φ : Projection S σ τ) (f : R → S) :
    {n : ℕ} → Program R σ n → Program S τ n
  | _, .nil => .nil
  | _, .snoc p op a b => .snoc (p.subst φ f) op (a.subst φ f) (b.subst φ f)

/-- Apply the same variable projection and scalar map to the program and its designated output
reference. -/
def Circuit.subst (c : Circuit R σ n) (φ : Projection S σ τ) (f : R → S) : Circuit S τ n :=
  ⟨c.program.subst φ f, c.output.subst φ f⟩

/-- Specialize each scalar operand along the given map while retaining the circuit's input
variables. -/
def Circuit.mapConstants (c : Circuit R σ n) (f : R → S) : Circuit S σ n :=
  c.subst Sum.inl f

private theorem Ref.read_subst (φ : Projection S σ τ) (f : R → S)
    (s : S → A) (x : τ → A) (w : Fin n → A) (r : Ref R σ n) :
    (r.subst φ f).read s x w = r.read (s ∘ f) (fun i => (φ i).elim x s) w := by
  cases r with
  | var i => cases h : φ i <;> simp [Ref.subst, Ref.read, h]
  | const | gate => rfl

private theorem Program.run_subst [Ring A] (φ : Projection S σ τ) (f : R → S)
    (s : S → A) (x : τ → A) (p : Program R σ n) :
    (p.subst φ f).run s x = p.run (s ∘ f) (fun i => (φ i).elim x s) := by
  induction p with
  | nil => rfl
  | snoc p op a b ih => simp only [Program.subst, Program.run, ih, Ref.read_subst]

theorem Circuit.eval_subst [Ring A] (c : Circuit R σ n) (φ : Projection S σ τ)
    (f : R → S) (s : S → A) (x : τ → A) :
    (c.subst φ f).eval s x = c.eval (s ∘ f) (fun i => (φ i).elim x s) := by
  simp only [Circuit.eval, Circuit.subst, Program.run_subst, Ref.read_subst]

private theorem Ref.read_hom [Ring A] [Ring B] (h : A →+* B) (s : R → A) (x : σ → A)
    (w : Fin n → A) (r : Ref R σ n) :
    h (r.read s x w) = r.read (h ∘ s) (h ∘ x) (h ∘ w) := by cases r <;> rfl

private theorem Program.run_hom [Ring A] [Ring B] (h : A →+* B) (s : R → A) (x : σ → A)
    (p : Program R σ n) : h ∘ p.run s x = p.run (h ∘ s) (h ∘ x) := by
  induction p with
  | nil => funext j; exact j.elim0
  | snoc p op a b ih =>
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Function.comp_apply, Program.run, Fin.lastCases_last]
      cases op <;> simp [BinOp.apply, Ref.read_hom, ih]
    · simpa [Program.run, Function.comp_def] using congrFun ih i

theorem Circuit.eval_hom [Ring A] [Ring B] (c : Circuit R σ n) (h : A →+* B)
    (s : R → A) (x : σ → A) : h (c.eval s x) = c.eval (h ∘ s) (h ∘ x) := by
  simp only [Circuit.eval, Ref.read_hom, Program.run_hom]

/-- Scalar specialization preserves every binary gate of the circuit. -/
theorem Circuit.map_polynomial [CommRing R] [CommRing S] (c : Circuit R σ n) (f : R →+* S) :
    (c.mapConstants f).polynomial = MvPolynomial.map f c.polynomial := by
  rw [Circuit.mapConstants, Circuit.polynomial, Circuit.eval_subst, Circuit.polynomial,
    Circuit.eval_hom]
  congr 1 <;> funext i <;> simp

/-- The coefficient-preserving polynomial semiring homomorphism substituting each source
variable by its prescribed target variable or scalar. -/
noncomputable def Projection.hom [CommSemiring R] (φ : Projection R σ τ) :
    MvPolynomial σ R →+* MvPolynomial τ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => (φ i).elim MvPolynomial.X MvPolynomial.C)

/-- Projecting a formal polynomial computed with `n` gates gives an `n`-gate circuit. -/
theorem Circuit.project_polynomial [CommRing R] (c : Circuit R σ n) (φ : Projection R σ τ) :
    (c.subst φ id).polynomial = φ.hom c.polynomial := by
  rw [Circuit.polynomial, Circuit.eval_subst, Circuit.polynomial, Circuit.eval_hom]
  congr 1 <;> funext i <;> simp [Projection.hom]

end VPVNP
end Computability
end OAI

end

section


/-! # Composition of exact arithmetic circuits

Concatenating two topologically ordered programs preserves their internal wires. A final
binary gate then computes the chosen operation on the two designated outputs.
-/

namespace OAI
namespace Computability
namespace VPVNP

variable {R σ A : Type*} {n m : ℕ}

/-- Renumber the gate references while preserving scalar and variable inputs. -/
def Ref.reindex (f : Fin n → Fin m) : Ref R σ n → Ref R σ m
  | .var x => .var x
  | .const r => .const r
  | .gate i => .gate (f i)

private theorem Ref.read_reindex (f : Fin n → Fin m) (s : R → A) (x : σ → A)
    (w : Fin m → A) (r : Ref R σ n) :
    (r.reindex f).read s x w = r.read s x (w ∘ f) := by cases r <;> rfl

/-- Append the gates of the second program after those of the first program. -/
def Program.append (p : Program R σ n) : {m : ℕ} → Program R σ m → Program R σ (n + m)
  | _, .nil => p
  | _, .snoc q op a b =>
    .snoc (p.append q) op (a.reindex (Fin.natAdd n)) (b.reindex (Fin.natAdd n))

private theorem Program.run_append_left [Ring A] (s : R → A) (x : σ → A)
    (p : Program R σ n) (q : Program R σ m) :
    (p.append q).run s x ∘ Fin.castAdd m = p.run s x := by
  funext i
  induction q with
  | nil => rfl
  | snoc q op a b ih =>
    simp only [Function.comp_apply, Program.append, Program.run, ← Fin.castSucc_castAdd,
      Fin.lastCases_castSucc]
    exact ih

private theorem Program.run_append_right [Ring A] (s : R → A) (x : σ → A)
    (p : Program R σ n) (q : Program R σ m) :
    (p.append q).run s x ∘ Fin.natAdd n = q.run s x := by
  induction q with
  | nil => funext i; exact i.elim0
  | snoc q op a b ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, Program.append, Program.run, Fin.natAdd_last,
        Fin.lastCases_last, Ref.read_reindex, ih]
      exact Fin.lastCases_last
    · simpa only [Function.comp_apply, Program.append, Program.run, Fin.natAdd_castSucc,
        Fin.lastCases_castSucc] using congrFun ih j

/-- Combine the outputs of two circuits using one additional binary gate. -/
def Circuit.combine (op : BinOp) (c : Circuit R σ n) (d : Circuit R σ m) :
    Circuit R σ (n + m + 1) where
  program := .snoc (c.program.append d.program) op
    (c.output.reindex (Fin.castAdd m)) (d.output.reindex (Fin.natAdd n))
  output := .gate (Fin.last (n + m))

theorem Circuit.eval_combine [Ring A] (op : BinOp) (c : Circuit R σ n)
    (d : Circuit R σ m) (s : R → A) (x : σ → A) :
    (Circuit.combine op c d).eval s x = op.apply (c.eval s x) (d.eval s x) := by
  change Program.run s x (.snoc (c.program.append d.program) op _ _) (Fin.last _) = _
  simp only [Program.run, Fin.lastCases_last, Ref.read_reindex, Program.run_append_left,
    Program.run_append_right, Circuit.eval]

theorem Circuit.polynomial_combine [CommRing R] (op : BinOp) (c : Circuit R σ n)
    (d : Circuit R σ m) :
    (Circuit.combine op c d).polynomial = op.apply c.polynomial d.polynomial :=
  Circuit.eval_combine op c d MvPolynomial.C MvPolynomial.X

end VPVNP
end Computability
end OAI

end

section


/-!
# Descent of exact polynomial computations

Section 1 of *VP and VNP differ over every field* passes from a circuit over an
arbitrary field to the same circuit topology over the algebraic closure of the prime
field. Each scalar input of the topology can first be replaced by a parameter. The
coefficients of the resulting formal output are polynomials in these parameters.
Hilbert's Nullstellensatz descends the simultaneous coefficient equations to any
algebraically closed extension of the base field.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {k F K σ υ : Type*} [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] [IsAlgClosed K] [Finite σ]

/-- A polynomial system in finitely many unknowns that has a solution in an extension
field of `k` has a solution in every algebraically closed extension of `k`. -/
theorem polynomialSystem_descent (S : Set (MvPolynomial σ k)) (a : σ → F)
    (ha : ∀ p ∈ S, aeval a p = 0) :
    ∃ b : σ → K, ∀ p ∈ S, aeval b p = 0 := by
  have hproper : Ideal.span S ≠ ⊤ := by
    have hle : Ideal.span S ≤ vanishingIdeal k {a} :=
      Ideal.span_le.mpr fun p hp ↦ (mem_vanishingIdeal_singleton_iff a p).mpr (ha p hp)
    exact fun h ↦ (inferInstance : (vanishingIdeal k {a}).IsPrime).ne_top <|
      top_unique (h ▸ hle)
  obtain ⟨M, hM, hSM⟩ := Ideal.exists_le_maximal (Ideal.span S) hproper
  obtain ⟨b, rfl⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hM
  exact ⟨b, fun p hp ↦ (mem_vanishingIdeal_singleton_iff b p).mp
    (hSM (Ideal.subset_span hp))⟩

/-- An exact specialization of a formal output polynomial over a parameter ring descends
simultaneously in all its coefficients. This applies to a circuit with any degree of
intermediate cancellation, using its scalar inputs as the parameters. -/
theorem formalOutput_descent (P : MvPolynomial υ (MvPolynomial σ k)) (f : MvPolynomial υ k)
    (a : σ → F) (ha : map (aeval a).toRingHom P = map (algebraMap k F) f) :
    ∃ b : σ → K, map (aeval b).toRingHom P = map (algebraMap k K) f := by
  let eqn (m : υ →₀ ℕ) : MvPolynomial σ k := P.coeff m - C (f.coeff m)
  obtain ⟨b, hb⟩ := polynomialSystem_descent (K := K) (Set.range eqn) a (by
    rintro _ ⟨m, rfl⟩
    have h := congrArg (fun p : MvPolynomial υ F ↦ p.coeff m) ha
    simpa [eqn, sub_eq_zero, coeff_map] using h)
  refine ⟨b, MvPolynomial.ext _ _ fun m ↦ ?_⟩
  have h := hb (eqn m) (Set.mem_range_self m)
  simpa [eqn, sub_eq_zero, coeff_map] using h

end VPVNP
end Computability
end OAI

end

section



/-!
# Descent without changing the circuit topology

A circuit for a polynomial defined over a base field `k` can replace every scalar
label with a new value in an algebraically closed extension of `k`. This applies
when the original labels belong to an arbitrary extension of `k`. Binary gate
types, wiring, reuse, the designated output and the gate count all persist.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {R S T σ : Type*} {n : ℕ}

private def Ref.scalarLabels : Ref R σ n → List R
  | .const c => [c]
  | .var _ | .gate _ => []

private def Program.scalarLabels : {n : ℕ} → Program R σ n → List R
  | _, .nil => []
  | _, .snoc p _ a b => p.scalarLabels ++ a.scalarLabels ++ b.scalarLabels

/-- All scalar occurrences in a circuit, including an output that is a scalar. -/
def Circuit.scalarLabels (c : Circuit R σ n) : List R :=
  c.program.scalarLabels ++ c.output.scalarLabels

private theorem Ref.subst_inl_comp (r : Ref R σ n) (f : R → S) (g : S → T) :
    (r.subst Sum.inl f).subst Sum.inl g = r.subst Sum.inl (g ∘ f) := by cases r <;> rfl

private theorem Program.subst_inl_comp (p : Program R σ n) (f : R → S) (g : S → T) :
    (p.subst Sum.inl f).subst Sum.inl g = p.subst Sum.inl (g ∘ f) := by
  induction p with
  | nil => rfl
  | snoc p op a b ih => simp only [Program.subst, ih, Ref.subst_inl_comp]

theorem Circuit.mapConstants_comp (c : Circuit R σ n) (f : R → S) (g : S → T) :
    (c.mapConstants f).mapConstants g = c.mapConstants (g ∘ f) := by
  simp only [Circuit.mapConstants, Circuit.subst, Ref.subst_inl_comp, Program.subst_inl_comp]

private theorem Ref.subst_inl_self (r : Ref R σ n) (f : R → R)
    (hf : ∀ x ∈ r.scalarLabels, f x = x) : r.subst Sum.inl f = r := by
  cases r with
  | const x => simp [Ref.subst, hf x (by simp [Ref.scalarLabels])]
  | var | gate => rfl

private theorem Program.subst_inl_self (p : Program R σ n) (f : R → R)
    (hf : ∀ x ∈ p.scalarLabels, f x = x) : p.subst Sum.inl f = p := by
  induction p with
  | nil => rfl
  | snoc p op a b ih =>
    rw [Program.subst, ih (fun x hx ↦ hf x (by simp [Program.scalarLabels, hx])),
      a.subst_inl_self f (fun x hx ↦ hf x (by simp [Program.scalarLabels, hx])),
      b.subst_inl_self f (fun x hx ↦ hf x (by simp [Program.scalarLabels, hx]))]

theorem Circuit.mapConstants_self (c : Circuit R σ n) (f : R → R)
    (hf : ∀ x ∈ c.scalarLabels, f x = x) : c.mapConstants f = c := by
  simp only [Circuit.mapConstants, Circuit.subst,
    c.program.subst_inl_self f (fun x hx ↦ hf x (by simp [Circuit.scalarLabels, hx])),
    c.output.subst_inl_self f (fun x hx ↦ hf x (by simp [Circuit.scalarLabels, hx]))]

/-- Descent of an exact circuit by changing only its scalar labels. The formal target
polynomial is interpreted in the two fields by their respective algebra maps. -/
theorem Circuit.exists_scalar_relabeling {k F K : Type*} [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] [IsAlgClosed K] (c : Circuit F σ n) (p : MvPolynomial σ k)
    (hc : c.polynomial = map (algebraMap k F) p) :
    ∃ relabel : F → K, (c.mapConstants relabel).polynomial = map (algebraMap k K) p := by
  classical
  let labels := c.scalarLabels.toFinset
  let param (v : F) : MvPolynomial (↥labels) k :=
    if h : v ∈ labels then X ⟨v, h⟩ else 0
  let generic := c.mapConstants param
  let values : (↥labels) → F := Subtype.val
  have recover : generic.mapConstants (aeval values).toRingHom = c := by
    rw [Circuit.mapConstants_comp]
    apply Circuit.mapConstants_self
    intro v hv
    have hv' : v ∈ labels := List.mem_toFinset.mpr hv
    simp [param, values, hv']
  have hs : map (aeval values).toRingHom generic.polynomial = map (algebraMap k F) p := by
    rw [← Circuit.map_polynomial, recover, hc]
  obtain ⟨b, hb⟩ := formalOutput_descent (K := K) generic.polynomial p values hs
  exact ⟨(aeval b).toRingHom ∘ param, by
    rw [← Circuit.mapConstants_comp, Circuit.map_polynomial]
    exact hb⟩

end VPVNP
end Computability
end OAI

end

section




/-!
# Minimum exact circuit size

Every formal polynomial has a division-free arithmetic circuit. Taking the
minimum over topologically ordered circuits therefore defines the gate count
`L_F` of §1, including zero-gate circuits for variables and field constants.
-/

namespace OAI
namespace Computability
namespace VPVNP

variable {R σ τ : Type*} [CommRing R]

/-- A single scalar input is an output of a circuit with no binary gates. -/
def Circuit.constant (a : R) : Circuit R σ 0 := ⟨.nil, .const a⟩

/-- A single variable is an output of a circuit with no binary gates. -/
def Circuit.variable (i : σ) : Circuit R σ 0 := ⟨.nil, .var i⟩

@[simp] theorem Circuit.polynomial_constant (a : R) :
    (Circuit.constant a : Circuit R σ 0).polynomial = MvPolynomial.C a := rfl

@[simp] theorem Circuit.polynomial_variable (i : σ) :
    (Circuit.variable i : Circuit R σ 0).polynomial = MvPolynomial.X i := rfl

/-- Every multivariate polynomial is the formal output of a finite exact circuit. -/
theorem exists_circuit_polynomial (p : MvPolynomial σ R) :
    ∃ n, ∃ c : Circuit R σ n, c.polynomial = p := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, Circuit.constant a, rfl⟩
  | add p q hp hq =>
    obtain ⟨n, c, rfl⟩ := hp
    obtain ⟨m, d, rfl⟩ := hq
    exact ⟨n + m + 1, Circuit.combine .add c d, Circuit.polynomial_combine ..⟩
  | mul_X p i hp =>
    obtain ⟨n, c, rfl⟩ := hp
    exact ⟨n + 0 + 1, Circuit.combine .mul c (Circuit.variable i),
      Circuit.polynomial_combine ..⟩

/-- The least number of binary addition, subtraction and multiplication gates
in a circuit computing `p` as a formal polynomial, with arbitrary scalar inputs. -/
noncomputable def circuitSize (p : MvPolynomial σ R) : ℕ := by
  classical
  exact Nat.find (exists_circuit_polynomial p)

theorem circuitSize_spec (p : MvPolynomial σ R) :
    ∃ c : Circuit R σ (circuitSize p), c.polynomial = p := by
  classical
  exact Nat.find_spec (exists_circuit_polynomial p)

theorem circuitSize_le_iff {p : MvPolynomial σ R} {n : ℕ} :
    circuitSize p ≤ n ↔ ∃ m ≤ n, ∃ c : Circuit R σ m, c.polynomial = p := by
  classical
  exact Nat.find_le_iff (exists_circuit_polynomial p) n

theorem circuitSize_le_of_circuit {n : ℕ} (c : Circuit R σ n) :
    circuitSize c.polynomial ≤ n :=
  circuitSize_le_iff.mpr ⟨n, le_rfl, c, rfl⟩

@[simp] theorem circuitSize_C (a : R) : circuitSize (MvPolynomial.C (σ := σ) a) = 0 :=
  Nat.eq_zero_of_le_zero (circuitSize_le_of_circuit (Circuit.constant a))

@[simp] theorem circuitSize_X (i : σ) : circuitSize (MvPolynomial.X (R := R) i) = 0 :=
  Nat.eq_zero_of_le_zero (circuitSize_le_of_circuit (Circuit.variable i))

theorem circuitSize_binOp_le (op : BinOp) (p q : MvPolynomial σ R) :
    circuitSize (op.apply p q) ≤ circuitSize p + circuitSize q + 1 := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  obtain ⟨d, hd⟩ := circuitSize_spec q
  simpa only [Circuit.polynomial_combine, hc, hd] using
    circuitSize_le_of_circuit (Circuit.combine op c d)

/-- Replacing variables by variables or constants preserves an upper bound
on the number of binary gates, regardless of the field constants used. -/
theorem circuitSize_projection_le (φ : Projection R σ τ) (p : MvPolynomial σ R) :
    circuitSize (φ.hom p) ≤ circuitSize p := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  simpa only [Circuit.project_polynomial, hc] using circuitSize_le_of_circuit (c.subst φ id)

/-- Applying a scalar homomorphism to the output cannot increase its minimum gate count. -/
theorem circuitSize_map_le {S : Type*} [CommRing S] (f : R →+* S) (p : MvPolynomial σ R) :
    circuitSize (MvPolynomial.map f p) ≤ circuitSize p := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  simpa only [Circuit.map_polynomial, hc] using circuitSize_le_of_circuit (c.mapConstants f)

/-- Section 1's reduction to one algebraically closed field. For a polynomial over
the prime field `k`, a lower bound over its algebraic closure `K` holds with the
same numerical value over every field extension `F` of `k`. -/
theorem circuitSize_descent_le {k K F : Type*} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [IsAlgClosed K] (p : MvPolynomial σ k) :
    circuitSize (MvPolynomial.map (algebraMap k K) p) ≤
      circuitSize (MvPolynomial.map (algebraMap k F) p) := by
  obtain ⟨c, hc⟩ := circuitSize_spec (MvPolynomial.map (algebraMap k F) p)
  obtain ⟨f, hf⟩ := c.exists_scalar_relabeling (K := K) p hc
  simpa only [hf] using circuitSize_le_of_circuit (c.mapConstants f)

end VPVNP
end Computability
end OAI

end

section



/-! # Exact circuit correspondence for the project permanent-completeness statement -/

namespace OAI
namespace Computability
namespace VPVNP

namespace Valiant.Project

open MvPolynomial (C X)

variable {F σ : Type*} [Field F] {s k : ℕ}

private abbrev available (v : Fin s → MvPolynomial σ F) (k : ℕ) (x : MvPolynomial σ F) : Prop :=
  (∃ j : σ, X j = x) ∨ (∃ a : F, C a = x) ∨ ∃ j : Fin s, j.val < k ∧ v j = x

private abbrev prefixValues (v : Fin s → MvPolynomial σ F) (hk : k ≤ s) (i : Fin k) :=
  v (i.castLE hk)

private abbrev gateValue (allowed : MvPolynomial σ F → Prop) (x : MvPolynomial σ F) : Prop :=
  ∃ a b, allowed a ∧ allowed b ∧ (x = a + b ∨ x = a - b ∨ x = a * b)

private theorem available_iff_ref (v : Fin s → MvPolynomial σ F) (hk : k ≤ s)
    (x : MvPolynomial σ F) :
    available v k x ↔ ∃ r : Ref F σ k, r.read C X (prefixValues v hk) = x := by
  constructor
  · rintro (⟨j, rfl⟩ | ⟨c, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨.var j, rfl⟩
    · exact ⟨.const c, rfl⟩
    · exact ⟨.gate ⟨j, hj⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    cases r with
    | var j => exact Or.inl ⟨j, rfl⟩
    | const c => exact Or.inr (Or.inl ⟨c, rfl⟩)
    | gate j => exact Or.inr (Or.inr ⟨j.castLE hk, j.isLt, rfl⟩)

private theorem gateValue_iff (v : Fin s → MvPolynomial σ F) (hk : k ≤ s)
    (x : MvPolynomial σ F) :
    gateValue (available v k) x ↔ ∃ op : BinOp, ∃ a b : Ref F σ k,
      op.apply (a.read C X (prefixValues v hk)) (b.read C X (prefixValues v hk)) = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hx⟩
    obtain ⟨ra, rfl⟩ := (available_iff_ref v hk a).mp ha
    obtain ⟨rb, rfl⟩ := (available_iff_ref v hk b).mp hb
    rcases hx with rfl | rfl | rfl
    · exact ⟨.add, ra, rb, rfl⟩
    · exact ⟨.sub, ra, rb, rfl⟩
    · exact ⟨.mul, ra, rb, rfl⟩
  · rintro ⟨op, a, b, rfl⟩
    refine ⟨_, _, (available_iff_ref v hk _).mpr ⟨a, rfl⟩,
      (available_iff_ref v hk _).mpr ⟨b, rfl⟩, ?_⟩
    cases op with
    | add => exact Or.inl rfl
    | sub => exact Or.inr (Or.inl rfl)
    | mul => exact Or.inr (Or.inr rfl)

private theorem run_snoc_last (q : Program F σ s) (op : BinOp) (a b : Ref F σ s) :
    (q.snoc op a b).run C X (Fin.last s) =
      op.apply (a.read C X (q.run C X)) (b.read C X (q.run C X)) := by
  simp only [Program.run, Fin.lastCases_last]

private theorem run_snoc_castSucc (q : Program F σ s) (op : BinOp) (a b : Ref F σ s)
    (i : Fin s) : (q.snoc op a b).run C X i.castSucc = q.run C X i := by
  simp only [Program.run, Fin.lastCases_castSucc]

/-- Build a program for a prefix without duplicating any of its referenced gates. -/
private theorem realize_prefix (v : Fin s → MvPolynomial σ F)
    (h : ∀ i : Fin s, gateValue (available v i.val) (v i)) (k : ℕ) (hk : k ≤ s) :
    ∃ q : Program F σ k, q.run C X = prefixValues v hk := by
  induction k with
  | zero => exact ⟨.nil, Subsingleton.elim _ _⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih (Nat.le_of_succ_le hk)
    let i : Fin s := ⟨k, hk⟩
    obtain ⟨op, a, b, hop⟩ := (gateValue_iff v (Nat.le_of_succ_le hk) (v i)).mp (h i)
    refine ⟨q.snoc op a b, ?_⟩
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [run_snoc_last, hq]
      exact hop
    · rw [run_snoc_castSucc]
      exact congrFun hq j

/-- Reading a program as a table recovers legal operands at every position. -/
private theorem program_gate (q : Program F σ s) (i : Fin s) :
    gateValue (available (q.run C X) i.val) (q.run C X i) := by
  induction q with
  | nil => exact i.elim0
  | @snoc s q op a b ih =>
    let v := q.run C X
    let v' := (q.snoc op a b).run C X
    have previous (k : ℕ) (hk : k ≤ s) :
        prefixValues v' (Nat.le_succ_of_le hk) = prefixValues v hk := by
      funext j
      exact run_snoc_castSucc q op a b (j.castLE hk)
    cases i using Fin.lastCases with
    | last =>
      apply (gateValue_iff v' (Nat.le_succ s) _).mpr
      refine ⟨op, a, b, ?_⟩
      rw [previous s le_rfl]
      exact (run_snoc_last q op a b).symm
    | cast j =>
      obtain ⟨op', a', b', hj⟩ := (gateValue_iff v j.isLt.le _).mp (ih j)
      apply (gateValue_iff v' (Nat.le_succ_of_le j.isLt.le) _).mpr
      refine ⟨op', a', b', ?_⟩
      rw [previous j.val j.isLt.le]
      exact hj.trans (run_snoc_castSucc q op a b j).symm

/-- The self-contained table model and the project's exact circuits compute precisely
the same formal polynomials with exactly the same number of binary gates. -/
theorem computes_iff {s : ℕ} {p : MvPolynomial σ F} :
    Computes s p ↔ ∃ c : VPVNP.Circuit F σ s, c.polynomial = p := by
  constructor
  · rintro ⟨v, hout, h⟩
    obtain ⟨q, hq⟩ := realize_prefix v h s le_rfl
    obtain ⟨r, hr⟩ := (available_iff_ref v le_rfl p).mp hout
    refine ⟨⟨q, r⟩, ?_⟩
    change r.read C X (q.run C X) = p
    rwa [hq]
  · rintro ⟨c, rfl⟩
    exact ⟨c.program.run C X, (available_iff_ref _ le_rfl _).mpr ⟨c.output, rfl⟩,
      program_gate c.program⟩

end Valiant.Project

end VPVNP
end Computability
end OAI

end

section




/-!
# Selecting the first satisfied literal

Each literal occurrence is indexed by its position. In a satisfied clause, the
first match is unique even when the same literal occurs at several positions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

variable {m : ℕ}

/-- A true bit with no earlier true bit. -/
def firstMatch (f : Fin m → Bool) (i : Fin m) : Bool :=
  decide (f i = true ∧ ∀ j < i, f j = false)

theorem firstMatch_iff (f : Fin m → Bool) (i : Fin m) :
    firstMatch f i = true ↔ f i = true ∧ ∀ j < i, f j = false := by
  simp [firstMatch]

theorem firstMatch_unique (f : Fin m → Bool) {i j : Fin m}
    (hi : firstMatch f i = true) (hj : firstMatch f j = true) : i = j := by
  rw [firstMatch_iff] at hi hj
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (by simpa [hi.1] using hj.2 i h)
  · exact h
  · exact False.elim (by simpa [hj.1] using hi.2 j h)

theorem existsUnique_firstMatch (f : Fin m → Bool) (hf : ∃ i, f i = true) :
    ∃! i, firstMatch f i = true := by
  let s := Finset.univ.filter (fun i => f i = true)
  have hs : s.Nonempty := by simpa [s, Finset.Nonempty] using hf
  let i := s.min' hs
  have hi : firstMatch f i = true := by
    rw [firstMatch_iff]
    refine ⟨by simpa [s] using s.min'_mem hs, fun j hj => ?_⟩
    cases h : f j with
    | false => rfl
    | true => exact (not_le_of_gt hj (s.min'_le j (by simp [s, h]))).elim
  exact ⟨i, hi, fun j hj => firstMatch_unique f hj hi⟩

theorem countP_finRange_eq_one (f : Fin m → Bool) :
    (List.finRange m).countP f = 1 ↔ ∃! i, f i = true := by
  have h := (List.nodup_finRange m).card_eq_countP (P := fun i => f i = true)
  simp only [Bool.decide_eq_true] at h
  rw [← h, Finset.card_eq_one_iff_existsUnique]
  simp

end ExactOne

end VPVNP
end Computability
end OAI

end

section


/-!
# Finite control for a binary query program

A read addresses one of the fixed payload bits and branches to another
control state. The clock counts payload queries. Halting consumes no query.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- One binary query action, either a Boolean halt or a payload-bit read with low and high
successor states. -/
inductive QueryStep (k : Nat) (Q : Type*) where
  | halt (accept : Bool)
  | read (i : Fin k) (low high : Q)

/-- A binary query program on `k` payload bits, specified by its initial state and the action
at each state. -/
structure QueryProgram (k : Nat) (Q : Type*) where
  /-- State from which execution of the query program begins. -/
  start : Q
  /-- Action prescribed at each query state, including the addressed bit and the two successors
  for a read. -/
  step : Q → QueryStep k Q

/-- Evaluate from a given state, spending one unit of fuel per bit read and rejecting a read
attempted at zero fuel. -/
def QueryProgram.eval {k : Nat} {Q : Type*} (p : QueryProgram k Q) (x : Fin k → Bool) :
    Nat → Q → Bool
  | 0, q =>
    match p.step q with
    | .halt b => b
    | .read _ _ _ => false
  | fuel + 1, q =>
    match p.step q with
    | .halt b => b
    | .read i low high => p.eval x fuel (if x i then high else low)

end VPVNP
end Computability
end OAI

end

section



/-!
# Compiling a CNF test into a finite query program

The payload assigns one bit to each Boolean variable. Each occurrence of a literal
becomes one read state. A matching literal skips the rest of its clause, and an
exhausted clause goes directly to the rejecting halt.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessCNF

/-- The bit must equal the indicated polarity for this literal to hold. -/
abbrev Literal (k : ℕ) := Fin k × Bool

/-- A list of clauses over `k` Boolean variables. Each clause is a disjunction of signed
literals. -/
abbrev CNF (k : ℕ) := List (List (Literal k))

/-- Number of literal occurrences, counting repetitions within or across clauses. -/
def literalCount {k : ℕ} (φ : CNF k) : ℕ := (φ.map List.length).sum

/-- An assignment satisfies the formula when every clause contains a literal whose required bit
matches the assignment. -/
def Satisfies {k : ℕ} (φ : CNF k) (x : Fin k → Bool) : Prop :=
  ∀ clause ∈ φ, ∃ l ∈ clause, x l.1 = l.2

variable {k n : ℕ}

/-- The compiler reserves two halting states, then adds one state per literal. -/
def stateCount : CNF k → ℕ
  | [] => 2
  | clause :: φ => stateCount φ + clause.length

/-- The query evaluator has one control state per literal occurrence, in addition to its two
terminal states. -/
abbrev State (φ : CNF k) := Fin (stateCount φ)

theorem card_state (φ : CNF k) : Fintype.card (State φ) = 2 + literalCount φ := by
  rw [Fintype.card_fin]
  induction φ with
  | nil => rfl
  | cons c φ ih => simp [stateCount, literalCount] at ih ⊢; omega

/-- During assembly of a clause, the first matching literal jumps to `pass`
(the start of the remaining clauses), and exhaustion jumps to `reject`. -/
private structure Block (k n : ℕ) extends QueryProgram k (Fin n) where
  pass : Fin n
  reject : Fin n

private def liftStep : QueryStep k (Fin n) → QueryStep k (Fin (n + 1))
  | .halt b => .halt b
  | .read i lo hi => .read i lo.succ hi.succ

private def push (l : Literal k) (b : Block k n) : Block k (n + 1) where
  start := 0
  pass := b.pass.succ
  reject := b.reject.succ
  step := Fin.cases
    (.read l.1 (if l.2 then b.start.succ else b.pass.succ)
      (if l.2 then b.pass.succ else b.start.succ))
    (fun q => liftStep (b.step q))

/-- Existing states keep their behavior when a new literal is prepended. -/
private theorem eval_push_succ (l : Literal k) (b : Block k n) (x : Fin k → Bool)
    (f : ℕ) (q : Fin n) :
    (push l b).eval x f q.succ = b.eval x f q := by
  induction f generalizing q with
  | zero => cases h : b.step q <;> simp [QueryProgram.eval, push, h, liftStep]
  | succ f ih =>
    cases h : b.step q with
    | halt v => simp [QueryProgram.eval, push, h, liftStep]
    | read i lo hi =>
      cases hv : x i <;> simpa [QueryProgram.eval, push, h, liftStep, hv] using
        ih (if x i then hi else lo)

private def compileClause (b : Block k n) : (c : List (Literal k)) → Block k (n + c.length)
  | [] => { b with start := b.reject, pass := b.start }
  | l :: c => push l (compileClause b c)

private def compile : (φ : CNF k) → Block k (stateCount φ)
  | [] => (⟨⟨1, fun q => .halt (q == 1)⟩, 1, 0⟩ : Block k 2)
  | c :: φ => compileClause (compile φ) c

/-- A query program deciding whether the payload satisfies a CNF. -/
def query (φ : CNF k) : QueryProgram k (State φ) := (compile φ).toQueryProgram

private structure Correct (b : Block k n) (x : Fin k → Bool) (budget : ℕ)
    (pass start : Bool) : Prop where
  reject_ok : ∀ f, budget ≤ f → b.eval x f b.reject = false
  pass_ok : ∀ f, budget ≤ f → b.eval x f b.pass = pass
  start_ok : ∀ f, budget ≤ f → b.eval x f b.start = start

private theorem correct_push {b : Block k n} {x : Fin k → Bool} {budget : ℕ}
    {pass start : Bool} (h : Correct b x budget pass start) (l : Literal k) :
    Correct (push l b) x (budget + 1) pass (if x l.1 = l.2 then pass else start) := by
  constructor
  · intro f hf
    exact (eval_push_succ l b x f b.reject).trans (h.reject_ok f (by omega))
  · intro f hf
    exact (eval_push_succ l b x f b.pass).trans (h.pass_ok f (by omega))
  · intro f hf
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    change (push l b).eval x (f + 1) 0 = _
    rw [QueryProgram.eval]
    have hp := (eval_push_succ l b x f b.pass).trans (h.pass_ok f (by omega))
    have hs := (eval_push_succ l b x f b.start).trans (h.start_ok f (by omega))
    cases h₁ : x l.1 <;> cases h₂ : l.2 <;> simp [push, h₁, h₂] at hp hs ⊢ <;> assumption

private def clauseValue (x : Fin k → Bool) (c : List (Literal k)) : Bool :=
  c.any (fun l => x l.1 == l.2)

private theorem eval_step_congr {Q : Type*} (p p' : QueryProgram k Q)
    (h : p.step = p'.step) (x : Fin k → Bool) (f : ℕ) (q : Q) :
    p.eval x f q = p'.eval x f q := by
  induction f generalizing q with
  | zero => simp only [QueryProgram.eval, h]
  | succ f ih =>
    simp only [QueryProgram.eval, h]
    cases p'.step q with
    | halt v => rfl
    | read i lo hi => exact ih _

private theorem correct_clause {b : Block k n} {x : Fin k → Bool} {budget : ℕ}
    {oldPass next : Bool} (h : Correct b x budget oldPass next) (c : List (Literal k)) :
    Correct (compileClause b c) x (budget + c.length) next (clauseValue x c && next) := by
  induction c with
  | nil =>
    have he (f : ℕ) (q : Fin n) :=
      eval_step_congr (compileClause b []).toQueryProgram b.toQueryProgram rfl x f q
    exact ⟨fun f hf => (he f b.reject).trans (h.reject_ok f hf),
      fun f hf => (he f b.start).trans (h.start_ok f hf),
      fun f hf => (he f b.reject).trans (h.reject_ok f hf)⟩
  | cons l c ih =>
    have h' := correct_push ih l
    change Correct (push l (compileClause b c)) x (budget + c.length + 1) next _
    convert h' using 1
    cases hb : x l.1 <;> cases hl : l.2 <;> simp [clauseValue, hb, hl]

private theorem correct_compile (φ : CNF k) (x : Fin k → Bool) :
    ∃ pass, Correct (compile φ) x (literalCount φ) pass (φ.all (clauseValue x)) := by
  induction φ with
  | nil =>
    refine ⟨true, ?_⟩
    constructor <;> intro f _ <;> cases f <;> rfl
  | cons c φ ih =>
    obtain ⟨pass, h⟩ := ih
    refine ⟨φ.all (clauseValue x), ?_⟩
    have hc := correct_clause h c
    simpa [compile, stateCount, literalCount, Nat.add_comm] using hc

/-- At most one query per literal is sufficient, including for formulas with
empty clauses and the empty conjunction. -/
theorem query_eval_iff (φ : CNF k) (x : Fin k → Bool) {fuel : ℕ}
    (hf : literalCount φ ≤ fuel) :
    (query φ).eval x fuel (query φ).start = true ↔ Satisfies φ x := by
  obtain ⟨_, h⟩ := correct_compile φ x
  rw [show (query φ).eval x fuel (query φ).start = φ.all (clauseValue x) from h.start_ok _ hf]
  simp [List.all_eq_true, clauseValue, Satisfies]

end HardnessCNF

end VPVNP
end Computability
end OAI

end

section






/-!
# Exact-one clauses for a CNF verifier

Each clause selects one literal occurrence. Its selector requires that occurrence
to be true and all earlier occurrences to be false. Each implication uses one
filler bit in an exact-one triple. Pairs outside the triangular part of the table
receive a singleton constraint fixing their filler to false.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF
variable {k : ℕ}

/-- An exact-one constraint counts literal occurrences, including repetitions. -/
def Holds (φ : CNF k) (x : Fin k → Bool) : Prop :=
  ∀ c ∈ φ, c.countP (fun l => x l.1 == l.2) = 1

/-- A literal occurrence identified by its clause and its position within that clause. -/
abbrev Occ (φ : CNF k) := Σ c : Fin φ.length, Fin (φ[c].length)

/-- An ordered pair of literal occurrences in the same clause, including pairs with equal
positions. -/
abbrev PairOcc (φ : CNF k) := Σ c : Fin φ.length, Fin (φ[c].length) × Fin (φ[c].length)

/-- Variables of the exact-one encoding, partitioned into original data bits, occurrence
selectors, and pair fillers. -/
abbrev Slot (φ : CNF k) := Fin k ⊕ (Occ φ ⊕ PairOcc φ)

/-- Total number of Boolean variables in the exact-one encoding of the formula. -/
def width (φ : CNF k) := Fintype.card (Slot φ)

/-- Number the three kinds of exact-one variables by finite ordinals. -/
noncomputable def index (φ : CNF k) : Slot φ ≃ Fin (width φ) := Fintype.equivFin _

/-- Variable index in the exact-one encoding that carries the original Boolean variable `v`. -/
noncomputable def data (φ : CNF k) (v : Fin k) : Fin (width φ) := index φ (.inl v)

/-- Variable index marking occurrence `i` as the selected literal in clause `c`. -/
noncomputable def selector (φ : CNF k) (c : Fin φ.length) (i : Fin (φ[c].length)) :
    Fin (width φ) := index φ (.inr (.inl ⟨c,i⟩))

/-- Variable index for the filler attached to ordered positions `i,j` in clause `c`. -/
noncomputable def filler (φ : CNF k) (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    Fin (width φ) := index φ (.inr (.inr ⟨c,i,j⟩))

/-- Recover the original assignment from an assignment to the enlarged exact-one variable set. -/
noncomputable def original (φ : CNF k) (x : Fin (width φ) → Bool) : Fin k → Bool :=
  x ∘ data φ

/-- Bit required by selector `i` when testing occurrence `j ≤ i`. -/
def needed (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    Bool :=
  let l := φ[c][j]
  if j = i then y l.1 == l.2 else !(y l.1 == l.2)

/-- Clause of positive occurrence selectors requiring exactly one selected position in the
original clause. -/
noncomputable def selectorClause (φ : CNF k) (c : Fin φ.length) : List (Literal (width φ)) :=
  (List.finRange (φ[c].length)).map fun i => (selector φ c i, true)

/-- Exact-one constraint comparing a candidate selector at `i` with occurrence `j`, with a
filler bit making the choice canonical. -/
noncomputable def pairClause (φ : CNF k) (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    List (Literal (width φ)) :=
  let l := φ[c][j]
  if j ≤ i then [(selector φ c i, true), (data φ l.1, if j = i then !l.2 else l.2),
    (filler φ c i j, true)]
  else [(filler φ c i j, false)]

/-- The selector clause and all ordered-pair constraints for one clause of the original
formula. -/
noncomputable def rows (φ : CNF k) (c : Fin φ.length) : CNF (width φ) :=
  selectorClause φ c :: (List.finRange (φ[c].length)).flatMap fun i =>
    (List.finRange (φ[c].length)).map (pairClause φ c i)

/-- Polynomial-size exact-one CNF with original, selector and filler variables. -/
noncomputable def augment (φ : CNF k) : CNF (width φ) :=
  (List.finRange φ.length).flatMap (rows φ)

/-- Exactly one occurrence selector in clause `c` is true under assignment `x`. -/
noncomputable def selectedOnce (φ : CNF k) (x : Fin (width φ) → Bool) (c : Fin φ.length) : Prop :=
  (List.finRange (φ[c].length)).countP (fun i => x (selector φ c i)) = 1

private def exactlyOne {n : ℕ} (x : Fin n → Bool) (c : List (Literal n)) : Prop :=
  c.countP (fun l => x l.1 == l.2) = 1

private theorem exactlyOne_selector (φ : CNF k) (x : Fin (width φ) → Bool)
    (c : Fin φ.length) : exactlyOne x (selectorClause φ c) ↔ selectedOnce φ x c := by
  simp [exactlyOne, selectorClause, selectedOnce, List.countP_map, Function.comp_def]

private theorem triple (a b f : Bool) :
    ((if f then 1 else 0) + (if !b then 1 else 0) + (if a then 1 else 0) = 1) ↔
      (a = true → b = true) ∧ f = (b && !a) := by
  cases a <;> cases b <;> cases f <;> decide

private theorem exactlyOne_pair (φ : CNF k) (x : Fin (width φ) → Bool)
    (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    exactlyOne x (pairClause φ c i j) ↔
      if j ≤ i then
        (x (selector φ c i) = true → needed φ (original φ x) c i j = true) ∧
        x (filler φ c i j) = (needed φ (original φ x) c i j && !(x (selector φ c i)))
      else x (filler φ c i j) = false := by
  by_cases hji : j ≤ i
  · have complement :
        (x (data φ (φ[c][j]).1) == (if j = i then !(φ[c][j]).2 else (φ[c][j]).2)) =
          !(needed φ (original φ x) c i j) := by
      unfold needed original
      simp only [Function.comp_apply]
      split <;> cases h : x (data φ (φ[c][j]).1) <;> cases hp : (φ[c][j]).2 <;> rfl
    simp only [exactlyOne, pairClause, if_pos hji, List.countP_cons, List.countP_nil,
      Nat.zero_add, complement, beq_iff_eq]
    exact triple _ _ _
  · cases hx : x (filler φ c i j) <;> simp [exactlyOne, pairClause, hji, hx]

/-- Exact-one satisfaction determines one selector per clause, forces the tested
literal or its negation when that selector is true, and determines every filler bit. -/
theorem holds_augment_iff (φ : CNF k) (x : Fin (width φ) → Bool) :
    Holds (augment φ) x ↔ (∀ c, selectedOnce φ x c) ∧ ∀ c i j,
      if j ≤ i then
        (x (selector φ c i) = true → needed φ (original φ x) c i j = true) ∧
        x (filler φ c i j) = (needed φ (original φ x) c i j && !(x (selector φ c i)))
      else x (filler φ c i j) = false := by
  change (∀ row ∈ augment φ, exactlyOne x row) ↔ _
  have hh : (∀ row ∈ augment φ, exactlyOne x row) ↔
      ∀ c, exactlyOne x (selectorClause φ c) ∧ ∀ i j, exactlyOne x (pairClause φ c i j) := by
    simp only [augment, rows, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.mem_map, forall_exists_index, or_imp, forall_and]
    aesop
  rw [hh]
  simp only [exactlyOne_selector, exactlyOne_pair, forall_and]

end ExactOne

end VPVNP
end Computability
end OAI

end

section



/-!
# Transfer of eventual circuit-size bounds under polynomial projections

Section 15.1 of *VP and VNP differ over every field* uses two properties of a
complete family: its order-`j` polynomial projects from its order-`j+1`
polynomial for `j ≥ 2`, and the hard family projects from orders at most
`A * n ^ b`. Both projections preserve upper bounds on the number of binary
gates. The result below transfers the eventual lower bounds to every order.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- The all-sufficiently-large-length lower bound for each positive exponent. -/
def EventuallySuperpolynomial (size : ℕ → ℕ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ N : ℕ, ∀ n ≥ N, n ^ C < size n

/-- Section 15.1. For every order `m` above a fixed threshold, the floor root
of `m / A` supplies a length `n` whose projected order is at most `m` and whose
lower bound already exceeds `m ^ C`. The projection indices may have gaps. -/
theorem eventualBound_of_polynomialProjection
    {hard complete q : ℕ → ℕ} {A b n₀ : ℕ} (hA : 0 < A) (hb : 0 < b)
    (hhard : EventuallySuperpolynomial hard)
    (hproj : ∀ n ≥ n₀, 2 ≤ q n ∧ q n ≤ A * n ^ b ∧ hard n ≤ complete (q n))
    (hstep : ∀ j ≥ 2, complete j ≤ complete (j + 1)) (C : ℕ) :
    ∃ M : ℕ, ∀ m ≥ M, m ^ C < complete m := by
  obtain ⟨N, hN⟩ := hhard (b * C + 1) (Nat.le_add_left 1 _)
  let K := A * 2 ^ b
  let threshold := max (max N n₀) (max 1 (K ^ C))
  refine ⟨A * threshold ^ b, ?_⟩
  intro m hm
  let n := Nat.nthRoot b (m / A)
  have hn : threshold ≤ n := (Nat.le_nthRoot_iff hb.ne').mpr <|
    (Nat.le_div_iff_mul_le hA).mpr (by simpa [Nat.mul_comm] using hm)
  have hnN : N ≤ n := le_trans ((le_max_left ..).trans (le_max_left ..)) hn
  have hn₀ : n₀ ≤ n := le_trans ((le_max_right ..).trans (le_max_left ..)) hn
  have hn1 : 1 ≤ n := le_trans ((le_max_left ..).trans (le_max_right ..)) hn
  have hK : K ^ C ≤ n := le_trans ((le_max_right ..).trans (le_max_right ..)) hn
  obtain ⟨hq₂, hq, hred⟩ := hproj n hn₀
  have hqm : q n ≤ m := hq.trans <| by
    rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le hA).mp (Nat.pow_nthRoot_le (.inl hb.ne'))
  have hmupper : m ≤ K * n ^ b := calc
    m ≤ (n + 1) ^ b * A := ((Nat.div_lt_iff_lt_mul hA).mp
      (Nat.lt_pow_nthRoot_add_one hb.ne' (m / A))).le
    _ ≤ (2 * n) ^ b * A := Nat.mul_le_mul_right A (Nat.pow_le_pow_left (by omega) b)
    _ = K * n ^ b := by simp [K, mul_pow, Nat.mul_comm, Nat.mul_left_comm]
  calc
    m ^ C ≤ (K * n ^ b) ^ C := Nat.pow_le_pow_left hmupper C
    _ = n ^ (b * C) * K ^ C := by rw [mul_pow, pow_mul, Nat.mul_comm]
    _ ≤ n ^ (b * C + 1) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hK
    _ < hard n := hN n hnN
    _ ≤ complete (q n) := hred
    _ ≤ complete m := monotoneOn_nat_Ici_of_le_succ hstep hq₂ (hq₂.trans hqm) hqm

/-- An eventual lower bound for each exponent excludes every polynomial size
bound, including bounds with a multiplicative constant and a length cutoff. -/
theorem EventuallySuperpolynomial.not_polynomially_bounded {size : ℕ → ℕ}
    (hsize : EventuallySuperpolynomial size) :
    ¬ ∃ A d N : ℕ, ∀ n ≥ N, size n ≤ A * n ^ d := by
  rintro ⟨A, d, N, hupper⟩
  obtain ⟨M, hlower⟩ := hsize (d + 1) (Nat.le_add_left 1 d)
  let n := max A (max M N)
  have hA : A ≤ n := le_max_left ..
  have hM : M ≤ n := (le_max_left ..).trans (le_max_right ..)
  have hN : N ≤ n := (le_max_right ..).trans (le_max_right ..)
  apply (hlower n hM).not_ge
  calc
    size n ≤ A * n ^ d := hupper n hN
    _ ≤ n * n ^ d := Nat.mul_le_mul_right _ hA
    _ = n ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]

end VPVNP
end Computability
end OAI

end

section



/-! # Nonuniform arithmetic complexity classes

A family is indexed by its length. Its variables may be any finite type at that length.
The bounds are asymptotic, with an exponent and a leading constant independent of the
length. Circuits compute formal polynomials, and only Boolean witness variables are
specialized to field elements in the definition of VNP.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

/-- There are fixed natural numbers `A`, `d` and `N` such that `f n ≤ A * n^d` for every `n ≥
N`. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ A d N : ℕ, ∀ n ≥ N, f n ≤ A * n ^ d

variable {F : Type*} [Field F] {σ τ : ℕ → Type} [∀ n, Fintype (σ n)]

/-- A sequence of formal polynomials over `F` whose variable type `σ n` may depend on the index
`n`. -/
abbrev Family (F : Type*) [CommSemiring F] (σ : ℕ → Type) :=
  (n : ℕ) → MvPolynomial (σ n) F

/-- Both the number of variables and the total degree of the indexed polynomials are
polynomially bounded in the family index. -/
def PFamily (p : Family F σ) : Prop :=
  PolynomiallyBounded (fun n => Fintype.card (σ n)) ∧
    PolynomiallyBounded (fun n => (p n).totalDegree)

/-- The family has polynomially bounded variable count and degree, and each member is computed
exactly as a formal polynomial by arithmetic circuits of polynomially bounded size with
arbitrary field constants. -/
def IsVP (p : Family F σ) : Prop :=
  PFamily p ∧ PolynomiallyBounded (fun n => circuitSize (p n))

/-- Substitution of the bits of a single witness, leaving the output variables formal. -/
noncomputable def witnessValue {X W : Type} (bits : W → Bool) :
    MvPolynomial (X ⊕ W) F →+* MvPolynomial X F :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim MvPolynomial.X
    (fun i => MvPolynomial.C (if bits i then 1 else 0)))

/-- A polynomial family obtained by summing a VP family over all Boolean assignments to a
polynomially bounded number of witness variables, with the output variables left formal. -/
def IsVNP (p : Family F σ) : Prop :=
  PFamily p ∧ ∃ (W : ℕ → Type) (inst : ∀ n, Fintype (W n))
    (g : Family F (fun n => σ n ⊕ W n)),
    PolynomiallyBounded (fun n => @Fintype.card _ (inst n)) ∧ IsVP g ∧
    ∀ n, p n = ∑ y : W n → Bool, witnessValue y (g n)

/-- The source index can grow polynomially and need not be monotone. -/
def PProjects (target : Family F τ) (source : Family F σ) : Prop :=
  ∃ r : ℕ → ℕ, PolynomiallyBounded r ∧
    ∀ n, ∃ φ : Projection F (σ (r n)) (τ n), φ.hom (source (r n)) = target n

/-- The family belongs to VNP and every VNP family over the same field is obtained from it by a
polynomially bounded reindexing and substitutions of variables by target variables or field
constants. -/
def VNPComplete (p : Family F σ) : Prop :=
  IsVNP p ∧ ∀ (τ : ℕ → Type) [∀ n, Fintype (τ n)] (g : Family F τ), IsVNP g → PProjects g p

/-- The strict lower bound required in Theorem 1.1 excludes membership in VP. -/
theorem not_isVP_of_eventual_size {p : Family F σ}
    (h : EventuallySuperpolynomial (fun n => circuitSize (p n))) : ¬ IsVP p :=
  fun hp => h.not_polynomially_bounded hp.2

end VPVNP
end Computability
end OAI

end

section


/-!
# Closure properties of nonuniform polynomial bounds

The index of a p-projection may revisit small lengths infinitely often. A global
bound by a power of `n + 1` handles those lengths when composing two indices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PolynomiallyBounded

variable {f g : ℕ → ℕ}

/-- An eventual upper estimate by a polynomially bounded function suffices. -/
theorem of_eventually_le (hg : PolynomiallyBounded g) (N : ℕ)
    (h : ∀ n ≥ N, f n ≤ g n) : PolynomiallyBounded f := by
  obtain ⟨A, d, M, hM⟩ := hg
  refine ⟨A, d, max N M, fun n hn => ?_⟩
  exact (h n ((le_max_left ..).trans hn)).trans (hM n ((le_max_right ..).trans hn))

theorem of_le (hg : PolynomiallyBounded g) (h : ∀ n, f n ≤ g n) : PolynomiallyBounded f :=
  hg.of_eventually_le 0 fun n _ => h n

theorem const (c : ℕ) : PolynomiallyBounded (fun _ => c) :=
  ⟨c, 0, 0, fun _ _ => by simp⟩

theorem id : PolynomiallyBounded (fun n => n) :=
  ⟨1, 1, 0, fun _ _ => by simp⟩

theorem add (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  obtain ⟨A, a, N, hA⟩ := hf
  obtain ⟨B, b, M, hB⟩ := hg
  refine ⟨A + B, max a b, max 1 (max N M), fun n hn => ?_⟩
  have hn₁ : 1 ≤ n := (le_max_left ..).trans hn
  have hN : N ≤ n := (le_max_left ..).trans ((le_max_right ..).trans hn)
  have hM : M ≤ n := (le_max_right ..).trans ((le_max_right ..).trans hn)
  rw [Nat.add_mul]
  apply Nat.add_le_add
  · exact (hA n hN).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn₁ (le_max_left ..)))
  · exact (hB n hM).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn₁ (le_max_right ..)))

theorem mul (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨A, a, N, hA⟩ := hf
  obtain ⟨B, b, M, hB⟩ := hg
  refine ⟨A * B, a + b, max N M, fun n hn => ?_⟩
  calc
    f n * g n ≤ (A * n ^ a) * (B * n ^ b) :=
      Nat.mul_le_mul (hA n ((le_max_left ..).trans hn)) (hB n ((le_max_right ..).trans hn))
    _ = (A * B) * n ^ (a + b) := by rw [pow_add]; ac_rfl

theorem pow (hf : PolynomiallyBounded f) (b : ℕ) :
    PolynomiallyBounded (fun n => f n ^ b) := by
  obtain ⟨A, a, N, hA⟩ := hf
  exact ⟨A ^ b, a * b, N, fun n hn =>
    by simpa only [mul_pow, pow_mul] using Nat.pow_le_pow_left (hA n hn) b⟩

theorem succ : PolynomiallyBounded (fun n => n + 1) := id.add (const 1)

/-- Absorb the finite initial segment of a bounded function into its leading constant. -/
theorem exists_global_bound (hf : PolynomiallyBounded f) :
    ∃ A d : ℕ, ∀ n, f n ≤ A * (n + 1) ^ d := by
  obtain ⟨A, d, N, hA⟩ := hf
  let B := ∑ i ∈ Finset.range N, f i
  refine ⟨A + B, d, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hA n hn).trans (Nat.mul_le_mul (Nat.le_add_right ..)
      (Nat.pow_le_pow_left (Nat.le_succ _) d))
  · have hB : f n ≤ B := Finset.single_le_sum (fun i _ => Nat.zero_le (f i))
      (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    exact hB.trans ((Nat.le_add_left B A).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _))))

/-- Composition preserves polynomial bounds even for nonmonotone index functions. -/
theorem comp (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f (g n)) := by
  obtain ⟨A, d, hA⟩ := hf.exists_global_bound
  exact ((const A).mul ((hg.add (const 1)).pow d)).of_le (fun n => hA (g n))

end PolynomiallyBounded

end VPVNP
end Computability
end OAI

end

section






/-!
# Size of the exact-one verifier

A clause with `m` occurrences has `m` selector bits and `m²` filler bits.
The selector clause has `m` literals, and each of its `m²` pair clauses has at
most three literals. Summing over the original clauses gives quadratic bounds
in the total number of literal occurrences, even in the presence of empty clauses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF

variable {k : ℕ}

/-- Sum of the clause lengths in their indexed presentation. -/
theorem sum_lengths (φ : CNF k) : (∑ c : Fin φ.length, φ[c].length) = literalCount φ := by
  rw [← Fin.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map φ List.length)

private theorem sum_squares_le (φ : CNF k) :
    (∑ c : Fin φ.length, φ[c].length ^ 2) ≤ literalCount φ ^ 2 := by
  calc
    _ ≤ ∑ c : Fin φ.length, φ[c].length * literalCount φ := by
      apply Finset.sum_le_sum
      intro c hc
      rw [pow_two, ← sum_lengths]
      exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun i _ => Nat.zero_le (φ[i].length)) hc)
    _ = _ := by rw [← Finset.sum_mul, sum_lengths, pow_two]

/-- The selectors and fillers use at most `L + L²` new variables. -/
theorem width_le (φ : CNF k) : width φ ≤ k + literalCount φ + literalCount φ ^ 2 := by
  simp only [width, Slot, Occ, PairOcc, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
    Fintype.card_prod, ← pow_two, sum_lengths, Nat.add_assoc]
  exact Nat.add_le_add_left (Nat.add_le_add_left (sum_squares_le φ) _) _

private theorem rows_length (φ : CNF k) (c : Fin φ.length) :
    (rows φ c).length = 1 + φ[c].length ^ 2 := by
  simp [rows, List.length_flatMap, pow_two, Nat.add_comm]

/-- One selector clause is retained per original clause, including empty ones. -/
theorem length_augment_le (φ : CNF k) : (augment φ).length ≤ φ.length + literalCount φ ^ 2 := by
  rw [augment, List.length_flatMap, ← Fin.sum_univ_def]
  simp only [rows_length, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  exact Nat.add_le_add_left (sum_squares_le φ) _

private theorem literalCount_flatMap {A : Type*} (xs : List A) (f : A → CNF k) :
    literalCount (xs.flatMap f) = (xs.map fun a => literalCount (f a)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [literalCount] using ih

private theorem pairClause_length_le (φ : CNF k) (c : Fin φ.length) (i j : Fin (φ[c].length)) :
    (pairClause φ c i j).length ≤ 3 := by
  by_cases h : j ≤ i <;> simp [pairClause, h]

private theorem literalCount_rows_le (φ : CNF k) (c : Fin φ.length) :
    literalCount (rows φ c) ≤ φ[c].length + 3 * φ[c].length ^ 2 := by
  change (selectorClause φ c).length + literalCount _ ≤ _
  simp only [selectorClause, List.length_map, List.length_finRange, literalCount_flatMap,
    ← Fin.sum_univ_def]
  apply Nat.add_le_add_left
  have h (i : Fin (φ[c].length)) : literalCount ((List.finRange _).map (pairClause φ c i)) ≤
      φ[c].length * 3 := by
    simp only [literalCount, List.map_map, ← Fin.sum_univ_def]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => pairClause_length_le φ c i j)
  simpa [pow_two, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)

/-- A bound depending only on literal occurrences, even with arbitrarily many empty clauses. -/
theorem literalCount_augment_le (φ : CNF k) :
    literalCount (augment φ) ≤ literalCount φ + 3 * literalCount φ ^ 2 := by
  rw [augment, literalCount_flatMap, ← Fin.sum_univ_def]
  calc
    _ ≤ ∑ c : Fin φ.length, (φ[c].length + 3 * φ[c].length ^ 2) :=
      Finset.sum_le_sum (fun c _ => literalCount_rows_le φ c)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, sum_lengths, ← Finset.mul_sum]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (sum_squares_le φ)) _

/-- Polynomially bounded families of CNF verifiers retain polynomial width and literal count. -/
theorem polynomial_bounds {k : ℕ → ℕ} (φ : ∀ n, CNF (k n))
    (hk : PolynomiallyBounded k) (hL : PolynomiallyBounded fun n => literalCount (φ n)) :
    PolynomiallyBounded (fun n => width (φ n)) ∧
      PolynomiallyBounded (fun n => literalCount (augment (φ n))) :=
  ⟨((hk.add hL).add (hL.pow 2)).of_le (fun n => width_le (φ n)),
    (hL.add ((PolynomiallyBounded.const 3).mul (hL.pow 2))).of_le
      (fun n => literalCount_augment_le (φ n))⟩

end ExactOne

end VPVNP
end Computability
end OAI

end

section



/-!
# Flattening exact-one literal occurrences for the graph reductions

The graph for Hamiltonian cycles and the graph for cycle covers have one indexed
occurrence per literal position. Each occurrence retains its variable, clause,
and polarity. Multiple occurrences of the same literal stay distinct.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF

variable {k : ℕ}

theorem card_occ (φ : CNF k) : Fintype.card (Occ φ) = literalCount φ := by
  simp only [Occ, Fintype.card_sigma, Fintype.card_fin, sum_lengths]

/-- The graph may number occurrences by any bijection. -/
noncomputable def occurrenceIndex (φ : CNF k) : Fin (literalCount φ) ≃ Occ φ :=
  (Fintype.equivFinOfCardEq (card_occ φ)).symm

/-- The variable, clause and satisfying bit of occurrence `j`. -/
noncomputable def occurrences (φ : CNF k) (j : Fin (literalCount φ)) :
    Fin k × Fin φ.length × Bool :=
  let z := occurrenceIndex φ j
  let lit := φ[z.1][z.2]
  (lit.1, z.1, lit.2)

private theorem countP_eq_one_iff_position {A : Type*} (c : List A) (f : A → Bool) :
    c.countP f = 1 ↔ ∃! j : Fin c.length, f (c.get j) = true := by
  have hc : (List.finRange c.length).map (fun i : Fin c.length => c.get i) = c := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem
  have h := countP_finRange_eq_one (fun i : Fin c.length => f (c.get i))
  have eqCount := congrArg (List.countP f) hc
  rw [List.countP_map] at eqCount
  rw [← eqCount]
  exact h

private theorem existsUnique_occ_iff (φ : CNF k) (x : Fin k → Bool) (a : Fin φ.length) :
    (∃! z : Occ φ, z.1 = a ∧ x (φ[z.1][z.2]).1 = (φ[z.1][z.2]).2) ↔
      ∃! i : Fin φ[a].length, x (φ[a][i]).1 = (φ[a][i]).2 := by
  constructor
  · rintro ⟨⟨c, i⟩, ⟨rfl, hi⟩, hu⟩
    refine ⟨i, hi, fun j hj => ?_⟩
    exact eq_of_heq (Sigma.mk.inj_iff.mp (hu ⟨c, j⟩ ⟨rfl, hj⟩)).2
  · rintro ⟨i, hi, hu⟩
    refine ⟨⟨a, i⟩, ⟨rfl, hi⟩, ?_⟩
    rintro ⟨c, j⟩ ⟨rfl, hj⟩
    exact congrArg (Sigma.mk c) (hu j hj)

/-- Exact-one satisfaction is equivalent to one true numbered occurrence in each clause. -/
theorem holds_iff_unique_occurrence (φ : CNF k) (x : Fin k → Bool) :
    Holds φ x ↔ ∀ a : Fin φ.length, ∃! j : Fin (literalCount φ),
      (occurrences φ j).2.1 = a ∧ x (occurrences φ j).1 = (occurrences φ j).2.2 := by
  simp only [Holds, List.forall_mem_iff_get]
  apply forall_congr'
  intro a
  rw [countP_eq_one_iff_position]
  simp only [beq_iff_eq]
  exact (existsUnique_occ_iff φ x a).symm.trans
    (occurrenceIndex φ).existsUnique_congr_right.symm

/-- Any family member containing an empty clause has zero satisfying assignments. -/
theorem not_holds_of_nil_mem {φ : CNF k} (h : [] ∈ φ) (x : Fin k → Bool) : ¬ Holds φ x := by
  intro hx
  simpa using hx [] h

/-- Without empty clauses the graph's number of clause vertices is at most the literal count. -/
theorem length_le_literalCount_of_nil_notMem {φ : CNF k} (h : [] ∉ φ) :
    φ.length ≤ literalCount φ := by
  rw [← sum_lengths]
  have hpos (c : Fin φ.length) : 1 ≤ φ[c].length := by
    have hc : φ[c] ≠ [] := fun he => h (he ▸ List.getElem_mem _)
    exact List.length_pos_iff.mpr hc
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun c _ => hpos c)

end ExactOne

end VPVNP
end Computability
end OAI

end

section



/-!
# Generating polynomials of satisfying assignments

Weights may live in any commutative semiring. When each weight is a variable or
a scalar, the literal CNF test realizes this polynomial by a projection of the
universal integer family. Its source index is polynomial when the number of
Boolean variables and the total number of literals are polynomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessCNF

open MvPolynomial
open scoped Classical

/-- Sum of assignment weights over the satisfying assignments of a CNF. -/
noncomputable def weightedCNF {R : Type*} [CommSemiring R] {k : ℕ}
    (φ : CNF k) (weight : Fin k → R) : R :=
  ∑ x, if Satisfies φ x then ∏ i, if x i then weight i else 1 else 0


end HardnessCNF
end VPVNP
end Computability
end OAI

end

section



/-!
# Bounding the number of clauses by the number of literals

A single empty clause rejects every assignment. Replacing an inconsistent
formula containing an empty clause by that clause alone controls its clause
count even when the input length bound counts only literal occurrences.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessCNF

variable {k : ℕ}

/-- Keep a single empty clause when the input contains one. -/
def normalizeClauses (φ : CNF k) : CNF k :=
  if [] ∈ φ then [[]] else φ

@[simp] theorem satisfies_normalizeClauses (φ : CNF k) (x : Fin k → Bool) :
    Satisfies (normalizeClauses φ) x ↔ Satisfies φ x := by
  by_cases h : [] ∈ φ
  · have hfalse : ¬ Satisfies φ x := fun hs => by simpa using hs [] h
    rw [iff_false_intro hfalse, normalizeClauses, if_pos h]
    simp [Satisfies]
  · simp [normalizeClauses, h]

@[simp] theorem weightedCNF_normalizeClauses {R : Type*} [CommSemiring R] (φ : CNF k)
    (w : Fin k → R) : weightedCNF (normalizeClauses φ) w = weightedCNF φ w := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Satisfies φ x
  · rw [if_pos ((satisfies_normalizeClauses φ x).mpr hx), if_pos hx]
  · rw [if_neg (fun h => hx ((satisfies_normalizeClauses φ x).mp h)), if_neg hx]

theorem literalCount_normalizeClauses_le (φ : CNF k) :
    literalCount (normalizeClauses φ) ≤ literalCount φ := by
  by_cases h : [] ∈ φ <;> simp [normalizeClauses, h, literalCount]

theorem length_normalizeClauses_le (φ : CNF k) :
    (normalizeClauses φ).length ≤ literalCount φ + 1 := by
  by_cases h : [] ∈ φ
  · simp [normalizeClauses, h]
  · simpa [normalizeClauses, h] using (ExactOne.length_le_literalCount_of_nil_notMem h).trans (Nat.le_succ _)

/-- For a family bounded in literal occurrences, both normalized size measures
are polynomially bounded. -/
theorem normalizeClauses_polynomial_bounds {k : ℕ → ℕ} (φ : ∀ n, CNF (k n))
    (h : PolynomiallyBounded fun n => literalCount (φ n)) :
    PolynomiallyBounded (fun n => literalCount (normalizeClauses (φ n))) ∧
      PolynomiallyBounded (fun n => (normalizeClauses (φ n)).length) :=
  ⟨h.of_le (fun n => literalCount_normalizeClauses_le (φ n)),
    (h.add (.const 1)).of_le (fun n => length_normalizeClauses_le (φ n))⟩

end HardnessCNF

end VPVNP
end Computability
end OAI

end

section



/-!
# The parsimonious conversion from CNF to exact-one constraints

For a satisfying assignment, the selector in each clause marks its first
satisfied literal. This fixes the filler of every implication. Conversely an
assignment meeting the exact-one constraints must use these same selectors
and fillers. Restricting to the input bits therefore gives a bijection.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF

variable {k : ℕ}

private def hit (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length) (i : Fin (φ[c].length)) :
    Bool := y (φ[c][i]).1 == (φ[c][i]).2

private theorem satisfies_iff_hits (φ : CNF k) (y : Fin k → Bool) :
    Satisfies φ y ↔ ∀ c : Fin φ.length, ∃ i, hit φ y c i = true := by
  simp only [Satisfies, List.forall_mem_iff_get, List.exists_mem_iff_get, hit, beq_iff_eq]
  rfl

private theorem firstMatch_iff_needed (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length)
    (i : Fin (φ[c].length)) :
    firstMatch (hit φ y c) i = true ↔ ∀ j ≤ i, needed φ y c i j = true := by
  rw [firstMatch_iff]
  constructor
  · rintro ⟨hi, hprefix⟩ j hj
    rcases eq_or_lt_of_le hj with rfl | hlt
    · simpa [needed, hit] using hi
    · have h := hprefix j hlt
      simpa [needed, hit, hlt.ne] using h
  · intro h
    refine ⟨by simpa [needed, hit] using h i le_rfl, fun j hj => ?_⟩
    simpa [needed, hit, hj.ne] using h j hj.le

/-- The unique extension of a satisfying assignment sets the first-match selectors
and the complementary filler in each active implication. -/
private noncomputable def encode (φ : CNF k) (y : Fin k → Bool) : Fin (width φ) → Bool :=
  fun v => ((index φ).symm v).elim y (Sum.elim
    (fun ⟨c, i⟩ => firstMatch (hit φ y c) i)
    (fun ⟨c, i, j⟩ => if j ≤ i then needed φ y c i j && !(firstMatch (hit φ y c) i) else false))

@[simp] private theorem encode_data (φ : CNF k) (y : Fin k → Bool) (v : Fin k) :
    encode φ y (data φ v) = y v := by simp [encode, data]

@[simp] private theorem original_encode (φ : CNF k) (y : Fin k → Bool) :
    original φ (encode φ y) = y := by funext i; exact encode_data _ _ i

@[simp] private theorem encode_selector (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length)
    (i : Fin (φ[c].length)) : encode φ y (selector φ c i) = firstMatch (hit φ y c) i := by
  simp [encode, selector]

@[simp] private theorem encode_filler (φ : CNF k) (y : Fin k → Bool) (c : Fin φ.length)
    (i j : Fin (φ[c].length)) :
    encode φ y (filler φ c i j) =
      if j ≤ i then needed φ y c i j && !(firstMatch (hit φ y c) i) else false := by
  simp [encode, filler]

private theorem holds_encode (φ : CNF k) (y : Fin k → Bool) (hy : Satisfies φ y) :
    Holds (augment φ) (encode φ y) := by
  apply (holds_augment_iff φ _).2
  refine ⟨fun c => ?_, fun c i j => ?_⟩
  · simp only [selectedOnce, encode_selector, countP_finRange_eq_one]
    exact existsUnique_firstMatch _ ((satisfies_iff_hits φ y).1 hy c)
  · simp only [original_encode, encode_selector, encode_filler]
    by_cases hji : j ≤ i
    · simp only [hji, ite_true, and_true]
      exact fun hs => (firstMatch_iff_needed φ y c i).1 hs j hji
    · simp [hji]

private theorem selector_is_first (φ : CNF k) (x : Fin (width φ) → Bool)
    (hx : Holds (augment φ) x) (c : Fin φ.length) (i : Fin (φ[c].length)) :
    x (selector φ c i) = firstMatch (hit φ (original φ x) c) i := by
  obtain ⟨honce, hpairs⟩ := (holds_augment_iff φ x).1 hx
  have hfirst (a : Fin (φ[c].length)) (ha : x (selector φ c a) = true) :
      firstMatch (hit φ (original φ x) c) a = true := by
    apply (firstMatch_iff_needed _ _ _ _).2
    intro j hj
    have hp := hpairs c a j
    simp only [hj, ite_true] at hp
    exact hp.1 ha
  apply Bool.eq_iff_iff.mpr
  refine ⟨hfirst i, fun hi => ?_⟩
  obtain ⟨a, ha, _⟩ := (countP_finRange_eq_one _).1 (honce c)
  exact firstMatch_unique _ (hfirst a ha) hi ▸ ha

private theorem satisfies_original (φ : CNF k) (x : Fin (width φ) → Bool)
    (hx : Holds (augment φ) x) : Satisfies φ (original φ x) := by
  apply (satisfies_iff_hits _ _).2
  intro c
  obtain ⟨i, hi, _⟩ :=
    (countP_finRange_eq_one _).1 (((holds_augment_iff φ x).1 hx).1 c)
  rw [selector_is_first _ _ hx] at hi
  exact ⟨i, ((firstMatch_iff _ _).1 hi).1⟩

private theorem encode_original (φ : CNF k) (x : Fin (width φ) → Bool)
    (hx : Holds (augment φ) x) : encode φ (original φ x) = x := by
  funext v
  obtain ⟨s, rfl⟩ := (index φ).surjective v
  rcases s with v | ⟨c, i⟩ | ⟨c, i, j⟩
  · exact encode_data φ (original φ x) v
  · exact (encode_selector φ (original φ x) c i).trans (selector_is_first φ x hx c i).symm
  · change encode φ (original φ x) (filler φ c i j) = x (filler φ c i j)
    rw [encode_filler, ← selector_is_first φ x hx]
    have hf := ((holds_augment_iff φ x).1 hx).2 c i j
    by_cases hji : j ≤ i
    · simp only [hji, ite_true] at hf ⊢
      exact hf.2.symm
    · simp only [hji, ite_false] at hf ⊢
      exact hf.symm

/-- Each satisfying input has exactly one extension to the exact-one formula. -/
noncomputable def solutionsEquiv (φ : CNF k) :
    {x : Fin (width φ) → Bool // Holds (augment φ) x} ≃
      {y : Fin k → Bool // Satisfies φ y} where
  toFun x := ⟨original φ x.val, satisfies_original _ _ x.property⟩
  invFun y := ⟨encode φ y.val, holds_encode _ _ y.property⟩
  left_inv x := Subtype.ext (encode_original _ _ x.property)
  right_inv y := Subtype.ext (original_encode φ y.val)

@[simp] theorem solutionsEquiv_apply (φ : CNF k) (x) :
    (solutionsEquiv φ x).val = original φ x.val := rfl

end ExactOne

end VPVNP
end Computability
end OAI

end

section



/-!
# Weighted exact-one reduction

The original variables retain their weights. Every selector and filler has
weight one, so the unique extension of an assignment preserves its contribution
over any commutative semiring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF MvPolynomial
open scoped Classical

variable {k : ℕ} {R : Type*}

/-- Weighted generating function of assignments meeting each clause exactly once. -/
noncomputable def weightedExactOne [CommSemiring R] (φ : CNF k) (w : Fin k → R) : R :=
  ∑ x, if Holds φ x then ∏ i, if x i then w i else 1 else 0

/-- A selector or filler receives the supplied neutral label. -/
private noncomputable def extendLabels {A : Type*} (φ : CNF k) (w : Fin k → A) (neutral : A)
    (i : Fin (width φ)) : A :=
  ((index φ).symm i).elim w (fun _ => neutral)

/-- Extend the weights to all Boolean variables of the exact-one instance. -/
noncomputable def augmentWeight [One R] (φ : CNF k) (w : Fin k → R) : Fin (width φ) → R :=
  extendLabels φ w 1

/-- The extension also preserves variable-or-constant projection labels. -/
noncomputable def augmentProjection {τ : Type*} [One R] (φ : CNF k)
    (w : Projection R (Fin k) τ) : Projection R (Fin (width φ)) τ :=
  extendLabels φ w (.inr 1)

theorem augmentProjection_eval {τ : Type*} [CommSemiring R] (φ : CNF k)
    (w : Projection R (Fin k) τ) (i : Fin (width φ)) :
    (augmentProjection φ w i).elim X C = augmentWeight φ (fun j => (w j).elim X C) i := by
  obtain ⟨s, rfl⟩ := (index φ).surjective i
  cases s <;> simp [augmentProjection, augmentWeight, extendLabels]

private theorem product_augmentWeight [CommSemiring R] (φ : CNF k)
    (w : Fin k → R) (x : Fin (width φ) → Bool) :
    (∏ i, if x i then augmentWeight φ w i else 1) =
      ∏ j, if original φ x j then w j else 1 := by
  rw [← (index φ).prod_comp (fun i => if x i then augmentWeight φ w i else 1),
    Fintype.prod_sum_type]
  simp [augmentWeight, extendLabels, original, data]
  rfl

theorem weightedExactOne_eq_sum [CommSemiring R] (φ : CNF k) (w : Fin k → R) :
    weightedExactOne φ w =
      ∑ x : {x : Fin k → Bool // Holds φ x}, ∏ i, if x.val i then w i else 1 := by
  rw [weightedExactOne, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The exact-one reduction preserves the entire generating polynomial. -/
theorem weightedExactOne_augment [CommSemiring R] (φ : CNF k) (w : Fin k → R) :
    weightedExactOne (augment φ) (augmentWeight φ w) = weightedCNF φ w := by
  have hcnf : weightedCNF φ w =
      ∑ y : {y : Fin k → Bool // Satisfies φ y}, ∏ j, if y.val j then w j else 1 := by
    rw [weightedCNF, ← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [weightedExactOne_eq_sum, hcnf]
  rw [← (solutionsEquiv φ).sum_comp (fun y => ∏ j, if y.val j then w j else 1)]
  exact Finset.sum_congr rfl fun x _ => product_augmentWeight φ w x.val

end ExactOne

end VPVNP
end Computability
end OAI

end

section


/-!
# A dummy variable for exact-one instances

The Hamiltonian graph needs at least one variable track. Adding a final variable
and a singleton negative clause gives each old assignment a unique extension
with the same weight, including when the original instance has no variables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF MvPolynomial
open scoped Classical

variable {k : ℕ} {R τ : Type*}

/-- Embed the old variables as the initial coordinates and force the final one to false. -/
def pad (φ : CNF k) : CNF (k + 1) :=
  [(Fin.last k, false)] :: φ.map (List.map fun l => (l.1.castSucc, l.2))

/-- The forced coordinate carries the unit label. -/
def padProjection [One R] (w : Projection R (Fin k) τ) : Projection R (Fin (k + 1)) τ :=
  Fin.snoc (α := fun _ => τ ⊕ R) w (.inr 1)

@[simp] theorem length_pad (φ : CNF k) : (pad φ).length = φ.length + 1 := by simp [pad]

@[simp] theorem literalCount_pad (φ : CNF k) : literalCount (pad φ) = literalCount φ + 1 := by
  simp [pad, literalCount, List.map_map, Function.comp_def, Nat.add_comm]

/-- The old coordinates retain all the old constraints. -/
theorem holds_pad_iff (φ : CNF k) (x : Fin (k + 1) → Bool) :
    Holds (pad φ) x ↔ x (Fin.last k) = false ∧ Holds φ (fun i => x i.castSucc) := by
  cases hx : x (Fin.last k) <;>
    simp [Holds, pad, List.countP_map, Function.comp_def, hx]

/-- The added variable has weight one in every satisfying product because it is forced false. -/
theorem weightedExactOne_pad [CommSemiring R] (φ : CNF k) (w : Fin (k + 1) → R) :
    weightedExactOne (pad φ) w = weightedExactOne φ (fun i => w i.castSucc) := by
  let e := Fin.snocEquiv (n := k) (fun _ => Bool)
  unfold weightedExactOne
  rw [← e.sum_comp (fun x => if Holds (pad φ) x then ∏ i, if x i then w i else 1 else 0),
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [holds_pad_iff, e, Fin.snocEquiv_apply, Fin.snoc_last, Fin.snoc_castSucc,
    Bool.true_eq_false, false_and, ite_false, Finset.sum_const_zero, zero_add, true_and]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Holds φ x
  · simp [hx, Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc]
  · simp [hx]

/-- Variable-or-constant labels of the original exact-one polynomial lift to the padded graph. -/
theorem weightedExactOne_padProjection [CommSemiring R] (φ : CNF k) (w : Projection R (Fin k) τ) :
    weightedExactOne (pad φ) (fun i => (padProjection w i).elim X C) =
      weightedExactOne φ (fun i => (w i).elim X C) := by
  simp [weightedExactOne_pad, padProjection]

end ExactOne

end VPVNP
end Computability
end OAI

end

section






/-!
# Choosing among weighted CNFs

Each alternative has a selector bit and a private block of data bits. The selector
bits are one-hot. The chosen formula is enforced, while every unchosen block is
filled with zeros. Consequently an accepted local assignment extends uniquely
to an accepted global assignment, even for zero-variable formulas.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessAlternatives

open HardnessCNF
open scoped Classical

variable {I : Type*} [Fintype I] {k : I → ℕ}

/-- Boolean variables of the disjoint-alternatives formula. Each alternative gets a selector
and its own block of local variables. -/
abbrev Slot (k : I → ℕ) := I ⊕ (Σ i, Fin (k i))

/-- The total number of selectors and local variables in the alternatives formula. -/
def width (k : I → ℕ) := Fintype.card (Slot k)

/-- A bijection from the tagged selector and local-variable slots onto the finite set of CNF
variable indices. -/
noncomputable def index (k : I → ℕ) : Slot k ≃ Fin (width k) := Fintype.equivFin _

theorem width_le {K : ℕ} (h : ∀ i, k i ≤ K) :
    width k ≤ Fintype.card I * (1 + K) := by
  simp only [width, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Nat.mul_add,
    Nat.mul_one]
  apply Nat.add_le_add_left
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)

private noncomputable def flag (k : I → ℕ) (i : I) := index k (.inl i)
private noncomputable def bit (k : I → ℕ) (i : I) (j : Fin (k i)) := index k (.inr ⟨i,j⟩)

private noncomputable def allIndices (I : Type*) [Fintype I] : List I :=
  (Finset.univ : Finset I).toList

@[simp] private theorem mem_allIndices (i : I) : i ∈ allIndices I := by simp [allIndices]

@[simp] private theorem length_allIndices : (allIndices I).length = Fintype.card I := by
  simp [allIndices]

private noncomputable def exclusive (k : I → ℕ) (i : I) : CNF (width k) :=
  (allIndices I).map fun j => [(flag k i, false), (flag k j, decide (i = j))]

private noncomputable def inactive (k : I → ℕ) (i : I) : CNF (width k) :=
  (List.finRange (k i)).map fun j => [(flag k i, true), (bit k i j, false)]

private noncomputable def guarded (φ : ∀ i, CNF (k i)) (i : I) : CNF (width k) :=
  if [] ∈ φ i then [[(flag k i, false)]] else
    (φ i).map fun c => (flag k i, false) :: c.map fun l => (bit k i l.1, l.2)

/-- Select exactly one formula, enforcing its clauses and zeroing all inactive variables. -/
noncomputable def formula (φ : ∀ i, CNF (k i)) : CNF (width k) :=
  ((allIndices I).map fun i => (flag k i, true)) ::
    (allIndices I).flatMap fun i => exclusive k i ++ inactive k i ++ guarded φ i

private def Hits {n : ℕ} (x : Fin n → Bool) (c : List (Literal n)) : Prop :=
  ∃ l ∈ c, x l.1 = l.2

private theorem sat_map {A : Type*} {n : ℕ} (xs : List A) (f : A → List (Literal n))
    (x : Fin n → Bool) : Satisfies (xs.map f) x ↔ ∀ i ∈ xs, Hits x (f i) := by
  simp [Satisfies, Hits]

private theorem sat_append {n : ℕ} (φ ψ : CNF n) (x : Fin n → Bool) :
    Satisfies (φ ++ ψ) x ↔ Satisfies φ x ∧ Satisfies ψ x := by
  simp [Satisfies, or_imp, forall_and]

private theorem sat_exclusive (i : I) (x : Fin (width k) → Bool) :
    Satisfies (exclusive k i) x ↔ ∀ j, x (flag k i) = true → x (flag k j) = true → i = j := by
  rw [exclusive, sat_map]
  simp only [mem_allIndices, forall_const, Hits, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp]
  constructor
  · intro h j hi hj
    simpa [hi, hj] using h j
  · intro h j
    cases hi : x (flag k i) <;> cases hj : x (flag k j) <;> by_cases e : i = j <;>
      simp_all
    exact e (h j hj)

private theorem sat_inactive (i : I) (x : Fin (width k) → Bool) :
    Satisfies (inactive k i) x ↔ ∀ j, x (flag k i) = false → x (bit k i j) = false := by
  rw [inactive, sat_map]
  cases h : x (flag k i) <;> simp [Hits, h]

private theorem sat_guarded (φ : ∀ i, CNF (k i)) (i : I) (x : Fin (width k) → Bool) :
    Satisfies (guarded φ i) x ↔ x (flag k i) = true → Satisfies (φ i) (fun j => x (bit k i j)) := by
  by_cases he : [] ∈ φ i
  · have hn : ¬ Satisfies (φ i) (fun j => x (bit k i j)) := by
      intro h
      simpa using h [] he
    rw [guarded, if_pos he]
    simp only [hn, imp_false]
    simp [Satisfies]
  · rw [guarded, if_neg he, sat_map]
    have hit (c : List (Literal (k i))) :
        Hits x ((flag k i, false) :: c.map (fun l => (bit k i l.1, l.2))) ↔
          x (flag k i) = false ∨ Hits (fun j => x (bit k i j)) c := by
      simp only [Hits, List.mem_cons, exists_eq_or_imp, List.mem_map]
      aesop
    constructor
    · intro h hs c hc
      exact ((hit c).1 (h c hc)).resolve_left (by simp [hs])
    · intro h c hc
      apply (hit c).2
      cases hs : x (flag k i) with
      | false => exact Or.inl rfl
      | true => exact Or.inr (h hs c hc)

private theorem sat_formula (φ : ∀ i, CNF (k i)) (x : Fin (width k) → Bool) :
    Satisfies (formula φ) x ↔ (∃ i, x (flag k i) = true) ∧ ∀ i,
      (∀ j, x (flag k i) = true → x (flag k j) = true → i = j) ∧
      (∀ j, x (flag k i) = false → x (bit k i j) = false) ∧
      (x (flag k i) = true → Satisfies (φ i) (fun j => x (bit k i j))) := by
  have cons {n : ℕ} (c : List (Literal n)) (ψ : CNF n) (y : Fin n → Bool) :
      Satisfies (c :: ψ) y ↔ Hits y c ∧ Satisfies ψ y := by
    simp [Hits, Satisfies]
  have flat {n : ℕ} (l : List I) (f : I → CNF n) (y : Fin n → Bool) :
      Satisfies (l.flatMap f) y ↔ ∀ a ∈ l, Satisfies (f a) y := by
    simp [Satisfies]
    aesop
  rw [formula, cons, flat]
  simp [Hits, sat_append, sat_guarded, sat_exclusive, sat_inactive]

private noncomputable def encode (i : I) (y : Fin (k i) → Bool) : Fin (width k) → Bool :=
  fun z => ((index k).symm z).elim (fun j => decide (j = i))
    (fun s => Function.update (fun j (_ : Fin (k j)) => false) i y s.1 s.2)

@[simp] private theorem encode_flag (i j : I) (y : Fin (k i) → Bool) :
    encode i y (flag k j) = decide (j = i) := by simp [encode, flag]

@[simp] private theorem encode_bit_self (i : I) (y : Fin (k i) → Bool) (z : Fin (k i)) :
    encode i y (bit k i z) = y z := by simp [encode, bit]

private theorem encode_bit_other {i j : I} (hne : j ≠ i) (y : Fin (k i) → Bool) (z : Fin (k j)) :
    encode i y (bit k j z) = false := by simp [encode, bit, hne]

private theorem sat_encode (φ : ∀ i, CNF (k i)) (i : I) (y : Fin (k i) → Bool) :
    Satisfies (formula φ) (encode i y) ↔ Satisfies (φ i) y := by
  rw [sat_formula]
  constructor
  · rintro ⟨_, h⟩
    simpa using (h i).2.2 (by simp)
  · intro h
    refine ⟨⟨i, by simp⟩, fun j => ⟨?_, ?_, ?_⟩⟩
    · simp +contextual
    · intro z hj
      exact encode_bit_other (by simpa using hj) _ _
    · intro hj
      have : j = i := by simpa using hj
      subst j
      simpa using h

private noncomputable def solutions (φ : ∀ i, CNF (k i)) :
    (Σ i, {y : Fin (k i) → Bool // Satisfies (φ i) y}) ≃
      {x : Fin (width k) → Bool // Satisfies (formula φ) x} := by
  let f : (Σ i, {y : Fin (k i) → Bool // Satisfies (φ i) y}) →
      {x : Fin (width k) → Bool // Satisfies (formula φ) x} :=
    fun ⟨i,y⟩ => ⟨encode i y.val, (sat_encode φ i y.val).2 y.property⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i,y⟩ ⟨j,z⟩ he
    have h : encode i y.val = encode j z.val := congrArg Subtype.val he
    have hij : i = j := by simpa using congrFun h (flag k i)
    subst j
    congr 1
    apply Subtype.ext
    funext u
    simpa using congrFun h (bit k i u)
  · rintro ⟨x,hx⟩
    obtain ⟨⟨i,hi⟩, hr⟩ := (sat_formula φ x).1 hx
    let y (z : Fin (k i)) := x (bit k i z)
    refine ⟨⟨i, y, (hr i).2.2 hi⟩, Subtype.ext ?_⟩
    change encode i y = x
    funext z
    obtain ⟨s,rfl⟩ := (index k).surjective z
    cases s with
    | inl j =>
      change encode i y (flag k j) = x (flag k j)
      by_cases e : j = i
      · subst j; simp [hi]
      · have hj : x (flag k j) = false := by
          cases h : x (flag k j)
          · rfl
          · exact (e ((hr j).1 i h hi)).elim
        simp [hj, e]
    | inr s =>
      obtain ⟨j,u⟩ := s
      change encode i y (bit k j u) = x (bit k j u)
      by_cases e : j = i
      · subst j; simp [y]
      · rw [encode_bit_other e]
        symm
        apply (hr j).2.1 u
        cases h : x (flag k j)
        · rfl
        · exact (e ((hr j).1 i h hi)).elim

/-- Label each selector and each data slot. The labels can be weights or any
parameters from which the weights will be built. -/
noncomputable def weight {A : Type*} (k : I → ℕ) (a : I → A) (w : ∀ i, Fin (k i) → A)
    (z : Fin (width k)) : A := ((index k).symm z).elim a (fun s => w s.1 s.2)

@[simp] theorem weight_selector {A : Type*} (k : I → ℕ) (a : I → A) (w : ∀ i, Fin (k i) → A)
    (i : I) : weight k a w (index k (.inl i)) = a i := by simp [weight]

@[simp] theorem weight_data {A : Type*} (k : I → ℕ) (a : I → A) (w : ∀ i, Fin (k i) → A)
    (i : I) (j : Fin (k i)) : weight k a w (index k (.inr ⟨i,j⟩)) = w i j := by simp [weight]

variable {R : Type*} [CommSemiring R]

private theorem prod_encode (a : I → R) (w : ∀ i, Fin (k i) → R) (i : I) (y : Fin (k i) → Bool) :
    (∏ z, if encode i y z then weight k a w z else 1) =
      a i * ∏ j, if y j then w i j else 1 := by
  rw [← (index k).prod_comp (fun z => if encode i y z then weight k a w z else 1),
    Fintype.prod_sum_type, Fintype.prod_sigma]
  have sel (j : I) : encode i y (index k (.inl j)) = decide (j = i) := encode_flag i j y
  simp only [sel, decide_eq_true_eq, weight_selector, weight_data, Finset.prod_ite_eq',
    Finset.mem_univ, ite_true]
  congr 1
  rw [Finset.prod_eq_single i]
  · have self (j : Fin (k i)) : encode i y (index k (.inr ⟨i,j⟩)) = y j :=
      encode_bit_self i y j
    simp [self]
  · intro j _ hj
    have other (z : Fin (k j)) : encode i y (index k (.inr ⟨j,z⟩)) = false :=
      encode_bit_other hj y z
    simp [other]
  · simp

private theorem weightedCNF_eq_sum_subtype {n : ℕ} (φ : CNF n) (w : Fin n → R) :
    weightedCNF φ w = ∑ x : {x : Fin n → Bool // Satisfies φ x},
      ∏ j, if x.val j then w j else 1 := by
  rw [weightedCNF, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The polynomial of the selector formula is the sum of the individual polynomials,
each multiplied by the weight of its selected branch. -/
theorem weighted_formula (φ : ∀ i, CNF (k i)) (a : I → R) (w : ∀ i, Fin (k i) → R) :
    weightedCNF (formula φ) (weight k a w) = ∑ i, a i * weightedCNF (φ i) (w i) := by
  simp only [weightedCNF_eq_sum_subtype, Finset.mul_sum]
  rw [← (solutions φ).sum_comp (fun x => ∏ j, if x.val j then weight k a w j else 1),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl fun x _ => prod_encode a w i x.val

private theorem literalCount_append {n : ℕ} (a b : CNF n) :
    literalCount (a ++ b) = literalCount a + literalCount b := by simp [literalCount]

private theorem literalCount_flatMap_le {n : ℕ} {A : Type*} (xs : List A) (f : A → CNF n)
    (M : ℕ) (h : ∀ i, literalCount (f i) ≤ M) :
    literalCount (xs.flatMap f) ≤ xs.length * M := by
  induction xs with
  | nil => simp [literalCount]
  | cons a xs ih =>
    simpa [literalCount_append, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h a) ih

private theorem literalCount_guarded_le (φ : ∀ i, CNF (k i)) (i : I) :
    literalCount (guarded φ i) ≤ 1 + 2 * literalCount (φ i) := by
  by_cases he : [] ∈ φ i
  · simp [guarded, he, literalCount]
  · rw [guarded, if_neg he]
    generalize hv : φ i = cs at *
    clear hv
    induction cs with
    | nil => simp [literalCount]
    | cons c cs ih =>
      have hn : c ≠ [] := by aesop
      have hp : 0 < c.length := List.length_pos_iff.mpr hn
      have htail := ih (by aesop)
      simp only [List.map_cons, literalCount, List.sum_cons, List.length_map, List.length_cons]
      simp only [literalCount] at htail
      omega

private theorem literalCount_map_const {A : Type*} {n : ℕ} (xs : List A) (f : A → List (Literal n))
    (v : ℕ) (hv : ∀ a, (f a).length = v) :
    literalCount (xs.map f) = xs.length * v := by
  induction xs with
  | nil => simp [literalCount]
  | cons x xs ih => simpa [literalCount, hv, Nat.succ_mul, Nat.add_comm] using ih

/-- A uniform bound in the number of alternatives, the largest block width,
and the largest literal count. Empty clauses are detected before guarding. -/
theorem literalCount_formula_le (φ : ∀ i, CNF (k i)) {K L : ℕ}
    (hk : ∀ i, k i ≤ K) (hl : ∀ i, literalCount (φ i) ≤ L) :
    literalCount (formula φ) ≤ Fintype.card I +
      Fintype.card I * (2 * Fintype.card I + 2 * K + 1 + 2 * L) := by
  rw [formula]
  change ((allIndices I).map fun i => (flag k i, true)).length + literalCount _ ≤ _
  simp only [List.length_map, length_allIndices]
  apply Nat.add_le_add_left
  refine (literalCount_flatMap_le (allIndices I) _
    (2 * Fintype.card I + 2 * K + 1 + 2 * L) ?_).trans_eq (by simp)
  intro i
  have he : literalCount (exclusive k i) = Fintype.card I * 2 := by
    rw [exclusive, literalCount_map_const (v := 2) (hv := fun _ => rfl), length_allIndices]
  have ha : literalCount (inactive k i) = k i * 2 := by
    rw [inactive, literalCount_map_const (v := 2) (hv := fun _ => rfl), List.length_finRange]
  simp only [literalCount_append, he, ha]
  have := literalCount_guarded_le φ i
  have := hk i
  have := hl i
  omega

end HardnessAlternatives

end VPVNP
end Computability
end OAI

end

section



/-!
# Boolean formulas with scalar and variable labels

Each selected bit contributes a scalar and, optionally, a single formal
variable. The accepted assignments of the formula index a sum of monomials.
Selector bits implement finite scalar linear combinations of these sums.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Hardness

open MvPolynomial HardnessCNF
open scoped Classical

/-- A Boolean formula whose true variables contribute a scalar and, optionally, a polynomial
variable to the weight of an assignment. -/
structure MarkedCNF (F V : Type*) where
  /-- Number of Boolean variables in the marked formula. -/
  width : ℕ
  /-- The clauses selecting the assignments whose weights enter the polynomial. -/
  clauses : CNF width
  /-- Coefficient factor contributed when a given Boolean variable is true. -/
  scalar : Fin width → F
  /-- Optional polynomial variable contributed when a given Boolean variable is true. -/
  label : Fin width → Option V

namespace MarkedCNF

variable {F V : Type*} [CommSemiring F]

/-- The formal polynomial specified by the selected scalar and variable labels. -/
noncomputable def value (m : MarkedCNF F V) : MvPolynomial V F :=
  weightedCNF m.clauses (fun i => C (m.scalar i) * (m.label i).elim 1 X)

/-- The empty CNF with no Boolean variables has a single assignment of weight one. -/
def unit (F V : Type*) : MarkedCNF F V := ⟨0, [], Fin.elim0, Fin.elim0⟩

@[simp] theorem value_unit : (unit F V).value = 1 := by
  have hs (x : Fin 0 → Bool) : Satisfies [] x := fun _ h => nomatch h
  have hp (x : Fin 0 → Bool) :
      (∏ i : Fin 0, if x i then C (i.elim0 : F) * (i.elim0 : Option V).elim 1 X else 1) = 1 :=
    Finset.prod_eq_one fun i _ => i.elim0
  change weightedCNF ([] : CNF 0)
    (fun i => C (i.elim0 : F) * (i.elim0 : Option V).elim 1 X) = 1
  simp only [weightedCNF, hs, ite_true, hp]
  simp

variable {I : Type*} [Fintype I]

/-- The selector for a summand carries that summand's scalar. All data bits
retain the scalar and optional variable of the corresponding private block. -/
noncomputable def linearCombination (a : I → F) (m : I → MarkedCNF F V) :
    MarkedCNF F V where
  width := HardnessAlternatives.width (fun i => (m i).width)
  clauses := HardnessAlternatives.formula (fun i => (m i).clauses)
  scalar := HardnessAlternatives.weight _ a (fun i => (m i).scalar)
  label := HardnessAlternatives.weight _ (fun _ => none) (fun i => (m i).label)

theorem value_linearCombination (a : I → F) (m : I → MarkedCNF F V) :
    (linearCombination a m).value = ∑ i, C (a i) * (m i).value := by
  let k := fun i => (m i).width
  have hweight (j : Fin (HardnessAlternatives.width k)) :
      C ((linearCombination a m).scalar j) *
        ((linearCombination a m).label j).elim 1 X =
        HardnessAlternatives.weight k (fun i => C (a i))
          (fun i j => C ((m i).scalar j) * ((m i).label j).elim 1 X) j := by
    obtain ⟨s, rfl⟩ := (HardnessAlternatives.index k).surjective j
    rcases s with i | ⟨i, j⟩ <;> simp [linearCombination, k]
  change weightedCNF (HardnessAlternatives.formula fun i => (m i).clauses)
      (fun j => C ((linearCombination a m).scalar j) *
        ((linearCombination a m).label j).elim 1 X) = _
  rw [funext hweight]
  exact HardnessAlternatives.weighted_formula (fun i => (m i).clauses) (fun i => C (a i))
    (fun i j => C ((m i).scalar j) * ((m i).label j).elim 1 X)

end MarkedCNF
end Hardness

end VPVNP
end Computability
end OAI

end

section



/-! # Homogeneous components of the circuit grammar

In the grammar of Section 8.1 the degree-one states are arbitrary linear forms, and a
multiplication gate of degree `d` convolves the component lists of its input gates.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]



/-- The degree-`d` component of a product uses precisely the degree splits `i + j = d`. -/
theorem homogeneousComponent_mul (d : ℕ) (p q : MvPolynomial σ R) :
    homogeneousComponent d (p * q) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal d,
      homogeneousComponent ij.1 p * homogeneousComponent ij.2 q := by
  classical
  letI : GradedAlgebra (homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
  let A := homogeneousSubmodule σ R
  have component (p : MvPolynomial σ R) (i : ℕ) :
      (DirectSum.decompose A p i : MvPolynomial σ R) = homogeneousComponent i p :=
    decomposition.decompose'_apply p i
  simp_rw [← component]
  rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply]
  apply Finset.sum_subset
  · intro ij hij
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (Finset.mem_filter.mp hij).2
  · intro ij hsum hout
    have h : ij.1 ∉ (DirectSum.decompose A p).support ∨
        ij.2 ∉ (DirectSum.decompose A q).support := by
      by_contra! hin
      exact hout (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hin,
        Finset.HasAntidiagonal.mem_antidiagonal.mp hsum⟩)
    rcases h with h | h <;> simp [DFinsupp.notMem_support_iff.mp h]

/-- The linear component is the linear combination of the individual variables with
coefficients given by their degree-one monomials. -/
theorem homogeneousComponent_one_eq_sum [Fintype σ] (p : MvPolynomial σ R) :
    homogeneousComponent 1 p = ∑ x, C (p.coeff (Finsupp.single x 1)) * X x := by
  classical
  ext1 m
  rw [coeff_homogeneousComponent, coeff_sum]
  by_cases h : m.degree = 1
  · have hc : (Finsupp.toMultiset m).card = 1 := by rw [Finsupp.card_toMultiset]; exact h
    obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hc
    have hm : m = Finsupp.single x 1 := by
      simpa using congrArg Multiset.toFinsupp hx
    subst m
    simp [coeff_X, Finsupp.single_left_inj one_ne_zero]
  · have hx (x : σ) : Finsupp.single x 1 ≠ m := by
      rintro rfl
      exact h (Finsupp.degree_single _ _)
    simp [h, coeff_X, hx]

end VPVNP
end Computability
end OAI

end

section




/-!
# Eliminating same-degree dependencies in a circuit

For degrees at least two, every homogeneous piece of a gate lies in the linear span
of products of two positive-degree pieces of circuit nodes. Constants, additions,
subtractions and degree-zero factors can thus be absorbed into the scalar labels
of the graded grammar in Section 8.1 of *VP and VNP differ over every field*.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {R V H : Type*} [CommRing R] {n : ℕ}

private theorem positive_component_C (a : R) {k : ℕ} (hk : k ≠ 0) :
    homogeneousComponent k (C a : MvPolynomial V R) = 0 := by
  simp [homogeneousComponent_of_mem (isHomogeneous_C V a), hk]

/-- The start state, all variable inputs and one state per binary gate. -/
abbrev Circuit.GrammarSlots (V : Type*) (n : ℕ) := Option (V ⊕ Fin n)

/-- Read the polynomial at a grammar slot, returning the circuit output at the start slot, `X
v` at a variable slot, or the computed gate polynomial at a gate slot. -/
noncomputable def Circuit.slotPolynomial (c : Circuit R V n) :
    Circuit.GrammarSlots V n → MvPolynomial V R
  | none => c.polynomial
  | some (.inl v) => X v
  | some (.inr j) => c.program.run C X j

private theorem Ref.read_mem_or_constant {p : Program R V n} (r : Ref R V n)
    (v : H → MvPolynomial V R) (hX : ∀ a, X a ∈ Set.range v)
    (hp : ∀ j, p.run C X j ∈ Set.range v) :
    r.read C X (p.run C X) ∈ Set.range v ∨ ∃ a, r.read C X (p.run C X) = C a := by
  cases r with
  | const a => exact Or.inr ⟨a, rfl⟩
  | var x => exact Or.inl (hX x)
  | gate j => exact Or.inl (hp j)

private theorem Ref.component_mem {p : Program R V n} (r : Ref R V n)
    (M : Submodule R (MvPolynomial V R)) {d : ℕ} (hd : 1 < d)
    (hp : ∀ j, homogeneousComponent d (p.run C X j) ∈ M) :
    homogeneousComponent d (r.read C X (p.run C X)) ∈ M := by
  cases r with
  | const a => simp [Ref.read, positive_component_C a (by omega : d ≠ 0)]
  | var x =>
    rw [Ref.read, homogeneousComponent_of_mem (isHomogeneous_X R x)]
    split
    · omega
    · exact M.zero_mem
  | gate j => exact hp j

private theorem component_product_mem {d : ℕ} (p q : MvPolynomial V R)
    (M : Submodule R (MvPolynomial V R)) (v : H → MvPolynomial V R)
    (hp : homogeneousComponent d p ∈ M) (hq : homogeneousComponent d q ∈ M)
    (hpv : p ∈ Set.range v ∨ ∃ a, p = C a) (hqv : q ∈ Set.range v ∨ ∃ a, q = C a)
    (hprod : ∀ i j a b, 0 < a → 0 < b → a + b = d →
      homogeneousComponent a (v i) * homogeneousComponent b (v j) ∈ M) :
    homogeneousComponent d (p * q) ∈ M := by
  rw [homogeneousComponent_mul]
  apply M.sum_mem
  rintro ⟨a, b⟩ hab
  have hab' : a + b = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  by_cases ha : a = 0
  · subst a
    simp only [zero_add] at hab'
    subst b
    simpa only [homogeneousComponent_zero, smul_eq_C_mul] using M.smul_mem (p.coeff 0) hq
  by_cases hb : b = 0
  · subst b
    simp only [add_zero] at hab'
    subst a
    simpa only [homogeneousComponent_zero, smul_eq_C_mul, mul_comm] using M.smul_mem (q.coeff 0) hp
  rcases hpv with ⟨i, rfl⟩ | ⟨x, rfl⟩
  · rcases hqv with ⟨j, rfl⟩ | ⟨y, rfl⟩
    · exact hprod i j a b (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hab'
    · simp [positive_component_C y hb]
  · simp [positive_component_C x ha]

private theorem Program.components_mem (p : Program R V n) (M : Submodule R (MvPolynomial V R))
    (v : H → MvPolynomial V R) {d : ℕ} (hd : 1 < d) (hX : ∀ a, X a ∈ Set.range v)
    (hprod : ∀ i j a b, 0 < a → 0 < b → a + b = d →
      homogeneousComponent a (v i) * homogeneousComponent b (v j) ∈ M)
    (hp : ∀ j, p.run C X j ∈ Set.range v) :
    ∀ j, homogeneousComponent d (p.run C X j) ∈ M := by
  induction p with
  | nil => exact fun j ↦ j.elim0
  | snoc p op a b ih =>
    have hprev : ∀ j, p.run C X j ∈ Set.range v := fun j ↦
      by simpa only [Program.run, Fin.lastCases_castSucc] using hp j.castSucc
    have ha := a.component_mem M hd (ih hprev)
    have hb := b.component_mem M hd (ih hprev)
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [Program.run, Fin.lastCases_last]
      cases op with
      | add => simpa only [BinOp.apply, map_add] using M.add_mem ha hb
      | sub => simpa only [BinOp.apply, map_sub] using M.sub_mem ha hb
      | mul =>
        exact component_product_mem _ _ M v ha hb (a.read_mem_or_constant v hX hprev)
          (b.read_mem_or_constant v hX hprev) hprod
    · simpa only [Program.run, Fin.lastCases_castSucc] using ih hprev i

/-- Every graded state of degree above one is in the span of lower-degree productions,
using the specified slots for this very circuit, including its output slot. -/
theorem Circuit.slot_component_mem (c : Circuit R V n) {d : ℕ} (hd : 1 < d)
    (M : Submodule R (MvPolynomial V R))
    (hprod : ∀ i j a b, 0 < a → 0 < b → a + b = d →
      homogeneousComponent a (c.slotPolynomial i) * homogeneousComponent b (c.slotPolynomial j)
        ∈ M) :
    ∀ h, homogeneousComponent d (c.slotPolynomial h) ∈ M := by
  have hX : ∀ a, X a ∈ Set.range c.slotPolynomial := fun a ↦ ⟨some (.inl a), rfl⟩
  have hp : ∀ j, c.program.run C X j ∈ Set.range c.slotPolynomial :=
    fun j ↦ ⟨some (.inr j), rfl⟩
  have hgate := c.program.components_mem M c.slotPolynomial hd hX hprod hp
  rintro (_ | (a | j))
  · exact c.output.component_mem M hd hgate
  · exact (Ref.var a : Ref R V n).component_mem M hd hgate
  · exact hgate j

end VPVNP
end Computability
end OAI

end

section



/-!
# Finite ordered parses

A parse of layer `d` has `d + 1` terminal occurrences. At a binary production, the
split records the layer of the left child, and the two state labels specify the roots
of the child parses. The root state of the entire parse is supplied by the grammar.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

universe u v

/-- Ordered binary parse with terminal variables, child states and fixed leaf count. -/
inductive OrderedParse (V : Type u) (H : Type v) : ℕ → Type (max u v) where
  | leaf (v : V) : OrderedParse V H 0
  | node {d : ℕ} (b : Fin (d + 1)) (i j : H)
      (left : OrderedParse V H b.val) (right : OrderedParse V H (d - b.val)) :
      OrderedParse V H (d + 1)

namespace OrderedParse

variable {V : Type u} {H : Type v}

/-- A parse in degree one is determined by its sole terminal. -/
def leafEquiv : OrderedParse V H 0 ≃ V where
  toFun | leaf v => v
  invFun := leaf
  left_inv t := by cases t; rfl
  right_inv _ := rfl

/-- Decompose a binary parse into its split, child states and ordered subtrees. -/
def nodeEquiv (d : ℕ) : OrderedParse V H (d + 1) ≃
    Σ b : Fin (d + 1), H × H × OrderedParse V H b.val × OrderedParse V H (d - b.val) where
  toFun | node b i j left right => ⟨b, i, j, left, right⟩
  invFun | ⟨b, i, j, left, right⟩ => node b i j left right
  left_inv t := by cases t; rfl
  right_inv _ := rfl

instance instFintype [Fintype V] [Fintype H] : (d : ℕ) → Fintype (OrderedParse V H d)
  | 0 => Fintype.ofEquiv _ leafEquiv.symm
  | d + 1 => by
    letI (b : Fin (d + 1)) : Fintype (OrderedParse V H b.val) := instFintype b.val
    letI (b : Fin (d + 1)) : Fintype (OrderedParse V H (d - b.val)) := instFintype (d - b.val)
    exact Fintype.ofEquiv _ (nodeEquiv d).symm
termination_by d => d
decreasing_by
  · exact b.isLt
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- Terminal word, read from left to right with multiplicity. -/
def leaves {d : ℕ} : OrderedParse V H d → List V
  | leaf v => [v]
  | node _ _ _ left right => leaves left ++ leaves right

@[simp] theorem length_leaves {d : ℕ} (t : OrderedParse V H d) :
    t.leaves.length = d + 1 := by
  induction t with
  | leaf => rfl
  | node b _ _ _ _ ih₁ ih₂ =>
    rw [leaves, List.length_append, ih₁, ih₂]
    have := b.isLt
    omega

end OrderedParse
end ParseGrammar

end VPVNP
end Computability
end OAI

end

section



/-!
# Graded parse tables for arithmetic circuits

Section 8.1 of *VP and VNP differ over every field* uses an ordered binary grammar to
record a homogeneous component of a circuit output. Here the layer index `d : Fin n`
represents degree `d.val + 1`. Each production has its own scalar, including a separate
scalar for each choice of terminal variable.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

/-- Scalar labels on all terminals and ordered binary productions through degree `n`. -/
structure ParseGrammar (R V H : Type*) (n : ℕ) where
  /-- The scalar weight for emitting terminal variable `v` from state `h` in degree one. -/
  terminal : H → V → R
  /-- The scalar weight for a binary production at layer `d`, given its parent state, split and
  ordered child states. -/
  binary : (d : Fin n) → H → Fin d.val → H → H → R

namespace ParseGrammar

variable {R V H : Type*} {n : ℕ}

/-- Layer of the left child at split `b`. Its degree is `b.val + 1`. -/
def leftDegree (d : Fin n) (b : Fin d.val) : Fin n :=
  ⟨b.val, b.isLt.trans d.isLt⟩

/-- Layer of the right child. Its degree is the remaining `d.val - b.val`. -/
def rightDegree (d : Fin n) (b : Fin d.val) : Fin n :=
  ⟨d.val - 1 - b.val, by have := b.isLt; have := d.isLt; omega⟩

theorem leftDegree_lt (d : Fin n) (b : Fin d.val) : (leftDegree d b).val < d.val :=
  b.isLt

theorem rightDegree_lt (d : Fin n) (b : Fin d.val) : (rightDegree d b).val < d.val := by
  change d.val - 1 - b.val < d.val
  have := b.isLt
  omega

theorem split_degrees (d : Fin n) (b : Fin d.val) :
    ((leftDegree d b).val + 1) + ((rightDegree d b).val + 1) = d.val + 1 := by
  change b.val + 1 + (d.val - 1 - b.val + 1) = d.val + 1
  have := b.isLt
  omega

variable [Fintype V] [Fintype H] [CommSemiring R]

/-- Evaluate a grammar state as a formal polynomial by multiplying the two ordered
children of each binary production and summing over all productions. -/
noncomputable def eval (G : ParseGrammar R V H n) (d : Fin n) (h : H) : MvPolynomial V R :=
  if d.val = 0 then ∑ v, C (G.terminal h v) * X v
  else ∑ b, ∑ i, ∑ j,
    C (G.binary d h b i j) * G.eval (leftDegree d b) i * G.eval (rightDegree d b) j
termination_by d.val
decreasing_by
  all_goals first | exact leftDegree_lt _ _ | exact rightDegree_lt _ _

theorem eval_terminal (G : ParseGrammar R V H n) {d : Fin n} (hd : d.val = 0) (h : H) :
    G.eval d h = ∑ v, C (G.terminal h v) * X v := by
  rw [eval]; simp [hd]

theorem eval_binary (G : ParseGrammar R V H n) {d : Fin n} (hd : d.val ≠ 0) (h : H) :
    G.eval d h = ∑ b, ∑ i, ∑ j,
      C (G.binary d h b i j) * G.eval (leftDegree d b) i * G.eval (rightDegree d b) j := by
  rw [eval]; simp [hd]

/-- The recursive evaluation agrees with every state table that satisfies the grammar
equations, simultaneously for all states and positive degrees through `n`. -/
theorem eval_eq_of_recurrence (G : ParseGrammar R V H n) (f : Fin n → H → MvPolynomial V R)
    (hterminal : ∀ d h, d.val = 0 → f d h = ∑ v, C (G.terminal h v) * X v)
    (hbinary : ∀ d h, d.val ≠ 0 → f d h = ∑ b, ∑ i, ∑ j,
      C (G.binary d h b i j) * f (leftDegree d b) i * f (rightDegree d b) j)
    (d : Fin n) (h : H) : G.eval d h = f d h := by
  induction d using (measure (fun d : Fin n ↦ d.val)).wf.induction generalizing h with
  | h d ih =>
    by_cases hd : d.val = 0
    · rw [eval_terminal _ hd, hterminal _ _ hd]
    · rw [eval_binary _ hd, hbinary _ _ hd]
      refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      rw [ih _ (leftDegree_lt d b) i, ih _ (rightDegree_lt d b) j]

/-- Every state polynomial is homogeneous in the input variables of its declared degree. -/
theorem eval_isHomogeneous (G : ParseGrammar R V H n) (d : Fin n) (h : H) :
    (G.eval d h).IsHomogeneous (d.val + 1) := by
  induction d using (measure (fun d : Fin n ↦ d.val)).wf.induction generalizing h with
  | h d ih =>
    by_cases hd : d.val = 0
    · rw [eval_terminal _ hd, hd]
      refine IsHomogeneous.sum _ _ _ fun v _ ↦ ?_
      simpa using (isHomogeneous_C V (G.terminal h v)).mul (isHomogeneous_X R v)
    · rw [eval_binary _ hd]
      refine IsHomogeneous.sum _ _ _ fun b _ ↦ IsHomogeneous.sum _ _ _ fun i _ ↦
        IsHomogeneous.sum _ _ _ fun j _ ↦ ?_
      simpa [split_degrees] using
        ((isHomogeneous_C V (G.binary d h b i j)).mul (ih _ (leftDegree_lt d b) i)).mul
          (ih _ (rightDegree_lt d b) j)


variable (G : ParseGrammar R V H n)

/-- Multiply the terminal and internal scalar labels occurring in this ordered parse. -/
def weight (G : ParseGrammar R V H n) (d : Fin n) (h : H) (p : OrderedParse V H d.val) : R :=
  match d, p with
  | ⟨0, _⟩, .leaf v => G.terminal h v
  | ⟨k + 1, hk⟩, .node b i j l r =>
    G.binary ⟨k + 1, hk⟩ h b i j *
      G.weight (leftDegree ⟨k + 1, hk⟩ b) i l *
      G.weight (rightDegree ⟨k + 1, hk⟩ b) j r
termination_by d.val
decreasing_by
  all_goals first | exact leftDegree_lt _ _ | exact rightDegree_lt _ _

omit [Fintype V] [Fintype H] in
@[simp] theorem weight_leaf (hn : 0 < n) (h : H) (v : V) :
    G.weight ⟨0, hn⟩ h (.leaf v) = G.terminal h v := by
  rw [weight]

omit [Fintype V] [Fintype H] in
@[simp] theorem weight_node {k : ℕ} (hk : k + 1 < n) (h : H) (b : Fin (k + 1))
    (i j : H) (l : OrderedParse V H b.val) (r : OrderedParse V H (k - b.val)) :
    G.weight ⟨k + 1, hk⟩ h (.node b i j l r) =
      G.binary ⟨k + 1, hk⟩ h b i j *
      G.weight (leftDegree ⟨k + 1, hk⟩ b) i l *
      G.weight (rightDegree ⟨k + 1, hk⟩ b) j r := by
  rw [weight]

/-- Expansion of the state polynomial as a sum over the actual ordered parse trees.
The multiplicative terminal monomial reads the leaves in their left-to-right order. -/
theorem eval_eq_sum (d : Fin n) (h : H) :
    G.eval d h = ∑ p : OrderedParse V H d.val,
      C (G.weight d h p) * (p.leaves.map (X (R := R))).prod := by
  classical
  apply G.eval_eq_of_recurrence
    (fun d h ↦ ∑ p : OrderedParse V H d.val, C (G.weight d h p) * (p.leaves.map X).prod)
  · rintro ⟨d, hd⟩ h rfl
    rw [← (OrderedParse.leafEquiv (V := V) (H := H)).symm.sum_comp]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    change C (G.weight ⟨0, hd⟩ h (.leaf v)) * (List.map X [v]).prod = _
    simp
  · rintro ⟨k, hk⟩ h hpos
    cases k with
    | zero => exact (hpos rfl).elim
    | succ k =>
      rw [← (OrderedParse.nodeEquiv (V := V) (H := H) k).symm.sum_comp]
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      change C (G.weight ⟨k+1, hk⟩ h (.node b i j l r)) *
        (List.map X (l.leaves ++ r.leaves)).prod = _
      simp only [weight_node, map_mul, List.map_append, List.prod_append]
      ac_rfl

/-- Evaluate the parse expansion with arbitrary terminal values and a change of scalars. -/
theorem eval₂_eq_sum {S : Type*} [CommSemiring S] (scalar : R →+* S) (input : V → S)
    (d : Fin n) (h : H) :
    eval₂Hom scalar input (G.eval d h) = ∑ p : OrderedParse V H d.val,
      scalar (G.weight d h p) * (p.leaves.map input).prod := by
  rw [G.eval_eq_sum]
  simp only [map_sum, map_mul, eval₂Hom_C, map_list_prod, List.map_map]
  simp [Function.comp_def]

end ParseGrammar

end VPVNP
end Computability
end OAI

end

section



/-!
# Graded parse labels for exact circuits

An exact circuit determines one assignment of the labels of the grammar of Section 8.1
of *VP and VNP differ over every field*. This assignment works simultaneously for all
homogeneous pieces up to the prescribed cutoff and for all gate, variable and output
states. It allows arbitrary field constants and does not require homogeneous intermediate
gate computations.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial ParseGrammar

variable {R V H : Type*} [CommRing R] [Fintype V] [Fintype H] {n D : ℕ}

omit [Fintype V] in
private theorem Circuit.exists_production_labels (c : Circuit R V n)
    (state : H → Circuit.GrammarSlots V n) (surj : Function.Surjective state)
    (d : Fin D) (h : H) (hd : d.val ≠ 0) :
    ∃ w : Fin d.val → H → H → R, homogeneousComponent (d.val + 1) (c.slotPolynomial (state h)) =
      ∑ b, ∑ i, ∑ j, C (w b i j) *
        homogeneousComponent ((leftDegree d b).val + 1) (c.slotPolynomial (state i)) *
        homogeneousComponent ((rightDegree d b).val + 1) (c.slotPolynomial (state j)) := by
  classical
  let prod (s : Fin d.val × H × H) : MvPolynomial V R :=
    homogeneousComponent ((leftDegree d s.1).val + 1) (c.slotPolynomial (state s.2.1)) *
    homogeneousComponent ((rightDegree d s.1).val + 1) (c.slotPolynomial (state s.2.2))
  have hmem : homogeneousComponent (d.val + 1) (c.slotPolynomial (state h)) ∈
      Submodule.span R (Set.range prod) := by
    apply c.slot_component_mem (by omega)
    intro i j a b ha hb hab
    obtain ⟨i', rfl⟩ := surj i
    obtain ⟨j', rfl⟩ := surj j
    let split : Fin d.val := ⟨a - 1, by omega⟩
    have hl : (leftDegree d split).val + 1 = a := by change a - 1 + 1 = a; omega
    have hr : (rightDegree d split).val + 1 = b := by
      have htotal := split_degrees d split
      omega
    rw [← hl, ← hr]
    exact Submodule.subset_span (Set.mem_range_self (split, i', j') : prod _ ∈ _)
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hmem
  refine ⟨fun b i j ↦ w (b, i, j), ?_⟩
  simpa only [Fintype.sum_prod_type, prod, smul_eq_C_mul, mul_assoc] using hw.symm

/-- A single assignment of the scalar labels represents the given circuit at every
state and every degree up to `D`. The state list can contain extra copies of any slot. -/
theorem Circuit.exists_parseGrammar_on (c : Circuit R V n) (D : ℕ)
    (state : H → Circuit.GrammarSlots V n) (surj : Function.Surjective state) :
    ∃ G : ParseGrammar R V H D, ∀ d h,
      G.eval d h = homogeneousComponent (d.val + 1) (c.slotPolynomial (state h)) := by
  classical
  let binary (d : Fin D) (h : H) : Fin d.val → H → H → R :=
    if hd : d.val ≠ 0 then (c.exists_production_labels state surj d h hd).choose
    else fun _ _ _ ↦ 0
  let G : ParseGrammar R V H D :=
    ⟨fun h v ↦ (c.slotPolynomial (state h)).coeff (Finsupp.single v 1), binary⟩
  refine ⟨G, G.eval_eq_of_recurrence _ ?_ ?_⟩
  · intro d h hd
    simpa only [hd, zero_add] using homogeneousComponent_one_eq_sum (c.slotPolynomial (state h))
  · intro d h hd
    simpa only [G, binary, dif_pos hd] using
      (c.exists_production_labels state surj d h hd).choose_spec

/-- The start state computes the requested piece of the exact output polynomial. -/
theorem Circuit.exists_parseGrammar (c : Circuit R V n) (D : ℕ) :
    ∃ G : ParseGrammar R V (Circuit.GrammarSlots V n) D, ∀ d,
      G.eval d none = homogeneousComponent (d.val + 1) c.polynomial := by
  obtain ⟨G, hG⟩ := c.exists_parseGrammar_on D id Function.surjective_id
  exact ⟨G, fun d ↦ hG d none⟩

/-- The state count is one plus the number of variables and binary gates. -/
theorem Circuit.card_grammarSlots (V : Type*) [Fintype V] (n : ℕ) :
    Fintype.card (Circuit.GrammarSlots V n) = Fintype.card V + n + 1 := by
  simp [GrammarSlots]

/-- The prescribed rectangular table can be padded to any sufficiently large width.
The start slot is number zero (number one in the paper). -/
theorem Circuit.exists_parseGrammar_fin (c : Circuit R V n) (D S : ℕ)
    (hS : Fintype.card V + n + 1 ≤ S) :
    ∃ G : ParseGrammar R V (Fin S) D, ∀ d,
      G.eval d ⟨0, by omega⟩ = homogeneousComponent (d.val + 1) c.polynomial := by
  classical
  obtain ⟨e⟩ : Nonempty (Circuit.GrammarSlots V n ↪ Fin S) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [card_grammarSlots, Fintype.card_fin])
  let start : Fin S := ⟨0, by omega⟩
  let switch := Equiv.swap (e none) start
  let state : Fin S → Circuit.GrammarSlots V n := Function.invFun e ∘ switch
  have hs : Function.Surjective state :=
    (Function.leftInverse_invFun e.injective).surjective.comp switch.surjective
  obtain ⟨G, hG⟩ := c.exists_parseGrammar_on D state hs
  have hstart : state start = none := by
    simp only [state, switch, Function.comp_apply, Equiv.swap_apply_right]
    exact Function.leftInverse_invFun e.injective none
  exact ⟨G, fun d ↦ by simpa only [hstart, slotPolynomial] using hG d start⟩

end VPVNP
end Computability
end OAI

end

section



/-!
# Assembling the homogeneous parse layers

The graded grammar of §8.1 represents the positive-degree pieces of a circuit.
Its scalar output at degree zero must also be retained when expanding a general
VNP witness summand. The number of grammar states uses the variables and the
binary gates of the exact circuit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Hardness

open MvPolynomial
open scoped Classical

variable {V : Type*} {F : Type*} [Field F]

/-- The constant term plus all positive homogeneous components recover the formal polynomial. -/
theorem eq_constant_add_positive_components (p : MvPolynomial V F) :
    p = C p.constantCoeff +
      ∑ d : Fin p.totalDegree, homogeneousComponent (d.val + 1) p := by
  rw [Fin.sum_univ_eq_sum_range (fun i => homogeneousComponent (i + 1) p), add_comm]
  simpa only [Finset.sum_range_succ', homogeneousComponent_zero, constantCoeff_eq]
    using (sum_homogeneousComponent p).symm

variable [Fintype V]

/-- Choose a single table of labels from an exact circuit of minimum size. -/
noncomputable def grammarFor (p : MvPolynomial V F) :
    ParseGrammar F V (Circuit.GrammarSlots V (circuitSize p)) p.totalDegree :=
  ((circuitSize_spec p).choose.exists_parseGrammar p.totalDegree).choose

theorem eval_grammarFor (p : MvPolynomial V F) (d : Fin p.totalDegree) :
    (grammarFor p).eval d none = homogeneousComponent (d.val + 1) p := by
  rw [grammarFor, ((circuitSize_spec p).choose.exists_parseGrammar p.totalDegree).choose_spec d,
    (circuitSize_spec p).choose_spec]

theorem polynomial_eq_constant_add_grammar (p : MvPolynomial V F) :
    p = C p.constantCoeff + ∑ d : Fin p.totalDegree, (grammarFor p).eval d none := by
  simp only [eval_grammarFor]
  exact eq_constant_add_positive_components p

variable {X W : Type} [Fintype X] [Fintype W]

/-- Under witness specialization, a leaf either contributes a visible variable or
the field constant zero or one selected by the witness bit. -/
noncomputable def leafValue (y : W → Bool) : X ⊕ W → MvPolynomial X F :=
  Sum.elim MvPolynomial.X (fun i => C (if y i then 1 else 0))

/-- The exact specialization at any witness, as a sum of scalar-weighted ordered parses. -/
theorem witnessValue_eq_constant_add_parses (p : MvPolynomial (X ⊕ W) F) (y : W → Bool) :
    witnessValue y p = C p.constantCoeff + ∑ d : Fin p.totalDegree,
      ∑ t : ParseGrammar.OrderedParse (X ⊕ W) (Circuit.GrammarSlots (X ⊕ W) (circuitSize p)) d.val,
        C ((grammarFor p).weight d none t) * (t.leaves.map (leafValue y)).prod := by
  conv_lhs => rw [polynomial_eq_constant_add_grammar p]
  rw [map_add, map_sum]
  simp only [witnessValue, eval₂Hom_C]
  apply congrArg (_ + ·)
  apply Finset.sum_congr rfl
  intro d _
  exact (grammarFor p).eval₂_eq_sum C (leafValue y) d none

/-- A VP summand supplies polynomial bounds on both the number of positive layers
and the number of states, even when the intermediate circuit degrees are much larger. -/
theorem grammar_bounds_of_isVP {σ : ℕ → Type} [∀ n, Fintype (σ n)]
    {p : Family F σ} (hp : IsVP p) :
    PolynomiallyBounded (fun n => (p n).totalDegree) ∧
    PolynomiallyBounded (fun n => Fintype.card (Circuit.GrammarSlots (σ n) (circuitSize (p n)))) := by
  refine ⟨hp.1.2, ?_⟩
  simp only [Circuit.card_grammarSlots]
  exact (hp.1.1.add hp.2).add (.const 1)

end Hardness

end VPVNP
end Computability
end OAI

end

section


/-! # Local incidence conditions for ordered grammar parses

An event names a half-open interval of leaves by its starting offset and its length
minus one. A binary event requests precisely its two ordered child intervals.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

/-- A candidate production occurrence in an ordered parse, recording a leaf interval, the state
at its root and the production used there. -/
structure ParseEvent (V H : Type*) where
  /-- The zero-based offset of the first leaf in the occurrence. -/
  start : ℕ
  /-- The length of the occurrence's leaf interval minus one. -/
  layer : ℕ
  /-- The grammar state at the root of the occurrence. -/
  state : H
  /-- The terminal variable emitted by a leaf, or the left child's layer and the ordered pair
  of child states at a binary node. -/
  production : V ⊕ (ℕ × H × H)
  deriving DecidableEq

variable {V H : Type*}

/-- A terminal has one leaf. A binary split has two positive child lengths. -/
def ParseEvent.WellFormed (e : ParseEvent V H) : Prop :=
  match e.production with
  | .inl _ => e.layer = 0
  | .inr (b, _, _) => b < e.layer

/-- An occurrence matches a requested interval and state when its start, layer and root state
agree with all three arguments. -/
def ParseEvent.Matches (e : ParseEvent V H) (l d : ℕ) (h : H) : Prop :=
  e.start = l ∧ e.layer = d ∧ e.state = h

/-- A binary occurrence requests its two ordered child intervals and their states. A terminal
occurrence has no child requests. -/
def ParseEvent.Requests (e : ParseEvent V H) (l d : ℕ) (h : H) : Prop :=
  match e.production with
  | .inl _ => False
  | .inr (b, i, j) => (l = e.start ∧ d = b ∧ h = i) ∨
      (l = e.start + b + 1 ∧ d = e.layer - b - 1 ∧ h = j)

/-- Exactly one production at every occupied interval, with the designated root and
both children of each binary production. Every other event has an incoming request. -/
structure IsParseTable (T : Finset (ParseEvent V H)) (l d : ℕ) (h : H) : Prop where
  root : ∃ e ∈ T, e.Matches l d h
  typed : ∀ e ∈ T, e.WellFormed
  unique : ∀ e ∈ T, ∀ f ∈ T, e.start = f.start → e.layer = f.layer → e = f
  children : ∀ e ∈ T, ∀ l d h, e.Requests l d h → ∃ f ∈ T, f.Matches l d h
  parent : ∀ e ∈ T, e.Matches l d h ∨ ∃ f ∈ T, f.Requests e.start e.layer e.state

end ParseGrammar

end VPVNP
end Computability
end OAI

end

section



/-! # Canonical interval tables of ordered parses -/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar.OrderedParse

variable {V H : Type*} {d : ℕ}

/-- The occurrence at the root interval, including its production choice. -/
def rootEvent : {d : ℕ} → OrderedParse V H d → ℕ → H → ParseEvent V H
  | _, .leaf v, l, h => ⟨l, 0, h, .inl v⟩
  | _ + 1, .node (d := d) b i j _ _, l, h => ⟨l, d + 1, h, .inr (b.val, i, j)⟩

@[simp] theorem rootEvent_matches (t : OrderedParse V H d) (l : ℕ) (h : H) :
    (t.rootEvent l h).Matches l d h := by cases t <;> exact ⟨rfl, rfl, rfl⟩

open scoped Classical

/-- Include the root and concatenate the two children in their leaf intervals. -/
noncomputable def events : {d : ℕ} → OrderedParse V H d → ℕ → H → Finset (ParseEvent V H)
  | _, .leaf v, l, h => {(.leaf v : OrderedParse V H 0).rootEvent l h}
  | _, .node b i j left right, l, h =>
    insert ((.node b i j left right : OrderedParse V H _).rootEvent l h)
      (left.events l i ∪ right.events (l + b.val + 1) j)

@[simp] theorem rootEvent_mem (t : OrderedParse V H d) (l : ℕ) (h : H) :
    t.rootEvent l h ∈ t.events l h := by cases t <;> simp [events]

/-- Every occupied interval is contained in the leaf interval of its ancestor. -/
theorem event_bounds (t : OrderedParse V H d) (l : ℕ) (h : H) {e : ParseEvent V H}
    (he : e ∈ t.events l h) : l ≤ e.start ∧ e.start + e.layer ≤ l + d := by
  induction t generalizing l h with
  | leaf v =>
    simp only [events, Finset.mem_singleton] at he
    subst e
    simp [rootEvent]
  | node b i j left right ih₁ ih₂ =>
    simp only [events, Finset.mem_insert, Finset.mem_union] at he
    rcases he with rfl | h₁ | h₂
    · simp [rootEvent]
    · have := ih₁ l i h₁
      have := b.isLt
      omega
    · have := ih₂ (l + b.val + 1) j h₂
      have := b.isLt
      omega

/-- The left and right subtrees have disjoint occurrences. -/
theorem disjoint_childEvents {k : ℕ} (b : Fin (k + 1)) (i j : H)
    (left : OrderedParse V H b.val) (right : OrderedParse V H (k - b.val)) (l : ℕ) :
    Disjoint (left.events l i) (right.events (l + b.val + 1) j) := by
  rw [Finset.disjoint_left]
  intro e h₁ h₂
  have := left.event_bounds l i h₁
  have := right.event_bounds (l + b.val + 1) j h₂
  omega

theorem rootEvent_notMem_children {k : ℕ} (b : Fin (k + 1)) (i j : H)
    (left : OrderedParse V H b.val) (right : OrderedParse V H (k - b.val)) (l : ℕ) (h : H) :
    (.node b i j left right : OrderedParse V H _).rootEvent l h ∉
      left.events l i ∪ right.events (l + b.val + 1) j := by
  intro he
  rcases Finset.mem_union.mp he with he | he
  · have := left.event_bounds l i he
    simp only [rootEvent] at this
    have := b.isLt
    omega
  · have := right.event_bounds (l + b.val + 1) j he
    simp only [rootEvent] at this
    omega

end ParseGrammar.OrderedParse

end VPVNP
end Computability
end OAI

end

section




/-! # Weights of the interval events in an ordered parse

Each production occurrence contributes its grammar scalar. Each leaf also contributes
its input value. The interval coordinate distinguishes repeated occurrences of the same
production. Consequently a product over the finite event table counts these repetitions
with the same multiplicity as the recursive parse weight.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

open MvPolynomial OrderedParse

variable {R S V H : Type*} {n : ℕ} [CommSemiring R]

/-- Scalar of a terminal or binary production. A binary coordinate outside the
layer or split bounds of the grammar receives zero. -/
def eventScalar (G : ParseGrammar R V H n) (e : ParseEvent V H) : R :=
  match e.production with
  | .inl v => G.terminal e.state v
  | .inr (b, i, j) =>
    if hd : e.layer < n then
      if hb : b < e.layer then G.binary ⟨e.layer, hd⟩ e.state ⟨b, hb⟩ i j else 0
    else 0

/-- Optional variable supplied by a leaf production. -/
def ParseEvent.leafVariable? (e : ParseEvent V H) : Option V :=
  e.production.elim some (fun _ => none)

/-- A terminal contributes its input value, and a binary production contributes one. -/
def ParseEvent.leafValue [One S] (e : ParseEvent V H) (input : V → S) : S :=
  e.leafVariable?.elim 1 input

/-- Multiplying the selected production scalars recovers the recursively defined
parse weight, independently of the left endpoint of the root interval. -/
theorem prod_eventScalar (G : ParseGrammar R V H n) {d : ℕ} (t : OrderedParse V H d)
    (hd : d < n) (l : ℕ) (h : H) :
    ∏ e ∈ t.events l h, G.eventScalar e = G.weight ⟨d, hd⟩ h t := by
  classical
  induction t generalizing l h with
  | leaf v => simp [events, rootEvent, eventScalar]
  | @node k b i j left right ih₁ ih₂ =>
    rw [events, Finset.prod_insert (rootEvent_notMem_children b i j left right l h),
      Finset.prod_union (disjoint_childEvents b i j left right l), weight_node]
    have hleft := (leftDegree ⟨k + 1, hd⟩ b).isLt
    have hright := (rightDegree ⟨k + 1, hd⟩ b).isLt
    rw [ih₁ hleft, ih₂ hright]
    simp [eventScalar, rootEvent, hd, b.isLt, mul_assoc, leftDegree, rightDegree]

/-- The product of the leaf inputs over the event table is the product of the
parse's left-to-right list of leaves. -/
theorem prod_leafValue [CommMonoid S] (input : V → S) {d : ℕ} (t : OrderedParse V H d)
    (l : ℕ) (h : H) :
    ∏ e ∈ t.events l h, e.leafValue input = (t.leaves.map input).prod := by
  classical
  induction t generalizing l h with
  | leaf v => simp [events, rootEvent, ParseEvent.leafValue, ParseEvent.leafVariable?, leaves]
  | node b i j left right ih₁ ih₂ =>
    rw [events, Finset.prod_insert (rootEvent_notMem_children b i j left right l h),
      Finset.prod_union (disjoint_childEvents b i j left right l), ih₁, ih₂]
    simp [rootEvent, ParseEvent.leafValue, ParseEvent.leafVariable?, leaves]

variable [CommSemiring S]

/-- Local scalar and leaf factors can be multiplied at each selected event. -/
theorem prod_eventWeights (G : ParseGrammar R V H n) (scalar : R →+* S) (input : V → S)
    (d : Fin n) (h : H) (t : OrderedParse V H d.val) (l : ℕ) :
    ∏ e ∈ t.events l h, scalar (G.eventScalar e) * e.leafValue input =
      scalar (G.weight d h t) * (t.leaves.map input).prod := by
  rw [Finset.prod_mul_distrib, ← map_prod, prod_eventScalar G t d.isLt, prod_leafValue]

/-- Evaluating the grammar is a sum of products over canonical finite event tables. -/
theorem eval₂_eq_sum_eventWeights [Fintype V] [Fintype H] (G : ParseGrammar R V H n)
    (scalar : R →+* S) (input : V → S) (d : Fin n) (h : H) (l : ℕ) :
    eval₂Hom scalar input (G.eval d h) = ∑ t : OrderedParse V H d.val,
      ∏ e ∈ t.events l h, scalar (G.eventScalar e) * e.leafValue input := by
  rw [G.eval₂_eq_sum]
  simp only [G.prod_eventWeights]

/-- The formal state polynomial is the weighted sum of its finite event tables. -/
theorem eval_eq_sum_eventWeights [Fintype V] [Fintype H] (G : ParseGrammar R V H n)
    (d : Fin n) (h : H) (l : ℕ) :
    G.eval d h = ∑ t : OrderedParse V H d.val,
      ∏ e ∈ t.events l h, C (G.eventScalar e) * e.leafValue X := by
  rw [G.eval_eq_sum]
  simp only [G.prod_eventWeights]

/-- In the Boolean witness sum, an output variable remains formal and a witness
variable contributes its chosen bit as a field constant at each leaf. -/
theorem witnessValue_eval_eq_sum_eventWeights {F : Type*} [Field F] {X W : Type}
    [Fintype X] [Fintype W] [Fintype H] (G : ParseGrammar F (X ⊕ W) H n)
    (bits : W → Bool) (d : Fin n) (h : H) (l : ℕ) :
    witnessValue bits (G.eval d h) = ∑ t : OrderedParse (X ⊕ W) H d.val,
      ∏ e ∈ t.events l h, C (G.eventScalar e) *
        e.leafValue (Sum.elim MvPolynomial.X (fun w => C (if bits w then 1 else 0))) :=
  G.eval₂_eq_sum_eventWeights ..

end ParseGrammar

end VPVNP
end Computability
end OAI

end

section





/-! # Finite Boolean coordinates for ordered parse occurrences

The coordinates bound the start, layer and binary split independently. This rectangular
index set includes candidate productions which may be ruled out by the local grammar
conditions. Its cardinality is polynomial in the degree cutoff and the alphabet sizes.
A Boolean word specifies a finite table by its characteristic function on these coordinates.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

/-- An occurrence fits the coordinate table if all its numerical fields are below `D`. -/
def ParseEvent.Bounded {V H : Type*} (e : ParseEvent V H) (D : ℕ) : Prop :=
  e.start < D ∧ e.layer < D ∧ match e.production with
    | .inl _ => True
    | .inr (b, _, _) => b < D

theorem ParseEvent.bounded_of_wellFormed {V H : Type*} (e : ParseEvent V H)
    (h : e.WellFormed) {D : ℕ} (hs : e.start < D) (hl : e.layer < D) : e.Bounded D := by
  refine ⟨hs, hl, ?_⟩
  cases hp : e.production with
  | inl v => trivial
  | inr s =>
    rcases s with ⟨b, i, j⟩
    have hb : b < e.layer := by simpa [ParseEvent.WellFormed, hp] using h
    exact hb.trans hl

/-- A candidate event has an interval, parent state and either a terminal or a split
together with the two ordered child states. -/
abbrev EventCode (V H : Type*) (D : ℕ) :=
  Fin D × Fin D × H × (V ⊕ (Fin D × H × H))

namespace EventCode

variable {V H : Type*} {D : ℕ}

/-- Decode a candidate event by taking the natural values of its start, layer and binary split
indices. -/
def event (c : EventCode V H D) : ParseEvent V H :=
  ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.map id (fun (b, i, j) => (b.val, i, j))⟩

theorem event_bounded (c : EventCode V H D) : c.event.Bounded D := by
  rcases c with ⟨l, d, h, v | ⟨b, i, j⟩⟩
  · exact ⟨l.isLt, d.isLt, trivial⟩
  · exact ⟨l.isLt, d.isLt, b.isLt⟩

/-- The coordinate tuple is recovered from the natural-valued event and its bounds. -/
def ofEvent (e : ParseEvent V H) (he : e.Bounded D) : EventCode V H D :=
  (⟨e.start, he.1⟩, ⟨e.layer, he.2.1⟩, e.state, match hp : e.production with
    | .inl v => .inl v
    | .inr (b, i, j) => .inr (⟨b, by simpa [hp] using he.2.2⟩, i, j))

@[simp] theorem event_ofEvent (e : ParseEvent V H) (he : e.Bounded D) :
    (ofEvent e he).event = e := by
  rcases e with ⟨l, d, h, v | ⟨b, i, j⟩⟩ <;> rfl

@[simp] theorem ofEvent_event (c : EventCode V H D) : ofEvent c.event (event_bounded c) = c := by
  rcases c with ⟨l, d, h, v | ⟨b, i, j⟩⟩ <;> rfl

/-- The bijection between event codes with indices in `Fin D` and parse events whose start,
layer and binary split are below `D`. -/
def boundedEquiv : EventCode V H D ≃ {e : ParseEvent V H // e.Bounded D} where
  toFun c := ⟨c.event, c.event_bounded⟩
  invFun e := ofEvent e.1 e.2
  left_inv := ofEvent_event
  right_inv e := Subtype.ext (event_ofEvent e.1 e.2)

theorem event_injective : Function.Injective (event (V := V) (H := H) (D := D)) :=
  fun _ _ h => boundedEquiv.injective (Subtype.ext h)

variable (V H) [Fintype V] [Fintype H] (D : ℕ)

theorem card : Fintype.card (EventCode V H D) =
    D * D * Fintype.card H * (Fintype.card V + D * Fintype.card H * Fintype.card H) := by
  simp [EventCode, Nat.mul_assoc]

/-- Enumerate the rectangular coordinate set with a single finite address. -/
noncomputable def enumerate (i : Fin (Fintype.card (EventCode V H D))) : ParseEvent V H :=
  event ((Fintype.equivFin (EventCode V H D)).symm i)

theorem enumerate_injective : Function.Injective (enumerate V H D) :=
  event_injective.comp (Fintype.equivFin _).symm.injective

theorem enumerate_bounded (i : Fin (Fintype.card (EventCode V H D))) :
    (enumerate V H D i).Bounded D := event_bounded _

theorem exists_enumerate_iff (e : ParseEvent V H) :
    (∃ i, enumerate V H D i = e) ↔ e.Bounded D := by
  constructor
  · rintro ⟨i, rfl⟩
    exact enumerate_bounded V H D i
  · intro he
    refine ⟨Fintype.equivFin _ (ofEvent e he), ?_⟩
    simp [enumerate]

/-- Table of all occurrences whose enumerated Boolean flags are set. -/
noncomputable def selected (x : Fin (Fintype.card (EventCode V H D)) → Bool) :
    Finset (ParseEvent V H) := by
  classical
  exact (Finset.univ.filter (fun i => x i = true)).image (enumerate V H D)

theorem mem_selected (x : Fin (Fintype.card (EventCode V H D)) → Bool) (e : ParseEvent V H) :
    e ∈ selected V H D x ↔ ∃ i, x i = true ∧ enumerate V H D i = e := by
  classical
  simp [selected]

@[simp] theorem enumerate_mem_selected (x : Fin (Fintype.card (EventCode V H D)) → Bool)
    (i : Fin (Fintype.card (EventCode V H D))) :
    enumerate V H D i ∈ selected V H D x ↔ x i = true := by
  rw [mem_selected]
  constructor
  · rintro ⟨j, hj, h⟩
    exact (enumerate_injective V H D h) ▸ hj
  · exact fun hi => ⟨i, hi, rfl⟩

/-- Boolean words and bounded occurrence tables are in bijection, without additional
bits for unused events or auxiliary witnesses. -/
noncomputable def selectedEquiv : (Fin (Fintype.card (EventCode V H D)) → Bool) ≃
    {T : Finset (ParseEvent V H) // ∀ e ∈ T, e.Bounded D} := by
  classical
  exact {
    toFun := fun x => ⟨selected V H D x, fun e he =>
      let ⟨i, _, hi⟩ := (mem_selected V H D x e).mp he
      hi ▸ enumerate_bounded V H D i⟩
    invFun := fun T i => decide (enumerate V H D i ∈ T.1)
    left_inv := fun x => by
      funext i
      simp
    right_inv := fun T => by
      apply Subtype.ext
      ext e
      rw [mem_selected]
      constructor
      · rintro ⟨i, hi, rfl⟩
        simpa using hi
      · intro he
        obtain ⟨i, hi⟩ := (exists_enumerate_iff V H D e).mpr (T.2 e he)
        exact ⟨i, by simpa [hi] using he, hi⟩ }

@[simp] theorem selectedEquiv_apply (x : Fin (Fintype.card (EventCode V H D)) → Bool) :
    (selectedEquiv V H D x).1 = selected V H D x := rfl

end EventCode
end ParseGrammar

end VPVNP
end Computability
end OAI

end

section


/-! # Local incidence validity of an ordered parse tree

Each non-root occurrence is requested by its parent, and each binary occurrence
requests exactly the roots of its two ordered subtrees. Their disjoint leaf
intervals give uniqueness at every occupied interval.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar.OrderedParse

variable {V H : Type*}

private theorem node_unique [DecidableEq V] [DecidableEq H] {r : ParseEvent V H}
    {L R : Finset (ParseEvent V H)} {l d b : ℕ} {i j : H}
    (hl : IsParseTable L l b i) (hr : IsParseTable R (l + b + 1) (d - b) j)
    (hrl : r.layer = d + 1) (hb : b ≤ d)
    (boundsL : ∀ e ∈ L, e.start + e.layer ≤ l + b ∧ e.layer ≤ b)
    (boundsR : ∀ e ∈ R, l + b + 1 ≤ e.start ∧ e.layer ≤ d - b) :
    ∀ e ∈ insert r (L ∪ R), ∀ f ∈ insert r (L ∪ R),
      e.start = f.start → e.layer = f.layer → e = f := by
  intro e he f hf hs hd
  simp only [Finset.mem_insert, Finset.mem_union] at he hf
  rcases he with rfl | he | he <;> rcases hf with rfl | hf | hf
  · rfl
  · have := (boundsL f hf).2
    omega
  · have := (boundsR f hf).2
    omega
  · have := (boundsL e he).2
    omega
  · exact hl.unique e he f hf hs hd
  · have := (boundsL e he).1
    have := (boundsR f hf).1
    omega
  · have := (boundsR e he).2
    omega
  · have := (boundsR e he).1
    have := (boundsL f hf).1
    omega
  · exact hr.unique e he f hf hs hd

private theorem table_node {V H : Type*} [DecidableEq V] [DecidableEq H]
    {L R : Finset (ParseEvent V H)} {l d b : ℕ} {h i j : H}
    (hb : b ≤ d) (hl : IsParseTable L l b i) (hr : IsParseTable R (l + b + 1) (d - b) j)
    (boundsL : ∀ e ∈ L, e.start + e.layer ≤ l + b ∧ e.layer ≤ b)
    (boundsR : ∀ e ∈ R, l + b + 1 ≤ e.start ∧ e.layer ≤ d - b) :
    IsParseTable (insert ⟨l, d + 1, h, .inr (b, i, j)⟩ (L ∪ R)) l (d + 1) h := by
  let r : ParseEvent V H := ⟨l, d + 1, h, .inr (b, i, j)⟩
  let T := insert r (L ∪ R)
  have rootMem : r ∈ T := Finset.mem_insert_self _ _
  have leftSub : L ⊆ T := fun _ he => Finset.mem_insert_of_mem (Finset.mem_union_left _ he)
  have rightSub : R ⊆ T := fun _ he => Finset.mem_insert_of_mem (Finset.mem_union_right _ he)
  have splitMem (e : ParseEvent V H) (he : e ∈ T) : e = r ∨ e ∈ L ∨ e ∈ R := by
    simpa only [T, Finset.mem_insert, Finset.mem_union] using he
  have req (x k : ℕ) (a : H) : r.Requests x k a ↔
      (x = l ∧ k = b ∧ a = i) ∨ (x = l + b + 1 ∧ k = d - b ∧ a = j) := by
    simp only [r, ParseEvent.Requests, show d + 1 - b - 1 = d - b by omega]
  refine ⟨⟨r, rootMem, ⟨rfl, rfl, rfl⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases splitMem e he with rfl | he | he
    · exact Nat.lt_succ_of_le hb
    · exact hl.typed e he
    · exact hr.typed e he
  · exact node_unique hl hr rfl hb boundsL boundsR
  · intro e he x k a ha
    rcases splitMem e he with rfl | he | he
    · rcases (req x k a).mp ha with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · obtain ⟨f, hf, hm⟩ := hl.root
        exact ⟨f, leftSub hf, hm⟩
      · obtain ⟨f, hf, hm⟩ := hr.root
        exact ⟨f, rightSub hf, hm⟩
    · obtain ⟨f, hf, hm⟩ := hl.children e he x k a ha
      exact ⟨f, leftSub hf, hm⟩
    · obtain ⟨f, hf, hm⟩ := hr.children e he x k a ha
      exact ⟨f, rightSub hf, hm⟩
  · intro e he
    rcases splitMem e he with rfl | he | he
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · right
      rcases hl.parent e he with hm | ⟨f, hf, hm⟩
      · exact ⟨r, rootMem, (req _ _ _).mpr (Or.inl hm)⟩
      · exact ⟨f, leftSub hf, hm⟩
    · right
      rcases hr.parent e he with hm | ⟨f, hf, hm⟩
      · exact ⟨r, rootMem, (req _ _ _).mpr (Or.inr hm)⟩
      · exact ⟨f, rightSub hf, hm⟩

/-- The interval occurrences of an ordered parse satisfy all local table conditions. -/
theorem events_isParseTable {V H : Type*} {d : ℕ} (t : OrderedParse V H d) (l : ℕ) (h : H) :
    IsParseTable (t.events l h) l d h := by
  classical
  induction t generalizing l h with
  | leaf v =>
    let r := (leaf v : OrderedParse V H 0).rootEvent l h
    have mem {e : ParseEvent V H} (he : e ∈ (leaf v).events l h) : e = r := by
      simpa only [events, Finset.mem_singleton] using he
    refine ⟨⟨r, rootEvent_mem _ _ _, rootEvent_matches _ _ _⟩, ?_, ?_, ?_, ?_⟩
    · intro e he
      rw [mem he]
      rfl
    · intro e he f hf _ _
      exact (mem he).trans (mem hf).symm
    · intro e he x k a ha
      rw [mem he] at ha
      exact False.elim ha
    · intro e he
      rw [mem he]
      exact Or.inl (rootEvent_matches _ _ _)
  | node b i j left right ih₁ ih₂ =>
    apply table_node (Nat.le_of_lt_succ b.isLt) (ih₁ l i) (ih₂ (l + b.val + 1) j)
    · intro e he
      have := left.event_bounds l i he
      omega
    · intro e he
      have := right.event_bounds (l + b.val + 1) j he
      omega

end ParseGrammar.OrderedParse

end VPVNP
end Computability
end OAI

end

section



/-! # Reconstructing ordered parses from their incidence tables

Starting at a selected event, follow the two child requests to build a parse. Child
layers decrease strictly. Conversely, every selected event has a chain of parents
ending at the root. This rules out disconnected selections and makes the encoding
parsimonious.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

variable {V H : Type*}

private theorem exists_subtree {T : Finset (ParseEvent V H)}
    (htyped : ∀ e ∈ T, e.WellFormed)
    (hchildren : ∀ e ∈ T, ∀ l d h, e.Requests l d h → ∃ f ∈ T, f.Matches l d h)
    (d l : ℕ) (h : H) (hex : ∃ e ∈ T, e.Matches l d h) :
    ∃ t : OrderedParse V H d, t.events l h ⊆ T := by
  classical
  induction d using Nat.strong_induction_on generalizing l h with
  | h d ih =>
    obtain ⟨⟨l', d', h', rule⟩, he, hm⟩ := hex
    obtain ⟨rfl, rfl, rfl⟩ := hm
    have hform := htyped _ he
    rcases rule with v | ⟨b, i, j⟩
    · change d' = 0 at hform
      subst d'
      exact ⟨.leaf v, by simpa [OrderedParse.events, OrderedParse.rootEvent] using he⟩
    · change b < d' at hform
      cases d' with
      | zero => omega
      | succ k =>
        let left := hchildren _ he l' b i (Or.inl ⟨rfl, rfl, rfl⟩)
        have rlayer : k + 1 - b - 1 = k - b := by omega
        let right := hchildren _ he (l' + b + 1) (k - b) j (Or.inr ⟨rfl, rlayer.symm, rfl⟩)
        obtain ⟨t₁, ht₁⟩ := ih b hform l' i left
        obtain ⟨t₂, ht₂⟩ := ih (k - b) (by change k - b < k + 1; omega) (l' + b + 1) j right
        refine ⟨.node ⟨b, hform⟩ i j t₁ t₂, ?_⟩
        simpa [OrderedParse.events, OrderedParse.rootEvent] using
          (Finset.insert_subset_iff.mpr ⟨he, Finset.union_subset ht₁ ht₂⟩)

private theorem subtree_unique {T : Finset (ParseEvent V H)}
    (hunique : ∀ e ∈ T, ∀ f ∈ T, e.start = f.start → e.layer = f.layer → e = f)
    {d : ℕ} (t u : OrderedParse V H d) (l : ℕ) (h : H)
    (ht : t.events l h ⊆ T) (hu : u.events l h ⊆ T) : t = u := by
  classical
  induction t generalizing l h with
  | leaf v =>
    cases u with
    | leaf w =>
      have eq := hunique _ (ht (OrderedParse.rootEvent_mem _ _ _)) _
        (hu (OrderedParse.rootEvent_mem _ _ _)) rfl rfl
      have hv := congrArg ParseEvent.production eq
      simpa [OrderedParse.rootEvent] using hv
  | @node k b i j left right ih₁ ih₂ =>
    cases u with
    | node b' i' j' left' right' =>
      have eq := hunique _ (ht (OrderedParse.rootEvent_mem _ _ _)) _
        (hu (OrderedParse.rootEvent_mem _ _ _)) rfl rfl
      have hs := congrArg ParseEvent.production eq
      simp only [OrderedParse.rootEvent, Sum.inr.injEq, Prod.mk.injEq] at hs
      obtain ⟨hb, rfl, rfl⟩ := hs
      have hb' : b = b' := Fin.ext hb
      subst b'
      simp only [OrderedParse.events, Finset.insert_subset_iff, Finset.union_subset_iff] at ht hu
      rw [ih₁ left' l i ht.2.1 hu.2.1, ih₂ right' (l + b.val + 1) j ht.2.2 hu.2.2]

private theorem requested_layer_lt {e : ParseEvent V H} (hw : e.WellFormed)
    {l d : ℕ} {h : H} (hr : e.Requests l d h) : d < e.layer := by
  rcases e with ⟨l', d', h', v | ⟨b, i, j⟩⟩
  · exact hr.elim
  · change b < d' at hw
    obtain ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ := hr <;> dsimp <;> omega

/-- If two locally valid tables have the same root and one is contained in the other,
they coincide. Ascending parent links ends at the root because the table is finite. -/
private theorem eq_of_valid_subset {S T : Finset (ParseEvent V H)} {l d : ℕ} {h : H}
    (hS : IsParseTable S l d h) (hT : IsParseTable T l d h) (hst : S ⊆ T) : S = T := by
  classical
  apply Finset.Subset.antisymm hst
  intro e he
  induction e using (measure fun e : ParseEvent V H ↦ T.sup ParseEvent.layer - e.layer).wf.induction with
  | h e ih =>
    rcases hT.parent e he with hr | ⟨f, hf, hreq⟩
    · obtain ⟨g, hg, hgr⟩ := hS.root
      exact (hT.unique _ (hst hg) _ he (hgr.1.trans hr.1.symm) (hgr.2.1.trans hr.2.1.symm)) ▸ hg
    · have hlt := requested_layer_lt (hT.typed f hf) hreq
      have hmax := Finset.le_sup (f := ParseEvent.layer) hf
      have hparent : f ∈ S := ih f (by change T.sup ParseEvent.layer - f.layer < T.sup ParseEvent.layer - e.layer; omega) hf
      obtain ⟨g, hg, hgm⟩ := hS.children f hparent _ _ _ hreq
      exact (hT.unique _ (hst hg) _ he hgm.1 hgm.2.1) ▸ hg

/-- Local incidence tests give exactly one ordered parse, with one event for each
terminal or binary production occurrence. -/
theorem IsParseTable.existsUnique_parse {T : Finset (ParseEvent V H)} {l d : ℕ} {h : H}
    (hT : IsParseTable T l d h) : ∃! t : OrderedParse V H d, t.events l h = T := by
  obtain ⟨t, ht⟩ := exists_subtree hT.typed hT.children d l h hT.root
  have heq : t.events l h = T := eq_of_valid_subset (t.events_isParseTable l h) hT ht
  refine ⟨t, heq, fun u hu ↦ subtree_unique hT.unique u t l h ?_ ht⟩
  rw [hu]

end ParseGrammar

end VPVNP
end Computability
end OAI

end

section



/-! # Boolean clauses for the local incidence of an ordered parse

Each candidate production has one selection bit. Clauses require a root and both children
of each selected split, exclude ill-typed or conflicting events, and give every nonroot
production a parent. The clauses refer only to selection bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

open HardnessCNF

variable {k : ℕ} {V H : Type*}

private noncomputable def positives (p : Fin k → Prop) : List (Literal k) := by
  classical exact ((List.finRange k).filter (fun i => decide (p i))).map (fun i => (i, true))

private noncomputable def whenClause (p : Prop) (c : List (Literal k)) : CNF k := by
  classical exact if p then [c] else []

private def targets (e : ParseEvent V H) : List (ℕ × ℕ × H) :=
  match e.production with
  | .inl _ => []
  | .inr (b, i, j) => [(e.start, b, i), (e.start + b + 1, e.layer - b - 1, j)]

private theorem mem_targets (e : ParseEvent V H) (l d : ℕ) (h : H) :
    (l, d, h) ∈ targets e ↔ e.Requests l d h := by
  rcases e with ⟨a, t, s, v | ⟨b,i,j⟩⟩ <;> simp [targets, ParseEvent.Requests]

/-- Clauses for a designated root and a finite enumeration of candidate productions. -/
noncomputable def incidenceCNF (event : Fin k → ParseEvent V H) (l d : ℕ) (h : H) : CNF k :=
  [positives (fun i => (event i).Matches l d h)] ++
    (List.finRange k).flatMap fun i =>
      whenClause (¬ (event i).WellFormed) [(i, false)] ++
      ((List.finRange k).flatMap fun j =>
        whenClause ((event i).start = (event j).start ∧ (event i).layer = (event j).layer ∧
          event i ≠ event j) [(i, false), (j, false)]) ++
      ((targets (event i)).map fun t =>
        (i, false) :: positives fun j => (event j).Matches t.1 t.2.1 t.2.2) ++
      whenClause (¬ (event i).Matches l d h) ((i, false) :: positives fun j =>
        (event j).Requests (event i).start (event i).layer (event i).state)

/-- The table whose events have selected flags. -/
noncomputable def selectedEvents (event : Fin k → ParseEvent V H) (x : Fin k → Bool) :
    Finset (ParseEvent V H) := by
  classical exact (Finset.univ.filter fun i => x i = true).image event

@[simp] theorem mem_selectedEvents (event : Fin k → ParseEvent V H) (x : Fin k → Bool)
    (e : ParseEvent V H) : e ∈ selectedEvents event x ↔ ∃ i, x i = true ∧ event i = e := by
  classical simp [selectedEvents]

private def satClause (x : Fin k → Bool) (c : List (Literal k)) : Prop :=
  ∃ a ∈ c, x a.1 = a.2

private theorem sat_positives (p : Fin k → Prop) (x : Fin k → Bool) :
    satClause x (positives p) ↔ ∃ i, p i ∧ x i = true := by
  classical simp [satClause, positives]

private theorem sat_cons_neg (i : Fin k) (c : List (Literal k)) (x : Fin k → Bool) :
    satClause x ((i, false) :: c) ↔ (x i = true → satClause x c) := by
  cases h : x i <;> simp [satClause, h]

private theorem sat_append (p q : CNF k) (x : Fin k → Bool) :
    Satisfies (p ++ q) x ↔ Satisfies p x ∧ Satisfies q x := by
  simp [Satisfies]; aesop

private theorem sat_flatMap {α : Type*} (s : List α) (f : α → CNF k) (x : Fin k → Bool) :
    Satisfies (s.flatMap f) x ↔ ∀ a ∈ s, Satisfies (f a) x := by
  simp [Satisfies]; aesop

private theorem sat_map {α : Type*} (s : List α) (f : α → List (Literal k))
    (x : Fin k → Bool) : Satisfies (s.map f) x ↔ ∀ a ∈ s, satClause x (f a) := by
  simp [Satisfies, satClause]

private theorem sat_single (c : List (Literal k)) (x : Fin k → Bool) :
    Satisfies [c] x ↔ satClause x c := by simp [Satisfies, satClause]

private theorem sat_when (p : Prop) (c : List (Literal k)) (x : Fin k → Bool) :
    Satisfies (whenClause p c) x ↔ (p → satClause x c) := by
  classical by_cases h : p <;> simp [whenClause, h, Satisfies, satClause]

/-- The satisfying assignments select exactly the locally valid tables with the given root. -/
theorem satisfies_incidenceCNF_iff (event : Fin k → ParseEvent V H) (l d : ℕ) (h : H)
    (x : Fin k → Bool) :
    Satisfies (incidenceCNF event l d h) x ↔ IsParseTable (selectedEvents event x) l d h := by
  classical
  simp only [incidenceCNF, sat_append, sat_flatMap, sat_map, sat_single, sat_when,
    sat_cons_neg, sat_positives, List.mem_finRange, true_implies]
  have empty : ¬ satClause x [] := by simp [satClause]
  constructor
  · rintro ⟨⟨r, hr, xr⟩, hy⟩
    constructor
    · exact ⟨event r, (mem_selectedEvents ..).mpr ⟨r, xr, rfl⟩, hr⟩
    · intro e he
      obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
      exact Classical.byContradiction fun hn => empty ((hy i).1.1.1 hn xi)
    · intro e he f hf hs ht
      obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
      obtain ⟨j, xj, rfl⟩ := (mem_selectedEvents ..).mp hf
      exact Classical.byContradiction fun hn => empty ((hy i).1.1.2 j ⟨hs, ht, hn⟩ xi xj)
    · intro e he a t v req
      obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
      obtain ⟨j, hj, xj⟩ := (hy i).1.2 (a,t,v) ((mem_targets ..).mpr req) xi
      exact ⟨event j, (mem_selectedEvents ..).mpr ⟨j, xj, rfl⟩, hj⟩
    · intro e he
      obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
      by_cases hr : (event i).Matches l d h
      · exact Or.inl hr
      · obtain ⟨j, hj, xj⟩ := (hy i).2 hr xi
        exact Or.inr ⟨event j, (mem_selectedEvents ..).mpr ⟨j, xj, rfl⟩, hj⟩
  · intro table
    obtain ⟨e, he, hr⟩ := table.root
    obtain ⟨i, xi, rfl⟩ := (mem_selectedEvents ..).mp he
    refine ⟨⟨i, hr, xi⟩, fun i => ?_⟩
    have mem (j : Fin k) (xj : x j = true) := (mem_selectedEvents event x (event j)).mpr ⟨j, xj, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro hn xi
      exact (hn (table.typed _ (mem _ xi))).elim
    · rintro j ⟨hs, ht, hn⟩ xi xj
      exact (hn (table.unique _ (mem _ xi) _ (mem _ xj) hs ht)).elim
    · rintro ⟨a,t,v⟩ hreq xi
      obtain ⟨f, hf, hm⟩ := table.children _ (mem _ xi) a t v ((mem_targets ..).mp hreq)
      obtain ⟨j, xj, rfl⟩ := (mem_selectedEvents ..).mp hf
      exact ⟨j, hm, xj⟩
    · intro hn xi
      obtain ⟨f, hf, hr⟩ := (table.parent _ (mem _ xi)).resolve_left hn
      obtain ⟨j, xj, rfl⟩ := (mem_selectedEvents ..).mp hf
      exact ⟨j, hr, xj⟩



@[simp] private theorem literalCount_zero : literalCount ([] : CNF k) = 0 := rfl

@[simp] private theorem literalCount_singleton (c : List (Literal k)) : literalCount [c] = c.length := by
  simp [literalCount]

private theorem literalCount_append (p q : CNF k) :
    literalCount (p ++ q) = literalCount p + literalCount q := by
  simp [literalCount]

private theorem literalCount_flatMap_le {α : Type*} (xs : List α) (f : α → CNF k) (M : ℕ)
    (h : ∀ a ∈ xs, literalCount (f a) ≤ M) :
    literalCount (xs.flatMap f) ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have hx := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simpa [literalCount_append, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add ha hx

private theorem positives_length_le (p : Fin k → Prop) : (positives p).length ≤ k := by
  classical
  simp only [positives, List.length_map]
  simpa using List.length_filter_le (fun i => decide (p i)) (List.finRange k)

private theorem when_count_le (p : Prop) (c : List (Literal k)) :
    literalCount (whenClause p c) ≤ c.length := by
  classical by_cases h : p <;> simp [whenClause, h]

private theorem child_count_le (e : ParseEvent V H) (i : Fin k)
    (p : ℕ × ℕ × H → Fin k → Prop) :
    literalCount ((targets e).map fun t => (i, false) :: positives (p t)) ≤ 2 * (k + 1) := by
  cases he : e.production with
  | inl _ => simp [targets, he]
  | inr v =>
    obtain ⟨b, j, j'⟩ := v
    simp only [targets, he, List.map_cons, List.map_nil, literalCount, List.length_cons,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    have h₁ := positives_length_le (p (e.start, b, j))
    have h₂ := positives_length_le (p (e.start + b + 1, e.layer - b - 1, j'))
    omega

/-- Quadratic bound on the number of literal occurrences read by the query program. -/
theorem literalCount_incidenceCNF_le (event : Fin k → ParseEvent V H) (l d : ℕ) (h : H) :
    literalCount (incidenceCNF event l d h) ≤ k + k * (5 * k + 4) := by
  classical
  rw [incidenceCNF, literalCount_append, literalCount_singleton]
  apply Nat.add_le_add (positives_length_le _)
  refine (literalCount_flatMap_le _ _ (5 * k + 4) ?_).trans (by simp)
  intro i _
  simp only [literalCount_append]
  have h₁ := when_count_le (¬ (event i).WellFormed) [(i, false)]
  have h₂ := literalCount_flatMap_le (List.finRange k) (fun j =>
    whenClause ((event i).start = (event j).start ∧ (event i).layer = (event j).layer ∧
      event i ≠ event j) [(i, false), (j, false)]) 2
      (fun j _ => when_count_le _ _)
  have h₃ := child_count_le (event i) i (fun t j => (event j).Matches t.1 t.2.1 t.2.2)
  have h₄ := when_count_le (¬ (event i).Matches l d h) ((i, false) :: positives fun j =>
    (event j).Requests (event i).start (event i).layer (event i).state)
  have h₅ := positives_length_le (fun j => (event j).Requests (event i).start
    (event i).layer (event i).state)
  simp only [List.length_cons, List.length_nil, List.length_finRange] at h₁ h₂ h₄
  omega

private theorem length_flatMap_le {α β : Type*} (xs : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ xs, (f a).length ≤ M) : (xs.flatMap f).length ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hx := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h a List.mem_cons_self) hx

private theorem when_length_le (p : Prop) (c : List (Literal k)) : (whenClause p c).length ≤ 1 := by
  classical by_cases h : p <;> simp [whenClause, h]

/-- Guarding each clause costs at most this many extra literals. -/
theorem length_incidenceCNF_le (event : Fin k → ParseEvent V H) (l d : ℕ) (h : H) :
    (incidenceCNF event l d h).length ≤ 1 + k * (k + 4) := by
  classical
  rw [incidenceCNF, List.length_append]
  apply Nat.add_le_add_left
  refine (length_flatMap_le _ _ (k + 4) ?_).trans (by simp)
  intro i _
  simp only [List.length_append, List.length_map]
  have h₁ := when_length_le (¬ (event i).WellFormed) [(i, false)]
  have h₂ := length_flatMap_le (List.finRange k) (fun j =>
    whenClause ((event i).start = (event j).start ∧ (event i).layer = (event j).layer ∧
      event i ≠ event j) [(i, false), (j, false)]) 1
      (fun j _ => when_length_le _ _)
  have h₃ : (targets (event i)).length ≤ 2 := by
    cases he : (event i).production with
    | inl _ => simp [targets, he]
    | inr v => obtain ⟨b,u,v⟩ := v; simp [targets, he]
  have h₄ := when_length_le (¬ (event i).Matches l d h) ((i, false) :: positives fun j =>
    (event j).Requests (event i).start (event i).layer (event i).state)
  simp only [List.length_finRange, Nat.mul_one] at h₂
  omega

end ParseGrammar

end VPVNP
end Computability
end OAI

end

section





/-! # Parsimonious Boolean encoding of an ordered parse

The flags selected by a satisfying assignment are precisely the occurrences of
one tree. Conversely, the characteristic function of a tree's occurrences
satisfies every incidence clause. Thus summation over accepted Boolean witnesses
counts each ordered tree exactly once.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar.EventCode

variable (V H : Type*) [Fintype V] [Fintype H] (D : ℕ) (d : Fin D) (h : H)

/-- The finite Boolean word recording exactly the occurrences of the parse. -/
noncomputable def treeBits (t : OrderedParse V H d.val) :
    Fin (Fintype.card (EventCode V H D)) → Bool :=
  (selectedEquiv V H D).symm ⟨t.events 0 h, fun e he => by
    have hb := t.event_bounds 0 h he
    have hd := d.isLt
    exact e.bounded_of_wellFormed ((t.events_isParseTable 0 h).typed e he) (by omega) (by omega)⟩

@[simp] theorem selected_treeBits (t : OrderedParse V H d.val) :
    selected V H D (treeBits V H D d h t) = t.events 0 h :=
  congrArg Subtype.val ((selectedEquiv V H D).apply_symm_apply _)

theorem treeBits_satisfies (t : OrderedParse V H d.val) :
    HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) (treeBits V H D d h t) := by
  apply (satisfies_incidenceCNF_iff ..).mpr
  change IsParseTable (selected V H D (treeBits V H D d h t)) 0 d.val h
  rw [selected_treeBits]
  exact t.events_isParseTable 0 h

private theorem unique_tree
    (x : {x // HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) x}) :
    ∃! t : OrderedParse V H d.val, t.events 0 h = selected V H D x.1 :=
  ((satisfies_incidenceCNF_iff ..).mp x.2).existsUnique_parse

/-- For a fixed root degree and state, the accepting words are in bijection
with the ordered parse trees. -/
noncomputable def satisfyingEquiv :
    {x // HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) x} ≃
      OrderedParse V H d.val where
  toFun x := (unique_tree V H D d h x).exists.choose
  invFun t := ⟨treeBits V H D d h t, treeBits_satisfies V H D d h t⟩
  left_inv x := by
    apply Subtype.ext
    apply (selectedEquiv V H D).injective
    apply Subtype.ext
    rw [selectedEquiv_apply, selectedEquiv_apply, selected_treeBits]
    exact (unique_tree V H D d h x).exists.choose_spec
  right_inv t := by
    let x := (⟨treeBits V H D d h t, treeBits_satisfies V H D d h t⟩ :
      {x // HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) x})
    exact (unique_tree V H D d h x).unique (unique_tree V H D d h x).exists.choose_spec
      (selected_treeBits V H D d h t).symm

theorem events_satisfyingEquiv
    (x : {x // HardnessCNF.Satisfies (incidenceCNF (enumerate V H D) 0 d.val h) x}) :
    (satisfyingEquiv V H D d h x).events 0 h = selected V H D x.val :=
  (unique_tree V H D d h x).exists.choose_spec

end ParseGrammar.EventCode

end VPVNP
end Computability
end OAI

end

section




/-! # Weighted CNF for a grammar state

The incidence clauses select one Boolean assignment per ordered parse. The
product of its selected coordinates counts every production scalar and every
terminal variable with the multiplicity of that occurrence in the tree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

open HardnessCNF MvPolynomial
open scoped Classical

variable {R V H : Type*} {D : ℕ}
variable [CommSemiring R] [Fintype V] [Fintype H]

private theorem weightedCNF_eq_sum_subtype {k : ℕ} (φ : CNF k) (w : Fin k → R) :
    weightedCNF φ w = ∑ x : {x // Satisfies φ x}, ∏ i, if x.val i then w i else 1 := by
  rw [weightedCNF, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun x => by simp) _

private theorem prod_selected_events (w : ParseEvent V H → R)
    (x : Fin (Fintype.card (EventCode V H D)) → Bool) :
    ∏ e ∈ EventCode.selected V H D x, w e =
      ∏ i, if x i then w (EventCode.enumerate V H D i) else 1 := by
  rw [EventCode.selected, Finset.prod_image (EventCode.enumerate_injective V H D).injOn,
    Finset.prod_filter]

/-- Reindex the grammar polynomial's parse expansion by satisfying Boolean
assignments to the incidence clauses. -/
theorem eval_eq_weightedCNF (G : ParseGrammar R V H D) (d : Fin D) (h : H) :
    G.eval d h = weightedCNF (incidenceCNF (EventCode.enumerate V H D) 0 d.val h)
      (fun i => C (G.eventScalar (EventCode.enumerate V H D i)) *
        (EventCode.enumerate V H D i).leafValue X) := by
  rw [G.eval_eq_sum_eventWeights d h 0, weightedCNF_eq_sum_subtype,
    ← (EventCode.satisfyingEquiv V H D d h).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [EventCode.events_satisfyingEquiv]
  exact prod_selected_events _ x.val

end ParseGrammar

end VPVNP
end Computability
end OAI

end

section




/-!
# A weighted CNF representation for every VP family

The positive homogeneous components of a polynomial computed by a circuit are
generated by the graded parse table. A satisfying incidence assignment chooses
exactly one ordered parse. Its selected coordinates carry the rule scalars and
the terminal variable labels. A selector joins these formulas and the constant
term into one CNF of polynomial width and literal count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Hardness

open MvPolynomial ParseGrammar HardnessCNF
open scoped Classical

variable {F V : Type*} [Field F] [Fintype V]

/-- Number of Boolean occurrence coordinates for one homogeneous parse. -/
private noncomputable def eventWidth (p : MvPolynomial V F) : ℕ :=
  Fintype.card (EventCode V (Circuit.GrammarSlots V (circuitSize p)) p.totalDegree)

/-- The absent degree selects the scalar term, with a single empty assignment. -/
private noncomputable def layer (p : MvPolynomial V F) :
    Option (Fin p.totalDegree) → MarkedCNF F V
  | none => MarkedCNF.unit F V
  | some d =>
    let e := EventCode.enumerate V (Circuit.GrammarSlots V (circuitSize p)) p.totalDegree
    ⟨eventWidth p, incidenceCNF e 0 d.val none, fun i => (grammarFor p).eventScalar (e i),
      fun i => (e i).leafVariable?⟩

private theorem value_layer_some (p : MvPolynomial V F) (d : Fin p.totalDegree) :
    (layer p (some d)).value = (grammarFor p).eval d none :=
  ((grammarFor p).eval_eq_weightedCNF d none).symm

private theorem width_layer_le (p : MvPolynomial V F) (d : Option (Fin p.totalDegree)) :
    (layer p d).width ≤ eventWidth p := by
  cases d
  · exact Nat.zero_le _
  · rfl

private theorem literalCount_layer_le (p : MvPolynomial V F) (d : Option (Fin p.totalDegree)) :
    literalCount (layer p d).clauses ≤ eventWidth p + eventWidth p * (5 * eventWidth p + 4) := by
  cases d with
  | none => exact Nat.zero_le _
  | some d => exact literalCount_incidenceCNF_le _ _ _ _

/-- A single formula encodes every homogeneous component and the scalar term. -/
private noncomputable def circuitModel (p : MvPolynomial V F) : MarkedCNF F V :=
  MarkedCNF.linearCombination (fun d : Option (Fin p.totalDegree) => d.elim p.constantCoeff (fun _ => 1))
    (layer p)

private theorem value_circuitModel (p : MvPolynomial V F) : (circuitModel p).value = p := by
  rw [circuitModel, MarkedCNF.value_linearCombination, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, map_one, one_mul, value_layer_some,
    show layer p none = MarkedCNF.unit F V from rfl, MarkedCNF.value_unit, mul_one]
  exact (polynomial_eq_constant_add_grammar p).symm

/-- Polynomially bounded circuit size, formal degree and variable count suffice
for a single scalar-and-variable-labelled CNF at each family length. -/
theorem exists_markedCNF_of_isVP {V : ℕ → Type} [∀ n, Fintype (V n)]
    (g : Family F V) (hg : IsVP g) :
    ∃ m : ∀ n, MarkedCNF F (V n),
      PolynomiallyBounded (fun n => (m n).width) ∧
      PolynomiallyBounded (fun n => literalCount (m n).clauses) ∧
      ∀ n, (m n).value = g n := by
  obtain ⟨hd, hs⟩ := grammar_bounds_of_isVP hg
  have hk : PolynomiallyBounded fun n => eventWidth (g n) := by
    simp only [eventWidth, EventCode.card]
    exact ((hd.mul hd).mul hs).mul (hg.1.1.add ((hd.mul hs).mul hs))
  have hl := hk.add (hk.mul (((PolynomiallyBounded.const 5).mul hk).add (.const 4)))
  have hc : PolynomiallyBounded fun n => Fintype.card (Option (Fin (g n).totalDegree)) := by
    simpa using hd.add (.const 1)
  refine ⟨fun n => circuitModel (g n), ?_, ?_, fun n => value_circuitModel _⟩
  · exact (hc.mul ((PolynomiallyBounded.const 1).add hk)).of_le
      fun n => HardnessAlternatives.width_le (width_layer_le (g n))
  · have hbody := (((PolynomiallyBounded.const 2).mul hc).add
      ((PolynomiallyBounded.const 2).mul hk)).add (.const 1)
    exact (hc.add (hc.mul (hbody.add ((PolynomiallyBounded.const 2).mul hl)))).of_le fun n =>
      HardnessAlternatives.literalCount_formula_le (fun i => (layer (g n) i).clauses)
        (width_layer_le (g n)) (literalCount_layer_le (g n))

end Hardness

end VPVNP
end Computability
end OAI

end

section




/-! # Copying selection flags and testing witness bits

The augmented formula contains the original selection flags, a second copy of
each flag and one bit per witness variable. Each selected event labelled by a
witness variable forces the corresponding witness bit to be true.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessWitness

open HardnessCNF

/-- The augmented formula has the original `k` flags, their `k` copies, and one Boolean
variable for each witness coordinate. -/
def width (k : ℕ) (W : Type*) [Fintype W] := k + (k + Fintype.card W)

/-- The three disjoint blocks of Boolean slots. -/
noncomputable def slots (k : ℕ) (W : Type*) [Fintype W] :
    (Fin k ⊕ (Fin k ⊕ W)) ≃ Fin (width k W) :=
  Fintype.equivFinOfCardEq (by simp [width])

variable {k : ℕ} {X W : Type*} [Fintype W]

private def relabel {k m : ℕ} (f : Fin k → Fin m) (φ : CNF k) : CNF m :=
  φ.map fun c => c.map fun p => (f p.1, p.2)

private noncomputable def flagClauses (i : Fin k) (tag : Option (X ⊕ W)) : CNF (width k W) :=
  let a := slots k W (.inl i)
  let b := slots k W (.inr (.inl i))
  [[(a, false), (b, true)], [(b, false), (a, true)]] ++
    match tag with
    | some (.inr w) => [[(a, false), (slots k W (.inr (.inr w)), true)]]
    | _ => []

/-- Lift all original clauses, constrain the copied flags, and add witness implications. -/
noncomputable def augment (φ : CNF k) (tag : Fin k → Option (X ⊕ W)) : CNF (width k W) :=
  relabel (fun i => slots k W (.inl i)) φ ++
    (List.finRange k).flatMap (fun i => flagClauses i (tag i))

/-- Each selected flag with a witness label has a true bit for its label. -/
def Compatible (tag : Fin k → Option (X ⊕ W)) (x : Fin k → Bool) (y : W → Bool) : Prop :=
  ∀ i w, x i = true → tag i = some (.inr w) → y w = true

private theorem satisfies_relabel {k m : ℕ} (f : Fin k → Fin m) (φ : CNF k) (z : Fin m → Bool) :
    Satisfies (relabel f φ) z ↔ Satisfies φ (fun i => z (f i)) := by
  simp [Satisfies, relabel]

private theorem satisfies_flagClauses (i : Fin k) (tag : Option (X ⊕ W))
    (z : Fin (width k W) → Bool) : Satisfies (flagClauses i tag) z ↔
    z (slots k W (.inr (.inl i))) = z (slots k W (.inl i)) ∧
      (∀ w, z (slots k W (.inl i)) = true → tag = some (.inr w) →
        z (slots k W (.inr (.inr w))) = true) := by
  rcases tag with _ | v | w <;>
    cases hx : z (slots k W (.inl i)) <;> cases hb : z (slots k W (.inr (.inl i))) <;>
      simp only [flagClauses, List.cons_append, List.nil_append, Satisfies, List.forall_mem_cons] <;>
      simp [hx, hb]

/-- Satisfiability of the augmented formula separates into the original clauses,
equality of every copy with its flag, and the witness implications. -/
theorem satisfies_augment (φ : CNF k) (tag : Fin k → Option (X ⊕ W))
    (z : Fin (width k W) → Bool) :
    Satisfies (augment φ tag) z ↔
      Satisfies φ (fun i => z (slots k W (.inl i))) ∧
      (∀ i, z (slots k W (.inr (.inl i))) = z (slots k W (.inl i))) ∧
      Compatible tag (fun i => z (slots k W (.inl i))) (fun w => z (slots k W (.inr (.inr w)))) := by
  have split : Satisfies (augment φ tag) z ↔
      Satisfies (relabel (fun i => slots k W (.inl i)) φ) z ∧
        ∀ i, Satisfies (flagClauses i (tag i)) z := by
    simp only [augment, Satisfies, List.mem_append, List.mem_flatMap, List.mem_finRange,
      true_and]
    aesop
  rw [split, satisfies_relabel]
  simp only [satisfies_flagClauses, forall_and, Compatible]

private theorem literalCount_relabel {m : ℕ} (f : Fin k → Fin m) (φ : CNF k) :
    literalCount (relabel f φ) = literalCount φ := by
  simp [relabel, literalCount, List.map_map, Function.comp_def]

private theorem literalCount_flagClauses_le (i : Fin k) (t : Option (X ⊕ W)) :
    literalCount (flagClauses i t) ≤ 6 := by
  cases t with
  | none => simp [flagClauses, literalCount]
  | some e => cases e <;> simp [flagClauses, literalCount]

private theorem literalCount_flags_le (is : List (Fin k)) (tag : Fin k → Option (X ⊕ W)) :
    literalCount (is.flatMap (fun i => flagClauses i (tag i))) ≤ 6 * is.length := by
  induction is with
  | nil => simp [literalCount]
  | cons i is ih =>
    have h := Nat.add_le_add (literalCount_flagClauses_le i (tag i)) ih
    simpa [literalCount, Nat.mul_succ, Nat.add_comm] using h

/-- Each original flag contributes at most six literals to the augmented CNF. -/
theorem literalCount_augment_le (φ : CNF k) (tag : Fin k → Option (X ⊕ W)) :
    literalCount (augment φ tag) ≤ literalCount φ + 6 * k := by
  have hadd (a b : CNF (width k W)) : literalCount (a ++ b) = literalCount a + literalCount b := by
    simp [literalCount]
  rw [augment, hadd, literalCount_relabel]
  exact Nat.add_le_add_left (by simpa using literalCount_flags_le (List.finRange k) tag) _

end HardnessWitness

end VPVNP
end Computability
end OAI

end

section


/-! # Specializing the selected monomials at a Boolean witness

A selected scalar may be labelled by one output variable or one witness variable.
After specialization, a selected witness label contributes zero if its bit is false
and one if it is true. The output-variable labels survive as formal variables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessWitness

open scoped Classical
open MvPolynomial

/-- A scalar, optionally multiplied by one labelled variable. -/
noncomputable def monomial {F V : Type*} [Field F] (a : F) (t : Option V) :
    MvPolynomial V F := C a * t.elim 1 X

/-- The formal variable retained by a compatible label, or the constant one. -/
def variableWeight {F X W : Type*} [Field F] : Option (X ⊕ W) → X ⊕ F
  | some (.inl v) => .inl v
  | some (.inr _) | none => .inr 1

private theorem witnessValue_monomial {F : Type*} [Field F] {X W : Type}
    (a : F) (t : Option (X ⊕ W)) (y : W → Bool)
    (h : ∀ w, t = some (.inr w) → y w = true) :
    witnessValue y (monomial a t) = C a * (variableWeight (F := F) t).elim MvPolynomial.X C := by
  rcases t with _ | (v | w) <;> simp_all [monomial, witnessValue, variableWeight]

/-- A false selected witness variable annihilates the product. Otherwise the
product factors into the selected scalars and the selected output variables. -/
theorem witnessValue_prod_monomial {F : Type*} [Field F] {X W : Type} {k : ℕ}
    (a : Fin k → F) (tag : Fin k → Option (X ⊕ W)) (x : Fin k → Bool) (y : W → Bool) :
    witnessValue y (∏ i, if x i then monomial (a i) (tag i) else 1) =
      if (∀ i w, x i = true → tag i = some (.inr w) → y w = true) then
        (∏ i, if x i then C (a i) else 1) *
          (∏ i, if x i then (variableWeight (F := F) (tag i)).elim MvPolynomial.X C else 1)
      else 0 := by
  rw [map_prod]
  split_ifs with compatible
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases hi : x i with
    | false => simp
    | true => simpa [hi] using witnessValue_monomial (a i) (tag i) y (fun w => compatible i w hi)
  · push Not at compatible
    obtain ⟨i, w, hi, ht, hw⟩ := compatible
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi, ht, hw, monomial, witnessValue]

end HardnessWitness

end VPVNP
end Computability
end OAI

end

section




/-!
# Eliminating Boolean witness substitutions in a weighted CNF

A selected flag can carry both a scalar and a variable. Its duplicate in the
augmented formula accounts for the variable while the original carries the scalar.
For a witness variable the added implication excludes precisely the assignments
where that variable specializes to zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessWitness

open HardnessCNF
open scoped Classical
variable {k : ℕ} {F : Type*} {X W : Type} [Field F] [Fintype W]

/-- Projection weights on the three blocks of bits. An original flag carries
its scalar, its duplicate carries its formal variable, and the witness is unweighted. -/
noncomputable def augmentedWeight (a : Fin k → F) (tag : Fin k → Option (X ⊕ W)) :
    Projection F (Fin (width k W)) X := fun j =>
  Sum.elim (fun i => .inr (a i))
    (Sum.elim (fun i => variableWeight (F := F) (tag i)) (fun _ => .inr 1))
    ((slots k W).symm j)

/-- Reindex a payload assignment by its witness, flags, and copies of the flags. -/
private noncomputable def assignments (k : ℕ) (W : Type) [Fintype W] :
    ((W → Bool) × (Fin k → Bool) × (Fin k → Bool)) ≃ (Fin (width k W) → Bool) where
  toFun s j := Sum.elim s.2.1 (Sum.elim s.2.2 s.1) ((slots k W).symm j)
  invFun z := (fun w => z (slots k W (.inr (.inr w))), fun i => z (slots k W (.inl i)),
    fun i => z (slots k W (.inr (.inl i))))
  left_inv s := by ext <;> simp
  right_inv z := by
    funext j
    obtain ⟨u, rfl⟩ := (slots k W).surjective j
    rcases u with i | i | w <;> simp

private theorem satisfies_assignment (φ : CNF k) (tag : Fin k → Option (X ⊕ W))
    (y : W → Bool) (x z : Fin k → Bool) :
    Satisfies (augment φ tag) (assignments k W (y, x, z)) ↔
      Satisfies φ x ∧ z = x ∧ Compatible tag x y := by
  rw [satisfies_augment]
  simp only [assignments, Equiv.coe_fn_mk, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  rw [funext_iff]

private theorem prod_assignment (a : Fin k → F) (tag : Fin k → Option (X ⊕ W))
    (y : W → Bool) (x z : Fin k → Bool) :
    (∏ i, if assignments k W (y, x, z) i then
        (augmentedWeight a tag i).elim MvPolynomial.X MvPolynomial.C else 1) =
      (∏ i, if x i then MvPolynomial.C (a i) else 1) *
      (∏ i, if z i then (variableWeight (F := F) (tag i)).elim MvPolynomial.X MvPolynomial.C else 1) := by
  classical
  rw [← (slots k W).prod_comp (fun i => if assignments k W (y, x, z) i then
        (augmentedWeight a tag i).elim MvPolynomial.X MvPolynomial.C else 1)]
  have hw : (∏ w : W, if y w then (1 : MvPolynomial X F) else 1) = 1 :=
    Finset.prod_eq_one fun w _ => by cases y w <;> rfl
  simp [Fintype.prod_sum_type, assignments, augmentedWeight]
  erw [hw, mul_one]
  rfl

/-- After summing the Boolean witnesses, a product with one scalar and one
optional variable per selected flag has a CNF presentation with projection weights. -/
theorem sum_witnessValue_weightedCNF (φ : CNF k) (a : Fin k → F) (tag : Fin k → Option (X ⊕ W)) :
    ∑ y : W → Bool, witnessValue y (weightedCNF φ (fun i => monomial (a i) (tag i))) =
      weightedCNF (augment φ tag) (fun i => (augmentedWeight a tag i).elim MvPolynomial.X MvPolynomial.C) := by
  classical
  unfold weightedCNF
  simp only [map_sum, apply_ite, map_zero]
  rw [← (assignments k W).sum_comp (fun b => if Satisfies (augment φ tag) b then
      ∏ i, if b i then (augmentedWeight a tag i).elim MvPolynomial.X MvPolynomial.C else 1 else 0)]
  simp only [Fintype.sum_prod_type, satisfies_assignment, prod_assignment]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · by_cases hs : Satisfies φ x
    · simp only [hs, ite_true, eq_self, true_and, Compatible]
      refine (witnessValue_prod_monomial a tag x y).trans ?_
      congr 1
    · simp [hs]
  · intro z _ hz
    simp [hz]
  · simp

end HardnessWitness

end VPVNP
end Computability
end OAI

end

section




/-!
# VNP-completeness of the integer family

A VNP summand has a polynomial-size ordered-parse CNF presentation. Copying each selected
production flag separates its scalar and variable labels. Witness variables become free Boolean
bits constrained by their selected occurrences. This leaves only variable and scalar projection
weights. The universal coefficient machine can check the resulting CNF by querying its payload.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Hardness

open MvPolynomial HardnessCNF

variable {F : Type*} [Field F] {V : ℕ → Type} [∀ n, Fintype (V n)]

/-- Every VNP family has a CNF presentation with polynomially many bits and literals.
Each selected bit contributes a single variable or a single scalar. -/
theorem exists_weightedCNF_of_isVNP (p : Family F V) (hp : IsVNP p) :
    ∃ (k : ℕ → ℕ) (φ : ∀ n, CNF (k n)) (weights : ∀ n, Projection F (Fin (k n)) (V n)),
      PolynomiallyBounded k ∧ PolynomiallyBounded (fun n => literalCount (φ n)) ∧
        ∀ n, weightedCNF (φ n) (fun i => (weights n i).elim X C) = p n := by
  obtain ⟨W, inst, g, hW, hg, he⟩ := hp.2
  let : ∀ n, Fintype (W n) := inst
  obtain ⟨m, hk, hlit, hm⟩ := exists_markedCNF_of_isVP g hg
  refine ⟨fun n => HardnessWitness.width (m n).width (W n),
    fun n => HardnessWitness.augment (m n).clauses (m n).label,
    fun n => HardnessWitness.augmentedWeight (m n).scalar (m n).label, ?_, ?_, ?_⟩
  · exact hk.add (hk.add hW)
  · exact (hlit.add ((PolynomiallyBounded.const 6).mul hk)).of_le
      fun n => HardnessWitness.literalCount_augment_le (m n).clauses (m n).label
  · intro n
    rw [he n, ← hm n]
    exact (HardnessWitness.sum_witnessValue_weightedCNF (m n).clauses (m n).scalar (m n).label).symm


end Hardness
end VPVNP
end Computability
end OAI

end

section




/-!
# Polynomial-size exact-one presentations of VNP families

The weighted CNF for a VNP summand can be replaced by exact-one clauses
without changing its generating polynomial. Clause normalization bounds the
number of clause vertices used by the graph reductions. A fixed false bit
gives every instance at least one variable.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF MvPolynomial

variable {F : Type*} [Field F] {V : ℕ → Type} [∀ n, Fintype (V n)]

/-- The Boolean variables carry only projection labels. Variable count,
clause count and literal-occurrence count are all polynomially bounded. -/
theorem exists_family_of_isVNP (p : Family F V) (hp : IsVNP p) :
    ∃ (k : ℕ → ℕ) (φ : ∀ n, CNF (k n)) (w : ∀ n, Projection F (Fin (k n)) (V n)),
      (∀ n, 0 < k n) ∧ PolynomiallyBounded k ∧
      PolynomiallyBounded (fun n => (φ n).length) ∧
      PolynomiallyBounded (fun n => literalCount (φ n)) ∧
      ∀ n, weightedExactOne (φ n) (fun i => (w n i).elim X C) = p n := by
  obtain ⟨k, φ, w, hk, hl, hφ⟩ := Hardness.exists_weightedCNF_of_isVNP p hp
  let ψ := fun n => normalizeClauses (φ n)
  obtain ⟨hL, hlen⟩ := normalizeClauses_polynomial_bounds φ hl
  obtain ⟨hwidth, hocc⟩ := polynomial_bounds ψ hk hL
  refine ⟨fun n => width (ψ n) + 1, fun n => pad (augment (ψ n)),
    fun n => padProjection (augmentProjection (ψ n) (w n)), fun _ => Nat.succ_pos _,
    hwidth.add (.const 1), ?_, ?_, ?_⟩
  · have hrows := (hlen.add (hL.pow 2)).of_le (fun n => length_augment_le (ψ n))
    simpa only [length_pad] using hrows.add (.const 1)
  · simpa only [literalCount_pad] using hocc.add (.const 1)
  · intro n
    rw [weightedExactOne_padProjection]
    simp_rw [augmentProjection_eval, weightedExactOne_augment, ψ, weightedCNF_normalizeClauses]
    exact hφ n

end ExactOne

end VPVNP
end Computability
end OAI

end

section




/-! Unpadded weighted exact-one presentations for the OMA circuit-table model.
Adapted from OpenAI/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6,
Valiant/Project.lean and ExactOneFamily.lean. Copyright OpenAI, Apache-2.0.
Changes: use the imported OMA predicates and expose a common coefficient-free power bound.
-/
namespace OMA.UnpaddedExactOne
open OAI.Computability.VPVNP MvPolynomial
open scoped Classical
variable {F : Type*} [Field F] {σ : ℕ → Type} [∀ n, Fintype (σ n)]

theorem omaComputes_iff {τ : Type*} {s : ℕ} {q : MvPolynomial τ F} :
    S_wpc_vp_vs_vnp.Computes s q ↔ ∃ c : Circuit F τ s, c.polynomial = q :=
  Valiant.Project.computes_iff

theorem sourceVNP {p : Family F σ} (hp : S_wpc_vp_vs_vnp.IsVNP p) : IsVNP p := by
  obtain ⟨hf, W, inst, g, hW, ⟨hg, s, hs, hc⟩, he⟩ := hp
  refine ⟨hf, W, inst, g, hW, ⟨hg, PolynomiallyBounded.of_le hs fun n => ?_⟩, he⟩
  obtain ⟨c, heq⟩ := omaComputes_iff.mp (hc n)
  exact heq ▸ circuitSize_le_of_circuit c

private theorem power_bound {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∃ a N : ℕ, ∀ n ≥ N, f n ≤ n ^ a := by
  obtain ⟨A, d, N, h⟩ := hf
  refine ⟨d + 1, max N A, fun n hn => ?_⟩
  calc f n ≤ A * n ^ d := h n ((le_max_left ..).trans hn)
       _ ≤ n * n ^ d := Nat.mul_le_mul_right _ ((le_max_right ..).trans hn)
       _ = n ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Positivity and the polynomial identity hold at every index, including zero.
Only the common power bound needs a threshold. No lower bound on k relative to n is claimed. -/
theorem exists_family_of_isVNP (p : Family F σ) (hp : S_wpc_vp_vs_vnp.IsVNP p) :
    ∃ (k : ℕ → ℕ) (φ : ∀ n, List (List (Fin (k n) × Bool)))
      (w : ∀ n, Fin (k n) → σ n ⊕ F) (a N : ℕ),
      (∀ n, 0 < k n) ∧
      (∀ n ≥ N, k n ≤ n^a ∧ (φ n).length ≤ n^a ∧ ((φ n).map List.length).sum ≤ n^a) ∧
      ∀ n, (∑ x : Fin (k n) → Bool,
        if ∀ c ∈ φ n, c.countP (fun l => x l.1 == l.2) = 1 then
          ∏ i, if x i then (w n i).elim X C else 1 else 0) = p n := by
  obtain ⟨k, φ, w, hpos, hk, hl, ho, he⟩ := ExactOne.exists_family_of_isVNP p (sourceVNP hp)
  obtain ⟨a, N, h⟩ := power_bound ((hk.add hl).add ho)
  refine ⟨k, φ, w, a, N, hpos, ?_, ?_⟩
  intro n hn
  have H : k n + (φ n).length + ((φ n).map List.length).sum ≤ n^a := h n hn
  omega
  intro n
  simpa only [ExactOne.weightedExactOne, ExactOne.Holds] using he n


end OMA.UnpaddedExactOne

end

section


namespace OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1_H2_R1
open OMA.S_wpc_vp_vs_vnp MvPolynomial
open scoped Classical
def H1 : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] [Countable K]
  (p : Family K (fun n => Fin n × Bool)), IsVNP p → ∃ a M : ℕ, ∀ n ≥ M,
  ∃ (k : ℕ) (φ : List (List (Fin k × Bool))) (w : Fin k → (Fin n × Bool) ⊕ K), 0 < k ∧ k ≤ n^a ∧ φ.length ≤ n^a ∧ (φ.map List.length).sum ≤ n^a ∧ (∑ x : Fin k → Bool, if ∀ c ∈ φ, c.countP (fun l => x l.1 == l.2) = 1 then ∏ i, if x i then (w i).elim X C else 1 else 0) = p n
private theorem padToParent : H1 → OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro h K _ _ _ p hp
  obtain ⟨a,M,h⟩ := h K p hp
  refine ⟨(a+1)+(a+1)+1,max M 16,?_⟩
  intro n hn
  obtain ⟨k,φ,w,hk,hk',hc,hl,hw⟩ := h n ((le_max_left _ _).trans hn)
  have hn' : 16 ≤ n := (le_max_right _ _).trans hn
  let j : Fin k := ⟨0,hk⟩
  let c : List (Fin k × Bool) := [(j,true),(j,false)]
  let ψ := φ ++ List.replicate n c
  have ls : (ψ.map List.length).sum = (φ.map List.length).sum + 2*n := by simp [ψ,c,Nat.mul_comm]
  have lc : ψ.length = φ.length + n := by simp [ψ]
  refine ⟨k,ψ,w,hk,by rw [lc]; omega,?_,?_⟩
  · rw [ls,lc,pow_succ,pow_add]
    let B := n^(a+1)
    have ha : n^a ≤ B := Nat.pow_le_pow_right (by omega) (by omega : a ≤ a+1)
    have hb : n ≤ B := by simpa using Nat.pow_le_pow_right (by omega : 0<n) (by omega : 1 ≤ a+1)
    have hb1 : 1 ≤ B := by omega
    change _ ≤ B*B*n
    calc
      _ ≤ B*(3*(B+2*B)+4)+(B+B) := by gcongr <;> omega
      _ ≤ B*B*16 := by nlinarith [Nat.mul_le_mul_left B hb1]
      _ ≤ _ := Nat.mul_le_mul_left _ hn'
  · rw [← hw]; apply Finset.sum_congr rfl; intro x _
    have good : c.countP (fun l => x l.1 == l.2) = 1 := by cases hx : x j <;> simp [c,hx,List.countP_cons]
    have iff' : (∀ d ∈ ψ, d.countP (fun l => x l.1 == l.2) = 1) ↔ (∀ d ∈ φ, d.countP (fun l => x l.1 == l.2) = 1) := by
      constructor
      · intro hh d hd; exact hh d (List.mem_append_left _ hd)
      · intro hh d hd; rcases List.mem_append.mp hd with hd | hd
        · exact hh d hd
        · have eq := (List.mem_replicate.mp hd).2; subst d; exact good
    simp only [iff']
theorem unpadded : H1 := by
  intro K _ _ _ p hp
  obtain ⟨k, φ, w, a, N, pos, bound, eqn⟩ := OMA.UnpaddedExactOne.exists_family_of_isVNP p hp
  refine ⟨a, N, fun n hn => ?_⟩
  obtain ⟨hk, hl, ho⟩ := bound n hn
  exact ⟨k n, φ n, w n, pos n, hk, hl, ho, eqn n⟩

theorem padded : OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1.H2 := padToParent unpadded

end OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1_H2_R1
end

theorem OMA.branch2 : OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1.H2 := OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1_H2_R1.padded

theorem OMA.solution : OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1.H1 := OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1_H1_R1.main OMA.branch1 OMA.branch2
