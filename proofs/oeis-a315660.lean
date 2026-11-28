import OMAStatements.S_oeis_a315660
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A315660.

Method: an explicit distance certificate. Every vertex outside the origin cell lies on one of the
rays through the vertices of the growth polygon or in one of the cones between them (split into a
finite corner, two boundary strips and an interior), and is written as base + k T + j U with a base
from a finite list. The certificate gives the distance of each code as v + L (k + j). A Boolean
checker, evaluated by the kernel, verifies that every neighbour of a coded vertex has a code of
value at most one more, that every coded vertex other than the base vertex has a neighbour of value
exactly one less, and that codes are injective. So the ball of radius n is the image of the codes
of value at most n, and the coordination sequence is a sum of explicit quasi-linear counts, which
satisfies both conjectures. The certificate data was produced by a script written with the help of
an AI agent (Claude Code).
-/

namespace GalCert

/-- A target code given by affine forms in two free variables `k1 j1`. -/
structure Tgt where
  r : ℕ
  b : ℕ
  ka : ℕ
  kb : ℕ
  kc : ℕ
  ja : ℕ
  jb : ℕ
  jc : ℕ
  e : ℕ

def Tgt.dflt : Tgt := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- A rule: `s b e` is a target in the same region at base `b` (offsets derived by the checker),
`f t` an explicit target. -/
inductive Rule where
  | s (b e : ℕ)
  | f (t : Tgt)

structure Base (m : ℕ) where
  x : ℤ
  y : ℤ
  i : Fin m
  v : ℕ
  out : List (List Rule)
  pred : List Rule

structure Region (m : ℕ) where
  kind : ℕ
  Tx : ℤ
  Ty : ℤ
  Ux : ℤ
  Uy : ℤ
  tests : List (ℤ × ℤ × ℤ)
  px : ℤ
  py : ℤ
  pc : ℤ
  pM : ℤ
  qx : ℤ
  qy : ℤ
  qc : ℤ
  qM : ℤ
  bases : List (Base m)

structure Cfg (m : ℕ) where
  adj : Fin m → List (ℤ × ℤ × Fin m)
  x0 : ℤ × ℤ × Fin m
  L : ℕ
  regs : List (Region m)
  certs : List (List (List (Bool × ℕ × ℕ)))
  r0 : ℕ
  b0 : ℕ

variable {m : ℕ} [NeZero m]

def Base.dflt : Base m := ⟨0, 0, 0, 0, [], []⟩
def Region.dflt : Region m := ⟨0, 0, 0, 0, 0, [], 0, 0, 0, 0, 0, 0, 0, 0, []⟩
def edflt : ℤ × ℤ × Fin m := (0, 0, 0)

def nbrs (adj : Fin m → List (ℤ × ℤ × Fin m)) (v : ℤ × ℤ × Fin m) : Finset (ℤ × ℤ × Fin m) :=
  ((adj v.2.2).map (fun d => (v.1 + d.1, v.2.1 + d.2.1, d.2.2))).toFinset

def ball (adj : Fin m → List (ℤ × ℤ × Fin m)) (x0 : ℤ × ℤ × Fin m) : ℕ → Finset (ℤ × ℤ × Fin m)
  | 0 => {x0}
  | n + 1 => ball adj x0 n ∪ (ball adj x0 n).biUnion (nbrs adj)

def sh (p d : ℤ × ℤ × Fin m) : ℤ × ℤ × Fin m := (p.1 + d.1, p.2.1 + d.2.1, d.2.2)

namespace Cfg
variable (C : Cfg m)

def reg (r : ℕ) : Region m := C.regs.getD r Region.dflt
def bas (r b : ℕ) : Base m := (C.reg r).bases.getD b Base.dflt

def dec (r b k j : ℕ) : ℤ × ℤ × Fin m :=
  ((C.bas r b).x + (k : ℤ) * (C.reg r).Tx + (j : ℤ) * (C.reg r).Ux,
   (C.bas r b).y + (k : ℤ) * (C.reg r).Ty + (j : ℤ) * (C.reg r).Uy, (C.bas r b).i)

def val (r b k j : ℕ) : ℕ := (C.bas r b).v + C.L * (k + j)

def Valid (r b k j : ℕ) : Prop :=
  r < C.regs.length ∧ b < (C.reg r).bases.length ∧ (1 ≤ (C.reg r).kind ∨ k = 0) ∧
    (2 ≤ (C.reg r).kind ∨ j = 0)

def ncases (kind : ℕ) : ℕ := if kind = 0 then 1 else if kind = 1 then 2 else 4

/-- Closure/Lipschitz rule check for source base `B` in region `R`, edge `d`, case `(kk, jj)`. -/
def okOut (R : Region m) (B : Base m) (d : ℤ × ℤ × Fin m) (kk jj : ℕ) (t : Tgt) : Bool :=
  let R' := C.reg t.r
  let B' := C.bas t.r t.b
  decide (t.r < C.regs.length) && decide (t.b < R'.bases.length) &&
  (decide (1 ≤ R'.kind) || (t.ka == 0 && t.kb == 0 && t.kc == 0)) &&
  (decide (2 ≤ R'.kind) || (t.ja == 0 && t.jb == 0 && t.jc == 0)) &&
  decide ((t.ka : ℤ) * R'.Tx + (t.ja : ℤ) * R'.Ux = (kk : ℤ) * R.Tx) &&
  decide ((t.kb : ℤ) * R'.Tx + (t.jb : ℤ) * R'.Ux = (jj : ℤ) * R.Ux) &&
  decide (B'.x + (t.kc : ℤ) * R'.Tx + (t.jc : ℤ) * R'.Ux = B.x + d.1 + (kk : ℤ) * R.Tx + (jj : ℤ) * R.Ux) &&
  decide ((t.ka : ℤ) * R'.Ty + (t.ja : ℤ) * R'.Uy = (kk : ℤ) * R.Ty) &&
  decide ((t.kb : ℤ) * R'.Ty + (t.jb : ℤ) * R'.Uy = (jj : ℤ) * R.Uy) &&
  decide (B'.y + (t.kc : ℤ) * R'.Ty + (t.jc : ℤ) * R'.Uy = B.y + d.2.1 + (kk : ℤ) * R.Ty + (jj : ℤ) * R.Uy) &&
  decide (B'.i = d.2.2) &&
  decide (C.L * (t.ka + t.ja) ≤ C.L * kk) && decide (C.L * (t.kb + t.jb) ≤ C.L * jj) &&
  decide (B'.v + C.L * (t.kc + t.jc) ≤ B.v + C.L * (kk + jj) + 1)

/-- Descending rule check: the target code is a neighbour one step closer. -/
def okPred (R : Region m) (B : Base m) (kk jj : ℕ) (t : Tgt) : Bool :=
  let R' := C.reg t.r
  let B' := C.bas t.r t.b
  let d := (C.adj B'.i).getD t.e edflt
  decide (t.r < C.regs.length) && decide (t.b < R'.bases.length) &&
  decide (t.e < (C.adj B'.i).length) &&
  (decide (1 ≤ R'.kind) || (t.ka == 0 && t.kb == 0 && t.kc == 0)) &&
  (decide (2 ≤ R'.kind) || (t.ja == 0 && t.jb == 0 && t.jc == 0)) &&
  decide ((t.ka : ℤ) * R'.Tx + (t.ja : ℤ) * R'.Ux = (kk : ℤ) * R.Tx) &&
  decide ((t.kb : ℤ) * R'.Tx + (t.jb : ℤ) * R'.Ux = (jj : ℤ) * R.Ux) &&
  decide (B'.x + (t.kc : ℤ) * R'.Tx + (t.jc : ℤ) * R'.Ux + d.1 = B.x + (kk : ℤ) * R.Tx + (jj : ℤ) * R.Ux) &&
  decide ((t.ka : ℤ) * R'.Ty + (t.ja : ℤ) * R'.Uy = (kk : ℤ) * R.Ty) &&
  decide ((t.kb : ℤ) * R'.Ty + (t.jb : ℤ) * R'.Uy = (jj : ℤ) * R.Uy) &&
  decide (B'.y + (t.kc : ℤ) * R'.Ty + (t.jc : ℤ) * R'.Uy + d.2.1 = B.y + (kk : ℤ) * R.Ty + (jj : ℤ) * R.Uy) &&
  decide (d.2.2 = B.i) &&
  decide (C.L * (t.ka + t.ja) = C.L * kk) && decide (C.L * (t.kb + t.jb) = C.L * jj) &&
  decide (B'.v + C.L * (t.kc + t.jc) + 1 = B.v + C.L * (kk + jj))

def tst (f : ℤ × ℤ × ℤ) (x y : ℤ) : Prop := f.2.2 ≤ f.1 * x + f.2.1 * y

/-- Zone membership of a base, and invariance of the zone under the region's translations. -/
def okZone (R : Region m) (B : Base m) : Bool :=
  R.tests.all (fun f => decide (f.2.2 ≤ f.1 * B.x + f.2.1 * B.y) &&
    (decide (R.kind = 0) || decide (0 ≤ f.1 * R.Tx + f.2.1 * R.Ty)) &&
    (decide (R.kind ≤ 1) || decide (0 ≤ f.1 * R.Ux + f.2.1 * R.Uy)))

def okCoord (R : Region m) (B : Base m) : Bool :=
  (decide (R.kind = 0) ||
    (decide (R.pc ≤ R.px * B.x + R.py * B.y) && decide (R.px * B.x + R.py * B.y < R.pc + R.pM))) &&
  (decide (R.kind ≤ 1) ||
    (decide (R.qc ≤ R.qx * B.x + R.qy * B.y) && decide (R.qx * B.x + R.qy * B.y < R.qc + R.qM)))

def okRegCoord (R : Region m) : Bool :=
  (decide (R.kind = 0) || (decide (0 < R.pM) && decide (R.px * R.Tx + R.py * R.Ty = R.pM))) &&
  (decide (R.kind ≤ 1) || (decide (R.px * R.Ux + R.py * R.Uy = 0) && decide (0 < R.qM) &&
    decide (R.qx * R.Ux + R.qy * R.Uy = R.qM) && decide (R.qx * R.Tx + R.qy * R.Ty = 0)))

/-- Offsets `(kc, jc)` with `kc T + jc U = (dx, dy)` in region `R`, read off by the coordinate functionals. -/
def offs (R : Region m) (dx dy : ℤ) : ℕ × ℕ :=
  (if R.kind = 0 then 0 else ((R.px * dx + R.py * dy) / R.pM).toNat,
   if R.kind ≤ 1 then 0 else ((R.qx * dx + R.qy * dy) / R.qM).toNat)

def expOut (r : ℕ) (R : Region m) (B : Base m) (d : ℤ × ℤ × Fin m) (kk jj : ℕ) : Rule → Tgt
  | .f t => t
  | .s b e =>
    let B' := R.bases.getD b Base.dflt
    let o := offs R (B.x + d.1 + (kk : ℤ) * R.Tx + (jj : ℤ) * R.Ux - B'.x)
      (B.y + d.2.1 + (kk : ℤ) * R.Ty + (jj : ℤ) * R.Uy - B'.y)
    ⟨r, b, kk, 0, o.1, 0, jj, o.2, e⟩

def expPred (r : ℕ) (R : Region m) (B : Base m) (kk jj : ℕ) : Rule → Tgt
  | .f t => t
  | .s b e =>
    let B' := R.bases.getD b Base.dflt
    let d := (C.adj B'.i).getD e edflt
    let o := offs R (B.x + (kk : ℤ) * R.Tx + (jj : ℤ) * R.Ux - B'.x - d.1)
      (B.y + (kk : ℤ) * R.Ty + (jj : ℤ) * R.Uy - B'.y - d.2.1)
    ⟨r, b, kk, 0, o.1, 0, jj, o.2, e⟩

def ci (k j : ℕ) : ℕ := (if k = 0 then 0 else 1) + (if j = 0 then 0 else 2)
def kkOf (c : ℕ) : ℕ := c % 2
def jjOf (c : ℕ) : ℕ := c / 2

def okBase (r b : ℕ) : Bool :=
  let R := C.reg r
  let B := C.bas r b
  okZone R B && okCoord R B && decide (R.kind ≤ 2) &&
  (!decide (B.v = 0) || decide (C.dec r b 0 0 = C.x0)) &&
  (List.range (C.adj B.i).length).all (fun e => (List.range (ncases R.kind)).all (fun c =>
    C.okOut R B ((C.adj B.i).getD e edflt) (kkOf c) (jjOf c)
      (expOut r R B ((C.adj B.i).getD e edflt) (kkOf c) (jjOf c) ((B.out.getD e []).getD c (.f Tgt.dflt))))) &&
  (List.range (ncases R.kind)).all (fun c =>
    (decide (kkOf c = 0 ∧ jjOf c = 0 ∧ B.v = 0)) ||
      C.okPred R B (kkOf c) (jjOf c) (C.expPred r R B (kkOf c) (jjOf c) (B.pred.getD c (.f Tgt.dflt)))) &&
  (List.range R.bases.length).all (fun b2 =>
    decide (b2 = b) || !(decide ((C.bas r b2).x = B.x ∧ (C.bas r b2).y = B.y ∧ (C.bas r b2).i = B.i)))

def testOf (r : ℕ) (s : Bool) (r2 idx : ℕ) : ℤ × ℤ × ℤ :=
  (C.reg (if s then r2 else r)).tests.getD idx (0, 0, 0)

def okCert (r1 r2 : ℕ) (l : List (Bool × ℕ × ℕ)) : Bool :=
  decide ((l.map (fun t => (t.2.2 : ℤ) * (C.testOf r1 t.1 r2 t.2.1).1)).sum = 0) &&
  decide ((l.map (fun t => (t.2.2 : ℤ) * (C.testOf r1 t.1 r2 t.2.1).2.1)).sum = 0) &&
  decide (0 < (l.map (fun t => (t.2.2 : ℤ) * (C.testOf r1 t.1 r2 t.2.1).2.2)).sum)

def hasCert (r1 r2 : ℕ) : Bool :=
  C.okCert r1 r2 ((C.certs.getD r1 []).getD r2 [])

def check : Bool :=
  decide (0 < C.L) &&
  decide (C.r0 < C.regs.length) && decide (C.b0 < (C.reg C.r0).bases.length) &&
  decide ((C.bas C.r0 C.b0).v = 0) && decide (C.dec C.r0 C.b0 0 0 = C.x0) &&
  (List.range C.regs.length).all (fun r => okRegCoord (C.reg r) &&
    (List.range (C.reg r).bases.length).all (fun b => C.okBase r b)) &&
  (List.range C.regs.length).all (fun r1 => (List.range C.regs.length).all (fun r2 =>
    decide (r1 = r2) || C.hasCert r1 r2))

end Cfg
end GalCert
namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] (C : Cfg m)

theorem all_range {p : ℕ → Bool} {n : ℕ} (h : (List.range n).all p = true) {i : ℕ} (hi : i < n) :
    p i = true := by
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

theorem kk_ci (k j : ℕ) : kkOf (ci k j) = if k = 0 then 0 else 1 := by
  unfold kkOf ci; split_ifs <;> simp_all

theorem jj_ci (k j : ℕ) : jjOf (ci k j) = if j = 0 then 0 else 1 := by
  unfold jjOf ci; split_ifs <;> simp_all

theorem ci_lt {K k j : ℕ} (hK : K ≤ 2) (h1 : 1 ≤ K ∨ k = 0) (h2 : 2 ≤ K ∨ j = 0) :
    ci k j < ncases K := by
  unfold ci ncases; split_ifs <;> omega

theorem kk_eq (k : ℕ) : ((k : ℤ)) = ((if k = 0 then 0 else 1 : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ) +
    ((if k = 0 then 0 else 1 : ℕ) : ℤ) := by
  split_ifs with h
  · simp [h]
  · have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h
    push_cast [Nat.cast_sub this]; ring

theorem kk_eqN (k : ℕ) : k = (if k = 0 then 0 else 1) * (k - 1) + (if k = 0 then 0 else 1) := by
  split_ifs with h <;> omega

theorem aff_le {vB vB' L ka kb kc ja jb jc kk jj K1 J1 : ℕ} (h1 : L * (ka + ja) ≤ L * kk)
    (h2 : L * (kb + jb) ≤ L * jj) (h3 : vB' + L * (kc + jc) ≤ vB + L * (kk + jj) + 1) :
    vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) ≤
      vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) + 1 := by
  have e1 : vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) =
      (vB' + L * (kc + jc)) + K1 * (L * (ka + ja)) + J1 * (L * (kb + jb)) := by ring
  have e2 : vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) + 1 =
      (vB + L * (kk + jj) + 1) + K1 * (L * kk) + J1 * (L * jj) := by ring
  rw [e1, e2]
  exact Nat.add_le_add (Nat.add_le_add h3 (Nat.mul_le_mul_left _ h1)) (Nat.mul_le_mul_left _ h2)

theorem aff_eq {vB vB' L ka kb kc ja jb jc kk jj K1 J1 : ℕ} (h1 : L * (ka + ja) = L * kk)
    (h2 : L * (kb + jb) = L * jj) (h3 : vB' + L * (kc + jc) + 1 = vB + L * (kk + jj)) :
    vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) + 1 =
      vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) := by
  have e1 : vB' + L * ((ka * K1 + kb * J1 + kc) + (ja * K1 + jb * J1 + jc)) + 1 =
      (vB' + L * (kc + jc) + 1) + K1 * (L * (ka + ja)) + J1 * (L * (kb + jb)) := by ring
  have e2 : vB + L * ((kk * K1 + kk) + (jj * J1 + jj)) =
      (vB + L * (kk + jj)) + K1 * (L * kk) + J1 * (L * jj) := by ring
  rw [e1, e2, h1, h2, h3]

structure Facts (C : Cfg m) : Prop where
  Lpos : 0 < C.L
  r0 : C.r0 < C.regs.length
  b0 : C.b0 < (C.reg C.r0).bases.length
  v0 : (C.bas C.r0 C.b0).v = 0
  d0 : C.dec C.r0 C.b0 0 0 = C.x0
  reg : ∀ r < C.regs.length, okRegCoord (C.reg r) = true
  base : ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, C.okBase r b = true
  cert : ∀ r1 < C.regs.length, ∀ r2 < C.regs.length, r1 ≠ r2 → C.hasCert r1 r2 = true

theorem facts (hc : C.check = true) : Facts C := by
  unfold check at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · intro r hr
    have := all_range h6 hr
    simp only [Bool.and_eq_true] at this
    exact this.1
  · intro r hr b hb
    have := all_range h6 hr
    simp only [Bool.and_eq_true] at this
    exact all_range this.2 hb
  · intro r1 h1' r2 h2' hne
    have := all_range (all_range h7 h1') h2'
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.resolve_left hne

section
variable {C}

theorem okBase_parts {r b : ℕ} (h : C.okBase r b = true) :
    okZone (C.reg r) (C.bas r b) = true ∧ okCoord (C.reg r) (C.bas r b) = true ∧ (C.reg r).kind ≤ 2 ∧
    ((C.bas r b).v = 0 → C.dec r b 0 0 = C.x0) ∧
    (∀ e < (C.adj (C.bas r b).i).length, ∀ c < ncases (C.reg r).kind,
      C.okOut (C.reg r) (C.bas r b) ((C.adj (C.bas r b).i).getD e edflt) (kkOf c) (jjOf c)
        (expOut r (C.reg r) (C.bas r b) ((C.adj (C.bas r b).i).getD e edflt) (kkOf c) (jjOf c)
          (((C.bas r b).out.getD e []).getD c (.f Tgt.dflt))) = true) ∧
    (∀ c < ncases (C.reg r).kind, (kkOf c = 0 ∧ jjOf c = 0 ∧ (C.bas r b).v = 0) ∨
      C.okPred (C.reg r) (C.bas r b) (kkOf c) (jjOf c)
        (C.expPred r (C.reg r) (C.bas r b) (kkOf c) (jjOf c) ((C.bas r b).pred.getD c (.f Tgt.dflt))) = true) ∧
    (∀ b2 < (C.reg r).bases.length, (C.bas r b2).x = (C.bas r b).x → (C.bas r b2).y = (C.bas r b).y →
      (C.bas r b2).i = (C.bas r b).i → b2 = b) := by
  unfold okBase at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨hz, hco⟩, hk⟩, h0⟩, ho⟩, hp⟩, hd⟩ := h
  refine ⟨hz, hco, hk, ?_, ?_, ?_, ?_⟩
  · intro hv; rcases h0 with h0 | h0
    · exact absurd hv h0
    · exact h0
  · intro e he c hc
    exact all_range (all_range ho he) hc
  · intro c hc
    have := all_range hp hc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this
  · intro b2 hb2 hx hy hi
    have := all_range hd hb2
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this
    rcases this with h | h
    · exact h
    · exact absurd ⟨hx, hy, hi⟩ h

theorem out_sound (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j) {e : ℕ}
    (he : e < (C.adj (C.bas r b).i).length) :
    ∃ r' b' k' j', C.Valid r' b' k' j' ∧
      C.dec r' b' k' j' = sh (C.dec r b k j) ((C.adj (C.bas r b).i).getD e edflt) ∧
      C.val r' b' k' j' ≤ C.val r b k j + 1 := by
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  have F := facts C hc
  obtain ⟨-, -, hK, -, ho, -, -⟩ := okBase_parts (F.base r hr b hb)
  have hci := ci_lt hK hk1 hj1
  have h := ho e he (ci k j) hci
  set t := expOut r (C.reg r) (C.bas r b) ((C.adj (C.bas r b).i).getD e edflt) (kkOf (ci k j))
    (jjOf (ci k j)) (((C.bas r b).out.getD e []).getD (ci k j) (.f Tgt.dflt))
  set d := (C.adj (C.bas r b).i).getD e edflt
  rw [kk_ci, jj_ci] at h
  unfold okOut at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr', hb'⟩, hK1⟩, hK2⟩, ex1⟩, ex2⟩, ex3⟩, ey1⟩, ey2⟩, ey3⟩, hi⟩, hv1⟩, hv2⟩, hv3⟩ := h
  refine ⟨t.r, t.b, t.ka * (k - 1) + t.kb * (j - 1) + t.kc, t.ja * (k - 1) + t.jb * (j - 1) + t.jc,
    ⟨hr', hb', ?_, ?_⟩, ?_, ?_⟩
  · obtain h | h := hK1
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · obtain h | h := hK2
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · have ek := kk_eq k
    have ej := kk_eq j
    set kk := (if k = 0 then 0 else 1 : ℕ)
    set jj := (if j = 0 then 0 else 1 : ℕ)
    unfold dec sh
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only
      push_cast
      rw [ek, ej]
      linear_combination ex3 + ((k - 1 : ℕ) : ℤ) * ex1 + ((j - 1 : ℕ) : ℤ) * ex2
    · simp only
      push_cast
      rw [ek, ej]
      linear_combination ey3 + ((k - 1 : ℕ) : ℤ) * ey1 + ((j - 1 : ℕ) : ℤ) * ey2
    · exact hi
  · have ek := kk_eqN k
    have ej := kk_eqN j
    set kk := (if k = 0 then 0 else 1 : ℕ)
    set jj := (if j = 0 then 0 else 1 : ℕ)
    unfold val
    have := aff_le (K1 := k - 1) (J1 := j - 1) hv1 hv2 hv3
    rw [← ek, ← ej] at this
    exact this

theorem pred_sound (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j)
    (hpos : 0 < C.val r b k j) :
    ∃ r' b' k' j', C.Valid r' b' k' j' ∧ C.val r' b' k' j' + 1 = C.val r b k j ∧
      C.dec r b k j ∈ nbrs C.adj (C.dec r' b' k' j') := by
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  have F := facts C hc
  obtain ⟨-, -, hK, -, -, hp, -⟩ := okBase_parts (F.base r hr b hb)
  have hci := ci_lt hK hk1 hj1
  have h := hp (ci k j) hci
  set t := C.expPred r (C.reg r) (C.bas r b) (kkOf (ci k j)) (jjOf (ci k j))
    ((C.bas r b).pred.getD (ci k j) (.f Tgt.dflt))
  rw [kk_ci, jj_ci] at h
  rcases h with ⟨h1, h2, h3⟩ | h
  · exfalso
    unfold val at hpos
    split_ifs at h1 h2 with hk0 hj0 <;> simp_all
  unfold okPred at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr', hb'⟩, he⟩, hK1⟩, hK2⟩, ex1⟩, ex2⟩, ex3⟩, ey1⟩, ey2⟩, ey3⟩, hi⟩, hv1⟩, hv2⟩, hv3⟩ := h
  refine ⟨t.r, t.b, t.ka * (k - 1) + t.kb * (j - 1) + t.kc, t.ja * (k - 1) + t.jb * (j - 1) + t.jc,
    ⟨hr', hb', ?_, ?_⟩, ?_, ?_⟩
  · obtain h | h := hK1
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · obtain h | h := hK2
    · exact Or.inl h
    · right; rw [h.1.1, h.1.2, h.2]; simp
  · have ek := kk_eqN k
    have ej := kk_eqN j
    set kk := (if k = 0 then 0 else 1 : ℕ)
    set jj := (if j = 0 then 0 else 1 : ℕ)
    unfold val
    have := aff_eq (K1 := k - 1) (J1 := j - 1) hv1 hv2 hv3
    rw [← ek, ← ej] at this
    exact this
  · unfold nbrs
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨(C.adj (C.bas t.r t.b).i).getD t.e edflt, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he
    · have ek := kk_eq k
      have ej := kk_eq j
      set kk := (if k = 0 then 0 else 1 : ℕ)
      set jj := (if j = 0 then 0 else 1 : ℕ)
      unfold dec
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp only
        push_cast
        rw [ek, ej]
        linear_combination ex3 + ((k - 1 : ℕ) : ℤ) * ex1 + ((j - 1 : ℕ) : ℤ) * ex2
      · simp only
        push_cast
        rw [ek, ej]
        linear_combination ey3 + ((k - 1 : ℕ) : ℤ) * ey1 + ((j - 1 : ℕ) : ℤ) * ey2
      · exact hi

end
end Cfg
end GalCert
namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem zone_sound (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j) :
    ∀ f ∈ (C.reg r).tests, f.2.2 ≤ f.1 * (C.dec r b k j).1 + f.2.1 * (C.dec r b k j).2.1 := by
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  have F := facts C hc
  obtain ⟨hz, -, -, -, -, -, -⟩ := okBase_parts (F.base r hr b hb)
  intro f hf
  unfold okZone at hz
  rw [List.all_eq_true] at hz
  have h := hz f hf
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have t1 : 0 ≤ (k : ℤ) * (f.1 * (C.reg r).Tx + f.2.1 * (C.reg r).Ty) := by
    rcases h1 with h1 | h1
    · rcases hk1 with h | h
      · omega
      · simp [h]
    · exact mul_nonneg (by positivity) h1
  have t2 : 0 ≤ (j : ℤ) * (f.1 * (C.reg r).Ux + f.2.1 * (C.reg r).Uy) := by
    rcases h2 with h2 | h2
    · rcases hj1 with h | h
      · omega
      · simp [h]
    · exact mul_nonneg (by positivity) h2
  unfold dec
  linarith

theorem cert_sum (x y : ℤ) (l : List (Bool × ℕ × ℕ)) (tf : Bool → ℕ → ℤ × ℤ × ℤ)
    (h : ∀ t ∈ l, (tf t.1 t.2.1).2.2 ≤ (tf t.1 t.2.1).1 * x + (tf t.1 t.2.1).2.1 * y) :
    (l.map (fun t => (t.2.2 : ℤ) * (tf t.1 t.2.1).2.2)).sum ≤
      x * (l.map (fun t => (t.2.2 : ℤ) * (tf t.1 t.2.1).1)).sum +
      y * (l.map (fun t => (t.2.2 : ℤ) * (tf t.1 t.2.1).2.1)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (List.mem_cons_self ..)
    have hl := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    have : (a.2.2 : ℤ) * (tf a.1 a.2.1).2.2 ≤ (a.2.2 : ℤ) * ((tf a.1 a.2.1).1 * x + (tf a.1 a.2.1).2.1 * y) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    nlinarith [this, hl]

theorem getD_test {l : List (ℤ × ℤ × ℤ)} {x y : ℤ}
    (h : ∀ f ∈ l, f.2.2 ≤ f.1 * x + f.2.1 * y) (i : ℕ) :
    (l.getD i (0, 0, 0)).2.2 ≤ (l.getD i (0, 0, 0)).1 * x + (l.getD i (0, 0, 0)).2.1 * y := by
  rcases lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; simp

theorem no_two_zones (hc : C.check = true) {r1 r2 : ℕ} (h1 : r1 < C.regs.length)
    (h2 : r2 < C.regs.length) (hne : r1 ≠ r2) (x y : ℤ)
    (z1 : ∀ f ∈ (C.reg r1).tests, f.2.2 ≤ f.1 * x + f.2.1 * y)
    (z2 : ∀ f ∈ (C.reg r2).tests, f.2.2 ≤ f.1 * x + f.2.1 * y) : False := by
  have F := facts C hc
  have hh := F.cert r1 h1 r2 h2 hne
  unfold hasCert okCert at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨⟨s1, s2⟩, s3⟩ := hh
  set c2 := (C.certs.getD r1 []).getD r2 []
  have := cert_sum x y c2 (fun s i => C.testOf r1 s r2 i) (by
    intro t _
    unfold testOf
    split_ifs
    · exact getD_test z2 _
    · exact getD_test z1 _)
  beta_reduce at this
  rw [s1, s2] at this
  linarith

theorem coord_unique {a a' c M : ℤ} {k k' : ℕ} (hM : 0 < M) (ha : c ≤ a) (ha' : a < c + M)
    (hb : c ≤ a') (hb' : a' < c + M) (h : a + k * M = a' + k' * M) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have : (k : ℤ) + 1 ≤ k' := by exact_mod_cast hl
    nlinarith
  · have : (k' : ℤ) + 1 ≤ k := by exact_mod_cast hl
    nlinarith

theorem dec_inj (hc : C.check = true) {r b k j r' b' k' j' : ℕ} (hv : C.Valid r b k j)
    (hv' : C.Valid r' b' k' j') (h : C.dec r b k j = C.dec r' b' k' j') :
    r = r' ∧ b = b' ∧ k = k' ∧ j = j' := by
  have F := facts C hc
  by_cases hr : r = r'
  · subst hr
    refine ⟨rfl, ?_⟩
    obtain ⟨hr, hb, hk1, hj1⟩ := hv
    obtain ⟨-, hb', hk1', hj1'⟩ := hv'
    obtain ⟨-, hco, hK, -, -, -, hd⟩ := okBase_parts (F.base r hr b hb)
    obtain ⟨-, hco', -, -, -, -, -⟩ := okBase_parts (F.base r hr b' hb')
    have hrc := F.reg r hr
    unfold okRegCoord at hrc
    unfold okCoord at hco hco'
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hrc hco hco'
    unfold dec at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hx, hy, hi⟩ := h
    have hkk : k = k' := by
      rcases hrc.1 with h0 | ⟨hM, hT⟩
      · rcases hk1 with h | h
        · omega
        · rcases hk1' with h' | h'
          · omega
          · omega
      · rcases hco.1 with h0 | ⟨p1, p2⟩
        · omega
        rcases hco'.1 with h0 | ⟨q1, q2⟩
        · omega
        have hU : (j : ℤ) * ((C.reg r).px * (C.reg r).Ux + (C.reg r).py * (C.reg r).Uy) =
            (j' : ℤ) * ((C.reg r).px * (C.reg r).Ux + (C.reg r).py * (C.reg r).Uy) := by
          rcases hrc.2 with h2 | ⟨⟨⟨hU0, -⟩, -⟩, -⟩
          · rcases hj1 with h | h
            · omega
            rcases hj1' with h' | h'
            · omega
            simp [h, h']
          · rw [hU0]; simp
        refine coord_unique hM p1 p2 q1 q2 ?_
        rw [← hT]
        have := congrArg (fun z => (C.reg r).px * z) hx
        have h2 := congrArg (fun z => (C.reg r).py * z) hy
        linear_combination this + h2 - hU
    subst hkk
    have hjj : j = j' := by
      rcases hrc.2 with h0 | ⟨⟨⟨hU0, hM⟩, hQ⟩, hT0⟩
      · rcases hj1 with h | h
        · omega
        · rcases hj1' with h' | h'
          · omega
          · omega
      · rcases hco.2 with h0 | ⟨p1, p2⟩
        · omega
        rcases hco'.2 with h0 | ⟨q1, q2⟩
        · omega
        refine coord_unique hM p1 p2 q1 q2 ?_
        rw [← hQ]
        have := congrArg (fun z => (C.reg r).qx * z) hx
        have h2 := congrArg (fun z => (C.reg r).qy * z) hy
        linear_combination this + h2 - (k : ℤ) * hT0 + (k : ℤ) * hT0
    subst hjj
    refine ⟨?_, rfl, rfl⟩
    exact (hd b' hb' (by linarith) (by linarith) hi.symm).symm
  · exfalso
    have z1 := zone_sound hc hv
    have z2 := zone_sound hc hv'
    rw [← h] at z2
    exact no_two_zones hc hv.1 hv'.1 hr _ _ z1 z2

theorem val_zero (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j)
    (h0 : C.val r b k j = 0) : C.dec r b k j = C.x0 := by
  have F := facts C hc
  obtain ⟨hr, hb, -, -⟩ := hv
  obtain ⟨-, -, -, hz, -, -, -⟩ := okBase_parts (F.base r hr b hb)
  unfold val at h0
  have hv0 : (C.bas r b).v = 0 := by omega
  have hkj : C.L * (k + j) = 0 := by omega
  rcases Nat.mul_eq_zero.mp hkj with h | h
  · exact absurd h (Nat.pos_iff_ne_zero.mp F.Lpos)
  · have hk : k = 0 := by omega
    have hj : j = 0 := by omega
    subst hk hj
    exact hz hv0

theorem mem_nbrs {adj : Fin m → List (ℤ × ℤ × Fin m)} {x y : ℤ × ℤ × Fin m} :
    y ∈ nbrs adj x ↔ ∃ e < (adj x.2.2).length, y = sh x ((adj x.2.2).getD e edflt) := by
  unfold nbrs sh
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hd
    exact ⟨e, he, by rw [List.getD_eq_getElem _ _ he]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨_, by rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he, rfl⟩

theorem ball_iff (hc : C.check = true) (n : ℕ) (x : ℤ × ℤ × Fin m) :
    x ∈ ball C.adj C.x0 n ↔ ∃ r b k j, C.Valid r b k j ∧ C.val r b k j ≤ n ∧ C.dec r b k j = x := by
  have F := facts C hc
  induction n generalizing x with
  | zero =>
    simp only [ball, Finset.mem_singleton, Nat.le_zero]
    constructor
    · rintro rfl
      refine ⟨C.r0, C.b0, 0, 0, ⟨F.r0, F.b0, Or.inr rfl, Or.inr rfl⟩, ?_, F.d0⟩
      unfold val; rw [F.v0]; simp
    · rintro ⟨r, b, k, j, hv, h0, rfl⟩
      exact val_zero hc hv h0
  | succ n ih =>
    simp only [ball, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro (h | ⟨z, hz, hxz⟩)
      · obtain ⟨r, b, k, j, hv, hle, hd⟩ := (ih x).mp h
        exact ⟨r, b, k, j, hv, by omega, hd⟩
      · obtain ⟨r, b, k, j, hv, hle, rfl⟩ := (ih z).mp hz
        obtain ⟨e, he, rfl⟩ := mem_nbrs.mp hxz
        have he' : e < (C.adj (C.bas r b).i).length := he
        obtain ⟨r', b', k', j', hv', hd', hval⟩ := out_sound hc hv he'
        exact ⟨r', b', k', j', hv', by omega, hd'⟩
    · rintro ⟨r, b, k, j, hv, hle, rfl⟩
      rcases Nat.lt_or_ge n (C.val r b k j) with hlt | hge
      · right
        obtain ⟨r', b', k', j', hv', hval, hmem⟩ := pred_sound hc hv (by omega)
        exact ⟨C.dec r' b' k' j', (ih _).mpr ⟨r', b', k', j', hv', by omega, rfl⟩, hmem⟩
      · left
        exact (ih _).mpr ⟨r, b, k, j, hv, hge, rfl⟩

end Cfg
end GalCert
namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m]

def pcard (C : Cfg m) (r b n : ℕ) : ℕ :=
  if (C.reg r).kind = 0 then (if (C.bas r b).v = n then 1 else 0)
  else if (C.bas r b).v ≤ n ∧ C.L ∣ (n - (C.bas r b).v) then
    (if (C.reg r).kind = 1 then 1 else (n - (C.bas r b).v) / C.L + 1) else 0

def A (C : Cfg m) (n : ℕ) : ℕ :=
  ((List.range C.regs.length).map (fun r =>
    ((List.range (C.reg r).bases.length).map (fun b => C.pcard r b n)).sum)).sum

theorem emb_inj (r b : ℕ) : Function.Injective (fun p : ℕ × ℕ => (r, b, p.1, p.2)) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.2.2.1 h.2.2.2

def piece (C : Cfg m) (r b n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  if (C.reg r).kind = 0 then (if (C.bas r b).v = n then {(r, b, 0, 0)} else ∅)
  else if (C.bas r b).v ≤ n ∧ C.L ∣ (n - (C.bas r b).v) then
    (if (C.reg r).kind = 1 then {(r, b, (n - (C.bas r b).v) / C.L, 0)}
     else (Finset.HasAntidiagonal.antidiagonal ((n - (C.bas r b).v) / C.L) : Finset (ℕ × ℕ)).map ⟨_, emb_inj r b⟩)
  else ∅

def Sph (C : Cfg m) (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range C.regs.length).biUnion fun r =>
    (Finset.range (C.reg r).bases.length).biUnion fun b => C.piece r b n

variable {C : Cfg m}

theorem val_iff {v L s n : ℕ} (hL : 0 < L) :
    v + L * s = n ↔ v ≤ n ∧ L ∣ (n - v) ∧ s = (n - v) / L := by
  constructor
  · rintro rfl
    refine ⟨by omega, ⟨s, by omega⟩, ?_⟩
    rw [show v + L * s - v = L * s by omega, Nat.mul_div_cancel_left _ hL]
  · rintro ⟨h1, h2, rfl⟩
    rw [Nat.mul_div_cancel' h2]; omega

theorem mem_piece (hL : 0 < C.L) {r b n r' b' k j : ℕ} :
    (r', b', k, j) ∈ C.piece r b n ↔ r' = r ∧ b' = b ∧ (1 ≤ (C.reg r).kind ∨ k = 0) ∧
      (2 ≤ (C.reg r).kind ∨ j = 0) ∧ C.val r b k j = n := by
  unfold piece val
  by_cases h0 : (C.reg r).kind = 0
  · simp only [h0, if_true]
    by_cases h1 : (C.bas r b).v = n
    · simp only [h1, if_true, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨rfl, rfl, Or.inr rfl, Or.inr rfl, by simp⟩
      · rintro ⟨rfl, rfl, hk, hj, hv⟩
        have hk' : k = 0 := by omega
        have hj' : j = 0 := by omega
        exact ⟨rfl, rfl, hk', hj'⟩
    · simp only [h1, if_false, Finset.notMem_empty, false_iff]
      rintro ⟨rfl, rfl, hk, hj, hv⟩
      have hk' : k = 0 := by omega
      have hj' : j = 0 := by omega
      subst hk' hj'
      simp at hv
      exact h1 hv
  · simp only [h0, if_false]
    by_cases h1 : (C.bas r b).v ≤ n ∧ C.L ∣ (n - (C.bas r b).v)
    · simp only [h1, and_self, if_true]
      by_cases h2 : (C.reg r).kind = 1
      · simp only [h2, if_true, Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨rfl, rfl, Or.inl (by omega), Or.inr rfl, ?_⟩
          rw [add_zero]
          exact (val_iff hL).mpr ⟨h1.1, h1.2, rfl⟩
        · rintro ⟨rfl, rfl, hk, hj, hv⟩
          have hj' : j = 0 := by omega
          subst hj'
          rw [add_zero] at hv
          exact ⟨rfl, rfl, ((val_iff hL).mp hv).2.2, rfl⟩
      · simp only [h2, if_false]
        rw [Finset.mem_map]
        constructor
        · rintro ⟨⟨p1, p2⟩, hp, he⟩
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
          simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl, rfl⟩ := he
          refine ⟨rfl, rfl, Or.inl (by omega), Or.inl (by omega), ?_⟩
          exact (val_iff hL).mpr ⟨h1.1, h1.2, hp⟩
        · rintro ⟨rfl, rfl, -, -, hv⟩
          exact ⟨(k, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr ((val_iff hL).mp hv).2.2, rfl⟩
    · simp only [h1, if_false, Finset.notMem_empty, false_iff]
      rintro ⟨rfl, rfl, -, -, hv⟩
      have := (val_iff hL).mp hv
      exact h1 ⟨this.1, this.2.1⟩

theorem mem_Sph (hL : 0 < C.L) {n r b k j : ℕ} :
    (r, b, k, j) ∈ C.Sph n ↔ C.Valid r b k j ∧ C.val r b k j = n := by
  unfold Sph Valid
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨r', hr', b', hb', h⟩
    obtain ⟨rfl, rfl, hk, hj, hv⟩ := (mem_piece hL).mp h
    exact ⟨⟨hr', hb', hk, hj⟩, hv⟩
  · rintro ⟨⟨hr, hb, hk, hj⟩, hv⟩
    exact ⟨r, hr, b, hb, (mem_piece hL).mpr ⟨rfl, rfl, hk, hj, hv⟩⟩

theorem piece_fst (hL : 0 < C.L) {r b n : ℕ} {c : ℕ × ℕ × ℕ × ℕ} (h : c ∈ C.piece r b n) :
    c.1 = r ∧ c.2.1 = b := by
  obtain ⟨r', b', k, j⟩ := c
  have := (mem_piece hL).mp h
  exact ⟨this.1, this.2.1⟩

theorem card_piece (r b n : ℕ) : (C.piece r b n).card = C.pcard r b n := by
  unfold piece pcard
  split_ifs <;> simp

theorem lsum_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

theorem card_Sph (hL : 0 < C.L) (n : ℕ) : (C.Sph n).card = C.A n := by
  unfold Sph A
  rw [Finset.card_biUnion, lsum_range]
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.card_biUnion, lsum_range]
    · apply Finset.sum_congr rfl
      intro b _
      exact card_piece r b n
    · intro b1 _ b2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro c h1 h2
      exact hne ((piece_fst hL h1).2.symm.trans (piece_fst hL h2).2)
  · intro r1 _ r2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro c h1 h2
    simp only [Finset.mem_biUnion] at h1 h2
    obtain ⟨b1, -, h1⟩ := h1
    obtain ⟨b2, -, h2⟩ := h2
    exact hne ((piece_fst hL h1).1.symm.trans (piece_fst hL h2).1)

theorem ball_mono (n : ℕ) : ball C.adj C.x0 n ⊆ ball C.adj C.x0 (n + 1) := by
  intro x hx
  simp only [ball, Finset.mem_union]
  exact Or.inl hx

theorem sphere_eq (hc : C.check = true) (n : ℕ) :
    ball C.adj C.x0 (n + 1) \ ball C.adj C.x0 n =
      (C.Sph (n + 1)).image (fun c => C.dec c.1 c.2.1 c.2.2.1 c.2.2.2) := by
  have F := facts C hc
  ext x
  rw [Finset.mem_sdiff, Finset.mem_image, ball_iff hc, ball_iff hc]
  constructor
  · rintro ⟨⟨r, b, k, j, hv, hle, rfl⟩, hn⟩
    refine ⟨(r, b, k, j), (mem_Sph F.Lpos).mpr ⟨hv, ?_⟩, rfl⟩
    by_contra hne
    exact hn ⟨r, b, k, j, hv, by omega, rfl⟩
  · rintro ⟨⟨r, b, k, j⟩, hc', rfl⟩
    obtain ⟨hv, hval⟩ := (mem_Sph F.Lpos).mp hc'
    refine ⟨⟨r, b, k, j, hv, hval.le, rfl⟩, ?_⟩
    rintro ⟨r', b', k', j', hv', hle, hd⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := dec_inj hc hv' hv hd
    omega

theorem card_step (hc : C.check = true) (n : ℕ) :
    ((ball C.adj C.x0 (n + 1)).card : ℤ) - (ball C.adj C.x0 n).card = C.A (n + 1) := by
  have F := facts C hc
  have h1 := Finset.card_sdiff_add_card_eq_card (ball_mono (C := C) n)
  have h2 : (ball C.adj C.x0 (n + 1) \ ball C.adj C.x0 n).card = C.A (n + 1) := by
    rw [sphere_eq hc, Finset.card_image_of_injOn, card_Sph F.Lpos]
    rintro ⟨r, b, k, j⟩ h1 ⟨r', b', k', j'⟩ h2 hd
    obtain ⟨hv, -⟩ := (mem_Sph F.Lpos).mp h1
    obtain ⟨hv', -⟩ := (mem_Sph F.Lpos).mp h2
    obtain ⟨rfl, rfl, rfl, rfl⟩ := dec_inj hc hv hv' hd
    rfl
  omega

theorem pcard_rec (hL : 0 < C.L) {r b n : ℕ} (hv : (C.bas r b).v < n) :
    C.pcard r b (n + 2 * C.L) + C.pcard r b n = 2 * C.pcard r b (n + C.L) := by
  unfold pcard
  set v := (C.bas r b).v
  have e2 : n + 2 * C.L - v = (n - v) + C.L * 2 := by omega
  have e1 : n + C.L - v = (n - v) + C.L * 1 := by omega
  rw [e2, e1]
  have d2 : C.L ∣ (n - v) + C.L * 2 ↔ C.L ∣ (n - v) :=
    (Nat.dvd_add_left (Dvd.intro 2 rfl))
  have d1 : C.L ∣ (n - v) + C.L * 1 ↔ C.L ∣ (n - v) :=
    (Nat.dvd_add_left (Dvd.intro 1 rfl))
  have q2 : ((n - v) + C.L * 2) / C.L = (n - v) / C.L + 2 := by
    rw [Nat.add_mul_div_left _ _ hL]
  have q1 : ((n - v) + C.L * 1) / C.L = (n - v) / C.L + 1 := by
    rw [Nat.add_mul_div_left _ _ hL]
  simp only [d2, d1, q2, q1]
  split_ifs <;> omega

theorem A_rec (hc : C.check = true) {V : ℕ}
    (hV : ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, (C.bas r b).v ≤ V) {n : ℕ}
    (hn : V < n) : C.A (n + 2 * C.L) + C.A n = 2 * C.A (n + C.L) := by
  have F := facts C hc
  unfold A
  rw [← List.sum_map_add, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [List.mem_range] at hr
  rw [← List.sum_map_add, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro b hb
  rw [List.mem_range] at hb
  exact pcard_rec F.Lpos (lt_of_le_of_lt (hV r hr b hb) hn)

end Cfg

theorem zero_of_window {g : ℕ → ℤ} {L N : ℕ} (hL0 : 0 < L) (hrec : ∀ n, N ≤ n → g (n + 2 * L) + g n = 2 * g (n + L))
    (hw : ∀ n, N ≤ n → n < N + 2 * L → g n = 0) : ∀ n, N ≤ n → g n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n (N + 2 * L) with h | h
    · exact hw n hn h
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 * L := ⟨n - 2 * L, by omega⟩
      have h1 := hrec n' (by omega)
      rw [ih n' (by omega) (by omega), ih (n' + L) (by omega) (by omega)] at h1
      linarith

open PowerSeries in
noncomputable def polyOf : List ℤ → PowerSeries ℤ
  | [] => 0
  | c :: l => PowerSeries.C c + PowerSeries.X * polyOf l

def conv (a : ℕ → ℤ) : List ℤ → ℕ → ℤ
  | [], _ => 0
  | c :: l, 0 => c * a 0
  | c :: l, n + 1 => c * a (n + 1) + conv a l n

open PowerSeries in
theorem coeff_mul_polyOf (a : ℕ → ℤ) (l : List ℤ) (n : ℕ) :
    coeff n (mk a * polyOf l) = conv a l n := by
  induction l generalizing n with
  | nil => simp [polyOf, conv]
  | cons c l ih =>
    rw [polyOf, mul_add, mul_comm (mk a) (C c), mul_left_comm, map_add, coeff_C_mul, coeff_mk]
    cases n with
    | zero => simp [conv]
    | succ n => rw [coeff_succ_X_mul, ih]; simp [conv]

open PowerSeries in
theorem coeff_polyOf (l : List ℤ) (n : ℕ) : coeff n (polyOf l) = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [polyOf]
  | cons c l ih =>
    cases n with
    | zero => simp [polyOf]
    | succ n => rw [polyOf, map_add, coeff_C, coeff_succ_X_mul, ih]; simp

open PowerSeries in
theorem gf_of_conv (a : ℕ → ℤ) (dl pl : List ℤ) (h : ∀ n, conv a dl n = pl.getD n 0) :
    mk a * polyOf dl = polyOf pl := by
  ext n
  rw [coeff_mul_polyOf, coeff_polyOf, h]

end GalCert

namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

def vbound (C : Cfg m) (V : ℕ) : Bool :=
  (List.range C.regs.length).all (fun r =>
    (List.range (C.reg r).bases.length).all (fun b => decide ((C.bas r b).v ≤ V)))

theorem vbound_spec {V : ℕ} (h : C.vbound V = true) :
    ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, (C.bas r b).v ≤ V := by
  intro r hr b hb
  have := all_range (all_range h hr) hb
  simpa using this

theorem lin_rec (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (cs : List (ℤ × ℕ))
    (hs : ∀ p ∈ cs, 1 ≤ p.2) (n : ℕ) (hn : V ≤ n) :
    (cs.map fun p => p.1 * (C.A (n + 2 * C.L + p.2) : ℤ)).sum +
      (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum =
      2 * (cs.map fun p => p.1 * (C.A (n + C.L + p.2) : ℤ)).sum := by
  induction cs with
  | nil => simp
  | cons p cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))
    have hp := hs p (List.mem_cons_self ..)
    have h2 := A_rec hc (vbound_spec hV) (n := n + p.2) (by omega)
    rw [show n + p.2 + 2 * C.L = n + 2 * C.L + p.2 by omega,
      show n + p.2 + C.L = n + C.L + p.2 by omega] at h2
    have h3 : (C.A (n + 2 * C.L + p.2) : ℤ) + C.A (n + p.2) = 2 * C.A (n + C.L + p.2) := by
      exact_mod_cast h2
    linear_combination h1 + p.1 * h3

theorem lin_zero (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (cs : List (ℤ × ℕ))
    (hs : ∀ p ∈ cs, 1 ≤ p.2)
    (hw : ∀ n < V + 2 * C.L, (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0) :
    ∀ n, (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0 := by
  have F := facts C hc
  intro n
  rcases Nat.lt_or_ge n (V + 2 * C.L) with h | h
  · exact hw n h
  · refine zero_of_window (g := fun n => (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum)
      (L := C.L) (N := V) F.Lpos (fun n hn => lin_rec hc hV cs hs n hn) (fun n _ h2 => hw n h2) n
      (by omega)

end Cfg
end GalCert

namespace GalCert

theorem conv_cs (a : ℕ → ℤ) (l : List ℤ) (k : ℕ) :
    conv a l (k + l.length) = ((List.range l.length).map fun i => l.getD i 0 * a (k + l.length - i)).sum := by
  induction l generalizing k with
  | nil => simp [conv]
  | cons c l ih =>
    rw [List.length_cons, show k + (l.length + 1) = (k + l.length) + 1 by omega, conv, ih,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [List.getD_cons_zero, Nat.sub_zero, Function.comp_def, List.getD_cons_succ]
    congr 2
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    congr 2
    omega

def csOf (l : List ℤ) (M : ℕ) : List (ℤ × ℕ) := (List.range l.length).map fun i => (l.getD i 0, M - i)

theorem csOf_pos (l : List ℤ) (M : ℕ) (hM : l.length ≤ M) : ∀ p ∈ csOf l M, 1 ≤ p.2 := by
  intro p hp
  unfold csOf at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [List.mem_range] at hi
  simp only
  omega

namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem gf_from (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (a : ℕ → ℤ)
    (ha : ∀ n, 1 ≤ n → a n = C.A n) (dl pl : List ℤ) (M : ℕ) (hM : dl.length ≤ M)
    (hP : pl.length ≤ M)
    (hw : ∀ n < V + 2 * C.L, ((csOf dl M).map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0)
    (hsmall : ∀ n < M, conv a dl n = pl.getD n 0) :
    PowerSeries.mk a * polyOf dl = polyOf pl := by
  apply gf_of_conv
  intro n
  rcases Nat.lt_or_ge n M with h | h
  · exact hsmall n h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + M := ⟨n - M, by omega⟩
    rw [List.getD_eq_default _ _ (by omega),
      show k + M = (k + (M - dl.length)) + dl.length by omega, conv_cs]
    have hz := lin_zero hc hV (csOf dl M) (csOf_pos dl M hM) hw k
    unfold csOf at hz
    rw [List.map_map] at hz
    refine Eq.trans ?_ hz
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [ha _ (by omega), show k + (M - dl.length) + dl.length - i = k + (M - i) by omega]

end Cfg
end GalCert


namespace P315660
open OMA.S_oeis_a315660

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 26) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 2, [[.f ⟨27, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 12 0], [.f ⟨23, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 0]⟩,
    ⟨0, 0, 1, 2, [[.f ⟨27, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 3 0], [.s 7 0], [.s 14 0]], [.s 7 0]⟩,
    ⟨0, 0, 2, 3, [[.f ⟨7, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0]], [.f ⟨27, 11, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨0, 0, 3, 2, [[.s 1 0], [.s 4 0], [.s 7 0], [.s 8 0], [.s 15 0]], [.s 7 1]⟩,
    ⟨0, 0, 4, 3, [[.s 3 0], [.s 5 0], [.s 8 0], [.s 10 0], [.s 17 0]], [.s 3 1]⟩,
    ⟨0, 0, 5, 4, [[.f ⟨11, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 10 0]], [.s 4 1]⟩,
    ⟨0, 0, 6, 1, [[.s 0 0], [.s 12 0], [.s 13 0], [.s 18 0], [.s 19 0], [.f ⟨23, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 18 1]⟩,
    ⟨0, 0, 7, 1, [[.s 1 0], [.s 3 0], [.s 14 0], [.s 15 0], [.s 18 0], [.s 19 0]], [.s 18 2]⟩,
    ⟨0, 0, 8, 3, [[.s 3 0], [.s 4 0], [.s 15 0], [.s 17 0], [.s 20 0], [.s 21 0]], [.s 3 3]⟩,
    ⟨0, 0, 9, 4, [[.s 16 0], [.s 20 0], [.s 21 0], [.f ⟨15, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 16 0]⟩,
    ⟨0, 0, 10, 4, [[.f ⟨11, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 5 0], [.s 17 0], [.s 22 0], [.s 23 0]], [.s 4 3]⟩,
    ⟨0, 0, 11, 6, [[.f ⟨11, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.s 22 0], [.s 23 0], [.f ⟨15, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 22 1]⟩,
    ⟨0, 0, 12, 1, [[.f ⟨27, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 21, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 0 0], [.s 6 0], [.s 18 0]], [.s 18 3]⟩,
    ⟨0, 0, 13, 2, [[.s 6 0], [.s 19 0], [.s 24 0], [.f ⟨23, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 2]⟩,
    ⟨0, 0, 14, 1, [[.f ⟨27, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 22, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 7 0], [.s 18 0]], [.s 18 4]⟩,
    ⟨0, 0, 15, 2, [[.s 3 0], [.s 7 0], [.s 8 0], [.s 19 0], [.s 20 0], [.s 24 0]], [.s 7 3]⟩,
    ⟨0, 0, 16, 3, [[.s 9 0], [.s 20 0], [.s 24 0], [.f ⟨23, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 23, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 24 2]⟩,
    ⟨0, 0, 17, 4, [[.s 4 0], [.s 8 0], [.s 10 0], [.s 21 0], [.s 22 0], [.s 25 0]], [.s 4 4]⟩,
    ⟨0, 0, 18, 0, [[.f ⟨27, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 7 0], [.s 12 0], [.s 14 0], [.s 19 0]], [.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨0, 0, 19, 1, [[.s 6 0], [.s 7 0], [.s 13 0], [.s 15 0], [.s 18 0], [.s 24 0]], [.s 18 5]⟩,
    ⟨0, 0, 20, 3, [[.s 8 0], [.s 9 0], [.s 15 0], [.s 16 0], [.s 21 0], [.s 24 0]], [.s 15 4]⟩,
    ⟨0, 0, 21, 4, [[.s 8 0], [.s 9 0], [.s 17 0], [.s 20 0], [.s 25 0], [.f ⟨15, 12, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 5]⟩,
    ⟨0, 0, 22, 5, [[.s 10 0], [.s 11 0], [.s 17 0], [.s 23 0], [.s 25 0], [.f ⟨15, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 10 4]⟩,
    ⟨0, 0, 23, 5, [[.f ⟨11, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.s 10 0], [.s 11 0], [.s 22 0]], [.s 10 5]⟩,
    ⟨0, 0, 24, 2, [[.s 13 0], [.s 15 0], [.s 16 0], [.s 19 0], [.s 20 0], [.f ⟨23, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 19 5]⟩,
    ⟨0, 0, 25, 5, [[.s 17 0], [.s 21 0], [.s 22 0], [.f ⟨15, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 18, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 17 5]⟩]⟩,
  ⟨1, -2, -1, 0, 0, [(1, -2, 0), (-1, 2, 0), (-2, -1, 5)], -2, -1, 5, 5, 0, 0, 0, 0,
   [⟨-2, -1, 0, 10, [[.f ⟨29, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨30, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 54, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨30, 57, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 57, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 6 0, .s 6 0]⟩,
    ⟨-2, -1, 1, 10, [[.f ⟨29, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 3 0, .s 3 0]⟩,
    ⟨-2, -1, 2, 11, [[.f ⟨8, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨8, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨29, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 52, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 52, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.s 1 1, .s 1 1]⟩,
    ⟨-2, -1, 3, 9, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 8 0, .s 8 0]⟩,
    ⟨-2, -1, 4, 9, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 8 1, .s 8 1]⟩,
    ⟨-2, -1, 5, 10, [[.f ⟨10, 52, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 52, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 58, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 58, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 65, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 65, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.s 4 1, .s 4 1]⟩,
    ⟨-2, -1, 6, 9, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨30, 57, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 57, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 13 0, .s 13 0]⟩,
    ⟨-2, -1, 7, 9, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 15 1, .s 15 1]⟩,
    ⟨-2, -1, 8, 8, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 20 0, .s 20 0]⟩,
    ⟨-2, -1, 9, 6, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 12, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 2, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 0, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-2, -1, 10, 9, [[.f ⟨10, 65, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 65, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 17 2, .s 17 2]⟩,
    ⟨-2, -1, 11, 8, [[.f ⟨10, 68, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 68, 1, 0, 1, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨7, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 14, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨7, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 1, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-2, -1, 12, 10, [[.f ⟨29, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨29, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 21, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨29, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.s 6 1, .s 6 1]⟩,
    ⟨-2, -1, 13, 8, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨30, 57, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 57, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨30, 62, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 62, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨30, 75, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 75, 0, 0, 0, 1, 0, 1, 0⟩]], [.f ⟨30, 75, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 75, 0, 0, 0, 1, 0, 1, 0⟩]⟩,
    ⟨-2, -1, 14, 10, [[.f ⟨29, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨29, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 22, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨29, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.s 7 2, .s 7 2]⟩,
    ⟨-2, -1, 15, 8, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 20 2, .s 20 2]⟩,
    ⟨-2, -1, 16, 7, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨30, 63, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 63, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨30, 75, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 75, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨27, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 2, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 9 0, .s 9 0]⟩,
    ⟨-2, -1, 17, 8, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 21 2, .s 21 2]⟩,
    ⟨-2, -1, 18, 10, [[.f ⟨29, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 6 3, .s 6 3]⟩,
    ⟨-2, -1, 19, 9, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 13 1, .s 13 1]⟩,
    ⟨-2, -1, 20, 7, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 9 1, .s 9 1]⟩,
    ⟨-2, -1, 21, 7, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨7, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 12, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 9 2, .s 9 2]⟩,
    ⟨-2, -1, 22, 8, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨7, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 14, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 25 2, .s 25 2]⟩,
    ⟨-2, -1, 23, 9, [[.f ⟨10, 65, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 65, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 68, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 68, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 76, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 76, 1, 0, 1, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 11 2, .s 11 2]⟩,
    ⟨-2, -1, 24, 8, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨30, 75, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 75, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 16 2, .s 16 2]⟩,
    ⟨-2, -1, 25, 7, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨7, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 12, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 14, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 18, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨7, 12, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨8, 12, 1, 0, 0, 0, 0, 0, 2⟩]⟩]⟩,
  ⟨1, -1, -2, 0, 0, [(2, -1, 0), (-2, 1, 0), (-1, -2, 5)], -1, -2, 5, 5, 0, 0, 0, 0,
   [⟨-1, -2, 0, 8, [[.f ⟨10, 61, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 61, 0, 0, 0, 1, 0, 1, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 5, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 5, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, -2, 1, 11, [[.f ⟨10, 63, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 63, 0, 0, 0, 1, 0, 1, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 7 0, .s 7 0]⟩,
    ⟨-1, -2, 2, 12, [[.f ⟨9, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨9, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 63, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 63, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨10, 63, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨10, 63, 0, 0, 0, 1, 0, 1, 4⟩]⟩,
    ⟨-1, -2, 3, 11, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 7 1, .s 7 1]⟩,
    ⟨-1, -2, 4, 12, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 3 1, .s 3 1]⟩,
    ⟨-1, -2, 5, 13, [[.f ⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 6, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.s 4 1, .s 4 1]⟩,
    ⟨-1, -2, 6, 8, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 5, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨9, 5, 1, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨-1, -2, 7, 10, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 18 2, .s 18 2]⟩,
    ⟨-1, -2, 8, 11, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 15 2, .s 15 2]⟩,
    ⟨-1, -2, 9, 10, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨14, 52, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 52, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 64, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 64, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 2, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 16 0, .s 16 0]⟩,
    ⟨-1, -2, 10, 13, [[.f ⟨12, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 4 3, .s 4 3]⟩,
    ⟨-1, -2, 11, 14, [[.f ⟨12, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨14, 53, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 53, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 54, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 66, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 66, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 22 1, .s 22 1]⟩,
    ⟨-1, -2, 12, 9, [[.f ⟨10, 61, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 61, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 73, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 73, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 77, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 77, 0, 0, 0, 1, 0, 1, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.s 0 2, .s 0 2]⟩,
    ⟨-1, -2, 13, 8, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 23, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨9, 5, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-1, -2, 14, 10, [[.f ⟨10, 63, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 63, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 74, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 74, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 77, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 77, 0, 0, 0, 1, 0, 1, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.s 18 4, .s 18 4]⟩,
    ⟨-1, -2, 15, 10, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 19 3, .s 19 3]⟩,
    ⟨-1, -2, 16, 9, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 23, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 2, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 11, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, -2, 17, 12, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 8 3, .s 8 3]⟩,
    ⟨-1, -2, 18, 9, [[.f ⟨10, 77, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 77, 0, 0, 0, 1, 0, 1, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 6 3, .s 6 3]⟩,
    ⟨-1, -2, 19, 9, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 6 4, .s 6 4]⟩,
    ⟨-1, -2, 20, 10, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 16 1, .s 16 1]⟩,
    ⟨-1, -2, 21, 11, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨14, 64, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 64, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 9 2, .s 9 2]⟩,
    ⟨-1, -2, 22, 13, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨14, 66, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 66, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 17 4, .s 17 4]⟩,
    ⟨-1, -2, 23, 14, [[.f ⟨12, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 24, 1, 0, 1, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 10 5, .s 10 5]⟩,
    ⟨-1, -2, 24, 9, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨7, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 23, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 13 2, .s 13 2]⟩,
    ⟨-1, -2, 25, 12, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨14, 64, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 64, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 66, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 66, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 70, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 70, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 21 4, .s 21 4]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 2)], 1, -1, 2, 2, 0, 0, 0, 0,
   [⟨1, -1, 0, 8, [[.f ⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨15, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 5, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨11, 9, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨13, 9, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, -1, 1, 11, [[.f ⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 7 0, .s 7 0]⟩,
    ⟨1, -1, 2, 12, [[.f ⟨14, 61, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 61, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨14, 68, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 68, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨13, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨11, 11, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨13, 11, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, -1, 3, 11, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 7 1, .s 7 1]⟩,
    ⟨1, -1, 4, 12, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 3 1, .s 3 1]⟩,
    ⟨1, -1, 5, 13, [[.f ⟨13, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨13, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 6, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨13, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.s 4 1, .s 4 1]⟩,
    ⟨1, -1, 6, 9, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨15, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 5, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 0 1, .s 0 1]⟩,
    ⟨1, -1, 7, 10, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 18 2, .s 18 2]⟩,
    ⟨1, -1, 8, 12, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 3 3, .s 3 3]⟩,
    ⟨1, -1, 9, 13, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨16, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 16 0, .s 16 0]⟩,
    ⟨1, -1, 10, 13, [[.f ⟨13, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 4 3, .s 4 3]⟩,
    ⟨1, -1, 11, 15, [[.f ⟨13, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨16, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 1, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 22 1, .s 22 1]⟩,
    ⟨1, -1, 12, 8, [[.f ⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 21, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 25, 1, 0, 0, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨11, 9, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨13, 9, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, -1, 13, 10, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨15, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 23, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨1, -1, 14, 10, [[.f ⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 22, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 25, 1, 0, 0, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨11, 25, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨13, 25, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, -1, 15, 11, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 7 3, .s 7 3]⟩,
    ⟨1, -1, 16, 12, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨15, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 23, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨18, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 24 2, .s 24 2]⟩,
    ⟨1, -1, 17, 13, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 4 4, .s 4 4]⟩,
    ⟨1, -1, 18, 9, [[.f ⟨11, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 25, 1, 0, 0, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 12 5, .s 12 5]⟩,
    ⟨1, -1, 19, 10, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 6 4, .s 6 4]⟩,
    ⟨1, -1, 20, 12, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 15 4, .s 15 4]⟩,
    ⟨1, -1, 21, 13, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨16, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 12, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 8 5, .s 8 5]⟩,
    ⟨1, -1, 22, 14, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨16, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 10 4, .s 10 4]⟩,
    ⟨1, -1, 23, 14, [[.f ⟨13, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨13, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨13, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 24, 1, 0, 1, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 10 5, .s 10 5]⟩,
    ⟨1, -1, 24, 11, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨15, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 23, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 13 2, .s 13 2]⟩,
    ⟨1, -1, 25, 14, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨16, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 14, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 18, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 17 5, .s 17 5]⟩]⟩,
  ⟨1, 2, 1, 0, 0, [(-1, 2, 0), (1, -2, 0), (2, 1, 5)], 2, 1, 5, 5, 0, 0, 0, 0,
   [⟨2, 1, 0, 10, [[.f ⟨19, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨22, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨19, 9, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨20, 9, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨2, 1, 1, 10, [[.f ⟨19, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.f ⟨19, 11, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨20, 11, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨2, 1, 2, 10, [[.f ⟨15, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 16, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨18, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 0, 0, 0, 0, 1, 0, 1, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨15, 16, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨17, 16, 1, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨2, 1, 3, 11, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 1 2, .s 1 2]⟩,
    ⟨2, 1, 4, 12, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 3 1, .s 3 1]⟩,
    ⟨2, 1, 5, 12, [[.f ⟨18, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 0, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨18, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 6, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨18, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 13, 0, 0, 0, 1, 0, 1, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨18, 0, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨18, 0, 0, 0, 0, 1, 0, 1, 4⟩]⟩,
    ⟨2, 1, 6, 10, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨22, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 12 4, .s 12 4]⟩,
    ⟨2, 1, 7, 10, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 14 4, .s 14 4]⟩,
    ⟨2, 1, 8, 12, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 3 3, .s 3 3]⟩,
    ⟨2, 1, 9, 13, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨17, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨20, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 20 1, .s 20 1]⟩,
    ⟨2, 1, 10, 13, [[.f ⟨18, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 13, 0, 0, 0, 1, 0, 1, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 4 3, .s 4 3]⟩,
    ⟨2, 1, 11, 15, [[.f ⟨18, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 16, 0, 0, 0, 1, 0, 1, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨17, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 1, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 22 1, .s 22 1]⟩,
    ⟨2, 1, 12, 9, [[.f ⟨19, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 21, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 25, 1, 0, 0, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨19, 21, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨20, 21, 1, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨2, 1, 13, 11, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨22, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨2, 1, 14, 9, [[.f ⟨19, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 22, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 25, 1, 0, 0, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨19, 22, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨20, 22, 1, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨2, 1, 15, 11, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 7 3, .s 7 3]⟩,
    ⟨2, 1, 16, 13, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 23, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨20, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 20 3, .s 20 3]⟩,
    ⟨2, 1, 17, 13, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 4 4, .s 4 4]⟩,
    ⟨2, 1, 18, 10, [[.f ⟨19, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 25, 1, 0, 0, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.f ⟨19, 25, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨20, 25, 1, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨2, 1, 19, 11, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 6 4, .s 6 4]⟩,
    ⟨2, 1, 20, 12, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 15 4, .s 15 4]⟩,
    ⟨2, 1, 21, 13, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨17, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 12, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 8 5, .s 8 5]⟩,
    ⟨2, 1, 22, 14, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨17, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 10 4, .s 10 4]⟩,
    ⟨2, 1, 23, 14, [[.f ⟨18, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 13, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨18, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 16, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨18, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 24, 0, 0, 0, 1, 0, 1, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨18, 13, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨18, 13, 0, 0, 0, 1, 0, 1, 5⟩]⟩,
    ⟨2, 1, 24, 12, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨22, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 13 2, .s 13 2]⟩,
    ⟨2, 1, 25, 14, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨17, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 14, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 18, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 17 5, .s 17 5]⟩]⟩,
  ⟨1, 1, 2, 0, 0, [(-2, 1, 0), (2, -1, 0), (1, 2, 5)], 1, 2, 5, 5, 0, 0, 0, 0,
   [⟨1, 2, 0, 11, [[.f ⟨26, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨24, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 6 0, .s 6 0]⟩,
    ⟨1, 2, 1, 8, [[.f ⟨26, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.f ⟨26, 11, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨26, 11, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, 2, 2, 7, [[.f ⟨23, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 16, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨26, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨19, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨23, 9, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨24, 9, 1, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 2, 3, 9, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 1 2, .s 1 2]⟩,
    ⟨1, 2, 4, 9, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 5 3, .s 5 3]⟩,
    ⟨1, 2, 5, 8, [[.f ⟨19, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 6, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 13, 1, 0, 0, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨19, 0, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨21, 0, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 2, 6, 10, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨24, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 18 1, .s 18 1]⟩,
    ⟨1, 2, 7, 9, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 1 3, .s 1 3]⟩,
    ⟨1, 2, 8, 10, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 3 3, .s 3 3]⟩,
    ⟨1, 2, 9, 12, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 0, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 12, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨21, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 20 1, .s 20 1]⟩,
    ⟨1, 2, 10, 9, [[.f ⟨19, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 13, 1, 0, 0, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.f ⟨19, 13, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨21, 13, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 2, 11, 10, [[.f ⟨19, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 16, 1, 0, 0, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨22, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 1, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 2, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 14, 0, 0, 0, 1, 0, 1, 0⟩]], [.f ⟨19, 16, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨21, 16, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 2, 12, 10, [[.f ⟨26, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 21, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨26, 25, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨26, 25, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, 2, 13, 11, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨24, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨1, 2, 14, 8, [[.f ⟨26, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 22, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨26, 11, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨26, 11, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨1, 2, 15, 10, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 3 4, .s 3 4]⟩,
    ⟨1, 2, 16, 12, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨24, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 23, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨21, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 20 3, .s 20 3]⟩,
    ⟨1, 2, 17, 10, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 4 4, .s 4 4]⟩,
    ⟨1, 2, 18, 9, [[.f ⟨26, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 14 5, .s 14 5]⟩,
    ⟨1, 2, 19, 10, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 7 5, .s 7 5]⟩,
    ⟨1, 2, 20, 11, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 8 4, .s 8 4]⟩,
    ⟨1, 2, 21, 11, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨22, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 12, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 8 5, .s 8 5]⟩,
    ⟨1, 2, 22, 10, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨22, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 14, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 10 4, .s 10 4]⟩,
    ⟨1, 2, 23, 9, [[.f ⟨19, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 13, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 16, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 24, 1, 0, 0, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨19, 13, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨21, 13, 1, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 2, 24, 11, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨24, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 15 5, .s 15 5]⟩,
    ⟨1, 2, 25, 11, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨22, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 12, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 14, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 18, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 17 5, .s 17 5]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 2)], -1, 1, 2, 2, 0, 0, 0, 0,
   [⟨-1, 1, 0, 11, [[.f ⟨28, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨25, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨25, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 6 0, .s 6 0]⟩,
    ⟨-1, 1, 1, 8, [[.f ⟨28, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 3 0, .s 3 0]⟩,
    ⟨-1, 1, 2, 8, [[.f ⟨30, 61, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 61, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨30, 68, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 68, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨28, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨27, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨27, 0, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨28, 0, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 1, 3, 7, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 4 0, .s 4 0]⟩,
    ⟨-1, 1, 4, 6, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 10 1, .s 10 1]⟩,
    ⟨-1, 1, 5, 6, [[.f ⟨27, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 6, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 13, 1, 0, 0, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨27, 13, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨28, 13, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 1, 6, 10, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨25, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 18 1, .s 18 1]⟩,
    ⟨-1, 1, 7, 8, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 3 2, .s 3 2]⟩,
    ⟨-1, 1, 8, 7, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 4 2, .s 4 2]⟩,
    ⟨-1, 1, 9, 8, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨23, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 12, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨26, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 2, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 21 1, .s 21 1]⟩,
    ⟨-1, 1, 10, 5, [[.f ⟨27, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 13, 1, 0, 0, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 23 3, .s 23 3]⟩,
    ⟨-1, 1, 11, 4, [[.f ⟨27, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 16, 1, 0, 0, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨23, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 14, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨27, 16, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨28, 16, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 1, 12, 10, [[.f ⟨28, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨28, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 21, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨28, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.s 18 3, .s 18 3]⟩,
    ⟨-1, 1, 13, 10, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨25, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨25, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨25, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 19 2, .s 19 2]⟩,
    ⟨-1, 1, 14, 9, [[.f ⟨28, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨28, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 22, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨28, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.s 1 4, .s 1 4]⟩,
    ⟨-1, 1, 15, 8, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 3 4, .s 3 4]⟩,
    ⟨-1, 1, 16, 9, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨25, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨25, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 23, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 2, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 9 0, .s 9 0]⟩,
    ⟨-1, 1, 17, 6, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 10 3, .s 10 3]⟩,
    ⟨-1, 1, 18, 9, [[.f ⟨28, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 7 4, .s 7 4]⟩,
    ⟨-1, 1, 19, 9, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 7 5, .s 7 5]⟩,
    ⟨-1, 1, 20, 8, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 8 4, .s 8 4]⟩,
    ⟨-1, 1, 21, 7, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨23, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 12, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 17 3, .s 17 3]⟩,
    ⟨-1, 1, 22, 5, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨23, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 14, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 11 1, .s 11 1]⟩,
    ⟨-1, 1, 23, 4, [[.f ⟨27, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 13, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 16, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 24, 1, 0, 0, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨27, 16, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨28, 16, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨-1, 1, 24, 9, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨25, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 15 5, .s 15 5]⟩,
    ⟨-1, 1, 25, 6, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨23, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 12, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 14, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 18, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 22 4, .s 22 4]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-2, 1, 1), (1, -2, 1), (2, -1, -1), (-1, 2, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, -1, 0, 5, [[.f ⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 12 0], [.f ⟨27, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨27, 5, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, -1, 1, 7, [[.f ⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 3 0], [.s 7 0], [.s 14 0]], [.s 3 0]⟩,
    ⟨-1, -1, 2, 8, [[.f ⟨10, 61, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨10, 68, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨2, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0]], [.s 1 1]⟩,
    ⟨-1, -1, 3, 6, [[.s 1 0], [.s 4 0], [.s 7 0], [.s 8 0], [.s 15 0]], [.s 8 0]⟩,
    ⟨-1, -1, 4, 6, [[.s 3 0], [.s 5 0], [.s 8 0], [.s 10 0], [.s 17 0]], [.s 8 1]⟩,
    ⟨-1, -1, 5, 7, [[.f ⟨2, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨2, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨2, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 10 0]], [.s 4 1]⟩,
    ⟨-1, -1, 6, 5, [[.s 0 0], [.s 12 0], [.s 13 0], [.s 18 0], [.s 19 0], [.f ⟨27, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 13 0]⟩,
    ⟨-1, -1, 7, 6, [[.s 1 0], [.s 3 0], [.s 14 0], [.s 15 0], [.s 18 0], [.s 19 0]], [.s 15 1]⟩,
    ⟨-1, -1, 8, 5, [[.s 3 0], [.s 4 0], [.s 15 0], [.s 17 0], [.s 20 0], [.s 21 0]], [.s 20 0]⟩,
    ⟨-1, -1, 9, 4, [[.s 16 0], [.s 20 0], [.s 21 0], [.f ⟨11, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 16 0]⟩,
    ⟨-1, -1, 10, 7, [[.f ⟨2, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 5 0], [.s 17 0], [.s 22 0], [.s 23 0]], [.s 4 3]⟩,
    ⟨-1, -1, 11, 8, [[.f ⟨2, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.s 22 0], [.s 23 0], [.f ⟨11, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 22 1]⟩,
    ⟨-1, -1, 12, 6, [[.f ⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 21, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 0 0], [.s 6 0], [.s 18 0]], [.s 0 2]⟩,
    ⟨-1, -1, 13, 4, [[.s 6 0], [.s 19 0], [.s 24 0], [.f ⟨27, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨27, 10, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, -1, 14, 7, [[.f ⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 22, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 7 0], [.s 18 0]], [.s 7 2]⟩,
    ⟨-1, -1, 15, 5, [[.s 3 0], [.s 7 0], [.s 8 0], [.s 19 0], [.s 20 0], [.s 24 0]], [.s 20 2]⟩,
    ⟨-1, -1, 16, 3, [[.s 9 0], [.s 20 0], [.s 24 0], [.f ⟨27, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 23, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨27, 11, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, -1, 17, 6, [[.s 4 0], [.s 8 0], [.s 10 0], [.s 21 0], [.s 22 0], [.s 25 0]], [.s 8 3]⟩,
    ⟨-1, -1, 18, 6, [[.f ⟨1, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 7 0], [.s 12 0], [.s 14 0], [.s 19 0]], [.s 6 3]⟩,
    ⟨-1, -1, 19, 5, [[.s 6 0], [.s 7 0], [.s 13 0], [.s 15 0], [.s 18 0], [.s 24 0]], [.s 13 1]⟩,
    ⟨-1, -1, 20, 4, [[.s 8 0], [.s 9 0], [.s 15 0], [.s 16 0], [.s 21 0], [.s 24 0]], [.s 16 1]⟩,
    ⟨-1, -1, 21, 5, [[.s 8 0], [.s 9 0], [.s 17 0], [.s 20 0], [.s 25 0], [.f ⟨11, 12, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 9 2]⟩,
    ⟨-1, -1, 22, 7, [[.s 10 0], [.s 11 0], [.s 17 0], [.s 23 0], [.s 25 0], [.f ⟨11, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 17 4]⟩,
    ⟨-1, -1, 23, 8, [[.f ⟨2, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨2, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨2, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.s 10 0], [.s 11 0], [.s 22 0]], [.s 10 5]⟩,
    ⟨-1, -1, 24, 4, [[.s 13 0], [.s 15 0], [.s 16 0], [.s 19 0], [.s 20 0], [.f ⟨27, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 16 2]⟩,
    ⟨-1, -1, 25, 6, [[.s 17 0], [.s 21 0], [.s 22 0], [.f ⟨11, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 18, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 21 4]⟩]⟩,
  ⟨1, -2, -1, 0, 0, [(-2, 1, 2), (1, -2, 1), (-1, 2, -1)], -2, 1, 2, 3, 0, 0, 0, 0,
   [⟨-3, -2, 0, 14, [[.f ⟨1, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 9, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨29, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨29, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨29, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 5, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-3, -2, 1, 16, [[.f ⟨1, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 3 0, .s 3 0]⟩,
    ⟨-3, -2, 2, 17, [[.f ⟨10, 61, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨10, 61, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨10, 68, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨10, 68, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨1, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨10, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 26, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.s 1 1, .s 1 1]⟩,
    ⟨-3, -2, 3, 15, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 8 0, .s 8 0]⟩,
    ⟨-3, -2, 4, 15, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 8 1, .s 8 1]⟩,
    ⟨-3, -2, 5, 16, [[.f ⟨10, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 26, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 32, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 32, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 39, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 39, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.s 4 1, .s 4 1]⟩,
    ⟨-3, -2, 6, 14, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨29, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 13 0, .s 13 0]⟩,
    ⟨-3, -2, 7, 15, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 15 1, .s 15 1]⟩,
    ⟨-3, -2, 8, 14, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 20 0, .s 20 0]⟩,
    ⟨-3, -2, 9, 12, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨10, 52, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 52, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 64, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 64, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨10, 52, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 52, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-3, -2, 10, 15, [[.f ⟨10, 39, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 39, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 17 2, .s 17 2]⟩,
    ⟨-3, -2, 11, 14, [[.f ⟨10, 42, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 42, 1, 0, 1, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨10, 53, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 53, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 54, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 66, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 66, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨10, 53, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 53, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-3, -2, 12, 15, [[.f ⟨1, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 9, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨1, 21, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 21, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨1, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.s 0 2, .s 0 2]⟩,
    ⟨-3, -2, 13, 13, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨29, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨29, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨29, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨29, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 10, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-3, -2, 14, 16, [[.f ⟨1, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨1, 22, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 22, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨1, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.s 7 2, .s 7 2]⟩,
    ⟨-3, -2, 15, 14, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 20 2, .s 20 2]⟩,
    ⟨-3, -2, 16, 12, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨29, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨29, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 23, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨29, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 11, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-3, -2, 17, 14, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 21 2, .s 21 2]⟩,
    ⟨-3, -2, 18, 15, [[.f ⟨1, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 6 3, .s 6 3]⟩,
    ⟨-3, -2, 19, 14, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 13 1, .s 13 1]⟩,
    ⟨-3, -2, 20, 13, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 9 1, .s 9 1]⟩,
    ⟨-3, -2, 21, 13, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨10, 64, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 64, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 9 2, .s 9 2]⟩,
    ⟨-3, -2, 22, 14, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨10, 66, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 66, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 25 2, .s 25 2]⟩,
    ⟨-3, -2, 23, 15, [[.f ⟨10, 39, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 39, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 42, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 42, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 50, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 50, 1, 0, 1, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 11 2, .s 11 2]⟩,
    ⟨-3, -2, 24, 13, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨29, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 16 2, .s 16 2]⟩,
    ⟨-3, -2, 25, 13, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨10, 64, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 64, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 66, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 66, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨10, 70, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 70, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨10, 64, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨10, 64, 1, 0, 1, 0, 0, 0, 2⟩]⟩]⟩,
  ⟨1, -1, -2, 0, 0, [(1, -2, 2), (-2, 1, 1), (2, -1, -1)], 1, -2, 2, 3, 0, 0, 0, 0,
   [⟨-2, -3, 0, 14, [[.f ⟨10, 35, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 35, 0, 0, 0, 1, 0, 1, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨10, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 54, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 57, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 57, 0, 0, 0, 1, 0, 1, 0⟩]], [.f ⟨10, 57, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 57, 0, 0, 0, 1, 0, 1, 0⟩]⟩,
    ⟨-2, -3, 1, 16, [[.f ⟨10, 37, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 37, 0, 0, 0, 1, 0, 1, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 3 0, .s 3 0]⟩,
    ⟨-2, -3, 2, 17, [[.f ⟨10, 61, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨10, 61, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨10, 68, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨10, 68, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨10, 37, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 37, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨2, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.s 1 1, .s 1 1]⟩,
    ⟨-2, -3, 3, 15, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 8 0, .s 8 0]⟩,
    ⟨-2, -3, 4, 15, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 8 1, .s 8 1]⟩,
    ⟨-2, -3, 5, 16, [[.f ⟨2, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨2, 6, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 6, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨2, 13, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 13, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.s 4 1, .s 4 1]⟩,
    ⟨-2, -3, 6, 14, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨10, 57, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 57, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 13 0, .s 13 0]⟩,
    ⟨-2, -3, 7, 15, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 15 1, .s 15 1]⟩,
    ⟨-2, -3, 8, 14, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 20 0, .s 20 0]⟩,
    ⟨-2, -3, 9, 13, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨2, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 16 0, .s 16 0]⟩,
    ⟨-2, -3, 10, 16, [[.f ⟨2, 13, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 13, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 4 3, .s 4 3]⟩,
    ⟨-2, -3, 11, 17, [[.f ⟨2, 16, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 16, 1, 0, 2, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨12, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 1, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 22 1, .s 22 1]⟩,
    ⟨-2, -3, 12, 15, [[.f ⟨10, 35, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 35, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 47, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 47, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 51, 0, 0, 0, 1, 0, 1, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.s 0 2, .s 0 2]⟩,
    ⟨-2, -3, 13, 13, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨10, 57, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 57, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 62, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 62, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 75, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 75, 0, 0, 0, 1, 0, 1, 0⟩]], [.f ⟨10, 62, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 62, 0, 0, 0, 1, 0, 1, 0⟩]⟩,
    ⟨-2, -3, 14, 16, [[.f ⟨10, 37, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 37, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 48, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 48, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 51, 0, 0, 0, 1, 0, 1, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.s 7 2, .s 7 2]⟩,
    ⟨-2, -3, 15, 14, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 20 2, .s 20 2]⟩,
    ⟨-2, -3, 16, 12, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨10, 63, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 63, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨10, 75, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 75, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨2, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨10, 63, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 63, 0, 0, 0, 1, 0, 1, 0⟩]⟩,
    ⟨-2, -3, 17, 15, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 8 3, .s 8 3]⟩,
    ⟨-2, -3, 18, 15, [[.f ⟨10, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 51, 0, 0, 0, 1, 0, 1, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 6 3, .s 6 3]⟩,
    ⟨-2, -3, 19, 14, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 13 1, .s 13 1]⟩,
    ⟨-2, -3, 20, 13, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 16 1, .s 16 1]⟩,
    ⟨-2, -3, 21, 14, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨12, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 12, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 9 2, .s 9 2]⟩,
    ⟨-2, -3, 22, 16, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨12, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 17 4, .s 17 4]⟩,
    ⟨-2, -3, 23, 17, [[.f ⟨2, 13, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 13, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨2, 16, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 16, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨2, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 24, 1, 0, 2, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 10 5, .s 10 5]⟩,
    ⟨-2, -3, 24, 13, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨10, 75, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 75, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 16 2, .s 16 2]⟩,
    ⟨-2, -3, 25, 15, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨12, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 14, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 18, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 21 4, .s 21 4]⟩]⟩,
  ⟨2, -2, -1, -1, -2, [(-2, 1, 2), (1, -2, 2)], -2, 1, 2, 3, 1, -2, 2, 3,
   [⟨-4, -4, 0, 23, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]⟩,
    ⟨-4, -4, 1, 25, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 3 0, .s 3 0, .s 3 0, .s 3 0]⟩,
    ⟨-4, -4, 2, 26, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.s 1 1, .s 1 1, .s 1 1, .s 1 1]⟩,
    ⟨-4, -4, 3, 24, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0]], [.s 8 0, .s 8 0, .s 8 0, .s 8 0]⟩,
    ⟨-4, -4, 4, 24, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0]], [.s 8 1, .s 8 1, .s 8 1, .s 8 1]⟩,
    ⟨-4, -4, 5, 25, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.s 4 1, .s 4 1, .s 4 1, .s 4 1]⟩,
    ⟨-4, -4, 6, 23, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 13 0, .s 13 0, .s 13 0, .s 13 0]⟩,
    ⟨-4, -4, 7, 24, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 15 1, .s 15 1, .s 15 1, .s 15 1]⟩,
    ⟨-4, -4, 8, 23, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.s 20 0, .s 20 0, .s 20 0, .s 20 0]⟩,
    ⟨-4, -4, 9, 21, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]⟩,
    ⟨-4, -4, 10, 24, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 17 2, .s 17 2, .s 17 2, .s 17 2]⟩,
    ⟨-4, -4, 11, 23, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 53 0, .s 53 0, .s 53 0, .s 53 0]⟩,
    ⟨-4, -4, 12, 24, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 0 2, .s 0 2, .s 0 2, .s 0 2]⟩,
    ⟨-4, -4, 13, 22, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]⟩,
    ⟨-4, -4, 14, 25, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 7 2, .s 7 2, .s 7 2, .s 7 2]⟩,
    ⟨-4, -4, 15, 23, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 20 2, .s 20 2, .s 20 2, .s 20 2]⟩,
    ⟨-4, -4, 16, 21, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 63 0, .s 63 0, .s 63 0, .s 63 0]⟩,
    ⟨-4, -4, 17, 23, [[.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 21 2, .s 21 2, .s 21 2, .s 21 2]⟩,
    ⟨-4, -4, 18, 24, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 6 3, .s 6 3, .s 6 3, .s 6 3]⟩,
    ⟨-4, -4, 19, 23, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 13 1, .s 13 1, .s 13 1, .s 13 1]⟩,
    ⟨-4, -4, 20, 22, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 9 1, .s 9 1, .s 9 1, .s 9 1]⟩,
    ⟨-4, -4, 21, 22, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 9 2, .s 9 2, .s 9 2, .s 9 2]⟩,
    ⟨-4, -4, 22, 23, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 25 2, .s 25 2, .s 25 2, .s 25 2]⟩,
    ⟨-4, -4, 23, 24, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.s 11 2, .s 11 2, .s 11 2, .s 11 2]⟩,
    ⟨-4, -4, 24, 22, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 16 2, .s 16 2, .s 16 2, .s 16 2]⟩,
    ⟨-4, -4, 25, 22, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 64 2, .s 64 2, .s 64 2, .s 64 2]⟩,
    ⟨-3, -3, 0, 17, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.f ⟨8, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 2 0, .s 2 0], [.f ⟨8, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 5 0, .s 5 0]], [.f ⟨8, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 5 0, .s 5 0]⟩,
    ⟨-3, -3, 1, 19, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 29 0, .s 29 0, .s 29 0, .s 29 0]⟩,
    ⟨-3, -3, 2, 20, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0]], [.s 27 1, .s 27 1, .s 27 1, .s 27 1]⟩,
    ⟨-3, -3, 3, 18, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0]], [.s 34 0, .s 34 0, .s 34 0, .s 34 0]⟩,
    ⟨-3, -3, 4, 18, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 34 1, .s 34 1, .s 34 1, .s 34 1]⟩,
    ⟨-3, -3, 5, 19, [[.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.s 30 1, .s 30 1, .s 30 1, .s 30 1]⟩,
    ⟨-3, -3, 6, 17, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.f ⟨8, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 5 0, .s 5 0]], [.s 39 0, .s 39 0, .s 39 0, .s 39 0]⟩,
    ⟨-3, -3, 7, 18, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 41 1, .s 41 1, .s 41 1, .s 41 1]⟩,
    ⟨-3, -3, 8, 17, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 46 0, .s 46 0, .s 46 0, .s 46 0]⟩,
    ⟨-3, -3, 9, 15, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.f ⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨9, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨9, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 12 0, .f ⟨9, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 12 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.f ⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨9, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0]⟩,
    ⟨-3, -3, 10, 18, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 43 2, .s 43 2, .s 43 2, .s 43 2]⟩,
    ⟨-3, -3, 11, 17, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.f ⟨9, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 1 0, .f ⟨9, 1, 0, 1, 1, 0, 0, 0, 0⟩, .s 1 0], [.f ⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0, .f ⟨9, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 2 0], [.f ⟨9, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 14 0, .f ⟨9, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 14 0]], [.f ⟨9, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 1 0, .f ⟨9, 1, 0, 1, 1, 0, 0, 0, 0⟩, .s 1 0]⟩,
    ⟨-3, -3, 12, 18, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 26 2, .s 26 2, .s 26 2, .s 26 2]⟩,
    ⟨-3, -3, 13, 16, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.f ⟨8, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 5 0, .s 5 0], [.f ⟨8, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 10, 1, 0, 1, 0, 0, 0, 0⟩, .s 10 0, .s 10 0], [.f ⟨8, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 23 0, .s 23 0]], [.f ⟨8, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 10, 1, 0, 1, 0, 0, 0, 0⟩, .s 10 0, .s 10 0]⟩,
    ⟨-3, -3, 14, 19, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 33 2, .s 33 2, .s 33 2, .s 33 2]⟩,
    ⟨-3, -3, 15, 17, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 46 2, .s 46 2, .s 46 2, .s 46 2]⟩,
    ⟨-3, -3, 16, 15, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.f ⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0], [.f ⟨8, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 23 0, .s 23 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.f ⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0]⟩,
    ⟨-3, -3, 17, 17, [[.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0]], [.s 47 2, .s 47 2, .s 47 2, .s 47 2]⟩,
    ⟨-3, -3, 18, 18, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 32 3, .s 32 3, .s 32 3, .s 32 3]⟩,
    ⟨-3, -3, 19, 17, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 39 1, .s 39 1, .s 39 1, .s 39 1]⟩,
    ⟨-3, -3, 20, 16, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 35 1, .s 35 1, .s 35 1, .s 35 1]⟩,
    ⟨-3, -3, 21, 16, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.f ⟨9, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 12 0, .f ⟨9, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 12 0]], [.s 35 2, .s 35 2, .s 35 2, .s 35 2]⟩,
    ⟨-3, -3, 22, 17, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.f ⟨9, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 14 0, .f ⟨9, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 14 0]], [.s 51 2, .s 51 2, .s 51 2, .s 51 2]⟩,
    ⟨-3, -3, 23, 18, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.s 37 2, .s 37 2, .s 37 2, .s 37 2]⟩,
    ⟨-3, -3, 24, 16, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.f ⟨8, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 23 0, .s 23 0]], [.s 42 2, .s 42 2, .s 42 2, .s 42 2]⟩,
    ⟨-3, -3, 25, 16, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.f ⟨9, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 12 0, .f ⟨9, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 12 0], [.f ⟨9, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 14 0, .f ⟨9, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 14 0], [.f ⟨9, 18, 0, 0, 0, 0, 0, 0, 0⟩, .s 18 0, .f ⟨9, 18, 0, 1, 1, 0, 0, 0, 0⟩, .s 18 0]], [.f ⟨9, 12, 0, 0, 0, 0, 0, 0, 2⟩, .s 12 2, .f ⟨9, 12, 0, 1, 1, 0, 0, 0, 2⟩, .s 12 2]⟩,
    ⟨-2, -2, 0, 11, [[.f ⟨8, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 9 0, .s 9 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.f ⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 28 0, .s 28 0], [.f ⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 31 0, .s 31 0]], [.f ⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 31 0, .s 31 0]⟩,
    ⟨-2, -2, 1, 13, [[.f ⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 55 0, .s 55 0, .s 55 0, .s 55 0]⟩,
    ⟨-2, -2, 2, 14, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.f ⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0], [.f ⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨9, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0]], [.s 53 1, .s 53 1, .s 53 1, .s 53 1]⟩,
    ⟨-2, -2, 3, 12, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 60 0, .s 60 0, .s 60 0, .s 60 0]⟩,
    ⟨-2, -2, 4, 12, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 60 1, .s 60 1, .s 60 1, .s 60 1]⟩,
    ⟨-2, -2, 5, 13, [[.f ⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨9, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨9, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 6 0, .f ⟨9, 6, 0, 1, 1, 0, 0, 0, 0⟩, .s 6 0], [.f ⟨9, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 13 0, .f ⟨9, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 13 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.s 56 1, .s 56 1, .s 56 1, .s 56 1]⟩,
    ⟨-2, -2, 6, 11, [[.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.f ⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 31 0, .s 31 0]], [.s 65 0, .s 65 0, .s 65 0, .s 65 0]⟩,
    ⟨-2, -2, 7, 12, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 67 1, .s 67 1, .s 67 1, .s 67 1]⟩,
    ⟨-2, -2, 8, 11, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 72 0, .s 72 0, .s 72 0, .s 72 0]⟩,
    ⟨-2, -2, 9, 9, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.f ⟨2, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 26 0, .f ⟨2, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 26 0], [.f ⟨2, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 38 0, .f ⟨2, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 38 0], [.f ⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 2, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 2, 0, 1, 0, 0, 0, 0, 0⟩, .s 2 0]], [.f ⟨2, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 26 0, .f ⟨2, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 26 0]⟩,
    ⟨-2, -2, 10, 12, [[.f ⟨9, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 13 0, .f ⟨9, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 13 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 69 2, .s 69 2, .s 69 2, .s 69 2]⟩,
    ⟨-2, -2, 11, 11, [[.f ⟨9, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 16 0, .f ⟨9, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 16 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.f ⟨2, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 27 0, .f ⟨2, 1, 0, 1, 1, 0, 0, 0, 0⟩, .s 27 0], [.f ⟨2, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 28 0, .f ⟨2, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 28 0], [.f ⟨2, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 40 0, .f ⟨2, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 40 0]], [.f ⟨2, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 27 0, .f ⟨2, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 27 0]⟩,
    ⟨-2, -2, 12, 12, [[.f ⟨8, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 9 0, .s 9 0], [.f ⟨8, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 21, 1, 0, 1, 0, 0, 0, 0⟩, .s 21 0, .s 21 0], [.f ⟨8, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 25 0, .s 25 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 52 2, .s 52 2, .s 52 2, .s 52 2]⟩,
    ⟨-2, -2, 13, 10, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.f ⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 31 0, .s 31 0], [.f ⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 10, 1, 0, 1, 0, 0, 0, 0⟩, .s 36 0, .s 36 0], [.f ⟨1, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 49 0, .s 49 0]], [.f ⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 10, 1, 0, 1, 0, 0, 0, 0⟩, .s 36 0, .s 36 0]⟩,
    ⟨-2, -2, 14, 13, [[.f ⟨8, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0], [.f ⟨8, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 22, 1, 0, 1, 0, 0, 0, 0⟩, .s 22 0, .s 22 0], [.f ⟨8, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 25 0, .s 25 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 59 2, .s 59 2, .s 59 2, .s 59 2]⟩,
    ⟨-2, -2, 15, 11, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 72 2, .s 72 2, .s 72 2, .s 72 2]⟩,
    ⟨-2, -2, 16, 9, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.f ⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 37 0, .s 37 0], [.f ⟨1, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 49 0, .s 49 0], [.f ⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 2, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 2, 0, 1, 0, 0, 0, 0, 0⟩, .s 2 0]], [.f ⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 37 0, .s 37 0]⟩,
    ⟨-2, -2, 17, 11, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0]], [.s 73 2, .s 73 2, .s 73 2, .s 73 2]⟩,
    ⟨-2, -2, 18, 12, [[.f ⟨8, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 25 0, .s 25 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 58 3, .s 58 3, .s 58 3, .s 58 3]⟩,
    ⟨-2, -2, 19, 11, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 65 1, .s 65 1, .s 65 1, .s 65 1]⟩,
    ⟨-2, -2, 20, 10, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 61 1, .s 61 1, .s 61 1, .s 61 1]⟩,
    ⟨-2, -2, 21, 10, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.f ⟨2, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 38 0, .f ⟨2, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 38 0]], [.s 61 2, .s 61 2, .s 61 2, .s 61 2]⟩,
    ⟨-2, -2, 22, 11, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.f ⟨2, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 40 0, .f ⟨2, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 40 0]], [.s 77 2, .s 77 2, .s 77 2, .s 77 2]⟩,
    ⟨-2, -2, 23, 12, [[.f ⟨9, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 13 0, .f ⟨9, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 13 0], [.f ⟨9, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 16 0, .f ⟨9, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 16 0], [.f ⟨9, 24, 0, 0, 0, 0, 0, 0, 0⟩, .s 24 0, .f ⟨9, 24, 0, 1, 1, 0, 0, 0, 0⟩, .s 24 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.s 63 2, .s 63 2, .s 63 2, .s 63 2]⟩,
    ⟨-2, -2, 24, 10, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.f ⟨1, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 49 0, .s 49 0]], [.s 68 2, .s 68 2, .s 68 2, .s 68 2]⟩,
    ⟨-2, -2, 25, 10, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.f ⟨2, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 38 0, .f ⟨2, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 38 0], [.f ⟨2, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 40 0, .f ⟨2, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 40 0], [.f ⟨2, 18, 0, 0, 0, 0, 0, 0, 0⟩, .s 44 0, .f ⟨2, 18, 0, 1, 1, 0, 0, 0, 0⟩, .s 44 0]], [.f ⟨2, 12, 0, 0, 0, 0, 0, 0, 2⟩, .s 38 2, .f ⟨2, 12, 0, 1, 1, 0, 0, 0, 2⟩, .s 38 2]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, -1, 1), (2, -1, 1), (1, 1, -1), (-2, 1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, -1, 0, 4, [[.f ⟨7, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 12 0], [.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, -1, 1, 8, [[.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 3 0], [.s 7 0], [.s 14 0]], [.s 7 0]⟩,
    ⟨0, -1, 2, 9, [[.f ⟨2, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨2, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 52, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0]], [.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨0, -1, 3, 8, [[.s 1 0], [.s 4 0], [.s 7 0], [.s 8 0], [.s 15 0]], [.s 7 1]⟩,
    ⟨0, -1, 4, 9, [[.s 3 0], [.s 5 0], [.s 8 0], [.s 10 0], [.s 17 0]], [.s 3 1]⟩,
    ⟨0, -1, 5, 10, [[.f ⟨14, 52, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 58, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 65, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 10 0]], [.s 4 1]⟩,
    ⟨0, -1, 6, 5, [[.s 0 0], [.s 12 0], [.s 13 0], [.s 18 0], [.s 19 0], [.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 0 1]⟩,
    ⟨0, -1, 7, 7, [[.s 1 0], [.s 3 0], [.s 14 0], [.s 15 0], [.s 18 0], [.s 19 0]], [.s 18 2]⟩,
    ⟨0, -1, 8, 8, [[.s 3 0], [.s 4 0], [.s 15 0], [.s 17 0], [.s 20 0], [.s 21 0]], [.s 15 2]⟩,
    ⟨0, -1, 9, 7, [[.s 16 0], [.s 20 0], [.s 21 0], [.f ⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 16 0]⟩,
    ⟨0, -1, 10, 10, [[.f ⟨14, 65, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 5 0], [.s 17 0], [.s 22 0], [.s 23 0]], [.s 4 3]⟩,
    ⟨0, -1, 11, 11, [[.f ⟨14, 68, 0, 0, 0, 0, 0, 0, 0⟩], [.s 22 0], [.s 23 0], [.f ⟨3, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 22 1]⟩,
    ⟨0, -1, 12, 5, [[.f ⟨7, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 21, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 0 0], [.s 6 0], [.s 18 0]], [.f ⟨7, 9, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨0, -1, 13, 5, [[.s 6 0], [.s 19 0], [.s 24 0], [.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, -1, 14, 7, [[.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 22, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 7 0], [.s 18 0]], [.f ⟨7, 25, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨0, -1, 15, 7, [[.s 3 0], [.s 7 0], [.s 8 0], [.s 19 0], [.s 20 0], [.s 24 0]], [.s 19 3]⟩,
    ⟨0, -1, 16, 6, [[.s 9 0], [.s 20 0], [.s 24 0], [.f ⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 23, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 23, 0, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨0, -1, 17, 9, [[.s 4 0], [.s 8 0], [.s 10 0], [.s 21 0], [.s 22 0], [.s 25 0]], [.s 8 3]⟩,
    ⟨0, -1, 18, 6, [[.f ⟨7, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 7 0], [.s 12 0], [.s 14 0], [.s 19 0]], [.s 6 3]⟩,
    ⟨0, -1, 19, 6, [[.s 6 0], [.s 7 0], [.s 13 0], [.s 15 0], [.s 18 0], [.s 24 0]], [.s 6 4]⟩,
    ⟨0, -1, 20, 7, [[.s 8 0], [.s 9 0], [.s 15 0], [.s 16 0], [.s 21 0], [.s 24 0]], [.s 16 1]⟩,
    ⟨0, -1, 21, 8, [[.s 8 0], [.s 9 0], [.s 17 0], [.s 20 0], [.s 25 0], [.f ⟨3, 12, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 9 2]⟩,
    ⟨0, -1, 22, 10, [[.s 10 0], [.s 11 0], [.s 17 0], [.s 23 0], [.s 25 0], [.f ⟨3, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 17 4]⟩,
    ⟨0, -1, 23, 11, [[.f ⟨14, 65, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 68, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 76, 0, 0, 0, 0, 0, 0, 0⟩], [.s 10 0], [.s 11 0], [.s 22 0]], [.s 10 5]⟩,
    ⟨0, -1, 24, 6, [[.s 13 0], [.s 15 0], [.s 16 0], [.s 19 0], [.s 20 0], [.f ⟨0, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 13 2]⟩,
    ⟨0, -1, 25, 9, [[.s 17 0], [.s 21 0], [.s 22 0], [.f ⟨3, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 18, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 21 4]⟩]⟩,
  ⟨1, -1, -2, 0, 0, [(-1, -1, 2), (2, -1, 1), (-2, 1, -1)], -1, -1, 2, 3, 0, 0, 0, 0,
   [⟨-1, -3, 0, 13, [[.f ⟨9, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨2, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨2, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨2, 2, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨2, 2, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-1, -3, 1, 17, [[.f ⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 7 0, .s 7 0]⟩,
    ⟨-1, -3, 2, 18, [[.f ⟨2, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 9, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨2, 16, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨2, 16, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 52, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 52, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨9, 11, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨9, 11, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨-1, -3, 3, 17, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 7 1, .s 7 1]⟩,
    ⟨-1, -3, 4, 18, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 3 1, .s 3 1]⟩,
    ⟨-1, -3, 5, 19, [[.f ⟨14, 52, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 52, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 58, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 58, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 65, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 65, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.s 4 1, .s 4 1]⟩,
    ⟨-1, -3, 6, 14, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨2, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 0 1, .s 0 1]⟩,
    ⟨-1, -3, 7, 16, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 18 2, .s 18 2]⟩,
    ⟨-1, -3, 8, 17, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 15 2, .s 15 2]⟩,
    ⟨-1, -3, 9, 16, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨14, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 26, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 38, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 38, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 54, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 16 0, .s 16 0]⟩,
    ⟨-1, -3, 10, 19, [[.f ⟨14, 65, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 65, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 4 3, .s 4 3]⟩,
    ⟨-1, -3, 11, 20, [[.f ⟨14, 68, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 68, 1, 0, 2, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨14, 27, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 27, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 28, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 28, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 40, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 40, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 22 1, .s 22 1]⟩,
    ⟨-1, -3, 12, 14, [[.f ⟨9, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨9, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 21, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨9, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨9, 9, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨9, 9, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨-1, -3, 13, 14, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨2, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨2, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨2, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨2, 5, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨2, 5, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨-1, -3, 14, 16, [[.f ⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨9, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 22, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨9, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨9, 25, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨9, 25, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨-1, -3, 15, 16, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 19 3, .s 19 3]⟩,
    ⟨-1, -3, 16, 15, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨2, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 23, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 54, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 11, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-1, -3, 17, 18, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 8 3, .s 8 3]⟩,
    ⟨-1, -3, 18, 15, [[.f ⟨9, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨9, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 6 3, .s 6 3]⟩,
    ⟨-1, -3, 19, 15, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 6 4, .s 6 4]⟩,
    ⟨-1, -3, 20, 16, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 16 1, .s 16 1]⟩,
    ⟨-1, -3, 21, 17, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨14, 38, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 38, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 9 2, .s 9 2]⟩,
    ⟨-1, -3, 22, 19, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨14, 40, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 40, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 17 4, .s 17 4]⟩,
    ⟨-1, -3, 23, 20, [[.f ⟨14, 65, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 65, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 68, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 68, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 76, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 76, 1, 0, 2, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 10 5, .s 10 5]⟩,
    ⟨-1, -3, 24, 15, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨2, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 13 2, .s 13 2]⟩,
    ⟨-1, -3, 25, 18, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨14, 38, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 38, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 40, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 40, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 44, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 44, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 21 4, .s 21 4]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(2, -1, 2), (-1, -1, 1), (1, 1, -1)], 2, -1, 2, 3, 0, 0, 0, 0,
   [⟨1, -2, 0, 13, [[.f ⟨14, 61, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 61, 0, 0, 0, 1, 0, 1, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨3, 2, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, -2, 1, 17, [[.f ⟨14, 63, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 63, 0, 0, 0, 1, 0, 1, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 7 0, .s 7 0]⟩,
    ⟨1, -2, 2, 18, [[.f ⟨14, 35, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 35, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨14, 42, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 42, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨14, 63, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 63, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨14, 52, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨14, 52, 0, 0, 0, 1, 0, 2, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨14, 63, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨14, 63, 0, 0, 0, 1, 0, 1, 4⟩]⟩,
    ⟨1, -2, 3, 17, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 7 1, .s 7 1]⟩,
    ⟨1, -2, 4, 18, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 3 1, .s 3 1]⟩,
    ⟨1, -2, 5, 19, [[.f ⟨14, 52, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨14, 52, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨14, 58, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨14, 58, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨14, 65, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨14, 65, 0, 0, 0, 1, 0, 2, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.s 4 1, .s 4 1]⟩,
    ⟨1, -2, 6, 14, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 0 1, .s 0 1]⟩,
    ⟨1, -2, 7, 16, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 18 2, .s 18 2]⟩,
    ⟨1, -2, 8, 17, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 15 2, .s 15 2]⟩,
    ⟨1, -2, 9, 16, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨3, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨3, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 12, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨16, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 16 0, .s 16 0]⟩,
    ⟨1, -2, 10, 19, [[.f ⟨14, 65, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨14, 65, 0, 0, 0, 1, 0, 2, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 4 3, .s 4 3]⟩,
    ⟨1, -2, 11, 20, [[.f ⟨14, 68, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨14, 68, 0, 0, 0, 1, 0, 2, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨3, 1, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 1, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨3, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨3, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 14, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 22 1, .s 22 1]⟩,
    ⟨1, -2, 12, 14, [[.f ⟨14, 61, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 61, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨14, 73, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 73, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨14, 77, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 77, 0, 0, 0, 1, 0, 1, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨14, 61, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨14, 61, 0, 0, 0, 1, 0, 1, 4⟩]⟩,
    ⟨1, -2, 13, 14, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨3, 5, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨1, -2, 14, 16, [[.f ⟨14, 63, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 63, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨14, 74, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 74, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨14, 77, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 77, 0, 0, 0, 1, 0, 1, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨14, 77, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨14, 77, 0, 0, 0, 1, 0, 1, 4⟩]⟩,
    ⟨1, -2, 15, 16, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 19 3, .s 19 3]⟩,
    ⟨1, -2, 16, 15, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 23, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨3, 23, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨3, 23, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨1, -2, 17, 18, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 8 3, .s 8 3]⟩,
    ⟨1, -2, 18, 15, [[.f ⟨14, 77, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 77, 0, 0, 0, 1, 0, 1, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 6 3, .s 6 3]⟩,
    ⟨1, -2, 19, 15, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 6 4, .s 6 4]⟩,
    ⟨1, -2, 20, 16, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 16 1, .s 16 1]⟩,
    ⟨1, -2, 21, 17, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨3, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 12, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 9 2, .s 9 2]⟩,
    ⟨1, -2, 22, 19, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨3, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 14, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 17 4, .s 17 4]⟩,
    ⟨1, -2, 23, 20, [[.f ⟨14, 65, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨14, 65, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨14, 68, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨14, 68, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨14, 76, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨14, 76, 0, 0, 0, 1, 0, 2, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 10 5, .s 10 5]⟩,
    ⟨1, -2, 24, 15, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨3, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 13 2, .s 13 2]⟩,
    ⟨1, -2, 25, 18, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨3, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 12, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨3, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 14, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨3, 18, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 18, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 21 4, .s 21 4]⟩]⟩,
  ⟨2, -1, -2, 1, -1, [(-1, -1, 2), (2, -1, 2)], -1, -1, 2, 3, 2, -1, 2, 3,
   [⟨0, -4, 0, 22, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 28 3, .s 28 3, .s 28 3, .s 28 3]⟩,
    ⟨0, -4, 1, 26, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 7 0, .s 7 0, .s 7 0, .s 7 0]⟩,
    ⟨0, -4, 2, 27, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.s 63 4, .s 63 4, .s 63 4, .s 63 4]⟩,
    ⟨0, -4, 3, 26, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0]], [.s 7 1, .s 7 1, .s 7 1, .s 7 1]⟩,
    ⟨0, -4, 4, 27, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0]], [.s 3 1, .s 3 1, .s 3 1, .s 3 1]⟩,
    ⟨0, -4, 5, 28, [[.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.s 4 1, .s 4 1, .s 4 1, .s 4 1]⟩,
    ⟨0, -4, 6, 23, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 0 1, .s 0 1, .s 0 1, .s 0 1]⟩,
    ⟨0, -4, 7, 25, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 18 2, .s 18 2, .s 18 2, .s 18 2]⟩,
    ⟨0, -4, 8, 26, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.s 15 2, .s 15 2, .s 15 2, .s 15 2]⟩,
    ⟨0, -4, 9, 25, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]⟩,
    ⟨0, -4, 10, 28, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 4 3, .s 4 3, .s 4 3, .s 4 3]⟩,
    ⟨0, -4, 11, 29, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 22 1, .s 22 1, .s 22 1, .s 22 1]⟩,
    ⟨0, -4, 12, 23, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 61 4, .s 61 4, .s 61 4, .s 61 4]⟩,
    ⟨0, -4, 13, 23, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 31 2, .s 31 2, .s 31 2, .s 31 2]⟩,
    ⟨0, -4, 14, 25, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 77 4, .s 77 4, .s 77 4, .s 77 4]⟩,
    ⟨0, -4, 15, 25, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 19 3, .s 19 3, .s 19 3, .s 19 3]⟩,
    ⟨0, -4, 16, 24, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 37 0, .s 37 0, .s 37 0, .s 37 0]⟩,
    ⟨0, -4, 17, 27, [[.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 8 3, .s 8 3, .s 8 3, .s 8 3]⟩,
    ⟨0, -4, 18, 24, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 6 3, .s 6 3, .s 6 3, .s 6 3]⟩,
    ⟨0, -4, 19, 24, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 6 4, .s 6 4, .s 6 4, .s 6 4]⟩,
    ⟨0, -4, 20, 25, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 16 1, .s 16 1, .s 16 1, .s 16 1]⟩,
    ⟨0, -4, 21, 26, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.s 9 2, .s 9 2, .s 9 2, .s 9 2]⟩,
    ⟨0, -4, 22, 28, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 17 4, .s 17 4, .s 17 4, .s 17 4]⟩,
    ⟨0, -4, 23, 29, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.s 10 5, .s 10 5, .s 10 5, .s 10 5]⟩,
    ⟨0, -4, 24, 24, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 13 2, .s 13 2, .s 13 2, .s 13 2]⟩,
    ⟨0, -4, 25, 27, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 21 4, .s 21 4, .s 21 4, .s 21 4]⟩,
    ⟨0, -3, 0, 16, [[.f ⟨12, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 9 0, .s 9 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 54 3, .s 54 3, .s 54 3, .s 54 3]⟩,
    ⟨0, -3, 1, 20, [[.f ⟨12, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 33 0, .s 33 0, .s 33 0, .s 33 0]⟩,
    ⟨0, -3, 2, 21, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.f ⟨12, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0]], [.f ⟨12, 11, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨12, 11, 1, 0, 1, 0, 0, 0, 4⟩, .s 11 4, .s 11 4]⟩,
    ⟨0, -3, 3, 20, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0]], [.s 33 1, .s 33 1, .s 33 1, .s 33 1]⟩,
    ⟨0, -3, 4, 21, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 29 1, .s 29 1, .s 29 1, .s 29 1]⟩,
    ⟨0, -3, 5, 22, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.s 30 1, .s 30 1, .s 30 1, .s 30 1]⟩,
    ⟨0, -3, 6, 17, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 26 1, .s 26 1, .s 26 1, .s 26 1]⟩,
    ⟨0, -3, 7, 19, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 44 2, .s 44 2, .s 44 2, .s 44 2]⟩,
    ⟨0, -3, 8, 20, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 41 2, .s 41 2, .s 41 2, .s 41 2]⟩,
    ⟨0, -3, 9, 19, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.f ⟨13, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0, .f ⟨13, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 2 0]], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]⟩,
    ⟨0, -3, 10, 22, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 30 3, .s 30 3, .s 30 3, .s 30 3]⟩,
    ⟨0, -3, 11, 23, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 48 1, .s 48 1, .s 48 1, .s 48 1]⟩,
    ⟨0, -3, 12, 17, [[.f ⟨12, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 9 0, .s 9 0], [.f ⟨12, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 21, 1, 0, 1, 0, 0, 0, 0⟩, .s 21 0, .s 21 0], [.f ⟨12, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 25 0, .s 25 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.f ⟨12, 9, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨12, 9, 1, 0, 1, 0, 0, 0, 4⟩, .s 9 4, .s 9 4]⟩,
    ⟨0, -3, 13, 17, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 57 2, .s 57 2, .s 57 2, .s 57 2]⟩,
    ⟨0, -3, 14, 19, [[.f ⟨12, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0], [.f ⟨12, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 22, 1, 0, 1, 0, 0, 0, 0⟩, .s 22 0, .s 22 0], [.f ⟨12, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 25 0, .s 25 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.f ⟨12, 25, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨12, 25, 1, 0, 1, 0, 0, 0, 4⟩, .s 25 4, .s 25 4]⟩,
    ⟨0, -3, 15, 19, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 45 3, .s 45 3, .s 45 3, .s 45 3]⟩,
    ⟨0, -3, 16, 18, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.f ⟨13, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0, .f ⟨13, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 2 0]], [.s 63 0, .s 63 0, .s 63 0, .s 63 0]⟩,
    ⟨0, -3, 17, 21, [[.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0]], [.s 34 3, .s 34 3, .s 34 3, .s 34 3]⟩,
    ⟨0, -3, 18, 18, [[.f ⟨12, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 25 0, .s 25 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 32 3, .s 32 3, .s 32 3, .s 32 3]⟩,
    ⟨0, -3, 19, 18, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 32 4, .s 32 4, .s 32 4, .s 32 4]⟩,
    ⟨0, -3, 20, 19, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 42 1, .s 42 1, .s 42 1, .s 42 1]⟩,
    ⟨0, -3, 21, 20, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 35 2, .s 35 2, .s 35 2, .s 35 2]⟩,
    ⟨0, -3, 22, 22, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 43 4, .s 43 4, .s 43 4, .s 43 4]⟩,
    ⟨0, -3, 23, 23, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.s 36 5, .s 36 5, .s 36 5, .s 36 5]⟩,
    ⟨0, -3, 24, 18, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 39 2, .s 39 2, .s 39 2, .s 39 2]⟩,
    ⟨0, -3, 25, 21, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 47 4, .s 47 4, .s 47 4, .s 47 4]⟩,
    ⟨0, -2, 0, 10, [[.f ⟨2, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 35 0, .s 35 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 2, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 2, 0, 1, 0, 0, 0, 0, 0⟩, .s 2 0], [.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 5, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 5, 0, 1, 0, 0, 0, 0, 0⟩, .s 5 0]], [.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨12, 2, 1, 0, 0, 0, 0, 0, 3⟩, .f ⟨13, 2, 0, 1, 0, 0, 0, 0, 3⟩, .s 2 3]⟩,
    ⟨0, -2, 1, 14, [[.f ⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 37 0, .s 37 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 59 0, .s 59 0, .s 59 0, .s 59 0]⟩,
    ⟨0, -2, 2, 15, [[.f ⟨12, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 9 0, .s 9 0], [.f ⟨12, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 16 0, .s 16 0], [.f ⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 37 0, .s 37 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0]], [.f ⟨2, 11, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨2, 11, 1, 0, 1, 0, 0, 0, 4⟩, .s 37 4, .s 37 4]⟩,
    ⟨0, -2, 3, 14, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 59 1, .s 59 1, .s 59 1, .s 59 1]⟩,
    ⟨0, -2, 4, 15, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 55 1, .s 55 1, .s 55 1, .s 55 1]⟩,
    ⟨0, -2, 5, 16, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.s 56 1, .s 56 1, .s 56 1, .s 56 1]⟩,
    ⟨0, -2, 6, 11, [[.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 5, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 5, 0, 1, 0, 0, 0, 0, 0⟩, .s 5 0]], [.s 52 1, .s 52 1, .s 52 1, .s 52 1]⟩,
    ⟨0, -2, 7, 13, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 70 2, .s 70 2, .s 70 2, .s 70 2]⟩,
    ⟨0, -2, 8, 14, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 67 2, .s 67 2, .s 67 2, .s 67 2]⟩,
    ⟨0, -2, 9, 13, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.f ⟨13, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨13, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨13, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 12 0, .f ⟨13, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 12 0], [.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 28 0, .f ⟨3, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 28 0]], [.s 68 0, .s 68 0, .s 68 0, .s 68 0]⟩,
    ⟨0, -2, 10, 16, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 56 3, .s 56 3, .s 56 3, .s 56 3]⟩,
    ⟨0, -2, 11, 17, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.f ⟨13, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 1 0, .f ⟨13, 1, 0, 1, 1, 0, 0, 0, 0⟩, .s 1 0], [.f ⟨13, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0, .f ⟨13, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 2 0], [.f ⟨13, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 14 0, .f ⟨13, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 14 0]], [.s 74 1, .s 74 1, .s 74 1, .s 74 1]⟩,
    ⟨0, -2, 12, 11, [[.f ⟨2, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 35 0, .s 35 0], [.f ⟨2, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 21, 1, 0, 1, 0, 0, 0, 0⟩, .s 47 0, .s 47 0], [.f ⟨2, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.f ⟨2, 9, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨2, 9, 1, 0, 1, 0, 0, 0, 4⟩, .s 35 4, .s 35 4]⟩,
    ⟨0, -2, 13, 11, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 5, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 5, 0, 1, 0, 0, 0, 0, 0⟩, .s 5 0], [.f ⟨11, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 10, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 10, 0, 1, 0, 0, 0, 0, 0⟩, .s 10 0], [.f ⟨11, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 23, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 23, 0, 1, 0, 0, 0, 0, 0⟩, .s 23 0]], [.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨12, 5, 1, 0, 0, 0, 0, 0, 2⟩, .f ⟨13, 5, 0, 1, 0, 0, 0, 0, 2⟩, .s 5 2]⟩,
    ⟨0, -2, 14, 13, [[.f ⟨2, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 37 0, .s 37 0], [.f ⟨2, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 22, 1, 0, 1, 0, 0, 0, 0⟩, .s 48 0, .s 48 0], [.f ⟨2, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 51 0, .s 51 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.f ⟨2, 25, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨2, 25, 1, 0, 1, 0, 0, 0, 4⟩, .s 51 4, .s 51 4]⟩,
    ⟨0, -2, 15, 13, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 71 3, .s 71 3, .s 71 3, .s 71 3]⟩,
    ⟨0, -2, 16, 12, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.f ⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 11, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 11, 0, 1, 0, 0, 0, 0, 0⟩, .s 11 0], [.f ⟨11, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 23, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 23, 0, 1, 0, 0, 0, 0, 0⟩, .s 23 0], [.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 28 0, .f ⟨3, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 28 0]], [.f ⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 11, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 11, 0, 1, 0, 0, 0, 0, 0⟩, .s 11 0]⟩,
    ⟨0, -2, 17, 15, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0]], [.s 60 3, .s 60 3, .s 60 3, .s 60 3]⟩,
    ⟨0, -2, 18, 12, [[.f ⟨2, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 51 0, .s 51 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 58 3, .s 58 3, .s 58 3, .s 58 3]⟩,
    ⟨0, -2, 19, 12, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 58 4, .s 58 4, .s 58 4, .s 58 4]⟩,
    ⟨0, -2, 20, 13, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 68 1, .s 68 1, .s 68 1, .s 68 1]⟩,
    ⟨0, -2, 21, 14, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.f ⟨13, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 12 0, .f ⟨13, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 12 0]], [.s 61 2, .s 61 2, .s 61 2, .s 61 2]⟩,
    ⟨0, -2, 22, 16, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.f ⟨13, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 14 0, .f ⟨13, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 14 0]], [.s 69 4, .s 69 4, .s 69 4, .s 69 4]⟩,
    ⟨0, -2, 23, 17, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.s 62 5, .s 62 5, .s 62 5, .s 62 5]⟩,
    ⟨0, -2, 24, 12, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.f ⟨11, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 23, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 23, 0, 1, 0, 0, 0, 0, 0⟩, .s 23 0]], [.s 65 2, .s 65 2, .s 65 2, .s 65 2]⟩,
    ⟨0, -2, 25, 15, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.f ⟨13, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 12 0, .f ⟨13, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 12 0], [.f ⟨13, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 14 0, .f ⟨13, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 14 0], [.f ⟨13, 18, 0, 0, 0, 0, 0, 0, 0⟩, .s 18 0, .f ⟨13, 18, 0, 1, 1, 0, 0, 0, 0⟩, .s 18 0]], [.s 73 4, .s 73 4, .s 73 4, .s 73 4]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, -2, 1), (1, 1, 1), (-1, 2, -1), (-1, -1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, 0, 0, 5, [[.f ⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 12 0], [.f ⟨19, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 9, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 1, 7, [[.f ⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 3 0], [.s 7 0], [.s 14 0]], [.f ⟨0, 11, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 2, 7, [[.f ⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0]], [.f ⟨11, 16, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 0, 3, 8, [[.s 1 0], [.s 4 0], [.s 7 0], [.s 8 0], [.s 15 0]], [.s 1 2]⟩,
    ⟨1, 0, 4, 9, [[.s 3 0], [.s 5 0], [.s 8 0], [.s 10 0], [.s 17 0]], [.s 3 1]⟩,
    ⟨1, 0, 5, 9, [[.f ⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 10 0]], [.f ⟨3, 0, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 0, 6, 6, [[.s 0 0], [.s 12 0], [.s 13 0], [.s 18 0], [.s 19 0], [.f ⟨19, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 0 1]⟩,
    ⟨1, 0, 7, 7, [[.s 1 0], [.s 3 0], [.s 14 0], [.s 15 0], [.s 18 0], [.s 19 0]], [.s 14 4]⟩,
    ⟨1, 0, 8, 9, [[.s 3 0], [.s 4 0], [.s 15 0], [.s 17 0], [.s 20 0], [.s 21 0]], [.s 3 3]⟩,
    ⟨1, 0, 9, 10, [[.s 16 0], [.s 20 0], [.s 21 0], [.f ⟨18, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨18, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 16 0]⟩,
    ⟨1, 0, 10, 10, [[.f ⟨3, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 5 0], [.s 17 0], [.s 22 0], [.s 23 0]], [.s 4 3]⟩,
    ⟨1, 0, 11, 12, [[.f ⟨3, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.s 22 0], [.s 23 0], [.f ⟨18, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨18, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨18, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 22 1]⟩,
    ⟨1, 0, 12, 5, [[.f ⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 21, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 0 0], [.s 6 0], [.s 18 0]], [.f ⟨0, 9, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 0, 13, 7, [[.s 6 0], [.s 19 0], [.s 24 0], [.f ⟨19, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 2]⟩,
    ⟨1, 0, 14, 6, [[.f ⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 22, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 7 0], [.s 18 0]], [.f ⟨0, 22, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 0, 15, 8, [[.s 3 0], [.s 7 0], [.s 8 0], [.s 19 0], [.s 20 0], [.s 24 0]], [.s 7 3]⟩,
    ⟨1, 0, 16, 9, [[.s 9 0], [.s 20 0], [.s 24 0], [.f ⟨19, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 23, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 24 2]⟩,
    ⟨1, 0, 17, 10, [[.s 4 0], [.s 8 0], [.s 10 0], [.s 21 0], [.s 22 0], [.s 25 0]], [.s 4 4]⟩,
    ⟨1, 0, 18, 6, [[.f ⟨0, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 7 0], [.s 12 0], [.s 14 0], [.s 19 0]], [.f ⟨0, 25, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 0, 19, 7, [[.s 6 0], [.s 7 0], [.s 13 0], [.s 15 0], [.s 18 0], [.s 24 0]], [.s 6 4]⟩,
    ⟨1, 0, 20, 9, [[.s 8 0], [.s 9 0], [.s 15 0], [.s 16 0], [.s 21 0], [.s 24 0]], [.s 15 4]⟩,
    ⟨1, 0, 21, 10, [[.s 8 0], [.s 9 0], [.s 17 0], [.s 20 0], [.s 25 0], [.f ⟨18, 12, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 5]⟩,
    ⟨1, 0, 22, 11, [[.s 10 0], [.s 11 0], [.s 17 0], [.s 23 0], [.s 25 0], [.f ⟨18, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 10 4]⟩,
    ⟨1, 0, 23, 11, [[.f ⟨3, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.s 10 0], [.s 11 0], [.s 22 0]], [.f ⟨3, 13, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 0, 24, 8, [[.s 13 0], [.s 15 0], [.s 16 0], [.s 19 0], [.s 20 0], [.f ⟨19, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 13 2]⟩,
    ⟨1, 0, 25, 11, [[.s 17 0], [.s 21 0], [.s 22 0], [.f ⟨18, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨18, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨18, 18, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 17 5]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, -2, 2), (1, 1, 1), (-1, -1, -1)], 1, -2, 2, 3, 0, 0, 0, 0,
   [⟨2, -1, 0, 14, [[.f ⟨3, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨18, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨3, 9, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨3, 9, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨2, -1, 1, 16, [[.f ⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.f ⟨3, 11, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨3, 11, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨2, -1, 2, 16, [[.f ⟨13, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨13, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨13, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨13, 16, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨13, 16, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨2, -1, 3, 17, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 1 2, .s 1 2]⟩,
    ⟨2, -1, 4, 18, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 3 1, .s 3 1]⟩,
    ⟨2, -1, 5, 18, [[.f ⟨3, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨3, 6, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 6, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨3, 13, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 13, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨3, 0, 0, 0, 1, 0, 0, 0, 4⟩, .f ⟨3, 0, 1, 0, 2, 0, 0, 0, 4⟩]⟩,
    ⟨2, -1, 6, 15, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨18, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 0 1, .s 0 1]⟩,
    ⟨2, -1, 7, 16, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 14 4, .s 14 4]⟩,
    ⟨2, -1, 8, 18, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 3 3, .s 3 3]⟩,
    ⟨2, -1, 9, 19, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨18, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨18, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 12, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨18, 28, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 28, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 16 0, .s 16 0]⟩,
    ⟨2, -1, 10, 19, [[.f ⟨3, 13, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 13, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 4 3, .s 4 3]⟩,
    ⟨2, -1, 11, 21, [[.f ⟨3, 16, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 16, 1, 0, 2, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨18, 1, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 1, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨18, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨18, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 14, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 22 1, .s 22 1]⟩,
    ⟨2, -1, 12, 14, [[.f ⟨3, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 21, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨3, 9, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨3, 9, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨2, -1, 13, 16, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨18, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨2, -1, 14, 15, [[.f ⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 22, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨3, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨3, 22, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨3, 22, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨2, -1, 15, 17, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 7 3, .s 7 3]⟩,
    ⟨2, -1, 16, 18, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨18, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 23, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 28, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 28, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 24 2, .s 24 2]⟩,
    ⟨2, -1, 17, 19, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 4 4, .s 4 4]⟩,
    ⟨2, -1, 18, 15, [[.f ⟨3, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.f ⟨3, 25, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨3, 25, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨2, -1, 19, 16, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 6 4, .s 6 4]⟩,
    ⟨2, -1, 20, 18, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 15 4, .s 15 4]⟩,
    ⟨2, -1, 21, 19, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨18, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 12, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 8 5, .s 8 5]⟩,
    ⟨2, -1, 22, 20, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨18, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 14, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 10 4, .s 10 4]⟩,
    ⟨2, -1, 23, 20, [[.f ⟨3, 13, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 13, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨3, 16, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 16, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨3, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨3, 24, 1, 0, 2, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨3, 13, 0, 0, 1, 0, 0, 0, 5⟩, .f ⟨3, 13, 1, 0, 2, 0, 0, 0, 5⟩]⟩,
    ⟨2, -1, 24, 17, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨18, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 13 2, .s 13 2]⟩,
    ⟨2, -1, 25, 20, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨18, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 12, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨18, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 14, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨18, 18, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨18, 18, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 17 5, .s 17 5]⟩]⟩,
  ⟨1, 2, 1, 0, 0, [(1, 1, 2), (1, -2, 1), (-1, 2, -1)], 1, 1, 2, 3, 0, 0, 0, 0,
   [⟨3, 1, 0, 14, [[.f ⟨4, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨20, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨20, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨4, 9, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨4, 9, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨3, 1, 1, 16, [[.f ⟨4, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.f ⟨4, 11, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨4, 11, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨3, 1, 2, 16, [[.f ⟨18, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 9, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨18, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 16, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨4, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 26, 0, 0, 0, 1, 0, 1, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨18, 16, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨18, 16, 0, 0, 0, 1, 0, 1, 5⟩]⟩,
    ⟨3, 1, 3, 17, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 1 2, .s 1 2]⟩,
    ⟨3, 1, 4, 18, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 3 1, .s 3 1]⟩,
    ⟨3, 1, 5, 18, [[.f ⟨18, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 26, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨18, 32, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 32, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨18, 39, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 39, 0, 0, 0, 1, 0, 1, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨18, 26, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨18, 26, 0, 0, 0, 1, 0, 1, 4⟩]⟩,
    ⟨3, 1, 6, 15, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨20, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 5, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 0 1, .s 0 1]⟩,
    ⟨3, 1, 7, 16, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 14 4, .s 14 4]⟩,
    ⟨3, 1, 8, 18, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 3 3, .s 3 3]⟩,
    ⟨3, 1, 9, 19, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨18, 0, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 0, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨18, 12, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 12, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨4, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 2, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 16 0, .s 16 0]⟩,
    ⟨3, 1, 10, 19, [[.f ⟨18, 39, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 39, 0, 0, 0, 1, 0, 1, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 4 3, .s 4 3]⟩,
    ⟨3, 1, 11, 21, [[.f ⟨18, 42, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 42, 0, 0, 0, 1, 0, 1, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨18, 1, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 1, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨18, 2, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 2, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨18, 14, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 14, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 22 1, .s 22 1]⟩,
    ⟨3, 1, 12, 14, [[.f ⟨4, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨4, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 21, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨4, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨4, 9, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨4, 9, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨3, 1, 13, 16, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨20, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨20, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨20, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨3, 1, 14, 15, [[.f ⟨4, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨4, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 22, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨4, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨4, 22, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨4, 22, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨3, 1, 15, 17, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 7 3, .s 7 3]⟩,
    ⟨3, 1, 16, 18, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨20, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨20, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 23, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨4, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 2, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 24 2, .s 24 2]⟩,
    ⟨3, 1, 17, 19, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 4 4, .s 4 4]⟩,
    ⟨3, 1, 18, 15, [[.f ⟨4, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.f ⟨4, 25, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨4, 25, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨3, 1, 19, 16, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 6 4, .s 6 4]⟩,
    ⟨3, 1, 20, 18, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 15 4, .s 15 4]⟩,
    ⟨3, 1, 21, 19, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨18, 12, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 12, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 8 5, .s 8 5]⟩,
    ⟨3, 1, 22, 20, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨18, 14, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 14, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 10 4, .s 10 4]⟩,
    ⟨3, 1, 23, 20, [[.f ⟨18, 39, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 39, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨18, 42, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 42, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨18, 50, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 50, 0, 0, 0, 1, 0, 1, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨18, 39, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨18, 39, 0, 0, 0, 1, 0, 1, 5⟩]⟩,
    ⟨3, 1, 24, 17, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨20, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 23, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 13 2, .s 13 2]⟩,
    ⟨3, 1, 25, 20, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨18, 12, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 12, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨18, 14, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 14, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨18, 18, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨18, 18, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 17 5, .s 17 5]⟩]⟩,
  ⟨2, 1, -1, 2, 1, [(1, -2, 2), (1, 1, 2)], 1, -2, 2, 3, 1, 1, 2, 3,
   [⟨2, 0, 0, 11, [[.f ⟨15, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 9, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 9, 0, 1, 0, 0, 0, 0, 0⟩, .s 61 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.f ⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 28 0, .f ⟨4, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 28 0], [.f ⟨4, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 31 0, .f ⟨4, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 31 0]], [.f ⟨15, 9, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨16, 9, 1, 0, 0, 0, 0, 0, 3⟩, .f ⟨17, 9, 0, 1, 0, 0, 0, 0, 3⟩, .s 61 3]⟩,
    ⟨2, 0, 1, 13, [[.f ⟨15, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 11, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 11, 0, 1, 0, 0, 0, 0, 0⟩, .s 63 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.f ⟨15, 11, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨16, 11, 1, 0, 0, 0, 0, 0, 3⟩, .f ⟨17, 11, 0, 1, 0, 0, 0, 0, 3⟩, .s 63 3]⟩,
    ⟨2, 0, 2, 13, [[.f ⟨3, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 35 0, .s 35 0], [.f ⟨3, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨3, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 42 0, .s 42 0], [.f ⟨15, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 11, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 11, 0, 1, 0, 0, 0, 0, 0⟩, .s 63 0], [.f ⟨16, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 52 0, .s 52 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.f ⟨3, 16, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨3, 16, 1, 0, 1, 0, 0, 0, 5⟩, .s 42 5, .s 42 5]⟩,
    ⟨2, 0, 3, 14, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0]], [.s 1 2, .s 1 2, .s 1 2, .s 1 2]⟩,
    ⟨2, 0, 4, 15, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0]], [.s 3 1, .s 3 1, .s 3 1, .s 3 1]⟩,
    ⟨2, 0, 5, 15, [[.f ⟨16, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 52 0, .s 52 0], [.f ⟨16, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 6, 1, 0, 1, 0, 0, 0, 0⟩, .s 58 0, .s 58 0], [.f ⟨16, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 65 0, .s 65 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.f ⟨16, 0, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨16, 0, 1, 0, 1, 0, 0, 0, 4⟩, .s 52 4, .s 52 4]⟩,
    ⟨2, 0, 6, 12, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.f ⟨4, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 31 0, .f ⟨4, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 31 0]], [.s 0 1, .s 0 1, .s 0 1, .s 0 1]⟩,
    ⟨2, 0, 7, 13, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 14 4, .s 14 4, .s 14 4, .s 14 4]⟩,
    ⟨2, 0, 8, 15, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.s 3 3, .s 3 3, .s 3 3, .s 3 3]⟩,
    ⟨2, 0, 9, 16, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.f ⟨17, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 54 0, .f ⟨17, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 54 0]], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]⟩,
    ⟨2, 0, 10, 16, [[.f ⟨16, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 65 0, .s 65 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 4 3, .s 4 3, .s 4 3, .s 4 3]⟩,
    ⟨2, 0, 11, 18, [[.f ⟨16, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 68 0, .s 68 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 22 1, .s 22 1, .s 22 1, .s 22 1]⟩,
    ⟨2, 0, 12, 11, [[.f ⟨15, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 9, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 9, 0, 1, 0, 0, 0, 0, 0⟩, .s 61 0], [.f ⟨15, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 21, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 21, 0, 1, 0, 0, 0, 0, 0⟩, .s 73 0], [.f ⟨15, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 25, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 25, 0, 1, 0, 0, 0, 0, 0⟩, .s 77 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨15, 9, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨16, 9, 1, 0, 0, 0, 0, 0, 4⟩, .f ⟨17, 9, 0, 1, 0, 0, 0, 0, 4⟩, .s 61 4]⟩,
    ⟨2, 0, 13, 13, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.f ⟨4, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 31 0, .f ⟨4, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 31 0], [.f ⟨4, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 36 0, .f ⟨4, 10, 0, 1, 1, 0, 0, 0, 0⟩, .s 36 0], [.f ⟨4, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 49 0, .f ⟨4, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 49 0]], [.s 6 2, .s 6 2, .s 6 2, .s 6 2]⟩,
    ⟨2, 0, 14, 12, [[.f ⟨15, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 11, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 11, 0, 1, 0, 0, 0, 0, 0⟩, .s 63 0], [.f ⟨15, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 22, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 22, 0, 1, 0, 0, 0, 0, 0⟩, .s 74 0], [.f ⟨15, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 25, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 25, 0, 1, 0, 0, 0, 0, 0⟩, .s 77 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨15, 22, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨16, 22, 1, 0, 0, 0, 0, 0, 5⟩, .f ⟨17, 22, 0, 1, 0, 0, 0, 0, 5⟩, .s 74 5]⟩,
    ⟨2, 0, 15, 14, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 7 3, .s 7 3, .s 7 3, .s 7 3]⟩,
    ⟨2, 0, 16, 15, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.f ⟨4, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 37 0, .f ⟨4, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 37 0], [.f ⟨4, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 49 0, .f ⟨4, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 49 0], [.f ⟨17, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 54 0, .f ⟨17, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 54 0]], [.s 24 2, .s 24 2, .s 24 2, .s 24 2]⟩,
    ⟨2, 0, 17, 16, [[.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 4 4, .s 4 4, .s 4 4, .s 4 4]⟩,
    ⟨2, 0, 18, 12, [[.f ⟨15, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 25, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 25, 0, 1, 0, 0, 0, 0, 0⟩, .s 77 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.f ⟨15, 25, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨16, 25, 1, 0, 0, 0, 0, 0, 5⟩, .f ⟨17, 25, 0, 1, 0, 0, 0, 0, 5⟩, .s 77 5]⟩,
    ⟨2, 0, 19, 13, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 6 4, .s 6 4, .s 6 4, .s 6 4]⟩,
    ⟨2, 0, 20, 15, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 15 4, .s 15 4, .s 15 4, .s 15 4]⟩,
    ⟨2, 0, 21, 16, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.s 8 5, .s 8 5, .s 8 5, .s 8 5]⟩,
    ⟨2, 0, 22, 17, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 10 4, .s 10 4, .s 10 4, .s 10 4]⟩,
    ⟨2, 0, 23, 17, [[.f ⟨16, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 65 0, .s 65 0], [.f ⟨16, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 68 0, .s 68 0], [.f ⟨16, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 24, 1, 0, 1, 0, 0, 0, 0⟩, .s 76 0, .s 76 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.f ⟨16, 13, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨16, 13, 1, 0, 1, 0, 0, 0, 5⟩, .s 65 5, .s 65 5]⟩,
    ⟨2, 0, 24, 14, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.f ⟨4, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 49 0, .f ⟨4, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 49 0]], [.s 13 2, .s 13 2, .s 13 2, .s 13 2]⟩,
    ⟨2, 0, 25, 17, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 17 5, .s 17 5, .s 17 5, .s 17 5]⟩,
    ⟨3, 0, 0, 17, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.f ⟨17, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 54 0, .f ⟨17, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 54 0], [.f ⟨17, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 57 0, .f ⟨17, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 57 0]], [.s 9 3, .s 9 3, .s 9 3, .s 9 3]⟩,
    ⟨3, 0, 1, 19, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 11 3, .s 11 3, .s 11 3, .s 11 3]⟩,
    ⟨3, 0, 2, 19, [[.f ⟨16, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 61 0, .s 61 0], [.f ⟨16, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 68 0, .s 68 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0]], [.f ⟨16, 16, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨16, 16, 1, 0, 1, 0, 0, 0, 5⟩, .s 68 5, .s 68 5]⟩,
    ⟨3, 0, 3, 20, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0]], [.s 27 2, .s 27 2, .s 27 2, .s 27 2]⟩,
    ⟨3, 0, 4, 21, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 29 1, .s 29 1, .s 29 1, .s 29 1]⟩,
    ⟨3, 0, 5, 21, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.s 0 4, .s 0 4, .s 0 4, .s 0 4]⟩,
    ⟨3, 0, 6, 18, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.f ⟨17, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 57 0, .f ⟨17, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 57 0]], [.s 26 1, .s 26 1, .s 26 1, .s 26 1]⟩,
    ⟨3, 0, 7, 19, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 40 4, .s 40 4, .s 40 4, .s 40 4]⟩,
    ⟨3, 0, 8, 21, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 29 3, .s 29 3, .s 29 3, .s 29 3]⟩,
    ⟨3, 0, 9, 22, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]⟩,
    ⟨3, 0, 10, 22, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 30 3, .s 30 3, .s 30 3, .s 30 3]⟩,
    ⟨3, 0, 11, 24, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 48 1, .s 48 1, .s 48 1, .s 48 1]⟩,
    ⟨3, 0, 12, 17, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 9 4, .s 9 4, .s 9 4, .s 9 4]⟩,
    ⟨3, 0, 13, 19, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.f ⟨17, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 57 0, .f ⟨17, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 57 0], [.f ⟨17, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 62 0, .f ⟨17, 10, 0, 1, 1, 0, 0, 0, 0⟩, .s 62 0], [.f ⟨17, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 75 0, .f ⟨17, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 75 0]], [.s 32 2, .s 32 2, .s 32 2, .s 32 2]⟩,
    ⟨3, 0, 14, 18, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 22 5, .s 22 5, .s 22 5, .s 22 5]⟩,
    ⟨3, 0, 15, 20, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 33 3, .s 33 3, .s 33 3, .s 33 3]⟩,
    ⟨3, 0, 16, 21, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.f ⟨17, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 63 0, .f ⟨17, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 63 0], [.f ⟨17, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 75 0, .f ⟨17, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 75 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 50 2, .s 50 2, .s 50 2, .s 50 2]⟩,
    ⟨3, 0, 17, 22, [[.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0]], [.s 30 4, .s 30 4, .s 30 4, .s 30 4]⟩,
    ⟨3, 0, 18, 18, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 25 5, .s 25 5, .s 25 5, .s 25 5]⟩,
    ⟨3, 0, 19, 19, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 32 4, .s 32 4, .s 32 4, .s 32 4]⟩,
    ⟨3, 0, 20, 21, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 41 4, .s 41 4, .s 41 4, .s 41 4]⟩,
    ⟨3, 0, 21, 22, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 34 5, .s 34 5, .s 34 5, .s 34 5]⟩,
    ⟨3, 0, 22, 23, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 36 4, .s 36 4, .s 36 4, .s 36 4]⟩,
    ⟨3, 0, 23, 23, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.s 13 5, .s 13 5, .s 13 5, .s 13 5]⟩,
    ⟨3, 0, 24, 20, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.f ⟨17, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 75 0, .f ⟨17, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 75 0]], [.s 39 2, .s 39 2, .s 39 2, .s 39 2]⟩,
    ⟨3, 0, 25, 23, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 43 5, .s 43 5, .s 43 5, .s 43 5]⟩,
    ⟨4, 0, 0, 23, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0]], [.s 35 3, .s 35 3, .s 35 3, .s 35 3]⟩,
    ⟨4, 0, 1, 25, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 37 3, .s 37 3, .s 37 3, .s 37 3]⟩,
    ⟨4, 0, 2, 25, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0]], [.s 16 5, .s 16 5, .s 16 5, .s 16 5]⟩,
    ⟨4, 0, 3, 26, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 53 2, .s 53 2, .s 53 2, .s 53 2]⟩,
    ⟨4, 0, 4, 27, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 55 1, .s 55 1, .s 55 1, .s 55 1]⟩,
    ⟨4, 0, 5, 27, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.s 26 4, .s 26 4, .s 26 4, .s 26 4]⟩,
    ⟨4, 0, 6, 24, [[.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0]], [.s 52 1, .s 52 1, .s 52 1, .s 52 1]⟩,
    ⟨4, 0, 7, 25, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 66 4, .s 66 4, .s 66 4, .s 66 4]⟩,
    ⟨4, 0, 8, 27, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 55 3, .s 55 3, .s 55 3, .s 55 3]⟩,
    ⟨4, 0, 9, 28, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 68 0, .s 68 0, .s 68 0, .s 68 0]⟩,
    ⟨4, 0, 10, 28, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 56 3, .s 56 3, .s 56 3, .s 56 3]⟩,
    ⟨4, 0, 11, 30, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 74 1, .s 74 1, .s 74 1, .s 74 1]⟩,
    ⟨4, 0, 12, 23, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 35 4, .s 35 4, .s 35 4, .s 35 4]⟩,
    ⟨4, 0, 13, 25, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 58 2, .s 58 2, .s 58 2, .s 58 2]⟩,
    ⟨4, 0, 14, 24, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 48 5, .s 48 5, .s 48 5, .s 48 5]⟩,
    ⟨4, 0, 15, 26, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 59 3, .s 59 3, .s 59 3, .s 59 3]⟩,
    ⟨4, 0, 16, 27, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 76 2, .s 76 2, .s 76 2, .s 76 2]⟩,
    ⟨4, 0, 17, 28, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0]], [.s 56 4, .s 56 4, .s 56 4, .s 56 4]⟩,
    ⟨4, 0, 18, 24, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 51 5, .s 51 5, .s 51 5, .s 51 5]⟩,
    ⟨4, 0, 19, 25, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 58 4, .s 58 4, .s 58 4, .s 58 4]⟩,
    ⟨4, 0, 20, 27, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 67 4, .s 67 4, .s 67 4, .s 67 4]⟩,
    ⟨4, 0, 21, 28, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0]], [.s 60 5, .s 60 5, .s 60 5, .s 60 5]⟩,
    ⟨4, 0, 22, 29, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 62 4, .s 62 4, .s 62 4, .s 62 4]⟩,
    ⟨4, 0, 23, 29, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.s 39 5, .s 39 5, .s 39 5, .s 39 5]⟩,
    ⟨4, 0, 24, 26, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 65 2, .s 65 2, .s 65 2, .s 65 2]⟩,
    ⟨4, 0, 25, 29, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 69 5, .s 69 5, .s 69 5, .s 69 5]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(2, -1, 1), (-1, 2, 1), (-2, 1, -1), (1, -2, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, 1, 0, 7, [[.f ⟨23, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 12 0], [.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨23, 9, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 1, 1, 5, [[.f ⟨23, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 3 0], [.s 7 0], [.s 14 0]], [.f ⟨23, 11, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 1, 2, 4, [[.f ⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0]], [.f ⟨0, 16, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 1, 3, 6, [[.s 1 0], [.s 4 0], [.s 7 0], [.s 8 0], [.s 15 0]], [.s 1 2]⟩,
    ⟨1, 1, 4, 7, [[.s 3 0], [.s 5 0], [.s 8 0], [.s 10 0], [.s 17 0]], [.s 3 1]⟩,
    ⟨1, 1, 5, 6, [[.f ⟨15, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 10 0]], [.f ⟨15, 0, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 1, 6, 7, [[.s 0 0], [.s 12 0], [.s 13 0], [.s 18 0], [.s 19 0], [.f ⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 12 4]⟩,
    ⟨1, 1, 7, 6, [[.s 1 0], [.s 3 0], [.s 14 0], [.s 15 0], [.s 18 0], [.s 19 0]], [.s 1 3]⟩,
    ⟨1, 1, 8, 7, [[.s 3 0], [.s 4 0], [.s 15 0], [.s 17 0], [.s 20 0], [.s 21 0]], [.s 3 3]⟩,
    ⟨1, 1, 9, 9, [[.s 16 0], [.s 20 0], [.s 21 0], [.f ⟨4, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨4, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 20 1]⟩,
    ⟨1, 1, 10, 7, [[.f ⟨15, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 5 0], [.s 17 0], [.s 22 0], [.s 23 0]], [.s 5 4]⟩,
    ⟨1, 1, 11, 9, [[.f ⟨15, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.s 22 0], [.s 23 0], [.f ⟨4, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨4, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 22 1]⟩,
    ⟨1, 1, 12, 6, [[.f ⟨23, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 21, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 0 0], [.s 6 0], [.s 18 0]], [.f ⟨23, 21, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 1, 13, 8, [[.s 6 0], [.s 19 0], [.s 24 0], [.f ⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 2]⟩,
    ⟨1, 1, 14, 5, [[.f ⟨23, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 22, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 7 0], [.s 18 0]], [.f ⟨23, 11, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 1, 15, 7, [[.s 3 0], [.s 7 0], [.s 8 0], [.s 19 0], [.s 20 0], [.s 24 0]], [.s 3 4]⟩,
    ⟨1, 1, 16, 9, [[.s 9 0], [.s 20 0], [.s 24 0], [.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 23, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 20 3]⟩,
    ⟨1, 1, 17, 8, [[.s 4 0], [.s 8 0], [.s 10 0], [.s 21 0], [.s 22 0], [.s 25 0]], [.s 4 4]⟩,
    ⟨1, 1, 18, 6, [[.f ⟨23, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 7 0], [.s 12 0], [.s 14 0], [.s 19 0]], [.f ⟨23, 25, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 1, 19, 7, [[.s 6 0], [.s 7 0], [.s 13 0], [.s 15 0], [.s 18 0], [.s 24 0]], [.s 7 5]⟩,
    ⟨1, 1, 20, 8, [[.s 8 0], [.s 9 0], [.s 15 0], [.s 16 0], [.s 21 0], [.s 24 0]], [.s 8 4]⟩,
    ⟨1, 1, 21, 8, [[.s 8 0], [.s 9 0], [.s 17 0], [.s 20 0], [.s 25 0], [.f ⟨4, 12, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 5]⟩,
    ⟨1, 1, 22, 8, [[.s 10 0], [.s 11 0], [.s 17 0], [.s 23 0], [.s 25 0], [.f ⟨4, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 10 4]⟩,
    ⟨1, 1, 23, 8, [[.f ⟨15, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.s 10 0], [.s 11 0], [.s 22 0]], [.f ⟨15, 13, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨1, 1, 24, 8, [[.s 13 0], [.s 15 0], [.s 16 0], [.s 19 0], [.s 20 0], [.f ⟨5, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 15 5]⟩,
    ⟨1, 1, 25, 9, [[.s 17 0], [.s 21 0], [.s 22 0], [.f ⟨4, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨4, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨4, 18, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 17 5]⟩]⟩,
  ⟨1, 2, 1, 0, 0, [(2, -1, 2), (-1, 2, 1), (1, -2, -1)], 2, -1, 2, 3, 0, 0, 0, 0,
   [⟨3, 2, 0, 16, [[.f ⟨22, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨22, 28, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 28, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 31, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 31, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨22, 9, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨22, 9, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨3, 2, 1, 14, [[.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨22, 11, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨3, 2, 2, 14, [[.f ⟨4, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨4, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨4, 9, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨4, 9, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨3, 2, 3, 15, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 1 2, .s 1 2]⟩,
    ⟨3, 2, 4, 16, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 3 1, .s 3 1]⟩,
    ⟨3, 2, 5, 15, [[.f ⟨17, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 6, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨17, 0, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨17, 0, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨3, 2, 6, 16, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨22, 31, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 31, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 12 4, .s 12 4]⟩,
    ⟨3, 2, 7, 15, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 1 3, .s 1 3]⟩,
    ⟨3, 2, 8, 16, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 3 3, .s 3 3]⟩,
    ⟨3, 2, 9, 18, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨4, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨4, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 12, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨22, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 2, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 20 1, .s 20 1]⟩,
    ⟨3, 2, 10, 16, [[.f ⟨17, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 5 4, .s 5 4]⟩,
    ⟨3, 2, 11, 18, [[.f ⟨17, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨4, 1, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 1, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨4, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨4, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 14, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 22 1, .s 22 1]⟩,
    ⟨3, 2, 12, 15, [[.f ⟨22, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 21, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨22, 21, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨22, 21, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨3, 2, 13, 17, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨22, 31, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 31, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 36, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 36, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 49, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨3, 2, 14, 14, [[.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 22, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨22, 11, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨3, 2, 15, 16, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 3 4, .s 3 4]⟩,
    ⟨3, 2, 16, 18, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨22, 37, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 37, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 49, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 2, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 20 3, .s 20 3]⟩,
    ⟨3, 2, 17, 17, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 4 4, .s 4 4]⟩,
    ⟨3, 2, 18, 15, [[.f ⟨22, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.f ⟨22, 25, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨22, 25, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨3, 2, 19, 16, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 7 5, .s 7 5]⟩,
    ⟨3, 2, 20, 17, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 8 4, .s 8 4]⟩,
    ⟨3, 2, 21, 17, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨4, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 12, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 8 5, .s 8 5]⟩,
    ⟨3, 2, 22, 17, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨4, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 14, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 10 4, .s 10 4]⟩,
    ⟨3, 2, 23, 17, [[.f ⟨17, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 24, 1, 0, 1, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨17, 13, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨17, 13, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨3, 2, 24, 17, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨22, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 49, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 15 5, .s 15 5]⟩,
    ⟨3, 2, 25, 18, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨4, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 12, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨4, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 14, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨4, 18, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨4, 18, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 17 5, .s 17 5]⟩]⟩,
  ⟨1, 1, 2, 0, 0, [(-1, 2, 2), (2, -1, 1), (-2, 1, -1)], -1, 2, 2, 3, 0, 0, 0, 0,
   [⟨2, 3, 0, 16, [[.f ⟨24, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨5, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨5, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 5, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨24, 9, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨24, 9, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨2, 3, 1, 14, [[.f ⟨24, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.f ⟨24, 11, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨24, 11, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨2, 3, 2, 13, [[.f ⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨5, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 0, 0, 0, 0, 1, 0, 1, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨5, 9, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨5, 9, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨2, 3, 3, 15, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 1 2, .s 1 2]⟩,
    ⟨2, 3, 4, 15, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 5 3, .s 5 3]⟩,
    ⟨2, 3, 5, 14, [[.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 0, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 6, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 13, 0, 0, 0, 1, 0, 1, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨22, 0, 0, 0, 0, 1, 0, 1, 4⟩]⟩,
    ⟨2, 3, 6, 16, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨5, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 5, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 12 4, .s 12 4]⟩,
    ⟨2, 3, 7, 15, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 1 3, .s 1 3]⟩,
    ⟨2, 3, 8, 16, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 3 3, .s 3 3]⟩,
    ⟨2, 3, 9, 18, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨22, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 26, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 38, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 38, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 2, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨22, 2, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 20 1, .s 20 1]⟩,
    ⟨2, 3, 10, 15, [[.f ⟨22, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 13, 0, 0, 0, 1, 0, 1, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.f ⟨22, 13, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨22, 13, 0, 0, 0, 1, 0, 1, 4⟩]⟩,
    ⟨2, 3, 11, 16, [[.f ⟨22, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 16, 0, 0, 0, 1, 0, 1, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨22, 27, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 27, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 28, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 28, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 40, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 40, 0, 0, 0, 1, 0, 1, 0⟩]], [.f ⟨22, 16, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨22, 16, 0, 0, 0, 1, 0, 1, 3⟩]⟩,
    ⟨2, 3, 12, 15, [[.f ⟨24, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 21, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨24, 21, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨24, 21, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨2, 3, 13, 17, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨5, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨5, 10, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 10, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨5, 23, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 23, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨2, 3, 14, 14, [[.f ⟨24, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 11, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 22, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨24, 11, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨24, 11, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨2, 3, 15, 16, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 3 4, .s 3 4]⟩,
    ⟨2, 3, 16, 18, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨5, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨5, 23, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 23, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨22, 2, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨22, 2, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 20 3, .s 20 3]⟩,
    ⟨2, 3, 17, 16, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 4 4, .s 4 4]⟩,
    ⟨2, 3, 18, 15, [[.f ⟨24, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 25, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.f ⟨24, 25, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨24, 25, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨2, 3, 19, 16, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 7 5, .s 7 5]⟩,
    ⟨2, 3, 20, 17, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 8 4, .s 8 4]⟩,
    ⟨2, 3, 21, 17, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨22, 38, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 38, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 8 5, .s 8 5]⟩,
    ⟨2, 3, 22, 16, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨22, 40, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 40, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 10 4, .s 10 4]⟩,
    ⟨2, 3, 23, 15, [[.f ⟨22, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 13, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 16, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 24, 0, 0, 0, 1, 0, 1, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨22, 13, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨22, 13, 0, 0, 0, 1, 0, 1, 5⟩]⟩,
    ⟨2, 3, 24, 17, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨5, 23, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 23, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 15 5, .s 15 5]⟩,
    ⟨2, 3, 25, 17, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨22, 38, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 38, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 40, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 40, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨22, 44, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 44, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 17 5, .s 17 5]⟩]⟩,
  ⟨2, 2, 1, 1, 2, [(2, -1, 2), (-1, 2, 2)], 2, -1, 2, 3, -1, 2, 2, 3,
   [⟨2, 2, 0, 13, [[.f ⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 35 0, .f ⟨5, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 35 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.f ⟨21, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 54 0, .f ⟨21, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 54 0], [.f ⟨21, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 57 0, .f ⟨21, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 57 0]], [.f ⟨5, 9, 0, 0, 0, 0, 0, 0, 3⟩, .s 35 3, .f ⟨5, 9, 0, 1, 1, 0, 0, 0, 3⟩, .s 35 3]⟩,
    ⟨2, 2, 1, 11, [[.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 37 0, .f ⟨5, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 37 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 3⟩, .s 37 3, .f ⟨5, 11, 0, 1, 1, 0, 0, 0, 3⟩, .s 37 3]⟩,
    ⟨2, 2, 2, 10, [[.f ⟨19, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 9, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 9, 0, 1, 0, 0, 0, 0, 0⟩, .s 61 0], [.f ⟨19, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 16, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 16, 0, 1, 0, 0, 0, 0, 0⟩, .s 68 0], [.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 37 0, .f ⟨5, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 37 0], [.f ⟨4, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 26 0, .s 26 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.f ⟨19, 9, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨20, 9, 1, 0, 0, 0, 0, 0, 5⟩, .f ⟨21, 9, 0, 1, 0, 0, 0, 0, 5⟩, .s 61 5]⟩,
    ⟨2, 2, 3, 12, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0]], [.s 1 2, .s 1 2, .s 1 2, .s 1 2]⟩,
    ⟨2, 2, 4, 12, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0]], [.s 5 3, .s 5 3, .s 5 3, .s 5 3]⟩,
    ⟨2, 2, 5, 11, [[.f ⟨4, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 26 0, .s 26 0], [.f ⟨4, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 6, 1, 0, 1, 0, 0, 0, 0⟩, .s 32 0, .s 32 0], [.f ⟨4, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 39 0, .s 39 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.f ⟨4, 0, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨4, 0, 1, 0, 1, 0, 0, 0, 4⟩, .s 26 4, .s 26 4]⟩,
    ⟨2, 2, 6, 13, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.f ⟨21, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 57 0, .f ⟨21, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 57 0]], [.s 12 4, .s 12 4, .s 12 4, .s 12 4]⟩,
    ⟨2, 2, 7, 12, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 1 3, .s 1 3, .s 1 3, .s 1 3]⟩,
    ⟨2, 2, 8, 13, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.s 3 3, .s 3 3, .s 3 3, .s 3 3]⟩,
    ⟨2, 2, 9, 15, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.f ⟨20, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 52 0, .s 52 0], [.f ⟨20, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 64 0, .s 64 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 20 1, .s 20 1, .s 20 1, .s 20 1]⟩,
    ⟨2, 2, 10, 12, [[.f ⟨4, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 39 0, .s 39 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.f ⟨4, 13, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨4, 13, 1, 0, 1, 0, 0, 0, 4⟩, .s 39 4, .s 39 4]⟩,
    ⟨2, 2, 11, 13, [[.f ⟨4, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 42 0, .s 42 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.f ⟨20, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 1, 1, 0, 1, 0, 0, 0, 0⟩, .s 53 0, .s 53 0], [.f ⟨20, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 54 0, .s 54 0], [.f ⟨20, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 66 0, .s 66 0]], [.s 23 4, .s 23 4, .s 42 3, .s 42 3]⟩,
    ⟨2, 2, 12, 12, [[.f ⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 35 0, .f ⟨5, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 35 0], [.f ⟨5, 21, 0, 0, 0, 0, 0, 0, 0⟩, .s 47 0, .f ⟨5, 21, 0, 1, 1, 0, 0, 0, 0⟩, .s 47 0], [.f ⟨5, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 51 0, .f ⟨5, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 51 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨5, 21, 0, 0, 0, 0, 0, 0, 5⟩, .s 47 5, .f ⟨5, 21, 0, 1, 1, 0, 0, 0, 5⟩, .s 47 5]⟩,
    ⟨2, 2, 13, 14, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.f ⟨21, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 57 0, .f ⟨21, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 57 0], [.f ⟨21, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 62 0, .f ⟨21, 10, 0, 1, 1, 0, 0, 0, 0⟩, .s 62 0], [.f ⟨21, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 75 0, .f ⟨21, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 75 0]], [.s 6 2, .s 6 2, .s 6 2, .s 6 2]⟩,
    ⟨2, 2, 14, 11, [[.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 37 0, .f ⟨5, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 37 0], [.f ⟨5, 22, 0, 0, 0, 0, 0, 0, 0⟩, .s 48 0, .f ⟨5, 22, 0, 1, 1, 0, 0, 0, 0⟩, .s 48 0], [.f ⟨5, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 51 0, .f ⟨5, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 51 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 5⟩, .s 37 5, .f ⟨5, 11, 0, 1, 1, 0, 0, 0, 5⟩, .s 37 5]⟩,
    ⟨2, 2, 15, 13, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 3 4, .s 3 4, .s 3 4, .s 3 4]⟩,
    ⟨2, 2, 16, 15, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.f ⟨21, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 63 0, .f ⟨21, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 63 0], [.f ⟨21, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 75 0, .f ⟨21, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 75 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 20 3, .s 20 3, .s 20 3, .s 20 3]⟩,
    ⟨2, 2, 17, 13, [[.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 4 4, .s 4 4, .s 4 4, .s 4 4]⟩,
    ⟨2, 2, 18, 12, [[.f ⟨5, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 51 0, .f ⟨5, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 51 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.f ⟨5, 25, 0, 0, 0, 0, 0, 0, 5⟩, .s 51 5, .f ⟨5, 25, 0, 1, 1, 0, 0, 0, 5⟩, .s 51 5]⟩,
    ⟨2, 2, 19, 13, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 7 5, .s 7 5, .s 7 5, .s 7 5]⟩,
    ⟨2, 2, 20, 14, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 8 4, .s 8 4, .s 8 4, .s 8 4]⟩,
    ⟨2, 2, 21, 14, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.f ⟨20, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 64 0, .s 64 0]], [.s 8 5, .s 8 5, .s 8 5, .s 8 5]⟩,
    ⟨2, 2, 22, 13, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.f ⟨20, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 66 0, .s 66 0]], [.s 10 4, .s 10 4, .s 10 4, .s 10 4]⟩,
    ⟨2, 2, 23, 12, [[.f ⟨4, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 39 0, .s 39 0], [.f ⟨4, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 42 0, .s 42 0], [.f ⟨4, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 24, 1, 0, 1, 0, 0, 0, 0⟩, .s 50 0, .s 50 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.f ⟨4, 13, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨4, 13, 1, 0, 1, 0, 0, 0, 5⟩, .s 39 5, .s 39 5]⟩,
    ⟨2, 2, 24, 14, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.f ⟨21, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 75 0, .f ⟨21, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 75 0]], [.s 15 5, .s 15 5, .s 15 5, .s 15 5]⟩,
    ⟨2, 2, 25, 14, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.f ⟨20, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 64 0, .s 64 0], [.f ⟨20, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 66 0, .s 66 0], [.f ⟨20, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 18, 1, 0, 1, 0, 0, 0, 0⟩, .s 70 0, .s 70 0]], [.s 17 5, .s 17 5, .s 17 5, .s 17 5]⟩,
    ⟨3, 3, 0, 19, [[.f ⟨21, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 61 0, .f ⟨21, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 61 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0]], [.f ⟨21, 9, 0, 0, 0, 0, 0, 0, 3⟩, .s 61 3, .f ⟨21, 9, 0, 1, 1, 0, 0, 0, 3⟩, .s 61 3]⟩,
    ⟨3, 3, 1, 17, [[.f ⟨21, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 63 0, .f ⟨21, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 63 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.f ⟨21, 11, 0, 0, 0, 0, 0, 0, 3⟩, .s 63 3, .f ⟨21, 11, 0, 1, 1, 0, 0, 0, 3⟩, .s 63 3]⟩,
    ⟨3, 3, 2, 16, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.f ⟨21, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 63 0, .f ⟨21, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 63 0], [.f ⟨20, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 52 0, .s 52 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0]], [.s 9 5, .s 9 5, .s 9 5, .s 9 5]⟩,
    ⟨3, 3, 3, 18, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0]], [.s 27 2, .s 27 2, .s 27 2, .s 27 2]⟩,
    ⟨3, 3, 4, 18, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 31 3, .s 31 3, .s 31 3, .s 31 3]⟩,
    ⟨3, 3, 5, 17, [[.f ⟨20, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 52 0, .s 52 0], [.f ⟨20, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 6, 1, 0, 1, 0, 0, 0, 0⟩, .s 58 0, .s 58 0], [.f ⟨20, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 65 0, .s 65 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.f ⟨20, 0, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨20, 0, 1, 0, 1, 0, 0, 0, 4⟩, .s 52 4, .s 52 4]⟩,
    ⟨3, 3, 6, 19, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0]], [.s 38 4, .s 38 4, .s 38 4, .s 38 4]⟩,
    ⟨3, 3, 7, 18, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 27 3, .s 27 3, .s 27 3, .s 27 3]⟩,
    ⟨3, 3, 8, 19, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 29 3, .s 29 3, .s 29 3, .s 29 3]⟩,
    ⟨3, 3, 9, 21, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 46 1, .s 46 1, .s 46 1, .s 46 1]⟩,
    ⟨3, 3, 10, 18, [[.f ⟨20, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 65 0, .s 65 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.f ⟨20, 13, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨20, 13, 1, 0, 1, 0, 0, 0, 4⟩, .s 65 4, .s 65 4]⟩,
    ⟨3, 3, 11, 19, [[.f ⟨20, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 68 0, .s 68 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.f ⟨20, 16, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨20, 16, 1, 0, 1, 0, 0, 0, 3⟩, .s 68 3, .s 68 3]⟩,
    ⟨3, 3, 12, 18, [[.f ⟨21, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 61 0, .f ⟨21, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 61 0], [.f ⟨21, 21, 0, 0, 0, 0, 0, 0, 0⟩, .s 73 0, .f ⟨21, 21, 0, 1, 1, 0, 0, 0, 0⟩, .s 73 0], [.f ⟨21, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 77 0, .f ⟨21, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 77 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.f ⟨21, 21, 0, 0, 0, 0, 0, 0, 5⟩, .s 73 5, .f ⟨21, 21, 0, 1, 1, 0, 0, 0, 5⟩, .s 73 5]⟩,
    ⟨3, 3, 13, 20, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 32 2, .s 32 2, .s 32 2, .s 32 2]⟩,
    ⟨3, 3, 14, 17, [[.f ⟨21, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 63 0, .f ⟨21, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 63 0], [.f ⟨21, 22, 0, 0, 0, 0, 0, 0, 0⟩, .s 74 0, .f ⟨21, 22, 0, 1, 1, 0, 0, 0, 0⟩, .s 74 0], [.f ⟨21, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 77 0, .f ⟨21, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 77 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.f ⟨21, 11, 0, 0, 0, 0, 0, 0, 5⟩, .s 63 5, .f ⟨21, 11, 0, 1, 1, 0, 0, 0, 5⟩, .s 63 5]⟩,
    ⟨3, 3, 15, 19, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 29 4, .s 29 4, .s 29 4, .s 29 4]⟩,
    ⟨3, 3, 16, 21, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 46 3, .s 46 3, .s 46 3, .s 46 3]⟩,
    ⟨3, 3, 17, 19, [[.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0]], [.s 30 4, .s 30 4, .s 30 4, .s 30 4]⟩,
    ⟨3, 3, 18, 18, [[.f ⟨21, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 77 0, .f ⟨21, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 77 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.f ⟨21, 25, 0, 0, 0, 0, 0, 0, 5⟩, .s 77 5, .f ⟨21, 25, 0, 1, 1, 0, 0, 0, 5⟩, .s 77 5]⟩,
    ⟨3, 3, 19, 19, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 33 5, .s 33 5, .s 33 5, .s 33 5]⟩,
    ⟨3, 3, 20, 20, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 34 4, .s 34 4, .s 34 4, .s 34 4]⟩,
    ⟨3, 3, 21, 20, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0]], [.s 34 5, .s 34 5, .s 34 5, .s 34 5]⟩,
    ⟨3, 3, 22, 19, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 36 4, .s 36 4, .s 36 4, .s 36 4]⟩,
    ⟨3, 3, 23, 18, [[.f ⟨20, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 65 0, .s 65 0], [.f ⟨20, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 68 0, .s 68 0], [.f ⟨20, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 24, 1, 0, 1, 0, 0, 0, 0⟩, .s 76 0, .s 76 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.f ⟨20, 13, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨20, 13, 1, 0, 1, 0, 0, 0, 5⟩, .s 65 5, .s 65 5]⟩,
    ⟨3, 3, 24, 20, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 41 5, .s 41 5, .s 41 5, .s 41 5]⟩,
    ⟨3, 3, 25, 20, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 43 5, .s 43 5, .s 43 5, .s 43 5]⟩,
    ⟨4, 4, 0, 25, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 9 3, .s 9 3, .s 9 3, .s 9 3]⟩,
    ⟨4, 4, 1, 23, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 11 3, .s 11 3, .s 11 3, .s 11 3]⟩,
    ⟨4, 4, 2, 22, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0]], [.s 35 5, .s 35 5, .s 35 5, .s 35 5]⟩,
    ⟨4, 4, 3, 24, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 53 2, .s 53 2, .s 53 2, .s 53 2]⟩,
    ⟨4, 4, 4, 24, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 57 3, .s 57 3, .s 57 3, .s 57 3]⟩,
    ⟨4, 4, 5, 23, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.s 0 4, .s 0 4, .s 0 4, .s 0 4]⟩,
    ⟨4, 4, 6, 25, [[.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 64 4, .s 64 4, .s 64 4, .s 64 4]⟩,
    ⟨4, 4, 7, 24, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 53 3, .s 53 3, .s 53 3, .s 53 3]⟩,
    ⟨4, 4, 8, 25, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 55 3, .s 55 3, .s 55 3, .s 55 3]⟩,
    ⟨4, 4, 9, 27, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 72 1, .s 72 1, .s 72 1, .s 72 1]⟩,
    ⟨4, 4, 10, 24, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 13 4, .s 13 4, .s 13 4, .s 13 4]⟩,
    ⟨4, 4, 11, 25, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 16 3, .s 16 3, .s 16 3, .s 16 3]⟩,
    ⟨4, 4, 12, 24, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 21 5, .s 21 5, .s 21 5, .s 21 5]⟩,
    ⟨4, 4, 13, 26, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 58 2, .s 58 2, .s 58 2, .s 58 2]⟩,
    ⟨4, 4, 14, 23, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 11 5, .s 11 5, .s 11 5, .s 11 5]⟩,
    ⟨4, 4, 15, 25, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 55 4, .s 55 4, .s 55 4, .s 55 4]⟩,
    ⟨4, 4, 16, 27, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 72 3, .s 72 3, .s 72 3, .s 72 3]⟩,
    ⟨4, 4, 17, 25, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0]], [.s 56 4, .s 56 4, .s 56 4, .s 56 4]⟩,
    ⟨4, 4, 18, 24, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 25 5, .s 25 5, .s 25 5, .s 25 5]⟩,
    ⟨4, 4, 19, 25, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 59 5, .s 59 5, .s 59 5, .s 59 5]⟩,
    ⟨4, 4, 20, 26, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 60 4, .s 60 4, .s 60 4, .s 60 4]⟩,
    ⟨4, 4, 21, 26, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.s 60 5, .s 60 5, .s 60 5, .s 60 5]⟩,
    ⟨4, 4, 22, 25, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 62 4, .s 62 4, .s 62 4, .s 62 4]⟩,
    ⟨4, 4, 23, 24, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.s 13 5, .s 13 5, .s 13 5, .s 13 5]⟩,
    ⟨4, 4, 24, 26, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 67 5, .s 67 5, .s 67 5, .s 67 5]⟩,
    ⟨4, 4, 25, 26, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 69 5, .s 69 5, .s 69 5, .s 69 5]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 1, 1), (-2, 1, 1), (-1, -1, -1), (2, -1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 1, 0, 8, [[.f ⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 12 0], [.f ⟨26, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨26, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 0]⟩,
    ⟨0, 1, 1, 4, [[.f ⟨6, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 3 0], [.s 7 0], [.s 14 0]], [.s 2 4]⟩,
    ⟨0, 1, 2, 3, [[.f ⟨27, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0]], [.f ⟨27, 9, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨0, 1, 3, 4, [[.s 1 0], [.s 4 0], [.s 7 0], [.s 8 0], [.s 15 0]], [.s 4 0]⟩,
    ⟨0, 1, 4, 3, [[.s 3 0], [.s 5 0], [.s 8 0], [.s 10 0], [.s 17 0]], [.s 5 3]⟩,
    ⟨0, 1, 5, 2, [[.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 10 0]], [.f ⟨0, 6, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨0, 1, 6, 7, [[.s 0 0], [.s 12 0], [.s 13 0], [.s 18 0], [.s 19 0], [.f ⟨26, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 18 1]⟩,
    ⟨0, 1, 7, 5, [[.s 1 0], [.s 3 0], [.s 14 0], [.s 15 0], [.s 18 0], [.s 19 0]], [.s 1 3]⟩,
    ⟨0, 1, 8, 4, [[.s 3 0], [.s 4 0], [.s 15 0], [.s 17 0], [.s 20 0], [.s 21 0]], [.s 4 2]⟩,
    ⟨0, 1, 9, 6, [[.s 16 0], [.s 20 0], [.s 21 0], [.f ⟨19, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 20 1]⟩,
    ⟨0, 1, 10, 3, [[.f ⟨0, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 5 0], [.s 17 0], [.s 22 0], [.s 23 0]], [.f ⟨0, 13, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨0, 1, 11, 4, [[.f ⟨0, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.s 22 0], [.s 23 0], [.f ⟨19, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 16, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 1, 12, 7, [[.f ⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 21, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 0 0], [.s 6 0], [.s 18 0]], [.f ⟨6, 25, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 1, 13, 7, [[.s 6 0], [.s 19 0], [.s 24 0], [.f ⟨26, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨26, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨26, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 19 2]⟩,
    ⟨0, 1, 14, 5, [[.f ⟨6, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 22, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 7 0], [.s 18 0]], [.f ⟨6, 11, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨0, 1, 15, 5, [[.s 3 0], [.s 7 0], [.s 8 0], [.s 19 0], [.s 20 0], [.s 24 0]], [.s 3 4]⟩,
    ⟨0, 1, 16, 6, [[.s 9 0], [.s 20 0], [.s 24 0], [.f ⟨26, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨26, 23, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 20 3]⟩,
    ⟨0, 1, 17, 4, [[.s 4 0], [.s 8 0], [.s 10 0], [.s 21 0], [.s 22 0], [.s 25 0]], [.s 4 4]⟩,
    ⟨0, 1, 18, 6, [[.f ⟨6, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 7 0], [.s 12 0], [.s 14 0], [.s 19 0]], [.s 7 4]⟩,
    ⟨0, 1, 19, 6, [[.s 6 0], [.s 7 0], [.s 13 0], [.s 15 0], [.s 18 0], [.s 24 0]], [.s 7 5]⟩,
    ⟨0, 1, 20, 5, [[.s 8 0], [.s 9 0], [.s 15 0], [.s 16 0], [.s 21 0], [.s 24 0]], [.s 8 4]⟩,
    ⟨0, 1, 21, 5, [[.s 8 0], [.s 9 0], [.s 17 0], [.s 20 0], [.s 25 0], [.f ⟨19, 12, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 5]⟩,
    ⟨0, 1, 22, 4, [[.s 10 0], [.s 11 0], [.s 17 0], [.s 23 0], [.s 25 0], [.f ⟨19, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 10 4]⟩,
    ⟨0, 1, 23, 3, [[.f ⟨0, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.s 10 0], [.s 11 0], [.s 22 0]], [.f ⟨0, 13, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨0, 1, 24, 6, [[.s 13 0], [.s 15 0], [.s 16 0], [.s 19 0], [.s 20 0], [.f ⟨26, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 15 5]⟩,
    ⟨0, 1, 25, 5, [[.s 17 0], [.s 21 0], [.s 22 0], [.f ⟨19, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 18, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 17 5]⟩]⟩,
  ⟨1, 1, 2, 0, 0, [(1, 1, 2), (-2, 1, 1), (2, -1, -1)], 1, 1, 2, 3, 0, 0, 0, 0,
   [⟨1, 3, 0, 17, [[.f ⟨26, 35, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 35, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨26, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨26, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨26, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨26, 5, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 6 0, .s 6 0]⟩,
    ⟨1, 3, 1, 13, [[.f ⟨26, 37, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 37, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 2 4, .s 2 4]⟩,
    ⟨1, 3, 2, 12, [[.f ⟨26, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 37, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 37, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨26, 9, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨26, 9, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨1, 3, 3, 13, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 4 0, .s 4 0]⟩,
    ⟨1, 3, 4, 12, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 5 3, .s 5 3]⟩,
    ⟨1, 3, 5, 11, [[.f ⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨5, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 6, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨5, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨5, 6, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨5, 6, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨1, 3, 6, 16, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨26, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨26, 5, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 18 1, .s 18 1]⟩,
    ⟨1, 3, 7, 14, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 1 3, .s 1 3]⟩,
    ⟨1, 3, 8, 13, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 4 2, .s 4 2]⟩,
    ⟨1, 3, 9, 15, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨21, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨21, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨5, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 2, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 20 1, .s 20 1]⟩,
    ⟨1, 3, 10, 12, [[.f ⟨5, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.f ⟨5, 13, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨5, 13, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨1, 3, 11, 13, [[.f ⟨5, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨21, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 1, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨21, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨21, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨5, 16, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨5, 16, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, 3, 12, 16, [[.f ⟨26, 35, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 35, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 47, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 47, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 51, 1, 0, 1, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨26, 51, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨26, 51, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, 3, 13, 16, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨26, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨26, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨26, 10, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨26, 10, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨26, 23, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨26, 23, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 19 2, .s 19 2]⟩,
    ⟨1, 3, 14, 14, [[.f ⟨26, 37, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 37, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 48, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 48, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 51, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨26, 37, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨26, 37, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨1, 3, 15, 14, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 3 4, .s 3 4]⟩,
    ⟨1, 3, 16, 15, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨26, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨26, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨26, 23, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨26, 23, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨5, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨5, 2, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 20 3, .s 20 3]⟩,
    ⟨1, 3, 17, 13, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 4 4, .s 4 4]⟩,
    ⟨1, 3, 18, 15, [[.f ⟨26, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 51, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 7 4, .s 7 4]⟩,
    ⟨1, 3, 19, 15, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 7 5, .s 7 5]⟩,
    ⟨1, 3, 20, 14, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 8 4, .s 8 4]⟩,
    ⟨1, 3, 21, 14, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨21, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 12, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 8 5, .s 8 5]⟩,
    ⟨1, 3, 22, 13, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨21, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 10 4, .s 10 4]⟩,
    ⟨1, 3, 23, 12, [[.f ⟨5, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨5, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨5, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 24, 1, 0, 1, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨5, 13, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨5, 13, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨1, 3, 24, 15, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨26, 23, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨26, 23, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 15 5, .s 15 5]⟩,
    ⟨1, 3, 25, 14, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨21, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨21, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 14, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨21, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨21, 18, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 17 5, .s 17 5]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-2, 1, 2), (1, 1, 1), (-1, -1, -1)], -2, 1, 2, 3, 0, 0, 0, 0,
   [⟨-1, 2, 0, 17, [[.f ⟨6, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 9, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨26, 2, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨26, 2, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨26, 5, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨26, 5, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 6 0, .s 6 0]⟩,
    ⟨-1, 2, 1, 13, [[.f ⟨6, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 2 4, .s 2 4]⟩,
    ⟨-1, 2, 2, 12, [[.f ⟨28, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 9, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨28, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨28, 9, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨28, 9, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨-1, 2, 3, 13, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 4 0, .s 4 0]⟩,
    ⟨-1, 2, 4, 12, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 5 3, .s 5 3]⟩,
    ⟨-1, 2, 5, 11, [[.f ⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 6, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨6, 6, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨6, 6, 1, 0, 1, 0, 0, 0, 5⟩]⟩,
    ⟨-1, 2, 6, 16, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨26, 5, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨26, 5, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 18 1, .s 18 1]⟩,
    ⟨-1, 2, 7, 14, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 1 3, .s 1 3]⟩,
    ⟨-1, 2, 8, 13, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 4 2, .s 4 2]⟩,
    ⟨-1, 2, 9, 14, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨26, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 0, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨26, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 12, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨26, 28, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 28, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 21 1, .s 21 1]⟩,
    ⟨-1, 2, 10, 11, [[.f ⟨6, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.f ⟨6, 13, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨6, 13, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨-1, 2, 11, 10, [[.f ⟨6, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨26, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 1, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨26, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 2, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨26, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 14, 0, 0, 0, 1, 0, 1, 0⟩]], [.f ⟨6, 16, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨6, 16, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 2, 12, 16, [[.f ⟨6, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 9, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨6, 21, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 21, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨6, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.f ⟨6, 25, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨6, 25, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 2, 13, 16, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨26, 5, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨26, 5, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨26, 10, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨26, 10, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨26, 23, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨26, 23, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 19 2, .s 19 2]⟩,
    ⟨-1, 2, 14, 14, [[.f ⟨6, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨6, 22, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 22, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨6, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.f ⟨6, 11, 0, 0, 1, 0, 0, 0, 5⟩, .f ⟨6, 11, 1, 0, 2, 0, 0, 0, 5⟩]⟩,
    ⟨-1, 2, 15, 14, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 3 4, .s 3 4]⟩,
    ⟨-1, 2, 16, 15, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨26, 11, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨26, 11, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨26, 23, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨26, 23, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨26, 28, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 28, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 9 0, .s 9 0]⟩,
    ⟨-1, 2, 17, 12, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 10 3, .s 10 3]⟩,
    ⟨-1, 2, 18, 15, [[.f ⟨6, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 7 4, .s 7 4]⟩,
    ⟨-1, 2, 19, 15, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 7 5, .s 7 5]⟩,
    ⟨-1, 2, 20, 14, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 8 4, .s 8 4]⟩,
    ⟨-1, 2, 21, 13, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨26, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 12, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 17 3, .s 17 3]⟩,
    ⟨-1, 2, 22, 11, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨26, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 14, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 11 1, .s 11 1]⟩,
    ⟨-1, 2, 23, 10, [[.f ⟨6, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 24, 1, 0, 1, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨6, 16, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨6, 16, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨-1, 2, 24, 15, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨26, 23, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨26, 23, 0, 0, 0, 1, 0, 2, 0⟩]], [.s 15 5, .s 15 5]⟩,
    ⟨-1, 2, 25, 12, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨26, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 12, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨26, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 14, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨26, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 18, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 22 4, .s 22 4]⟩]⟩,
  ⟨2, 1, 2, -1, 1, [(1, 1, 2), (-2, 1, 2)], 1, 1, 2, 3, -2, 1, 2, 3,
   [⟨0, 2, 0, 14, [[.f ⟨25, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 61 0, .f ⟨25, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 61 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]⟩,
    ⟨0, 2, 1, 10, [[.f ⟨25, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 63 0, .f ⟨25, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 63 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 2 4, .s 2 4, .s 2 4, .s 2 4]⟩,
    ⟨0, 2, 2, 9, [[.f ⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 35 0, .f ⟨6, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 35 0], [.f ⟨6, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 42 0, .f ⟨6, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 42 0], [.f ⟨25, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 63 0, .f ⟨25, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 63 0], [.f ⟨23, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 0, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 0, 0, 1, 0, 0, 0, 0, 0⟩, .s 52 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.f ⟨6, 9, 0, 0, 0, 0, 0, 0, 5⟩, .s 35 5, .f ⟨6, 9, 0, 1, 1, 0, 0, 0, 5⟩, .s 35 5]⟩,
    ⟨0, 2, 3, 10, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0]], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]⟩,
    ⟨0, 2, 4, 9, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0]], [.s 5 3, .s 5 3, .s 5 3, .s 5 3]⟩,
    ⟨0, 2, 5, 8, [[.f ⟨23, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 0, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 0, 0, 1, 0, 0, 0, 0, 0⟩, .s 52 0], [.f ⟨23, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 6, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 6, 0, 1, 0, 0, 0, 0, 0⟩, .s 58 0], [.f ⟨23, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 13, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 13, 0, 1, 0, 0, 0, 0, 0⟩, .s 65 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.f ⟨23, 6, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨24, 6, 1, 0, 0, 0, 0, 0, 5⟩, .f ⟨25, 6, 0, 1, 0, 0, 0, 0, 5⟩, .s 58 5]⟩,
    ⟨0, 2, 6, 13, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 18 1, .s 18 1, .s 18 1, .s 18 1]⟩,
    ⟨0, 2, 7, 11, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 1 3, .s 1 3, .s 1 3, .s 1 3]⟩,
    ⟨0, 2, 8, 10, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.s 4 2, .s 4 2, .s 4 2, .s 4 2]⟩,
    ⟨0, 2, 9, 11, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.f ⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 26 0, .s 26 0], [.f ⟨5, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 38 0, .s 38 0], [.f ⟨24, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 54 0, .s 54 0]], [.s 21 1, .s 21 1, .s 21 1, .s 21 1]⟩,
    ⟨0, 2, 10, 8, [[.f ⟨23, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 13, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 13, 0, 1, 0, 0, 0, 0, 0⟩, .s 65 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.f ⟨23, 13, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨24, 13, 1, 0, 0, 0, 0, 0, 4⟩, .f ⟨25, 13, 0, 1, 0, 0, 0, 0, 4⟩, .s 65 4]⟩,
    ⟨0, 2, 11, 7, [[.f ⟨23, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 16, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 16, 0, 1, 0, 0, 0, 0, 0⟩, .s 68 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.f ⟨5, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 1, 1, 0, 1, 0, 0, 0, 0⟩, .s 27 0, .s 27 0], [.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 28 0, .s 28 0], [.f ⟨5, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 40 0, .s 40 0]], [.f ⟨23, 16, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨24, 16, 1, 0, 0, 0, 0, 0, 3⟩, .f ⟨25, 16, 0, 1, 0, 0, 0, 0, 3⟩, .s 68 3]⟩,
    ⟨0, 2, 12, 13, [[.f ⟨25, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 61 0, .f ⟨25, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 61 0], [.f ⟨25, 21, 0, 0, 0, 0, 0, 0, 0⟩, .s 73 0, .f ⟨25, 21, 0, 1, 1, 0, 0, 0, 0⟩, .s 73 0], [.f ⟨25, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 77 0, .f ⟨25, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 77 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨25, 25, 0, 0, 0, 0, 0, 0, 3⟩, .s 77 3, .f ⟨25, 25, 0, 1, 1, 0, 0, 0, 3⟩, .s 77 3]⟩,
    ⟨0, 2, 13, 13, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 19 2, .s 19 2, .s 19 2, .s 19 2]⟩,
    ⟨0, 2, 14, 11, [[.f ⟨25, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 63 0, .f ⟨25, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 63 0], [.f ⟨25, 22, 0, 0, 0, 0, 0, 0, 0⟩, .s 74 0, .f ⟨25, 22, 0, 1, 1, 0, 0, 0, 0⟩, .s 74 0], [.f ⟨25, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 77 0, .f ⟨25, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 77 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨25, 11, 0, 0, 0, 0, 0, 0, 5⟩, .s 63 5, .f ⟨25, 11, 0, 1, 1, 0, 0, 0, 5⟩, .s 63 5]⟩,
    ⟨0, 2, 15, 11, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 3 4, .s 3 4, .s 3 4, .s 3 4]⟩,
    ⟨0, 2, 16, 12, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.f ⟨24, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 54 0, .s 54 0]], [.s 9 0, .s 9 0, .s 9 0, .s 9 0]⟩,
    ⟨0, 2, 17, 9, [[.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 10 3, .s 10 3, .s 10 3, .s 10 3]⟩,
    ⟨0, 2, 18, 12, [[.f ⟨25, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 77 0, .f ⟨25, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 77 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 7 4, .s 7 4, .s 7 4, .s 7 4]⟩,
    ⟨0, 2, 19, 12, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 7 5, .s 7 5, .s 7 5, .s 7 5]⟩,
    ⟨0, 2, 20, 11, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 8 4, .s 8 4, .s 8 4, .s 8 4]⟩,
    ⟨0, 2, 21, 10, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.f ⟨5, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 38 0, .s 38 0]], [.s 17 3, .s 17 3, .s 17 3, .s 17 3]⟩,
    ⟨0, 2, 22, 8, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.f ⟨5, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 40 0, .s 40 0]], [.s 11 1, .s 11 1, .s 11 1, .s 11 1]⟩,
    ⟨0, 2, 23, 7, [[.f ⟨23, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 13, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 13, 0, 1, 0, 0, 0, 0, 0⟩, .s 65 0], [.f ⟨23, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 16, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 16, 0, 1, 0, 0, 0, 0, 0⟩, .s 68 0], [.f ⟨23, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 24, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 24, 0, 1, 0, 0, 0, 0, 0⟩, .s 76 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.f ⟨23, 16, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨24, 16, 1, 0, 0, 0, 0, 0, 4⟩, .f ⟨25, 16, 0, 1, 0, 0, 0, 0, 4⟩, .s 68 4]⟩,
    ⟨0, 2, 24, 12, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 15 5, .s 15 5, .s 15 5, .s 15 5]⟩,
    ⟨0, 2, 25, 9, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.f ⟨5, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 38 0, .s 38 0], [.f ⟨5, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 40 0, .s 40 0], [.f ⟨5, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨5, 18, 1, 0, 1, 0, 0, 0, 0⟩, .s 44 0, .s 44 0]], [.s 22 4, .s 22 4, .s 22 4, .s 22 4]⟩,
    ⟨0, 3, 0, 20, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 32 0, .s 32 0, .s 32 0, .s 32 0]⟩,
    ⟨0, 3, 1, 16, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 28 4, .s 28 4, .s 28 4, .s 28 4]⟩,
    ⟨0, 3, 2, 15, [[.f ⟨25, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 61 0, .f ⟨25, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 61 0], [.f ⟨25, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 68 0, .f ⟨25, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 68 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0]], [.f ⟨25, 9, 0, 0, 0, 0, 0, 0, 5⟩, .s 61 5, .f ⟨25, 9, 0, 1, 1, 0, 0, 0, 5⟩, .s 61 5]⟩,
    ⟨0, 3, 3, 16, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0]], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]⟩,
    ⟨0, 3, 4, 15, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 31 3, .s 31 3, .s 31 3, .s 31 3]⟩,
    ⟨0, 3, 5, 14, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.s 6 5, .s 6 5, .s 6 5, .s 6 5]⟩,
    ⟨0, 3, 6, 19, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 44 1, .s 44 1, .s 44 1, .s 44 1]⟩,
    ⟨0, 3, 7, 17, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 27 3, .s 27 3, .s 27 3, .s 27 3]⟩,
    ⟨0, 3, 8, 16, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 30 2, .s 30 2, .s 30 2, .s 30 2]⟩,
    ⟨0, 3, 9, 17, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.f ⟨24, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 52 0, .s 52 0], [.f ⟨24, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 64 0, .s 64 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 47 1, .s 47 1, .s 47 1, .s 47 1]⟩,
    ⟨0, 3, 10, 14, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 13 4, .s 13 4, .s 13 4, .s 13 4]⟩,
    ⟨0, 3, 11, 13, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.f ⟨24, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 1, 1, 0, 1, 0, 0, 0, 0⟩, .s 53 0, .s 53 0], [.f ⟨24, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 54 0, .s 54 0], [.f ⟨24, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 66 0, .s 66 0]], [.s 16 3, .s 16 3, .s 16 3, .s 16 3]⟩,
    ⟨0, 3, 12, 19, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 25 3, .s 25 3, .s 25 3, .s 25 3]⟩,
    ⟨0, 3, 13, 19, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 45 2, .s 45 2, .s 45 2, .s 45 2]⟩,
    ⟨0, 3, 14, 17, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 11 5, .s 11 5, .s 11 5, .s 11 5]⟩,
    ⟨0, 3, 15, 17, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 29 4, .s 29 4, .s 29 4, .s 29 4]⟩,
    ⟨0, 3, 16, 18, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 35 0, .s 35 0, .s 35 0, .s 35 0]⟩,
    ⟨0, 3, 17, 15, [[.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0]], [.s 36 3, .s 36 3, .s 36 3, .s 36 3]⟩,
    ⟨0, 3, 18, 18, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 33 4, .s 33 4, .s 33 4, .s 33 4]⟩,
    ⟨0, 3, 19, 18, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 33 5, .s 33 5, .s 33 5, .s 33 5]⟩,
    ⟨0, 3, 20, 17, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 34 4, .s 34 4, .s 34 4, .s 34 4]⟩,
    ⟨0, 3, 21, 16, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.f ⟨24, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 64 0, .s 64 0]], [.s 43 3, .s 43 3, .s 43 3, .s 43 3]⟩,
    ⟨0, 3, 22, 14, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.f ⟨24, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 66 0, .s 66 0]], [.s 37 1, .s 37 1, .s 37 1, .s 37 1]⟩,
    ⟨0, 3, 23, 13, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.s 16 4, .s 16 4, .s 16 4, .s 16 4]⟩,
    ⟨0, 3, 24, 18, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 41 5, .s 41 5, .s 41 5, .s 41 5]⟩,
    ⟨0, 3, 25, 15, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.f ⟨24, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 64 0, .s 64 0], [.f ⟨24, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 66 0, .s 66 0], [.f ⟨24, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 18, 1, 0, 1, 0, 0, 0, 0⟩, .s 70 0, .s 70 0]], [.s 48 4, .s 48 4, .s 48 4, .s 48 4]⟩,
    ⟨0, 4, 0, 26, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0]], [.s 58 0, .s 58 0, .s 58 0, .s 58 0]⟩,
    ⟨0, 4, 1, 22, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 54 4, .s 54 4, .s 54 4, .s 54 4]⟩,
    ⟨0, 4, 2, 21, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0]], [.s 9 5, .s 9 5, .s 9 5, .s 9 5]⟩,
    ⟨0, 4, 3, 22, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 56 0, .s 56 0, .s 56 0, .s 56 0]⟩,
    ⟨0, 4, 4, 21, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 57 3, .s 57 3, .s 57 3, .s 57 3]⟩,
    ⟨0, 4, 5, 20, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.s 32 5, .s 32 5, .s 32 5, .s 32 5]⟩,
    ⟨0, 4, 6, 25, [[.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0]], [.s 70 1, .s 70 1, .s 70 1, .s 70 1]⟩,
    ⟨0, 4, 7, 23, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 53 3, .s 53 3, .s 53 3, .s 53 3]⟩,
    ⟨0, 4, 8, 22, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 56 2, .s 56 2, .s 56 2, .s 56 2]⟩,
    ⟨0, 4, 9, 23, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 73 1, .s 73 1, .s 73 1, .s 73 1]⟩,
    ⟨0, 4, 10, 20, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 39 4, .s 39 4, .s 39 4, .s 39 4]⟩,
    ⟨0, 4, 11, 19, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 42 3, .s 42 3, .s 42 3, .s 42 3]⟩,
    ⟨0, 4, 12, 25, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 51 3, .s 51 3, .s 51 3, .s 51 3]⟩,
    ⟨0, 4, 13, 25, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 71 2, .s 71 2, .s 71 2, .s 71 2]⟩,
    ⟨0, 4, 14, 23, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 37 5, .s 37 5, .s 37 5, .s 37 5]⟩,
    ⟨0, 4, 15, 23, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 55 4, .s 55 4, .s 55 4, .s 55 4]⟩,
    ⟨0, 4, 16, 24, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 61 0, .s 61 0, .s 61 0, .s 61 0]⟩,
    ⟨0, 4, 17, 21, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0]], [.s 62 3, .s 62 3, .s 62 3, .s 62 3]⟩,
    ⟨0, 4, 18, 24, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 59 4, .s 59 4, .s 59 4, .s 59 4]⟩,
    ⟨0, 4, 19, 24, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 59 5, .s 59 5, .s 59 5, .s 59 5]⟩,
    ⟨0, 4, 20, 23, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 60 4, .s 60 4, .s 60 4, .s 60 4]⟩,
    ⟨0, 4, 21, 22, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0]], [.s 69 3, .s 69 3, .s 69 3, .s 69 3]⟩,
    ⟨0, 4, 22, 20, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 63 1, .s 63 1, .s 63 1, .s 63 1]⟩,
    ⟨0, 4, 23, 19, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.s 42 4, .s 42 4, .s 42 4, .s 42 4]⟩,
    ⟨0, 4, 24, 24, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 67 5, .s 67 5, .s 67 5, .s 67 5]⟩,
    ⟨0, 4, 25, 21, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 74 4, .s 74 4, .s 74 4, .s 74 4]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, 2, 1), (-1, -1, 1), (1, -2, -1), (1, 1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, 0, 0, 7, [[.f ⟨30, 61, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 12 0], [.f ⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 0]⟩,
    ⟨-1, 0, 1, 5, [[.f ⟨30, 63, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 3 0], [.s 7 0], [.s 14 0]], [.s 3 0]⟩,
    ⟨-1, 0, 2, 6, [[.f ⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨30, 63, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0]], [.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 0, 3, 4, [[.s 1 0], [.s 4 0], [.s 7 0], [.s 8 0], [.s 15 0]], [.s 4 0]⟩,
    ⟨-1, 0, 4, 3, [[.s 3 0], [.s 5 0], [.s 8 0], [.s 10 0], [.s 17 0]], [.s 17 0]⟩,
    ⟨-1, 0, 5, 4, [[.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 10 0]], [.s 4 1]⟩,
    ⟨-1, 0, 6, 6, [[.s 0 0], [.s 12 0], [.s 13 0], [.s 18 0], [.s 19 0], [.f ⟨6, 5, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 13 0]⟩,
    ⟨-1, 0, 7, 5, [[.s 1 0], [.s 3 0], [.s 14 0], [.s 15 0], [.s 18 0], [.s 19 0]], [.s 3 2]⟩,
    ⟨-1, 0, 8, 3, [[.s 3 0], [.s 4 0], [.s 15 0], [.s 17 0], [.s 20 0], [.s 21 0]], [.s 17 1]⟩,
    ⟨-1, 0, 9, 2, [[.s 16 0], [.s 20 0], [.s 21 0], [.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 12, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 10, 3, [[.f ⟨7, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 5 0], [.s 17 0], [.s 22 0], [.s 23 0]], [.s 17 2]⟩,
    ⟨-1, 0, 11, 2, [[.f ⟨7, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.s 22 0], [.s 23 0], [.f ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 14, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 12, 7, [[.f ⟨30, 61, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨30, 73, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨30, 77, 0, 0, 0, 0, 0, 0, 0⟩], [.s 0 0], [.s 6 0], [.s 18 0]], [.s 6 1]⟩,
    ⟨-1, 0, 13, 5, [[.s 6 0], [.s 19 0], [.s 24 0], [.f ⟨6, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 24 0]⟩,
    ⟨-1, 0, 14, 6, [[.f ⟨30, 63, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨30, 74, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨30, 77, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 7 0], [.s 18 0]], [.s 1 4]⟩,
    ⟨-1, 0, 15, 4, [[.s 3 0], [.s 7 0], [.s 8 0], [.s 19 0], [.s 20 0], [.s 24 0]], [.s 8 2]⟩,
    ⟨-1, 0, 16, 3, [[.s 9 0], [.s 20 0], [.s 24 0], [.f ⟨6, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 23, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 9 0]⟩,
    ⟨-1, 0, 17, 2, [[.s 4 0], [.s 8 0], [.s 10 0], [.s 21 0], [.s 22 0], [.s 25 0]], [.s 25 0]⟩,
    ⟨-1, 0, 18, 6, [[.f ⟨30, 77, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 7 0], [.s 12 0], [.s 14 0], [.s 19 0]], [.s 7 4]⟩,
    ⟨-1, 0, 19, 5, [[.s 6 0], [.s 7 0], [.s 13 0], [.s 15 0], [.s 18 0], [.s 24 0]], [.s 15 3]⟩,
    ⟨-1, 0, 20, 3, [[.s 8 0], [.s 9 0], [.s 15 0], [.s 16 0], [.s 21 0], [.s 24 0]], [.s 9 1]⟩,
    ⟨-1, 0, 21, 2, [[.s 8 0], [.s 9 0], [.s 17 0], [.s 20 0], [.s 25 0], [.f ⟨0, 12, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 25 1]⟩,
    ⟨-1, 0, 22, 2, [[.s 10 0], [.s 11 0], [.s 17 0], [.s 23 0], [.s 25 0], [.f ⟨0, 14, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 25 2]⟩,
    ⟨-1, 0, 23, 3, [[.f ⟨7, 13, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 16, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.s 10 0], [.s 11 0], [.s 22 0]], [.s 11 2]⟩,
    ⟨-1, 0, 24, 4, [[.s 13 0], [.s 15 0], [.s 16 0], [.s 19 0], [.s 20 0], [.f ⟨6, 23, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 16 2]⟩,
    ⟨-1, 0, 25, 1, [[.s 17 0], [.s 21 0], [.s 22 0], [.f ⟨0, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 18, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 18, 0, 0, 0, 0, 0, 0, 0⟩]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, 2, 2), (-1, -1, 1), (1, 1, -1)], -1, 2, 2, 3, 0, 0, 0, 0,
   [⟨-2, 1, 0, 16, [[.f ⟨30, 61, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 61, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨6, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨6, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 5, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 6 0, .s 6 0]⟩,
    ⟨-2, 1, 1, 14, [[.f ⟨30, 63, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 63, 1, 0, 2, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 3 0, .s 3 0]⟩,
    ⟨-2, 1, 2, 14, [[.f ⟨30, 35, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 35, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨30, 42, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 42, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨30, 63, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 63, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨30, 52, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 52, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨30, 52, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨30, 52, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-2, 1, 3, 13, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 4 0, .s 4 0]⟩,
    ⟨-2, 1, 4, 12, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 10 1, .s 10 1]⟩,
    ⟨-2, 1, 5, 12, [[.f ⟨30, 52, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 52, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨30, 58, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 58, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨30, 65, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 65, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.f ⟨30, 65, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨30, 65, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-2, 1, 6, 15, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨6, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 5, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 13 0, .s 13 0]⟩,
    ⟨-2, 1, 7, 14, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 3 2, .s 3 2]⟩,
    ⟨-2, 1, 8, 12, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 17 1, .s 17 1]⟩,
    ⟨-2, 1, 9, 11, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨25, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨6, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 12, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-2, 1, 10, 11, [[.f ⟨30, 65, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 65, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 22 0, .s 22 0]⟩,
    ⟨-2, 1, 11, 9, [[.f ⟨30, 68, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 68, 1, 0, 1, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨6, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 1, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨6, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 1, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-2, 1, 12, 16, [[.f ⟨30, 61, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 61, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨30, 73, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 73, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨30, 77, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 77, 1, 0, 2, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.s 6 1, .s 6 1]⟩,
    ⟨-2, 1, 13, 14, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨6, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨6, 10, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 10, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨6, 23, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 23, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 24 0, .s 24 0]⟩,
    ⟨-2, 1, 14, 15, [[.f ⟨30, 63, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 63, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨30, 74, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 74, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨30, 77, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 77, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.s 1 4, .s 1 4]⟩,
    ⟨-2, 1, 15, 13, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 8 2, .s 8 2]⟩,
    ⟨-2, 1, 16, 12, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨6, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨6, 23, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 23, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨25, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 9 0, .s 9 0]⟩,
    ⟨-2, 1, 17, 11, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 22 2, .s 22 2]⟩,
    ⟨-2, 1, 18, 15, [[.f ⟨30, 77, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨30, 77, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 7 4, .s 7 4]⟩,
    ⟨-2, 1, 19, 14, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 15 3, .s 15 3]⟩,
    ⟨-2, 1, 20, 12, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 9 1, .s 9 1]⟩,
    ⟨-2, 1, 21, 11, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨6, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 12, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 25 1, .s 25 1]⟩,
    ⟨-2, 1, 22, 10, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨6, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 11 1, .s 11 1]⟩,
    ⟨-2, 1, 23, 10, [[.f ⟨30, 65, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 65, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨30, 68, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 68, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨30, 76, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 76, 1, 0, 1, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨30, 68, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨30, 68, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨-2, 1, 24, 13, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨6, 23, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 23, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 16 2, .s 16 2]⟩,
    ⟨-2, 1, 25, 10, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨6, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 14, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨6, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 18, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨6, 14, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨6, 14, 1, 0, 1, 0, 0, 0, 2⟩]⟩]⟩,
  ⟨1, -2, -1, 0, 0, [(-1, -1, 2), (-1, 2, 1), (1, -2, -1)], -1, -1, 2, 3, 0, 0, 0, 0,
   [⟨-3, -1, 0, 16, [[.f ⟨30, 61, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 61, 0, 0, 0, 1, 0, 2, 0⟩], [.s 6 0, .s 6 0], [.s 12 0, .s 12 0], [.f ⟨30, 28, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 28, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨30, 31, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 31, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 6 0, .s 6 0]⟩,
    ⟨-3, -1, 1, 14, [[.f ⟨30, 63, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 63, 0, 0, 0, 1, 0, 2, 0⟩], [.s 2 0, .s 2 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 14 0, .s 14 0]], [.s 3 0, .s 3 0]⟩,
    ⟨-3, -1, 2, 15, [[.f ⟨1, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 9, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨1, 16, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨1, 16, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨30, 63, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 63, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨8, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0]], [.f ⟨8, 0, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨8, 0, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-3, -1, 3, 13, [[.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 15 0, .s 15 0]], [.s 8 0, .s 8 0]⟩,
    ⟨-3, -1, 4, 13, [[.s 3 0, .s 3 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 17 0, .s 17 0]], [.s 8 1, .s 8 1]⟩,
    ⟨-3, -1, 5, 13, [[.f ⟨8, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨8, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 6, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨8, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 10 0, .s 10 0]], [.s 10 2, .s 10 2]⟩,
    ⟨-3, -1, 6, 15, [[.s 0 0, .s 0 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0], [.f ⟨30, 31, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 31, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 13 0, .s 13 0]⟩,
    ⟨-3, -1, 7, 14, [[.s 1 0, .s 1 0], [.s 3 0, .s 3 0], [.s 14 0, .s 14 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 19 0, .s 19 0]], [.s 3 2, .s 3 2]⟩,
    ⟨-3, -1, 8, 12, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0]], [.s 21 0, .s 21 0]⟩,
    ⟨-3, -1, 9, 11, [[.s 16 0, .s 16 0], [.s 20 0, .s 20 0], [.s 21 0, .s 21 0], [.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨1, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨30, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 54, 0, 0, 0, 1, 0, 1, 0⟩]], [.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 0, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-3, -1, 10, 12, [[.f ⟨8, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 22 0, .s 22 0]⟩,
    ⟨-3, -1, 11, 11, [[.f ⟨8, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.f ⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 1, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨1, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 1, 1, 0, 1, 0, 0, 0, 0⟩]⟩,
    ⟨-3, -1, 12, 16, [[.f ⟨30, 61, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 61, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨30, 73, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 73, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨30, 77, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 77, 0, 0, 0, 1, 0, 2, 0⟩], [.s 0 0, .s 0 0], [.s 6 0, .s 6 0], [.s 18 0, .s 18 0]], [.s 6 1, .s 6 1]⟩,
    ⟨-3, -1, 13, 14, [[.s 6 0, .s 6 0], [.s 19 0, .s 19 0], [.s 24 0, .s 24 0], [.f ⟨30, 31, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 31, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨30, 36, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 36, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨30, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 49, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 24 0, .s 24 0]⟩,
    ⟨-3, -1, 14, 15, [[.f ⟨30, 63, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 63, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨30, 74, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 74, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨30, 77, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 77, 0, 0, 0, 1, 0, 2, 0⟩], [.s 1 0, .s 1 0], [.s 7 0, .s 7 0], [.s 18 0, .s 18 0]], [.s 1 4, .s 1 4]⟩,
    ⟨-3, -1, 15, 13, [[.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 8 0, .s 8 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0]], [.s 8 2, .s 8 2]⟩,
    ⟨-3, -1, 16, 12, [[.s 9 0, .s 9 0], [.s 20 0, .s 20 0], [.s 24 0, .s 24 0], [.f ⟨30, 37, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 37, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨30, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 49, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨30, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 54, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 9 0, .s 9 0]⟩,
    ⟨-3, -1, 17, 12, [[.s 4 0, .s 4 0], [.s 8 0, .s 8 0], [.s 10 0, .s 10 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 25 0, .s 25 0]], [.s 21 2, .s 21 2]⟩,
    ⟨-3, -1, 18, 15, [[.f ⟨30, 77, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨30, 77, 0, 0, 0, 1, 0, 2, 0⟩], [.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 12 0, .s 12 0], [.s 14 0, .s 14 0], [.s 19 0, .s 19 0]], [.s 7 4, .s 7 4]⟩,
    ⟨-3, -1, 19, 14, [[.s 6 0, .s 6 0], [.s 7 0, .s 7 0], [.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 18 0, .s 18 0], [.s 24 0, .s 24 0]], [.s 15 3, .s 15 3]⟩,
    ⟨-3, -1, 20, 12, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 24 0, .s 24 0]], [.s 9 1, .s 9 1]⟩,
    ⟨-3, -1, 21, 11, [[.s 8 0, .s 8 0], [.s 9 0, .s 9 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 25 0, .s 25 0], [.f ⟨1, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 12, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨1, 12, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨1, 12, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-3, -1, 22, 11, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 17 0, .s 17 0], [.s 23 0, .s 23 0], [.s 25 0, .s 25 0], [.f ⟨1, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 14, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨1, 14, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨1, 14, 1, 0, 1, 0, 0, 0, 1⟩]⟩,
    ⟨-3, -1, 23, 12, [[.f ⟨8, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 13, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨8, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 16, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨8, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 24, 1, 0, 1, 0, 0, 0, 0⟩], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 11 2, .s 11 2]⟩,
    ⟨-3, -1, 24, 13, [[.s 13 0, .s 13 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 20 0, .s 20 0], [.f ⟨30, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨30, 49, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 16 2, .s 16 2]⟩,
    ⟨-3, -1, 25, 11, [[.s 17 0, .s 17 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨1, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨1, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 14, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨1, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨1, 18, 1, 0, 1, 0, 0, 0, 0⟩]], [.f ⟨1, 12, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨1, 12, 1, 0, 1, 0, 0, 0, 2⟩]⟩]⟩,
  ⟨2, -1, 1, -2, -1, [(-1, 2, 2), (-1, -1, 2)], -1, 2, 2, 3, -1, -1, 2, 3,
   [⟨-4, 0, 0, 25, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]⟩,
    ⟨-4, 0, 1, 23, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 3 0, .s 3 0, .s 3 0, .s 3 0]⟩,
    ⟨-4, 0, 2, 23, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.s 52 3, .s 52 3, .s 52 3, .s 52 3]⟩,
    ⟨-4, 0, 3, 22, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0]], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]⟩,
    ⟨-4, 0, 4, 21, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0]], [.s 10 1, .s 10 1, .s 10 1, .s 10 1]⟩,
    ⟨-4, 0, 5, 21, [[.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.s 65 3, .s 65 3, .s 65 3, .s 65 3]⟩,
    ⟨-4, 0, 6, 24, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 13 0, .s 13 0, .s 13 0, .s 13 0]⟩,
    ⟨-4, 0, 7, 23, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 3 2, .s 3 2, .s 3 2, .s 3 2]⟩,
    ⟨-4, 0, 8, 21, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.s 17 1, .s 17 1, .s 17 1, .s 17 1]⟩,
    ⟨-4, 0, 9, 20, [[.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 26 0, .s 26 0, .s 26 0, .s 26 0]⟩,
    ⟨-4, 0, 10, 20, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]⟩,
    ⟨-4, 0, 11, 18, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 27 0, .s 27 0, .s 27 0, .s 27 0]⟩,
    ⟨-4, 0, 12, 25, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 6 1, .s 6 1, .s 6 1, .s 6 1]⟩,
    ⟨-4, 0, 13, 23, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]⟩,
    ⟨-4, 0, 14, 24, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 1 4, .s 1 4, .s 1 4, .s 1 4]⟩,
    ⟨-4, 0, 15, 22, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 8 2, .s 8 2, .s 8 2, .s 8 2]⟩,
    ⟨-4, 0, 16, 21, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 9 0, .s 9 0, .s 9 0, .s 9 0]⟩,
    ⟨-4, 0, 17, 20, [[.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 22 2, .s 22 2, .s 22 2, .s 22 2]⟩,
    ⟨-4, 0, 18, 24, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 7 4, .s 7 4, .s 7 4, .s 7 4]⟩,
    ⟨-4, 0, 19, 23, [[.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 15 3, .s 15 3, .s 15 3, .s 15 3]⟩,
    ⟨-4, 0, 20, 21, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 9 1, .s 9 1, .s 9 1, .s 9 1]⟩,
    ⟨-4, 0, 21, 20, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.s 25 1, .s 25 1, .s 25 1, .s 25 1]⟩,
    ⟨-4, 0, 22, 19, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 11 1, .s 11 1, .s 11 1, .s 11 1]⟩,
    ⟨-4, 0, 23, 19, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.s 68 4, .s 68 4, .s 68 4, .s 68 4]⟩,
    ⟨-4, 0, 24, 22, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 16 2, .s 16 2, .s 16 2, .s 16 2]⟩,
    ⟨-4, 0, 25, 19, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 40 2, .s 40 2, .s 40 2, .s 40 2]⟩,
    ⟨-3, 0, 0, 19, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 32 0, .s 32 0, .s 32 0, .s 32 0]⟩,
    ⟨-3, 0, 1, 17, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 29 0, .s 29 0, .s 29 0, .s 29 0]⟩,
    ⟨-3, 0, 2, 17, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.f ⟨29, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨29, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0]], [.f ⟨29, 0, 0, 0, 0, 0, 0, 0, 3⟩, .s 0 3, .f ⟨29, 0, 0, 1, 1, 0, 0, 0, 3⟩, .s 0 3]⟩,
    ⟨-3, 0, 3, 16, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0]], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]⟩,
    ⟨-3, 0, 4, 15, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 36 1, .s 36 1, .s 36 1, .s 36 1]⟩,
    ⟨-3, 0, 5, 15, [[.f ⟨29, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨29, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨29, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 6 0, .f ⟨29, 6, 0, 1, 1, 0, 0, 0, 0⟩, .s 6 0], [.f ⟨29, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 13 0, .f ⟨29, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 13 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.f ⟨29, 13, 0, 0, 0, 0, 0, 0, 3⟩, .s 13 3, .f ⟨29, 13, 0, 1, 1, 0, 0, 0, 3⟩, .s 13 3]⟩,
    ⟨-3, 0, 6, 18, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 39 0, .s 39 0, .s 39 0, .s 39 0]⟩,
    ⟨-3, 0, 7, 17, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 29 2, .s 29 2, .s 29 2, .s 29 2]⟩,
    ⟨-3, 0, 8, 15, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 43 1, .s 43 1, .s 43 1, .s 43 1]⟩,
    ⟨-3, 0, 9, 14, [[.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.f ⟨28, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 2 0, .s 2 0]], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]⟩,
    ⟨-3, 0, 10, 14, [[.f ⟨29, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 13 0, .f ⟨29, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 13 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]⟩,
    ⟨-3, 0, 11, 12, [[.f ⟨29, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 16 0, .f ⟨29, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 16 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 53 0, .s 53 0, .s 53 0, .s 53 0]⟩,
    ⟨-3, 0, 12, 19, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 32 1, .s 32 1, .s 32 1, .s 32 1]⟩,
    ⟨-3, 0, 13, 17, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]⟩,
    ⟨-3, 0, 14, 18, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 27 4, .s 27 4, .s 27 4, .s 27 4]⟩,
    ⟨-3, 0, 15, 16, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 34 2, .s 34 2, .s 34 2, .s 34 2]⟩,
    ⟨-3, 0, 16, 15, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.f ⟨28, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 2 0, .s 2 0]], [.s 35 0, .s 35 0, .s 35 0, .s 35 0]⟩,
    ⟨-3, 0, 17, 14, [[.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0]], [.s 48 2, .s 48 2, .s 48 2, .s 48 2]⟩,
    ⟨-3, 0, 18, 18, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 33 4, .s 33 4, .s 33 4, .s 33 4]⟩,
    ⟨-3, 0, 19, 17, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 41 3, .s 41 3, .s 41 3, .s 41 3]⟩,
    ⟨-3, 0, 20, 15, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 35 1, .s 35 1, .s 35 1, .s 35 1]⟩,
    ⟨-3, 0, 21, 14, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 51 1, .s 51 1, .s 51 1, .s 51 1]⟩,
    ⟨-3, 0, 22, 13, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 37 1, .s 37 1, .s 37 1, .s 37 1]⟩,
    ⟨-3, 0, 23, 13, [[.f ⟨29, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 13 0, .f ⟨29, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 13 0], [.f ⟨29, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 16 0, .f ⟨29, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 16 0], [.f ⟨29, 24, 0, 0, 0, 0, 0, 0, 0⟩, .s 24 0, .f ⟨29, 24, 0, 1, 1, 0, 0, 0, 0⟩, .s 24 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.f ⟨29, 16, 0, 0, 0, 0, 0, 0, 4⟩, .s 16 4, .f ⟨29, 16, 0, 1, 1, 0, 0, 0, 4⟩, .s 16 4]⟩,
    ⟨-3, 0, 24, 16, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 42 2, .s 42 2, .s 42 2, .s 42 2]⟩,
    ⟨-3, 0, 25, 13, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 66 2, .s 66 2, .s 66 2, .s 66 2]⟩,
    ⟨-2, 0, 0, 13, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.f ⟨28, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 2 0, .s 2 0], [.f ⟨28, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 5 0, .s 5 0]], [.s 58 0, .s 58 0, .s 58 0, .s 58 0]⟩,
    ⟨-2, 0, 1, 11, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 55 0, .s 55 0, .s 55 0, .s 55 0]⟩,
    ⟨-2, 0, 2, 11, [[.f ⟨29, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 9 0, .f ⟨29, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 9 0], [.f ⟨29, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 16 0, .f ⟨29, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 16 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 26 0, .f ⟨1, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 26 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0]], [.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 3⟩, .s 26 3, .f ⟨1, 0, 0, 1, 1, 0, 0, 0, 3⟩, .s 26 3]⟩,
    ⟨-2, 0, 3, 10, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 56 0, .s 56 0, .s 56 0, .s 56 0]⟩,
    ⟨-2, 0, 4, 9, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 62 1, .s 62 1, .s 62 1, .s 62 1]⟩,
    ⟨-2, 0, 5, 9, [[.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 26 0, .f ⟨1, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 26 0], [.f ⟨1, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 32 0, .f ⟨1, 6, 0, 1, 1, 0, 0, 0, 0⟩, .s 32 0], [.f ⟨1, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 39 0, .f ⟨1, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 39 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.f ⟨1, 13, 0, 0, 0, 0, 0, 0, 3⟩, .s 39 3, .f ⟨1, 13, 0, 1, 1, 0, 0, 0, 3⟩, .s 39 3]⟩,
    ⟨-2, 0, 6, 12, [[.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.f ⟨28, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 5 0, .s 5 0]], [.s 65 0, .s 65 0, .s 65 0, .s 65 0]⟩,
    ⟨-2, 0, 7, 11, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 55 2, .s 55 2, .s 55 2, .s 55 2]⟩,
    ⟨-2, 0, 8, 9, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 69 1, .s 69 1, .s 69 1, .s 69 1]⟩,
    ⟨-2, 0, 9, 8, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.f ⟨27, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 0, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 0, 0, 1, 0, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨27, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 12, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 12, 0, 1, 0, 0, 0, 0, 0⟩, .s 12 0], [.f ⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 28 0, .s 28 0]], [.f ⟨27, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 0, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 0, 0, 1, 0, 0, 0, 0, 0⟩, .s 0 0]⟩,
    ⟨-2, 0, 10, 8, [[.f ⟨1, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 39 0, .f ⟨1, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 39 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]⟩,
    ⟨-2, 0, 11, 6, [[.f ⟨1, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 42 0, .f ⟨1, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 42 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.f ⟨27, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 1, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 1, 0, 1, 0, 0, 0, 0, 0⟩, .s 1 0], [.f ⟨27, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 2, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 2, 0, 1, 0, 0, 0, 0, 0⟩, .s 2 0], [.f ⟨27, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 14, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 14, 0, 1, 0, 0, 0, 0, 0⟩, .s 14 0]], [.f ⟨27, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 1, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 1, 0, 1, 0, 0, 0, 0, 0⟩, .s 1 0]⟩,
    ⟨-2, 0, 12, 13, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 58 1, .s 58 1, .s 58 1, .s 58 1]⟩,
    ⟨-2, 0, 13, 11, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.f ⟨28, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 5 0, .s 5 0], [.f ⟨28, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 10, 1, 0, 1, 0, 0, 0, 0⟩, .s 10 0, .s 10 0], [.f ⟨28, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 23 0, .s 23 0]], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]⟩,
    ⟨-2, 0, 14, 12, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 53 4, .s 53 4, .s 53 4, .s 53 4]⟩,
    ⟨-2, 0, 15, 10, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 60 2, .s 60 2, .s 60 2, .s 60 2]⟩,
    ⟨-2, 0, 16, 9, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.f ⟨28, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0], [.f ⟨28, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 23 0, .s 23 0], [.f ⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 28 0, .s 28 0]], [.s 61 0, .s 61 0, .s 61 0, .s 61 0]⟩,
    ⟨-2, 0, 17, 8, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0]], [.s 74 2, .s 74 2, .s 74 2, .s 74 2]⟩,
    ⟨-2, 0, 18, 12, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 59 4, .s 59 4, .s 59 4, .s 59 4]⟩,
    ⟨-2, 0, 19, 11, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 67 3, .s 67 3, .s 67 3, .s 67 3]⟩,
    ⟨-2, 0, 20, 9, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 61 1, .s 61 1, .s 61 1, .s 61 1]⟩,
    ⟨-2, 0, 21, 8, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.f ⟨27, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 12, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 12, 0, 1, 0, 0, 0, 0, 0⟩, .s 12 0]], [.s 77 1, .s 77 1, .s 77 1, .s 77 1]⟩,
    ⟨-2, 0, 22, 7, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.f ⟨27, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 14, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 14, 0, 1, 0, 0, 0, 0, 0⟩, .s 14 0]], [.s 63 1, .s 63 1, .s 63 1, .s 63 1]⟩,
    ⟨-2, 0, 23, 7, [[.f ⟨1, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 39 0, .f ⟨1, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 39 0], [.f ⟨1, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 42 0, .f ⟨1, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 42 0], [.f ⟨1, 24, 0, 0, 0, 0, 0, 0, 0⟩, .s 50 0, .f ⟨1, 24, 0, 1, 1, 0, 0, 0, 0⟩, .s 50 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.s 63 2, .s 42 4, .s 63 2, .s 42 4]⟩,
    ⟨-2, 0, 24, 10, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.f ⟨28, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 23 0, .s 23 0]], [.s 68 2, .s 68 2, .s 68 2, .s 68 2]⟩,
    ⟨-2, 0, 25, 7, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.f ⟨27, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 12, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 12, 0, 1, 0, 0, 0, 0, 0⟩, .s 12 0], [.f ⟨27, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 14, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 14, 0, 1, 0, 0, 0, 0, 0⟩, .s 14 0], [.f ⟨27, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 18, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨29, 18, 0, 1, 0, 0, 0, 0, 0⟩, .s 18 0]], [.f ⟨27, 14, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨28, 14, 1, 0, 0, 0, 0, 0, 2⟩, .f ⟨29, 14, 0, 1, 0, 0, 0, 0, 2⟩, .s 14 2]⟩]⟩]

set_option maxRecDepth 100000 in
def certsData : List (List (List (Bool × ℕ × ℕ))) := [
  [[], [(false, 0, 2), (false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 2), (true, 2, 1)], [(false, 1, 1), (false, 2, 1), (true, 2, 1)], [(false, 1, 2), (false, 3, 1), (true, 2, 1)], [(false, 1, 1), (false, 3, 2), (true, 2, 1)], [(false, 0, 1), (false, 3, 1), (true, 2, 1)], [(false, 0, 2), (false, 3, 1), (true, 0, 1)], [(false, 0, 2), (false, 3, 1), (true, 0, 1)], [(false, 0, 2), (false, 3, 1), (true, 1, 1)], [(false, 0, 2), (false, 3, 1), (true, 0, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 1, 1), (false, 2, 2), (true, 0, 1)], [(false, 1, 1), (false, 2, 2), (true, 0, 1)], [(false, 1, 1), (false, 2, 2), (true, 1, 1)], [(false, 1, 1), (false, 2, 2), (true, 0, 1)], [(false, 0, 1), (false, 3, 2), (true, 1, 1)], [(false, 0, 1), (false, 3, 2), (true, 1, 1)], [(false, 0, 1), (false, 3, 2), (true, 0, 1)], [(false, 0, 1), (false, 3, 2), (true, 1, 1)], [(false, 0, 2), (false, 3, 1), (true, 1, 1)], [(false, 0, 2), (false, 3, 1), (true, 1, 1)], [(false, 0, 2), (false, 3, 1), (true, 0, 1)], [(false, 0, 2), (false, 3, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 2, 1), (true, 2, 5)], [], [(false, 1, 4), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (false, 2, 3), (true, 0, 5)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 3), (false, 2, 4), (true, 2, 5)], [(false, 0, 1), (false, 2, 3), (true, 1, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 3), (true, 2, 5)], [(false, 1, 4), (false, 2, 3), (true, 1, 5)], [(false, 0, 1), (false, 2, 3), (true, 2, 5)], [(false, 1, 4), (false, 2, 3), (true, 1, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (false, 2, 3), (true, 1, 5)], [(false, 0, 1), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 2, 2), (true, 2, 5)], [(false, 0, 4), (false, 2, 3), (true, 1, 5)], [], [(false, 1, 1), (false, 2, 3), (true, 0, 5)], [(false, 0, 4), (false, 2, 3), (true, 0, 5)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 3), (false, 2, 1), (true, 2, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 4), (false, 2, 3), (true, 2, 5)], [(false, 1, 1), (false, 2, 3), (true, 1, 5)], [(false, 0, 4), (false, 2, 3), (true, 2, 5)], [(false, 1, 1), (false, 2, 3), (true, 1, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 4), (false, 2, 3), (true, 0, 5)], [(false, 0, 4), (false, 2, 3), (true, 0, 5)], [(false, 0, 4), (false, 2, 3), (true, 1, 5)], [(false, 0, 4), (false, 2, 3), (true, 0, 5)]],
  [[(false, 0, 1), (false, 2, 1), (true, 1, 2)], [(false, 0, 3), (false, 2, 1), (true, 2, 2)], [(false, 0, 1), (false, 2, 3), (true, 1, 2)], [], [(false, 1, 1), (false, 2, 3), (true, 0, 2)], [(false, 0, 1), (false, 2, 3), (true, 0, 2)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 3), (true, 0, 2)], [(false, 0, 1), (false, 2, 3), (true, 0, 2)], [(false, 0, 1), (false, 2, 3), (true, 1, 2)], [(false, 0, 1), (false, 2, 3), (true, 0, 2)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 3), (true, 2, 2)], [(false, 1, 1), (false, 2, 3), (true, 1, 2)], [(false, 0, 1), (false, 2, 3), (true, 2, 2)], [(false, 1, 1), (false, 2, 3), (true, 1, 2)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 2, 1), (true, 3, 5)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 3), (false, 2, 4), (true, 2, 5)], [(false, 0, 1), (false, 2, 3), (true, 1, 5)], [], [(false, 1, 4), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (false, 2, 3), (true, 1, 5)], [(false, 0, 1), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 3), (true, 2, 5)], [(false, 1, 4), (false, 2, 3), (true, 1, 5)], [(false, 0, 1), (false, 2, 3), (true, 2, 5)], [(false, 1, 4), (false, 2, 3), (true, 1, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 2, 2), (true, 3, 5)], [(false, 0, 4), (false, 2, 3), (true, 0, 5)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 3), (false, 2, 1), (true, 2, 5)], [(false, 0, 4), (false, 2, 3), (true, 1, 5)], [], [(false, 1, 1), (false, 2, 3), (true, 0, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 4), (false, 2, 3), (true, 0, 5)], [(false, 0, 4), (false, 2, 3), (true, 0, 5)], [(false, 0, 4), (false, 2, 3), (true, 1, 5)], [(false, 0, 4), (false, 2, 3), (true, 0, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 4), (false, 2, 3), (true, 2, 5)], [(false, 1, 1), (false, 2, 3), (true, 1, 5)], [(false, 0, 4), (false, 2, 3), (true, 2, 5)], [(false, 1, 1), (false, 2, 3), (true, 1, 5)]],
  [[(false, 0, 1), (false, 2, 1), (true, 0, 2)], [(false, 1, 1), (false, 2, 3), (true, 0, 2)], [(false, 0, 1), (false, 2, 3), (true, 0, 2)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 3), (false, 2, 1), (true, 2, 2)], [(false, 0, 1), (false, 2, 3), (true, 1, 2)], [], [(false, 0, 1), (false, 2, 3), (true, 2, 2)], [(false, 1, 1), (false, 2, 3), (true, 1, 2)], [(false, 0, 1), (false, 2, 3), (true, 2, 2)], [(false, 1, 1), (false, 2, 3), (true, 1, 2)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 3), (true, 0, 2)], [(false, 0, 1), (false, 2, 3), (true, 0, 2)], [(false, 0, 1), (false, 2, 3), (true, 1, 2)], [(false, 0, 1), (false, 2, 3), (true, 0, 2)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 0, 3)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 0, 3)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 2, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 0, 3)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 0, 3)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 2, 3)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 2, 3)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 2, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 2, 3)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 2, 3)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 1, 3)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 1, 3)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 2, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 1, 3)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 1, 3)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 1, 3)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 1, 3)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 2, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 1, 3)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 1, 3)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 3, 3)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 3, 3)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 2, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 3, 3)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 3, 3)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 0, 3)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 0, 3)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 2, 1)], [(false, 2, 1), (true, 1, 1)]],
  [[(false, 0, 2), (false, 1, 1), (true, 0, 3)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 2, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 2), (true, 0, 3)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], []]]

def cfg : GalCert.Cfg 26 := ⟨adj, (0, 0, 18), 9, regsData, certsData, 0, 18⟩

set_option maxRecDepth 100000 in
theorem hc : cfg.check = true := by decide +kernel

theorem hV : cfg.vbound 30 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

theorem hrec : ∀ k, (([(1, 16), (-1, 15), (-1, 7), (1, 6)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide) (by decide +kernel)

theorem hgfw : ∀ n < 30 + 2 * cfg.L, ((GalCert.csOf [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] 16).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

theorem hsmall : ∀ n < 16, GalCert.conv a [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] n = ([1, 5, 6, 4, 7, 5, 7, 5, 6, 5, 1, 0, 0, 1, 0, -1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P315660

open PowerSeries OMA.S_oeis_a315660 in
theorem OMA.solution : type_of% @OMA.S_oeis_a315660.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 16 := ⟨n - 16, by omega⟩
    have h := P315660.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 16 - 1 = k + 15 by omega,
      show k + 16 - 9 = k + 7 by omega,
      show k + 16 - 10 = k + 6 by omega,
      P315660.ha (k + 16) (by omega),
      P315660.ha (k + 15) (by omega),
      P315660.ha (k + 7) (by omega),
      P315660.ha (k + 6) (by omega)]
    linarith
  · have hD : (X^10 - X^9 - X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (-X^15 + X^13 + X^10 + 5*X^9 + 6*X^8 + 5*X^7 + 7*X^6 + 5*X^5 + 7*X^4 + 4*X^3 + 6*X^2 + 5*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 5, 6, 4, 7, 5, 7, 5, 6, 5, 1, 0, 0, 1, 0, -1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from P315660.hc P315660.hV a P315660.ha _ _ 16 (by decide) (by decide) P315660.hgfw P315660.hsmall
