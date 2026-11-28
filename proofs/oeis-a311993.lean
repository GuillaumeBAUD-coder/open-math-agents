import OMAStatements.S_oeis_a311993
import Mathlib

/-!
Proof of the conjectured generating function and recurrence for A311993.

Method: an explicit distance certificate. Every vertex outside the origin cell lies on one of the
rays through the vertices of the growth polygon or in one of the cones between them (split into a
finite corner, two boundary strips and an interior), and is written as base + k T + j U with a base
from a finite list. The certificate gives the distance of each code as v + lT k + lU j, with step
costs lT, lU read off the growth polygon in each region. A Boolean checker, evaluated by the kernel,
verifies that every neighbour of a coded vertex has a code of value at most one more, that every
coded vertex other than the base vertex has a neighbour of value exactly one less, and that codes
are injective. So the ball of radius n (built from the neighbour table read off E) is the image of
the codes of value at most n, and the coordination sequence is a sum of explicit quasi-linear
counts, which satisfies both conjectures. The bridge to SimpleGraph.dist: the neighbour table has
the same members as the offsets of E in both directions, so the ball of radius n is the set of
vertices joined to v0 by a walk of length at most n; the graph is connected because translations
are automorphisms and explicit paths join v0 to every class and to its two lattice translates.
The certificate data was produced by a script.
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
  lT : ℕ
  lU : ℕ
  al : ℕ
  be : ℕ
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
def Region.dflt : Region m := ⟨0, 0, 0, 0, 0, [], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, []⟩
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

def val (r b k j : ℕ) : ℕ := (C.bas r b).v + (C.reg r).lT * k + (C.reg r).lU * j

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
  decide (R'.lT * t.ka + R'.lU * t.ja ≤ R.lT * kk) && decide (R'.lT * t.kb + R'.lU * t.jb ≤ R.lU * jj) &&
  decide (B'.v + R'.lT * t.kc + R'.lU * t.jc ≤ B.v + R.lT * kk + R.lU * jj + 1)

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
  decide (R'.lT * t.ka + R'.lU * t.ja = R.lT * kk) && decide (R'.lT * t.kb + R'.lU * t.jb = R.lU * jj) &&
  decide (B'.v + R'.lT * t.kc + R'.lU * t.jc + 1 = B.v + R.lT * kk + R.lU * jj)

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

/-- Step costs: a `T` step costs `lT`, a `U` step costs `lU`; `al` `T` steps and `be` `U` steps both cost
`al * lT`, which divides the global period `L`. -/
def okCost (L : ℕ) (R : Region m) : Bool :=
  (decide (R.kind = 0) || (decide (0 < R.lT) && decide (L % R.lT = 0))) &&
  (decide (R.kind ≤ 1) || (decide (0 < R.lU) && decide (0 < R.al) && decide (0 < R.be) &&
    decide (R.al * R.lT = R.be * R.lU) && decide (L % (R.al * R.lT) = 0)))

/-- Strict lexicographic order on base coordinates `(x, y, i)`. -/
def blt (a b : Base m) : Bool :=
  decide (a.x < b.x) || (decide (a.x = b.x) && (decide (a.y < b.y) ||
    (decide (a.y = b.y) && decide (a.i.val < b.i.val))))

/-- The bases of a region are listed in strictly increasing order, hence are distinct. -/
def sortedB : List (Base m) → Bool
  | a :: b :: l => blt a b && sortedB (b :: l)
  | _ => true

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
      C.okPred R B (kkOf c) (jjOf c) (C.expPred r R B (kkOf c) (jjOf c) (B.pred.getD c (.f Tgt.dflt))))

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
  (List.range C.regs.length).all (fun r => okRegCoord (C.reg r) && okCost C.L (C.reg r) && sortedB (C.reg r).bases &&
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

theorem aff_le {vB vB' a b a' b' ka kb kc ja jb jc kk jj K1 J1 : ℕ} (h1 : a' * ka + b' * ja ≤ a * kk)
    (h2 : a' * kb + b' * jb ≤ b * jj) (h3 : vB' + a' * kc + b' * jc ≤ vB + a * kk + b * jj + 1) :
    vB' + a' * (ka * K1 + kb * J1 + kc) + b' * (ja * K1 + jb * J1 + jc) ≤
      vB + a * (kk * K1 + kk) + b * (jj * J1 + jj) + 1 := by
  have e1 : vB' + a' * (ka * K1 + kb * J1 + kc) + b' * (ja * K1 + jb * J1 + jc) =
      (vB' + a' * kc + b' * jc) + K1 * (a' * ka + b' * ja) + J1 * (a' * kb + b' * jb) := by ring
  have e2 : vB + a * (kk * K1 + kk) + b * (jj * J1 + jj) + 1 =
      (vB + a * kk + b * jj + 1) + K1 * (a * kk) + J1 * (b * jj) := by ring
  rw [e1, e2]
  exact Nat.add_le_add (Nat.add_le_add h3 (Nat.mul_le_mul_left _ h1)) (Nat.mul_le_mul_left _ h2)

theorem aff_eq {vB vB' a b a' b' ka kb kc ja jb jc kk jj K1 J1 : ℕ} (h1 : a' * ka + b' * ja = a * kk)
    (h2 : a' * kb + b' * jb = b * jj) (h3 : vB' + a' * kc + b' * jc + 1 = vB + a * kk + b * jj) :
    vB' + a' * (ka * K1 + kb * J1 + kc) + b' * (ja * K1 + jb * J1 + jc) + 1 =
      vB + a * (kk * K1 + kk) + b * (jj * J1 + jj) := by
  have e1 : vB' + a' * (ka * K1 + kb * J1 + kc) + b' * (ja * K1 + jb * J1 + jc) + 1 =
      (vB' + a' * kc + b' * jc + 1) + K1 * (a' * ka + b' * ja) + J1 * (a' * kb + b' * jb) := by ring
  have e2 : vB + a * (kk * K1 + kk) + b * (jj * J1 + jj) =
      (vB + a * kk + b * jj) + K1 * (a * kk) + J1 * (b * jj) := by ring
  rw [e1, e2, h1, h2, h3]

structure Facts (C : Cfg m) : Prop where
  Lpos : 0 < C.L
  r0 : C.r0 < C.regs.length
  b0 : C.b0 < (C.reg C.r0).bases.length
  v0 : (C.bas C.r0 C.b0).v = 0
  d0 : C.dec C.r0 C.b0 0 0 = C.x0
  reg : ∀ r < C.regs.length, okRegCoord (C.reg r) = true
  cost : ∀ r < C.regs.length, okCost C.L (C.reg r) = true
  sorted : ∀ r < C.regs.length, sortedB (C.reg r).bases = true
  base : ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, C.okBase r b = true
  cert : ∀ r1 < C.regs.length, ∀ r2 < C.regs.length, r1 ≠ r2 → C.hasCert r1 r2 = true

theorem facts (hc : C.check = true) : Facts C := by
  unfold check at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have := all_range h6 hr
    simp only [Bool.and_eq_true] at this
    exact this.1.1.1
  · intro r hr
    have := all_range h6 hr
    simp only [Bool.and_eq_true] at this
    exact this.1.1.2
  · intro r hr
    have := all_range h6 hr
    simp only [Bool.and_eq_true] at this
    exact this.1.2
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
    True := by
  unfold okBase at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨hz, hco⟩, hk⟩, h0⟩, ho⟩, hp⟩ := h
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
  · trivial

theorem blt_trans {a b c : Base m} (h1 : blt a b = true) (h2 : blt b c = true) : blt a c = true := by
  unfold blt at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem blt_ne {a b : Base m} (h : blt a b = true) (hx : a.x = b.x) (hy : a.y = b.y) (hi : a.i = b.i) :
    False := by
  have hv : a.i.val = b.i.val := by rw [hi]
  unfold blt at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem sortedB_pairwise : ∀ l : List (Base m), sortedB l = true → l.Pairwise (fun a b => blt a b = true)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    have h' : blt a b = true ∧ sortedB (b :: l) = true := by simpa [sortedB] using h
    have ih := sortedB_pairwise (b :: l) h'.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h'.1
    · exact blt_trans h'.1 (List.rel_of_pairwise_cons ih hc)

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

theorem distinct_idx (hc : C.check = true) {r b b2 : ℕ} (hr : r < C.regs.length)
    (hb : b < (C.reg r).bases.length) (hb2 : b2 < (C.reg r).bases.length)
    (hx : (C.bas r b2).x = (C.bas r b).x) (hy : (C.bas r b2).y = (C.bas r b).y)
    (hi : (C.bas r b2).i = (C.bas r b).i) : b2 = b := by
  have hp := sortedB_pairwise _ ((facts C hc).sorted r hr)
  rw [List.pairwise_iff_getElem] at hp
  unfold bas at hx hy hi
  rw [List.getD_eq_getElem _ _ hb, List.getD_eq_getElem _ _ hb2] at hx hy hi
  rcases Nat.lt_trichotomy b2 b with h | h | h
  · exact (blt_ne (hp b2 b hb2 hb h) hx hy hi).elim
  · exact h
  · exact (blt_ne (hp b b2 hb hb2 h) hx.symm hy.symm hi.symm).elim

theorem dec_inj (hc : C.check = true) {r b k j r' b' k' j' : ℕ} (hv : C.Valid r b k j)
    (hv' : C.Valid r' b' k' j') (h : C.dec r b k j = C.dec r' b' k' j') :
    r = r' ∧ b = b' ∧ k = k' ∧ j = j' := by
  have F := facts C hc
  by_cases hr : r = r'
  · subst hr
    refine ⟨rfl, ?_⟩
    obtain ⟨hr, hb, hk1, hj1⟩ := hv
    obtain ⟨-, hb', hk1', hj1'⟩ := hv'
    obtain ⟨-, hco, hK, -, -, -, -⟩ := okBase_parts (F.base r hr b hb)
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
    exact (distinct_idx hc hr hb hb' (by linarith) (by linarith) hi.symm).symm
  · exfalso
    have z1 := zone_sound hc hv
    have z2 := zone_sound hc hv'
    rw [← h] at z2
    exact no_two_zones hc hv.1 hv'.1 hr _ _ z1 z2

theorem cost_parts {L : ℕ} {R : Region m} (h : okCost L R = true) :
    (R.kind = 0 ∨ (0 < R.lT ∧ L % R.lT = 0)) ∧
    (R.kind ≤ 1 ∨ (0 < R.lU ∧ 0 < R.al ∧ 0 < R.be ∧ R.al * R.lT = R.be * R.lU ∧
      L % (R.al * R.lT) = 0)) := by
  unfold okCost at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  tauto

theorem cost_of (hc : C.check = true) (r : ℕ) : okCost C.L (C.reg r) = true := by
  rcases Nat.lt_or_ge r C.regs.length with h | h
  · exact (facts C hc).cost r h
  · have e : C.reg r = Region.dflt := by unfold reg; exact List.getD_eq_default _ _ h
    rw [e]
    simp [okCost, Region.dflt]

theorem val_zero (hc : C.check = true) {r b k j : ℕ} (hv : C.Valid r b k j)
    (h0 : C.val r b k j = 0) : C.dec r b k j = C.x0 := by
  have F := facts C hc
  obtain ⟨hr, hb, hk1, hj1⟩ := hv
  obtain ⟨-, -, -, hz, -, -, -⟩ := okBase_parts (F.base r hr b hb)
  obtain ⟨c1, c2⟩ := cost_parts (cost_of hc r)
  unfold val at h0
  have hv0 : (C.bas r b).v = 0 := by omega
  have hk : k = 0 := by
    rcases hk1 with h | h
    · rcases c1 with h' | ⟨h', -⟩
      · omega
      · have e : (C.reg r).lT * k = 0 := by omega
        rcases Nat.mul_eq_zero.mp e with h'' | h''
        · omega
        · exact h''
    · exact h
  have hj : j = 0 := by
    rcases hj1 with h | h
    · rcases c2 with h' | ⟨h', -⟩
      · omega
      · have e : (C.reg r).lU * j = 0 := by omega
        rcases Nat.mul_eq_zero.mp e with h'' | h''
        · omega
        · exact h''
    · exact h
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

/-- The number of `(k, j)` with `w + M * (k + j) = n`. -/
def gcnt (M w n : ℕ) : ℕ := if w ≤ n ∧ M ∣ (n - w) then (n - w) / M + 1 else 0

/-- The number of codes of value `n` with base `B` in region `R`. -/
def pcB (R : Region m) (B : Base m) (n : ℕ) : ℕ :=
  if R.kind = 0 then (if B.v = n then 1 else 0)
  else if R.kind = 1 then
    (if B.v ≤ n ∧ R.lT ∣ (n - B.v) then 1 else 0)
  else ((List.range R.al).map (fun ρ => ((List.range R.be).map (fun σ =>
    gcnt (R.al * R.lT) (B.v + R.lT * ρ + R.lU * σ) n)).sum)).sum

def pcard (C : Cfg m) (r b n : ℕ) : ℕ := pcB (C.reg r) (C.bas r b) n

def A (C : Cfg m) (n : ℕ) : ℕ :=
  ((List.range C.regs.length).map (fun r =>
    ((List.range (C.reg r).bases.length).map (fun b => C.pcard r b n)).sum)).sum

/-- The same count, by a single pass over the data. -/
def Af (C : Cfg m) (n : ℕ) : ℕ :=
  (C.regs.map (fun R => (R.bases.map (fun B => pcB R B n)).sum)).sum

theorem map_range_getD {α β : Type} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun i => f (l.getD i d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have h3 : i < l.length := by simpa using h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ h3]

theorem Af_eq (C : Cfg m) (n : ℕ) : C.Af n = C.A n := by
  unfold Af A pcard bas reg
  rw [← map_range_getD C.regs Region.dflt]
  congr 1
  apply List.map_congr_left
  intro r _
  try dsimp only
  rw [← map_range_getD (C.regs.getD r Region.dflt).bases Base.dflt]

/-- Codes `(r, b, al * p + ρ, be * q + σ)` of value `n`, for one residue pair `(ρ, σ)`. -/
def sub (C : Cfg m) (r b n ρ σ : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  if (C.bas r b).v + (C.reg r).lT * ρ + (C.reg r).lU * σ ≤ n ∧
      (C.reg r).al * (C.reg r).lT ∣ (n - ((C.bas r b).v + (C.reg r).lT * ρ + (C.reg r).lU * σ)) then
    (Finset.HasAntidiagonal.antidiagonal ((n - ((C.bas r b).v + (C.reg r).lT * ρ + (C.reg r).lU * σ)) /
      ((C.reg r).al * (C.reg r).lT)) : Finset (ℕ × ℕ)).image
      (fun p => (r, b, (C.reg r).al * p.1 + ρ, (C.reg r).be * p.2 + σ))
  else ∅

def piece (C : Cfg m) (r b n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  if (C.reg r).kind = 0 then (if (C.bas r b).v = n then {(r, b, 0, 0)} else ∅)
  else if (C.reg r).kind = 1 then
    (if (C.bas r b).v ≤ n ∧ (C.reg r).lT ∣ (n - (C.bas r b).v) then
      {(r, b, (n - (C.bas r b).v) / (C.reg r).lT, 0)} else ∅)
  else (Finset.range (C.reg r).al).biUnion fun ρ => (Finset.range (C.reg r).be).biUnion fun σ =>
    C.sub r b n ρ σ

def Sph (C : Cfg m) (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range C.regs.length).biUnion fun r =>
    (Finset.range (C.reg r).bases.length).biUnion fun b => C.piece r b n

/-- The largest value `v + lT ρ + lU σ` of a residue class start. -/
def vtop (C : Cfg m) (r b : ℕ) : ℕ :=
  if (C.reg r).kind ≤ 1 then (C.bas r b).v
  else (C.bas r b).v + (C.reg r).lT * ((C.reg r).al - 1) + (C.reg r).lU * ((C.reg r).be - 1)

variable {C : Cfg m}

theorem val_iff {v L s n : ℕ} (hL : 0 < L) :
    v + L * s = n ↔ v ≤ n ∧ L ∣ (n - v) ∧ s = (n - v) / L := by
  constructor
  · rintro rfl
    refine ⟨by omega, ⟨s, by omega⟩, ?_⟩
    rw [show v + L * s - v = L * s by omega, Nat.mul_div_cancel_left _ hL]
  · rintro ⟨h1, h2, rfl⟩
    rw [Nat.mul_div_cancel' h2]; omega

theorem split_val {lT lU al be v k j : ℕ} (hM : al * lT = be * lU) :
    v + lT * k + lU * j = (v + lT * (k % al) + lU * (j % be)) + al * lT * (k / al + j / be) := by
  have e1 : lT * k = lT * (k % al) + al * lT * (k / al) := by
    conv_lhs => rw [← Nat.mod_add_div k al]
    ring
  have e2 : lU * j = lU * (j % be) + al * lT * (j / be) := by
    conv_lhs => rw [← Nat.mod_add_div j be]
    rw [hM]; ring
  rw [e1, e2]; ring

theorem arith_fwd {v lT lU al be ρ σ p1 p2 n : ℕ} (hM : al * lT = be * lU) (hMp : 0 < al * lT)
    (hw : v + lT * ρ + lU * σ ≤ n ∧ al * lT ∣ n - (v + lT * ρ + lU * σ))
    (hp : p1 + p2 = (n - (v + lT * ρ + lU * σ)) / (al * lT)) :
    v + lT * (al * p1 + ρ) + lU * (be * p2 + σ) = n := by
  have h2 : lU * (be * p2) = al * lT * p2 := by rw [hM]; ring
  have e : v + lT * (al * p1 + ρ) + lU * (be * p2 + σ) =
      (v + lT * ρ + lU * σ) + al * lT * (p1 + p2) := by
    calc v + lT * (al * p1 + ρ) + lU * (be * p2 + σ)
        = (v + lT * ρ + lU * σ) + al * lT * p1 + lU * (be * p2) := by ring
      _ = (v + lT * ρ + lU * σ) + al * lT * (p1 + p2) := by rw [h2]; ring
  rw [e]
  exact (val_iff hMp).mpr ⟨hw.1, hw.2, hp⟩

theorem kind2_facts (hc : C.check = true) {r : ℕ} (h0 : ¬ (C.reg r).kind = 0) (h1 : ¬ (C.reg r).kind = 1) :
    0 < (C.reg r).lT ∧ 0 < (C.reg r).al ∧ 0 < (C.reg r).be ∧
      (C.reg r).al * (C.reg r).lT = (C.reg r).be * (C.reg r).lU ∧ C.L % ((C.reg r).al * (C.reg r).lT) = 0 := by
  obtain ⟨c1, c2⟩ := cost_parts (cost_of hc r)
  rcases c1 with h | ⟨hT, -⟩
  · exact absurd h h0
  rcases c2 with h | ⟨-, ha, hb, hM, hL⟩
  · omega
  exact ⟨hT, ha, hb, hM, hL⟩

theorem kind1_facts (hc : C.check = true) {r : ℕ} (h0 : ¬ (C.reg r).kind = 0) :
    0 < (C.reg r).lT ∧ C.L % (C.reg r).lT = 0 := by
  obtain ⟨c1, -⟩ := cost_parts (cost_of hc r)
  rcases c1 with h | h
  · exact absurd h h0
  · exact h

theorem mem_piece (hc : C.check = true) {r b n r' b' k j : ℕ} :
    (r', b', k, j) ∈ C.piece r b n ↔ r' = r ∧ b' = b ∧ (1 ≤ (C.reg r).kind ∨ k = 0) ∧
      (2 ≤ (C.reg r).kind ∨ j = 0) ∧ C.val r b k j = n := by
  unfold piece val
  by_cases h0 : (C.reg r).kind = 0
  · rw [if_pos h0]
    by_cases h1 : (C.bas r b).v = n
    · rw [if_pos h1, Finset.mem_singleton]
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨rfl, rfl, Or.inr rfl, Or.inr rfl, by simp [h1]⟩
      · rintro ⟨rfl, rfl, hk, hj, hv⟩
        have hk' : k = 0 := by omega
        have hj' : j = 0 := by omega
        exact ⟨rfl, rfl, hk', hj'⟩
    · rw [if_neg h1]
      simp only [Finset.notMem_empty, false_iff]
      rintro ⟨rfl, rfl, hk, hj, hv⟩
      have hk' : k = 0 := by omega
      have hj' : j = 0 := by omega
      subst hk' hj'
      simp at hv
      exact h1 hv
  rw [if_neg h0]
  by_cases h2 : (C.reg r).kind = 1
  · obtain ⟨hT, -⟩ := kind1_facts hc h0
    rw [if_pos h2]
    by_cases h1 : (C.bas r b).v ≤ n ∧ (C.reg r).lT ∣ (n - (C.bas r b).v)
    · rw [if_pos h1, Finset.mem_singleton]
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl, rfl⟩
        refine ⟨rfl, rfl, Or.inl (by omega), Or.inr rfl, ?_⟩
        rw [mul_zero, add_zero]
        exact (val_iff hT).mpr ⟨h1.1, h1.2, rfl⟩
      · rintro ⟨rfl, rfl, hk, hj, hv⟩
        have hj' : j = 0 := by omega
        subst hj'
        rw [mul_zero, add_zero] at hv
        exact ⟨rfl, rfl, ((val_iff hT).mp hv).2.2, rfl⟩
    · rw [if_neg h1]
      simp only [Finset.notMem_empty, false_iff]
      rintro ⟨rfl, rfl, -, hj, hv⟩
      have hj' : j = 0 := by omega
      subst hj'
      rw [mul_zero, add_zero] at hv
      have := (val_iff hT).mp hv
      exact h1 ⟨this.1, this.2.1⟩
  rw [if_neg h2]
  obtain ⟨hT, hal, hbe, hM, -⟩ := kind2_facts hc h0 h2
  have hMp : 0 < (C.reg r).al * (C.reg r).lT := Nat.mul_pos hal hT
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨ρ, hρ, σ, hσ, hmem⟩
    unfold sub at hmem
    split_ifs at hmem with hw
    · rw [Finset.mem_image] at hmem
      obtain ⟨⟨p1, p2⟩, hp, he⟩ := hmem
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      exact ⟨rfl, rfl, Or.inl (by omega), Or.inl (by omega), arith_fwd hM hMp hw hp⟩
    · simp at hmem
  · rintro ⟨h1, h2, -, -, hv⟩
    rw [h1, h2]
    refine ⟨k % (C.reg r).al, Nat.mod_lt _ hal, j % (C.reg r).be, Nat.mod_lt _ hbe, ?_⟩
    rw [split_val hM] at hv
    have hb := (val_iff hMp).mp hv
    unfold sub
    rw [if_pos (And.intro hb.1 hb.2.1), Finset.mem_image]
    refine ⟨(k / (C.reg r).al, j / (C.reg r).be), Finset.HasAntidiagonal.mem_antidiagonal.mpr hb.2.2, ?_⟩
    simp only [Nat.div_add_mod]

theorem mem_Sph (hc : C.check = true) {n r b k j : ℕ} :
    (r, b, k, j) ∈ C.Sph n ↔ C.Valid r b k j ∧ C.val r b k j = n := by
  unfold Sph Valid
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨r', hr', b', hb', h⟩
    obtain ⟨rfl, rfl, hk, hj, hv⟩ := (mem_piece hc).mp h
    exact ⟨⟨hr', hb', hk, hj⟩, hv⟩
  · rintro ⟨⟨hr, hb, hk, hj⟩, hv⟩
    exact ⟨r, hr, b, hb, (mem_piece hc).mpr ⟨rfl, rfl, hk, hj, hv⟩⟩

theorem piece_fst (hc : C.check = true) {r b n : ℕ} {c : ℕ × ℕ × ℕ × ℕ} (h : c ∈ C.piece r b n) :
    c.1 = r ∧ c.2.1 = b := by
  obtain ⟨r', b', k, j⟩ := c
  have := (mem_piece hc).mp h
  exact ⟨this.1, this.2.1⟩

theorem mem_sub {r b n ρ σ : ℕ} {c : ℕ × ℕ × ℕ × ℕ} (hρ : ρ < (C.reg r).al) (hσ : σ < (C.reg r).be)
    (h : c ∈ C.sub r b n ρ σ) : c.2.2.1 % (C.reg r).al = ρ ∧ c.2.2.2 % (C.reg r).be = σ := by
  unfold sub at h
  split_ifs at h
  · rw [Finset.mem_image] at h
    obtain ⟨p, -, rfl⟩ := h
    simp only
    constructor
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hσ]
  · simp at h

theorem card_sub {r b n ρ σ : ℕ} (hal : 0 < (C.reg r).al) (hbe : 0 < (C.reg r).be) :
    (C.sub r b n ρ σ).card = gcnt ((C.reg r).al * (C.reg r).lT)
      ((C.bas r b).v + (C.reg r).lT * ρ + (C.reg r).lU * σ) n := by
  unfold sub gcnt
  split_ifs with hw
  · rw [Finset.card_image_of_injective]
    · simp
    · intro p q h
      have h1 := congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.1) h
      have h2 := congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.2) h
      simp only at h1 h2
      exact Prod.ext (Nat.eq_of_mul_eq_mul_left hal (Nat.add_right_cancel h1))
        (Nat.eq_of_mul_eq_mul_left hbe (Nat.add_right_cancel h2))
  · rfl

theorem lsum_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

theorem card_piece (hc : C.check = true) (r b n : ℕ) : (C.piece r b n).card = C.pcard r b n := by
  unfold piece pcard pcB
  by_cases h0 : (C.reg r).kind = 0
  · rw [if_pos h0, if_pos h0]
    split_ifs <;> simp
  rw [if_neg h0, if_neg h0]
  by_cases h2 : (C.reg r).kind = 1
  · rw [if_pos h2, if_pos h2]
    split_ifs <;> simp
  rw [if_neg h2, if_neg h2]
  obtain ⟨-, hal, hbe, -, -⟩ := kind2_facts hc h0 h2
  rw [Finset.card_biUnion, lsum_range]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [Finset.mem_range] at hρ
    rw [Finset.card_biUnion, lsum_range]
    · apply Finset.sum_congr rfl
      intro σ _
      exact card_sub hal hbe
    · intro s1 hs1 s2 hs2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro c h1 h2
      have hs1' : s1 < (C.reg r).be := by simpa using hs1
      have hs2' : s2 < (C.reg r).be := by simpa using hs2
      exact hne ((mem_sub hρ hs1' h1).2.symm.trans (mem_sub hρ hs2' h2).2)
  · intro r1 hr1 r2 hr2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro c h1 h2
    have hr1' : r1 < (C.reg r).al := by simpa using hr1
    have hr2' : r2 < (C.reg r).al := by simpa using hr2
    simp only [Finset.mem_biUnion, Finset.mem_range] at h1 h2
    obtain ⟨s1, hs1, h1⟩ := h1
    obtain ⟨s2, hs2, h2⟩ := h2
    exact hne ((mem_sub hr1' hs1 h1).1.symm.trans (mem_sub hr2' hs2 h2).1)

theorem card_Sph (hc : C.check = true) (n : ℕ) : (C.Sph n).card = C.A n := by
  unfold Sph A
  rw [Finset.card_biUnion, lsum_range]
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.card_biUnion, lsum_range]
    · apply Finset.sum_congr rfl
      intro b _
      exact card_piece hc r b n
    · intro b1 _ b2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro c h1 h2
      exact hne ((piece_fst hc h1).2.symm.trans (piece_fst hc h2).2)
  · intro r1 _ r2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro c h1 h2
    simp only [Finset.mem_biUnion] at h1 h2
    obtain ⟨b1, -, h1⟩ := h1
    obtain ⟨b2, -, h2⟩ := h2
    exact hne ((piece_fst hc h1).1.symm.trans (piece_fst hc h2).1)

theorem ball_mono (n : ℕ) : ball C.adj C.x0 n ⊆ ball C.adj C.x0 (n + 1) := by
  intro x hx
  simp only [ball, Finset.mem_union]
  exact Or.inl hx

theorem sphere_eq (hc : C.check = true) (n : ℕ) :
    ball C.adj C.x0 (n + 1) \ ball C.adj C.x0 n =
      (C.Sph (n + 1)).image (fun c => C.dec c.1 c.2.1 c.2.2.1 c.2.2.2) := by
  ext x
  rw [Finset.mem_sdiff, Finset.mem_image, ball_iff hc, ball_iff hc]
  constructor
  · rintro ⟨⟨r, b, k, j, hv, hle, rfl⟩, hn⟩
    refine ⟨(r, b, k, j), (mem_Sph hc).mpr ⟨hv, ?_⟩, rfl⟩
    by_contra hne
    exact hn ⟨r, b, k, j, hv, by omega, rfl⟩
  · rintro ⟨⟨r, b, k, j⟩, hc', rfl⟩
    obtain ⟨hv, hval⟩ := (mem_Sph hc).mp hc'
    refine ⟨⟨r, b, k, j, hv, hval.le, rfl⟩, ?_⟩
    rintro ⟨r', b', k', j', hv', hle, hd⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := dec_inj hc hv' hv hd
    omega

theorem card_step (hc : C.check = true) (n : ℕ) :
    ((ball C.adj C.x0 (n + 1)).card : ℤ) - (ball C.adj C.x0 n).card = C.A (n + 1) := by
  have h1 := Finset.card_sdiff_add_card_eq_card (ball_mono (C := C) n)
  have h2 : (ball C.adj C.x0 (n + 1) \ ball C.adj C.x0 n).card = C.A (n + 1) := by
    rw [sphere_eq hc, Finset.card_image_of_injOn, card_Sph hc]
    rintro ⟨r, b, k, j⟩ h1 ⟨r', b', k', j'⟩ h2 hd
    obtain ⟨hv, -⟩ := (mem_Sph hc).mp h1
    obtain ⟨hv', -⟩ := (mem_Sph hc).mp h2
    obtain ⟨rfl, rfl, rfl, rfl⟩ := dec_inj hc hv hv' hd
    rfl
  omega

theorem gcnt_rec {M w L n : ℕ} (hM : 0 < M) (hML : M ∣ L) (hw : w ≤ n) :
    gcnt M w (n + 2 * L) + gcnt M w n = 2 * gcnt M w (n + L) := by
  obtain ⟨c, rfl⟩ := hML
  unfold gcnt
  have e2 : n + 2 * (M * c) - w = (n - w) + M * (2 * c) := by
    rw [show M * (2 * c) = 2 * (M * c) by ring]; omega
  have e1 : n + M * c - w = (n - w) + M * c := by omega
  rw [e2, e1]
  have d2 : M ∣ (n - w) + M * (2 * c) ↔ M ∣ (n - w) := Nat.dvd_add_left (Dvd.intro _ rfl)
  have d1 : M ∣ (n - w) + M * c ↔ M ∣ (n - w) := Nat.dvd_add_left (Dvd.intro _ rfl)
  have q2 : ((n - w) + M * (2 * c)) / M = (n - w) / M + 2 * c := Nat.add_mul_div_left _ _ hM
  have q1 : ((n - w) + M * c) / M = (n - w) / M + c := Nat.add_mul_div_left _ _ hM
  have t2 : w ≤ n + 2 * (M * c) := by omega
  have t1 : w ≤ n + M * c := by omega
  simp only [d2, d1, q2, q1, t2, t1, hw, true_and]
  split_ifs <;> omega

theorem v_le_vtop (r b : ℕ) : (C.bas r b).v ≤ C.vtop r b := by
  unfold vtop; split_ifs <;> omega

theorem pcard_rec (hc : C.check = true) {r b n : ℕ} (hv : C.vtop r b < n) :
    C.pcard r b (n + 2 * C.L) + C.pcard r b n = 2 * C.pcard r b (n + C.L) := by
  have hvn : (C.bas r b).v < n := lt_of_le_of_lt (v_le_vtop r b) hv
  unfold pcard pcB
  by_cases h0 : (C.reg r).kind = 0
  · rw [if_pos h0, if_pos h0, if_pos h0]
    split_ifs <;> omega
  rw [if_neg h0, if_neg h0, if_neg h0]
  by_cases h2 : (C.reg r).kind = 1
  · rw [if_pos h2, if_pos h2, if_pos h2]
    obtain ⟨hT, hL⟩ := kind1_facts hc h0
    have hd : (C.reg r).lT ∣ C.L := Nat.dvd_of_mod_eq_zero hL
    have e2 : n + 2 * C.L - (C.bas r b).v = (n - (C.bas r b).v) + 2 * C.L := by omega
    have e1 : n + C.L - (C.bas r b).v = (n - (C.bas r b).v) + C.L := by omega
    rw [e2, e1]
    have d2 : (C.reg r).lT ∣ (n - (C.bas r b).v) + 2 * C.L ↔ (C.reg r).lT ∣ (n - (C.bas r b).v) :=
      Nat.dvd_add_left (Dvd.dvd.mul_left hd 2)
    have d1 : (C.reg r).lT ∣ (n - (C.bas r b).v) + C.L ↔ (C.reg r).lT ∣ (n - (C.bas r b).v) :=
      Nat.dvd_add_left hd
    have t2 : (C.bas r b).v ≤ n + 2 * C.L := by omega
    have t1 : (C.bas r b).v ≤ n + C.L := by omega
    have t0 : (C.bas r b).v ≤ n := by omega
    simp only [d2, d1, t2, t1, t0, true_and]
    split_ifs <;> omega
  rw [if_neg h2, if_neg h2, if_neg h2]
  obtain ⟨hT, hal, hbe, -, hL⟩ := kind2_facts hc h0 h2
  have hd : (C.reg r).al * (C.reg r).lT ∣ C.L := Nat.dvd_of_mod_eq_zero hL
  have hMp : 0 < (C.reg r).al * (C.reg r).lT := Nat.mul_pos hal hT
  have hk1 : ¬ (C.reg r).kind ≤ 1 := by omega
  unfold vtop at hv
  rw [if_neg hk1] at hv
  rw [← List.sum_map_add, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro ρ hρ
  rw [List.mem_range] at hρ
  rw [← List.sum_map_add, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro σ hσ
  rw [List.mem_range] at hσ
  apply gcnt_rec hMp hd
  have a1 : (C.reg r).lT * ρ ≤ (C.reg r).lT * ((C.reg r).al - 1) := Nat.mul_le_mul_left _ (by omega)
  have a2 : (C.reg r).lU * σ ≤ (C.reg r).lU * ((C.reg r).be - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem A_rec (hc : C.check = true) {V : ℕ}
    (hV : ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, C.vtop r b ≤ V) {n : ℕ}
    (hn : V < n) : C.A (n + 2 * C.L) + C.A n = 2 * C.A (n + C.L) := by
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
  exact pcard_rec hc (lt_of_le_of_lt (hV r hr b hb) hn)

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
    (List.range (C.reg r).bases.length).all (fun b => decide (C.vtop r b ≤ V)))

theorem vbound_spec {V : ℕ} (h : C.vbound V = true) :
    ∀ r < C.regs.length, ∀ b < (C.reg r).bases.length, C.vtop r b ≤ V := by
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

namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem A_of_list {N : ℕ} {Av : List ℕ} (hAv : (List.range N).map C.Af = Av) {n : ℕ} (hn : n < N) :
    C.A n = Av.getD n 0 := by
  have h3 : n < ((List.range N).map C.Af).length := by simpa using hn
  rw [← hAv, ← Af_eq, List.getD_eq_getElem _ _ h3]
  simp

theorem window_of_list {N : ℕ} {Av : List ℕ} (hAv : (List.range N).map C.Af = Av) (cs : List (ℤ × ℕ))
    (W : ℕ) (hN : ∀ p ∈ cs, W + p.2 ≤ N)
    (hw : ∀ n < W, (cs.map fun p => p.1 * (Av.getD (n + p.2) 0 : ℤ)).sum = 0) :
    ∀ n < W, (cs.map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0 := by
  intro n hn
  refine Eq.trans ?_ (hw n hn)
  congr 1
  apply List.map_congr_left
  intro p hp
  have hlt : n + p.2 < N := by have := hN p hp; omega
  rw [A_of_list hAv hlt]

end Cfg
end GalCert

namespace GalCert
namespace Cfg
variable {m : ℕ} [NeZero m] (C : Cfg m)

/-- The global part of `check`. -/
def head : Bool :=
  decide (0 < C.L) &&
  decide (C.r0 < C.regs.length) && decide (C.b0 < (C.reg C.r0).bases.length) &&
  decide ((C.bas C.r0 C.b0).v = 0) && decide (C.dec C.r0 C.b0 0 0 = C.x0)

/-- The part of `check` for one region. -/
def regOk (r : ℕ) : Bool :=
  okRegCoord (C.reg r) && okCost C.L (C.reg r) && sortedB (C.reg r).bases &&
    (List.range (C.reg r).bases.length).all (fun b => C.okBase r b)

/-- The zone certificates for one source region. -/
def certRow (r1 : ℕ) : Bool :=
  (List.range C.regs.length).all (fun r2 => decide (r1 = r2) || C.hasCert r1 r2)

theorem check_eq : C.check =
    (C.head && (List.range C.regs.length).all C.regOk && (List.range C.regs.length).all C.certRow) := rfl

/-- `check` from its parts, so that the kernel can evaluate each part in its own declaration. -/
theorem check_of_parts (hh : C.head = true) (hr : ∀ r < C.regs.length, C.regOk r = true)
    (hc : ∀ r < C.regs.length, C.certRow r = true) : C.check = true := by
  rw [check_eq]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact ⟨⟨hh, fun r h => hr r h⟩, fun r h => hc r h⟩

/-- Two consecutive blocks of a mapped range, for evaluating `Af` table chunks in separate declarations. -/
theorem rmap_app (f : ℕ → ℕ) (a b c : ℕ) {l1 l2 : List ℕ} (h1 : (List.range' a b).map f = l1)
    (h2 : (List.range' (a + b) c).map f = l2) : (List.range' a (b + c)).map f = l1 ++ l2 := by
  subst h1 h2
  rw [← List.map_append, List.range'_append_1]

end Cfg
end GalCert



/-! ### From the cell edge list to the graph distance -/

namespace SGB

variable {m : ℕ}

/-- The cell edge relation, as in the statement. -/
def Rel (E : List (Fin m × Fin m × ℤ × ℤ)) (u v : ℤ × ℤ × Fin m) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The neighbour offsets of class `s`, read off `E` in both directions. -/
def adjE (E : List (Fin m × Fin m × ℤ × ℤ)) (s : Fin m) : List (ℤ × ℤ × Fin m) :=
  (E.filter (fun e => decide (e.1 = s))).map (fun e => (e.2.2.1, e.2.2.2, e.2.1)) ++
    (E.filter (fun e => decide (e.2.1 = s))).map (fun e => (-e.2.2.1, -e.2.2.2, e.1))

theorem rel_iff (E : List (Fin m × Fin m × ℤ × ℤ)) (u v : ℤ × ℤ × Fin m) :
    (Rel E u v ∨ Rel E v u) ↔ ∃ d ∈ adjE E u.2.2, v = GalCert.sh u d := by
  obtain ⟨x, y, s⟩ := u
  obtain ⟨x', y', s'⟩ := v
  simp only [Rel, adjE, GalCert.sh, List.mem_append, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro (⟨⟨a, b, dx, dy⟩, he, h1, h2, h3, h4⟩ | ⟨⟨a, b, dx, dy⟩, he, h1, h2, h3, h4⟩)
    · exact ⟨(dx, dy, b), Or.inl ⟨(a, b, dx, dy), ⟨he, h1.symm⟩, rfl⟩, h3, h4, h2⟩
    · exact ⟨(-dx, -dy, a), Or.inr ⟨(a, b, dx, dy), ⟨he, h2.symm⟩, rfl⟩, by simp only at h3 ⊢; omega,
        by simp only at h4 ⊢; omega, h1⟩
  · rintro ⟨d, (⟨⟨a, b, dx, dy⟩, ⟨he, h1⟩, rfl⟩ | ⟨⟨a, b, dx, dy⟩, ⟨he, h1⟩, rfl⟩), h2, h3, h4⟩
    · exact Or.inl ⟨(a, b, dx, dy), he, h1.symm, h4, h2, h3⟩
    · refine Or.inr ⟨(a, b, dx, dy), he, h4, h1.symm, ?_, ?_⟩
      · simp only at h2 ⊢; omega
      · simp only at h3 ⊢; omega

theorem mem_nbrs_iff (adj : Fin m → List (ℤ × ℤ × Fin m)) (u v : ℤ × ℤ × Fin m) :
    v ∈ GalCert.nbrs adj u ↔ ∃ d ∈ adj u.2.2, v = GalCert.sh u d := by
  unfold GalCert.nbrs GalCert.sh
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩

/-- Two offset tables with the same members. -/
def sameAdj (A B : Fin m → List (ℤ × ℤ × Fin m)) : Bool :=
  (List.finRange m).all fun s => (A s).all (fun d => decide (d ∈ B s)) && (B s).all (fun d => decide (d ∈ A s))

theorem sameAdj_mem {A B : Fin m → List (ℤ × ℤ × Fin m)} (h : sameAdj A B = true) (s : Fin m)
    (d : ℤ × ℤ × Fin m) : d ∈ A s ↔ d ∈ B s := by
  simp only [sameAdj, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h s (List.mem_finRange s)
  exact ⟨fun hd => h1 d hd, fun hd => h2 d hd⟩

section Graph

variable {G : SimpleGraph (ℤ × ℤ × Fin m)} {adj : Fin m → List (ℤ × ℤ × Fin m)}

/-- The hypotheses tying the graph to the offset table. -/
structure Tie (G : SimpleGraph (ℤ × ℤ × Fin m)) (adj : Fin m → List (ℤ × ℤ × Fin m)) : Prop where
  fwd : ∀ u v, G.Adj u v → v ∈ GalCert.nbrs adj u
  bwd : ∀ u v, v ∈ GalCert.nbrs adj u → G.Adj u v ∨ u = v

theorem tie_of (E : List (Fin m × Fin m × ℤ × ℤ))
    (hG : ∀ u v, G.Adj u v ↔ u ≠ v ∧ (Rel E u v ∨ Rel E v u))
    (hA : sameAdj adj (adjE E) = true) : Tie G adj := by
  constructor
  · intro u v h
    obtain ⟨d, hd, rfl⟩ := (rel_iff E u v).mp ((hG u v).mp h).2
    exact (mem_nbrs_iff adj u _).mpr ⟨d, (sameAdj_mem hA _ d).mpr hd, rfl⟩
  · intro u v h
    obtain ⟨d, hd, rfl⟩ := (mem_nbrs_iff adj u v).mp h
    by_cases hne : u = GalCert.sh u d
    · exact Or.inr hne
    · exact Or.inl ((hG u _).mpr ⟨hne, (rel_iff E u _).mpr ⟨d, (sameAdj_mem hA _ d).mp hd, rfl⟩⟩)

theorem ball_mono_le (x0 : ℤ × ℤ × Fin m) {k n : ℕ} (h : k ≤ n) :
    GalCert.ball adj x0 k ⊆ GalCert.ball adj x0 n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    refine ih.trans ?_
    intro x hx
    simp only [GalCert.ball, Finset.mem_union]
    exact Or.inl hx

theorem walk_mem (hT : Tie G adj) {x y : ℤ × ℤ × Fin m} (p : G.Walk x y) :
    x ∈ GalCert.ball adj y p.length := by
  induction p with
  | nil => simp [GalCert.ball]
  | cons h q ih =>
    rw [SimpleGraph.Walk.length_cons]
    simp only [GalCert.ball, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inr ⟨_, ih, hT.fwd _ _ h.symm⟩

theorem mem_walk (hT : Tie G adj) (x0 : ℤ × ℤ × Fin m) :
    ∀ n x, x ∈ GalCert.ball adj x0 n → ∃ p : G.Walk x0 x, p.length ≤ n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [GalCert.ball, Finset.mem_singleton] at hx
    subst hx
    exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
  | succ n ih =>
    intro x hx
    simp only [GalCert.ball, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨y, hy, hxy⟩
    · obtain ⟨p, hp⟩ := ih x hx
      exact ⟨p, by omega⟩
    · obtain ⟨p, hp⟩ := ih y hy
      rcases hT.bwd y x hxy with h | rfl
      · exact ⟨p.concat h, by rw [SimpleGraph.Walk.length_concat]; omega⟩
      · exact ⟨p, by omega⟩

theorem mem_ball_iff (hT : Tie G adj) (x0 x : ℤ × ℤ × Fin m) (n : ℕ) :
    x ∈ GalCert.ball adj x0 n ↔ G.Reachable x0 x ∧ G.dist x0 x ≤ n := by
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := mem_walk hT x0 n x hx
    exact ⟨⟨p⟩, (SimpleGraph.dist_le p).trans hp⟩
  · rintro ⟨hr, hd⟩
    obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
    have h1 := walk_mem hT p
    rw [hp, SimpleGraph.dist_comm] at h1
    exact ball_mono_le x0 hd h1

theorem ncard_succ (hT : Tie G adj) (x0 : ℤ × ℤ × Fin m) (n : ℕ) :
    ((Set.ncard {v | G.dist x0 v = n + 1} : ℕ) : ℤ) =
      ((GalCert.ball adj x0 (n + 1)).card : ℤ) - (GalCert.ball adj x0 n).card := by
  have hs : {v | G.dist x0 v = n + 1} = ↑(GalCert.ball adj x0 (n + 1) \ GalCert.ball adj x0 n) := by
    ext v
    simp only [Set.mem_setOf_eq, Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe, mem_ball_iff hT]
    constructor
    · intro h
      have hr : G.Reachable x0 v := by
        by_contra hn
        rw [SimpleGraph.dist_eq_zero_of_not_reachable hn] at h
        omega
      exact ⟨⟨hr, h.le⟩, fun h2 => by omega⟩
    · rintro ⟨⟨hr, h1⟩, h2⟩
      have : ¬ G.dist x0 v ≤ n := fun h => h2 ⟨hr, h⟩
      omega
  rw [hs, Set.ncard_coe_finset, Finset.card_sdiff_of_subset (ball_mono_le x0 (by omega : n ≤ n + 1))]
  have := Finset.card_le_card (ball_mono_le (adj := adj) x0 (by omega : n ≤ n + 1))
  omega

theorem ncard_zero (x0 : ℤ × ℤ × Fin m) (hR : ∀ v, G.Reachable x0 v) :
    Set.ncard {v | G.dist x0 v = 0} = 1 := by
  have hs : {v | G.dist x0 v = 0} = {x0} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, (hR v).dist_eq_zero_iff]
    exact eq_comm
  rw [hs, Set.ncard_singleton]

/-- A path through the listed vertices, each a neighbour of the previous one. -/
def pathOk (adj : Fin m → List (ℤ × ℤ × Fin m)) :
    (ℤ × ℤ × Fin m) → (ℤ × ℤ × Fin m) → List (ℤ × ℤ × Fin m) → Bool
  | u, w, [] => decide (u = w)
  | u, w, v :: l => (adj u.2.2).any (fun d => decide (GalCert.sh u d = v)) && pathOk adj v w l

theorem reach_of_path (hT : Tie G adj) :
    ∀ (l : List (ℤ × ℤ × Fin m)) (u w : ℤ × ℤ × Fin m), pathOk adj u w l = true → G.Reachable u w := by
  intro l
  induction l with
  | nil =>
    intro u w h
    simp only [pathOk, decide_eq_true_eq] at h
    subst h
    exact SimpleGraph.Reachable.refl _
  | cons v l ih =>
    intro u w h
    simp only [pathOk, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨d, hd, hv⟩, h2⟩ := h
    have hn : v ∈ GalCert.nbrs adj u := (mem_nbrs_iff adj u v).mpr ⟨d, hd, hv.symm⟩
    refine SimpleGraph.Reachable.trans ?_ (ih v w h2)
    rcases hT.bwd u v hn with h | rfl
    · exact h.reachable
    · exact SimpleGraph.Reachable.refl _

/-- Translation of the lattice. -/
def tr (a b : ℤ) (u : ℤ × ℤ × Fin m) : ℤ × ℤ × Fin m := (u.1 + a, u.2.1 + b, u.2.2)

theorem rel_tr (E : List (Fin m × Fin m × ℤ × ℤ)) (a b : ℤ) {u v : ℤ × ℤ × Fin m} (h : Rel E u v) :
    Rel E (tr a b u) (tr a b v) := by
  obtain ⟨e, he, h1, h2, h3, h4⟩ := h
  exact ⟨e, he, h1, h2, by simp only [tr]; omega, by simp only [tr]; omega⟩

theorem reach_tr (E : List (Fin m × Fin m × ℤ × ℤ))
    (hG : ∀ u v, G.Adj u v ↔ u ≠ v ∧ (Rel E u v ∨ Rel E v u)) (a b : ℤ) {u v : ℤ × ℤ × Fin m}
    (h : G.Reachable u v) : G.Reachable (tr a b u) (tr a b v) := by
  let f : G →g G :=
    { toFun := tr a b
      map_rel' := by
        intro u v huv
        obtain ⟨hne, hr⟩ := (hG u v).mp huv
        refine (hG _ _).mpr ⟨?_, hr.imp (rel_tr E a b) (rel_tr E a b)⟩
        intro heq
        apply hne
        obtain ⟨u1, u2, u3⟩ := u
        obtain ⟨v1, v2, v3⟩ := v
        simp only [tr, Prod.mk.injEq] at heq
        obtain ⟨h1, h2, h3⟩ := heq
        rw [show u1 = v1 by omega, show u2 = v2 by omega, h3] }
  exact h.map f

theorem connected (E : List (Fin m × Fin m × ℤ × ℤ))
    (hG : ∀ u v, G.Adj u v ↔ u ≠ v ∧ (Rel E u v ∨ Rel E v u)) (i0 : Fin m)
    (hs : ∀ s, G.Reachable (0, 0, i0) (0, 0, s)) (hx : G.Reachable (0, 0, i0) (1, 0, i0))
    (hy : G.Reachable (0, 0, i0) (0, 1, i0)) : ∀ v, G.Reachable (0, 0, i0) v := by
  have stepx : ∀ x y : ℤ, G.Reachable (x, y, i0) (x + 1, y, i0) := by
    intro x y
    have := reach_tr E hG x y hx
    simpa [tr, add_comm] using this
  have stepy : ∀ x y : ℤ, G.Reachable (x, y, i0) (x, y + 1, i0) := by
    intro x y
    have := reach_tr E hG x y hy
    simpa [tr, add_comm] using this
  have hcell : ∀ x y : ℤ, G.Reachable (0, 0, i0) (x, y, i0) := by
    intro x y
    have h0 : G.Reachable (0, 0, i0) (x, 0, i0) := by
      induction x using Int.induction_on with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ i ih => exact ih.trans (stepx _ _)
      | pred i ih =>
        refine ih.trans ?_
        have := stepx (-(i : ℤ) - 1) 0
        rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at this
        exact this.symm
    induction y using Int.induction_on with
    | zero => exact h0
    | succ i ih => exact ih.trans (stepy _ _)
    | pred i ih =>
      refine ih.trans ?_
      have := stepy x (-(i : ℤ) - 1)
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at this
      exact this.symm
  rintro ⟨x, y, s⟩
  refine (hcell x y).trans ?_
  have := reach_tr E hG x y (hs s)
  simpa [tr] using this

end Graph

end SGB


namespace P311993
open OMA.S_oeis_a311993

def adjL : Fin 9 → List (ℤ × ℤ × Fin 9) := ![
  [(-1, 0, 0), (1, 0, 0), (0, -1, 1), (0, 0, 2)],
  [(0, 1, 0), (-1, 0, 1), (1, 0, 1), (0, 0, 3)],
  [(0, 0, 0), (-1, 0, 2), (1, 0, 2), (0, 0, 4)],
  [(0, 0, 1), (-1, 0, 3), (1, 0, 3), (0, 0, 5)],
  [(0, 0, 2), (-1, 0, 4), (1, 0, 4), (0, 0, 6)],
  [(0, 0, 3), (-1, 0, 5), (1, 0, 5), (-1, 0, 7), (0, 0, 7)],
  [(0, 0, 4), (-1, 0, 6), (1, 0, 6), (-1, 0, 8), (0, 0, 8)],
  [(0, 0, 5), (1, 0, 5), (-1, 0, 7), (1, 0, 7), (0, 0, 8)],
  [(0, 0, 6), (1, 0, 6), (0, 0, 7), (-1, 0, 8), (1, 0, 8)]]

theorem hsame : SGB.sameAdj adjL (SGB.adjE E) = true := by decide +kernel

theorem hG : ∀ u v, G.Adj u v ↔ u ≠ v ∧ (SGB.Rel E u v ∨ SGB.Rel E v u) :=
  fun u v => SimpleGraph.fromRel_adj R u v

theorem hT : SGB.Tie G adjL := SGB.tie_of E hG hsame

theorem pth0 : SGB.pathOk adjL (0, 0, 1) (0, 0, 0) [(0, 0, 3), (0, 0, 5), (-1, 0, 7), (-1, 0, 8), (0, 0, 6), (0, 0, 4), (0, 0, 2), (0, 0, 0)] = true := by decide +kernel
theorem pth1 : SGB.pathOk adjL (0, 0, 1) (0, 0, 1) [] = true := by decide +kernel
theorem pth2 : SGB.pathOk adjL (0, 0, 1) (0, 0, 2) [(0, 0, 3), (0, 0, 5), (-1, 0, 7), (-1, 0, 8), (0, 0, 6), (0, 0, 4), (0, 0, 2)] = true := by decide +kernel
theorem pth3 : SGB.pathOk adjL (0, 0, 1) (0, 0, 3) [(0, 0, 3)] = true := by decide +kernel
theorem pth4 : SGB.pathOk adjL (0, 0, 1) (0, 0, 4) [(0, 0, 3), (0, 0, 5), (-1, 0, 7), (-1, 0, 8), (0, 0, 6), (0, 0, 4)] = true := by decide +kernel
theorem pth5 : SGB.pathOk adjL (0, 0, 1) (0, 0, 5) [(0, 0, 3), (0, 0, 5)] = true := by decide +kernel
theorem pth6 : SGB.pathOk adjL (0, 0, 1) (0, 0, 6) [(0, 0, 3), (0, 0, 5), (-1, 0, 7), (-1, 0, 8), (0, 0, 6)] = true := by decide +kernel
theorem pth7 : SGB.pathOk adjL (0, 0, 1) (0, 0, 7) [(0, 0, 3), (0, 0, 5), (0, 0, 7)] = true := by decide +kernel
theorem pth8 : SGB.pathOk adjL (0, 0, 1) (0, 0, 8) [(0, 0, 3), (0, 0, 5), (0, 0, 7), (0, 0, 8)] = true := by decide +kernel
theorem pth9 : SGB.pathOk adjL (0, 0, 1) (1, 0, 1) [(1, 0, 1)] = true := by decide +kernel
theorem pth10 : SGB.pathOk adjL (0, 0, 1) (0, 1, 1) [(0, 1, 0), (0, 1, 2), (0, 1, 4), (0, 1, 6), (-1, 1, 8), (-1, 1, 7), (0, 1, 5), (0, 1, 3), (0, 1, 1)] = true := by decide +kernel

theorem hR : ∀ v, G.Reachable v0 v :=
  SGB.connected E hG 1 (fun s => by
    fin_cases s
    exacts [SGB.reach_of_path hT _ _ _ pth0, SGB.reach_of_path hT _ _ _ pth1, SGB.reach_of_path hT _ _ _ pth2, SGB.reach_of_path hT _ _ _ pth3, SGB.reach_of_path hT _ _ _ pth4, SGB.reach_of_path hT _ _ _ pth5, SGB.reach_of_path hT _ _ _ pth6, SGB.reach_of_path hT _ _ _ pth7, SGB.reach_of_path hT _ _ _ pth8])
    (SGB.reach_of_path hT _ _ _ pth9) (SGB.reach_of_path hT _ _ _ pth10)

theorem ha0 : a 0 = 1 := SGB.ncard_zero v0 hR

set_option maxRecDepth 100000 in
noncomputable def regsData : List (GalCert.Region 9) := [
⟨0,0,0,0,0,[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨0,0,0,8,[[.f ⟨6,0,0,0,0,0,0,0,0⟩],[.f ⟨3,0,0,0,0,0,0,0,0⟩],[.f ⟨7,10,0,0,0,0,0,0,0⟩],[.s 2 0]],[.s 2 0]⟩,
⟨0,0,1,0,[[.f ⟨10,0,0,0,0,0,0,0,0⟩],[.f ⟨6,1,0,0,0,0,0,0,0⟩],[.f ⟨3,1,0,0,0,0,0,0,0⟩],[.s 3 0]],[.f ⟨0,0,0,0,0,0,0,0,0⟩]⟩,
⟨0,0,2,7,[[.s 0 0],[.f ⟨6,2,0,0,0,0,0,0,0⟩],[.f ⟨3,2,0,0,0,0,0,0,0⟩],[.s 4 0]],[.s 4 0]⟩,
⟨0,0,3,1,[[.s 1 0],[.f ⟨6,3,0,0,0,0,0,0,0⟩],[.f ⟨3,3,0,0,0,0,0,0,0⟩],[.s 5 0]],[.s 1 3]⟩,
⟨0,0,4,6,[[.s 2 0],[.f ⟨6,4,0,0,0,0,0,0,0⟩],[.f ⟨3,4,0,0,0,0,0,0,0⟩],[.s 6 0]],[.s 6 0]⟩,
⟨0,0,5,2,[[.s 3 0],[.f ⟨6,5,0,0,0,0,0,0,0⟩],[.f ⟨3,5,0,0,0,0,0,0,0⟩],[.f ⟨6,7,0,0,0,0,0,0,0⟩],[.s 7 0]],[.s 3 3]⟩,
⟨0,0,6,5,[[.s 4 0],[.f ⟨6,6,0,0,0,0,0,0,0⟩],[.f ⟨3,6,0,0,0,0,0,0,0⟩],[.f ⟨6,8,0,0,0,0,0,0,0⟩],[.s 8 0]],[.f ⟨6,8,0,0,0,0,0,0,1⟩]⟩,
⟨0,0,7,3,[[.s 5 0],[.f ⟨3,5,0,0,0,0,0,0,0⟩],[.f ⟨6,7,0,0,0,0,0,0,0⟩],[.f ⟨3,7,0,0,0,0,0,0,0⟩],[.s 8 0]],[.s 5 4]⟩,
⟨0,0,8,4,[[.s 6 0],[.f ⟨3,6,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨6,8,0,0,0,0,0,0,0⟩],[.f ⟨3,8,0,0,0,0,0,0,0⟩]],[.s 7 4]⟩]⟩,
⟨1,-1,-1,0,0,[(1,-1,0),(-1,1,0),(-1,-1,2)],-1,-1,2,2,0,0,0,0,9,0,0,0,
[⟨-1,-1,0,17,[[.f ⟨12,0,0,0,0,0,0,0,0⟩,.f ⟨12,0,0,0,0,1,0,1,0⟩],[.f ⟨7,9,0,0,0,0,0,0,0⟩,.f ⟨7,9,1,0,1,0,0,0,0⟩],[.f ⟨7,10,0,0,1,0,0,0,0⟩,.f ⟨7,10,1,0,2,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 2 0,.s 2 0]⟩,
⟨-1,-1,1,9,[[.f ⟨6,0,0,0,0,0,0,0,0⟩,.f ⟨12,0,0,0,0,1,0,0,0⟩],[.f ⟨12,1,0,0,0,0,0,0,0⟩,.f ⟨12,1,0,0,0,1,0,1,0⟩],[.f ⟨7,10,0,0,0,0,0,0,0⟩,.f ⟨7,10,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0]],[.f ⟨6,0,0,0,0,0,0,0,2⟩,.f ⟨12,0,0,0,0,1,0,0,2⟩]⟩,
⟨-1,-1,2,16,[[.s 0 0,.s 0 0],[.f ⟨12,2,0,0,0,0,0,0,0⟩,.f ⟨12,2,0,0,0,1,0,1,0⟩],[.f ⟨7,11,0,0,0,0,0,0,0⟩,.f ⟨7,11,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0]],[.s 4 0,.s 4 0]⟩,
⟨-1,-1,3,10,[[.s 1 0,.s 1 0],[.f ⟨12,3,0,0,0,0,0,0,0⟩,.f ⟨12,3,0,0,0,1,0,1,0⟩],[.f ⟨7,12,0,0,0,0,0,0,0⟩,.f ⟨7,12,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0]],[.s 1 3,.s 1 3]⟩,
⟨-1,-1,4,15,[[.s 2 0,.s 2 0],[.f ⟨12,4,0,0,0,0,0,0,0⟩,.f ⟨12,4,0,0,0,1,0,1,0⟩],[.f ⟨7,13,0,0,0,0,0,0,0⟩,.f ⟨7,13,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.s 6 0,.s 6 0]⟩,
⟨-1,-1,5,11,[[.s 3 0,.s 3 0],[.f ⟨12,5,0,0,0,0,0,0,0⟩,.f ⟨12,5,0,0,0,1,0,1,0⟩],[.f ⟨7,14,0,0,0,0,0,0,0⟩,.f ⟨7,14,1,0,1,0,0,0,0⟩],[.f ⟨12,7,0,0,0,0,0,0,0⟩,.f ⟨12,7,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨-1,-1,6,14,[[.s 4 0,.s 4 0],[.f ⟨12,6,0,0,0,0,0,0,0⟩,.f ⟨12,6,0,0,0,1,0,1,0⟩],[.f ⟨7,15,0,0,0,0,0,0,0⟩,.f ⟨7,15,1,0,1,0,0,0,0⟩],[.f ⟨12,8,0,0,0,0,0,0,0⟩,.f ⟨12,8,0,0,0,1,0,1,0⟩],[.s 8 0,.s 8 0]],[.f ⟨12,8,0,0,0,0,0,0,1⟩,.f ⟨12,8,0,0,0,1,0,1,1⟩]⟩,
⟨-1,-1,7,12,[[.s 5 0,.s 5 0],[.f ⟨7,14,0,0,0,0,0,0,0⟩,.f ⟨7,14,1,0,1,0,0,0,0⟩],[.f ⟨12,7,0,0,0,0,0,0,0⟩,.f ⟨12,7,0,0,0,1,0,1,0⟩],[.f ⟨7,16,0,0,0,0,0,0,0⟩,.f ⟨7,16,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0]],[.s 5 4,.s 5 4]⟩,
⟨-1,-1,8,13,[[.s 6 0,.s 6 0],[.f ⟨7,15,0,0,0,0,0,0,0⟩,.f ⟨7,15,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨12,8,0,0,0,0,0,0,0⟩,.f ⟨12,8,0,0,0,1,0,1,0⟩],[.f ⟨7,17,0,0,0,0,0,0,0⟩,.f ⟨7,17,1,0,1,0,0,0,0⟩]],[.s 7 4,.s 7 4]⟩]⟩,
⟨1,1,-1,0,0,[(1,1,0),(-1,-1,0),(1,-1,2)],1,-1,2,2,0,0,0,0,9,0,0,0,
[⟨1,-1,0,17,[[.f ⟨7,9,0,0,0,0,0,0,0⟩,.f ⟨7,9,0,0,0,1,0,1,0⟩],[.f ⟨8,0,0,0,0,0,0,0,0⟩,.f ⟨8,0,1,0,1,0,0,0,0⟩],[.f ⟨7,10,0,0,0,0,0,1,0⟩,.f ⟨7,10,0,0,0,1,0,2,0⟩],[.s 2 0,.s 2 0]],[.s 2 0,.s 2 0]⟩,
⟨1,-1,1,9,[[.f ⟨3,0,0,0,0,0,0,0,0⟩,.f ⟨8,0,1,0,0,0,0,0,0⟩],[.f ⟨7,10,0,0,0,0,0,0,0⟩,.f ⟨7,10,0,0,0,1,0,1,0⟩],[.f ⟨8,1,0,0,0,0,0,0,0⟩,.f ⟨8,1,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0]],[.f ⟨3,0,0,0,0,0,0,0,2⟩,.f ⟨8,0,1,0,0,0,0,0,2⟩]⟩,
⟨1,-1,2,16,[[.s 0 0,.s 0 0],[.f ⟨7,11,0,0,0,0,0,0,0⟩,.f ⟨7,11,0,0,0,1,0,1,0⟩],[.f ⟨8,2,0,0,0,0,0,0,0⟩,.f ⟨8,2,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0]],[.s 4 0,.s 4 0]⟩,
⟨1,-1,3,10,[[.s 1 0,.s 1 0],[.f ⟨7,12,0,0,0,0,0,0,0⟩,.f ⟨7,12,0,0,0,1,0,1,0⟩],[.f ⟨8,3,0,0,0,0,0,0,0⟩,.f ⟨8,3,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0]],[.s 1 3,.s 1 3]⟩,
⟨1,-1,4,15,[[.s 2 0,.s 2 0],[.f ⟨7,13,0,0,0,0,0,0,0⟩,.f ⟨7,13,0,0,0,1,0,1,0⟩],[.f ⟨8,4,0,0,0,0,0,0,0⟩,.f ⟨8,4,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.s 6 0,.s 6 0]⟩,
⟨1,-1,5,11,[[.s 3 0,.s 3 0],[.f ⟨7,14,0,0,0,0,0,0,0⟩,.f ⟨7,14,0,0,0,1,0,1,0⟩],[.f ⟨8,5,0,0,0,0,0,0,0⟩,.f ⟨8,5,1,0,1,0,0,0,0⟩],[.f ⟨7,16,0,0,0,0,0,0,0⟩,.f ⟨7,16,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨1,-1,6,14,[[.s 4 0,.s 4 0],[.f ⟨7,15,0,0,0,0,0,0,0⟩,.f ⟨7,15,0,0,0,1,0,1,0⟩],[.f ⟨8,6,0,0,0,0,0,0,0⟩,.f ⟨8,6,1,0,1,0,0,0,0⟩],[.f ⟨7,17,0,0,0,0,0,0,0⟩,.f ⟨7,17,0,0,0,1,0,1,0⟩],[.s 8 0,.s 8 0]],[.f ⟨7,17,0,0,0,0,0,0,1⟩,.f ⟨7,17,0,0,0,1,0,1,1⟩]⟩,
⟨1,-1,7,12,[[.s 5 0,.s 5 0],[.f ⟨8,5,0,0,0,0,0,0,0⟩,.f ⟨8,5,1,0,1,0,0,0,0⟩],[.f ⟨7,16,0,0,0,0,0,0,0⟩,.f ⟨7,16,0,0,0,1,0,1,0⟩],[.f ⟨8,7,0,0,0,0,0,0,0⟩,.f ⟨8,7,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0]],[.s 5 4,.s 5 4]⟩,
⟨1,-1,8,13,[[.s 6 0,.s 6 0],[.f ⟨8,6,0,0,0,0,0,0,0⟩,.f ⟨8,6,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨7,17,0,0,0,0,0,0,0⟩,.f ⟨7,17,0,0,0,1,0,1,0⟩],[.f ⟨8,8,0,0,0,0,0,0,0⟩,.f ⟨8,8,1,0,1,0,0,0,0⟩]],[.s 7 4,.s 7 4]⟩]⟩,
⟨1,1,0,0,0,[(0,1,0),(0,-1,0),(1,0,1)],1,0,1,1,0,0,0,0,1,0,0,0,
[⟨1,0,0,8,[[.f ⟨0,0,0,0,0,0,0,0,0⟩,.s 0 0],[.s 0 0,.s 0 0],[.f ⟨2,1,0,0,0,0,0,0,0⟩,.f ⟨8,1,0,0,0,1,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 2 0,.s 0 1]⟩,
⟨1,0,1,1,[[.f ⟨4,0,0,0,0,0,0,0,0⟩,.f ⟨9,0,1,0,0,0,0,0,0⟩],[.f ⟨0,1,0,0,0,0,0,0,0⟩,.s 1 0],[.s 1 0,.s 1 0],[.s 3 0,.s 3 0]],[.f ⟨0,1,0,0,0,0,0,0,2⟩,.s 1 2]⟩,
⟨1,0,2,7,[[.s 0 0,.s 0 0],[.f ⟨0,2,0,0,0,0,0,0,0⟩,.s 2 0],[.s 2 0,.s 2 0],[.s 4 0,.s 4 0]],[.s 4 0,.s 2 2]⟩,
⟨1,0,3,2,[[.s 1 0,.s 1 0],[.f ⟨0,3,0,0,0,0,0,0,0⟩,.s 3 0],[.s 3 0,.s 3 0],[.s 5 0,.s 5 0]],[.s 1 3,.s 1 3]⟩,
⟨1,0,4,6,[[.s 2 0,.s 2 0],[.f ⟨0,4,0,0,0,0,0,0,0⟩,.s 4 0],[.s 4 0,.s 4 0],[.s 6 0,.s 6 0]],[.s 6 0,.s 4 2]⟩,
⟨1,0,5,3,[[.s 3 0,.s 3 0],[.f ⟨0,5,0,0,0,0,0,0,0⟩,.s 5 0],[.s 5 0,.s 5 0],[.f ⟨0,7,0,0,0,0,0,0,0⟩,.s 7 0],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨1,0,6,5,[[.s 4 0,.s 4 0],[.f ⟨0,6,0,0,0,0,0,0,0⟩,.s 6 0],[.s 6 0,.s 6 0],[.f ⟨0,8,0,0,0,0,0,0,0⟩,.s 8 0],[.s 8 0,.s 8 0]],[.f ⟨0,8,0,0,0,0,0,0,1⟩,.s 6 2]⟩,
⟨1,0,7,4,[[.s 5 0,.s 5 0],[.s 5 0,.s 5 0],[.f ⟨0,7,0,0,0,0,0,0,0⟩,.s 7 0],[.s 7 0,.s 7 0],[.s 8 0,.s 8 0]],[.s 5 4,.s 5 4]⟩,
⟨1,0,8,5,[[.s 6 0,.s 6 0],[.s 6 0,.s 6 0],[.s 7 0,.s 7 0],[.f ⟨0,8,0,0,0,0,0,0,0⟩,.s 8 0],[.s 8 0,.s 8 0]],[.s 7 4,.s 7 4]⟩]⟩,
⟨1,1,1,0,0,[(-1,1,0),(1,-1,0),(1,1,2)],1,1,2,2,0,0,0,0,9,0,0,0,
[⟨1,1,0,2,[[.f ⟨10,0,0,0,0,0,0,0,0⟩,.f ⟨10,0,1,0,1,0,0,0,0⟩],[.f ⟨9,0,0,0,0,0,0,0,0⟩,.f ⟨9,0,0,0,0,1,0,1,0⟩],[.f ⟨3,1,0,0,0,0,0,0,0⟩,.f ⟨9,1,0,0,0,1,0,0,0⟩],[.s 2 0,.s 2 0]],[.f ⟨10,0,0,0,0,0,0,0,1⟩,.f ⟨10,0,1,0,1,0,0,0,1⟩]⟩,
⟨1,1,1,9,[[.f ⟨10,0,0,0,1,0,0,0,0⟩,.f ⟨10,0,1,0,2,0,0,0,0⟩],[.f ⟨10,1,0,0,0,0,0,0,0⟩,.f ⟨10,1,1,0,1,0,0,0,0⟩],[.f ⟨9,1,0,0,0,0,0,0,0⟩,.f ⟨9,1,0,0,0,1,0,1,0⟩],[.s 3 0,.s 3 0]],[.s 3 0,.s 3 0]⟩,
⟨1,1,2,3,[[.s 0 0,.s 0 0],[.f ⟨10,2,0,0,0,0,0,0,0⟩,.f ⟨10,2,1,0,1,0,0,0,0⟩],[.f ⟨9,2,0,0,0,0,0,0,0⟩,.f ⟨9,2,0,0,0,1,0,1,0⟩],[.s 4 0,.s 4 0]],[.s 0 3,.s 0 3]⟩,
⟨1,1,3,8,[[.s 1 0,.s 1 0],[.f ⟨10,3,0,0,0,0,0,0,0⟩,.f ⟨10,3,1,0,1,0,0,0,0⟩],[.f ⟨9,3,0,0,0,0,0,0,0⟩,.f ⟨9,3,0,0,0,1,0,1,0⟩],[.s 5 0,.s 5 0]],[.s 5 0,.s 5 0]⟩,
⟨1,1,4,4,[[.s 2 0,.s 2 0],[.f ⟨10,4,0,0,0,0,0,0,0⟩,.f ⟨10,4,1,0,1,0,0,0,0⟩],[.f ⟨9,4,0,0,0,0,0,0,0⟩,.f ⟨9,4,0,0,0,1,0,1,0⟩],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨1,1,5,7,[[.s 3 0,.s 3 0],[.f ⟨10,5,0,0,0,0,0,0,0⟩,.f ⟨10,5,1,0,1,0,0,0,0⟩],[.f ⟨9,5,0,0,0,0,0,0,0⟩,.f ⟨9,5,0,0,0,1,0,1,0⟩],[.f ⟨10,7,0,0,0,0,0,0,0⟩,.f ⟨10,7,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.f ⟨10,7,0,0,0,0,0,0,1⟩,.f ⟨10,7,1,0,1,0,0,0,1⟩]⟩,
⟨1,1,6,5,[[.s 4 0,.s 4 0],[.f ⟨10,6,0,0,0,0,0,0,0⟩,.f ⟨10,6,1,0,1,0,0,0,0⟩],[.f ⟨9,6,0,0,0,0,0,0,0⟩,.f ⟨9,6,0,0,0,1,0,1,0⟩],[.f ⟨10,8,0,0,0,0,0,0,0⟩,.f ⟨10,8,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0]],[.s 4 3,.s 4 3]⟩,
⟨1,1,7,7,[[.s 5 0,.s 5 0],[.f ⟨9,5,0,0,0,0,0,0,0⟩,.f ⟨9,5,0,0,0,1,0,1,0⟩],[.f ⟨10,7,0,0,0,0,0,0,0⟩,.f ⟨10,7,1,0,1,0,0,0,0⟩],[.f ⟨9,7,0,0,0,0,0,0,0⟩,.f ⟨9,7,0,0,0,1,0,1,0⟩],[.s 8 0,.s 8 0]],[.f ⟨10,7,0,0,0,0,0,0,3⟩,.f ⟨10,7,1,0,1,0,0,0,3⟩]⟩,
⟨1,1,8,6,[[.s 6 0,.s 6 0],[.f ⟨9,6,0,0,0,0,0,0,0⟩,.f ⟨9,6,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0],[.f ⟨10,8,0,0,0,0,0,0,0⟩,.f ⟨10,8,1,0,1,0,0,0,0⟩],[.f ⟨9,8,0,0,0,0,0,0,0⟩,.f ⟨9,8,0,0,0,1,0,1,0⟩]],[.s 6 4,.s 6 4]⟩]⟩,
⟨1,-1,1,0,0,[(-1,-1,0),(1,1,0),(-1,1,2)],-1,1,2,2,0,0,0,0,9,0,0,0,
[⟨-1,1,0,2,[[.f ⟨11,0,0,0,0,0,0,0,0⟩,.f ⟨11,0,1,0,1,0,0,0,0⟩],[.f ⟨10,0,0,0,0,0,0,0,0⟩,.f ⟨10,0,0,0,0,1,0,1,0⟩],[.f ⟨6,1,0,0,0,0,0,0,0⟩,.f ⟨11,1,1,0,0,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.f ⟨10,0,0,0,0,0,0,0,0⟩,.f ⟨10,0,0,0,0,1,0,1,0⟩]⟩,
⟨-1,1,1,9,[[.f ⟨10,0,0,0,0,0,0,1,0⟩,.f ⟨10,0,0,0,0,1,0,2,0⟩],[.f ⟨11,1,0,0,0,0,0,0,0⟩,.f ⟨11,1,1,0,1,0,0,0,0⟩],[.f ⟨10,1,0,0,0,0,0,0,0⟩,.f ⟨10,1,0,0,0,1,0,1,0⟩],[.s 3 0,.s 3 0]],[.s 3 0,.s 3 0]⟩,
⟨-1,1,2,3,[[.s 0 0,.s 0 0],[.f ⟨11,2,0,0,0,0,0,0,0⟩,.f ⟨11,2,1,0,1,0,0,0,0⟩],[.f ⟨10,2,0,0,0,0,0,0,0⟩,.f ⟨10,2,0,0,0,1,0,1,0⟩],[.s 4 0,.s 4 0]],[.s 0 3,.s 0 3]⟩,
⟨-1,1,3,8,[[.s 1 0,.s 1 0],[.f ⟨11,3,0,0,0,0,0,0,0⟩,.f ⟨11,3,1,0,1,0,0,0,0⟩],[.f ⟨10,3,0,0,0,0,0,0,0⟩,.f ⟨10,3,0,0,0,1,0,1,0⟩],[.s 5 0,.s 5 0]],[.s 5 0,.s 5 0]⟩,
⟨-1,1,4,4,[[.s 2 0,.s 2 0],[.f ⟨11,4,0,0,0,0,0,0,0⟩,.f ⟨11,4,1,0,1,0,0,0,0⟩],[.f ⟨10,4,0,0,0,0,0,0,0⟩,.f ⟨10,4,0,0,0,1,0,1,0⟩],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨-1,1,5,7,[[.s 3 0,.s 3 0],[.f ⟨11,5,0,0,0,0,0,0,0⟩,.f ⟨11,5,1,0,1,0,0,0,0⟩],[.f ⟨10,5,0,0,0,0,0,0,0⟩,.f ⟨10,5,0,0,0,1,0,1,0⟩],[.f ⟨11,7,0,0,0,0,0,0,0⟩,.f ⟨11,7,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.s 7 0,.s 7 0]⟩,
⟨-1,1,6,5,[[.s 4 0,.s 4 0],[.f ⟨11,6,0,0,0,0,0,0,0⟩,.f ⟨11,6,1,0,1,0,0,0,0⟩],[.f ⟨10,6,0,0,0,0,0,0,0⟩,.f ⟨10,6,0,0,0,1,0,1,0⟩],[.f ⟨11,8,0,0,0,0,0,0,0⟩,.f ⟨11,8,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0]],[.s 4 3,.s 4 3]⟩,
⟨-1,1,7,6,[[.s 5 0,.s 5 0],[.f ⟨10,5,0,0,0,0,0,0,0⟩,.f ⟨10,5,0,0,0,1,0,1,0⟩],[.f ⟨11,7,0,0,0,0,0,0,0⟩,.f ⟨11,7,1,0,1,0,0,0,0⟩],[.f ⟨10,7,0,0,0,0,0,0,0⟩,.f ⟨10,7,0,0,0,1,0,1,0⟩],[.s 8 0,.s 8 0]],[.s 8 2,.s 8 2]⟩,
⟨-1,1,8,5,[[.s 6 0,.s 6 0],[.f ⟨10,6,0,0,0,0,0,0,0⟩,.f ⟨10,6,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0],[.f ⟨11,8,0,0,0,0,0,0,0⟩,.f ⟨11,8,1,0,1,0,0,0,0⟩],[.f ⟨10,8,0,0,0,0,0,0,0⟩,.f ⟨10,8,0,0,0,1,0,1,0⟩]],[.f ⟨10,6,0,0,0,0,0,0,3⟩,.f ⟨10,6,0,0,0,1,0,1,3⟩]⟩]⟩,
⟨1,-1,0,0,0,[(0,-1,0),(0,1,0),(-1,0,1)],-1,0,1,1,0,0,0,0,1,0,0,0,
[⟨-1,0,0,8,[[.s 0 0,.s 0 0],[.f ⟨0,0,0,0,0,0,0,0,0⟩,.s 0 0],[.f ⟨1,1,0,0,0,0,0,0,0⟩,.f ⟨12,1,1,0,0,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 2 0,.s 0 0]⟩,
⟨-1,0,1,1,[[.f ⟨5,0,0,0,0,0,0,0,0⟩,.f ⟨11,0,0,0,0,1,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨0,1,0,0,0,0,0,0,0⟩,.s 1 0],[.s 3 0,.s 3 0]],[.f ⟨0,1,0,0,0,0,0,0,1⟩,.s 1 1]⟩,
⟨-1,0,2,7,[[.s 0 0,.s 0 0],[.s 2 0,.s 2 0],[.f ⟨0,2,0,0,0,0,0,0,0⟩,.s 2 0],[.s 4 0,.s 4 0]],[.s 4 0,.s 2 1]⟩,
⟨-1,0,3,2,[[.s 1 0,.s 1 0],[.s 3 0,.s 3 0],[.f ⟨0,3,0,0,0,0,0,0,0⟩,.s 3 0],[.s 5 0,.s 5 0]],[.s 1 3,.s 1 3]⟩,
⟨-1,0,4,6,[[.s 2 0,.s 2 0],[.s 4 0,.s 4 0],[.f ⟨0,4,0,0,0,0,0,0,0⟩,.s 4 0],[.s 6 0,.s 6 0]],[.s 6 0,.s 4 1]⟩,
⟨-1,0,5,3,[[.s 3 0,.s 3 0],[.s 5 0,.s 5 0],[.f ⟨0,5,0,0,0,0,0,0,0⟩,.s 5 0],[.s 7 0,.s 7 0],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨-1,0,6,5,[[.s 4 0,.s 4 0],[.s 6 0,.s 6 0],[.f ⟨0,6,0,0,0,0,0,0,0⟩,.s 6 0],[.s 8 0,.s 8 0],[.s 8 0,.s 8 0]],[.s 8 0,.s 6 1]⟩,
⟨-1,0,7,3,[[.s 5 0,.s 5 0],[.f ⟨0,5,0,0,0,0,0,0,0⟩,.s 5 0],[.s 7 0,.s 7 0],[.f ⟨0,7,0,0,0,0,0,0,0⟩,.s 7 0],[.s 8 0,.s 8 0]],[.f ⟨0,5,0,0,0,0,0,0,3⟩,.s 5 3]⟩,
⟨-1,0,8,4,[[.s 6 0,.s 6 0],[.f ⟨0,6,0,0,0,0,0,0,0⟩,.s 6 0],[.s 7 0,.s 7 0],[.s 8 0,.s 8 0],[.f ⟨0,8,0,0,0,0,0,0,0⟩,.s 8 0]],[.s 7 4,.s 7 4]⟩]⟩,
⟨2,-1,-1,1,-1,[(-1,-1,1),(1,-1,1)],-1,-1,1,2,1,-1,1,2,9,9,1,1,
[⟨0,-2,0,26,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]⟩,
⟨0,-2,1,18,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.s 9 2,.s 9 2,.s 9 2,.s 9 2]⟩,
⟨0,-2,2,25,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]⟩,
⟨0,-2,3,19,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 1 3,.s 1 3,.s 1 3,.s 1 3]⟩,
⟨0,-2,4,24,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]⟩,
⟨0,-2,5,20,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.s 3 3,.s 3 3,.s 3 3,.s 3 3]⟩,
⟨0,-2,6,23,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 17 1,.s 17 1,.s 17 1,.s 17 1]⟩,
⟨0,-2,7,21,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 5 4,.s 5 4,.s 5 4,.s 5 4]⟩,
⟨0,-2,8,22,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 7 4,.s 7 4,.s 7 4,.s 7 4]⟩,
⟨0,-1,0,17,[[.f ⟨1,0,0,0,0,0,0,0,0⟩,.f ⟨1,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0],[.f ⟨2,0,0,0,0,0,0,0,0⟩,.s 0 0,.f ⟨2,0,0,1,1,0,0,0,0⟩,.s 0 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]⟩,
⟨0,-1,1,9,[[.f ⟨0,0,0,0,0,0,0,0,0⟩,.f ⟨1,0,1,0,0,0,0,0,0⟩,.f ⟨2,0,0,1,0,0,0,0,0⟩,.s 0 0],[.f ⟨1,1,0,0,0,0,0,0,0⟩,.f ⟨1,1,1,0,1,0,0,0,0⟩,.s 1 0,.s 1 0],[.f ⟨2,1,0,0,0,0,0,0,0⟩,.s 1 0,.f ⟨2,1,0,1,1,0,0,0,0⟩,.s 1 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]],[.f ⟨0,0,0,0,0,0,0,0,2⟩,.f ⟨1,0,1,0,0,0,0,0,2⟩,.f ⟨2,0,0,1,0,0,0,0,2⟩,.s 0 2]⟩,
⟨0,-1,2,16,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.f ⟨1,2,0,0,0,0,0,0,0⟩,.f ⟨1,2,1,0,1,0,0,0,0⟩,.s 2 0,.s 2 0],[.f ⟨2,2,0,0,0,0,0,0,0⟩,.s 2 0,.f ⟨2,2,0,1,1,0,0,0,0⟩,.s 2 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0]],[.s 13 0,.s 13 0,.s 13 0,.s 13 0]⟩,
⟨0,-1,3,10,[[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.f ⟨1,3,0,0,0,0,0,0,0⟩,.f ⟨1,3,1,0,1,0,0,0,0⟩,.s 3 0,.s 3 0],[.f ⟨2,3,0,0,0,0,0,0,0⟩,.s 3 0,.f ⟨2,3,0,1,1,0,0,0,0⟩,.s 3 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 10 3,.s 10 3,.s 10 3,.s 10 3]⟩,
⟨0,-1,4,15,[[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.f ⟨1,4,0,0,0,0,0,0,0⟩,.f ⟨1,4,1,0,1,0,0,0,0⟩,.s 4 0,.s 4 0],[.f ⟨2,4,0,0,0,0,0,0,0⟩,.s 4 0,.f ⟨2,4,0,1,1,0,0,0,0⟩,.s 4 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]⟩,
⟨0,-1,5,11,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.f ⟨1,5,0,0,0,0,0,0,0⟩,.f ⟨1,5,1,0,1,0,0,0,0⟩,.s 5 0,.s 5 0],[.f ⟨2,5,0,0,0,0,0,0,0⟩,.s 5 0,.f ⟨2,5,0,1,1,0,0,0,0⟩,.s 5 0],[.f ⟨1,7,0,0,0,0,0,0,0⟩,.f ⟨1,7,1,0,1,0,0,0,0⟩,.s 7 0,.s 7 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 12 3,.s 12 3,.s 12 3,.s 12 3]⟩,
⟨0,-1,6,14,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.f ⟨1,6,0,0,0,0,0,0,0⟩,.f ⟨1,6,1,0,1,0,0,0,0⟩,.s 6 0,.s 6 0],[.f ⟨2,6,0,0,0,0,0,0,0⟩,.s 6 0,.f ⟨2,6,0,1,1,0,0,0,0⟩,.s 6 0],[.f ⟨1,8,0,0,0,0,0,0,0⟩,.f ⟨1,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.f ⟨1,8,0,0,0,0,0,0,1⟩,.f ⟨1,8,1,0,1,0,0,0,1⟩,.s 8 1,.s 8 1]⟩,
⟨0,-1,7,12,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.f ⟨2,5,0,0,0,0,0,0,0⟩,.s 5 0,.f ⟨2,5,0,1,1,0,0,0,0⟩,.s 5 0],[.f ⟨1,7,0,0,0,0,0,0,0⟩,.f ⟨1,7,1,0,1,0,0,0,0⟩,.s 7 0,.s 7 0],[.f ⟨2,7,0,0,0,0,0,0,0⟩,.s 7 0,.f ⟨2,7,0,1,1,0,0,0,0⟩,.s 7 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 14 4,.s 14 4,.s 14 4,.s 14 4]⟩,
⟨0,-1,8,13,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.f ⟨2,6,0,0,0,0,0,0,0⟩,.s 6 0,.f ⟨2,6,0,1,1,0,0,0,0⟩,.s 6 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨1,8,0,0,0,0,0,0,0⟩,.f ⟨1,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0],[.f ⟨2,8,0,0,0,0,0,0,0⟩,.s 8 0,.f ⟨2,8,0,1,1,0,0,0,0⟩,.s 8 0]],[.s 16 4,.s 16 4,.s 16 4,.s 16 4]⟩]⟩,
⟨2,1,-1,1,0,[(0,-1,1),(1,1,1)],0,-1,1,1,1,1,1,1,9,1,1,9,
[⟨2,-1,0,17,[[.f ⟨2,0,0,0,0,0,0,0,0⟩,.f ⟨2,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨2,1,0,0,1,0,0,0,0⟩,.f ⟨2,1,1,0,2,0,0,0,0⟩,.s 1 0,.s 1 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 2 0,.s 2 0,.s 0 1,.s 0 1]⟩,
⟨2,-1,1,10,[[.f ⟨3,0,0,0,1,0,0,0,0⟩,.s 0 0,.f ⟨3,0,0,1,2,0,0,0,0⟩,.s 0 0],[.f ⟨2,1,0,0,0,0,0,0,0⟩,.f ⟨2,1,1,0,1,0,0,0,0⟩,.s 1 0,.s 1 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.f ⟨3,0,0,0,1,0,0,0,2⟩,.s 0 2,.f ⟨3,0,0,1,2,0,0,0,2⟩,.s 0 2]⟩,
⟨2,-1,2,16,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨2,2,0,0,0,0,0,0,0⟩,.f ⟨2,2,1,0,1,0,0,0,0⟩,.s 2 0,.s 2 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 4 0,.s 4 0,.s 2 2,.s 2 2]⟩,
⟨2,-1,3,11,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨2,3,0,0,0,0,0,0,0⟩,.f ⟨2,3,1,0,1,0,0,0,0⟩,.s 3 0,.s 3 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 1 3,.s 1 3,.s 1 3,.s 1 3]⟩,
⟨2,-1,4,15,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.f ⟨2,4,0,0,0,0,0,0,0⟩,.f ⟨2,4,1,0,1,0,0,0,0⟩,.s 4 0,.s 4 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 6 0,.s 6 0,.s 4 2,.s 4 2]⟩,
⟨2,-1,5,12,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.f ⟨2,5,0,0,0,0,0,0,0⟩,.f ⟨2,5,1,0,1,0,0,0,0⟩,.s 5 0,.s 5 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.f ⟨2,7,0,0,0,0,0,0,0⟩,.f ⟨2,7,1,0,1,0,0,0,0⟩,.s 7 0,.s 7 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.s 3 3,.s 3 3,.s 3 3,.s 3 3]⟩,
⟨2,-1,6,14,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨2,6,0,0,0,0,0,0,0⟩,.f ⟨2,6,1,0,1,0,0,0,0⟩,.s 6 0,.s 6 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨2,8,0,0,0,0,0,0,0⟩,.f ⟨2,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.f ⟨2,8,0,0,0,0,0,0,1⟩,.f ⟨2,8,1,0,1,0,0,0,1⟩,.s 6 2,.s 6 2]⟩,
⟨2,-1,7,13,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.f ⟨2,7,0,0,0,0,0,0,0⟩,.f ⟨2,7,1,0,1,0,0,0,0⟩,.s 7 0,.s 7 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 5 4,.s 5 4,.s 5 4,.s 5 4]⟩,
⟨2,-1,8,14,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.f ⟨2,8,0,0,0,0,0,0,0⟩,.f ⟨2,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 7 4,.s 7 4,.s 7 4,.s 7 4]⟩]⟩,
⟨2,1,0,1,1,[(1,-1,1),(0,1,1)],1,-1,1,1,0,1,1,1,1,9,9,1,
[⟨2,1,0,3,[[.f ⟨4,0,0,0,0,0,0,0,0⟩,.s 0 0,.f ⟨4,0,0,1,1,0,0,0,0⟩,.s 0 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨3,1,0,0,1,0,0,0,0⟩,.f ⟨3,1,1,0,2,0,0,0,0⟩,.s 1 0,.s 1 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.f ⟨4,0,0,0,0,0,0,0,1⟩,.s 0 1,.f ⟨4,0,0,1,1,0,0,0,1⟩,.s 0 1]⟩,
⟨2,1,1,10,[[.f ⟨4,0,0,0,1,0,0,0,0⟩,.s 0 0,.f ⟨4,0,0,1,2,0,0,0,0⟩,.s 0 0],[.f ⟨4,1,0,0,0,0,0,0,0⟩,.s 1 0,.f ⟨4,1,0,1,1,0,0,0,0⟩,.s 1 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.f ⟨4,1,0,0,0,0,0,0,2⟩,.s 1 2,.f ⟨4,1,0,1,1,0,0,0,2⟩,.s 1 2]⟩,
⟨2,1,2,4,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨4,2,0,0,0,0,0,0,0⟩,.s 2 0,.f ⟨4,2,0,1,1,0,0,0,0⟩,.s 2 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 0 3,.s 0 3,.s 0 3,.s 0 3]⟩,
⟨2,1,3,9,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨4,3,0,0,0,0,0,0,0⟩,.s 3 0,.f ⟨4,3,0,1,1,0,0,0,0⟩,.s 3 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.f ⟨4,3,0,0,0,0,0,0,2⟩,.s 3 2,.f ⟨4,3,0,1,1,0,0,0,2⟩,.s 3 2]⟩,
⟨2,1,4,5,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.f ⟨4,4,0,0,0,0,0,0,0⟩,.s 4 0,.f ⟨4,4,0,1,1,0,0,0,0⟩,.s 4 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 2 3,.s 2 3,.s 2 3,.s 2 3]⟩,
⟨2,1,5,8,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.f ⟨4,5,0,0,0,0,0,0,0⟩,.s 5 0,.f ⟨4,5,0,1,1,0,0,0,0⟩,.s 5 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.f ⟨4,7,0,0,0,0,0,0,0⟩,.s 7 0,.f ⟨4,7,0,1,1,0,0,0,0⟩,.s 7 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.f ⟨4,5,0,0,0,0,0,0,2⟩,.s 5 2,.f ⟨4,5,0,1,1,0,0,0,2⟩,.s 5 2]⟩,
⟨2,1,6,6,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨4,6,0,0,0,0,0,0,0⟩,.s 6 0,.f ⟨4,6,0,1,1,0,0,0,0⟩,.s 6 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨4,8,0,0,0,0,0,0,0⟩,.s 8 0,.f ⟨4,8,0,1,1,0,0,0,0⟩,.s 8 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 4 3,.s 4 3,.s 4 3,.s 4 3]⟩,
⟨2,1,7,8,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.f ⟨4,7,0,0,0,0,0,0,0⟩,.s 7 0,.f ⟨4,7,0,1,1,0,0,0,0⟩,.s 7 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.f ⟨4,7,0,0,0,0,0,0,3⟩,.s 7 3,.f ⟨4,7,0,1,1,0,0,0,3⟩,.s 7 3]⟩,
⟨2,1,8,7,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.f ⟨4,8,0,0,0,0,0,0,0⟩,.s 8 0,.f ⟨4,8,0,1,1,0,0,0,0⟩,.s 8 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 6 4,.s 6 4,.s 6 4,.s 6 4]⟩]⟩,
⟨2,1,1,-1,1,[(1,1,1),(-1,1,1)],1,1,1,2,-1,1,1,2,9,9,1,1,
[⟨0,1,0,1,[[.f ⟨5,0,0,0,0,0,0,0,0⟩,.s 9 0,.f ⟨5,0,0,1,1,0,0,0,0⟩,.s 9 0],[.f ⟨4,0,0,0,0,0,0,0,0⟩,.f ⟨4,0,1,0,1,0,0,0,0⟩,.s 9 0,.s 9 0],[.f ⟨0,1,0,0,0,0,0,0,0⟩,.f ⟨4,1,1,0,0,0,0,0,0⟩,.f ⟨5,1,0,1,0,0,0,0,0⟩,.s 10 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.f ⟨0,1,0,0,0,0,0,0,0⟩,.f ⟨4,1,1,0,0,0,0,0,0⟩,.f ⟨5,1,0,1,0,0,0,0,0⟩,.s 10 0]⟩,
⟨0,1,1,9,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.f ⟨5,1,0,0,0,0,0,0,0⟩,.s 10 0,.f ⟨5,1,0,1,1,0,0,0,0⟩,.s 10 0],[.f ⟨4,1,0,0,0,0,0,0,0⟩,.f ⟨4,1,1,0,1,0,0,0,0⟩,.s 10 0,.s 10 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]⟩,
⟨0,1,2,2,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨5,2,0,0,0,0,0,0,0⟩,.s 11 0,.f ⟨5,2,0,1,1,0,0,0,0⟩,.s 11 0],[.f ⟨4,2,0,0,0,0,0,0,0⟩,.f ⟨4,2,1,0,1,0,0,0,0⟩,.s 11 0,.s 11 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 0 3,.s 0 3,.s 0 3,.s 0 3]⟩,
⟨0,1,3,8,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨5,3,0,0,0,0,0,0,0⟩,.s 12 0,.f ⟨5,3,0,1,1,0,0,0,0⟩,.s 12 0],[.f ⟨4,3,0,0,0,0,0,0,0⟩,.f ⟨4,3,1,0,1,0,0,0,0⟩,.s 12 0,.s 12 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]⟩,
⟨0,1,4,3,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.f ⟨5,4,0,0,0,0,0,0,0⟩,.s 13 0,.f ⟨5,4,0,1,1,0,0,0,0⟩,.s 13 0],[.f ⟨4,4,0,0,0,0,0,0,0⟩,.f ⟨4,4,1,0,1,0,0,0,0⟩,.s 13 0,.s 13 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 2 3,.s 2 3,.s 2 3,.s 2 3]⟩,
⟨0,1,5,7,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.f ⟨5,5,0,0,0,0,0,0,0⟩,.s 14 0,.f ⟨5,5,0,1,1,0,0,0,0⟩,.s 14 0],[.f ⟨4,5,0,0,0,0,0,0,0⟩,.f ⟨4,5,1,0,1,0,0,0,0⟩,.s 14 0,.s 14 0],[.f ⟨5,7,0,0,0,0,0,0,0⟩,.s 16 0,.f ⟨5,7,0,1,1,0,0,0,0⟩,.s 16 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.f ⟨5,7,0,0,0,0,0,0,1⟩,.s 16 1,.f ⟨5,7,0,1,1,0,0,0,1⟩,.s 16 1]⟩,
⟨0,1,6,4,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨5,6,0,0,0,0,0,0,0⟩,.s 15 0,.f ⟨5,6,0,1,1,0,0,0,0⟩,.s 15 0],[.f ⟨4,6,0,0,0,0,0,0,0⟩,.f ⟨4,6,1,0,1,0,0,0,0⟩,.s 15 0,.s 15 0],[.f ⟨5,8,0,0,0,0,0,0,0⟩,.s 17 0,.f ⟨5,8,0,1,1,0,0,0,0⟩,.s 17 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 4 3,.s 4 3,.s 4 3,.s 4 3]⟩,
⟨0,1,7,6,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.f ⟨4,5,0,0,0,0,0,0,0⟩,.f ⟨4,5,1,0,1,0,0,0,0⟩,.s 14 0,.s 14 0],[.f ⟨5,7,0,0,0,0,0,0,0⟩,.s 16 0,.f ⟨5,7,0,1,1,0,0,0,0⟩,.s 16 0],[.f ⟨4,7,0,0,0,0,0,0,0⟩,.f ⟨4,7,1,0,1,0,0,0,0⟩,.s 16 0,.s 16 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 8 2,.s 8 2,.s 8 2,.s 8 2]⟩,
⟨0,1,8,5,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨4,6,0,0,0,0,0,0,0⟩,.f ⟨4,6,1,0,1,0,0,0,0⟩,.s 15 0,.s 15 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.f ⟨5,8,0,0,0,0,0,0,0⟩,.s 17 0,.f ⟨5,8,0,1,1,0,0,0,0⟩,.s 17 0],[.f ⟨4,8,0,0,0,0,0,0,0⟩,.f ⟨4,8,1,0,1,0,0,0,0⟩,.s 17 0,.s 17 0]],[.s 6 4,.s 6 4,.s 6 4,.s 6 4]⟩,
⟨0,2,0,10,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 1 0,.s 1 0,.s 1 0,.s 1 0]⟩,
⟨0,2,1,18,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]⟩,
⟨0,2,2,11,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0]],[.s 9 3,.s 9 3,.s 9 3,.s 9 3]⟩,
⟨0,2,3,17,[[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]⟩,
⟨0,2,4,12,[[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]],[.s 11 3,.s 11 3,.s 11 3,.s 11 3]⟩,
⟨0,2,5,16,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 7 1,.s 7 1,.s 7 1,.s 7 1]⟩,
⟨0,2,6,13,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 13 3,.s 13 3,.s 13 3,.s 13 3]⟩,
⟨0,2,7,15,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 17 2,.s 17 2,.s 17 2,.s 17 2]⟩,
⟨0,2,8,14,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 15 4,.s 15 4,.s 15 4,.s 15 4]⟩]⟩,
⟨2,-1,1,-1,0,[(0,1,1),(-1,-1,1)],0,1,1,1,-1,-1,1,1,9,1,1,9,
[⟨-2,1,0,3,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨5,0,0,0,0,0,0,0,0⟩,.f ⟨5,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0],[.f ⟨6,1,0,0,1,0,0,0,0⟩,.s 1 0,.f ⟨6,1,0,1,2,0,0,0,0⟩,.s 1 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.f ⟨5,0,0,0,0,0,0,0,0⟩,.f ⟨5,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0]⟩,
⟨-2,1,1,10,[[.f ⟨5,0,0,0,1,0,0,0,0⟩,.f ⟨5,0,1,0,2,0,0,0,0⟩,.s 0 0,.s 0 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨5,1,0,0,0,0,0,0,0⟩,.f ⟨5,1,1,0,1,0,0,0,0⟩,.s 1 0,.s 1 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.f ⟨5,1,0,0,0,0,0,0,1⟩,.f ⟨5,1,1,0,1,0,0,0,1⟩,.s 1 1,.s 1 1]⟩,
⟨-2,1,2,4,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.f ⟨5,2,0,0,0,0,0,0,0⟩,.f ⟨5,2,1,0,1,0,0,0,0⟩,.s 2 0,.s 2 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 0 3,.s 0 3,.s 0 3,.s 0 3]⟩,
⟨-2,1,3,9,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.f ⟨5,3,0,0,0,0,0,0,0⟩,.f ⟨5,3,1,0,1,0,0,0,0⟩,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.f ⟨5,3,0,0,0,0,0,0,1⟩,.f ⟨5,3,1,0,1,0,0,0,1⟩,.s 3 1,.s 3 1]⟩,
⟨-2,1,4,5,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨5,4,0,0,0,0,0,0,0⟩,.f ⟨5,4,1,0,1,0,0,0,0⟩,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 2 3,.s 2 3,.s 2 3,.s 2 3]⟩,
⟨-2,1,5,8,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.f ⟨5,5,0,0,0,0,0,0,0⟩,.f ⟨5,5,1,0,1,0,0,0,0⟩,.s 5 0,.s 5 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.f ⟨5,5,0,0,0,0,0,0,1⟩,.f ⟨5,5,1,0,1,0,0,0,1⟩,.s 5 1,.s 5 1]⟩,
⟨-2,1,6,6,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨5,6,0,0,0,0,0,0,0⟩,.f ⟨5,6,1,0,1,0,0,0,0⟩,.s 6 0,.s 6 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 4 3,.s 4 3,.s 4 3,.s 4 3]⟩,
⟨-2,1,7,7,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.f ⟨5,5,0,0,0,0,0,0,0⟩,.f ⟨5,5,1,0,1,0,0,0,0⟩,.s 5 0,.s 5 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.f ⟨5,7,0,0,0,0,0,0,0⟩,.f ⟨5,7,1,0,1,0,0,0,0⟩,.s 7 0,.s 7 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.f ⟨5,7,0,0,0,0,0,0,2⟩,.f ⟨5,7,1,0,1,0,0,0,2⟩,.s 7 2,.s 7 2]⟩,
⟨-2,1,8,6,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨5,6,0,0,0,0,0,0,0⟩,.f ⟨5,6,1,0,1,0,0,0,0⟩,.s 6 0,.s 6 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.f ⟨5,8,0,0,0,0,0,0,0⟩,.f ⟨5,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0]],[.f ⟨5,6,0,0,0,0,0,0,3⟩,.f ⟨5,6,1,0,1,0,0,0,3⟩,.s 6 3,.s 6 3]⟩]⟩,
⟨2,-1,0,-1,-1,[(-1,1,1),(0,-1,1)],-1,1,1,1,0,-1,1,1,1,9,9,1,
[⟨-2,-1,0,17,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨1,0,0,0,0,0,0,0,0⟩,.s 0 0,.f ⟨1,0,0,1,1,0,0,0,0⟩,.s 0 0],[.f ⟨1,1,0,0,1,0,0,0,0⟩,.s 1 0,.f ⟨1,1,0,1,2,0,0,0,0⟩,.s 1 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 2 0,.s 0 0,.s 2 0,.s 0 0]⟩,
⟨-2,-1,1,10,[[.f ⟨6,0,0,0,1,0,0,0,0⟩,.f ⟨6,0,1,0,2,0,0,0,0⟩,.s 0 0,.s 0 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨1,1,0,0,0,0,0,0,0⟩,.s 1 0,.f ⟨1,1,0,1,1,0,0,0,0⟩,.s 1 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.f ⟨6,0,0,0,1,0,0,0,2⟩,.f ⟨6,0,1,0,2,0,0,0,2⟩,.s 0 2,.s 0 2]⟩,
⟨-2,-1,2,16,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.f ⟨1,2,0,0,0,0,0,0,0⟩,.s 2 0,.f ⟨1,2,0,1,1,0,0,0,0⟩,.s 2 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 4 0,.s 2 1,.s 4 0,.s 2 1]⟩,
⟨-2,-1,3,11,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.f ⟨1,3,0,0,0,0,0,0,0⟩,.s 3 0,.f ⟨1,3,0,1,1,0,0,0,0⟩,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 1 3,.s 1 3,.s 1 3,.s 1 3]⟩,
⟨-2,-1,4,15,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨1,4,0,0,0,0,0,0,0⟩,.s 4 0,.f ⟨1,4,0,1,1,0,0,0,0⟩,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 6 0,.s 4 1,.s 6 0,.s 4 1]⟩,
⟨-2,-1,5,12,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.f ⟨1,5,0,0,0,0,0,0,0⟩,.s 5 0,.f ⟨1,5,0,1,1,0,0,0,0⟩,.s 5 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.s 3 3,.s 3 3,.s 3 3,.s 3 3]⟩,
⟨-2,-1,6,14,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨1,6,0,0,0,0,0,0,0⟩,.s 6 0,.f ⟨1,6,0,1,1,0,0,0,0⟩,.s 6 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 8 0,.s 6 1,.s 8 0,.s 6 1]⟩,
⟨-2,-1,7,12,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.f ⟨1,5,0,0,0,0,0,0,0⟩,.s 5 0,.f ⟨1,5,0,1,1,0,0,0,0⟩,.s 5 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.f ⟨1,7,0,0,0,0,0,0,0⟩,.s 7 0,.f ⟨1,7,0,1,1,0,0,0,0⟩,.s 7 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.f ⟨1,5,0,0,0,0,0,0,3⟩,.s 5 3,.f ⟨1,5,0,1,1,0,0,0,3⟩,.s 5 3]⟩,
⟨-2,-1,8,13,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨1,6,0,0,0,0,0,0,0⟩,.s 6 0,.f ⟨1,6,0,1,1,0,0,0,0⟩,.s 6 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.f ⟨1,8,0,0,0,0,0,0,0⟩,.s 8 0,.f ⟨1,8,0,1,1,0,0,0,0⟩,.s 8 0]],[.s 7 4,.s 7 4,.s 7 4,.s 7 4]⟩]⟩]

set_option maxRecDepth 100000 in
noncomputable def certsData : List (List (List (Bool × ℕ × ℕ))) := [
[[],[(false,0,1),(false,2,1),(true,2,1)],[(false,1,1),(false,2,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,1,1),(false,3,1),(true,2,1)],[(false,0,1),(false,3,1),(true,2,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,2,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,3,1),(true,1,1)],[(false,0,1),(false,3,1),(true,1,1)],[(false,3,1),(true,0,1)],[(false,2,1),(true,1,1)]],
[[(false,0,1),(false,2,1),(true,2,2)],[],[(false,1,1),(true,2,1)],[(false,0,1),(false,2,1),(true,0,2)],[(false,2,1),(true,2,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,2,1),(true,1,2)],[(false,1,1),(true,1,1)],[(false,2,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,2,1),(true,0,2)],[(false,0,1),(true,0,1)]],
[[(false,0,1),(false,2,1),(true,1,2)],[(false,0,1),(true,2,1)],[],[(false,1,1),(false,2,1),(true,0,2)],[(false,1,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,1),(true,2,2)],[(false,0,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(false,2,1),(true,1,2)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,2,1),(true,0,1)]],
[[(false,2,1),(true,1,1)],[(false,0,1),(false,2,1),(true,2,1)],[(false,0,1),(false,2,1),(true,1,1)],[],[(false,1,1),(false,2,1),(true,0,1)],[(false,0,1),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(false,2,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,1)]],
[[(false,0,1),(false,2,1),(true,3,2)],[(false,2,1),(true,2,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,2,1),(true,1,2)],[],[(false,1,1),(true,2,1)],[(false,0,1),(false,2,1),(true,0,2)],[(false,0,1),(true,1,1)],[(false,0,1),(false,2,1),(true,0,2)],[(false,0,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,2,1),(true,1,1)],[(false,1,1),(true,0,1)]],
[[(false,0,1),(false,2,1),(true,0,2)],[(false,1,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,1),(true,2,2)],[(false,0,1),(true,2,1)],[],[(false,1,1),(false,2,1),(true,0,2)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(false,2,1),(true,1,2)]],
[[(false,2,1),(true,0,1)],[(false,1,1),(false,2,1),(true,0,1)],[(false,0,1),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,1),(true,2,1)],[(false,0,1),(false,2,1),(true,1,1)],[],[(false,1,1),(false,2,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,2,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,1,1),(true,1,1)]],
[[(false,0,1),(false,1,1),(true,2,2)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(false,1,1),(true,0,2)],[(false,0,1),(true,2,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,2)],[],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,2)],[(false,0,1),(true,0,1)],[(false,0,1),(false,1,1),(true,0,2)],[(false,1,1),(true,0,1)]],
[[(false,0,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,2),(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,1,1),(true,0,1)],[],[(false,0,1),(true,1,1)],[(false,0,2),(false,1,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,2),(false,1,1),(true,0,1)]],
[[(false,1,1),(true,3,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,1)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,2,1)],[(false,1,1),(true,0,1)],[(false,0,1),(false,1,2),(true,0,1)],[(false,1,1),(true,0,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,1)],[(false,0,1),(true,0,1)]],
[[(false,0,1),(false,1,1),(true,3,2)],[(false,0,1),(true,2,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,2)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(false,1,1),(true,0,2)],[(false,0,1),(true,0,1)],[(false,0,1),(false,1,1),(true,0,2)],[(false,1,1),(true,0,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,2)]],
[[(false,0,1),(true,3,1)],[(false,0,2),(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,1,1),(true,2,1)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,2),(false,1,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,2),(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[],[(false,0,1),(true,1,1)]],
[[(false,1,1),(true,2,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,2,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,1)],[(false,1,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(false,1,2),(true,0,1)],[(false,1,1),(true,0,1)],[]]]

noncomputable def cfg : GalCert.Cfg 9 := ⟨adjL, (0, 0, 1), 9, regsData, certsData, 0, 1⟩

set_option maxRecDepth 100000 in
theorem hh : cfg.head = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr0 : cfg.regOk 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr1 : cfg.regOk 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr2 : cfg.regOk 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr3 : cfg.regOk 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr4 : cfg.regOk 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr5 : cfg.regOk 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr6 : cfg.regOk 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr7 : cfg.regOk 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr8 : cfg.regOk 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr9 : cfg.regOk 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr10 : cfg.regOk 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr11 : cfg.regOk 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr12 : cfg.regOk 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq0 : cfg.certRow 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq1 : cfg.certRow 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq2 : cfg.certRow 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq3 : cfg.certRow 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq4 : cfg.certRow 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq5 : cfg.certRow 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq6 : cfg.certRow 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq7 : cfg.certRow 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq8 : cfg.certRow 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq9 : cfg.certRow 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq10 : cfg.certRow 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq11 : cfg.certRow 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq12 : cfg.certRow 12 = true := by decide +kernel

theorem hc : cfg.check = true := by
  have e : cfg.regs.length = 13 := by decide +kernel
  refine GalCert.Cfg.check_of_parts cfg hh (fun r hr => ?_) (fun r hr => ?_) <;> rw [e] at hr <;> interval_cases r
  exacts [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12]

set_option maxHeartbeats 0 in
theorem hV : cfg.vbound 26 = true := by decide +kernel

theorem ha (n : ℕ) (hn : 1 ≤ n) : ((a n : ℕ) : ℤ) = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := SGB.ncard_succ hT v0 k
  unfold a
  rw [h]
  exact GalCert.Cfg.card_step hc k

set_option maxRecDepth 100000 in
def Avals : List ℕ := [1,4,8,13,17,23,27,32,36,40,44,48,53,57,63,67,72,76,80,84,88,93,97,103,107,112,116,120,124,128,133,137,143,147,152,156,160,164,168,173,177,183,187,192,196,200,204,208,213,217,223,227,232,236,240,244]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA0 : (List.range' 0 4).map cfg.Af = [1,4,8,13] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA1 : (List.range' 4 4).map cfg.Af = [17,23,27,32] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA2 : (List.range' 8 4).map cfg.Af = [36,40,44,48] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA3 : (List.range' 12 4).map cfg.Af = [53,57,63,67] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA4 : (List.range' 16 4).map cfg.Af = [72,76,80,84] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA5 : (List.range' 20 4).map cfg.Af = [88,93,97,103] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA6 : (List.range' 24 4).map cfg.Af = [107,112,116,120] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA7 : (List.range' 28 4).map cfg.Af = [124,128,133,137] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA8 : (List.range' 32 4).map cfg.Af = [143,147,152,156] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA9 : (List.range' 36 4).map cfg.Af = [160,164,168,173] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA10 : (List.range' 40 4).map cfg.Af = [177,183,187,192] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA11 : (List.range' 44 4).map cfg.Af = [196,200,204,208] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA12 : (List.range' 48 4).map cfg.Af = [213,217,223,227] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA13 : (List.range' 52 4).map cfg.Af = [232,236,240,244] := by decide +kernel

set_option maxRecDepth 100000 in
theorem hAv : (List.range 56).map cfg.Af = Avals := by
  rw [List.range_eq_range']
  exact GalCert.Cfg.rmap_app cfg.Af 0 4 52 hA0 (GalCert.Cfg.rmap_app cfg.Af 4 4 48 hA1 (GalCert.Cfg.rmap_app cfg.Af 8 4 44 hA2 (GalCert.Cfg.rmap_app cfg.Af 12 4 40 hA3 (GalCert.Cfg.rmap_app cfg.Af 16 4 36 hA4 (GalCert.Cfg.rmap_app cfg.Af 20 4 32 hA5 (GalCert.Cfg.rmap_app cfg.Af 24 4 28 hA6 (GalCert.Cfg.rmap_app cfg.Af 28 4 24 hA7 (GalCert.Cfg.rmap_app cfg.Af 32 4 20 hA8 (GalCert.Cfg.rmap_app cfg.Af 36 4 16 hA9 (GalCert.Cfg.rmap_app cfg.Af 40 4 12 hA10 (GalCert.Cfg.rmap_app cfg.Af 44 4 8 hA11 (GalCert.Cfg.rmap_app cfg.Af 48 4 4 hA12 (hA13)))))))))))))

set_option maxHeartbeats 0 in
theorem hrec : ∀ k, (([(1, 11), (-1, 10), (-1, 2), (1, 1)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide)
    (GalCert.Cfg.window_of_list hAv _ _ (by decide +kernel) (by decide +kernel))

set_option maxHeartbeats 0 in
theorem hgfw : ∀ n < 26 + 2 * cfg.L, ((GalCert.csOf [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] 11).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.window_of_list hAv _ _ (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
theorem hsmall : ∀ n < 11, GalCert.conv (fun n => ((a n : ℕ) : ℤ)) [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] n = ([1, 3, 4, 5, 4, 6, 4, 5, 4, 3, 1] : List ℤ).getD n 0 := by
  have e : (fun n => ((a n : ℕ) : ℤ)) = fun n => if n = 0 then 1 else if n < 56 then (Avals.getD n 0 : ℤ) else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [ha0]
    · have h0 : n ≠ 0 := by omega
      rw [if_neg h0]
      split_ifs with h2
      · rw [ha n h, GalCert.Cfg.A_of_list hAv h2]
      · exact ha n h
  rw [e]
  decide +kernel

theorem hZ : PowerSeries.mk (fun n => ((a n : ℕ) : ℤ)) * GalCert.polyOf [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] = GalCert.polyOf [1, 3, 4, 5, 4, 6, 4, 5, 4, 3, 1] :=
  GalCert.Cfg.gf_from hc hV _ (fun n hn => ha n hn) _ _ 11 (by decide) (by decide) hgfw hsmall

end P311993

open PowerSeries OMA.S_oeis_a311993 in
theorem OMA.solution : type_of% @OMA.S_oeis_a311993.main := by
  refine ⟨?_, ?_⟩
  · have hQ := congrArg (PowerSeries.map (Int.castRingHom ℚ)) P311993.hZ
    rw [map_mul] at hQ
    have hm : PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk fun n => ((a n : ℕ) : ℤ)) =
        PowerSeries.mk fun n => ((a n : ℕ) : ℚ) := by
      ext n; simp [PowerSeries.coeff_map]
    have hD : ((X ^ 10 - X ^ 9 - X + 1) : PowerSeries ℚ) = PowerSeries.map (Int.castRingHom ℚ) (GalCert.polyOf [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1]) := by
      simp [GalCert.polyOf, map_ofNat]; ring
    have hP : (X ^ 10 + 3 * X ^ 9 + 4 * X ^ 8 + 5 * X ^ 7 + 4 * X ^ 6 + 6 * X ^ 5 + 4 * X ^ 4 + 5 * X ^ 3 + 4 * X ^ 2 + 3 * X + 1 : PowerSeries ℚ) = PowerSeries.map (Int.castRingHom ℚ) (GalCert.polyOf [1, 3, 4, 5, 4, 6, 4, 5, 4, 3, 1]) := by
      simp [GalCert.polyOf, map_ofNat]; ring
    rw [hD, hP, ← hm]
    exact hQ
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    have h := P311993.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 11 - 1 = k + 10 by omega,
      show k + 11 - 9 = k + 2 by omega,
      show k + 11 - 10 = k + 1 by omega,
      P311993.ha (k + 11) (by omega),
      P311993.ha (k + 10) (by omega),
      P311993.ha (k + 2) (by omega),
      P311993.ha (k + 1) (by omega)]
    linarith
