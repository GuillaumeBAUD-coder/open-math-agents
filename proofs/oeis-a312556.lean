import OMAStatements.S_oeis_a312556
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A312556.

Method: an explicit distance certificate. Every vertex outside the origin cell lies on one of the
rays through the vertices of the growth polygon or in one of the cones between them (split into a
finite corner, two boundary strips and an interior), and is written as base + k T + j U with a base
from a finite list. The certificate gives the distance of each code as v + lT k + lU j, with step
costs lT, lU read off the growth polygon in each region. A Boolean
checker, evaluated by the kernel, verifies that every neighbour of a coded vertex has a code of
value at most one more, that every coded vertex other than the base vertex has a neighbour of value
exactly one less, and that codes are injective. So the ball of radius n is the image of the codes
of value at most n, and the coordination sequence is a sum of explicit quasi-linear counts, which
satisfies both conjectures. The certificate data was produced by a script.
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


namespace P312556
open OMA.S_oeis_a312556

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 11) := [
⟨0,0,0,0,0,[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨0,0,0,0,[[.f ⟨10,11,0,0,0,0,0,0,0⟩],[.f ⟨14,2,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨4,0,0,0,0,0,0,0,0⟩]],[.f ⟨0,0,0,0,0,0,0,0,0⟩]⟩,
⟨0,0,1,1,[[.f ⟨10,12,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.f ⟨4,1,0,0,0,0,0,0,0⟩]],[.s 0 2]⟩,
⟨0,0,2,10,[[.f ⟨10,13,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨26,66,0,0,0,0,0,0,0⟩],[.f ⟨4,2,0,0,0,0,0,0,0⟩]],[.s 4 2]⟩,
⟨0,0,3,2,[[.f ⟨10,14,0,0,0,0,0,0,0⟩],[.f ⟨10,16,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.f ⟨4,3,0,0,0,0,0,0,0⟩]],[.s 1 2]⟩,
⟨0,0,4,9,[[.f ⟨10,15,0,0,0,0,0,0,0⟩],[.f ⟨10,17,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.f ⟨4,4,0,0,0,0,0,0,0⟩]],[.f ⟨10,17,0,0,0,0,0,0,3⟩]⟩,
⟨0,0,5,3,[[.f ⟨10,16,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.f ⟨4,3,0,0,0,0,0,0,0⟩],[.f ⟨4,5,0,0,0,0,0,0,0⟩]],[.s 3 3]⟩,
⟨0,0,6,8,[[.f ⟨10,17,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.f ⟨4,4,0,0,0,0,0,0,0⟩],[.f ⟨4,6,0,0,0,0,0,0,0⟩]],[.s 8 1]⟩,
⟨0,0,7,4,[[.f ⟨10,18,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.f ⟨4,7,0,0,0,0,0,0,0⟩],[.f ⟨4,9,0,0,0,0,0,0,0⟩]],[.s 5 2]⟩,
⟨0,0,8,7,[[.f ⟨10,19,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.f ⟨4,8,0,0,0,0,0,0,0⟩],[.f ⟨4,10,0,0,0,0,0,0,0⟩]],[.s 10 2]⟩,
⟨0,0,9,5,[[.f ⟨10,18,0,0,0,0,0,0,0⟩],[.f ⟨10,20,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.f ⟨4,9,0,0,0,0,0,0,0⟩]],[.f ⟨10,18,0,0,0,0,0,0,4⟩]⟩,
⟨0,0,10,6,[[.f ⟨10,19,0,0,0,0,0,0,0⟩],[.f ⟨10,21,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.f ⟨4,10,0,0,0,0,0,0,0⟩]],[.s 9 3]⟩]⟩,
⟨1,-2,-1,0,0,[(1,-2,0),(-1,2,0),(-2,-1,5)],-2,-1,5,5,0,0,0,0,11,0,0,0,
[⟨-2,-1,0,11,[[.f ⟨31,11,0,0,0,0,0,0,0⟩,.f ⟨31,11,0,0,0,1,0,1,0⟩],[.f ⟨15,2,0,0,0,0,0,0,0⟩,.f ⟨15,2,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨12,0,0,0,0,0,0,0,0⟩,.f ⟨13,0,1,0,0,0,0,0,0⟩]],[.s 1 1,.s 1 1]⟩,
⟨-2,-1,1,10,[[.f ⟨31,12,0,0,0,0,0,0,0⟩,.f ⟨31,12,0,0,0,1,0,1,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨12,1,0,0,0,0,0,0,0⟩,.f ⟨13,1,1,0,0,0,0,0,0⟩]],[.s 3 2,.s 3 2]⟩,
⟨-2,-1,2,3,[[.f ⟨31,13,0,0,0,0,0,0,0⟩,.f ⟨31,13,0,0,0,1,0,1,0⟩],[.s 4 0,.s 4 0],[.f ⟨10,0,0,0,0,0,0,0,0⟩,.f ⟨31,0,0,0,0,1,0,0,0⟩],[.f ⟨12,2,0,0,0,0,0,0,0⟩,.f ⟨13,2,1,0,0,0,0,0,0⟩]],[.f ⟨10,0,0,0,0,0,0,0,1⟩,.f ⟨31,0,0,0,0,1,0,0,1⟩]⟩,
⟨-2,-1,3,9,[[.f ⟨31,14,0,0,0,0,0,0,0⟩,.f ⟨31,14,0,0,0,1,0,1,0⟩],[.f ⟨31,16,0,0,0,0,0,0,0⟩,.f ⟨31,16,0,0,0,1,0,1,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨12,3,0,0,0,0,0,0,0⟩,.f ⟨13,3,1,0,0,0,0,0,0⟩]],[.s 5 1,.s 5 1]⟩,
⟨-2,-1,4,4,[[.f ⟨31,15,0,0,0,0,0,0,0⟩,.f ⟨31,15,0,0,0,1,0,1,0⟩],[.f ⟨31,17,0,0,0,0,0,0,0⟩,.f ⟨31,17,0,0,0,1,0,1,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨12,4,0,0,0,0,0,0,0⟩,.f ⟨13,4,1,0,0,0,0,0,0⟩]],[.s 2 1,.s 2 1]⟩,
⟨-2,-1,5,8,[[.f ⟨31,16,0,0,0,0,0,0,0⟩,.f ⟨31,16,0,0,0,1,0,1,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨12,3,0,0,0,0,0,0,0⟩,.f ⟨13,3,1,0,0,0,0,0,0⟩],[.f ⟨12,5,0,0,0,0,0,0,0⟩,.f ⟨13,5,1,0,0,0,0,0,0⟩]],[.s 7 1,.s 7 1]⟩,
⟨-2,-1,6,4,[[.f ⟨31,17,0,0,0,0,0,0,0⟩,.f ⟨31,17,0,0,0,1,0,1,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨12,4,0,0,0,0,0,0,0⟩,.f ⟨13,4,1,0,0,0,0,0,0⟩],[.f ⟨12,6,0,0,0,0,0,0,0⟩,.f ⟨13,6,1,0,0,0,0,0,0⟩]],[.f ⟨12,4,0,0,0,0,0,0,1⟩,.f ⟨13,4,1,0,0,0,0,0,1⟩]⟩,
⟨-2,-1,7,7,[[.f ⟨31,18,0,0,0,0,0,0,0⟩,.f ⟨31,18,0,0,0,1,0,1,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨12,7,0,0,0,0,0,0,0⟩,.f ⟨13,7,1,0,0,0,0,0,0⟩],[.f ⟨12,9,0,0,0,0,0,0,0⟩,.f ⟨13,9,1,0,0,0,0,0,0⟩]],[.f ⟨12,9,0,0,0,0,0,0,0⟩,.f ⟨13,9,1,0,0,0,0,0,0⟩]⟩,
⟨-2,-1,8,5,[[.f ⟨31,19,0,0,0,0,0,0,0⟩,.f ⟨31,19,0,0,0,1,0,1,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨12,8,0,0,0,0,0,0,0⟩,.f ⟨13,8,1,0,0,0,0,0,0⟩],[.f ⟨12,10,0,0,0,0,0,0,0⟩,.f ⟨13,10,1,0,0,0,0,0,0⟩]],[.s 6 2,.s 6 2]⟩,
⟨-2,-1,9,7,[[.f ⟨31,18,0,0,0,0,0,0,0⟩,.f ⟨31,18,0,0,0,1,0,1,0⟩],[.f ⟨31,20,0,0,0,0,0,0,0⟩,.f ⟨31,20,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨12,9,0,0,0,0,0,0,0⟩,.f ⟨13,9,1,0,0,0,0,0,0⟩]],[.s 10 3,.s 10 3]⟩,
⟨-2,-1,10,6,[[.f ⟨31,19,0,0,0,0,0,0,0⟩,.f ⟨31,19,0,0,0,1,0,1,0⟩],[.f ⟨31,21,0,0,0,0,0,0,0⟩,.f ⟨31,21,0,0,0,1,0,1,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨12,10,0,0,0,0,0,0,0⟩,.f ⟨13,10,1,0,0,0,0,0,0⟩]],[.s 8 2,.s 8 2]⟩]⟩,
⟨0,0,0,0,0,[(1,2,0),(-1,-2,0),(2,-1,1),(-2,1,-5)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨2,-1,0,11,[[.f ⟨14,22,0,0,0,0,0,0,0⟩],[.f ⟨14,35,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨16,0,0,0,0,0,0,0,0⟩]],[.s 1 1]⟩,
⟨2,-1,1,10,[[.f ⟨14,23,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.f ⟨16,1,0,0,0,0,0,0,0⟩]],[.s 3 2]⟩,
⟨2,-1,2,3,[[.f ⟨14,24,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨4,11,0,0,0,0,0,0,0⟩],[.f ⟨16,2,0,0,0,0,0,0,0⟩]],[.f ⟨14,24,0,0,0,0,0,0,3⟩]⟩,
⟨2,-1,3,9,[[.f ⟨14,25,0,0,0,0,0,0,0⟩],[.f ⟨14,27,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.f ⟨16,3,0,0,0,0,0,0,0⟩]],[.f ⟨14,27,0,0,0,0,0,0,3⟩]⟩,
⟨2,-1,4,4,[[.f ⟨14,26,0,0,0,0,0,0,0⟩],[.f ⟨14,28,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.f ⟨16,4,0,0,0,0,0,0,0⟩]],[.f ⟨14,26,0,0,0,0,0,0,4⟩]⟩,
⟨2,-1,5,9,[[.f ⟨14,27,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.f ⟨16,3,0,0,0,0,0,0,0⟩],[.f ⟨16,5,0,0,0,0,0,0,0⟩]],[.f ⟨14,27,0,0,0,0,0,0,4⟩]⟩,
⟨2,-1,6,5,[[.f ⟨14,28,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.f ⟨16,4,0,0,0,0,0,0,0⟩],[.f ⟨16,6,0,0,0,0,0,0,0⟩]],[.f ⟨14,28,0,0,0,0,0,0,4⟩]⟩,
⟨2,-1,7,8,[[.f ⟨14,29,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.f ⟨16,7,0,0,0,0,0,0,0⟩],[.f ⟨16,9,0,0,0,0,0,0,0⟩]],[.f ⟨14,29,0,0,0,0,0,0,3⟩]⟩,
⟨2,-1,8,6,[[.f ⟨14,30,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.f ⟨16,8,0,0,0,0,0,0,0⟩],[.f ⟨16,10,0,0,0,0,0,0,0⟩]],[.f ⟨14,30,0,0,0,0,0,0,3⟩]⟩,
⟨2,-1,9,7,[[.f ⟨14,29,0,0,0,0,0,0,0⟩],[.f ⟨14,31,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.f ⟨16,9,0,0,0,0,0,0,0⟩]],[.f ⟨14,31,0,0,0,0,0,0,4⟩]⟩,
⟨2,-1,10,6,[[.f ⟨14,30,0,0,0,0,0,0,0⟩],[.f ⟨14,32,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.f ⟨16,10,0,0,0,0,0,0,0⟩]],[.f ⟨14,30,0,0,0,0,0,0,4⟩]⟩]⟩,
⟨1,4,-2,0,0,[(1,2,0),(-1,-2,0),(2,-1,10)],2,-1,10,10,0,0,0,0,22,0,0,0,
[⟨4,-2,0,22,[[.f ⟨14,55,0,0,0,0,0,0,0⟩,.f ⟨14,55,1,0,1,0,0,0,0⟩],[.f ⟨14,2,0,0,1,0,0,0,0⟩,.f ⟨14,2,1,0,2,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨17,0,0,0,0,0,0,0,0⟩,.f ⟨17,0,1,0,1,0,0,0,0⟩]],[.s 1 1,.s 1 1]⟩,
⟨4,-2,1,21,[[.f ⟨14,56,0,0,0,0,0,0,0⟩,.f ⟨14,56,1,0,1,0,0,0,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨17,1,0,0,0,0,0,0,0⟩,.f ⟨17,1,1,0,1,0,0,0,0⟩]],[.s 3 2,.s 3 2]⟩,
⟨4,-2,2,14,[[.f ⟨14,57,0,0,0,0,0,0,0⟩,.f ⟨14,57,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.f ⟨18,0,0,0,0,0,0,0,0⟩,.f ⟨19,22,1,0,0,0,0,0,0⟩],[.f ⟨17,2,0,0,0,0,0,0,0⟩,.f ⟨17,2,1,0,1,0,0,0,0⟩]],[.f ⟨14,57,0,0,0,0,0,0,3⟩,.f ⟨14,57,1,0,1,0,0,0,3⟩]⟩,
⟨4,-2,3,20,[[.f ⟨14,58,0,0,0,0,0,0,0⟩,.f ⟨14,58,1,0,1,0,0,0,0⟩],[.f ⟨14,60,0,0,0,0,0,0,0⟩,.f ⟨14,60,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨17,3,0,0,0,0,0,0,0⟩,.f ⟨17,3,1,0,1,0,0,0,0⟩]],[.f ⟨14,60,0,0,0,0,0,0,3⟩,.f ⟨14,60,1,0,1,0,0,0,3⟩]⟩,
⟨4,-2,4,15,[[.f ⟨14,59,0,0,0,0,0,0,0⟩,.f ⟨14,59,1,0,1,0,0,0,0⟩],[.f ⟨14,61,0,0,0,0,0,0,0⟩,.f ⟨14,61,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨17,4,0,0,0,0,0,0,0⟩,.f ⟨17,4,1,0,1,0,0,0,0⟩]],[.f ⟨14,59,0,0,0,0,0,0,4⟩,.f ⟨14,59,1,0,1,0,0,0,4⟩]⟩,
⟨4,-2,5,20,[[.f ⟨14,60,0,0,0,0,0,0,0⟩,.f ⟨14,60,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨17,3,0,0,0,0,0,0,0⟩,.f ⟨17,3,1,0,1,0,0,0,0⟩],[.f ⟨17,5,0,0,0,0,0,0,0⟩,.f ⟨17,5,1,0,1,0,0,0,0⟩]],[.f ⟨14,60,0,0,0,0,0,0,4⟩,.f ⟨14,60,1,0,1,0,0,0,4⟩]⟩,
⟨4,-2,6,16,[[.f ⟨14,61,0,0,0,0,0,0,0⟩,.f ⟨14,61,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨17,4,0,0,0,0,0,0,0⟩,.f ⟨17,4,1,0,1,0,0,0,0⟩],[.f ⟨17,6,0,0,0,0,0,0,0⟩,.f ⟨17,6,1,0,1,0,0,0,0⟩]],[.f ⟨14,61,0,0,0,0,0,0,4⟩,.f ⟨14,61,1,0,1,0,0,0,4⟩]⟩,
⟨4,-2,7,19,[[.f ⟨14,62,0,0,0,0,0,0,0⟩,.f ⟨14,62,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨17,7,0,0,0,0,0,0,0⟩,.f ⟨17,7,1,0,1,0,0,0,0⟩],[.f ⟨17,9,0,0,0,0,0,0,0⟩,.f ⟨17,9,1,0,1,0,0,0,0⟩]],[.f ⟨14,62,0,0,0,0,0,0,3⟩,.f ⟨14,62,1,0,1,0,0,0,3⟩]⟩,
⟨4,-2,8,17,[[.f ⟨14,63,0,0,0,0,0,0,0⟩,.f ⟨14,63,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨17,8,0,0,0,0,0,0,0⟩,.f ⟨17,8,1,0,1,0,0,0,0⟩],[.f ⟨17,10,0,0,0,0,0,0,0⟩,.f ⟨17,10,1,0,1,0,0,0,0⟩]],[.f ⟨14,63,0,0,0,0,0,0,3⟩,.f ⟨14,63,1,0,1,0,0,0,3⟩]⟩,
⟨4,-2,9,18,[[.f ⟨14,62,0,0,0,0,0,0,0⟩,.f ⟨14,62,1,0,1,0,0,0,0⟩],[.f ⟨14,64,0,0,0,0,0,0,0⟩,.f ⟨14,64,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨17,9,0,0,0,0,0,0,0⟩,.f ⟨17,9,1,0,1,0,0,0,0⟩]],[.f ⟨14,64,0,0,0,0,0,0,4⟩,.f ⟨14,64,1,0,1,0,0,0,4⟩]⟩,
⟨4,-2,10,17,[[.f ⟨14,63,0,0,0,0,0,0,0⟩,.f ⟨14,63,1,0,1,0,0,0,0⟩],[.f ⟨14,65,0,0,0,0,0,0,0⟩,.f ⟨14,65,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨17,10,0,0,0,0,0,0,0⟩,.f ⟨17,10,1,0,1,0,0,0,0⟩]],[.f ⟨14,63,0,0,0,0,0,0,4⟩,.f ⟨14,63,1,0,1,0,0,0,4⟩]⟩,
⟨6,-3,0,33,[[.f ⟨14,22,0,0,1,0,0,0,0⟩,.f ⟨14,22,1,0,2,0,0,0,0⟩],[.f ⟨14,35,0,0,1,0,0,0,0⟩,.f ⟨14,35,1,0,2,0,0,0,0⟩],[.s 12 0,.s 12 0],[.f ⟨17,11,0,0,0,0,0,0,0⟩,.f ⟨17,11,1,0,1,0,0,0,0⟩]],[.s 12 1,.s 12 1]⟩,
⟨6,-3,1,32,[[.f ⟨14,23,0,0,1,0,0,0,0⟩,.f ⟨14,23,1,0,2,0,0,0,0⟩],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨17,12,0,0,0,0,0,0,0⟩,.f ⟨17,12,1,0,1,0,0,0,0⟩]],[.s 14 2,.s 14 2]⟩,
⟨6,-3,2,25,[[.f ⟨14,24,0,0,1,0,0,0,0⟩,.f ⟨14,24,1,0,2,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨19,0,0,0,0,0,0,0,0⟩,.f ⟨19,0,1,0,1,0,0,0,0⟩],[.f ⟨17,13,0,0,0,0,0,0,0⟩,.f ⟨17,13,1,0,1,0,0,0,0⟩]],[.f ⟨14,24,0,0,1,0,0,0,3⟩,.f ⟨14,24,1,0,2,0,0,0,3⟩]⟩,
⟨6,-3,3,31,[[.f ⟨14,25,0,0,1,0,0,0,0⟩,.f ⟨14,25,1,0,2,0,0,0,0⟩],[.f ⟨14,27,0,0,1,0,0,0,0⟩,.f ⟨14,27,1,0,2,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨17,14,0,0,0,0,0,0,0⟩,.f ⟨17,14,1,0,1,0,0,0,0⟩]],[.f ⟨14,27,0,0,1,0,0,0,3⟩,.f ⟨14,27,1,0,2,0,0,0,3⟩]⟩,
⟨6,-3,4,26,[[.f ⟨14,26,0,0,1,0,0,0,0⟩,.f ⟨14,26,1,0,2,0,0,0,0⟩],[.f ⟨14,28,0,0,1,0,0,0,0⟩,.f ⟨14,28,1,0,2,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨17,15,0,0,0,0,0,0,0⟩,.f ⟨17,15,1,0,1,0,0,0,0⟩]],[.f ⟨14,26,0,0,1,0,0,0,4⟩,.f ⟨14,26,1,0,2,0,0,0,4⟩]⟩,
⟨6,-3,5,31,[[.f ⟨14,27,0,0,1,0,0,0,0⟩,.f ⟨14,27,1,0,2,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨17,14,0,0,0,0,0,0,0⟩,.f ⟨17,14,1,0,1,0,0,0,0⟩],[.f ⟨17,16,0,0,0,0,0,0,0⟩,.f ⟨17,16,1,0,1,0,0,0,0⟩]],[.f ⟨14,27,0,0,1,0,0,0,4⟩,.f ⟨14,27,1,0,2,0,0,0,4⟩]⟩,
⟨6,-3,6,27,[[.f ⟨14,28,0,0,1,0,0,0,0⟩,.f ⟨14,28,1,0,2,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨17,15,0,0,0,0,0,0,0⟩,.f ⟨17,15,1,0,1,0,0,0,0⟩],[.f ⟨17,17,0,0,0,0,0,0,0⟩,.f ⟨17,17,1,0,1,0,0,0,0⟩]],[.f ⟨14,28,0,0,1,0,0,0,4⟩,.f ⟨14,28,1,0,2,0,0,0,4⟩]⟩,
⟨6,-3,7,30,[[.f ⟨14,29,0,0,1,0,0,0,0⟩,.f ⟨14,29,1,0,2,0,0,0,0⟩],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨17,18,0,0,0,0,0,0,0⟩,.f ⟨17,18,1,0,1,0,0,0,0⟩],[.f ⟨17,20,0,0,0,0,0,0,0⟩,.f ⟨17,20,1,0,1,0,0,0,0⟩]],[.f ⟨14,29,0,0,1,0,0,0,3⟩,.f ⟨14,29,1,0,2,0,0,0,3⟩]⟩,
⟨6,-3,8,28,[[.f ⟨14,30,0,0,1,0,0,0,0⟩,.f ⟨14,30,1,0,2,0,0,0,0⟩],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨17,19,0,0,0,0,0,0,0⟩,.f ⟨17,19,1,0,1,0,0,0,0⟩],[.f ⟨17,21,0,0,0,0,0,0,0⟩,.f ⟨17,21,1,0,1,0,0,0,0⟩]],[.f ⟨14,30,0,0,1,0,0,0,3⟩,.f ⟨14,30,1,0,2,0,0,0,3⟩]⟩,
⟨6,-3,9,29,[[.f ⟨14,29,0,0,1,0,0,0,0⟩,.f ⟨14,29,1,0,2,0,0,0,0⟩],[.f ⟨14,31,0,0,1,0,0,0,0⟩,.f ⟨14,31,1,0,2,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨17,20,0,0,0,0,0,0,0⟩,.f ⟨17,20,1,0,1,0,0,0,0⟩]],[.f ⟨14,31,0,0,1,0,0,0,4⟩,.f ⟨14,31,1,0,2,0,0,0,4⟩]⟩,
⟨6,-3,10,28,[[.f ⟨14,30,0,0,1,0,0,0,0⟩,.f ⟨14,30,1,0,2,0,0,0,0⟩],[.f ⟨14,32,0,0,1,0,0,0,0⟩,.f ⟨14,32,1,0,2,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨17,21,0,0,0,0,0,0,0⟩,.f ⟨17,21,1,0,1,0,0,0,0⟩]],[.f ⟨14,30,0,0,1,0,0,0,4⟩,.f ⟨14,30,1,0,2,0,0,0,4⟩]⟩]⟩,
⟨0,0,0,0,0,[(0,1,0),(0,-1,0),(1,0,1),(-1,0,-2)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨1,0,0,1,[[.f ⟨0,0,0,0,0,0,0,0,0⟩],[.f ⟨14,24,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 11 0]],[.f ⟨0,0,0,0,0,0,0,0,3⟩]⟩,
⟨1,0,1,2,[[.f ⟨0,1,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.s 12 0]],[.f ⟨0,1,0,0,0,0,0,0,3⟩]⟩,
⟨1,0,2,10,[[.f ⟨0,2,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨24,0,0,0,0,0,0,0,0⟩],[.s 13 0]],[.s 4 2]⟩,
⟨1,0,3,3,[[.f ⟨0,3,0,0,0,0,0,0,0⟩],[.f ⟨0,5,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.s 14 0]],[.f ⟨0,3,0,0,0,0,0,0,4⟩]⟩,
⟨1,0,4,9,[[.f ⟨0,4,0,0,0,0,0,0,0⟩],[.f ⟨0,6,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.s 15 0]],[.f ⟨0,6,0,0,0,0,0,0,3⟩]⟩,
⟨1,0,5,4,[[.f ⟨0,5,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.s 14 0],[.s 16 0]],[.f ⟨0,5,0,0,0,0,0,0,4⟩]⟩,
⟨1,0,6,8,[[.f ⟨0,6,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.s 15 0],[.s 17 0]],[.s 8 1]⟩,
⟨1,0,7,5,[[.f ⟨0,7,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.s 18 0],[.s 20 0]],[.f ⟨0,7,0,0,0,0,0,0,3⟩]⟩,
⟨1,0,8,7,[[.f ⟨0,8,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.s 19 0],[.s 21 0]],[.s 10 2]⟩,
⟨1,0,9,5,[[.f ⟨0,7,0,0,0,0,0,0,0⟩],[.f ⟨0,9,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.s 20 0]],[.f ⟨0,7,0,0,0,0,0,0,4⟩]⟩,
⟨1,0,10,6,[[.f ⟨0,8,0,0,0,0,0,0,0⟩],[.f ⟨0,10,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.s 21 0]],[.s 9 3]⟩,
⟨2,0,0,2,[[.s 0 0],[.f ⟨2,2,0,0,0,0,0,0,0⟩],[.s 12 0],[.f ⟨5,0,0,0,0,0,0,0,0⟩]],[.s 0 3]⟩,
⟨2,0,1,3,[[.s 1 0],[.s 11 0],[.s 14 0],[.f ⟨5,1,0,0,0,0,0,0,0⟩]],[.s 1 3]⟩,
⟨2,0,2,10,[[.s 2 0],[.s 15 0],[.f ⟨6,0,0,0,0,0,0,0,0⟩],[.f ⟨5,2,0,0,0,0,0,0,0⟩]],[.s 15 2]⟩,
⟨2,0,3,4,[[.s 3 0],[.s 5 0],[.s 12 0],[.s 16 0],[.f ⟨5,3,0,0,0,0,0,0,0⟩]],[.s 3 4]⟩,
⟨2,0,4,9,[[.s 4 0],[.s 6 0],[.s 13 0],[.s 17 0],[.f ⟨5,4,0,0,0,0,0,0,0⟩]],[.s 6 3]⟩,
⟨2,0,5,5,[[.s 5 0],[.s 14 0],[.s 18 0],[.f ⟨5,3,0,0,0,0,0,0,0⟩],[.f ⟨5,5,0,0,0,0,0,0,0⟩]],[.s 5 4]⟩,
⟨2,0,6,9,[[.s 6 0],[.s 15 0],[.s 19 0],[.f ⟨5,4,0,0,0,0,0,0,0⟩],[.f ⟨5,6,0,0,0,0,0,0,0⟩]],[.s 6 4]⟩,
⟨2,0,7,6,[[.s 7 0],[.s 16 0],[.s 20 0],[.f ⟨5,7,0,0,0,0,0,0,0⟩],[.f ⟨5,9,0,0,0,0,0,0,0⟩]],[.s 7 3]⟩,
⟨2,0,8,8,[[.s 8 0],[.s 17 0],[.s 21 0],[.f ⟨5,8,0,0,0,0,0,0,0⟩],[.f ⟨5,10,0,0,0,0,0,0,0⟩]],[.s 8 3]⟩,
⟨2,0,9,6,[[.s 7 0],[.s 9 0],[.s 18 0],[.s 21 0],[.f ⟨5,9,0,0,0,0,0,0,0⟩]],[.s 7 4]⟩,
⟨2,0,10,7,[[.s 8 0],[.s 10 0],[.s 19 0],[.s 20 0],[.f ⟨5,10,0,0,0,0,0,0,0⟩]],[.s 10 4]⟩]⟩,
⟨1,2,0,0,0,[(0,1,0),(0,-1,0),(1,0,3)],1,0,3,2,0,0,0,0,2,0,0,0,
[⟨3,0,0,3,[[.f ⟨4,11,0,0,0,0,0,0,0⟩,.s 11 0],[.f ⟨16,2,0,0,0,0,0,0,0⟩,.f ⟨18,13,1,0,0,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 11 0,.s 11 0]],[.f ⟨4,11,0,0,0,0,0,0,3⟩,.s 11 3]⟩,
⟨3,0,1,4,[[.f ⟨4,12,0,0,0,0,0,0,0⟩,.s 12 0],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.s 12 0,.s 12 0]],[.f ⟨4,12,0,0,0,0,0,0,3⟩,.s 12 3]⟩,
⟨3,0,2,11,[[.f ⟨4,13,0,0,0,0,0,0,0⟩,.s 13 0],[.s 4 0,.s 4 0],[.f ⟨20,0,0,0,0,0,0,0,0⟩,.f ⟨21,11,1,0,0,0,0,0,0⟩],[.s 13 0,.s 13 0]],[.f ⟨4,13,0,0,0,0,0,0,3⟩,.s 13 3]⟩,
⟨3,0,3,5,[[.f ⟨4,14,0,0,0,0,0,0,0⟩,.s 14 0],[.f ⟨4,16,0,0,0,0,0,0,0⟩,.s 16 0],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.s 14 0,.s 14 0]],[.f ⟨4,14,0,0,0,0,0,0,4⟩,.s 14 4]⟩,
⟨3,0,4,10,[[.f ⟨4,15,0,0,0,0,0,0,0⟩,.s 15 0],[.f ⟨4,17,0,0,0,0,0,0,0⟩,.s 17 0],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.s 15 0,.s 15 0]],[.f ⟨4,15,0,0,0,0,0,0,4⟩,.s 15 4]⟩,
⟨3,0,5,6,[[.f ⟨4,16,0,0,0,0,0,0,0⟩,.s 16 0],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.s 14 0,.s 14 0],[.s 16 0,.s 16 0]],[.f ⟨4,16,0,0,0,0,0,0,4⟩,.s 16 4]⟩,
⟨3,0,6,10,[[.f ⟨4,17,0,0,0,0,0,0,0⟩,.s 17 0],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.s 15 0,.s 15 0],[.s 17 0,.s 17 0]],[.f ⟨4,17,0,0,0,0,0,0,4⟩,.s 17 4]⟩,
⟨3,0,7,7,[[.f ⟨4,18,0,0,0,0,0,0,0⟩,.s 18 0],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 20 0,.s 20 0]],[.f ⟨4,18,0,0,0,0,0,0,3⟩,.s 18 3]⟩,
⟨3,0,8,9,[[.f ⟨4,19,0,0,0,0,0,0,0⟩,.s 19 0],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 21 0,.s 21 0]],[.f ⟨4,19,0,0,0,0,0,0,3⟩,.s 19 3]⟩,
⟨3,0,9,7,[[.f ⟨4,18,0,0,0,0,0,0,0⟩,.s 18 0],[.f ⟨4,20,0,0,0,0,0,0,0⟩,.s 20 0],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.s 20 0,.s 20 0]],[.f ⟨4,18,0,0,0,0,0,0,4⟩,.s 18 4]⟩,
⟨3,0,10,8,[[.f ⟨4,19,0,0,0,0,0,0,0⟩,.s 19 0],[.f ⟨4,21,0,0,0,0,0,0,0⟩,.s 21 0],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.f ⟨4,21,0,0,0,0,0,0,4⟩,.s 21 4]⟩,
⟨4,0,0,4,[[.s 0 0,.s 0 0],[.f ⟨18,2,0,0,0,0,0,0,0⟩,.f ⟨18,2,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 0 0,.s 0 0]],[.s 0 3,.s 0 3]⟩,
⟨4,0,1,5,[[.s 1 0,.s 1 0],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.s 1 0,.s 1 0]],[.s 1 3,.s 1 3]⟩,
⟨4,0,2,12,[[.s 2 0,.s 2 0],[.s 15 0,.s 15 0],[.f ⟨21,0,0,0,0,0,0,0,0⟩,.f ⟨21,0,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 2 3,.s 2 3]⟩,
⟨4,0,3,6,[[.s 3 0,.s 3 0],[.s 5 0,.s 5 0],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.s 3 0,.s 3 0]],[.s 3 4,.s 3 4]⟩,
⟨4,0,4,11,[[.s 4 0,.s 4 0],[.s 6 0,.s 6 0],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.s 4 0,.s 4 0]],[.s 4 4,.s 4 4]⟩,
⟨4,0,5,7,[[.s 5 0,.s 5 0],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.s 3 0,.s 3 0],[.s 5 0,.s 5 0]],[.s 5 4,.s 5 4]⟩,
⟨4,0,6,11,[[.s 6 0,.s 6 0],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.s 4 0,.s 4 0],[.s 6 0,.s 6 0]],[.s 6 4,.s 6 4]⟩,
⟨4,0,7,8,[[.s 7 0,.s 7 0],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.s 7 0,.s 7 0],[.s 9 0,.s 9 0]],[.s 7 3,.s 7 3]⟩,
⟨4,0,8,10,[[.s 8 0,.s 8 0],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.s 8 0,.s 8 0],[.s 10 0,.s 10 0]],[.s 8 3,.s 8 3]⟩,
⟨4,0,9,8,[[.s 7 0,.s 7 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.s 9 0,.s 9 0]],[.s 7 4,.s 7 4]⟩,
⟨4,0,10,9,[[.s 8 0,.s 8 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.s 10 0,.s 10 0]],[.s 10 4,.s 10 4]⟩]⟩,
⟨0,0,0,0,0,[(-1,2,0),(1,-2,0),(2,1,1),(-2,-1,-5)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨2,1,0,11,[[.f ⟨24,0,0,0,0,0,0,0,0⟩],[.f ⟨4,13,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨20,0,0,0,0,0,0,0,0⟩]],[.f ⟨4,13,0,0,0,0,0,0,2⟩]⟩,
⟨2,1,1,12,[[.f ⟨24,1,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.f ⟨20,1,0,0,0,0,0,0,0⟩]],[.s 0 2]⟩,
⟨2,1,2,21,[[.f ⟨24,2,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨26,143,0,0,0,0,0,0,0⟩],[.f ⟨20,2,0,0,0,0,0,0,0⟩]],[.s 4 2]⟩,
⟨2,1,3,13,[[.f ⟨24,3,0,0,0,0,0,0,0⟩],[.f ⟨24,5,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.f ⟨20,3,0,0,0,0,0,0,0⟩]],[.s 1 2]⟩,
⟨2,1,4,20,[[.f ⟨24,4,0,0,0,0,0,0,0⟩],[.f ⟨24,6,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.f ⟨20,4,0,0,0,0,0,0,0⟩]],[.f ⟨24,6,0,0,0,0,0,0,3⟩]⟩,
⟨2,1,5,14,[[.f ⟨24,5,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.f ⟨20,3,0,0,0,0,0,0,0⟩],[.f ⟨20,5,0,0,0,0,0,0,0⟩]],[.s 3 3]⟩,
⟨2,1,6,19,[[.f ⟨24,6,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.f ⟨20,4,0,0,0,0,0,0,0⟩],[.f ⟨20,6,0,0,0,0,0,0,0⟩]],[.s 8 1]⟩,
⟨2,1,7,15,[[.f ⟨24,7,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.f ⟨20,7,0,0,0,0,0,0,0⟩],[.f ⟨20,9,0,0,0,0,0,0,0⟩]],[.s 5 2]⟩,
⟨2,1,8,18,[[.f ⟨24,8,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.f ⟨20,8,0,0,0,0,0,0,0⟩],[.f ⟨20,10,0,0,0,0,0,0,0⟩]],[.s 10 2]⟩,
⟨2,1,9,16,[[.f ⟨24,7,0,0,0,0,0,0,0⟩],[.f ⟨24,9,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.f ⟨20,9,0,0,0,0,0,0,0⟩]],[.f ⟨24,7,0,0,0,0,0,0,4⟩]⟩,
⟨2,1,10,17,[[.f ⟨24,8,0,0,0,0,0,0,0⟩],[.f ⟨24,10,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.f ⟨20,10,0,0,0,0,0,0,0⟩]],[.s 9 3]⟩]⟩,
⟨1,4,2,0,0,[(-1,2,0),(1,-2,0),(2,1,10)],2,1,10,10,0,0,0,0,22,0,0,0,
[⟨4,2,0,22,[[.f ⟨24,11,0,0,0,0,0,0,0⟩,.f ⟨24,11,1,0,1,0,0,0,0⟩],[.f ⟨21,2,0,0,0,0,0,0,0⟩,.f ⟨23,24,0,0,0,1,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨22,0,0,0,0,0,0,0,0⟩,.f ⟨22,0,1,0,1,0,0,0,0⟩]],[.f ⟨21,2,0,0,0,0,0,0,2⟩,.f ⟨23,24,0,0,0,1,0,0,2⟩]⟩,
⟨4,2,1,23,[[.f ⟨24,12,0,0,0,0,0,0,0⟩,.f ⟨24,12,1,0,1,0,0,0,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨22,1,0,0,0,0,0,0,0⟩,.f ⟨22,1,1,0,1,0,0,0,0⟩]],[.s 0 2,.s 0 2]⟩,
⟨4,2,2,32,[[.f ⟨24,13,0,0,0,0,0,0,0⟩,.f ⟨24,13,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.f ⟨26,66,0,0,1,0,0,0,0⟩,.f ⟨26,66,1,0,2,0,0,0,0⟩],[.f ⟨22,2,0,0,0,0,0,0,0⟩,.f ⟨22,2,1,0,1,0,0,0,0⟩]],[.s 4 2,.s 4 2]⟩,
⟨4,2,3,24,[[.f ⟨24,14,0,0,0,0,0,0,0⟩,.f ⟨24,14,1,0,1,0,0,0,0⟩],[.f ⟨24,16,0,0,0,0,0,0,0⟩,.f ⟨24,16,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨22,3,0,0,0,0,0,0,0⟩,.f ⟨22,3,1,0,1,0,0,0,0⟩]],[.s 1 2,.s 1 2]⟩,
⟨4,2,4,31,[[.f ⟨24,15,0,0,0,0,0,0,0⟩,.f ⟨24,15,1,0,1,0,0,0,0⟩],[.f ⟨24,17,0,0,0,0,0,0,0⟩,.f ⟨24,17,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨22,4,0,0,0,0,0,0,0⟩,.f ⟨22,4,1,0,1,0,0,0,0⟩]],[.f ⟨24,17,0,0,0,0,0,0,3⟩,.f ⟨24,17,1,0,1,0,0,0,3⟩]⟩,
⟨4,2,5,25,[[.f ⟨24,16,0,0,0,0,0,0,0⟩,.f ⟨24,16,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨22,3,0,0,0,0,0,0,0⟩,.f ⟨22,3,1,0,1,0,0,0,0⟩],[.f ⟨22,5,0,0,0,0,0,0,0⟩,.f ⟨22,5,1,0,1,0,0,0,0⟩]],[.s 3 3,.s 3 3]⟩,
⟨4,2,6,30,[[.f ⟨24,17,0,0,0,0,0,0,0⟩,.f ⟨24,17,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨22,4,0,0,0,0,0,0,0⟩,.f ⟨22,4,1,0,1,0,0,0,0⟩],[.f ⟨22,6,0,0,0,0,0,0,0⟩,.f ⟨22,6,1,0,1,0,0,0,0⟩]],[.s 8 1,.s 8 1]⟩,
⟨4,2,7,26,[[.f ⟨24,18,0,0,0,0,0,0,0⟩,.f ⟨24,18,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨22,7,0,0,0,0,0,0,0⟩,.f ⟨22,7,1,0,1,0,0,0,0⟩],[.f ⟨22,9,0,0,0,0,0,0,0⟩,.f ⟨22,9,1,0,1,0,0,0,0⟩]],[.s 5 2,.s 5 2]⟩,
⟨4,2,8,29,[[.f ⟨24,19,0,0,0,0,0,0,0⟩,.f ⟨24,19,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨22,8,0,0,0,0,0,0,0⟩,.f ⟨22,8,1,0,1,0,0,0,0⟩],[.f ⟨22,10,0,0,0,0,0,0,0⟩,.f ⟨22,10,1,0,1,0,0,0,0⟩]],[.s 10 2,.s 10 2]⟩,
⟨4,2,9,27,[[.f ⟨24,18,0,0,0,0,0,0,0⟩,.f ⟨24,18,1,0,1,0,0,0,0⟩],[.f ⟨24,20,0,0,0,0,0,0,0⟩,.f ⟨24,20,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨22,9,0,0,0,0,0,0,0⟩,.f ⟨22,9,1,0,1,0,0,0,0⟩]],[.f ⟨24,18,0,0,0,0,0,0,4⟩,.f ⟨24,18,1,0,1,0,0,0,4⟩]⟩,
⟨4,2,10,28,[[.f ⟨24,19,0,0,0,0,0,0,0⟩,.f ⟨24,19,1,0,1,0,0,0,0⟩],[.f ⟨24,21,0,0,0,0,0,0,0⟩,.f ⟨24,21,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨22,10,0,0,0,0,0,0,0⟩,.f ⟨22,10,1,0,1,0,0,0,0⟩]],[.s 9 3,.s 9 3]⟩,
⟨6,3,0,33,[[.f ⟨24,0,0,0,1,0,0,0,0⟩,.f ⟨24,0,1,0,2,0,0,0,0⟩],[.f ⟨23,2,0,0,0,0,0,0,0⟩,.f ⟨23,2,0,0,0,1,0,1,0⟩],[.s 12 0,.s 12 0],[.f ⟨22,11,0,0,0,0,0,0,0⟩,.f ⟨22,11,1,0,1,0,0,0,0⟩]],[.f ⟨23,2,0,0,0,0,0,0,2⟩,.f ⟨23,2,0,0,0,1,0,1,2⟩]⟩,
⟨6,3,1,34,[[.f ⟨24,1,0,0,1,0,0,0,0⟩,.f ⟨24,1,1,0,2,0,0,0,0⟩],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨22,12,0,0,0,0,0,0,0⟩,.f ⟨22,12,1,0,1,0,0,0,0⟩]],[.s 11 2,.s 11 2]⟩,
⟨6,3,2,43,[[.f ⟨24,2,0,0,1,0,0,0,0⟩,.f ⟨24,2,1,0,2,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨26,143,0,0,1,0,0,0,0⟩,.f ⟨26,143,1,0,2,0,0,0,0⟩],[.f ⟨22,13,0,0,0,0,0,0,0⟩,.f ⟨22,13,1,0,1,0,0,0,0⟩]],[.s 15 2,.s 15 2]⟩,
⟨6,3,3,35,[[.f ⟨24,3,0,0,1,0,0,0,0⟩,.f ⟨24,3,1,0,2,0,0,0,0⟩],[.f ⟨24,5,0,0,1,0,0,0,0⟩,.f ⟨24,5,1,0,2,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨22,14,0,0,0,0,0,0,0⟩,.f ⟨22,14,1,0,1,0,0,0,0⟩]],[.s 12 2,.s 12 2]⟩,
⟨6,3,4,42,[[.f ⟨24,4,0,0,1,0,0,0,0⟩,.f ⟨24,4,1,0,2,0,0,0,0⟩],[.f ⟨24,6,0,0,1,0,0,0,0⟩,.f ⟨24,6,1,0,2,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨22,15,0,0,0,0,0,0,0⟩,.f ⟨22,15,1,0,1,0,0,0,0⟩]],[.f ⟨24,6,0,0,1,0,0,0,3⟩,.f ⟨24,6,1,0,2,0,0,0,3⟩]⟩,
⟨6,3,5,36,[[.f ⟨24,5,0,0,1,0,0,0,0⟩,.f ⟨24,5,1,0,2,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨22,14,0,0,0,0,0,0,0⟩,.f ⟨22,14,1,0,1,0,0,0,0⟩],[.f ⟨22,16,0,0,0,0,0,0,0⟩,.f ⟨22,16,1,0,1,0,0,0,0⟩]],[.s 14 3,.s 14 3]⟩,
⟨6,3,6,41,[[.f ⟨24,6,0,0,1,0,0,0,0⟩,.f ⟨24,6,1,0,2,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨22,15,0,0,0,0,0,0,0⟩,.f ⟨22,15,1,0,1,0,0,0,0⟩],[.f ⟨22,17,0,0,0,0,0,0,0⟩,.f ⟨22,17,1,0,1,0,0,0,0⟩]],[.s 19 1,.s 19 1]⟩,
⟨6,3,7,37,[[.f ⟨24,7,0,0,1,0,0,0,0⟩,.f ⟨24,7,1,0,2,0,0,0,0⟩],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨22,18,0,0,0,0,0,0,0⟩,.f ⟨22,18,1,0,1,0,0,0,0⟩],[.f ⟨22,20,0,0,0,0,0,0,0⟩,.f ⟨22,20,1,0,1,0,0,0,0⟩]],[.s 16 2,.s 16 2]⟩,
⟨6,3,8,40,[[.f ⟨24,8,0,0,1,0,0,0,0⟩,.f ⟨24,8,1,0,2,0,0,0,0⟩],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨22,19,0,0,0,0,0,0,0⟩,.f ⟨22,19,1,0,1,0,0,0,0⟩],[.f ⟨22,21,0,0,0,0,0,0,0⟩,.f ⟨22,21,1,0,1,0,0,0,0⟩]],[.s 21 2,.s 21 2]⟩,
⟨6,3,9,38,[[.f ⟨24,7,0,0,1,0,0,0,0⟩,.f ⟨24,7,1,0,2,0,0,0,0⟩],[.f ⟨24,9,0,0,1,0,0,0,0⟩,.f ⟨24,9,1,0,2,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨22,20,0,0,0,0,0,0,0⟩,.f ⟨22,20,1,0,1,0,0,0,0⟩]],[.f ⟨24,7,0,0,1,0,0,0,4⟩,.f ⟨24,7,1,0,2,0,0,0,4⟩]⟩,
⟨6,3,10,39,[[.f ⟨24,8,0,0,1,0,0,0,0⟩,.f ⟨24,8,1,0,2,0,0,0,0⟩],[.f ⟨24,10,0,0,1,0,0,0,0⟩,.f ⟨24,10,1,0,2,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨22,21,0,0,0,0,0,0,0⟩,.f ⟨22,21,1,0,1,0,0,0,0⟩]],[.s 20 3,.s 20 3]⟩]⟩,
⟨0,0,0,0,0,[(-1,-2,0),(1,2,0),(-2,1,1),(2,-1,-5)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨-2,1,0,11,[[.f ⟨27,0,0,0,0,0,0,0,0⟩],[.f ⟨10,2,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨25,11,0,0,0,0,0,0,0⟩]],[.f ⟨10,2,0,0,0,0,0,0,2⟩]⟩,
⟨-2,1,1,12,[[.f ⟨27,1,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.f ⟨25,12,0,0,0,0,0,0,0⟩]],[.s 0 2]⟩,
⟨-2,1,2,21,[[.f ⟨27,2,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨26,11,0,0,0,0,0,0,0⟩],[.f ⟨25,13,0,0,0,0,0,0,0⟩]],[.s 4 2]⟩,
⟨-2,1,3,13,[[.f ⟨27,3,0,0,0,0,0,0,0⟩],[.f ⟨27,5,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.f ⟨25,14,0,0,0,0,0,0,0⟩]],[.s 1 2]⟩,
⟨-2,1,4,20,[[.f ⟨27,4,0,0,0,0,0,0,0⟩],[.f ⟨27,6,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.f ⟨25,15,0,0,0,0,0,0,0⟩]],[.f ⟨27,6,0,0,0,0,0,0,3⟩]⟩,
⟨-2,1,5,14,[[.f ⟨27,5,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.f ⟨25,14,0,0,0,0,0,0,0⟩],[.f ⟨25,16,0,0,0,0,0,0,0⟩]],[.s 3 3]⟩,
⟨-2,1,6,19,[[.f ⟨27,6,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.f ⟨25,15,0,0,0,0,0,0,0⟩],[.f ⟨25,17,0,0,0,0,0,0,0⟩]],[.s 8 1]⟩,
⟨-2,1,7,15,[[.f ⟨27,7,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.f ⟨25,18,0,0,0,0,0,0,0⟩],[.f ⟨25,20,0,0,0,0,0,0,0⟩]],[.s 5 2]⟩,
⟨-2,1,8,18,[[.f ⟨27,8,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.f ⟨25,19,0,0,0,0,0,0,0⟩],[.f ⟨25,21,0,0,0,0,0,0,0⟩]],[.s 10 2]⟩,
⟨-2,1,9,16,[[.f ⟨27,7,0,0,0,0,0,0,0⟩],[.f ⟨27,9,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.f ⟨25,20,0,0,0,0,0,0,0⟩]],[.f ⟨27,7,0,0,0,0,0,0,4⟩]⟩,
⟨-2,1,10,17,[[.f ⟨27,8,0,0,0,0,0,0,0⟩],[.f ⟨27,10,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.f ⟨25,21,0,0,0,0,0,0,0⟩]],[.s 9 3]⟩]⟩,
⟨1,-4,2,0,0,[(-1,-2,0),(1,2,0),(-2,1,10)],-2,1,10,10,0,0,0,0,22,0,0,0,
[⟨-6,3,0,33,[[.f ⟨28,0,0,0,0,0,0,0,0⟩,.f ⟨28,0,1,0,1,0,0,0,0⟩],[.f ⟨30,35,0,0,0,0,0,0,0⟩,.f ⟨30,35,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨25,11,0,0,1,0,0,0,0⟩,.f ⟨25,11,1,0,2,0,0,0,0⟩]],[.f ⟨30,35,0,0,0,0,0,0,2⟩,.f ⟨30,35,1,0,1,0,0,0,2⟩]⟩,
⟨-6,3,1,34,[[.f ⟨28,1,0,0,0,0,0,0,0⟩,.f ⟨28,1,1,0,1,0,0,0,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨25,12,0,0,1,0,0,0,0⟩,.f ⟨25,12,1,0,2,0,0,0,0⟩]],[.s 0 2,.s 0 2]⟩,
⟨-6,3,2,43,[[.f ⟨28,2,0,0,0,0,0,0,0⟩,.f ⟨28,2,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.f ⟨26,11,0,0,0,0,0,1,0⟩,.f ⟨26,11,0,0,0,1,0,2,0⟩],[.f ⟨25,13,0,0,1,0,0,0,0⟩,.f ⟨25,13,1,0,2,0,0,0,0⟩]],[.s 4 2,.s 4 2]⟩,
⟨-6,3,3,35,[[.f ⟨28,3,0,0,0,0,0,0,0⟩,.f ⟨28,3,1,0,1,0,0,0,0⟩],[.f ⟨28,5,0,0,0,0,0,0,0⟩,.f ⟨28,5,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨25,14,0,0,1,0,0,0,0⟩,.f ⟨25,14,1,0,2,0,0,0,0⟩]],[.s 1 2,.s 1 2]⟩,
⟨-6,3,4,42,[[.f ⟨28,4,0,0,0,0,0,0,0⟩,.f ⟨28,4,1,0,1,0,0,0,0⟩],[.f ⟨28,6,0,0,0,0,0,0,0⟩,.f ⟨28,6,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨25,15,0,0,1,0,0,0,0⟩,.f ⟨25,15,1,0,2,0,0,0,0⟩]],[.f ⟨28,6,0,0,0,0,0,0,3⟩,.f ⟨28,6,1,0,1,0,0,0,3⟩]⟩,
⟨-6,3,5,36,[[.f ⟨28,5,0,0,0,0,0,0,0⟩,.f ⟨28,5,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨25,14,0,0,1,0,0,0,0⟩,.f ⟨25,14,1,0,2,0,0,0,0⟩],[.f ⟨25,16,0,0,1,0,0,0,0⟩,.f ⟨25,16,1,0,2,0,0,0,0⟩]],[.s 3 3,.s 3 3]⟩,
⟨-6,3,6,41,[[.f ⟨28,6,0,0,0,0,0,0,0⟩,.f ⟨28,6,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨25,15,0,0,1,0,0,0,0⟩,.f ⟨25,15,1,0,2,0,0,0,0⟩],[.f ⟨25,17,0,0,1,0,0,0,0⟩,.f ⟨25,17,1,0,2,0,0,0,0⟩]],[.s 8 1,.s 8 1]⟩,
⟨-6,3,7,37,[[.f ⟨28,7,0,0,0,0,0,0,0⟩,.f ⟨28,7,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨25,18,0,0,1,0,0,0,0⟩,.f ⟨25,18,1,0,2,0,0,0,0⟩],[.f ⟨25,20,0,0,1,0,0,0,0⟩,.f ⟨25,20,1,0,2,0,0,0,0⟩]],[.s 5 2,.s 5 2]⟩,
⟨-6,3,8,40,[[.f ⟨28,8,0,0,0,0,0,0,0⟩,.f ⟨28,8,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨25,19,0,0,1,0,0,0,0⟩,.f ⟨25,19,1,0,2,0,0,0,0⟩],[.f ⟨25,21,0,0,1,0,0,0,0⟩,.f ⟨25,21,1,0,2,0,0,0,0⟩]],[.s 10 2,.s 10 2]⟩,
⟨-6,3,9,38,[[.f ⟨28,7,0,0,0,0,0,0,0⟩,.f ⟨28,7,1,0,1,0,0,0,0⟩],[.f ⟨28,9,0,0,0,0,0,0,0⟩,.f ⟨28,9,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨25,20,0,0,1,0,0,0,0⟩,.f ⟨25,20,1,0,2,0,0,0,0⟩]],[.f ⟨28,7,0,0,0,0,0,0,4⟩,.f ⟨28,7,1,0,1,0,0,0,4⟩]⟩,
⟨-6,3,10,39,[[.f ⟨28,8,0,0,0,0,0,0,0⟩,.f ⟨28,8,1,0,1,0,0,0,0⟩],[.f ⟨28,10,0,0,0,0,0,0,0⟩,.f ⟨28,10,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨25,21,0,0,1,0,0,0,0⟩,.f ⟨25,21,1,0,2,0,0,0,0⟩]],[.s 9 3,.s 9 3]⟩,
⟨-4,2,0,22,[[.f ⟨28,11,0,0,0,0,0,0,0⟩,.f ⟨28,11,1,0,1,0,0,0,0⟩],[.f ⟨29,13,0,0,0,0,0,0,0⟩,.f ⟨30,13,1,0,0,0,0,0,0⟩],[.s 12 0,.s 12 0],[.f ⟨25,0,0,0,0,0,0,0,0⟩,.f ⟨25,0,1,0,1,0,0,0,0⟩]],[.f ⟨29,13,0,0,0,0,0,0,2⟩,.f ⟨30,13,1,0,0,0,0,0,2⟩]⟩,
⟨-4,2,1,23,[[.f ⟨28,12,0,0,0,0,0,0,0⟩,.f ⟨28,12,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨25,1,0,0,0,0,0,0,0⟩,.f ⟨25,1,1,0,1,0,0,0,0⟩]],[.s 11 2,.s 11 2]⟩,
⟨-4,2,2,32,[[.f ⟨28,13,0,0,0,0,0,0,0⟩,.f ⟨28,13,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨26,66,0,0,0,0,0,1,0⟩,.f ⟨26,66,0,0,0,1,0,2,0⟩],[.f ⟨25,2,0,0,0,0,0,0,0⟩,.f ⟨25,2,1,0,1,0,0,0,0⟩]],[.s 15 2,.s 15 2]⟩,
⟨-4,2,3,24,[[.f ⟨28,14,0,0,0,0,0,0,0⟩,.f ⟨28,14,1,0,1,0,0,0,0⟩],[.f ⟨28,16,0,0,0,0,0,0,0⟩,.f ⟨28,16,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨25,3,0,0,0,0,0,0,0⟩,.f ⟨25,3,1,0,1,0,0,0,0⟩]],[.s 12 2,.s 12 2]⟩,
⟨-4,2,4,31,[[.f ⟨28,15,0,0,0,0,0,0,0⟩,.f ⟨28,15,1,0,1,0,0,0,0⟩],[.f ⟨28,17,0,0,0,0,0,0,0⟩,.f ⟨28,17,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨25,4,0,0,0,0,0,0,0⟩,.f ⟨25,4,1,0,1,0,0,0,0⟩]],[.f ⟨28,17,0,0,0,0,0,0,3⟩,.f ⟨28,17,1,0,1,0,0,0,3⟩]⟩,
⟨-4,2,5,25,[[.f ⟨28,16,0,0,0,0,0,0,0⟩,.f ⟨28,16,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨25,3,0,0,0,0,0,0,0⟩,.f ⟨25,3,1,0,1,0,0,0,0⟩],[.f ⟨25,5,0,0,0,0,0,0,0⟩,.f ⟨25,5,1,0,1,0,0,0,0⟩]],[.s 14 3,.s 14 3]⟩,
⟨-4,2,6,30,[[.f ⟨28,17,0,0,0,0,0,0,0⟩,.f ⟨28,17,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨25,4,0,0,0,0,0,0,0⟩,.f ⟨25,4,1,0,1,0,0,0,0⟩],[.f ⟨25,6,0,0,0,0,0,0,0⟩,.f ⟨25,6,1,0,1,0,0,0,0⟩]],[.s 19 1,.s 19 1]⟩,
⟨-4,2,7,26,[[.f ⟨28,18,0,0,0,0,0,0,0⟩,.f ⟨28,18,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨25,7,0,0,0,0,0,0,0⟩,.f ⟨25,7,1,0,1,0,0,0,0⟩],[.f ⟨25,9,0,0,0,0,0,0,0⟩,.f ⟨25,9,1,0,1,0,0,0,0⟩]],[.s 16 2,.s 16 2]⟩,
⟨-4,2,8,29,[[.f ⟨28,19,0,0,0,0,0,0,0⟩,.f ⟨28,19,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨25,8,0,0,0,0,0,0,0⟩,.f ⟨25,8,1,0,1,0,0,0,0⟩],[.f ⟨25,10,0,0,0,0,0,0,0⟩,.f ⟨25,10,1,0,1,0,0,0,0⟩]],[.s 21 2,.s 21 2]⟩,
⟨-4,2,9,27,[[.f ⟨28,18,0,0,0,0,0,0,0⟩,.f ⟨28,18,1,0,1,0,0,0,0⟩],[.f ⟨28,20,0,0,0,0,0,0,0⟩,.f ⟨28,20,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨25,9,0,0,0,0,0,0,0⟩,.f ⟨25,9,1,0,1,0,0,0,0⟩]],[.f ⟨28,18,0,0,0,0,0,0,4⟩,.f ⟨28,18,1,0,1,0,0,0,4⟩]⟩,
⟨-4,2,10,28,[[.f ⟨28,19,0,0,0,0,0,0,0⟩,.f ⟨28,19,1,0,1,0,0,0,0⟩],[.f ⟨28,21,0,0,0,0,0,0,0⟩,.f ⟨28,21,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨25,10,0,0,0,0,0,0,0⟩,.f ⟨25,10,1,0,1,0,0,0,0⟩]],[.s 20 3,.s 20 3]⟩]⟩,
⟨0,0,0,0,0,[(0,-1,0),(0,1,0),(-1,0,1),(1,0,-2)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨-2,0,0,2,[[.f ⟨11,11,0,0,0,0,0,0,0⟩],[.f ⟨1,2,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 11 0]],[.s 11 0]⟩,
⟨-2,0,1,3,[[.f ⟨11,12,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.s 12 0]],[.s 0 2]⟩,
⟨-2,0,2,10,[[.f ⟨11,13,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨8,0,0,0,0,0,0,0,0⟩],[.s 13 0]],[.s 4 2]⟩,
⟨-2,0,3,4,[[.f ⟨11,14,0,0,0,0,0,0,0⟩],[.f ⟨11,16,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.s 14 0]],[.s 1 2]⟩,
⟨-2,0,4,9,[[.f ⟨11,15,0,0,0,0,0,0,0⟩],[.f ⟨11,17,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.s 15 0]],[.s 6 1]⟩,
⟨-2,0,5,4,[[.f ⟨11,16,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.s 14 0],[.s 16 0]],[.s 14 1]⟩,
⟨-2,0,6,8,[[.f ⟨11,17,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.s 15 0],[.s 17 0]],[.s 8 1]⟩,
⟨-2,0,7,5,[[.f ⟨11,18,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.s 18 0],[.s 20 0]],[.s 5 2]⟩,
⟨-2,0,8,7,[[.f ⟨11,19,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.s 19 0],[.s 21 0]],[.s 21 0]⟩,
⟨-2,0,9,6,[[.f ⟨11,18,0,0,0,0,0,0,0⟩],[.f ⟨11,20,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.s 20 0]],[.s 7 2]⟩,
⟨-2,0,10,7,[[.f ⟨11,19,0,0,0,0,0,0,0⟩],[.f ⟨11,21,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.s 21 0]],[.s 9 3]⟩,
⟨-1,0,0,1,[[.s 0 0],[.f ⟨12,2,0,0,0,0,0,0,0⟩],[.s 12 0],[.f ⟨0,0,0,0,0,0,0,0,0⟩]],[.f ⟨0,0,0,0,0,0,0,0,0⟩]⟩,
⟨-1,0,1,2,[[.s 1 0],[.s 11 0],[.s 14 0],[.f ⟨0,1,0,0,0,0,0,0,0⟩]],[.s 11 2]⟩,
⟨-1,0,2,10,[[.s 2 0],[.s 15 0],[.f ⟨25,11,0,0,0,0,0,0,0⟩],[.f ⟨0,2,0,0,0,0,0,0,0⟩]],[.s 15 2]⟩,
⟨-1,0,3,3,[[.s 3 0],[.s 5 0],[.s 12 0],[.s 16 0],[.f ⟨0,3,0,0,0,0,0,0,0⟩]],[.s 12 2]⟩,
⟨-1,0,4,9,[[.s 4 0],[.s 6 0],[.s 13 0],[.s 17 0],[.f ⟨0,4,0,0,0,0,0,0,0⟩]],[.s 6 3]⟩,
⟨-1,0,5,3,[[.s 5 0],[.s 14 0],[.s 18 0],[.f ⟨0,3,0,0,0,0,0,0,0⟩],[.f ⟨0,5,0,0,0,0,0,0,0⟩]],[.f ⟨0,3,0,0,0,0,0,0,1⟩]⟩,
⟨-1,0,6,8,[[.s 6 0],[.s 15 0],[.s 19 0],[.f ⟨0,4,0,0,0,0,0,0,0⟩],[.f ⟨0,6,0,0,0,0,0,0,0⟩]],[.s 19 1]⟩,
⟨-1,0,7,4,[[.s 7 0],[.s 16 0],[.s 20 0],[.f ⟨0,7,0,0,0,0,0,0,0⟩],[.f ⟨0,9,0,0,0,0,0,0,0⟩]],[.s 16 2]⟩,
⟨-1,0,8,7,[[.s 8 0],[.s 17 0],[.s 21 0],[.f ⟨0,8,0,0,0,0,0,0,0⟩],[.f ⟨0,10,0,0,0,0,0,0,0⟩]],[.s 21 2]⟩,
⟨-1,0,9,5,[[.s 7 0],[.s 9 0],[.s 18 0],[.s 21 0],[.f ⟨0,9,0,0,0,0,0,0,0⟩]],[.s 18 2]⟩,
⟨-1,0,10,6,[[.s 8 0],[.s 10 0],[.s 19 0],[.s 20 0],[.f ⟨0,10,0,0,0,0,0,0,0⟩]],[.s 20 3]⟩]⟩,
⟨1,-2,0,0,0,[(0,-1,0),(0,1,0),(-1,0,3)],-1,0,3,2,0,0,0,0,2,0,0,0,
[⟨-4,0,0,4,[[.s 11 0,.s 11 0],[.f ⟨31,2,0,0,0,0,0,0,0⟩,.f ⟨31,2,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 11 0,.s 11 0]],[.s 11 0,.s 11 0]⟩,
⟨-4,0,1,5,[[.s 12 0,.s 12 0],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.s 12 0,.s 12 0]],[.s 0 2,.s 0 2]⟩,
⟨-4,0,2,12,[[.s 13 0,.s 13 0],[.s 4 0,.s 4 0],[.f ⟨29,11,0,0,0,0,0,0,0⟩,.f ⟨29,11,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0]],[.s 4 2,.s 4 2]⟩,
⟨-4,0,3,6,[[.s 14 0,.s 14 0],[.s 16 0,.s 16 0],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.s 14 0,.s 14 0]],[.s 1 2,.s 1 2]⟩,
⟨-4,0,4,11,[[.s 15 0,.s 15 0],[.s 17 0,.s 17 0],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.s 15 0,.s 15 0]],[.s 6 1,.s 6 1]⟩,
⟨-4,0,5,6,[[.s 16 0,.s 16 0],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.s 14 0,.s 14 0],[.s 16 0,.s 16 0]],[.s 14 1,.s 14 1]⟩,
⟨-4,0,6,10,[[.s 17 0,.s 17 0],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.s 15 0,.s 15 0],[.s 17 0,.s 17 0]],[.s 8 1,.s 8 1]⟩,
⟨-4,0,7,7,[[.s 18 0,.s 18 0],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 20 0,.s 20 0]],[.s 5 2,.s 5 2]⟩,
⟨-4,0,8,9,[[.s 19 0,.s 19 0],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 21 0,.s 21 0]],[.s 19 0,.s 19 0]⟩,
⟨-4,0,9,8,[[.s 18 0,.s 18 0],[.s 20 0,.s 20 0],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.s 20 0,.s 20 0]],[.s 7 2,.s 7 2]⟩,
⟨-4,0,10,9,[[.s 19 0,.s 19 0],[.s 21 0,.s 21 0],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.s 9 3,.s 9 3]⟩,
⟨-3,0,0,3,[[.s 0 0,.s 0 0],[.f ⟨31,13,0,0,0,0,0,0,0⟩,.f ⟨31,13,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.f ⟨10,0,0,0,0,0,0,0,0⟩,.s 0 0]],[.f ⟨10,0,0,0,0,0,0,0,0⟩,.s 0 0]⟩,
⟨-3,0,1,4,[[.s 1 0,.s 1 0],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨10,1,0,0,0,0,0,0,0⟩,.s 1 0]],[.s 11 2,.s 11 2]⟩,
⟨-3,0,2,11,[[.s 2 0,.s 2 0],[.s 15 0,.s 15 0],[.f ⟨27,0,0,0,0,0,0,0,0⟩,.f ⟨29,0,1,0,0,0,0,0,0⟩],[.f ⟨10,2,0,0,0,0,0,0,0⟩,.s 2 0]],[.s 15 2,.s 15 2]⟩,
⟨-3,0,3,5,[[.s 3 0,.s 3 0],[.s 5 0,.s 5 0],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨10,3,0,0,0,0,0,0,0⟩,.s 3 0]],[.s 12 2,.s 12 2]⟩,
⟨-3,0,4,10,[[.s 4 0,.s 4 0],[.s 6 0,.s 6 0],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨10,4,0,0,0,0,0,0,0⟩,.s 4 0]],[.s 17 1,.s 17 1]⟩,
⟨-3,0,5,5,[[.s 5 0,.s 5 0],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨10,3,0,0,0,0,0,0,0⟩,.s 3 0],[.f ⟨10,5,0,0,0,0,0,0,0⟩,.s 5 0]],[.f ⟨10,3,0,0,0,0,0,0,1⟩,.s 3 1]⟩,
⟨-3,0,6,9,[[.s 6 0,.s 6 0],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨10,4,0,0,0,0,0,0,0⟩,.s 4 0],[.f ⟨10,6,0,0,0,0,0,0,0⟩,.s 6 0]],[.s 19 1,.s 19 1]⟩,
⟨-3,0,7,6,[[.s 7 0,.s 7 0],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨10,7,0,0,0,0,0,0,0⟩,.s 7 0],[.f ⟨10,9,0,0,0,0,0,0,0⟩,.s 9 0]],[.s 16 2,.s 16 2]⟩,
⟨-3,0,8,8,[[.s 8 0,.s 8 0],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨10,8,0,0,0,0,0,0,0⟩,.s 8 0],[.f ⟨10,10,0,0,0,0,0,0,0⟩,.s 10 0]],[.f ⟨10,8,0,0,0,0,0,0,0⟩,.s 8 0]⟩,
⟨-3,0,9,7,[[.s 7 0,.s 7 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨10,9,0,0,0,0,0,0,0⟩,.s 9 0]],[.s 18 2,.s 18 2]⟩,
⟨-3,0,10,8,[[.s 8 0,.s 8 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨10,10,0,0,0,0,0,0,0⟩,.s 10 0]],[.s 20 3,.s 20 3]⟩]⟩,
⟨0,0,0,0,0,[(-2,-4,1),(1,-2,1),(2,4,-6),(-1,2,-1)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨-1,-1,0,11,[[.f ⟨1,0,0,0,0,0,0,0,0⟩],[.f ⟨15,24,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨14,0,0,0,0,0,0,0,0⟩]],[.s 1 1]⟩,
⟨-1,-1,1,10,[[.f ⟨1,1,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.f ⟨14,1,0,0,0,0,0,0,0⟩]],[.s 3 2]⟩,
⟨-1,-1,2,2,[[.f ⟨1,2,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨10,11,0,0,0,0,0,0,0⟩],[.f ⟨14,2,0,0,0,0,0,0,0⟩]],[.f ⟨10,11,0,0,0,0,0,0,1⟩]⟩,
⟨-1,-1,3,9,[[.f ⟨1,3,0,0,0,0,0,0,0⟩],[.f ⟨1,5,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.f ⟨14,3,0,0,0,0,0,0,0⟩]],[.f ⟨1,5,0,0,0,0,0,0,3⟩]⟩,
⟨-1,-1,4,3,[[.f ⟨1,4,0,0,0,0,0,0,0⟩],[.f ⟨1,6,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.f ⟨14,4,0,0,0,0,0,0,0⟩]],[.s 2 1]⟩,
⟨-1,-1,5,8,[[.f ⟨1,5,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.f ⟨14,3,0,0,0,0,0,0,0⟩],[.f ⟨14,5,0,0,0,0,0,0,0⟩]],[.s 7 1]⟩,
⟨-1,-1,6,3,[[.f ⟨1,6,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.f ⟨14,4,0,0,0,0,0,0,0⟩],[.f ⟨14,6,0,0,0,0,0,0,0⟩]],[.f ⟨14,4,0,0,0,0,0,0,1⟩]⟩,
⟨-1,-1,7,7,[[.f ⟨1,7,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.f ⟨14,7,0,0,0,0,0,0,0⟩],[.f ⟨14,9,0,0,0,0,0,0,0⟩]],[.s 9 2]⟩,
⟨-1,-1,8,4,[[.f ⟨1,8,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.f ⟨14,8,0,0,0,0,0,0,0⟩],[.f ⟨14,10,0,0,0,0,0,0,0⟩]],[.s 6 2]⟩,
⟨-1,-1,9,6,[[.f ⟨1,7,0,0,0,0,0,0,0⟩],[.f ⟨1,9,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.f ⟨14,9,0,0,0,0,0,0,0⟩]],[.s 10 3]⟩,
⟨-1,-1,10,5,[[.f ⟨1,8,0,0,0,0,0,0,0⟩],[.f ⟨1,10,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.f ⟨14,10,0,0,0,0,0,0,0⟩]],[.s 8 2]⟩]⟩,
⟨1,-2,-1,0,0,[(-2,-4,7),(1,-2,1),(-1,2,-1)],-2,-4,7,8,0,0,0,0,11,0,0,0,
[⟨-3,-2,0,22,[[.f ⟨1,0,0,0,1,0,0,0,0⟩,.f ⟨1,0,1,0,2,0,0,0,0⟩],[.f ⟨15,24,0,0,1,0,0,0,0⟩,.f ⟨15,24,1,0,2,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨15,0,0,0,0,0,0,0,0⟩,.f ⟨15,0,1,0,1,0,0,0,0⟩]],[.s 1 1,.s 1 1]⟩,
⟨-3,-2,1,21,[[.f ⟨1,1,0,0,1,0,0,0,0⟩,.f ⟨1,1,1,0,2,0,0,0,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨15,1,0,0,0,0,0,0,0⟩,.f ⟨15,1,1,0,1,0,0,0,0⟩]],[.s 3 2,.s 3 2]⟩,
⟨-3,-2,2,13,[[.f ⟨1,2,0,0,1,0,0,0,0⟩,.f ⟨1,2,1,0,2,0,0,0,0⟩],[.s 4 0,.s 4 0],[.f ⟨31,11,0,0,0,0,0,0,0⟩,.f ⟨31,11,0,0,0,1,0,1,0⟩],[.f ⟨15,2,0,0,0,0,0,0,0⟩,.f ⟨15,2,1,0,1,0,0,0,0⟩]],[.f ⟨31,11,0,0,0,0,0,0,1⟩,.f ⟨31,11,0,0,0,1,0,1,1⟩]⟩,
⟨-3,-2,3,20,[[.f ⟨1,3,0,0,1,0,0,0,0⟩,.f ⟨1,3,1,0,2,0,0,0,0⟩],[.f ⟨1,5,0,0,1,0,0,0,0⟩,.f ⟨1,5,1,0,2,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨15,3,0,0,0,0,0,0,0⟩,.f ⟨15,3,1,0,1,0,0,0,0⟩]],[.f ⟨1,5,0,0,1,0,0,0,3⟩,.f ⟨1,5,1,0,2,0,0,0,3⟩]⟩,
⟨-3,-2,4,14,[[.f ⟨1,4,0,0,1,0,0,0,0⟩,.f ⟨1,4,1,0,2,0,0,0,0⟩],[.f ⟨1,6,0,0,1,0,0,0,0⟩,.f ⟨1,6,1,0,2,0,0,0,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨15,4,0,0,0,0,0,0,0⟩,.f ⟨15,4,1,0,1,0,0,0,0⟩]],[.s 2 1,.s 2 1]⟩,
⟨-3,-2,5,19,[[.f ⟨1,5,0,0,1,0,0,0,0⟩,.f ⟨1,5,1,0,2,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨15,3,0,0,0,0,0,0,0⟩,.f ⟨15,3,1,0,1,0,0,0,0⟩],[.f ⟨15,5,0,0,0,0,0,0,0⟩,.f ⟨15,5,1,0,1,0,0,0,0⟩]],[.s 7 1,.s 7 1]⟩,
⟨-3,-2,6,14,[[.f ⟨1,6,0,0,1,0,0,0,0⟩,.f ⟨1,6,1,0,2,0,0,0,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨15,4,0,0,0,0,0,0,0⟩,.f ⟨15,4,1,0,1,0,0,0,0⟩],[.f ⟨15,6,0,0,0,0,0,0,0⟩,.f ⟨15,6,1,0,1,0,0,0,0⟩]],[.f ⟨15,4,0,0,0,0,0,0,1⟩,.f ⟨15,4,1,0,1,0,0,0,1⟩]⟩,
⟨-3,-2,7,18,[[.f ⟨1,7,0,0,1,0,0,0,0⟩,.f ⟨1,7,1,0,2,0,0,0,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨15,7,0,0,0,0,0,0,0⟩,.f ⟨15,7,1,0,1,0,0,0,0⟩],[.f ⟨15,9,0,0,0,0,0,0,0⟩,.f ⟨15,9,1,0,1,0,0,0,0⟩]],[.s 9 2,.s 9 2]⟩,
⟨-3,-2,8,15,[[.f ⟨1,8,0,0,1,0,0,0,0⟩,.f ⟨1,8,1,0,2,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨15,8,0,0,0,0,0,0,0⟩,.f ⟨15,8,1,0,1,0,0,0,0⟩],[.f ⟨15,10,0,0,0,0,0,0,0⟩,.f ⟨15,10,1,0,1,0,0,0,0⟩]],[.s 6 2,.s 6 2]⟩,
⟨-3,-2,9,17,[[.f ⟨1,7,0,0,1,0,0,0,0⟩,.f ⟨1,7,1,0,2,0,0,0,0⟩],[.f ⟨1,9,0,0,1,0,0,0,0⟩,.f ⟨1,9,1,0,2,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨15,9,0,0,0,0,0,0,0⟩,.f ⟨15,9,1,0,1,0,0,0,0⟩]],[.s 10 3,.s 10 3]⟩,
⟨-3,-2,10,16,[[.f ⟨1,8,0,0,1,0,0,0,0⟩,.f ⟨1,8,1,0,2,0,0,0,0⟩],[.f ⟨1,10,0,0,1,0,0,0,0⟩,.f ⟨1,10,1,0,2,0,0,0,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨15,10,0,0,0,0,0,0,0⟩,.f ⟨15,10,1,0,1,0,0,0,0⟩]],[.s 8 2,.s 8 2]⟩]⟩,
⟨1,4,-2,0,0,[(1,-2,2),(-2,-4,1),(2,4,-6)],1,-2,2,8,0,0,0,0,22,0,0,0,
[⟨0,-1,0,11,[[.f ⟨12,0,0,0,0,0,0,0,0⟩,.s 44 0],[.f ⟨15,46,0,0,0,0,0,0,0⟩,.f ⟨15,46,0,0,0,1,0,1,0⟩],[.s 1 0,.s 1 0],[.s 22 0,.s 22 0]],[.s 1 1,.s 1 1]⟩,
⟨0,-1,1,10,[[.f ⟨12,1,0,0,0,0,0,0,0⟩,.s 45 0],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.s 23 0,.s 23 0]],[.s 3 2,.s 3 2]⟩,
⟨0,-1,2,1,[[.f ⟨12,2,0,0,0,0,0,0,0⟩,.s 46 0],[.s 4 0,.s 4 0],[.f ⟨0,0,0,0,0,0,0,0,0⟩,.f ⟨3,0,1,0,0,0,0,0,0⟩],[.s 24 0,.s 24 0]],[.f ⟨0,0,0,0,0,0,0,0,1⟩,.f ⟨3,0,1,0,0,0,0,0,1⟩]⟩,
⟨0,-1,3,9,[[.f ⟨12,3,0,0,0,0,0,0,0⟩,.s 47 0],[.f ⟨12,5,0,0,0,0,0,0,0⟩,.s 49 0],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.s 25 0,.s 25 0]],[.f ⟨12,5,0,0,0,0,0,0,3⟩,.s 49 3]⟩,
⟨0,-1,4,2,[[.f ⟨12,4,0,0,0,0,0,0,0⟩,.s 48 0],[.f ⟨12,6,0,0,0,0,0,0,0⟩,.s 50 0],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.s 26 0,.s 26 0]],[.s 2 1,.s 2 1]⟩,
⟨0,-1,5,8,[[.f ⟨12,5,0,0,0,0,0,0,0⟩,.s 49 0],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.s 25 0,.s 25 0],[.s 27 0,.s 27 0]],[.s 7 1,.s 7 1]⟩,
⟨0,-1,6,3,[[.f ⟨12,6,0,0,0,0,0,0,0⟩,.s 50 0],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.s 26 0,.s 26 0],[.s 28 0,.s 28 0]],[.s 4 3,.s 4 3]⟩,
⟨0,-1,7,7,[[.f ⟨12,7,0,0,0,0,0,0,0⟩,.s 51 0],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.s 29 0,.s 29 0],[.s 31 0,.s 31 0]],[.s 9 2,.s 9 2]⟩,
⟨0,-1,8,4,[[.f ⟨12,8,0,0,0,0,0,0,0⟩,.s 52 0],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.s 30 0,.s 30 0],[.s 32 0,.s 32 0]],[.s 6 2,.s 6 2]⟩,
⟨0,-1,9,6,[[.f ⟨12,7,0,0,0,0,0,0,0⟩,.s 51 0],[.f ⟨12,9,0,0,0,0,0,0,0⟩,.s 53 0],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.s 31 0,.s 31 0]],[.s 10 3,.s 10 3]⟩,
⟨0,-1,10,5,[[.f ⟨12,8,0,0,0,0,0,0,0⟩,.s 52 0],[.f ⟨12,10,0,0,0,0,0,0,0⟩,.s 54 0],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.s 32 0,.s 32 0]],[.f ⟨12,8,0,0,0,0,0,0,4⟩,.s 52 4]⟩,
⟨1,-2,0,22,[[.f ⟨15,44,0,0,0,0,0,0,0⟩,.f ⟨15,44,0,0,0,1,0,1,0⟩],[.f ⟨15,68,0,0,0,0,0,0,0⟩,.f ⟨15,68,0,0,0,1,0,1,0⟩],[.s 12 0,.s 12 0],[.s 33 0,.s 33 0]],[.s 12 1,.s 12 1]⟩,
⟨1,-2,1,21,[[.f ⟨15,45,0,0,0,0,0,0,0⟩,.f ⟨15,45,0,0,0,1,0,1,0⟩],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.s 34 0,.s 34 0]],[.s 14 2,.s 14 2]⟩,
⟨1,-2,2,12,[[.f ⟨15,46,0,0,0,0,0,0,0⟩,.f ⟨15,46,0,0,0,1,0,1,0⟩],[.s 15 0,.s 15 0],[.s 22 0,.s 22 0],[.s 35 0,.s 35 0]],[.s 22 1,.s 22 1]⟩,
⟨1,-2,3,20,[[.f ⟨15,47,0,0,0,0,0,0,0⟩,.f ⟨15,47,0,0,0,1,0,1,0⟩],[.f ⟨15,49,0,0,0,0,0,0,0⟩,.f ⟨15,49,0,0,0,1,0,1,0⟩],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.s 36 0,.s 36 0]],[.f ⟨15,49,0,0,0,0,0,0,3⟩,.f ⟨15,49,0,0,0,1,0,1,3⟩]⟩,
⟨1,-2,4,13,[[.f ⟨15,48,0,0,0,0,0,0,0⟩,.f ⟨15,48,0,0,0,1,0,1,0⟩],[.f ⟨15,50,0,0,0,0,0,0,0⟩,.f ⟨15,50,0,0,0,1,0,1,0⟩],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.s 37 0,.s 37 0]],[.s 13 1,.s 13 1]⟩,
⟨1,-2,5,19,[[.f ⟨15,49,0,0,0,0,0,0,0⟩,.f ⟨15,49,0,0,0,1,0,1,0⟩],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.s 36 0,.s 36 0],[.s 38 0,.s 38 0]],[.s 18 1,.s 18 1]⟩,
⟨1,-2,6,14,[[.f ⟨15,50,0,0,0,0,0,0,0⟩,.f ⟨15,50,0,0,0,1,0,1,0⟩],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.s 37 0,.s 37 0],[.s 39 0,.s 39 0]],[.s 15 3,.s 15 3]⟩,
⟨1,-2,7,18,[[.f ⟨15,51,0,0,0,0,0,0,0⟩,.f ⟨15,51,0,0,0,1,0,1,0⟩],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.s 40 0,.s 40 0],[.s 42 0,.s 42 0]],[.s 20 2,.s 20 2]⟩,
⟨1,-2,8,15,[[.f ⟨15,52,0,0,0,0,0,0,0⟩,.f ⟨15,52,0,0,0,1,0,1,0⟩],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.s 41 0,.s 41 0],[.s 43 0,.s 43 0]],[.s 17 2,.s 17 2]⟩,
⟨1,-2,9,17,[[.f ⟨15,51,0,0,0,0,0,0,0⟩,.f ⟨15,51,0,0,0,1,0,1,0⟩],[.f ⟨15,53,0,0,0,0,0,0,0⟩,.f ⟨15,53,0,0,0,1,0,1,0⟩],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.s 42 0,.s 42 0]],[.s 21 3,.s 21 3]⟩,
⟨1,-2,10,16,[[.f ⟨15,52,0,0,0,0,0,0,0⟩,.f ⟨15,52,0,0,0,1,0,1,0⟩],[.f ⟨15,54,0,0,0,0,0,0,0⟩,.f ⟨15,54,0,0,0,1,0,1,0⟩],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.s 43 0,.s 43 0]],[.f ⟨15,52,0,0,0,0,0,0,4⟩,.f ⟨15,52,0,0,0,1,0,1,4⟩]⟩,
⟨1,-1,0,11,[[.s 0 0,.s 0 0],[.s 13 0,.s 13 0],[.s 23 0,.s 23 0],[.f ⟨2,0,0,0,0,0,0,0,0⟩,.f ⟨3,11,1,0,0,0,0,0,0⟩]],[.s 23 1,.s 23 1]⟩,
⟨1,-1,1,10,[[.s 1 0,.s 1 0],[.s 22 0,.s 22 0],[.s 25 0,.s 25 0],[.f ⟨2,1,0,0,0,0,0,0,0⟩,.f ⟨3,12,1,0,0,0,0,0,0⟩]],[.s 25 2,.s 25 2]⟩,
⟨1,-1,2,2,[[.s 2 0,.s 2 0],[.s 26 0,.s 26 0],[.f ⟨4,0,0,0,0,0,0,0,0⟩,.f ⟨17,0,1,0,0,0,0,0,0⟩],[.f ⟨2,2,0,0,0,0,0,0,0⟩,.f ⟨3,13,1,0,0,0,0,0,0⟩]],[.s 2 3,.s 2 3]⟩,
⟨1,-1,3,9,[[.s 3 0,.s 3 0],[.s 5 0,.s 5 0],[.s 23 0,.s 23 0],[.s 27 0,.s 27 0],[.f ⟨2,3,0,0,0,0,0,0,0⟩,.f ⟨3,14,1,0,0,0,0,0,0⟩]],[.s 5 3,.s 5 3]⟩,
⟨1,-1,4,3,[[.s 4 0,.s 4 0],[.s 6 0,.s 6 0],[.s 24 0,.s 24 0],[.s 28 0,.s 28 0],[.f ⟨2,4,0,0,0,0,0,0,0⟩,.f ⟨3,15,1,0,0,0,0,0,0⟩]],[.s 4 4,.s 4 4]⟩,
⟨1,-1,5,8,[[.s 5 0,.s 5 0],[.s 25 0,.s 25 0],[.s 29 0,.s 29 0],[.f ⟨2,3,0,0,0,0,0,0,0⟩,.f ⟨3,14,1,0,0,0,0,0,0⟩],[.f ⟨2,5,0,0,0,0,0,0,0⟩,.f ⟨3,16,1,0,0,0,0,0,0⟩]],[.s 29 1,.s 29 1]⟩,
⟨1,-1,6,4,[[.s 6 0,.s 6 0],[.s 26 0,.s 26 0],[.s 30 0,.s 30 0],[.f ⟨2,4,0,0,0,0,0,0,0⟩,.f ⟨3,15,1,0,0,0,0,0,0⟩],[.f ⟨2,6,0,0,0,0,0,0,0⟩,.f ⟨3,17,1,0,0,0,0,0,0⟩]],[.s 6 4,.s 6 4]⟩,
⟨1,-1,7,7,[[.s 7 0,.s 7 0],[.s 27 0,.s 27 0],[.s 31 0,.s 31 0],[.f ⟨2,7,0,0,0,0,0,0,0⟩,.f ⟨3,18,1,0,0,0,0,0,0⟩],[.f ⟨2,9,0,0,0,0,0,0,0⟩,.f ⟨3,20,1,0,0,0,0,0,0⟩]],[.s 31 2,.s 31 2]⟩,
⟨1,-1,8,5,[[.s 8 0,.s 8 0],[.s 28 0,.s 28 0],[.s 32 0,.s 32 0],[.f ⟨2,8,0,0,0,0,0,0,0⟩,.f ⟨3,19,1,0,0,0,0,0,0⟩],[.f ⟨2,10,0,0,0,0,0,0,0⟩,.f ⟨3,21,1,0,0,0,0,0,0⟩]],[.s 8 3,.s 8 3]⟩,
⟨1,-1,9,6,[[.s 7 0,.s 7 0],[.s 9 0,.s 9 0],[.s 29 0,.s 29 0],[.s 32 0,.s 32 0],[.f ⟨2,9,0,0,0,0,0,0,0⟩,.f ⟨3,20,1,0,0,0,0,0,0⟩]],[.s 32 3,.s 32 3]⟩,
⟨1,-1,10,5,[[.s 8 0,.s 8 0],[.s 10 0,.s 10 0],[.s 30 0,.s 30 0],[.s 31 0,.s 31 0],[.f ⟨2,10,0,0,0,0,0,0,0⟩,.f ⟨3,21,1,0,0,0,0,0,0⟩]],[.s 8 4,.s 8 4]⟩,
⟨2,-2,0,22,[[.s 11 0,.s 11 0],[.f ⟨15,79,0,0,0,0,0,0,0⟩,.f ⟨15,79,0,0,0,1,0,1,0⟩],[.s 34 0,.s 34 0],[.s 55 0,.s 55 0]],[.s 34 1,.s 34 1]⟩,
⟨2,-2,1,21,[[.s 12 0,.s 12 0],[.s 33 0,.s 33 0],[.s 36 0,.s 36 0],[.s 56 0,.s 56 0]],[.s 36 2,.s 36 2]⟩,
⟨2,-2,2,12,[[.s 13 0,.s 13 0],[.s 37 0,.s 37 0],[.f ⟨2,0,0,0,0,0,0,0,0⟩,.f ⟨3,11,1,0,0,0,0,0,0⟩],[.s 57 0,.s 57 0]],[.f ⟨2,0,0,0,0,0,0,0,1⟩,.f ⟨3,11,1,0,0,0,0,0,1⟩]⟩,
⟨2,-2,3,20,[[.s 14 0,.s 14 0],[.s 16 0,.s 16 0],[.s 34 0,.s 34 0],[.s 38 0,.s 38 0],[.s 58 0,.s 58 0]],[.s 16 3,.s 16 3]⟩,
⟨2,-2,4,13,[[.s 15 0,.s 15 0],[.s 17 0,.s 17 0],[.s 35 0,.s 35 0],[.s 39 0,.s 39 0],[.s 59 0,.s 59 0]],[.s 35 1,.s 35 1]⟩,
⟨2,-2,5,19,[[.s 16 0,.s 16 0],[.s 36 0,.s 36 0],[.s 40 0,.s 40 0],[.s 58 0,.s 58 0],[.s 60 0,.s 60 0]],[.s 40 1,.s 40 1]⟩,
⟨2,-2,6,14,[[.s 17 0,.s 17 0],[.s 37 0,.s 37 0],[.s 41 0,.s 41 0],[.s 59 0,.s 59 0],[.s 61 0,.s 61 0]],[.s 37 3,.s 37 3]⟩,
⟨2,-2,7,18,[[.s 18 0,.s 18 0],[.s 38 0,.s 38 0],[.s 42 0,.s 42 0],[.s 62 0,.s 62 0],[.s 64 0,.s 64 0]],[.s 42 2,.s 42 2]⟩,
⟨2,-2,8,15,[[.s 19 0,.s 19 0],[.s 39 0,.s 39 0],[.s 43 0,.s 43 0],[.s 63 0,.s 63 0],[.s 65 0,.s 65 0]],[.s 39 2,.s 39 2]⟩,
⟨2,-2,9,17,[[.s 18 0,.s 18 0],[.s 20 0,.s 20 0],[.s 40 0,.s 40 0],[.s 43 0,.s 43 0],[.s 64 0,.s 64 0]],[.s 43 3,.s 43 3]⟩,
⟨2,-2,10,16,[[.s 19 0,.s 19 0],[.s 21 0,.s 21 0],[.s 41 0,.s 41 0],[.s 42 0,.s 42 0],[.s 65 0,.s 65 0]],[.s 19 4,.s 19 4]⟩,
⟨3,-3,0,33,[[.f ⟨15,77,0,0,0,0,0,0,0⟩,.f ⟨15,77,0,0,0,1,0,1,0⟩],[.f ⟨15,24,0,0,0,0,0,1,0⟩,.f ⟨15,24,0,0,0,1,0,2,0⟩],[.s 45 0,.s 45 0],[.s 0 0,.s 0 0]],[.s 45 1,.s 45 1]⟩,
⟨3,-3,1,32,[[.f ⟨15,78,0,0,0,0,0,0,0⟩,.f ⟨15,78,0,0,0,1,0,1,0⟩],[.s 44 0,.s 44 0],[.s 47 0,.s 47 0],[.s 1 0,.s 1 0]],[.s 47 2,.s 47 2]⟩,
⟨3,-3,2,23,[[.f ⟨15,79,0,0,0,0,0,0,0⟩,.f ⟨15,79,0,0,0,1,0,1,0⟩],[.s 48 0,.s 48 0],[.s 55 0,.s 55 0],[.s 2 0,.s 2 0]],[.s 55 1,.s 55 1]⟩,
⟨3,-3,3,31,[[.f ⟨15,80,0,0,0,0,0,0,0⟩,.f ⟨15,80,0,0,0,1,0,1,0⟩],[.f ⟨15,82,0,0,0,0,0,0,0⟩,.f ⟨15,82,0,0,0,1,0,1,0⟩],[.s 45 0,.s 45 0],[.s 49 0,.s 49 0],[.s 3 0,.s 3 0]],[.f ⟨15,82,0,0,0,0,0,0,3⟩,.f ⟨15,82,0,0,0,1,0,1,3⟩]⟩,
⟨3,-3,4,24,[[.f ⟨15,81,0,0,0,0,0,0,0⟩,.f ⟨15,81,0,0,0,1,0,1,0⟩],[.f ⟨15,83,0,0,0,0,0,0,0⟩,.f ⟨15,83,0,0,0,1,0,1,0⟩],[.s 46 0,.s 46 0],[.s 50 0,.s 50 0],[.s 4 0,.s 4 0]],[.s 46 1,.s 46 1]⟩,
⟨3,-3,5,30,[[.f ⟨15,82,0,0,0,0,0,0,0⟩,.f ⟨15,82,0,0,0,1,0,1,0⟩],[.s 47 0,.s 47 0],[.s 51 0,.s 51 0],[.s 3 0,.s 3 0],[.s 5 0,.s 5 0]],[.s 51 1,.s 51 1]⟩,
⟨3,-3,6,25,[[.f ⟨15,83,0,0,0,0,0,0,0⟩,.f ⟨15,83,0,0,0,1,0,1,0⟩],[.s 48 0,.s 48 0],[.s 52 0,.s 52 0],[.s 4 0,.s 4 0],[.s 6 0,.s 6 0]],[.s 48 3,.s 48 3]⟩,
⟨3,-3,7,29,[[.f ⟨15,84,0,0,0,0,0,0,0⟩,.f ⟨15,84,0,0,0,1,0,1,0⟩],[.s 49 0,.s 49 0],[.s 53 0,.s 53 0],[.s 7 0,.s 7 0],[.s 9 0,.s 9 0]],[.s 53 2,.s 53 2]⟩,
⟨3,-3,8,26,[[.f ⟨15,85,0,0,0,0,0,0,0⟩,.f ⟨15,85,0,0,0,1,0,1,0⟩],[.s 50 0,.s 50 0],[.s 54 0,.s 54 0],[.s 8 0,.s 8 0],[.s 10 0,.s 10 0]],[.s 50 2,.s 50 2]⟩,
⟨3,-3,9,28,[[.f ⟨15,84,0,0,0,0,0,0,0⟩,.f ⟨15,84,0,0,0,1,0,1,0⟩],[.f ⟨15,86,0,0,0,0,0,0,0⟩,.f ⟨15,86,0,0,0,1,0,1,0⟩],[.s 51 0,.s 51 0],[.s 54 0,.s 54 0],[.s 9 0,.s 9 0]],[.s 54 3,.s 54 3]⟩,
⟨3,-3,10,27,[[.f ⟨15,85,0,0,0,0,0,0,0⟩,.f ⟨15,85,0,0,0,1,0,1,0⟩],[.f ⟨15,87,0,0,0,0,0,0,0⟩,.f ⟨15,87,0,0,0,1,0,1,0⟩],[.s 52 0,.s 52 0],[.s 53 0,.s 53 0],[.s 10 0,.s 10 0]],[.f ⟨15,85,0,0,0,0,0,0,4⟩,.f ⟨15,85,0,0,0,1,0,1,4⟩]⟩,
⟨3,-2,0,22,[[.s 33 0,.s 33 0],[.s 46 0,.s 46 0],[.s 56 0,.s 56 0],[.f ⟨3,0,0,0,0,0,0,0,0⟩,.f ⟨3,0,1,0,1,0,0,0,0⟩]],[.s 56 1,.s 56 1]⟩,
⟨3,-2,1,21,[[.s 34 0,.s 34 0],[.s 55 0,.s 55 0],[.s 58 0,.s 58 0],[.f ⟨3,1,0,0,0,0,0,0,0⟩,.f ⟨3,1,1,0,1,0,0,0,0⟩]],[.s 58 2,.s 58 2]⟩,
⟨3,-2,2,13,[[.s 35 0,.s 35 0],[.s 59 0,.s 59 0],[.f ⟨16,0,0,0,0,0,0,0,0⟩,.f ⟨17,11,1,0,0,0,0,0,0⟩],[.f ⟨3,2,0,0,0,0,0,0,0⟩,.f ⟨3,2,1,0,1,0,0,0,0⟩]],[.s 35 3,.s 35 3]⟩,
⟨3,-2,3,20,[[.s 36 0,.s 36 0],[.s 38 0,.s 38 0],[.s 56 0,.s 56 0],[.s 60 0,.s 60 0],[.f ⟨3,3,0,0,0,0,0,0,0⟩,.f ⟨3,3,1,0,1,0,0,0,0⟩]],[.s 38 3,.s 38 3]⟩,
⟨3,-2,4,14,[[.s 37 0,.s 37 0],[.s 39 0,.s 39 0],[.s 57 0,.s 57 0],[.s 61 0,.s 61 0],[.f ⟨3,4,0,0,0,0,0,0,0⟩,.f ⟨3,4,1,0,1,0,0,0,0⟩]],[.s 37 4,.s 37 4]⟩,
⟨3,-2,5,19,[[.s 38 0,.s 38 0],[.s 58 0,.s 58 0],[.s 62 0,.s 62 0],[.f ⟨3,3,0,0,0,0,0,0,0⟩,.f ⟨3,3,1,0,1,0,0,0,0⟩],[.f ⟨3,5,0,0,0,0,0,0,0⟩,.f ⟨3,5,1,0,1,0,0,0,0⟩]],[.s 62 1,.s 62 1]⟩,
⟨3,-2,6,15,[[.s 39 0,.s 39 0],[.s 59 0,.s 59 0],[.s 63 0,.s 63 0],[.f ⟨3,4,0,0,0,0,0,0,0⟩,.f ⟨3,4,1,0,1,0,0,0,0⟩],[.f ⟨3,6,0,0,0,0,0,0,0⟩,.f ⟨3,6,1,0,1,0,0,0,0⟩]],[.s 39 4,.s 39 4]⟩,
⟨3,-2,7,18,[[.s 40 0,.s 40 0],[.s 60 0,.s 60 0],[.s 64 0,.s 64 0],[.f ⟨3,7,0,0,0,0,0,0,0⟩,.f ⟨3,7,1,0,1,0,0,0,0⟩],[.f ⟨3,9,0,0,0,0,0,0,0⟩,.f ⟨3,9,1,0,1,0,0,0,0⟩]],[.s 64 2,.s 64 2]⟩,
⟨3,-2,8,16,[[.s 41 0,.s 41 0],[.s 61 0,.s 61 0],[.s 65 0,.s 65 0],[.f ⟨3,8,0,0,0,0,0,0,0⟩,.f ⟨3,8,1,0,1,0,0,0,0⟩],[.f ⟨3,10,0,0,0,0,0,0,0⟩,.f ⟨3,10,1,0,1,0,0,0,0⟩]],[.s 41 3,.s 41 3]⟩,
⟨3,-2,9,17,[[.s 40 0,.s 40 0],[.s 42 0,.s 42 0],[.s 62 0,.s 62 0],[.s 65 0,.s 65 0],[.f ⟨3,9,0,0,0,0,0,0,0⟩,.f ⟨3,9,1,0,1,0,0,0,0⟩]],[.s 65 3,.s 65 3]⟩,
⟨3,-2,10,16,[[.s 41 0,.s 41 0],[.s 43 0,.s 43 0],[.s 63 0,.s 63 0],[.s 64 0,.s 64 0],[.f ⟨3,10,0,0,0,0,0,0,0⟩,.f ⟨3,10,1,0,1,0,0,0,0⟩]],[.s 41 4,.s 41 4]⟩]⟩,
⟨2,-2,-1,4,-2,[(-2,-4,7),(1,-2,2)],-2,-4,7,8,1,-2,2,8,11,22,2,1,
[⟨-2,-2,0,22,[[.f ⟨13,0,0,0,0,0,0,0,0⟩,.f ⟨13,0,1,0,1,0,0,0,0⟩,.s 55 0,.s 55 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.s 1 1,.s 1 1,.s 1 1,.s 1 1]⟩,
⟨-2,-2,1,21,[[.f ⟨13,1,0,0,0,0,0,0,0⟩,.f ⟨13,1,1,0,1,0,0,0,0⟩,.s 56 0,.s 56 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 3 2,.s 3 2,.s 3 2,.s 3 2]⟩,
⟨-2,-2,2,12,[[.f ⟨13,2,0,0,0,0,0,0,0⟩,.f ⟨13,2,1,0,1,0,0,0,0⟩,.s 57 0,.s 57 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨1,0,0,0,0,0,0,0,0⟩,.f ⟨1,0,1,0,1,0,0,0,0⟩,.s 77 0,.s 77 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0]],[.f ⟨1,0,0,0,0,0,0,0,1⟩,.f ⟨1,0,1,0,1,0,0,0,1⟩,.s 77 1,.s 77 1]⟩,
⟨-2,-2,3,20,[[.f ⟨13,3,0,0,0,0,0,0,0⟩,.f ⟨13,3,1,0,1,0,0,0,0⟩,.s 58 0,.s 58 0],[.f ⟨13,5,0,0,0,0,0,0,0⟩,.f ⟨13,5,1,0,1,0,0,0,0⟩,.s 60 0,.s 60 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0]],[.f ⟨13,5,0,0,0,0,0,0,3⟩,.f ⟨13,5,1,0,1,0,0,0,3⟩,.s 60 3,.s 60 3]⟩,
⟨-2,-2,4,13,[[.f ⟨13,4,0,0,0,0,0,0,0⟩,.f ⟨13,4,1,0,1,0,0,0,0⟩,.s 59 0,.s 59 0],[.f ⟨13,6,0,0,0,0,0,0,0⟩,.f ⟨13,6,1,0,1,0,0,0,0⟩,.s 61 0,.s 61 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.s 2 1,.s 2 1,.s 2 1,.s 2 1]⟩,
⟨-2,-2,5,19,[[.f ⟨13,5,0,0,0,0,0,0,0⟩,.f ⟨13,5,1,0,1,0,0,0,0⟩,.s 60 0,.s 60 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0]],[.s 7 1,.s 7 1,.s 7 1,.s 7 1]⟩,
⟨-2,-2,6,14,[[.f ⟨13,6,0,0,0,0,0,0,0⟩,.f ⟨13,6,1,0,1,0,0,0,0⟩,.s 61 0,.s 61 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.s 4 3,.s 4 3,.s 4 3,.s 4 3]⟩,
⟨-2,-2,7,18,[[.f ⟨13,7,0,0,0,0,0,0,0⟩,.f ⟨13,7,1,0,1,0,0,0,0⟩,.s 62 0,.s 62 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 9 2,.s 9 2,.s 9 2,.s 9 2]⟩,
⟨-2,-2,8,15,[[.f ⟨13,8,0,0,0,0,0,0,0⟩,.f ⟨13,8,1,0,1,0,0,0,0⟩,.s 63 0,.s 63 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 6 2,.s 6 2,.s 6 2,.s 6 2]⟩,
⟨-2,-2,9,17,[[.f ⟨13,7,0,0,0,0,0,0,0⟩,.f ⟨13,7,1,0,1,0,0,0,0⟩,.s 62 0,.s 62 0],[.f ⟨13,9,0,0,0,0,0,0,0⟩,.f ⟨13,9,1,0,1,0,0,0,0⟩,.s 64 0,.s 64 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 10 3,.s 10 3,.s 10 3,.s 10 3]⟩,
⟨-2,-2,10,16,[[.f ⟨13,8,0,0,0,0,0,0,0⟩,.f ⟨13,8,1,0,1,0,0,0,0⟩,.s 63 0,.s 63 0],[.f ⟨13,10,0,0,0,0,0,0,0⟩,.f ⟨13,10,1,0,1,0,0,0,0⟩,.s 65 0,.s 65 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.f ⟨13,8,0,0,0,0,0,0,4⟩,.f ⟨13,8,1,0,1,0,0,0,4⟩,.s 63 4,.s 63 4]⟩,
⟨-1,-3,0,33,[[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.s 12 1,.s 12 1,.s 12 1,.s 12 1]⟩,
⟨-1,-3,1,32,[[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.s 14 2,.s 14 2,.s 14 2,.s 14 2]⟩,
⟨-1,-3,2,23,[[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 22 1,.s 22 1,.s 22 1,.s 22 1]⟩,
⟨-1,-3,3,31,[[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0]],[.s 49 3,.s 49 3,.s 49 3,.s 49 3]⟩,
⟨-1,-3,4,24,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0]],[.s 13 1,.s 13 1,.s 13 1,.s 13 1]⟩,
⟨-1,-3,5,30,[[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.s 18 1,.s 18 1,.s 18 1,.s 18 1]⟩,
⟨-1,-3,6,25,[[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0]],[.s 15 3,.s 15 3,.s 15 3,.s 15 3]⟩,
⟨-1,-3,7,29,[[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.s 20 2,.s 20 2,.s 20 2,.s 20 2]⟩,
⟨-1,-3,8,26,[[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 17 2,.s 17 2,.s 17 2,.s 17 2]⟩,
⟨-1,-3,9,28,[[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.s 21 3,.s 21 3,.s 21 3,.s 21 3]⟩,
⟨-1,-3,10,27,[[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 52 4,.s 52 4,.s 52 4,.s 52 4]⟩,
⟨-1,-2,0,22,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0]],[.s 23 1,.s 23 1,.s 23 1,.s 23 1]⟩,
⟨-1,-2,1,21,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0]],[.s 25 2,.s 25 2,.s 25 2,.s 25 2]⟩,
⟨-1,-2,2,12,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.f ⟨12,0,0,0,0,0,0,0,0⟩,.f ⟨13,0,1,0,0,0,0,0,0⟩,.f ⟨14,44,0,1,0,0,0,0,0⟩,.s 55 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0]],[.f ⟨12,0,0,0,0,0,0,0,1⟩,.f ⟨13,0,1,0,0,0,0,0,1⟩,.f ⟨14,44,0,1,0,0,0,0,1⟩,.s 55 1]⟩,
⟨-1,-2,3,20,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 5 3,.s 5 3,.s 5 3,.s 5 3]⟩,
⟨-1,-2,4,13,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0]],[.s 24 1,.s 24 1,.s 24 1,.s 24 1]⟩,
⟨-1,-2,5,19,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0]],[.s 29 1,.s 29 1,.s 29 1,.s 29 1]⟩,
⟨-1,-2,6,14,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0]],[.s 26 3,.s 26 3,.s 26 3,.s 26 3]⟩,
⟨-1,-2,7,18,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]],[.s 31 2,.s 31 2,.s 31 2,.s 31 2]⟩,
⟨-1,-2,8,15,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0]],[.s 28 2,.s 28 2,.s 28 2,.s 28 2]⟩,
⟨-1,-2,9,17,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]],[.s 32 3,.s 32 3,.s 32 3,.s 32 3]⟩,
⟨-1,-2,10,16,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0]],[.s 8 4,.s 8 4,.s 8 4,.s 8 4]⟩,
⟨0,-3,0,33,[[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0]],[.s 34 1,.s 34 1,.s 34 1,.s 34 1]⟩,
⟨0,-3,1,32,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0]],[.s 36 2,.s 36 2,.s 36 2,.s 36 2]⟩,
⟨0,-3,2,23,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0]],[.s 44 1,.s 44 1,.s 44 1,.s 44 1]⟩,
⟨0,-3,3,31,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0]],[.s 16 3,.s 16 3,.s 16 3,.s 16 3]⟩,
⟨0,-3,4,24,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0]],[.s 35 1,.s 35 1,.s 35 1,.s 35 1]⟩,
⟨0,-3,5,30,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 40 1,.s 40 1,.s 40 1,.s 40 1]⟩,
⟨0,-3,6,25,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0]],[.s 37 3,.s 37 3,.s 37 3,.s 37 3]⟩,
⟨0,-3,7,29,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0]],[.s 42 2,.s 42 2,.s 42 2,.s 42 2]⟩,
⟨0,-3,8,26,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0]],[.s 39 2,.s 39 2,.s 39 2,.s 39 2]⟩,
⟨0,-3,9,28,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0]],[.s 43 3,.s 43 3,.s 43 3,.s 43 3]⟩,
⟨0,-3,10,27,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0]],[.s 19 4,.s 19 4,.s 19 4,.s 19 4]⟩,
⟨0,-2,0,22,[[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.f ⟨14,11,0,0,0,0,0,0,0⟩,.s 11 0,.f ⟨14,11,0,1,1,0,0,0,0⟩,.s 11 0]],[.s 45 1,.s 45 1,.s 45 1,.s 45 1]⟩,
⟨0,-2,1,21,[[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.f ⟨14,12,0,0,0,0,0,0,0⟩,.s 12 0,.f ⟨14,12,0,1,1,0,0,0,0⟩,.s 12 0]],[.s 47 2,.s 47 2,.s 47 2,.s 47 2]⟩,
⟨0,-2,2,12,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.f ⟨14,0,0,0,0,0,0,0,0⟩,.s 0 0,.f ⟨14,0,0,1,1,0,0,0,0⟩,.s 0 0],[.f ⟨14,13,0,0,0,0,0,0,0⟩,.s 13 0,.f ⟨14,13,0,1,1,0,0,0,0⟩,.s 13 0]],[.f ⟨14,0,0,0,0,0,0,0,1⟩,.s 0 1,.f ⟨14,0,0,1,1,0,0,0,1⟩,.s 0 1]⟩,
⟨0,-2,3,20,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.f ⟨14,14,0,0,0,0,0,0,0⟩,.s 14 0,.f ⟨14,14,0,1,1,0,0,0,0⟩,.s 14 0]],[.s 27 3,.s 27 3,.s 27 3,.s 27 3]⟩,
⟨0,-2,4,13,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.f ⟨14,15,0,0,0,0,0,0,0⟩,.s 15 0,.f ⟨14,15,0,1,1,0,0,0,0⟩,.s 15 0]],[.s 46 1,.s 46 1,.s 46 1,.s 46 1]⟩,
⟨0,-2,5,19,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.f ⟨14,14,0,0,0,0,0,0,0⟩,.s 14 0,.f ⟨14,14,0,1,1,0,0,0,0⟩,.s 14 0],[.f ⟨14,16,0,0,0,0,0,0,0⟩,.s 16 0,.f ⟨14,16,0,1,1,0,0,0,0⟩,.s 16 0]],[.s 51 1,.s 51 1,.s 51 1,.s 51 1]⟩,
⟨0,-2,6,14,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.f ⟨14,15,0,0,0,0,0,0,0⟩,.s 15 0,.f ⟨14,15,0,1,1,0,0,0,0⟩,.s 15 0],[.f ⟨14,17,0,0,0,0,0,0,0⟩,.s 17 0,.f ⟨14,17,0,1,1,0,0,0,0⟩,.s 17 0]],[.s 48 3,.s 48 3,.s 48 3,.s 48 3]⟩,
⟨0,-2,7,18,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.f ⟨14,18,0,0,0,0,0,0,0⟩,.s 18 0,.f ⟨14,18,0,1,1,0,0,0,0⟩,.s 18 0],[.f ⟨14,20,0,0,0,0,0,0,0⟩,.s 20 0,.f ⟨14,20,0,1,1,0,0,0,0⟩,.s 20 0]],[.s 53 2,.s 53 2,.s 53 2,.s 53 2]⟩,
⟨0,-2,8,15,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.f ⟨14,19,0,0,0,0,0,0,0⟩,.s 19 0,.f ⟨14,19,0,1,1,0,0,0,0⟩,.s 19 0],[.f ⟨14,21,0,0,0,0,0,0,0⟩,.s 21 0,.f ⟨14,21,0,1,1,0,0,0,0⟩,.s 21 0]],[.s 50 2,.s 50 2,.s 50 2,.s 50 2]⟩,
⟨0,-2,9,17,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.f ⟨14,20,0,0,0,0,0,0,0⟩,.s 20 0,.f ⟨14,20,0,1,1,0,0,0,0⟩,.s 20 0]],[.s 54 3,.s 54 3,.s 54 3,.s 54 3]⟩,
⟨0,-2,10,16,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.f ⟨14,21,0,0,0,0,0,0,0⟩,.s 21 0,.f ⟨14,21,0,1,1,0,0,0,0⟩,.s 21 0]],[.s 30 4,.s 30 4,.s 30 4,.s 30 4]⟩,
⟨1,-4,0,44,[[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0]],[.s 56 1,.s 56 1,.s 56 1,.s 56 1]⟩,
⟨1,-4,1,43,[[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0]],[.s 58 2,.s 58 2,.s 58 2,.s 58 2]⟩,
⟨1,-4,2,34,[[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 66 1,.s 66 1,.s 66 1,.s 66 1]⟩,
⟨1,-4,3,42,[[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.s 82 3,.s 82 3,.s 82 3,.s 82 3]⟩,
⟨1,-4,4,35,[[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 57 1,.s 57 1,.s 57 1,.s 57 1]⟩,
⟨1,-4,5,41,[[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 62 1,.s 62 1,.s 62 1,.s 62 1]⟩,
⟨1,-4,6,36,[[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 59 3,.s 59 3,.s 59 3,.s 59 3]⟩,
⟨1,-4,7,40,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 64 2,.s 64 2,.s 64 2,.s 64 2]⟩,
⟨1,-4,8,37,[[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.s 61 2,.s 61 2,.s 61 2,.s 61 2]⟩,
⟨1,-4,9,39,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 65 3,.s 65 3,.s 65 3,.s 65 3]⟩,
⟨1,-4,10,38,[[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.s 85 4,.s 85 4,.s 85 4,.s 85 4]⟩,
⟨1,-3,0,33,[[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0]],[.s 67 1,.s 67 1,.s 67 1,.s 67 1]⟩,
⟨1,-3,1,32,[[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0]],[.s 69 2,.s 69 2,.s 69 2,.s 69 2]⟩,
⟨1,-3,2,23,[[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.f ⟨14,11,0,0,0,0,0,0,0⟩,.s 11 0,.f ⟨14,11,0,1,1,0,0,0,0⟩,.s 11 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0]],[.f ⟨14,11,0,0,0,0,0,0,1⟩,.s 11 1,.f ⟨14,11,0,1,1,0,0,0,1⟩,.s 11 1]⟩,
⟨1,-3,3,31,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0]],[.s 38 3,.s 38 3,.s 38 3,.s 38 3]⟩,
⟨1,-3,4,24,[[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0]],[.s 68 1,.s 68 1,.s 68 1,.s 68 1]⟩,
⟨1,-3,5,30,[[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0]],[.s 73 1,.s 73 1,.s 73 1,.s 73 1]⟩,
⟨1,-3,6,25,[[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0]],[.s 70 3,.s 70 3,.s 70 3,.s 70 3]⟩,
⟨1,-3,7,29,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0]],[.s 75 2,.s 75 2,.s 75 2,.s 75 2]⟩,
⟨1,-3,8,26,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0]],[.s 72 2,.s 72 2,.s 72 2,.s 72 2]⟩,
⟨1,-3,9,28,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0]],[.s 76 3,.s 76 3,.s 76 3,.s 76 3]⟩,
⟨1,-3,10,27,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0]],[.s 41 4,.s 41 4,.s 41 4,.s 41 4]⟩,
⟨2,-3,0,33,[[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.f ⟨14,44,0,0,0,0,0,0,0⟩,.s 55 0,.f ⟨14,44,0,1,1,0,0,0,0⟩,.s 55 0]],[.s 78 1,.s 78 1,.s 78 1,.s 78 1]⟩,
⟨2,-3,1,32,[[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.f ⟨14,45,0,0,0,0,0,0,0⟩,.s 56 0,.f ⟨14,45,0,1,1,0,0,0,0⟩,.s 56 0]],[.s 80 2,.s 80 2,.s 80 2,.s 80 2]⟩,
⟨2,-3,2,23,[[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.f ⟨14,33,0,0,0,0,0,0,0⟩,.s 33 0,.f ⟨14,33,0,1,1,0,0,0,0⟩,.s 33 0],[.f ⟨14,46,0,0,0,0,0,0,0⟩,.s 57 0,.f ⟨14,46,0,1,1,0,0,0,0⟩,.s 57 0]],[.f ⟨14,33,0,0,0,0,0,0,1⟩,.s 33 1,.f ⟨14,33,0,1,1,0,0,0,1⟩,.s 33 1]⟩,
⟨2,-3,3,31,[[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.f ⟨14,47,0,0,0,0,0,0,0⟩,.s 58 0,.f ⟨14,47,0,1,1,0,0,0,0⟩,.s 58 0]],[.s 71 3,.s 71 3,.s 71 3,.s 71 3]⟩,
⟨2,-3,4,24,[[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.f ⟨14,48,0,0,0,0,0,0,0⟩,.s 59 0,.f ⟨14,48,0,1,1,0,0,0,0⟩,.s 59 0]],[.s 79 1,.s 79 1,.s 79 1,.s 79 1]⟩,
⟨2,-3,5,30,[[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.f ⟨14,47,0,0,0,0,0,0,0⟩,.s 58 0,.f ⟨14,47,0,1,1,0,0,0,0⟩,.s 58 0],[.f ⟨14,49,0,0,0,0,0,0,0⟩,.s 60 0,.f ⟨14,49,0,1,1,0,0,0,0⟩,.s 60 0]],[.s 84 1,.s 84 1,.s 84 1,.s 84 1]⟩,
⟨2,-3,6,25,[[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.f ⟨14,48,0,0,0,0,0,0,0⟩,.s 59 0,.f ⟨14,48,0,1,1,0,0,0,0⟩,.s 59 0],[.f ⟨14,50,0,0,0,0,0,0,0⟩,.s 61 0,.f ⟨14,50,0,1,1,0,0,0,0⟩,.s 61 0]],[.s 81 3,.s 81 3,.s 81 3,.s 81 3]⟩,
⟨2,-3,7,29,[[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.f ⟨14,51,0,0,0,0,0,0,0⟩,.s 62 0,.f ⟨14,51,0,1,1,0,0,0,0⟩,.s 62 0],[.f ⟨14,53,0,0,0,0,0,0,0⟩,.s 64 0,.f ⟨14,53,0,1,1,0,0,0,0⟩,.s 64 0]],[.s 86 2,.s 86 2,.s 86 2,.s 86 2]⟩,
⟨2,-3,8,26,[[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.f ⟨14,52,0,0,0,0,0,0,0⟩,.s 63 0,.f ⟨14,52,0,1,1,0,0,0,0⟩,.s 63 0],[.f ⟨14,54,0,0,0,0,0,0,0⟩,.s 65 0,.f ⟨14,54,0,1,1,0,0,0,0⟩,.s 65 0]],[.s 83 2,.s 83 2,.s 83 2,.s 83 2]⟩,
⟨2,-3,9,28,[[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.f ⟨14,53,0,0,0,0,0,0,0⟩,.s 64 0,.f ⟨14,53,0,1,1,0,0,0,0⟩,.s 64 0]],[.s 87 3,.s 87 3,.s 87 3,.s 87 3]⟩,
⟨2,-3,10,27,[[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.f ⟨14,54,0,0,0,0,0,0,0⟩,.s 65 0,.f ⟨14,54,0,1,1,0,0,0,0⟩,.s 65 0]],[.s 74 4,.s 74 4,.s 74 4,.s 74 4]⟩]⟩,
⟨0,0,0,0,0,[(0,-2,1),(2,4,1),(0,2,-2),(-2,-4,-2)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨3,-1,0,12,[[.f ⟨2,0,0,0,0,0,0,0,0⟩],[.f ⟨14,57,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨18,0,0,0,0,0,0,0,0⟩]],[.f ⟨2,0,0,0,0,0,0,0,3⟩]⟩,
⟨3,-1,1,11,[[.f ⟨2,1,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.f ⟨18,1,0,0,0,0,0,0,0⟩]],[.f ⟨2,1,0,0,0,0,0,0,3⟩]⟩,
⟨3,-1,2,4,[[.f ⟨2,2,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨5,0,0,0,0,0,0,0,0⟩],[.f ⟨18,2,0,0,0,0,0,0,0⟩]],[.f ⟨2,2,0,0,0,0,0,0,3⟩]⟩,
⟨3,-1,3,10,[[.f ⟨2,3,0,0,0,0,0,0,0⟩],[.f ⟨2,5,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.f ⟨18,3,0,0,0,0,0,0,0⟩]],[.f ⟨2,3,0,0,0,0,0,0,4⟩]⟩,
⟨3,-1,4,5,[[.f ⟨2,4,0,0,0,0,0,0,0⟩],[.f ⟨2,6,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.f ⟨18,4,0,0,0,0,0,0,0⟩]],[.f ⟨2,4,0,0,0,0,0,0,4⟩]⟩,
⟨3,-1,5,10,[[.f ⟨2,5,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.f ⟨18,3,0,0,0,0,0,0,0⟩],[.f ⟨18,5,0,0,0,0,0,0,0⟩]],[.f ⟨2,5,0,0,0,0,0,0,4⟩]⟩,
⟨3,-1,6,6,[[.f ⟨2,6,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.f ⟨18,4,0,0,0,0,0,0,0⟩],[.f ⟨18,6,0,0,0,0,0,0,0⟩]],[.f ⟨2,6,0,0,0,0,0,0,4⟩]⟩,
⟨3,-1,7,9,[[.f ⟨2,7,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.f ⟨18,7,0,0,0,0,0,0,0⟩],[.f ⟨18,9,0,0,0,0,0,0,0⟩]],[.f ⟨2,7,0,0,0,0,0,0,3⟩]⟩,
⟨3,-1,8,7,[[.f ⟨2,8,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.f ⟨18,8,0,0,0,0,0,0,0⟩],[.f ⟨18,10,0,0,0,0,0,0,0⟩]],[.f ⟨2,8,0,0,0,0,0,0,3⟩]⟩,
⟨3,-1,9,8,[[.f ⟨2,7,0,0,0,0,0,0,0⟩],[.f ⟨2,9,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.f ⟨18,9,0,0,0,0,0,0,0⟩]],[.f ⟨2,9,0,0,0,0,0,0,4⟩]⟩,
⟨3,-1,10,7,[[.f ⟨2,8,0,0,0,0,0,0,0⟩],[.f ⟨2,10,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.f ⟨18,10,0,0,0,0,0,0,0⟩]],[.f ⟨2,8,0,0,0,0,0,0,4⟩]⟩]⟩,
⟨1,4,-2,0,0,[(0,-2,3),(2,4,1),(-2,-4,-2)],0,-2,3,4,0,0,0,0,22,0,0,0,
[⟨5,-2,0,23,[[.f ⟨3,0,0,0,0,0,0,0,0⟩,.f ⟨3,0,1,0,1,0,0,0,0⟩],[.f ⟨14,24,0,0,1,0,0,0,0⟩,.f ⟨14,24,1,0,2,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨19,0,0,0,0,0,0,0,0⟩,.f ⟨19,0,1,0,1,0,0,0,0⟩]],[.f ⟨3,0,0,0,0,0,0,0,3⟩,.f ⟨3,0,1,0,1,0,0,0,3⟩]⟩,
⟨5,-2,1,22,[[.f ⟨3,1,0,0,0,0,0,0,0⟩,.f ⟨3,1,1,0,1,0,0,0,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨19,1,0,0,0,0,0,0,0⟩,.f ⟨19,1,1,0,1,0,0,0,0⟩]],[.f ⟨3,1,0,0,0,0,0,0,3⟩,.f ⟨3,1,1,0,1,0,0,0,3⟩]⟩,
⟨5,-2,2,15,[[.f ⟨3,2,0,0,0,0,0,0,0⟩,.f ⟨3,2,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.f ⟨18,11,0,0,0,0,0,0,0⟩,.f ⟨19,33,1,0,0,0,0,0,0⟩],[.f ⟨19,2,0,0,0,0,0,0,0⟩,.f ⟨19,2,1,0,1,0,0,0,0⟩]],[.f ⟨3,2,0,0,0,0,0,0,3⟩,.f ⟨3,2,1,0,1,0,0,0,3⟩]⟩,
⟨5,-2,3,21,[[.f ⟨3,3,0,0,0,0,0,0,0⟩,.f ⟨3,3,1,0,1,0,0,0,0⟩],[.f ⟨3,5,0,0,0,0,0,0,0⟩,.f ⟨3,5,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨19,3,0,0,0,0,0,0,0⟩,.f ⟨19,3,1,0,1,0,0,0,0⟩]],[.f ⟨3,3,0,0,0,0,0,0,4⟩,.f ⟨3,3,1,0,1,0,0,0,4⟩]⟩,
⟨5,-2,4,16,[[.f ⟨3,4,0,0,0,0,0,0,0⟩,.f ⟨3,4,1,0,1,0,0,0,0⟩],[.f ⟨3,6,0,0,0,0,0,0,0⟩,.f ⟨3,6,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨19,4,0,0,0,0,0,0,0⟩,.f ⟨19,4,1,0,1,0,0,0,0⟩]],[.f ⟨3,4,0,0,0,0,0,0,4⟩,.f ⟨3,4,1,0,1,0,0,0,4⟩]⟩,
⟨5,-2,5,21,[[.f ⟨3,5,0,0,0,0,0,0,0⟩,.f ⟨3,5,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨19,3,0,0,0,0,0,0,0⟩,.f ⟨19,3,1,0,1,0,0,0,0⟩],[.f ⟨19,5,0,0,0,0,0,0,0⟩,.f ⟨19,5,1,0,1,0,0,0,0⟩]],[.f ⟨3,5,0,0,0,0,0,0,4⟩,.f ⟨3,5,1,0,1,0,0,0,4⟩]⟩,
⟨5,-2,6,17,[[.f ⟨3,6,0,0,0,0,0,0,0⟩,.f ⟨3,6,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨19,4,0,0,0,0,0,0,0⟩,.f ⟨19,4,1,0,1,0,0,0,0⟩],[.f ⟨19,6,0,0,0,0,0,0,0⟩,.f ⟨19,6,1,0,1,0,0,0,0⟩]],[.f ⟨3,6,0,0,0,0,0,0,4⟩,.f ⟨3,6,1,0,1,0,0,0,4⟩]⟩,
⟨5,-2,7,20,[[.f ⟨3,7,0,0,0,0,0,0,0⟩,.f ⟨3,7,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨19,7,0,0,0,0,0,0,0⟩,.f ⟨19,7,1,0,1,0,0,0,0⟩],[.f ⟨19,9,0,0,0,0,0,0,0⟩,.f ⟨19,9,1,0,1,0,0,0,0⟩]],[.f ⟨3,7,0,0,0,0,0,0,3⟩,.f ⟨3,7,1,0,1,0,0,0,3⟩]⟩,
⟨5,-2,8,18,[[.f ⟨3,8,0,0,0,0,0,0,0⟩,.f ⟨3,8,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨19,8,0,0,0,0,0,0,0⟩,.f ⟨19,8,1,0,1,0,0,0,0⟩],[.f ⟨19,10,0,0,0,0,0,0,0⟩,.f ⟨19,10,1,0,1,0,0,0,0⟩]],[.f ⟨3,8,0,0,0,0,0,0,3⟩,.f ⟨3,8,1,0,1,0,0,0,3⟩]⟩,
⟨5,-2,9,19,[[.f ⟨3,7,0,0,0,0,0,0,0⟩,.f ⟨3,7,1,0,1,0,0,0,0⟩],[.f ⟨3,9,0,0,0,0,0,0,0⟩,.f ⟨3,9,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨19,9,0,0,0,0,0,0,0⟩,.f ⟨19,9,1,0,1,0,0,0,0⟩]],[.f ⟨3,9,0,0,0,0,0,0,4⟩,.f ⟨3,9,1,0,1,0,0,0,4⟩]⟩,
⟨5,-2,10,18,[[.f ⟨3,8,0,0,0,0,0,0,0⟩,.f ⟨3,8,1,0,1,0,0,0,0⟩],[.f ⟨3,10,0,0,0,0,0,0,0⟩,.f ⟨3,10,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨19,10,0,0,0,0,0,0,0⟩,.f ⟨19,10,1,0,1,0,0,0,0⟩]],[.f ⟨3,8,0,0,0,0,0,0,4⟩,.f ⟨3,8,1,0,1,0,0,0,4⟩]⟩,
⟨7,-3,0,34,[[.f ⟨3,11,0,0,0,0,0,0,0⟩,.f ⟨3,11,1,0,1,0,0,0,0⟩],[.f ⟨14,57,0,0,1,0,0,0,0⟩,.f ⟨14,57,1,0,2,0,0,0,0⟩],[.s 12 0,.s 12 0],[.f ⟨19,22,0,0,0,0,0,0,0⟩,.f ⟨19,22,1,0,1,0,0,0,0⟩]],[.f ⟨3,11,0,0,0,0,0,0,3⟩,.f ⟨3,11,1,0,1,0,0,0,3⟩]⟩,
⟨7,-3,1,33,[[.f ⟨3,12,0,0,0,0,0,0,0⟩,.f ⟨3,12,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨19,23,0,0,0,0,0,0,0⟩,.f ⟨19,23,1,0,1,0,0,0,0⟩]],[.f ⟨3,12,0,0,0,0,0,0,3⟩,.f ⟨3,12,1,0,1,0,0,0,3⟩]⟩,
⟨7,-3,2,26,[[.f ⟨3,13,0,0,0,0,0,0,0⟩,.f ⟨3,13,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨19,11,0,0,0,0,0,0,0⟩,.f ⟨19,11,1,0,1,0,0,0,0⟩],[.f ⟨19,24,0,0,0,0,0,0,0⟩,.f ⟨19,24,1,0,1,0,0,0,0⟩]],[.f ⟨3,13,0,0,0,0,0,0,3⟩,.f ⟨3,13,1,0,1,0,0,0,3⟩]⟩,
⟨7,-3,3,32,[[.f ⟨3,14,0,0,0,0,0,0,0⟩,.f ⟨3,14,1,0,1,0,0,0,0⟩],[.f ⟨3,16,0,0,0,0,0,0,0⟩,.f ⟨3,16,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨19,25,0,0,0,0,0,0,0⟩,.f ⟨19,25,1,0,1,0,0,0,0⟩]],[.f ⟨3,14,0,0,0,0,0,0,4⟩,.f ⟨3,14,1,0,1,0,0,0,4⟩]⟩,
⟨7,-3,4,27,[[.f ⟨3,15,0,0,0,0,0,0,0⟩,.f ⟨3,15,1,0,1,0,0,0,0⟩],[.f ⟨3,17,0,0,0,0,0,0,0⟩,.f ⟨3,17,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨19,26,0,0,0,0,0,0,0⟩,.f ⟨19,26,1,0,1,0,0,0,0⟩]],[.f ⟨3,15,0,0,0,0,0,0,4⟩,.f ⟨3,15,1,0,1,0,0,0,4⟩]⟩,
⟨7,-3,5,32,[[.f ⟨3,16,0,0,0,0,0,0,0⟩,.f ⟨3,16,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨19,25,0,0,0,0,0,0,0⟩,.f ⟨19,25,1,0,1,0,0,0,0⟩],[.f ⟨19,27,0,0,0,0,0,0,0⟩,.f ⟨19,27,1,0,1,0,0,0,0⟩]],[.f ⟨3,16,0,0,0,0,0,0,4⟩,.f ⟨3,16,1,0,1,0,0,0,4⟩]⟩,
⟨7,-3,6,28,[[.f ⟨3,17,0,0,0,0,0,0,0⟩,.f ⟨3,17,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨19,26,0,0,0,0,0,0,0⟩,.f ⟨19,26,1,0,1,0,0,0,0⟩],[.f ⟨19,28,0,0,0,0,0,0,0⟩,.f ⟨19,28,1,0,1,0,0,0,0⟩]],[.f ⟨3,17,0,0,0,0,0,0,4⟩,.f ⟨3,17,1,0,1,0,0,0,4⟩]⟩,
⟨7,-3,7,31,[[.f ⟨3,18,0,0,0,0,0,0,0⟩,.f ⟨3,18,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨19,29,0,0,0,0,0,0,0⟩,.f ⟨19,29,1,0,1,0,0,0,0⟩],[.f ⟨19,31,0,0,0,0,0,0,0⟩,.f ⟨19,31,1,0,1,0,0,0,0⟩]],[.f ⟨3,18,0,0,0,0,0,0,3⟩,.f ⟨3,18,1,0,1,0,0,0,3⟩]⟩,
⟨7,-3,8,29,[[.f ⟨3,19,0,0,0,0,0,0,0⟩,.f ⟨3,19,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨19,30,0,0,0,0,0,0,0⟩,.f ⟨19,30,1,0,1,0,0,0,0⟩],[.f ⟨19,32,0,0,0,0,0,0,0⟩,.f ⟨19,32,1,0,1,0,0,0,0⟩]],[.f ⟨3,19,0,0,0,0,0,0,3⟩,.f ⟨3,19,1,0,1,0,0,0,3⟩]⟩,
⟨7,-3,9,30,[[.f ⟨3,18,0,0,0,0,0,0,0⟩,.f ⟨3,18,1,0,1,0,0,0,0⟩],[.f ⟨3,20,0,0,0,0,0,0,0⟩,.f ⟨3,20,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨19,31,0,0,0,0,0,0,0⟩,.f ⟨19,31,1,0,1,0,0,0,0⟩]],[.f ⟨3,20,0,0,0,0,0,0,4⟩,.f ⟨3,20,1,0,1,0,0,0,4⟩]⟩,
⟨7,-3,10,29,[[.f ⟨3,19,0,0,0,0,0,0,0⟩,.f ⟨3,19,1,0,1,0,0,0,0⟩],[.f ⟨3,21,0,0,0,0,0,0,0⟩,.f ⟨3,21,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨19,32,0,0,0,0,0,0,0⟩,.f ⟨19,32,1,0,1,0,0,0,0⟩]],[.f ⟨3,19,0,0,0,0,0,0,4⟩,.f ⟨3,19,1,0,1,0,0,0,4⟩]⟩]⟩,
⟨1,2,0,0,0,[(2,4,3),(0,-2,1),(0,2,-2)],2,4,3,4,0,0,0,0,2,0,0,0,
[⟨4,-1,0,13,[[.f ⟨16,0,0,0,0,0,0,0,0⟩,.s 11 0],[.f ⟨3,2,0,0,0,0,0,0,0⟩,.f ⟨19,2,0,0,0,1,0,0,0⟩],[.s 1 0,.s 1 0],[.s 11 0,.s 11 0]],[.f ⟨16,0,0,0,0,0,0,0,3⟩,.s 11 3]⟩,
⟨4,-1,1,12,[[.f ⟨16,1,0,0,0,0,0,0,0⟩,.s 12 0],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.s 12 0,.s 12 0]],[.f ⟨16,1,0,0,0,0,0,0,3⟩,.s 12 3]⟩,
⟨4,-1,2,5,[[.f ⟨16,2,0,0,0,0,0,0,0⟩,.s 13 0],[.s 4 0,.s 4 0],[.f ⟨5,11,0,0,0,0,0,0,0⟩,.f ⟨5,11,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0]],[.f ⟨16,2,0,0,0,0,0,0,3⟩,.s 13 3]⟩,
⟨4,-1,3,11,[[.f ⟨16,3,0,0,0,0,0,0,0⟩,.s 14 0],[.f ⟨16,5,0,0,0,0,0,0,0⟩,.s 16 0],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.s 14 0,.s 14 0]],[.f ⟨16,3,0,0,0,0,0,0,4⟩,.s 14 4]⟩,
⟨4,-1,4,6,[[.f ⟨16,4,0,0,0,0,0,0,0⟩,.s 15 0],[.f ⟨16,6,0,0,0,0,0,0,0⟩,.s 17 0],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.s 15 0,.s 15 0]],[.f ⟨16,4,0,0,0,0,0,0,4⟩,.s 15 4]⟩,
⟨4,-1,5,11,[[.f ⟨16,5,0,0,0,0,0,0,0⟩,.s 16 0],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.s 14 0,.s 14 0],[.s 16 0,.s 16 0]],[.f ⟨16,5,0,0,0,0,0,0,4⟩,.s 16 4]⟩,
⟨4,-1,6,7,[[.f ⟨16,6,0,0,0,0,0,0,0⟩,.s 17 0],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.s 15 0,.s 15 0],[.s 17 0,.s 17 0]],[.f ⟨16,6,0,0,0,0,0,0,4⟩,.s 17 4]⟩,
⟨4,-1,7,10,[[.f ⟨16,7,0,0,0,0,0,0,0⟩,.s 18 0],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 20 0,.s 20 0]],[.f ⟨16,7,0,0,0,0,0,0,3⟩,.s 18 3]⟩,
⟨4,-1,8,8,[[.f ⟨16,8,0,0,0,0,0,0,0⟩,.s 19 0],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 21 0,.s 21 0]],[.f ⟨16,8,0,0,0,0,0,0,3⟩,.s 19 3]⟩,
⟨4,-1,9,9,[[.f ⟨16,7,0,0,0,0,0,0,0⟩,.s 18 0],[.f ⟨16,9,0,0,0,0,0,0,0⟩,.s 20 0],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.s 20 0,.s 20 0]],[.f ⟨16,9,0,0,0,0,0,0,4⟩,.s 20 4]⟩,
⟨4,-1,10,8,[[.f ⟨16,8,0,0,0,0,0,0,0⟩,.s 19 0],[.f ⟨16,10,0,0,0,0,0,0,0⟩,.s 21 0],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.f ⟨16,8,0,0,0,0,0,0,4⟩,.s 19 4]⟩,
⟨5,-1,0,14,[[.s 0 0,.s 0 0],[.f ⟨17,2,0,0,0,0,0,0,0⟩,.f ⟨19,13,0,0,0,1,0,0,0⟩],[.s 12 0,.s 12 0],[.s 0 0,.s 0 0]],[.s 0 3,.s 0 3]⟩,
⟨5,-1,1,13,[[.s 1 0,.s 1 0],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.s 1 0,.s 1 0]],[.s 1 3,.s 1 3]⟩,
⟨5,-1,2,6,[[.s 2 0,.s 2 0],[.s 15 0,.s 15 0],[.f ⟨5,0,0,0,1,0,0,0,0⟩,.f ⟨5,0,1,0,2,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 2 3,.s 2 3]⟩,
⟨5,-1,3,12,[[.s 3 0,.s 3 0],[.s 5 0,.s 5 0],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.s 3 0,.s 3 0]],[.s 3 4,.s 3 4]⟩,
⟨5,-1,4,7,[[.s 4 0,.s 4 0],[.s 6 0,.s 6 0],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.s 4 0,.s 4 0]],[.s 4 4,.s 4 4]⟩,
⟨5,-1,5,12,[[.s 5 0,.s 5 0],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.s 3 0,.s 3 0],[.s 5 0,.s 5 0]],[.s 5 4,.s 5 4]⟩,
⟨5,-1,6,8,[[.s 6 0,.s 6 0],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.s 4 0,.s 4 0],[.s 6 0,.s 6 0]],[.s 6 4,.s 6 4]⟩,
⟨5,-1,7,11,[[.s 7 0,.s 7 0],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.s 7 0,.s 7 0],[.s 9 0,.s 9 0]],[.s 7 3,.s 7 3]⟩,
⟨5,-1,8,9,[[.s 8 0,.s 8 0],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.s 8 0,.s 8 0],[.s 10 0,.s 10 0]],[.s 8 3,.s 8 3]⟩,
⟨5,-1,9,10,[[.s 7 0,.s 7 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.s 9 0,.s 9 0]],[.s 9 4,.s 9 4]⟩,
⟨5,-1,10,9,[[.s 8 0,.s 8 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.s 10 0,.s 10 0]],[.s 8 4,.s 8 4]⟩]⟩,
⟨2,4,-2,2,0,[(0,-2,3),(2,4,3)],0,-2,3,4,2,4,3,4,22,2,1,11,
[⟨6,-2,0,24,[[.f ⟨17,0,0,0,0,0,0,0,0⟩,.f ⟨17,0,1,0,1,0,0,0,0⟩,.s 11 0,.s 11 0],[.f ⟨3,13,0,0,0,0,0,0,0⟩,.f ⟨3,13,1,0,1,0,0,0,0⟩,.s 24 0,.s 24 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.f ⟨17,0,0,0,0,0,0,0,3⟩,.f ⟨17,0,1,0,1,0,0,0,3⟩,.s 11 3,.s 11 3]⟩,
⟨6,-2,1,23,[[.f ⟨17,1,0,0,0,0,0,0,0⟩,.f ⟨17,1,1,0,1,0,0,0,0⟩,.s 12 0,.s 12 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]],[.f ⟨17,1,0,0,0,0,0,0,3⟩,.f ⟨17,1,1,0,1,0,0,0,3⟩,.s 12 3,.s 12 3]⟩,
⟨6,-2,2,16,[[.f ⟨17,2,0,0,0,0,0,0,0⟩,.f ⟨17,2,1,0,1,0,0,0,0⟩,.s 13 0,.s 13 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨18,0,0,0,1,0,0,0,0⟩,.s 22 0,.f ⟨18,0,0,1,2,0,0,0,0⟩,.s 22 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0]],[.f ⟨17,2,0,0,0,0,0,0,3⟩,.f ⟨17,2,1,0,1,0,0,0,3⟩,.s 13 3,.s 13 3]⟩,
⟨6,-2,3,22,[[.f ⟨17,3,0,0,0,0,0,0,0⟩,.f ⟨17,3,1,0,1,0,0,0,0⟩,.s 14 0,.s 14 0],[.f ⟨17,5,0,0,0,0,0,0,0⟩,.f ⟨17,5,1,0,1,0,0,0,0⟩,.s 16 0,.s 16 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.f ⟨17,3,0,0,0,0,0,0,4⟩,.f ⟨17,3,1,0,1,0,0,0,4⟩,.s 14 4,.s 14 4]⟩,
⟨6,-2,4,17,[[.f ⟨17,4,0,0,0,0,0,0,0⟩,.f ⟨17,4,1,0,1,0,0,0,0⟩,.s 15 0,.s 15 0],[.f ⟨17,6,0,0,0,0,0,0,0⟩,.f ⟨17,6,1,0,1,0,0,0,0⟩,.s 17 0,.s 17 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]],[.f ⟨17,4,0,0,0,0,0,0,4⟩,.f ⟨17,4,1,0,1,0,0,0,4⟩,.s 15 4,.s 15 4]⟩,
⟨6,-2,5,22,[[.f ⟨17,5,0,0,0,0,0,0,0⟩,.f ⟨17,5,1,0,1,0,0,0,0⟩,.s 16 0,.s 16 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.f ⟨17,5,0,0,0,0,0,0,4⟩,.f ⟨17,5,1,0,1,0,0,0,4⟩,.s 16 4,.s 16 4]⟩,
⟨6,-2,6,18,[[.f ⟨17,6,0,0,0,0,0,0,0⟩,.f ⟨17,6,1,0,1,0,0,0,0⟩,.s 17 0,.s 17 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.f ⟨17,6,0,0,0,0,0,0,4⟩,.f ⟨17,6,1,0,1,0,0,0,4⟩,.s 17 4,.s 17 4]⟩,
⟨6,-2,7,21,[[.f ⟨17,7,0,0,0,0,0,0,0⟩,.f ⟨17,7,1,0,1,0,0,0,0⟩,.s 18 0,.s 18 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.f ⟨17,7,0,0,0,0,0,0,3⟩,.f ⟨17,7,1,0,1,0,0,0,3⟩,.s 18 3,.s 18 3]⟩,
⟨6,-2,8,19,[[.f ⟨17,8,0,0,0,0,0,0,0⟩,.f ⟨17,8,1,0,1,0,0,0,0⟩,.s 19 0,.s 19 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.f ⟨17,8,0,0,0,0,0,0,3⟩,.f ⟨17,8,1,0,1,0,0,0,3⟩,.s 19 3,.s 19 3]⟩,
⟨6,-2,9,20,[[.f ⟨17,7,0,0,0,0,0,0,0⟩,.f ⟨17,7,1,0,1,0,0,0,0⟩,.s 18 0,.s 18 0],[.f ⟨17,9,0,0,0,0,0,0,0⟩,.f ⟨17,9,1,0,1,0,0,0,0⟩,.s 20 0,.s 20 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.f ⟨17,9,0,0,0,0,0,0,4⟩,.f ⟨17,9,1,0,1,0,0,0,4⟩,.s 20 4,.s 20 4]⟩,
⟨6,-2,10,19,[[.f ⟨17,8,0,0,0,0,0,0,0⟩,.f ⟨17,8,1,0,1,0,0,0,0⟩,.s 19 0,.s 19 0],[.f ⟨17,10,0,0,0,0,0,0,0⟩,.f ⟨17,10,1,0,1,0,0,0,0⟩,.s 21 0,.s 21 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.f ⟨17,8,0,0,0,0,0,0,4⟩,.f ⟨17,8,1,0,1,0,0,0,4⟩,.s 19 4,.s 19 4]⟩,
⟨7,-2,0,25,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨17,13,0,0,0,0,0,0,0⟩,.f ⟨17,13,1,0,1,0,0,0,0⟩,.s 35 0,.s 35 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0]],[.s 0 3,.s 0 3,.s 0 3,.s 0 3]⟩,
⟨7,-2,1,24,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0]],[.s 1 3,.s 1 3,.s 1 3,.s 1 3]⟩,
⟨7,-2,2,17,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.f ⟨18,11,0,0,1,0,0,0,0⟩,.s 33 0,.f ⟨18,11,0,1,2,0,0,0,0⟩,.s 33 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 2 3,.s 2 3,.s 2 3,.s 2 3]⟩,
⟨7,-2,3,23,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.s 3 4,.s 3 4,.s 3 4,.s 3 4]⟩,
⟨7,-2,4,18,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 4 4,.s 4 4,.s 4 4,.s 4 4]⟩,
⟨7,-2,5,23,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 5 4,.s 5 4,.s 5 4,.s 5 4]⟩,
⟨7,-2,6,19,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 6 4,.s 6 4,.s 6 4,.s 6 4]⟩,
⟨7,-2,7,22,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 7 3,.s 7 3,.s 7 3,.s 7 3]⟩,
⟨7,-2,8,20,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.s 8 3,.s 8 3,.s 8 3,.s 8 3]⟩,
⟨7,-2,9,21,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 9 4,.s 9 4,.s 9 4,.s 9 4]⟩,
⟨7,-2,10,20,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.s 8 4,.s 8 4,.s 8 4,.s 8 4]⟩,
⟨8,-3,0,35,[[.f ⟨17,11,0,0,0,0,0,0,0⟩,.f ⟨17,11,1,0,1,0,0,0,0⟩,.s 33 0,.s 33 0],[.f ⟨3,2,0,0,1,0,0,0,0⟩,.f ⟨3,2,1,0,2,0,0,0,0⟩,.s 2 0,.s 2 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.f ⟨17,11,0,0,0,0,0,0,3⟩,.f ⟨17,11,1,0,1,0,0,0,3⟩,.s 33 3,.s 33 3]⟩,
⟨8,-3,1,34,[[.f ⟨17,12,0,0,0,0,0,0,0⟩,.f ⟨17,12,1,0,1,0,0,0,0⟩,.s 34 0,.s 34 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.f ⟨17,12,0,0,0,0,0,0,3⟩,.f ⟨17,12,1,0,1,0,0,0,3⟩,.s 34 3,.s 34 3]⟩,
⟨8,-3,2,27,[[.f ⟨17,13,0,0,0,0,0,0,0⟩,.f ⟨17,13,1,0,1,0,0,0,0⟩,.s 35 0,.s 35 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.f ⟨17,13,0,0,0,0,0,0,3⟩,.f ⟨17,13,1,0,1,0,0,0,3⟩,.s 35 3,.s 35 3]⟩,
⟨8,-3,3,33,[[.f ⟨17,14,0,0,0,0,0,0,0⟩,.f ⟨17,14,1,0,1,0,0,0,0⟩,.s 36 0,.s 36 0],[.f ⟨17,16,0,0,0,0,0,0,0⟩,.f ⟨17,16,1,0,1,0,0,0,0⟩,.s 38 0,.s 38 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0]],[.f ⟨17,14,0,0,0,0,0,0,4⟩,.f ⟨17,14,1,0,1,0,0,0,4⟩,.s 36 4,.s 36 4]⟩,
⟨8,-3,4,28,[[.f ⟨17,15,0,0,0,0,0,0,0⟩,.f ⟨17,15,1,0,1,0,0,0,0⟩,.s 37 0,.s 37 0],[.f ⟨17,17,0,0,0,0,0,0,0⟩,.f ⟨17,17,1,0,1,0,0,0,0⟩,.s 39 0,.s 39 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0]],[.f ⟨17,15,0,0,0,0,0,0,4⟩,.f ⟨17,15,1,0,1,0,0,0,4⟩,.s 37 4,.s 37 4]⟩,
⟨8,-3,5,33,[[.f ⟨17,16,0,0,0,0,0,0,0⟩,.f ⟨17,16,1,0,1,0,0,0,0⟩,.s 38 0,.s 38 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.f ⟨17,16,0,0,0,0,0,0,4⟩,.f ⟨17,16,1,0,1,0,0,0,4⟩,.s 38 4,.s 38 4]⟩,
⟨8,-3,6,29,[[.f ⟨17,17,0,0,0,0,0,0,0⟩,.f ⟨17,17,1,0,1,0,0,0,0⟩,.s 39 0,.s 39 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0]],[.f ⟨17,17,0,0,0,0,0,0,4⟩,.f ⟨17,17,1,0,1,0,0,0,4⟩,.s 39 4,.s 39 4]⟩,
⟨8,-3,7,32,[[.f ⟨17,18,0,0,0,0,0,0,0⟩,.f ⟨17,18,1,0,1,0,0,0,0⟩,.s 40 0,.s 40 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.f ⟨17,18,0,0,0,0,0,0,3⟩,.f ⟨17,18,1,0,1,0,0,0,3⟩,.s 40 3,.s 40 3]⟩,
⟨8,-3,8,30,[[.f ⟨17,19,0,0,0,0,0,0,0⟩,.f ⟨17,19,1,0,1,0,0,0,0⟩,.s 41 0,.s 41 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.f ⟨17,19,0,0,0,0,0,0,3⟩,.f ⟨17,19,1,0,1,0,0,0,3⟩,.s 41 3,.s 41 3]⟩,
⟨8,-3,9,31,[[.f ⟨17,18,0,0,0,0,0,0,0⟩,.f ⟨17,18,1,0,1,0,0,0,0⟩,.s 40 0,.s 40 0],[.f ⟨17,20,0,0,0,0,0,0,0⟩,.f ⟨17,20,1,0,1,0,0,0,0⟩,.s 42 0,.s 42 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.f ⟨17,20,0,0,0,0,0,0,4⟩,.f ⟨17,20,1,0,1,0,0,0,4⟩,.s 42 4,.s 42 4]⟩,
⟨8,-3,10,30,[[.f ⟨17,19,0,0,0,0,0,0,0⟩,.f ⟨17,19,1,0,1,0,0,0,0⟩,.s 41 0,.s 41 0],[.f ⟨17,21,0,0,0,0,0,0,0⟩,.f ⟨17,21,1,0,1,0,0,0,0⟩,.s 43 0,.s 43 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.f ⟨17,19,0,0,0,0,0,0,4⟩,.f ⟨17,19,1,0,1,0,0,0,4⟩,.s 41 4,.s 41 4]⟩,
⟨9,-3,0,36,[[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.f ⟨17,2,0,0,1,0,0,0,0⟩,.f ⟨17,2,1,0,2,0,0,0,0⟩,.s 13 0,.s 13 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.s 22 3,.s 22 3,.s 22 3,.s 22 3]⟩,
⟨9,-3,1,35,[[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 23 3,.s 23 3,.s 23 3,.s 23 3]⟩,
⟨9,-3,2,28,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0]],[.s 24 3,.s 24 3,.s 24 3,.s 24 3]⟩,
⟨9,-3,3,34,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0]],[.s 25 4,.s 25 4,.s 25 4,.s 25 4]⟩,
⟨9,-3,4,29,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.s 26 4,.s 26 4,.s 26 4,.s 26 4]⟩,
⟨9,-3,5,34,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0]],[.s 27 4,.s 27 4,.s 27 4,.s 27 4]⟩,
⟨9,-3,6,30,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.s 28 4,.s 28 4,.s 28 4,.s 28 4]⟩,
⟨9,-3,7,33,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 29 3,.s 29 3,.s 29 3,.s 29 3]⟩,
⟨9,-3,8,31,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 30 3,.s 30 3,.s 30 3,.s 30 3]⟩,
⟨9,-3,9,32,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 31 4,.s 31 4,.s 31 4,.s 31 4]⟩,
⟨9,-3,10,31,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 30 4,.s 30 4,.s 30 4,.s 30 4]⟩]⟩,
⟨0,0,0,0,0,[(2,-4,1),(0,2,1),(-2,4,-2),(0,-2,-2)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨3,1,0,12,[[.f ⟨6,0,0,0,0,0,0,0,0⟩],[.f ⟨5,2,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨21,0,0,0,0,0,0,0,0⟩]],[.f ⟨6,0,0,0,0,0,0,0,3⟩]⟩,
⟨3,1,1,13,[[.f ⟨6,1,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.f ⟨21,1,0,0,0,0,0,0,0⟩]],[.f ⟨6,1,0,0,0,0,0,0,3⟩]⟩,
⟨3,1,2,21,[[.f ⟨6,2,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨24,11,0,0,0,0,0,0,0⟩],[.f ⟨21,2,0,0,0,0,0,0,0⟩]],[.s 4 2]⟩,
⟨3,1,3,14,[[.f ⟨6,3,0,0,0,0,0,0,0⟩],[.f ⟨6,5,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.f ⟨21,3,0,0,0,0,0,0,0⟩]],[.f ⟨6,3,0,0,0,0,0,0,4⟩]⟩,
⟨3,1,4,20,[[.f ⟨6,4,0,0,0,0,0,0,0⟩],[.f ⟨6,6,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.f ⟨21,4,0,0,0,0,0,0,0⟩]],[.f ⟨6,6,0,0,0,0,0,0,3⟩]⟩,
⟨3,1,5,15,[[.f ⟨6,5,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.f ⟨21,3,0,0,0,0,0,0,0⟩],[.f ⟨21,5,0,0,0,0,0,0,0⟩]],[.f ⟨6,5,0,0,0,0,0,0,4⟩]⟩,
⟨3,1,6,19,[[.f ⟨6,6,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.f ⟨21,4,0,0,0,0,0,0,0⟩],[.f ⟨21,6,0,0,0,0,0,0,0⟩]],[.s 8 1]⟩,
⟨3,1,7,16,[[.f ⟨6,7,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.f ⟨21,7,0,0,0,0,0,0,0⟩],[.f ⟨21,9,0,0,0,0,0,0,0⟩]],[.f ⟨6,7,0,0,0,0,0,0,3⟩]⟩,
⟨3,1,8,18,[[.f ⟨6,8,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.f ⟨21,8,0,0,0,0,0,0,0⟩],[.f ⟨21,10,0,0,0,0,0,0,0⟩]],[.s 10 2]⟩,
⟨3,1,9,16,[[.f ⟨6,7,0,0,0,0,0,0,0⟩],[.f ⟨6,9,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.f ⟨21,9,0,0,0,0,0,0,0⟩]],[.f ⟨6,7,0,0,0,0,0,0,4⟩]⟩,
⟨3,1,10,17,[[.f ⟨6,8,0,0,0,0,0,0,0⟩],[.f ⟨6,10,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.f ⟨21,10,0,0,0,0,0,0,0⟩]],[.s 9 3]⟩]⟩,
⟨1,2,0,0,0,[(2,-4,3),(0,2,1),(0,-2,-2)],2,-4,3,4,0,0,0,0,2,0,0,0,
[⟨4,1,0,13,[[.f ⟨20,0,0,0,0,0,0,0,0⟩,.s 11 0],[.f ⟨5,13,0,0,0,0,0,0,0⟩,.f ⟨5,13,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 11 0,.s 11 0]],[.f ⟨20,0,0,0,0,0,0,0,3⟩,.s 11 3]⟩,
⟨4,1,1,14,[[.f ⟨20,1,0,0,0,0,0,0,0⟩,.s 12 0],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.s 12 0,.s 12 0]],[.f ⟨20,1,0,0,0,0,0,0,3⟩,.s 12 3]⟩,
⟨4,1,2,21,[[.f ⟨20,2,0,0,0,0,0,0,0⟩,.s 13 0],[.s 4 0,.s 4 0],[.f ⟨7,0,0,0,0,0,0,0,0⟩,.f ⟨23,0,1,0,0,0,0,0,0⟩],[.s 13 0,.s 13 0]],[.s 4 2,.s 13 3]⟩,
⟨4,1,3,15,[[.f ⟨20,3,0,0,0,0,0,0,0⟩,.s 14 0],[.f ⟨20,5,0,0,0,0,0,0,0⟩,.s 16 0],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.s 14 0,.s 14 0]],[.f ⟨20,3,0,0,0,0,0,0,4⟩,.s 14 4]⟩,
⟨4,1,4,20,[[.f ⟨20,4,0,0,0,0,0,0,0⟩,.s 15 0],[.f ⟨20,6,0,0,0,0,0,0,0⟩,.s 17 0],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.s 15 0,.s 15 0]],[.f ⟨20,6,0,0,0,0,0,0,3⟩,.s 15 4]⟩,
⟨4,1,5,16,[[.f ⟨20,5,0,0,0,0,0,0,0⟩,.s 16 0],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.s 14 0,.s 14 0],[.s 16 0,.s 16 0]],[.f ⟨20,5,0,0,0,0,0,0,4⟩,.s 16 4]⟩,
⟨4,1,6,20,[[.f ⟨20,6,0,0,0,0,0,0,0⟩,.s 17 0],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.s 15 0,.s 15 0],[.s 17 0,.s 17 0]],[.f ⟨20,6,0,0,0,0,0,0,4⟩,.s 17 4]⟩,
⟨4,1,7,17,[[.f ⟨20,7,0,0,0,0,0,0,0⟩,.s 18 0],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 20 0,.s 20 0]],[.f ⟨20,7,0,0,0,0,0,0,3⟩,.s 18 3]⟩,
⟨4,1,8,19,[[.f ⟨20,8,0,0,0,0,0,0,0⟩,.s 19 0],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 21 0,.s 21 0]],[.f ⟨20,8,0,0,0,0,0,0,3⟩,.s 19 3]⟩,
⟨4,1,9,17,[[.f ⟨20,7,0,0,0,0,0,0,0⟩,.s 18 0],[.f ⟨20,9,0,0,0,0,0,0,0⟩,.s 20 0],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.s 20 0,.s 20 0]],[.f ⟨20,7,0,0,0,0,0,0,4⟩,.s 18 4]⟩,
⟨4,1,10,18,[[.f ⟨20,8,0,0,0,0,0,0,0⟩,.s 19 0],[.f ⟨20,10,0,0,0,0,0,0,0⟩,.s 21 0],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.f ⟨20,10,0,0,0,0,0,0,4⟩,.s 21 4]⟩,
⟨5,1,0,14,[[.s 0 0,.s 0 0],[.f ⟨5,2,0,0,1,0,0,0,0⟩,.f ⟨5,2,1,0,2,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 0 0,.s 0 0]],[.s 0 3,.s 0 3]⟩,
⟨5,1,1,15,[[.s 1 0,.s 1 0],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.s 1 0,.s 1 0]],[.s 1 3,.s 1 3]⟩,
⟨5,1,2,22,[[.s 2 0,.s 2 0],[.s 15 0,.s 15 0],[.f ⟨22,0,0,0,0,0,0,0,0⟩,.f ⟨23,11,1,0,0,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 2 3,.s 2 3]⟩,
⟨5,1,3,16,[[.s 3 0,.s 3 0],[.s 5 0,.s 5 0],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.s 3 0,.s 3 0]],[.s 3 4,.s 3 4]⟩,
⟨5,1,4,21,[[.s 4 0,.s 4 0],[.s 6 0,.s 6 0],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.s 4 0,.s 4 0]],[.s 4 4,.s 4 4]⟩,
⟨5,1,5,17,[[.s 5 0,.s 5 0],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.s 3 0,.s 3 0],[.s 5 0,.s 5 0]],[.s 5 4,.s 5 4]⟩,
⟨5,1,6,21,[[.s 6 0,.s 6 0],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.s 4 0,.s 4 0],[.s 6 0,.s 6 0]],[.s 6 4,.s 6 4]⟩,
⟨5,1,7,18,[[.s 7 0,.s 7 0],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.s 7 0,.s 7 0],[.s 9 0,.s 9 0]],[.s 7 3,.s 7 3]⟩,
⟨5,1,8,20,[[.s 8 0,.s 8 0],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.s 8 0,.s 8 0],[.s 10 0,.s 10 0]],[.s 8 3,.s 8 3]⟩,
⟨5,1,9,18,[[.s 7 0,.s 7 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.s 9 0,.s 9 0]],[.s 7 4,.s 7 4]⟩,
⟨5,1,10,19,[[.s 8 0,.s 8 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.s 10 0,.s 10 0]],[.s 10 4,.s 10 4]⟩]⟩,
⟨1,4,2,0,0,[(0,2,3),(2,-4,1),(-2,4,-2)],0,2,3,4,0,0,0,0,22,0,0,0,
[⟨5,2,0,23,[[.f ⟨7,0,0,0,0,0,0,0,0⟩,.f ⟨7,0,1,0,1,0,0,0,0⟩],[.f ⟨21,13,0,0,0,0,0,0,0⟩,.f ⟨23,35,0,0,0,1,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨23,0,0,0,0,0,0,0,0⟩,.f ⟨23,0,0,0,0,1,0,1,0⟩]],[.f ⟨7,0,0,0,0,0,0,0,3⟩,.f ⟨7,0,1,0,1,0,0,0,3⟩]⟩,
⟨5,2,1,24,[[.f ⟨7,1,0,0,0,0,0,0,0⟩,.f ⟨7,1,1,0,1,0,0,0,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨23,1,0,0,0,0,0,0,0⟩,.f ⟨23,1,0,0,0,1,0,1,0⟩]],[.f ⟨7,1,0,0,0,0,0,0,3⟩,.f ⟨7,1,1,0,1,0,0,0,3⟩]⟩,
⟨5,2,2,32,[[.f ⟨7,2,0,0,0,0,0,0,0⟩,.f ⟨7,2,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.f ⟨24,0,0,0,1,0,0,0,0⟩,.f ⟨24,0,1,0,2,0,0,0,0⟩],[.f ⟨23,2,0,0,0,0,0,0,0⟩,.f ⟨23,2,0,0,0,1,0,1,0⟩]],[.s 4 2,.s 4 2]⟩,
⟨5,2,3,25,[[.f ⟨7,3,0,0,0,0,0,0,0⟩,.f ⟨7,3,1,0,1,0,0,0,0⟩],[.f ⟨7,5,0,0,0,0,0,0,0⟩,.f ⟨7,5,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨23,3,0,0,0,0,0,0,0⟩,.f ⟨23,3,0,0,0,1,0,1,0⟩]],[.f ⟨7,3,0,0,0,0,0,0,4⟩,.f ⟨7,3,1,0,1,0,0,0,4⟩]⟩,
⟨5,2,4,31,[[.f ⟨7,4,0,0,0,0,0,0,0⟩,.f ⟨7,4,1,0,1,0,0,0,0⟩],[.f ⟨7,6,0,0,0,0,0,0,0⟩,.f ⟨7,6,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨23,4,0,0,0,0,0,0,0⟩,.f ⟨23,4,0,0,0,1,0,1,0⟩]],[.f ⟨7,6,0,0,0,0,0,0,3⟩,.f ⟨7,6,1,0,1,0,0,0,3⟩]⟩,
⟨5,2,5,26,[[.f ⟨7,5,0,0,0,0,0,0,0⟩,.f ⟨7,5,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨23,3,0,0,0,0,0,0,0⟩,.f ⟨23,3,0,0,0,1,0,1,0⟩],[.f ⟨23,5,0,0,0,0,0,0,0⟩,.f ⟨23,5,0,0,0,1,0,1,0⟩]],[.f ⟨7,5,0,0,0,0,0,0,4⟩,.f ⟨7,5,1,0,1,0,0,0,4⟩]⟩,
⟨5,2,6,30,[[.f ⟨7,6,0,0,0,0,0,0,0⟩,.f ⟨7,6,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨23,4,0,0,0,0,0,0,0⟩,.f ⟨23,4,0,0,0,1,0,1,0⟩],[.f ⟨23,6,0,0,0,0,0,0,0⟩,.f ⟨23,6,0,0,0,1,0,1,0⟩]],[.s 8 1,.s 8 1]⟩,
⟨5,2,7,27,[[.f ⟨7,7,0,0,0,0,0,0,0⟩,.f ⟨7,7,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨23,7,0,0,0,0,0,0,0⟩,.f ⟨23,7,0,0,0,1,0,1,0⟩],[.f ⟨23,9,0,0,0,0,0,0,0⟩,.f ⟨23,9,0,0,0,1,0,1,0⟩]],[.f ⟨7,7,0,0,0,0,0,0,3⟩,.f ⟨7,7,1,0,1,0,0,0,3⟩]⟩,
⟨5,2,8,29,[[.f ⟨7,8,0,0,0,0,0,0,0⟩,.f ⟨7,8,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨23,8,0,0,0,0,0,0,0⟩,.f ⟨23,8,0,0,0,1,0,1,0⟩],[.f ⟨23,10,0,0,0,0,0,0,0⟩,.f ⟨23,10,0,0,0,1,0,1,0⟩]],[.s 10 2,.s 10 2]⟩,
⟨5,2,9,27,[[.f ⟨7,7,0,0,0,0,0,0,0⟩,.f ⟨7,7,1,0,1,0,0,0,0⟩],[.f ⟨7,9,0,0,0,0,0,0,0⟩,.f ⟨7,9,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨23,9,0,0,0,0,0,0,0⟩,.f ⟨23,9,0,0,0,1,0,1,0⟩]],[.f ⟨7,7,0,0,0,0,0,0,4⟩,.f ⟨7,7,1,0,1,0,0,0,4⟩]⟩,
⟨5,2,10,28,[[.f ⟨7,8,0,0,0,0,0,0,0⟩,.f ⟨7,8,1,0,1,0,0,0,0⟩],[.f ⟨7,10,0,0,0,0,0,0,0⟩,.f ⟨7,10,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨23,10,0,0,0,0,0,0,0⟩,.f ⟨23,10,0,0,0,1,0,1,0⟩]],[.s 9 3,.s 9 3]⟩,
⟨7,3,0,34,[[.f ⟨7,11,0,0,0,0,0,0,0⟩,.f ⟨7,11,1,0,1,0,0,0,0⟩],[.f ⟨23,13,0,0,0,0,0,0,0⟩,.f ⟨23,13,0,0,0,1,0,1,0⟩],[.s 12 0,.s 12 0],[.f ⟨23,22,0,0,0,0,0,0,0⟩,.f ⟨23,22,0,0,0,1,0,1,0⟩]],[.f ⟨7,11,0,0,0,0,0,0,3⟩,.f ⟨7,11,1,0,1,0,0,0,3⟩]⟩,
⟨7,3,1,35,[[.f ⟨7,12,0,0,0,0,0,0,0⟩,.f ⟨7,12,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨23,23,0,0,0,0,0,0,0⟩,.f ⟨23,23,0,0,0,1,0,1,0⟩]],[.f ⟨7,12,0,0,0,0,0,0,3⟩,.f ⟨7,12,1,0,1,0,0,0,3⟩]⟩,
⟨7,3,2,43,[[.f ⟨7,13,0,0,0,0,0,0,0⟩,.f ⟨7,13,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨24,11,0,0,1,0,0,0,0⟩,.f ⟨24,11,1,0,2,0,0,0,0⟩],[.f ⟨23,24,0,0,0,0,0,0,0⟩,.f ⟨23,24,0,0,0,1,0,1,0⟩]],[.s 15 2,.s 15 2]⟩,
⟨7,3,3,36,[[.f ⟨7,14,0,0,0,0,0,0,0⟩,.f ⟨7,14,1,0,1,0,0,0,0⟩],[.f ⟨7,16,0,0,0,0,0,0,0⟩,.f ⟨7,16,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨23,25,0,0,0,0,0,0,0⟩,.f ⟨23,25,0,0,0,1,0,1,0⟩]],[.f ⟨7,14,0,0,0,0,0,0,4⟩,.f ⟨7,14,1,0,1,0,0,0,4⟩]⟩,
⟨7,3,4,42,[[.f ⟨7,15,0,0,0,0,0,0,0⟩,.f ⟨7,15,1,0,1,0,0,0,0⟩],[.f ⟨7,17,0,0,0,0,0,0,0⟩,.f ⟨7,17,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨23,26,0,0,0,0,0,0,0⟩,.f ⟨23,26,0,0,0,1,0,1,0⟩]],[.f ⟨7,17,0,0,0,0,0,0,3⟩,.f ⟨7,17,1,0,1,0,0,0,3⟩]⟩,
⟨7,3,5,37,[[.f ⟨7,16,0,0,0,0,0,0,0⟩,.f ⟨7,16,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨23,25,0,0,0,0,0,0,0⟩,.f ⟨23,25,0,0,0,1,0,1,0⟩],[.f ⟨23,27,0,0,0,0,0,0,0⟩,.f ⟨23,27,0,0,0,1,0,1,0⟩]],[.f ⟨7,16,0,0,0,0,0,0,4⟩,.f ⟨7,16,1,0,1,0,0,0,4⟩]⟩,
⟨7,3,6,41,[[.f ⟨7,17,0,0,0,0,0,0,0⟩,.f ⟨7,17,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨23,26,0,0,0,0,0,0,0⟩,.f ⟨23,26,0,0,0,1,0,1,0⟩],[.f ⟨23,28,0,0,0,0,0,0,0⟩,.f ⟨23,28,0,0,0,1,0,1,0⟩]],[.s 19 1,.s 19 1]⟩,
⟨7,3,7,38,[[.f ⟨7,18,0,0,0,0,0,0,0⟩,.f ⟨7,18,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨23,29,0,0,0,0,0,0,0⟩,.f ⟨23,29,0,0,0,1,0,1,0⟩],[.f ⟨23,31,0,0,0,0,0,0,0⟩,.f ⟨23,31,0,0,0,1,0,1,0⟩]],[.f ⟨7,18,0,0,0,0,0,0,3⟩,.f ⟨7,18,1,0,1,0,0,0,3⟩]⟩,
⟨7,3,8,40,[[.f ⟨7,19,0,0,0,0,0,0,0⟩,.f ⟨7,19,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨23,30,0,0,0,0,0,0,0⟩,.f ⟨23,30,0,0,0,1,0,1,0⟩],[.f ⟨23,32,0,0,0,0,0,0,0⟩,.f ⟨23,32,0,0,0,1,0,1,0⟩]],[.s 21 2,.s 21 2]⟩,
⟨7,3,9,38,[[.f ⟨7,18,0,0,0,0,0,0,0⟩,.f ⟨7,18,1,0,1,0,0,0,0⟩],[.f ⟨7,20,0,0,0,0,0,0,0⟩,.f ⟨7,20,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨23,31,0,0,0,0,0,0,0⟩,.f ⟨23,31,0,0,0,1,0,1,0⟩]],[.f ⟨7,18,0,0,0,0,0,0,4⟩,.f ⟨7,18,1,0,1,0,0,0,4⟩]⟩,
⟨7,3,10,39,[[.f ⟨7,19,0,0,0,0,0,0,0⟩,.f ⟨7,19,1,0,1,0,0,0,0⟩],[.f ⟨7,21,0,0,0,0,0,0,0⟩,.f ⟨7,21,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨23,32,0,0,0,0,0,0,0⟩,.f ⟨23,32,0,0,0,1,0,1,0⟩]],[.s 20 3,.s 20 3]⟩]⟩,
⟨2,2,0,4,2,[(2,-4,3),(0,2,3)],2,-4,3,4,0,2,3,4,2,22,11,1,
[⟨6,2,0,24,[[.f ⟨22,0,0,0,0,0,0,0,0⟩,.s 11 0,.f ⟨22,0,0,1,1,0,0,0,0⟩,.s 11 0],[.f ⟨21,2,0,0,1,0,0,0,0⟩,.f ⟨21,2,1,0,2,0,0,0,0⟩,.s 24 0,.s 24 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.f ⟨22,0,0,0,0,0,0,0,3⟩,.s 11 3,.f ⟨22,0,0,1,1,0,0,0,3⟩,.s 11 3]⟩,
⟨6,2,1,25,[[.f ⟨22,1,0,0,0,0,0,0,0⟩,.s 12 0,.f ⟨22,1,0,1,1,0,0,0,0⟩,.s 12 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]],[.f ⟨22,1,0,0,0,0,0,0,3⟩,.s 12 3,.f ⟨22,1,0,1,1,0,0,0,3⟩,.s 12 3]⟩,
⟨6,2,2,32,[[.f ⟨22,2,0,0,0,0,0,0,0⟩,.s 13 0,.f ⟨22,2,0,1,1,0,0,0,0⟩,.s 13 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨7,11,0,0,0,0,0,0,0⟩,.s 22 0,.f ⟨7,11,0,1,1,0,0,0,0⟩,.s 22 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0]],[.s 4 2,.s 13 3,.s 4 2,.s 13 3]⟩,
⟨6,2,3,26,[[.f ⟨22,3,0,0,0,0,0,0,0⟩,.s 14 0,.f ⟨22,3,0,1,1,0,0,0,0⟩,.s 14 0],[.f ⟨22,5,0,0,0,0,0,0,0⟩,.s 16 0,.f ⟨22,5,0,1,1,0,0,0,0⟩,.s 16 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.f ⟨22,3,0,0,0,0,0,0,4⟩,.s 14 4,.f ⟨22,3,0,1,1,0,0,0,4⟩,.s 14 4]⟩,
⟨6,2,4,31,[[.f ⟨22,4,0,0,0,0,0,0,0⟩,.s 15 0,.f ⟨22,4,0,1,1,0,0,0,0⟩,.s 15 0],[.f ⟨22,6,0,0,0,0,0,0,0⟩,.s 17 0,.f ⟨22,6,0,1,1,0,0,0,0⟩,.s 17 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]],[.f ⟨22,6,0,0,0,0,0,0,3⟩,.s 15 4,.f ⟨22,6,0,1,1,0,0,0,3⟩,.s 15 4]⟩,
⟨6,2,5,27,[[.f ⟨22,5,0,0,0,0,0,0,0⟩,.s 16 0,.f ⟨22,5,0,1,1,0,0,0,0⟩,.s 16 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.f ⟨22,5,0,0,0,0,0,0,4⟩,.s 16 4,.f ⟨22,5,0,1,1,0,0,0,4⟩,.s 16 4]⟩,
⟨6,2,6,31,[[.f ⟨22,6,0,0,0,0,0,0,0⟩,.s 17 0,.f ⟨22,6,0,1,1,0,0,0,0⟩,.s 17 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.f ⟨22,6,0,0,0,0,0,0,4⟩,.s 17 4,.f ⟨22,6,0,1,1,0,0,0,4⟩,.s 17 4]⟩,
⟨6,2,7,28,[[.f ⟨22,7,0,0,0,0,0,0,0⟩,.s 18 0,.f ⟨22,7,0,1,1,0,0,0,0⟩,.s 18 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.f ⟨22,7,0,0,0,0,0,0,3⟩,.s 18 3,.f ⟨22,7,0,1,1,0,0,0,3⟩,.s 18 3]⟩,
⟨6,2,8,30,[[.f ⟨22,8,0,0,0,0,0,0,0⟩,.s 19 0,.f ⟨22,8,0,1,1,0,0,0,0⟩,.s 19 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.f ⟨22,8,0,0,0,0,0,0,3⟩,.s 19 3,.f ⟨22,8,0,1,1,0,0,0,3⟩,.s 19 3]⟩,
⟨6,2,9,28,[[.f ⟨22,7,0,0,0,0,0,0,0⟩,.s 18 0,.f ⟨22,7,0,1,1,0,0,0,0⟩,.s 18 0],[.f ⟨22,9,0,0,0,0,0,0,0⟩,.s 20 0,.f ⟨22,9,0,1,1,0,0,0,0⟩,.s 20 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.f ⟨22,7,0,0,0,0,0,0,4⟩,.s 18 4,.f ⟨22,7,0,1,1,0,0,0,4⟩,.s 18 4]⟩,
⟨6,2,10,29,[[.f ⟨22,8,0,0,0,0,0,0,0⟩,.s 19 0,.f ⟨22,8,0,1,1,0,0,0,0⟩,.s 19 0],[.f ⟨22,10,0,0,0,0,0,0,0⟩,.s 21 0,.f ⟨22,10,0,1,1,0,0,0,0⟩,.s 21 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.f ⟨22,10,0,0,0,0,0,0,4⟩,.s 21 4,.f ⟨22,10,0,1,1,0,0,0,4⟩,.s 21 4]⟩,
⟨7,2,0,25,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨21,13,0,0,1,0,0,0,0⟩,.f ⟨21,13,1,0,2,0,0,0,0⟩,.s 35 0,.s 35 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0]],[.s 0 3,.s 0 3,.s 0 3,.s 0 3]⟩,
⟨7,2,1,26,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0]],[.s 1 3,.s 1 3,.s 1 3,.s 1 3]⟩,
⟨7,2,2,33,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.f ⟨22,11,0,0,0,0,0,0,0⟩,.s 33 0,.f ⟨22,11,0,1,1,0,0,0,0⟩,.s 33 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 2 3,.s 2 3,.s 2 3,.s 2 3]⟩,
⟨7,2,3,27,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.s 3 4,.s 3 4,.s 3 4,.s 3 4]⟩,
⟨7,2,4,32,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 4 4,.s 4 4,.s 4 4,.s 4 4]⟩,
⟨7,2,5,28,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 5 4,.s 5 4,.s 5 4,.s 5 4]⟩,
⟨7,2,6,32,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 6 4,.s 6 4,.s 6 4,.s 6 4]⟩,
⟨7,2,7,29,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 7 3,.s 7 3,.s 7 3,.s 7 3]⟩,
⟨7,2,8,31,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.s 8 3,.s 8 3,.s 8 3,.s 8 3]⟩,
⟨7,2,9,29,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 7 4,.s 7 4,.s 7 4,.s 7 4]⟩,
⟨7,2,10,30,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.s 10 4,.s 10 4,.s 10 4,.s 10 4]⟩,
⟨8,3,0,35,[[.f ⟨22,11,0,0,0,0,0,0,0⟩,.s 33 0,.f ⟨22,11,0,1,1,0,0,0,0⟩,.s 33 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.f ⟨22,11,0,0,0,0,0,0,3⟩,.s 33 3,.f ⟨22,11,0,1,1,0,0,0,3⟩,.s 33 3]⟩,
⟨8,3,1,36,[[.f ⟨22,12,0,0,0,0,0,0,0⟩,.s 34 0,.f ⟨22,12,0,1,1,0,0,0,0⟩,.s 34 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.f ⟨22,12,0,0,0,0,0,0,3⟩,.s 34 3,.f ⟨22,12,0,1,1,0,0,0,3⟩,.s 34 3]⟩,
⟨8,3,2,43,[[.f ⟨22,13,0,0,0,0,0,0,0⟩,.s 35 0,.f ⟨22,13,0,1,1,0,0,0,0⟩,.s 35 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.f ⟨7,0,0,0,1,0,0,0,0⟩,.s 0 0,.f ⟨7,0,0,1,2,0,0,0,0⟩,.s 0 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 26 2,.s 35 3,.s 26 2,.s 35 3]⟩,
⟨8,3,3,37,[[.f ⟨22,14,0,0,0,0,0,0,0⟩,.s 36 0,.f ⟨22,14,0,1,1,0,0,0,0⟩,.s 36 0],[.f ⟨22,16,0,0,0,0,0,0,0⟩,.s 38 0,.f ⟨22,16,0,1,1,0,0,0,0⟩,.s 38 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0]],[.f ⟨22,14,0,0,0,0,0,0,4⟩,.s 36 4,.f ⟨22,14,0,1,1,0,0,0,4⟩,.s 36 4]⟩,
⟨8,3,4,42,[[.f ⟨22,15,0,0,0,0,0,0,0⟩,.s 37 0,.f ⟨22,15,0,1,1,0,0,0,0⟩,.s 37 0],[.f ⟨22,17,0,0,0,0,0,0,0⟩,.s 39 0,.f ⟨22,17,0,1,1,0,0,0,0⟩,.s 39 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0]],[.f ⟨22,17,0,0,0,0,0,0,3⟩,.s 37 4,.f ⟨22,17,0,1,1,0,0,0,3⟩,.s 37 4]⟩,
⟨8,3,5,38,[[.f ⟨22,16,0,0,0,0,0,0,0⟩,.s 38 0,.f ⟨22,16,0,1,1,0,0,0,0⟩,.s 38 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.f ⟨22,16,0,0,0,0,0,0,4⟩,.s 38 4,.f ⟨22,16,0,1,1,0,0,0,4⟩,.s 38 4]⟩,
⟨8,3,6,42,[[.f ⟨22,17,0,0,0,0,0,0,0⟩,.s 39 0,.f ⟨22,17,0,1,1,0,0,0,0⟩,.s 39 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0]],[.f ⟨22,17,0,0,0,0,0,0,4⟩,.s 39 4,.f ⟨22,17,0,1,1,0,0,0,4⟩,.s 39 4]⟩,
⟨8,3,7,39,[[.f ⟨22,18,0,0,0,0,0,0,0⟩,.s 40 0,.f ⟨22,18,0,1,1,0,0,0,0⟩,.s 40 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.f ⟨22,18,0,0,0,0,0,0,3⟩,.s 40 3,.f ⟨22,18,0,1,1,0,0,0,3⟩,.s 40 3]⟩,
⟨8,3,8,41,[[.f ⟨22,19,0,0,0,0,0,0,0⟩,.s 41 0,.f ⟨22,19,0,1,1,0,0,0,0⟩,.s 41 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.f ⟨22,19,0,0,0,0,0,0,3⟩,.s 41 3,.f ⟨22,19,0,1,1,0,0,0,3⟩,.s 41 3]⟩,
⟨8,3,9,39,[[.f ⟨22,18,0,0,0,0,0,0,0⟩,.s 40 0,.f ⟨22,18,0,1,1,0,0,0,0⟩,.s 40 0],[.f ⟨22,20,0,0,0,0,0,0,0⟩,.s 42 0,.f ⟨22,20,0,1,1,0,0,0,0⟩,.s 42 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.f ⟨22,18,0,0,0,0,0,0,4⟩,.s 40 4,.f ⟨22,18,0,1,1,0,0,0,4⟩,.s 40 4]⟩,
⟨8,3,10,40,[[.f ⟨22,19,0,0,0,0,0,0,0⟩,.s 41 0,.f ⟨22,19,0,1,1,0,0,0,0⟩,.s 41 0],[.f ⟨22,21,0,0,0,0,0,0,0⟩,.s 43 0,.f ⟨22,21,0,1,1,0,0,0,0⟩,.s 43 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.f ⟨22,21,0,0,0,0,0,0,4⟩,.s 43 4,.f ⟨22,21,0,1,1,0,0,0,4⟩,.s 43 4]⟩,
⟨9,3,0,36,[[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.s 22 3,.s 22 3,.s 22 3,.s 22 3]⟩,
⟨9,3,1,37,[[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 23 3,.s 23 3,.s 23 3,.s 23 3]⟩,
⟨9,3,2,44,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.f ⟨22,0,0,0,1,0,0,0,0⟩,.s 11 0,.f ⟨22,0,0,1,2,0,0,0,0⟩,.s 11 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0]],[.s 24 3,.s 24 3,.s 24 3,.s 24 3]⟩,
⟨9,3,3,38,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0]],[.s 25 4,.s 25 4,.s 25 4,.s 25 4]⟩,
⟨9,3,4,43,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.s 26 4,.s 26 4,.s 26 4,.s 26 4]⟩,
⟨9,3,5,39,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0]],[.s 27 4,.s 27 4,.s 27 4,.s 27 4]⟩,
⟨9,3,6,43,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.s 28 4,.s 28 4,.s 28 4,.s 28 4]⟩,
⟨9,3,7,40,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 29 3,.s 29 3,.s 29 3,.s 29 3]⟩,
⟨9,3,8,42,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 30 3,.s 30 3,.s 30 3,.s 30 3]⟩,
⟨9,3,9,40,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 29 4,.s 29 4,.s 29 4,.s 29 4]⟩,
⟨9,3,10,41,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 32 4,.s 32 4,.s 32 4,.s 32 4]⟩]⟩,
⟨1,4,2,0,0,[(2,4,3),(-2,4,1),(2,-4,-2)],2,4,3,16,0,0,0,0,22,0,0,0,
[⟨1,1,0,11,[[.f ⟨26,66,0,0,0,0,0,0,0⟩,.f ⟨26,66,1,0,1,0,0,0,0⟩],[.f ⟨4,2,0,0,0,0,0,0,0⟩,.f ⟨22,2,1,0,0,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨6,0,0,0,0,0,0,0,0⟩,.f ⟨7,11,1,0,0,0,0,0,0⟩]],[.f ⟨4,2,0,0,0,0,0,0,2⟩,.f ⟨22,2,1,0,0,0,0,0,2⟩]⟩,
⟨1,1,1,12,[[.f ⟨26,67,0,0,0,0,0,0,0⟩,.f ⟨26,67,1,0,1,0,0,0,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨6,1,0,0,0,0,0,0,0⟩,.f ⟨7,12,1,0,0,0,0,0,0⟩]],[.s 0 2,.s 0 2]⟩,
⟨1,1,2,21,[[.f ⟨26,68,0,0,0,0,0,0,0⟩,.f ⟨26,68,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.f ⟨26,110,0,0,0,0,0,0,0⟩,.f ⟨26,110,1,0,1,0,0,0,0⟩],[.f ⟨6,2,0,0,0,0,0,0,0⟩,.f ⟨7,13,1,0,0,0,0,0,0⟩]],[.s 4 2,.s 4 2]⟩,
⟨1,1,3,13,[[.f ⟨26,69,0,0,0,0,0,0,0⟩,.f ⟨26,69,1,0,1,0,0,0,0⟩],[.f ⟨26,71,0,0,0,0,0,0,0⟩,.f ⟨26,71,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨6,3,0,0,0,0,0,0,0⟩,.f ⟨7,14,1,0,0,0,0,0,0⟩]],[.s 1 2,.s 1 2]⟩,
⟨1,1,4,20,[[.f ⟨26,70,0,0,0,0,0,0,0⟩,.f ⟨26,70,1,0,1,0,0,0,0⟩],[.f ⟨26,72,0,0,0,0,0,0,0⟩,.f ⟨26,72,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨6,4,0,0,0,0,0,0,0⟩,.f ⟨7,15,1,0,0,0,0,0,0⟩]],[.f ⟨26,72,0,0,0,0,0,0,3⟩,.f ⟨26,72,1,0,1,0,0,0,3⟩]⟩,
⟨1,1,5,14,[[.f ⟨26,71,0,0,0,0,0,0,0⟩,.f ⟨26,71,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨6,3,0,0,0,0,0,0,0⟩,.f ⟨7,14,1,0,0,0,0,0,0⟩],[.f ⟨6,5,0,0,0,0,0,0,0⟩,.f ⟨7,16,1,0,0,0,0,0,0⟩]],[.s 3 3,.s 3 3]⟩,
⟨1,1,6,19,[[.f ⟨26,72,0,0,0,0,0,0,0⟩,.f ⟨26,72,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨6,4,0,0,0,0,0,0,0⟩,.f ⟨7,15,1,0,0,0,0,0,0⟩],[.f ⟨6,6,0,0,0,0,0,0,0⟩,.f ⟨7,17,1,0,0,0,0,0,0⟩]],[.s 8 1,.s 8 1]⟩,
⟨1,1,7,15,[[.f ⟨26,73,0,0,0,0,0,0,0⟩,.f ⟨26,73,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨6,7,0,0,0,0,0,0,0⟩,.f ⟨7,18,1,0,0,0,0,0,0⟩],[.f ⟨6,9,0,0,0,0,0,0,0⟩,.f ⟨7,20,1,0,0,0,0,0,0⟩]],[.s 5 2,.s 5 2]⟩,
⟨1,1,8,18,[[.f ⟨26,74,0,0,0,0,0,0,0⟩,.f ⟨26,74,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨6,8,0,0,0,0,0,0,0⟩,.f ⟨7,19,1,0,0,0,0,0,0⟩],[.f ⟨6,10,0,0,0,0,0,0,0⟩,.f ⟨7,21,1,0,0,0,0,0,0⟩]],[.s 10 2,.s 10 2]⟩,
⟨1,1,9,16,[[.f ⟨26,73,0,0,0,0,0,0,0⟩,.f ⟨26,73,1,0,1,0,0,0,0⟩],[.f ⟨26,75,0,0,0,0,0,0,0⟩,.f ⟨26,75,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨6,9,0,0,0,0,0,0,0⟩,.f ⟨7,20,1,0,0,0,0,0,0⟩]],[.f ⟨26,73,0,0,0,0,0,0,4⟩,.f ⟨26,73,1,0,1,0,0,0,4⟩]⟩,
⟨1,1,10,17,[[.f ⟨26,74,0,0,0,0,0,0,0⟩,.f ⟨26,74,1,0,1,0,0,0,0⟩],[.f ⟨26,76,0,0,0,0,0,0,0⟩,.f ⟨26,76,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨6,10,0,0,0,0,0,0,0⟩,.f ⟨7,21,1,0,0,0,0,0,0⟩]],[.s 9 3,.s 9 3]⟩,
⟨3,2,0,22,[[.f ⟨26,143,0,0,0,0,0,0,0⟩,.f ⟨26,143,1,0,1,0,0,0,0⟩],[.f ⟨20,2,0,0,0,0,0,0,0⟩,.f ⟨22,13,1,0,0,0,0,0,0⟩],[.s 12 0,.s 12 0],[.f ⟨7,0,0,0,0,0,0,0,0⟩,.f ⟨7,0,1,0,1,0,0,0,0⟩]],[.f ⟨20,2,0,0,0,0,0,0,2⟩,.f ⟨22,13,1,0,0,0,0,0,2⟩]⟩,
⟨3,2,1,23,[[.f ⟨26,144,0,0,0,0,0,0,0⟩,.f ⟨26,144,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨7,1,0,0,0,0,0,0,0⟩,.f ⟨7,1,1,0,1,0,0,0,0⟩]],[.s 11 2,.s 11 2]⟩,
⟨3,2,2,32,[[.f ⟨26,145,0,0,0,0,0,0,0⟩,.f ⟨26,145,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨26,165,0,0,0,0,0,0,0⟩,.f ⟨26,165,1,0,1,0,0,0,0⟩],[.f ⟨7,2,0,0,0,0,0,0,0⟩,.f ⟨7,2,1,0,1,0,0,0,0⟩]],[.s 15 2,.s 15 2]⟩,
⟨3,2,3,24,[[.f ⟨26,146,0,0,0,0,0,0,0⟩,.f ⟨26,146,1,0,1,0,0,0,0⟩],[.f ⟨26,148,0,0,0,0,0,0,0⟩,.f ⟨26,148,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨7,3,0,0,0,0,0,0,0⟩,.f ⟨7,3,1,0,1,0,0,0,0⟩]],[.s 12 2,.s 12 2]⟩,
⟨3,2,4,31,[[.f ⟨26,147,0,0,0,0,0,0,0⟩,.f ⟨26,147,1,0,1,0,0,0,0⟩],[.f ⟨26,149,0,0,0,0,0,0,0⟩,.f ⟨26,149,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨7,4,0,0,0,0,0,0,0⟩,.f ⟨7,4,1,0,1,0,0,0,0⟩]],[.f ⟨26,149,0,0,0,0,0,0,3⟩,.f ⟨26,149,1,0,1,0,0,0,3⟩]⟩,
⟨3,2,5,25,[[.f ⟨26,148,0,0,0,0,0,0,0⟩,.f ⟨26,148,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨7,3,0,0,0,0,0,0,0⟩,.f ⟨7,3,1,0,1,0,0,0,0⟩],[.f ⟨7,5,0,0,0,0,0,0,0⟩,.f ⟨7,5,1,0,1,0,0,0,0⟩]],[.s 14 3,.s 14 3]⟩,
⟨3,2,6,30,[[.f ⟨26,149,0,0,0,0,0,0,0⟩,.f ⟨26,149,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨7,4,0,0,0,0,0,0,0⟩,.f ⟨7,4,1,0,1,0,0,0,0⟩],[.f ⟨7,6,0,0,0,0,0,0,0⟩,.f ⟨7,6,1,0,1,0,0,0,0⟩]],[.s 19 1,.s 19 1]⟩,
⟨3,2,7,26,[[.f ⟨26,150,0,0,0,0,0,0,0⟩,.f ⟨26,150,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨7,7,0,0,0,0,0,0,0⟩,.f ⟨7,7,1,0,1,0,0,0,0⟩],[.f ⟨7,9,0,0,0,0,0,0,0⟩,.f ⟨7,9,1,0,1,0,0,0,0⟩]],[.s 16 2,.s 16 2]⟩,
⟨3,2,8,29,[[.f ⟨26,151,0,0,0,0,0,0,0⟩,.f ⟨26,151,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨7,8,0,0,0,0,0,0,0⟩,.f ⟨7,8,1,0,1,0,0,0,0⟩],[.f ⟨7,10,0,0,0,0,0,0,0⟩,.f ⟨7,10,1,0,1,0,0,0,0⟩]],[.s 21 2,.s 21 2]⟩,
⟨3,2,9,27,[[.f ⟨26,150,0,0,0,0,0,0,0⟩,.f ⟨26,150,1,0,1,0,0,0,0⟩],[.f ⟨26,152,0,0,0,0,0,0,0⟩,.f ⟨26,152,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨7,9,0,0,0,0,0,0,0⟩,.f ⟨7,9,1,0,1,0,0,0,0⟩]],[.f ⟨26,150,0,0,0,0,0,0,4⟩,.f ⟨26,150,1,0,1,0,0,0,4⟩]⟩,
⟨3,2,10,28,[[.f ⟨26,151,0,0,0,0,0,0,0⟩,.f ⟨26,151,1,0,1,0,0,0,0⟩],[.f ⟨26,153,0,0,0,0,0,0,0⟩,.f ⟨26,153,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨7,10,0,0,0,0,0,0,0⟩,.f ⟨7,10,1,0,1,0,0,0,0⟩]],[.s 20 3,.s 20 3]⟩]⟩,
⟨1,-4,2,0,0,[(-2,4,3),(2,4,1),(-2,-4,-2)],-2,4,3,16,0,0,0,0,22,0,0,0,
[⟨-3,2,0,22,[[.f ⟨9,11,0,0,0,0,0,0,0⟩,.f ⟨9,11,1,0,1,0,0,0,0⟩],[.f ⟨27,2,0,0,0,0,0,0,0⟩,.f ⟨28,2,1,0,0,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨26,11,0,0,0,0,0,0,0⟩,.f ⟨26,11,0,0,0,1,0,1,0⟩]],[.f ⟨27,2,0,0,0,0,0,0,2⟩,.f ⟨28,2,1,0,0,0,0,0,2⟩]⟩,
⟨-3,2,1,23,[[.f ⟨9,12,0,0,0,0,0,0,0⟩,.f ⟨9,12,1,0,1,0,0,0,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨26,12,0,0,0,0,0,0,0⟩,.f ⟨26,12,0,0,0,1,0,1,0⟩]],[.s 0 2,.s 0 2]⟩,
⟨-3,2,2,32,[[.f ⟨9,13,0,0,0,0,0,0,0⟩,.f ⟨9,13,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.f ⟨26,0,0,0,0,0,0,0,0⟩,.f ⟨26,0,0,0,0,1,0,1,0⟩],[.f ⟨26,13,0,0,0,0,0,0,0⟩,.f ⟨26,13,0,0,0,1,0,1,0⟩]],[.s 4 2,.s 4 2]⟩,
⟨-3,2,3,24,[[.f ⟨9,14,0,0,0,0,0,0,0⟩,.f ⟨9,14,1,0,1,0,0,0,0⟩],[.f ⟨9,16,0,0,0,0,0,0,0⟩,.f ⟨9,16,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨26,14,0,0,0,0,0,0,0⟩,.f ⟨26,14,0,0,0,1,0,1,0⟩]],[.s 1 2,.s 1 2]⟩,
⟨-3,2,4,31,[[.f ⟨9,15,0,0,0,0,0,0,0⟩,.f ⟨9,15,1,0,1,0,0,0,0⟩],[.f ⟨9,17,0,0,0,0,0,0,0⟩,.f ⟨9,17,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨26,15,0,0,0,0,0,0,0⟩,.f ⟨26,15,0,0,0,1,0,1,0⟩]],[.f ⟨9,17,0,0,0,0,0,0,3⟩,.f ⟨9,17,1,0,1,0,0,0,3⟩]⟩,
⟨-3,2,5,25,[[.f ⟨9,16,0,0,0,0,0,0,0⟩,.f ⟨9,16,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨26,14,0,0,0,0,0,0,0⟩,.f ⟨26,14,0,0,0,1,0,1,0⟩],[.f ⟨26,16,0,0,0,0,0,0,0⟩,.f ⟨26,16,0,0,0,1,0,1,0⟩]],[.s 3 3,.s 3 3]⟩,
⟨-3,2,6,30,[[.f ⟨9,17,0,0,0,0,0,0,0⟩,.f ⟨9,17,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨26,15,0,0,0,0,0,0,0⟩,.f ⟨26,15,0,0,0,1,0,1,0⟩],[.f ⟨26,17,0,0,0,0,0,0,0⟩,.f ⟨26,17,0,0,0,1,0,1,0⟩]],[.s 8 1,.s 8 1]⟩,
⟨-3,2,7,26,[[.f ⟨9,18,0,0,0,0,0,0,0⟩,.f ⟨9,18,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨26,18,0,0,0,0,0,0,0⟩,.f ⟨26,18,0,0,0,1,0,1,0⟩],[.f ⟨26,20,0,0,0,0,0,0,0⟩,.f ⟨26,20,0,0,0,1,0,1,0⟩]],[.s 5 2,.s 5 2]⟩,
⟨-3,2,8,29,[[.f ⟨9,19,0,0,0,0,0,0,0⟩,.f ⟨9,19,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨26,19,0,0,0,0,0,0,0⟩,.f ⟨26,19,0,0,0,1,0,1,0⟩],[.f ⟨26,21,0,0,0,0,0,0,0⟩,.f ⟨26,21,0,0,0,1,0,1,0⟩]],[.s 10 2,.s 10 2]⟩,
⟨-3,2,9,27,[[.f ⟨9,18,0,0,0,0,0,0,0⟩,.f ⟨9,18,1,0,1,0,0,0,0⟩],[.f ⟨9,20,0,0,0,0,0,0,0⟩,.f ⟨9,20,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨26,20,0,0,0,0,0,0,0⟩,.f ⟨26,20,0,0,0,1,0,1,0⟩]],[.f ⟨9,18,0,0,0,0,0,0,4⟩,.f ⟨9,18,1,0,1,0,0,0,4⟩]⟩,
⟨-3,2,10,28,[[.f ⟨9,19,0,0,0,0,0,0,0⟩,.f ⟨9,19,1,0,1,0,0,0,0⟩],[.f ⟨9,21,0,0,0,0,0,0,0⟩,.f ⟨9,21,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨26,21,0,0,0,0,0,0,0⟩,.f ⟨26,21,0,0,0,1,0,1,0⟩]],[.s 9 3,.s 9 3]⟩,
⟨-1,1,0,11,[[.f ⟨8,0,0,0,0,0,0,0,0⟩,.f ⟨9,0,1,0,0,0,0,0,0⟩],[.f ⟨10,13,0,0,0,0,0,0,0⟩,.f ⟨28,13,1,0,0,0,0,0,0⟩],[.s 12 0,.s 12 0],[.f ⟨26,66,0,0,0,0,0,0,0⟩,.f ⟨26,66,0,0,0,1,0,1,0⟩]],[.f ⟨10,13,0,0,0,0,0,0,2⟩,.f ⟨28,13,1,0,0,0,0,0,2⟩]⟩,
⟨-1,1,1,12,[[.f ⟨8,1,0,0,0,0,0,0,0⟩,.f ⟨9,1,1,0,0,0,0,0,0⟩],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨26,67,0,0,0,0,0,0,0⟩,.f ⟨26,67,0,0,0,1,0,1,0⟩]],[.s 11 2,.s 11 2]⟩,
⟨-1,1,2,21,[[.f ⟨8,2,0,0,0,0,0,0,0⟩,.f ⟨9,2,1,0,0,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨26,33,0,0,0,0,0,0,0⟩,.f ⟨26,33,0,0,0,1,0,1,0⟩],[.f ⟨26,68,0,0,0,0,0,0,0⟩,.f ⟨26,68,0,0,0,1,0,1,0⟩]],[.s 15 2,.s 15 2]⟩,
⟨-1,1,3,13,[[.f ⟨8,3,0,0,0,0,0,0,0⟩,.f ⟨9,3,1,0,0,0,0,0,0⟩],[.f ⟨8,5,0,0,0,0,0,0,0⟩,.f ⟨9,5,1,0,0,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨26,69,0,0,0,0,0,0,0⟩,.f ⟨26,69,0,0,0,1,0,1,0⟩]],[.s 12 2,.s 12 2]⟩,
⟨-1,1,4,20,[[.f ⟨8,4,0,0,0,0,0,0,0⟩,.f ⟨9,4,1,0,0,0,0,0,0⟩],[.f ⟨8,6,0,0,0,0,0,0,0⟩,.f ⟨9,6,1,0,0,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨26,70,0,0,0,0,0,0,0⟩,.f ⟨26,70,0,0,0,1,0,1,0⟩]],[.f ⟨8,6,0,0,0,0,0,0,3⟩,.f ⟨9,6,1,0,0,0,0,0,3⟩]⟩,
⟨-1,1,5,14,[[.f ⟨8,5,0,0,0,0,0,0,0⟩,.f ⟨9,5,1,0,0,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨26,69,0,0,0,0,0,0,0⟩,.f ⟨26,69,0,0,0,1,0,1,0⟩],[.f ⟨26,71,0,0,0,0,0,0,0⟩,.f ⟨26,71,0,0,0,1,0,1,0⟩]],[.s 14 3,.s 14 3]⟩,
⟨-1,1,6,19,[[.f ⟨8,6,0,0,0,0,0,0,0⟩,.f ⟨9,6,1,0,0,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨26,70,0,0,0,0,0,0,0⟩,.f ⟨26,70,0,0,0,1,0,1,0⟩],[.f ⟨26,72,0,0,0,0,0,0,0⟩,.f ⟨26,72,0,0,0,1,0,1,0⟩]],[.s 19 1,.s 19 1]⟩,
⟨-1,1,7,15,[[.f ⟨8,7,0,0,0,0,0,0,0⟩,.f ⟨9,7,1,0,0,0,0,0,0⟩],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨26,73,0,0,0,0,0,0,0⟩,.f ⟨26,73,0,0,0,1,0,1,0⟩],[.f ⟨26,75,0,0,0,0,0,0,0⟩,.f ⟨26,75,0,0,0,1,0,1,0⟩]],[.s 16 2,.s 16 2]⟩,
⟨-1,1,8,18,[[.f ⟨8,8,0,0,0,0,0,0,0⟩,.f ⟨9,8,1,0,0,0,0,0,0⟩],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨26,74,0,0,0,0,0,0,0⟩,.f ⟨26,74,0,0,0,1,0,1,0⟩],[.f ⟨26,76,0,0,0,0,0,0,0⟩,.f ⟨26,76,0,0,0,1,0,1,0⟩]],[.s 21 2,.s 21 2]⟩,
⟨-1,1,9,16,[[.f ⟨8,7,0,0,0,0,0,0,0⟩,.f ⟨9,7,1,0,0,0,0,0,0⟩],[.f ⟨8,9,0,0,0,0,0,0,0⟩,.f ⟨9,9,1,0,0,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨26,75,0,0,0,0,0,0,0⟩,.f ⟨26,75,0,0,0,1,0,1,0⟩]],[.f ⟨8,7,0,0,0,0,0,0,4⟩,.f ⟨9,7,1,0,0,0,0,0,4⟩]⟩,
⟨-1,1,10,17,[[.f ⟨8,8,0,0,0,0,0,0,0⟩,.f ⟨9,8,1,0,0,0,0,0,0⟩],[.f ⟨8,10,0,0,0,0,0,0,0⟩,.f ⟨9,10,1,0,0,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨26,76,0,0,0,0,0,0,0⟩,.f ⟨26,76,0,0,0,1,0,1,0⟩]],[.s 20 3,.s 20 3]⟩]⟩,
⟨2,4,2,-4,2,[(2,4,3),(-2,4,3)],2,4,3,16,-2,4,3,16,22,22,1,1,
[⟨-3,3,0,33,[[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.f ⟨25,2,0,0,0,0,0,0,0⟩,.s 134 0,.f ⟨25,2,0,1,1,0,0,0,0⟩,.s 134 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.f ⟨25,2,0,0,0,0,0,0,2⟩,.s 134 2,.f ⟨25,2,0,1,1,0,0,0,2⟩,.s 134 2]⟩,
⟨-3,3,1,34,[[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 0 2,.s 0 2,.s 0 2,.s 0 2]⟩,
⟨-3,3,2,43,[[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 110 0,.s 110 0,.s 110 0,.s 110 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0]],[.s 4 2,.s 4 2,.s 4 2,.s 4 2]⟩,
⟨-3,3,3,35,[[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0]],[.s 1 2,.s 1 2,.s 1 2,.s 1 2]⟩,
⟨-3,3,4,42,[[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.s 72 3,.s 72 3,.s 72 3,.s 72 3]⟩,
⟨-3,3,5,36,[[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0]],[.s 3 3,.s 3 3,.s 3 3,.s 3 3]⟩,
⟨-3,3,6,41,[[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.s 8 1,.s 8 1,.s 8 1,.s 8 1]⟩,
⟨-3,3,7,37,[[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 5 2,.s 5 2,.s 5 2,.s 5 2]⟩,
⟨-3,3,8,40,[[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 10 2,.s 10 2,.s 10 2,.s 10 2]⟩,
⟨-3,3,9,38,[[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 73 4,.s 73 4,.s 73 4,.s 73 4]⟩,
⟨-3,3,10,39,[[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 9 3,.s 9 3,.s 9 3,.s 9 3]⟩,
⟨-2,2,0,22,[[.f ⟨25,0,0,0,0,0,0,0,0⟩,.s 132 0,.f ⟨25,0,0,1,1,0,0,0,0⟩,.s 132 0],[.f ⟨8,2,0,0,0,0,0,0,0⟩,.s 156 0,.f ⟨9,2,0,1,0,0,0,0,0⟩,.s 156 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.f ⟨8,2,0,0,0,0,0,0,2⟩,.s 156 2,.f ⟨9,2,0,1,0,0,0,0,2⟩,.s 156 2]⟩,
⟨-2,2,1,23,[[.f ⟨25,1,0,0,0,0,0,0,0⟩,.s 133 0,.f ⟨25,1,0,1,1,0,0,0,0⟩,.s 133 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.s 11 2,.s 11 2,.s 11 2,.s 11 2]⟩,
⟨-2,2,2,32,[[.f ⟨25,2,0,0,0,0,0,0,0⟩,.s 134 0,.f ⟨25,2,0,1,1,0,0,0,0⟩,.s 134 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 15 2,.s 15 2,.s 15 2,.s 15 2]⟩,
⟨-2,2,3,24,[[.f ⟨25,3,0,0,0,0,0,0,0⟩,.s 135 0,.f ⟨25,3,0,1,1,0,0,0,0⟩,.s 135 0],[.f ⟨25,5,0,0,0,0,0,0,0⟩,.s 137 0,.f ⟨25,5,0,1,1,0,0,0,0⟩,.s 137 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0]],[.s 12 2,.s 12 2,.s 12 2,.s 12 2]⟩,
⟨-2,2,4,31,[[.f ⟨25,4,0,0,0,0,0,0,0⟩,.s 136 0,.f ⟨25,4,0,1,1,0,0,0,0⟩,.s 136 0],[.f ⟨25,6,0,0,0,0,0,0,0⟩,.s 138 0,.f ⟨25,6,0,1,1,0,0,0,0⟩,.s 138 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0]],[.f ⟨25,6,0,0,0,0,0,0,3⟩,.s 138 3,.f ⟨25,6,0,1,1,0,0,0,3⟩,.s 138 3]⟩,
⟨-2,2,5,25,[[.f ⟨25,5,0,0,0,0,0,0,0⟩,.s 137 0,.f ⟨25,5,0,1,1,0,0,0,0⟩,.s 137 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.s 14 3,.s 14 3,.s 14 3,.s 14 3]⟩,
⟨-2,2,6,30,[[.f ⟨25,6,0,0,0,0,0,0,0⟩,.s 138 0,.f ⟨25,6,0,1,1,0,0,0,0⟩,.s 138 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0]],[.s 19 1,.s 19 1,.s 19 1,.s 19 1]⟩,
⟨-2,2,7,26,[[.f ⟨25,7,0,0,0,0,0,0,0⟩,.s 139 0,.f ⟨25,7,0,1,1,0,0,0,0⟩,.s 139 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.s 16 2,.s 16 2,.s 16 2,.s 16 2]⟩,
⟨-2,2,8,29,[[.f ⟨25,8,0,0,0,0,0,0,0⟩,.s 140 0,.f ⟨25,8,0,1,1,0,0,0,0⟩,.s 140 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 21 2,.s 21 2,.s 21 2,.s 21 2]⟩,
⟨-2,2,9,27,[[.f ⟨25,7,0,0,0,0,0,0,0⟩,.s 139 0,.f ⟨25,7,0,1,1,0,0,0,0⟩,.s 139 0],[.f ⟨25,9,0,0,0,0,0,0,0⟩,.s 141 0,.f ⟨25,9,0,1,1,0,0,0,0⟩,.s 141 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.f ⟨25,7,0,0,0,0,0,0,4⟩,.s 139 4,.f ⟨25,7,0,1,1,0,0,0,4⟩,.s 139 4]⟩,
⟨-2,2,10,28,[[.f ⟨25,8,0,0,0,0,0,0,0⟩,.s 140 0,.f ⟨25,8,0,1,1,0,0,0,0⟩,.s 140 0],[.f ⟨25,10,0,0,0,0,0,0,0⟩,.s 142 0,.f ⟨25,10,0,1,1,0,0,0,0⟩,.s 142 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 20 3,.s 20 3,.s 20 3,.s 20 3]⟩,
⟨-2,3,0,33,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0]],[.s 13 2,.s 13 2,.s 13 2,.s 13 2]⟩,
⟨-2,3,1,34,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0]],[.s 22 2,.s 22 2,.s 22 2,.s 22 2]⟩,
⟨-2,3,2,43,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0]],[.s 26 2,.s 26 2,.s 26 2,.s 26 2]⟩,
⟨-2,3,3,35,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 23 2,.s 23 2,.s 23 2,.s 23 2]⟩,
⟨-2,3,4,42,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0]],[.s 6 3,.s 6 3,.s 6 3,.s 6 3]⟩,
⟨-2,3,5,36,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0]],[.s 25 3,.s 25 3,.s 25 3,.s 25 3]⟩,
⟨-2,3,6,41,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0]],[.s 30 1,.s 30 1,.s 30 1,.s 30 1]⟩,
⟨-2,3,7,37,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]],[.s 27 2,.s 27 2,.s 27 2,.s 27 2]⟩,
⟨-2,3,8,40,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0]],[.s 32 2,.s 32 2,.s 32 2,.s 32 2]⟩,
⟨-2,3,9,38,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]],[.s 7 4,.s 7 4,.s 7 4,.s 7 4]⟩,
⟨-2,3,10,39,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0]],[.s 31 3,.s 31 3,.s 31 3,.s 31 3]⟩,
⟨-1,2,0,22,[[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.f ⟨25,13,0,0,0,0,0,0,0⟩,.s 167 0,.f ⟨25,13,0,1,1,0,0,0,0⟩,.s 167 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0]],[.f ⟨25,13,0,0,0,0,0,0,2⟩,.s 167 2,.f ⟨25,13,0,1,1,0,0,0,2⟩,.s 167 2]⟩,
⟨-1,2,1,23,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0]],[.s 33 2,.s 33 2,.s 33 2,.s 33 2]⟩,
⟨-1,2,2,32,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0]],[.s 37 2,.s 37 2,.s 37 2,.s 37 2]⟩,
⟨-1,2,3,24,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0]],[.s 34 2,.s 34 2,.s 34 2,.s 34 2]⟩,
⟨-1,2,4,31,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0]],[.s 17 3,.s 17 3,.s 17 3,.s 17 3]⟩,
⟨-1,2,5,25,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0]],[.s 36 3,.s 36 3,.s 36 3,.s 36 3]⟩,
⟨-1,2,6,30,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0]],[.s 41 1,.s 41 1,.s 41 1,.s 41 1]⟩,
⟨-1,2,7,26,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0]],[.s 38 2,.s 38 2,.s 38 2,.s 38 2]⟩,
⟨-1,2,8,29,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0]],[.s 43 2,.s 43 2,.s 43 2,.s 43 2]⟩,
⟨-1,2,9,27,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0]],[.s 18 4,.s 18 4,.s 18 4,.s 18 4]⟩,
⟨-1,2,10,28,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0]],[.s 42 3,.s 42 3,.s 42 3,.s 42 3]⟩,
⟨-1,3,0,33,[[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0]],[.s 35 2,.s 35 2,.s 35 2,.s 35 2]⟩,
⟨-1,3,1,34,[[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0]],[.s 44 2,.s 44 2,.s 44 2,.s 44 2]⟩,
⟨-1,3,2,43,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0]],[.s 48 2,.s 48 2,.s 48 2,.s 48 2]⟩,
⟨-1,3,3,35,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0]],[.s 45 2,.s 45 2,.s 45 2,.s 45 2]⟩,
⟨-1,3,4,42,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0]],[.s 28 3,.s 28 3,.s 28 3,.s 28 3]⟩,
⟨-1,3,5,36,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0]],[.s 47 3,.s 47 3,.s 47 3,.s 47 3]⟩,
⟨-1,3,6,41,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0]],[.s 52 1,.s 52 1,.s 52 1,.s 52 1]⟩,
⟨-1,3,7,37,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0],[.s 97 0,.s 97 0,.s 97 0,.s 97 0]],[.s 49 2,.s 49 2,.s 49 2,.s 49 2]⟩,
⟨-1,3,8,40,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 98 0,.s 98 0,.s 98 0,.s 98 0]],[.s 54 2,.s 54 2,.s 54 2,.s 54 2]⟩,
⟨-1,3,9,38,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 97 0,.s 97 0,.s 97 0,.s 97 0]],[.s 29 4,.s 29 4,.s 29 4,.s 29 4]⟩,
⟨-1,3,10,39,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 98 0,.s 98 0,.s 98 0,.s 98 0]],[.s 53 3,.s 53 3,.s 53 3,.s 53 3]⟩,
⟨-1,4,0,44,[[.s 143 0,.s 143 0,.s 143 0,.s 143 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 99 0,.s 99 0,.s 99 0,.s 99 0]],[.s 46 2,.s 46 2,.s 46 2,.s 46 2]⟩,
⟨-1,4,1,45,[[.s 144 0,.s 144 0,.s 144 0,.s 144 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 100 0,.s 100 0,.s 100 0,.s 100 0]],[.s 55 2,.s 55 2,.s 55 2,.s 55 2]⟩,
⟨-1,4,2,54,[[.s 145 0,.s 145 0,.s 145 0,.s 145 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 165 0,.s 165 0,.s 165 0,.s 165 0],[.s 101 0,.s 101 0,.s 101 0,.s 101 0]],[.s 59 2,.s 59 2,.s 59 2,.s 59 2]⟩,
⟨-1,4,3,46,[[.s 146 0,.s 146 0,.s 146 0,.s 146 0],[.s 148 0,.s 148 0,.s 148 0,.s 148 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0]],[.s 56 2,.s 56 2,.s 56 2,.s 56 2]⟩,
⟨-1,4,4,53,[[.s 147 0,.s 147 0,.s 147 0,.s 147 0],[.s 149 0,.s 149 0,.s 149 0,.s 149 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0]],[.s 149 3,.s 149 3,.s 149 3,.s 149 3]⟩,
⟨-1,4,5,47,[[.s 148 0,.s 148 0,.s 148 0,.s 148 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0]],[.s 58 3,.s 58 3,.s 58 3,.s 58 3]⟩,
⟨-1,4,6,52,[[.s 149 0,.s 149 0,.s 149 0,.s 149 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0]],[.s 63 1,.s 63 1,.s 63 1,.s 63 1]⟩,
⟨-1,4,7,48,[[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 108 0,.s 108 0,.s 108 0,.s 108 0]],[.s 60 2,.s 60 2,.s 60 2,.s 60 2]⟩,
⟨-1,4,8,51,[[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0]],[.s 65 2,.s 65 2,.s 65 2,.s 65 2]⟩,
⟨-1,4,9,49,[[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 108 0,.s 108 0,.s 108 0,.s 108 0]],[.s 150 4,.s 150 4,.s 150 4,.s 150 4]⟩,
⟨-1,4,10,50,[[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0]],[.s 64 3,.s 64 3,.s 64 3,.s 64 3]⟩,
⟨0,1,0,11,[[.f ⟨25,11,0,0,0,0,0,0,0⟩,.s 165 0,.f ⟨25,11,0,1,1,0,0,0,0⟩,.s 165 0],[.f ⟨0,2,0,0,0,0,0,0,0⟩,.f ⟨7,2,1,0,0,0,0,0,0⟩,.f ⟨9,13,0,1,0,0,0,0,0⟩,.s 101 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.f ⟨24,0,0,0,0,0,0,0,0⟩,.f ⟨24,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0]],[.f ⟨0,2,0,0,0,0,0,0,2⟩,.f ⟨7,2,1,0,0,0,0,0,2⟩,.f ⟨9,13,0,1,0,0,0,0,2⟩,.s 101 2]⟩,
⟨0,1,1,12,[[.f ⟨25,12,0,0,0,0,0,0,0⟩,.s 166 0,.f ⟨25,12,0,1,1,0,0,0,0⟩,.s 166 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.f ⟨24,1,0,0,0,0,0,0,0⟩,.f ⟨24,1,1,0,1,0,0,0,0⟩,.s 1 0,.s 1 0]],[.s 66 2,.s 66 2,.s 66 2,.s 66 2]⟩,
⟨0,1,2,21,[[.f ⟨25,13,0,0,0,0,0,0,0⟩,.s 167 0,.f ⟨25,13,0,1,1,0,0,0,0⟩,.s 167 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.f ⟨24,2,0,0,0,0,0,0,0⟩,.f ⟨24,2,1,0,1,0,0,0,0⟩,.s 2 0,.s 2 0]],[.s 70 2,.s 70 2,.s 70 2,.s 70 2]⟩,
⟨0,1,3,13,[[.f ⟨25,14,0,0,0,0,0,0,0⟩,.s 168 0,.f ⟨25,14,0,1,1,0,0,0,0⟩,.s 168 0],[.f ⟨25,16,0,0,0,0,0,0,0⟩,.s 170 0,.f ⟨25,16,0,1,1,0,0,0,0⟩,.s 170 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.f ⟨24,3,0,0,0,0,0,0,0⟩,.f ⟨24,3,1,0,1,0,0,0,0⟩,.s 3 0,.s 3 0]],[.s 67 2,.s 67 2,.s 67 2,.s 67 2]⟩,
⟨0,1,4,20,[[.f ⟨25,15,0,0,0,0,0,0,0⟩,.s 169 0,.f ⟨25,15,0,1,1,0,0,0,0⟩,.s 169 0],[.f ⟨25,17,0,0,0,0,0,0,0⟩,.s 171 0,.f ⟨25,17,0,1,1,0,0,0,0⟩,.s 171 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.f ⟨24,4,0,0,0,0,0,0,0⟩,.f ⟨24,4,1,0,1,0,0,0,0⟩,.s 4 0,.s 4 0]],[.f ⟨25,17,0,0,0,0,0,0,3⟩,.s 171 3,.f ⟨25,17,0,1,1,0,0,0,3⟩,.s 171 3]⟩,
⟨0,1,5,14,[[.f ⟨25,16,0,0,0,0,0,0,0⟩,.s 170 0,.f ⟨25,16,0,1,1,0,0,0,0⟩,.s 170 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.f ⟨24,3,0,0,0,0,0,0,0⟩,.f ⟨24,3,1,0,1,0,0,0,0⟩,.s 3 0,.s 3 0],[.f ⟨24,5,0,0,0,0,0,0,0⟩,.f ⟨24,5,1,0,1,0,0,0,0⟩,.s 5 0,.s 5 0]],[.s 69 3,.s 69 3,.s 69 3,.s 69 3]⟩,
⟨0,1,6,19,[[.f ⟨25,17,0,0,0,0,0,0,0⟩,.s 171 0,.f ⟨25,17,0,1,1,0,0,0,0⟩,.s 171 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.f ⟨24,4,0,0,0,0,0,0,0⟩,.f ⟨24,4,1,0,1,0,0,0,0⟩,.s 4 0,.s 4 0],[.f ⟨24,6,0,0,0,0,0,0,0⟩,.f ⟨24,6,1,0,1,0,0,0,0⟩,.s 6 0,.s 6 0]],[.s 74 1,.s 74 1,.s 74 1,.s 74 1]⟩,
⟨0,1,7,15,[[.f ⟨25,18,0,0,0,0,0,0,0⟩,.s 172 0,.f ⟨25,18,0,1,1,0,0,0,0⟩,.s 172 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.f ⟨24,7,0,0,0,0,0,0,0⟩,.f ⟨24,7,1,0,1,0,0,0,0⟩,.s 7 0,.s 7 0],[.f ⟨24,9,0,0,0,0,0,0,0⟩,.f ⟨24,9,1,0,1,0,0,0,0⟩,.s 9 0,.s 9 0]],[.s 71 2,.s 71 2,.s 71 2,.s 71 2]⟩,
⟨0,1,8,18,[[.f ⟨25,19,0,0,0,0,0,0,0⟩,.s 173 0,.f ⟨25,19,0,1,1,0,0,0,0⟩,.s 173 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.f ⟨24,8,0,0,0,0,0,0,0⟩,.f ⟨24,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0],[.f ⟨24,10,0,0,0,0,0,0,0⟩,.f ⟨24,10,1,0,1,0,0,0,0⟩,.s 10 0,.s 10 0]],[.s 76 2,.s 76 2,.s 76 2,.s 76 2]⟩,
⟨0,1,9,16,[[.f ⟨25,18,0,0,0,0,0,0,0⟩,.s 172 0,.f ⟨25,18,0,1,1,0,0,0,0⟩,.s 172 0],[.f ⟨25,20,0,0,0,0,0,0,0⟩,.s 174 0,.f ⟨25,20,0,1,1,0,0,0,0⟩,.s 174 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.f ⟨24,9,0,0,0,0,0,0,0⟩,.f ⟨24,9,1,0,1,0,0,0,0⟩,.s 9 0,.s 9 0]],[.f ⟨25,18,0,0,0,0,0,0,4⟩,.s 172 4,.f ⟨25,18,0,1,1,0,0,0,4⟩,.s 172 4]⟩,
⟨0,1,10,17,[[.f ⟨25,19,0,0,0,0,0,0,0⟩,.s 173 0,.f ⟨25,19,0,1,1,0,0,0,0⟩,.s 173 0],[.f ⟨25,21,0,0,0,0,0,0,0⟩,.s 175 0,.f ⟨25,21,0,1,1,0,0,0,0⟩,.s 175 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.f ⟨24,10,0,0,0,0,0,0,0⟩,.f ⟨24,10,1,0,1,0,0,0,0⟩,.s 10 0,.s 10 0]],[.s 75 3,.s 75 3,.s 75 3,.s 75 3]⟩,
⟨0,2,0,22,[[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 110 0,.s 110 0,.s 110 0,.s 110 0]],[.s 68 2,.s 68 2,.s 68 2,.s 68 2]⟩,
⟨0,2,1,23,[[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 111 0,.s 111 0,.s 111 0,.s 111 0]],[.s 77 2,.s 77 2,.s 77 2,.s 77 2]⟩,
⟨0,2,2,32,[[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 112 0,.s 112 0,.s 112 0,.s 112 0]],[.s 81 2,.s 81 2,.s 81 2,.s 81 2]⟩,
⟨0,2,3,24,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0]],[.s 78 2,.s 78 2,.s 78 2,.s 78 2]⟩,
⟨0,2,4,31,[[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0]],[.s 39 3,.s 39 3,.s 39 3,.s 39 3]⟩,
⟨0,2,5,25,[[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0]],[.s 80 3,.s 80 3,.s 80 3,.s 80 3]⟩,
⟨0,2,6,30,[[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0]],[.s 85 1,.s 85 1,.s 85 1,.s 85 1]⟩,
⟨0,2,7,26,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0]],[.s 82 2,.s 82 2,.s 82 2,.s 82 2]⟩,
⟨0,2,8,29,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 120 0,.s 120 0,.s 120 0,.s 120 0]],[.s 87 2,.s 87 2,.s 87 2,.s 87 2]⟩,
⟨0,2,9,27,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0]],[.s 40 4,.s 40 4,.s 40 4,.s 40 4]⟩,
⟨0,2,10,28,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 120 0,.s 120 0,.s 120 0,.s 120 0]],[.s 86 3,.s 86 3,.s 86 3,.s 86 3]⟩,
⟨0,3,0,33,[[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 121 0,.s 121 0,.s 121 0,.s 121 0]],[.s 79 2,.s 79 2,.s 79 2,.s 79 2]⟩,
⟨0,3,1,34,[[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 122 0,.s 122 0,.s 122 0,.s 122 0]],[.s 88 2,.s 88 2,.s 88 2,.s 88 2]⟩,
⟨0,3,2,43,[[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 99 0,.s 99 0,.s 99 0,.s 99 0],[.s 123 0,.s 123 0,.s 123 0,.s 123 0]],[.s 92 2,.s 92 2,.s 92 2,.s 92 2]⟩,
⟨0,3,3,35,[[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0]],[.s 89 2,.s 89 2,.s 89 2,.s 89 2]⟩,
⟨0,3,4,42,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0]],[.s 50 3,.s 50 3,.s 50 3,.s 50 3]⟩,
⟨0,3,5,36,[[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0]],[.s 91 3,.s 91 3,.s 91 3,.s 91 3]⟩,
⟨0,3,6,41,[[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0]],[.s 96 1,.s 96 1,.s 96 1,.s 96 1]⟩,
⟨0,3,7,37,[[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 97 0,.s 97 0,.s 97 0,.s 97 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0]],[.s 93 2,.s 93 2,.s 93 2,.s 93 2]⟩,
⟨0,3,8,40,[[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 98 0,.s 98 0,.s 98 0,.s 98 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0]],[.s 98 2,.s 98 2,.s 98 2,.s 98 2]⟩,
⟨0,3,9,38,[[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0],[.s 98 0,.s 98 0,.s 98 0,.s 98 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0]],[.s 51 4,.s 51 4,.s 51 4,.s 51 4]⟩,
⟨0,3,10,39,[[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 97 0,.s 97 0,.s 97 0,.s 97 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0]],[.s 97 3,.s 97 3,.s 97 3,.s 97 3]⟩,
⟨0,4,0,44,[[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 100 0,.s 100 0,.s 100 0,.s 100 0],[.s 132 0,.s 132 0,.s 132 0,.s 132 0]],[.s 90 2,.s 90 2,.s 90 2,.s 90 2]⟩,
⟨0,4,1,45,[[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 99 0,.s 99 0,.s 99 0,.s 99 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 133 0,.s 133 0,.s 133 0,.s 133 0]],[.s 99 2,.s 99 2,.s 99 2,.s 99 2]⟩,
⟨0,4,2,54,[[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 134 0,.s 134 0,.s 134 0,.s 134 0]],[.s 103 2,.s 103 2,.s 103 2,.s 103 2]⟩,
⟨0,4,3,46,[[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 100 0,.s 100 0,.s 100 0,.s 100 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0]],[.s 100 2,.s 100 2,.s 100 2,.s 100 2]⟩,
⟨0,4,4,53,[[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 101 0,.s 101 0,.s 101 0,.s 101 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0]],[.s 61 3,.s 61 3,.s 61 3,.s 61 3]⟩,
⟨0,4,5,47,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0]],[.s 102 3,.s 102 3,.s 102 3,.s 102 3]⟩,
⟨0,4,6,52,[[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0]],[.s 107 1,.s 107 1,.s 107 1,.s 107 1]⟩,
⟨0,4,7,48,[[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0]],[.s 104 2,.s 104 2,.s 104 2,.s 104 2]⟩,
⟨0,4,8,51,[[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0]],[.s 109 2,.s 109 2,.s 109 2,.s 109 2]⟩,
⟨0,4,9,49,[[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0]],[.s 62 4,.s 62 4,.s 62 4,.s 62 4]⟩,
⟨0,4,10,50,[[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0],[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0]],[.s 108 3,.s 108 3,.s 108 3,.s 108 3]⟩,
⟨1,2,0,22,[[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.f ⟨24,2,0,0,0,0,0,0,0⟩,.f ⟨24,2,1,0,1,0,0,0,0⟩,.s 2 0,.s 2 0],[.s 111 0,.s 111 0,.s 111 0,.s 111 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0]],[.f ⟨24,2,0,0,0,0,0,0,2⟩,.f ⟨24,2,1,0,1,0,0,0,2⟩,.s 2 2,.s 2 2]⟩,
⟨1,2,1,23,[[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 110 0,.s 110 0,.s 110 0,.s 110 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 144 0,.s 144 0,.s 144 0,.s 144 0]],[.s 110 2,.s 110 2,.s 110 2,.s 110 2]⟩,
⟨1,2,2,32,[[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.s 145 0,.s 145 0,.s 145 0,.s 145 0]],[.s 114 2,.s 114 2,.s 114 2,.s 114 2]⟩,
⟨1,2,3,24,[[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 111 0,.s 111 0,.s 111 0,.s 111 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 146 0,.s 146 0,.s 146 0,.s 146 0]],[.s 111 2,.s 111 2,.s 111 2,.s 111 2]⟩,
⟨1,2,4,31,[[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 112 0,.s 112 0,.s 112 0,.s 112 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 147 0,.s 147 0,.s 147 0,.s 147 0]],[.s 83 3,.s 83 3,.s 83 3,.s 83 3]⟩,
⟨1,2,5,25,[[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 146 0,.s 146 0,.s 146 0,.s 146 0],[.s 148 0,.s 148 0,.s 148 0,.s 148 0]],[.s 113 3,.s 113 3,.s 113 3,.s 113 3]⟩,
⟨1,2,6,30,[[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 147 0,.s 147 0,.s 147 0,.s 147 0],[.s 149 0,.s 149 0,.s 149 0,.s 149 0]],[.s 118 1,.s 118 1,.s 118 1,.s 118 1]⟩,
⟨1,2,7,26,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0],[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0]],[.s 115 2,.s 115 2,.s 115 2,.s 115 2]⟩,
⟨1,2,8,29,[[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0]],[.s 120 2,.s 120 2,.s 120 2,.s 120 2]⟩,
⟨1,2,9,27,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0]],[.s 84 4,.s 84 4,.s 84 4,.s 84 4]⟩,
⟨1,2,10,28,[[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0]],[.s 119 3,.s 119 3,.s 119 3,.s 119 3]⟩,
⟨1,3,0,33,[[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 112 0,.s 112 0,.s 112 0,.s 112 0],[.s 122 0,.s 122 0,.s 122 0,.s 122 0],[.s 154 0,.s 154 0,.s 154 0,.s 154 0]],[.s 112 2,.s 112 2,.s 112 2,.s 112 2]⟩,
⟨1,3,1,34,[[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.s 155 0,.s 155 0,.s 155 0,.s 155 0]],[.s 121 2,.s 121 2,.s 121 2,.s 121 2]⟩,
⟨1,3,2,43,[[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.s 132 0,.s 132 0,.s 132 0,.s 132 0],[.s 156 0,.s 156 0,.s 156 0,.s 156 0]],[.s 125 2,.s 125 2,.s 125 2,.s 125 2]⟩,
⟨1,3,3,35,[[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 122 0,.s 122 0,.s 122 0,.s 122 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 157 0,.s 157 0,.s 157 0,.s 157 0]],[.s 122 2,.s 122 2,.s 122 2,.s 122 2]⟩,
⟨1,3,4,42,[[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 123 0,.s 123 0,.s 123 0,.s 123 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 158 0,.s 158 0,.s 158 0,.s 158 0]],[.s 94 3,.s 94 3,.s 94 3,.s 94 3]⟩,
⟨1,3,5,36,[[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 157 0,.s 157 0,.s 157 0,.s 157 0],[.s 159 0,.s 159 0,.s 159 0,.s 159 0]],[.s 124 3,.s 124 3,.s 124 3,.s 124 3]⟩,
⟨1,3,6,41,[[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 158 0,.s 158 0,.s 158 0,.s 158 0],[.s 160 0,.s 160 0,.s 160 0,.s 160 0]],[.s 129 1,.s 129 1,.s 129 1,.s 129 1]⟩,
⟨1,3,7,37,[[.s 95 0,.s 95 0,.s 95 0,.s 95 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.s 161 0,.s 161 0,.s 161 0,.s 161 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0]],[.s 126 2,.s 126 2,.s 126 2,.s 126 2]⟩,
⟨1,3,8,40,[[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0],[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0]],[.s 131 2,.s 131 2,.s 131 2,.s 131 2]⟩,
⟨1,3,9,38,[[.s 95 0,.s 95 0,.s 95 0,.s 95 0],[.s 97 0,.s 97 0,.s 97 0,.s 97 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0]],[.s 95 4,.s 95 4,.s 95 4,.s 95 4]⟩,
⟨1,3,10,39,[[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 98 0,.s 98 0,.s 98 0,.s 98 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0]],[.s 130 3,.s 130 3,.s 130 3,.s 130 3]⟩,
⟨1,4,0,44,[[.s 99 0,.s 99 0,.s 99 0,.s 99 0],[.s 123 0,.s 123 0,.s 123 0,.s 123 0],[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 123 2,.s 123 2,.s 123 2,.s 123 2]⟩,
⟨1,4,1,45,[[.s 100 0,.s 100 0,.s 100 0,.s 100 0],[.s 132 0,.s 132 0,.s 132 0,.s 132 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]],[.s 132 2,.s 132 2,.s 132 2,.s 132 2]⟩,
⟨1,4,2,54,[[.s 101 0,.s 101 0,.s 101 0,.s 101 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0]],[.s 136 2,.s 136 2,.s 136 2,.s 136 2]⟩,
⟨1,4,3,46,[[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 133 2,.s 133 2,.s 133 2,.s 133 2]⟩,
⟨1,4,4,53,[[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 134 0,.s 134 0,.s 134 0,.s 134 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]],[.s 105 3,.s 105 3,.s 105 3,.s 105 3]⟩,
⟨1,4,5,47,[[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 135 3,.s 135 3,.s 135 3,.s 135 3]⟩,
⟨1,4,6,52,[[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 140 1,.s 140 1,.s 140 1,.s 140 1]⟩,
⟨1,4,7,48,[[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 137 2,.s 137 2,.s 137 2,.s 137 2]⟩,
⟨1,4,8,51,[[.s 107 0,.s 107 0,.s 107 0,.s 107 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 142 2,.s 142 2,.s 142 2,.s 142 2]⟩,
⟨1,4,9,49,[[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 106 4,.s 106 4,.s 106 4,.s 106 4]⟩,
⟨1,4,10,50,[[.s 107 0,.s 107 0,.s 107 0,.s 107 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 141 3,.s 141 3,.s 141 3,.s 141 3]⟩,
⟨2,2,0,22,[[.s 110 0,.s 110 0,.s 110 0,.s 110 0],[.f ⟨6,2,0,0,0,0,0,0,0⟩,.f ⟨7,13,1,0,0,0,0,0,0⟩,.s 24 0,.s 24 0],[.s 144 0,.s 144 0,.s 144 0,.s 144 0],[.f ⟨24,11,0,0,0,0,0,0,0⟩,.f ⟨24,11,1,0,1,0,0,0,0⟩,.s 55 0,.s 55 0]],[.f ⟨6,2,0,0,0,0,0,0,2⟩,.f ⟨7,13,1,0,0,0,0,0,2⟩,.s 24 2,.s 24 2]⟩,
⟨2,2,1,23,[[.s 111 0,.s 111 0,.s 111 0,.s 111 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0],[.s 146 0,.s 146 0,.s 146 0,.s 146 0],[.f ⟨24,12,0,0,0,0,0,0,0⟩,.f ⟨24,12,1,0,1,0,0,0,0⟩,.s 56 0,.s 56 0]],[.s 143 2,.s 143 2,.s 143 2,.s 143 2]⟩,
⟨2,2,2,32,[[.s 112 0,.s 112 0,.s 112 0,.s 112 0],[.s 147 0,.s 147 0,.s 147 0,.s 147 0],[.s 154 0,.s 154 0,.s 154 0,.s 154 0],[.f ⟨24,13,0,0,0,0,0,0,0⟩,.f ⟨24,13,1,0,1,0,0,0,0⟩,.s 57 0,.s 57 0]],[.s 147 2,.s 147 2,.s 147 2,.s 147 2]⟩,
⟨2,2,3,24,[[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 144 0,.s 144 0,.s 144 0,.s 144 0],[.s 148 0,.s 148 0,.s 148 0,.s 148 0],[.f ⟨24,14,0,0,0,0,0,0,0⟩,.f ⟨24,14,1,0,1,0,0,0,0⟩,.s 58 0,.s 58 0]],[.s 144 2,.s 144 2,.s 144 2,.s 144 2]⟩,
⟨2,2,4,31,[[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 145 0,.s 145 0,.s 145 0,.s 145 0],[.s 149 0,.s 149 0,.s 149 0,.s 149 0],[.f ⟨24,15,0,0,0,0,0,0,0⟩,.f ⟨24,15,1,0,1,0,0,0,0⟩,.s 59 0,.s 59 0]],[.s 116 3,.s 116 3,.s 116 3,.s 116 3]⟩,
⟨2,2,5,25,[[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 146 0,.s 146 0,.s 146 0,.s 146 0],[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.f ⟨24,14,0,0,0,0,0,0,0⟩,.f ⟨24,14,1,0,1,0,0,0,0⟩,.s 58 0,.s 58 0],[.f ⟨24,16,0,0,0,0,0,0,0⟩,.f ⟨24,16,1,0,1,0,0,0,0⟩,.s 60 0,.s 60 0]],[.s 146 3,.s 146 3,.s 146 3,.s 146 3]⟩,
⟨2,2,6,30,[[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 147 0,.s 147 0,.s 147 0,.s 147 0],[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.f ⟨24,15,0,0,0,0,0,0,0⟩,.f ⟨24,15,1,0,1,0,0,0,0⟩,.s 59 0,.s 59 0],[.f ⟨24,17,0,0,0,0,0,0,0⟩,.f ⟨24,17,1,0,1,0,0,0,0⟩,.s 61 0,.s 61 0]],[.s 151 1,.s 151 1,.s 151 1,.s 151 1]⟩,
⟨2,2,7,26,[[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 148 0,.s 148 0,.s 148 0,.s 148 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0],[.f ⟨24,18,0,0,0,0,0,0,0⟩,.f ⟨24,18,1,0,1,0,0,0,0⟩,.s 62 0,.s 62 0],[.f ⟨24,20,0,0,0,0,0,0,0⟩,.f ⟨24,20,1,0,1,0,0,0,0⟩,.s 64 0,.s 64 0]],[.s 148 2,.s 148 2,.s 148 2,.s 148 2]⟩,
⟨2,2,8,29,[[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 149 0,.s 149 0,.s 149 0,.s 149 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0],[.f ⟨24,19,0,0,0,0,0,0,0⟩,.f ⟨24,19,1,0,1,0,0,0,0⟩,.s 63 0,.s 63 0],[.f ⟨24,21,0,0,0,0,0,0,0⟩,.f ⟨24,21,1,0,1,0,0,0,0⟩,.s 65 0,.s 65 0]],[.s 153 2,.s 153 2,.s 153 2,.s 153 2]⟩,
⟨2,2,9,27,[[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0],[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0],[.f ⟨24,20,0,0,0,0,0,0,0⟩,.f ⟨24,20,1,0,1,0,0,0,0⟩,.s 64 0,.s 64 0]],[.s 117 4,.s 117 4,.s 117 4,.s 117 4]⟩,
⟨2,2,10,28,[[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0],[.f ⟨24,21,0,0,0,0,0,0,0⟩,.f ⟨24,21,1,0,1,0,0,0,0⟩,.s 65 0,.s 65 0]],[.s 152 3,.s 152 3,.s 152 3,.s 152 3]⟩,
⟨2,3,0,33,[[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.s 145 0,.s 145 0,.s 145 0,.s 145 0],[.s 155 0,.s 155 0,.s 155 0,.s 155 0],[.s 165 0,.s 165 0,.s 165 0,.s 165 0]],[.s 145 2,.s 145 2,.s 145 2,.s 145 2]⟩,
⟨2,3,1,34,[[.s 122 0,.s 122 0,.s 122 0,.s 122 0],[.s 154 0,.s 154 0,.s 154 0,.s 154 0],[.s 157 0,.s 157 0,.s 157 0,.s 157 0],[.s 166 0,.s 166 0,.s 166 0,.s 166 0]],[.s 154 2,.s 154 2,.s 154 2,.s 154 2]⟩,
⟨2,3,2,43,[[.s 123 0,.s 123 0,.s 123 0,.s 123 0],[.s 158 0,.s 158 0,.s 158 0,.s 158 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 167 0,.s 167 0,.s 167 0,.s 167 0]],[.s 158 2,.s 158 2,.s 158 2,.s 158 2]⟩,
⟨2,3,3,35,[[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 155 0,.s 155 0,.s 155 0,.s 155 0],[.s 159 0,.s 159 0,.s 159 0,.s 159 0],[.s 168 0,.s 168 0,.s 168 0,.s 168 0]],[.s 155 2,.s 155 2,.s 155 2,.s 155 2]⟩,
⟨2,3,4,42,[[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 156 0,.s 156 0,.s 156 0,.s 156 0],[.s 160 0,.s 160 0,.s 160 0,.s 160 0],[.s 169 0,.s 169 0,.s 169 0,.s 169 0]],[.s 127 3,.s 127 3,.s 127 3,.s 127 3]⟩,
⟨2,3,5,36,[[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 157 0,.s 157 0,.s 157 0,.s 157 0],[.s 161 0,.s 161 0,.s 161 0,.s 161 0],[.s 168 0,.s 168 0,.s 168 0,.s 168 0],[.s 170 0,.s 170 0,.s 170 0,.s 170 0]],[.s 157 3,.s 157 3,.s 157 3,.s 157 3]⟩,
⟨2,3,6,41,[[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 158 0,.s 158 0,.s 158 0,.s 158 0],[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 169 0,.s 169 0,.s 169 0,.s 169 0],[.s 171 0,.s 171 0,.s 171 0,.s 171 0]],[.s 162 1,.s 162 1,.s 162 1,.s 162 1]⟩,
⟨2,3,7,37,[[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 159 0,.s 159 0,.s 159 0,.s 159 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0],[.s 172 0,.s 172 0,.s 172 0,.s 172 0],[.s 174 0,.s 174 0,.s 174 0,.s 174 0]],[.s 159 2,.s 159 2,.s 159 2,.s 159 2]⟩,
⟨2,3,8,40,[[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 160 0,.s 160 0,.s 160 0,.s 160 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0],[.s 173 0,.s 173 0,.s 173 0,.s 173 0],[.s 175 0,.s 175 0,.s 175 0,.s 175 0]],[.s 164 2,.s 164 2,.s 164 2,.s 164 2]⟩,
⟨2,3,9,38,[[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.s 161 0,.s 161 0,.s 161 0,.s 161 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0],[.s 174 0,.s 174 0,.s 174 0,.s 174 0]],[.s 128 4,.s 128 4,.s 128 4,.s 128 4]⟩,
⟨2,3,10,39,[[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0],[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0],[.s 175 0,.s 175 0,.s 175 0,.s 175 0]],[.s 163 3,.s 163 3,.s 163 3,.s 163 3]⟩,
⟨3,3,0,33,[[.s 154 0,.s 154 0,.s 154 0,.s 154 0],[.f ⟨24,13,0,0,0,0,0,0,0⟩,.f ⟨24,13,1,0,1,0,0,0,0⟩,.s 57 0,.s 57 0],[.s 166 0,.s 166 0,.s 166 0,.s 166 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0]],[.f ⟨24,13,0,0,0,0,0,0,2⟩,.f ⟨24,13,1,0,1,0,0,0,2⟩,.s 57 2,.s 57 2]⟩,
⟨3,3,1,34,[[.s 155 0,.s 155 0,.s 155 0,.s 155 0],[.s 165 0,.s 165 0,.s 165 0,.s 165 0],[.s 168 0,.s 168 0,.s 168 0,.s 168 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0]],[.s 165 2,.s 165 2,.s 165 2,.s 165 2]⟩,
⟨3,3,2,43,[[.s 156 0,.s 156 0,.s 156 0,.s 156 0],[.s 169 0,.s 169 0,.s 169 0,.s 169 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0]],[.s 169 2,.s 169 2,.s 169 2,.s 169 2]⟩,
⟨3,3,3,35,[[.s 157 0,.s 157 0,.s 157 0,.s 157 0],[.s 159 0,.s 159 0,.s 159 0,.s 159 0],[.s 166 0,.s 166 0,.s 166 0,.s 166 0],[.s 170 0,.s 170 0,.s 170 0,.s 170 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0]],[.s 166 2,.s 166 2,.s 166 2,.s 166 2]⟩,
⟨3,3,4,42,[[.s 158 0,.s 158 0,.s 158 0,.s 158 0],[.s 160 0,.s 160 0,.s 160 0,.s 160 0],[.s 167 0,.s 167 0,.s 167 0,.s 167 0],[.s 171 0,.s 171 0,.s 171 0,.s 171 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0]],[.s 160 3,.s 160 3,.s 160 3,.s 160 3]⟩,
⟨3,3,5,36,[[.s 159 0,.s 159 0,.s 159 0,.s 159 0],[.s 168 0,.s 168 0,.s 168 0,.s 168 0],[.s 172 0,.s 172 0,.s 172 0,.s 172 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 168 3,.s 168 3,.s 168 3,.s 168 3]⟩,
⟨3,3,6,41,[[.s 160 0,.s 160 0,.s 160 0,.s 160 0],[.s 169 0,.s 169 0,.s 169 0,.s 169 0],[.s 173 0,.s 173 0,.s 173 0,.s 173 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0]],[.s 173 1,.s 173 1,.s 173 1,.s 173 1]⟩,
⟨3,3,7,37,[[.s 161 0,.s 161 0,.s 161 0,.s 161 0],[.s 170 0,.s 170 0,.s 170 0,.s 170 0],[.s 174 0,.s 174 0,.s 174 0,.s 174 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0]],[.s 170 2,.s 170 2,.s 170 2,.s 170 2]⟩,
⟨3,3,8,40,[[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 171 0,.s 171 0,.s 171 0,.s 171 0],[.s 175 0,.s 175 0,.s 175 0,.s 175 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0]],[.s 175 2,.s 175 2,.s 175 2,.s 175 2]⟩,
⟨3,3,9,38,[[.s 161 0,.s 161 0,.s 161 0,.s 161 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0],[.s 172 0,.s 172 0,.s 172 0,.s 172 0],[.s 175 0,.s 175 0,.s 175 0,.s 175 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0]],[.s 161 4,.s 161 4,.s 161 4,.s 161 4]⟩,
⟨3,3,10,39,[[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0],[.s 173 0,.s 173 0,.s 173 0,.s 173 0],[.s 174 0,.s 174 0,.s 174 0,.s 174 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0]],[.s 174 3,.s 174 3,.s 174 3,.s 174 3]⟩]⟩,
⟨0,0,0,0,0,[(0,2,1),(-2,-4,1),(0,-2,-2),(2,4,-2)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨-3,1,0,12,[[.f ⟨29,11,0,0,0,0,0,0,0⟩],[.f ⟨11,13,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨8,0,0,0,0,0,0,0,0⟩]],[.f ⟨11,13,0,0,0,0,0,0,2⟩]⟩,
⟨-3,1,1,13,[[.f ⟨29,12,0,0,0,0,0,0,0⟩],[.s 0 0],[.s 3 0],[.f ⟨8,1,0,0,0,0,0,0,0⟩]],[.s 0 2]⟩,
⟨-3,1,2,21,[[.f ⟨29,13,0,0,0,0,0,0,0⟩],[.s 4 0],[.f ⟨25,0,0,0,0,0,0,0,0⟩],[.f ⟨8,2,0,0,0,0,0,0,0⟩]],[.s 4 2]⟩,
⟨-3,1,3,14,[[.f ⟨29,14,0,0,0,0,0,0,0⟩],[.f ⟨29,16,0,0,0,0,0,0,0⟩],[.s 1 0],[.s 5 0],[.f ⟨8,3,0,0,0,0,0,0,0⟩]],[.s 1 2]⟩,
⟨-3,1,4,20,[[.f ⟨29,15,0,0,0,0,0,0,0⟩],[.f ⟨29,17,0,0,0,0,0,0,0⟩],[.s 2 0],[.s 6 0],[.f ⟨8,4,0,0,0,0,0,0,0⟩]],[.f ⟨29,17,0,0,0,0,0,0,3⟩]⟩,
⟨-3,1,5,14,[[.f ⟨29,16,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 7 0],[.f ⟨8,3,0,0,0,0,0,0,0⟩],[.f ⟨8,5,0,0,0,0,0,0,0⟩]],[.f ⟨8,3,0,0,0,0,0,0,1⟩]⟩,
⟨-3,1,6,19,[[.f ⟨29,17,0,0,0,0,0,0,0⟩],[.s 4 0],[.s 8 0],[.f ⟨8,4,0,0,0,0,0,0,0⟩],[.f ⟨8,6,0,0,0,0,0,0,0⟩]],[.s 8 1]⟩,
⟨-3,1,7,15,[[.f ⟨29,18,0,0,0,0,0,0,0⟩],[.s 5 0],[.s 9 0],[.f ⟨8,7,0,0,0,0,0,0,0⟩],[.f ⟨8,9,0,0,0,0,0,0,0⟩]],[.s 5 2]⟩,
⟨-3,1,8,18,[[.f ⟨29,19,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 10 0],[.f ⟨8,8,0,0,0,0,0,0,0⟩],[.f ⟨8,10,0,0,0,0,0,0,0⟩]],[.s 10 2]⟩,
⟨-3,1,9,16,[[.f ⟨29,18,0,0,0,0,0,0,0⟩],[.f ⟨29,20,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 10 0],[.f ⟨8,9,0,0,0,0,0,0,0⟩]],[.s 7 2]⟩,
⟨-3,1,10,17,[[.f ⟨29,19,0,0,0,0,0,0,0⟩],[.f ⟨29,21,0,0,0,0,0,0,0⟩],[.s 8 0],[.s 9 0],[.f ⟨8,10,0,0,0,0,0,0,0⟩]],[.s 9 3]⟩]⟩,
⟨1,-4,2,0,0,[(0,2,3),(-2,-4,1),(2,4,-2)],0,2,3,4,0,0,0,0,22,0,0,0,
[⟨-7,3,0,34,[[.f ⟨30,11,0,0,0,0,0,0,0⟩,.f ⟨30,11,1,0,1,0,0,0,0⟩],[.f ⟨30,24,0,0,0,0,0,0,0⟩,.f ⟨30,24,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨9,0,0,0,0,0,0,0,0⟩,.f ⟨9,0,1,0,1,0,0,0,0⟩]],[.f ⟨30,24,0,0,0,0,0,0,2⟩,.f ⟨30,24,1,0,1,0,0,0,2⟩]⟩,
⟨-7,3,1,35,[[.f ⟨30,12,0,0,0,0,0,0,0⟩,.f ⟨30,12,1,0,1,0,0,0,0⟩],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.f ⟨9,1,0,0,0,0,0,0,0⟩,.f ⟨9,1,1,0,1,0,0,0,0⟩]],[.s 0 2,.s 0 2]⟩,
⟨-7,3,2,43,[[.f ⟨30,13,0,0,0,0,0,0,0⟩,.f ⟨30,13,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.f ⟨25,0,0,0,1,0,0,0,0⟩,.f ⟨25,0,1,0,2,0,0,0,0⟩],[.f ⟨9,2,0,0,0,0,0,0,0⟩,.f ⟨9,2,1,0,1,0,0,0,0⟩]],[.s 4 2,.s 4 2]⟩,
⟨-7,3,3,36,[[.f ⟨30,14,0,0,0,0,0,0,0⟩,.f ⟨30,14,1,0,1,0,0,0,0⟩],[.f ⟨30,16,0,0,0,0,0,0,0⟩,.f ⟨30,16,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.f ⟨9,3,0,0,0,0,0,0,0⟩,.f ⟨9,3,1,0,1,0,0,0,0⟩]],[.s 1 2,.s 1 2]⟩,
⟨-7,3,4,42,[[.f ⟨30,15,0,0,0,0,0,0,0⟩,.f ⟨30,15,1,0,1,0,0,0,0⟩],[.f ⟨30,17,0,0,0,0,0,0,0⟩,.f ⟨30,17,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.f ⟨9,4,0,0,0,0,0,0,0⟩,.f ⟨9,4,1,0,1,0,0,0,0⟩]],[.f ⟨30,17,0,0,0,0,0,0,3⟩,.f ⟨30,17,1,0,1,0,0,0,3⟩]⟩,
⟨-7,3,5,36,[[.f ⟨30,16,0,0,0,0,0,0,0⟩,.f ⟨30,16,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.f ⟨9,3,0,0,0,0,0,0,0⟩,.f ⟨9,3,1,0,1,0,0,0,0⟩],[.f ⟨9,5,0,0,0,0,0,0,0⟩,.f ⟨9,5,1,0,1,0,0,0,0⟩]],[.f ⟨9,3,0,0,0,0,0,0,1⟩,.f ⟨9,3,1,0,1,0,0,0,1⟩]⟩,
⟨-7,3,6,41,[[.f ⟨30,17,0,0,0,0,0,0,0⟩,.f ⟨30,17,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.f ⟨9,4,0,0,0,0,0,0,0⟩,.f ⟨9,4,1,0,1,0,0,0,0⟩],[.f ⟨9,6,0,0,0,0,0,0,0⟩,.f ⟨9,6,1,0,1,0,0,0,0⟩]],[.s 8 1,.s 8 1]⟩,
⟨-7,3,7,37,[[.f ⟨30,18,0,0,0,0,0,0,0⟩,.f ⟨30,18,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.f ⟨9,7,0,0,0,0,0,0,0⟩,.f ⟨9,7,1,0,1,0,0,0,0⟩],[.f ⟨9,9,0,0,0,0,0,0,0⟩,.f ⟨9,9,1,0,1,0,0,0,0⟩]],[.s 5 2,.s 5 2]⟩,
⟨-7,3,8,40,[[.f ⟨30,19,0,0,0,0,0,0,0⟩,.f ⟨30,19,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.f ⟨9,8,0,0,0,0,0,0,0⟩,.f ⟨9,8,1,0,1,0,0,0,0⟩],[.f ⟨9,10,0,0,0,0,0,0,0⟩,.f ⟨9,10,1,0,1,0,0,0,0⟩]],[.s 10 2,.s 10 2]⟩,
⟨-7,3,9,38,[[.f ⟨30,18,0,0,0,0,0,0,0⟩,.f ⟨30,18,1,0,1,0,0,0,0⟩],[.f ⟨30,20,0,0,0,0,0,0,0⟩,.f ⟨30,20,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.f ⟨9,9,0,0,0,0,0,0,0⟩,.f ⟨9,9,1,0,1,0,0,0,0⟩]],[.s 7 2,.s 7 2]⟩,
⟨-7,3,10,39,[[.f ⟨30,19,0,0,0,0,0,0,0⟩,.f ⟨30,19,1,0,1,0,0,0,0⟩],[.f ⟨30,21,0,0,0,0,0,0,0⟩,.f ⟨30,21,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.f ⟨9,10,0,0,0,0,0,0,0⟩,.f ⟨9,10,1,0,1,0,0,0,0⟩]],[.s 9 3,.s 9 3]⟩,
⟨-5,2,0,23,[[.f ⟨30,33,0,0,0,0,0,0,0⟩,.f ⟨30,33,1,0,1,0,0,0,0⟩],[.f ⟨29,2,0,0,0,0,0,0,0⟩,.f ⟨30,2,1,0,0,0,0,0,0⟩],[.s 12 0,.s 12 0],[.f ⟨9,11,0,0,0,0,0,0,0⟩,.f ⟨9,11,1,0,1,0,0,0,0⟩]],[.f ⟨29,2,0,0,0,0,0,0,2⟩,.f ⟨30,2,1,0,0,0,0,0,2⟩]⟩,
⟨-5,2,1,24,[[.f ⟨30,34,0,0,0,0,0,0,0⟩,.f ⟨30,34,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨9,12,0,0,0,0,0,0,0⟩,.f ⟨9,12,1,0,1,0,0,0,0⟩]],[.s 11 2,.s 11 2]⟩,
⟨-5,2,2,32,[[.f ⟨30,35,0,0,0,0,0,0,0⟩,.f ⟨30,35,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨25,11,0,0,1,0,0,0,0⟩,.f ⟨25,11,1,0,2,0,0,0,0⟩],[.f ⟨9,13,0,0,0,0,0,0,0⟩,.f ⟨9,13,1,0,1,0,0,0,0⟩]],[.s 15 2,.s 15 2]⟩,
⟨-5,2,3,25,[[.f ⟨30,36,0,0,0,0,0,0,0⟩,.f ⟨30,36,1,0,1,0,0,0,0⟩],[.f ⟨30,38,0,0,0,0,0,0,0⟩,.f ⟨30,38,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨9,14,0,0,0,0,0,0,0⟩,.f ⟨9,14,1,0,1,0,0,0,0⟩]],[.s 12 2,.s 12 2]⟩,
⟨-5,2,4,31,[[.f ⟨30,37,0,0,0,0,0,0,0⟩,.f ⟨30,37,1,0,1,0,0,0,0⟩],[.f ⟨30,39,0,0,0,0,0,0,0⟩,.f ⟨30,39,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨9,15,0,0,0,0,0,0,0⟩,.f ⟨9,15,1,0,1,0,0,0,0⟩]],[.f ⟨30,39,0,0,0,0,0,0,3⟩,.f ⟨30,39,1,0,1,0,0,0,3⟩]⟩,
⟨-5,2,5,25,[[.f ⟨30,38,0,0,0,0,0,0,0⟩,.f ⟨30,38,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨9,14,0,0,0,0,0,0,0⟩,.f ⟨9,14,1,0,1,0,0,0,0⟩],[.f ⟨9,16,0,0,0,0,0,0,0⟩,.f ⟨9,16,1,0,1,0,0,0,0⟩]],[.f ⟨9,14,0,0,0,0,0,0,1⟩,.f ⟨9,14,1,0,1,0,0,0,1⟩]⟩,
⟨-5,2,6,30,[[.f ⟨30,39,0,0,0,0,0,0,0⟩,.f ⟨30,39,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨9,15,0,0,0,0,0,0,0⟩,.f ⟨9,15,1,0,1,0,0,0,0⟩],[.f ⟨9,17,0,0,0,0,0,0,0⟩,.f ⟨9,17,1,0,1,0,0,0,0⟩]],[.s 19 1,.s 19 1]⟩,
⟨-5,2,7,26,[[.f ⟨30,40,0,0,0,0,0,0,0⟩,.f ⟨30,40,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨9,18,0,0,0,0,0,0,0⟩,.f ⟨9,18,1,0,1,0,0,0,0⟩],[.f ⟨9,20,0,0,0,0,0,0,0⟩,.f ⟨9,20,1,0,1,0,0,0,0⟩]],[.s 16 2,.s 16 2]⟩,
⟨-5,2,8,29,[[.f ⟨30,41,0,0,0,0,0,0,0⟩,.f ⟨30,41,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨9,19,0,0,0,0,0,0,0⟩,.f ⟨9,19,1,0,1,0,0,0,0⟩],[.f ⟨9,21,0,0,0,0,0,0,0⟩,.f ⟨9,21,1,0,1,0,0,0,0⟩]],[.s 21 2,.s 21 2]⟩,
⟨-5,2,9,27,[[.f ⟨30,40,0,0,0,0,0,0,0⟩,.f ⟨30,40,1,0,1,0,0,0,0⟩],[.f ⟨30,42,0,0,0,0,0,0,0⟩,.f ⟨30,42,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨9,20,0,0,0,0,0,0,0⟩,.f ⟨9,20,1,0,1,0,0,0,0⟩]],[.s 18 2,.s 18 2]⟩,
⟨-5,2,10,28,[[.f ⟨30,41,0,0,0,0,0,0,0⟩,.f ⟨30,41,1,0,1,0,0,0,0⟩],[.f ⟨30,43,0,0,0,0,0,0,0⟩,.f ⟨30,43,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨9,21,0,0,0,0,0,0,0⟩,.f ⟨9,21,1,0,1,0,0,0,0⟩]],[.s 20 3,.s 20 3]⟩]⟩,
⟨1,-2,0,0,0,[(-2,-4,3),(0,2,1),(0,-2,-2)],-2,-4,3,4,0,0,0,0,2,0,0,0,
[⟨-5,1,0,14,[[.s 11 0,.s 11 0],[.f ⟨11,13,0,0,1,0,0,0,0⟩,.f ⟨11,13,1,0,2,0,0,0,0⟩],[.s 1 0,.s 1 0],[.s 11 0,.s 11 0]],[.f ⟨11,13,0,0,1,0,0,0,2⟩,.f ⟨11,13,1,0,2,0,0,0,2⟩]⟩,
⟨-5,1,1,15,[[.s 12 0,.s 12 0],[.s 0 0,.s 0 0],[.s 3 0,.s 3 0],[.s 12 0,.s 12 0]],[.s 0 2,.s 0 2]⟩,
⟨-5,1,2,22,[[.s 13 0,.s 13 0],[.s 4 0,.s 4 0],[.f ⟨28,11,0,0,0,0,0,0,0⟩,.f ⟨30,22,0,0,0,1,0,0,0⟩],[.s 13 0,.s 13 0]],[.s 4 2,.s 4 2]⟩,
⟨-5,1,3,16,[[.s 14 0,.s 14 0],[.s 16 0,.s 16 0],[.s 1 0,.s 1 0],[.s 5 0,.s 5 0],[.s 14 0,.s 14 0]],[.s 1 2,.s 1 2]⟩,
⟨-5,1,4,21,[[.s 15 0,.s 15 0],[.s 17 0,.s 17 0],[.s 2 0,.s 2 0],[.s 6 0,.s 6 0],[.s 15 0,.s 15 0]],[.s 6 1,.s 6 1]⟩,
⟨-5,1,5,16,[[.s 16 0,.s 16 0],[.s 3 0,.s 3 0],[.s 7 0,.s 7 0],[.s 14 0,.s 14 0],[.s 16 0,.s 16 0]],[.s 14 1,.s 14 1]⟩,
⟨-5,1,6,20,[[.s 17 0,.s 17 0],[.s 4 0,.s 4 0],[.s 8 0,.s 8 0],[.s 15 0,.s 15 0],[.s 17 0,.s 17 0]],[.s 8 1,.s 8 1]⟩,
⟨-5,1,7,17,[[.s 18 0,.s 18 0],[.s 5 0,.s 5 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 20 0,.s 20 0]],[.s 5 2,.s 5 2]⟩,
⟨-5,1,8,19,[[.s 19 0,.s 19 0],[.s 6 0,.s 6 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 21 0,.s 21 0]],[.s 19 0,.s 19 0]⟩,
⟨-5,1,9,18,[[.s 18 0,.s 18 0],[.s 20 0,.s 20 0],[.s 7 0,.s 7 0],[.s 10 0,.s 10 0],[.s 20 0,.s 20 0]],[.s 7 2,.s 7 2]⟩,
⟨-5,1,10,19,[[.s 19 0,.s 19 0],[.s 21 0,.s 21 0],[.s 8 0,.s 8 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.s 9 3,.s 9 3]⟩,
⟨-4,1,0,13,[[.s 0 0,.s 0 0],[.f ⟨11,2,0,0,0,0,0,0,0⟩,.f ⟨11,2,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.f ⟨27,0,0,0,0,0,0,0,0⟩,.s 0 0]],[.f ⟨11,2,0,0,0,0,0,0,2⟩,.f ⟨11,2,1,0,1,0,0,0,2⟩]⟩,
⟨-4,1,1,14,[[.s 1 0,.s 1 0],[.s 11 0,.s 11 0],[.s 14 0,.s 14 0],[.f ⟨27,1,0,0,0,0,0,0,0⟩,.s 1 0]],[.s 11 2,.s 11 2]⟩,
⟨-4,1,2,21,[[.s 2 0,.s 2 0],[.s 15 0,.s 15 0],[.f ⟨9,11,0,0,0,0,0,0,0⟩,.f ⟨30,33,0,0,0,1,0,0,0⟩],[.f ⟨27,2,0,0,0,0,0,0,0⟩,.s 2 0]],[.s 15 2,.s 15 2]⟩,
⟨-4,1,3,15,[[.s 3 0,.s 3 0],[.s 5 0,.s 5 0],[.s 12 0,.s 12 0],[.s 16 0,.s 16 0],[.f ⟨27,3,0,0,0,0,0,0,0⟩,.s 3 0]],[.s 12 2,.s 12 2]⟩,
⟨-4,1,4,20,[[.s 4 0,.s 4 0],[.s 6 0,.s 6 0],[.s 13 0,.s 13 0],[.s 17 0,.s 17 0],[.f ⟨27,4,0,0,0,0,0,0,0⟩,.s 4 0]],[.s 17 1,.s 17 1]⟩,
⟨-4,1,5,15,[[.s 5 0,.s 5 0],[.s 14 0,.s 14 0],[.s 18 0,.s 18 0],[.f ⟨27,3,0,0,0,0,0,0,0⟩,.s 3 0],[.f ⟨27,5,0,0,0,0,0,0,0⟩,.s 5 0]],[.f ⟨27,3,0,0,0,0,0,0,1⟩,.s 3 1]⟩,
⟨-4,1,6,19,[[.s 6 0,.s 6 0],[.s 15 0,.s 15 0],[.s 19 0,.s 19 0],[.f ⟨27,4,0,0,0,0,0,0,0⟩,.s 4 0],[.f ⟨27,6,0,0,0,0,0,0,0⟩,.s 6 0]],[.s 19 1,.s 19 1]⟩,
⟨-4,1,7,16,[[.s 7 0,.s 7 0],[.s 16 0,.s 16 0],[.s 20 0,.s 20 0],[.f ⟨27,7,0,0,0,0,0,0,0⟩,.s 7 0],[.f ⟨27,9,0,0,0,0,0,0,0⟩,.s 9 0]],[.s 16 2,.s 16 2]⟩,
⟨-4,1,8,18,[[.s 8 0,.s 8 0],[.s 17 0,.s 17 0],[.s 21 0,.s 21 0],[.f ⟨27,8,0,0,0,0,0,0,0⟩,.s 8 0],[.f ⟨27,10,0,0,0,0,0,0,0⟩,.s 10 0]],[.f ⟨27,10,0,0,0,0,0,0,0⟩,.s 8 0]⟩,
⟨-4,1,9,17,[[.s 7 0,.s 7 0],[.s 9 0,.s 9 0],[.s 18 0,.s 18 0],[.s 21 0,.s 21 0],[.f ⟨27,9,0,0,0,0,0,0,0⟩,.s 9 0]],[.s 18 2,.s 18 2]⟩,
⟨-4,1,10,18,[[.s 8 0,.s 8 0],[.s 10 0,.s 10 0],[.s 19 0,.s 19 0],[.s 20 0,.s 20 0],[.f ⟨27,10,0,0,0,0,0,0,0⟩,.s 10 0]],[.s 20 3,.s 20 3]⟩]⟩,
⟨2,-4,2,-2,0,[(0,2,3),(-2,-4,3)],0,2,3,4,-2,-4,3,4,22,2,1,11,
[⟨-9,3,0,36,[[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 24 2,.s 24 2,.s 24 2,.s 24 2]⟩,
⟨-9,3,1,37,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]],[.s 0 2,.s 0 2,.s 0 2,.s 0 2]⟩,
⟨-9,3,2,44,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨28,11,0,0,1,0,0,0,0⟩,.f ⟨28,11,1,0,2,0,0,0,0⟩,.s 22 0,.s 22 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0]],[.s 4 2,.s 4 2,.s 4 2,.s 4 2]⟩,
⟨-9,3,3,38,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 1 2,.s 1 2,.s 1 2,.s 1 2]⟩,
⟨-9,3,4,43,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]],[.s 6 1,.s 6 1,.s 6 1,.s 6 1]⟩,
⟨-9,3,5,38,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 14 1,.s 14 1,.s 14 1,.s 14 1]⟩,
⟨-9,3,6,42,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 8 1,.s 8 1,.s 8 1,.s 8 1]⟩,
⟨-9,3,7,39,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 5 2,.s 5 2,.s 5 2,.s 5 2]⟩,
⟨-9,3,8,41,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 19 0,.s 19 0,.s 19 0,.s 19 0]⟩,
⟨-9,3,9,40,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 7 2,.s 7 2,.s 7 2,.s 7 2]⟩,
⟨-9,3,10,41,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 9 3,.s 9 3,.s 9 3,.s 9 3]⟩,
⟨-8,3,0,35,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.f ⟨28,0,0,0,0,0,0,0,0⟩,.f ⟨28,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0]],[.s 35 2,.s 35 2,.s 35 2,.s 35 2]⟩,
⟨-8,3,1,36,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.f ⟨28,1,0,0,0,0,0,0,0⟩,.f ⟨28,1,1,0,1,0,0,0,0⟩,.s 1 0,.s 1 0]],[.s 11 2,.s 11 2,.s 11 2,.s 11 2]⟩,
⟨-8,3,2,43,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.f ⟨9,11,0,0,1,0,0,0,0⟩,.f ⟨9,11,1,0,2,0,0,0,0⟩,.s 33 0,.s 33 0],[.f ⟨28,2,0,0,0,0,0,0,0⟩,.f ⟨28,2,1,0,1,0,0,0,0⟩,.s 2 0,.s 2 0]],[.s 15 2,.s 15 2,.s 15 2,.s 15 2]⟩,
⟨-8,3,3,37,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨28,3,0,0,0,0,0,0,0⟩,.f ⟨28,3,1,0,1,0,0,0,0⟩,.s 3 0,.s 3 0]],[.s 12 2,.s 12 2,.s 12 2,.s 12 2]⟩,
⟨-8,3,4,42,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨28,4,0,0,0,0,0,0,0⟩,.f ⟨28,4,1,0,1,0,0,0,0⟩,.s 4 0,.s 4 0]],[.s 17 1,.s 17 1,.s 17 1,.s 17 1]⟩,
⟨-8,3,5,37,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.f ⟨28,3,0,0,0,0,0,0,0⟩,.f ⟨28,3,1,0,1,0,0,0,0⟩,.s 3 0,.s 3 0],[.f ⟨28,5,0,0,0,0,0,0,0⟩,.f ⟨28,5,1,0,1,0,0,0,0⟩,.s 5 0,.s 5 0]],[.f ⟨28,3,0,0,0,0,0,0,1⟩,.f ⟨28,3,1,0,1,0,0,0,1⟩,.s 3 1,.s 3 1]⟩,
⟨-8,3,6,41,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.f ⟨28,4,0,0,0,0,0,0,0⟩,.f ⟨28,4,1,0,1,0,0,0,0⟩,.s 4 0,.s 4 0],[.f ⟨28,6,0,0,0,0,0,0,0⟩,.f ⟨28,6,1,0,1,0,0,0,0⟩,.s 6 0,.s 6 0]],[.s 19 1,.s 19 1,.s 19 1,.s 19 1]⟩,
⟨-8,3,7,38,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨28,7,0,0,0,0,0,0,0⟩,.f ⟨28,7,1,0,1,0,0,0,0⟩,.s 7 0,.s 7 0],[.f ⟨28,9,0,0,0,0,0,0,0⟩,.f ⟨28,9,1,0,1,0,0,0,0⟩,.s 9 0,.s 9 0]],[.s 16 2,.s 16 2,.s 16 2,.s 16 2]⟩,
⟨-8,3,8,40,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.f ⟨28,8,0,0,0,0,0,0,0⟩,.f ⟨28,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0],[.f ⟨28,10,0,0,0,0,0,0,0⟩,.f ⟨28,10,1,0,1,0,0,0,0⟩,.s 10 0,.s 10 0]],[.f ⟨28,10,0,0,0,0,0,0,0⟩,.f ⟨28,10,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0]⟩,
⟨-8,3,9,39,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.f ⟨28,9,0,0,0,0,0,0,0⟩,.f ⟨28,9,1,0,1,0,0,0,0⟩,.s 9 0,.s 9 0]],[.s 18 2,.s 18 2,.s 18 2,.s 18 2]⟩,
⟨-8,3,10,40,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨28,10,0,0,0,0,0,0,0⟩,.f ⟨28,10,1,0,1,0,0,0,0⟩,.s 10 0,.s 10 0]],[.s 20 3,.s 20 3,.s 20 3,.s 20 3]⟩,
⟨-7,2,0,25,[[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.f ⟨29,2,0,0,1,0,0,0,0⟩,.s 2 0,.f ⟨29,2,0,1,2,0,0,0,0⟩,.s 2 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.f ⟨29,2,0,0,1,0,0,0,2⟩,.s 2 2,.f ⟨29,2,0,1,2,0,0,0,2⟩,.s 2 2]⟩,
⟨-7,2,1,26,[[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.s 22 2,.s 22 2,.s 22 2,.s 22 2]⟩,
⟨-7,2,2,33,[[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.f ⟨28,0,0,0,0,0,0,0,0⟩,.f ⟨28,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 26 2,.s 26 2,.s 26 2,.s 26 2]⟩,
⟨-7,2,3,27,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0]],[.s 23 2,.s 23 2,.s 23 2,.s 23 2]⟩,
⟨-7,2,4,32,[[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0]],[.s 28 1,.s 28 1,.s 28 1,.s 28 1]⟩,
⟨-7,2,5,27,[[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.s 36 1,.s 36 1,.s 36 1,.s 36 1]⟩,
⟨-7,2,6,31,[[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0]],[.s 30 1,.s 30 1,.s 30 1,.s 30 1]⟩,
⟨-7,2,7,28,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.s 27 2,.s 27 2,.s 27 2,.s 27 2]⟩,
⟨-7,2,8,30,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 41 0,.s 41 0,.s 41 0,.s 41 0]⟩,
⟨-7,2,9,29,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.s 29 2,.s 29 2,.s 29 2,.s 29 2]⟩,
⟨-7,2,10,30,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 31 3,.s 31 3,.s 31 3,.s 31 3]⟩,
⟨-6,2,0,24,[[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.f ⟨29,13,0,0,1,0,0,0,0⟩,.s 13 0,.f ⟨29,13,0,1,2,0,0,0,0⟩,.s 13 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.f ⟨28,11,0,0,0,0,0,0,0⟩,.f ⟨28,11,1,0,1,0,0,0,0⟩,.s 22 0,.s 22 0]],[.f ⟨29,13,0,0,1,0,0,0,2⟩,.s 13 2,.f ⟨29,13,0,1,2,0,0,0,2⟩,.s 13 2]⟩,
⟨-6,2,1,25,[[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.f ⟨28,12,0,0,0,0,0,0,0⟩,.f ⟨28,12,1,0,1,0,0,0,0⟩,.s 23 0,.s 23 0]],[.s 33 2,.s 33 2,.s 33 2,.s 33 2]⟩,
⟨-6,2,2,32,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.f ⟨9,0,0,0,0,0,0,0,0⟩,.f ⟨9,0,1,0,1,0,0,0,0⟩,.s 11 0,.s 11 0],[.f ⟨28,13,0,0,0,0,0,0,0⟩,.f ⟨28,13,1,0,1,0,0,0,0⟩,.s 24 0,.s 24 0]],[.s 37 2,.s 37 2,.s 37 2,.s 37 2]⟩,
⟨-6,2,3,26,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.f ⟨28,14,0,0,0,0,0,0,0⟩,.f ⟨28,14,1,0,1,0,0,0,0⟩,.s 25 0,.s 25 0]],[.s 34 2,.s 34 2,.s 34 2,.s 34 2]⟩,
⟨-6,2,4,31,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.f ⟨28,15,0,0,0,0,0,0,0⟩,.f ⟨28,15,1,0,1,0,0,0,0⟩,.s 26 0,.s 26 0]],[.s 39 1,.s 39 1,.s 39 1,.s 39 1]⟩,
⟨-6,2,5,26,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.f ⟨28,14,0,0,0,0,0,0,0⟩,.f ⟨28,14,1,0,1,0,0,0,0⟩,.s 25 0,.s 25 0],[.f ⟨28,16,0,0,0,0,0,0,0⟩,.f ⟨28,16,1,0,1,0,0,0,0⟩,.s 27 0,.s 27 0]],[.f ⟨28,14,0,0,0,0,0,0,1⟩,.f ⟨28,14,1,0,1,0,0,0,1⟩,.s 25 1,.s 25 1]⟩,
⟨-6,2,6,30,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.f ⟨28,15,0,0,0,0,0,0,0⟩,.f ⟨28,15,1,0,1,0,0,0,0⟩,.s 26 0,.s 26 0],[.f ⟨28,17,0,0,0,0,0,0,0⟩,.f ⟨28,17,1,0,1,0,0,0,0⟩,.s 28 0,.s 28 0]],[.s 41 1,.s 41 1,.s 41 1,.s 41 1]⟩,
⟨-6,2,7,27,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.f ⟨28,18,0,0,0,0,0,0,0⟩,.f ⟨28,18,1,0,1,0,0,0,0⟩,.s 29 0,.s 29 0],[.f ⟨28,20,0,0,0,0,0,0,0⟩,.f ⟨28,20,1,0,1,0,0,0,0⟩,.s 31 0,.s 31 0]],[.s 38 2,.s 38 2,.s 38 2,.s 38 2]⟩,
⟨-6,2,8,29,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.f ⟨28,19,0,0,0,0,0,0,0⟩,.f ⟨28,19,1,0,1,0,0,0,0⟩,.s 30 0,.s 30 0],[.f ⟨28,21,0,0,0,0,0,0,0⟩,.f ⟨28,21,1,0,1,0,0,0,0⟩,.s 32 0,.s 32 0]],[.f ⟨28,21,0,0,0,0,0,0,0⟩,.f ⟨28,21,1,0,1,0,0,0,0⟩,.s 30 0,.s 30 0]⟩,
⟨-6,2,9,28,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.f ⟨28,20,0,0,0,0,0,0,0⟩,.f ⟨28,20,1,0,1,0,0,0,0⟩,.s 31 0,.s 31 0]],[.s 40 2,.s 40 2,.s 40 2,.s 40 2]⟩,
⟨-6,2,10,29,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.f ⟨28,21,0,0,0,0,0,0,0⟩,.f ⟨28,21,1,0,1,0,0,0,0⟩,.s 32 0,.s 32 0]],[.s 42 3,.s 42 3,.s 42 3,.s 42 3]⟩]⟩,
⟨2,-2,0,-2,-1,[(-1,2,1),(0,-2,1)],-1,2,1,2,0,-2,1,2,2,11,11,2,
[⟨-4,-1,0,13,[[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.f ⟨1,2,0,0,1,0,0,0,0⟩,.s 2 0,.f ⟨1,2,0,1,2,0,0,0,0⟩,.s 2 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 1 1,.s 1 1,.s 1 1,.s 1 1]⟩,
⟨-4,-1,1,12,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]],[.s 3 2,.s 3 2,.s 3 2,.s 3 2]⟩,
⟨-4,-1,2,5,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.f ⟨11,0,0,0,0,0,0,0,0⟩,.f ⟨11,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0]],[.f ⟨11,0,0,0,0,0,0,0,1⟩,.f ⟨11,0,1,0,1,0,0,0,1⟩,.s 0 1,.s 0 1]⟩,
⟨-4,-1,3,11,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 5 1,.s 5 1,.s 5 1,.s 5 1]⟩,
⟨-4,-1,4,6,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]],[.s 2 1,.s 2 1,.s 2 1,.s 2 1]⟩,
⟨-4,-1,5,10,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 7 1,.s 7 1,.s 7 1,.s 7 1]⟩,
⟨-4,-1,6,6,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 15 1,.s 15 1,.s 15 1,.s 15 1]⟩,
⟨-4,-1,7,9,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 18 0,.s 18 0,.s 18 0,.s 18 0]⟩,
⟨-4,-1,8,7,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 6 2,.s 6 2,.s 6 2,.s 6 2]⟩,
⟨-4,-1,9,9,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 10 3,.s 10 3,.s 10 3,.s 10 3]⟩,
⟨-4,-1,10,8,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 8 2,.s 8 2,.s 8 2,.s 8 2]⟩,
⟨-3,-1,0,12,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨13,2,0,0,0,0,0,0,0⟩,.s 13 0,.f ⟨13,2,0,1,1,0,0,0,0⟩,.s 13 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.f ⟨1,0,0,0,0,0,0,0,0⟩,.s 0 0,.f ⟨1,0,0,1,1,0,0,0,0⟩,.s 0 0]],[.s 12 1,.s 12 1,.s 12 1,.s 12 1]⟩,
⟨-3,-1,1,11,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.f ⟨1,1,0,0,0,0,0,0,0⟩,.s 1 0,.f ⟨1,1,0,1,1,0,0,0,0⟩,.s 1 0]],[.s 14 2,.s 14 2,.s 14 2,.s 14 2]⟩,
⟨-3,-1,2,4,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.f ⟨11,11,0,0,0,0,0,0,0⟩,.f ⟨11,11,1,0,1,0,0,0,0⟩,.s 11 0,.s 11 0],[.f ⟨1,2,0,0,0,0,0,0,0⟩,.s 2 0,.f ⟨1,2,0,1,1,0,0,0,0⟩,.s 2 0]],[.f ⟨11,11,0,0,0,0,0,0,1⟩,.f ⟨11,11,1,0,1,0,0,0,1⟩,.s 11 1,.s 11 1]⟩,
⟨-3,-1,3,10,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨1,3,0,0,0,0,0,0,0⟩,.s 3 0,.f ⟨1,3,0,1,1,0,0,0,0⟩,.s 3 0]],[.s 16 1,.s 16 1,.s 16 1,.s 16 1]⟩,
⟨-3,-1,4,5,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨1,4,0,0,0,0,0,0,0⟩,.s 4 0,.f ⟨1,4,0,1,1,0,0,0,0⟩,.s 4 0]],[.s 13 1,.s 13 1,.s 13 1,.s 13 1]⟩,
⟨-3,-1,5,9,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.f ⟨1,3,0,0,0,0,0,0,0⟩,.s 3 0,.f ⟨1,3,0,1,1,0,0,0,0⟩,.s 3 0],[.f ⟨1,5,0,0,0,0,0,0,0⟩,.s 5 0,.f ⟨1,5,0,1,1,0,0,0,0⟩,.s 5 0]],[.s 18 1,.s 18 1,.s 18 1,.s 18 1]⟩,
⟨-3,-1,6,5,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.f ⟨1,4,0,0,0,0,0,0,0⟩,.s 4 0,.f ⟨1,4,0,1,1,0,0,0,0⟩,.s 4 0],[.f ⟨1,6,0,0,0,0,0,0,0⟩,.s 6 0,.f ⟨1,6,0,1,1,0,0,0,0⟩,.s 6 0]],[.f ⟨1,4,0,0,0,0,0,0,1⟩,.s 4 1,.f ⟨1,4,0,1,1,0,0,0,1⟩,.s 4 1]⟩,
⟨-3,-1,7,8,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨1,7,0,0,0,0,0,0,0⟩,.s 7 0,.f ⟨1,7,0,1,1,0,0,0,0⟩,.s 7 0],[.f ⟨1,9,0,0,0,0,0,0,0⟩,.s 9 0,.f ⟨1,9,0,1,1,0,0,0,0⟩,.s 9 0]],[.f ⟨1,7,0,0,0,0,0,0,0⟩,.s 7 0,.f ⟨1,7,0,1,1,0,0,0,0⟩,.s 7 0]⟩,
⟨-3,-1,8,6,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.f ⟨1,8,0,0,0,0,0,0,0⟩,.s 8 0,.f ⟨1,8,0,1,1,0,0,0,0⟩,.s 8 0],[.f ⟨1,10,0,0,0,0,0,0,0⟩,.s 10 0,.f ⟨1,10,0,1,1,0,0,0,0⟩,.s 10 0]],[.s 17 2,.s 17 2,.s 17 2,.s 17 2]⟩,
⟨-3,-1,9,8,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.f ⟨1,9,0,0,0,0,0,0,0⟩,.s 9 0,.f ⟨1,9,0,1,1,0,0,0,0⟩,.s 9 0]],[.s 21 3,.s 21 3,.s 21 3,.s 21 3]⟩,
⟨-3,-1,10,7,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨1,10,0,0,0,0,0,0,0⟩,.s 10 0,.f ⟨1,10,0,1,1,0,0,0,0⟩,.s 10 0]],[.s 19 2,.s 19 2,.s 19 2,.s 19 2]⟩]⟩]

set_option maxRecDepth 100000 in
def certsData : List (List (List (Bool × ℕ × ℕ))) := [
[[],[(false,0,2),(false,2,1),(true,2,1)],[(false,1,2),(false,2,1),(true,2,1)],[(false,1,2),(false,2,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,1,2),(false,3,1),(true,2,1)],[(false,1,2),(false,3,1),(true,2,1)],[(false,0,2),(false,3,1),(true,2,1)],[(false,0,2),(false,3,1),(true,2,1)],[(false,0,1),(true,2,1)],[(false,0,1),(true,2,1)],[(false,0,2),(false,2,4),(true,0,1)],[(false,0,2),(false,2,4),(true,0,1)],[(false,0,2),(false,2,4),(true,1,1)],[(false,0,2),(false,2,4),(true,0,1)],[(false,2,2),(true,0,1)],[(false,2,2),(true,0,1)],[(false,2,2),(true,1,1)],[(false,2,2),(true,0,1)],[(false,3,2),(true,1,1)],[(false,3,2),(true,1,1)],[(false,3,2),(true,0,1)],[(false,3,2),(true,1,1)],[(false,0,2),(false,3,4),(true,1,1)],[(false,0,2),(false,3,4),(true,0,1)],[(false,0,2),(false,3,4),(true,1,1)],[(false,3,2),(true,0,1)],[(false,3,2),(true,0,1)],[(false,3,2),(true,1,1)],[(false,3,2),(true,0,1)],[(false,2,2),(true,1,1)]],
[[(false,0,2),(false,2,1),(true,2,5)],[],[(false,0,3),(false,2,4),(true,0,5)],[(false,0,3),(false,2,4),(true,0,5)],[(false,0,2),(false,2,1),(true,0,5)],[(false,0,2),(false,2,1),(true,0,5)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,3),(false,2,4),(true,1,5)],[(false,0,3),(false,2,4),(true,1,5)],[(false,0,2),(false,2,1),(true,1,5)],[(false,0,2),(false,2,1),(true,1,5)],[(false,1,1),(true,1,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,6),(false,2,8),(true,1,5)],[(false,0,6),(false,2,8),(true,1,5)],[(false,0,6),(false,2,8),(true,0,5)],[(false,0,6),(false,2,8),(true,1,5)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,4),(false,2,2),(true,0,5)],[(false,0,4),(false,2,2),(true,0,5)],[(false,0,4),(false,2,2),(true,1,5)],[(false,0,4),(false,2,2),(true,0,5)],[(false,0,1),(true,0,1)]],
[[(false,0,1),(false,2,2),(true,1,5)],[(false,0,4),(false,2,3),(true,2,5)],[],[(false,3,1),(true,2,1)],[(false,1,2),(false,2,1),(true,0,5)],[(false,1,2),(false,2,1),(true,0,5)],[(false,1,3),(false,2,4),(true,0,5)],[(false,1,3),(false,2,4),(true,0,5)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,2),(true,2,5)],[(false,0,1),(false,2,2),(true,2,5)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,4),(false,2,2),(true,1,5)],[(false,1,4),(false,2,2),(true,1,5)],[(false,1,4),(false,2,2),(true,0,5)],[(false,1,4),(false,2,2),(true,1,5)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,1),(true,0,1),(true,1,2)]],
[[(false,0,1),(false,2,2),(true,1,5)],[(false,0,4),(false,2,3),(true,2,5)],[(false,2,1),(true,3,1)],[],[(false,0,1),(false,2,2),(true,3,5)],[(false,1,2),(false,2,1),(true,0,5)],[(false,0,4),(false,2,3),(true,3,5)],[(false,1,3),(false,2,4),(true,0,5)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,2),(true,2,5)],[(false,0,1),(false,2,2),(true,2,5)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,4),(false,2,2),(true,1,5)],[(false,1,4),(false,2,2),(true,1,5)],[(false,1,4),(false,2,2),(true,0,5)],[(false,1,4),(false,2,2),(true,1,5)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,1),(true,0,1),(true,1,2)]],
[[(false,2,1),(true,1,1)],[(false,0,1),(false,2,2),(true,2,1)],[(false,0,2),(false,2,1),(true,1,1)],[(false,0,2),(false,2,1),(true,1,1)],[],[(false,3,1),(true,2,1)],[(false,1,2),(false,2,1),(true,0,1)],[(false,1,2),(false,2,1),(true,0,1)],[(false,0,2),(false,2,1),(true,0,1)],[(false,0,2),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,4),(false,2,2),(true,1,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,4),(false,2,2),(true,1,1)],[(false,1,4),(false,2,2),(true,0,1)],[(false,1,4),(false,2,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)]],
[[(false,2,1),(true,1,1)],[(false,0,1),(false,2,2),(true,2,1)],[(false,0,2),(false,2,1),(true,1,1)],[(false,0,2),(false,2,1),(true,1,1)],[(false,2,1),(true,3,1)],[],[(false,0,1),(false,2,2),(true,3,1)],[(false,1,2),(false,2,1),(true,0,1)],[(false,0,2),(false,2,1),(true,0,1)],[(false,0,2),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,4),(false,2,2),(true,1,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,4),(false,2,2),(true,1,1)],[(false,0,4),(false,2,2),(true,2,1)],[(false,1,4),(false,2,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)]],
[[(false,0,2),(false,2,1),(true,3,5)],[(false,2,1),(true,2,1)],[(false,0,3),(false,2,4),(true,1,5)],[(false,0,3),(false,2,4),(true,1,5)],[(false,0,2),(false,2,1),(true,1,5)],[(false,0,2),(false,2,1),(true,1,5)],[],[(false,3,1),(true,2,1)],[(false,0,3),(false,2,4),(true,0,5)],[(false,0,3),(false,2,4),(true,0,5)],[(false,0,2),(false,2,1),(true,0,5)],[(false,0,2),(false,2,1),(true,0,5)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,4),(false,2,2),(true,0,5)],[(false,0,4),(false,2,2),(true,0,5)],[(false,0,4),(false,2,2),(true,1,5)],[(false,0,4),(false,2,2),(true,0,5)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,0,6),(false,2,8),(true,1,5)],[(false,0,6),(false,2,8),(true,1,5)],[(false,0,6),(false,2,8),(true,0,5)],[(false,0,6),(false,2,8),(true,1,5)],[(false,1,1),(true,0,1)]],
[[(false,0,2),(false,2,1),(true,3,5)],[(false,2,1),(true,2,1)],[(false,0,3),(false,2,4),(true,1,5)],[(false,0,3),(false,2,4),(true,1,5)],[(false,0,2),(false,2,1),(true,1,5)],[(false,0,2),(false,2,1),(true,1,5)],[(false,2,1),(true,3,1)],[],[(false,0,3),(false,2,4),(true,0,5)],[(false,0,3),(false,2,4),(true,0,5)],[(false,0,2),(false,2,1),(true,0,5)],[(false,0,2),(false,2,1),(true,0,5)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,4),(false,2,2),(true,0,5)],[(false,0,4),(false,2,2),(true,0,5)],[(false,0,4),(false,2,2),(true,1,5)],[(false,0,4),(false,2,2),(true,0,5)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,0,6),(false,2,8),(true,1,5)],[(false,0,6),(false,2,8),(true,1,5)],[(false,0,6),(false,2,8),(true,0,5)],[(false,0,6),(false,2,8),(true,1,5)],[(false,1,1),(true,0,1)]],
[[(false,0,1),(false,2,2),(true,0,5)],[(false,1,3),(false,2,4),(true,0,5)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,2),(true,2,5)],[(false,0,1),(false,2,2),(true,2,5)],[(false,0,4),(false,2,3),(true,2,5)],[(false,0,4),(false,2,3),(true,2,5)],[],[(false,3,1),(true,2,1)],[(false,1,2),(false,2,1),(true,0,5)],[(false,1,2),(false,2,1),(true,0,5)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,4),(false,3,2),(true,0,5)],[(false,0,4),(false,3,2),(true,1,5)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,4),(false,2,2),(true,1,5)]],
[[(false,0,1),(false,2,2),(true,0,5)],[(false,1,3),(false,2,4),(true,0,5)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,2),(true,2,5)],[(false,0,1),(false,2,2),(true,2,5)],[(false,0,4),(false,2,3),(true,2,5)],[(false,0,4),(false,2,3),(true,2,5)],[(false,2,1),(true,3,1)],[],[(false,0,1),(false,2,2),(true,3,5)],[(false,1,2),(false,2,1),(true,0,5)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,2),(true,0,4),(true,1,1)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,4),(false,2,2),(true,1,5)]],
[[(false,2,1),(true,0,1)],[(false,1,2),(false,2,1),(true,0,1)],[(false,0,2),(false,2,1),(true,0,1)],[(false,0,2),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,2),(true,2,1)],[(false,0,1),(false,2,2),(true,2,1)],[(false,0,2),(false,2,1),(true,1,1)],[(false,0,2),(false,2,1),(true,1,1)],[],[(false,3,1),(true,2,1)],[(false,1,2),(false,2,1),(true,1,1)],[(false,1,2),(false,2,1),(true,1,1)],[(false,1,2),(false,2,1),(true,0,1)],[(false,1,2),(false,2,1),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,4),(false,2,2),(true,1,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)]],
[[(false,2,1),(true,0,1)],[(false,1,2),(false,2,1),(true,0,1)],[(false,0,2),(false,2,1),(true,0,1)],[(false,0,2),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,2),(true,2,1)],[(false,0,1),(false,2,2),(true,2,1)],[(false,0,2),(false,2,1),(true,1,1)],[(false,0,2),(false,2,1),(true,1,1)],[(false,2,1),(true,3,1)],[],[(false,1,2),(false,2,1),(true,1,1)],[(false,1,2),(false,2,1),(true,1,1)],[(false,1,2),(false,2,1),(true,0,1)],[(false,1,2),(false,2,1),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,4),(false,2,2),(true,1,1)],[(false,0,4),(false,2,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)]],
[[(false,0,1),(false,1,2),(true,2,8)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,2),(true,0,8)],[(false,0,1),(false,1,2),(true,0,8)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,2),(true,1,8)],[(false,0,1),(false,1,2),(true,1,8)],[],[(false,2,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,3,2),(true,0,1)],[(false,0,1),(false,1,2),(true,0,4)],[(false,3,2),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(false,1,2),(true,0,4)],[(false,0,1),(false,1,2),(true,0,4)],[(false,0,1),(false,1,2),(true,1,4)],[(false,0,1),(false,1,2),(true,0,4)],[(false,1,1),(true,0,1)]],
[[(false,0,1),(false,1,2),(true,2,8)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,2),(true,0,8)],[(false,0,1),(false,1,2),(true,0,8)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,2),(true,1,8)],[(false,0,1),(false,1,2),(true,1,8)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,2,2),(true,0,1)],[(false,0,1),(false,1,2),(true,0,4)],[(false,2,2),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,0,1),(false,1,2),(true,0,4)],[(false,1,1),(true,0,1)]],
[[(false,0,2),(false,1,1),(true,2,8)],[(false,0,1),(true,1,1)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,2),(false,1,1),(true,0,8)],[(false,0,2),(false,1,1),(true,0,8)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,2),(false,1,1),(true,1,8)],[(false,0,2),(false,1,1),(true,1,8)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,2),(true,2,1)],[(false,0,2),(false,1,1),(true,1,4)],[(false,0,2),(true,2,1)],[(false,0,2),(false,1,1),(true,1,4)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(false,1,1),(true,0,4)],[(false,0,2),(false,1,1),(true,0,4)],[(false,0,2),(false,1,1),(true,1,4)],[(false,0,2),(false,1,1),(true,0,4)],[(false,0,1),(true,0,1)]],
[[(false,0,1),(false,1,2),(true,2,8)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,2),(true,0,8)],[(false,0,1),(false,1,2),(true,0,8)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,2),(true,1,8)],[(false,0,1),(false,1,2),(true,1,8)],[(false,0,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,1,2),(true,2,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,1,2),(true,2,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,0,1),(false,1,2),(true,0,4)],[(false,1,1),(true,0,1)]],
[[(false,0,1),(true,2,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[],[(false,2,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,3,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)]],
[[(false,0,1),(true,2,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,2,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)]],
[[(false,1,1),(true,2,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,4),(true,0,2)]],
[[(false,0,1),(true,2,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,1,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)]],
[[(false,1,1),(true,3,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(false,1,4),(true,0,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,2,1),(true,0,2)],[(false,2,1),(true,1,2)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[],[(false,2,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,3,1),(true,0,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,3,1),(true,0,1)],[(false,0,1),(true,0,2)]],
[[(false,1,1),(true,3,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,3,2)],[(false,0,1),(true,2,2)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,2,1),(true,0,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,0,2)]],
[[(false,0,1),(true,3,2)],[(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,2,1),(true,0,2)],[(false,2,1),(true,1,2)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,1),(true,1,1)]],
[[(false,1,1),(true,3,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,3,2)],[(false,0,1),(true,2,2)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,1,1),(true,2,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,1,1),(true,2,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(true,0,2)]],
[[(false,0,1),(false,1,1),(true,3,8)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,1),(true,1,8)],[(false,0,1),(false,1,1),(true,1,8)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,1),(true,0,8)],[(false,0,1),(false,1,1),(true,0,8)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,1),(true,1,4)],[(false,0,1),(false,1,1),(true,0,4)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,4)]],
[[(false,0,1),(false,1,1),(true,3,8)],[(false,0,1),(true,0,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(false,1,1),(true,1,8)],[(false,0,1),(false,1,1),(true,1,8)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(false,1,1),(true,0,8)],[(false,0,1),(false,1,1),(true,0,8)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,1),(true,0,4)],[(false,0,1),(false,1,1),(true,0,4)],[(false,2,1),(true,0,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,4)]],
[[(false,0,1),(false,1,1),(true,3,8)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,1),(true,1,8)],[(false,0,1),(false,1,1),(true,1,8)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,1),(true,0,8)],[(false,0,1),(false,1,1),(true,0,8)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,1),(true,1,4)],[(false,0,1),(false,1,1),(true,0,4)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,4)]],
[[(false,0,1),(true,3,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,3,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)],[(false,3,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,2,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[],[(false,2,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,1,1)]],
[[(false,0,1),(true,3,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,2,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)],[(false,2,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)]],
[[(false,1,1),(true,3,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,2,1),(true,0,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)]],
[[(false,0,1),(true,3,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)]],
[[(false,1,1),(true,2,2)],[(false,0,1),(true,0,1)],[(false,0,1),(false,1,2),(true,0,1)],[(false,0,1),(false,1,2),(true,0,1)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,1)],[(false,0,1),(false,1,2),(true,1,1)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,2),(false,1,4),(true,1,1)],[(false,0,2),(false,1,4),(true,1,1)],[(false,0,2),(false,1,4),(true,0,1)],[(false,0,2),(false,1,4),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(false,1,4),(true,0,1)],[(false,0,2),(false,1,4),(true,1,1)],[(false,0,2),(false,1,4),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[]]]

def cfg : GalCert.Cfg 11 := ⟨adj, (0, 0, 0), 22, regsData, certsData, 0, 0⟩

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
theorem hr13 : cfg.regOk 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr14 : cfg.regOk 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr15 : cfg.regOk 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr16 : cfg.regOk 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr17 : cfg.regOk 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr18 : cfg.regOk 18 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr19 : cfg.regOk 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr20 : cfg.regOk 20 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr21 : cfg.regOk 21 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr22 : cfg.regOk 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr23 : cfg.regOk 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr24 : cfg.regOk 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr25 : cfg.regOk 25 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr26 : cfg.regOk 26 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr27 : cfg.regOk 27 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr28 : cfg.regOk 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr29 : cfg.regOk 29 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr30 : cfg.regOk 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hr31 : cfg.regOk 31 = true := by decide +kernel

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq13 : cfg.certRow 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq14 : cfg.certRow 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq15 : cfg.certRow 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq16 : cfg.certRow 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq17 : cfg.certRow 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq18 : cfg.certRow 18 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq19 : cfg.certRow 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq20 : cfg.certRow 20 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq21 : cfg.certRow 21 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq22 : cfg.certRow 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq23 : cfg.certRow 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq24 : cfg.certRow 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq25 : cfg.certRow 25 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq26 : cfg.certRow 26 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq27 : cfg.certRow 27 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq28 : cfg.certRow 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq29 : cfg.certRow 29 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq30 : cfg.certRow 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hq31 : cfg.certRow 31 = true := by decide +kernel

theorem hc : cfg.check = true := by
  have e : cfg.regs.length = 32 := by decide +kernel
  refine GalCert.Cfg.check_of_parts cfg hh (fun r hr => ?_) (fun r hr => ?_) <;> rw [e] at hr <;> interval_cases r
  exacts [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22, hr23, hr24, hr25, hr26, hr27, hr28, hr29, hr30, hr31, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, hq19, hq20, hq21, hq22, hq23, hq24, hq25, hq26, hq27, hq28, hq29, hq30, hq31]

set_option maxHeartbeats 0 in
theorem hV : cfg.vbound 64 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

set_option maxRecDepth 100000 in
def Avals : List ℕ := [1,4,8,14,18,24,28,34,38,44,48,52,56,60,66,70,76,80,86,90,96,100,104,108,112,118,122,128,132,138,142,148,152,156,160,164,170,174,180,184,190,194,200,204,208,212,216,222,226,232,236,242,246,252,256,260,264,268,274,278,284,288,294,298,304,308,312,316,320,326,330,336,340,346,350,356,360,364,368,372,378,382,388,392,398,402,408,412,416,420,424,430,434,440,444,450,454,460,464,468,472,476,482,486,492,496,502,506,512,516,520,524,528,534,538,544,548,554,558,564,568,572]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA0 : (List.range' 0 4).map cfg.Af = [1,4,8,14] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA1 : (List.range' 4 4).map cfg.Af = [18,24,28,34] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA2 : (List.range' 8 4).map cfg.Af = [38,44,48,52] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA3 : (List.range' 12 4).map cfg.Af = [56,60,66,70] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA4 : (List.range' 16 4).map cfg.Af = [76,80,86,90] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA5 : (List.range' 20 4).map cfg.Af = [96,100,104,108] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA6 : (List.range' 24 4).map cfg.Af = [112,118,122,128] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA7 : (List.range' 28 4).map cfg.Af = [132,138,142,148] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA8 : (List.range' 32 4).map cfg.Af = [152,156,160,164] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA9 : (List.range' 36 4).map cfg.Af = [170,174,180,184] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA10 : (List.range' 40 4).map cfg.Af = [190,194,200,204] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA11 : (List.range' 44 4).map cfg.Af = [208,212,216,222] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA12 : (List.range' 48 4).map cfg.Af = [226,232,236,242] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA13 : (List.range' 52 4).map cfg.Af = [246,252,256,260] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA14 : (List.range' 56 4).map cfg.Af = [264,268,274,278] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA15 : (List.range' 60 4).map cfg.Af = [284,288,294,298] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA16 : (List.range' 64 4).map cfg.Af = [304,308,312,316] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA17 : (List.range' 68 4).map cfg.Af = [320,326,330,336] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA18 : (List.range' 72 4).map cfg.Af = [340,346,350,356] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA19 : (List.range' 76 4).map cfg.Af = [360,364,368,372] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA20 : (List.range' 80 4).map cfg.Af = [378,382,388,392] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA21 : (List.range' 84 4).map cfg.Af = [398,402,408,412] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA22 : (List.range' 88 4).map cfg.Af = [416,420,424,430] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA23 : (List.range' 92 4).map cfg.Af = [434,440,444,450] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA24 : (List.range' 96 4).map cfg.Af = [454,460,464,468] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA25 : (List.range' 100 4).map cfg.Af = [472,476,482,486] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA26 : (List.range' 104 4).map cfg.Af = [492,496,502,506] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA27 : (List.range' 108 4).map cfg.Af = [512,516,520,524] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA28 : (List.range' 112 4).map cfg.Af = [528,534,538,544] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA29 : (List.range' 116 4).map cfg.Af = [548,554,558,564] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA30 : (List.range' 120 2).map cfg.Af = [568,572] := by decide +kernel

set_option maxRecDepth 100000 in
theorem hAv : (List.range 122).map cfg.Af = Avals := by
  rw [List.range_eq_range']
  exact GalCert.Cfg.rmap_app cfg.Af 0 4 118 hA0 (GalCert.Cfg.rmap_app cfg.Af 4 4 114 hA1 (GalCert.Cfg.rmap_app cfg.Af 8 4 110 hA2 (GalCert.Cfg.rmap_app cfg.Af 12 4 106 hA3 (GalCert.Cfg.rmap_app cfg.Af 16 4 102 hA4 (GalCert.Cfg.rmap_app cfg.Af 20 4 98 hA5 (GalCert.Cfg.rmap_app cfg.Af 24 4 94 hA6 (GalCert.Cfg.rmap_app cfg.Af 28 4 90 hA7 (GalCert.Cfg.rmap_app cfg.Af 32 4 86 hA8 (GalCert.Cfg.rmap_app cfg.Af 36 4 82 hA9 (GalCert.Cfg.rmap_app cfg.Af 40 4 78 hA10 (GalCert.Cfg.rmap_app cfg.Af 44 4 74 hA11 (GalCert.Cfg.rmap_app cfg.Af 48 4 70 hA12 (GalCert.Cfg.rmap_app cfg.Af 52 4 66 hA13 (GalCert.Cfg.rmap_app cfg.Af 56 4 62 hA14 (GalCert.Cfg.rmap_app cfg.Af 60 4 58 hA15 (GalCert.Cfg.rmap_app cfg.Af 64 4 54 hA16 (GalCert.Cfg.rmap_app cfg.Af 68 4 50 hA17 (GalCert.Cfg.rmap_app cfg.Af 72 4 46 hA18 (GalCert.Cfg.rmap_app cfg.Af 76 4 42 hA19 (GalCert.Cfg.rmap_app cfg.Af 80 4 38 hA20 (GalCert.Cfg.rmap_app cfg.Af 84 4 34 hA21 (GalCert.Cfg.rmap_app cfg.Af 88 4 30 hA22 (GalCert.Cfg.rmap_app cfg.Af 92 4 26 hA23 (GalCert.Cfg.rmap_app cfg.Af 96 4 22 hA24 (GalCert.Cfg.rmap_app cfg.Af 100 4 18 hA25 (GalCert.Cfg.rmap_app cfg.Af 104 4 14 hA26 (GalCert.Cfg.rmap_app cfg.Af 108 4 10 hA27 (GalCert.Cfg.rmap_app cfg.Af 112 4 6 hA28 (GalCert.Cfg.rmap_app cfg.Af 116 4 2 hA29 (hA30))))))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
theorem hrec : ∀ k, (([(1, 13), (-1, 12), (-1, 2), (1, 1)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide)
    (GalCert.Cfg.window_of_list hAv _ _ (by decide +kernel) (by decide +kernel))

set_option maxHeartbeats 0 in
theorem hgfw : ∀ n < 64 + 2 * cfg.L, ((GalCert.csOf [1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1] 13).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.window_of_list hAv _ _ (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
theorem hsmall : ∀ n < 13, GalCert.conv a [1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1] n = ([1, 3, 4, 6, 4, 6, 4, 6, 4, 6, 4, 3, 1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else if n < 122 then (Avals.getD n 0 : ℤ) else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · have h0 : n ≠ 0 := by omega
      rw [if_neg h0]
      split_ifs with h2
      · rw [ha n h, GalCert.Cfg.A_of_list hAv h2]
      · exact ha n h
  rw [e]
  decide +kernel

end P312556

open PowerSeries OMA.S_oeis_a312556 in
theorem OMA.solution : type_of% @OMA.S_oeis_a312556.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
    have h := P312556.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 13 - 1 = k + 12 by omega,
      show k + 13 - 11 = k + 2 by omega,
      show k + 13 - 12 = k + 1 by omega,
      P312556.ha (k + 13) (by omega),
      P312556.ha (k + 12) (by omega),
      P312556.ha (k + 2) (by omega),
      P312556.ha (k + 1) (by omega)]
    linarith
  · have hD : (X^12 - X^11 - X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (X^12 + 3*X^11 + 4*X^10 + 6*X^9 + 4*X^8 + 6*X^7 + 4*X^6 + 6*X^5 + 4*X^4 + 6*X^3 + 4*X^2 + 3*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 3, 4, 6, 4, 6, 4, 6, 4, 6, 4, 3, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from P312556.hc P312556.hV a P312556.ha _ _ 13 (by decide) (by decide) P312556.hgfw P312556.hsmall
