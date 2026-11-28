import OMAStatements.S_oeis_a313698
import Mathlib

/-!
Proof of the conjectured generating function and recurrence for A313698.

Method: an explicit distance certificate for the periodic graph G of the statement. Every vertex
outside the origin cell lies on one of the rays through the vertices of the growth polygon or in
one of the cones between them (split into a finite corner, two boundary strips and an interior),
and is written as base + k T + j U with a base from a finite list. The certificate gives the
distance of each code as v + lT k + lU j. A Boolean checker, evaluated by the kernel, verifies that
every neighbour of a coded vertex has a code of value at most one more, that every coded vertex
other than the base vertex has a neighbour of value exactly one less, and that codes are
injective. So the ball of radius n is the image of the codes of value at most n, and the number
of vertices at distance n is a sum of explicit quasi-linear counts, which satisfies both
conjectures. The bridge to SimpleGraph.dist: walks in G are exactly walks along the listed
neighbour offsets (both orientations of the edge list E), and G is connected because explicit
paths join the base vertex to its two lattice translates and to a vertex of every class.
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


namespace SGBridge

variable {m : ℕ}

/-- The edge relation of a periodic graph given by one cell's directed edges. -/
def Rel (E : List (Fin m × Fin m × ℤ × ℤ)) (u v : ℤ × ℤ × Fin m) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- Both orientations of the edges leaving class `i`, as neighbour offsets. -/
def adjE (E : List (Fin m × Fin m × ℤ × ℤ)) (i : Fin m) : List (ℤ × ℤ × Fin m) :=
  (E.filter (fun e => decide (e.1 = i))).map (fun e => (e.2.2.1, e.2.2.2, e.2.1)) ++
    (E.filter (fun e => decide (e.2.1 = i))).map (fun e => (-e.2.2.1, -e.2.2.2, e.1))

/-- The literal table `adj` has the same entries as `adjE E`. -/
def adjOk (E : List (Fin m × Fin m × ℤ × ℤ)) (adj : Fin m → List (ℤ × ℤ × Fin m)) : Bool :=
  (List.finRange m).all fun i =>
    (adj i).all (fun d => decide (d ∈ adjE E i)) && (adjE E i).all (fun d => decide (d ∈ adj i))

theorem mem_adj {E : List (Fin m × Fin m × ℤ × ℤ)} {adj : Fin m → List (ℤ × ℤ × Fin m)}
    (h : adjOk E adj = true) (i : Fin m) (d : ℤ × ℤ × Fin m) : d ∈ adj i ↔ d ∈ adjE E i := by
  simp only [adjOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h i (List.mem_finRange i)
  exact ⟨h1 d, h2 d⟩

theorem rel_iff (E : List (Fin m × Fin m × ℤ × ℤ)) (u v : ℤ × ℤ × Fin m) :
    (Rel E u v ∨ Rel E v u) ↔ ∃ d ∈ adjE E u.2.2, v = (u.1 + d.1, u.2.1 + d.2.1, d.2.2) := by
  obtain ⟨ux, uy, ui⟩ := u
  obtain ⟨vx, vy, vi⟩ := v
  simp only [Rel, adjE, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨⟨a, b, dx, dy⟩, he, h1, h2, h3, h4⟩ | ⟨⟨a, b, dx, dy⟩, he, h1, h2, h3, h4⟩)
    · simp only at h1 h2 h3 h4
      subst h1 h2 h3 h4
      exact ⟨_, Or.inl ⟨_, ⟨he, rfl⟩, rfl⟩, rfl⟩
    · simp only at h1 h2 h3 h4
      subst h1 h2
      refine ⟨_, Or.inr ⟨_, ⟨he, rfl⟩, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq, and_true]
      constructor <;> omega
  · rintro ⟨d, (⟨⟨a, b, dx, dy⟩, ⟨he, h1⟩, rfl⟩ | ⟨⟨a, b, dx, dy⟩, ⟨he, h1⟩, rfl⟩), hv⟩
    · simp only at h1
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inl ⟨_, he, h1.symm, rfl, rfl, rfl⟩
    · simp only at h1
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      refine Or.inr ⟨_, he, rfl, h1.symm, ?_, ?_⟩ <;> simp only <;> omega

variable [NeZero m] {E : List (Fin m × Fin m × ℤ × ℤ)} {adj : Fin m → List (ℤ × ℤ × Fin m)}

theorem adj_iff (h : adjOk E adj = true) (u v : ℤ × ℤ × Fin m) :
    (SimpleGraph.fromRel (Rel E)).Adj u v ↔ u ≠ v ∧ v ∈ GalCert.nbrs adj u := by
  rw [SimpleGraph.fromRel_adj, rel_iff]
  simp only [GalCert.nbrs, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨hne, d, hd, rfl⟩
    exact ⟨hne, d, (mem_adj h _ d).mpr hd, rfl⟩
  · rintro ⟨hne, d, hd, rfl⟩
    exact ⟨hne, d, (mem_adj h _ d).mp hd, rfl⟩

theorem mem_ball_zero (x0 : ℤ × ℤ × Fin m) : ∀ n, x0 ∈ GalCert.ball adj x0 n
  | 0 => by simp [GalCert.ball]
  | n + 1 => by
    simp only [GalCert.ball, Finset.mem_union]
    exact Or.inl (mem_ball_zero x0 n)

theorem mem_ball_iff (h : adjOk E adj = true) (x0 : ℤ × ℤ × Fin m) :
    ∀ (n : ℕ) (v : ℤ × ℤ × Fin m), v ∈ GalCert.ball adj x0 n ↔
      ∃ p : (SimpleGraph.fromRel (Rel E)).Walk v x0, p.length ≤ n
  | 0, v => by
    simp only [GalCert.ball, Finset.mem_singleton, Nat.le_zero]
    constructor
    · rintro rfl
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
    · rintro ⟨p, hp⟩
      exact SimpleGraph.Walk.eq_of_length_eq_zero hp
  | n + 1, v => by
    simp only [GalCert.ball, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro (hv | ⟨u, hu, hv⟩)
      · obtain ⟨p, hp⟩ := (mem_ball_iff h x0 n v).mp hv
        exact ⟨p, by omega⟩
      · obtain ⟨p, hp⟩ := (mem_ball_iff h x0 n u).mp hu
        by_cases hvu : v = u
        · subst hvu
          exact ⟨p, by omega⟩
        · have hadj : (SimpleGraph.fromRel (Rel E)).Adj u v := (adj_iff h u v).mpr ⟨Ne.symm hvu, hv⟩
          exact ⟨SimpleGraph.Walk.cons hadj.symm p, by simp [SimpleGraph.Walk.length_cons]; omega⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => exact Or.inl (mem_ball_zero x0 n)
      | @cons _ w _ hadj q =>
        rw [SimpleGraph.Walk.length_cons] at hp
        have hw : w ∈ GalCert.ball adj x0 n := (mem_ball_iff h x0 n w).mpr ⟨q, by omega⟩
        exact Or.inr ⟨w, hw, ((adj_iff h w v).mp hadj.symm).2⟩

theorem reach_of_ball (h : adjOk E adj = true) {x0 v : ℤ × ℤ × Fin m} {n : ℕ}
    (hv : v ∈ GalCert.ball adj x0 n) : (SimpleGraph.fromRel (Rel E)).Reachable x0 v := by
  obtain ⟨p, -⟩ := (mem_ball_iff h x0 n v).mp hv
  exact ⟨p.reverse⟩

/-- A path given as a list of vertices, each a listed neighbour of the previous one. -/
def pathOk (adj : Fin m → List (ℤ × ℤ × Fin m)) :
    ℤ × ℤ × Fin m → List (ℤ × ℤ × Fin m) → ℤ × ℤ × Fin m → Bool
  | u, [], v => decide (u = v)
  | u, w :: ws, v => decide (w ∈ (adj u.2.2).map (GalCert.sh u)) && pathOk adj w ws v

theorem reach_of_path (h : adjOk E adj = true) :
    ∀ (u : ℤ × ℤ × Fin m) (ws : List (ℤ × ℤ × Fin m)) (v : ℤ × ℤ × Fin m),
      pathOk adj u ws v = true → (SimpleGraph.fromRel (Rel E)).Reachable u v
  | u, [], v, hp => by
    simp only [pathOk, decide_eq_true_eq] at hp
    subst hp
    rfl
  | u, w :: ws, v, hp => by
    simp only [pathOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    refine SimpleGraph.Reachable.trans ?_ (reach_of_path h w ws v hp.2)
    by_cases hw : u = w
    · subst hw
      rfl
    · refine SimpleGraph.Adj.reachable ((adj_iff h u w).mpr ⟨hw, ?_⟩)
      simp only [GalCert.nbrs, List.mem_toFinset]
      exact hp.1

/-- Translation by a lattice vector is a graph homomorphism. -/
def transl (E : List (Fin m × Fin m × ℤ × ℤ)) (tx ty : ℤ) :
    SimpleGraph.fromRel (Rel E) →g SimpleGraph.fromRel (Rel E) where
  toFun v := (v.1 + tx, v.2.1 + ty, v.2.2)
  map_rel' := by
    rintro ⟨ux, uy, ui⟩ ⟨vx, vy, vi⟩ hadj
    rw [SimpleGraph.fromRel_adj] at hadj ⊢
    obtain ⟨hne, hr⟩ := hadj
    refine ⟨?_, ?_⟩
    · intro heq
      apply hne
      simp only [Prod.mk.injEq] at heq ⊢
      exact ⟨by omega, by omega, heq.2.2⟩
    · rcases hr with ⟨e, he, h1, h2, h3, h4⟩ | ⟨e, he, h1, h2, h3, h4⟩
      · exact Or.inl ⟨e, he, h1, h2, by simp only at h3 ⊢; omega, by simp only at h4 ⊢; omega⟩
      · exact Or.inr ⟨e, he, h1, h2, by simp only at h3 ⊢; omega, by simp only at h4 ⊢; omega⟩

theorem reach_transl {u v : ℤ × ℤ × Fin m} (hr : (SimpleGraph.fromRel (Rel E)).Reachable u v)
    (tx ty : ℤ) :
    (SimpleGraph.fromRel (Rel E)).Reachable (u.1 + tx, u.2.1 + ty, u.2.2) (v.1 + tx, v.2.1 + ty, v.2.2) :=
  hr.map (transl E tx ty)

/-- Connectivity from three kinds of reachability facts at the base vertex. -/
theorem connected (i0 : Fin m)
    (hx : (SimpleGraph.fromRel (Rel E)).Reachable (0, 0, i0) (1, 0, i0))
    (hy : (SimpleGraph.fromRel (Rel E)).Reachable (0, 0, i0) (0, 1, i0))
    (hcls : ∀ i : Fin m, ∃ c : ℤ × ℤ, (SimpleGraph.fromRel (Rel E)).Reachable (0, 0, i0) (c.1, c.2, i))
    (v : ℤ × ℤ × Fin m) : (SimpleGraph.fromRel (Rel E)).Reachable (0, 0, i0) v := by
  have hX : ∀ x y : ℤ, (SimpleGraph.fromRel (Rel E)).Reachable (x, y, i0) (x + 1, y, i0) := by
    intro x y
    simpa [add_comm] using reach_transl hx x y
  have hY : ∀ x y : ℤ, (SimpleGraph.fromRel (Rel E)).Reachable (x, y, i0) (x, y + 1, i0) := by
    intro x y
    simpa [add_comm] using reach_transl hy x y
  have hrow : ∀ x : ℤ, (SimpleGraph.fromRel (Rel E)).Reachable (0, 0, i0) (x, 0, i0) := by
    intro x
    induction x using Int.induction_on with
    | zero => rfl
    | succ k ih => exact ih.trans (hX k 0)
    | pred k ih =>
      refine ih.trans ?_
      have := (hX (-(k : ℤ) - 1) 0).symm
      simpa using this
  have hall : ∀ x y : ℤ, (SimpleGraph.fromRel (Rel E)).Reachable (0, 0, i0) (x, y, i0) := by
    intro x y
    induction y using Int.induction_on with
    | zero => exact hrow x
    | succ k ih => exact ih.trans (hY x k)
    | pred k ih =>
      refine ih.trans ?_
      have := (hY x (-(k : ℤ) - 1)).symm
      simpa using this
  obtain ⟨x, y, i⟩ := v
  obtain ⟨c, hc⟩ := hcls i
  have h2 := reach_transl hc (x - c.1) (y - c.2)
  simp only [zero_add, add_sub_cancel] at h2
  exact (hall (x - c.1) (y - c.2)).trans h2

theorem dist_le_iff (h : adjOk E adj = true) {x0 : ℤ × ℤ × Fin m}
    (hconn : ∀ v, (SimpleGraph.fromRel (Rel E)).Reachable x0 v) (n : ℕ) (v : ℤ × ℤ × Fin m) :
    (SimpleGraph.fromRel (Rel E)).dist x0 v ≤ n ↔ v ∈ GalCert.ball adj x0 n := by
  rw [mem_ball_iff h x0 n v]
  constructor
  · intro hd
    obtain ⟨p, hp⟩ := (hconn v).exists_walk_length_eq_dist
    exact ⟨p.reverse, by rw [SimpleGraph.Walk.length_reverse]; omega⟩
  · rintro ⟨p, hp⟩
    have := SimpleGraph.dist_le p.reverse
    rw [SimpleGraph.Walk.length_reverse] at this
    omega

theorem ncard_zero (h : adjOk E adj = true) {x0 : ℤ × ℤ × Fin m}
    (hconn : ∀ v, (SimpleGraph.fromRel (Rel E)).Reachable x0 v) :
    Set.ncard {v | (SimpleGraph.fromRel (Rel E)).dist x0 v = 0} = 1 := by
  have e : {v | (SimpleGraph.fromRel (Rel E)).dist x0 v = 0} = ↑(GalCert.ball adj x0 0) := by
    ext v
    simp only [Set.mem_setOf_eq, Finset.mem_coe, ← dist_le_iff h hconn 0 v, Nat.le_zero]
  rw [e, Set.ncard_coe_finset]
  simp [GalCert.ball]

theorem ncard_succ (h : adjOk E adj = true) {x0 : ℤ × ℤ × Fin m}
    (hconn : ∀ v, (SimpleGraph.fromRel (Rel E)).Reachable x0 v) (k : ℕ) :
    (Set.ncard {v | (SimpleGraph.fromRel (Rel E)).dist x0 v = k + 1} : ℤ) =
      ((GalCert.ball adj x0 (k + 1)).card : ℤ) - (GalCert.ball adj x0 k).card := by
  have e : {v | (SimpleGraph.fromRel (Rel E)).dist x0 v = k + 1} =
      ↑(GalCert.ball adj x0 (k + 1) \ GalCert.ball adj x0 k) := by
    ext v
    simp only [Set.mem_setOf_eq, Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe,
      ← dist_le_iff h hconn]
    omega
  have hsub : GalCert.ball adj x0 k ⊆ GalCert.ball adj x0 (k + 1) := by
    intro x hx
    simp only [GalCert.ball, Finset.mem_union]
    exact Or.inl hx
  rw [e, Set.ncard_coe_finset]
  have := Finset.card_sdiff_add_card_eq_card hsub
  omega

end SGBridge


namespace P313698
open OMA.S_oeis_a313698

def adjL : Fin 12 → List (ℤ × ℤ × Fin 12) := ![
  [(-1, 0, 0), (1, 0, 0), (0, 0, 1), (0, -1, 3)],
  [(0, 0, 0), (-1, 0, 1), (1, 0, 1), (0, 0, 2)],
  [(0, 0, 1), (-1, 0, 2), (1, 0, 2), (0, 0, 4)],
  [(0, 1, 0), (-1, 0, 3), (1, 0, 3), (0, 0, 5)],
  [(0, 0, 2), (-1, 0, 4), (1, 0, 4), (-1, 0, 6), (0, 0, 6)],
  [(0, 0, 3), (-1, 0, 5), (1, 0, 5), (-1, 0, 7), (0, 0, 7)],
  [(0, 0, 4), (1, 0, 4), (-1, 0, 6), (1, 0, 6), (0, 0, 8), (1, 0, 8)],
  [(0, 0, 5), (1, 0, 5), (-1, 0, 7), (1, 0, 7), (0, 0, 9), (1, 0, 9)],
  [(-1, 0, 6), (0, 0, 6), (-1, 0, 8), (1, 0, 8), (-1, 0, 10), (0, 0, 10)],
  [(-1, 0, 7), (0, 0, 7), (-1, 0, 9), (1, 0, 9), (-1, 0, 11), (0, 0, 11)],
  [(0, 0, 8), (1, 0, 8), (-1, 0, 10), (1, 0, 10), (0, 0, 11)],
  [(0, 0, 9), (1, 0, 9), (0, 0, 10), (-1, 0, 11), (1, 0, 11)]]

theorem hadj : SGBridge.adjOk E adjL = true := by decide +kernel

set_option maxRecDepth 100000 in
noncomputable def regsData : List (GalCert.Region 12) := [
⟨0,0,0,0,0,[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨0,0,0,3,[[.f ⟨10,36,0,0,0,0,0,0,0⟩],[.f ⟨4,0,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨14,3,0,0,0,0,0,0,0⟩]],[.s 1 0]⟩,
⟨0,0,1,2,[[.s 0 0],[.f ⟨10,37,0,0,0,0,0,0,0⟩],[.f ⟨4,1,0,0,0,0,0,0,0⟩],[.s 2 0]],[.s 2 0]⟩,
⟨0,0,2,1,[[.s 1 0],[.f ⟨10,38,0,0,0,0,0,0,0⟩],[.f ⟨4,2,0,0,0,0,0,0,0⟩],[.s 4 0]],[.s 4 0]⟩,
⟨0,0,3,8,[[.f ⟨26,120,0,0,0,0,0,0,0⟩],[.f ⟨10,39,0,0,0,0,0,0,0⟩],[.f ⟨4,3,0,0,0,0,0,0,0⟩],[.s 5 0]],[.s 5 0]⟩,
⟨0,0,4,0,[[.s 2 0],[.f ⟨10,40,0,0,0,0,0,0,0⟩],[.f ⟨4,4,0,0,0,0,0,0,0⟩],[.f ⟨10,42,0,0,0,0,0,0,0⟩],[.s 6 0]],[.f ⟨0,0,0,0,0,0,0,0,0⟩]⟩,
⟨0,0,5,7,[[.s 3 0],[.f ⟨10,41,0,0,0,0,0,0,0⟩],[.f ⟨4,5,0,0,0,0,0,0,0⟩],[.f ⟨10,43,0,0,0,0,0,0,0⟩],[.s 7 0]],[.f ⟨10,43,0,0,0,0,0,0,1⟩]⟩,
⟨0,0,6,1,[[.s 4 0],[.f ⟨4,4,0,0,0,0,0,0,0⟩],[.f ⟨10,42,0,0,0,0,0,0,0⟩],[.f ⟨4,6,0,0,0,0,0,0,0⟩],[.s 8 0],[.f ⟨4,8,0,0,0,0,0,0,0⟩]],[.s 4 4]⟩,
⟨0,0,7,6,[[.s 5 0],[.f ⟨4,5,0,0,0,0,0,0,0⟩],[.f ⟨10,43,0,0,0,0,0,0,0⟩],[.f ⟨4,7,0,0,0,0,0,0,0⟩],[.s 9 0],[.f ⟨4,9,0,0,0,0,0,0,0⟩]],[.s 9 1]⟩,
⟨0,0,8,2,[[.f ⟨10,42,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨10,44,0,0,0,0,0,0,0⟩],[.f ⟨4,8,0,0,0,0,0,0,0⟩],[.f ⟨10,46,0,0,0,0,0,0,0⟩],[.s 10 0]],[.f ⟨10,42,0,0,0,0,0,0,5⟩]⟩,
⟨0,0,9,5,[[.f ⟨10,43,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨10,45,0,0,0,0,0,0,0⟩],[.f ⟨4,9,0,0,0,0,0,0,0⟩],[.f ⟨10,47,0,0,0,0,0,0,0⟩],[.s 11 0]],[.f ⟨10,47,0,0,0,0,0,0,1⟩]⟩,
⟨0,0,10,3,[[.s 8 0],[.f ⟨4,8,0,0,0,0,0,0,0⟩],[.f ⟨10,46,0,0,0,0,0,0,0⟩],[.f ⟨4,10,0,0,0,0,0,0,0⟩],[.s 11 0]],[.s 8 5]⟩,
⟨0,0,11,4,[[.s 9 0],[.f ⟨4,9,0,0,0,0,0,0,0⟩],[.s 10 0],[.f ⟨10,47,0,0,0,0,0,0,0⟩],[.f ⟨4,11,0,0,0,0,0,0,0⟩]],[.s 10 4]⟩]⟩,
⟨1,-3,-1,0,0,[(1,-3,0),(-1,3,0),(-3,-1,10)],-3,-1,10,10,0,0,0,0,12,0,0,0,
[⟨-3,-1,0,15,[[.f ⟨31,24,0,0,0,0,0,0,0⟩,.f ⟨31,24,0,0,0,1,0,1,0⟩],[.f ⟨13,12,0,0,0,0,0,0,0⟩,.f ⟨13,12,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨15,3,0,0,0,0,0,0,0⟩,.f ⟨15,3,1,0,1,0,0,0,0⟩]],[.s 1 0,.s 1 0]⟩,
⟨-3,-1,1,14,[[.s 0 0,.s 0 0],[.f ⟨31,25,0,0,0,0,0,0,0⟩,.f ⟨31,25,0,0,0,1,0,1,0⟩],[.f ⟨13,13,0,0,0,0,0,0,0⟩,.f ⟨13,13,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 2 0,.s 2 0]⟩,
⟨-3,-1,2,13,[[.s 1 0,.s 1 0],[.f ⟨31,26,0,0,0,0,0,0,0⟩,.f ⟨31,26,0,0,0,1,0,1,0⟩],[.f ⟨13,14,0,0,0,0,0,0,0⟩,.f ⟨13,14,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0]],[.s 4 0,.s 4 0]⟩,
⟨-3,-1,3,7,[[.f ⟨10,12,0,0,0,0,0,0,0⟩,.f ⟨31,0,0,0,0,1,0,0,0⟩],[.f ⟨31,27,0,0,0,0,0,0,0⟩,.f ⟨31,27,0,0,0,1,0,1,0⟩],[.f ⟨13,15,0,0,0,0,0,0,0⟩,.f ⟨13,15,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0]],[.f ⟨10,12,0,0,0,0,0,0,3⟩,.f ⟨31,0,0,0,0,1,0,0,3⟩]⟩,
⟨-3,-1,4,12,[[.s 2 0,.s 2 0],[.f ⟨31,28,0,0,0,0,0,0,0⟩,.f ⟨31,28,0,0,0,1,0,1,0⟩],[.f ⟨13,16,0,0,0,0,0,0,0⟩,.f ⟨13,16,1,0,1,0,0,0,0⟩],[.f ⟨31,30,0,0,0,0,0,0,0⟩,.f ⟨31,30,0,0,0,1,0,1,0⟩],[.s 6 0,.s 6 0]],[.s 6 0,.s 6 0]⟩,
⟨-3,-1,5,8,[[.s 3 0,.s 3 0],[.f ⟨31,29,0,0,0,0,0,0,0⟩,.f ⟨31,29,0,0,0,1,0,1,0⟩],[.f ⟨13,17,0,0,0,0,0,0,0⟩,.f ⟨13,17,1,0,1,0,0,0,0⟩],[.f ⟨31,31,0,0,0,0,0,0,0⟩,.f ⟨31,31,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨-3,-1,6,11,[[.s 4 0,.s 4 0],[.f ⟨13,16,0,0,0,0,0,0,0⟩,.f ⟨13,16,1,0,1,0,0,0,0⟩],[.f ⟨31,30,0,0,0,0,0,0,0⟩,.f ⟨31,30,0,0,0,1,0,1,0⟩],[.f ⟨13,18,0,0,0,0,0,0,0⟩,.f ⟨13,18,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.f ⟨13,20,0,0,0,0,0,0,0⟩,.f ⟨13,20,1,0,1,0,0,0,0⟩]],[.f ⟨13,20,0,0,0,0,0,0,0⟩,.f ⟨13,20,1,0,1,0,0,0,0⟩]⟩,
⟨-3,-1,7,8,[[.s 5 0,.s 5 0],[.f ⟨13,17,0,0,0,0,0,0,0⟩,.f ⟨13,17,1,0,1,0,0,0,0⟩],[.f ⟨31,31,0,0,0,0,0,0,0⟩,.f ⟨31,31,0,0,0,1,0,1,0⟩],[.f ⟨13,19,0,0,0,0,0,0,0⟩,.f ⟨13,19,1,0,1,0,0,0,0⟩],[.s 9 0,.s 9 0],[.f ⟨13,21,0,0,0,0,0,0,0⟩,.f ⟨13,21,1,0,1,0,0,0,0⟩]],[.f ⟨13,17,0,0,0,0,0,0,3⟩,.f ⟨13,17,1,0,1,0,0,0,3⟩]⟩,
⟨-3,-1,8,11,[[.f ⟨31,30,0,0,0,0,0,0,0⟩,.f ⟨31,30,0,0,0,1,0,1,0⟩],[.s 6 0,.s 6 0],[.f ⟨31,32,0,0,0,0,0,0,0⟩,.f ⟨31,32,0,0,0,1,0,1,0⟩],[.f ⟨13,20,0,0,0,0,0,0,0⟩,.f ⟨13,20,1,0,1,0,0,0,0⟩],[.f ⟨31,34,0,0,0,0,0,0,0⟩,.f ⟨31,34,0,0,0,1,0,1,0⟩],[.s 10 0,.s 10 0]],[.f ⟨13,20,0,0,0,0,0,0,2⟩,.f ⟨13,20,1,0,1,0,0,0,2⟩]⟩,
⟨-3,-1,9,9,[[.f ⟨31,31,0,0,0,0,0,0,0⟩,.f ⟨31,31,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0],[.f ⟨31,33,0,0,0,0,0,0,0⟩,.f ⟨31,33,0,0,0,1,0,1,0⟩],[.f ⟨13,21,0,0,0,0,0,0,0⟩,.f ⟨13,21,1,0,1,0,0,0,0⟩],[.f ⟨31,35,0,0,0,0,0,0,0⟩,.f ⟨31,35,0,0,0,1,0,1,0⟩],[.s 11 0,.s 11 0]],[.s 7 4,.s 7 4]⟩,
⟨-3,-1,10,10,[[.s 8 0,.s 8 0],[.f ⟨13,20,0,0,0,0,0,0,0⟩,.f ⟨13,20,1,0,1,0,0,0,0⟩],[.f ⟨31,34,0,0,0,0,0,0,0⟩,.f ⟨31,34,0,0,0,1,0,1,0⟩],[.f ⟨13,22,0,0,0,0,0,0,0⟩,.f ⟨13,22,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨13,22,0,0,0,0,0,0,2⟩,.f ⟨13,22,1,0,1,0,0,0,2⟩]⟩,
⟨-3,-1,11,9,[[.s 9 0,.s 9 0],[.f ⟨13,21,0,0,0,0,0,0,0⟩,.f ⟨13,21,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0],[.f ⟨31,35,0,0,0,0,0,0,0⟩,.f ⟨31,35,0,0,0,1,0,1,0⟩],[.f ⟨13,23,0,0,0,0,0,0,0⟩,.f ⟨13,23,1,0,1,0,0,0,0⟩]],[.f ⟨13,21,0,0,0,0,0,0,4⟩,.f ⟨13,21,1,0,1,0,0,0,4⟩]⟩]⟩,
⟨0,0,0,0,0,[(1,3,0),(-1,-3,0),(3,-1,1),(-3,1,-10)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨3,-1,0,15,[[.f ⟨14,36,0,0,0,0,0,0,0⟩],[.f ⟨16,0,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨14,51,0,0,0,0,0,0,0⟩]],[.s 1 0]⟩,
⟨3,-1,1,14,[[.s 0 0],[.f ⟨14,37,0,0,0,0,0,0,0⟩],[.f ⟨16,1,0,0,0,0,0,0,0⟩],[.s 2 0]],[.s 2 0]⟩,
⟨3,-1,2,13,[[.s 1 0],[.f ⟨14,38,0,0,0,0,0,0,0⟩],[.f ⟨16,2,0,0,0,0,0,0,0⟩],[.s 4 0]],[.s 4 0]⟩,
⟨3,-1,3,7,[[.f ⟨4,24,0,0,0,0,0,0,0⟩],[.f ⟨14,39,0,0,0,0,0,0,0⟩],[.f ⟨16,3,0,0,0,0,0,0,0⟩],[.s 5 0]],[.f ⟨4,24,0,0,0,0,0,0,3⟩]⟩,
⟨3,-1,4,12,[[.s 2 0],[.f ⟨14,40,0,0,0,0,0,0,0⟩],[.f ⟨16,4,0,0,0,0,0,0,0⟩],[.f ⟨14,42,0,0,0,0,0,0,0⟩],[.s 6 0]],[.f ⟨14,42,0,0,0,0,0,0,1⟩]⟩,
⟨3,-1,5,8,[[.s 3 0],[.f ⟨14,41,0,0,0,0,0,0,0⟩],[.f ⟨16,5,0,0,0,0,0,0,0⟩],[.f ⟨14,43,0,0,0,0,0,0,0⟩],[.s 7 0]],[.s 3 3]⟩,
⟨3,-1,6,12,[[.s 4 0],[.f ⟨16,4,0,0,0,0,0,0,0⟩],[.f ⟨14,42,0,0,0,0,0,0,0⟩],[.f ⟨16,6,0,0,0,0,0,0,0⟩],[.s 8 0],[.f ⟨16,8,0,0,0,0,0,0,0⟩]],[.f ⟨14,42,0,0,0,0,0,0,3⟩]⟩,
⟨3,-1,7,9,[[.s 5 0],[.f ⟨16,5,0,0,0,0,0,0,0⟩],[.f ⟨14,43,0,0,0,0,0,0,0⟩],[.f ⟨16,7,0,0,0,0,0,0,0⟩],[.s 9 0],[.f ⟨16,9,0,0,0,0,0,0,0⟩]],[.s 5 4]⟩,
⟨3,-1,8,11,[[.f ⟨14,42,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨14,44,0,0,0,0,0,0,0⟩],[.f ⟨16,8,0,0,0,0,0,0,0⟩],[.f ⟨14,46,0,0,0,0,0,0,0⟩],[.s 10 0]],[.f ⟨14,44,0,0,0,0,0,0,3⟩]⟩,
⟨3,-1,9,9,[[.f ⟨14,43,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨14,45,0,0,0,0,0,0,0⟩],[.f ⟨16,9,0,0,0,0,0,0,0⟩],[.f ⟨14,47,0,0,0,0,0,0,0⟩],[.s 11 0]],[.f ⟨14,43,0,0,0,0,0,0,5⟩]⟩,
⟨3,-1,10,11,[[.s 8 0],[.f ⟨16,8,0,0,0,0,0,0,0⟩],[.f ⟨14,46,0,0,0,0,0,0,0⟩],[.f ⟨16,10,0,0,0,0,0,0,0⟩],[.s 11 0]],[.f ⟨14,46,0,0,0,0,0,0,3⟩]⟩,
⟨3,-1,11,10,[[.s 9 0],[.f ⟨16,9,0,0,0,0,0,0,0⟩],[.s 10 0],[.f ⟨14,47,0,0,0,0,0,0,0⟩],[.f ⟨16,11,0,0,0,0,0,0,0⟩]],[.s 9 5]⟩]⟩,
⟨1,6,-2,0,0,[(1,3,0),(-1,-3,0),(3,-1,20)],3,-1,20,20,0,0,0,0,24,0,0,0,
[⟨6,-2,0,27,[[.f ⟨14,84,0,0,0,0,0,0,0⟩,.f ⟨14,84,1,0,1,0,0,0,0⟩],[.f ⟨17,0,0,0,0,0,0,0,0⟩,.f ⟨17,0,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨14,3,0,0,1,0,0,0,0⟩,.f ⟨14,3,1,0,2,0,0,0,0⟩]],[.s 1 0,.s 1 0]⟩,
⟨6,-2,1,26,[[.s 0 0,.s 0 0],[.f ⟨14,85,0,0,0,0,0,0,0⟩,.f ⟨14,85,1,0,1,0,0,0,0⟩],[.f ⟨17,1,0,0,0,0,0,0,0⟩,.f ⟨17,1,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 2 0,.s 2 0]⟩,
⟨6,-2,2,25,[[.s 1 0,.s 1 0],[.f ⟨14,86,0,0,0,0,0,0,0⟩,.f ⟨14,86,1,0,1,0,0,0,0⟩],[.f ⟨17,2,0,0,0,0,0,0,0⟩,.f ⟨17,2,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0]],[.s 4 0,.s 4 0]⟩,
⟨6,-2,3,19,[[.f ⟨18,12,0,0,0,0,0,0,0⟩,.f ⟨19,48,1,0,0,0,0,0,0⟩],[.f ⟨14,87,0,0,0,0,0,0,0⟩,.f ⟨14,87,1,0,1,0,0,0,0⟩],[.f ⟨17,3,0,0,0,0,0,0,0⟩,.f ⟨17,3,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0]],[.f ⟨18,12,0,0,0,0,0,0,3⟩,.f ⟨19,48,1,0,0,0,0,0,3⟩]⟩,
⟨6,-2,4,24,[[.s 2 0,.s 2 0],[.f ⟨14,88,0,0,0,0,0,0,0⟩,.f ⟨14,88,1,0,1,0,0,0,0⟩],[.f ⟨17,4,0,0,0,0,0,0,0⟩,.f ⟨17,4,1,0,1,0,0,0,0⟩],[.f ⟨14,90,0,0,0,0,0,0,0⟩,.f ⟨14,90,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.f ⟨14,90,0,0,0,0,0,0,1⟩,.f ⟨14,90,1,0,1,0,0,0,1⟩]⟩,
⟨6,-2,5,20,[[.s 3 0,.s 3 0],[.f ⟨14,89,0,0,0,0,0,0,0⟩,.f ⟨14,89,1,0,1,0,0,0,0⟩],[.f ⟨17,5,0,0,0,0,0,0,0⟩,.f ⟨17,5,1,0,1,0,0,0,0⟩],[.f ⟨14,91,0,0,0,0,0,0,0⟩,.f ⟨14,91,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨6,-2,6,24,[[.s 4 0,.s 4 0],[.f ⟨17,4,0,0,0,0,0,0,0⟩,.f ⟨17,4,1,0,1,0,0,0,0⟩],[.f ⟨14,90,0,0,0,0,0,0,0⟩,.f ⟨14,90,1,0,1,0,0,0,0⟩],[.f ⟨17,6,0,0,0,0,0,0,0⟩,.f ⟨17,6,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.f ⟨17,8,0,0,0,0,0,0,0⟩,.f ⟨17,8,1,0,1,0,0,0,0⟩]],[.f ⟨14,90,0,0,0,0,0,0,3⟩,.f ⟨14,90,1,0,1,0,0,0,3⟩]⟩,
⟨6,-2,7,21,[[.s 5 0,.s 5 0],[.f ⟨17,5,0,0,0,0,0,0,0⟩,.f ⟨17,5,1,0,1,0,0,0,0⟩],[.f ⟨14,91,0,0,0,0,0,0,0⟩,.f ⟨14,91,1,0,1,0,0,0,0⟩],[.f ⟨17,7,0,0,0,0,0,0,0⟩,.f ⟨17,7,1,0,1,0,0,0,0⟩],[.s 9 0,.s 9 0],[.f ⟨17,9,0,0,0,0,0,0,0⟩,.f ⟨17,9,1,0,1,0,0,0,0⟩]],[.s 5 4,.s 5 4]⟩,
⟨6,-2,8,23,[[.f ⟨14,90,0,0,0,0,0,0,0⟩,.f ⟨14,90,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.f ⟨14,92,0,0,0,0,0,0,0⟩,.f ⟨14,92,1,0,1,0,0,0,0⟩],[.f ⟨17,8,0,0,0,0,0,0,0⟩,.f ⟨17,8,1,0,1,0,0,0,0⟩],[.f ⟨14,94,0,0,0,0,0,0,0⟩,.f ⟨14,94,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0]],[.f ⟨14,92,0,0,0,0,0,0,3⟩,.f ⟨14,92,1,0,1,0,0,0,3⟩]⟩,
⟨6,-2,9,21,[[.f ⟨14,91,0,0,0,0,0,0,0⟩,.f ⟨14,91,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨14,93,0,0,0,0,0,0,0⟩,.f ⟨14,93,1,0,1,0,0,0,0⟩],[.f ⟨17,9,0,0,0,0,0,0,0⟩,.f ⟨17,9,1,0,1,0,0,0,0⟩],[.f ⟨14,95,0,0,0,0,0,0,0⟩,.f ⟨14,95,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨14,91,0,0,0,0,0,0,5⟩,.f ⟨14,91,1,0,1,0,0,0,5⟩]⟩,
⟨6,-2,10,23,[[.s 8 0,.s 8 0],[.f ⟨17,8,0,0,0,0,0,0,0⟩,.f ⟨17,8,1,0,1,0,0,0,0⟩],[.f ⟨14,94,0,0,0,0,0,0,0⟩,.f ⟨14,94,1,0,1,0,0,0,0⟩],[.f ⟨17,10,0,0,0,0,0,0,0⟩,.f ⟨17,10,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨14,94,0,0,0,0,0,0,3⟩,.f ⟨14,94,1,0,1,0,0,0,3⟩]⟩,
⟨6,-2,11,22,[[.s 9 0,.s 9 0],[.f ⟨17,9,0,0,0,0,0,0,0⟩,.f ⟨17,9,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0],[.f ⟨14,95,0,0,0,0,0,0,0⟩,.f ⟨14,95,1,0,1,0,0,0,0⟩],[.f ⟨17,11,0,0,0,0,0,0,0⟩,.f ⟨17,11,1,0,1,0,0,0,0⟩]],[.s 9 5,.s 9 5]⟩,
⟨9,-3,0,39,[[.f ⟨14,36,0,0,1,0,0,0,0⟩,.f ⟨14,36,1,0,2,0,0,0,0⟩],[.f ⟨17,12,0,0,0,0,0,0,0⟩,.f ⟨17,12,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.f ⟨14,51,0,0,1,0,0,0,0⟩,.f ⟨14,51,1,0,2,0,0,0,0⟩]],[.s 13 0,.s 13 0]⟩,
⟨9,-3,1,38,[[.s 12 0,.s 12 0],[.f ⟨14,37,0,0,1,0,0,0,0⟩,.f ⟨14,37,1,0,2,0,0,0,0⟩],[.f ⟨17,13,0,0,0,0,0,0,0⟩,.f ⟨17,13,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0]],[.s 14 0,.s 14 0]⟩,
⟨9,-3,2,37,[[.s 13 0,.s 13 0],[.f ⟨14,38,0,0,1,0,0,0,0⟩,.f ⟨14,38,1,0,2,0,0,0,0⟩],[.f ⟨17,14,0,0,0,0,0,0,0⟩,.f ⟨17,14,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0]],[.s 16 0,.s 16 0]⟩,
⟨9,-3,3,31,[[.f ⟨19,12,0,0,0,0,0,0,0⟩,.f ⟨19,12,1,0,1,0,0,0,0⟩],[.f ⟨14,39,0,0,1,0,0,0,0⟩,.f ⟨14,39,1,0,2,0,0,0,0⟩],[.f ⟨17,15,0,0,0,0,0,0,0⟩,.f ⟨17,15,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0]],[.f ⟨19,12,0,0,0,0,0,0,3⟩,.f ⟨19,12,1,0,1,0,0,0,3⟩]⟩,
⟨9,-3,4,36,[[.s 14 0,.s 14 0],[.f ⟨14,40,0,0,1,0,0,0,0⟩,.f ⟨14,40,1,0,2,0,0,0,0⟩],[.f ⟨17,16,0,0,0,0,0,0,0⟩,.f ⟨17,16,1,0,1,0,0,0,0⟩],[.f ⟨14,42,0,0,1,0,0,0,0⟩,.f ⟨14,42,1,0,2,0,0,0,0⟩],[.s 18 0,.s 18 0]],[.f ⟨14,42,0,0,1,0,0,0,1⟩,.f ⟨14,42,1,0,2,0,0,0,1⟩]⟩,
⟨9,-3,5,32,[[.s 15 0,.s 15 0],[.f ⟨14,41,0,0,1,0,0,0,0⟩,.f ⟨14,41,1,0,2,0,0,0,0⟩],[.f ⟨17,17,0,0,0,0,0,0,0⟩,.f ⟨17,17,1,0,1,0,0,0,0⟩],[.f ⟨14,43,0,0,1,0,0,0,0⟩,.f ⟨14,43,1,0,2,0,0,0,0⟩],[.s 19 0,.s 19 0]],[.s 15 3,.s 15 3]⟩,
⟨9,-3,6,36,[[.s 16 0,.s 16 0],[.f ⟨17,16,0,0,0,0,0,0,0⟩,.f ⟨17,16,1,0,1,0,0,0,0⟩],[.f ⟨14,42,0,0,1,0,0,0,0⟩,.f ⟨14,42,1,0,2,0,0,0,0⟩],[.f ⟨17,18,0,0,0,0,0,0,0⟩,.f ⟨17,18,1,0,1,0,0,0,0⟩],[.s 20 0,.s 20 0],[.f ⟨17,20,0,0,0,0,0,0,0⟩,.f ⟨17,20,1,0,1,0,0,0,0⟩]],[.f ⟨14,42,0,0,1,0,0,0,3⟩,.f ⟨14,42,1,0,2,0,0,0,3⟩]⟩,
⟨9,-3,7,33,[[.s 17 0,.s 17 0],[.f ⟨17,17,0,0,0,0,0,0,0⟩,.f ⟨17,17,1,0,1,0,0,0,0⟩],[.f ⟨14,43,0,0,1,0,0,0,0⟩,.f ⟨14,43,1,0,2,0,0,0,0⟩],[.f ⟨17,19,0,0,0,0,0,0,0⟩,.f ⟨17,19,1,0,1,0,0,0,0⟩],[.s 21 0,.s 21 0],[.f ⟨17,21,0,0,0,0,0,0,0⟩,.f ⟨17,21,1,0,1,0,0,0,0⟩]],[.s 17 4,.s 17 4]⟩,
⟨9,-3,8,35,[[.f ⟨14,42,0,0,1,0,0,0,0⟩,.f ⟨14,42,1,0,2,0,0,0,0⟩],[.s 18 0,.s 18 0],[.f ⟨14,44,0,0,1,0,0,0,0⟩,.f ⟨14,44,1,0,2,0,0,0,0⟩],[.f ⟨17,20,0,0,0,0,0,0,0⟩,.f ⟨17,20,1,0,1,0,0,0,0⟩],[.f ⟨14,46,0,0,1,0,0,0,0⟩,.f ⟨14,46,1,0,2,0,0,0,0⟩],[.s 22 0,.s 22 0]],[.f ⟨14,44,0,0,1,0,0,0,3⟩,.f ⟨14,44,1,0,2,0,0,0,3⟩]⟩,
⟨9,-3,9,33,[[.f ⟨14,43,0,0,1,0,0,0,0⟩,.f ⟨14,43,1,0,2,0,0,0,0⟩],[.s 19 0,.s 19 0],[.f ⟨14,45,0,0,1,0,0,0,0⟩,.f ⟨14,45,1,0,2,0,0,0,0⟩],[.f ⟨17,21,0,0,0,0,0,0,0⟩,.f ⟨17,21,1,0,1,0,0,0,0⟩],[.f ⟨14,47,0,0,1,0,0,0,0⟩,.f ⟨14,47,1,0,2,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.f ⟨14,43,0,0,1,0,0,0,5⟩,.f ⟨14,43,1,0,2,0,0,0,5⟩]⟩,
⟨9,-3,10,35,[[.s 20 0,.s 20 0],[.f ⟨17,20,0,0,0,0,0,0,0⟩,.f ⟨17,20,1,0,1,0,0,0,0⟩],[.f ⟨14,46,0,0,1,0,0,0,0⟩,.f ⟨14,46,1,0,2,0,0,0,0⟩],[.f ⟨17,22,0,0,0,0,0,0,0⟩,.f ⟨17,22,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.f ⟨14,46,0,0,1,0,0,0,3⟩,.f ⟨14,46,1,0,2,0,0,0,3⟩]⟩,
⟨9,-3,11,34,[[.s 21 0,.s 21 0],[.f ⟨17,21,0,0,0,0,0,0,0⟩,.f ⟨17,21,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.f ⟨14,47,0,0,1,0,0,0,0⟩,.f ⟨14,47,1,0,2,0,0,0,0⟩],[.f ⟨17,23,0,0,0,0,0,0,0⟩,.f ⟨17,23,1,0,1,0,0,0,0⟩]],[.s 21 5,.s 21 5]⟩]⟩,
⟨0,0,0,0,0,[(0,1,0),(0,-1,0),(1,0,1),(-1,0,-4)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨1,0,0,4,[[.f ⟨0,0,0,0,0,0,0,0,0⟩],[.s 12 0],[.s 1 0],[.f ⟨14,15,0,0,0,0,0,0,0⟩]],[.f ⟨0,0,0,0,0,0,0,0,1⟩]⟩,
⟨1,0,1,3,[[.s 0 0],[.f ⟨0,1,0,0,0,0,0,0,0⟩],[.s 13 0],[.s 2 0]],[.f ⟨0,1,0,0,0,0,0,0,2⟩]⟩,
⟨1,0,2,2,[[.s 1 0],[.f ⟨0,2,0,0,0,0,0,0,0⟩],[.s 14 0],[.s 4 0]],[.f ⟨0,2,0,0,0,0,0,0,2⟩]⟩,
⟨1,0,3,8,[[.f ⟨26,168,0,0,0,0,0,0,0⟩],[.f ⟨0,3,0,0,0,0,0,0,0⟩],[.s 15 0],[.s 5 0]],[.s 5 0]⟩,
⟨1,0,4,1,[[.s 2 0],[.f ⟨0,4,0,0,0,0,0,0,0⟩],[.s 16 0],[.f ⟨0,6,0,0,0,0,0,0,0⟩],[.s 6 0]],[.f ⟨0,4,0,0,0,0,0,0,2⟩]⟩,
⟨1,0,5,7,[[.s 3 0],[.f ⟨0,5,0,0,0,0,0,0,0⟩],[.s 17 0],[.f ⟨0,7,0,0,0,0,0,0,0⟩],[.s 7 0]],[.f ⟨0,7,0,0,0,0,0,0,1⟩]⟩,
⟨1,0,6,2,[[.s 4 0],[.s 16 0],[.f ⟨0,6,0,0,0,0,0,0,0⟩],[.s 18 0],[.s 8 0],[.s 20 0]],[.s 4 4]⟩,
⟨1,0,7,6,[[.s 5 0],[.s 17 0],[.f ⟨0,7,0,0,0,0,0,0,0⟩],[.s 19 0],[.s 9 0],[.s 21 0]],[.s 9 1]⟩,
⟨1,0,8,2,[[.f ⟨0,6,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨0,8,0,0,0,0,0,0,0⟩],[.s 20 0],[.f ⟨0,10,0,0,0,0,0,0,0⟩],[.s 10 0]],[.f ⟨0,6,0,0,0,0,0,0,5⟩]⟩,
⟨1,0,9,5,[[.f ⟨0,7,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨0,9,0,0,0,0,0,0,0⟩],[.s 21 0],[.f ⟨0,11,0,0,0,0,0,0,0⟩],[.s 11 0]],[.f ⟨0,11,0,0,0,0,0,0,1⟩]⟩,
⟨1,0,10,3,[[.s 8 0],[.s 20 0],[.f ⟨0,10,0,0,0,0,0,0,0⟩],[.s 22 0],[.s 11 0]],[.s 8 5]⟩,
⟨1,0,11,4,[[.s 9 0],[.s 21 0],[.s 10 0],[.f ⟨0,11,0,0,0,0,0,0,0⟩],[.s 23 0]],[.s 10 4]⟩,
⟨2,0,0,5,[[.s 0 0],[.s 24 0],[.s 13 0],[.f ⟨14,39,0,0,0,0,0,0,0⟩]],[.s 0 1]⟩,
⟨2,0,1,4,[[.s 12 0],[.s 1 0],[.s 25 0],[.s 14 0]],[.s 1 2]⟩,
⟨2,0,2,3,[[.s 13 0],[.s 2 0],[.s 26 0],[.s 16 0]],[.s 2 2]⟩,
⟨2,0,3,8,[[.f ⟨24,0,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 27 0],[.s 17 0]],[.s 17 0]⟩,
⟨2,0,4,2,[[.s 14 0],[.s 4 0],[.s 28 0],[.s 6 0],[.s 18 0]],[.s 4 2]⟩,
⟨2,0,5,7,[[.s 15 0],[.s 5 0],[.s 29 0],[.s 7 0],[.s 19 0]],[.s 7 1]⟩,
⟨2,0,6,3,[[.s 16 0],[.s 28 0],[.s 6 0],[.s 30 0],[.s 20 0],[.s 32 0]],[.s 16 4]⟩,
⟨2,0,7,6,[[.s 17 0],[.s 29 0],[.s 7 0],[.s 31 0],[.s 21 0],[.s 33 0]],[.s 21 1]⟩,
⟨2,0,8,3,[[.s 6 0],[.s 18 0],[.s 8 0],[.s 32 0],[.s 10 0],[.s 22 0]],[.s 6 5]⟩,
⟨2,0,9,5,[[.s 7 0],[.s 19 0],[.s 9 0],[.s 33 0],[.s 11 0],[.s 23 0]],[.s 11 1]⟩,
⟨2,0,10,4,[[.s 20 0],[.s 32 0],[.s 10 0],[.s 34 0],[.s 23 0]],[.s 20 5]⟩,
⟨2,0,11,5,[[.s 21 0],[.s 33 0],[.s 22 0],[.s 11 0],[.s 35 0]],[.s 22 4]⟩,
⟨3,0,0,6,[[.s 12 0],[.s 36 0],[.s 25 0],[.f ⟨2,3,0,0,0,0,0,0,0⟩]],[.s 12 1]⟩,
⟨3,0,1,5,[[.s 24 0],[.s 13 0],[.s 37 0],[.s 26 0]],[.s 13 2]⟩,
⟨3,0,2,4,[[.s 25 0],[.s 14 0],[.s 38 0],[.s 28 0]],[.s 14 2]⟩,
⟨3,0,3,8,[[.f ⟨6,0,0,0,0,0,0,0,0⟩],[.s 15 0],[.s 39 0],[.s 29 0]],[.s 29 0]⟩,
⟨3,0,4,3,[[.s 26 0],[.s 16 0],[.s 40 0],[.s 18 0],[.s 30 0]],[.s 16 2]⟩,
⟨3,0,5,7,[[.s 27 0],[.s 17 0],[.s 41 0],[.s 19 0],[.s 31 0]],[.s 19 1]⟩,
⟨3,0,6,4,[[.s 28 0],[.s 40 0],[.s 18 0],[.s 42 0],[.s 32 0],[.s 44 0]],[.s 28 4]⟩,
⟨3,0,7,7,[[.s 29 0],[.s 41 0],[.s 19 0],[.s 43 0],[.s 33 0],[.s 45 0]],[.s 19 3]⟩,
⟨3,0,8,4,[[.s 18 0],[.s 30 0],[.s 20 0],[.s 44 0],[.s 22 0],[.s 34 0]],[.s 18 5]⟩,
⟨3,0,9,6,[[.s 19 0],[.s 31 0],[.s 21 0],[.s 45 0],[.s 23 0],[.s 35 0]],[.s 21 3]⟩,
⟨3,0,10,5,[[.s 32 0],[.s 44 0],[.s 22 0],[.s 46 0],[.s 35 0]],[.s 32 5]⟩,
⟨3,0,11,6,[[.s 33 0],[.s 45 0],[.s 34 0],[.s 23 0],[.s 47 0]],[.s 34 4]⟩,
⟨4,0,0,7,[[.s 24 0],[.f ⟨5,0,0,0,0,0,0,0,0⟩],[.s 37 0],[.f ⟨16,3,0,0,0,0,0,0,0⟩]],[.s 24 1]⟩,
⟨4,0,1,6,[[.s 36 0],[.s 25 0],[.f ⟨5,1,0,0,0,0,0,0,0⟩],[.s 38 0]],[.s 25 2]⟩,
⟨4,0,2,5,[[.s 37 0],[.s 26 0],[.f ⟨5,2,0,0,0,0,0,0,0⟩],[.s 40 0]],[.s 26 2]⟩,
⟨4,0,3,9,[[.f ⟨20,0,0,0,0,0,0,0,0⟩],[.s 27 0],[.f ⟨5,3,0,0,0,0,0,0,0⟩],[.s 41 0]],[.s 27 2]⟩,
⟨4,0,4,4,[[.s 38 0],[.s 28 0],[.f ⟨5,4,0,0,0,0,0,0,0⟩],[.s 30 0],[.s 42 0]],[.s 28 2]⟩,
⟨4,0,5,8,[[.s 39 0],[.s 29 0],[.f ⟨5,5,0,0,0,0,0,0,0⟩],[.s 31 0],[.s 43 0]],[.s 29 2]⟩,
⟨4,0,6,5,[[.s 40 0],[.f ⟨5,4,0,0,0,0,0,0,0⟩],[.s 30 0],[.f ⟨5,6,0,0,0,0,0,0,0⟩],[.s 44 0],[.f ⟨5,8,0,0,0,0,0,0,0⟩]],[.s 40 4]⟩,
⟨4,0,7,8,[[.s 41 0],[.f ⟨5,5,0,0,0,0,0,0,0⟩],[.s 31 0],[.f ⟨5,7,0,0,0,0,0,0,0⟩],[.s 45 0],[.f ⟨5,9,0,0,0,0,0,0,0⟩]],[.s 31 3]⟩,
⟨4,0,8,5,[[.s 30 0],[.s 42 0],[.s 32 0],[.f ⟨5,8,0,0,0,0,0,0,0⟩],[.s 34 0],[.s 46 0]],[.s 30 5]⟩,
⟨4,0,9,7,[[.s 31 0],[.s 43 0],[.s 33 0],[.f ⟨5,9,0,0,0,0,0,0,0⟩],[.s 35 0],[.s 47 0]],[.s 33 3]⟩,
⟨4,0,10,6,[[.s 44 0],[.f ⟨5,8,0,0,0,0,0,0,0⟩],[.s 34 0],[.f ⟨5,10,0,0,0,0,0,0,0⟩],[.s 47 0]],[.s 44 5]⟩,
⟨4,0,11,7,[[.s 45 0],[.f ⟨5,9,0,0,0,0,0,0,0⟩],[.s 46 0],[.s 35 0],[.f ⟨5,11,0,0,0,0,0,0,0⟩]],[.s 46 4]⟩]⟩,
⟨1,3,0,0,0,[(0,1,0),(0,-1,0),(1,0,5)],1,0,5,3,0,0,0,0,3,0,0,0,
[⟨5,0,0,8,[[.f ⟨4,36,0,0,0,0,0,0,0⟩,.s 24 0],[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨18,3,0,0,0,0,0,0,0⟩,.f ⟨18,3,1,0,1,0,0,0,0⟩]],[.f ⟨4,36,0,0,0,0,0,0,1⟩,.s 24 1]⟩,
⟨5,0,1,7,[[.s 0 0,.s 0 0],[.f ⟨4,37,0,0,0,0,0,0,0⟩,.s 25 0],[.s 13 0,.s 13 0],[.s 2 0,.s 2 0]],[.f ⟨4,37,0,0,0,0,0,0,2⟩,.s 25 2]⟩,
⟨5,0,2,6,[[.s 1 0,.s 1 0],[.f ⟨4,38,0,0,0,0,0,0,0⟩,.s 26 0],[.s 14 0,.s 14 0],[.s 4 0,.s 4 0]],[.f ⟨4,38,0,0,0,0,0,0,2⟩,.s 26 2]⟩,
⟨5,0,3,10,[[.f ⟨20,12,0,0,0,0,0,0,0⟩,.f ⟨21,24,1,0,0,0,0,0,0⟩],[.f ⟨4,39,0,0,0,0,0,0,0⟩,.s 27 0],[.s 15 0,.s 15 0],[.s 5 0,.s 5 0]],[.f ⟨4,39,0,0,0,0,0,0,2⟩,.s 27 2]⟩,
⟨5,0,4,5,[[.s 2 0,.s 2 0],[.f ⟨4,40,0,0,0,0,0,0,0⟩,.s 28 0],[.s 16 0,.s 16 0],[.f ⟨4,42,0,0,0,0,0,0,0⟩,.s 30 0],[.s 6 0,.s 6 0]],[.f ⟨4,40,0,0,0,0,0,0,2⟩,.s 28 2]⟩,
⟨5,0,5,9,[[.s 3 0,.s 3 0],[.f ⟨4,41,0,0,0,0,0,0,0⟩,.s 29 0],[.s 17 0,.s 17 0],[.f ⟨4,43,0,0,0,0,0,0,0⟩,.s 31 0],[.s 7 0,.s 7 0]],[.f ⟨4,41,0,0,0,0,0,0,2⟩,.s 29 2]⟩,
⟨5,0,6,6,[[.s 4 0,.s 4 0],[.s 16 0,.s 16 0],[.f ⟨4,42,0,0,0,0,0,0,0⟩,.s 30 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 20 0,.s 20 0]],[.s 4 4,.s 4 4]⟩,
⟨5,0,7,9,[[.s 5 0,.s 5 0],[.s 17 0,.s 17 0],[.f ⟨4,43,0,0,0,0,0,0,0⟩,.s 31 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.f ⟨4,43,0,0,0,0,0,0,3⟩,.s 31 3]⟩,
⟨5,0,8,6,[[.f ⟨4,42,0,0,0,0,0,0,0⟩,.s 30 0],[.s 6 0,.s 6 0],[.f ⟨4,44,0,0,0,0,0,0,0⟩,.s 32 0],[.s 20 0,.s 20 0],[.f ⟨4,46,0,0,0,0,0,0,0⟩,.s 34 0],[.s 10 0,.s 10 0]],[.f ⟨4,42,0,0,0,0,0,0,5⟩,.s 30 5]⟩,
⟨5,0,9,8,[[.f ⟨4,43,0,0,0,0,0,0,0⟩,.s 31 0],[.s 7 0,.s 7 0],[.f ⟨4,45,0,0,0,0,0,0,0⟩,.s 33 0],[.s 21 0,.s 21 0],[.f ⟨4,47,0,0,0,0,0,0,0⟩,.s 35 0],[.s 11 0,.s 11 0]],[.f ⟨4,45,0,0,0,0,0,0,3⟩,.s 33 3]⟩,
⟨5,0,10,7,[[.s 8 0,.s 8 0],[.s 20 0,.s 20 0],[.f ⟨4,46,0,0,0,0,0,0,0⟩,.s 34 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0]],[.s 8 5,.s 8 5]⟩,
⟨5,0,11,8,[[.s 9 0,.s 9 0],[.s 21 0,.s 21 0],[.s 10 0,.s 10 0],[.f ⟨4,47,0,0,0,0,0,0,0⟩,.s 35 0],[.s 23 0,.s 23 0]],[.s 10 4,.s 10 4]⟩,
⟨6,0,0,9,[[.s 0 0,.s 0 0],[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.f ⟨18,15,0,0,0,0,0,0,0⟩,.f ⟨18,15,1,0,1,0,0,0,0⟩]],[.s 0 1,.s 0 1]⟩,
⟨6,0,1,8,[[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.s 25 0,.s 25 0],[.s 14 0,.s 14 0]],[.s 1 2,.s 1 2]⟩,
⟨6,0,2,7,[[.s 13 0,.s 13 0],[.s 2 0,.s 2 0],[.s 26 0,.s 26 0],[.s 16 0,.s 16 0]],[.s 2 2,.s 2 2]⟩,
⟨6,0,3,11,[[.f ⟨21,0,0,0,0,0,0,0,0⟩,.f ⟨21,0,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 27 0,.s 27 0],[.s 17 0,.s 17 0]],[.s 3 2,.s 3 2]⟩,
⟨6,0,4,6,[[.s 14 0,.s 14 0],[.s 4 0,.s 4 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 18 0,.s 18 0]],[.s 4 2,.s 4 2]⟩,
⟨6,0,5,10,[[.s 15 0,.s 15 0],[.s 5 0,.s 5 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 19 0,.s 19 0]],[.s 5 2,.s 5 2]⟩,
⟨6,0,6,7,[[.s 16 0,.s 16 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.s 32 0,.s 32 0]],[.s 16 4,.s 16 4]⟩,
⟨6,0,7,10,[[.s 17 0,.s 17 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.s 33 0,.s 33 0]],[.s 7 3,.s 7 3]⟩,
⟨6,0,8,7,[[.s 6 0,.s 6 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 22 0,.s 22 0]],[.s 6 5,.s 6 5]⟩,
⟨6,0,9,9,[[.s 7 0,.s 7 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 33 0,.s 33 0],[.s 11 0,.s 11 0],[.s 23 0,.s 23 0]],[.s 9 3,.s 9 3]⟩,
⟨6,0,10,8,[[.s 20 0,.s 20 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0]],[.s 20 5,.s 20 5]⟩,
⟨6,0,11,9,[[.s 21 0,.s 21 0],[.s 33 0,.s 33 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0],[.s 35 0,.s 35 0]],[.s 22 4,.s 22 4]⟩,
⟨7,0,0,10,[[.s 12 0,.s 12 0],[.s 0 0,.s 0 0],[.s 25 0,.s 25 0],[.f ⟨18,27,0,0,0,0,0,0,0⟩,.f ⟨18,27,1,0,1,0,0,0,0⟩]],[.s 12 1,.s 12 1]⟩,
⟨7,0,1,9,[[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.s 1 0,.s 1 0],[.s 26 0,.s 26 0]],[.s 13 2,.s 13 2]⟩,
⟨7,0,2,8,[[.s 25 0,.s 25 0],[.s 14 0,.s 14 0],[.s 2 0,.s 2 0],[.s 28 0,.s 28 0]],[.s 14 2,.s 14 2]⟩,
⟨7,0,3,12,[[.f ⟨21,12,0,0,0,0,0,0,0⟩,.f ⟨21,12,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 3 0,.s 3 0],[.s 29 0,.s 29 0]],[.s 15 2,.s 15 2]⟩,
⟨7,0,4,7,[[.s 26 0,.s 26 0],[.s 16 0,.s 16 0],[.s 4 0,.s 4 0],[.s 18 0,.s 18 0],[.s 30 0,.s 30 0]],[.s 16 2,.s 16 2]⟩,
⟨7,0,5,11,[[.s 27 0,.s 27 0],[.s 17 0,.s 17 0],[.s 5 0,.s 5 0],[.s 19 0,.s 19 0],[.s 31 0,.s 31 0]],[.s 17 2,.s 17 2]⟩,
⟨7,0,6,8,[[.s 28 0,.s 28 0],[.s 4 0,.s 4 0],[.s 18 0,.s 18 0],[.s 6 0,.s 6 0],[.s 32 0,.s 32 0],[.s 8 0,.s 8 0]],[.s 28 4,.s 28 4]⟩,
⟨7,0,7,11,[[.s 29 0,.s 29 0],[.s 5 0,.s 5 0],[.s 19 0,.s 19 0],[.s 7 0,.s 7 0],[.s 33 0,.s 33 0],[.s 9 0,.s 9 0]],[.s 19 3,.s 19 3]⟩,
⟨7,0,8,8,[[.s 18 0,.s 18 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.s 8 0,.s 8 0],[.s 22 0,.s 22 0],[.s 34 0,.s 34 0]],[.s 18 5,.s 18 5]⟩,
⟨7,0,9,10,[[.s 19 0,.s 19 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.s 9 0,.s 9 0],[.s 23 0,.s 23 0],[.s 35 0,.s 35 0]],[.s 21 3,.s 21 3]⟩,
⟨7,0,10,9,[[.s 32 0,.s 32 0],[.s 8 0,.s 8 0],[.s 22 0,.s 22 0],[.s 10 0,.s 10 0],[.s 35 0,.s 35 0]],[.s 32 5,.s 32 5]⟩,
⟨7,0,11,10,[[.s 33 0,.s 33 0],[.s 9 0,.s 9 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0],[.s 11 0,.s 11 0]],[.s 34 4,.s 34 4]⟩]⟩,
⟨0,0,0,0,0,[(-1,3,0),(1,-3,0),(3,1,1),(-3,-1,-10)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨3,1,0,9,[[.f ⟨24,0,0,0,0,0,0,0,0⟩],[.f ⟨20,0,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨4,27,0,0,0,0,0,0,0⟩]],[.f ⟨4,27,0,0,0,0,0,0,0⟩]⟩,
⟨3,1,1,10,[[.s 0 0],[.f ⟨24,1,0,0,0,0,0,0,0⟩],[.f ⟨20,1,0,0,0,0,0,0,0⟩],[.s 2 0]],[.s 0 2]⟩,
⟨3,1,2,11,[[.s 1 0],[.f ⟨24,2,0,0,0,0,0,0,0⟩],[.f ⟨20,2,0,0,0,0,0,0,0⟩],[.s 4 0]],[.s 1 3]⟩,
⟨3,1,3,20,[[.f ⟨26,240,0,0,0,0,0,0,0⟩],[.f ⟨24,3,0,0,0,0,0,0,0⟩],[.f ⟨20,3,0,0,0,0,0,0,0⟩],[.s 5 0]],[.s 5 0]⟩,
⟨3,1,4,12,[[.s 2 0],[.f ⟨24,4,0,0,0,0,0,0,0⟩],[.f ⟨20,4,0,0,0,0,0,0,0⟩],[.f ⟨24,6,0,0,0,0,0,0,0⟩],[.s 6 0]],[.s 2 3]⟩,
⟨3,1,5,19,[[.s 3 0],[.f ⟨24,5,0,0,0,0,0,0,0⟩],[.f ⟨20,5,0,0,0,0,0,0,0⟩],[.f ⟨24,7,0,0,0,0,0,0,0⟩],[.s 7 0]],[.f ⟨24,7,0,0,0,0,0,0,1⟩]⟩,
⟨3,1,6,13,[[.s 4 0],[.f ⟨20,4,0,0,0,0,0,0,0⟩],[.f ⟨24,6,0,0,0,0,0,0,0⟩],[.f ⟨20,6,0,0,0,0,0,0,0⟩],[.s 8 0],[.f ⟨20,8,0,0,0,0,0,0,0⟩]],[.s 4 4]⟩,
⟨3,1,7,18,[[.s 5 0],[.f ⟨20,5,0,0,0,0,0,0,0⟩],[.f ⟨24,7,0,0,0,0,0,0,0⟩],[.f ⟨20,7,0,0,0,0,0,0,0⟩],[.s 9 0],[.f ⟨20,9,0,0,0,0,0,0,0⟩]],[.s 9 1]⟩,
⟨3,1,8,14,[[.f ⟨24,6,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨24,8,0,0,0,0,0,0,0⟩],[.f ⟨20,8,0,0,0,0,0,0,0⟩],[.f ⟨24,10,0,0,0,0,0,0,0⟩],[.s 10 0]],[.f ⟨24,6,0,0,0,0,0,0,5⟩]⟩,
⟨3,1,9,17,[[.f ⟨24,7,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨24,9,0,0,0,0,0,0,0⟩],[.f ⟨20,9,0,0,0,0,0,0,0⟩],[.f ⟨24,11,0,0,0,0,0,0,0⟩],[.s 11 0]],[.f ⟨24,11,0,0,0,0,0,0,1⟩]⟩,
⟨3,1,10,15,[[.s 8 0],[.f ⟨20,8,0,0,0,0,0,0,0⟩],[.f ⟨24,10,0,0,0,0,0,0,0⟩],[.f ⟨20,10,0,0,0,0,0,0,0⟩],[.s 11 0]],[.s 8 5]⟩,
⟨3,1,11,16,[[.s 9 0],[.f ⟨20,9,0,0,0,0,0,0,0⟩],[.s 10 0],[.f ⟨24,11,0,0,0,0,0,0,0⟩],[.f ⟨20,11,0,0,0,0,0,0,0⟩]],[.s 10 4]⟩]⟩,
⟨1,6,2,0,0,[(-1,3,0),(1,-3,0),(3,1,20)],3,1,20,20,0,0,0,0,24,0,0,0,
[⟨6,2,0,21,[[.f ⟨24,12,0,0,0,0,0,0,0⟩,.f ⟨24,12,1,0,1,0,0,0,0⟩],[.f ⟨22,0,0,0,0,0,0,0,0⟩,.f ⟨22,0,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨21,3,0,0,0,0,0,0,0⟩,.f ⟨23,39,0,0,0,1,0,0,0⟩]],[.f ⟨21,3,0,0,0,0,0,0,0⟩,.f ⟨23,39,0,0,0,1,0,0,0⟩]⟩,
⟨6,2,1,22,[[.s 0 0,.s 0 0],[.f ⟨24,13,0,0,0,0,0,0,0⟩,.f ⟨24,13,1,0,1,0,0,0,0⟩],[.f ⟨22,1,0,0,0,0,0,0,0⟩,.f ⟨22,1,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 0 2,.s 0 2]⟩,
⟨6,2,2,23,[[.s 1 0,.s 1 0],[.f ⟨24,14,0,0,0,0,0,0,0⟩,.f ⟨24,14,1,0,1,0,0,0,0⟩],[.f ⟨22,2,0,0,0,0,0,0,0⟩,.f ⟨22,2,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0]],[.s 1 3,.s 1 3]⟩,
⟨6,2,3,32,[[.f ⟨26,120,0,0,1,0,0,0,0⟩,.f ⟨26,120,1,0,2,0,0,0,0⟩],[.f ⟨24,15,0,0,0,0,0,0,0⟩,.f ⟨24,15,1,0,1,0,0,0,0⟩],[.f ⟨22,3,0,0,0,0,0,0,0⟩,.f ⟨22,3,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0]],[.s 5 0,.s 5 0]⟩,
⟨6,2,4,24,[[.s 2 0,.s 2 0],[.f ⟨24,16,0,0,0,0,0,0,0⟩,.f ⟨24,16,1,0,1,0,0,0,0⟩],[.f ⟨22,4,0,0,0,0,0,0,0⟩,.f ⟨22,4,1,0,1,0,0,0,0⟩],[.f ⟨24,18,0,0,0,0,0,0,0⟩,.f ⟨24,18,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨6,2,5,31,[[.s 3 0,.s 3 0],[.f ⟨24,17,0,0,0,0,0,0,0⟩,.f ⟨24,17,1,0,1,0,0,0,0⟩],[.f ⟨22,5,0,0,0,0,0,0,0⟩,.f ⟨22,5,1,0,1,0,0,0,0⟩],[.f ⟨24,19,0,0,0,0,0,0,0⟩,.f ⟨24,19,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.f ⟨24,19,0,0,0,0,0,0,1⟩,.f ⟨24,19,1,0,1,0,0,0,1⟩]⟩,
⟨6,2,6,25,[[.s 4 0,.s 4 0],[.f ⟨22,4,0,0,0,0,0,0,0⟩,.f ⟨22,4,1,0,1,0,0,0,0⟩],[.f ⟨24,18,0,0,0,0,0,0,0⟩,.f ⟨24,18,1,0,1,0,0,0,0⟩],[.f ⟨22,6,0,0,0,0,0,0,0⟩,.f ⟨22,6,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.f ⟨22,8,0,0,0,0,0,0,0⟩,.f ⟨22,8,1,0,1,0,0,0,0⟩]],[.s 4 4,.s 4 4]⟩,
⟨6,2,7,30,[[.s 5 0,.s 5 0],[.f ⟨22,5,0,0,0,0,0,0,0⟩,.f ⟨22,5,1,0,1,0,0,0,0⟩],[.f ⟨24,19,0,0,0,0,0,0,0⟩,.f ⟨24,19,1,0,1,0,0,0,0⟩],[.f ⟨22,7,0,0,0,0,0,0,0⟩,.f ⟨22,7,1,0,1,0,0,0,0⟩],[.s 9 0,.s 9 0],[.f ⟨22,9,0,0,0,0,0,0,0⟩,.f ⟨22,9,1,0,1,0,0,0,0⟩]],[.s 9 1,.s 9 1]⟩,
⟨6,2,8,26,[[.f ⟨24,18,0,0,0,0,0,0,0⟩,.f ⟨24,18,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.f ⟨24,20,0,0,0,0,0,0,0⟩,.f ⟨24,20,1,0,1,0,0,0,0⟩],[.f ⟨22,8,0,0,0,0,0,0,0⟩,.f ⟨22,8,1,0,1,0,0,0,0⟩],[.f ⟨24,22,0,0,0,0,0,0,0⟩,.f ⟨24,22,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0]],[.f ⟨24,18,0,0,0,0,0,0,5⟩,.f ⟨24,18,1,0,1,0,0,0,5⟩]⟩,
⟨6,2,9,29,[[.f ⟨24,19,0,0,0,0,0,0,0⟩,.f ⟨24,19,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨24,21,0,0,0,0,0,0,0⟩,.f ⟨24,21,1,0,1,0,0,0,0⟩],[.f ⟨22,9,0,0,0,0,0,0,0⟩,.f ⟨22,9,1,0,1,0,0,0,0⟩],[.f ⟨24,23,0,0,0,0,0,0,0⟩,.f ⟨24,23,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨24,23,0,0,0,0,0,0,1⟩,.f ⟨24,23,1,0,1,0,0,0,1⟩]⟩,
⟨6,2,10,27,[[.s 8 0,.s 8 0],[.f ⟨22,8,0,0,0,0,0,0,0⟩,.f ⟨22,8,1,0,1,0,0,0,0⟩],[.f ⟨24,22,0,0,0,0,0,0,0⟩,.f ⟨24,22,1,0,1,0,0,0,0⟩],[.f ⟨22,10,0,0,0,0,0,0,0⟩,.f ⟨22,10,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.s 8 5,.s 8 5]⟩,
⟨6,2,11,28,[[.s 9 0,.s 9 0],[.f ⟨22,9,0,0,0,0,0,0,0⟩,.f ⟨22,9,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0],[.f ⟨24,23,0,0,0,0,0,0,0⟩,.f ⟨24,23,1,0,1,0,0,0,0⟩],[.f ⟨22,11,0,0,0,0,0,0,0⟩,.f ⟨22,11,1,0,1,0,0,0,0⟩]],[.s 10 4,.s 10 4]⟩,
⟨9,3,0,33,[[.f ⟨24,0,0,0,1,0,0,0,0⟩,.f ⟨24,0,1,0,2,0,0,0,0⟩],[.f ⟨22,24,0,0,0,0,0,0,0⟩,.f ⟨22,24,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.f ⟨23,3,0,0,0,0,0,0,0⟩,.f ⟨23,3,0,0,0,1,0,1,0⟩]],[.f ⟨23,3,0,0,0,0,0,0,0⟩,.f ⟨23,3,0,0,0,1,0,1,0⟩]⟩,
⟨9,3,1,34,[[.s 12 0,.s 12 0],[.f ⟨24,1,0,0,1,0,0,0,0⟩,.f ⟨24,1,1,0,2,0,0,0,0⟩],[.f ⟨22,25,0,0,0,0,0,0,0⟩,.f ⟨22,25,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0]],[.s 12 2,.s 12 2]⟩,
⟨9,3,2,35,[[.s 13 0,.s 13 0],[.f ⟨24,2,0,0,1,0,0,0,0⟩,.f ⟨24,2,1,0,2,0,0,0,0⟩],[.f ⟨22,26,0,0,0,0,0,0,0⟩,.f ⟨22,26,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0]],[.s 13 3,.s 13 3]⟩,
⟨9,3,3,44,[[.f ⟨26,240,0,0,1,0,0,0,0⟩,.f ⟨26,240,1,0,2,0,0,0,0⟩],[.f ⟨24,3,0,0,1,0,0,0,0⟩,.f ⟨24,3,1,0,2,0,0,0,0⟩],[.f ⟨22,27,0,0,0,0,0,0,0⟩,.f ⟨22,27,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0]],[.s 17 0,.s 17 0]⟩,
⟨9,3,4,36,[[.s 14 0,.s 14 0],[.f ⟨24,4,0,0,1,0,0,0,0⟩,.f ⟨24,4,1,0,2,0,0,0,0⟩],[.f ⟨22,28,0,0,0,0,0,0,0⟩,.f ⟨22,28,1,0,1,0,0,0,0⟩],[.f ⟨24,6,0,0,1,0,0,0,0⟩,.f ⟨24,6,1,0,2,0,0,0,0⟩],[.s 18 0,.s 18 0]],[.s 14 3,.s 14 3]⟩,
⟨9,3,5,43,[[.s 15 0,.s 15 0],[.f ⟨24,5,0,0,1,0,0,0,0⟩,.f ⟨24,5,1,0,2,0,0,0,0⟩],[.f ⟨22,29,0,0,0,0,0,0,0⟩,.f ⟨22,29,1,0,1,0,0,0,0⟩],[.f ⟨24,7,0,0,1,0,0,0,0⟩,.f ⟨24,7,1,0,2,0,0,0,0⟩],[.s 19 0,.s 19 0]],[.f ⟨24,7,0,0,1,0,0,0,1⟩,.f ⟨24,7,1,0,2,0,0,0,1⟩]⟩,
⟨9,3,6,37,[[.s 16 0,.s 16 0],[.f ⟨22,28,0,0,0,0,0,0,0⟩,.f ⟨22,28,1,0,1,0,0,0,0⟩],[.f ⟨24,6,0,0,1,0,0,0,0⟩,.f ⟨24,6,1,0,2,0,0,0,0⟩],[.f ⟨22,30,0,0,0,0,0,0,0⟩,.f ⟨22,30,1,0,1,0,0,0,0⟩],[.s 20 0,.s 20 0],[.f ⟨22,32,0,0,0,0,0,0,0⟩,.f ⟨22,32,1,0,1,0,0,0,0⟩]],[.s 16 4,.s 16 4]⟩,
⟨9,3,7,42,[[.s 17 0,.s 17 0],[.f ⟨22,29,0,0,0,0,0,0,0⟩,.f ⟨22,29,1,0,1,0,0,0,0⟩],[.f ⟨24,7,0,0,1,0,0,0,0⟩,.f ⟨24,7,1,0,2,0,0,0,0⟩],[.f ⟨22,31,0,0,0,0,0,0,0⟩,.f ⟨22,31,1,0,1,0,0,0,0⟩],[.s 21 0,.s 21 0],[.f ⟨22,33,0,0,0,0,0,0,0⟩,.f ⟨22,33,1,0,1,0,0,0,0⟩]],[.s 21 1,.s 21 1]⟩,
⟨9,3,8,38,[[.f ⟨24,6,0,0,1,0,0,0,0⟩,.f ⟨24,6,1,0,2,0,0,0,0⟩],[.s 18 0,.s 18 0],[.f ⟨24,8,0,0,1,0,0,0,0⟩,.f ⟨24,8,1,0,2,0,0,0,0⟩],[.f ⟨22,32,0,0,0,0,0,0,0⟩,.f ⟨22,32,1,0,1,0,0,0,0⟩],[.f ⟨24,10,0,0,1,0,0,0,0⟩,.f ⟨24,10,1,0,2,0,0,0,0⟩],[.s 22 0,.s 22 0]],[.f ⟨24,6,0,0,1,0,0,0,5⟩,.f ⟨24,6,1,0,2,0,0,0,5⟩]⟩,
⟨9,3,9,41,[[.f ⟨24,7,0,0,1,0,0,0,0⟩,.f ⟨24,7,1,0,2,0,0,0,0⟩],[.s 19 0,.s 19 0],[.f ⟨24,9,0,0,1,0,0,0,0⟩,.f ⟨24,9,1,0,2,0,0,0,0⟩],[.f ⟨22,33,0,0,0,0,0,0,0⟩,.f ⟨22,33,1,0,1,0,0,0,0⟩],[.f ⟨24,11,0,0,1,0,0,0,0⟩,.f ⟨24,11,1,0,2,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.f ⟨24,11,0,0,1,0,0,0,1⟩,.f ⟨24,11,1,0,2,0,0,0,1⟩]⟩,
⟨9,3,10,39,[[.s 20 0,.s 20 0],[.f ⟨22,32,0,0,0,0,0,0,0⟩,.f ⟨22,32,1,0,1,0,0,0,0⟩],[.f ⟨24,10,0,0,1,0,0,0,0⟩,.f ⟨24,10,1,0,2,0,0,0,0⟩],[.f ⟨22,34,0,0,0,0,0,0,0⟩,.f ⟨22,34,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.s 20 5,.s 20 5]⟩,
⟨9,3,11,40,[[.s 21 0,.s 21 0],[.f ⟨22,33,0,0,0,0,0,0,0⟩,.f ⟨22,33,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.f ⟨24,11,0,0,1,0,0,0,0⟩,.f ⟨24,11,1,0,2,0,0,0,0⟩],[.f ⟨22,35,0,0,0,0,0,0,0⟩,.f ⟨22,35,1,0,1,0,0,0,0⟩]],[.s 22 4,.s 22 4]⟩]⟩,
⟨0,0,0,0,0,[(-1,-3,0),(1,3,0),(-3,1,1),(3,-1,-10)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨-3,1,0,9,[[.f ⟨27,12,0,0,0,0,0,0,0⟩],[.f ⟨25,12,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨10,15,0,0,0,0,0,0,0⟩]],[.f ⟨10,15,0,0,0,0,0,0,0⟩]⟩,
⟨-3,1,1,10,[[.s 0 0],[.f ⟨27,13,0,0,0,0,0,0,0⟩],[.f ⟨25,13,0,0,0,0,0,0,0⟩],[.s 2 0]],[.s 0 2]⟩,
⟨-3,1,2,11,[[.s 1 0],[.f ⟨27,14,0,0,0,0,0,0,0⟩],[.f ⟨25,14,0,0,0,0,0,0,0⟩],[.s 4 0]],[.s 1 3]⟩,
⟨-3,1,3,20,[[.f ⟨26,24,0,0,0,0,0,0,0⟩],[.f ⟨27,15,0,0,0,0,0,0,0⟩],[.f ⟨25,15,0,0,0,0,0,0,0⟩],[.s 5 0]],[.s 5 0]⟩,
⟨-3,1,4,12,[[.s 2 0],[.f ⟨27,16,0,0,0,0,0,0,0⟩],[.f ⟨25,16,0,0,0,0,0,0,0⟩],[.f ⟨27,18,0,0,0,0,0,0,0⟩],[.s 6 0]],[.s 2 3]⟩,
⟨-3,1,5,19,[[.s 3 0],[.f ⟨27,17,0,0,0,0,0,0,0⟩],[.f ⟨25,17,0,0,0,0,0,0,0⟩],[.f ⟨27,19,0,0,0,0,0,0,0⟩],[.s 7 0]],[.f ⟨27,19,0,0,0,0,0,0,1⟩]⟩,
⟨-3,1,6,13,[[.s 4 0],[.f ⟨25,16,0,0,0,0,0,0,0⟩],[.f ⟨27,18,0,0,0,0,0,0,0⟩],[.f ⟨25,18,0,0,0,0,0,0,0⟩],[.s 8 0],[.f ⟨25,20,0,0,0,0,0,0,0⟩]],[.s 4 4]⟩,
⟨-3,1,7,18,[[.s 5 0],[.f ⟨25,17,0,0,0,0,0,0,0⟩],[.f ⟨27,19,0,0,0,0,0,0,0⟩],[.f ⟨25,19,0,0,0,0,0,0,0⟩],[.s 9 0],[.f ⟨25,21,0,0,0,0,0,0,0⟩]],[.s 9 1]⟩,
⟨-3,1,8,14,[[.f ⟨27,18,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨27,20,0,0,0,0,0,0,0⟩],[.f ⟨25,20,0,0,0,0,0,0,0⟩],[.f ⟨27,22,0,0,0,0,0,0,0⟩],[.s 10 0]],[.f ⟨27,18,0,0,0,0,0,0,5⟩]⟩,
⟨-3,1,9,17,[[.f ⟨27,19,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨27,21,0,0,0,0,0,0,0⟩],[.f ⟨25,21,0,0,0,0,0,0,0⟩],[.f ⟨27,23,0,0,0,0,0,0,0⟩],[.s 11 0]],[.f ⟨27,23,0,0,0,0,0,0,1⟩]⟩,
⟨-3,1,10,15,[[.s 8 0],[.f ⟨25,20,0,0,0,0,0,0,0⟩],[.f ⟨27,22,0,0,0,0,0,0,0⟩],[.f ⟨25,22,0,0,0,0,0,0,0⟩],[.s 11 0]],[.s 8 5]⟩,
⟨-3,1,11,16,[[.s 9 0],[.f ⟨25,21,0,0,0,0,0,0,0⟩],[.s 10 0],[.f ⟨27,23,0,0,0,0,0,0,0⟩],[.f ⟨25,23,0,0,0,0,0,0,0⟩]],[.s 10 4]⟩]⟩,
⟨1,-6,2,0,0,[(-1,-3,0),(1,3,0),(-3,1,20)],-3,1,20,20,0,0,0,0,24,0,0,0,
[⟨-9,3,0,33,[[.f ⟨28,12,0,0,0,0,0,0,0⟩,.f ⟨28,12,1,0,1,0,0,0,0⟩],[.f ⟨25,12,0,0,1,0,0,0,0⟩,.f ⟨25,12,1,0,2,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨30,63,0,0,0,0,0,0,0⟩,.f ⟨30,63,1,0,1,0,0,0,0⟩]],[.f ⟨30,63,0,0,0,0,0,0,0⟩,.f ⟨30,63,1,0,1,0,0,0,0⟩]⟩,
⟨-9,3,1,34,[[.s 0 0,.s 0 0],[.f ⟨28,13,0,0,0,0,0,0,0⟩,.f ⟨28,13,1,0,1,0,0,0,0⟩],[.f ⟨25,13,0,0,1,0,0,0,0⟩,.f ⟨25,13,1,0,2,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 0 2,.s 0 2]⟩,
⟨-9,3,2,35,[[.s 1 0,.s 1 0],[.f ⟨28,14,0,0,0,0,0,0,0⟩,.f ⟨28,14,1,0,1,0,0,0,0⟩],[.f ⟨25,14,0,0,1,0,0,0,0⟩,.f ⟨25,14,1,0,2,0,0,0,0⟩],[.s 4 0,.s 4 0]],[.s 1 3,.s 1 3]⟩,
⟨-9,3,3,44,[[.f ⟨26,24,0,0,0,0,0,1,0⟩,.f ⟨26,24,0,0,0,1,0,2,0⟩],[.f ⟨28,15,0,0,0,0,0,0,0⟩,.f ⟨28,15,1,0,1,0,0,0,0⟩],[.f ⟨25,15,0,0,1,0,0,0,0⟩,.f ⟨25,15,1,0,2,0,0,0,0⟩],[.s 5 0,.s 5 0]],[.s 5 0,.s 5 0]⟩,
⟨-9,3,4,36,[[.s 2 0,.s 2 0],[.f ⟨28,16,0,0,0,0,0,0,0⟩,.f ⟨28,16,1,0,1,0,0,0,0⟩],[.f ⟨25,16,0,0,1,0,0,0,0⟩,.f ⟨25,16,1,0,2,0,0,0,0⟩],[.f ⟨28,18,0,0,0,0,0,0,0⟩,.f ⟨28,18,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨-9,3,5,43,[[.s 3 0,.s 3 0],[.f ⟨28,17,0,0,0,0,0,0,0⟩,.f ⟨28,17,1,0,1,0,0,0,0⟩],[.f ⟨25,17,0,0,1,0,0,0,0⟩,.f ⟨25,17,1,0,2,0,0,0,0⟩],[.f ⟨28,19,0,0,0,0,0,0,0⟩,.f ⟨28,19,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.f ⟨28,19,0,0,0,0,0,0,1⟩,.f ⟨28,19,1,0,1,0,0,0,1⟩]⟩,
⟨-9,3,6,37,[[.s 4 0,.s 4 0],[.f ⟨25,16,0,0,1,0,0,0,0⟩,.f ⟨25,16,1,0,2,0,0,0,0⟩],[.f ⟨28,18,0,0,0,0,0,0,0⟩,.f ⟨28,18,1,0,1,0,0,0,0⟩],[.f ⟨25,18,0,0,1,0,0,0,0⟩,.f ⟨25,18,1,0,2,0,0,0,0⟩],[.s 8 0,.s 8 0],[.f ⟨25,20,0,0,1,0,0,0,0⟩,.f ⟨25,20,1,0,2,0,0,0,0⟩]],[.s 4 4,.s 4 4]⟩,
⟨-9,3,7,42,[[.s 5 0,.s 5 0],[.f ⟨25,17,0,0,1,0,0,0,0⟩,.f ⟨25,17,1,0,2,0,0,0,0⟩],[.f ⟨28,19,0,0,0,0,0,0,0⟩,.f ⟨28,19,1,0,1,0,0,0,0⟩],[.f ⟨25,19,0,0,1,0,0,0,0⟩,.f ⟨25,19,1,0,2,0,0,0,0⟩],[.s 9 0,.s 9 0],[.f ⟨25,21,0,0,1,0,0,0,0⟩,.f ⟨25,21,1,0,2,0,0,0,0⟩]],[.s 9 1,.s 9 1]⟩,
⟨-9,3,8,38,[[.f ⟨28,18,0,0,0,0,0,0,0⟩,.f ⟨28,18,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.f ⟨28,20,0,0,0,0,0,0,0⟩,.f ⟨28,20,1,0,1,0,0,0,0⟩],[.f ⟨25,20,0,0,1,0,0,0,0⟩,.f ⟨25,20,1,0,2,0,0,0,0⟩],[.f ⟨28,22,0,0,0,0,0,0,0⟩,.f ⟨28,22,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0]],[.f ⟨28,18,0,0,0,0,0,0,5⟩,.f ⟨28,18,1,0,1,0,0,0,5⟩]⟩,
⟨-9,3,9,41,[[.f ⟨28,19,0,0,0,0,0,0,0⟩,.f ⟨28,19,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨28,21,0,0,0,0,0,0,0⟩,.f ⟨28,21,1,0,1,0,0,0,0⟩],[.f ⟨25,21,0,0,1,0,0,0,0⟩,.f ⟨25,21,1,0,2,0,0,0,0⟩],[.f ⟨28,23,0,0,0,0,0,0,0⟩,.f ⟨28,23,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨28,23,0,0,0,0,0,0,1⟩,.f ⟨28,23,1,0,1,0,0,0,1⟩]⟩,
⟨-9,3,10,39,[[.s 8 0,.s 8 0],[.f ⟨25,20,0,0,1,0,0,0,0⟩,.f ⟨25,20,1,0,2,0,0,0,0⟩],[.f ⟨28,22,0,0,0,0,0,0,0⟩,.f ⟨28,22,1,0,1,0,0,0,0⟩],[.f ⟨25,22,0,0,1,0,0,0,0⟩,.f ⟨25,22,1,0,2,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.s 8 5,.s 8 5]⟩,
⟨-9,3,11,40,[[.s 9 0,.s 9 0],[.f ⟨25,21,0,0,1,0,0,0,0⟩,.f ⟨25,21,1,0,2,0,0,0,0⟩],[.s 10 0,.s 10 0],[.f ⟨28,23,0,0,0,0,0,0,0⟩,.f ⟨28,23,1,0,1,0,0,0,0⟩],[.f ⟨25,23,0,0,1,0,0,0,0⟩,.f ⟨25,23,1,0,2,0,0,0,0⟩]],[.s 10 4,.s 10 4]⟩,
⟨-6,2,0,21,[[.f ⟨28,36,0,0,0,0,0,0,0⟩,.f ⟨28,36,1,0,1,0,0,0,0⟩],[.f ⟨25,0,0,0,0,0,0,0,0⟩,.f ⟨25,0,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.f ⟨29,27,0,0,0,0,0,0,0⟩,.f ⟨30,27,1,0,0,0,0,0,0⟩]],[.f ⟨29,27,0,0,0,0,0,0,0⟩,.f ⟨30,27,1,0,0,0,0,0,0⟩]⟩,
⟨-6,2,1,22,[[.s 12 0,.s 12 0],[.f ⟨28,37,0,0,0,0,0,0,0⟩,.f ⟨28,37,1,0,1,0,0,0,0⟩],[.f ⟨25,1,0,0,0,0,0,0,0⟩,.f ⟨25,1,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0]],[.s 12 2,.s 12 2]⟩,
⟨-6,2,2,23,[[.s 13 0,.s 13 0],[.f ⟨28,38,0,0,0,0,0,0,0⟩,.f ⟨28,38,1,0,1,0,0,0,0⟩],[.f ⟨25,2,0,0,0,0,0,0,0⟩,.f ⟨25,2,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0]],[.s 13 3,.s 13 3]⟩,
⟨-6,2,3,32,[[.f ⟨26,120,0,0,0,0,0,1,0⟩,.f ⟨26,120,0,0,0,1,0,2,0⟩],[.f ⟨28,39,0,0,0,0,0,0,0⟩,.f ⟨28,39,1,0,1,0,0,0,0⟩],[.f ⟨25,3,0,0,0,0,0,0,0⟩,.f ⟨25,3,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0]],[.s 17 0,.s 17 0]⟩,
⟨-6,2,4,24,[[.s 14 0,.s 14 0],[.f ⟨28,40,0,0,0,0,0,0,0⟩,.f ⟨28,40,1,0,1,0,0,0,0⟩],[.f ⟨25,4,0,0,0,0,0,0,0⟩,.f ⟨25,4,1,0,1,0,0,0,0⟩],[.f ⟨28,42,0,0,0,0,0,0,0⟩,.f ⟨28,42,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0]],[.s 14 3,.s 14 3]⟩,
⟨-6,2,5,31,[[.s 15 0,.s 15 0],[.f ⟨28,41,0,0,0,0,0,0,0⟩,.f ⟨28,41,1,0,1,0,0,0,0⟩],[.f ⟨25,5,0,0,0,0,0,0,0⟩,.f ⟨25,5,1,0,1,0,0,0,0⟩],[.f ⟨28,43,0,0,0,0,0,0,0⟩,.f ⟨28,43,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0]],[.f ⟨28,43,0,0,0,0,0,0,1⟩,.f ⟨28,43,1,0,1,0,0,0,1⟩]⟩,
⟨-6,2,6,25,[[.s 16 0,.s 16 0],[.f ⟨25,4,0,0,0,0,0,0,0⟩,.f ⟨25,4,1,0,1,0,0,0,0⟩],[.f ⟨28,42,0,0,0,0,0,0,0⟩,.f ⟨28,42,1,0,1,0,0,0,0⟩],[.f ⟨25,6,0,0,0,0,0,0,0⟩,.f ⟨25,6,1,0,1,0,0,0,0⟩],[.s 20 0,.s 20 0],[.f ⟨25,8,0,0,0,0,0,0,0⟩,.f ⟨25,8,1,0,1,0,0,0,0⟩]],[.s 16 4,.s 16 4]⟩,
⟨-6,2,7,30,[[.s 17 0,.s 17 0],[.f ⟨25,5,0,0,0,0,0,0,0⟩,.f ⟨25,5,1,0,1,0,0,0,0⟩],[.f ⟨28,43,0,0,0,0,0,0,0⟩,.f ⟨28,43,1,0,1,0,0,0,0⟩],[.f ⟨25,7,0,0,0,0,0,0,0⟩,.f ⟨25,7,1,0,1,0,0,0,0⟩],[.s 21 0,.s 21 0],[.f ⟨25,9,0,0,0,0,0,0,0⟩,.f ⟨25,9,1,0,1,0,0,0,0⟩]],[.s 21 1,.s 21 1]⟩,
⟨-6,2,8,26,[[.f ⟨28,42,0,0,0,0,0,0,0⟩,.f ⟨28,42,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.f ⟨28,44,0,0,0,0,0,0,0⟩,.f ⟨28,44,1,0,1,0,0,0,0⟩],[.f ⟨25,8,0,0,0,0,0,0,0⟩,.f ⟨25,8,1,0,1,0,0,0,0⟩],[.f ⟨28,46,0,0,0,0,0,0,0⟩,.f ⟨28,46,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0]],[.f ⟨28,42,0,0,0,0,0,0,5⟩,.f ⟨28,42,1,0,1,0,0,0,5⟩]⟩,
⟨-6,2,9,29,[[.f ⟨28,43,0,0,0,0,0,0,0⟩,.f ⟨28,43,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.f ⟨28,45,0,0,0,0,0,0,0⟩,.f ⟨28,45,1,0,1,0,0,0,0⟩],[.f ⟨25,9,0,0,0,0,0,0,0⟩,.f ⟨25,9,1,0,1,0,0,0,0⟩],[.f ⟨28,47,0,0,0,0,0,0,0⟩,.f ⟨28,47,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.f ⟨28,47,0,0,0,0,0,0,1⟩,.f ⟨28,47,1,0,1,0,0,0,1⟩]⟩,
⟨-6,2,10,27,[[.s 20 0,.s 20 0],[.f ⟨25,8,0,0,0,0,0,0,0⟩,.f ⟨25,8,1,0,1,0,0,0,0⟩],[.f ⟨28,46,0,0,0,0,0,0,0⟩,.f ⟨28,46,1,0,1,0,0,0,0⟩],[.f ⟨25,10,0,0,0,0,0,0,0⟩,.f ⟨25,10,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.s 20 5,.s 20 5]⟩,
⟨-6,2,11,28,[[.s 21 0,.s 21 0],[.f ⟨25,9,0,0,0,0,0,0,0⟩,.f ⟨25,9,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.f ⟨28,47,0,0,0,0,0,0,0⟩,.f ⟨28,47,1,0,1,0,0,0,0⟩],[.f ⟨25,11,0,0,0,0,0,0,0⟩,.f ⟨25,11,1,0,1,0,0,0,0⟩]],[.s 22 4,.s 22 4]⟩]⟩,
⟨0,0,0,0,0,[(0,-1,0),(0,1,0),(-1,0,1),(1,0,-4)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨-4,0,0,7,[[.f ⟨11,24,0,0,0,0,0,0,0⟩],[.s 12 0],[.s 1 0],[.f ⟨31,27,0,0,0,0,0,0,0⟩]],[.s 12 0]⟩,
⟨-4,0,1,6,[[.s 0 0],[.f ⟨11,25,0,0,0,0,0,0,0⟩],[.s 13 0],[.s 2 0]],[.s 13 1]⟩,
⟨-4,0,2,5,[[.s 1 0],[.f ⟨11,26,0,0,0,0,0,0,0⟩],[.s 14 0],[.s 4 0]],[.s 14 1]⟩,
⟨-4,0,3,9,[[.f ⟨27,12,0,0,0,0,0,0,0⟩],[.f ⟨11,27,0,0,0,0,0,0,0⟩],[.s 15 0],[.s 5 0]],[.s 15 1]⟩,
⟨-4,0,4,4,[[.s 2 0],[.f ⟨11,28,0,0,0,0,0,0,0⟩],[.s 16 0],[.f ⟨11,30,0,0,0,0,0,0,0⟩],[.s 6 0]],[.s 16 1]⟩,
⟨-4,0,5,8,[[.s 3 0],[.f ⟨11,29,0,0,0,0,0,0,0⟩],[.s 17 0],[.f ⟨11,31,0,0,0,0,0,0,0⟩],[.s 7 0]],[.s 17 1]⟩,
⟨-4,0,6,4,[[.s 4 0],[.s 16 0],[.f ⟨11,30,0,0,0,0,0,0,0⟩],[.s 18 0],[.s 8 0],[.s 20 0]],[.s 16 3]⟩,
⟨-4,0,7,7,[[.s 5 0],[.s 17 0],[.f ⟨11,31,0,0,0,0,0,0,0⟩],[.s 19 0],[.s 9 0],[.s 21 0]],[.s 19 2]⟩,
⟨-4,0,8,5,[[.f ⟨11,30,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨11,32,0,0,0,0,0,0,0⟩],[.s 20 0],[.f ⟨11,34,0,0,0,0,0,0,0⟩],[.s 10 0]],[.s 6 4]⟩,
⟨-4,0,9,7,[[.f ⟨11,31,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨11,33,0,0,0,0,0,0,0⟩],[.s 21 0],[.f ⟨11,35,0,0,0,0,0,0,0⟩],[.s 11 0]],[.s 21 2]⟩,
⟨-4,0,10,5,[[.s 8 0],[.s 20 0],[.f ⟨11,34,0,0,0,0,0,0,0⟩],[.s 22 0],[.s 11 0]],[.s 20 4]⟩,
⟨-4,0,11,6,[[.s 9 0],[.s 21 0],[.s 10 0],[.f ⟨11,35,0,0,0,0,0,0,0⟩],[.s 23 0]],[.s 10 4]⟩,
⟨-3,0,0,6,[[.s 0 0],[.s 24 0],[.s 13 0],[.f ⟨1,3,0,0,0,0,0,0,0⟩]],[.s 24 0]⟩,
⟨-3,0,1,5,[[.s 12 0],[.s 1 0],[.s 25 0],[.s 14 0]],[.s 25 1]⟩,
⟨-3,0,2,4,[[.s 13 0],[.s 2 0],[.s 26 0],[.s 16 0]],[.s 26 1]⟩,
⟨-3,0,3,8,[[.f ⟨8,0,0,0,0,0,0,0,0⟩],[.s 3 0],[.s 27 0],[.s 17 0]],[.s 17 0]⟩,
⟨-3,0,4,3,[[.s 14 0],[.s 4 0],[.s 28 0],[.s 6 0],[.s 18 0]],[.s 28 1]⟩,
⟨-3,0,5,7,[[.s 15 0],[.s 5 0],[.s 29 0],[.s 7 0],[.s 19 0]],[.s 19 0]⟩,
⟨-3,0,6,3,[[.s 16 0],[.s 28 0],[.s 6 0],[.s 30 0],[.s 20 0],[.s 32 0]],[.s 28 3]⟩,
⟨-3,0,7,6,[[.s 17 0],[.s 29 0],[.s 7 0],[.s 31 0],[.s 21 0],[.s 33 0]],[.s 33 0]⟩,
⟨-3,0,8,4,[[.s 6 0],[.s 18 0],[.s 8 0],[.s 32 0],[.s 10 0],[.s 22 0]],[.s 18 4]⟩,
⟨-3,0,9,6,[[.s 7 0],[.s 19 0],[.s 9 0],[.s 33 0],[.s 11 0],[.s 23 0]],[.s 33 2]⟩,
⟨-3,0,10,4,[[.s 20 0],[.s 32 0],[.s 10 0],[.s 34 0],[.s 23 0]],[.s 32 4]⟩,
⟨-3,0,11,5,[[.s 21 0],[.s 33 0],[.s 22 0],[.s 11 0],[.s 35 0]],[.s 22 4]⟩,
⟨-2,0,0,5,[[.s 12 0],[.s 36 0],[.s 25 0],[.f ⟨13,15,0,0,0,0,0,0,0⟩]],[.s 36 0]⟩,
⟨-2,0,1,4,[[.s 24 0],[.s 13 0],[.s 37 0],[.s 26 0]],[.s 37 1]⟩,
⟨-2,0,2,3,[[.s 25 0],[.s 14 0],[.s 38 0],[.s 28 0]],[.s 38 1]⟩,
⟨-2,0,3,8,[[.f ⟨25,12,0,0,0,0,0,0,0⟩],[.s 15 0],[.s 39 0],[.s 29 0]],[.s 29 0]⟩,
⟨-2,0,4,2,[[.s 26 0],[.s 16 0],[.s 40 0],[.s 18 0],[.s 30 0]],[.s 40 1]⟩,
⟨-2,0,5,7,[[.s 27 0],[.s 17 0],[.s 41 0],[.s 19 0],[.s 31 0]],[.s 19 1]⟩,
⟨-2,0,6,2,[[.s 28 0],[.s 40 0],[.s 18 0],[.s 42 0],[.s 32 0],[.s 44 0]],[.s 40 3]⟩,
⟨-2,0,7,6,[[.s 29 0],[.s 41 0],[.s 19 0],[.s 43 0],[.s 33 0],[.s 45 0]],[.s 33 1]⟩,
⟨-2,0,8,3,[[.s 18 0],[.s 30 0],[.s 20 0],[.s 44 0],[.s 22 0],[.s 34 0]],[.s 30 4]⟩,
⟨-2,0,9,5,[[.s 19 0],[.s 31 0],[.s 21 0],[.s 45 0],[.s 23 0],[.s 35 0]],[.s 35 0]⟩,
⟨-2,0,10,3,[[.s 32 0],[.s 44 0],[.s 22 0],[.s 46 0],[.s 35 0]],[.s 44 4]⟩,
⟨-2,0,11,4,[[.s 33 0],[.s 45 0],[.s 34 0],[.s 23 0],[.s 47 0]],[.s 34 4]⟩,
⟨-1,0,0,4,[[.s 24 0],[.f ⟨0,0,0,0,0,0,0,0,0⟩],[.s 37 0],[.f ⟨12,3,0,0,0,0,0,0,0⟩]],[.f ⟨0,0,0,0,0,0,0,0,0⟩]⟩,
⟨-1,0,1,3,[[.s 36 0],[.s 25 0],[.f ⟨0,1,0,0,0,0,0,0,0⟩],[.s 38 0]],[.f ⟨0,1,0,0,0,0,0,0,1⟩]⟩,
⟨-1,0,2,2,[[.s 37 0],[.s 26 0],[.f ⟨0,2,0,0,0,0,0,0,0⟩],[.s 40 0]],[.f ⟨0,2,0,0,0,0,0,0,1⟩]⟩,
⟨-1,0,3,8,[[.f ⟨26,72,0,0,0,0,0,0,0⟩],[.s 27 0],[.f ⟨0,3,0,0,0,0,0,0,0⟩],[.s 41 0]],[.s 41 0]⟩,
⟨-1,0,4,1,[[.s 38 0],[.s 28 0],[.f ⟨0,4,0,0,0,0,0,0,0⟩],[.s 30 0],[.s 42 0]],[.f ⟨0,4,0,0,0,0,0,0,1⟩]⟩,
⟨-1,0,5,7,[[.s 39 0],[.s 29 0],[.f ⟨0,5,0,0,0,0,0,0,0⟩],[.s 31 0],[.s 43 0]],[.s 31 1]⟩,
⟨-1,0,6,1,[[.s 40 0],[.f ⟨0,4,0,0,0,0,0,0,0⟩],[.s 30 0],[.f ⟨0,6,0,0,0,0,0,0,0⟩],[.s 44 0],[.f ⟨0,8,0,0,0,0,0,0,0⟩]],[.f ⟨0,4,0,0,0,0,0,0,3⟩]⟩,
⟨-1,0,7,6,[[.s 41 0],[.f ⟨0,5,0,0,0,0,0,0,0⟩],[.s 31 0],[.f ⟨0,7,0,0,0,0,0,0,0⟩],[.s 45 0],[.f ⟨0,9,0,0,0,0,0,0,0⟩]],[.s 45 1]⟩,
⟨-1,0,8,2,[[.s 30 0],[.s 42 0],[.s 32 0],[.f ⟨0,8,0,0,0,0,0,0,0⟩],[.s 34 0],[.s 46 0]],[.s 42 4]⟩,
⟨-1,0,9,5,[[.s 31 0],[.s 43 0],[.s 33 0],[.f ⟨0,9,0,0,0,0,0,0,0⟩],[.s 35 0],[.s 47 0]],[.s 35 1]⟩,
⟨-1,0,10,3,[[.s 44 0],[.f ⟨0,8,0,0,0,0,0,0,0⟩],[.s 34 0],[.f ⟨0,10,0,0,0,0,0,0,0⟩],[.s 47 0]],[.s 44 5]⟩,
⟨-1,0,11,4,[[.s 45 0],[.f ⟨0,9,0,0,0,0,0,0,0⟩],[.s 46 0],[.s 35 0],[.f ⟨0,11,0,0,0,0,0,0,0⟩]],[.s 46 4]⟩]⟩,
⟨1,-3,0,0,0,[(0,-1,0),(0,1,0),(-1,0,5)],-1,0,5,3,0,0,0,0,3,0,0,0,
[⟨-7,0,0,10,[[.s 24 0,.s 24 0],[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨31,27,0,0,1,0,0,0,0⟩,.f ⟨31,27,1,0,2,0,0,0,0⟩]],[.s 12 0,.s 12 0]⟩,
⟨-7,0,1,9,[[.s 0 0,.s 0 0],[.s 25 0,.s 25 0],[.s 13 0,.s 13 0],[.s 2 0,.s 2 0]],[.s 13 1,.s 13 1]⟩,
⟨-7,0,2,8,[[.s 1 0,.s 1 0],[.s 26 0,.s 26 0],[.s 14 0,.s 14 0],[.s 4 0,.s 4 0]],[.s 14 1,.s 14 1]⟩,
⟨-7,0,3,12,[[.f ⟨29,12,0,0,0,0,0,0,0⟩,.f ⟨29,12,1,0,1,0,0,0,0⟩],[.s 27 0,.s 27 0],[.s 15 0,.s 15 0],[.s 5 0,.s 5 0]],[.s 15 1,.s 15 1]⟩,
⟨-7,0,4,7,[[.s 2 0,.s 2 0],[.s 28 0,.s 28 0],[.s 16 0,.s 16 0],[.s 30 0,.s 30 0],[.s 6 0,.s 6 0]],[.s 16 1,.s 16 1]⟩,
⟨-7,0,5,11,[[.s 3 0,.s 3 0],[.s 29 0,.s 29 0],[.s 17 0,.s 17 0],[.s 31 0,.s 31 0],[.s 7 0,.s 7 0]],[.s 17 1,.s 17 1]⟩,
⟨-7,0,6,7,[[.s 4 0,.s 4 0],[.s 16 0,.s 16 0],[.s 30 0,.s 30 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 20 0,.s 20 0]],[.s 16 3,.s 16 3]⟩,
⟨-7,0,7,10,[[.s 5 0,.s 5 0],[.s 17 0,.s 17 0],[.s 31 0,.s 31 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.s 19 2,.s 19 2]⟩,
⟨-7,0,8,8,[[.s 30 0,.s 30 0],[.s 6 0,.s 6 0],[.s 32 0,.s 32 0],[.s 20 0,.s 20 0],[.s 34 0,.s 34 0],[.s 10 0,.s 10 0]],[.s 6 4,.s 6 4]⟩,
⟨-7,0,9,10,[[.s 31 0,.s 31 0],[.s 7 0,.s 7 0],[.s 33 0,.s 33 0],[.s 21 0,.s 21 0],[.s 35 0,.s 35 0],[.s 11 0,.s 11 0]],[.s 21 2,.s 21 2]⟩,
⟨-7,0,10,8,[[.s 8 0,.s 8 0],[.s 20 0,.s 20 0],[.s 34 0,.s 34 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0]],[.s 20 4,.s 20 4]⟩,
⟨-7,0,11,9,[[.s 9 0,.s 9 0],[.s 21 0,.s 21 0],[.s 10 0,.s 10 0],[.s 35 0,.s 35 0],[.s 23 0,.s 23 0]],[.s 10 4,.s 10 4]⟩,
⟨-6,0,0,9,[[.s 0 0,.s 0 0],[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.f ⟨31,3,0,0,0,0,0,0,0⟩,.f ⟨31,3,1,0,1,0,0,0,0⟩]],[.s 24 0,.s 24 0]⟩,
⟨-6,0,1,8,[[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.s 25 0,.s 25 0],[.s 14 0,.s 14 0]],[.s 25 1,.s 25 1]⟩,
⟨-6,0,2,7,[[.s 13 0,.s 13 0],[.s 2 0,.s 2 0],[.s 26 0,.s 26 0],[.s 16 0,.s 16 0]],[.s 26 1,.s 26 1]⟩,
⟨-6,0,3,11,[[.f ⟨29,24,0,0,0,0,0,0,0⟩,.f ⟨29,24,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 27 0,.s 27 0],[.s 17 0,.s 17 0]],[.s 27 1,.s 27 1]⟩,
⟨-6,0,4,6,[[.s 14 0,.s 14 0],[.s 4 0,.s 4 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 18 0,.s 18 0]],[.s 28 1,.s 28 1]⟩,
⟨-6,0,5,10,[[.s 15 0,.s 15 0],[.s 5 0,.s 5 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 19 0,.s 19 0]],[.s 29 1,.s 29 1]⟩,
⟨-6,0,6,6,[[.s 16 0,.s 16 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.s 32 0,.s 32 0]],[.s 28 3,.s 28 3]⟩,
⟨-6,0,7,9,[[.s 17 0,.s 17 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.s 33 0,.s 33 0]],[.s 31 2,.s 31 2]⟩,
⟨-6,0,8,7,[[.s 6 0,.s 6 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 22 0,.s 22 0]],[.s 18 4,.s 18 4]⟩,
⟨-6,0,9,9,[[.s 7 0,.s 7 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 33 0,.s 33 0],[.s 11 0,.s 11 0],[.s 23 0,.s 23 0]],[.s 33 2,.s 33 2]⟩,
⟨-6,0,10,7,[[.s 20 0,.s 20 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0]],[.s 32 4,.s 32 4]⟩,
⟨-6,0,11,8,[[.s 21 0,.s 21 0],[.s 33 0,.s 33 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0],[.s 35 0,.s 35 0]],[.s 22 4,.s 22 4]⟩,
⟨-5,0,0,8,[[.s 12 0,.s 12 0],[.f ⟨10,0,0,0,0,0,0,0,0⟩,.s 0 0],[.s 25 0,.s 25 0],[.f ⟨31,15,0,0,0,0,0,0,0⟩,.f ⟨31,15,1,0,1,0,0,0,0⟩]],[.f ⟨10,0,0,0,0,0,0,0,0⟩,.s 0 0]⟩,
⟨-5,0,1,7,[[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.f ⟨10,1,0,0,0,0,0,0,0⟩,.s 1 0],[.s 26 0,.s 26 0]],[.f ⟨10,1,0,0,0,0,0,0,1⟩,.s 1 1]⟩,
⟨-5,0,2,6,[[.s 25 0,.s 25 0],[.s 14 0,.s 14 0],[.f ⟨10,2,0,0,0,0,0,0,0⟩,.s 2 0],[.s 28 0,.s 28 0]],[.f ⟨10,2,0,0,0,0,0,0,1⟩,.s 2 1]⟩,
⟨-5,0,3,10,[[.f ⟨27,0,0,0,0,0,0,0,0⟩,.f ⟨29,0,1,0,0,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨10,3,0,0,0,0,0,0,0⟩,.s 3 0],[.s 29 0,.s 29 0]],[.f ⟨10,3,0,0,0,0,0,0,1⟩,.s 3 1]⟩,
⟨-5,0,4,5,[[.s 26 0,.s 26 0],[.s 16 0,.s 16 0],[.f ⟨10,4,0,0,0,0,0,0,0⟩,.s 4 0],[.s 18 0,.s 18 0],[.s 30 0,.s 30 0]],[.f ⟨10,4,0,0,0,0,0,0,1⟩,.s 4 1]⟩,
⟨-5,0,5,9,[[.s 27 0,.s 27 0],[.s 17 0,.s 17 0],[.f ⟨10,5,0,0,0,0,0,0,0⟩,.s 5 0],[.s 19 0,.s 19 0],[.s 31 0,.s 31 0]],[.f ⟨10,5,0,0,0,0,0,0,1⟩,.s 5 1]⟩,
⟨-5,0,6,5,[[.s 28 0,.s 28 0],[.f ⟨10,4,0,0,0,0,0,0,0⟩,.s 4 0],[.s 18 0,.s 18 0],[.f ⟨10,6,0,0,0,0,0,0,0⟩,.s 6 0],[.s 32 0,.s 32 0],[.f ⟨10,8,0,0,0,0,0,0,0⟩,.s 8 0]],[.f ⟨10,4,0,0,0,0,0,0,3⟩,.s 4 3]⟩,
⟨-5,0,7,8,[[.s 29 0,.s 29 0],[.f ⟨10,5,0,0,0,0,0,0,0⟩,.s 5 0],[.s 19 0,.s 19 0],[.f ⟨10,7,0,0,0,0,0,0,0⟩,.s 7 0],[.s 33 0,.s 33 0],[.f ⟨10,9,0,0,0,0,0,0,0⟩,.s 9 0]],[.f ⟨10,7,0,0,0,0,0,0,2⟩,.s 7 2]⟩,
⟨-5,0,8,6,[[.s 18 0,.s 18 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.f ⟨10,8,0,0,0,0,0,0,0⟩,.s 8 0],[.s 22 0,.s 22 0],[.s 34 0,.s 34 0]],[.s 30 4,.s 30 4]⟩,
⟨-5,0,9,8,[[.s 19 0,.s 19 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.f ⟨10,9,0,0,0,0,0,0,0⟩,.s 9 0],[.s 23 0,.s 23 0],[.s 35 0,.s 35 0]],[.f ⟨10,9,0,0,0,0,0,0,2⟩,.s 9 2]⟩,
⟨-5,0,10,6,[[.s 32 0,.s 32 0],[.f ⟨10,8,0,0,0,0,0,0,0⟩,.s 8 0],[.s 22 0,.s 22 0],[.f ⟨10,10,0,0,0,0,0,0,0⟩,.s 10 0],[.s 35 0,.s 35 0]],[.f ⟨10,8,0,0,0,0,0,0,4⟩,.s 8 4]⟩,
⟨-5,0,11,7,[[.s 33 0,.s 33 0],[.f ⟨10,9,0,0,0,0,0,0,0⟩,.s 9 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0],[.f ⟨10,11,0,0,0,0,0,0,0⟩,.s 11 0]],[.s 34 4,.s 34 4]⟩]⟩,
⟨0,0,0,0,0,[(-2,-6,1),(1,-3,1),(2,6,-8),(-1,3,-2)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨-1,-1,0,15,[[.f ⟨13,12,0,0,0,0,0,0,0⟩],[.f ⟨14,0,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨15,39,0,0,0,0,0,0,0⟩]],[.s 1 0]⟩,
⟨-1,-1,1,14,[[.s 0 0],[.f ⟨13,13,0,0,0,0,0,0,0⟩],[.f ⟨14,1,0,0,0,0,0,0,0⟩],[.s 2 0]],[.s 2 0]⟩,
⟨-1,-1,2,13,[[.s 1 0],[.f ⟨13,14,0,0,0,0,0,0,0⟩],[.f ⟨14,2,0,0,0,0,0,0,0⟩],[.s 4 0]],[.s 4 0]⟩,
⟨-1,-1,3,5,[[.f ⟨10,36,0,0,0,0,0,0,0⟩],[.f ⟨13,15,0,0,0,0,0,0,0⟩],[.f ⟨14,3,0,0,0,0,0,0,0⟩],[.s 5 0]],[.f ⟨10,36,0,0,0,0,0,0,3⟩]⟩,
⟨-1,-1,4,12,[[.s 2 0],[.f ⟨13,16,0,0,0,0,0,0,0⟩],[.f ⟨14,4,0,0,0,0,0,0,0⟩],[.f ⟨13,18,0,0,0,0,0,0,0⟩],[.s 6 0]],[.f ⟨13,18,0,0,0,0,0,0,1⟩]⟩,
⟨-1,-1,5,6,[[.s 3 0],[.f ⟨13,17,0,0,0,0,0,0,0⟩],[.f ⟨14,5,0,0,0,0,0,0,0⟩],[.f ⟨13,19,0,0,0,0,0,0,0⟩],[.s 7 0]],[.s 3 3]⟩,
⟨-1,-1,6,11,[[.s 4 0],[.f ⟨14,4,0,0,0,0,0,0,0⟩],[.f ⟨13,18,0,0,0,0,0,0,0⟩],[.f ⟨14,6,0,0,0,0,0,0,0⟩],[.s 8 0],[.f ⟨14,8,0,0,0,0,0,0,0⟩]],[.s 8 1]⟩,
⟨-1,-1,7,6,[[.s 5 0],[.f ⟨14,5,0,0,0,0,0,0,0⟩],[.f ⟨13,19,0,0,0,0,0,0,0⟩],[.f ⟨14,7,0,0,0,0,0,0,0⟩],[.s 9 0],[.f ⟨14,9,0,0,0,0,0,0,0⟩]],[.f ⟨14,5,0,0,0,0,0,0,3⟩]⟩,
⟨-1,-1,8,10,[[.f ⟨13,18,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨13,20,0,0,0,0,0,0,0⟩],[.f ⟨14,8,0,0,0,0,0,0,0⟩],[.f ⟨13,22,0,0,0,0,0,0,0⟩],[.s 10 0]],[.f ⟨13,22,0,0,0,0,0,0,1⟩]⟩,
⟨-1,-1,9,7,[[.f ⟨13,19,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨13,21,0,0,0,0,0,0,0⟩],[.f ⟨14,9,0,0,0,0,0,0,0⟩],[.f ⟨13,23,0,0,0,0,0,0,0⟩],[.s 11 0]],[.s 7 4]⟩,
⟨-1,-1,10,9,[[.s 8 0],[.f ⟨14,8,0,0,0,0,0,0,0⟩],[.f ⟨13,22,0,0,0,0,0,0,0⟩],[.f ⟨14,10,0,0,0,0,0,0,0⟩],[.s 11 0]],[.s 11 2]⟩,
⟨-1,-1,11,8,[[.s 9 0],[.f ⟨14,9,0,0,0,0,0,0,0⟩],[.s 10 0],[.f ⟨13,23,0,0,0,0,0,0,0⟩],[.f ⟨14,11,0,0,0,0,0,0,0⟩]],[.s 9 5]⟩]⟩,
⟨1,-3,-1,0,0,[(-2,-6,9),(1,-3,1),(-1,3,-2)],-2,-6,9,12,0,0,0,0,12,0,0,0,
[⟨-4,-2,0,27,[[.s 12 0,.s 12 0],[.f ⟨15,0,0,0,0,0,0,0,0⟩,.f ⟨15,0,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨15,39,0,0,1,0,0,0,0⟩,.f ⟨15,39,1,0,2,0,0,0,0⟩]],[.s 1 0,.s 1 0]⟩,
⟨-4,-2,1,26,[[.s 0 0,.s 0 0],[.s 13 0,.s 13 0],[.f ⟨15,1,0,0,0,0,0,0,0⟩,.f ⟨15,1,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 2 0,.s 2 0]⟩,
⟨-4,-2,2,25,[[.s 1 0,.s 1 0],[.s 14 0,.s 14 0],[.f ⟨15,2,0,0,0,0,0,0,0⟩,.f ⟨15,2,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0]],[.s 4 0,.s 4 0]⟩,
⟨-4,-2,3,17,[[.f ⟨31,24,0,0,0,0,0,0,0⟩,.f ⟨31,24,0,0,0,1,0,1,0⟩],[.s 15 0,.s 15 0],[.f ⟨15,3,0,0,0,0,0,0,0⟩,.f ⟨15,3,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0]],[.f ⟨31,24,0,0,0,0,0,0,3⟩,.f ⟨31,24,0,0,0,1,0,1,3⟩]⟩,
⟨-4,-2,4,24,[[.s 2 0,.s 2 0],[.s 16 0,.s 16 0],[.f ⟨15,4,0,0,0,0,0,0,0⟩,.f ⟨15,4,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 6 0,.s 6 0]],[.s 18 1,.s 18 1]⟩,
⟨-4,-2,5,18,[[.s 3 0,.s 3 0],[.s 17 0,.s 17 0],[.f ⟨15,5,0,0,0,0,0,0,0⟩,.f ⟨15,5,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨-4,-2,6,23,[[.s 4 0,.s 4 0],[.f ⟨15,4,0,0,0,0,0,0,0⟩,.f ⟨15,4,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.f ⟨15,6,0,0,0,0,0,0,0⟩,.f ⟨15,6,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.f ⟨15,8,0,0,0,0,0,0,0⟩,.f ⟨15,8,1,0,1,0,0,0,0⟩]],[.s 8 1,.s 8 1]⟩,
⟨-4,-2,7,18,[[.s 5 0,.s 5 0],[.f ⟨15,5,0,0,0,0,0,0,0⟩,.f ⟨15,5,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.f ⟨15,7,0,0,0,0,0,0,0⟩,.f ⟨15,7,1,0,1,0,0,0,0⟩],[.s 9 0,.s 9 0],[.f ⟨15,9,0,0,0,0,0,0,0⟩,.f ⟨15,9,1,0,1,0,0,0,0⟩]],[.f ⟨15,5,0,0,0,0,0,0,3⟩,.f ⟨15,5,1,0,1,0,0,0,3⟩]⟩,
⟨-4,-2,8,22,[[.s 18 0,.s 18 0],[.s 6 0,.s 6 0],[.s 20 0,.s 20 0],[.f ⟨15,8,0,0,0,0,0,0,0⟩,.f ⟨15,8,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.s 10 0,.s 10 0]],[.s 22 1,.s 22 1]⟩,
⟨-4,-2,9,19,[[.s 19 0,.s 19 0],[.s 7 0,.s 7 0],[.s 21 0,.s 21 0],[.f ⟨15,9,0,0,0,0,0,0,0⟩,.f ⟨15,9,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0],[.s 11 0,.s 11 0]],[.s 7 4,.s 7 4]⟩,
⟨-4,-2,10,21,[[.s 8 0,.s 8 0],[.f ⟨15,8,0,0,0,0,0,0,0⟩,.f ⟨15,8,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.f ⟨15,10,0,0,0,0,0,0,0⟩,.f ⟨15,10,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.s 11 2,.s 11 2]⟩,
⟨-4,-2,11,20,[[.s 9 0,.s 9 0],[.f ⟨15,9,0,0,0,0,0,0,0⟩,.f ⟨15,9,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0],[.s 23 0,.s 23 0],[.f ⟨15,11,0,0,0,0,0,0,0⟩,.f ⟨15,11,1,0,1,0,0,0,0⟩]],[.s 9 5,.s 9 5]⟩,
⟨-2,-1,0,15,[[.f ⟨1,0,0,0,0,0,0,0,0⟩,.f ⟨1,0,1,0,1,0,0,0,0⟩],[.f ⟨12,0,0,0,0,0,0,0,0⟩,.s 0 0],[.s 13 0,.s 13 0],[.f ⟨15,15,0,0,0,0,0,0,0⟩,.f ⟨15,15,1,0,1,0,0,0,0⟩]],[.s 13 0,.s 13 0]⟩,
⟨-2,-1,1,14,[[.s 12 0,.s 12 0],[.f ⟨1,1,0,0,0,0,0,0,0⟩,.f ⟨1,1,1,0,1,0,0,0,0⟩],[.f ⟨12,1,0,0,0,0,0,0,0⟩,.s 1 0],[.s 14 0,.s 14 0]],[.s 14 0,.s 14 0]⟩,
⟨-2,-1,2,13,[[.s 13 0,.s 13 0],[.f ⟨1,2,0,0,0,0,0,0,0⟩,.f ⟨1,2,1,0,1,0,0,0,0⟩],[.f ⟨12,2,0,0,0,0,0,0,0⟩,.s 2 0],[.s 16 0,.s 16 0]],[.s 16 0,.s 16 0]⟩,
⟨-2,-1,3,6,[[.f ⟨10,24,0,0,0,0,0,0,0⟩,.f ⟨31,12,0,0,0,1,0,0,0⟩],[.f ⟨1,3,0,0,0,0,0,0,0⟩,.f ⟨1,3,1,0,1,0,0,0,0⟩],[.f ⟨12,3,0,0,0,0,0,0,0⟩,.s 3 0],[.s 17 0,.s 17 0]],[.f ⟨10,24,0,0,0,0,0,0,3⟩,.f ⟨31,12,0,0,0,1,0,0,3⟩]⟩,
⟨-2,-1,4,12,[[.s 14 0,.s 14 0],[.f ⟨1,4,0,0,0,0,0,0,0⟩,.f ⟨1,4,1,0,1,0,0,0,0⟩],[.f ⟨12,4,0,0,0,0,0,0,0⟩,.s 4 0],[.f ⟨1,6,0,0,0,0,0,0,0⟩,.f ⟨1,6,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0]],[.f ⟨1,6,0,0,0,0,0,0,1⟩,.f ⟨1,6,1,0,1,0,0,0,1⟩]⟩,
⟨-2,-1,5,7,[[.s 15 0,.s 15 0],[.f ⟨1,5,0,0,0,0,0,0,0⟩,.f ⟨1,5,1,0,1,0,0,0,0⟩],[.f ⟨12,5,0,0,0,0,0,0,0⟩,.s 5 0],[.f ⟨1,7,0,0,0,0,0,0,0⟩,.f ⟨1,7,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0]],[.s 15 3,.s 15 3]⟩,
⟨-2,-1,6,11,[[.s 16 0,.s 16 0],[.f ⟨12,4,0,0,0,0,0,0,0⟩,.s 4 0],[.f ⟨1,6,0,0,0,0,0,0,0⟩,.f ⟨1,6,1,0,1,0,0,0,0⟩],[.f ⟨12,6,0,0,0,0,0,0,0⟩,.s 6 0],[.s 20 0,.s 20 0],[.f ⟨12,8,0,0,0,0,0,0,0⟩,.s 8 0]],[.s 20 1,.s 20 1]⟩,
⟨-2,-1,7,7,[[.s 17 0,.s 17 0],[.f ⟨12,5,0,0,0,0,0,0,0⟩,.s 5 0],[.f ⟨1,7,0,0,0,0,0,0,0⟩,.f ⟨1,7,1,0,1,0,0,0,0⟩],[.f ⟨12,7,0,0,0,0,0,0,0⟩,.s 7 0],[.s 21 0,.s 21 0],[.f ⟨12,9,0,0,0,0,0,0,0⟩,.s 9 0]],[.f ⟨12,5,0,0,0,0,0,0,3⟩,.s 5 3]⟩,
⟨-2,-1,8,10,[[.f ⟨1,6,0,0,0,0,0,0,0⟩,.f ⟨1,6,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.f ⟨1,8,0,0,0,0,0,0,0⟩,.f ⟨1,8,1,0,1,0,0,0,0⟩],[.f ⟨12,8,0,0,0,0,0,0,0⟩,.s 8 0],[.f ⟨1,10,0,0,0,0,0,0,0⟩,.f ⟨1,10,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0]],[.s 22 0,.s 22 0]⟩,
⟨-2,-1,9,8,[[.f ⟨1,7,0,0,0,0,0,0,0⟩,.f ⟨1,7,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.f ⟨1,9,0,0,0,0,0,0,0⟩,.f ⟨1,9,1,0,1,0,0,0,0⟩],[.f ⟨12,9,0,0,0,0,0,0,0⟩,.s 9 0],[.f ⟨1,11,0,0,0,0,0,0,0⟩,.f ⟨1,11,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.s 19 4,.s 19 4]⟩,
⟨-2,-1,10,9,[[.s 20 0,.s 20 0],[.f ⟨12,8,0,0,0,0,0,0,0⟩,.s 8 0],[.f ⟨1,10,0,0,0,0,0,0,0⟩,.f ⟨1,10,1,0,1,0,0,0,0⟩],[.f ⟨12,10,0,0,0,0,0,0,0⟩,.s 10 0],[.s 23 0,.s 23 0]],[.s 23 2,.s 23 2]⟩,
⟨-2,-1,11,8,[[.s 21 0,.s 21 0],[.f ⟨12,9,0,0,0,0,0,0,0⟩,.s 9 0],[.s 22 0,.s 22 0],[.f ⟨1,11,0,0,0,0,0,0,0⟩,.f ⟨1,11,1,0,1,0,0,0,0⟩],[.f ⟨12,11,0,0,0,0,0,0,0⟩,.s 11 0]],[.f ⟨12,9,0,0,0,0,0,0,4⟩,.s 9 4]⟩]⟩,
⟨1,6,-2,0,0,[(1,-3,3),(-2,-6,1),(2,6,-8)],1,-3,3,12,0,0,0,0,24,0,0,0,
[⟨0,-1,0,15,[[.f ⟨12,0,0,0,0,0,0,0,0⟩,.s 72 0],[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨15,63,0,0,0,0,0,0,0⟩,.f ⟨15,63,0,0,0,1,0,1,0⟩]],[.s 1 0,.s 1 0]⟩,
⟨0,-1,1,14,[[.s 0 0,.s 0 0],[.f ⟨12,1,0,0,0,0,0,0,0⟩,.s 73 0],[.s 13 0,.s 13 0],[.s 2 0,.s 2 0]],[.s 2 0,.s 2 0]⟩,
⟨0,-1,2,13,[[.s 1 0,.s 1 0],[.f ⟨12,2,0,0,0,0,0,0,0⟩,.s 74 0],[.s 14 0,.s 14 0],[.s 4 0,.s 4 0]],[.s 4 0,.s 4 0]⟩,
⟨0,-1,3,4,[[.f ⟨0,0,0,0,0,0,0,0,0⟩,.f ⟨3,0,1,0,0,0,0,0,0⟩],[.f ⟨12,3,0,0,0,0,0,0,0⟩,.s 75 0],[.s 15 0,.s 15 0],[.s 5 0,.s 5 0]],[.f ⟨0,0,0,0,0,0,0,0,3⟩,.f ⟨3,0,1,0,0,0,0,0,3⟩]⟩,
⟨0,-1,4,12,[[.s 2 0,.s 2 0],[.f ⟨12,4,0,0,0,0,0,0,0⟩,.s 76 0],[.s 16 0,.s 16 0],[.f ⟨12,6,0,0,0,0,0,0,0⟩,.s 78 0],[.s 6 0,.s 6 0]],[.f ⟨12,6,0,0,0,0,0,0,1⟩,.s 78 1]⟩,
⟨0,-1,5,5,[[.s 3 0,.s 3 0],[.f ⟨12,5,0,0,0,0,0,0,0⟩,.s 77 0],[.s 17 0,.s 17 0],[.f ⟨12,7,0,0,0,0,0,0,0⟩,.s 79 0],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨0,-1,6,11,[[.s 4 0,.s 4 0],[.s 16 0,.s 16 0],[.f ⟨12,6,0,0,0,0,0,0,0⟩,.s 78 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 20 0,.s 20 0]],[.s 8 1,.s 8 1]⟩,
⟨0,-1,7,6,[[.s 5 0,.s 5 0],[.s 17 0,.s 17 0],[.f ⟨12,7,0,0,0,0,0,0,0⟩,.s 79 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.s 5 4,.s 5 4]⟩,
⟨0,-1,8,10,[[.f ⟨12,6,0,0,0,0,0,0,0⟩,.s 78 0],[.s 6 0,.s 6 0],[.f ⟨12,8,0,0,0,0,0,0,0⟩,.s 80 0],[.s 20 0,.s 20 0],[.f ⟨12,10,0,0,0,0,0,0,0⟩,.s 82 0],[.s 10 0,.s 10 0]],[.f ⟨12,10,0,0,0,0,0,0,1⟩,.s 82 1]⟩,
⟨0,-1,9,7,[[.f ⟨12,7,0,0,0,0,0,0,0⟩,.s 79 0],[.s 7 0,.s 7 0],[.f ⟨12,9,0,0,0,0,0,0,0⟩,.s 81 0],[.s 21 0,.s 21 0],[.f ⟨12,11,0,0,0,0,0,0,0⟩,.s 83 0],[.s 11 0,.s 11 0]],[.f ⟨12,7,0,0,0,0,0,0,5⟩,.s 79 5]⟩,
⟨0,-1,10,9,[[.s 8 0,.s 8 0],[.s 20 0,.s 20 0],[.f ⟨12,10,0,0,0,0,0,0,0⟩,.s 82 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0]],[.s 11 2,.s 11 2]⟩,
⟨0,-1,11,8,[[.s 9 0,.s 9 0],[.s 21 0,.s 21 0],[.s 10 0,.s 10 0],[.f ⟨12,11,0,0,0,0,0,0,0⟩,.s 83 0],[.s 23 0,.s 23 0]],[.s 9 5,.s 9 5]⟩,
⟨1,-1,0,15,[[.s 0 0,.s 0 0],[.s 36 0,.s 36 0],[.s 13 0,.s 13 0],[.f ⟨15,87,0,0,0,0,0,0,0⟩,.f ⟨15,87,0,0,0,1,0,1,0⟩]],[.s 13 0,.s 13 0]⟩,
⟨1,-1,1,14,[[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.s 37 0,.s 37 0],[.s 14 0,.s 14 0]],[.s 14 0,.s 14 0]⟩,
⟨1,-1,2,13,[[.s 13 0,.s 13 0],[.s 2 0,.s 2 0],[.s 38 0,.s 38 0],[.s 16 0,.s 16 0]],[.s 16 0,.s 16 0]⟩,
⟨1,-1,3,5,[[.f ⟨4,0,0,0,0,0,0,0,0⟩,.f ⟨17,0,1,0,0,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 39 0,.s 39 0],[.s 17 0,.s 17 0]],[.f ⟨4,0,0,0,0,0,0,0,3⟩,.f ⟨17,0,1,0,0,0,0,0,3⟩]⟩,
⟨1,-1,4,12,[[.s 14 0,.s 14 0],[.s 4 0,.s 4 0],[.s 40 0,.s 40 0],[.s 6 0,.s 6 0],[.s 18 0,.s 18 0]],[.s 6 1,.s 6 1]⟩,
⟨1,-1,5,6,[[.s 15 0,.s 15 0],[.s 5 0,.s 5 0],[.s 41 0,.s 41 0],[.s 7 0,.s 7 0],[.s 19 0,.s 19 0]],[.s 15 3,.s 15 3]⟩,
⟨1,-1,6,11,[[.s 16 0,.s 16 0],[.s 40 0,.s 40 0],[.s 6 0,.s 6 0],[.s 42 0,.s 42 0],[.s 20 0,.s 20 0],[.s 44 0,.s 44 0]],[.s 20 1,.s 20 1]⟩,
⟨1,-1,7,7,[[.s 17 0,.s 17 0],[.s 41 0,.s 41 0],[.s 7 0,.s 7 0],[.s 43 0,.s 43 0],[.s 21 0,.s 21 0],[.s 45 0,.s 45 0]],[.s 17 4,.s 17 4]⟩,
⟨1,-1,8,10,[[.s 6 0,.s 6 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 44 0,.s 44 0],[.s 10 0,.s 10 0],[.s 22 0,.s 22 0]],[.s 10 1,.s 10 1]⟩,
⟨1,-1,9,7,[[.s 7 0,.s 7 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 45 0,.s 45 0],[.s 11 0,.s 11 0],[.s 23 0,.s 23 0]],[.s 7 5,.s 7 5]⟩,
⟨1,-1,10,9,[[.s 20 0,.s 20 0],[.s 44 0,.s 44 0],[.s 10 0,.s 10 0],[.s 46 0,.s 46 0],[.s 23 0,.s 23 0]],[.s 23 2,.s 23 2]⟩,
⟨1,-1,11,8,[[.s 21 0,.s 21 0],[.s 45 0,.s 45 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0],[.s 47 0,.s 47 0]],[.s 21 5,.s 21 5]⟩,
⟨2,-2,0,27,[[.f ⟨15,84,0,0,0,0,0,0,0⟩,.f ⟨15,84,0,0,0,1,0,1,0⟩],[.s 48 0,.s 48 0],[.s 25 0,.s 25 0],[.f ⟨15,111,0,0,0,0,0,0,0⟩,.f ⟨15,111,0,0,0,1,0,1,0⟩]],[.s 25 0,.s 25 0]⟩,
⟨2,-2,1,26,[[.s 24 0,.s 24 0],[.f ⟨15,85,0,0,0,0,0,0,0⟩,.f ⟨15,85,0,0,0,1,0,1,0⟩],[.s 49 0,.s 49 0],[.s 26 0,.s 26 0]],[.s 26 0,.s 26 0]⟩,
⟨2,-2,2,25,[[.s 25 0,.s 25 0],[.f ⟨15,86,0,0,0,0,0,0,0⟩,.f ⟨15,86,0,0,0,1,0,1,0⟩],[.s 50 0,.s 50 0],[.s 28 0,.s 28 0]],[.s 28 0,.s 28 0]⟩,
⟨2,-2,3,16,[[.s 36 0,.s 36 0],[.f ⟨15,87,0,0,0,0,0,0,0⟩,.f ⟨15,87,0,0,0,1,0,1,0⟩],[.s 51 0,.s 51 0],[.s 29 0,.s 29 0]],[.s 36 3,.s 36 3]⟩,
⟨2,-2,4,24,[[.s 26 0,.s 26 0],[.f ⟨15,88,0,0,0,0,0,0,0⟩,.f ⟨15,88,0,0,0,1,0,1,0⟩],[.s 52 0,.s 52 0],[.f ⟨15,90,0,0,0,0,0,0,0⟩,.f ⟨15,90,0,0,0,1,0,1,0⟩],[.s 30 0,.s 30 0]],[.f ⟨15,90,0,0,0,0,0,0,1⟩,.f ⟨15,90,0,0,0,1,0,1,1⟩]⟩,
⟨2,-2,5,17,[[.s 27 0,.s 27 0],[.f ⟨15,89,0,0,0,0,0,0,0⟩,.f ⟨15,89,0,0,0,1,0,1,0⟩],[.s 53 0,.s 53 0],[.f ⟨15,91,0,0,0,0,0,0,0⟩,.f ⟨15,91,0,0,0,1,0,1,0⟩],[.s 31 0,.s 31 0]],[.s 27 3,.s 27 3]⟩,
⟨2,-2,6,23,[[.s 28 0,.s 28 0],[.s 52 0,.s 52 0],[.f ⟨15,90,0,0,0,0,0,0,0⟩,.f ⟨15,90,0,0,0,1,0,1,0⟩],[.s 54 0,.s 54 0],[.s 32 0,.s 32 0],[.s 56 0,.s 56 0]],[.s 32 1,.s 32 1]⟩,
⟨2,-2,7,18,[[.s 29 0,.s 29 0],[.s 53 0,.s 53 0],[.f ⟨15,91,0,0,0,0,0,0,0⟩,.f ⟨15,91,0,0,0,1,0,1,0⟩],[.s 55 0,.s 55 0],[.s 33 0,.s 33 0],[.s 57 0,.s 57 0]],[.s 29 4,.s 29 4]⟩,
⟨2,-2,8,22,[[.f ⟨15,90,0,0,0,0,0,0,0⟩,.f ⟨15,90,0,0,0,1,0,1,0⟩],[.s 30 0,.s 30 0],[.f ⟨15,92,0,0,0,0,0,0,0⟩,.f ⟨15,92,0,0,0,1,0,1,0⟩],[.s 56 0,.s 56 0],[.f ⟨15,94,0,0,0,0,0,0,0⟩,.f ⟨15,94,0,0,0,1,0,1,0⟩],[.s 34 0,.s 34 0]],[.f ⟨15,94,0,0,0,0,0,0,1⟩,.f ⟨15,94,0,0,0,1,0,1,1⟩]⟩,
⟨2,-2,9,19,[[.f ⟨15,91,0,0,0,0,0,0,0⟩,.f ⟨15,91,0,0,0,1,0,1,0⟩],[.s 31 0,.s 31 0],[.f ⟨15,93,0,0,0,0,0,0,0⟩,.f ⟨15,93,0,0,0,1,0,1,0⟩],[.s 57 0,.s 57 0],[.f ⟨15,95,0,0,0,0,0,0,0⟩,.f ⟨15,95,0,0,0,1,0,1,0⟩],[.s 35 0,.s 35 0]],[.f ⟨15,91,0,0,0,0,0,0,5⟩,.f ⟨15,91,0,0,0,1,0,1,5⟩]⟩,
⟨2,-2,10,21,[[.s 32 0,.s 32 0],[.s 56 0,.s 56 0],[.f ⟨15,94,0,0,0,0,0,0,0⟩,.f ⟨15,94,0,0,0,1,0,1,0⟩],[.s 58 0,.s 58 0],[.s 35 0,.s 35 0]],[.s 35 2,.s 35 2]⟩,
⟨2,-2,11,20,[[.s 33 0,.s 33 0],[.s 57 0,.s 57 0],[.s 34 0,.s 34 0],[.f ⟨15,95,0,0,0,0,0,0,0⟩,.f ⟨15,95,0,0,0,1,0,1,0⟩],[.s 59 0,.s 59 0]],[.s 33 5,.s 33 5]⟩,
⟨2,-1,0,15,[[.s 12 0,.s 12 0],[.f ⟨2,0,0,0,0,0,0,0,0⟩,.f ⟨3,12,1,0,0,0,0,0,0⟩],[.s 37 0,.s 37 0],[.s 27 0,.s 27 0]],[.s 37 0,.s 37 0]⟩,
⟨2,-1,1,14,[[.s 36 0,.s 36 0],[.s 13 0,.s 13 0],[.f ⟨2,1,0,0,0,0,0,0,0⟩,.f ⟨3,13,1,0,0,0,0,0,0⟩],[.s 38 0,.s 38 0]],[.s 38 0,.s 38 0]⟩,
⟨2,-1,2,13,[[.s 37 0,.s 37 0],[.s 14 0,.s 14 0],[.f ⟨2,2,0,0,0,0,0,0,0⟩,.f ⟨3,14,1,0,0,0,0,0,0⟩],[.s 40 0,.s 40 0]],[.s 40 0,.s 40 0]⟩,
⟨2,-1,3,6,[[.f ⟨4,12,0,0,0,0,0,0,0⟩,.f ⟨19,0,1,0,0,0,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨2,3,0,0,0,0,0,0,0⟩,.f ⟨3,15,1,0,0,0,0,0,0⟩],[.s 41 0,.s 41 0]],[.f ⟨4,12,0,0,0,0,0,0,3⟩,.f ⟨19,0,1,0,0,0,0,0,3⟩]⟩,
⟨2,-1,4,12,[[.s 38 0,.s 38 0],[.s 16 0,.s 16 0],[.f ⟨2,4,0,0,0,0,0,0,0⟩,.f ⟨3,16,1,0,0,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 42 0,.s 42 0]],[.s 18 1,.s 18 1]⟩,
⟨2,-1,5,7,[[.s 39 0,.s 39 0],[.s 17 0,.s 17 0],[.f ⟨2,5,0,0,0,0,0,0,0⟩,.f ⟨3,17,1,0,0,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 43 0,.s 43 0]],[.s 39 3,.s 39 3]⟩,
⟨2,-1,6,11,[[.s 40 0,.s 40 0],[.f ⟨2,4,0,0,0,0,0,0,0⟩,.f ⟨3,16,1,0,0,0,0,0,0⟩],[.s 18 0,.s 18 0],[.f ⟨2,6,0,0,0,0,0,0,0⟩,.f ⟨3,18,1,0,0,0,0,0,0⟩],[.s 44 0,.s 44 0],[.f ⟨2,8,0,0,0,0,0,0,0⟩,.f ⟨3,20,1,0,0,0,0,0,0⟩]],[.s 44 1,.s 44 1]⟩,
⟨2,-1,7,8,[[.s 41 0,.s 41 0],[.f ⟨2,5,0,0,0,0,0,0,0⟩,.f ⟨3,17,1,0,0,0,0,0,0⟩],[.s 19 0,.s 19 0],[.f ⟨2,7,0,0,0,0,0,0,0⟩,.f ⟨3,19,1,0,0,0,0,0,0⟩],[.s 45 0,.s 45 0],[.f ⟨2,9,0,0,0,0,0,0,0⟩,.f ⟨3,21,1,0,0,0,0,0,0⟩]],[.s 41 4,.s 41 4]⟩,
⟨2,-1,8,10,[[.s 18 0,.s 18 0],[.s 42 0,.s 42 0],[.s 20 0,.s 20 0],[.f ⟨2,8,0,0,0,0,0,0,0⟩,.f ⟨3,20,1,0,0,0,0,0,0⟩],[.s 22 0,.s 22 0],[.s 46 0,.s 46 0]],[.s 22 1,.s 22 1]⟩,
⟨2,-1,9,8,[[.s 19 0,.s 19 0],[.s 43 0,.s 43 0],[.s 21 0,.s 21 0],[.f ⟨2,9,0,0,0,0,0,0,0⟩,.f ⟨3,21,1,0,0,0,0,0,0⟩],[.s 23 0,.s 23 0],[.s 47 0,.s 47 0]],[.s 19 5,.s 19 5]⟩,
⟨2,-1,10,10,[[.s 44 0,.s 44 0],[.f ⟨2,8,0,0,0,0,0,0,0⟩,.f ⟨3,20,1,0,0,0,0,0,0⟩],[.s 22 0,.s 22 0],[.f ⟨2,10,0,0,0,0,0,0,0⟩,.f ⟨3,22,1,0,0,0,0,0,0⟩],[.s 47 0,.s 47 0]],[.s 22 3,.s 22 3]⟩,
⟨2,-1,11,9,[[.s 45 0,.s 45 0],[.f ⟨2,9,0,0,0,0,0,0,0⟩,.f ⟨3,21,1,0,0,0,0,0,0⟩],[.s 46 0,.s 46 0],[.s 23 0,.s 23 0],[.f ⟨2,11,0,0,0,0,0,0,0⟩,.f ⟨3,23,1,0,0,0,0,0,0⟩]],[.s 45 5,.s 45 5]⟩,
⟨3,-2,0,27,[[.s 24 0,.s 24 0],[.s 60 0,.s 60 0],[.s 49 0,.s 49 0],[.f ⟨15,123,0,0,0,0,0,0,0⟩,.f ⟨15,123,0,0,0,1,0,1,0⟩]],[.s 49 0,.s 49 0]⟩,
⟨3,-2,1,26,[[.s 48 0,.s 48 0],[.s 25 0,.s 25 0],[.s 61 0,.s 61 0],[.s 50 0,.s 50 0]],[.s 50 0,.s 50 0]⟩,
⟨3,-2,2,25,[[.s 49 0,.s 49 0],[.s 26 0,.s 26 0],[.s 62 0,.s 62 0],[.s 52 0,.s 52 0]],[.s 52 0,.s 52 0]⟩,
⟨3,-2,3,16,[[.f ⟨2,0,0,0,0,0,0,0,0⟩,.f ⟨3,12,1,0,0,0,0,0,0⟩],[.s 27 0,.s 27 0],[.s 63 0,.s 63 0],[.s 53 0,.s 53 0]],[.f ⟨2,0,0,0,0,0,0,0,3⟩,.f ⟨3,12,1,0,0,0,0,0,3⟩]⟩,
⟨3,-2,4,24,[[.s 50 0,.s 50 0],[.s 28 0,.s 28 0],[.s 64 0,.s 64 0],[.s 30 0,.s 30 0],[.s 54 0,.s 54 0]],[.s 30 1,.s 30 1]⟩,
⟨3,-2,5,17,[[.s 51 0,.s 51 0],[.s 29 0,.s 29 0],[.s 65 0,.s 65 0],[.s 31 0,.s 31 0],[.s 55 0,.s 55 0]],[.s 51 3,.s 51 3]⟩,
⟨3,-2,6,23,[[.s 52 0,.s 52 0],[.s 64 0,.s 64 0],[.s 30 0,.s 30 0],[.s 66 0,.s 66 0],[.s 56 0,.s 56 0],[.s 68 0,.s 68 0]],[.s 56 1,.s 56 1]⟩,
⟨3,-2,7,18,[[.s 53 0,.s 53 0],[.s 65 0,.s 65 0],[.s 31 0,.s 31 0],[.s 67 0,.s 67 0],[.s 57 0,.s 57 0],[.s 69 0,.s 69 0]],[.s 53 4,.s 53 4]⟩,
⟨3,-2,8,22,[[.s 30 0,.s 30 0],[.s 54 0,.s 54 0],[.s 32 0,.s 32 0],[.s 68 0,.s 68 0],[.s 34 0,.s 34 0],[.s 58 0,.s 58 0]],[.s 34 1,.s 34 1]⟩,
⟨3,-2,9,19,[[.s 31 0,.s 31 0],[.s 55 0,.s 55 0],[.s 33 0,.s 33 0],[.s 69 0,.s 69 0],[.s 35 0,.s 35 0],[.s 59 0,.s 59 0]],[.s 31 5,.s 31 5]⟩,
⟨3,-2,10,21,[[.s 56 0,.s 56 0],[.s 68 0,.s 68 0],[.s 34 0,.s 34 0],[.s 70 0,.s 70 0],[.s 59 0,.s 59 0]],[.s 59 2,.s 59 2]⟩,
⟨3,-2,11,20,[[.s 57 0,.s 57 0],[.s 69 0,.s 69 0],[.s 58 0,.s 58 0],[.s 35 0,.s 35 0],[.s 71 0,.s 71 0]],[.s 57 5,.s 57 5]⟩,
⟨4,-2,0,27,[[.s 48 0,.s 48 0],[.s 84 0,.s 84 0],[.s 61 0,.s 61 0],[.f ⟨15,135,0,0,0,0,0,0,0⟩,.f ⟨15,135,0,0,0,1,0,1,0⟩]],[.s 61 0,.s 61 0]⟩,
⟨4,-2,1,26,[[.s 60 0,.s 60 0],[.s 49 0,.s 49 0],[.s 85 0,.s 85 0],[.s 62 0,.s 62 0]],[.s 62 0,.s 62 0]⟩,
⟨4,-2,2,25,[[.s 61 0,.s 61 0],[.s 50 0,.s 50 0],[.s 86 0,.s 86 0],[.s 64 0,.s 64 0]],[.s 64 0,.s 64 0]⟩,
⟨4,-2,3,17,[[.f ⟨16,0,0,0,0,0,0,0,0⟩,.f ⟨17,12,1,0,0,0,0,0,0⟩],[.s 51 0,.s 51 0],[.s 87 0,.s 87 0],[.s 65 0,.s 65 0]],[.f ⟨16,0,0,0,0,0,0,0,3⟩,.f ⟨17,12,1,0,0,0,0,0,3⟩]⟩,
⟨4,-2,4,24,[[.s 62 0,.s 62 0],[.s 52 0,.s 52 0],[.s 88 0,.s 88 0],[.s 54 0,.s 54 0],[.s 66 0,.s 66 0]],[.s 54 1,.s 54 1]⟩,
⟨4,-2,5,18,[[.s 63 0,.s 63 0],[.s 53 0,.s 53 0],[.s 89 0,.s 89 0],[.s 55 0,.s 55 0],[.s 67 0,.s 67 0]],[.s 63 3,.s 63 3]⟩,
⟨4,-2,6,23,[[.s 64 0,.s 64 0],[.s 88 0,.s 88 0],[.s 54 0,.s 54 0],[.s 90 0,.s 90 0],[.s 68 0,.s 68 0],[.s 92 0,.s 92 0]],[.s 68 1,.s 68 1]⟩,
⟨4,-2,7,19,[[.s 65 0,.s 65 0],[.s 89 0,.s 89 0],[.s 55 0,.s 55 0],[.s 91 0,.s 91 0],[.s 69 0,.s 69 0],[.s 93 0,.s 93 0]],[.s 65 4,.s 65 4]⟩,
⟨4,-2,8,22,[[.s 54 0,.s 54 0],[.s 66 0,.s 66 0],[.s 56 0,.s 56 0],[.s 92 0,.s 92 0],[.s 58 0,.s 58 0],[.s 70 0,.s 70 0]],[.s 58 1,.s 58 1]⟩,
⟨4,-2,9,19,[[.s 55 0,.s 55 0],[.s 67 0,.s 67 0],[.s 57 0,.s 57 0],[.s 93 0,.s 93 0],[.s 59 0,.s 59 0],[.s 71 0,.s 71 0]],[.s 55 5,.s 55 5]⟩,
⟨4,-2,10,21,[[.s 68 0,.s 68 0],[.s 92 0,.s 92 0],[.s 58 0,.s 58 0],[.s 94 0,.s 94 0],[.s 71 0,.s 71 0]],[.s 71 2,.s 71 2]⟩,
⟨4,-2,11,20,[[.s 69 0,.s 69 0],[.s 93 0,.s 93 0],[.s 70 0,.s 70 0],[.s 59 0,.s 59 0],[.s 95 0,.s 95 0]],[.s 69 5,.s 69 5]⟩,
⟨5,-3,0,39,[[.f ⟨15,132,0,0,0,0,0,0,0⟩,.f ⟨15,132,0,0,0,1,0,1,0⟩],[.s 0 0,.s 0 0],[.s 73 0,.s 73 0],[.f ⟨15,39,0,0,0,0,0,1,0⟩,.f ⟨15,39,0,0,0,1,0,2,0⟩]],[.s 73 0,.s 73 0]⟩,
⟨5,-3,1,38,[[.s 72 0,.s 72 0],[.f ⟨15,133,0,0,0,0,0,0,0⟩,.f ⟨15,133,0,0,0,1,0,1,0⟩],[.s 1 0,.s 1 0],[.s 74 0,.s 74 0]],[.s 74 0,.s 74 0]⟩,
⟨5,-3,2,37,[[.s 73 0,.s 73 0],[.f ⟨15,134,0,0,0,0,0,0,0⟩,.f ⟨15,134,0,0,0,1,0,1,0⟩],[.s 2 0,.s 2 0],[.s 76 0,.s 76 0]],[.s 76 0,.s 76 0]⟩,
⟨5,-3,3,28,[[.s 84 0,.s 84 0],[.f ⟨15,135,0,0,0,0,0,0,0⟩,.f ⟨15,135,0,0,0,1,0,1,0⟩],[.s 3 0,.s 3 0],[.s 77 0,.s 77 0]],[.s 84 3,.s 84 3]⟩,
⟨5,-3,4,36,[[.s 74 0,.s 74 0],[.f ⟨15,136,0,0,0,0,0,0,0⟩,.f ⟨15,136,0,0,0,1,0,1,0⟩],[.s 4 0,.s 4 0],[.f ⟨15,138,0,0,0,0,0,0,0⟩,.f ⟨15,138,0,0,0,1,0,1,0⟩],[.s 78 0,.s 78 0]],[.f ⟨15,138,0,0,0,0,0,0,1⟩,.f ⟨15,138,0,0,0,1,0,1,1⟩]⟩,
⟨5,-3,5,29,[[.s 75 0,.s 75 0],[.f ⟨15,137,0,0,0,0,0,0,0⟩,.f ⟨15,137,0,0,0,1,0,1,0⟩],[.s 5 0,.s 5 0],[.f ⟨15,139,0,0,0,0,0,0,0⟩,.f ⟨15,139,0,0,0,1,0,1,0⟩],[.s 79 0,.s 79 0]],[.s 75 3,.s 75 3]⟩,
⟨5,-3,6,35,[[.s 76 0,.s 76 0],[.s 4 0,.s 4 0],[.f ⟨15,138,0,0,0,0,0,0,0⟩,.f ⟨15,138,0,0,0,1,0,1,0⟩],[.s 6 0,.s 6 0],[.s 80 0,.s 80 0],[.s 8 0,.s 8 0]],[.s 80 1,.s 80 1]⟩,
⟨5,-3,7,30,[[.s 77 0,.s 77 0],[.s 5 0,.s 5 0],[.f ⟨15,139,0,0,0,0,0,0,0⟩,.f ⟨15,139,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0],[.s 81 0,.s 81 0],[.s 9 0,.s 9 0]],[.s 77 4,.s 77 4]⟩,
⟨5,-3,8,34,[[.f ⟨15,138,0,0,0,0,0,0,0⟩,.f ⟨15,138,0,0,0,1,0,1,0⟩],[.s 78 0,.s 78 0],[.f ⟨15,140,0,0,0,0,0,0,0⟩,.f ⟨15,140,0,0,0,1,0,1,0⟩],[.s 8 0,.s 8 0],[.f ⟨15,142,0,0,0,0,0,0,0⟩,.f ⟨15,142,0,0,0,1,0,1,0⟩],[.s 82 0,.s 82 0]],[.f ⟨15,142,0,0,0,0,0,0,1⟩,.f ⟨15,142,0,0,0,1,0,1,1⟩]⟩,
⟨5,-3,9,31,[[.f ⟨15,139,0,0,0,0,0,0,0⟩,.f ⟨15,139,0,0,0,1,0,1,0⟩],[.s 79 0,.s 79 0],[.f ⟨15,141,0,0,0,0,0,0,0⟩,.f ⟨15,141,0,0,0,1,0,1,0⟩],[.s 9 0,.s 9 0],[.f ⟨15,143,0,0,0,0,0,0,0⟩,.f ⟨15,143,0,0,0,1,0,1,0⟩],[.s 83 0,.s 83 0]],[.f ⟨15,139,0,0,0,0,0,0,5⟩,.f ⟨15,139,0,0,0,1,0,1,5⟩]⟩,
⟨5,-3,10,33,[[.s 80 0,.s 80 0],[.s 8 0,.s 8 0],[.f ⟨15,142,0,0,0,0,0,0,0⟩,.f ⟨15,142,0,0,0,1,0,1,0⟩],[.s 10 0,.s 10 0],[.s 83 0,.s 83 0]],[.s 83 2,.s 83 2]⟩,
⟨5,-3,11,32,[[.s 81 0,.s 81 0],[.s 9 0,.s 9 0],[.s 82 0,.s 82 0],[.f ⟨15,143,0,0,0,0,0,0,0⟩,.f ⟨15,143,0,0,0,1,0,1,0⟩],[.s 11 0,.s 11 0]],[.s 81 5,.s 81 5]⟩,
⟨5,-2,0,27,[[.s 60 0,.s 60 0],[.f ⟨3,0,0,0,0,0,0,0,0⟩,.f ⟨3,0,1,0,1,0,0,0,0⟩],[.s 85 0,.s 85 0],[.s 75 0,.s 75 0]],[.s 85 0,.s 85 0]⟩,
⟨5,-2,1,26,[[.s 84 0,.s 84 0],[.s 61 0,.s 61 0],[.f ⟨3,1,0,0,0,0,0,0,0⟩,.f ⟨3,1,1,0,1,0,0,0,0⟩],[.s 86 0,.s 86 0]],[.s 86 0,.s 86 0]⟩,
⟨5,-2,2,25,[[.s 85 0,.s 85 0],[.s 62 0,.s 62 0],[.f ⟨3,2,0,0,0,0,0,0,0⟩,.f ⟨3,2,1,0,1,0,0,0,0⟩],[.s 88 0,.s 88 0]],[.s 88 0,.s 88 0]⟩,
⟨5,-2,3,18,[[.f ⟨18,0,0,0,0,0,0,0,0⟩,.f ⟨19,36,1,0,0,0,0,0,0⟩],[.s 63 0,.s 63 0],[.f ⟨3,3,0,0,0,0,0,0,0⟩,.f ⟨3,3,1,0,1,0,0,0,0⟩],[.s 89 0,.s 89 0]],[.f ⟨18,0,0,0,0,0,0,0,3⟩,.f ⟨19,36,1,0,0,0,0,0,3⟩]⟩,
⟨5,-2,4,24,[[.s 86 0,.s 86 0],[.s 64 0,.s 64 0],[.f ⟨3,4,0,0,0,0,0,0,0⟩,.f ⟨3,4,1,0,1,0,0,0,0⟩],[.s 66 0,.s 66 0],[.s 90 0,.s 90 0]],[.s 66 1,.s 66 1]⟩,
⟨5,-2,5,19,[[.s 87 0,.s 87 0],[.s 65 0,.s 65 0],[.f ⟨3,5,0,0,0,0,0,0,0⟩,.f ⟨3,5,1,0,1,0,0,0,0⟩],[.s 67 0,.s 67 0],[.s 91 0,.s 91 0]],[.s 87 3,.s 87 3]⟩,
⟨5,-2,6,23,[[.s 88 0,.s 88 0],[.f ⟨3,4,0,0,0,0,0,0,0⟩,.f ⟨3,4,1,0,1,0,0,0,0⟩],[.s 66 0,.s 66 0],[.f ⟨3,6,0,0,0,0,0,0,0⟩,.f ⟨3,6,1,0,1,0,0,0,0⟩],[.s 92 0,.s 92 0],[.f ⟨3,8,0,0,0,0,0,0,0⟩,.f ⟨3,8,1,0,1,0,0,0,0⟩]],[.s 92 1,.s 92 1]⟩,
⟨5,-2,7,20,[[.s 89 0,.s 89 0],[.f ⟨3,5,0,0,0,0,0,0,0⟩,.f ⟨3,5,1,0,1,0,0,0,0⟩],[.s 67 0,.s 67 0],[.f ⟨3,7,0,0,0,0,0,0,0⟩,.f ⟨3,7,1,0,1,0,0,0,0⟩],[.s 93 0,.s 93 0],[.f ⟨3,9,0,0,0,0,0,0,0⟩,.f ⟨3,9,1,0,1,0,0,0,0⟩]],[.s 89 4,.s 89 4]⟩,
⟨5,-2,8,22,[[.s 66 0,.s 66 0],[.s 90 0,.s 90 0],[.s 68 0,.s 68 0],[.f ⟨3,8,0,0,0,0,0,0,0⟩,.f ⟨3,8,1,0,1,0,0,0,0⟩],[.s 70 0,.s 70 0],[.s 94 0,.s 94 0]],[.s 70 1,.s 70 1]⟩,
⟨5,-2,9,20,[[.s 67 0,.s 67 0],[.s 91 0,.s 91 0],[.s 69 0,.s 69 0],[.f ⟨3,9,0,0,0,0,0,0,0⟩,.f ⟨3,9,1,0,1,0,0,0,0⟩],[.s 71 0,.s 71 0],[.s 95 0,.s 95 0]],[.s 67 5,.s 67 5]⟩,
⟨5,-2,10,22,[[.s 92 0,.s 92 0],[.f ⟨3,8,0,0,0,0,0,0,0⟩,.f ⟨3,8,1,0,1,0,0,0,0⟩],[.s 70 0,.s 70 0],[.f ⟨3,10,0,0,0,0,0,0,0⟩,.f ⟨3,10,1,0,1,0,0,0,0⟩],[.s 95 0,.s 95 0]],[.s 70 3,.s 70 3]⟩,
⟨5,-2,11,21,[[.s 93 0,.s 93 0],[.f ⟨3,9,0,0,0,0,0,0,0⟩,.f ⟨3,9,1,0,1,0,0,0,0⟩],[.s 94 0,.s 94 0],[.s 71 0,.s 71 0],[.f ⟨3,11,0,0,0,0,0,0,0⟩,.f ⟨3,11,1,0,1,0,0,0,0⟩]],[.s 93 5,.s 93 5]⟩]⟩,
⟨2,-3,-1,6,-2,[(-2,-6,9),(1,-3,3)],-2,-6,9,12,1,-3,3,12,12,24,2,1,
[⟨-3,-2,0,27,[[.f ⟨13,0,0,0,0,0,0,0,0⟩,.f ⟨13,0,1,0,1,0,0,0,0⟩,.s 96 0,.s 96 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0]],[.s 1 0,.s 1 0,.s 1 0,.s 1 0]⟩,
⟨-3,-2,1,26,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨13,1,0,0,0,0,0,0,0⟩,.f ⟨13,1,1,0,1,0,0,0,0⟩,.s 97 0,.s 97 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]⟩,
⟨-3,-2,2,25,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨13,2,0,0,0,0,0,0,0⟩,.f ⟨13,2,1,0,1,0,0,0,0⟩,.s 98 0,.s 98 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]⟩,
⟨-3,-2,3,16,[[.f ⟨1,0,0,0,0,0,0,0,0⟩,.f ⟨1,0,1,0,1,0,0,0,0⟩,.s 120 0,.s 120 0],[.f ⟨13,3,0,0,0,0,0,0,0⟩,.f ⟨13,3,1,0,1,0,0,0,0⟩,.s 99 0,.s 99 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.f ⟨1,0,0,0,0,0,0,0,3⟩,.f ⟨1,0,1,0,1,0,0,0,3⟩,.s 120 3,.s 120 3]⟩,
⟨-3,-2,4,24,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.f ⟨13,4,0,0,0,0,0,0,0⟩,.f ⟨13,4,1,0,1,0,0,0,0⟩,.s 100 0,.s 100 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨13,6,0,0,0,0,0,0,0⟩,.f ⟨13,6,1,0,1,0,0,0,0⟩,.s 102 0,.s 102 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.f ⟨13,6,0,0,0,0,0,0,1⟩,.f ⟨13,6,1,0,1,0,0,0,1⟩,.s 102 1,.s 102 1]⟩,
⟨-3,-2,5,17,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.f ⟨13,5,0,0,0,0,0,0,0⟩,.f ⟨13,5,1,0,1,0,0,0,0⟩,.s 101 0,.s 101 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨13,7,0,0,0,0,0,0,0⟩,.f ⟨13,7,1,0,1,0,0,0,0⟩,.s 103 0,.s 103 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.s 3 3,.s 3 3,.s 3 3,.s 3 3]⟩,
⟨-3,-2,6,23,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨13,6,0,0,0,0,0,0,0⟩,.f ⟨13,6,1,0,1,0,0,0,0⟩,.s 102 0,.s 102 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 8 1,.s 8 1,.s 8 1,.s 8 1]⟩,
⟨-3,-2,7,18,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨13,7,0,0,0,0,0,0,0⟩,.f ⟨13,7,1,0,1,0,0,0,0⟩,.s 103 0,.s 103 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 5 4,.s 5 4,.s 5 4,.s 5 4]⟩,
⟨-3,-2,8,22,[[.f ⟨13,6,0,0,0,0,0,0,0⟩,.f ⟨13,6,1,0,1,0,0,0,0⟩,.s 102 0,.s 102 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨13,8,0,0,0,0,0,0,0⟩,.f ⟨13,8,1,0,1,0,0,0,0⟩,.s 104 0,.s 104 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨13,10,0,0,0,0,0,0,0⟩,.f ⟨13,10,1,0,1,0,0,0,0⟩,.s 106 0,.s 106 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.f ⟨13,10,0,0,0,0,0,0,1⟩,.f ⟨13,10,1,0,1,0,0,0,1⟩,.s 106 1,.s 106 1]⟩,
⟨-3,-2,9,19,[[.f ⟨13,7,0,0,0,0,0,0,0⟩,.f ⟨13,7,1,0,1,0,0,0,0⟩,.s 103 0,.s 103 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.f ⟨13,9,0,0,0,0,0,0,0⟩,.f ⟨13,9,1,0,1,0,0,0,0⟩,.s 105 0,.s 105 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.f ⟨13,11,0,0,0,0,0,0,0⟩,.f ⟨13,11,1,0,1,0,0,0,0⟩,.s 107 0,.s 107 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.f ⟨13,7,0,0,0,0,0,0,5⟩,.f ⟨13,7,1,0,1,0,0,0,5⟩,.s 103 5,.s 103 5]⟩,
⟨-3,-2,10,21,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨13,10,0,0,0,0,0,0,0⟩,.f ⟨13,10,1,0,1,0,0,0,0⟩,.s 106 0,.s 106 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 11 2,.s 11 2,.s 11 2,.s 11 2]⟩,
⟨-3,-2,11,20,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.f ⟨13,11,0,0,0,0,0,0,0⟩,.f ⟨13,11,1,0,1,0,0,0,0⟩,.s 107 0,.s 107 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 9 5,.s 9 5,.s 9 5,.s 9 5]⟩,
⟨-2,-2,0,27,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0]],[.s 13 0,.s 13 0,.s 13 0,.s 13 0]⟩,
⟨-2,-2,1,26,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]⟩,
⟨-2,-2,2,25,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]⟩,
⟨-2,-2,3,16,[[.f ⟨13,12,0,0,0,0,0,0,0⟩,.f ⟨13,12,1,0,1,0,0,0,0⟩,.s 132 0,.s 132 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.f ⟨13,12,0,0,0,0,0,0,3⟩,.f ⟨13,12,1,0,1,0,0,0,3⟩,.s 132 3,.s 132 3]⟩,
⟨-2,-2,4,24,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0]],[.s 6 1,.s 6 1,.s 6 1,.s 6 1]⟩,
⟨-2,-2,5,17,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0]],[.s 15 3,.s 15 3,.s 15 3,.s 15 3]⟩,
⟨-2,-2,6,23,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0]],[.s 20 1,.s 20 1,.s 20 1,.s 20 1]⟩,
⟨-2,-2,7,18,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0]],[.s 17 4,.s 17 4,.s 17 4,.s 17 4]⟩,
⟨-2,-2,8,22,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.s 10 1,.s 10 1,.s 10 1,.s 10 1]⟩,
⟨-2,-2,9,19,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 7 5,.s 7 5,.s 7 5,.s 7 5]⟩,
⟨-2,-2,10,21,[[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 23 2,.s 23 2,.s 23 2,.s 23 2]⟩,
⟨-2,-2,11,20,[[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 21 5,.s 21 5,.s 21 5,.s 21 5]⟩,
⟨-1,-3,0,39,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 111 0,.s 111 0,.s 111 0,.s 111 0]],[.s 25 0,.s 25 0,.s 25 0,.s 25 0]⟩,
⟨-1,-3,1,38,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]⟩,
⟨-1,-3,2,37,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]⟩,
⟨-1,-3,3,28,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0]],[.s 36 3,.s 36 3,.s 36 3,.s 36 3]⟩,
⟨-1,-3,4,36,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0]],[.s 90 1,.s 90 1,.s 90 1,.s 90 1]⟩,
⟨-1,-3,5,29,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 27 3,.s 27 3,.s 27 3,.s 27 3]⟩,
⟨-1,-3,6,35,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0]],[.s 32 1,.s 32 1,.s 32 1,.s 32 1]⟩,
⟨-1,-3,7,30,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0]],[.s 29 4,.s 29 4,.s 29 4,.s 29 4]⟩,
⟨-1,-3,8,34,[[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.s 94 1,.s 94 1,.s 94 1,.s 94 1]⟩,
⟨-1,-3,9,31,[[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 91 5,.s 91 5,.s 91 5,.s 91 5]⟩,
⟨-1,-3,10,33,[[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 35 2,.s 35 2,.s 35 2,.s 35 2]⟩,
⟨-1,-3,11,32,[[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 33 5,.s 33 5,.s 33 5,.s 33 5]⟩,
⟨-1,-2,0,27,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0]],[.s 37 0,.s 37 0,.s 37 0,.s 37 0]⟩,
⟨-1,-2,1,26,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]⟩,
⟨-1,-2,2,25,[[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0]],[.s 40 0,.s 40 0,.s 40 0,.s 40 0]⟩,
⟨-1,-2,3,16,[[.f ⟨12,0,0,0,0,0,0,0,0⟩,.f ⟨13,0,1,0,0,0,0,0,0⟩,.f ⟨14,72,0,1,0,0,0,0,0⟩,.s 96 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0]],[.f ⟨12,0,0,0,0,0,0,0,3⟩,.f ⟨13,0,1,0,0,0,0,0,3⟩,.f ⟨14,72,0,1,0,0,0,0,3⟩,.s 96 3]⟩,
⟨-1,-2,4,24,[[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.s 18 1,.s 18 1,.s 18 1,.s 18 1]⟩,
⟨-1,-2,5,17,[[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 39 3,.s 39 3,.s 39 3,.s 39 3]⟩,
⟨-1,-2,6,23,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0]],[.s 44 1,.s 44 1,.s 44 1,.s 44 1]⟩,
⟨-1,-2,7,18,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0]],[.s 41 4,.s 41 4,.s 41 4,.s 41 4]⟩,
⟨-1,-2,8,22,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0]],[.s 22 1,.s 22 1,.s 22 1,.s 22 1]⟩,
⟨-1,-2,9,19,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 19 5,.s 19 5,.s 19 5,.s 19 5]⟩,
⟨-1,-2,10,21,[[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 47 2,.s 47 2,.s 47 2,.s 47 2]⟩,
⟨-1,-2,11,20,[[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 45 5,.s 45 5,.s 45 5,.s 45 5]⟩,
⟨0,-3,0,39,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 123 0,.s 123 0,.s 123 0,.s 123 0]],[.s 49 0,.s 49 0,.s 49 0,.s 49 0]⟩,
⟨0,-3,1,38,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0]],[.s 50 0,.s 50 0,.s 50 0,.s 50 0]⟩,
⟨0,-3,2,37,[[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0]],[.s 52 0,.s 52 0,.s 52 0,.s 52 0]⟩,
⟨0,-3,3,28,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]],[.s 60 3,.s 60 3,.s 60 3,.s 60 3]⟩,
⟨0,-3,4,36,[[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0]],[.s 30 1,.s 30 1,.s 30 1,.s 30 1]⟩,
⟨0,-3,5,29,[[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0]],[.s 51 3,.s 51 3,.s 51 3,.s 51 3]⟩,
⟨0,-3,6,35,[[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0]],[.s 56 1,.s 56 1,.s 56 1,.s 56 1]⟩,
⟨0,-3,7,30,[[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0]],[.s 53 4,.s 53 4,.s 53 4,.s 53 4]⟩,
⟨0,-3,8,34,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0]],[.s 34 1,.s 34 1,.s 34 1,.s 34 1]⟩,
⟨0,-3,9,31,[[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 31 5,.s 31 5,.s 31 5,.s 31 5]⟩,
⟨0,-3,10,33,[[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 59 2,.s 59 2,.s 59 2,.s 59 2]⟩,
⟨0,-3,11,32,[[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0]],[.s 57 5,.s 57 5,.s 57 5,.s 57 5]⟩,
⟨0,-2,0,27,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0]],[.s 61 0,.s 61 0,.s 61 0,.s 61 0]⟩,
⟨0,-2,1,26,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0]],[.s 62 0,.s 62 0,.s 62 0,.s 62 0]⟩,
⟨0,-2,2,25,[[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0]],[.s 64 0,.s 64 0,.s 64 0,.s 64 0]⟩,
⟨0,-2,3,16,[[.f ⟨14,0,0,0,0,0,0,0,0⟩,.s 0 0,.f ⟨14,0,0,1,1,0,0,0,0⟩,.s 0 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0]],[.f ⟨14,0,0,0,0,0,0,0,3⟩,.s 0 3,.f ⟨14,0,0,1,1,0,0,0,3⟩,.s 0 3]⟩,
⟨0,-2,4,24,[[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0]],[.s 42 1,.s 42 1,.s 42 1,.s 42 1]⟩,
⟨0,-2,5,17,[[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0]],[.s 63 3,.s 63 3,.s 63 3,.s 63 3]⟩,
⟨0,-2,6,23,[[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0]],[.s 68 1,.s 68 1,.s 68 1,.s 68 1]⟩,
⟨0,-2,7,18,[[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0]],[.s 65 4,.s 65 4,.s 65 4,.s 65 4]⟩,
⟨0,-2,8,22,[[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0]],[.s 46 1,.s 46 1,.s 46 1,.s 46 1]⟩,
⟨0,-2,9,19,[[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 43 5,.s 43 5,.s 43 5,.s 43 5]⟩,
⟨0,-2,10,21,[[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 71 2,.s 71 2,.s 71 2,.s 71 2]⟩,
⟨0,-2,11,20,[[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0]],[.s 69 5,.s 69 5,.s 69 5,.s 69 5]⟩,
⟨1,-3,0,39,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0]],[.s 73 0,.s 73 0,.s 73 0,.s 73 0]⟩,
⟨1,-3,1,38,[[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0]],[.s 74 0,.s 74 0,.s 74 0,.s 74 0]⟩,
⟨1,-3,2,37,[[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 110 0,.s 110 0,.s 110 0,.s 110 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0]],[.s 76 0,.s 76 0,.s 76 0,.s 76 0]⟩,
⟨1,-3,3,28,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 111 0,.s 111 0,.s 111 0,.s 111 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0]],[.s 84 3,.s 84 3,.s 84 3,.s 84 3]⟩,
⟨1,-3,4,36,[[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 112 0,.s 112 0,.s 112 0,.s 112 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0]],[.s 54 1,.s 54 1,.s 54 1,.s 54 1]⟩,
⟨1,-3,5,29,[[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0]],[.s 75 3,.s 75 3,.s 75 3,.s 75 3]⟩,
⟨1,-3,6,35,[[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 112 0,.s 112 0,.s 112 0,.s 112 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0]],[.s 80 1,.s 80 1,.s 80 1,.s 80 1]⟩,
⟨1,-3,7,30,[[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0]],[.s 77 4,.s 77 4,.s 77 4,.s 77 4]⟩,
⟨1,-3,8,34,[[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0]],[.s 58 1,.s 58 1,.s 58 1,.s 58 1]⟩,
⟨1,-3,9,31,[[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0]],[.s 55 5,.s 55 5,.s 55 5,.s 55 5]⟩,
⟨1,-3,10,33,[[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0]],[.s 83 2,.s 83 2,.s 83 2,.s 83 2]⟩,
⟨1,-3,11,32,[[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0]],[.s 81 5,.s 81 5,.s 81 5,.s 81 5]⟩,
⟨1,-2,0,27,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.f ⟨14,24,0,0,0,0,0,0,0⟩,.s 24 0,.f ⟨14,24,0,1,1,0,0,0,0⟩,.s 24 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0]],[.s 85 0,.s 85 0,.s 85 0,.s 85 0]⟩,
⟨1,-2,1,26,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.f ⟨14,25,0,0,0,0,0,0,0⟩,.s 25 0,.f ⟨14,25,0,1,1,0,0,0,0⟩,.s 25 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0]],[.s 86 0,.s 86 0,.s 86 0,.s 86 0]⟩,
⟨1,-2,2,25,[[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.f ⟨14,26,0,0,0,0,0,0,0⟩,.s 26 0,.f ⟨14,26,0,1,1,0,0,0,0⟩,.s 26 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0]],[.s 88 0,.s 88 0,.s 88 0,.s 88 0]⟩,
⟨1,-2,3,16,[[.f ⟨14,12,0,0,0,0,0,0,0⟩,.s 12 0,.f ⟨14,12,0,1,1,0,0,0,0⟩,.s 12 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.f ⟨14,27,0,0,0,0,0,0,0⟩,.s 27 0,.f ⟨14,27,0,1,1,0,0,0,0⟩,.s 27 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0]],[.f ⟨14,12,0,0,0,0,0,0,3⟩,.s 12 3,.f ⟨14,12,0,1,1,0,0,0,3⟩,.s 12 3]⟩,
⟨1,-2,4,24,[[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.f ⟨14,28,0,0,0,0,0,0,0⟩,.s 28 0,.f ⟨14,28,0,1,1,0,0,0,0⟩,.s 28 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0]],[.s 66 1,.s 66 1,.s 66 1,.s 66 1]⟩,
⟨1,-2,5,17,[[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.f ⟨14,29,0,0,0,0,0,0,0⟩,.s 29 0,.f ⟨14,29,0,1,1,0,0,0,0⟩,.s 29 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0]],[.s 87 3,.s 87 3,.s 87 3,.s 87 3]⟩,
⟨1,-2,6,23,[[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.f ⟨14,28,0,0,0,0,0,0,0⟩,.s 28 0,.f ⟨14,28,0,1,1,0,0,0,0⟩,.s 28 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.f ⟨14,30,0,0,0,0,0,0,0⟩,.s 30 0,.f ⟨14,30,0,1,1,0,0,0,0⟩,.s 30 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.f ⟨14,32,0,0,0,0,0,0,0⟩,.s 32 0,.f ⟨14,32,0,1,1,0,0,0,0⟩,.s 32 0]],[.s 92 1,.s 92 1,.s 92 1,.s 92 1]⟩,
⟨1,-2,7,18,[[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.f ⟨14,29,0,0,0,0,0,0,0⟩,.s 29 0,.f ⟨14,29,0,1,1,0,0,0,0⟩,.s 29 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.f ⟨14,31,0,0,0,0,0,0,0⟩,.s 31 0,.f ⟨14,31,0,1,1,0,0,0,0⟩,.s 31 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.f ⟨14,33,0,0,0,0,0,0,0⟩,.s 33 0,.f ⟨14,33,0,1,1,0,0,0,0⟩,.s 33 0]],[.s 89 4,.s 89 4,.s 89 4,.s 89 4]⟩,
⟨1,-2,8,22,[[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.f ⟨14,32,0,0,0,0,0,0,0⟩,.s 32 0,.f ⟨14,32,0,1,1,0,0,0,0⟩,.s 32 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0]],[.s 70 1,.s 70 1,.s 70 1,.s 70 1]⟩,
⟨1,-2,9,19,[[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.f ⟨14,33,0,0,0,0,0,0,0⟩,.s 33 0,.f ⟨14,33,0,1,1,0,0,0,0⟩,.s 33 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0]],[.s 67 5,.s 67 5,.s 67 5,.s 67 5]⟩,
⟨1,-2,10,21,[[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.f ⟨14,32,0,0,0,0,0,0,0⟩,.s 32 0,.f ⟨14,32,0,1,1,0,0,0,0⟩,.s 32 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.f ⟨14,34,0,0,0,0,0,0,0⟩,.s 34 0,.f ⟨14,34,0,1,1,0,0,0,0⟩,.s 34 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0]],[.s 95 2,.s 95 2,.s 95 2,.s 95 2]⟩,
⟨1,-2,11,20,[[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.f ⟨14,33,0,0,0,0,0,0,0⟩,.s 33 0,.f ⟨14,33,0,1,1,0,0,0,0⟩,.s 33 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.f ⟨14,35,0,0,0,0,0,0,0⟩,.s 35 0,.f ⟨14,35,0,1,1,0,0,0,0⟩,.s 35 0]],[.s 93 5,.s 93 5,.s 93 5,.s 93 5]⟩,
⟨2,-4,0,51,[[.s 132 0,.s 132 0,.s 132 0,.s 132 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 97 0,.s 97 0,.s 97 0,.s 97 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0]],[.s 97 0,.s 97 0,.s 97 0,.s 97 0]⟩,
⟨2,-4,1,50,[[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 98 0,.s 98 0,.s 98 0,.s 98 0]],[.s 98 0,.s 98 0,.s 98 0,.s 98 0]⟩,
⟨2,-4,2,49,[[.s 97 0,.s 97 0,.s 97 0,.s 97 0],[.s 134 0,.s 134 0,.s 134 0,.s 134 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 100 0,.s 100 0,.s 100 0,.s 100 0]],[.s 100 0,.s 100 0,.s 100 0,.s 100 0]⟩,
⟨2,-4,3,40,[[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 101 0,.s 101 0,.s 101 0,.s 101 0]],[.s 108 3,.s 108 3,.s 108 3,.s 108 3]⟩,
⟨2,-4,4,48,[[.s 98 0,.s 98 0,.s 98 0,.s 98 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0]],[.s 138 1,.s 138 1,.s 138 1,.s 138 1]⟩,
⟨2,-4,5,41,[[.s 99 0,.s 99 0,.s 99 0,.s 99 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0]],[.s 99 3,.s 99 3,.s 99 3,.s 99 3]⟩,
⟨2,-4,6,47,[[.s 100 0,.s 100 0,.s 100 0,.s 100 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 104 1,.s 104 1,.s 104 1,.s 104 1]⟩,
⟨2,-4,7,42,[[.s 101 0,.s 101 0,.s 101 0,.s 101 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 101 4,.s 101 4,.s 101 4,.s 101 4]⟩,
⟨2,-4,8,46,[[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0]],[.s 142 1,.s 142 1,.s 142 1,.s 142 1]⟩,
⟨2,-4,9,43,[[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0]],[.s 139 5,.s 139 5,.s 139 5,.s 139 5]⟩,
⟨2,-4,10,45,[[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0]],[.s 107 2,.s 107 2,.s 107 2,.s 107 2]⟩,
⟨2,-4,11,44,[[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 105 5,.s 105 5,.s 105 5,.s 105 5]⟩,
⟨2,-3,0,39,[[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 99 0,.s 99 0,.s 99 0,.s 99 0]],[.s 109 0,.s 109 0,.s 109 0,.s 109 0]⟩,
⟨2,-3,1,38,[[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.s 110 0,.s 110 0,.s 110 0,.s 110 0]],[.s 110 0,.s 110 0,.s 110 0,.s 110 0]⟩,
⟨2,-3,2,37,[[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 122 0,.s 122 0,.s 122 0,.s 122 0],[.s 112 0,.s 112 0,.s 112 0,.s 112 0]],[.s 112 0,.s 112 0,.s 112 0,.s 112 0]⟩,
⟨2,-3,3,28,[[.f ⟨14,24,0,0,0,0,0,0,0⟩,.s 24 0,.f ⟨14,24,0,1,1,0,0,0,0⟩,.s 24 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.s 123 0,.s 123 0,.s 123 0,.s 123 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0]],[.f ⟨14,24,0,0,0,0,0,0,3⟩,.s 24 3,.f ⟨14,24,0,1,1,0,0,0,3⟩,.s 24 3]⟩,
⟨2,-3,4,36,[[.s 110 0,.s 110 0,.s 110 0,.s 110 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0]],[.s 78 1,.s 78 1,.s 78 1,.s 78 1]⟩,
⟨2,-3,5,29,[[.s 111 0,.s 111 0,.s 111 0,.s 111 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0]],[.s 111 3,.s 111 3,.s 111 3,.s 111 3]⟩,
⟨2,-3,6,35,[[.s 112 0,.s 112 0,.s 112 0,.s 112 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0]],[.s 116 1,.s 116 1,.s 116 1,.s 116 1]⟩,
⟨2,-3,7,30,[[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0]],[.s 113 4,.s 113 4,.s 113 4,.s 113 4]⟩,
⟨2,-3,8,34,[[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0]],[.s 82 1,.s 82 1,.s 82 1,.s 82 1]⟩,
⟨2,-3,9,31,[[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0]],[.s 79 5,.s 79 5,.s 79 5,.s 79 5]⟩,
⟨2,-3,10,33,[[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0]],[.s 119 2,.s 119 2,.s 119 2,.s 119 2]⟩,
⟨2,-3,11,32,[[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0]],[.s 117 5,.s 117 5,.s 117 5,.s 117 5]⟩,
⟨3,-3,0,39,[[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 132 0,.s 132 0,.s 132 0,.s 132 0],[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.s 121 0,.s 121 0,.s 121 0,.s 121 0]⟩,
⟨3,-3,1,38,[[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 122 0,.s 122 0,.s 122 0,.s 122 0]],[.s 122 0,.s 122 0,.s 122 0,.s 122 0]⟩,
⟨3,-3,2,37,[[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.s 110 0,.s 110 0,.s 110 0,.s 110 0],[.s 134 0,.s 134 0,.s 134 0,.s 134 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0]],[.s 124 0,.s 124 0,.s 124 0,.s 124 0]⟩,
⟨3,-3,3,28,[[.f ⟨14,48,0,0,0,0,0,0,0⟩,.s 48 0,.f ⟨14,48,0,1,1,0,0,0,0⟩,.s 48 0],[.s 111 0,.s 111 0,.s 111 0,.s 111 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0]],[.f ⟨14,48,0,0,0,0,0,0,3⟩,.s 48 3,.f ⟨14,48,0,1,1,0,0,0,3⟩,.s 48 3]⟩,
⟨3,-3,4,36,[[.s 122 0,.s 122 0,.s 122 0,.s 122 0],[.s 112 0,.s 112 0,.s 112 0,.s 112 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0]],[.s 114 1,.s 114 1,.s 114 1,.s 114 1]⟩,
⟨3,-3,5,29,[[.s 123 0,.s 123 0,.s 123 0,.s 123 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0]],[.s 123 3,.s 123 3,.s 123 3,.s 123 3]⟩,
⟨3,-3,6,35,[[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0]],[.s 128 1,.s 128 1,.s 128 1,.s 128 1]⟩,
⟨3,-3,7,30,[[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0]],[.s 125 4,.s 125 4,.s 125 4,.s 125 4]⟩,
⟨3,-3,8,34,[[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0]],[.s 118 1,.s 118 1,.s 118 1,.s 118 1]⟩,
⟨3,-3,9,31,[[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0]],[.s 115 5,.s 115 5,.s 115 5,.s 115 5]⟩,
⟨3,-3,10,33,[[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0]],[.s 131 2,.s 131 2,.s 131 2,.s 131 2]⟩,
⟨3,-3,11,32,[[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0]],[.s 129 5,.s 129 5,.s 129 5,.s 129 5]⟩,
⟨4,-3,0,39,[[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.f ⟨14,72,0,0,0,0,0,0,0⟩,.s 96 0,.f ⟨14,72,0,1,1,0,0,0,0⟩,.s 96 0],[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]],[.s 133 0,.s 133 0,.s 133 0,.s 133 0]⟩,
⟨4,-3,1,38,[[.s 132 0,.s 132 0,.s 132 0,.s 132 0],[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.f ⟨14,73,0,0,0,0,0,0,0⟩,.s 97 0,.f ⟨14,73,0,1,1,0,0,0,0⟩,.s 97 0],[.s 134 0,.s 134 0,.s 134 0,.s 134 0]],[.s 134 0,.s 134 0,.s 134 0,.s 134 0]⟩,
⟨4,-3,2,37,[[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 122 0,.s 122 0,.s 122 0,.s 122 0],[.f ⟨14,74,0,0,0,0,0,0,0⟩,.s 98 0,.f ⟨14,74,0,1,1,0,0,0,0⟩,.s 98 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0]],[.s 136 0,.s 136 0,.s 136 0,.s 136 0]⟩,
⟨4,-3,3,28,[[.f ⟨14,60,0,0,0,0,0,0,0⟩,.s 72 0,.f ⟨14,60,0,1,1,0,0,0,0⟩,.s 72 0],[.s 123 0,.s 123 0,.s 123 0,.s 123 0],[.f ⟨14,75,0,0,0,0,0,0,0⟩,.s 99 0,.f ⟨14,75,0,1,1,0,0,0,0⟩,.s 99 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0]],[.f ⟨14,60,0,0,0,0,0,0,3⟩,.s 72 3,.f ⟨14,60,0,1,1,0,0,0,3⟩,.s 72 3]⟩,
⟨4,-3,4,36,[[.s 134 0,.s 134 0,.s 134 0,.s 134 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.f ⟨14,76,0,0,0,0,0,0,0⟩,.s 100 0,.f ⟨14,76,0,1,1,0,0,0,0⟩,.s 100 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0]],[.s 126 1,.s 126 1,.s 126 1,.s 126 1]⟩,
⟨4,-3,5,29,[[.s 135 0,.s 135 0,.s 135 0,.s 135 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.f ⟨14,77,0,0,0,0,0,0,0⟩,.s 101 0,.f ⟨14,77,0,1,1,0,0,0,0⟩,.s 101 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0]],[.s 135 3,.s 135 3,.s 135 3,.s 135 3]⟩,
⟨4,-3,6,35,[[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.f ⟨14,76,0,0,0,0,0,0,0⟩,.s 100 0,.f ⟨14,76,0,1,1,0,0,0,0⟩,.s 100 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.f ⟨14,78,0,0,0,0,0,0,0⟩,.s 102 0,.f ⟨14,78,0,1,1,0,0,0,0⟩,.s 102 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.f ⟨14,80,0,0,0,0,0,0,0⟩,.s 104 0,.f ⟨14,80,0,1,1,0,0,0,0⟩,.s 104 0]],[.s 140 1,.s 140 1,.s 140 1,.s 140 1]⟩,
⟨4,-3,7,30,[[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.f ⟨14,77,0,0,0,0,0,0,0⟩,.s 101 0,.f ⟨14,77,0,1,1,0,0,0,0⟩,.s 101 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.f ⟨14,79,0,0,0,0,0,0,0⟩,.s 103 0,.f ⟨14,79,0,1,1,0,0,0,0⟩,.s 103 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.f ⟨14,81,0,0,0,0,0,0,0⟩,.s 105 0,.f ⟨14,81,0,1,1,0,0,0,0⟩,.s 105 0]],[.s 137 4,.s 137 4,.s 137 4,.s 137 4]⟩,
⟨4,-3,8,34,[[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.f ⟨14,80,0,0,0,0,0,0,0⟩,.s 104 0,.f ⟨14,80,0,1,1,0,0,0,0⟩,.s 104 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0]],[.s 130 1,.s 130 1,.s 130 1,.s 130 1]⟩,
⟨4,-3,9,31,[[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.f ⟨14,81,0,0,0,0,0,0,0⟩,.s 105 0,.f ⟨14,81,0,1,1,0,0,0,0⟩,.s 105 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0]],[.s 127 5,.s 127 5,.s 127 5,.s 127 5]⟩,
⟨4,-3,10,33,[[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.f ⟨14,80,0,0,0,0,0,0,0⟩,.s 104 0,.f ⟨14,80,0,1,1,0,0,0,0⟩,.s 104 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.f ⟨14,82,0,0,0,0,0,0,0⟩,.s 106 0,.f ⟨14,82,0,1,1,0,0,0,0⟩,.s 106 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0]],[.s 143 2,.s 143 2,.s 143 2,.s 143 2]⟩,
⟨4,-3,11,32,[[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.f ⟨14,81,0,0,0,0,0,0,0⟩,.s 105 0,.f ⟨14,81,0,1,1,0,0,0,0⟩,.s 105 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0],[.f ⟨14,83,0,0,0,0,0,0,0⟩,.s 107 0,.f ⟨14,83,0,1,1,0,0,0,0⟩,.s 107 0]],[.s 141 5,.s 141 5,.s 141 5,.s 141 5]⟩]⟩,
⟨0,0,0,0,0,[(0,-3,1),(2,6,1),(0,3,-3),(-2,-6,-2)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨4,-1,0,16,[[.f ⟨2,0,0,0,0,0,0,0,0⟩],[.f ⟨18,0,0,0,0,0,0,0,0⟩],[.s 1 0],[.f ⟨14,63,0,0,0,0,0,0,0⟩]],[.f ⟨2,0,0,0,0,0,0,0,1⟩]⟩,
⟨4,-1,1,15,[[.s 0 0],[.f ⟨2,1,0,0,0,0,0,0,0⟩],[.f ⟨18,1,0,0,0,0,0,0,0⟩],[.s 2 0]],[.f ⟨2,1,0,0,0,0,0,0,2⟩]⟩,
⟨4,-1,2,14,[[.s 1 0],[.f ⟨2,2,0,0,0,0,0,0,0⟩],[.f ⟨18,2,0,0,0,0,0,0,0⟩],[.s 4 0]],[.f ⟨2,2,0,0,0,0,0,0,2⟩]⟩,
⟨4,-1,3,8,[[.f ⟨4,36,0,0,0,0,0,0,0⟩],[.f ⟨2,3,0,0,0,0,0,0,0⟩],[.f ⟨18,3,0,0,0,0,0,0,0⟩],[.s 5 0]],[.f ⟨4,36,0,0,0,0,0,0,3⟩]⟩,
⟨4,-1,4,13,[[.s 2 0],[.f ⟨2,4,0,0,0,0,0,0,0⟩],[.f ⟨18,4,0,0,0,0,0,0,0⟩],[.f ⟨2,6,0,0,0,0,0,0,0⟩],[.s 6 0]],[.f ⟨2,4,0,0,0,0,0,0,2⟩]⟩,
⟨4,-1,5,9,[[.s 3 0],[.f ⟨2,5,0,0,0,0,0,0,0⟩],[.f ⟨18,5,0,0,0,0,0,0,0⟩],[.f ⟨2,7,0,0,0,0,0,0,0⟩],[.s 7 0]],[.s 3 3]⟩,
⟨4,-1,6,13,[[.s 4 0],[.f ⟨18,4,0,0,0,0,0,0,0⟩],[.f ⟨2,6,0,0,0,0,0,0,0⟩],[.f ⟨18,6,0,0,0,0,0,0,0⟩],[.s 8 0],[.f ⟨18,8,0,0,0,0,0,0,0⟩]],[.f ⟨2,6,0,0,0,0,0,0,3⟩]⟩,
⟨4,-1,7,10,[[.s 5 0],[.f ⟨18,5,0,0,0,0,0,0,0⟩],[.f ⟨2,7,0,0,0,0,0,0,0⟩],[.f ⟨18,7,0,0,0,0,0,0,0⟩],[.s 9 0],[.f ⟨18,9,0,0,0,0,0,0,0⟩]],[.s 5 4]⟩,
⟨4,-1,8,12,[[.f ⟨2,6,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨2,8,0,0,0,0,0,0,0⟩],[.f ⟨18,8,0,0,0,0,0,0,0⟩],[.f ⟨2,10,0,0,0,0,0,0,0⟩],[.s 10 0]],[.f ⟨2,8,0,0,0,0,0,0,3⟩]⟩,
⟨4,-1,9,10,[[.f ⟨2,7,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨2,9,0,0,0,0,0,0,0⟩],[.f ⟨18,9,0,0,0,0,0,0,0⟩],[.f ⟨2,11,0,0,0,0,0,0,0⟩],[.s 11 0]],[.f ⟨2,7,0,0,0,0,0,0,5⟩]⟩,
⟨4,-1,10,12,[[.s 8 0],[.f ⟨18,8,0,0,0,0,0,0,0⟩],[.f ⟨2,10,0,0,0,0,0,0,0⟩],[.f ⟨18,10,0,0,0,0,0,0,0⟩],[.s 11 0]],[.f ⟨2,10,0,0,0,0,0,0,3⟩]⟩,
⟨4,-1,11,11,[[.s 9 0],[.f ⟨18,9,0,0,0,0,0,0,0⟩],[.s 10 0],[.f ⟨2,11,0,0,0,0,0,0,0⟩],[.f ⟨18,11,0,0,0,0,0,0,0⟩]],[.s 9 5]⟩]⟩,
⟨1,6,-2,0,0,[(0,-3,4),(2,6,1),(-2,-6,-2)],0,-3,4,6,0,0,0,0,24,0,0,0,
[⟨7,-2,0,28,[[.f ⟨3,0,0,0,0,0,0,0,0⟩,.f ⟨3,0,1,0,1,0,0,0,0⟩],[.f ⟨19,0,0,0,0,0,0,0,0⟩,.f ⟨19,0,1,0,1,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨14,15,0,0,1,0,0,0,0⟩,.f ⟨14,15,1,0,2,0,0,0,0⟩]],[.f ⟨3,0,0,0,0,0,0,0,1⟩,.f ⟨3,0,1,0,1,0,0,0,1⟩]⟩,
⟨7,-2,1,27,[[.s 0 0,.s 0 0],[.f ⟨3,1,0,0,0,0,0,0,0⟩,.f ⟨3,1,1,0,1,0,0,0,0⟩],[.f ⟨19,1,0,0,0,0,0,0,0⟩,.f ⟨19,1,1,0,1,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.f ⟨3,1,0,0,0,0,0,0,2⟩,.f ⟨3,1,1,0,1,0,0,0,2⟩]⟩,
⟨7,-2,2,26,[[.s 1 0,.s 1 0],[.f ⟨3,2,0,0,0,0,0,0,0⟩,.f ⟨3,2,1,0,1,0,0,0,0⟩],[.f ⟨19,2,0,0,0,0,0,0,0⟩,.f ⟨19,2,1,0,1,0,0,0,0⟩],[.s 4 0,.s 4 0]],[.f ⟨3,2,0,0,0,0,0,0,2⟩,.f ⟨3,2,1,0,1,0,0,0,2⟩]⟩,
⟨7,-2,3,20,[[.f ⟨18,24,0,0,0,0,0,0,0⟩,.f ⟨19,60,1,0,0,0,0,0,0⟩],[.f ⟨3,3,0,0,0,0,0,0,0⟩,.f ⟨3,3,1,0,1,0,0,0,0⟩],[.f ⟨19,3,0,0,0,0,0,0,0⟩,.f ⟨19,3,1,0,1,0,0,0,0⟩],[.s 5 0,.s 5 0]],[.f ⟨18,24,0,0,0,0,0,0,3⟩,.f ⟨19,60,1,0,0,0,0,0,3⟩]⟩,
⟨7,-2,4,25,[[.s 2 0,.s 2 0],[.f ⟨3,4,0,0,0,0,0,0,0⟩,.f ⟨3,4,1,0,1,0,0,0,0⟩],[.f ⟨19,4,0,0,0,0,0,0,0⟩,.f ⟨19,4,1,0,1,0,0,0,0⟩],[.f ⟨3,6,0,0,0,0,0,0,0⟩,.f ⟨3,6,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.f ⟨3,4,0,0,0,0,0,0,2⟩,.f ⟨3,4,1,0,1,0,0,0,2⟩]⟩,
⟨7,-2,5,21,[[.s 3 0,.s 3 0],[.f ⟨3,5,0,0,0,0,0,0,0⟩,.f ⟨3,5,1,0,1,0,0,0,0⟩],[.f ⟨19,5,0,0,0,0,0,0,0⟩,.f ⟨19,5,1,0,1,0,0,0,0⟩],[.f ⟨3,7,0,0,0,0,0,0,0⟩,.f ⟨3,7,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨7,-2,6,25,[[.s 4 0,.s 4 0],[.f ⟨19,4,0,0,0,0,0,0,0⟩,.f ⟨19,4,1,0,1,0,0,0,0⟩],[.f ⟨3,6,0,0,0,0,0,0,0⟩,.f ⟨3,6,1,0,1,0,0,0,0⟩],[.f ⟨19,6,0,0,0,0,0,0,0⟩,.f ⟨19,6,1,0,1,0,0,0,0⟩],[.s 8 0,.s 8 0],[.f ⟨19,8,0,0,0,0,0,0,0⟩,.f ⟨19,8,1,0,1,0,0,0,0⟩]],[.f ⟨3,6,0,0,0,0,0,0,3⟩,.f ⟨3,6,1,0,1,0,0,0,3⟩]⟩,
⟨7,-2,7,22,[[.s 5 0,.s 5 0],[.f ⟨19,5,0,0,0,0,0,0,0⟩,.f ⟨19,5,1,0,1,0,0,0,0⟩],[.f ⟨3,7,0,0,0,0,0,0,0⟩,.f ⟨3,7,1,0,1,0,0,0,0⟩],[.f ⟨19,7,0,0,0,0,0,0,0⟩,.f ⟨19,7,1,0,1,0,0,0,0⟩],[.s 9 0,.s 9 0],[.f ⟨19,9,0,0,0,0,0,0,0⟩,.f ⟨19,9,1,0,1,0,0,0,0⟩]],[.s 5 4,.s 5 4]⟩,
⟨7,-2,8,24,[[.f ⟨3,6,0,0,0,0,0,0,0⟩,.f ⟨3,6,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.f ⟨3,8,0,0,0,0,0,0,0⟩,.f ⟨3,8,1,0,1,0,0,0,0⟩],[.f ⟨19,8,0,0,0,0,0,0,0⟩,.f ⟨19,8,1,0,1,0,0,0,0⟩],[.f ⟨3,10,0,0,0,0,0,0,0⟩,.f ⟨3,10,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0]],[.f ⟨3,8,0,0,0,0,0,0,3⟩,.f ⟨3,8,1,0,1,0,0,0,3⟩]⟩,
⟨7,-2,9,22,[[.f ⟨3,7,0,0,0,0,0,0,0⟩,.f ⟨3,7,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨3,9,0,0,0,0,0,0,0⟩,.f ⟨3,9,1,0,1,0,0,0,0⟩],[.f ⟨19,9,0,0,0,0,0,0,0⟩,.f ⟨19,9,1,0,1,0,0,0,0⟩],[.f ⟨3,11,0,0,0,0,0,0,0⟩,.f ⟨3,11,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨3,7,0,0,0,0,0,0,5⟩,.f ⟨3,7,1,0,1,0,0,0,5⟩]⟩,
⟨7,-2,10,24,[[.s 8 0,.s 8 0],[.f ⟨19,8,0,0,0,0,0,0,0⟩,.f ⟨19,8,1,0,1,0,0,0,0⟩],[.f ⟨3,10,0,0,0,0,0,0,0⟩,.f ⟨3,10,1,0,1,0,0,0,0⟩],[.f ⟨19,10,0,0,0,0,0,0,0⟩,.f ⟨19,10,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨3,10,0,0,0,0,0,0,3⟩,.f ⟨3,10,1,0,1,0,0,0,3⟩]⟩,
⟨7,-2,11,23,[[.s 9 0,.s 9 0],[.f ⟨19,9,0,0,0,0,0,0,0⟩,.f ⟨19,9,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0],[.f ⟨3,11,0,0,0,0,0,0,0⟩,.f ⟨3,11,1,0,1,0,0,0,0⟩],[.f ⟨19,11,0,0,0,0,0,0,0⟩,.f ⟨19,11,1,0,1,0,0,0,0⟩]],[.s 9 5,.s 9 5]⟩,
⟨10,-3,0,40,[[.f ⟨3,12,0,0,0,0,0,0,0⟩,.f ⟨3,12,1,0,1,0,0,0,0⟩],[.f ⟨19,36,0,0,0,0,0,0,0⟩,.f ⟨19,36,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.f ⟨14,63,0,0,1,0,0,0,0⟩,.f ⟨14,63,1,0,2,0,0,0,0⟩]],[.f ⟨3,12,0,0,0,0,0,0,1⟩,.f ⟨3,12,1,0,1,0,0,0,1⟩]⟩,
⟨10,-3,1,39,[[.s 12 0,.s 12 0],[.f ⟨3,13,0,0,0,0,0,0,0⟩,.f ⟨3,13,1,0,1,0,0,0,0⟩],[.f ⟨19,37,0,0,0,0,0,0,0⟩,.f ⟨19,37,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0]],[.f ⟨3,13,0,0,0,0,0,0,2⟩,.f ⟨3,13,1,0,1,0,0,0,2⟩]⟩,
⟨10,-3,2,38,[[.s 13 0,.s 13 0],[.f ⟨3,14,0,0,0,0,0,0,0⟩,.f ⟨3,14,1,0,1,0,0,0,0⟩],[.f ⟨19,38,0,0,0,0,0,0,0⟩,.f ⟨19,38,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0]],[.f ⟨3,14,0,0,0,0,0,0,2⟩,.f ⟨3,14,1,0,1,0,0,0,2⟩]⟩,
⟨10,-3,3,32,[[.f ⟨19,24,0,0,0,0,0,0,0⟩,.f ⟨19,24,1,0,1,0,0,0,0⟩],[.f ⟨3,15,0,0,0,0,0,0,0⟩,.f ⟨3,15,1,0,1,0,0,0,0⟩],[.f ⟨19,39,0,0,0,0,0,0,0⟩,.f ⟨19,39,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0]],[.f ⟨19,24,0,0,0,0,0,0,3⟩,.f ⟨19,24,1,0,1,0,0,0,3⟩]⟩,
⟨10,-3,4,37,[[.s 14 0,.s 14 0],[.f ⟨3,16,0,0,0,0,0,0,0⟩,.f ⟨3,16,1,0,1,0,0,0,0⟩],[.f ⟨19,40,0,0,0,0,0,0,0⟩,.f ⟨19,40,1,0,1,0,0,0,0⟩],[.f ⟨3,18,0,0,0,0,0,0,0⟩,.f ⟨3,18,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0]],[.f ⟨3,16,0,0,0,0,0,0,2⟩,.f ⟨3,16,1,0,1,0,0,0,2⟩]⟩,
⟨10,-3,5,33,[[.s 15 0,.s 15 0],[.f ⟨3,17,0,0,0,0,0,0,0⟩,.f ⟨3,17,1,0,1,0,0,0,0⟩],[.f ⟨19,41,0,0,0,0,0,0,0⟩,.f ⟨19,41,1,0,1,0,0,0,0⟩],[.f ⟨3,19,0,0,0,0,0,0,0⟩,.f ⟨3,19,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0]],[.s 15 3,.s 15 3]⟩,
⟨10,-3,6,37,[[.s 16 0,.s 16 0],[.f ⟨19,40,0,0,0,0,0,0,0⟩,.f ⟨19,40,1,0,1,0,0,0,0⟩],[.f ⟨3,18,0,0,0,0,0,0,0⟩,.f ⟨3,18,1,0,1,0,0,0,0⟩],[.f ⟨19,42,0,0,0,0,0,0,0⟩,.f ⟨19,42,1,0,1,0,0,0,0⟩],[.s 20 0,.s 20 0],[.f ⟨19,44,0,0,0,0,0,0,0⟩,.f ⟨19,44,1,0,1,0,0,0,0⟩]],[.f ⟨3,18,0,0,0,0,0,0,3⟩,.f ⟨3,18,1,0,1,0,0,0,3⟩]⟩,
⟨10,-3,7,34,[[.s 17 0,.s 17 0],[.f ⟨19,41,0,0,0,0,0,0,0⟩,.f ⟨19,41,1,0,1,0,0,0,0⟩],[.f ⟨3,19,0,0,0,0,0,0,0⟩,.f ⟨3,19,1,0,1,0,0,0,0⟩],[.f ⟨19,43,0,0,0,0,0,0,0⟩,.f ⟨19,43,1,0,1,0,0,0,0⟩],[.s 21 0,.s 21 0],[.f ⟨19,45,0,0,0,0,0,0,0⟩,.f ⟨19,45,1,0,1,0,0,0,0⟩]],[.s 17 4,.s 17 4]⟩,
⟨10,-3,8,36,[[.f ⟨3,18,0,0,0,0,0,0,0⟩,.f ⟨3,18,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.f ⟨3,20,0,0,0,0,0,0,0⟩,.f ⟨3,20,1,0,1,0,0,0,0⟩],[.f ⟨19,44,0,0,0,0,0,0,0⟩,.f ⟨19,44,1,0,1,0,0,0,0⟩],[.f ⟨3,22,0,0,0,0,0,0,0⟩,.f ⟨3,22,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0]],[.f ⟨3,20,0,0,0,0,0,0,3⟩,.f ⟨3,20,1,0,1,0,0,0,3⟩]⟩,
⟨10,-3,9,34,[[.f ⟨3,19,0,0,0,0,0,0,0⟩,.f ⟨3,19,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.f ⟨3,21,0,0,0,0,0,0,0⟩,.f ⟨3,21,1,0,1,0,0,0,0⟩],[.f ⟨19,45,0,0,0,0,0,0,0⟩,.f ⟨19,45,1,0,1,0,0,0,0⟩],[.f ⟨3,23,0,0,0,0,0,0,0⟩,.f ⟨3,23,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.f ⟨3,19,0,0,0,0,0,0,5⟩,.f ⟨3,19,1,0,1,0,0,0,5⟩]⟩,
⟨10,-3,10,36,[[.s 20 0,.s 20 0],[.f ⟨19,44,0,0,0,0,0,0,0⟩,.f ⟨19,44,1,0,1,0,0,0,0⟩],[.f ⟨3,22,0,0,0,0,0,0,0⟩,.f ⟨3,22,1,0,1,0,0,0,0⟩],[.f ⟨19,46,0,0,0,0,0,0,0⟩,.f ⟨19,46,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.f ⟨3,22,0,0,0,0,0,0,3⟩,.f ⟨3,22,1,0,1,0,0,0,3⟩]⟩,
⟨10,-3,11,35,[[.s 21 0,.s 21 0],[.f ⟨19,45,0,0,0,0,0,0,0⟩,.f ⟨19,45,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.f ⟨3,23,0,0,0,0,0,0,0⟩,.f ⟨3,23,1,0,1,0,0,0,0⟩],[.f ⟨19,47,0,0,0,0,0,0,0⟩,.f ⟨19,47,1,0,1,0,0,0,0⟩]],[.s 21 5,.s 21 5]⟩]⟩,
⟨1,3,0,0,0,[(2,6,3),(0,-3,1),(0,3,-3)],2,6,3,6,0,0,0,0,3,0,0,0,
[⟨5,-1,0,17,[[.f ⟨16,0,0,0,0,0,0,0,0⟩,.s 24 0],[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨14,87,0,0,0,0,0,0,0⟩,.f ⟨19,3,0,0,0,1,0,0,0⟩]],[.f ⟨16,0,0,0,0,0,0,0,1⟩,.s 24 1]⟩,
⟨5,-1,1,16,[[.s 0 0,.s 0 0],[.f ⟨16,1,0,0,0,0,0,0,0⟩,.s 25 0],[.s 13 0,.s 13 0],[.s 2 0,.s 2 0]],[.f ⟨16,1,0,0,0,0,0,0,2⟩,.s 25 2]⟩,
⟨5,-1,2,15,[[.s 1 0,.s 1 0],[.f ⟨16,2,0,0,0,0,0,0,0⟩,.s 26 0],[.s 14 0,.s 14 0],[.s 4 0,.s 4 0]],[.f ⟨16,2,0,0,0,0,0,0,2⟩,.s 26 2]⟩,
⟨5,-1,3,9,[[.f ⟨5,0,0,0,0,0,0,0,0⟩,.f ⟨5,0,1,0,1,0,0,0,0⟩],[.f ⟨16,3,0,0,0,0,0,0,0⟩,.s 27 0],[.s 15 0,.s 15 0],[.s 5 0,.s 5 0]],[.f ⟨5,0,0,0,0,0,0,0,3⟩,.f ⟨5,0,1,0,1,0,0,0,3⟩]⟩,
⟨5,-1,4,14,[[.s 2 0,.s 2 0],[.f ⟨16,4,0,0,0,0,0,0,0⟩,.s 28 0],[.s 16 0,.s 16 0],[.f ⟨16,6,0,0,0,0,0,0,0⟩,.s 30 0],[.s 6 0,.s 6 0]],[.f ⟨16,4,0,0,0,0,0,0,2⟩,.s 28 2]⟩,
⟨5,-1,5,10,[[.s 3 0,.s 3 0],[.f ⟨16,5,0,0,0,0,0,0,0⟩,.s 29 0],[.s 17 0,.s 17 0],[.f ⟨16,7,0,0,0,0,0,0,0⟩,.s 31 0],[.s 7 0,.s 7 0]],[.s 3 3,.s 3 3]⟩,
⟨5,-1,6,14,[[.s 4 0,.s 4 0],[.s 16 0,.s 16 0],[.f ⟨16,6,0,0,0,0,0,0,0⟩,.s 30 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 20 0,.s 20 0]],[.f ⟨16,6,0,0,0,0,0,0,3⟩,.s 30 3]⟩,
⟨5,-1,7,11,[[.s 5 0,.s 5 0],[.s 17 0,.s 17 0],[.f ⟨16,7,0,0,0,0,0,0,0⟩,.s 31 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.s 5 4,.s 5 4]⟩,
⟨5,-1,8,13,[[.f ⟨16,6,0,0,0,0,0,0,0⟩,.s 30 0],[.s 6 0,.s 6 0],[.f ⟨16,8,0,0,0,0,0,0,0⟩,.s 32 0],[.s 20 0,.s 20 0],[.f ⟨16,10,0,0,0,0,0,0,0⟩,.s 34 0],[.s 10 0,.s 10 0]],[.f ⟨16,8,0,0,0,0,0,0,3⟩,.s 32 3]⟩,
⟨5,-1,9,11,[[.f ⟨16,7,0,0,0,0,0,0,0⟩,.s 31 0],[.s 7 0,.s 7 0],[.f ⟨16,9,0,0,0,0,0,0,0⟩,.s 33 0],[.s 21 0,.s 21 0],[.f ⟨16,11,0,0,0,0,0,0,0⟩,.s 35 0],[.s 11 0,.s 11 0]],[.f ⟨16,7,0,0,0,0,0,0,5⟩,.s 31 5]⟩,
⟨5,-1,10,13,[[.s 8 0,.s 8 0],[.s 20 0,.s 20 0],[.f ⟨16,10,0,0,0,0,0,0,0⟩,.s 34 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0]],[.f ⟨16,10,0,0,0,0,0,0,3⟩,.s 34 3]⟩,
⟨5,-1,11,12,[[.s 9 0,.s 9 0],[.s 21 0,.s 21 0],[.s 10 0,.s 10 0],[.f ⟨16,11,0,0,0,0,0,0,0⟩,.s 35 0],[.s 23 0,.s 23 0]],[.s 9 5,.s 9 5]⟩,
⟨6,-1,0,18,[[.s 0 0,.s 0 0],[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.f ⟨3,3,0,0,0,0,0,0,0⟩,.f ⟨19,15,0,0,0,1,0,0,0⟩]],[.s 0 1,.s 0 1]⟩,
⟨6,-1,1,17,[[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.s 25 0,.s 25 0],[.s 14 0,.s 14 0]],[.s 1 2,.s 1 2]⟩,
⟨6,-1,2,16,[[.s 13 0,.s 13 0],[.s 2 0,.s 2 0],[.s 26 0,.s 26 0],[.s 16 0,.s 16 0]],[.s 2 2,.s 2 2]⟩,
⟨6,-1,3,10,[[.f ⟨5,12,0,0,0,0,0,0,0⟩,.f ⟨5,12,1,0,1,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 27 0,.s 27 0],[.s 17 0,.s 17 0]],[.f ⟨5,12,0,0,0,0,0,0,3⟩,.f ⟨5,12,1,0,1,0,0,0,3⟩]⟩,
⟨6,-1,4,15,[[.s 14 0,.s 14 0],[.s 4 0,.s 4 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 18 0,.s 18 0]],[.s 4 2,.s 4 2]⟩,
⟨6,-1,5,11,[[.s 15 0,.s 15 0],[.s 5 0,.s 5 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 19 0,.s 19 0]],[.s 15 3,.s 15 3]⟩,
⟨6,-1,6,15,[[.s 16 0,.s 16 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.s 32 0,.s 32 0]],[.s 6 3,.s 6 3]⟩,
⟨6,-1,7,12,[[.s 17 0,.s 17 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.s 33 0,.s 33 0]],[.s 17 4,.s 17 4]⟩,
⟨6,-1,8,14,[[.s 6 0,.s 6 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 22 0,.s 22 0]],[.s 8 3,.s 8 3]⟩,
⟨6,-1,9,12,[[.s 7 0,.s 7 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 33 0,.s 33 0],[.s 11 0,.s 11 0],[.s 23 0,.s 23 0]],[.s 7 5,.s 7 5]⟩,
⟨6,-1,10,14,[[.s 20 0,.s 20 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0]],[.s 10 3,.s 10 3]⟩,
⟨6,-1,11,13,[[.s 21 0,.s 21 0],[.s 33 0,.s 33 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0],[.s 35 0,.s 35 0]],[.s 21 5,.s 21 5]⟩,
⟨7,-1,0,19,[[.s 12 0,.s 12 0],[.s 0 0,.s 0 0],[.s 25 0,.s 25 0],[.f ⟨17,3,0,0,0,0,0,0,0⟩,.f ⟨19,27,0,0,0,1,0,0,0⟩]],[.s 12 1,.s 12 1]⟩,
⟨7,-1,1,18,[[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.s 1 0,.s 1 0],[.s 26 0,.s 26 0]],[.s 13 2,.s 13 2]⟩,
⟨7,-1,2,17,[[.s 25 0,.s 25 0],[.s 14 0,.s 14 0],[.s 2 0,.s 2 0],[.s 28 0,.s 28 0]],[.s 14 2,.s 14 2]⟩,
⟨7,-1,3,11,[[.f ⟨5,24,0,0,0,0,0,0,0⟩,.f ⟨5,24,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 3 0,.s 3 0],[.s 29 0,.s 29 0]],[.f ⟨5,24,0,0,0,0,0,0,3⟩,.f ⟨5,24,1,0,1,0,0,0,3⟩]⟩,
⟨7,-1,4,16,[[.s 26 0,.s 26 0],[.s 16 0,.s 16 0],[.s 4 0,.s 4 0],[.s 18 0,.s 18 0],[.s 30 0,.s 30 0]],[.s 16 2,.s 16 2]⟩,
⟨7,-1,5,12,[[.s 27 0,.s 27 0],[.s 17 0,.s 17 0],[.s 5 0,.s 5 0],[.s 19 0,.s 19 0],[.s 31 0,.s 31 0]],[.s 27 3,.s 27 3]⟩,
⟨7,-1,6,16,[[.s 28 0,.s 28 0],[.s 4 0,.s 4 0],[.s 18 0,.s 18 0],[.s 6 0,.s 6 0],[.s 32 0,.s 32 0],[.s 8 0,.s 8 0]],[.s 18 3,.s 18 3]⟩,
⟨7,-1,7,13,[[.s 29 0,.s 29 0],[.s 5 0,.s 5 0],[.s 19 0,.s 19 0],[.s 7 0,.s 7 0],[.s 33 0,.s 33 0],[.s 9 0,.s 9 0]],[.s 29 4,.s 29 4]⟩,
⟨7,-1,8,15,[[.s 18 0,.s 18 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.s 8 0,.s 8 0],[.s 22 0,.s 22 0],[.s 34 0,.s 34 0]],[.s 20 3,.s 20 3]⟩,
⟨7,-1,9,13,[[.s 19 0,.s 19 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.s 9 0,.s 9 0],[.s 23 0,.s 23 0],[.s 35 0,.s 35 0]],[.s 19 5,.s 19 5]⟩,
⟨7,-1,10,15,[[.s 32 0,.s 32 0],[.s 8 0,.s 8 0],[.s 22 0,.s 22 0],[.s 10 0,.s 10 0],[.s 35 0,.s 35 0]],[.s 22 3,.s 22 3]⟩,
⟨7,-1,11,14,[[.s 33 0,.s 33 0],[.s 9 0,.s 9 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0],[.s 11 0,.s 11 0]],[.s 33 5,.s 33 5]⟩]⟩,
⟨2,6,-2,3,0,[(0,-3,4),(2,6,3)],0,-3,4,6,2,6,3,6,24,3,1,8,
[⟨8,-2,0,29,[[.f ⟨17,0,0,0,0,0,0,0,0⟩,.f ⟨17,0,1,0,1,0,0,0,0⟩,.s 24 0,.s 24 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨14,39,0,0,1,0,0,0,0⟩,.f ⟨14,39,1,0,2,0,0,0,0⟩,.s 39 0,.s 39 0]],[.f ⟨17,0,0,0,0,0,0,0,1⟩,.f ⟨17,0,1,0,1,0,0,0,1⟩,.s 24 1,.s 24 1]⟩,
⟨8,-2,1,28,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨17,1,0,0,0,0,0,0,0⟩,.f ⟨17,1,1,0,1,0,0,0,0⟩,.s 25 0,.s 25 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.f ⟨17,1,0,0,0,0,0,0,2⟩,.f ⟨17,1,1,0,1,0,0,0,2⟩,.s 25 2,.s 25 2]⟩,
⟨8,-2,2,27,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨17,2,0,0,0,0,0,0,0⟩,.f ⟨17,2,1,0,1,0,0,0,0⟩,.s 26 0,.s 26 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.f ⟨17,2,0,0,0,0,0,0,2⟩,.f ⟨17,2,1,0,1,0,0,0,2⟩,.s 26 2,.s 26 2]⟩,
⟨8,-2,3,21,[[.f ⟨18,0,0,0,1,0,0,0,0⟩,.s 36 0,.f ⟨18,0,0,1,2,0,0,0,0⟩,.s 36 0],[.f ⟨17,3,0,0,0,0,0,0,0⟩,.f ⟨17,3,1,0,1,0,0,0,0⟩,.s 27 0,.s 27 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.f ⟨18,0,0,0,1,0,0,0,3⟩,.s 36 3,.f ⟨18,0,0,1,2,0,0,0,3⟩,.s 36 3]⟩,
⟨8,-2,4,26,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.f ⟨17,4,0,0,0,0,0,0,0⟩,.f ⟨17,4,1,0,1,0,0,0,0⟩,.s 28 0,.s 28 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨17,6,0,0,0,0,0,0,0⟩,.f ⟨17,6,1,0,1,0,0,0,0⟩,.s 30 0,.s 30 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.f ⟨17,4,0,0,0,0,0,0,2⟩,.f ⟨17,4,1,0,1,0,0,0,2⟩,.s 28 2,.s 28 2]⟩,
⟨8,-2,5,22,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.f ⟨17,5,0,0,0,0,0,0,0⟩,.f ⟨17,5,1,0,1,0,0,0,0⟩,.s 29 0,.s 29 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨17,7,0,0,0,0,0,0,0⟩,.f ⟨17,7,1,0,1,0,0,0,0⟩,.s 31 0,.s 31 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.s 3 3,.s 3 3,.s 3 3,.s 3 3]⟩,
⟨8,-2,6,26,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨17,6,0,0,0,0,0,0,0⟩,.f ⟨17,6,1,0,1,0,0,0,0⟩,.s 30 0,.s 30 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.f ⟨17,6,0,0,0,0,0,0,3⟩,.f ⟨17,6,1,0,1,0,0,0,3⟩,.s 30 3,.s 30 3]⟩,
⟨8,-2,7,23,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨17,7,0,0,0,0,0,0,0⟩,.f ⟨17,7,1,0,1,0,0,0,0⟩,.s 31 0,.s 31 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 5 4,.s 5 4,.s 5 4,.s 5 4]⟩,
⟨8,-2,8,25,[[.f ⟨17,6,0,0,0,0,0,0,0⟩,.f ⟨17,6,1,0,1,0,0,0,0⟩,.s 30 0,.s 30 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨17,8,0,0,0,0,0,0,0⟩,.f ⟨17,8,1,0,1,0,0,0,0⟩,.s 32 0,.s 32 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨17,10,0,0,0,0,0,0,0⟩,.f ⟨17,10,1,0,1,0,0,0,0⟩,.s 34 0,.s 34 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.f ⟨17,8,0,0,0,0,0,0,3⟩,.f ⟨17,8,1,0,1,0,0,0,3⟩,.s 32 3,.s 32 3]⟩,
⟨8,-2,9,23,[[.f ⟨17,7,0,0,0,0,0,0,0⟩,.f ⟨17,7,1,0,1,0,0,0,0⟩,.s 31 0,.s 31 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.f ⟨17,9,0,0,0,0,0,0,0⟩,.f ⟨17,9,1,0,1,0,0,0,0⟩,.s 33 0,.s 33 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.f ⟨17,11,0,0,0,0,0,0,0⟩,.f ⟨17,11,1,0,1,0,0,0,0⟩,.s 35 0,.s 35 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.f ⟨17,7,0,0,0,0,0,0,5⟩,.f ⟨17,7,1,0,1,0,0,0,5⟩,.s 31 5,.s 31 5]⟩,
⟨8,-2,10,25,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨17,10,0,0,0,0,0,0,0⟩,.f ⟨17,10,1,0,1,0,0,0,0⟩,.s 34 0,.s 34 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.f ⟨17,10,0,0,0,0,0,0,3⟩,.f ⟨17,10,1,0,1,0,0,0,3⟩,.s 34 3,.s 34 3]⟩,
⟨8,-2,11,24,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.f ⟨17,11,0,0,0,0,0,0,0⟩,.f ⟨17,11,1,0,1,0,0,0,0⟩,.s 35 0,.s 35 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 9 5,.s 9 5,.s 9 5,.s 9 5]⟩,
⟨9,-2,0,30,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.f ⟨3,15,0,0,0,0,0,0,0⟩,.f ⟨3,15,1,0,1,0,0,0,0⟩,.s 51 0,.s 51 0]],[.s 0 1,.s 0 1,.s 0 1,.s 0 1]⟩,
⟨9,-2,1,29,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 1 2,.s 1 2,.s 1 2,.s 1 2]⟩,
⟨9,-2,2,28,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 2 2,.s 2 2,.s 2 2,.s 2 2]⟩,
⟨9,-2,3,22,[[.f ⟨18,12,0,0,1,0,0,0,0⟩,.s 48 0,.f ⟨18,12,0,1,2,0,0,0,0⟩,.s 48 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.f ⟨18,12,0,0,1,0,0,0,3⟩,.s 48 3,.f ⟨18,12,0,1,2,0,0,0,3⟩,.s 48 3]⟩,
⟨9,-2,4,27,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0]],[.s 4 2,.s 4 2,.s 4 2,.s 4 2]⟩,
⟨9,-2,5,23,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0]],[.s 15 3,.s 15 3,.s 15 3,.s 15 3]⟩,
⟨9,-2,6,27,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 6 3,.s 6 3,.s 6 3,.s 6 3]⟩,
⟨9,-2,7,24,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.s 17 4,.s 17 4,.s 17 4,.s 17 4]⟩,
⟨9,-2,8,26,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.s 8 3,.s 8 3,.s 8 3,.s 8 3]⟩,
⟨9,-2,9,24,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 7 5,.s 7 5,.s 7 5,.s 7 5]⟩,
⟨9,-2,10,26,[[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 10 3,.s 10 3,.s 10 3,.s 10 3]⟩,
⟨9,-2,11,25,[[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 21 5,.s 21 5,.s 21 5,.s 21 5]⟩,
⟨10,-2,0,31,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.f ⟨17,15,0,0,0,0,0,0,0⟩,.f ⟨17,15,1,0,1,0,0,0,0⟩,.s 63 0,.s 63 0]],[.s 12 1,.s 12 1,.s 12 1,.s 12 1]⟩,
⟨10,-2,1,30,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.s 13 2,.s 13 2,.s 13 2,.s 13 2]⟩,
⟨10,-2,2,29,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.s 14 2,.s 14 2,.s 14 2,.s 14 2]⟩,
⟨10,-2,3,23,[[.f ⟨18,24,0,0,1,0,0,0,0⟩,.s 60 0,.f ⟨18,24,0,1,2,0,0,0,0⟩,.s 60 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0]],[.f ⟨18,24,0,0,1,0,0,0,3⟩,.s 60 3,.f ⟨18,24,0,1,2,0,0,0,3⟩,.s 60 3]⟩,
⟨10,-2,4,28,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0]],[.s 16 2,.s 16 2,.s 16 2,.s 16 2]⟩,
⟨10,-2,5,24,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 27 3,.s 27 3,.s 27 3,.s 27 3]⟩,
⟨10,-2,6,28,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 18 3,.s 18 3,.s 18 3,.s 18 3]⟩,
⟨10,-2,7,25,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 29 4,.s 29 4,.s 29 4,.s 29 4]⟩,
⟨10,-2,8,27,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.s 20 3,.s 20 3,.s 20 3,.s 20 3]⟩,
⟨10,-2,9,25,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 19 5,.s 19 5,.s 19 5,.s 19 5]⟩,
⟨10,-2,10,27,[[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 22 3,.s 22 3,.s 22 3,.s 22 3]⟩,
⟨10,-2,11,26,[[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 33 5,.s 33 5,.s 33 5,.s 33 5]⟩,
⟨11,-3,0,41,[[.f ⟨17,12,0,0,0,0,0,0,0⟩,.f ⟨17,12,1,0,1,0,0,0,0⟩,.s 60 0,.s 60 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.f ⟨14,87,0,0,1,0,0,0,0⟩,.f ⟨14,87,1,0,2,0,0,0,0⟩,.s 3 0,.s 3 0]],[.f ⟨17,12,0,0,0,0,0,0,1⟩,.f ⟨17,12,1,0,1,0,0,0,1⟩,.s 60 1,.s 60 1]⟩,
⟨11,-3,1,40,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.f ⟨17,13,0,0,0,0,0,0,0⟩,.f ⟨17,13,1,0,1,0,0,0,0⟩,.s 61 0,.s 61 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.f ⟨17,13,0,0,0,0,0,0,2⟩,.f ⟨17,13,1,0,1,0,0,0,2⟩,.s 61 2,.s 61 2]⟩,
⟨11,-3,2,39,[[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.f ⟨17,14,0,0,0,0,0,0,0⟩,.f ⟨17,14,1,0,1,0,0,0,0⟩,.s 62 0,.s 62 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0]],[.f ⟨17,14,0,0,0,0,0,0,2⟩,.f ⟨17,14,1,0,1,0,0,0,2⟩,.s 62 2,.s 62 2]⟩,
⟨11,-3,3,33,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨17,15,0,0,0,0,0,0,0⟩,.f ⟨17,15,1,0,1,0,0,0,0⟩,.s 63 0,.s 63 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0]],[.s 0 3,.s 0 3,.s 0 3,.s 0 3]⟩,
⟨11,-3,4,38,[[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.f ⟨17,16,0,0,0,0,0,0,0⟩,.f ⟨17,16,1,0,1,0,0,0,0⟩,.s 64 0,.s 64 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.f ⟨17,18,0,0,0,0,0,0,0⟩,.f ⟨17,18,1,0,1,0,0,0,0⟩,.s 66 0,.s 66 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.f ⟨17,16,0,0,0,0,0,0,2⟩,.f ⟨17,16,1,0,1,0,0,0,2⟩,.s 64 2,.s 64 2]⟩,
⟨11,-3,5,34,[[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.f ⟨17,17,0,0,0,0,0,0,0⟩,.f ⟨17,17,1,0,1,0,0,0,0⟩,.s 65 0,.s 65 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.f ⟨17,19,0,0,0,0,0,0,0⟩,.f ⟨17,19,1,0,1,0,0,0,0⟩,.s 67 0,.s 67 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 39 3,.s 39 3,.s 39 3,.s 39 3]⟩,
⟨11,-3,6,38,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.f ⟨17,18,0,0,0,0,0,0,0⟩,.f ⟨17,18,1,0,1,0,0,0,0⟩,.s 66 0,.s 66 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0]],[.f ⟨17,18,0,0,0,0,0,0,3⟩,.f ⟨17,18,1,0,1,0,0,0,3⟩,.s 66 3,.s 66 3]⟩,
⟨11,-3,7,35,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.f ⟨17,19,0,0,0,0,0,0,0⟩,.f ⟨17,19,1,0,1,0,0,0,0⟩,.s 67 0,.s 67 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0]],[.s 41 4,.s 41 4,.s 41 4,.s 41 4]⟩,
⟨11,-3,8,37,[[.f ⟨17,18,0,0,0,0,0,0,0⟩,.f ⟨17,18,1,0,1,0,0,0,0⟩,.s 66 0,.s 66 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.f ⟨17,20,0,0,0,0,0,0,0⟩,.f ⟨17,20,1,0,1,0,0,0,0⟩,.s 68 0,.s 68 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.f ⟨17,22,0,0,0,0,0,0,0⟩,.f ⟨17,22,1,0,1,0,0,0,0⟩,.s 70 0,.s 70 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0]],[.f ⟨17,20,0,0,0,0,0,0,3⟩,.f ⟨17,20,1,0,1,0,0,0,3⟩,.s 68 3,.s 68 3]⟩,
⟨11,-3,9,35,[[.f ⟨17,19,0,0,0,0,0,0,0⟩,.f ⟨17,19,1,0,1,0,0,0,0⟩,.s 67 0,.s 67 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.f ⟨17,21,0,0,0,0,0,0,0⟩,.f ⟨17,21,1,0,1,0,0,0,0⟩,.s 69 0,.s 69 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.f ⟨17,23,0,0,0,0,0,0,0⟩,.f ⟨17,23,1,0,1,0,0,0,0⟩,.s 71 0,.s 71 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.f ⟨17,19,0,0,0,0,0,0,5⟩,.f ⟨17,19,1,0,1,0,0,0,5⟩,.s 67 5,.s 67 5]⟩,
⟨11,-3,10,37,[[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.f ⟨17,22,0,0,0,0,0,0,0⟩,.f ⟨17,22,1,0,1,0,0,0,0⟩,.s 70 0,.s 70 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.f ⟨17,22,0,0,0,0,0,0,3⟩,.f ⟨17,22,1,0,1,0,0,0,3⟩,.s 70 3,.s 70 3]⟩,
⟨11,-3,11,36,[[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.f ⟨17,23,0,0,0,0,0,0,0⟩,.f ⟨17,23,1,0,1,0,0,0,0⟩,.s 71 0,.s 71 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 45 5,.s 45 5,.s 45 5,.s 45 5]⟩,
⟨12,-3,0,42,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.f ⟨3,3,0,0,1,0,0,0,0⟩,.f ⟨3,3,1,0,2,0,0,0,0⟩,.s 15 0,.s 15 0]],[.s 36 1,.s 36 1,.s 36 1,.s 36 1]⟩,
⟨12,-3,1,41,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0]],[.s 37 2,.s 37 2,.s 37 2,.s 37 2]⟩,
⟨12,-3,2,40,[[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0]],[.s 38 2,.s 38 2,.s 38 2,.s 38 2]⟩,
⟨12,-3,3,34,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]],[.s 12 3,.s 12 3,.s 12 3,.s 12 3]⟩,
⟨12,-3,4,39,[[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0]],[.s 40 2,.s 40 2,.s 40 2,.s 40 2]⟩,
⟨12,-3,5,35,[[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0]],[.s 51 3,.s 51 3,.s 51 3,.s 51 3]⟩,
⟨12,-3,6,39,[[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0]],[.s 42 3,.s 42 3,.s 42 3,.s 42 3]⟩,
⟨12,-3,7,36,[[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0]],[.s 53 4,.s 53 4,.s 53 4,.s 53 4]⟩,
⟨12,-3,8,38,[[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0]],[.s 44 3,.s 44 3,.s 44 3,.s 44 3]⟩,
⟨12,-3,9,36,[[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 43 5,.s 43 5,.s 43 5,.s 43 5]⟩,
⟨12,-3,10,38,[[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 46 3,.s 46 3,.s 46 3,.s 46 3]⟩,
⟨12,-3,11,37,[[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 57 5,.s 57 5,.s 57 5,.s 57 5]⟩,
⟨13,-3,0,43,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.f ⟨17,3,0,0,1,0,0,0,0⟩,.f ⟨17,3,1,0,2,0,0,0,0⟩,.s 27 0,.s 27 0]],[.s 48 1,.s 48 1,.s 48 1,.s 48 1]⟩,
⟨13,-3,1,42,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0]],[.s 49 2,.s 49 2,.s 49 2,.s 49 2]⟩,
⟨13,-3,2,41,[[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0]],[.s 50 2,.s 50 2,.s 50 2,.s 50 2]⟩,
⟨13,-3,3,35,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0]],[.s 24 3,.s 24 3,.s 24 3,.s 24 3]⟩,
⟨13,-3,4,40,[[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0]],[.s 52 2,.s 52 2,.s 52 2,.s 52 2]⟩,
⟨13,-3,5,36,[[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0]],[.s 63 3,.s 63 3,.s 63 3,.s 63 3]⟩,
⟨13,-3,6,40,[[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0]],[.s 54 3,.s 54 3,.s 54 3,.s 54 3]⟩,
⟨13,-3,7,37,[[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0]],[.s 65 4,.s 65 4,.s 65 4,.s 65 4]⟩,
⟨13,-3,8,39,[[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0]],[.s 56 3,.s 56 3,.s 56 3,.s 56 3]⟩,
⟨13,-3,9,37,[[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 55 5,.s 55 5,.s 55 5,.s 55 5]⟩,
⟨13,-3,10,39,[[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 58 3,.s 58 3,.s 58 3,.s 58 3]⟩,
⟨13,-3,11,38,[[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 69 5,.s 69 5,.s 69 5,.s 69 5]⟩]⟩,
⟨0,0,0,0,0,[(2,-6,1),(0,3,1),(-2,6,-4),(0,-3,-3)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨4,1,0,10,[[.f ⟨6,0,0,0,0,0,0,0,0⟩],[.s 12 0],[.s 1 0],[.f ⟨4,39,0,0,0,0,0,0,0⟩]],[.f ⟨6,0,0,0,0,0,0,0,1⟩]⟩,
⟨4,1,1,11,[[.s 0 0],[.f ⟨6,1,0,0,0,0,0,0,0⟩],[.s 13 0],[.s 2 0]],[.s 0 2]⟩,
⟨4,1,2,12,[[.s 1 0],[.f ⟨6,2,0,0,0,0,0,0,0⟩],[.s 14 0],[.s 4 0]],[.s 1 3]⟩,
⟨4,1,3,20,[[.f ⟨26,264,0,0,0,0,0,0,0⟩],[.f ⟨6,3,0,0,0,0,0,0,0⟩],[.s 15 0],[.s 5 0]],[.s 5 0]⟩,
⟨4,1,4,13,[[.s 2 0],[.f ⟨6,4,0,0,0,0,0,0,0⟩],[.s 16 0],[.f ⟨6,6,0,0,0,0,0,0,0⟩],[.s 6 0]],[.s 2 3]⟩,
⟨4,1,5,19,[[.s 3 0],[.f ⟨6,5,0,0,0,0,0,0,0⟩],[.s 17 0],[.f ⟨6,7,0,0,0,0,0,0,0⟩],[.s 7 0]],[.f ⟨6,7,0,0,0,0,0,0,1⟩]⟩,
⟨4,1,6,14,[[.s 4 0],[.s 16 0],[.f ⟨6,6,0,0,0,0,0,0,0⟩],[.s 18 0],[.s 8 0],[.s 20 0]],[.s 4 4]⟩,
⟨4,1,7,18,[[.s 5 0],[.s 17 0],[.f ⟨6,7,0,0,0,0,0,0,0⟩],[.s 19 0],[.s 9 0],[.s 21 0]],[.s 9 1]⟩,
⟨4,1,8,14,[[.f ⟨6,6,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨6,8,0,0,0,0,0,0,0⟩],[.s 20 0],[.f ⟨6,10,0,0,0,0,0,0,0⟩],[.s 10 0]],[.f ⟨6,6,0,0,0,0,0,0,5⟩]⟩,
⟨4,1,9,17,[[.f ⟨6,7,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨6,9,0,0,0,0,0,0,0⟩],[.s 21 0],[.f ⟨6,11,0,0,0,0,0,0,0⟩],[.s 11 0]],[.f ⟨6,11,0,0,0,0,0,0,1⟩]⟩,
⟨4,1,10,15,[[.s 8 0],[.s 20 0],[.f ⟨6,10,0,0,0,0,0,0,0⟩],[.s 22 0],[.s 11 0]],[.s 8 5]⟩,
⟨4,1,11,16,[[.s 9 0],[.s 21 0],[.s 10 0],[.f ⟨6,11,0,0,0,0,0,0,0⟩],[.s 23 0]],[.s 10 4]⟩,
⟨5,1,0,11,[[.s 0 0],[.f ⟨21,0,0,0,0,0,0,0,0⟩],[.s 13 0],[.f ⟨5,3,0,0,0,0,0,0,0⟩]],[.s 0 1]⟩,
⟨5,1,1,12,[[.s 12 0],[.s 1 0],[.f ⟨21,1,0,0,0,0,0,0,0⟩],[.s 14 0]],[.s 12 2]⟩,
⟨5,1,2,13,[[.s 13 0],[.s 2 0],[.f ⟨21,2,0,0,0,0,0,0,0⟩],[.s 16 0]],[.s 13 3]⟩,
⟨5,1,3,20,[[.f ⟨24,12,0,0,0,0,0,0,0⟩],[.s 3 0],[.f ⟨21,3,0,0,0,0,0,0,0⟩],[.s 17 0]],[.s 17 0]⟩,
⟨5,1,4,14,[[.s 14 0],[.s 4 0],[.f ⟨21,4,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 18 0]],[.s 14 3]⟩,
⟨5,1,5,19,[[.s 15 0],[.s 5 0],[.f ⟨21,5,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 19 0]],[.s 7 1]⟩,
⟨5,1,6,15,[[.s 16 0],[.f ⟨21,4,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨21,6,0,0,0,0,0,0,0⟩],[.s 20 0],[.f ⟨21,8,0,0,0,0,0,0,0⟩]],[.s 16 4]⟩,
⟨5,1,7,18,[[.s 17 0],[.f ⟨21,5,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨21,7,0,0,0,0,0,0,0⟩],[.s 21 0],[.f ⟨21,9,0,0,0,0,0,0,0⟩]],[.s 21 1]⟩,
⟨5,1,8,15,[[.s 6 0],[.s 18 0],[.s 8 0],[.f ⟨21,8,0,0,0,0,0,0,0⟩],[.s 10 0],[.s 22 0]],[.s 6 5]⟩,
⟨5,1,9,17,[[.s 7 0],[.s 19 0],[.s 9 0],[.f ⟨21,9,0,0,0,0,0,0,0⟩],[.s 11 0],[.s 23 0]],[.s 11 1]⟩,
⟨5,1,10,16,[[.s 20 0],[.f ⟨21,8,0,0,0,0,0,0,0⟩],[.s 10 0],[.f ⟨21,10,0,0,0,0,0,0,0⟩],[.s 23 0]],[.s 20 5]⟩,
⟨5,1,11,17,[[.s 21 0],[.f ⟨21,9,0,0,0,0,0,0,0⟩],[.s 22 0],[.s 11 0],[.f ⟨21,11,0,0,0,0,0,0,0⟩]],[.s 22 4]⟩]⟩,
⟨1,3,0,0,0,[(2,-6,5),(0,3,1),(0,-3,-3)],2,-6,5,6,0,0,0,0,3,0,0,0,
[⟨6,1,0,12,[[.f ⟨20,12,0,0,0,0,0,0,0⟩,.s 24 0],[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨5,15,0,0,0,0,0,0,0⟩,.f ⟨5,15,1,0,1,0,0,0,0⟩]],[.f ⟨20,12,0,0,0,0,0,0,1⟩,.s 24 1]⟩,
⟨6,1,1,13,[[.s 0 0,.s 0 0],[.f ⟨20,13,0,0,0,0,0,0,0⟩,.s 25 0],[.s 13 0,.s 13 0],[.s 2 0,.s 2 0]],[.s 0 2,.s 0 2]⟩,
⟨6,1,2,14,[[.s 1 0,.s 1 0],[.f ⟨20,14,0,0,0,0,0,0,0⟩,.s 26 0],[.s 14 0,.s 14 0],[.s 4 0,.s 4 0]],[.s 1 3,.s 1 3]⟩,
⟨6,1,3,20,[[.f ⟨7,0,0,0,0,0,0,0,0⟩,.f ⟨23,0,1,0,0,0,0,0,0⟩],[.f ⟨20,15,0,0,0,0,0,0,0⟩,.s 27 0],[.s 15 0,.s 15 0],[.s 5 0,.s 5 0]],[.s 5 0,.s 27 2]⟩,
⟨6,1,4,15,[[.s 2 0,.s 2 0],[.f ⟨20,16,0,0,0,0,0,0,0⟩,.s 28 0],[.s 16 0,.s 16 0],[.f ⟨20,18,0,0,0,0,0,0,0⟩,.s 30 0],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨6,1,5,19,[[.s 3 0,.s 3 0],[.f ⟨20,17,0,0,0,0,0,0,0⟩,.s 29 0],[.s 17 0,.s 17 0],[.f ⟨20,19,0,0,0,0,0,0,0⟩,.s 31 0],[.s 7 0,.s 7 0]],[.f ⟨20,19,0,0,0,0,0,0,1⟩,.s 29 2]⟩,
⟨6,1,6,16,[[.s 4 0,.s 4 0],[.s 16 0,.s 16 0],[.f ⟨20,18,0,0,0,0,0,0,0⟩,.s 30 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 20 0,.s 20 0]],[.s 4 4,.s 4 4]⟩,
⟨6,1,7,19,[[.s 5 0,.s 5 0],[.s 17 0,.s 17 0],[.f ⟨20,19,0,0,0,0,0,0,0⟩,.s 31 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.f ⟨20,19,0,0,0,0,0,0,3⟩,.s 31 3]⟩,
⟨6,1,8,16,[[.f ⟨20,18,0,0,0,0,0,0,0⟩,.s 30 0],[.s 6 0,.s 6 0],[.f ⟨20,20,0,0,0,0,0,0,0⟩,.s 32 0],[.s 20 0,.s 20 0],[.f ⟨20,22,0,0,0,0,0,0,0⟩,.s 34 0],[.s 10 0,.s 10 0]],[.f ⟨20,18,0,0,0,0,0,0,5⟩,.s 30 5]⟩,
⟨6,1,9,18,[[.f ⟨20,19,0,0,0,0,0,0,0⟩,.s 31 0],[.s 7 0,.s 7 0],[.f ⟨20,21,0,0,0,0,0,0,0⟩,.s 33 0],[.s 21 0,.s 21 0],[.f ⟨20,23,0,0,0,0,0,0,0⟩,.s 35 0],[.s 11 0,.s 11 0]],[.f ⟨20,21,0,0,0,0,0,0,3⟩,.s 33 3]⟩,
⟨6,1,10,17,[[.s 8 0,.s 8 0],[.s 20 0,.s 20 0],[.f ⟨20,22,0,0,0,0,0,0,0⟩,.s 34 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0]],[.s 8 5,.s 8 5]⟩,
⟨6,1,11,18,[[.s 9 0,.s 9 0],[.s 21 0,.s 21 0],[.s 10 0,.s 10 0],[.f ⟨20,23,0,0,0,0,0,0,0⟩,.s 35 0],[.s 23 0,.s 23 0]],[.s 10 4,.s 10 4]⟩,
⟨7,1,0,13,[[.s 0 0,.s 0 0],[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.f ⟨5,27,0,0,0,0,0,0,0⟩,.f ⟨5,27,1,0,1,0,0,0,0⟩]],[.s 0 1,.s 0 1]⟩,
⟨7,1,1,14,[[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.s 25 0,.s 25 0],[.s 14 0,.s 14 0]],[.s 12 2,.s 12 2]⟩,
⟨7,1,2,15,[[.s 13 0,.s 13 0],[.s 2 0,.s 2 0],[.s 26 0,.s 26 0],[.s 16 0,.s 16 0]],[.s 13 3,.s 13 3]⟩,
⟨7,1,3,21,[[.f ⟨22,0,0,0,0,0,0,0,0⟩,.f ⟨23,12,1,0,0,0,0,0,0⟩],[.s 3 0,.s 3 0],[.s 27 0,.s 27 0],[.s 17 0,.s 17 0]],[.s 3 2,.s 3 2]⟩,
⟨7,1,4,16,[[.s 14 0,.s 14 0],[.s 4 0,.s 4 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 18 0,.s 18 0]],[.s 14 3,.s 14 3]⟩,
⟨7,1,5,20,[[.s 15 0,.s 15 0],[.s 5 0,.s 5 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 19 0,.s 19 0]],[.s 5 2,.s 5 2]⟩,
⟨7,1,6,17,[[.s 16 0,.s 16 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.s 32 0,.s 32 0]],[.s 16 4,.s 16 4]⟩,
⟨7,1,7,20,[[.s 17 0,.s 17 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.s 33 0,.s 33 0]],[.s 7 3,.s 7 3]⟩,
⟨7,1,8,17,[[.s 6 0,.s 6 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 22 0,.s 22 0]],[.s 6 5,.s 6 5]⟩,
⟨7,1,9,19,[[.s 7 0,.s 7 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 33 0,.s 33 0],[.s 11 0,.s 11 0],[.s 23 0,.s 23 0]],[.s 9 3,.s 9 3]⟩,
⟨7,1,10,18,[[.s 20 0,.s 20 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0]],[.s 20 5,.s 20 5]⟩,
⟨7,1,11,19,[[.s 21 0,.s 21 0],[.s 33 0,.s 33 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0],[.s 35 0,.s 35 0]],[.s 22 4,.s 22 4]⟩,
⟨8,1,0,14,[[.s 12 0,.s 12 0],[.s 0 0,.s 0 0],[.s 25 0,.s 25 0],[.f ⟨5,3,0,0,1,0,0,0,0⟩,.f ⟨5,3,1,0,2,0,0,0,0⟩]],[.s 12 1,.s 12 1]⟩,
⟨8,1,1,15,[[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.s 1 0,.s 1 0],[.s 26 0,.s 26 0]],[.s 24 2,.s 24 2]⟩,
⟨8,1,2,16,[[.s 25 0,.s 25 0],[.s 14 0,.s 14 0],[.s 2 0,.s 2 0],[.s 28 0,.s 28 0]],[.s 25 3,.s 25 3]⟩,
⟨8,1,3,22,[[.f ⟨22,12,0,0,0,0,0,0,0⟩,.f ⟨23,24,1,0,0,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 3 0,.s 3 0],[.s 29 0,.s 29 0]],[.s 15 2,.s 15 2]⟩,
⟨8,1,4,17,[[.s 26 0,.s 26 0],[.s 16 0,.s 16 0],[.s 4 0,.s 4 0],[.s 18 0,.s 18 0],[.s 30 0,.s 30 0]],[.s 26 3,.s 26 3]⟩,
⟨8,1,5,21,[[.s 27 0,.s 27 0],[.s 17 0,.s 17 0],[.s 5 0,.s 5 0],[.s 19 0,.s 19 0],[.s 31 0,.s 31 0]],[.s 17 2,.s 17 2]⟩,
⟨8,1,6,18,[[.s 28 0,.s 28 0],[.s 4 0,.s 4 0],[.s 18 0,.s 18 0],[.s 6 0,.s 6 0],[.s 32 0,.s 32 0],[.s 8 0,.s 8 0]],[.s 28 4,.s 28 4]⟩,
⟨8,1,7,21,[[.s 29 0,.s 29 0],[.s 5 0,.s 5 0],[.s 19 0,.s 19 0],[.s 7 0,.s 7 0],[.s 33 0,.s 33 0],[.s 9 0,.s 9 0]],[.s 19 3,.s 19 3]⟩,
⟨8,1,8,18,[[.s 18 0,.s 18 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.s 8 0,.s 8 0],[.s 22 0,.s 22 0],[.s 34 0,.s 34 0]],[.s 18 5,.s 18 5]⟩,
⟨8,1,9,20,[[.s 19 0,.s 19 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.s 9 0,.s 9 0],[.s 23 0,.s 23 0],[.s 35 0,.s 35 0]],[.s 21 3,.s 21 3]⟩,
⟨8,1,10,19,[[.s 32 0,.s 32 0],[.s 8 0,.s 8 0],[.s 22 0,.s 22 0],[.s 10 0,.s 10 0],[.s 35 0,.s 35 0]],[.s 32 5,.s 32 5]⟩,
⟨8,1,11,20,[[.s 33 0,.s 33 0],[.s 9 0,.s 9 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0],[.s 11 0,.s 11 0]],[.s 34 4,.s 34 4]⟩]⟩,
⟨1,6,2,0,0,[(0,3,4),(2,-6,1),(-2,6,-4)],0,3,4,6,0,0,0,0,24,0,0,0,
[⟨7,2,0,22,[[.f ⟨7,0,0,0,0,0,0,0,0⟩,.f ⟨7,0,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨21,15,0,0,0,0,0,0,0⟩,.f ⟨23,51,0,0,0,1,0,0,0⟩]],[.f ⟨7,0,0,0,0,0,0,0,1⟩,.f ⟨7,0,1,0,1,0,0,0,1⟩]⟩,
⟨7,2,1,23,[[.s 0 0,.s 0 0],[.f ⟨7,1,0,0,0,0,0,0,0⟩,.f ⟨7,1,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 2 0,.s 2 0]],[.s 0 2,.s 0 2]⟩,
⟨7,2,2,24,[[.s 1 0,.s 1 0],[.f ⟨7,2,0,0,0,0,0,0,0⟩,.f ⟨7,2,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 4 0,.s 4 0]],[.s 1 3,.s 1 3]⟩,
⟨7,2,3,32,[[.f ⟨26,168,0,0,1,0,0,0,0⟩,.f ⟨26,168,1,0,2,0,0,0,0⟩],[.f ⟨7,3,0,0,0,0,0,0,0⟩,.f ⟨7,3,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 5 0,.s 5 0]],[.s 5 0,.s 5 0]⟩,
⟨7,2,4,25,[[.s 2 0,.s 2 0],[.f ⟨7,4,0,0,0,0,0,0,0⟩,.f ⟨7,4,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0],[.f ⟨7,6,0,0,0,0,0,0,0⟩,.f ⟨7,6,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨7,2,5,31,[[.s 3 0,.s 3 0],[.f ⟨7,5,0,0,0,0,0,0,0⟩,.f ⟨7,5,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0],[.f ⟨7,7,0,0,0,0,0,0,0⟩,.f ⟨7,7,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.f ⟨7,7,0,0,0,0,0,0,1⟩,.f ⟨7,7,1,0,1,0,0,0,1⟩]⟩,
⟨7,2,6,26,[[.s 4 0,.s 4 0],[.s 16 0,.s 16 0],[.f ⟨7,6,0,0,0,0,0,0,0⟩,.f ⟨7,6,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 20 0,.s 20 0]],[.s 4 4,.s 4 4]⟩,
⟨7,2,7,30,[[.s 5 0,.s 5 0],[.s 17 0,.s 17 0],[.f ⟨7,7,0,0,0,0,0,0,0⟩,.f ⟨7,7,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.s 9 1,.s 9 1]⟩,
⟨7,2,8,26,[[.f ⟨7,6,0,0,0,0,0,0,0⟩,.f ⟨7,6,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.f ⟨7,8,0,0,0,0,0,0,0⟩,.f ⟨7,8,1,0,1,0,0,0,0⟩],[.s 20 0,.s 20 0],[.f ⟨7,10,0,0,0,0,0,0,0⟩,.f ⟨7,10,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0]],[.f ⟨7,6,0,0,0,0,0,0,5⟩,.f ⟨7,6,1,0,1,0,0,0,5⟩]⟩,
⟨7,2,9,29,[[.f ⟨7,7,0,0,0,0,0,0,0⟩,.f ⟨7,7,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨7,9,0,0,0,0,0,0,0⟩,.f ⟨7,9,1,0,1,0,0,0,0⟩],[.s 21 0,.s 21 0],[.f ⟨7,11,0,0,0,0,0,0,0⟩,.f ⟨7,11,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨7,11,0,0,0,0,0,0,1⟩,.f ⟨7,11,1,0,1,0,0,0,1⟩]⟩,
⟨7,2,10,27,[[.s 8 0,.s 8 0],[.s 20 0,.s 20 0],[.f ⟨7,10,0,0,0,0,0,0,0⟩,.f ⟨7,10,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0]],[.s 8 5,.s 8 5]⟩,
⟨7,2,11,28,[[.s 9 0,.s 9 0],[.s 21 0,.s 21 0],[.s 10 0,.s 10 0],[.f ⟨7,11,0,0,0,0,0,0,0⟩,.f ⟨7,11,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.s 10 4,.s 10 4]⟩,
⟨8,2,0,23,[[.s 0 0,.s 0 0],[.f ⟨23,0,0,0,0,0,0,0,0⟩,.f ⟨23,0,0,0,0,1,0,1,0⟩],[.s 13 0,.s 13 0],[.f ⟨21,27,0,0,0,0,0,0,0⟩,.f ⟨23,63,0,0,0,1,0,0,0⟩]],[.s 0 1,.s 0 1]⟩,
⟨8,2,1,24,[[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨23,1,0,0,0,0,0,0,0⟩,.f ⟨23,1,0,0,0,1,0,1,0⟩],[.s 14 0,.s 14 0]],[.s 12 2,.s 12 2]⟩,
⟨8,2,2,25,[[.s 13 0,.s 13 0],[.s 2 0,.s 2 0],[.f ⟨23,2,0,0,0,0,0,0,0⟩,.f ⟨23,2,0,0,0,1,0,1,0⟩],[.s 16 0,.s 16 0]],[.s 13 3,.s 13 3]⟩,
⟨8,2,3,32,[[.f ⟨24,0,0,0,1,0,0,0,0⟩,.f ⟨24,0,1,0,2,0,0,0,0⟩],[.s 3 0,.s 3 0],[.f ⟨23,3,0,0,0,0,0,0,0⟩,.f ⟨23,3,0,0,0,1,0,1,0⟩],[.s 17 0,.s 17 0]],[.s 17 0,.s 17 0]⟩,
⟨8,2,4,26,[[.s 14 0,.s 14 0],[.s 4 0,.s 4 0],[.f ⟨23,4,0,0,0,0,0,0,0⟩,.f ⟨23,4,0,0,0,1,0,1,0⟩],[.s 6 0,.s 6 0],[.s 18 0,.s 18 0]],[.s 14 3,.s 14 3]⟩,
⟨8,2,5,31,[[.s 15 0,.s 15 0],[.s 5 0,.s 5 0],[.f ⟨23,5,0,0,0,0,0,0,0⟩,.f ⟨23,5,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0],[.s 19 0,.s 19 0]],[.s 7 1,.s 7 1]⟩,
⟨8,2,6,27,[[.s 16 0,.s 16 0],[.f ⟨23,4,0,0,0,0,0,0,0⟩,.f ⟨23,4,0,0,0,1,0,1,0⟩],[.s 6 0,.s 6 0],[.f ⟨23,6,0,0,0,0,0,0,0⟩,.f ⟨23,6,0,0,0,1,0,1,0⟩],[.s 20 0,.s 20 0],[.f ⟨23,8,0,0,0,0,0,0,0⟩,.f ⟨23,8,0,0,0,1,0,1,0⟩]],[.s 16 4,.s 16 4]⟩,
⟨8,2,7,30,[[.s 17 0,.s 17 0],[.f ⟨23,5,0,0,0,0,0,0,0⟩,.f ⟨23,5,0,0,0,1,0,1,0⟩],[.s 7 0,.s 7 0],[.f ⟨23,7,0,0,0,0,0,0,0⟩,.f ⟨23,7,0,0,0,1,0,1,0⟩],[.s 21 0,.s 21 0],[.f ⟨23,9,0,0,0,0,0,0,0⟩,.f ⟨23,9,0,0,0,1,0,1,0⟩]],[.s 21 1,.s 21 1]⟩,
⟨8,2,8,27,[[.s 6 0,.s 6 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.f ⟨23,8,0,0,0,0,0,0,0⟩,.f ⟨23,8,0,0,0,1,0,1,0⟩],[.s 10 0,.s 10 0],[.s 22 0,.s 22 0]],[.s 6 5,.s 6 5]⟩,
⟨8,2,9,29,[[.s 7 0,.s 7 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.f ⟨23,9,0,0,0,0,0,0,0⟩,.f ⟨23,9,0,0,0,1,0,1,0⟩],[.s 11 0,.s 11 0],[.s 23 0,.s 23 0]],[.s 11 1,.s 11 1]⟩,
⟨8,2,10,28,[[.s 20 0,.s 20 0],[.f ⟨23,8,0,0,0,0,0,0,0⟩,.f ⟨23,8,0,0,0,1,0,1,0⟩],[.s 10 0,.s 10 0],[.f ⟨23,10,0,0,0,0,0,0,0⟩,.f ⟨23,10,0,0,0,1,0,1,0⟩],[.s 23 0,.s 23 0]],[.s 20 5,.s 20 5]⟩,
⟨8,2,11,29,[[.s 21 0,.s 21 0],[.f ⟨23,9,0,0,0,0,0,0,0⟩,.f ⟨23,9,0,0,0,1,0,1,0⟩],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0],[.f ⟨23,11,0,0,0,0,0,0,0⟩,.f ⟨23,11,0,0,0,1,0,1,0⟩]],[.s 22 4,.s 22 4]⟩,
⟨10,3,0,34,[[.f ⟨7,12,0,0,0,0,0,0,0⟩,.f ⟨7,12,1,0,1,0,0,0,0⟩],[.s 36 0,.s 36 0],[.s 25 0,.s 25 0],[.f ⟨23,15,0,0,0,0,0,0,0⟩,.f ⟨23,15,0,0,0,1,0,1,0⟩]],[.f ⟨7,12,0,0,0,0,0,0,1⟩,.f ⟨7,12,1,0,1,0,0,0,1⟩]⟩,
⟨10,3,1,35,[[.s 24 0,.s 24 0],[.f ⟨7,13,0,0,0,0,0,0,0⟩,.f ⟨7,13,1,0,1,0,0,0,0⟩],[.s 37 0,.s 37 0],[.s 26 0,.s 26 0]],[.s 24 2,.s 24 2]⟩,
⟨10,3,2,36,[[.s 25 0,.s 25 0],[.f ⟨7,14,0,0,0,0,0,0,0⟩,.f ⟨7,14,1,0,1,0,0,0,0⟩],[.s 38 0,.s 38 0],[.s 28 0,.s 28 0]],[.s 25 3,.s 25 3]⟩,
⟨10,3,3,44,[[.f ⟨26,264,0,0,1,0,0,0,0⟩,.f ⟨26,264,1,0,2,0,0,0,0⟩],[.f ⟨7,15,0,0,0,0,0,0,0⟩,.f ⟨7,15,1,0,1,0,0,0,0⟩],[.s 39 0,.s 39 0],[.s 29 0,.s 29 0]],[.s 29 0,.s 29 0]⟩,
⟨10,3,4,37,[[.s 26 0,.s 26 0],[.f ⟨7,16,0,0,0,0,0,0,0⟩,.f ⟨7,16,1,0,1,0,0,0,0⟩],[.s 40 0,.s 40 0],[.f ⟨7,18,0,0,0,0,0,0,0⟩,.f ⟨7,18,1,0,1,0,0,0,0⟩],[.s 30 0,.s 30 0]],[.s 26 3,.s 26 3]⟩,
⟨10,3,5,43,[[.s 27 0,.s 27 0],[.f ⟨7,17,0,0,0,0,0,0,0⟩,.f ⟨7,17,1,0,1,0,0,0,0⟩],[.s 41 0,.s 41 0],[.f ⟨7,19,0,0,0,0,0,0,0⟩,.f ⟨7,19,1,0,1,0,0,0,0⟩],[.s 31 0,.s 31 0]],[.f ⟨7,19,0,0,0,0,0,0,1⟩,.f ⟨7,19,1,0,1,0,0,0,1⟩]⟩,
⟨10,3,6,38,[[.s 28 0,.s 28 0],[.s 40 0,.s 40 0],[.f ⟨7,18,0,0,0,0,0,0,0⟩,.f ⟨7,18,1,0,1,0,0,0,0⟩],[.s 42 0,.s 42 0],[.s 32 0,.s 32 0],[.s 44 0,.s 44 0]],[.s 28 4,.s 28 4]⟩,
⟨10,3,7,42,[[.s 29 0,.s 29 0],[.s 41 0,.s 41 0],[.f ⟨7,19,0,0,0,0,0,0,0⟩,.f ⟨7,19,1,0,1,0,0,0,0⟩],[.s 43 0,.s 43 0],[.s 33 0,.s 33 0],[.s 45 0,.s 45 0]],[.s 33 1,.s 33 1]⟩,
⟨10,3,8,38,[[.f ⟨7,18,0,0,0,0,0,0,0⟩,.f ⟨7,18,1,0,1,0,0,0,0⟩],[.s 30 0,.s 30 0],[.f ⟨7,20,0,0,0,0,0,0,0⟩,.f ⟨7,20,1,0,1,0,0,0,0⟩],[.s 44 0,.s 44 0],[.f ⟨7,22,0,0,0,0,0,0,0⟩,.f ⟨7,22,1,0,1,0,0,0,0⟩],[.s 34 0,.s 34 0]],[.f ⟨7,18,0,0,0,0,0,0,5⟩,.f ⟨7,18,1,0,1,0,0,0,5⟩]⟩,
⟨10,3,9,41,[[.f ⟨7,19,0,0,0,0,0,0,0⟩,.f ⟨7,19,1,0,1,0,0,0,0⟩],[.s 31 0,.s 31 0],[.f ⟨7,21,0,0,0,0,0,0,0⟩,.f ⟨7,21,1,0,1,0,0,0,0⟩],[.s 45 0,.s 45 0],[.f ⟨7,23,0,0,0,0,0,0,0⟩,.f ⟨7,23,1,0,1,0,0,0,0⟩],[.s 35 0,.s 35 0]],[.f ⟨7,23,0,0,0,0,0,0,1⟩,.f ⟨7,23,1,0,1,0,0,0,1⟩]⟩,
⟨10,3,10,39,[[.s 32 0,.s 32 0],[.s 44 0,.s 44 0],[.f ⟨7,22,0,0,0,0,0,0,0⟩,.f ⟨7,22,1,0,1,0,0,0,0⟩],[.s 46 0,.s 46 0],[.s 35 0,.s 35 0]],[.s 32 5,.s 32 5]⟩,
⟨10,3,11,40,[[.s 33 0,.s 33 0],[.s 45 0,.s 45 0],[.s 34 0,.s 34 0],[.f ⟨7,23,0,0,0,0,0,0,0⟩,.f ⟨7,23,1,0,1,0,0,0,0⟩],[.s 47 0,.s 47 0]],[.s 34 4,.s 34 4]⟩,
⟨11,3,0,35,[[.s 24 0,.s 24 0],[.f ⟨23,36,0,0,0,0,0,0,0⟩,.f ⟨23,36,0,0,0,1,0,1,0⟩],[.s 37 0,.s 37 0],[.f ⟨23,27,0,0,0,0,0,0,0⟩,.f ⟨23,27,0,0,0,1,0,1,0⟩]],[.s 24 1,.s 24 1]⟩,
⟨11,3,1,36,[[.s 36 0,.s 36 0],[.s 25 0,.s 25 0],[.f ⟨23,37,0,0,0,0,0,0,0⟩,.f ⟨23,37,0,0,0,1,0,1,0⟩],[.s 38 0,.s 38 0]],[.s 36 2,.s 36 2]⟩,
⟨11,3,2,37,[[.s 37 0,.s 37 0],[.s 26 0,.s 26 0],[.f ⟨23,38,0,0,0,0,0,0,0⟩,.f ⟨23,38,0,0,0,1,0,1,0⟩],[.s 40 0,.s 40 0]],[.s 37 3,.s 37 3]⟩,
⟨11,3,3,44,[[.f ⟨24,12,0,0,1,0,0,0,0⟩,.f ⟨24,12,1,0,2,0,0,0,0⟩],[.s 27 0,.s 27 0],[.f ⟨23,39,0,0,0,0,0,0,0⟩,.f ⟨23,39,0,0,0,1,0,1,0⟩],[.s 41 0,.s 41 0]],[.s 41 0,.s 41 0]⟩,
⟨11,3,4,38,[[.s 38 0,.s 38 0],[.s 28 0,.s 28 0],[.f ⟨23,40,0,0,0,0,0,0,0⟩,.f ⟨23,40,0,0,0,1,0,1,0⟩],[.s 30 0,.s 30 0],[.s 42 0,.s 42 0]],[.s 38 3,.s 38 3]⟩,
⟨11,3,5,43,[[.s 39 0,.s 39 0],[.s 29 0,.s 29 0],[.f ⟨23,41,0,0,0,0,0,0,0⟩,.f ⟨23,41,0,0,0,1,0,1,0⟩],[.s 31 0,.s 31 0],[.s 43 0,.s 43 0]],[.s 31 1,.s 31 1]⟩,
⟨11,3,6,39,[[.s 40 0,.s 40 0],[.f ⟨23,40,0,0,0,0,0,0,0⟩,.f ⟨23,40,0,0,0,1,0,1,0⟩],[.s 30 0,.s 30 0],[.f ⟨23,42,0,0,0,0,0,0,0⟩,.f ⟨23,42,0,0,0,1,0,1,0⟩],[.s 44 0,.s 44 0],[.f ⟨23,44,0,0,0,0,0,0,0⟩,.f ⟨23,44,0,0,0,1,0,1,0⟩]],[.s 40 4,.s 40 4]⟩,
⟨11,3,7,42,[[.s 41 0,.s 41 0],[.f ⟨23,41,0,0,0,0,0,0,0⟩,.f ⟨23,41,0,0,0,1,0,1,0⟩],[.s 31 0,.s 31 0],[.f ⟨23,43,0,0,0,0,0,0,0⟩,.f ⟨23,43,0,0,0,1,0,1,0⟩],[.s 45 0,.s 45 0],[.f ⟨23,45,0,0,0,0,0,0,0⟩,.f ⟨23,45,0,0,0,1,0,1,0⟩]],[.s 45 1,.s 45 1]⟩,
⟨11,3,8,39,[[.s 30 0,.s 30 0],[.s 42 0,.s 42 0],[.s 32 0,.s 32 0],[.f ⟨23,44,0,0,0,0,0,0,0⟩,.f ⟨23,44,0,0,0,1,0,1,0⟩],[.s 34 0,.s 34 0],[.s 46 0,.s 46 0]],[.s 30 5,.s 30 5]⟩,
⟨11,3,9,41,[[.s 31 0,.s 31 0],[.s 43 0,.s 43 0],[.s 33 0,.s 33 0],[.f ⟨23,45,0,0,0,0,0,0,0⟩,.f ⟨23,45,0,0,0,1,0,1,0⟩],[.s 35 0,.s 35 0],[.s 47 0,.s 47 0]],[.s 35 1,.s 35 1]⟩,
⟨11,3,10,40,[[.s 44 0,.s 44 0],[.f ⟨23,44,0,0,0,0,0,0,0⟩,.f ⟨23,44,0,0,0,1,0,1,0⟩],[.s 34 0,.s 34 0],[.f ⟨23,46,0,0,0,0,0,0,0⟩,.f ⟨23,46,0,0,0,1,0,1,0⟩],[.s 47 0,.s 47 0]],[.s 44 5,.s 44 5]⟩,
⟨11,3,11,41,[[.s 45 0,.s 45 0],[.f ⟨23,45,0,0,0,0,0,0,0⟩,.f ⟨23,45,0,0,0,1,0,1,0⟩],[.s 46 0,.s 46 0],[.s 35 0,.s 35 0],[.f ⟨23,47,0,0,0,0,0,0,0⟩,.f ⟨23,47,0,0,0,1,0,1,0⟩]],[.s 46 4,.s 46 4]⟩]⟩,
⟨2,3,0,6,2,[(2,-6,5),(0,3,4)],2,-6,5,6,0,3,4,6,3,24,8,1,
[⟨9,2,0,24,[[.f ⟨22,12,0,0,0,0,0,0,0⟩,.s 24 0,.f ⟨22,12,0,1,1,0,0,0,0⟩,.s 24 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨21,3,0,0,1,0,0,0,0⟩,.f ⟨21,3,1,0,2,0,0,0,0⟩,.s 39 0,.s 39 0]],[.f ⟨22,12,0,0,0,0,0,0,1⟩,.s 24 1,.f ⟨22,12,0,1,1,0,0,0,1⟩,.s 24 1]⟩,
⟨9,2,1,25,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨22,13,0,0,0,0,0,0,0⟩,.s 25 0,.f ⟨22,13,0,1,1,0,0,0,0⟩,.s 25 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 0 2,.s 0 2,.s 0 2,.s 0 2]⟩,
⟨9,2,2,26,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨22,14,0,0,0,0,0,0,0⟩,.s 26 0,.f ⟨22,14,0,1,1,0,0,0,0⟩,.s 26 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 1 3,.s 1 3,.s 1 3,.s 1 3]⟩,
⟨9,2,3,32,[[.f ⟨7,12,0,0,0,0,0,0,0⟩,.s 36 0,.f ⟨7,12,0,1,1,0,0,0,0⟩,.s 36 0],[.f ⟨22,15,0,0,0,0,0,0,0⟩,.s 27 0,.f ⟨22,15,0,1,1,0,0,0,0⟩,.s 27 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 5 0,.s 27 2,.s 5 0,.s 27 2]⟩,
⟨9,2,4,27,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.f ⟨22,16,0,0,0,0,0,0,0⟩,.s 28 0,.f ⟨22,16,0,1,1,0,0,0,0⟩,.s 28 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨22,18,0,0,0,0,0,0,0⟩,.s 30 0,.f ⟨22,18,0,1,1,0,0,0,0⟩,.s 30 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 2 3,.s 2 3,.s 2 3,.s 2 3]⟩,
⟨9,2,5,31,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.f ⟨22,17,0,0,0,0,0,0,0⟩,.s 29 0,.f ⟨22,17,0,1,1,0,0,0,0⟩,.s 29 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨22,19,0,0,0,0,0,0,0⟩,.s 31 0,.f ⟨22,19,0,1,1,0,0,0,0⟩,.s 31 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.f ⟨22,19,0,0,0,0,0,0,1⟩,.s 29 2,.f ⟨22,19,0,1,1,0,0,0,1⟩,.s 29 2]⟩,
⟨9,2,6,28,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨22,18,0,0,0,0,0,0,0⟩,.s 30 0,.f ⟨22,18,0,1,1,0,0,0,0⟩,.s 30 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 4 4,.s 4 4,.s 4 4,.s 4 4]⟩,
⟨9,2,7,31,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨22,19,0,0,0,0,0,0,0⟩,.s 31 0,.f ⟨22,19,0,1,1,0,0,0,0⟩,.s 31 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.f ⟨22,19,0,0,0,0,0,0,3⟩,.s 31 3,.f ⟨22,19,0,1,1,0,0,0,3⟩,.s 31 3]⟩,
⟨9,2,8,28,[[.f ⟨22,18,0,0,0,0,0,0,0⟩,.s 30 0,.f ⟨22,18,0,1,1,0,0,0,0⟩,.s 30 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨22,20,0,0,0,0,0,0,0⟩,.s 32 0,.f ⟨22,20,0,1,1,0,0,0,0⟩,.s 32 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨22,22,0,0,0,0,0,0,0⟩,.s 34 0,.f ⟨22,22,0,1,1,0,0,0,0⟩,.s 34 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.f ⟨22,18,0,0,0,0,0,0,5⟩,.s 30 5,.f ⟨22,18,0,1,1,0,0,0,5⟩,.s 30 5]⟩,
⟨9,2,9,30,[[.f ⟨22,19,0,0,0,0,0,0,0⟩,.s 31 0,.f ⟨22,19,0,1,1,0,0,0,0⟩,.s 31 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.f ⟨22,21,0,0,0,0,0,0,0⟩,.s 33 0,.f ⟨22,21,0,1,1,0,0,0,0⟩,.s 33 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.f ⟨22,23,0,0,0,0,0,0,0⟩,.s 35 0,.f ⟨22,23,0,1,1,0,0,0,0⟩,.s 35 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.f ⟨22,21,0,0,0,0,0,0,3⟩,.s 33 3,.f ⟨22,21,0,1,1,0,0,0,3⟩,.s 33 3]⟩,
⟨9,2,10,29,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨22,22,0,0,0,0,0,0,0⟩,.s 34 0,.f ⟨22,22,0,1,1,0,0,0,0⟩,.s 34 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 8 5,.s 8 5,.s 8 5,.s 8 5]⟩,
⟨9,2,11,30,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.f ⟨22,23,0,0,0,0,0,0,0⟩,.s 35 0,.f ⟨22,23,0,1,1,0,0,0,0⟩,.s 35 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 10 4,.s 10 4,.s 10 4,.s 10 4]⟩,
⟨10,2,0,25,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.f ⟨21,15,0,0,1,0,0,0,0⟩,.f ⟨21,15,1,0,2,0,0,0,0⟩,.s 51 0,.s 51 0]],[.s 0 1,.s 0 1,.s 0 1,.s 0 1]⟩,
⟨10,2,1,26,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 12 2,.s 12 2,.s 12 2,.s 12 2]⟩,
⟨10,2,2,27,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 13 3,.s 13 3,.s 13 3,.s 13 3]⟩,
⟨10,2,3,33,[[.f ⟨22,24,0,0,0,0,0,0,0⟩,.s 48 0,.f ⟨22,24,0,1,1,0,0,0,0⟩,.s 48 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 3 2,.s 3 2,.s 3 2,.s 3 2]⟩,
⟨10,2,4,28,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0]],[.s 14 3,.s 14 3,.s 14 3,.s 14 3]⟩,
⟨10,2,5,32,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0]],[.s 5 2,.s 5 2,.s 5 2,.s 5 2]⟩,
⟨10,2,6,29,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 16 4,.s 16 4,.s 16 4,.s 16 4]⟩,
⟨10,2,7,32,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.s 7 3,.s 7 3,.s 7 3,.s 7 3]⟩,
⟨10,2,8,29,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.s 6 5,.s 6 5,.s 6 5,.s 6 5]⟩,
⟨10,2,9,31,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 9 3,.s 9 3,.s 9 3,.s 9 3]⟩,
⟨10,2,10,30,[[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 20 5,.s 20 5,.s 20 5,.s 20 5]⟩,
⟨10,2,11,31,[[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 22 4,.s 22 4,.s 22 4,.s 22 4]⟩,
⟨11,2,0,26,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.f ⟨21,27,0,0,1,0,0,0,0⟩,.f ⟨21,27,1,0,2,0,0,0,0⟩,.s 63 0,.s 63 0]],[.s 12 1,.s 12 1,.s 12 1,.s 12 1]⟩,
⟨11,2,1,27,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.s 24 2,.s 24 2,.s 24 2,.s 24 2]⟩,
⟨11,2,2,28,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.s 25 3,.s 25 3,.s 25 3,.s 25 3]⟩,
⟨11,2,3,34,[[.f ⟨22,36,0,0,0,0,0,0,0⟩,.s 60 0,.f ⟨22,36,0,1,1,0,0,0,0⟩,.s 60 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0]],[.s 15 2,.s 15 2,.s 15 2,.s 15 2]⟩,
⟨11,2,4,29,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0]],[.s 26 3,.s 26 3,.s 26 3,.s 26 3]⟩,
⟨11,2,5,33,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 17 2,.s 17 2,.s 17 2,.s 17 2]⟩,
⟨11,2,6,30,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 28 4,.s 28 4,.s 28 4,.s 28 4]⟩,
⟨11,2,7,33,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 19 3,.s 19 3,.s 19 3,.s 19 3]⟩,
⟨11,2,8,30,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.s 18 5,.s 18 5,.s 18 5,.s 18 5]⟩,
⟨11,2,9,32,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 21 3,.s 21 3,.s 21 3,.s 21 3]⟩,
⟨11,2,10,31,[[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 32 5,.s 32 5,.s 32 5,.s 32 5]⟩,
⟨11,2,11,32,[[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 34 4,.s 34 4,.s 34 4,.s 34 4]⟩,
⟨12,3,0,36,[[.f ⟨22,36,0,0,0,0,0,0,0⟩,.s 60 0,.f ⟨22,36,0,1,1,0,0,0,0⟩,.s 60 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.f ⟨22,36,0,0,0,0,0,0,1⟩,.s 60 1,.f ⟨22,36,0,1,1,0,0,0,1⟩,.s 60 1]⟩,
⟨12,3,1,37,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.f ⟨22,37,0,0,0,0,0,0,0⟩,.s 61 0,.f ⟨22,37,0,1,1,0,0,0,0⟩,.s 61 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.s 36 2,.s 36 2,.s 36 2,.s 36 2]⟩,
⟨12,3,2,38,[[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.f ⟨22,38,0,0,0,0,0,0,0⟩,.s 62 0,.f ⟨22,38,0,1,1,0,0,0,0⟩,.s 62 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0]],[.s 37 3,.s 37 3,.s 37 3,.s 37 3]⟩,
⟨12,3,3,44,[[.f ⟨7,0,0,0,1,0,0,0,0⟩,.s 0 0,.f ⟨7,0,0,1,2,0,0,0,0⟩,.s 0 0],[.f ⟨22,39,0,0,0,0,0,0,0⟩,.s 63 0,.f ⟨22,39,0,1,1,0,0,0,0⟩,.s 63 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0]],[.s 41 0,.s 63 2,.s 41 0,.s 63 2]⟩,
⟨12,3,4,39,[[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.f ⟨22,40,0,0,0,0,0,0,0⟩,.s 64 0,.f ⟨22,40,0,1,1,0,0,0,0⟩,.s 64 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.f ⟨22,42,0,0,0,0,0,0,0⟩,.s 66 0,.f ⟨22,42,0,1,1,0,0,0,0⟩,.s 66 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.s 38 3,.s 38 3,.s 38 3,.s 38 3]⟩,
⟨12,3,5,43,[[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.f ⟨22,41,0,0,0,0,0,0,0⟩,.s 65 0,.f ⟨22,41,0,1,1,0,0,0,0⟩,.s 65 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.f ⟨22,43,0,0,0,0,0,0,0⟩,.s 67 0,.f ⟨22,43,0,1,1,0,0,0,0⟩,.s 67 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.f ⟨22,43,0,0,0,0,0,0,1⟩,.s 65 2,.f ⟨22,43,0,1,1,0,0,0,1⟩,.s 65 2]⟩,
⟨12,3,6,40,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.f ⟨22,42,0,0,0,0,0,0,0⟩,.s 66 0,.f ⟨22,42,0,1,1,0,0,0,0⟩,.s 66 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0]],[.s 40 4,.s 40 4,.s 40 4,.s 40 4]⟩,
⟨12,3,7,43,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.f ⟨22,43,0,0,0,0,0,0,0⟩,.s 67 0,.f ⟨22,43,0,1,1,0,0,0,0⟩,.s 67 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0]],[.f ⟨22,43,0,0,0,0,0,0,3⟩,.s 67 3,.f ⟨22,43,0,1,1,0,0,0,3⟩,.s 67 3]⟩,
⟨12,3,8,40,[[.f ⟨22,42,0,0,0,0,0,0,0⟩,.s 66 0,.f ⟨22,42,0,1,1,0,0,0,0⟩,.s 66 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.f ⟨22,44,0,0,0,0,0,0,0⟩,.s 68 0,.f ⟨22,44,0,1,1,0,0,0,0⟩,.s 68 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.f ⟨22,46,0,0,0,0,0,0,0⟩,.s 70 0,.f ⟨22,46,0,1,1,0,0,0,0⟩,.s 70 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0]],[.f ⟨22,42,0,0,0,0,0,0,5⟩,.s 66 5,.f ⟨22,42,0,1,1,0,0,0,5⟩,.s 66 5]⟩,
⟨12,3,9,42,[[.f ⟨22,43,0,0,0,0,0,0,0⟩,.s 67 0,.f ⟨22,43,0,1,1,0,0,0,0⟩,.s 67 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.f ⟨22,45,0,0,0,0,0,0,0⟩,.s 69 0,.f ⟨22,45,0,1,1,0,0,0,0⟩,.s 69 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.f ⟨22,47,0,0,0,0,0,0,0⟩,.s 71 0,.f ⟨22,47,0,1,1,0,0,0,0⟩,.s 71 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.f ⟨22,45,0,0,0,0,0,0,3⟩,.s 69 3,.f ⟨22,45,0,1,1,0,0,0,3⟩,.s 69 3]⟩,
⟨12,3,10,41,[[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.f ⟨22,46,0,0,0,0,0,0,0⟩,.s 70 0,.f ⟨22,46,0,1,1,0,0,0,0⟩,.s 70 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 44 5,.s 44 5,.s 44 5,.s 44 5]⟩,
⟨12,3,11,42,[[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.f ⟨22,47,0,0,0,0,0,0,0⟩,.s 71 0,.f ⟨22,47,0,1,1,0,0,0,0⟩,.s 71 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 46 4,.s 46 4,.s 46 4,.s 46 4]⟩,
⟨13,3,0,37,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0]],[.s 36 1,.s 36 1,.s 36 1,.s 36 1]⟩,
⟨13,3,1,38,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0]],[.s 48 2,.s 48 2,.s 48 2,.s 48 2]⟩,
⟨13,3,2,39,[[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0]],[.s 49 3,.s 49 3,.s 49 3,.s 49 3]⟩,
⟨13,3,3,45,[[.f ⟨22,0,0,0,1,0,0,0,0⟩,.s 12 0,.f ⟨22,0,0,1,2,0,0,0,0⟩,.s 12 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]],[.s 39 2,.s 39 2,.s 39 2,.s 39 2]⟩,
⟨13,3,4,40,[[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0]],[.s 50 3,.s 50 3,.s 50 3,.s 50 3]⟩,
⟨13,3,5,44,[[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0]],[.s 41 2,.s 41 2,.s 41 2,.s 41 2]⟩,
⟨13,3,6,41,[[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0]],[.s 52 4,.s 52 4,.s 52 4,.s 52 4]⟩,
⟨13,3,7,44,[[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0]],[.s 43 3,.s 43 3,.s 43 3,.s 43 3]⟩,
⟨13,3,8,41,[[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0]],[.s 42 5,.s 42 5,.s 42 5,.s 42 5]⟩,
⟨13,3,9,43,[[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 45 3,.s 45 3,.s 45 3,.s 45 3]⟩,
⟨13,3,10,42,[[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 56 5,.s 56 5,.s 56 5,.s 56 5]⟩,
⟨13,3,11,43,[[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 58 4,.s 58 4,.s 58 4,.s 58 4]⟩,
⟨14,3,0,38,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0]],[.s 48 1,.s 48 1,.s 48 1,.s 48 1]⟩,
⟨14,3,1,39,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0]],[.s 60 2,.s 60 2,.s 60 2,.s 60 2]⟩,
⟨14,3,2,40,[[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0]],[.s 61 3,.s 61 3,.s 61 3,.s 61 3]⟩,
⟨14,3,3,46,[[.f ⟨22,12,0,0,1,0,0,0,0⟩,.s 24 0,.f ⟨22,12,0,1,2,0,0,0,0⟩,.s 24 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0]],[.s 51 2,.s 51 2,.s 51 2,.s 51 2]⟩,
⟨14,3,4,41,[[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0]],[.s 62 3,.s 62 3,.s 62 3,.s 62 3]⟩,
⟨14,3,5,45,[[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0]],[.s 53 2,.s 53 2,.s 53 2,.s 53 2]⟩,
⟨14,3,6,42,[[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0]],[.s 64 4,.s 64 4,.s 64 4,.s 64 4]⟩,
⟨14,3,7,45,[[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0]],[.s 55 3,.s 55 3,.s 55 3,.s 55 3]⟩,
⟨14,3,8,42,[[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0]],[.s 54 5,.s 54 5,.s 54 5,.s 54 5]⟩,
⟨14,3,9,44,[[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 57 3,.s 57 3,.s 57 3,.s 57 3]⟩,
⟨14,3,10,43,[[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 68 5,.s 68 5,.s 68 5,.s 68 5]⟩,
⟨14,3,11,44,[[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 70 4,.s 70 4,.s 70 4,.s 70 4]⟩]⟩,
⟨1,6,2,0,0,[(2,6,3),(-2,6,1),(2,-6,-2)],2,6,3,24,0,0,0,0,24,0,0,0,
[⟨2,1,0,9,[[.f ⟨26,168,0,0,0,0,0,0,0⟩,.f ⟨26,168,1,0,1,0,0,0,0⟩],[.f ⟨6,0,0,0,0,0,0,0,0⟩,.f ⟨7,12,1,0,0,0,0,0,0⟩],[.s 1 0,.s 1 0],[.f ⟨4,15,0,0,0,0,0,0,0⟩,.f ⟨22,15,1,0,0,0,0,0,0⟩]],[.f ⟨4,15,0,0,0,0,0,0,0⟩,.f ⟨22,15,1,0,0,0,0,0,0⟩]⟩,
⟨2,1,1,10,[[.s 0 0,.s 0 0],[.f ⟨26,169,0,0,0,0,0,0,0⟩,.f ⟨26,169,1,0,1,0,0,0,0⟩],[.f ⟨6,1,0,0,0,0,0,0,0⟩,.f ⟨7,13,1,0,0,0,0,0,0⟩],[.s 2 0,.s 2 0]],[.s 0 2,.s 0 2]⟩,
⟨2,1,2,11,[[.s 1 0,.s 1 0],[.f ⟨26,170,0,0,0,0,0,0,0⟩,.f ⟨26,170,1,0,1,0,0,0,0⟩],[.f ⟨6,2,0,0,0,0,0,0,0⟩,.f ⟨7,14,1,0,0,0,0,0,0⟩],[.s 4 0,.s 4 0]],[.s 1 3,.s 1 3]⟩,
⟨2,1,3,20,[[.f ⟨26,216,0,0,0,0,0,0,0⟩,.f ⟨26,216,1,0,1,0,0,0,0⟩],[.f ⟨26,171,0,0,0,0,0,0,0⟩,.f ⟨26,171,1,0,1,0,0,0,0⟩],[.f ⟨6,3,0,0,0,0,0,0,0⟩,.f ⟨7,15,1,0,0,0,0,0,0⟩],[.s 5 0,.s 5 0]],[.s 5 0,.s 5 0]⟩,
⟨2,1,4,12,[[.s 2 0,.s 2 0],[.f ⟨26,172,0,0,0,0,0,0,0⟩,.f ⟨26,172,1,0,1,0,0,0,0⟩],[.f ⟨6,4,0,0,0,0,0,0,0⟩,.f ⟨7,16,1,0,0,0,0,0,0⟩],[.f ⟨26,174,0,0,0,0,0,0,0⟩,.f ⟨26,174,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨2,1,5,19,[[.s 3 0,.s 3 0],[.f ⟨26,173,0,0,0,0,0,0,0⟩,.f ⟨26,173,1,0,1,0,0,0,0⟩],[.f ⟨6,5,0,0,0,0,0,0,0⟩,.f ⟨7,17,1,0,0,0,0,0,0⟩],[.f ⟨26,175,0,0,0,0,0,0,0⟩,.f ⟨26,175,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.f ⟨26,175,0,0,0,0,0,0,1⟩,.f ⟨26,175,1,0,1,0,0,0,1⟩]⟩,
⟨2,1,6,13,[[.s 4 0,.s 4 0],[.f ⟨6,4,0,0,0,0,0,0,0⟩,.f ⟨7,16,1,0,0,0,0,0,0⟩],[.f ⟨26,174,0,0,0,0,0,0,0⟩,.f ⟨26,174,1,0,1,0,0,0,0⟩],[.f ⟨6,6,0,0,0,0,0,0,0⟩,.f ⟨7,18,1,0,0,0,0,0,0⟩],[.s 8 0,.s 8 0],[.f ⟨6,8,0,0,0,0,0,0,0⟩,.f ⟨7,20,1,0,0,0,0,0,0⟩]],[.s 4 4,.s 4 4]⟩,
⟨2,1,7,18,[[.s 5 0,.s 5 0],[.f ⟨6,5,0,0,0,0,0,0,0⟩,.f ⟨7,17,1,0,0,0,0,0,0⟩],[.f ⟨26,175,0,0,0,0,0,0,0⟩,.f ⟨26,175,1,0,1,0,0,0,0⟩],[.f ⟨6,7,0,0,0,0,0,0,0⟩,.f ⟨7,19,1,0,0,0,0,0,0⟩],[.s 9 0,.s 9 0],[.f ⟨6,9,0,0,0,0,0,0,0⟩,.f ⟨7,21,1,0,0,0,0,0,0⟩]],[.s 9 1,.s 9 1]⟩,
⟨2,1,8,14,[[.f ⟨26,174,0,0,0,0,0,0,0⟩,.f ⟨26,174,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.f ⟨26,176,0,0,0,0,0,0,0⟩,.f ⟨26,176,1,0,1,0,0,0,0⟩],[.f ⟨6,8,0,0,0,0,0,0,0⟩,.f ⟨7,20,1,0,0,0,0,0,0⟩],[.f ⟨26,178,0,0,0,0,0,0,0⟩,.f ⟨26,178,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0]],[.f ⟨26,174,0,0,0,0,0,0,5⟩,.f ⟨26,174,1,0,1,0,0,0,5⟩]⟩,
⟨2,1,9,17,[[.f ⟨26,175,0,0,0,0,0,0,0⟩,.f ⟨26,175,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨26,177,0,0,0,0,0,0,0⟩,.f ⟨26,177,1,0,1,0,0,0,0⟩],[.f ⟨6,9,0,0,0,0,0,0,0⟩,.f ⟨7,21,1,0,0,0,0,0,0⟩],[.f ⟨26,179,0,0,0,0,0,0,0⟩,.f ⟨26,179,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨26,179,0,0,0,0,0,0,1⟩,.f ⟨26,179,1,0,1,0,0,0,1⟩]⟩,
⟨2,1,10,15,[[.s 8 0,.s 8 0],[.f ⟨6,8,0,0,0,0,0,0,0⟩,.f ⟨7,20,1,0,0,0,0,0,0⟩],[.f ⟨26,178,0,0,0,0,0,0,0⟩,.f ⟨26,178,1,0,1,0,0,0,0⟩],[.f ⟨6,10,0,0,0,0,0,0,0⟩,.f ⟨7,22,1,0,0,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.s 8 5,.s 8 5]⟩,
⟨2,1,11,16,[[.s 9 0,.s 9 0],[.f ⟨6,9,0,0,0,0,0,0,0⟩,.f ⟨7,21,1,0,0,0,0,0,0⟩],[.s 10 0,.s 10 0],[.f ⟨26,179,0,0,0,0,0,0,0⟩,.f ⟨26,179,1,0,1,0,0,0,0⟩],[.f ⟨6,11,0,0,0,0,0,0,0⟩,.f ⟨7,23,1,0,0,0,0,0,0⟩]],[.s 10 4,.s 10 4]⟩,
⟨5,2,0,21,[[.f ⟨26,264,0,0,0,0,0,0,0⟩,.f ⟨26,264,1,0,1,0,0,0,0⟩],[.f ⟨7,0,0,0,0,0,0,0,0⟩,.f ⟨7,0,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.f ⟨20,15,0,0,0,0,0,0,0⟩,.f ⟨22,39,1,0,0,0,0,0,0⟩]],[.f ⟨20,15,0,0,0,0,0,0,0⟩,.f ⟨22,39,1,0,0,0,0,0,0⟩]⟩,
⟨5,2,1,22,[[.s 12 0,.s 12 0],[.f ⟨26,265,0,0,0,0,0,0,0⟩,.f ⟨26,265,1,0,1,0,0,0,0⟩],[.f ⟨7,1,0,0,0,0,0,0,0⟩,.f ⟨7,1,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0]],[.s 12 2,.s 12 2]⟩,
⟨5,2,2,23,[[.s 13 0,.s 13 0],[.f ⟨26,266,0,0,0,0,0,0,0⟩,.f ⟨26,266,1,0,1,0,0,0,0⟩],[.f ⟨7,2,0,0,0,0,0,0,0⟩,.f ⟨7,2,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0]],[.s 13 3,.s 13 3]⟩,
⟨5,2,3,32,[[.f ⟨26,72,0,0,1,0,0,0,0⟩,.f ⟨26,72,1,0,2,0,0,0,0⟩],[.f ⟨26,267,0,0,0,0,0,0,0⟩,.f ⟨26,267,1,0,1,0,0,0,0⟩],[.f ⟨7,3,0,0,0,0,0,0,0⟩,.f ⟨7,3,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0]],[.s 17 0,.s 17 0]⟩,
⟨5,2,4,24,[[.s 14 0,.s 14 0],[.f ⟨26,268,0,0,0,0,0,0,0⟩,.f ⟨26,268,1,0,1,0,0,0,0⟩],[.f ⟨7,4,0,0,0,0,0,0,0⟩,.f ⟨7,4,1,0,1,0,0,0,0⟩],[.f ⟨26,270,0,0,0,0,0,0,0⟩,.f ⟨26,270,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0]],[.s 14 3,.s 14 3]⟩,
⟨5,2,5,31,[[.s 15 0,.s 15 0],[.f ⟨26,269,0,0,0,0,0,0,0⟩,.f ⟨26,269,1,0,1,0,0,0,0⟩],[.f ⟨7,5,0,0,0,0,0,0,0⟩,.f ⟨7,5,1,0,1,0,0,0,0⟩],[.f ⟨26,271,0,0,0,0,0,0,0⟩,.f ⟨26,271,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0]],[.f ⟨26,271,0,0,0,0,0,0,1⟩,.f ⟨26,271,1,0,1,0,0,0,1⟩]⟩,
⟨5,2,6,25,[[.s 16 0,.s 16 0],[.f ⟨7,4,0,0,0,0,0,0,0⟩,.f ⟨7,4,1,0,1,0,0,0,0⟩],[.f ⟨26,270,0,0,0,0,0,0,0⟩,.f ⟨26,270,1,0,1,0,0,0,0⟩],[.f ⟨7,6,0,0,0,0,0,0,0⟩,.f ⟨7,6,1,0,1,0,0,0,0⟩],[.s 20 0,.s 20 0],[.f ⟨7,8,0,0,0,0,0,0,0⟩,.f ⟨7,8,1,0,1,0,0,0,0⟩]],[.s 16 4,.s 16 4]⟩,
⟨5,2,7,30,[[.s 17 0,.s 17 0],[.f ⟨7,5,0,0,0,0,0,0,0⟩,.f ⟨7,5,1,0,1,0,0,0,0⟩],[.f ⟨26,271,0,0,0,0,0,0,0⟩,.f ⟨26,271,1,0,1,0,0,0,0⟩],[.f ⟨7,7,0,0,0,0,0,0,0⟩,.f ⟨7,7,1,0,1,0,0,0,0⟩],[.s 21 0,.s 21 0],[.f ⟨7,9,0,0,0,0,0,0,0⟩,.f ⟨7,9,1,0,1,0,0,0,0⟩]],[.s 21 1,.s 21 1]⟩,
⟨5,2,8,26,[[.f ⟨26,270,0,0,0,0,0,0,0⟩,.f ⟨26,270,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.f ⟨26,272,0,0,0,0,0,0,0⟩,.f ⟨26,272,1,0,1,0,0,0,0⟩],[.f ⟨7,8,0,0,0,0,0,0,0⟩,.f ⟨7,8,1,0,1,0,0,0,0⟩],[.f ⟨26,274,0,0,0,0,0,0,0⟩,.f ⟨26,274,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0]],[.f ⟨26,270,0,0,0,0,0,0,5⟩,.f ⟨26,270,1,0,1,0,0,0,5⟩]⟩,
⟨5,2,9,29,[[.f ⟨26,271,0,0,0,0,0,0,0⟩,.f ⟨26,271,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.f ⟨26,273,0,0,0,0,0,0,0⟩,.f ⟨26,273,1,0,1,0,0,0,0⟩],[.f ⟨7,9,0,0,0,0,0,0,0⟩,.f ⟨7,9,1,0,1,0,0,0,0⟩],[.f ⟨26,275,0,0,0,0,0,0,0⟩,.f ⟨26,275,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.f ⟨26,275,0,0,0,0,0,0,1⟩,.f ⟨26,275,1,0,1,0,0,0,1⟩]⟩,
⟨5,2,10,27,[[.s 20 0,.s 20 0],[.f ⟨7,8,0,0,0,0,0,0,0⟩,.f ⟨7,8,1,0,1,0,0,0,0⟩],[.f ⟨26,274,0,0,0,0,0,0,0⟩,.f ⟨26,274,1,0,1,0,0,0,0⟩],[.f ⟨7,10,0,0,0,0,0,0,0⟩,.f ⟨7,10,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.s 20 5,.s 20 5]⟩,
⟨5,2,11,28,[[.s 21 0,.s 21 0],[.f ⟨7,9,0,0,0,0,0,0,0⟩,.f ⟨7,9,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.f ⟨26,275,0,0,0,0,0,0,0⟩,.f ⟨26,275,1,0,1,0,0,0,0⟩],[.f ⟨7,11,0,0,0,0,0,0,0⟩,.f ⟨7,11,1,0,1,0,0,0,0⟩]],[.s 22 4,.s 22 4]⟩]⟩,
⟨1,-6,2,0,0,[(-2,6,3),(2,6,1),(-2,-6,-2)],-2,6,3,24,0,0,0,0,24,0,0,0,
[⟨-5,2,0,21,[[.f ⟨9,12,0,0,0,0,0,0,0⟩,.f ⟨9,12,1,0,1,0,0,0,0⟩],[.f ⟨26,0,0,0,0,0,0,0,0⟩,.f ⟨26,0,0,0,0,1,0,1,0⟩],[.s 1 0,.s 1 0],[.f ⟨27,3,0,0,0,0,0,0,0⟩,.f ⟨28,3,1,0,0,0,0,0,0⟩]],[.f ⟨27,3,0,0,0,0,0,0,0⟩,.f ⟨28,3,1,0,0,0,0,0,0⟩]⟩,
⟨-5,2,1,22,[[.s 0 0,.s 0 0],[.f ⟨9,13,0,0,0,0,0,0,0⟩,.f ⟨9,13,1,0,1,0,0,0,0⟩],[.f ⟨26,1,0,0,0,0,0,0,0⟩,.f ⟨26,1,0,0,0,1,0,1,0⟩],[.s 2 0,.s 2 0]],[.s 0 2,.s 0 2]⟩,
⟨-5,2,2,23,[[.s 1 0,.s 1 0],[.f ⟨9,14,0,0,0,0,0,0,0⟩,.f ⟨9,14,1,0,1,0,0,0,0⟩],[.f ⟨26,2,0,0,0,0,0,0,0⟩,.f ⟨26,2,0,0,0,1,0,1,0⟩],[.s 4 0,.s 4 0]],[.s 1 3,.s 1 3]⟩,
⟨-5,2,3,32,[[.f ⟨26,168,0,0,0,0,0,1,0⟩,.f ⟨26,168,0,0,0,1,0,2,0⟩],[.f ⟨9,15,0,0,0,0,0,0,0⟩,.f ⟨9,15,1,0,1,0,0,0,0⟩],[.f ⟨26,3,0,0,0,0,0,0,0⟩,.f ⟨26,3,0,0,0,1,0,1,0⟩],[.s 5 0,.s 5 0]],[.s 5 0,.s 5 0]⟩,
⟨-5,2,4,24,[[.s 2 0,.s 2 0],[.f ⟨9,16,0,0,0,0,0,0,0⟩,.f ⟨9,16,1,0,1,0,0,0,0⟩],[.f ⟨26,4,0,0,0,0,0,0,0⟩,.f ⟨26,4,0,0,0,1,0,1,0⟩],[.f ⟨9,18,0,0,0,0,0,0,0⟩,.f ⟨9,18,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨-5,2,5,31,[[.s 3 0,.s 3 0],[.f ⟨9,17,0,0,0,0,0,0,0⟩,.f ⟨9,17,1,0,1,0,0,0,0⟩],[.f ⟨26,5,0,0,0,0,0,0,0⟩,.f ⟨26,5,0,0,0,1,0,1,0⟩],[.f ⟨9,19,0,0,0,0,0,0,0⟩,.f ⟨9,19,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.f ⟨9,19,0,0,0,0,0,0,1⟩,.f ⟨9,19,1,0,1,0,0,0,1⟩]⟩,
⟨-5,2,6,25,[[.s 4 0,.s 4 0],[.f ⟨26,4,0,0,0,0,0,0,0⟩,.f ⟨26,4,0,0,0,1,0,1,0⟩],[.f ⟨9,18,0,0,0,0,0,0,0⟩,.f ⟨9,18,1,0,1,0,0,0,0⟩],[.f ⟨26,6,0,0,0,0,0,0,0⟩,.f ⟨26,6,0,0,0,1,0,1,0⟩],[.s 8 0,.s 8 0],[.f ⟨26,8,0,0,0,0,0,0,0⟩,.f ⟨26,8,0,0,0,1,0,1,0⟩]],[.s 4 4,.s 4 4]⟩,
⟨-5,2,7,30,[[.s 5 0,.s 5 0],[.f ⟨26,5,0,0,0,0,0,0,0⟩,.f ⟨26,5,0,0,0,1,0,1,0⟩],[.f ⟨9,19,0,0,0,0,0,0,0⟩,.f ⟨9,19,1,0,1,0,0,0,0⟩],[.f ⟨26,7,0,0,0,0,0,0,0⟩,.f ⟨26,7,0,0,0,1,0,1,0⟩],[.s 9 0,.s 9 0],[.f ⟨26,9,0,0,0,0,0,0,0⟩,.f ⟨26,9,0,0,0,1,0,1,0⟩]],[.s 9 1,.s 9 1]⟩,
⟨-5,2,8,26,[[.f ⟨9,18,0,0,0,0,0,0,0⟩,.f ⟨9,18,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.f ⟨9,20,0,0,0,0,0,0,0⟩,.f ⟨9,20,1,0,1,0,0,0,0⟩],[.f ⟨26,8,0,0,0,0,0,0,0⟩,.f ⟨26,8,0,0,0,1,0,1,0⟩],[.f ⟨9,22,0,0,0,0,0,0,0⟩,.f ⟨9,22,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0]],[.f ⟨9,18,0,0,0,0,0,0,5⟩,.f ⟨9,18,1,0,1,0,0,0,5⟩]⟩,
⟨-5,2,9,29,[[.f ⟨9,19,0,0,0,0,0,0,0⟩,.f ⟨9,19,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨9,21,0,0,0,0,0,0,0⟩,.f ⟨9,21,1,0,1,0,0,0,0⟩],[.f ⟨26,9,0,0,0,0,0,0,0⟩,.f ⟨26,9,0,0,0,1,0,1,0⟩],[.f ⟨9,23,0,0,0,0,0,0,0⟩,.f ⟨9,23,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.f ⟨9,23,0,0,0,0,0,0,1⟩,.f ⟨9,23,1,0,1,0,0,0,1⟩]⟩,
⟨-5,2,10,27,[[.s 8 0,.s 8 0],[.f ⟨26,8,0,0,0,0,0,0,0⟩,.f ⟨26,8,0,0,0,1,0,1,0⟩],[.f ⟨9,22,0,0,0,0,0,0,0⟩,.f ⟨9,22,1,0,1,0,0,0,0⟩],[.f ⟨26,10,0,0,0,0,0,0,0⟩,.f ⟨26,10,0,0,0,1,0,1,0⟩],[.s 11 0,.s 11 0]],[.s 8 5,.s 8 5]⟩,
⟨-5,2,11,28,[[.s 9 0,.s 9 0],[.f ⟨26,9,0,0,0,0,0,0,0⟩,.f ⟨26,9,0,0,0,1,0,1,0⟩],[.s 10 0,.s 10 0],[.f ⟨9,23,0,0,0,0,0,0,0⟩,.f ⟨9,23,1,0,1,0,0,0,0⟩],[.f ⟨26,11,0,0,0,0,0,0,0⟩,.f ⟨26,11,0,0,0,1,0,1,0⟩]],[.s 10 4,.s 10 4]⟩,
⟨-2,1,0,9,[[.f ⟨8,0,0,0,0,0,0,0,0⟩,.f ⟨9,0,1,0,0,0,0,0,0⟩],[.f ⟨26,72,0,0,0,0,0,0,0⟩,.f ⟨26,72,0,0,0,1,0,1,0⟩],[.s 13 0,.s 13 0],[.f ⟨10,27,0,0,0,0,0,0,0⟩,.f ⟨28,27,1,0,0,0,0,0,0⟩]],[.f ⟨10,27,0,0,0,0,0,0,0⟩,.f ⟨28,27,1,0,0,0,0,0,0⟩]⟩,
⟨-2,1,1,10,[[.s 12 0,.s 12 0],[.f ⟨8,1,0,0,0,0,0,0,0⟩,.f ⟨9,1,1,0,0,0,0,0,0⟩],[.f ⟨26,73,0,0,0,0,0,0,0⟩,.f ⟨26,73,0,0,0,1,0,1,0⟩],[.s 14 0,.s 14 0]],[.s 12 2,.s 12 2]⟩,
⟨-2,1,2,11,[[.s 13 0,.s 13 0],[.f ⟨8,2,0,0,0,0,0,0,0⟩,.f ⟨9,2,1,0,0,0,0,0,0⟩],[.f ⟨26,74,0,0,0,0,0,0,0⟩,.f ⟨26,74,0,0,0,1,0,1,0⟩],[.s 16 0,.s 16 0]],[.s 13 3,.s 13 3]⟩,
⟨-2,1,3,20,[[.f ⟨26,48,0,0,0,0,0,0,0⟩,.f ⟨26,48,0,0,0,1,0,1,0⟩],[.f ⟨8,3,0,0,0,0,0,0,0⟩,.f ⟨9,3,1,0,0,0,0,0,0⟩],[.f ⟨26,75,0,0,0,0,0,0,0⟩,.f ⟨26,75,0,0,0,1,0,1,0⟩],[.s 17 0,.s 17 0]],[.s 17 0,.s 17 0]⟩,
⟨-2,1,4,12,[[.s 14 0,.s 14 0],[.f ⟨8,4,0,0,0,0,0,0,0⟩,.f ⟨9,4,1,0,0,0,0,0,0⟩],[.f ⟨26,76,0,0,0,0,0,0,0⟩,.f ⟨26,76,0,0,0,1,0,1,0⟩],[.f ⟨8,6,0,0,0,0,0,0,0⟩,.f ⟨9,6,1,0,0,0,0,0,0⟩],[.s 18 0,.s 18 0]],[.s 14 3,.s 14 3]⟩,
⟨-2,1,5,19,[[.s 15 0,.s 15 0],[.f ⟨8,5,0,0,0,0,0,0,0⟩,.f ⟨9,5,1,0,0,0,0,0,0⟩],[.f ⟨26,77,0,0,0,0,0,0,0⟩,.f ⟨26,77,0,0,0,1,0,1,0⟩],[.f ⟨8,7,0,0,0,0,0,0,0⟩,.f ⟨9,7,1,0,0,0,0,0,0⟩],[.s 19 0,.s 19 0]],[.f ⟨8,7,0,0,0,0,0,0,1⟩,.f ⟨9,7,1,0,0,0,0,0,1⟩]⟩,
⟨-2,1,6,13,[[.s 16 0,.s 16 0],[.f ⟨26,76,0,0,0,0,0,0,0⟩,.f ⟨26,76,0,0,0,1,0,1,0⟩],[.f ⟨8,6,0,0,0,0,0,0,0⟩,.f ⟨9,6,1,0,0,0,0,0,0⟩],[.f ⟨26,78,0,0,0,0,0,0,0⟩,.f ⟨26,78,0,0,0,1,0,1,0⟩],[.s 20 0,.s 20 0],[.f ⟨26,80,0,0,0,0,0,0,0⟩,.f ⟨26,80,0,0,0,1,0,1,0⟩]],[.s 16 4,.s 16 4]⟩,
⟨-2,1,7,18,[[.s 17 0,.s 17 0],[.f ⟨26,77,0,0,0,0,0,0,0⟩,.f ⟨26,77,0,0,0,1,0,1,0⟩],[.f ⟨8,7,0,0,0,0,0,0,0⟩,.f ⟨9,7,1,0,0,0,0,0,0⟩],[.f ⟨26,79,0,0,0,0,0,0,0⟩,.f ⟨26,79,0,0,0,1,0,1,0⟩],[.s 21 0,.s 21 0],[.f ⟨26,81,0,0,0,0,0,0,0⟩,.f ⟨26,81,0,0,0,1,0,1,0⟩]],[.s 21 1,.s 21 1]⟩,
⟨-2,1,8,14,[[.f ⟨8,6,0,0,0,0,0,0,0⟩,.f ⟨9,6,1,0,0,0,0,0,0⟩],[.s 18 0,.s 18 0],[.f ⟨8,8,0,0,0,0,0,0,0⟩,.f ⟨9,8,1,0,0,0,0,0,0⟩],[.f ⟨26,80,0,0,0,0,0,0,0⟩,.f ⟨26,80,0,0,0,1,0,1,0⟩],[.f ⟨8,10,0,0,0,0,0,0,0⟩,.f ⟨9,10,1,0,0,0,0,0,0⟩],[.s 22 0,.s 22 0]],[.f ⟨8,6,0,0,0,0,0,0,5⟩,.f ⟨9,6,1,0,0,0,0,0,5⟩]⟩,
⟨-2,1,9,17,[[.f ⟨8,7,0,0,0,0,0,0,0⟩,.f ⟨9,7,1,0,0,0,0,0,0⟩],[.s 19 0,.s 19 0],[.f ⟨8,9,0,0,0,0,0,0,0⟩,.f ⟨9,9,1,0,0,0,0,0,0⟩],[.f ⟨26,81,0,0,0,0,0,0,0⟩,.f ⟨26,81,0,0,0,1,0,1,0⟩],[.f ⟨8,11,0,0,0,0,0,0,0⟩,.f ⟨9,11,1,0,0,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.f ⟨8,11,0,0,0,0,0,0,1⟩,.f ⟨9,11,1,0,0,0,0,0,1⟩]⟩,
⟨-2,1,10,15,[[.s 20 0,.s 20 0],[.f ⟨26,80,0,0,0,0,0,0,0⟩,.f ⟨26,80,0,0,0,1,0,1,0⟩],[.f ⟨8,10,0,0,0,0,0,0,0⟩,.f ⟨9,10,1,0,0,0,0,0,0⟩],[.f ⟨26,82,0,0,0,0,0,0,0⟩,.f ⟨26,82,0,0,0,1,0,1,0⟩],[.s 23 0,.s 23 0]],[.s 20 5,.s 20 5]⟩,
⟨-2,1,11,16,[[.s 21 0,.s 21 0],[.f ⟨26,81,0,0,0,0,0,0,0⟩,.f ⟨26,81,0,0,0,1,0,1,0⟩],[.s 22 0,.s 22 0],[.f ⟨8,11,0,0,0,0,0,0,0⟩,.f ⟨9,11,1,0,0,0,0,0,0⟩],[.f ⟨26,83,0,0,0,0,0,0,0⟩,.f ⟨26,83,0,0,0,1,0,1,0⟩]],[.s 22 4,.s 22 4]⟩]⟩,
⟨2,6,2,-6,2,[(2,6,3),(-2,6,3)],2,6,3,24,-2,6,3,24,24,24,1,1,
[⟨-4,2,0,21,[[.f ⟨25,0,0,0,0,0,0,0,0⟩,.s 204 0,.f ⟨25,0,0,1,1,0,0,0,0⟩,.s 204 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨27,15,0,0,0,0,0,0,0⟩,.s 231 0,.f ⟨28,15,0,1,0,0,0,0,0⟩,.s 231 0]],[.f ⟨27,15,0,0,0,0,0,0,0⟩,.s 231 0,.f ⟨28,15,0,1,0,0,0,0,0⟩,.s 231 0]⟩,
⟨-4,2,1,22,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.f ⟨25,1,0,0,0,0,0,0,0⟩,.s 205 0,.f ⟨25,1,0,1,1,0,0,0,0⟩,.s 205 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 0 2,.s 0 2,.s 0 2,.s 0 2]⟩,
⟨-4,2,2,23,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨25,2,0,0,0,0,0,0,0⟩,.s 206 0,.f ⟨25,2,0,1,1,0,0,0,0⟩,.s 206 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 1 3,.s 1 3,.s 1 3,.s 1 3]⟩,
⟨-4,2,3,32,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.f ⟨25,3,0,0,0,0,0,0,0⟩,.s 207 0,.f ⟨25,3,0,1,1,0,0,0,0⟩,.s 207 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]⟩,
⟨-4,2,4,24,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.f ⟨25,4,0,0,0,0,0,0,0⟩,.s 208 0,.f ⟨25,4,0,1,1,0,0,0,0⟩,.s 208 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.f ⟨25,6,0,0,0,0,0,0,0⟩,.s 210 0,.f ⟨25,6,0,1,1,0,0,0,0⟩,.s 210 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 2 3,.s 2 3,.s 2 3,.s 2 3]⟩,
⟨-4,2,5,31,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.f ⟨25,5,0,0,0,0,0,0,0⟩,.s 209 0,.f ⟨25,5,0,1,1,0,0,0,0⟩,.s 209 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.f ⟨25,7,0,0,0,0,0,0,0⟩,.s 211 0,.f ⟨25,7,0,1,1,0,0,0,0⟩,.s 211 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.f ⟨25,7,0,0,0,0,0,0,1⟩,.s 211 1,.f ⟨25,7,0,1,1,0,0,0,1⟩,.s 211 1]⟩,
⟨-4,2,6,25,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.f ⟨25,6,0,0,0,0,0,0,0⟩,.s 210 0,.f ⟨25,6,0,1,1,0,0,0,0⟩,.s 210 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 4 4,.s 4 4,.s 4 4,.s 4 4]⟩,
⟨-4,2,7,30,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.f ⟨25,7,0,0,0,0,0,0,0⟩,.s 211 0,.f ⟨25,7,0,1,1,0,0,0,0⟩,.s 211 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.s 9 1,.s 9 1,.s 9 1,.s 9 1]⟩,
⟨-4,2,8,26,[[.f ⟨25,6,0,0,0,0,0,0,0⟩,.s 210 0,.f ⟨25,6,0,1,1,0,0,0,0⟩,.s 210 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.f ⟨25,8,0,0,0,0,0,0,0⟩,.s 212 0,.f ⟨25,8,0,1,1,0,0,0,0⟩,.s 212 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.f ⟨25,10,0,0,0,0,0,0,0⟩,.s 214 0,.f ⟨25,10,0,1,1,0,0,0,0⟩,.s 214 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.f ⟨25,6,0,0,0,0,0,0,5⟩,.s 210 5,.f ⟨25,6,0,1,1,0,0,0,5⟩,.s 210 5]⟩,
⟨-4,2,9,29,[[.f ⟨25,7,0,0,0,0,0,0,0⟩,.s 211 0,.f ⟨25,7,0,1,1,0,0,0,0⟩,.s 211 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.f ⟨25,9,0,0,0,0,0,0,0⟩,.s 213 0,.f ⟨25,9,0,1,1,0,0,0,0⟩,.s 213 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.f ⟨25,11,0,0,0,0,0,0,0⟩,.s 215 0,.f ⟨25,11,0,1,1,0,0,0,0⟩,.s 215 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.f ⟨25,11,0,0,0,0,0,0,1⟩,.s 215 1,.f ⟨25,11,0,1,1,0,0,0,1⟩,.s 215 1]⟩,
⟨-4,2,10,27,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.f ⟨25,10,0,0,0,0,0,0,0⟩,.s 214 0,.f ⟨25,10,0,1,1,0,0,0,0⟩,.s 214 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 8 5,.s 8 5,.s 8 5,.s 8 5]⟩,
⟨-4,2,11,28,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.f ⟨25,11,0,0,0,0,0,0,0⟩,.s 215 0,.f ⟨25,11,0,1,1,0,0,0,0⟩,.s 215 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 10 4,.s 10 4,.s 10 4,.s 10 4]⟩,
⟨-4,3,0,33,[[.s 168 0,.s 168 0,.s 168 0,.s 168 0],[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]],[.s 3 0,.s 3 0,.s 3 0,.s 3 0]⟩,
⟨-4,3,1,34,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 169 0,.s 169 0,.s 169 0,.s 169 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 12 2,.s 12 2,.s 12 2,.s 12 2]⟩,
⟨-4,3,2,35,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 170 0,.s 170 0,.s 170 0,.s 170 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 13 3,.s 13 3,.s 13 3,.s 13 3]⟩,
⟨-4,3,3,44,[[.s 216 0,.s 216 0,.s 216 0,.s 216 0],[.s 171 0,.s 171 0,.s 171 0,.s 171 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]⟩,
⟨-4,3,4,36,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 172 0,.s 172 0,.s 172 0,.s 172 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 174 0,.s 174 0,.s 174 0,.s 174 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0]],[.s 14 3,.s 14 3,.s 14 3,.s 14 3]⟩,
⟨-4,3,5,43,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 173 0,.s 173 0,.s 173 0,.s 173 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 175 0,.s 175 0,.s 175 0,.s 175 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0]],[.s 175 1,.s 175 1,.s 175 1,.s 175 1]⟩,
⟨-4,3,6,37,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 174 0,.s 174 0,.s 174 0,.s 174 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0]],[.s 16 4,.s 16 4,.s 16 4,.s 16 4]⟩,
⟨-4,3,7,42,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 175 0,.s 175 0,.s 175 0,.s 175 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0]],[.s 21 1,.s 21 1,.s 21 1,.s 21 1]⟩,
⟨-4,3,8,38,[[.s 174 0,.s 174 0,.s 174 0,.s 174 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 176 0,.s 176 0,.s 176 0,.s 176 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 178 0,.s 178 0,.s 178 0,.s 178 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.s 174 5,.s 174 5,.s 174 5,.s 174 5]⟩,
⟨-4,3,9,41,[[.s 175 0,.s 175 0,.s 175 0,.s 175 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 177 0,.s 177 0,.s 177 0,.s 177 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 179 0,.s 179 0,.s 179 0,.s 179 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 179 1,.s 179 1,.s 179 1,.s 179 1]⟩,
⟨-4,3,10,39,[[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 178 0,.s 178 0,.s 178 0,.s 178 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 20 5,.s 20 5,.s 20 5,.s 20 5]⟩,
⟨-4,3,11,40,[[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 179 0,.s 179 0,.s 179 0,.s 179 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 22 4,.s 22 4,.s 22 4,.s 22 4]⟩,
⟨-3,2,0,21,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.f ⟨8,3,0,0,0,0,0,0,0⟩,.s 255 0,.f ⟨9,3,0,1,0,0,0,0,0⟩,.s 255 0]],[.f ⟨8,3,0,0,0,0,0,0,0⟩,.s 255 0,.f ⟨9,3,0,1,0,0,0,0,0⟩,.s 255 0]⟩,
⟨-3,2,1,22,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.s 24 2,.s 24 2,.s 24 2,.s 24 2]⟩,
⟨-3,2,2,23,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.s 25 3,.s 25 3,.s 25 3,.s 25 3]⟩,
⟨-3,2,3,32,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0]],[.s 29 0,.s 29 0,.s 29 0,.s 29 0]⟩,
⟨-3,2,4,24,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0]],[.s 26 3,.s 26 3,.s 26 3,.s 26 3]⟩,
⟨-3,2,5,31,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 7 1,.s 7 1,.s 7 1,.s 7 1]⟩,
⟨-3,2,6,25,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0]],[.s 28 4,.s 28 4,.s 28 4,.s 28 4]⟩,
⟨-3,2,7,30,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0]],[.s 33 1,.s 33 1,.s 33 1,.s 33 1]⟩,
⟨-3,2,8,26,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.s 6 5,.s 6 5,.s 6 5,.s 6 5]⟩,
⟨-3,2,9,29,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 11 1,.s 11 1,.s 11 1,.s 11 1]⟩,
⟨-3,2,10,27,[[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 32 5,.s 32 5,.s 32 5,.s 32 5]⟩,
⟨-3,2,11,28,[[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 34 4,.s 34 4,.s 34 4,.s 34 4]⟩,
⟨-3,3,0,33,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0]],[.s 27 0,.s 27 0,.s 27 0,.s 27 0]⟩,
⟨-3,3,1,34,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.s 36 2,.s 36 2,.s 36 2,.s 36 2]⟩,
⟨-3,3,2,35,[[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0]],[.s 37 3,.s 37 3,.s 37 3,.s 37 3]⟩,
⟨-3,3,3,44,[[.s 240 0,.s 240 0,.s 240 0,.s 240 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0]],[.s 41 0,.s 41 0,.s 41 0,.s 41 0]⟩,
⟨-3,3,4,36,[[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.s 38 3,.s 38 3,.s 38 3,.s 38 3]⟩,
⟨-3,3,5,43,[[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 19 1,.s 19 1,.s 19 1,.s 19 1]⟩,
⟨-3,3,6,37,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0]],[.s 40 4,.s 40 4,.s 40 4,.s 40 4]⟩,
⟨-3,3,7,42,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0]],[.s 45 1,.s 45 1,.s 45 1,.s 45 1]⟩,
⟨-3,3,8,38,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0]],[.s 18 5,.s 18 5,.s 18 5,.s 18 5]⟩,
⟨-3,3,9,41,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 23 1,.s 23 1,.s 23 1,.s 23 1]⟩,
⟨-3,3,10,39,[[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 44 5,.s 44 5,.s 44 5,.s 44 5]⟩,
⟨-3,3,11,40,[[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 46 4,.s 46 4,.s 46 4,.s 46 4]⟩,
⟨-2,2,0,21,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.f ⟨25,15,0,0,0,0,0,0,0⟩,.s 279 0,.f ⟨25,15,0,1,1,0,0,0,0⟩,.s 279 0]],[.f ⟨25,15,0,0,0,0,0,0,0⟩,.s 279 0,.f ⟨25,15,0,1,1,0,0,0,0⟩,.s 279 0]⟩,
⟨-2,2,1,22,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0]],[.s 48 2,.s 48 2,.s 48 2,.s 48 2]⟩,
⟨-2,2,2,23,[[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0]],[.s 49 3,.s 49 3,.s 49 3,.s 49 3]⟩,
⟨-2,2,3,32,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]⟩,
⟨-2,2,4,24,[[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0]],[.s 50 3,.s 50 3,.s 50 3,.s 50 3]⟩,
⟨-2,2,5,31,[[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0]],[.s 31 1,.s 31 1,.s 31 1,.s 31 1]⟩,
⟨-2,2,6,25,[[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0]],[.s 52 4,.s 52 4,.s 52 4,.s 52 4]⟩,
⟨-2,2,7,30,[[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0]],[.s 57 1,.s 57 1,.s 57 1,.s 57 1]⟩,
⟨-2,2,8,26,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0]],[.s 30 5,.s 30 5,.s 30 5,.s 30 5]⟩,
⟨-2,2,9,29,[[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 35 1,.s 35 1,.s 35 1,.s 35 1]⟩,
⟨-2,2,10,27,[[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 56 5,.s 56 5,.s 56 5,.s 56 5]⟩,
⟨-2,2,11,28,[[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0]],[.s 58 4,.s 58 4,.s 58 4,.s 58 4]⟩,
⟨-2,3,0,33,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0]],[.s 51 0,.s 51 0,.s 51 0,.s 51 0]⟩,
⟨-2,3,1,34,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 97 0,.s 97 0,.s 97 0,.s 97 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0]],[.s 60 2,.s 60 2,.s 60 2,.s 60 2]⟩,
⟨-2,3,2,35,[[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 98 0,.s 98 0,.s 98 0,.s 98 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0]],[.s 61 3,.s 61 3,.s 61 3,.s 61 3]⟩,
⟨-2,3,3,44,[[.s 264 0,.s 264 0,.s 264 0,.s 264 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 99 0,.s 99 0,.s 99 0,.s 99 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0]],[.s 65 0,.s 65 0,.s 65 0,.s 65 0]⟩,
⟨-2,3,4,36,[[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 100 0,.s 100 0,.s 100 0,.s 100 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0]],[.s 62 3,.s 62 3,.s 62 3,.s 62 3]⟩,
⟨-2,3,5,43,[[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 101 0,.s 101 0,.s 101 0,.s 101 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0]],[.s 43 1,.s 43 1,.s 43 1,.s 43 1]⟩,
⟨-2,3,6,37,[[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 100 0,.s 100 0,.s 100 0,.s 100 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0]],[.s 64 4,.s 64 4,.s 64 4,.s 64 4]⟩,
⟨-2,3,7,42,[[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 101 0,.s 101 0,.s 101 0,.s 101 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0]],[.s 69 1,.s 69 1,.s 69 1,.s 69 1]⟩,
⟨-2,3,8,38,[[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0]],[.s 42 5,.s 42 5,.s 42 5,.s 42 5]⟩,
⟨-2,3,9,41,[[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 47 1,.s 47 1,.s 47 1,.s 47 1]⟩,
⟨-2,3,10,39,[[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 68 5,.s 68 5,.s 68 5,.s 68 5]⟩,
⟨-2,3,11,40,[[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0]],[.s 70 4,.s 70 4,.s 70 4,.s 70 4]⟩,
⟨-1,1,0,9,[[.f ⟨25,12,0,0,0,0,0,0,0⟩,.s 276 0,.f ⟨25,12,0,1,1,0,0,0,0⟩,.s 276 0],[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.f ⟨10,39,0,0,0,0,0,0,0⟩,.f ⟨24,15,1,0,0,0,0,0,0⟩,.f ⟨28,39,0,1,0,0,0,0,0⟩,.s 111 0]],[.f ⟨10,39,0,0,0,0,0,0,0⟩,.f ⟨24,15,1,0,0,0,0,0,0⟩,.f ⟨28,39,0,1,0,0,0,0,0⟩,.s 111 0]⟩,
⟨-1,1,1,10,[[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.f ⟨25,13,0,0,0,0,0,0,0⟩,.s 277 0,.f ⟨25,13,0,1,1,0,0,0,0⟩,.s 277 0],[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0]],[.s 72 2,.s 72 2,.s 72 2,.s 72 2]⟩,
⟨-1,1,2,11,[[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.f ⟨25,14,0,0,0,0,0,0,0⟩,.s 278 0,.f ⟨25,14,0,1,1,0,0,0,0⟩,.s 278 0],[.s 122 0,.s 122 0,.s 122 0,.s 122 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0]],[.s 73 3,.s 73 3,.s 73 3,.s 73 3]⟩,
⟨-1,1,3,20,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.f ⟨25,15,0,0,0,0,0,0,0⟩,.s 279 0,.f ⟨25,15,0,1,1,0,0,0,0⟩,.s 279 0],[.s 123 0,.s 123 0,.s 123 0,.s 123 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0]],[.s 77 0,.s 77 0,.s 77 0,.s 77 0]⟩,
⟨-1,1,4,12,[[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.f ⟨25,16,0,0,0,0,0,0,0⟩,.s 280 0,.f ⟨25,16,0,1,1,0,0,0,0⟩,.s 280 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.f ⟨25,18,0,0,0,0,0,0,0⟩,.s 282 0,.f ⟨25,18,0,1,1,0,0,0,0⟩,.s 282 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0]],[.s 74 3,.s 74 3,.s 74 3,.s 74 3]⟩,
⟨-1,1,5,19,[[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.f ⟨25,17,0,0,0,0,0,0,0⟩,.s 281 0,.f ⟨25,17,0,1,1,0,0,0,0⟩,.s 281 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.f ⟨25,19,0,0,0,0,0,0,0⟩,.s 283 0,.f ⟨25,19,0,1,1,0,0,0,0⟩,.s 283 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0]],[.f ⟨25,19,0,0,0,0,0,0,1⟩,.s 283 1,.f ⟨25,19,0,1,1,0,0,0,1⟩,.s 283 1]⟩,
⟨-1,1,6,13,[[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.f ⟨25,18,0,0,0,0,0,0,0⟩,.s 282 0,.f ⟨25,18,0,1,1,0,0,0,0⟩,.s 282 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0]],[.s 76 4,.s 76 4,.s 76 4,.s 76 4]⟩,
⟨-1,1,7,18,[[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.f ⟨25,19,0,0,0,0,0,0,0⟩,.s 283 0,.f ⟨25,19,0,1,1,0,0,0,0⟩,.s 283 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0]],[.s 81 1,.s 81 1,.s 81 1,.s 81 1]⟩,
⟨-1,1,8,14,[[.f ⟨25,18,0,0,0,0,0,0,0⟩,.s 282 0,.f ⟨25,18,0,1,1,0,0,0,0⟩,.s 282 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.f ⟨25,20,0,0,0,0,0,0,0⟩,.s 284 0,.f ⟨25,20,0,1,1,0,0,0,0⟩,.s 284 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.f ⟨25,22,0,0,0,0,0,0,0⟩,.s 286 0,.f ⟨25,22,0,1,1,0,0,0,0⟩,.s 286 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0]],[.f ⟨25,18,0,0,0,0,0,0,5⟩,.s 282 5,.f ⟨25,18,0,1,1,0,0,0,5⟩,.s 282 5]⟩,
⟨-1,1,9,17,[[.f ⟨25,19,0,0,0,0,0,0,0⟩,.s 283 0,.f ⟨25,19,0,1,1,0,0,0,0⟩,.s 283 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.f ⟨25,21,0,0,0,0,0,0,0⟩,.s 285 0,.f ⟨25,21,0,1,1,0,0,0,0⟩,.s 285 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.f ⟨25,23,0,0,0,0,0,0,0⟩,.s 287 0,.f ⟨25,23,0,1,1,0,0,0,0⟩,.s 287 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0]],[.f ⟨25,23,0,0,0,0,0,0,1⟩,.s 287 1,.f ⟨25,23,0,1,1,0,0,0,1⟩,.s 287 1]⟩,
⟨-1,1,10,15,[[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.f ⟨25,22,0,0,0,0,0,0,0⟩,.s 286 0,.f ⟨25,22,0,1,1,0,0,0,0⟩,.s 286 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0]],[.s 80 5,.s 80 5,.s 80 5,.s 80 5]⟩,
⟨-1,1,11,16,[[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.f ⟨25,23,0,0,0,0,0,0,0⟩,.s 287 0,.f ⟨25,23,0,1,1,0,0,0,0⟩,.s 287 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0]],[.s 82 4,.s 82 4,.s 82 4,.s 82 4]⟩,
⟨-1,2,0,21,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 132 0,.s 132 0,.s 132 0,.s 132 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0]],[.s 75 0,.s 75 0,.s 75 0,.s 75 0]⟩,
⟨-1,2,1,22,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0]],[.s 84 2,.s 84 2,.s 84 2,.s 84 2]⟩,
⟨-1,2,2,23,[[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 134 0,.s 134 0,.s 134 0,.s 134 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0]],[.s 85 3,.s 85 3,.s 85 3,.s 85 3]⟩,
⟨-1,2,3,32,[[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0]],[.s 89 0,.s 89 0,.s 89 0,.s 89 0]⟩,
⟨-1,2,4,24,[[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0]],[.s 86 3,.s 86 3,.s 86 3,.s 86 3]⟩,
⟨-1,2,5,31,[[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0]],[.s 55 1,.s 55 1,.s 55 1,.s 55 1]⟩,
⟨-1,2,6,25,[[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0]],[.s 88 4,.s 88 4,.s 88 4,.s 88 4]⟩,
⟨-1,2,7,30,[[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0]],[.s 93 1,.s 93 1,.s 93 1,.s 93 1]⟩,
⟨-1,2,8,26,[[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0]],[.s 54 5,.s 54 5,.s 54 5,.s 54 5]⟩,
⟨-1,2,9,29,[[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0]],[.s 59 1,.s 59 1,.s 59 1,.s 59 1]⟩,
⟨-1,2,10,27,[[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0]],[.s 92 5,.s 92 5,.s 92 5,.s 92 5]⟩,
⟨-1,2,11,28,[[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0]],[.s 94 4,.s 94 4,.s 94 4,.s 94 4]⟩,
⟨-1,3,0,33,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 144 0,.s 144 0,.s 144 0,.s 144 0],[.s 97 0,.s 97 0,.s 97 0,.s 97 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0]],[.s 87 0,.s 87 0,.s 87 0,.s 87 0]⟩,
⟨-1,3,1,34,[[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 145 0,.s 145 0,.s 145 0,.s 145 0],[.s 98 0,.s 98 0,.s 98 0,.s 98 0]],[.s 96 2,.s 96 2,.s 96 2,.s 96 2]⟩,
⟨-1,3,2,35,[[.s 97 0,.s 97 0,.s 97 0,.s 97 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 146 0,.s 146 0,.s 146 0,.s 146 0],[.s 100 0,.s 100 0,.s 100 0,.s 100 0]],[.s 97 3,.s 97 3,.s 97 3,.s 97 3]⟩,
⟨-1,3,3,44,[[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 147 0,.s 147 0,.s 147 0,.s 147 0],[.s 101 0,.s 101 0,.s 101 0,.s 101 0]],[.s 101 0,.s 101 0,.s 101 0,.s 101 0]⟩,
⟨-1,3,4,36,[[.s 98 0,.s 98 0,.s 98 0,.s 98 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 148 0,.s 148 0,.s 148 0,.s 148 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0]],[.s 98 3,.s 98 3,.s 98 3,.s 98 3]⟩,
⟨-1,3,5,43,[[.s 99 0,.s 99 0,.s 99 0,.s 99 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 149 0,.s 149 0,.s 149 0,.s 149 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0]],[.s 67 1,.s 67 1,.s 67 1,.s 67 1]⟩,
⟨-1,3,6,37,[[.s 100 0,.s 100 0,.s 100 0,.s 100 0],[.s 148 0,.s 148 0,.s 148 0,.s 148 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0]],[.s 100 4,.s 100 4,.s 100 4,.s 100 4]⟩,
⟨-1,3,7,42,[[.s 101 0,.s 101 0,.s 101 0,.s 101 0],[.s 149 0,.s 149 0,.s 149 0,.s 149 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0]],[.s 105 1,.s 105 1,.s 105 1,.s 105 1]⟩,
⟨-1,3,8,38,[[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0]],[.s 66 5,.s 66 5,.s 66 5,.s 66 5]⟩,
⟨-1,3,9,41,[[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0]],[.s 71 1,.s 71 1,.s 71 1,.s 71 1]⟩,
⟨-1,3,10,39,[[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 154 0,.s 154 0,.s 154 0,.s 154 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0]],[.s 104 5,.s 104 5,.s 104 5,.s 104 5]⟩,
⟨-1,3,11,40,[[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 155 0,.s 155 0,.s 155 0,.s 155 0]],[.s 106 4,.s 106 4,.s 106 4,.s 106 4]⟩,
⟨-1,4,0,45,[[.s 264 0,.s 264 0,.s 264 0,.s 264 0],[.s 156 0,.s 156 0,.s 156 0,.s 156 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 99 0,.s 99 0,.s 99 0,.s 99 0]],[.s 99 0,.s 99 0,.s 99 0,.s 99 0]⟩,
⟨-1,4,1,46,[[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 265 0,.s 265 0,.s 265 0,.s 265 0],[.s 157 0,.s 157 0,.s 157 0,.s 157 0],[.s 110 0,.s 110 0,.s 110 0,.s 110 0]],[.s 108 2,.s 108 2,.s 108 2,.s 108 2]⟩,
⟨-1,4,2,47,[[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 266 0,.s 266 0,.s 266 0,.s 266 0],[.s 158 0,.s 158 0,.s 158 0,.s 158 0],[.s 112 0,.s 112 0,.s 112 0,.s 112 0]],[.s 109 3,.s 109 3,.s 109 3,.s 109 3]⟩,
⟨-1,4,3,56,[[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 267 0,.s 267 0,.s 267 0,.s 267 0],[.s 159 0,.s 159 0,.s 159 0,.s 159 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0]],[.s 113 0,.s 113 0,.s 113 0,.s 113 0]⟩,
⟨-1,4,4,48,[[.s 110 0,.s 110 0,.s 110 0,.s 110 0],[.s 268 0,.s 268 0,.s 268 0,.s 268 0],[.s 160 0,.s 160 0,.s 160 0,.s 160 0],[.s 270 0,.s 270 0,.s 270 0,.s 270 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0]],[.s 110 3,.s 110 3,.s 110 3,.s 110 3]⟩,
⟨-1,4,5,55,[[.s 111 0,.s 111 0,.s 111 0,.s 111 0],[.s 269 0,.s 269 0,.s 269 0,.s 269 0],[.s 161 0,.s 161 0,.s 161 0,.s 161 0],[.s 271 0,.s 271 0,.s 271 0,.s 271 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0]],[.s 271 1,.s 271 1,.s 271 1,.s 271 1]⟩,
⟨-1,4,6,49,[[.s 112 0,.s 112 0,.s 112 0,.s 112 0],[.s 160 0,.s 160 0,.s 160 0,.s 160 0],[.s 270 0,.s 270 0,.s 270 0,.s 270 0],[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0]],[.s 112 4,.s 112 4,.s 112 4,.s 112 4]⟩,
⟨-1,4,7,54,[[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 161 0,.s 161 0,.s 161 0,.s 161 0],[.s 271 0,.s 271 0,.s 271 0,.s 271 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 165 0,.s 165 0,.s 165 0,.s 165 0]],[.s 117 1,.s 117 1,.s 117 1,.s 117 1]⟩,
⟨-1,4,8,50,[[.s 270 0,.s 270 0,.s 270 0,.s 270 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 272 0,.s 272 0,.s 272 0,.s 272 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0],[.s 274 0,.s 274 0,.s 274 0,.s 274 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0]],[.s 270 5,.s 270 5,.s 270 5,.s 270 5]⟩,
⟨-1,4,9,53,[[.s 271 0,.s 271 0,.s 271 0,.s 271 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 273 0,.s 273 0,.s 273 0,.s 273 0],[.s 165 0,.s 165 0,.s 165 0,.s 165 0],[.s 275 0,.s 275 0,.s 275 0,.s 275 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0]],[.s 275 1,.s 275 1,.s 275 1,.s 275 1]⟩,
⟨-1,4,10,51,[[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0],[.s 274 0,.s 274 0,.s 274 0,.s 274 0],[.s 166 0,.s 166 0,.s 166 0,.s 166 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0]],[.s 116 5,.s 116 5,.s 116 5,.s 116 5]⟩,
⟨-1,4,11,52,[[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 165 0,.s 165 0,.s 165 0,.s 165 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 275 0,.s 275 0,.s 275 0,.s 275 0],[.s 167 0,.s 167 0,.s 167 0,.s 167 0]],[.s 118 4,.s 118 4,.s 118 4,.s 118 4]⟩,
⟨0,1,0,9,[[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 168 0,.s 168 0,.s 168 0,.s 168 0],[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.f ⟨0,3,0,0,0,0,0,0,0⟩,.f ⟨7,3,1,0,0,0,0,0,0⟩,.f ⟨9,15,0,1,0,0,0,0,0⟩,.s 159 0]],[.f ⟨0,3,0,0,0,0,0,0,0⟩,.f ⟨7,3,1,0,0,0,0,0,0⟩,.f ⟨9,15,0,1,0,0,0,0,0⟩,.s 159 0]⟩,
⟨0,1,1,10,[[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 169 0,.s 169 0,.s 169 0,.s 169 0],[.s 122 0,.s 122 0,.s 122 0,.s 122 0]],[.s 120 2,.s 120 2,.s 120 2,.s 120 2]⟩,
⟨0,1,2,11,[[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 170 0,.s 170 0,.s 170 0,.s 170 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0]],[.s 121 3,.s 121 3,.s 121 3,.s 121 3]⟩,
⟨0,1,3,20,[[.s 132 0,.s 132 0,.s 132 0,.s 132 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.s 171 0,.s 171 0,.s 171 0,.s 171 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0]],[.s 125 0,.s 125 0,.s 125 0,.s 125 0]⟩,
⟨0,1,4,12,[[.s 122 0,.s 122 0,.s 122 0,.s 122 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 172 0,.s 172 0,.s 172 0,.s 172 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0]],[.s 122 3,.s 122 3,.s 122 3,.s 122 3]⟩,
⟨0,1,5,19,[[.s 123 0,.s 123 0,.s 123 0,.s 123 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 173 0,.s 173 0,.s 173 0,.s 173 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0]],[.s 79 1,.s 79 1,.s 79 1,.s 79 1]⟩,
⟨0,1,6,13,[[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.s 172 0,.s 172 0,.s 172 0,.s 172 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 174 0,.s 174 0,.s 174 0,.s 174 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 176 0,.s 176 0,.s 176 0,.s 176 0]],[.s 124 4,.s 124 4,.s 124 4,.s 124 4]⟩,
⟨0,1,7,18,[[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.s 173 0,.s 173 0,.s 173 0,.s 173 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 175 0,.s 175 0,.s 175 0,.s 175 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 177 0,.s 177 0,.s 177 0,.s 177 0]],[.s 129 1,.s 129 1,.s 129 1,.s 129 1]⟩,
⟨0,1,8,14,[[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 176 0,.s 176 0,.s 176 0,.s 176 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0]],[.s 78 5,.s 78 5,.s 78 5,.s 78 5]⟩,
⟨0,1,9,17,[[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 177 0,.s 177 0,.s 177 0,.s 177 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0]],[.s 83 1,.s 83 1,.s 83 1,.s 83 1]⟩,
⟨0,1,10,15,[[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.s 176 0,.s 176 0,.s 176 0,.s 176 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 178 0,.s 178 0,.s 178 0,.s 178 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0]],[.s 128 5,.s 128 5,.s 128 5,.s 128 5]⟩,
⟨0,1,11,16,[[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.s 177 0,.s 177 0,.s 177 0,.s 177 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0],[.s 179 0,.s 179 0,.s 179 0,.s 179 0]],[.s 130 4,.s 130 4,.s 130 4,.s 130 4]⟩,
⟨0,2,0,21,[[.s 84 0,.s 84 0,.s 84 0,.s 84 0],[.s 180 0,.s 180 0,.s 180 0,.s 180 0],[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 123 0,.s 123 0,.s 123 0,.s 123 0]],[.s 123 0,.s 123 0,.s 123 0,.s 123 0]⟩,
⟨0,2,1,22,[[.s 132 0,.s 132 0,.s 132 0,.s 132 0],[.s 85 0,.s 85 0,.s 85 0,.s 85 0],[.s 181 0,.s 181 0,.s 181 0,.s 181 0],[.s 134 0,.s 134 0,.s 134 0,.s 134 0]],[.s 132 2,.s 132 2,.s 132 2,.s 132 2]⟩,
⟨0,2,2,23,[[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 86 0,.s 86 0,.s 86 0,.s 86 0],[.s 182 0,.s 182 0,.s 182 0,.s 182 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0]],[.s 133 3,.s 133 3,.s 133 3,.s 133 3]⟩,
⟨0,2,3,32,[[.s 144 0,.s 144 0,.s 144 0,.s 144 0],[.s 87 0,.s 87 0,.s 87 0,.s 87 0],[.s 183 0,.s 183 0,.s 183 0,.s 183 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0]],[.s 137 0,.s 137 0,.s 137 0,.s 137 0]⟩,
⟨0,2,4,24,[[.s 134 0,.s 134 0,.s 134 0,.s 134 0],[.s 88 0,.s 88 0,.s 88 0,.s 88 0],[.s 184 0,.s 184 0,.s 184 0,.s 184 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0]],[.s 134 3,.s 134 3,.s 134 3,.s 134 3]⟩,
⟨0,2,5,31,[[.s 135 0,.s 135 0,.s 135 0,.s 135 0],[.s 89 0,.s 89 0,.s 89 0,.s 89 0],[.s 185 0,.s 185 0,.s 185 0,.s 185 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0]],[.s 91 1,.s 91 1,.s 91 1,.s 91 1]⟩,
⟨0,2,6,25,[[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 184 0,.s 184 0,.s 184 0,.s 184 0],[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 186 0,.s 186 0,.s 186 0,.s 186 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 188 0,.s 188 0,.s 188 0,.s 188 0]],[.s 136 4,.s 136 4,.s 136 4,.s 136 4]⟩,
⟨0,2,7,30,[[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.s 185 0,.s 185 0,.s 185 0,.s 185 0],[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 187 0,.s 187 0,.s 187 0,.s 187 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 189 0,.s 189 0,.s 189 0,.s 189 0]],[.s 141 1,.s 141 1,.s 141 1,.s 141 1]⟩,
⟨0,2,8,26,[[.s 90 0,.s 90 0,.s 90 0,.s 90 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 92 0,.s 92 0,.s 92 0,.s 92 0],[.s 188 0,.s 188 0,.s 188 0,.s 188 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0]],[.s 90 5,.s 90 5,.s 90 5,.s 90 5]⟩,
⟨0,2,9,29,[[.s 91 0,.s 91 0,.s 91 0,.s 91 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 93 0,.s 93 0,.s 93 0,.s 93 0],[.s 189 0,.s 189 0,.s 189 0,.s 189 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0]],[.s 95 1,.s 95 1,.s 95 1,.s 95 1]⟩,
⟨0,2,10,27,[[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 188 0,.s 188 0,.s 188 0,.s 188 0],[.s 94 0,.s 94 0,.s 94 0,.s 94 0],[.s 190 0,.s 190 0,.s 190 0,.s 190 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0]],[.s 140 5,.s 140 5,.s 140 5,.s 140 5]⟩,
⟨0,2,11,28,[[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 189 0,.s 189 0,.s 189 0,.s 189 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 95 0,.s 95 0,.s 95 0,.s 95 0],[.s 191 0,.s 191 0,.s 191 0,.s 191 0]],[.s 142 4,.s 142 4,.s 142 4,.s 142 4]⟩,
⟨0,3,0,33,[[.s 96 0,.s 96 0,.s 96 0,.s 96 0],[.s 192 0,.s 192 0,.s 192 0,.s 192 0],[.s 145 0,.s 145 0,.s 145 0,.s 145 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0]],[.s 135 0,.s 135 0,.s 135 0,.s 135 0]⟩,
⟨0,3,1,34,[[.s 144 0,.s 144 0,.s 144 0,.s 144 0],[.s 97 0,.s 97 0,.s 97 0,.s 97 0],[.s 193 0,.s 193 0,.s 193 0,.s 193 0],[.s 146 0,.s 146 0,.s 146 0,.s 146 0]],[.s 144 2,.s 144 2,.s 144 2,.s 144 2]⟩,
⟨0,3,2,35,[[.s 145 0,.s 145 0,.s 145 0,.s 145 0],[.s 98 0,.s 98 0,.s 98 0,.s 98 0],[.s 194 0,.s 194 0,.s 194 0,.s 194 0],[.s 148 0,.s 148 0,.s 148 0,.s 148 0]],[.s 145 3,.s 145 3,.s 145 3,.s 145 3]⟩,
⟨0,3,3,44,[[.s 156 0,.s 156 0,.s 156 0,.s 156 0],[.s 99 0,.s 99 0,.s 99 0,.s 99 0],[.s 195 0,.s 195 0,.s 195 0,.s 195 0],[.s 149 0,.s 149 0,.s 149 0,.s 149 0]],[.s 149 0,.s 149 0,.s 149 0,.s 149 0]⟩,
⟨0,3,4,36,[[.s 146 0,.s 146 0,.s 146 0,.s 146 0],[.s 100 0,.s 100 0,.s 100 0,.s 100 0],[.s 196 0,.s 196 0,.s 196 0,.s 196 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 150 0,.s 150 0,.s 150 0,.s 150 0]],[.s 146 3,.s 146 3,.s 146 3,.s 146 3]⟩,
⟨0,3,5,43,[[.s 147 0,.s 147 0,.s 147 0,.s 147 0],[.s 101 0,.s 101 0,.s 101 0,.s 101 0],[.s 197 0,.s 197 0,.s 197 0,.s 197 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 151 0,.s 151 0,.s 151 0,.s 151 0]],[.s 103 1,.s 103 1,.s 103 1,.s 103 1]⟩,
⟨0,3,6,37,[[.s 148 0,.s 148 0,.s 148 0,.s 148 0],[.s 196 0,.s 196 0,.s 196 0,.s 196 0],[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 198 0,.s 198 0,.s 198 0,.s 198 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0],[.s 200 0,.s 200 0,.s 200 0,.s 200 0]],[.s 148 4,.s 148 4,.s 148 4,.s 148 4]⟩,
⟨0,3,7,42,[[.s 149 0,.s 149 0,.s 149 0,.s 149 0],[.s 197 0,.s 197 0,.s 197 0,.s 197 0],[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 199 0,.s 199 0,.s 199 0,.s 199 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0],[.s 201 0,.s 201 0,.s 201 0,.s 201 0]],[.s 153 1,.s 153 1,.s 153 1,.s 153 1]⟩,
⟨0,3,8,38,[[.s 102 0,.s 102 0,.s 102 0,.s 102 0],[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.s 104 0,.s 104 0,.s 104 0,.s 104 0],[.s 200 0,.s 200 0,.s 200 0,.s 200 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 154 0,.s 154 0,.s 154 0,.s 154 0]],[.s 102 5,.s 102 5,.s 102 5,.s 102 5]⟩,
⟨0,3,9,41,[[.s 103 0,.s 103 0,.s 103 0,.s 103 0],[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.s 105 0,.s 105 0,.s 105 0,.s 105 0],[.s 201 0,.s 201 0,.s 201 0,.s 201 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0],[.s 155 0,.s 155 0,.s 155 0,.s 155 0]],[.s 107 1,.s 107 1,.s 107 1,.s 107 1]⟩,
⟨0,3,10,39,[[.s 152 0,.s 152 0,.s 152 0,.s 152 0],[.s 200 0,.s 200 0,.s 200 0,.s 200 0],[.s 106 0,.s 106 0,.s 106 0,.s 106 0],[.s 202 0,.s 202 0,.s 202 0,.s 202 0],[.s 155 0,.s 155 0,.s 155 0,.s 155 0]],[.s 152 5,.s 152 5,.s 152 5,.s 152 5]⟩,
⟨0,3,11,40,[[.s 153 0,.s 153 0,.s 153 0,.s 153 0],[.s 201 0,.s 201 0,.s 201 0,.s 201 0],[.s 154 0,.s 154 0,.s 154 0,.s 154 0],[.s 107 0,.s 107 0,.s 107 0,.s 107 0],[.s 203 0,.s 203 0,.s 203 0,.s 203 0]],[.s 154 4,.s 154 4,.s 154 4,.s 154 4]⟩,
⟨0,4,0,45,[[.s 108 0,.s 108 0,.s 108 0,.s 108 0],[.s 204 0,.s 204 0,.s 204 0,.s 204 0],[.s 157 0,.s 157 0,.s 157 0,.s 157 0],[.s 147 0,.s 147 0,.s 147 0,.s 147 0]],[.s 147 0,.s 147 0,.s 147 0,.s 147 0]⟩,
⟨0,4,1,46,[[.s 156 0,.s 156 0,.s 156 0,.s 156 0],[.s 109 0,.s 109 0,.s 109 0,.s 109 0],[.s 205 0,.s 205 0,.s 205 0,.s 205 0],[.s 158 0,.s 158 0,.s 158 0,.s 158 0]],[.s 156 2,.s 156 2,.s 156 2,.s 156 2]⟩,
⟨0,4,2,47,[[.s 157 0,.s 157 0,.s 157 0,.s 157 0],[.s 110 0,.s 110 0,.s 110 0,.s 110 0],[.s 206 0,.s 206 0,.s 206 0,.s 206 0],[.s 160 0,.s 160 0,.s 160 0,.s 160 0]],[.s 157 3,.s 157 3,.s 157 3,.s 157 3]⟩,
⟨0,4,3,56,[[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.s 111 0,.s 111 0,.s 111 0,.s 111 0],[.s 207 0,.s 207 0,.s 207 0,.s 207 0],[.s 161 0,.s 161 0,.s 161 0,.s 161 0]],[.s 161 0,.s 161 0,.s 161 0,.s 161 0]⟩,
⟨0,4,4,48,[[.s 158 0,.s 158 0,.s 158 0,.s 158 0],[.s 112 0,.s 112 0,.s 112 0,.s 112 0],[.s 208 0,.s 208 0,.s 208 0,.s 208 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 162 0,.s 162 0,.s 162 0,.s 162 0]],[.s 158 3,.s 158 3,.s 158 3,.s 158 3]⟩,
⟨0,4,5,55,[[.s 159 0,.s 159 0,.s 159 0,.s 159 0],[.s 113 0,.s 113 0,.s 113 0,.s 113 0],[.s 209 0,.s 209 0,.s 209 0,.s 209 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0]],[.s 115 1,.s 115 1,.s 115 1,.s 115 1]⟩,
⟨0,4,6,49,[[.s 160 0,.s 160 0,.s 160 0,.s 160 0],[.s 208 0,.s 208 0,.s 208 0,.s 208 0],[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 210 0,.s 210 0,.s 210 0,.s 210 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0],[.s 212 0,.s 212 0,.s 212 0,.s 212 0]],[.s 160 4,.s 160 4,.s 160 4,.s 160 4]⟩,
⟨0,4,7,54,[[.s 161 0,.s 161 0,.s 161 0,.s 161 0],[.s 209 0,.s 209 0,.s 209 0,.s 209 0],[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 211 0,.s 211 0,.s 211 0,.s 211 0],[.s 165 0,.s 165 0,.s 165 0,.s 165 0],[.s 213 0,.s 213 0,.s 213 0,.s 213 0]],[.s 165 1,.s 165 1,.s 165 1,.s 165 1]⟩,
⟨0,4,8,50,[[.s 114 0,.s 114 0,.s 114 0,.s 114 0],[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 116 0,.s 116 0,.s 116 0,.s 116 0],[.s 212 0,.s 212 0,.s 212 0,.s 212 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 166 0,.s 166 0,.s 166 0,.s 166 0]],[.s 114 5,.s 114 5,.s 114 5,.s 114 5]⟩,
⟨0,4,9,53,[[.s 115 0,.s 115 0,.s 115 0,.s 115 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0],[.s 117 0,.s 117 0,.s 117 0,.s 117 0],[.s 213 0,.s 213 0,.s 213 0,.s 213 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0],[.s 167 0,.s 167 0,.s 167 0,.s 167 0]],[.s 119 1,.s 119 1,.s 119 1,.s 119 1]⟩,
⟨0,4,10,51,[[.s 164 0,.s 164 0,.s 164 0,.s 164 0],[.s 212 0,.s 212 0,.s 212 0,.s 212 0],[.s 118 0,.s 118 0,.s 118 0,.s 118 0],[.s 214 0,.s 214 0,.s 214 0,.s 214 0],[.s 167 0,.s 167 0,.s 167 0,.s 167 0]],[.s 164 5,.s 164 5,.s 164 5,.s 164 5]⟩,
⟨0,4,11,52,[[.s 165 0,.s 165 0,.s 165 0,.s 165 0],[.s 213 0,.s 213 0,.s 213 0,.s 213 0],[.s 166 0,.s 166 0,.s 166 0,.s 166 0],[.s 119 0,.s 119 0,.s 119 0,.s 119 0],[.s 215 0,.s 215 0,.s 215 0,.s 215 0]],[.s 166 4,.s 166 4,.s 166 4,.s 166 4]⟩,
⟨1,1,0,9,[[.s 120 0,.s 120 0,.s 120 0,.s 120 0],[.f ⟨24,0,0,0,0,0,0,0,0⟩,.f ⟨24,0,1,0,1,0,0,0,0⟩,.s 12 0,.s 12 0],[.s 169 0,.s 169 0,.s 169 0,.s 169 0],[.f ⟨4,3,0,0,0,0,0,0,0⟩,.f ⟨22,3,1,0,0,0,0,0,0⟩,.f ⟨25,3,0,1,0,0,0,0,0⟩,.s 207 0]],[.f ⟨4,3,0,0,0,0,0,0,0⟩,.f ⟨22,3,1,0,0,0,0,0,0⟩,.f ⟨25,3,0,1,0,0,0,0,0⟩,.s 207 0]⟩,
⟨1,1,1,10,[[.s 168 0,.s 168 0,.s 168 0,.s 168 0],[.s 121 0,.s 121 0,.s 121 0,.s 121 0],[.f ⟨24,1,0,0,0,0,0,0,0⟩,.f ⟨24,1,1,0,1,0,0,0,0⟩,.s 13 0,.s 13 0],[.s 170 0,.s 170 0,.s 170 0,.s 170 0]],[.s 168 2,.s 168 2,.s 168 2,.s 168 2]⟩,
⟨1,1,2,11,[[.s 169 0,.s 169 0,.s 169 0,.s 169 0],[.s 122 0,.s 122 0,.s 122 0,.s 122 0],[.f ⟨24,2,0,0,0,0,0,0,0⟩,.f ⟨24,2,1,0,1,0,0,0,0⟩,.s 14 0,.s 14 0],[.s 172 0,.s 172 0,.s 172 0,.s 172 0]],[.s 169 3,.s 169 3,.s 169 3,.s 169 3]⟩,
⟨1,1,3,20,[[.s 180 0,.s 180 0,.s 180 0,.s 180 0],[.s 123 0,.s 123 0,.s 123 0,.s 123 0],[.f ⟨24,3,0,0,0,0,0,0,0⟩,.f ⟨24,3,1,0,1,0,0,0,0⟩,.s 15 0,.s 15 0],[.s 173 0,.s 173 0,.s 173 0,.s 173 0]],[.s 173 0,.s 173 0,.s 173 0,.s 173 0]⟩,
⟨1,1,4,12,[[.s 170 0,.s 170 0,.s 170 0,.s 170 0],[.s 124 0,.s 124 0,.s 124 0,.s 124 0],[.f ⟨24,4,0,0,0,0,0,0,0⟩,.f ⟨24,4,1,0,1,0,0,0,0⟩,.s 16 0,.s 16 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 174 0,.s 174 0,.s 174 0,.s 174 0]],[.s 170 3,.s 170 3,.s 170 3,.s 170 3]⟩,
⟨1,1,5,19,[[.s 171 0,.s 171 0,.s 171 0,.s 171 0],[.s 125 0,.s 125 0,.s 125 0,.s 125 0],[.f ⟨24,5,0,0,0,0,0,0,0⟩,.f ⟨24,5,1,0,1,0,0,0,0⟩,.s 17 0,.s 17 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 175 0,.s 175 0,.s 175 0,.s 175 0]],[.s 127 1,.s 127 1,.s 127 1,.s 127 1]⟩,
⟨1,1,6,13,[[.s 172 0,.s 172 0,.s 172 0,.s 172 0],[.f ⟨24,4,0,0,0,0,0,0,0⟩,.f ⟨24,4,1,0,1,0,0,0,0⟩,.s 16 0,.s 16 0],[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.f ⟨24,6,0,0,0,0,0,0,0⟩,.f ⟨24,6,1,0,1,0,0,0,0⟩,.s 18 0,.s 18 0],[.s 176 0,.s 176 0,.s 176 0,.s 176 0],[.f ⟨24,8,0,0,0,0,0,0,0⟩,.f ⟨24,8,1,0,1,0,0,0,0⟩,.s 20 0,.s 20 0]],[.s 172 4,.s 172 4,.s 172 4,.s 172 4]⟩,
⟨1,1,7,18,[[.s 173 0,.s 173 0,.s 173 0,.s 173 0],[.f ⟨24,5,0,0,0,0,0,0,0⟩,.f ⟨24,5,1,0,1,0,0,0,0⟩,.s 17 0,.s 17 0],[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.f ⟨24,7,0,0,0,0,0,0,0⟩,.f ⟨24,7,1,0,1,0,0,0,0⟩,.s 19 0,.s 19 0],[.s 177 0,.s 177 0,.s 177 0,.s 177 0],[.f ⟨24,9,0,0,0,0,0,0,0⟩,.f ⟨24,9,1,0,1,0,0,0,0⟩,.s 21 0,.s 21 0]],[.s 177 1,.s 177 1,.s 177 1,.s 177 1]⟩,
⟨1,1,8,14,[[.s 126 0,.s 126 0,.s 126 0,.s 126 0],[.s 174 0,.s 174 0,.s 174 0,.s 174 0],[.s 128 0,.s 128 0,.s 128 0,.s 128 0],[.f ⟨24,8,0,0,0,0,0,0,0⟩,.f ⟨24,8,1,0,1,0,0,0,0⟩,.s 20 0,.s 20 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.s 178 0,.s 178 0,.s 178 0,.s 178 0]],[.s 126 5,.s 126 5,.s 126 5,.s 126 5]⟩,
⟨1,1,9,17,[[.s 127 0,.s 127 0,.s 127 0,.s 127 0],[.s 175 0,.s 175 0,.s 175 0,.s 175 0],[.s 129 0,.s 129 0,.s 129 0,.s 129 0],[.f ⟨24,9,0,0,0,0,0,0,0⟩,.f ⟨24,9,1,0,1,0,0,0,0⟩,.s 21 0,.s 21 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0],[.s 179 0,.s 179 0,.s 179 0,.s 179 0]],[.s 131 1,.s 131 1,.s 131 1,.s 131 1]⟩,
⟨1,1,10,15,[[.s 176 0,.s 176 0,.s 176 0,.s 176 0],[.f ⟨24,8,0,0,0,0,0,0,0⟩,.f ⟨24,8,1,0,1,0,0,0,0⟩,.s 20 0,.s 20 0],[.s 130 0,.s 130 0,.s 130 0,.s 130 0],[.f ⟨24,10,0,0,0,0,0,0,0⟩,.f ⟨24,10,1,0,1,0,0,0,0⟩,.s 22 0,.s 22 0],[.s 179 0,.s 179 0,.s 179 0,.s 179 0]],[.s 176 5,.s 176 5,.s 176 5,.s 176 5]⟩,
⟨1,1,11,16,[[.s 177 0,.s 177 0,.s 177 0,.s 177 0],[.f ⟨24,9,0,0,0,0,0,0,0⟩,.f ⟨24,9,1,0,1,0,0,0,0⟩,.s 21 0,.s 21 0],[.s 178 0,.s 178 0,.s 178 0,.s 178 0],[.s 131 0,.s 131 0,.s 131 0,.s 131 0],[.f ⟨24,11,0,0,0,0,0,0,0⟩,.f ⟨24,11,1,0,1,0,0,0,0⟩,.s 23 0,.s 23 0]],[.s 178 4,.s 178 4,.s 178 4,.s 178 4]⟩,
⟨1,2,0,21,[[.s 132 0,.s 132 0,.s 132 0,.s 132 0],[.s 216 0,.s 216 0,.s 216 0,.s 216 0],[.s 181 0,.s 181 0,.s 181 0,.s 181 0],[.s 171 0,.s 171 0,.s 171 0,.s 171 0]],[.s 171 0,.s 171 0,.s 171 0,.s 171 0]⟩,
⟨1,2,1,22,[[.s 180 0,.s 180 0,.s 180 0,.s 180 0],[.s 133 0,.s 133 0,.s 133 0,.s 133 0],[.s 217 0,.s 217 0,.s 217 0,.s 217 0],[.s 182 0,.s 182 0,.s 182 0,.s 182 0]],[.s 180 2,.s 180 2,.s 180 2,.s 180 2]⟩,
⟨1,2,2,23,[[.s 181 0,.s 181 0,.s 181 0,.s 181 0],[.s 134 0,.s 134 0,.s 134 0,.s 134 0],[.s 218 0,.s 218 0,.s 218 0,.s 218 0],[.s 184 0,.s 184 0,.s 184 0,.s 184 0]],[.s 181 3,.s 181 3,.s 181 3,.s 181 3]⟩,
⟨1,2,3,32,[[.s 192 0,.s 192 0,.s 192 0,.s 192 0],[.s 135 0,.s 135 0,.s 135 0,.s 135 0],[.s 219 0,.s 219 0,.s 219 0,.s 219 0],[.s 185 0,.s 185 0,.s 185 0,.s 185 0]],[.s 185 0,.s 185 0,.s 185 0,.s 185 0]⟩,
⟨1,2,4,24,[[.s 182 0,.s 182 0,.s 182 0,.s 182 0],[.s 136 0,.s 136 0,.s 136 0,.s 136 0],[.s 220 0,.s 220 0,.s 220 0,.s 220 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 186 0,.s 186 0,.s 186 0,.s 186 0]],[.s 182 3,.s 182 3,.s 182 3,.s 182 3]⟩,
⟨1,2,5,31,[[.s 183 0,.s 183 0,.s 183 0,.s 183 0],[.s 137 0,.s 137 0,.s 137 0,.s 137 0],[.s 221 0,.s 221 0,.s 221 0,.s 221 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 187 0,.s 187 0,.s 187 0,.s 187 0]],[.s 139 1,.s 139 1,.s 139 1,.s 139 1]⟩,
⟨1,2,6,25,[[.s 184 0,.s 184 0,.s 184 0,.s 184 0],[.s 220 0,.s 220 0,.s 220 0,.s 220 0],[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 222 0,.s 222 0,.s 222 0,.s 222 0],[.s 188 0,.s 188 0,.s 188 0,.s 188 0],[.s 224 0,.s 224 0,.s 224 0,.s 224 0]],[.s 184 4,.s 184 4,.s 184 4,.s 184 4]⟩,
⟨1,2,7,30,[[.s 185 0,.s 185 0,.s 185 0,.s 185 0],[.s 221 0,.s 221 0,.s 221 0,.s 221 0],[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 223 0,.s 223 0,.s 223 0,.s 223 0],[.s 189 0,.s 189 0,.s 189 0,.s 189 0],[.s 225 0,.s 225 0,.s 225 0,.s 225 0]],[.s 189 1,.s 189 1,.s 189 1,.s 189 1]⟩,
⟨1,2,8,26,[[.s 138 0,.s 138 0,.s 138 0,.s 138 0],[.s 186 0,.s 186 0,.s 186 0,.s 186 0],[.s 140 0,.s 140 0,.s 140 0,.s 140 0],[.s 224 0,.s 224 0,.s 224 0,.s 224 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 190 0,.s 190 0,.s 190 0,.s 190 0]],[.s 138 5,.s 138 5,.s 138 5,.s 138 5]⟩,
⟨1,2,9,29,[[.s 139 0,.s 139 0,.s 139 0,.s 139 0],[.s 187 0,.s 187 0,.s 187 0,.s 187 0],[.s 141 0,.s 141 0,.s 141 0,.s 141 0],[.s 225 0,.s 225 0,.s 225 0,.s 225 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0],[.s 191 0,.s 191 0,.s 191 0,.s 191 0]],[.s 143 1,.s 143 1,.s 143 1,.s 143 1]⟩,
⟨1,2,10,27,[[.s 188 0,.s 188 0,.s 188 0,.s 188 0],[.s 224 0,.s 224 0,.s 224 0,.s 224 0],[.s 142 0,.s 142 0,.s 142 0,.s 142 0],[.s 226 0,.s 226 0,.s 226 0,.s 226 0],[.s 191 0,.s 191 0,.s 191 0,.s 191 0]],[.s 188 5,.s 188 5,.s 188 5,.s 188 5]⟩,
⟨1,2,11,28,[[.s 189 0,.s 189 0,.s 189 0,.s 189 0],[.s 225 0,.s 225 0,.s 225 0,.s 225 0],[.s 190 0,.s 190 0,.s 190 0,.s 190 0],[.s 143 0,.s 143 0,.s 143 0,.s 143 0],[.s 227 0,.s 227 0,.s 227 0,.s 227 0]],[.s 190 4,.s 190 4,.s 190 4,.s 190 4]⟩,
⟨1,3,0,33,[[.s 144 0,.s 144 0,.s 144 0,.s 144 0],[.s 228 0,.s 228 0,.s 228 0,.s 228 0],[.s 193 0,.s 193 0,.s 193 0,.s 193 0],[.s 183 0,.s 183 0,.s 183 0,.s 183 0]],[.s 183 0,.s 183 0,.s 183 0,.s 183 0]⟩,
⟨1,3,1,34,[[.s 192 0,.s 192 0,.s 192 0,.s 192 0],[.s 145 0,.s 145 0,.s 145 0,.s 145 0],[.s 229 0,.s 229 0,.s 229 0,.s 229 0],[.s 194 0,.s 194 0,.s 194 0,.s 194 0]],[.s 192 2,.s 192 2,.s 192 2,.s 192 2]⟩,
⟨1,3,2,35,[[.s 193 0,.s 193 0,.s 193 0,.s 193 0],[.s 146 0,.s 146 0,.s 146 0,.s 146 0],[.s 230 0,.s 230 0,.s 230 0,.s 230 0],[.s 196 0,.s 196 0,.s 196 0,.s 196 0]],[.s 193 3,.s 193 3,.s 193 3,.s 193 3]⟩,
⟨1,3,3,44,[[.s 204 0,.s 204 0,.s 204 0,.s 204 0],[.s 147 0,.s 147 0,.s 147 0,.s 147 0],[.s 231 0,.s 231 0,.s 231 0,.s 231 0],[.s 197 0,.s 197 0,.s 197 0,.s 197 0]],[.s 197 0,.s 197 0,.s 197 0,.s 197 0]⟩,
⟨1,3,4,36,[[.s 194 0,.s 194 0,.s 194 0,.s 194 0],[.s 148 0,.s 148 0,.s 148 0,.s 148 0],[.s 232 0,.s 232 0,.s 232 0,.s 232 0],[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.s 198 0,.s 198 0,.s 198 0,.s 198 0]],[.s 194 3,.s 194 3,.s 194 3,.s 194 3]⟩,
⟨1,3,5,43,[[.s 195 0,.s 195 0,.s 195 0,.s 195 0],[.s 149 0,.s 149 0,.s 149 0,.s 149 0],[.s 233 0,.s 233 0,.s 233 0,.s 233 0],[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.s 199 0,.s 199 0,.s 199 0,.s 199 0]],[.s 151 1,.s 151 1,.s 151 1,.s 151 1]⟩,
⟨1,3,6,37,[[.s 196 0,.s 196 0,.s 196 0,.s 196 0],[.s 232 0,.s 232 0,.s 232 0,.s 232 0],[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.s 234 0,.s 234 0,.s 234 0,.s 234 0],[.s 200 0,.s 200 0,.s 200 0,.s 200 0],[.s 236 0,.s 236 0,.s 236 0,.s 236 0]],[.s 196 4,.s 196 4,.s 196 4,.s 196 4]⟩,
⟨1,3,7,42,[[.s 197 0,.s 197 0,.s 197 0,.s 197 0],[.s 233 0,.s 233 0,.s 233 0,.s 233 0],[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.s 235 0,.s 235 0,.s 235 0,.s 235 0],[.s 201 0,.s 201 0,.s 201 0,.s 201 0],[.s 237 0,.s 237 0,.s 237 0,.s 237 0]],[.s 201 1,.s 201 1,.s 201 1,.s 201 1]⟩,
⟨1,3,8,38,[[.s 150 0,.s 150 0,.s 150 0,.s 150 0],[.s 198 0,.s 198 0,.s 198 0,.s 198 0],[.s 152 0,.s 152 0,.s 152 0,.s 152 0],[.s 236 0,.s 236 0,.s 236 0,.s 236 0],[.s 154 0,.s 154 0,.s 154 0,.s 154 0],[.s 202 0,.s 202 0,.s 202 0,.s 202 0]],[.s 150 5,.s 150 5,.s 150 5,.s 150 5]⟩,
⟨1,3,9,41,[[.s 151 0,.s 151 0,.s 151 0,.s 151 0],[.s 199 0,.s 199 0,.s 199 0,.s 199 0],[.s 153 0,.s 153 0,.s 153 0,.s 153 0],[.s 237 0,.s 237 0,.s 237 0,.s 237 0],[.s 155 0,.s 155 0,.s 155 0,.s 155 0],[.s 203 0,.s 203 0,.s 203 0,.s 203 0]],[.s 155 1,.s 155 1,.s 155 1,.s 155 1]⟩,
⟨1,3,10,39,[[.s 200 0,.s 200 0,.s 200 0,.s 200 0],[.s 236 0,.s 236 0,.s 236 0,.s 236 0],[.s 154 0,.s 154 0,.s 154 0,.s 154 0],[.s 238 0,.s 238 0,.s 238 0,.s 238 0],[.s 203 0,.s 203 0,.s 203 0,.s 203 0]],[.s 200 5,.s 200 5,.s 200 5,.s 200 5]⟩,
⟨1,3,11,40,[[.s 201 0,.s 201 0,.s 201 0,.s 201 0],[.s 237 0,.s 237 0,.s 237 0,.s 237 0],[.s 202 0,.s 202 0,.s 202 0,.s 202 0],[.s 155 0,.s 155 0,.s 155 0,.s 155 0],[.s 239 0,.s 239 0,.s 239 0,.s 239 0]],[.s 202 4,.s 202 4,.s 202 4,.s 202 4]⟩,
⟨1,4,0,45,[[.s 156 0,.s 156 0,.s 156 0,.s 156 0],[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 205 0,.s 205 0,.s 205 0,.s 205 0],[.s 195 0,.s 195 0,.s 195 0,.s 195 0]],[.s 195 0,.s 195 0,.s 195 0,.s 195 0]⟩,
⟨1,4,1,46,[[.s 204 0,.s 204 0,.s 204 0,.s 204 0],[.s 157 0,.s 157 0,.s 157 0,.s 157 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 206 0,.s 206 0,.s 206 0,.s 206 0]],[.s 204 2,.s 204 2,.s 204 2,.s 204 2]⟩,
⟨1,4,2,47,[[.s 205 0,.s 205 0,.s 205 0,.s 205 0],[.s 158 0,.s 158 0,.s 158 0,.s 158 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 208 0,.s 208 0,.s 208 0,.s 208 0]],[.s 205 3,.s 205 3,.s 205 3,.s 205 3]⟩,
⟨1,4,3,56,[[.s 168 0,.s 168 0,.s 168 0,.s 168 0],[.s 159 0,.s 159 0,.s 159 0,.s 159 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 209 0,.s 209 0,.s 209 0,.s 209 0]],[.s 209 0,.s 209 0,.s 209 0,.s 209 0]⟩,
⟨1,4,4,48,[[.s 206 0,.s 206 0,.s 206 0,.s 206 0],[.s 160 0,.s 160 0,.s 160 0,.s 160 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 210 0,.s 210 0,.s 210 0,.s 210 0]],[.s 206 3,.s 206 3,.s 206 3,.s 206 3]⟩,
⟨1,4,5,55,[[.s 207 0,.s 207 0,.s 207 0,.s 207 0],[.s 161 0,.s 161 0,.s 161 0,.s 161 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0],[.s 211 0,.s 211 0,.s 211 0,.s 211 0]],[.s 163 1,.s 163 1,.s 163 1,.s 163 1]⟩,
⟨1,4,6,49,[[.s 208 0,.s 208 0,.s 208 0,.s 208 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 212 0,.s 212 0,.s 212 0,.s 212 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0]],[.s 208 4,.s 208 4,.s 208 4,.s 208 4]⟩,
⟨1,4,7,54,[[.s 209 0,.s 209 0,.s 209 0,.s 209 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 163 0,.s 163 0,.s 163 0,.s 163 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 213 0,.s 213 0,.s 213 0,.s 213 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0]],[.s 213 1,.s 213 1,.s 213 1,.s 213 1]⟩,
⟨1,4,8,50,[[.s 162 0,.s 162 0,.s 162 0,.s 162 0],[.s 210 0,.s 210 0,.s 210 0,.s 210 0],[.s 164 0,.s 164 0,.s 164 0,.s 164 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 166 0,.s 166 0,.s 166 0,.s 166 0],[.s 214 0,.s 214 0,.s 214 0,.s 214 0]],[.s 162 5,.s 162 5,.s 162 5,.s 162 5]⟩,
⟨1,4,9,53,[[.s 163 0,.s 163 0,.s 163 0,.s 163 0],[.s 211 0,.s 211 0,.s 211 0,.s 211 0],[.s 165 0,.s 165 0,.s 165 0,.s 165 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 167 0,.s 167 0,.s 167 0,.s 167 0],[.s 215 0,.s 215 0,.s 215 0,.s 215 0]],[.s 167 1,.s 167 1,.s 167 1,.s 167 1]⟩,
⟨1,4,10,51,[[.s 212 0,.s 212 0,.s 212 0,.s 212 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 166 0,.s 166 0,.s 166 0,.s 166 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 215 0,.s 215 0,.s 215 0,.s 215 0]],[.s 212 5,.s 212 5,.s 212 5,.s 212 5]⟩,
⟨1,4,11,52,[[.s 213 0,.s 213 0,.s 213 0,.s 213 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 214 0,.s 214 0,.s 214 0,.s 214 0],[.s 167 0,.s 167 0,.s 167 0,.s 167 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 214 4,.s 214 4,.s 214 4,.s 214 4]⟩,
⟨2,2,0,21,[[.s 180 0,.s 180 0,.s 180 0,.s 180 0],[.s 240 0,.s 240 0,.s 240 0,.s 240 0],[.s 217 0,.s 217 0,.s 217 0,.s 217 0],[.f ⟨24,3,0,0,0,0,0,0,0⟩,.f ⟨24,3,1,0,1,0,0,0,0⟩,.s 15 0,.s 15 0]],[.f ⟨24,3,0,0,0,0,0,0,0⟩,.f ⟨24,3,1,0,1,0,0,0,0⟩,.s 15 0,.s 15 0]⟩,
⟨2,2,1,22,[[.s 216 0,.s 216 0,.s 216 0,.s 216 0],[.s 181 0,.s 181 0,.s 181 0,.s 181 0],[.s 241 0,.s 241 0,.s 241 0,.s 241 0],[.s 218 0,.s 218 0,.s 218 0,.s 218 0]],[.s 216 2,.s 216 2,.s 216 2,.s 216 2]⟩,
⟨2,2,2,23,[[.s 217 0,.s 217 0,.s 217 0,.s 217 0],[.s 182 0,.s 182 0,.s 182 0,.s 182 0],[.s 242 0,.s 242 0,.s 242 0,.s 242 0],[.s 220 0,.s 220 0,.s 220 0,.s 220 0]],[.s 217 3,.s 217 3,.s 217 3,.s 217 3]⟩,
⟨2,2,3,32,[[.s 228 0,.s 228 0,.s 228 0,.s 228 0],[.s 183 0,.s 183 0,.s 183 0,.s 183 0],[.s 243 0,.s 243 0,.s 243 0,.s 243 0],[.s 221 0,.s 221 0,.s 221 0,.s 221 0]],[.s 221 0,.s 221 0,.s 221 0,.s 221 0]⟩,
⟨2,2,4,24,[[.s 218 0,.s 218 0,.s 218 0,.s 218 0],[.s 184 0,.s 184 0,.s 184 0,.s 184 0],[.s 244 0,.s 244 0,.s 244 0,.s 244 0],[.s 186 0,.s 186 0,.s 186 0,.s 186 0],[.s 222 0,.s 222 0,.s 222 0,.s 222 0]],[.s 218 3,.s 218 3,.s 218 3,.s 218 3]⟩,
⟨2,2,5,31,[[.s 219 0,.s 219 0,.s 219 0,.s 219 0],[.s 185 0,.s 185 0,.s 185 0,.s 185 0],[.s 245 0,.s 245 0,.s 245 0,.s 245 0],[.s 187 0,.s 187 0,.s 187 0,.s 187 0],[.s 223 0,.s 223 0,.s 223 0,.s 223 0]],[.s 187 1,.s 187 1,.s 187 1,.s 187 1]⟩,
⟨2,2,6,25,[[.s 220 0,.s 220 0,.s 220 0,.s 220 0],[.s 244 0,.s 244 0,.s 244 0,.s 244 0],[.s 186 0,.s 186 0,.s 186 0,.s 186 0],[.s 246 0,.s 246 0,.s 246 0,.s 246 0],[.s 224 0,.s 224 0,.s 224 0,.s 224 0],[.s 248 0,.s 248 0,.s 248 0,.s 248 0]],[.s 220 4,.s 220 4,.s 220 4,.s 220 4]⟩,
⟨2,2,7,30,[[.s 221 0,.s 221 0,.s 221 0,.s 221 0],[.s 245 0,.s 245 0,.s 245 0,.s 245 0],[.s 187 0,.s 187 0,.s 187 0,.s 187 0],[.s 247 0,.s 247 0,.s 247 0,.s 247 0],[.s 225 0,.s 225 0,.s 225 0,.s 225 0],[.s 249 0,.s 249 0,.s 249 0,.s 249 0]],[.s 225 1,.s 225 1,.s 225 1,.s 225 1]⟩,
⟨2,2,8,26,[[.s 186 0,.s 186 0,.s 186 0,.s 186 0],[.s 222 0,.s 222 0,.s 222 0,.s 222 0],[.s 188 0,.s 188 0,.s 188 0,.s 188 0],[.s 248 0,.s 248 0,.s 248 0,.s 248 0],[.s 190 0,.s 190 0,.s 190 0,.s 190 0],[.s 226 0,.s 226 0,.s 226 0,.s 226 0]],[.s 186 5,.s 186 5,.s 186 5,.s 186 5]⟩,
⟨2,2,9,29,[[.s 187 0,.s 187 0,.s 187 0,.s 187 0],[.s 223 0,.s 223 0,.s 223 0,.s 223 0],[.s 189 0,.s 189 0,.s 189 0,.s 189 0],[.s 249 0,.s 249 0,.s 249 0,.s 249 0],[.s 191 0,.s 191 0,.s 191 0,.s 191 0],[.s 227 0,.s 227 0,.s 227 0,.s 227 0]],[.s 191 1,.s 191 1,.s 191 1,.s 191 1]⟩,
⟨2,2,10,27,[[.s 224 0,.s 224 0,.s 224 0,.s 224 0],[.s 248 0,.s 248 0,.s 248 0,.s 248 0],[.s 190 0,.s 190 0,.s 190 0,.s 190 0],[.s 250 0,.s 250 0,.s 250 0,.s 250 0],[.s 227 0,.s 227 0,.s 227 0,.s 227 0]],[.s 224 5,.s 224 5,.s 224 5,.s 224 5]⟩,
⟨2,2,11,28,[[.s 225 0,.s 225 0,.s 225 0,.s 225 0],[.s 249 0,.s 249 0,.s 249 0,.s 249 0],[.s 226 0,.s 226 0,.s 226 0,.s 226 0],[.s 191 0,.s 191 0,.s 191 0,.s 191 0],[.s 251 0,.s 251 0,.s 251 0,.s 251 0]],[.s 226 4,.s 226 4,.s 226 4,.s 226 4]⟩,
⟨2,3,0,33,[[.s 192 0,.s 192 0,.s 192 0,.s 192 0],[.s 252 0,.s 252 0,.s 252 0,.s 252 0],[.s 229 0,.s 229 0,.s 229 0,.s 229 0],[.s 219 0,.s 219 0,.s 219 0,.s 219 0]],[.s 219 0,.s 219 0,.s 219 0,.s 219 0]⟩,
⟨2,3,1,34,[[.s 228 0,.s 228 0,.s 228 0,.s 228 0],[.s 193 0,.s 193 0,.s 193 0,.s 193 0],[.s 253 0,.s 253 0,.s 253 0,.s 253 0],[.s 230 0,.s 230 0,.s 230 0,.s 230 0]],[.s 228 2,.s 228 2,.s 228 2,.s 228 2]⟩,
⟨2,3,2,35,[[.s 229 0,.s 229 0,.s 229 0,.s 229 0],[.s 194 0,.s 194 0,.s 194 0,.s 194 0],[.s 254 0,.s 254 0,.s 254 0,.s 254 0],[.s 232 0,.s 232 0,.s 232 0,.s 232 0]],[.s 229 3,.s 229 3,.s 229 3,.s 229 3]⟩,
⟨2,3,3,44,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 195 0,.s 195 0,.s 195 0,.s 195 0],[.s 255 0,.s 255 0,.s 255 0,.s 255 0],[.s 233 0,.s 233 0,.s 233 0,.s 233 0]],[.s 233 0,.s 233 0,.s 233 0,.s 233 0]⟩,
⟨2,3,4,36,[[.s 230 0,.s 230 0,.s 230 0,.s 230 0],[.s 196 0,.s 196 0,.s 196 0,.s 196 0],[.s 256 0,.s 256 0,.s 256 0,.s 256 0],[.s 198 0,.s 198 0,.s 198 0,.s 198 0],[.s 234 0,.s 234 0,.s 234 0,.s 234 0]],[.s 230 3,.s 230 3,.s 230 3,.s 230 3]⟩,
⟨2,3,5,43,[[.s 231 0,.s 231 0,.s 231 0,.s 231 0],[.s 197 0,.s 197 0,.s 197 0,.s 197 0],[.s 257 0,.s 257 0,.s 257 0,.s 257 0],[.s 199 0,.s 199 0,.s 199 0,.s 199 0],[.s 235 0,.s 235 0,.s 235 0,.s 235 0]],[.s 199 1,.s 199 1,.s 199 1,.s 199 1]⟩,
⟨2,3,6,37,[[.s 232 0,.s 232 0,.s 232 0,.s 232 0],[.s 256 0,.s 256 0,.s 256 0,.s 256 0],[.s 198 0,.s 198 0,.s 198 0,.s 198 0],[.s 258 0,.s 258 0,.s 258 0,.s 258 0],[.s 236 0,.s 236 0,.s 236 0,.s 236 0],[.s 260 0,.s 260 0,.s 260 0,.s 260 0]],[.s 232 4,.s 232 4,.s 232 4,.s 232 4]⟩,
⟨2,3,7,42,[[.s 233 0,.s 233 0,.s 233 0,.s 233 0],[.s 257 0,.s 257 0,.s 257 0,.s 257 0],[.s 199 0,.s 199 0,.s 199 0,.s 199 0],[.s 259 0,.s 259 0,.s 259 0,.s 259 0],[.s 237 0,.s 237 0,.s 237 0,.s 237 0],[.s 261 0,.s 261 0,.s 261 0,.s 261 0]],[.s 237 1,.s 237 1,.s 237 1,.s 237 1]⟩,
⟨2,3,8,38,[[.s 198 0,.s 198 0,.s 198 0,.s 198 0],[.s 234 0,.s 234 0,.s 234 0,.s 234 0],[.s 200 0,.s 200 0,.s 200 0,.s 200 0],[.s 260 0,.s 260 0,.s 260 0,.s 260 0],[.s 202 0,.s 202 0,.s 202 0,.s 202 0],[.s 238 0,.s 238 0,.s 238 0,.s 238 0]],[.s 198 5,.s 198 5,.s 198 5,.s 198 5]⟩,
⟨2,3,9,41,[[.s 199 0,.s 199 0,.s 199 0,.s 199 0],[.s 235 0,.s 235 0,.s 235 0,.s 235 0],[.s 201 0,.s 201 0,.s 201 0,.s 201 0],[.s 261 0,.s 261 0,.s 261 0,.s 261 0],[.s 203 0,.s 203 0,.s 203 0,.s 203 0],[.s 239 0,.s 239 0,.s 239 0,.s 239 0]],[.s 203 1,.s 203 1,.s 203 1,.s 203 1]⟩,
⟨2,3,10,39,[[.s 236 0,.s 236 0,.s 236 0,.s 236 0],[.s 260 0,.s 260 0,.s 260 0,.s 260 0],[.s 202 0,.s 202 0,.s 202 0,.s 202 0],[.s 262 0,.s 262 0,.s 262 0,.s 262 0],[.s 239 0,.s 239 0,.s 239 0,.s 239 0]],[.s 236 5,.s 236 5,.s 236 5,.s 236 5]⟩,
⟨2,3,11,40,[[.s 237 0,.s 237 0,.s 237 0,.s 237 0],[.s 261 0,.s 261 0,.s 261 0,.s 261 0],[.s 238 0,.s 238 0,.s 238 0,.s 238 0],[.s 203 0,.s 203 0,.s 203 0,.s 203 0],[.s 263 0,.s 263 0,.s 263 0,.s 263 0]],[.s 238 4,.s 238 4,.s 238 4,.s 238 4]⟩,
⟨3,2,0,21,[[.s 216 0,.s 216 0,.s 216 0,.s 216 0],[.s 264 0,.s 264 0,.s 264 0,.s 264 0],[.s 241 0,.s 241 0,.s 241 0,.s 241 0],[.f ⟨6,3,0,0,0,0,0,0,0⟩,.f ⟨7,15,1,0,0,0,0,0,0⟩,.s 39 0,.s 39 0]],[.f ⟨6,3,0,0,0,0,0,0,0⟩,.f ⟨7,15,1,0,0,0,0,0,0⟩,.s 39 0,.s 39 0]⟩,
⟨3,2,1,22,[[.s 240 0,.s 240 0,.s 240 0,.s 240 0],[.s 217 0,.s 217 0,.s 217 0,.s 217 0],[.s 265 0,.s 265 0,.s 265 0,.s 265 0],[.s 242 0,.s 242 0,.s 242 0,.s 242 0]],[.s 240 2,.s 240 2,.s 240 2,.s 240 2]⟩,
⟨3,2,2,23,[[.s 241 0,.s 241 0,.s 241 0,.s 241 0],[.s 218 0,.s 218 0,.s 218 0,.s 218 0],[.s 266 0,.s 266 0,.s 266 0,.s 266 0],[.s 244 0,.s 244 0,.s 244 0,.s 244 0]],[.s 241 3,.s 241 3,.s 241 3,.s 241 3]⟩,
⟨3,2,3,32,[[.s 252 0,.s 252 0,.s 252 0,.s 252 0],[.s 219 0,.s 219 0,.s 219 0,.s 219 0],[.s 267 0,.s 267 0,.s 267 0,.s 267 0],[.s 245 0,.s 245 0,.s 245 0,.s 245 0]],[.s 245 0,.s 245 0,.s 245 0,.s 245 0]⟩,
⟨3,2,4,24,[[.s 242 0,.s 242 0,.s 242 0,.s 242 0],[.s 220 0,.s 220 0,.s 220 0,.s 220 0],[.s 268 0,.s 268 0,.s 268 0,.s 268 0],[.s 222 0,.s 222 0,.s 222 0,.s 222 0],[.s 246 0,.s 246 0,.s 246 0,.s 246 0]],[.s 242 3,.s 242 3,.s 242 3,.s 242 3]⟩,
⟨3,2,5,31,[[.s 243 0,.s 243 0,.s 243 0,.s 243 0],[.s 221 0,.s 221 0,.s 221 0,.s 221 0],[.s 269 0,.s 269 0,.s 269 0,.s 269 0],[.s 223 0,.s 223 0,.s 223 0,.s 223 0],[.s 247 0,.s 247 0,.s 247 0,.s 247 0]],[.s 223 1,.s 223 1,.s 223 1,.s 223 1]⟩,
⟨3,2,6,25,[[.s 244 0,.s 244 0,.s 244 0,.s 244 0],[.s 268 0,.s 268 0,.s 268 0,.s 268 0],[.s 222 0,.s 222 0,.s 222 0,.s 222 0],[.s 270 0,.s 270 0,.s 270 0,.s 270 0],[.s 248 0,.s 248 0,.s 248 0,.s 248 0],[.s 272 0,.s 272 0,.s 272 0,.s 272 0]],[.s 244 4,.s 244 4,.s 244 4,.s 244 4]⟩,
⟨3,2,7,30,[[.s 245 0,.s 245 0,.s 245 0,.s 245 0],[.s 269 0,.s 269 0,.s 269 0,.s 269 0],[.s 223 0,.s 223 0,.s 223 0,.s 223 0],[.s 271 0,.s 271 0,.s 271 0,.s 271 0],[.s 249 0,.s 249 0,.s 249 0,.s 249 0],[.s 273 0,.s 273 0,.s 273 0,.s 273 0]],[.s 249 1,.s 249 1,.s 249 1,.s 249 1]⟩,
⟨3,2,8,26,[[.s 222 0,.s 222 0,.s 222 0,.s 222 0],[.s 246 0,.s 246 0,.s 246 0,.s 246 0],[.s 224 0,.s 224 0,.s 224 0,.s 224 0],[.s 272 0,.s 272 0,.s 272 0,.s 272 0],[.s 226 0,.s 226 0,.s 226 0,.s 226 0],[.s 250 0,.s 250 0,.s 250 0,.s 250 0]],[.s 222 5,.s 222 5,.s 222 5,.s 222 5]⟩,
⟨3,2,9,29,[[.s 223 0,.s 223 0,.s 223 0,.s 223 0],[.s 247 0,.s 247 0,.s 247 0,.s 247 0],[.s 225 0,.s 225 0,.s 225 0,.s 225 0],[.s 273 0,.s 273 0,.s 273 0,.s 273 0],[.s 227 0,.s 227 0,.s 227 0,.s 227 0],[.s 251 0,.s 251 0,.s 251 0,.s 251 0]],[.s 227 1,.s 227 1,.s 227 1,.s 227 1]⟩,
⟨3,2,10,27,[[.s 248 0,.s 248 0,.s 248 0,.s 248 0],[.s 272 0,.s 272 0,.s 272 0,.s 272 0],[.s 226 0,.s 226 0,.s 226 0,.s 226 0],[.s 274 0,.s 274 0,.s 274 0,.s 274 0],[.s 251 0,.s 251 0,.s 251 0,.s 251 0]],[.s 248 5,.s 248 5,.s 248 5,.s 248 5]⟩,
⟨3,2,11,28,[[.s 249 0,.s 249 0,.s 249 0,.s 249 0],[.s 273 0,.s 273 0,.s 273 0,.s 273 0],[.s 250 0,.s 250 0,.s 250 0,.s 250 0],[.s 227 0,.s 227 0,.s 227 0,.s 227 0],[.s 275 0,.s 275 0,.s 275 0,.s 275 0]],[.s 250 4,.s 250 4,.s 250 4,.s 250 4]⟩,
⟨3,3,0,33,[[.s 228 0,.s 228 0,.s 228 0,.s 228 0],[.s 276 0,.s 276 0,.s 276 0,.s 276 0],[.s 253 0,.s 253 0,.s 253 0,.s 253 0],[.s 243 0,.s 243 0,.s 243 0,.s 243 0]],[.s 243 0,.s 243 0,.s 243 0,.s 243 0]⟩,
⟨3,3,1,34,[[.s 252 0,.s 252 0,.s 252 0,.s 252 0],[.s 229 0,.s 229 0,.s 229 0,.s 229 0],[.s 277 0,.s 277 0,.s 277 0,.s 277 0],[.s 254 0,.s 254 0,.s 254 0,.s 254 0]],[.s 252 2,.s 252 2,.s 252 2,.s 252 2]⟩,
⟨3,3,2,35,[[.s 253 0,.s 253 0,.s 253 0,.s 253 0],[.s 230 0,.s 230 0,.s 230 0,.s 230 0],[.s 278 0,.s 278 0,.s 278 0,.s 278 0],[.s 256 0,.s 256 0,.s 256 0,.s 256 0]],[.s 253 3,.s 253 3,.s 253 3,.s 253 3]⟩,
⟨3,3,3,44,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 231 0,.s 231 0,.s 231 0,.s 231 0],[.s 279 0,.s 279 0,.s 279 0,.s 279 0],[.s 257 0,.s 257 0,.s 257 0,.s 257 0]],[.s 257 0,.s 257 0,.s 257 0,.s 257 0]⟩,
⟨3,3,4,36,[[.s 254 0,.s 254 0,.s 254 0,.s 254 0],[.s 232 0,.s 232 0,.s 232 0,.s 232 0],[.s 280 0,.s 280 0,.s 280 0,.s 280 0],[.s 234 0,.s 234 0,.s 234 0,.s 234 0],[.s 258 0,.s 258 0,.s 258 0,.s 258 0]],[.s 254 3,.s 254 3,.s 254 3,.s 254 3]⟩,
⟨3,3,5,43,[[.s 255 0,.s 255 0,.s 255 0,.s 255 0],[.s 233 0,.s 233 0,.s 233 0,.s 233 0],[.s 281 0,.s 281 0,.s 281 0,.s 281 0],[.s 235 0,.s 235 0,.s 235 0,.s 235 0],[.s 259 0,.s 259 0,.s 259 0,.s 259 0]],[.s 235 1,.s 235 1,.s 235 1,.s 235 1]⟩,
⟨3,3,6,37,[[.s 256 0,.s 256 0,.s 256 0,.s 256 0],[.s 280 0,.s 280 0,.s 280 0,.s 280 0],[.s 234 0,.s 234 0,.s 234 0,.s 234 0],[.s 282 0,.s 282 0,.s 282 0,.s 282 0],[.s 260 0,.s 260 0,.s 260 0,.s 260 0],[.s 284 0,.s 284 0,.s 284 0,.s 284 0]],[.s 256 4,.s 256 4,.s 256 4,.s 256 4]⟩,
⟨3,3,7,42,[[.s 257 0,.s 257 0,.s 257 0,.s 257 0],[.s 281 0,.s 281 0,.s 281 0,.s 281 0],[.s 235 0,.s 235 0,.s 235 0,.s 235 0],[.s 283 0,.s 283 0,.s 283 0,.s 283 0],[.s 261 0,.s 261 0,.s 261 0,.s 261 0],[.s 285 0,.s 285 0,.s 285 0,.s 285 0]],[.s 261 1,.s 261 1,.s 261 1,.s 261 1]⟩,
⟨3,3,8,38,[[.s 234 0,.s 234 0,.s 234 0,.s 234 0],[.s 258 0,.s 258 0,.s 258 0,.s 258 0],[.s 236 0,.s 236 0,.s 236 0,.s 236 0],[.s 284 0,.s 284 0,.s 284 0,.s 284 0],[.s 238 0,.s 238 0,.s 238 0,.s 238 0],[.s 262 0,.s 262 0,.s 262 0,.s 262 0]],[.s 234 5,.s 234 5,.s 234 5,.s 234 5]⟩,
⟨3,3,9,41,[[.s 235 0,.s 235 0,.s 235 0,.s 235 0],[.s 259 0,.s 259 0,.s 259 0,.s 259 0],[.s 237 0,.s 237 0,.s 237 0,.s 237 0],[.s 285 0,.s 285 0,.s 285 0,.s 285 0],[.s 239 0,.s 239 0,.s 239 0,.s 239 0],[.s 263 0,.s 263 0,.s 263 0,.s 263 0]],[.s 239 1,.s 239 1,.s 239 1,.s 239 1]⟩,
⟨3,3,10,39,[[.s 260 0,.s 260 0,.s 260 0,.s 260 0],[.s 284 0,.s 284 0,.s 284 0,.s 284 0],[.s 238 0,.s 238 0,.s 238 0,.s 238 0],[.s 286 0,.s 286 0,.s 286 0,.s 286 0],[.s 263 0,.s 263 0,.s 263 0,.s 263 0]],[.s 260 5,.s 260 5,.s 260 5,.s 260 5]⟩,
⟨3,3,11,40,[[.s 261 0,.s 261 0,.s 261 0,.s 261 0],[.s 285 0,.s 285 0,.s 285 0,.s 285 0],[.s 262 0,.s 262 0,.s 262 0,.s 262 0],[.s 239 0,.s 239 0,.s 239 0,.s 239 0],[.s 287 0,.s 287 0,.s 287 0,.s 287 0]],[.s 262 4,.s 262 4,.s 262 4,.s 262 4]⟩,
⟨4,2,0,21,[[.s 240 0,.s 240 0,.s 240 0,.s 240 0],[.f ⟨24,12,0,0,0,0,0,0,0⟩,.f ⟨24,12,1,0,1,0,0,0,0⟩,.s 108 0,.s 108 0],[.s 265 0,.s 265 0,.s 265 0,.s 265 0],[.f ⟨20,3,0,0,0,0,0,0,0⟩,.f ⟨22,27,1,0,0,0,0,0,0⟩,.s 63 0,.s 63 0]],[.f ⟨20,3,0,0,0,0,0,0,0⟩,.f ⟨22,27,1,0,0,0,0,0,0⟩,.s 63 0,.s 63 0]⟩,
⟨4,2,1,22,[[.s 264 0,.s 264 0,.s 264 0,.s 264 0],[.s 241 0,.s 241 0,.s 241 0,.s 241 0],[.f ⟨24,13,0,0,0,0,0,0,0⟩,.f ⟨24,13,1,0,1,0,0,0,0⟩,.s 109 0,.s 109 0],[.s 266 0,.s 266 0,.s 266 0,.s 266 0]],[.s 264 2,.s 264 2,.s 264 2,.s 264 2]⟩,
⟨4,2,2,23,[[.s 265 0,.s 265 0,.s 265 0,.s 265 0],[.s 242 0,.s 242 0,.s 242 0,.s 242 0],[.f ⟨24,14,0,0,0,0,0,0,0⟩,.f ⟨24,14,1,0,1,0,0,0,0⟩,.s 110 0,.s 110 0],[.s 268 0,.s 268 0,.s 268 0,.s 268 0]],[.s 265 3,.s 265 3,.s 265 3,.s 265 3]⟩,
⟨4,2,3,32,[[.s 276 0,.s 276 0,.s 276 0,.s 276 0],[.s 243 0,.s 243 0,.s 243 0,.s 243 0],[.f ⟨24,15,0,0,0,0,0,0,0⟩,.f ⟨24,15,1,0,1,0,0,0,0⟩,.s 111 0,.s 111 0],[.s 269 0,.s 269 0,.s 269 0,.s 269 0]],[.s 269 0,.s 269 0,.s 269 0,.s 269 0]⟩,
⟨4,2,4,24,[[.s 266 0,.s 266 0,.s 266 0,.s 266 0],[.s 244 0,.s 244 0,.s 244 0,.s 244 0],[.f ⟨24,16,0,0,0,0,0,0,0⟩,.f ⟨24,16,1,0,1,0,0,0,0⟩,.s 112 0,.s 112 0],[.s 246 0,.s 246 0,.s 246 0,.s 246 0],[.s 270 0,.s 270 0,.s 270 0,.s 270 0]],[.s 266 3,.s 266 3,.s 266 3,.s 266 3]⟩,
⟨4,2,5,31,[[.s 267 0,.s 267 0,.s 267 0,.s 267 0],[.s 245 0,.s 245 0,.s 245 0,.s 245 0],[.f ⟨24,17,0,0,0,0,0,0,0⟩,.f ⟨24,17,1,0,1,0,0,0,0⟩,.s 113 0,.s 113 0],[.s 247 0,.s 247 0,.s 247 0,.s 247 0],[.s 271 0,.s 271 0,.s 271 0,.s 271 0]],[.s 247 1,.s 247 1,.s 247 1,.s 247 1]⟩,
⟨4,2,6,25,[[.s 268 0,.s 268 0,.s 268 0,.s 268 0],[.f ⟨24,16,0,0,0,0,0,0,0⟩,.f ⟨24,16,1,0,1,0,0,0,0⟩,.s 112 0,.s 112 0],[.s 246 0,.s 246 0,.s 246 0,.s 246 0],[.f ⟨24,18,0,0,0,0,0,0,0⟩,.f ⟨24,18,1,0,1,0,0,0,0⟩,.s 114 0,.s 114 0],[.s 272 0,.s 272 0,.s 272 0,.s 272 0],[.f ⟨24,20,0,0,0,0,0,0,0⟩,.f ⟨24,20,1,0,1,0,0,0,0⟩,.s 116 0,.s 116 0]],[.s 268 4,.s 268 4,.s 268 4,.s 268 4]⟩,
⟨4,2,7,30,[[.s 269 0,.s 269 0,.s 269 0,.s 269 0],[.f ⟨24,17,0,0,0,0,0,0,0⟩,.f ⟨24,17,1,0,1,0,0,0,0⟩,.s 113 0,.s 113 0],[.s 247 0,.s 247 0,.s 247 0,.s 247 0],[.f ⟨24,19,0,0,0,0,0,0,0⟩,.f ⟨24,19,1,0,1,0,0,0,0⟩,.s 115 0,.s 115 0],[.s 273 0,.s 273 0,.s 273 0,.s 273 0],[.f ⟨24,21,0,0,0,0,0,0,0⟩,.f ⟨24,21,1,0,1,0,0,0,0⟩,.s 117 0,.s 117 0]],[.s 273 1,.s 273 1,.s 273 1,.s 273 1]⟩,
⟨4,2,8,26,[[.s 246 0,.s 246 0,.s 246 0,.s 246 0],[.s 270 0,.s 270 0,.s 270 0,.s 270 0],[.s 248 0,.s 248 0,.s 248 0,.s 248 0],[.f ⟨24,20,0,0,0,0,0,0,0⟩,.f ⟨24,20,1,0,1,0,0,0,0⟩,.s 116 0,.s 116 0],[.s 250 0,.s 250 0,.s 250 0,.s 250 0],[.s 274 0,.s 274 0,.s 274 0,.s 274 0]],[.s 246 5,.s 246 5,.s 246 5,.s 246 5]⟩,
⟨4,2,9,29,[[.s 247 0,.s 247 0,.s 247 0,.s 247 0],[.s 271 0,.s 271 0,.s 271 0,.s 271 0],[.s 249 0,.s 249 0,.s 249 0,.s 249 0],[.f ⟨24,21,0,0,0,0,0,0,0⟩,.f ⟨24,21,1,0,1,0,0,0,0⟩,.s 117 0,.s 117 0],[.s 251 0,.s 251 0,.s 251 0,.s 251 0],[.s 275 0,.s 275 0,.s 275 0,.s 275 0]],[.s 251 1,.s 251 1,.s 251 1,.s 251 1]⟩,
⟨4,2,10,27,[[.s 272 0,.s 272 0,.s 272 0,.s 272 0],[.f ⟨24,20,0,0,0,0,0,0,0⟩,.f ⟨24,20,1,0,1,0,0,0,0⟩,.s 116 0,.s 116 0],[.s 250 0,.s 250 0,.s 250 0,.s 250 0],[.f ⟨24,22,0,0,0,0,0,0,0⟩,.f ⟨24,22,1,0,1,0,0,0,0⟩,.s 118 0,.s 118 0],[.s 275 0,.s 275 0,.s 275 0,.s 275 0]],[.s 272 5,.s 272 5,.s 272 5,.s 272 5]⟩,
⟨4,2,11,28,[[.s 273 0,.s 273 0,.s 273 0,.s 273 0],[.f ⟨24,21,0,0,0,0,0,0,0⟩,.f ⟨24,21,1,0,1,0,0,0,0⟩,.s 117 0,.s 117 0],[.s 274 0,.s 274 0,.s 274 0,.s 274 0],[.s 251 0,.s 251 0,.s 251 0,.s 251 0],[.f ⟨24,23,0,0,0,0,0,0,0⟩,.f ⟨24,23,1,0,1,0,0,0,0⟩,.s 119 0,.s 119 0]],[.s 274 4,.s 274 4,.s 274 4,.s 274 4]⟩,
⟨4,3,0,33,[[.s 252 0,.s 252 0,.s 252 0,.s 252 0],[.s 72 0,.s 72 0,.s 72 0,.s 72 0],[.s 277 0,.s 277 0,.s 277 0,.s 277 0],[.s 267 0,.s 267 0,.s 267 0,.s 267 0]],[.s 267 0,.s 267 0,.s 267 0,.s 267 0]⟩,
⟨4,3,1,34,[[.s 276 0,.s 276 0,.s 276 0,.s 276 0],[.s 253 0,.s 253 0,.s 253 0,.s 253 0],[.s 73 0,.s 73 0,.s 73 0,.s 73 0],[.s 278 0,.s 278 0,.s 278 0,.s 278 0]],[.s 276 2,.s 276 2,.s 276 2,.s 276 2]⟩,
⟨4,3,2,35,[[.s 277 0,.s 277 0,.s 277 0,.s 277 0],[.s 254 0,.s 254 0,.s 254 0,.s 254 0],[.s 74 0,.s 74 0,.s 74 0,.s 74 0],[.s 280 0,.s 280 0,.s 280 0,.s 280 0]],[.s 277 3,.s 277 3,.s 277 3,.s 277 3]⟩,
⟨4,3,3,44,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 255 0,.s 255 0,.s 255 0,.s 255 0],[.s 75 0,.s 75 0,.s 75 0,.s 75 0],[.s 281 0,.s 281 0,.s 281 0,.s 281 0]],[.s 281 0,.s 281 0,.s 281 0,.s 281 0]⟩,
⟨4,3,4,36,[[.s 278 0,.s 278 0,.s 278 0,.s 278 0],[.s 256 0,.s 256 0,.s 256 0,.s 256 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 258 0,.s 258 0,.s 258 0,.s 258 0],[.s 282 0,.s 282 0,.s 282 0,.s 282 0]],[.s 278 3,.s 278 3,.s 278 3,.s 278 3]⟩,
⟨4,3,5,43,[[.s 279 0,.s 279 0,.s 279 0,.s 279 0],[.s 257 0,.s 257 0,.s 257 0,.s 257 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 259 0,.s 259 0,.s 259 0,.s 259 0],[.s 283 0,.s 283 0,.s 283 0,.s 283 0]],[.s 259 1,.s 259 1,.s 259 1,.s 259 1]⟩,
⟨4,3,6,37,[[.s 280 0,.s 280 0,.s 280 0,.s 280 0],[.s 76 0,.s 76 0,.s 76 0,.s 76 0],[.s 258 0,.s 258 0,.s 258 0,.s 258 0],[.s 78 0,.s 78 0,.s 78 0,.s 78 0],[.s 284 0,.s 284 0,.s 284 0,.s 284 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0]],[.s 280 4,.s 280 4,.s 280 4,.s 280 4]⟩,
⟨4,3,7,42,[[.s 281 0,.s 281 0,.s 281 0,.s 281 0],[.s 77 0,.s 77 0,.s 77 0,.s 77 0],[.s 259 0,.s 259 0,.s 259 0,.s 259 0],[.s 79 0,.s 79 0,.s 79 0,.s 79 0],[.s 285 0,.s 285 0,.s 285 0,.s 285 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0]],[.s 285 1,.s 285 1,.s 285 1,.s 285 1]⟩,
⟨4,3,8,38,[[.s 258 0,.s 258 0,.s 258 0,.s 258 0],[.s 282 0,.s 282 0,.s 282 0,.s 282 0],[.s 260 0,.s 260 0,.s 260 0,.s 260 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 262 0,.s 262 0,.s 262 0,.s 262 0],[.s 286 0,.s 286 0,.s 286 0,.s 286 0]],[.s 258 5,.s 258 5,.s 258 5,.s 258 5]⟩,
⟨4,3,9,41,[[.s 259 0,.s 259 0,.s 259 0,.s 259 0],[.s 283 0,.s 283 0,.s 283 0,.s 283 0],[.s 261 0,.s 261 0,.s 261 0,.s 261 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 263 0,.s 263 0,.s 263 0,.s 263 0],[.s 287 0,.s 287 0,.s 287 0,.s 287 0]],[.s 263 1,.s 263 1,.s 263 1,.s 263 1]⟩,
⟨4,3,10,39,[[.s 284 0,.s 284 0,.s 284 0,.s 284 0],[.s 80 0,.s 80 0,.s 80 0,.s 80 0],[.s 262 0,.s 262 0,.s 262 0,.s 262 0],[.s 82 0,.s 82 0,.s 82 0,.s 82 0],[.s 287 0,.s 287 0,.s 287 0,.s 287 0]],[.s 284 5,.s 284 5,.s 284 5,.s 284 5]⟩,
⟨4,3,11,40,[[.s 285 0,.s 285 0,.s 285 0,.s 285 0],[.s 81 0,.s 81 0,.s 81 0,.s 81 0],[.s 286 0,.s 286 0,.s 286 0,.s 286 0],[.s 263 0,.s 263 0,.s 263 0,.s 263 0],[.s 83 0,.s 83 0,.s 83 0,.s 83 0]],[.s 286 4,.s 286 4,.s 286 4,.s 286 4]⟩]⟩,
⟨0,0,0,0,0,[(0,3,1),(-2,-6,1),(0,-3,-3),(2,6,-4)],0,0,0,0,0,0,0,0,0,0,0,0,
[⟨-5,1,0,11,[[.f ⟨29,24,0,0,0,0,0,0,0⟩],[.s 12 0],[.s 1 0],[.f ⟨11,27,0,0,0,0,0,0,0⟩]],[.s 12 0]⟩,
⟨-5,1,1,12,[[.s 0 0],[.f ⟨29,25,0,0,0,0,0,0,0⟩],[.s 13 0],[.s 2 0]],[.s 0 2]⟩,
⟨-5,1,2,13,[[.s 1 0],[.f ⟨29,26,0,0,0,0,0,0,0⟩],[.s 14 0],[.s 4 0]],[.s 1 3]⟩,
⟨-5,1,3,20,[[.f ⟨25,0,0,0,0,0,0,0,0⟩],[.f ⟨29,27,0,0,0,0,0,0,0⟩],[.s 15 0],[.s 5 0]],[.s 5 0]⟩,
⟨-5,1,4,14,[[.s 2 0],[.f ⟨29,28,0,0,0,0,0,0,0⟩],[.s 16 0],[.f ⟨29,30,0,0,0,0,0,0,0⟩],[.s 6 0]],[.s 2 3]⟩,
⟨-5,1,5,19,[[.s 3 0],[.f ⟨29,29,0,0,0,0,0,0,0⟩],[.s 17 0],[.f ⟨29,31,0,0,0,0,0,0,0⟩],[.s 7 0]],[.f ⟨29,31,0,0,0,0,0,0,1⟩]⟩,
⟨-5,1,6,14,[[.s 4 0],[.s 16 0],[.f ⟨29,30,0,0,0,0,0,0,0⟩],[.s 18 0],[.s 8 0],[.s 20 0]],[.s 16 3]⟩,
⟨-5,1,7,18,[[.s 5 0],[.s 17 0],[.f ⟨29,31,0,0,0,0,0,0,0⟩],[.s 19 0],[.s 9 0],[.s 21 0]],[.s 9 1]⟩,
⟨-5,1,8,15,[[.f ⟨29,30,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨29,32,0,0,0,0,0,0,0⟩],[.s 20 0],[.f ⟨29,34,0,0,0,0,0,0,0⟩],[.s 10 0]],[.s 6 4]⟩,
⟨-5,1,9,17,[[.f ⟨29,31,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨29,33,0,0,0,0,0,0,0⟩],[.s 21 0],[.f ⟨29,35,0,0,0,0,0,0,0⟩],[.s 11 0]],[.s 11 0]⟩,
⟨-5,1,10,15,[[.s 8 0],[.s 20 0],[.f ⟨29,34,0,0,0,0,0,0,0⟩],[.s 22 0],[.s 11 0]],[.s 20 4]⟩,
⟨-5,1,11,16,[[.s 9 0],[.s 21 0],[.s 10 0],[.f ⟨29,35,0,0,0,0,0,0,0⟩],[.s 23 0]],[.s 10 4]⟩,
⟨-4,1,0,10,[[.s 0 0],[.f ⟨8,0,0,0,0,0,0,0,0⟩],[.s 13 0],[.f ⟨10,3,0,0,0,0,0,0,0⟩]],[.f ⟨8,0,0,0,0,0,0,0,0⟩]⟩,
⟨-4,1,1,11,[[.s 12 0],[.s 1 0],[.f ⟨8,1,0,0,0,0,0,0,0⟩],[.s 14 0]],[.s 12 2]⟩,
⟨-4,1,2,12,[[.s 13 0],[.s 2 0],[.f ⟨8,2,0,0,0,0,0,0,0⟩],[.s 16 0]],[.s 13 3]⟩,
⟨-4,1,3,20,[[.f ⟨26,0,0,0,0,0,0,0,0⟩],[.s 3 0],[.f ⟨8,3,0,0,0,0,0,0,0⟩],[.s 17 0]],[.s 17 0]⟩,
⟨-4,1,4,13,[[.s 14 0],[.s 4 0],[.f ⟨8,4,0,0,0,0,0,0,0⟩],[.s 6 0],[.s 18 0]],[.s 14 3]⟩,
⟨-4,1,5,19,[[.s 15 0],[.s 5 0],[.f ⟨8,5,0,0,0,0,0,0,0⟩],[.s 7 0],[.s 19 0]],[.s 7 1]⟩,
⟨-4,1,6,13,[[.s 16 0],[.f ⟨8,4,0,0,0,0,0,0,0⟩],[.s 6 0],[.f ⟨8,6,0,0,0,0,0,0,0⟩],[.s 20 0],[.f ⟨8,8,0,0,0,0,0,0,0⟩]],[.f ⟨8,4,0,0,0,0,0,0,3⟩]⟩,
⟨-4,1,7,18,[[.s 17 0],[.f ⟨8,5,0,0,0,0,0,0,0⟩],[.s 7 0],[.f ⟨8,7,0,0,0,0,0,0,0⟩],[.s 21 0],[.f ⟨8,9,0,0,0,0,0,0,0⟩]],[.s 21 1]⟩,
⟨-4,1,8,14,[[.s 6 0],[.s 18 0],[.s 8 0],[.f ⟨8,8,0,0,0,0,0,0,0⟩],[.s 10 0],[.s 22 0]],[.s 18 4]⟩,
⟨-4,1,9,17,[[.s 7 0],[.s 19 0],[.s 9 0],[.f ⟨8,9,0,0,0,0,0,0,0⟩],[.s 11 0],[.s 23 0]],[.s 11 1]⟩,
⟨-4,1,10,15,[[.s 20 0],[.f ⟨8,8,0,0,0,0,0,0,0⟩],[.s 10 0],[.f ⟨8,10,0,0,0,0,0,0,0⟩],[.s 23 0]],[.s 20 5]⟩,
⟨-4,1,11,16,[[.s 21 0],[.f ⟨8,9,0,0,0,0,0,0,0⟩],[.s 22 0],[.s 11 0],[.f ⟨8,11,0,0,0,0,0,0,0⟩]],[.s 22 4]⟩]⟩,
⟨1,-6,2,0,0,[(0,3,4),(-2,-6,1),(2,6,-4)],0,3,4,6,0,0,0,0,24,0,0,0,
[⟨-11,3,0,35,[[.f ⟨30,24,0,0,0,0,0,0,0⟩,.f ⟨30,24,1,0,1,0,0,0,0⟩],[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨30,39,0,0,0,0,0,0,0⟩,.f ⟨30,39,1,0,1,0,0,0,0⟩]],[.s 12 0,.s 12 0]⟩,
⟨-11,3,1,36,[[.s 0 0,.s 0 0],[.f ⟨30,25,0,0,0,0,0,0,0⟩,.f ⟨30,25,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.s 2 0,.s 2 0]],[.s 0 2,.s 0 2]⟩,
⟨-11,3,2,37,[[.s 1 0,.s 1 0],[.f ⟨30,26,0,0,0,0,0,0,0⟩,.f ⟨30,26,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0],[.s 4 0,.s 4 0]],[.s 1 3,.s 1 3]⟩,
⟨-11,3,3,44,[[.f ⟨25,0,0,0,1,0,0,0,0⟩,.f ⟨25,0,1,0,2,0,0,0,0⟩],[.f ⟨30,27,0,0,0,0,0,0,0⟩,.f ⟨30,27,1,0,1,0,0,0,0⟩],[.s 15 0,.s 15 0],[.s 5 0,.s 5 0]],[.s 5 0,.s 5 0]⟩,
⟨-11,3,4,38,[[.s 2 0,.s 2 0],[.f ⟨30,28,0,0,0,0,0,0,0⟩,.f ⟨30,28,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0],[.f ⟨30,30,0,0,0,0,0,0,0⟩,.f ⟨30,30,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨-11,3,5,43,[[.s 3 0,.s 3 0],[.f ⟨30,29,0,0,0,0,0,0,0⟩,.f ⟨30,29,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0],[.f ⟨30,31,0,0,0,0,0,0,0⟩,.f ⟨30,31,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0]],[.f ⟨30,31,0,0,0,0,0,0,1⟩,.f ⟨30,31,1,0,1,0,0,0,1⟩]⟩,
⟨-11,3,6,38,[[.s 4 0,.s 4 0],[.s 16 0,.s 16 0],[.f ⟨30,30,0,0,0,0,0,0,0⟩,.f ⟨30,30,1,0,1,0,0,0,0⟩],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 20 0,.s 20 0]],[.s 16 3,.s 16 3]⟩,
⟨-11,3,7,42,[[.s 5 0,.s 5 0],[.s 17 0,.s 17 0],[.f ⟨30,31,0,0,0,0,0,0,0⟩,.f ⟨30,31,1,0,1,0,0,0,0⟩],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.s 9 1,.s 9 1]⟩,
⟨-11,3,8,39,[[.f ⟨30,30,0,0,0,0,0,0,0⟩,.f ⟨30,30,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.f ⟨30,32,0,0,0,0,0,0,0⟩,.f ⟨30,32,1,0,1,0,0,0,0⟩],[.s 20 0,.s 20 0],[.f ⟨30,34,0,0,0,0,0,0,0⟩,.f ⟨30,34,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0]],[.s 6 4,.s 6 4]⟩,
⟨-11,3,9,41,[[.f ⟨30,31,0,0,0,0,0,0,0⟩,.f ⟨30,31,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨30,33,0,0,0,0,0,0,0⟩,.f ⟨30,33,1,0,1,0,0,0,0⟩],[.s 21 0,.s 21 0],[.f ⟨30,35,0,0,0,0,0,0,0⟩,.f ⟨30,35,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0]],[.s 11 0,.s 11 0]⟩,
⟨-11,3,10,39,[[.s 8 0,.s 8 0],[.s 20 0,.s 20 0],[.f ⟨30,34,0,0,0,0,0,0,0⟩,.f ⟨30,34,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0]],[.s 20 4,.s 20 4]⟩,
⟨-11,3,11,40,[[.s 9 0,.s 9 0],[.s 21 0,.s 21 0],[.s 10 0,.s 10 0],[.f ⟨30,35,0,0,0,0,0,0,0⟩,.f ⟨30,35,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.s 10 4,.s 10 4]⟩,
⟨-10,3,0,34,[[.s 0 0,.s 0 0],[.f ⟨9,0,0,0,0,0,0,0,0⟩,.f ⟨9,0,1,0,1,0,0,0,0⟩],[.s 13 0,.s 13 0],[.f ⟨30,51,0,0,0,0,0,0,0⟩,.f ⟨30,51,1,0,1,0,0,0,0⟩]],[.f ⟨9,0,0,0,0,0,0,0,0⟩,.f ⟨9,0,1,0,1,0,0,0,0⟩]⟩,
⟨-10,3,1,35,[[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨9,1,0,0,0,0,0,0,0⟩,.f ⟨9,1,1,0,1,0,0,0,0⟩],[.s 14 0,.s 14 0]],[.s 12 2,.s 12 2]⟩,
⟨-10,3,2,36,[[.s 13 0,.s 13 0],[.s 2 0,.s 2 0],[.f ⟨9,2,0,0,0,0,0,0,0⟩,.f ⟨9,2,1,0,1,0,0,0,0⟩],[.s 16 0,.s 16 0]],[.s 13 3,.s 13 3]⟩,
⟨-10,3,3,44,[[.f ⟨26,0,0,0,0,0,0,1,0⟩,.f ⟨26,0,0,0,0,1,0,2,0⟩],[.s 3 0,.s 3 0],[.f ⟨9,3,0,0,0,0,0,0,0⟩,.f ⟨9,3,1,0,1,0,0,0,0⟩],[.s 17 0,.s 17 0]],[.s 17 0,.s 17 0]⟩,
⟨-10,3,4,37,[[.s 14 0,.s 14 0],[.s 4 0,.s 4 0],[.f ⟨9,4,0,0,0,0,0,0,0⟩,.f ⟨9,4,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.s 18 0,.s 18 0]],[.s 14 3,.s 14 3]⟩,
⟨-10,3,5,43,[[.s 15 0,.s 15 0],[.s 5 0,.s 5 0],[.f ⟨9,5,0,0,0,0,0,0,0⟩,.f ⟨9,5,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.s 19 0,.s 19 0]],[.s 7 1,.s 7 1]⟩,
⟨-10,3,6,37,[[.s 16 0,.s 16 0],[.f ⟨9,4,0,0,0,0,0,0,0⟩,.f ⟨9,4,1,0,1,0,0,0,0⟩],[.s 6 0,.s 6 0],[.f ⟨9,6,0,0,0,0,0,0,0⟩,.f ⟨9,6,1,0,1,0,0,0,0⟩],[.s 20 0,.s 20 0],[.f ⟨9,8,0,0,0,0,0,0,0⟩,.f ⟨9,8,1,0,1,0,0,0,0⟩]],[.f ⟨9,4,0,0,0,0,0,0,3⟩,.f ⟨9,4,1,0,1,0,0,0,3⟩]⟩,
⟨-10,3,7,42,[[.s 17 0,.s 17 0],[.f ⟨9,5,0,0,0,0,0,0,0⟩,.f ⟨9,5,1,0,1,0,0,0,0⟩],[.s 7 0,.s 7 0],[.f ⟨9,7,0,0,0,0,0,0,0⟩,.f ⟨9,7,1,0,1,0,0,0,0⟩],[.s 21 0,.s 21 0],[.f ⟨9,9,0,0,0,0,0,0,0⟩,.f ⟨9,9,1,0,1,0,0,0,0⟩]],[.s 21 1,.s 21 1]⟩,
⟨-10,3,8,38,[[.s 6 0,.s 6 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.f ⟨9,8,0,0,0,0,0,0,0⟩,.f ⟨9,8,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0],[.s 22 0,.s 22 0]],[.s 18 4,.s 18 4]⟩,
⟨-10,3,9,41,[[.s 7 0,.s 7 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.f ⟨9,9,0,0,0,0,0,0,0⟩,.f ⟨9,9,1,0,1,0,0,0,0⟩],[.s 11 0,.s 11 0],[.s 23 0,.s 23 0]],[.s 11 1,.s 11 1]⟩,
⟨-10,3,10,39,[[.s 20 0,.s 20 0],[.f ⟨9,8,0,0,0,0,0,0,0⟩,.f ⟨9,8,1,0,1,0,0,0,0⟩],[.s 10 0,.s 10 0],[.f ⟨9,10,0,0,0,0,0,0,0⟩,.f ⟨9,10,1,0,1,0,0,0,0⟩],[.s 23 0,.s 23 0]],[.s 20 5,.s 20 5]⟩,
⟨-10,3,11,40,[[.s 21 0,.s 21 0],[.f ⟨9,9,0,0,0,0,0,0,0⟩,.f ⟨9,9,1,0,1,0,0,0,0⟩],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0],[.f ⟨9,11,0,0,0,0,0,0,0⟩,.f ⟨9,11,1,0,1,0,0,0,0⟩]],[.s 22 4,.s 22 4]⟩,
⟨-8,2,0,23,[[.f ⟨30,60,0,0,0,0,0,0,0⟩,.f ⟨30,60,1,0,1,0,0,0,0⟩],[.s 36 0,.s 36 0],[.s 25 0,.s 25 0],[.f ⟨29,3,0,0,0,0,0,0,0⟩,.f ⟨30,3,1,0,0,0,0,0,0⟩]],[.s 36 0,.s 36 0]⟩,
⟨-8,2,1,24,[[.s 24 0,.s 24 0],[.f ⟨30,61,0,0,0,0,0,0,0⟩,.f ⟨30,61,1,0,1,0,0,0,0⟩],[.s 37 0,.s 37 0],[.s 26 0,.s 26 0]],[.s 24 2,.s 24 2]⟩,
⟨-8,2,2,25,[[.s 25 0,.s 25 0],[.f ⟨30,62,0,0,0,0,0,0,0⟩,.f ⟨30,62,1,0,1,0,0,0,0⟩],[.s 38 0,.s 38 0],[.s 28 0,.s 28 0]],[.s 25 3,.s 25 3]⟩,
⟨-8,2,3,32,[[.f ⟨25,12,0,0,1,0,0,0,0⟩,.f ⟨25,12,1,0,2,0,0,0,0⟩],[.f ⟨30,63,0,0,0,0,0,0,0⟩,.f ⟨30,63,1,0,1,0,0,0,0⟩],[.s 39 0,.s 39 0],[.s 29 0,.s 29 0]],[.s 29 0,.s 29 0]⟩,
⟨-8,2,4,26,[[.s 26 0,.s 26 0],[.f ⟨30,64,0,0,0,0,0,0,0⟩,.f ⟨30,64,1,0,1,0,0,0,0⟩],[.s 40 0,.s 40 0],[.f ⟨30,66,0,0,0,0,0,0,0⟩,.f ⟨30,66,1,0,1,0,0,0,0⟩],[.s 30 0,.s 30 0]],[.s 26 3,.s 26 3]⟩,
⟨-8,2,5,31,[[.s 27 0,.s 27 0],[.f ⟨30,65,0,0,0,0,0,0,0⟩,.f ⟨30,65,1,0,1,0,0,0,0⟩],[.s 41 0,.s 41 0],[.f ⟨30,67,0,0,0,0,0,0,0⟩,.f ⟨30,67,1,0,1,0,0,0,0⟩],[.s 31 0,.s 31 0]],[.f ⟨30,67,0,0,0,0,0,0,1⟩,.f ⟨30,67,1,0,1,0,0,0,1⟩]⟩,
⟨-8,2,6,26,[[.s 28 0,.s 28 0],[.s 40 0,.s 40 0],[.f ⟨30,66,0,0,0,0,0,0,0⟩,.f ⟨30,66,1,0,1,0,0,0,0⟩],[.s 42 0,.s 42 0],[.s 32 0,.s 32 0],[.s 44 0,.s 44 0]],[.s 40 3,.s 40 3]⟩,
⟨-8,2,7,30,[[.s 29 0,.s 29 0],[.s 41 0,.s 41 0],[.f ⟨30,67,0,0,0,0,0,0,0⟩,.f ⟨30,67,1,0,1,0,0,0,0⟩],[.s 43 0,.s 43 0],[.s 33 0,.s 33 0],[.s 45 0,.s 45 0]],[.s 33 1,.s 33 1]⟩,
⟨-8,2,8,27,[[.f ⟨30,66,0,0,0,0,0,0,0⟩,.f ⟨30,66,1,0,1,0,0,0,0⟩],[.s 30 0,.s 30 0],[.f ⟨30,68,0,0,0,0,0,0,0⟩,.f ⟨30,68,1,0,1,0,0,0,0⟩],[.s 44 0,.s 44 0],[.f ⟨30,70,0,0,0,0,0,0,0⟩,.f ⟨30,70,1,0,1,0,0,0,0⟩],[.s 34 0,.s 34 0]],[.s 30 4,.s 30 4]⟩,
⟨-8,2,9,29,[[.f ⟨30,67,0,0,0,0,0,0,0⟩,.f ⟨30,67,1,0,1,0,0,0,0⟩],[.s 31 0,.s 31 0],[.f ⟨30,69,0,0,0,0,0,0,0⟩,.f ⟨30,69,1,0,1,0,0,0,0⟩],[.s 45 0,.s 45 0],[.f ⟨30,71,0,0,0,0,0,0,0⟩,.f ⟨30,71,1,0,1,0,0,0,0⟩],[.s 35 0,.s 35 0]],[.s 35 0,.s 35 0]⟩,
⟨-8,2,10,27,[[.s 32 0,.s 32 0],[.s 44 0,.s 44 0],[.f ⟨30,70,0,0,0,0,0,0,0⟩,.f ⟨30,70,1,0,1,0,0,0,0⟩],[.s 46 0,.s 46 0],[.s 35 0,.s 35 0]],[.s 44 4,.s 44 4]⟩,
⟨-8,2,11,28,[[.s 33 0,.s 33 0],[.s 45 0,.s 45 0],[.s 34 0,.s 34 0],[.f ⟨30,71,0,0,0,0,0,0,0⟩,.f ⟨30,71,1,0,1,0,0,0,0⟩],[.s 47 0,.s 47 0]],[.s 34 4,.s 34 4]⟩,
⟨-7,2,0,22,[[.s 24 0,.s 24 0],[.f ⟨9,12,0,0,0,0,0,0,0⟩,.f ⟨9,12,1,0,1,0,0,0,0⟩],[.s 37 0,.s 37 0],[.f ⟨29,15,0,0,0,0,0,0,0⟩,.f ⟨30,15,1,0,0,0,0,0,0⟩]],[.f ⟨9,12,0,0,0,0,0,0,0⟩,.f ⟨9,12,1,0,1,0,0,0,0⟩]⟩,
⟨-7,2,1,23,[[.s 36 0,.s 36 0],[.s 25 0,.s 25 0],[.f ⟨9,13,0,0,0,0,0,0,0⟩,.f ⟨9,13,1,0,1,0,0,0,0⟩],[.s 38 0,.s 38 0]],[.s 36 2,.s 36 2]⟩,
⟨-7,2,2,24,[[.s 37 0,.s 37 0],[.s 26 0,.s 26 0],[.f ⟨9,14,0,0,0,0,0,0,0⟩,.f ⟨9,14,1,0,1,0,0,0,0⟩],[.s 40 0,.s 40 0]],[.s 37 3,.s 37 3]⟩,
⟨-7,2,3,32,[[.f ⟨26,72,0,0,0,0,0,1,0⟩,.f ⟨26,72,0,0,0,1,0,2,0⟩],[.s 27 0,.s 27 0],[.f ⟨9,15,0,0,0,0,0,0,0⟩,.f ⟨9,15,1,0,1,0,0,0,0⟩],[.s 41 0,.s 41 0]],[.s 41 0,.s 41 0]⟩,
⟨-7,2,4,25,[[.s 38 0,.s 38 0],[.s 28 0,.s 28 0],[.f ⟨9,16,0,0,0,0,0,0,0⟩,.f ⟨9,16,1,0,1,0,0,0,0⟩],[.s 30 0,.s 30 0],[.s 42 0,.s 42 0]],[.s 38 3,.s 38 3]⟩,
⟨-7,2,5,31,[[.s 39 0,.s 39 0],[.s 29 0,.s 29 0],[.f ⟨9,17,0,0,0,0,0,0,0⟩,.f ⟨9,17,1,0,1,0,0,0,0⟩],[.s 31 0,.s 31 0],[.s 43 0,.s 43 0]],[.s 31 1,.s 31 1]⟩,
⟨-7,2,6,25,[[.s 40 0,.s 40 0],[.f ⟨9,16,0,0,0,0,0,0,0⟩,.f ⟨9,16,1,0,1,0,0,0,0⟩],[.s 30 0,.s 30 0],[.f ⟨9,18,0,0,0,0,0,0,0⟩,.f ⟨9,18,1,0,1,0,0,0,0⟩],[.s 44 0,.s 44 0],[.f ⟨9,20,0,0,0,0,0,0,0⟩,.f ⟨9,20,1,0,1,0,0,0,0⟩]],[.f ⟨9,16,0,0,0,0,0,0,3⟩,.f ⟨9,16,1,0,1,0,0,0,3⟩]⟩,
⟨-7,2,7,30,[[.s 41 0,.s 41 0],[.f ⟨9,17,0,0,0,0,0,0,0⟩,.f ⟨9,17,1,0,1,0,0,0,0⟩],[.s 31 0,.s 31 0],[.f ⟨9,19,0,0,0,0,0,0,0⟩,.f ⟨9,19,1,0,1,0,0,0,0⟩],[.s 45 0,.s 45 0],[.f ⟨9,21,0,0,0,0,0,0,0⟩,.f ⟨9,21,1,0,1,0,0,0,0⟩]],[.s 45 1,.s 45 1]⟩,
⟨-7,2,8,26,[[.s 30 0,.s 30 0],[.s 42 0,.s 42 0],[.s 32 0,.s 32 0],[.f ⟨9,20,0,0,0,0,0,0,0⟩,.f ⟨9,20,1,0,1,0,0,0,0⟩],[.s 34 0,.s 34 0],[.s 46 0,.s 46 0]],[.s 42 4,.s 42 4]⟩,
⟨-7,2,9,29,[[.s 31 0,.s 31 0],[.s 43 0,.s 43 0],[.s 33 0,.s 33 0],[.f ⟨9,21,0,0,0,0,0,0,0⟩,.f ⟨9,21,1,0,1,0,0,0,0⟩],[.s 35 0,.s 35 0],[.s 47 0,.s 47 0]],[.s 35 1,.s 35 1]⟩,
⟨-7,2,10,27,[[.s 44 0,.s 44 0],[.f ⟨9,20,0,0,0,0,0,0,0⟩,.f ⟨9,20,1,0,1,0,0,0,0⟩],[.s 34 0,.s 34 0],[.f ⟨9,22,0,0,0,0,0,0,0⟩,.f ⟨9,22,1,0,1,0,0,0,0⟩],[.s 47 0,.s 47 0]],[.s 44 5,.s 44 5]⟩,
⟨-7,2,11,28,[[.s 45 0,.s 45 0],[.f ⟨9,21,0,0,0,0,0,0,0⟩,.f ⟨9,21,1,0,1,0,0,0,0⟩],[.s 46 0,.s 46 0],[.s 35 0,.s 35 0],[.f ⟨9,23,0,0,0,0,0,0,0⟩,.f ⟨9,23,1,0,1,0,0,0,0⟩]],[.s 46 4,.s 46 4]⟩]⟩,
⟨1,-3,0,0,0,[(-2,-6,5),(0,3,1),(0,-3,-3)],-2,-6,5,6,0,0,0,0,3,0,0,0,
[⟨-8,1,0,14,[[.s 24 0,.s 24 0],[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.f ⟨11,27,0,0,1,0,0,0,0⟩,.f ⟨11,27,1,0,2,0,0,0,0⟩]],[.s 12 0,.s 12 0]⟩,
⟨-8,1,1,15,[[.s 0 0,.s 0 0],[.s 25 0,.s 25 0],[.s 13 0,.s 13 0],[.s 2 0,.s 2 0]],[.s 0 2,.s 0 2]⟩,
⟨-8,1,2,16,[[.s 1 0,.s 1 0],[.s 26 0,.s 26 0],[.s 14 0,.s 14 0],[.s 4 0,.s 4 0]],[.s 1 3,.s 1 3]⟩,
⟨-8,1,3,22,[[.f ⟨28,24,0,0,0,0,0,0,0⟩,.f ⟨30,36,0,0,0,1,0,0,0⟩],[.s 27 0,.s 27 0],[.s 15 0,.s 15 0],[.s 5 0,.s 5 0]],[.s 15 1,.s 15 1]⟩,
⟨-8,1,4,17,[[.s 2 0,.s 2 0],[.s 28 0,.s 28 0],[.s 16 0,.s 16 0],[.s 30 0,.s 30 0],[.s 6 0,.s 6 0]],[.s 2 3,.s 2 3]⟩,
⟨-8,1,5,21,[[.s 3 0,.s 3 0],[.s 29 0,.s 29 0],[.s 17 0,.s 17 0],[.s 31 0,.s 31 0],[.s 7 0,.s 7 0]],[.s 17 1,.s 17 1]⟩,
⟨-8,1,6,17,[[.s 4 0,.s 4 0],[.s 16 0,.s 16 0],[.s 30 0,.s 30 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 20 0,.s 20 0]],[.s 16 3,.s 16 3]⟩,
⟨-8,1,7,20,[[.s 5 0,.s 5 0],[.s 17 0,.s 17 0],[.s 31 0,.s 31 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 21 0,.s 21 0]],[.s 19 2,.s 19 2]⟩,
⟨-8,1,8,18,[[.s 30 0,.s 30 0],[.s 6 0,.s 6 0],[.s 32 0,.s 32 0],[.s 20 0,.s 20 0],[.s 34 0,.s 34 0],[.s 10 0,.s 10 0]],[.s 6 4,.s 6 4]⟩,
⟨-8,1,9,20,[[.s 31 0,.s 31 0],[.s 7 0,.s 7 0],[.s 33 0,.s 33 0],[.s 21 0,.s 21 0],[.s 35 0,.s 35 0],[.s 11 0,.s 11 0]],[.s 21 2,.s 21 2]⟩,
⟨-8,1,10,18,[[.s 8 0,.s 8 0],[.s 20 0,.s 20 0],[.s 34 0,.s 34 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0]],[.s 20 4,.s 20 4]⟩,
⟨-8,1,11,19,[[.s 9 0,.s 9 0],[.s 21 0,.s 21 0],[.s 10 0,.s 10 0],[.s 35 0,.s 35 0],[.s 23 0,.s 23 0]],[.s 10 4,.s 10 4]⟩,
⟨-7,1,0,13,[[.s 0 0,.s 0 0],[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.f ⟨11,3,0,0,0,0,0,0,0⟩,.f ⟨11,3,1,0,1,0,0,0,0⟩]],[.s 24 0,.s 24 0]⟩,
⟨-7,1,1,14,[[.s 12 0,.s 12 0],[.s 1 0,.s 1 0],[.s 25 0,.s 25 0],[.s 14 0,.s 14 0]],[.s 12 2,.s 12 2]⟩,
⟨-7,1,2,15,[[.s 13 0,.s 13 0],[.s 2 0,.s 2 0],[.s 26 0,.s 26 0],[.s 16 0,.s 16 0]],[.s 13 3,.s 13 3]⟩,
⟨-7,1,3,21,[[.f ⟨28,36,0,0,0,0,0,0,0⟩,.f ⟨30,48,0,0,0,1,0,0,0⟩],[.s 3 0,.s 3 0],[.s 27 0,.s 27 0],[.s 17 0,.s 17 0]],[.s 27 1,.s 27 1]⟩,
⟨-7,1,4,16,[[.s 14 0,.s 14 0],[.s 4 0,.s 4 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 18 0,.s 18 0]],[.s 14 3,.s 14 3]⟩,
⟨-7,1,5,20,[[.s 15 0,.s 15 0],[.s 5 0,.s 5 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 19 0,.s 19 0]],[.s 29 1,.s 29 1]⟩,
⟨-7,1,6,16,[[.s 16 0,.s 16 0],[.s 28 0,.s 28 0],[.s 6 0,.s 6 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.s 32 0,.s 32 0]],[.s 28 3,.s 28 3]⟩,
⟨-7,1,7,19,[[.s 17 0,.s 17 0],[.s 29 0,.s 29 0],[.s 7 0,.s 7 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.s 33 0,.s 33 0]],[.s 31 2,.s 31 2]⟩,
⟨-7,1,8,17,[[.s 6 0,.s 6 0],[.s 18 0,.s 18 0],[.s 8 0,.s 8 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 22 0,.s 22 0]],[.s 18 4,.s 18 4]⟩,
⟨-7,1,9,19,[[.s 7 0,.s 7 0],[.s 19 0,.s 19 0],[.s 9 0,.s 9 0],[.s 33 0,.s 33 0],[.s 11 0,.s 11 0],[.s 23 0,.s 23 0]],[.s 33 2,.s 33 2]⟩,
⟨-7,1,10,17,[[.s 20 0,.s 20 0],[.s 32 0,.s 32 0],[.s 10 0,.s 10 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0]],[.s 32 4,.s 32 4]⟩,
⟨-7,1,11,18,[[.s 21 0,.s 21 0],[.s 33 0,.s 33 0],[.s 22 0,.s 22 0],[.s 11 0,.s 11 0],[.s 35 0,.s 35 0]],[.s 22 4,.s 22 4]⟩,
⟨-6,1,0,12,[[.s 12 0,.s 12 0],[.f ⟨27,0,0,0,0,0,0,0,0⟩,.s 0 0],[.s 25 0,.s 25 0],[.f ⟨11,15,0,0,0,0,0,0,0⟩,.f ⟨11,15,1,0,1,0,0,0,0⟩]],[.f ⟨27,0,0,0,0,0,0,0,0⟩,.s 0 0]⟩,
⟨-6,1,1,13,[[.s 24 0,.s 24 0],[.s 13 0,.s 13 0],[.f ⟨27,1,0,0,0,0,0,0,0⟩,.s 1 0],[.s 26 0,.s 26 0]],[.s 24 2,.s 24 2]⟩,
⟨-6,1,2,14,[[.s 25 0,.s 25 0],[.s 14 0,.s 14 0],[.f ⟨27,2,0,0,0,0,0,0,0⟩,.s 2 0],[.s 28 0,.s 28 0]],[.s 25 3,.s 25 3]⟩,
⟨-6,1,3,20,[[.f ⟨9,12,0,0,0,0,0,0,0⟩,.f ⟨30,60,0,0,0,1,0,0,0⟩],[.s 15 0,.s 15 0],[.f ⟨27,3,0,0,0,0,0,0,0⟩,.s 3 0],[.s 29 0,.s 29 0]],[.s 29 0,.s 3 1]⟩,
⟨-6,1,4,15,[[.s 26 0,.s 26 0],[.s 16 0,.s 16 0],[.f ⟨27,4,0,0,0,0,0,0,0⟩,.s 4 0],[.s 18 0,.s 18 0],[.s 30 0,.s 30 0]],[.s 26 3,.s 26 3]⟩,
⟨-6,1,5,19,[[.s 27 0,.s 27 0],[.s 17 0,.s 17 0],[.f ⟨27,5,0,0,0,0,0,0,0⟩,.s 5 0],[.s 19 0,.s 19 0],[.s 31 0,.s 31 0]],[.s 31 0,.s 5 1]⟩,
⟨-6,1,6,15,[[.s 28 0,.s 28 0],[.f ⟨27,4,0,0,0,0,0,0,0⟩,.s 4 0],[.s 18 0,.s 18 0],[.f ⟨27,6,0,0,0,0,0,0,0⟩,.s 6 0],[.s 32 0,.s 32 0],[.f ⟨27,8,0,0,0,0,0,0,0⟩,.s 8 0]],[.f ⟨27,4,0,0,0,0,0,0,3⟩,.s 4 3]⟩,
⟨-6,1,7,18,[[.s 29 0,.s 29 0],[.f ⟨27,5,0,0,0,0,0,0,0⟩,.s 5 0],[.s 19 0,.s 19 0],[.f ⟨27,7,0,0,0,0,0,0,0⟩,.s 7 0],[.s 33 0,.s 33 0],[.f ⟨27,9,0,0,0,0,0,0,0⟩,.s 9 0]],[.f ⟨27,9,0,0,0,0,0,0,0⟩,.s 7 2]⟩,
⟨-6,1,8,16,[[.s 18 0,.s 18 0],[.s 30 0,.s 30 0],[.s 20 0,.s 20 0],[.f ⟨27,8,0,0,0,0,0,0,0⟩,.s 8 0],[.s 22 0,.s 22 0],[.s 34 0,.s 34 0]],[.s 30 4,.s 30 4]⟩,
⟨-6,1,9,18,[[.s 19 0,.s 19 0],[.s 31 0,.s 31 0],[.s 21 0,.s 21 0],[.f ⟨27,9,0,0,0,0,0,0,0⟩,.s 9 0],[.s 23 0,.s 23 0],[.s 35 0,.s 35 0]],[.f ⟨27,9,0,0,0,0,0,0,2⟩,.s 9 2]⟩,
⟨-6,1,10,16,[[.s 32 0,.s 32 0],[.f ⟨27,8,0,0,0,0,0,0,0⟩,.s 8 0],[.s 22 0,.s 22 0],[.f ⟨27,10,0,0,0,0,0,0,0⟩,.s 10 0],[.s 35 0,.s 35 0]],[.f ⟨27,8,0,0,0,0,0,0,4⟩,.s 8 4]⟩,
⟨-6,1,11,17,[[.s 33 0,.s 33 0],[.f ⟨27,9,0,0,0,0,0,0,0⟩,.s 9 0],[.s 34 0,.s 34 0],[.s 23 0,.s 23 0],[.f ⟨27,11,0,0,0,0,0,0,0⟩,.s 11 0]],[.s 34 4,.s 34 4]⟩]⟩,
⟨2,-6,2,-3,0,[(0,3,4),(-2,-6,5)],0,3,4,6,-2,-6,5,6,24,3,1,8,
[⟨-14,3,0,38,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0]],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]⟩,
⟨-14,3,1,39,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 0 2,.s 0 2,.s 0 2,.s 0 2]⟩,
⟨-14,3,2,40,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 1 3,.s 1 3,.s 1 3,.s 1 3]⟩,
⟨-14,3,3,46,[[.f ⟨28,24,0,0,1,0,0,0,0⟩,.f ⟨28,24,1,0,2,0,0,0,0⟩,.s 36 0,.s 36 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.s 15 1,.s 15 1,.s 15 1,.s 15 1]⟩,
⟨-14,3,4,41,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 2 3,.s 2 3,.s 2 3,.s 2 3]⟩,
⟨-14,3,5,45,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.s 17 1,.s 17 1,.s 17 1,.s 17 1]⟩,
⟨-14,3,6,41,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 16 3,.s 16 3,.s 16 3,.s 16 3]⟩,
⟨-14,3,7,44,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 19 2,.s 19 2,.s 19 2,.s 19 2]⟩,
⟨-14,3,8,42,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.s 6 4,.s 6 4,.s 6 4,.s 6 4]⟩,
⟨-14,3,9,44,[[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 21 2,.s 21 2,.s 21 2,.s 21 2]⟩,
⟨-14,3,10,42,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 20 4,.s 20 4,.s 20 4,.s 20 4]⟩,
⟨-14,3,11,43,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 10 4,.s 10 4,.s 10 4,.s 10 4]⟩,
⟨-13,3,0,37,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0]],[.s 24 0,.s 24 0,.s 24 0,.s 24 0]⟩,
⟨-13,3,1,38,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 12 2,.s 12 2,.s 12 2,.s 12 2]⟩,
⟨-13,3,2,39,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 13 3,.s 13 3,.s 13 3,.s 13 3]⟩,
⟨-13,3,3,45,[[.f ⟨28,36,0,0,1,0,0,0,0⟩,.f ⟨28,36,1,0,2,0,0,0,0⟩,.s 48 0,.s 48 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.s 27 1,.s 27 1,.s 27 1,.s 27 1]⟩,
⟨-13,3,4,40,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0]],[.s 14 3,.s 14 3,.s 14 3,.s 14 3]⟩,
⟨-13,3,5,44,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0]],[.s 29 1,.s 29 1,.s 29 1,.s 29 1]⟩,
⟨-13,3,6,40,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 28 3,.s 28 3,.s 28 3,.s 28 3]⟩,
⟨-13,3,7,43,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.s 31 2,.s 31 2,.s 31 2,.s 31 2]⟩,
⟨-13,3,8,41,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.s 18 4,.s 18 4,.s 18 4,.s 18 4]⟩,
⟨-13,3,9,43,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 33 2,.s 33 2,.s 33 2,.s 33 2]⟩,
⟨-13,3,10,41,[[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 32 4,.s 32 4,.s 32 4,.s 32 4]⟩,
⟨-13,3,11,42,[[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 22 4,.s 22 4,.s 22 4,.s 22 4]⟩,
⟨-12,3,0,36,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.f ⟨28,0,0,0,0,0,0,0,0⟩,.f ⟨28,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0]],[.f ⟨28,0,0,0,0,0,0,0,0⟩,.f ⟨28,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0]⟩,
⟨-12,3,1,37,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.f ⟨28,1,0,0,0,0,0,0,0⟩,.f ⟨28,1,1,0,1,0,0,0,0⟩,.s 1 0,.s 1 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.s 24 2,.s 24 2,.s 24 2,.s 24 2]⟩,
⟨-12,3,2,38,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.f ⟨28,2,0,0,0,0,0,0,0⟩,.f ⟨28,2,1,0,1,0,0,0,0⟩,.s 2 0,.s 2 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.s 25 3,.s 25 3,.s 25 3,.s 25 3]⟩,
⟨-12,3,3,44,[[.f ⟨9,12,0,0,1,0,0,0,0⟩,.f ⟨9,12,1,0,2,0,0,0,0⟩,.s 60 0,.s 60 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.f ⟨28,3,0,0,0,0,0,0,0⟩,.f ⟨28,3,1,0,1,0,0,0,0⟩,.s 3 0,.s 3 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0]],[.s 29 0,.s 29 0,.s 3 1,.s 3 1]⟩,
⟨-12,3,4,39,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨28,4,0,0,0,0,0,0,0⟩,.f ⟨28,4,1,0,1,0,0,0,0⟩,.s 4 0,.s 4 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0]],[.s 26 3,.s 26 3,.s 26 3,.s 26 3]⟩,
⟨-12,3,5,43,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨28,5,0,0,0,0,0,0,0⟩,.f ⟨28,5,1,0,1,0,0,0,0⟩,.s 5 0,.s 5 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 31 0,.s 31 0,.s 5 1,.s 5 1]⟩,
⟨-12,3,6,39,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.f ⟨28,4,0,0,0,0,0,0,0⟩,.f ⟨28,4,1,0,1,0,0,0,0⟩,.s 4 0,.s 4 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.f ⟨28,6,0,0,0,0,0,0,0⟩,.f ⟨28,6,1,0,1,0,0,0,0⟩,.s 6 0,.s 6 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.f ⟨28,8,0,0,0,0,0,0,0⟩,.f ⟨28,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0]],[.f ⟨28,4,0,0,0,0,0,0,3⟩,.f ⟨28,4,1,0,1,0,0,0,3⟩,.s 4 3,.s 4 3]⟩,
⟨-12,3,7,42,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.f ⟨28,5,0,0,0,0,0,0,0⟩,.f ⟨28,5,1,0,1,0,0,0,0⟩,.s 5 0,.s 5 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.f ⟨28,7,0,0,0,0,0,0,0⟩,.f ⟨28,7,1,0,1,0,0,0,0⟩,.s 7 0,.s 7 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.f ⟨28,9,0,0,0,0,0,0,0⟩,.f ⟨28,9,1,0,1,0,0,0,0⟩,.s 9 0,.s 9 0]],[.f ⟨28,9,0,0,0,0,0,0,0⟩,.f ⟨28,9,1,0,1,0,0,0,0⟩,.s 7 2,.s 7 2]⟩,
⟨-12,3,8,40,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨28,8,0,0,0,0,0,0,0⟩,.f ⟨28,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.s 30 4,.s 30 4,.s 30 4,.s 30 4]⟩,
⟨-12,3,9,42,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.f ⟨28,9,0,0,0,0,0,0,0⟩,.f ⟨28,9,1,0,1,0,0,0,0⟩,.s 9 0,.s 9 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.f ⟨28,9,0,0,0,0,0,0,2⟩,.f ⟨28,9,1,0,1,0,0,0,2⟩,.s 9 2,.s 9 2]⟩,
⟨-12,3,10,40,[[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.f ⟨28,8,0,0,0,0,0,0,0⟩,.f ⟨28,8,1,0,1,0,0,0,0⟩,.s 8 0,.s 8 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.f ⟨28,10,0,0,0,0,0,0,0⟩,.f ⟨28,10,1,0,1,0,0,0,0⟩,.s 10 0,.s 10 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.f ⟨28,8,0,0,0,0,0,0,4⟩,.f ⟨28,8,1,0,1,0,0,0,4⟩,.s 8 4,.s 8 4]⟩,
⟨-12,3,11,41,[[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.f ⟨28,9,0,0,0,0,0,0,0⟩,.f ⟨28,9,1,0,1,0,0,0,0⟩,.s 9 0,.s 9 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.f ⟨28,11,0,0,0,0,0,0,0⟩,.f ⟨28,11,1,0,1,0,0,0,0⟩,.s 11 0,.s 11 0]],[.s 34 4,.s 34 4,.s 34 4,.s 34 4]⟩,
⟨-11,2,0,26,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.f ⟨29,3,0,0,1,0,0,0,0⟩,.s 3 0,.f ⟨29,3,0,1,2,0,0,0,0⟩,.s 3 0]],[.s 48 0,.s 48 0,.s 48 0,.s 48 0]⟩,
⟨-11,2,1,27,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0]],[.s 36 2,.s 36 2,.s 36 2,.s 36 2]⟩,
⟨-11,2,2,28,[[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0]],[.s 37 3,.s 37 3,.s 37 3,.s 37 3]⟩,
⟨-11,2,3,34,[[.f ⟨28,0,0,0,0,0,0,0,0⟩,.f ⟨28,0,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0]],[.s 51 1,.s 51 1,.s 51 1,.s 51 1]⟩,
⟨-11,2,4,29,[[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0]],[.s 38 3,.s 38 3,.s 38 3,.s 38 3]⟩,
⟨-11,2,5,33,[[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0]],[.s 53 1,.s 53 1,.s 53 1,.s 53 1]⟩,
⟨-11,2,6,29,[[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0]],[.s 52 3,.s 52 3,.s 52 3,.s 52 3]⟩,
⟨-11,2,7,32,[[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0]],[.s 55 2,.s 55 2,.s 55 2,.s 55 2]⟩,
⟨-11,2,8,30,[[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0]],[.s 42 4,.s 42 4,.s 42 4,.s 42 4]⟩,
⟨-11,2,9,32,[[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 57 2,.s 57 2,.s 57 2,.s 57 2]⟩,
⟨-11,2,10,30,[[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0]],[.s 56 4,.s 56 4,.s 56 4,.s 56 4]⟩,
⟨-11,2,11,31,[[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 46 4,.s 46 4,.s 46 4,.s 46 4]⟩,
⟨-10,2,0,25,[[.s 36 0,.s 36 0,.s 36 0,.s 36 0],[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.f ⟨29,15,0,0,1,0,0,0,0⟩,.s 15 0,.f ⟨29,15,0,1,2,0,0,0,0⟩,.s 15 0]],[.s 60 0,.s 60 0,.s 60 0,.s 60 0]⟩,
⟨-10,2,1,26,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.s 37 0,.s 37 0,.s 37 0,.s 37 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0]],[.s 48 2,.s 48 2,.s 48 2,.s 48 2]⟩,
⟨-10,2,2,27,[[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.s 38 0,.s 38 0,.s 38 0,.s 38 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0]],[.s 49 3,.s 49 3,.s 49 3,.s 49 3]⟩,
⟨-10,2,3,33,[[.f ⟨28,12,0,0,0,0,0,0,0⟩,.f ⟨28,12,1,0,1,0,0,0,0⟩,.s 12 0,.s 12 0],[.s 39 0,.s 39 0,.s 39 0,.s 39 0],[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0]],[.s 63 1,.s 63 1,.s 63 1,.s 63 1]⟩,
⟨-10,2,4,28,[[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.s 40 0,.s 40 0,.s 40 0,.s 40 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0]],[.s 50 3,.s 50 3,.s 50 3,.s 50 3]⟩,
⟨-10,2,5,32,[[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.s 41 0,.s 41 0,.s 41 0,.s 41 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0]],[.s 65 1,.s 65 1,.s 65 1,.s 65 1]⟩,
⟨-10,2,6,28,[[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0]],[.s 64 3,.s 64 3,.s 64 3,.s 64 3]⟩,
⟨-10,2,7,31,[[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0]],[.s 67 2,.s 67 2,.s 67 2,.s 67 2]⟩,
⟨-10,2,8,29,[[.s 42 0,.s 42 0,.s 42 0,.s 42 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 44 0,.s 44 0,.s 44 0,.s 44 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0]],[.s 54 4,.s 54 4,.s 54 4,.s 54 4]⟩,
⟨-10,2,9,31,[[.s 43 0,.s 43 0,.s 43 0,.s 43 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 45 0,.s 45 0,.s 45 0,.s 45 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 69 2,.s 69 2,.s 69 2,.s 69 2]⟩,
⟨-10,2,10,29,[[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.s 46 0,.s 46 0,.s 46 0,.s 46 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0]],[.s 68 4,.s 68 4,.s 68 4,.s 68 4]⟩,
⟨-10,2,11,30,[[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 47 0,.s 47 0,.s 47 0,.s 47 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.s 58 4,.s 58 4,.s 58 4,.s 58 4]⟩,
⟨-9,2,0,24,[[.s 48 0,.s 48 0,.s 48 0,.s 48 0],[.f ⟨28,24,0,0,0,0,0,0,0⟩,.f ⟨28,24,1,0,1,0,0,0,0⟩,.s 36 0,.s 36 0],[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.f ⟨29,27,0,0,1,0,0,0,0⟩,.s 27 0,.f ⟨29,27,0,1,2,0,0,0,0⟩,.s 27 0]],[.f ⟨28,24,0,0,0,0,0,0,0⟩,.f ⟨28,24,1,0,1,0,0,0,0⟩,.s 36 0,.s 36 0]⟩,
⟨-9,2,1,25,[[.s 60 0,.s 60 0,.s 60 0,.s 60 0],[.s 49 0,.s 49 0,.s 49 0,.s 49 0],[.f ⟨28,25,0,0,0,0,0,0,0⟩,.f ⟨28,25,1,0,1,0,0,0,0⟩,.s 37 0,.s 37 0],[.s 62 0,.s 62 0,.s 62 0,.s 62 0]],[.s 60 2,.s 60 2,.s 60 2,.s 60 2]⟩,
⟨-9,2,2,26,[[.s 61 0,.s 61 0,.s 61 0,.s 61 0],[.s 50 0,.s 50 0,.s 50 0,.s 50 0],[.f ⟨28,26,0,0,0,0,0,0,0⟩,.f ⟨28,26,1,0,1,0,0,0,0⟩,.s 38 0,.s 38 0],[.s 64 0,.s 64 0,.s 64 0,.s 64 0]],[.s 61 3,.s 61 3,.s 61 3,.s 61 3]⟩,
⟨-9,2,3,32,[[.f ⟨9,0,0,0,0,0,0,0,0⟩,.f ⟨9,0,1,0,1,0,0,0,0⟩,.s 24 0,.s 24 0],[.s 51 0,.s 51 0,.s 51 0,.s 51 0],[.f ⟨28,27,0,0,0,0,0,0,0⟩,.f ⟨28,27,1,0,1,0,0,0,0⟩,.s 39 0,.s 39 0],[.s 65 0,.s 65 0,.s 65 0,.s 65 0]],[.s 65 0,.s 65 0,.s 39 1,.s 39 1]⟩,
⟨-9,2,4,27,[[.s 62 0,.s 62 0,.s 62 0,.s 62 0],[.s 52 0,.s 52 0,.s 52 0,.s 52 0],[.f ⟨28,28,0,0,0,0,0,0,0⟩,.f ⟨28,28,1,0,1,0,0,0,0⟩,.s 40 0,.s 40 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0]],[.s 62 3,.s 62 3,.s 62 3,.s 62 3]⟩,
⟨-9,2,5,31,[[.s 63 0,.s 63 0,.s 63 0,.s 63 0],[.s 53 0,.s 53 0,.s 53 0,.s 53 0],[.f ⟨28,29,0,0,0,0,0,0,0⟩,.f ⟨28,29,1,0,1,0,0,0,0⟩,.s 41 0,.s 41 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0]],[.s 67 0,.s 67 0,.s 41 1,.s 41 1]⟩,
⟨-9,2,6,27,[[.s 64 0,.s 64 0,.s 64 0,.s 64 0],[.f ⟨28,28,0,0,0,0,0,0,0⟩,.f ⟨28,28,1,0,1,0,0,0,0⟩,.s 40 0,.s 40 0],[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.f ⟨28,30,0,0,0,0,0,0,0⟩,.f ⟨28,30,1,0,1,0,0,0,0⟩,.s 42 0,.s 42 0],[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.f ⟨28,32,0,0,0,0,0,0,0⟩,.f ⟨28,32,1,0,1,0,0,0,0⟩,.s 44 0,.s 44 0]],[.f ⟨28,28,0,0,0,0,0,0,3⟩,.f ⟨28,28,1,0,1,0,0,0,3⟩,.s 40 3,.s 40 3]⟩,
⟨-9,2,7,30,[[.s 65 0,.s 65 0,.s 65 0,.s 65 0],[.f ⟨28,29,0,0,0,0,0,0,0⟩,.f ⟨28,29,1,0,1,0,0,0,0⟩,.s 41 0,.s 41 0],[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.f ⟨28,31,0,0,0,0,0,0,0⟩,.f ⟨28,31,1,0,1,0,0,0,0⟩,.s 43 0,.s 43 0],[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.f ⟨28,33,0,0,0,0,0,0,0⟩,.f ⟨28,33,1,0,1,0,0,0,0⟩,.s 45 0,.s 45 0]],[.f ⟨28,33,0,0,0,0,0,0,0⟩,.f ⟨28,33,1,0,1,0,0,0,0⟩,.s 43 2,.s 43 2]⟩,
⟨-9,2,8,28,[[.s 54 0,.s 54 0,.s 54 0,.s 54 0],[.s 66 0,.s 66 0,.s 66 0,.s 66 0],[.s 56 0,.s 56 0,.s 56 0,.s 56 0],[.f ⟨28,32,0,0,0,0,0,0,0⟩,.f ⟨28,32,1,0,1,0,0,0,0⟩,.s 44 0,.s 44 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0]],[.s 66 4,.s 66 4,.s 66 4,.s 66 4]⟩,
⟨-9,2,9,30,[[.s 55 0,.s 55 0,.s 55 0,.s 55 0],[.s 67 0,.s 67 0,.s 67 0,.s 67 0],[.s 57 0,.s 57 0,.s 57 0,.s 57 0],[.f ⟨28,33,0,0,0,0,0,0,0⟩,.f ⟨28,33,1,0,1,0,0,0,0⟩,.s 45 0,.s 45 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.f ⟨28,33,0,0,0,0,0,0,2⟩,.f ⟨28,33,1,0,1,0,0,0,2⟩,.s 45 2,.s 45 2]⟩,
⟨-9,2,10,28,[[.s 68 0,.s 68 0,.s 68 0,.s 68 0],[.f ⟨28,32,0,0,0,0,0,0,0⟩,.f ⟨28,32,1,0,1,0,0,0,0⟩,.s 44 0,.s 44 0],[.s 58 0,.s 58 0,.s 58 0,.s 58 0],[.f ⟨28,34,0,0,0,0,0,0,0⟩,.f ⟨28,34,1,0,1,0,0,0,0⟩,.s 46 0,.s 46 0],[.s 71 0,.s 71 0,.s 71 0,.s 71 0]],[.f ⟨28,32,0,0,0,0,0,0,4⟩,.f ⟨28,32,1,0,1,0,0,0,4⟩,.s 44 4,.s 44 4]⟩,
⟨-9,2,11,29,[[.s 69 0,.s 69 0,.s 69 0,.s 69 0],[.f ⟨28,33,0,0,0,0,0,0,0⟩,.f ⟨28,33,1,0,1,0,0,0,0⟩,.s 45 0,.s 45 0],[.s 70 0,.s 70 0,.s 70 0,.s 70 0],[.s 59 0,.s 59 0,.s 59 0,.s 59 0],[.f ⟨28,35,0,0,0,0,0,0,0⟩,.f ⟨28,35,1,0,1,0,0,0,0⟩,.s 47 0,.s 47 0]],[.s 70 4,.s 70 4,.s 70 4,.s 70 4]⟩]⟩,
⟨2,-3,0,-3,-1,[(-1,3,1),(0,-3,1)],-1,3,1,3,0,-3,1,3,3,12,4,1,
[⟨-6,-1,0,18,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.f ⟨1,3,0,0,1,0,0,0,0⟩,.s 3 0,.f ⟨1,3,0,1,2,0,0,0,0⟩,.s 3 0]],[.s 12 0,.s 12 0,.s 12 0,.s 12 0]⟩,
⟨-6,-1,1,17,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0]],[.s 13 1,.s 13 1,.s 13 1,.s 13 1]⟩,
⟨-6,-1,2,16,[[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0]],[.s 14 1,.s 14 1,.s 14 1,.s 14 1]⟩,
⟨-6,-1,3,10,[[.f ⟨11,12,0,0,0,0,0,0,0⟩,.f ⟨11,12,1,0,1,0,0,0,0⟩,.s 0 0,.s 0 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0]],[.f ⟨11,12,0,0,0,0,0,0,3⟩,.f ⟨11,12,1,0,1,0,0,0,3⟩,.s 0 3,.s 0 3]⟩,
⟨-6,-1,4,15,[[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0]],[.s 16 1,.s 16 1,.s 16 1,.s 16 1]⟩,
⟨-6,-1,5,11,[[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0]],[.s 3 3,.s 3 3,.s 3 3,.s 3 3]⟩,
⟨-6,-1,6,14,[[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0]],[.s 18 2,.s 18 2,.s 18 2,.s 18 2]⟩,
⟨-6,-1,7,11,[[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0]],[.s 17 3,.s 17 3,.s 17 3,.s 17 3]⟩,
⟨-6,-1,8,14,[[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0]],[.s 20 2,.s 20 2,.s 20 2,.s 20 2]⟩,
⟨-6,-1,9,12,[[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 7 4,.s 7 4,.s 7 4,.s 7 4]⟩,
⟨-6,-1,10,13,[[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0]],[.s 22 2,.s 22 2,.s 22 2,.s 22 2]⟩,
⟨-6,-1,11,12,[[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 21 4,.s 21 4,.s 21 4,.s 21 4]⟩,
⟨-5,-1,0,17,[[.s 0 0,.s 0 0,.s 0 0,.s 0 0],[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.f ⟨13,15,0,0,1,0,0,0,0⟩,.s 15 0,.f ⟨13,15,0,1,2,0,0,0,0⟩,.s 15 0]],[.s 24 0,.s 24 0,.s 24 0,.s 24 0]⟩,
⟨-5,-1,1,16,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.s 1 0,.s 1 0,.s 1 0,.s 1 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0]],[.s 25 1,.s 25 1,.s 25 1,.s 25 1]⟩,
⟨-5,-1,2,15,[[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.s 2 0,.s 2 0,.s 2 0,.s 2 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0]],[.s 26 1,.s 26 1,.s 26 1,.s 26 1]⟩,
⟨-5,-1,3,9,[[.f ⟨11,24,0,0,0,0,0,0,0⟩,.f ⟨11,24,1,0,1,0,0,0,0⟩,.s 12 0,.s 12 0],[.s 3 0,.s 3 0,.s 3 0,.s 3 0],[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0]],[.f ⟨11,24,0,0,0,0,0,0,3⟩,.f ⟨11,24,1,0,1,0,0,0,3⟩,.s 12 3,.s 12 3]⟩,
⟨-5,-1,4,14,[[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.s 4 0,.s 4 0,.s 4 0,.s 4 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0]],[.s 28 1,.s 28 1,.s 28 1,.s 28 1]⟩,
⟨-5,-1,5,10,[[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.s 5 0,.s 5 0,.s 5 0,.s 5 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0]],[.s 15 3,.s 15 3,.s 15 3,.s 15 3]⟩,
⟨-5,-1,6,13,[[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0]],[.s 30 2,.s 30 2,.s 30 2,.s 30 2]⟩,
⟨-5,-1,7,10,[[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0]],[.s 29 3,.s 29 3,.s 29 3,.s 29 3]⟩,
⟨-5,-1,8,13,[[.s 6 0,.s 6 0,.s 6 0,.s 6 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 8 0,.s 8 0,.s 8 0,.s 8 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0]],[.s 32 2,.s 32 2,.s 32 2,.s 32 2]⟩,
⟨-5,-1,9,11,[[.s 7 0,.s 7 0,.s 7 0,.s 7 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 9 0,.s 9 0,.s 9 0,.s 9 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 19 4,.s 19 4,.s 19 4,.s 19 4]⟩,
⟨-5,-1,10,12,[[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.s 10 0,.s 10 0,.s 10 0,.s 10 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0]],[.s 34 2,.s 34 2,.s 34 2,.s 34 2]⟩,
⟨-5,-1,11,11,[[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 11 0,.s 11 0,.s 11 0,.s 11 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 33 4,.s 33 4,.s 33 4,.s 33 4]⟩,
⟨-4,-1,0,16,[[.s 12 0,.s 12 0,.s 12 0,.s 12 0],[.f ⟨1,0,0,0,0,0,0,0,0⟩,.s 0 0,.f ⟨1,0,0,1,1,0,0,0,0⟩,.s 0 0],[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.f ⟨13,3,0,0,0,0,0,0,0⟩,.s 27 0,.f ⟨13,3,0,1,1,0,0,0,0⟩,.s 27 0]],[.f ⟨1,0,0,0,0,0,0,0,0⟩,.s 0 0,.f ⟨1,0,0,1,1,0,0,0,0⟩,.s 0 0]⟩,
⟨-4,-1,1,15,[[.s 24 0,.s 24 0,.s 24 0,.s 24 0],[.s 13 0,.s 13 0,.s 13 0,.s 13 0],[.f ⟨1,1,0,0,0,0,0,0,0⟩,.s 1 0,.f ⟨1,1,0,1,1,0,0,0,0⟩,.s 1 0],[.s 26 0,.s 26 0,.s 26 0,.s 26 0]],[.f ⟨1,1,0,0,0,0,0,0,1⟩,.s 1 1,.f ⟨1,1,0,1,1,0,0,0,1⟩,.s 1 1]⟩,
⟨-4,-1,2,14,[[.s 25 0,.s 25 0,.s 25 0,.s 25 0],[.s 14 0,.s 14 0,.s 14 0,.s 14 0],[.f ⟨1,2,0,0,0,0,0,0,0⟩,.s 2 0,.f ⟨1,2,0,1,1,0,0,0,0⟩,.s 2 0],[.s 28 0,.s 28 0,.s 28 0,.s 28 0]],[.f ⟨1,2,0,0,0,0,0,0,1⟩,.s 2 1,.f ⟨1,2,0,1,1,0,0,0,1⟩,.s 2 1]⟩,
⟨-4,-1,3,8,[[.f ⟨10,0,0,0,0,0,0,0,0⟩,.f ⟨11,0,1,0,0,0,0,0,0⟩,.s 24 0,.s 24 0],[.s 15 0,.s 15 0,.s 15 0,.s 15 0],[.f ⟨1,3,0,0,0,0,0,0,0⟩,.s 3 0,.f ⟨1,3,0,1,1,0,0,0,0⟩,.s 3 0],[.s 29 0,.s 29 0,.s 29 0,.s 29 0]],[.f ⟨10,0,0,0,0,0,0,0,3⟩,.f ⟨11,0,1,0,0,0,0,0,3⟩,.s 24 3,.s 24 3]⟩,
⟨-4,-1,4,13,[[.s 26 0,.s 26 0,.s 26 0,.s 26 0],[.s 16 0,.s 16 0,.s 16 0,.s 16 0],[.f ⟨1,4,0,0,0,0,0,0,0⟩,.s 4 0,.f ⟨1,4,0,1,1,0,0,0,0⟩,.s 4 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0]],[.f ⟨1,4,0,0,0,0,0,0,1⟩,.s 4 1,.f ⟨1,4,0,1,1,0,0,0,1⟩,.s 4 1]⟩,
⟨-4,-1,5,9,[[.s 27 0,.s 27 0,.s 27 0,.s 27 0],[.s 17 0,.s 17 0,.s 17 0,.s 17 0],[.f ⟨1,5,0,0,0,0,0,0,0⟩,.s 5 0,.f ⟨1,5,0,1,1,0,0,0,0⟩,.s 5 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0]],[.s 27 3,.s 27 3,.s 27 3,.s 27 3]⟩,
⟨-4,-1,6,12,[[.s 28 0,.s 28 0,.s 28 0,.s 28 0],[.f ⟨1,4,0,0,0,0,0,0,0⟩,.s 4 0,.f ⟨1,4,0,1,1,0,0,0,0⟩,.s 4 0],[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.f ⟨1,6,0,0,0,0,0,0,0⟩,.s 6 0,.f ⟨1,6,0,1,1,0,0,0,0⟩,.s 6 0],[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.f ⟨1,8,0,0,0,0,0,0,0⟩,.s 8 0,.f ⟨1,8,0,1,1,0,0,0,0⟩,.s 8 0]],[.f ⟨1,6,0,0,0,0,0,0,2⟩,.s 6 2,.f ⟨1,6,0,1,1,0,0,0,2⟩,.s 6 2]⟩,
⟨-4,-1,7,9,[[.s 29 0,.s 29 0,.s 29 0,.s 29 0],[.f ⟨1,5,0,0,0,0,0,0,0⟩,.s 5 0,.f ⟨1,5,0,1,1,0,0,0,0⟩,.s 5 0],[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.f ⟨1,7,0,0,0,0,0,0,0⟩,.s 7 0,.f ⟨1,7,0,1,1,0,0,0,0⟩,.s 7 0],[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.f ⟨1,9,0,0,0,0,0,0,0⟩,.s 9 0,.f ⟨1,9,0,1,1,0,0,0,0⟩,.s 9 0]],[.f ⟨1,5,0,0,0,0,0,0,3⟩,.s 5 3,.f ⟨1,5,0,1,1,0,0,0,3⟩,.s 5 3]⟩,
⟨-4,-1,8,12,[[.s 18 0,.s 18 0,.s 18 0,.s 18 0],[.s 30 0,.s 30 0,.s 30 0,.s 30 0],[.s 20 0,.s 20 0,.s 20 0,.s 20 0],[.f ⟨1,8,0,0,0,0,0,0,0⟩,.s 8 0,.f ⟨1,8,0,1,1,0,0,0,0⟩,.s 8 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0]],[.f ⟨1,8,0,0,0,0,0,0,2⟩,.s 8 2,.f ⟨1,8,0,1,1,0,0,0,2⟩,.s 8 2]⟩,
⟨-4,-1,9,10,[[.s 19 0,.s 19 0,.s 19 0,.s 19 0],[.s 31 0,.s 31 0,.s 31 0,.s 31 0],[.s 21 0,.s 21 0,.s 21 0,.s 21 0],[.f ⟨1,9,0,0,0,0,0,0,0⟩,.s 9 0,.f ⟨1,9,0,1,1,0,0,0,0⟩,.s 9 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.s 31 4,.s 31 4,.s 31 4,.s 31 4]⟩,
⟨-4,-1,10,11,[[.s 32 0,.s 32 0,.s 32 0,.s 32 0],[.f ⟨1,8,0,0,0,0,0,0,0⟩,.s 8 0,.f ⟨1,8,0,1,1,0,0,0,0⟩,.s 8 0],[.s 22 0,.s 22 0,.s 22 0,.s 22 0],[.f ⟨1,10,0,0,0,0,0,0,0⟩,.s 10 0,.f ⟨1,10,0,1,1,0,0,0,0⟩,.s 10 0],[.s 35 0,.s 35 0,.s 35 0,.s 35 0]],[.f ⟨1,10,0,0,0,0,0,0,2⟩,.s 10 2,.f ⟨1,10,0,1,1,0,0,0,2⟩,.s 10 2]⟩,
⟨-4,-1,11,10,[[.s 33 0,.s 33 0,.s 33 0,.s 33 0],[.f ⟨1,9,0,0,0,0,0,0,0⟩,.s 9 0,.f ⟨1,9,0,1,1,0,0,0,0⟩,.s 9 0],[.s 34 0,.s 34 0,.s 34 0,.s 34 0],[.s 23 0,.s 23 0,.s 23 0,.s 23 0],[.f ⟨1,11,0,0,0,0,0,0,0⟩,.s 11 0,.f ⟨1,11,0,1,1,0,0,0,0⟩,.s 11 0]],[.f ⟨1,9,0,0,0,0,0,0,4⟩,.s 9 4,.f ⟨1,9,0,1,1,0,0,0,4⟩,.s 9 4]⟩]⟩]

set_option maxRecDepth 100000 in
noncomputable def certsData : List (List (List (Bool × ℕ × ℕ))) := [
[[],[(false,0,3),(false,2,1),(true,2,1)],[(false,1,3),(false,2,1),(true,2,1)],[(false,1,3),(false,2,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,1,3),(false,3,1),(true,2,1)],[(false,1,3),(false,3,1),(true,2,1)],[(false,0,3),(false,3,1),(true,2,1)],[(false,0,3),(false,3,1),(true,2,1)],[(false,0,1),(true,2,1)],[(false,0,1),(true,2,1)],[(false,0,2),(false,2,6),(true,0,1)],[(false,0,2),(false,2,6),(true,0,1)],[(false,0,2),(false,2,6),(true,1,1)],[(false,0,2),(false,2,6),(true,0,1)],[(false,2,3),(true,0,1)],[(false,2,3),(true,0,1)],[(false,2,3),(true,1,1)],[(false,2,3),(true,0,1)],[(false,3,3),(true,1,1)],[(false,3,3),(true,1,1)],[(false,3,3),(true,0,1)],[(false,3,3),(true,1,1)],[(false,0,2),(false,3,6),(true,1,1)],[(false,0,2),(false,3,6),(true,0,1)],[(false,0,2),(false,3,6),(true,1,1)],[(false,3,3),(true,0,1)],[(false,3,3),(true,0,1)],[(false,3,3),(true,1,1)],[(false,3,3),(true,0,1)],[(false,2,3),(true,1,1)]],
[[(false,0,3),(false,2,1),(true,2,10)],[],[(false,0,4),(false,2,3),(true,0,5)],[(false,0,4),(false,2,3),(true,0,5)],[(false,0,3),(false,2,1),(true,0,10)],[(false,0,3),(false,2,1),(true,0,10)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,4),(false,2,3),(true,1,5)],[(false,0,4),(false,2,3),(true,1,5)],[(false,0,3),(false,2,1),(true,1,10)],[(false,0,3),(false,2,1),(true,1,10)],[(false,1,1),(true,1,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,8),(false,2,6),(true,1,5)],[(false,0,8),(false,2,6),(true,1,5)],[(false,0,8),(false,2,6),(true,0,5)],[(false,0,8),(false,2,6),(true,1,5)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,9),(false,2,3),(true,0,10)],[(false,0,9),(false,2,3),(true,0,10)],[(false,0,9),(false,2,3),(true,1,10)],[(false,0,9),(false,2,3),(true,0,10)],[(false,0,1),(true,0,1)]],
[[(false,0,1),(false,2,3),(true,1,10)],[(false,0,3),(false,2,4),(true,2,5)],[],[(false,3,1),(true,2,1)],[(false,1,3),(false,2,1),(true,0,10)],[(false,1,3),(false,2,1),(true,0,10)],[(false,1,4),(false,2,3),(true,0,5)],[(false,1,4),(false,2,3),(true,0,5)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,3),(true,2,10)],[(false,0,1),(false,2,3),(true,2,10)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,9),(false,2,3),(true,1,10)],[(false,1,9),(false,2,3),(true,1,10)],[(false,1,9),(false,2,3),(true,0,10)],[(false,1,9),(false,2,3),(true,1,10)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,1),(true,0,1),(true,1,2)]],
[[(false,0,1),(false,2,3),(true,1,10)],[(false,0,3),(false,2,4),(true,2,5)],[(false,2,1),(true,3,1)],[],[(false,0,1),(false,2,3),(true,3,10)],[(false,1,3),(false,2,1),(true,0,10)],[(false,0,3),(false,2,4),(true,3,5)],[(false,1,4),(false,2,3),(true,0,5)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,3),(true,2,10)],[(false,0,1),(false,2,3),(true,2,10)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,9),(false,2,3),(true,1,10)],[(false,1,9),(false,2,3),(true,1,10)],[(false,1,9),(false,2,3),(true,0,10)],[(false,1,9),(false,2,3),(true,1,10)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,1),(true,0,1),(true,1,2)]],
[[(false,2,1),(true,1,1)],[(false,0,1),(false,2,3),(true,2,1)],[(false,0,3),(false,2,1),(true,1,1)],[(false,0,3),(false,2,1),(true,1,1)],[],[(false,3,1),(true,2,1)],[(false,1,3),(false,2,1),(true,0,1)],[(false,1,3),(false,2,1),(true,0,1)],[(false,0,3),(false,2,1),(true,0,1)],[(false,0,3),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,6),(false,2,2),(true,1,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,1,1)],[(false,0,3),(true,0,1)],[(false,1,3),(true,1,1)],[(false,1,3),(true,1,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,1,1)],[(false,1,6),(false,2,2),(true,1,1)],[(false,1,6),(false,2,2),(true,0,1)],[(false,1,6),(false,2,2),(true,1,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,1,1)],[(false,1,3),(true,0,1)],[(false,0,3),(true,1,1)]],
[[(false,2,1),(true,1,1)],[(false,0,1),(false,2,3),(true,2,1)],[(false,0,3),(false,2,1),(true,1,1)],[(false,0,3),(false,2,1),(true,1,1)],[(false,2,1),(true,3,1)],[],[(false,0,1),(false,2,3),(true,3,1)],[(false,1,3),(false,2,1),(true,0,1)],[(false,0,3),(false,2,1),(true,0,1)],[(false,0,3),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,6),(false,2,2),(true,1,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,1,1)],[(false,0,3),(true,0,1)],[(false,1,3),(true,1,1)],[(false,1,3),(true,1,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,1,1)],[(false,1,6),(false,2,2),(true,1,1)],[(false,0,6),(false,2,2),(true,2,1)],[(false,1,6),(false,2,2),(true,1,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,1,1)],[(false,1,3),(true,0,1)],[(false,0,3),(true,1,1)]],
[[(false,0,3),(false,2,1),(true,3,10)],[(false,2,1),(true,2,1)],[(false,0,4),(false,2,3),(true,1,5)],[(false,0,4),(false,2,3),(true,1,5)],[(false,0,3),(false,2,1),(true,1,10)],[(false,0,3),(false,2,1),(true,1,10)],[],[(false,3,1),(true,2,1)],[(false,0,4),(false,2,3),(true,0,5)],[(false,0,4),(false,2,3),(true,0,5)],[(false,0,3),(false,2,1),(true,0,10)],[(false,0,3),(false,2,1),(true,0,10)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,9),(false,2,3),(true,0,10)],[(false,0,9),(false,2,3),(true,0,10)],[(false,0,9),(false,2,3),(true,1,10)],[(false,0,9),(false,2,3),(true,0,10)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,0,8),(false,2,6),(true,1,5)],[(false,0,8),(false,2,6),(true,1,5)],[(false,0,8),(false,2,6),(true,0,5)],[(false,0,8),(false,2,6),(true,1,5)],[(false,1,1),(true,0,1)]],
[[(false,0,3),(false,2,1),(true,3,10)],[(false,2,1),(true,2,1)],[(false,0,4),(false,2,3),(true,1,5)],[(false,0,4),(false,2,3),(true,1,5)],[(false,0,3),(false,2,1),(true,1,10)],[(false,0,3),(false,2,1),(true,1,10)],[(false,2,1),(true,3,1)],[],[(false,0,4),(false,2,3),(true,0,5)],[(false,0,4),(false,2,3),(true,0,5)],[(false,0,3),(false,2,1),(true,0,10)],[(false,0,3),(false,2,1),(true,0,10)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,9),(false,2,3),(true,0,10)],[(false,0,9),(false,2,3),(true,0,10)],[(false,0,9),(false,2,3),(true,1,10)],[(false,0,9),(false,2,3),(true,0,10)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,0,8),(false,2,6),(true,1,5)],[(false,0,8),(false,2,6),(true,1,5)],[(false,0,8),(false,2,6),(true,0,5)],[(false,0,8),(false,2,6),(true,1,5)],[(false,1,1),(true,0,1)]],
[[(false,0,1),(false,2,3),(true,0,10)],[(false,1,4),(false,2,3),(true,0,5)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,3),(true,2,10)],[(false,0,1),(false,2,3),(true,2,10)],[(false,0,3),(false,2,4),(true,2,5)],[(false,0,3),(false,2,4),(true,2,5)],[],[(false,3,1),(true,2,1)],[(false,1,3),(false,2,1),(true,0,10)],[(false,1,3),(false,2,1),(true,0,10)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,9),(false,3,3),(true,0,10)],[(false,0,9),(false,3,3),(true,1,10)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,9),(false,2,3),(true,1,10)]],
[[(false,0,1),(false,2,3),(true,0,10)],[(false,1,4),(false,2,3),(true,0,5)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,3),(true,2,10)],[(false,0,1),(false,2,3),(true,2,10)],[(false,0,3),(false,2,4),(true,2,5)],[(false,0,3),(false,2,4),(true,2,5)],[(false,2,1),(true,3,1)],[],[(false,0,1),(false,2,3),(true,3,10)],[(false,1,3),(false,2,1),(true,0,10)],[(false,1,2),(true,0,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,2),(true,0,4),(true,1,1)],[(false,0,2),(true,0,1),(true,1,4)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,1,1)],[(false,1,2),(true,0,1)],[(false,1,2),(true,1,1)],[(false,1,9),(false,2,3),(true,1,10)]],
[[(false,2,1),(true,0,1)],[(false,1,3),(false,2,1),(true,0,1)],[(false,0,3),(false,2,1),(true,0,1)],[(false,0,3),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,3),(true,2,1)],[(false,0,1),(false,2,3),(true,2,1)],[(false,0,3),(false,2,1),(true,1,1)],[(false,0,3),(false,2,1),(true,1,1)],[],[(false,3,1),(true,2,1)],[(false,1,3),(false,2,1),(true,1,1)],[(false,1,3),(false,2,1),(true,1,1)],[(false,1,3),(false,2,1),(true,0,1)],[(false,1,3),(false,2,1),(true,1,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,1,1)],[(false,1,3),(true,0,1)],[(false,0,3),(true,1,1)],[(false,0,3),(true,1,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,1,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,6),(false,2,2),(true,1,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,1,1)],[(false,0,3),(true,0,1)],[(false,1,3),(true,1,1)]],
[[(false,2,1),(true,0,1)],[(false,1,3),(false,2,1),(true,0,1)],[(false,0,3),(false,2,1),(true,0,1)],[(false,0,3),(false,2,1),(true,0,1)],[(false,2,1),(true,2,1)],[(false,2,1),(true,2,1)],[(false,0,1),(false,2,3),(true,2,1)],[(false,0,1),(false,2,3),(true,2,1)],[(false,0,3),(false,2,1),(true,1,1)],[(false,0,3),(false,2,1),(true,1,1)],[(false,2,1),(true,3,1)],[],[(false,0,6),(false,2,2),(true,2,1)],[(false,1,3),(false,2,1),(true,1,1)],[(false,0,6),(false,2,2),(true,2,1)],[(false,1,3),(false,2,1),(true,1,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,0,1)],[(false,1,3),(true,1,1)],[(false,1,3),(true,0,1)],[(false,0,3),(true,1,1)],[(false,0,3),(true,1,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,1,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,6),(false,2,2),(true,1,1)],[(false,0,6),(false,2,2),(true,0,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,0,1)],[(false,0,3),(true,1,1)],[(false,0,3),(true,0,1)],[(false,1,3),(true,1,1)]],
[[(false,0,1),(false,1,2),(true,2,12)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,2),(true,0,12)],[(false,0,1),(false,1,2),(true,0,12)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,2),(true,1,12)],[(false,0,1),(false,1,2),(true,1,12)],[],[(false,2,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,3,2),(true,0,1)],[(false,0,1),(false,1,2),(true,0,4)],[(false,3,2),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(false,1,2),(true,0,4)],[(false,0,1),(false,1,2),(true,0,4)],[(false,0,1),(false,1,2),(true,1,4)],[(false,0,1),(false,1,2),(true,0,4)],[(false,1,1),(true,0,1)]],
[[(false,0,1),(false,1,2),(true,2,12)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,2),(true,0,12)],[(false,0,1),(false,1,2),(true,0,12)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,2),(true,1,12)],[(false,0,1),(false,1,2),(true,1,12)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,2,2),(true,0,1)],[(false,0,1),(false,1,2),(true,0,4)],[(false,2,2),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,0,1),(false,1,2),(true,0,4)],[(false,1,1),(true,0,1)]],
[[(false,0,2),(false,1,1),(true,2,12)],[(false,0,1),(true,1,1)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,2),(false,1,1),(true,0,12)],[(false,0,2),(false,1,1),(true,0,12)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,2),(false,1,1),(true,1,12)],[(false,0,2),(false,1,1),(true,1,12)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,2),(true,2,1)],[(false,0,2),(false,1,1),(true,1,4)],[(false,0,2),(true,2,1)],[(false,0,2),(false,1,1),(true,1,4)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(false,1,1),(true,0,4)],[(false,0,2),(false,1,1),(true,0,4)],[(false,0,2),(false,1,1),(true,1,4)],[(false,0,2),(false,1,1),(true,0,4)],[(false,0,1),(true,0,1)]],
[[(false,0,1),(false,1,2),(true,2,12)],[(false,1,1),(true,1,1)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,2),(true,0,12)],[(false,0,1),(false,1,2),(true,0,12)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,2),(true,1,12)],[(false,0,1),(false,1,2),(true,1,12)],[(false,0,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,1,2),(true,2,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,1,2),(true,2,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,2),(true,1,4)],[(false,0,1),(false,1,2),(true,0,4)],[(false,1,1),(true,0,1)]],
[[(false,0,1),(true,2,3)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,3)],[(false,0,1),(true,0,3)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,3)],[(false,0,1),(true,1,3)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[],[(false,2,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,3,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)]],
[[(false,0,1),(true,2,3)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,3)],[(false,0,1),(true,0,3)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,3)],[(false,0,1),(true,1,3)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,2,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)]],
[[(false,1,1),(true,2,3)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,3)],[(false,1,1),(true,0,3)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,1,1),(true,1,3)],[(false,1,1),(true,1,3)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,4),(true,0,2)]],
[[(false,0,1),(true,2,3)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,3)],[(false,0,1),(true,0,3)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,3)],[(false,0,1),(true,1,3)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,1,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)]],
[[(false,1,1),(true,3,3)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,1,1),(true,1,3)],[(false,1,1),(true,1,3)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,1,1),(true,0,3)],[(false,1,1),(true,0,3)],[(false,0,1),(false,1,4),(true,0,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,2,1),(true,0,2)],[(false,2,1),(true,1,2)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[],[(false,2,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,3,1),(true,0,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,3,1),(true,0,1)],[(false,0,1),(true,0,2)]],
[[(false,1,1),(true,3,3)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,1,1),(true,1,3)],[(false,1,1),(true,1,3)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,1,1),(true,0,3)],[(false,1,1),(true,0,3)],[(false,0,1),(true,3,2)],[(false,0,1),(true,2,2)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,2,1),(true,0,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,0,2)]],
[[(false,0,1),(true,3,3)],[(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,1),(true,1,3)],[(false,0,1),(true,1,3)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,1),(true,0,3)],[(false,0,1),(true,0,3)],[(false,0,4),(false,1,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,2,1),(true,0,2)],[(false,2,1),(true,1,2)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,1),(true,1,1)]],
[[(false,1,1),(true,3,3)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,1,1),(true,1,3)],[(false,1,1),(true,1,3)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,1,1),(true,0,3)],[(false,1,1),(true,0,3)],[(false,0,1),(true,3,2)],[(false,0,1),(true,2,2)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,1,1),(true,2,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,1,1),(true,2,1)],[(false,0,1),(false,1,4),(true,1,1)],[(false,0,1),(true,0,2)]],
[[(false,0,1),(false,1,1),(true,3,12)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,1),(true,1,12)],[(false,0,1),(false,1,1),(true,1,12)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,1),(true,0,12)],[(false,0,1),(false,1,1),(true,0,12)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,1),(true,1,4)],[(false,0,1),(false,1,1),(true,0,4)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,4)]],
[[(false,0,1),(false,1,1),(true,3,12)],[(false,0,1),(true,0,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(false,1,1),(true,1,12)],[(false,0,1),(false,1,1),(true,1,12)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(false,1,1),(true,0,12)],[(false,0,1),(false,1,1),(true,0,12)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,1),(true,0,4)],[(false,0,1),(false,1,1),(true,0,4)],[(false,2,1),(true,0,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,4)]],
[[(false,0,1),(false,1,1),(true,3,12)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(false,1,1),(true,1,12)],[(false,0,1),(false,1,1),(true,1,12)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(false,1,1),(true,0,12)],[(false,0,1),(false,1,1),(true,0,12)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,1),(false,1,1),(true,1,4)],[(false,0,1),(false,1,1),(true,0,4)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,1),(true,1,4)]],
[[(false,0,1),(true,3,3)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,3)],[(false,0,1),(true,1,3)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,3)],[(false,0,1),(true,0,3)],[(false,0,4),(false,1,1),(true,1,2)],[(false,3,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)],[(false,3,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,2,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[],[(false,2,1),(true,0,1)],[(false,3,1),(true,0,1)],[(false,2,1),(true,0,1)],[(false,0,1),(true,1,1)]],
[[(false,0,1),(true,3,3)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,3)],[(false,0,1),(true,1,3)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,3)],[(false,0,1),(true,0,3)],[(false,0,4),(false,1,1),(true,1,2)],[(false,2,1),(true,0,1)],[(false,0,4),(false,1,1),(true,0,2)],[(false,2,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,2,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,1,1)]],
[[(false,1,1),(true,3,3)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(true,0,2)],[(false,0,1),(true,0,2)],[(false,1,1),(true,1,3)],[(false,1,1),(true,1,3)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(true,1,2)],[(false,0,1),(true,1,2)],[(false,1,1),(true,0,3)],[(false,1,1),(true,0,3)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(false,1,4),(true,0,2)],[(false,0,1),(false,1,4),(true,1,2)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,0,1),(false,1,4),(true,0,1)],[(false,2,1),(true,0,1)],[(false,2,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[],[(false,2,1),(true,0,1)],[(false,1,1),(true,1,1)]],
[[(false,0,1),(true,3,3)],[(false,0,4),(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,1,1),(true,0,2)],[(false,0,1),(true,1,3)],[(false,0,1),(true,1,3)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,1,1),(true,1,2)],[(false,0,1),(true,0,3)],[(false,0,1),(true,0,3)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,4),(false,1,1),(true,0,2)],[(false,0,4),(false,1,1),(true,1,2)],[(false,0,1),(true,0,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,3,1)],[(false,0,1),(true,2,1)],[(false,0,4),(false,1,1),(true,1,1)],[(false,0,4),(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[(false,0,1),(true,2,1)],[(false,1,1),(true,2,1)],[(false,0,1),(true,2,1)],[],[(false,0,1),(true,1,1)]],
[[(false,1,1),(true,2,3)],[(false,0,1),(true,0,1)],[(false,0,1),(false,1,2),(true,0,1)],[(false,0,1),(false,1,2),(true,0,1)],[(false,1,1),(true,0,3)],[(false,1,1),(true,0,3)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(false,1,2),(true,1,1)],[(false,0,1),(false,1,2),(true,1,1)],[(false,1,1),(true,1,3)],[(false,1,1),(true,1,3)],[(false,0,1),(true,1,1)],[(false,0,1),(true,1,1)],[(false,0,1),(true,0,1)],[(false,0,1),(true,1,1)],[(false,0,2),(false,1,4),(true,1,1)],[(false,0,2),(false,1,4),(true,1,1)],[(false,0,2),(false,1,4),(true,0,1)],[(false,0,2),(false,1,4),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,0,1)],[(false,0,2),(true,1,1)],[(false,0,2),(true,0,1)],[(false,0,2),(false,1,4),(true,0,1)],[(false,0,2),(false,1,4),(true,1,1)],[(false,0,2),(false,1,4),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,0,1)],[(false,1,1),(true,1,1)],[(false,1,1),(true,0,1)],[]]]

noncomputable def cfg : GalCert.Cfg 12 := ⟨adjL, (0, 0, 4), 24, regsData, certsData, 0, 4⟩

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
theorem hV : cfg.vbound 67 = true := by decide +kernel

/-- The sphere sizes read off the balls of the frame. -/
def aZ : ℕ → ℤ
  | 0 => 1
  | n + 1 => ((GalCert.ball adjL (0, 0, 4) (n + 1)).card : ℤ) - (GalCert.ball adjL (0, 0, 4) n).card

theorem ha (n : ℕ) (hn : 1 ≤ n) : aZ n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact GalCert.Cfg.card_step hc k

set_option maxRecDepth 100000 in
def Avals : List ℕ := [1,5,10,15,19,24,30,36,41,45,50,55,60,65,70,75,79,84,90,96,101,105,110,115,120,125,130,135,139,144,150,156,161,165,170,175,180,185,190,195,199,204,210,216,221,225,230,235,240,245,250,255,259,264,270,276,281,285,290,295,300,305,310,315,319,324,330,336,341,345,350,355,360,365,370,375,379,384,390,396,401,405,410,415,420,425,430,435,439,444,450,456,461,465,470,475,480,485,490,495,499,504,510,516,521,525,530,535,540,545,550,555,559,564,570,576,581,585,590,595,600,605,610,615,619,624,630]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA0 : (List.range' 0 4).map cfg.Af = [1,5,10,15] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA1 : (List.range' 4 4).map cfg.Af = [19,24,30,36] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA2 : (List.range' 8 4).map cfg.Af = [41,45,50,55] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA3 : (List.range' 12 4).map cfg.Af = [60,65,70,75] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA4 : (List.range' 16 4).map cfg.Af = [79,84,90,96] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA5 : (List.range' 20 4).map cfg.Af = [101,105,110,115] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA6 : (List.range' 24 4).map cfg.Af = [120,125,130,135] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA7 : (List.range' 28 4).map cfg.Af = [139,144,150,156] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA8 : (List.range' 32 4).map cfg.Af = [161,165,170,175] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA9 : (List.range' 36 4).map cfg.Af = [180,185,190,195] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA10 : (List.range' 40 4).map cfg.Af = [199,204,210,216] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA11 : (List.range' 44 4).map cfg.Af = [221,225,230,235] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA12 : (List.range' 48 4).map cfg.Af = [240,245,250,255] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA13 : (List.range' 52 4).map cfg.Af = [259,264,270,276] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA14 : (List.range' 56 4).map cfg.Af = [281,285,290,295] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA15 : (List.range' 60 4).map cfg.Af = [300,305,310,315] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA16 : (List.range' 64 4).map cfg.Af = [319,324,330,336] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA17 : (List.range' 68 4).map cfg.Af = [341,345,350,355] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA18 : (List.range' 72 4).map cfg.Af = [360,365,370,375] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA19 : (List.range' 76 4).map cfg.Af = [379,384,390,396] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA20 : (List.range' 80 4).map cfg.Af = [401,405,410,415] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA21 : (List.range' 84 4).map cfg.Af = [420,425,430,435] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA22 : (List.range' 88 4).map cfg.Af = [439,444,450,456] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA23 : (List.range' 92 4).map cfg.Af = [461,465,470,475] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA24 : (List.range' 96 4).map cfg.Af = [480,485,490,495] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA25 : (List.range' 100 4).map cfg.Af = [499,504,510,516] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA26 : (List.range' 104 4).map cfg.Af = [521,525,530,535] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA27 : (List.range' 108 4).map cfg.Af = [540,545,550,555] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA28 : (List.range' 112 4).map cfg.Af = [559,564,570,576] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA29 : (List.range' 116 4).map cfg.Af = [581,585,590,595] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA30 : (List.range' 120 4).map cfg.Af = [600,605,610,615] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hA31 : (List.range' 124 3).map cfg.Af = [619,624,630] := by decide +kernel

set_option maxRecDepth 100000 in
theorem hAv : (List.range 127).map cfg.Af = Avals := by
  rw [List.range_eq_range']
  exact GalCert.Cfg.rmap_app cfg.Af 0 4 123 hA0 (GalCert.Cfg.rmap_app cfg.Af 4 4 119 hA1 (GalCert.Cfg.rmap_app cfg.Af 8 4 115 hA2 (GalCert.Cfg.rmap_app cfg.Af 12 4 111 hA3 (GalCert.Cfg.rmap_app cfg.Af 16 4 107 hA4 (GalCert.Cfg.rmap_app cfg.Af 20 4 103 hA5 (GalCert.Cfg.rmap_app cfg.Af 24 4 99 hA6 (GalCert.Cfg.rmap_app cfg.Af 28 4 95 hA7 (GalCert.Cfg.rmap_app cfg.Af 32 4 91 hA8 (GalCert.Cfg.rmap_app cfg.Af 36 4 87 hA9 (GalCert.Cfg.rmap_app cfg.Af 40 4 83 hA10 (GalCert.Cfg.rmap_app cfg.Af 44 4 79 hA11 (GalCert.Cfg.rmap_app cfg.Af 48 4 75 hA12 (GalCert.Cfg.rmap_app cfg.Af 52 4 71 hA13 (GalCert.Cfg.rmap_app cfg.Af 56 4 67 hA14 (GalCert.Cfg.rmap_app cfg.Af 60 4 63 hA15 (GalCert.Cfg.rmap_app cfg.Af 64 4 59 hA16 (GalCert.Cfg.rmap_app cfg.Af 68 4 55 hA17 (GalCert.Cfg.rmap_app cfg.Af 72 4 51 hA18 (GalCert.Cfg.rmap_app cfg.Af 76 4 47 hA19 (GalCert.Cfg.rmap_app cfg.Af 80 4 43 hA20 (GalCert.Cfg.rmap_app cfg.Af 84 4 39 hA21 (GalCert.Cfg.rmap_app cfg.Af 88 4 35 hA22 (GalCert.Cfg.rmap_app cfg.Af 92 4 31 hA23 (GalCert.Cfg.rmap_app cfg.Af 96 4 27 hA24 (GalCert.Cfg.rmap_app cfg.Af 100 4 23 hA25 (GalCert.Cfg.rmap_app cfg.Af 104 4 19 hA26 (GalCert.Cfg.rmap_app cfg.Af 108 4 15 hA27 (GalCert.Cfg.rmap_app cfg.Af 112 4 11 hA28 (GalCert.Cfg.rmap_app cfg.Af 116 4 7 hA29 (GalCert.Cfg.rmap_app cfg.Af 120 4 3 hA30 (hA31)))))))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
theorem hrec : ∀ k, (([(1, 11), (-3, 10), (4, 9), (-3, 8), (1, 7), (1, 5), (-3, 4), (4, 3), (-3, 2), (1, 1)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide)
    (GalCert.Cfg.window_of_list hAv _ _ (by decide +kernel) (by decide +kernel))

set_option maxHeartbeats 0 in
theorem hgfw : ∀ n < 67 + 2 * cfg.L, ((GalCert.csOf [1, -3, 4, -3, 1, 0, 1, -3, 4, -3, 1] 11).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.window_of_list hAv _ _ (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
theorem hsmall : ∀ n < 11, GalCert.conv aZ [1, -3, 4, -3, 1, 0, 1, -3, 4, -3, 1] n = ([1, 2, -1, 2, 0, 2, 0, 2, -1, 2, 1] : List ℤ).getD n 0 := by
  have e : aZ = fun n => if n = 0 then 1 else if n < 127 then (Avals.getD n 0 : ℤ) else (cfg.A n : ℤ) := by
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

theorem hrecZ : ∀ n : ℕ, 10 < n → aZ n = 3 * aZ (n - 1) - 4 * aZ (n - 2) + 3 * aZ (n - 3) - aZ (n - 4) - aZ (n - 6) + 3 * aZ (n - 7) - 4 * aZ (n - 8) + 3 * aZ (n - 9) - aZ (n - 10) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
  have h := hrec k
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
  rw [show k + 11 - 1 = k + 10 by omega,
    show k + 11 - 2 = k + 9 by omega,
    show k + 11 - 3 = k + 8 by omega,
    show k + 11 - 4 = k + 7 by omega,
    show k + 11 - 6 = k + 5 by omega,
    show k + 11 - 7 = k + 4 by omega,
    show k + 11 - 8 = k + 3 by omega,
    show k + 11 - 9 = k + 2 by omega,
    show k + 11 - 10 = k + 1 by omega,
    ha (k + 11) (by omega),
    ha (k + 10) (by omega),
    ha (k + 9) (by omega),
    ha (k + 8) (by omega),
    ha (k + 7) (by omega),
    ha (k + 5) (by omega),
    ha (k + 4) (by omega),
    ha (k + 3) (by omega),
    ha (k + 2) (by omega),
    ha (k + 1) (by omega)]
  linarith

open PowerSeries in
theorem hgfZ : PowerSeries.mk aZ * (((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 2 - X + 1) * (X ^ 4 - X ^ 2 + 1)) : PowerSeries ℤ) = (X ^ 10 + 2 * X ^ 9 - X ^ 8 + 2 * X ^ 7 + 2 * X ^ 5 + 2 * X ^ 3 - X ^ 2 + 2 * X + 1 : PowerSeries ℤ) := by
  have hD : (((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 2 - X + 1) * (X ^ 4 - X ^ 2 + 1)) : PowerSeries ℤ) = GalCert.polyOf [1, -3, 4, -3, 1, 0, 1, -3, 4, -3, 1] := by
    simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
  have hP : (X ^ 10 + 2 * X ^ 9 - X ^ 8 + 2 * X ^ 7 + 2 * X ^ 5 + 2 * X ^ 3 - X ^ 2 + 2 * X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 2, -1, 2, 0, 2, 0, 2, -1, 2, 1] := by
    simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
  rw [hD, hP]
  exact GalCert.Cfg.gf_from hc hV aZ ha _ _ 11 (by decide) (by decide) hgfw hsmall

theorem hpx : SGBridge.pathOk adjL (0, 0, 4) [(1, 0, 4)] (1, 0, 4) = true := by decide +kernel

theorem hpy : SGBridge.pathOk adjL (0, 0, 4) [(-1, 0, 6), (-1, 0, 8), (-2, 0, 10), (-2, 0, 11), (-1, 0, 9), (-1, 0, 7), (0, 0, 5), (0, 0, 3), (0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 1, 4)] (0, 1, 4) = true := by decide +kernel

def clsW : Fin 12 → (ℤ × ℤ) × List (ℤ × ℤ × Fin 12) := ![
  ((0, 0), [(0, 0, 2), (0, 0, 1), (0, 0, 0)]),
  ((0, 0), [(0, 0, 2), (0, 0, 1)]),
  ((0, 0), [(0, 0, 2)]),
  ((0, -1), [(0, 0, 2), (0, 0, 1), (0, 0, 0), (0, -1, 3)]),
  ((0, 0), []),
  ((0, -1), [(0, 0, 2), (0, 0, 1), (0, 0, 0), (0, -1, 3), (0, -1, 5)]),
  ((-1, 0), [(-1, 0, 6)]),
  ((-3, 0), [(-1, 0, 6), (-1, 0, 8), (-2, 0, 10), (-2, 0, 11), (-2, 0, 9), (-3, 0, 7)]),
  ((-1, 0), [(-1, 0, 6), (-1, 0, 8)]),
  ((-2, 0), [(-1, 0, 6), (-1, 0, 8), (-2, 0, 10), (-2, 0, 11), (-2, 0, 9)]),
  ((-2, 0), [(-1, 0, 6), (-1, 0, 8), (-2, 0, 10)]),
  ((-2, 0), [(-1, 0, 6), (-1, 0, 8), (-2, 0, 10), (-2, 0, 11)])]

theorem hpc : ∀ i : Fin 12, SGBridge.pathOk adjL (0, 0, 4) (clsW i).2 ((clsW i).1.1, (clsW i).1.2, i) = true := by
  decide +kernel

theorem hconn : ∀ v, (SimpleGraph.fromRel (SGBridge.Rel E)).Reachable (0, 0, 4) v :=
  SGBridge.connected 4 (SGBridge.reach_of_path hadj _ _ _ hpx) (SGBridge.reach_of_path hadj _ _ _ hpy)
    (fun i => ⟨(clsW i).1, SGBridge.reach_of_path hadj _ _ _ (hpc i)⟩)

theorem hbr : ∀ n, (a n : ℤ) = aZ n
  | 0 => by
    have h := SGBridge.ncard_zero hadj hconn
    exact congrArg (fun k : ℕ => (k : ℤ)) h
  | k + 1 => SGBridge.ncard_succ hadj hconn k

end P313698

open PowerSeries OMA.S_oeis_a313698 in
theorem OMA.solution : type_of% @OMA.S_oeis_a313698.main := by
  refine ⟨?_, ?_⟩
  · have hm : PowerSeries.mk (fun n => (a n : ℚ)) = PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk P313698.aZ) := by
      ext n
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_map, PowerSeries.coeff_mk, ← P313698.hbr n]
      simp
    have hD : (((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 2 - X + 1) * (X ^ 4 - X ^ 2 + 1)) : PowerSeries ℚ) = PowerSeries.map (Int.castRingHom ℚ) (((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 2 - X + 1) * (X ^ 4 - X ^ 2 + 1)) : PowerSeries ℤ) := by
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, PowerSeries.map_X, map_one, map_ofNat]
    have hN : (X ^ 10 + 2 * X ^ 9 - X ^ 8 + 2 * X ^ 7 + 2 * X ^ 5 + 2 * X ^ 3 - X ^ 2 + 2 * X + 1 : PowerSeries ℚ) = PowerSeries.map (Int.castRingHom ℚ) (X ^ 10 + 2 * X ^ 9 - X ^ 8 + 2 * X ^ 7 + 2 * X ^ 5 + 2 * X ^ 3 - X ^ 2 + 2 * X + 1 : PowerSeries ℤ) := by
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, PowerSeries.map_X, map_one, map_ofNat]
    rw [hm, hD, hN, ← map_mul, P313698.hgfZ]
  · intro n hn
    rw [P313698.hbr n, P313698.hbr (n - 1), P313698.hbr (n - 2), P313698.hbr (n - 3), P313698.hbr (n - 4), P313698.hbr (n - 6), P313698.hbr (n - 7), P313698.hbr (n - 8), P313698.hbr (n - 9), P313698.hbr (n - 10)]
    exact P313698.hrecZ n hn
