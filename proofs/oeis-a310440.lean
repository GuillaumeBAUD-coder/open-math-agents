import OMAStatements.S_oeis_a310440
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A310440.

Method: an explicit distance certificate. Every vertex outside the origin cell lies on one of the
rays through the vertices of the growth polygon or in one of the cones between them (split into a
finite corner, two boundary strips and an interior), and is written as base + k T + j U with a base
from a finite list. The certificate gives the distance of each code as v + L (k + j). A Boolean
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

def csOf (l : List ℤ) : List (ℤ × ℕ) := (List.range l.length).map fun i => (l.getD i 0, l.length - i)

theorem csOf_pos (l : List ℤ) : ∀ p ∈ csOf l, 1 ≤ p.2 := by
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
    (hw : ∀ n < V + 2 * C.L, ((csOf dl).map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0)
    (hsmall : ∀ n < M, conv a dl n = pl.getD n 0) :
    PowerSeries.mk a * polyOf dl = polyOf pl := by
  apply gf_of_conv
  intro n
  rcases Nat.lt_or_ge n M with h | h
  · exact hsmall n h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + dl.length := ⟨n - dl.length, by omega⟩
    rw [List.getD_eq_default _ _ (by omega), conv_cs]
    have hz := lin_zero hc hV (csOf dl) (csOf_pos dl) hw k
    unfold csOf at hz
    rw [List.map_map] at hz
    refine Eq.trans ?_ hz
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [ha _ (by omega), show k + dl.length - i = k + (dl.length - i) by omega]

end Cfg
end GalCert


namespace P310440
open OMA.S_oeis_a310440

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 12) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 8, [[.f ⟨11, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨13, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨11, 1, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, 0, 1, 7, [[.f ⟨11, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.f ⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 1, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 3 1]⟩,
    ⟨0, 0, 2, 3, [[.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.f ⟨21, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 0, 3, 6, [[.f ⟨11, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 4 0], [.f ⟨5, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 4 3]⟩,
    ⟨0, 0, 4, 5, [[.f ⟨11, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 7 0], [.f ⟨5, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨11, 7, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 0, 5, 2, [[.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 6 0], [.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 2]⟩,
    ⟨0, 0, 6, 1, [[.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.s 8 0], [.f ⟨5, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 1]⟩,
    ⟨0, 0, 7, 4, [[.f ⟨11, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 9 0], [.f ⟨5, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 7, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 9 1]⟩,
    ⟨0, 0, 8, 0, [[.f ⟨11, 8, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 10 0], [.f ⟨5, 8, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨0, 0, 9, 3, [[.f ⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 7 0], [.s 11 0], [.f ⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 11 1]⟩,
    ⟨0, 0, 10, 1, [[.f ⟨11, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 8 0], [.s 11 0], [.f ⟨5, 10, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 2]⟩,
    ⟨0, 0, 11, 2, [[.f ⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 9 0], [.s 10 0], [.f ⟨5, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 10 3]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, -2, 0), (-1, 2, 0), (-2, -1, 1), (2, 1, -5)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-2, -1, 0, 20, [[.f ⟨27, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 24, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨27, 25, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-2, -1, 1, 19, [[.f ⟨27, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.f ⟨14, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 25, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 3 1]⟩,
    ⟨-2, -1, 2, 10, [[.f ⟨27, 26, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.f ⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 26, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨12, 0, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-2, -1, 3, 18, [[.f ⟨27, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 4 0], [.f ⟨14, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 28, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 4 3]⟩,
    ⟨-2, -1, 4, 17, [[.f ⟨27, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 28, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 31, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 7 0], [.f ⟨14, 28, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨27, 31, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-2, -1, 5, 10, [[.f ⟨27, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 6 0], [.f ⟨14, 26, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 30, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨14, 26, 0, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨-2, -1, 6, 11, [[.f ⟨27, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 30, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.s 8 0], [.f ⟨14, 30, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 5 2]⟩,
    ⟨-2, -1, 7, 16, [[.f ⟨27, 31, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 9 0], [.f ⟨14, 28, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 31, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 9 1]⟩,
    ⟨-2, -1, 8, 12, [[.f ⟨27, 32, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 10 0], [.f ⟨14, 32, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 3]⟩,
    ⟨-2, -1, 9, 15, [[.f ⟨27, 33, 0, 0, 0, 0, 0, 0, 0⟩], [.s 7 0], [.s 11 0], [.f ⟨14, 33, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 11 1]⟩,
    ⟨-2, -1, 10, 13, [[.f ⟨27, 34, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨27, 35, 0, 0, 0, 0, 0, 0, 0⟩], [.s 8 0], [.s 11 0], [.f ⟨14, 34, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 2]⟩,
    ⟨-2, -1, 11, 14, [[.f ⟨27, 35, 0, 0, 0, 0, 0, 0, 0⟩], [.s 9 0], [.s 10 0], [.f ⟨14, 34, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 35, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 10 3]⟩]⟩,
  ⟨1, -2, -1, 0, 0, [(1, -2, 0), (-1, 2, 0), (-2, -1, 10)], -2, -1, 10, 5, 0, 0, 0, 0,
   [⟨-4, -2, 0, 32, [[.f ⟨27, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 24, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨27, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 24, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨27, 25, 0, 0, 1, 0, 0, 0, 2⟩, .f ⟨27, 25, 1, 0, 2, 0, 0, 0, 2⟩]⟩,
    ⟨-4, -2, 1, 31, [[.f ⟨27, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.f ⟨14, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 24, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 25, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 3 1, .s 3 1]⟩,
    ⟨-4, -2, 2, 22, [[.f ⟨27, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 26, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨27, 29, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 29, 1, 0, 2, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.f ⟨27, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨27, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨14, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 26, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨27, 12, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨27, 12, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨-4, -2, 3, 30, [[.f ⟨27, 27, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 27, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.f ⟨14, 27, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 27, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 28, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 28, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 4 3, .s 4 3]⟩,
    ⟨-4, -2, 4, 29, [[.f ⟨27, 27, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 27, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨27, 28, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 28, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨27, 31, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 31, 1, 0, 2, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.f ⟨14, 28, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 28, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨27, 31, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨27, 31, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨-4, -2, 5, 22, [[.f ⟨27, 29, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 29, 1, 0, 2, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.f ⟨14, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 26, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 29, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 29, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 30, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 30, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨14, 26, 0, 0, 1, 0, 0, 0, 1⟩, .f ⟨14, 26, 1, 0, 2, 0, 0, 0, 1⟩]⟩,
    ⟨-4, -2, 6, 23, [[.f ⟨27, 29, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 29, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨27, 30, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 30, 1, 0, 2, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.f ⟨14, 30, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 30, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 5 2, .s 5 2]⟩,
    ⟨-4, -2, 7, 28, [[.f ⟨27, 31, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 31, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.f ⟨14, 28, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 28, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 31, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 31, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 9 1, .s 9 1]⟩,
    ⟨-4, -2, 8, 24, [[.f ⟨27, 32, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 32, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.f ⟨14, 32, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 32, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 6 3, .s 6 3]⟩,
    ⟨-4, -2, 9, 27, [[.f ⟨27, 33, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 33, 1, 0, 2, 0, 0, 0, 0⟩], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.f ⟨14, 33, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 33, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 11 1, .s 11 1]⟩,
    ⟨-4, -2, 10, 25, [[.f ⟨27, 34, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 34, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨27, 35, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 35, 1, 0, 2, 0, 0, 0, 0⟩], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.f ⟨14, 34, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 34, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 8 2, .s 8 2]⟩,
    ⟨-4, -2, 11, 26, [[.f ⟨27, 35, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨27, 35, 1, 0, 2, 0, 0, 0, 0⟩], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.f ⟨14, 34, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 34, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨14, 35, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 35, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 10 3, .s 10 3]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 3, 0), (-1, -3, 0), (3, -1, 1), (-3, 1, -10)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨3, -1, 0, 20, [[.f ⟨15, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨17, 0, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨15, 1, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨3, -1, 1, 19, [[.f ⟨15, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.f ⟨17, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨17, 1, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 3 1]⟩,
    ⟨3, -1, 2, 10, [[.f ⟨15, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.f ⟨6, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨17, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨15, 2, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨3, -1, 3, 18, [[.f ⟨15, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 4 0], [.f ⟨17, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨17, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 4 3]⟩,
    ⟨3, -1, 4, 17, [[.f ⟨15, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 7 0], [.f ⟨17, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨15, 7, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨3, -1, 5, 11, [[.f ⟨15, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 6 0], [.f ⟨17, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨17, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨17, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨15, 5, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨3, -1, 6, 11, [[.f ⟨15, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.s 8 0], [.f ⟨17, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨15, 5, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨3, -1, 7, 16, [[.f ⟨15, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 9 0], [.f ⟨17, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨17, 7, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 9 1]⟩,
    ⟨3, -1, 8, 12, [[.f ⟨15, 8, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 10 0], [.f ⟨17, 8, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 3]⟩,
    ⟨3, -1, 9, 15, [[.f ⟨15, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 7 0], [.s 11 0], [.f ⟨17, 9, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 11 1]⟩,
    ⟨3, -1, 10, 13, [[.f ⟨15, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 8 0], [.s 11 0], [.f ⟨17, 10, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 2]⟩,
    ⟨3, -1, 11, 14, [[.f ⟨15, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 9 0], [.s 10 0], [.f ⟨17, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨17, 11, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 10 3]⟩]⟩,
  ⟨1, 3, -1, 0, 0, [(1, 3, 0), (-1, -3, 0), (3, -1, 20)], 3, -1, 20, 10, 0, 0, 0, 0,
   [⟨6, -2, 0, 32, [[.f ⟨15, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨15, 1, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 1, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨15, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 14, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨17, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 0, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨15, 1, 0, 0, 1, 0, 0, 0, 2⟩, .f ⟨15, 1, 1, 0, 2, 0, 0, 0, 2⟩]⟩,
    ⟨6, -2, 1, 31, [[.f ⟨15, 1, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 1, 1, 0, 2, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.f ⟨17, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨17, 1, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 1, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 3 1, .s 3 1]⟩,
    ⟨6, -2, 2, 22, [[.f ⟨15, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨15, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.f ⟨17, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 24, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨17, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 2, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨15, 2, 0, 0, 1, 0, 0, 0, 4⟩, .f ⟨15, 2, 1, 0, 2, 0, 0, 0, 4⟩]⟩,
    ⟨6, -2, 3, 30, [[.f ⟨15, 3, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 3, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.f ⟨17, 3, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 3, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨17, 4, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 4, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 4 3, .s 4 3]⟩,
    ⟨6, -2, 4, 29, [[.f ⟨15, 3, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 3, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨15, 4, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 4, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨15, 7, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 7, 1, 0, 2, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.f ⟨17, 4, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 4, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨15, 7, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨15, 7, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨6, -2, 5, 23, [[.f ⟨15, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.f ⟨17, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨17, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨17, 6, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 6, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨15, 5, 0, 0, 1, 0, 0, 0, 4⟩, .f ⟨15, 5, 1, 0, 2, 0, 0, 0, 4⟩]⟩,
    ⟨6, -2, 6, 23, [[.f ⟨15, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨15, 6, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 6, 1, 0, 2, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.f ⟨17, 6, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 6, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨15, 5, 0, 0, 1, 0, 0, 0, 5⟩, .f ⟨15, 5, 1, 0, 2, 0, 0, 0, 5⟩]⟩,
    ⟨6, -2, 7, 28, [[.f ⟨15, 7, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 7, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.f ⟨17, 4, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 4, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨17, 7, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 7, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 9 1, .s 9 1]⟩,
    ⟨6, -2, 8, 24, [[.f ⟨15, 8, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 8, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.f ⟨17, 8, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 8, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 6 3, .s 6 3]⟩,
    ⟨6, -2, 9, 27, [[.f ⟨15, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 9, 1, 0, 2, 0, 0, 0, 0⟩], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.f ⟨17, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 9, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 11 1, .s 11 1]⟩,
    ⟨6, -2, 10, 25, [[.f ⟨15, 10, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 10, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨15, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.f ⟨17, 10, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 10, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 8 2, .s 8 2]⟩,
    ⟨6, -2, 11, 26, [[.f ⟨15, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.f ⟨17, 10, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 10, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨17, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 11, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 10 3, .s 10 3]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 1), (-1, 0, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, 0, 0, 8, [[.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨13, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 1, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨1, 0, 1, 7, [[.f ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.f ⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 1, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 3 1]⟩,
    ⟨1, 0, 2, 3, [[.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 3, 6, [[.f ⟨0, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 4 0], [.f ⟨6, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 4 3]⟩,
    ⟨1, 0, 4, 5, [[.f ⟨0, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 7 0], [.f ⟨6, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 7, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 5, 3, [[.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 6 0], [.f ⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 0, 6, 2, [[.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.s 8 0], [.f ⟨6, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 6, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 0, 7, 5, [[.f ⟨0, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 9 0], [.f ⟨6, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 7, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 7, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 0, 8, 1, [[.f ⟨0, 8, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 10 0], [.f ⟨6, 8, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 8, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 9, 4, [[.f ⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 7 0], [.s 11 0], [.f ⟨6, 9, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 9, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 0, 10, 2, [[.f ⟨0, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 8 0], [.s 11 0], [.f ⟨6, 10, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 10, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨1, 0, 11, 3, [[.f ⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 9 0], [.s 10 0], [.f ⟨6, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 11, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 11, 0, 0, 0, 0, 0, 0, 4⟩]⟩]⟩,
  ⟨1, 12, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 2)], 1, 0, 2, 12, 0, 0, 0, 0,
   [⟨2, 0, 0, 8, [[.f ⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 132 0], [.f ⟨5, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 133 0], [.f ⟨15, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 86, 0, 0, 0, 1, 0, 0, 0⟩], [.s 12 0, .s 12 0]], [.f ⟨5, 1, 0, 0, 0, 0, 0, 0, 2⟩, .s 132 3]⟩,
    ⟨2, 0, 1, 8, [[.f ⟨5, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 133 0], [.s 3 0, .s 3 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0]], [.f ⟨5, 1, 0, 0, 0, 0, 0, 0, 3⟩, .s 133 3]⟩,
    ⟨2, 0, 2, 4, [[.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 134 0], [.f ⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 137 0], [.s 5 0, .s 5 0], [.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 96, 1, 0, 0, 0, 0, 0, 0⟩], [.s 14 0, .s 14 0]], [.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 4⟩, .s 134 4]⟩,
    ⟨2, 0, 3, 7, [[.f ⟨5, 3, 0, 0, 0, 0, 0, 0, 0⟩, .s 135 0], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0]], [.f ⟨5, 3, 0, 0, 0, 0, 0, 0, 3⟩, .s 135 3]⟩,
    ⟨2, 0, 4, 6, [[.f ⟨5, 3, 0, 0, 0, 0, 0, 0, 0⟩, .s 135 0], [.f ⟨5, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 136 0], [.f ⟨5, 7, 0, 0, 0, 0, 0, 0, 0⟩, .s 139 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 16 0, .s 16 0]], [.f ⟨5, 4, 0, 0, 0, 0, 0, 0, 5⟩, .s 136 5]⟩,
    ⟨2, 0, 5, 4, [[.f ⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 137 0], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 18 0, .s 18 0]], [.f ⟨5, 5, 0, 0, 0, 0, 0, 0, 4⟩, .s 137 4]⟩,
    ⟨2, 0, 6, 3, [[.f ⟨5, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 137 0], [.f ⟨5, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 138 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 18 0, .s 18 0]], [.f ⟨5, 6, 0, 0, 0, 0, 0, 0, 4⟩, .s 138 4]⟩,
    ⟨2, 0, 7, 6, [[.f ⟨5, 7, 0, 0, 0, 0, 0, 0, 0⟩, .s 139 0], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0]], [.f ⟨5, 7, 0, 0, 0, 0, 0, 0, 4⟩, .s 139 4]⟩,
    ⟨2, 0, 8, 2, [[.f ⟨5, 8, 0, 0, 0, 0, 0, 0, 0⟩, .s 140 0], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.s 20 0, .s 20 0]], [.f ⟨5, 8, 0, 0, 0, 0, 0, 0, 3⟩, .s 140 3]⟩,
    ⟨2, 0, 9, 5, [[.f ⟨5, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 141 0], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.s 21 0, .s 21 0]], [.f ⟨5, 9, 0, 0, 0, 0, 0, 0, 3⟩, .s 141 3]⟩,
    ⟨2, 0, 10, 3, [[.f ⟨5, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 142 0], [.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 143 0], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨5, 10, 0, 0, 0, 0, 0, 0, 4⟩, .s 142 4]⟩,
    ⟨2, 0, 11, 4, [[.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 143 0], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.f ⟨5, 11, 0, 0, 0, 0, 0, 0, 4⟩, .s 143 4]⟩,
    ⟨3, 0, 0, 9, [[.s 0 0, .s 0 0], [.s 1 0, .s 1 0], [.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 98, 0, 0, 0, 1, 0, 0, 0⟩], [.s 24 0, .s 24 0]], [.s 0 3, .s 0 3]⟩,
    ⟨3, 0, 1, 9, [[.s 1 0, .s 1 0], [.s 15 0, .s 15 0], [.s 24 0, .s 24 0], [.s 25 0, .s 25 0]], [.s 1 3, .s 1 3]⟩,
    ⟨3, 0, 2, 5, [[.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.f ⟨19, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 108, 1, 0, 0, 0, 0, 0, 0⟩], [.s 26 0, .s 26 0]], [.s 2 4, .s 2 4]⟩,
    ⟨3, 0, 3, 8, [[.s 3 0, .s 3 0], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.s 27 0, .s 27 0], [.s 28 0, .s 28 0]], [.s 3 3, .s 3 3]⟩,
    ⟨3, 0, 4, 7, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.s 28 0, .s 28 0]], [.s 4 5, .s 4 5]⟩,
    ⟨3, 0, 5, 5, [[.s 5 0, .s 5 0], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 30 0, .s 30 0]], [.s 5 4, .s 5 4]⟩,
    ⟨3, 0, 6, 4, [[.s 5 0, .s 5 0], [.s 6 0, .s 6 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 30 0, .s 30 0]], [.s 6 4, .s 6 4]⟩,
    ⟨3, 0, 7, 7, [[.s 7 0, .s 7 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0]], [.s 7 4, .s 7 4]⟩,
    ⟨3, 0, 8, 3, [[.s 8 0, .s 8 0], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.s 32 0, .s 32 0]], [.s 8 3, .s 8 3]⟩,
    ⟨3, 0, 9, 6, [[.s 9 0, .s 9 0], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.s 33 0, .s 33 0]], [.s 9 3, .s 9 3]⟩,
    ⟨3, 0, 10, 4, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.s 34 0, .s 34 0]], [.s 10 4, .s 10 4]⟩,
    ⟨3, 0, 11, 5, [[.s 11 0, .s 11 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 34 0, .s 34 0], [.s 35 0, .s 35 0]], [.s 11 4, .s 11 4]⟩,
    ⟨4, 0, 0, 10, [[.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.f ⟨17, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 110, 0, 0, 0, 1, 0, 0, 0⟩], [.s 36 0, .s 36 0]], [.s 12 3, .s 12 3]⟩,
    ⟨4, 0, 1, 10, [[.s 13 0, .s 13 0], [.s 27 0, .s 27 0], [.s 36 0, .s 36 0], [.s 37 0, .s 37 0]], [.s 13 3, .s 13 3]⟩,
    ⟨4, 0, 2, 6, [[.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 29 0, .s 29 0], [.f ⟨19, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 120, 1, 0, 0, 0, 0, 0, 0⟩], [.s 38 0, .s 38 0]], [.s 14 4, .s 14 4]⟩,
    ⟨4, 0, 3, 9, [[.s 15 0, .s 15 0], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.s 39 0, .s 39 0], [.s 40 0, .s 40 0]], [.s 15 3, .s 15 3]⟩,
    ⟨4, 0, 4, 8, [[.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.s 40 0, .s 40 0]], [.s 16 5, .s 16 5]⟩,
    ⟨4, 0, 5, 6, [[.s 17 0, .s 17 0], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.s 38 0, .s 38 0], [.s 41 0, .s 41 0], [.s 42 0, .s 42 0]], [.s 17 4, .s 17 4]⟩,
    ⟨4, 0, 6, 5, [[.s 17 0, .s 17 0], [.s 18 0, .s 18 0], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.s 42 0, .s 42 0]], [.s 18 4, .s 18 4]⟩,
    ⟨4, 0, 7, 8, [[.s 19 0, .s 19 0], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.s 40 0, .s 40 0], [.s 43 0, .s 43 0]], [.s 19 4, .s 19 4]⟩,
    ⟨4, 0, 8, 4, [[.s 20 0, .s 20 0], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.s 44 0, .s 44 0]], [.s 20 3, .s 20 3]⟩,
    ⟨4, 0, 9, 7, [[.s 21 0, .s 21 0], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.s 45 0, .s 45 0]], [.s 21 3, .s 21 3]⟩,
    ⟨4, 0, 10, 5, [[.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.s 46 0, .s 46 0]], [.s 22 4, .s 22 4]⟩,
    ⟨4, 0, 11, 6, [[.s 23 0, .s 23 0], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.s 46 0, .s 46 0], [.s 47 0, .s 47 0]], [.s 23 4, .s 23 4]⟩,
    ⟨5, 0, 0, 11, [[.s 24 0, .s 24 0], [.s 25 0, .s 25 0], [.f ⟨17, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 122, 0, 0, 0, 1, 0, 0, 0⟩], [.s 48 0, .s 48 0]], [.s 24 3, .s 24 3]⟩,
    ⟨5, 0, 1, 11, [[.s 25 0, .s 25 0], [.s 39 0, .s 39 0], [.s 48 0, .s 48 0], [.s 49 0, .s 49 0]], [.s 25 3, .s 25 3]⟩,
    ⟨5, 0, 2, 7, [[.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 41 0, .s 41 0], [.f ⟨19, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 132, 1, 0, 0, 0, 0, 0, 0⟩], [.s 50 0, .s 50 0]], [.s 26 4, .s 26 4]⟩,
    ⟨5, 0, 3, 10, [[.s 27 0, .s 27 0], [.s 37 0, .s 37 0], [.s 40 0, .s 40 0], [.s 51 0, .s 51 0], [.s 52 0, .s 52 0]], [.s 27 3, .s 27 3]⟩,
    ⟨5, 0, 4, 9, [[.s 27 0, .s 27 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0], [.s 39 0, .s 39 0], [.s 43 0, .s 43 0], [.s 52 0, .s 52 0]], [.s 28 5, .s 28 5]⟩,
    ⟨5, 0, 5, 7, [[.s 29 0, .s 29 0], [.s 38 0, .s 38 0], [.s 42 0, .s 42 0], [.s 50 0, .s 50 0], [.s 53 0, .s 53 0], [.s 54 0, .s 54 0]], [.s 29 4, .s 29 4]⟩,
    ⟨5, 0, 6, 6, [[.s 29 0, .s 29 0], [.s 30 0, .s 30 0], [.s 41 0, .s 41 0], [.s 44 0, .s 44 0], [.s 54 0, .s 54 0]], [.s 30 4, .s 30 4]⟩,
    ⟨5, 0, 7, 9, [[.s 31 0, .s 31 0], [.s 40 0, .s 40 0], [.s 45 0, .s 45 0], [.s 52 0, .s 52 0], [.s 55 0, .s 55 0]], [.s 31 4, .s 31 4]⟩,
    ⟨5, 0, 8, 5, [[.s 32 0, .s 32 0], [.s 42 0, .s 42 0], [.s 46 0, .s 46 0], [.s 56 0, .s 56 0]], [.s 32 3, .s 32 3]⟩,
    ⟨5, 0, 9, 8, [[.s 33 0, .s 33 0], [.s 43 0, .s 43 0], [.s 47 0, .s 47 0], [.s 57 0, .s 57 0]], [.s 33 3, .s 33 3]⟩,
    ⟨5, 0, 10, 6, [[.s 34 0, .s 34 0], [.s 35 0, .s 35 0], [.s 44 0, .s 44 0], [.s 47 0, .s 47 0], [.s 58 0, .s 58 0]], [.s 34 4, .s 34 4]⟩,
    ⟨5, 0, 11, 7, [[.s 35 0, .s 35 0], [.s 45 0, .s 45 0], [.s 46 0, .s 46 0], [.s 58 0, .s 58 0], [.s 59 0, .s 59 0]], [.s 35 4, .s 35 4]⟩,
    ⟨6, 0, 0, 12, [[.s 36 0, .s 36 0], [.s 37 0, .s 37 0], [.f ⟨17, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 134, 0, 0, 0, 1, 0, 0, 0⟩], [.s 60 0, .s 60 0]], [.s 36 3, .s 36 3]⟩,
    ⟨6, 0, 1, 12, [[.s 37 0, .s 37 0], [.s 51 0, .s 51 0], [.s 60 0, .s 60 0], [.s 61 0, .s 61 0]], [.s 37 3, .s 37 3]⟩,
    ⟨6, 0, 2, 8, [[.s 38 0, .s 38 0], [.s 41 0, .s 41 0], [.s 53 0, .s 53 0], [.f ⟨20, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 62 0, .s 62 0]], [.s 38 4, .s 38 4]⟩,
    ⟨6, 0, 3, 11, [[.s 39 0, .s 39 0], [.s 49 0, .s 49 0], [.s 52 0, .s 52 0], [.s 63 0, .s 63 0], [.s 64 0, .s 64 0]], [.s 39 3, .s 39 3]⟩,
    ⟨6, 0, 4, 10, [[.s 39 0, .s 39 0], [.s 40 0, .s 40 0], [.s 43 0, .s 43 0], [.s 51 0, .s 51 0], [.s 55 0, .s 55 0], [.s 64 0, .s 64 0]], [.s 40 5, .s 40 5]⟩,
    ⟨6, 0, 5, 8, [[.s 41 0, .s 41 0], [.s 50 0, .s 50 0], [.s 54 0, .s 54 0], [.s 62 0, .s 62 0], [.s 65 0, .s 65 0], [.s 66 0, .s 66 0]], [.s 41 4, .s 41 4]⟩,
    ⟨6, 0, 6, 7, [[.s 41 0, .s 41 0], [.s 42 0, .s 42 0], [.s 53 0, .s 53 0], [.s 56 0, .s 56 0], [.s 66 0, .s 66 0]], [.s 42 4, .s 42 4]⟩,
    ⟨6, 0, 7, 10, [[.s 43 0, .s 43 0], [.s 52 0, .s 52 0], [.s 57 0, .s 57 0], [.s 64 0, .s 64 0], [.s 67 0, .s 67 0]], [.s 43 4, .s 43 4]⟩,
    ⟨6, 0, 8, 6, [[.s 44 0, .s 44 0], [.s 54 0, .s 54 0], [.s 58 0, .s 58 0], [.s 68 0, .s 68 0]], [.s 44 3, .s 44 3]⟩,
    ⟨6, 0, 9, 9, [[.s 45 0, .s 45 0], [.s 55 0, .s 55 0], [.s 59 0, .s 59 0], [.s 69 0, .s 69 0]], [.s 45 3, .s 45 3]⟩,
    ⟨6, 0, 10, 7, [[.s 46 0, .s 46 0], [.s 47 0, .s 47 0], [.s 56 0, .s 56 0], [.s 59 0, .s 59 0], [.s 70 0, .s 70 0]], [.s 46 4, .s 46 4]⟩,
    ⟨6, 0, 11, 8, [[.s 47 0, .s 47 0], [.s 57 0, .s 57 0], [.s 58 0, .s 58 0], [.s 70 0, .s 70 0], [.s 71 0, .s 71 0]], [.s 47 4, .s 47 4]⟩,
    ⟨7, 0, 0, 13, [[.s 48 0, .s 48 0], [.s 49 0, .s 49 0], [.f ⟨18, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 2, 0, 0, 0, 1, 0, 1, 0⟩], [.s 72 0, .s 72 0]], [.s 48 3, .s 48 3]⟩,
    ⟨7, 0, 1, 13, [[.s 49 0, .s 49 0], [.s 63 0, .s 63 0], [.s 72 0, .s 72 0], [.s 73 0, .s 73 0]], [.s 49 3, .s 49 3]⟩,
    ⟨7, 0, 2, 9, [[.s 50 0, .s 50 0], [.s 53 0, .s 53 0], [.s 65 0, .s 65 0], [.f ⟨20, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 12, 1, 0, 1, 0, 0, 0, 0⟩], [.s 74 0, .s 74 0]], [.s 50 4, .s 50 4]⟩,
    ⟨7, 0, 3, 12, [[.s 51 0, .s 51 0], [.s 61 0, .s 61 0], [.s 64 0, .s 64 0], [.s 75 0, .s 75 0], [.s 76 0, .s 76 0]], [.s 51 3, .s 51 3]⟩,
    ⟨7, 0, 4, 11, [[.s 51 0, .s 51 0], [.s 52 0, .s 52 0], [.s 55 0, .s 55 0], [.s 63 0, .s 63 0], [.s 67 0, .s 67 0], [.s 76 0, .s 76 0]], [.s 52 5, .s 52 5]⟩,
    ⟨7, 0, 5, 9, [[.s 53 0, .s 53 0], [.s 62 0, .s 62 0], [.s 66 0, .s 66 0], [.s 74 0, .s 74 0], [.s 77 0, .s 77 0], [.s 78 0, .s 78 0]], [.s 53 4, .s 53 4]⟩,
    ⟨7, 0, 6, 8, [[.s 53 0, .s 53 0], [.s 54 0, .s 54 0], [.s 65 0, .s 65 0], [.s 68 0, .s 68 0], [.s 78 0, .s 78 0]], [.s 54 4, .s 54 4]⟩,
    ⟨7, 0, 7, 11, [[.s 55 0, .s 55 0], [.s 64 0, .s 64 0], [.s 69 0, .s 69 0], [.s 76 0, .s 76 0], [.s 79 0, .s 79 0]], [.s 55 4, .s 55 4]⟩,
    ⟨7, 0, 8, 7, [[.s 56 0, .s 56 0], [.s 66 0, .s 66 0], [.s 70 0, .s 70 0], [.s 80 0, .s 80 0]], [.s 56 3, .s 56 3]⟩,
    ⟨7, 0, 9, 10, [[.s 57 0, .s 57 0], [.s 67 0, .s 67 0], [.s 71 0, .s 71 0], [.s 81 0, .s 81 0]], [.s 57 3, .s 57 3]⟩,
    ⟨7, 0, 10, 8, [[.s 58 0, .s 58 0], [.s 59 0, .s 59 0], [.s 68 0, .s 68 0], [.s 71 0, .s 71 0], [.s 82 0, .s 82 0]], [.s 58 4, .s 58 4]⟩,
    ⟨7, 0, 11, 9, [[.s 59 0, .s 59 0], [.s 69 0, .s 69 0], [.s 70 0, .s 70 0], [.s 82 0, .s 82 0], [.s 83 0, .s 83 0]], [.s 59 4, .s 59 4]⟩,
    ⟨8, 0, 0, 14, [[.s 60 0, .s 60 0], [.s 61 0, .s 61 0], [.f ⟨18, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 14, 0, 0, 0, 1, 0, 1, 0⟩], [.s 84 0, .s 84 0]], [.s 60 3, .s 60 3]⟩,
    ⟨8, 0, 1, 14, [[.s 61 0, .s 61 0], [.s 75 0, .s 75 0], [.s 84 0, .s 84 0], [.s 85 0, .s 85 0]], [.s 61 3, .s 61 3]⟩,
    ⟨8, 0, 2, 10, [[.s 62 0, .s 62 0], [.s 65 0, .s 65 0], [.s 77 0, .s 77 0], [.f ⟨20, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 24, 1, 0, 1, 0, 0, 0, 0⟩], [.s 86 0, .s 86 0]], [.s 62 4, .s 62 4]⟩,
    ⟨8, 0, 3, 13, [[.s 63 0, .s 63 0], [.s 73 0, .s 73 0], [.s 76 0, .s 76 0], [.s 87 0, .s 87 0], [.s 88 0, .s 88 0]], [.s 63 3, .s 63 3]⟩,
    ⟨8, 0, 4, 12, [[.s 63 0, .s 63 0], [.s 64 0, .s 64 0], [.s 67 0, .s 67 0], [.s 75 0, .s 75 0], [.s 79 0, .s 79 0], [.s 88 0, .s 88 0]], [.s 64 5, .s 64 5]⟩,
    ⟨8, 0, 5, 10, [[.s 65 0, .s 65 0], [.s 74 0, .s 74 0], [.s 78 0, .s 78 0], [.s 86 0, .s 86 0], [.s 89 0, .s 89 0], [.s 90 0, .s 90 0]], [.s 65 4, .s 65 4]⟩,
    ⟨8, 0, 6, 9, [[.s 65 0, .s 65 0], [.s 66 0, .s 66 0], [.s 77 0, .s 77 0], [.s 80 0, .s 80 0], [.s 90 0, .s 90 0]], [.s 66 4, .s 66 4]⟩,
    ⟨8, 0, 7, 12, [[.s 67 0, .s 67 0], [.s 76 0, .s 76 0], [.s 81 0, .s 81 0], [.s 88 0, .s 88 0], [.s 91 0, .s 91 0]], [.s 67 4, .s 67 4]⟩,
    ⟨8, 0, 8, 8, [[.s 68 0, .s 68 0], [.s 78 0, .s 78 0], [.s 82 0, .s 82 0], [.s 92 0, .s 92 0]], [.s 68 3, .s 68 3]⟩,
    ⟨8, 0, 9, 11, [[.s 69 0, .s 69 0], [.s 79 0, .s 79 0], [.s 83 0, .s 83 0], [.s 93 0, .s 93 0]], [.s 69 3, .s 69 3]⟩,
    ⟨8, 0, 10, 9, [[.s 70 0, .s 70 0], [.s 71 0, .s 71 0], [.s 80 0, .s 80 0], [.s 83 0, .s 83 0], [.s 94 0, .s 94 0]], [.s 70 4, .s 70 4]⟩,
    ⟨8, 0, 11, 10, [[.s 71 0, .s 71 0], [.s 81 0, .s 81 0], [.s 82 0, .s 82 0], [.s 94 0, .s 94 0], [.s 95 0, .s 95 0]], [.s 71 4, .s 71 4]⟩,
    ⟨9, 0, 0, 15, [[.s 72 0, .s 72 0], [.s 73 0, .s 73 0], [.f ⟨18, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 26, 0, 0, 0, 1, 0, 1, 0⟩], [.s 96 0, .s 96 0]], [.s 72 3, .s 72 3]⟩,
    ⟨9, 0, 1, 15, [[.s 73 0, .s 73 0], [.s 87 0, .s 87 0], [.s 96 0, .s 96 0], [.s 97 0, .s 97 0]], [.s 73 3, .s 73 3]⟩,
    ⟨9, 0, 2, 11, [[.s 74 0, .s 74 0], [.s 77 0, .s 77 0], [.s 89 0, .s 89 0], [.f ⟨20, 36, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 36, 1, 0, 1, 0, 0, 0, 0⟩], [.s 98 0, .s 98 0]], [.s 74 4, .s 74 4]⟩,
    ⟨9, 0, 3, 14, [[.s 75 0, .s 75 0], [.s 85 0, .s 85 0], [.s 88 0, .s 88 0], [.s 99 0, .s 99 0], [.s 100 0, .s 100 0]], [.s 75 3, .s 75 3]⟩,
    ⟨9, 0, 4, 13, [[.s 75 0, .s 75 0], [.s 76 0, .s 76 0], [.s 79 0, .s 79 0], [.s 87 0, .s 87 0], [.s 91 0, .s 91 0], [.s 100 0, .s 100 0]], [.s 76 5, .s 76 5]⟩,
    ⟨9, 0, 5, 11, [[.s 77 0, .s 77 0], [.s 86 0, .s 86 0], [.s 90 0, .s 90 0], [.s 98 0, .s 98 0], [.s 101 0, .s 101 0], [.s 102 0, .s 102 0]], [.s 77 4, .s 77 4]⟩,
    ⟨9, 0, 6, 10, [[.s 77 0, .s 77 0], [.s 78 0, .s 78 0], [.s 89 0, .s 89 0], [.s 92 0, .s 92 0], [.s 102 0, .s 102 0]], [.s 78 4, .s 78 4]⟩,
    ⟨9, 0, 7, 13, [[.s 79 0, .s 79 0], [.s 88 0, .s 88 0], [.s 93 0, .s 93 0], [.s 100 0, .s 100 0], [.s 103 0, .s 103 0]], [.s 79 4, .s 79 4]⟩,
    ⟨9, 0, 8, 9, [[.s 80 0, .s 80 0], [.s 90 0, .s 90 0], [.s 94 0, .s 94 0], [.s 104 0, .s 104 0]], [.s 80 3, .s 80 3]⟩,
    ⟨9, 0, 9, 12, [[.s 81 0, .s 81 0], [.s 91 0, .s 91 0], [.s 95 0, .s 95 0], [.s 105 0, .s 105 0]], [.s 81 3, .s 81 3]⟩,
    ⟨9, 0, 10, 10, [[.s 82 0, .s 82 0], [.s 83 0, .s 83 0], [.s 92 0, .s 92 0], [.s 95 0, .s 95 0], [.s 106 0, .s 106 0]], [.s 82 4, .s 82 4]⟩,
    ⟨9, 0, 11, 11, [[.s 83 0, .s 83 0], [.s 93 0, .s 93 0], [.s 94 0, .s 94 0], [.s 106 0, .s 106 0], [.s 107 0, .s 107 0]], [.s 83 4, .s 83 4]⟩,
    ⟨10, 0, 0, 16, [[.s 84 0, .s 84 0], [.s 85 0, .s 85 0], [.f ⟨18, 38, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 38, 0, 0, 0, 1, 0, 1, 0⟩], [.s 108 0, .s 108 0]], [.s 84 3, .s 84 3]⟩,
    ⟨10, 0, 1, 16, [[.s 85 0, .s 85 0], [.s 99 0, .s 99 0], [.s 108 0, .s 108 0], [.s 109 0, .s 109 0]], [.s 85 3, .s 85 3]⟩,
    ⟨10, 0, 2, 12, [[.s 86 0, .s 86 0], [.s 89 0, .s 89 0], [.s 101 0, .s 101 0], [.f ⟨20, 48, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 48, 1, 0, 1, 0, 0, 0, 0⟩], [.s 110 0, .s 110 0]], [.s 86 4, .s 86 4]⟩,
    ⟨10, 0, 3, 15, [[.s 87 0, .s 87 0], [.s 97 0, .s 97 0], [.s 100 0, .s 100 0], [.s 111 0, .s 111 0], [.s 112 0, .s 112 0]], [.s 87 3, .s 87 3]⟩,
    ⟨10, 0, 4, 14, [[.s 87 0, .s 87 0], [.s 88 0, .s 88 0], [.s 91 0, .s 91 0], [.s 99 0, .s 99 0], [.s 103 0, .s 103 0], [.s 112 0, .s 112 0]], [.s 88 5, .s 88 5]⟩,
    ⟨10, 0, 5, 12, [[.s 89 0, .s 89 0], [.s 98 0, .s 98 0], [.s 102 0, .s 102 0], [.s 110 0, .s 110 0], [.s 113 0, .s 113 0], [.s 114 0, .s 114 0]], [.s 89 4, .s 89 4]⟩,
    ⟨10, 0, 6, 11, [[.s 89 0, .s 89 0], [.s 90 0, .s 90 0], [.s 101 0, .s 101 0], [.s 104 0, .s 104 0], [.s 114 0, .s 114 0]], [.s 90 4, .s 90 4]⟩,
    ⟨10, 0, 7, 14, [[.s 91 0, .s 91 0], [.s 100 0, .s 100 0], [.s 105 0, .s 105 0], [.s 112 0, .s 112 0], [.s 115 0, .s 115 0]], [.s 91 4, .s 91 4]⟩,
    ⟨10, 0, 8, 10, [[.s 92 0, .s 92 0], [.s 102 0, .s 102 0], [.s 106 0, .s 106 0], [.s 116 0, .s 116 0]], [.s 92 3, .s 92 3]⟩,
    ⟨10, 0, 9, 13, [[.s 93 0, .s 93 0], [.s 103 0, .s 103 0], [.s 107 0, .s 107 0], [.s 117 0, .s 117 0]], [.s 93 3, .s 93 3]⟩,
    ⟨10, 0, 10, 11, [[.s 94 0, .s 94 0], [.s 95 0, .s 95 0], [.s 104 0, .s 104 0], [.s 107 0, .s 107 0], [.s 118 0, .s 118 0]], [.s 94 4, .s 94 4]⟩,
    ⟨10, 0, 11, 12, [[.s 95 0, .s 95 0], [.s 105 0, .s 105 0], [.s 106 0, .s 106 0], [.s 118 0, .s 118 0], [.s 119 0, .s 119 0]], [.s 95 4, .s 95 4]⟩,
    ⟨11, 0, 0, 17, [[.s 96 0, .s 96 0], [.s 97 0, .s 97 0], [.f ⟨18, 50, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 50, 0, 0, 0, 1, 0, 1, 0⟩], [.s 120 0, .s 120 0]], [.s 96 3, .s 96 3]⟩,
    ⟨11, 0, 1, 17, [[.s 97 0, .s 97 0], [.s 111 0, .s 111 0], [.s 120 0, .s 120 0], [.s 121 0, .s 121 0]], [.s 97 3, .s 97 3]⟩,
    ⟨11, 0, 2, 13, [[.s 98 0, .s 98 0], [.s 101 0, .s 101 0], [.s 113 0, .s 113 0], [.f ⟨20, 60, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 60, 1, 0, 1, 0, 0, 0, 0⟩], [.s 122 0, .s 122 0]], [.s 98 4, .s 98 4]⟩,
    ⟨11, 0, 3, 16, [[.s 99 0, .s 99 0], [.s 109 0, .s 109 0], [.s 112 0, .s 112 0], [.s 123 0, .s 123 0], [.s 124 0, .s 124 0]], [.s 99 3, .s 99 3]⟩,
    ⟨11, 0, 4, 15, [[.s 99 0, .s 99 0], [.s 100 0, .s 100 0], [.s 103 0, .s 103 0], [.s 111 0, .s 111 0], [.s 115 0, .s 115 0], [.s 124 0, .s 124 0]], [.s 100 5, .s 100 5]⟩,
    ⟨11, 0, 5, 13, [[.s 101 0, .s 101 0], [.s 110 0, .s 110 0], [.s 114 0, .s 114 0], [.s 122 0, .s 122 0], [.s 125 0, .s 125 0], [.s 126 0, .s 126 0]], [.s 101 4, .s 101 4]⟩,
    ⟨11, 0, 6, 12, [[.s 101 0, .s 101 0], [.s 102 0, .s 102 0], [.s 113 0, .s 113 0], [.s 116 0, .s 116 0], [.s 126 0, .s 126 0]], [.s 102 4, .s 102 4]⟩,
    ⟨11, 0, 7, 15, [[.s 103 0, .s 103 0], [.s 112 0, .s 112 0], [.s 117 0, .s 117 0], [.s 124 0, .s 124 0], [.s 127 0, .s 127 0]], [.s 103 4, .s 103 4]⟩,
    ⟨11, 0, 8, 11, [[.s 104 0, .s 104 0], [.s 114 0, .s 114 0], [.s 118 0, .s 118 0], [.s 128 0, .s 128 0]], [.s 104 3, .s 104 3]⟩,
    ⟨11, 0, 9, 14, [[.s 105 0, .s 105 0], [.s 115 0, .s 115 0], [.s 119 0, .s 119 0], [.s 129 0, .s 129 0]], [.s 105 3, .s 105 3]⟩,
    ⟨11, 0, 10, 12, [[.s 106 0, .s 106 0], [.s 107 0, .s 107 0], [.s 116 0, .s 116 0], [.s 119 0, .s 119 0], [.s 130 0, .s 130 0]], [.s 106 4, .s 106 4]⟩,
    ⟨11, 0, 11, 13, [[.s 107 0, .s 107 0], [.s 117 0, .s 117 0], [.s 118 0, .s 118 0], [.s 130 0, .s 130 0], [.s 131 0, .s 131 0]], [.s 107 4, .s 107 4]⟩,
    ⟨12, 0, 0, 18, [[.s 108 0, .s 108 0], [.s 109 0, .s 109 0], [.f ⟨18, 62, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 62, 0, 0, 0, 1, 0, 1, 0⟩], [.s 132 0, .s 132 0]], [.s 108 3, .s 108 3]⟩,
    ⟨12, 0, 1, 18, [[.s 109 0, .s 109 0], [.s 123 0, .s 123 0], [.s 132 0, .s 132 0], [.s 133 0, .s 133 0]], [.s 109 3, .s 109 3]⟩,
    ⟨12, 0, 2, 14, [[.s 110 0, .s 110 0], [.s 113 0, .s 113 0], [.s 125 0, .s 125 0], [.f ⟨20, 72, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 72, 1, 0, 1, 0, 0, 0, 0⟩], [.s 134 0, .s 134 0]], [.s 110 4, .s 110 4]⟩,
    ⟨12, 0, 3, 17, [[.s 111 0, .s 111 0], [.s 121 0, .s 121 0], [.s 124 0, .s 124 0], [.s 135 0, .s 135 0], [.s 136 0, .s 136 0]], [.s 111 3, .s 111 3]⟩,
    ⟨12, 0, 4, 16, [[.s 111 0, .s 111 0], [.s 112 0, .s 112 0], [.s 115 0, .s 115 0], [.s 123 0, .s 123 0], [.s 127 0, .s 127 0], [.s 136 0, .s 136 0]], [.s 112 5, .s 112 5]⟩,
    ⟨12, 0, 5, 14, [[.s 113 0, .s 113 0], [.s 122 0, .s 122 0], [.s 126 0, .s 126 0], [.s 134 0, .s 134 0], [.s 137 0, .s 137 0], [.s 138 0, .s 138 0]], [.s 113 4, .s 113 4]⟩,
    ⟨12, 0, 6, 13, [[.s 113 0, .s 113 0], [.s 114 0, .s 114 0], [.s 125 0, .s 125 0], [.s 128 0, .s 128 0], [.s 138 0, .s 138 0]], [.s 114 4, .s 114 4]⟩,
    ⟨12, 0, 7, 16, [[.s 115 0, .s 115 0], [.s 124 0, .s 124 0], [.s 129 0, .s 129 0], [.s 136 0, .s 136 0], [.s 139 0, .s 139 0]], [.s 115 4, .s 115 4]⟩,
    ⟨12, 0, 8, 12, [[.s 116 0, .s 116 0], [.s 126 0, .s 126 0], [.s 130 0, .s 130 0], [.s 140 0, .s 140 0]], [.s 116 3, .s 116 3]⟩,
    ⟨12, 0, 9, 15, [[.s 117 0, .s 117 0], [.s 127 0, .s 127 0], [.s 131 0, .s 131 0], [.s 141 0, .s 141 0]], [.s 117 3, .s 117 3]⟩,
    ⟨12, 0, 10, 13, [[.s 118 0, .s 118 0], [.s 119 0, .s 119 0], [.s 128 0, .s 128 0], [.s 131 0, .s 131 0], [.s 142 0, .s 142 0]], [.s 118 4, .s 118 4]⟩,
    ⟨12, 0, 11, 14, [[.s 119 0, .s 119 0], [.s 129 0, .s 129 0], [.s 130 0, .s 130 0], [.s 142 0, .s 142 0], [.s 143 0, .s 143 0]], [.s 119 4, .s 119 4]⟩,
    ⟨13, 0, 0, 19, [[.s 120 0, .s 120 0], [.s 121 0, .s 121 0], [.f ⟨18, 74, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 74, 0, 0, 0, 1, 0, 1, 0⟩], [.s 0 0, .s 0 0]], [.s 120 3, .s 120 3]⟩,
    ⟨13, 0, 1, 19, [[.s 121 0, .s 121 0], [.s 135 0, .s 135 0], [.s 0 0, .s 0 0], [.s 1 0, .s 1 0]], [.s 121 3, .s 121 3]⟩,
    ⟨13, 0, 2, 15, [[.s 122 0, .s 122 0], [.s 125 0, .s 125 0], [.s 137 0, .s 137 0], [.f ⟨20, 84, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 84, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0]], [.s 122 4, .s 122 4]⟩,
    ⟨13, 0, 3, 18, [[.s 123 0, .s 123 0], [.s 133 0, .s 133 0], [.s 136 0, .s 136 0], [.s 3 0, .s 3 0], [.s 4 0, .s 4 0]], [.s 123 3, .s 123 3]⟩,
    ⟨13, 0, 4, 17, [[.s 123 0, .s 123 0], [.s 124 0, .s 124 0], [.s 127 0, .s 127 0], [.s 135 0, .s 135 0], [.s 139 0, .s 139 0], [.s 4 0, .s 4 0]], [.s 124 5, .s 124 5]⟩,
    ⟨13, 0, 5, 15, [[.s 125 0, .s 125 0], [.s 134 0, .s 134 0], [.s 138 0, .s 138 0], [.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 6 0, .s 6 0]], [.s 125 4, .s 125 4]⟩,
    ⟨13, 0, 6, 14, [[.s 125 0, .s 125 0], [.s 126 0, .s 126 0], [.s 137 0, .s 137 0], [.s 140 0, .s 140 0], [.s 6 0, .s 6 0]], [.s 126 4, .s 126 4]⟩,
    ⟨13, 0, 7, 17, [[.s 127 0, .s 127 0], [.s 136 0, .s 136 0], [.s 141 0, .s 141 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0]], [.s 127 4, .s 127 4]⟩,
    ⟨13, 0, 8, 13, [[.s 128 0, .s 128 0], [.s 138 0, .s 138 0], [.s 142 0, .s 142 0], [.s 8 0, .s 8 0]], [.s 128 3, .s 128 3]⟩,
    ⟨13, 0, 9, 16, [[.s 129 0, .s 129 0], [.s 139 0, .s 139 0], [.s 143 0, .s 143 0], [.s 9 0, .s 9 0]], [.s 129 3, .s 129 3]⟩,
    ⟨13, 0, 10, 14, [[.s 130 0, .s 130 0], [.s 131 0, .s 131 0], [.s 140 0, .s 140 0], [.s 143 0, .s 143 0], [.s 10 0, .s 10 0]], [.s 130 4, .s 130 4]⟩,
    ⟨13, 0, 11, 15, [[.s 131 0, .s 131 0], [.s 141 0, .s 141 0], [.s 142 0, .s 142 0], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0]], [.s 131 4, .s 131 4]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, 2, 0), (1, -2, 0), (2, 1, 1), (-2, -1, -5)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨2, 1, 0, 5, [[.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 0, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨2, 1, 1, 7, [[.f ⟨22, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.f ⟨19, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 1, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 1, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨2, 1, 2, 15, [[.f ⟨22, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.f ⟨22, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 5, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨2, 1, 3, 8, [[.f ⟨22, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 4 0], [.f ⟨19, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 3, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨2, 1, 4, 8, [[.f ⟨22, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 7 0], [.f ⟨19, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 3, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨2, 1, 5, 14, [[.f ⟨22, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 6 0], [.f ⟨19, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 2]⟩,
    ⟨2, 1, 6, 13, [[.f ⟨22, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.s 8 0], [.f ⟨19, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 1]⟩,
    ⟨2, 1, 7, 9, [[.f ⟨22, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 9 0], [.f ⟨19, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 7, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 7, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨2, 1, 8, 12, [[.f ⟨22, 8, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 10 0], [.f ⟨19, 8, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 10 2]⟩,
    ⟨2, 1, 9, 10, [[.f ⟨22, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 7 0], [.s 11 0], [.f ⟨19, 9, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 9, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨2, 1, 10, 11, [[.f ⟨22, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 8 0], [.s 11 0], [.f ⟨19, 10, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨2, 1, 11, 11, [[.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 9 0], [.s 10 0], [.f ⟨19, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨19, 11, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 4⟩]⟩]⟩,
  ⟨1, 2, 1, 0, 0, [(-1, 2, 0), (1, -2, 0), (2, 1, 10)], 2, 1, 10, 5, 0, 0, 0, 0,
   [⟨4, 2, 0, 17, [[.f ⟨22, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨22, 1, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 1, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨19, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨19, 14, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨19, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 0, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨22, 0, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨22, 0, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨4, 2, 1, 19, [[.f ⟨22, 1, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 1, 1, 0, 2, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.f ⟨19, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨19, 1, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 1, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨22, 1, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨22, 1, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨4, 2, 2, 27, [[.f ⟨22, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨22, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.f ⟨22, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 24, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨19, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 2, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨22, 5, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨22, 5, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨4, 2, 3, 20, [[.f ⟨22, 3, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 3, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.f ⟨19, 3, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 3, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨19, 4, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 4, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨22, 3, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨22, 3, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨4, 2, 4, 20, [[.f ⟨22, 3, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 3, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨22, 4, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 4, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨22, 7, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 7, 1, 0, 2, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.f ⟨19, 4, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 4, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨22, 3, 0, 0, 1, 0, 0, 0, 4⟩, .f ⟨22, 3, 1, 0, 2, 0, 0, 0, 4⟩]⟩,
    ⟨4, 2, 5, 26, [[.f ⟨22, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.f ⟨19, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨19, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨19, 6, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 6, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨4, 2, 6, 25, [[.f ⟨22, 5, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 5, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨22, 6, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 6, 1, 0, 2, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.f ⟨19, 6, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 6, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 8 1, .s 8 1]⟩,
    ⟨4, 2, 7, 21, [[.f ⟨22, 7, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 7, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.f ⟨19, 4, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 4, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨19, 7, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 7, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨22, 7, 0, 0, 1, 0, 0, 0, 4⟩, .f ⟨22, 7, 1, 0, 2, 0, 0, 0, 4⟩]⟩,
    ⟨4, 2, 8, 24, [[.f ⟨22, 8, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 8, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.f ⟨19, 8, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 8, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 10 2, .s 10 2]⟩,
    ⟨4, 2, 9, 22, [[.f ⟨22, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 9, 1, 0, 2, 0, 0, 0, 0⟩], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.f ⟨19, 9, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 9, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨22, 9, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨22, 9, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨4, 2, 10, 23, [[.f ⟨22, 10, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 10, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨22, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.f ⟨19, 10, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 10, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨22, 11, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨22, 11, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨4, 2, 11, 23, [[.f ⟨22, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 11, 1, 0, 2, 0, 0, 0, 0⟩], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.f ⟨19, 10, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 10, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨19, 11, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨19, 11, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨22, 11, 0, 0, 1, 0, 0, 0, 4⟩, .f ⟨22, 11, 1, 0, 2, 0, 0, 0, 4⟩]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, -3, 0), (1, 3, 0), (-3, 1, 1), (3, -1, -10)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-3, 1, 0, 6, [[.f ⟨25, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨25, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨12, 14, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 24, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨12, 14, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-3, 1, 1, 6, [[.f ⟨25, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.f ⟨23, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 25, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨23, 24, 0, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨-3, 1, 2, 15, [[.f ⟨25, 26, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨25, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.f ⟨23, 12, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 26, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨25, 29, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-3, 1, 3, 7, [[.f ⟨25, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 4 0], [.f ⟨23, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 28, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 1 1]⟩,
    ⟨-3, 1, 4, 8, [[.f ⟨25, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨25, 28, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨25, 31, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 7 0], [.f ⟨23, 28, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 3 2]⟩,
    ⟨-3, 1, 5, 14, [[.f ⟨25, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 6 0], [.f ⟨23, 26, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 30, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 6 2]⟩,
    ⟨-3, 1, 6, 13, [[.f ⟨25, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨25, 30, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.s 8 0], [.f ⟨23, 30, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 1]⟩,
    ⟨-3, 1, 7, 8, [[.f ⟨25, 31, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 9 0], [.f ⟨23, 28, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 31, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨23, 28, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-3, 1, 8, 12, [[.f ⟨25, 32, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 10 0], [.f ⟨23, 32, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 10 2]⟩,
    ⟨-3, 1, 9, 9, [[.f ⟨25, 33, 0, 0, 0, 0, 0, 0, 0⟩], [.s 7 0], [.s 11 0], [.f ⟨23, 33, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 7 2]⟩,
    ⟨-3, 1, 10, 11, [[.f ⟨25, 34, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨25, 35, 0, 0, 0, 0, 0, 0, 0⟩], [.s 8 0], [.s 11 0], [.f ⟨23, 34, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 11 2]⟩,
    ⟨-3, 1, 11, 10, [[.f ⟨25, 35, 0, 0, 0, 0, 0, 0, 0⟩], [.s 9 0], [.s 10 0], [.f ⟨23, 34, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 35, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 9 2]⟩]⟩,
  ⟨1, -3, 1, 0, 0, [(-1, -3, 0), (1, 3, 0), (-3, 1, 20)], -3, 1, 20, 10, 0, 0, 0, 0,
   [⟨-6, 2, 0, 18, [[.f ⟨25, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 24, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨25, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨25, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨23, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 24, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨25, 2, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨25, 2, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-6, 2, 1, 18, [[.f ⟨25, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 25, 1, 0, 2, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.f ⟨23, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 24, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨23, 25, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 25, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨23, 24, 0, 0, 1, 0, 0, 0, 1⟩, .f ⟨23, 24, 1, 0, 2, 0, 0, 0, 1⟩]⟩,
    ⟨-6, 2, 2, 27, [[.f ⟨25, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 26, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨25, 29, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 29, 1, 0, 2, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.f ⟨23, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 12, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨23, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 26, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨25, 29, 0, 0, 1, 0, 0, 0, 3⟩, .f ⟨25, 29, 1, 0, 2, 0, 0, 0, 3⟩]⟩,
    ⟨-6, 2, 3, 19, [[.f ⟨25, 27, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 27, 1, 0, 2, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.f ⟨23, 27, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 27, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨23, 28, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 28, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 1 1, .s 1 1]⟩,
    ⟨-6, 2, 4, 20, [[.f ⟨25, 27, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 27, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨25, 28, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 28, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨25, 31, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 31, 1, 0, 2, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.f ⟨23, 28, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 28, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 3 2, .s 3 2]⟩,
    ⟨-6, 2, 5, 26, [[.f ⟨25, 29, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 29, 1, 0, 2, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.f ⟨23, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 26, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨23, 29, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 29, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨23, 30, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 30, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨-6, 2, 6, 25, [[.f ⟨25, 29, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 29, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨25, 30, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 30, 1, 0, 2, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.f ⟨23, 30, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 30, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 8 1, .s 8 1]⟩,
    ⟨-6, 2, 7, 20, [[.f ⟨25, 31, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 31, 1, 0, 2, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.f ⟨23, 28, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 28, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨23, 31, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 31, 1, 0, 2, 0, 0, 0, 0⟩]], [.f ⟨23, 28, 0, 0, 1, 0, 0, 0, 2⟩, .f ⟨23, 28, 1, 0, 2, 0, 0, 0, 2⟩]⟩,
    ⟨-6, 2, 8, 24, [[.f ⟨25, 32, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 32, 1, 0, 2, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.f ⟨23, 32, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 32, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 10 2, .s 10 2]⟩,
    ⟨-6, 2, 9, 21, [[.f ⟨25, 33, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 33, 1, 0, 2, 0, 0, 0, 0⟩], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.f ⟨23, 33, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 33, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 7 2, .s 7 2]⟩,
    ⟨-6, 2, 10, 23, [[.f ⟨25, 34, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 34, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨25, 35, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 35, 1, 0, 2, 0, 0, 0, 0⟩], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.f ⟨23, 34, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 34, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 11 2, .s 11 2]⟩,
    ⟨-6, 2, 11, 22, [[.f ⟨25, 35, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 35, 1, 0, 2, 0, 0, 0, 0⟩], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.f ⟨23, 34, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 34, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨23, 35, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 35, 1, 0, 2, 0, 0, 0, 0⟩]], [.s 9 2, .s 9 2]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 1), (1, 0, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, 0, 0, 8, [[.f ⟨12, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨12, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 26, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨12, 1, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-1, 0, 1, 7, [[.f ⟨12, 1, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 3 1]⟩,
    ⟨-1, 0, 2, 3, [[.f ⟨12, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨12, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.f ⟨21, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 5 1]⟩,
    ⟨-1, 0, 3, 6, [[.f ⟨12, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 4 0], [.f ⟨0, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 4 3]⟩,
    ⟨-1, 0, 4, 5, [[.f ⟨12, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨12, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨12, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 7 0], [.f ⟨0, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 7 1]⟩,
    ⟨-1, 0, 5, 2, [[.f ⟨12, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 6 0], [.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 6, 2, [[.f ⟨12, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨12, 6, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.s 8 0], [.f ⟨0, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 1]⟩,
    ⟨-1, 0, 7, 4, [[.f ⟨12, 7, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 9 0], [.f ⟨0, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 7, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 9 1]⟩,
    ⟨-1, 0, 8, 1, [[.f ⟨12, 8, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 10 0], [.f ⟨0, 8, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 8, 0, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-1, 0, 9, 3, [[.f ⟨12, 9, 0, 0, 0, 0, 0, 0, 0⟩], [.s 7 0], [.s 11 0], [.f ⟨0, 9, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 11 1]⟩,
    ⟨-1, 0, 10, 2, [[.f ⟨12, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨12, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 8 0], [.s 11 0], [.f ⟨0, 10, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 8 2]⟩,
    ⟨-1, 0, 11, 2, [[.f ⟨12, 11, 0, 0, 0, 0, 0, 0, 0⟩], [.s 9 0], [.s 10 0], [.f ⟨0, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨0, 11, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 10, 0, 0, 0, 0, 0, 0, 1⟩]⟩]⟩,
  ⟨1, -12, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 2)], -1, 0, 2, 12, 0, 0, 0, 0,
   [⟨-2, 0, 0, 9, [[.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.f ⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 38, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 132 0]], [.s 13 2, .s 13 2]⟩,
    ⟨-2, 0, 1, 7, [[.s 13 0, .s 13 0], [.s 3 0, .s 3 0], [.f ⟨11, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 132 0], [.f ⟨11, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 133 0]], [.s 3 1, .s 3 1]⟩,
    ⟨-2, 0, 2, 4, [[.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 5 0, .s 5 0], [.f ⟨23, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 48, 0, 0, 0, 1, 0, 0, 0⟩], [.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 134 0]], [.s 5 1, .s 5 1]⟩,
    ⟨-2, 0, 3, 6, [[.s 15 0, .s 15 0], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.f ⟨11, 3, 0, 0, 0, 0, 0, 0, 0⟩, .s 135 0], [.f ⟨11, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 136 0]], [.f ⟨11, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 135 0]⟩,
    ⟨-2, 0, 4, 6, [[.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.f ⟨11, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 136 0]], [.s 7 1, .s 7 1]⟩,
    ⟨-2, 0, 5, 3, [[.s 17 0, .s 17 0], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 134 0], [.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 137 0], [.f ⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 138 0]], [.f ⟨11, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 137 0]⟩,
    ⟨-2, 0, 6, 3, [[.s 17 0, .s 17 0], [.s 18 0, .s 18 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.f ⟨11, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 138 0]], [.s 8 1, .s 8 1]⟩,
    ⟨-2, 0, 7, 5, [[.s 19 0, .s 19 0], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.f ⟨11, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 136 0], [.f ⟨11, 7, 0, 0, 0, 0, 0, 0, 0⟩, .s 139 0]], [.s 9 1, .s 9 1]⟩,
    ⟨-2, 0, 8, 2, [[.s 20 0, .s 20 0], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.f ⟨11, 8, 0, 0, 0, 0, 0, 0, 0⟩, .s 140 0]], [.f ⟨11, 8, 0, 0, 0, 0, 0, 0, 0⟩, .s 140 0]⟩,
    ⟨-2, 0, 9, 4, [[.s 21 0, .s 21 0], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.f ⟨11, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 141 0]], [.s 11 1, .s 11 1]⟩,
    ⟨-2, 0, 10, 3, [[.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.f ⟨11, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 142 0]], [.s 8 2, .s 8 2]⟩,
    ⟨-2, 0, 11, 3, [[.s 23 0, .s 23 0], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.f ⟨11, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 142 0], [.f ⟨11, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 143 0]], [.f ⟨11, 10, 0, 0, 0, 0, 0, 0, 1⟩, .s 142 1]⟩,
    ⟨-3, 0, 0, 10, [[.s 24 0, .s 24 0], [.s 25 0, .s 25 0], [.f ⟨27, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 26, 1, 0, 0, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0]], [.s 25 2, .s 25 2]⟩,
    ⟨-3, 0, 1, 8, [[.s 25 0, .s 25 0], [.s 15 0, .s 15 0], [.s 0 0, .s 0 0], [.s 1 0, .s 1 0]], [.s 15 1, .s 15 1]⟩,
    ⟨-3, 0, 2, 5, [[.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 17 0, .s 17 0], [.f ⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 36, 0, 0, 0, 1, 0, 0, 0⟩], [.s 2 0, .s 2 0]], [.s 17 1, .s 17 1]⟩,
    ⟨-3, 0, 3, 7, [[.s 27 0, .s 27 0], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.s 3 0, .s 3 0], [.s 4 0, .s 4 0]], [.s 3 0, .s 3 0]⟩,
    ⟨-3, 0, 4, 7, [[.s 27 0, .s 27 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.s 4 0, .s 4 0]], [.s 19 1, .s 19 1]⟩,
    ⟨-3, 0, 5, 4, [[.s 29 0, .s 29 0], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 6 0, .s 6 0]], [.s 5 0, .s 5 0]⟩,
    ⟨-3, 0, 6, 4, [[.s 29 0, .s 29 0], [.s 30 0, .s 30 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 6 0, .s 6 0]], [.s 20 1, .s 20 1]⟩,
    ⟨-3, 0, 7, 6, [[.s 31 0, .s 31 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0]], [.s 21 1, .s 21 1]⟩,
    ⟨-3, 0, 8, 3, [[.s 32 0, .s 32 0], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.s 8 0, .s 8 0]], [.s 8 0, .s 8 0]⟩,
    ⟨-3, 0, 9, 5, [[.s 33 0, .s 33 0], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.s 9 0, .s 9 0]], [.s 23 1, .s 23 1]⟩,
    ⟨-3, 0, 10, 4, [[.s 34 0, .s 34 0], [.s 35 0, .s 35 0], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.s 10 0, .s 10 0]], [.s 20 2, .s 20 2]⟩,
    ⟨-3, 0, 11, 4, [[.s 35 0, .s 35 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0]], [.s 10 1, .s 10 1]⟩,
    ⟨-4, 0, 0, 11, [[.s 36 0, .s 36 0], [.s 37 0, .s 37 0], [.f ⟨27, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 14, 1, 0, 0, 0, 0, 0, 0⟩], [.s 12 0, .s 12 0]], [.s 37 2, .s 37 2]⟩,
    ⟨-4, 0, 1, 9, [[.s 37 0, .s 37 0], [.s 27 0, .s 27 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0]], [.s 27 1, .s 27 1]⟩,
    ⟨-4, 0, 2, 6, [[.s 38 0, .s 38 0], [.s 41 0, .s 41 0], [.s 29 0, .s 29 0], [.f ⟨25, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 24, 0, 0, 0, 1, 0, 0, 0⟩], [.s 14 0, .s 14 0]], [.s 29 1, .s 29 1]⟩,
    ⟨-4, 0, 3, 8, [[.s 39 0, .s 39 0], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0]], [.s 15 0, .s 15 0]⟩,
    ⟨-4, 0, 4, 8, [[.s 39 0, .s 39 0], [.s 40 0, .s 40 0], [.s 43 0, .s 43 0], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.s 16 0, .s 16 0]], [.s 31 1, .s 31 1]⟩,
    ⟨-4, 0, 5, 5, [[.s 41 0, .s 41 0], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 18 0, .s 18 0]], [.s 17 0, .s 17 0]⟩,
    ⟨-4, 0, 6, 5, [[.s 41 0, .s 41 0], [.s 42 0, .s 42 0], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.s 18 0, .s 18 0]], [.s 32 1, .s 32 1]⟩,
    ⟨-4, 0, 7, 7, [[.s 43 0, .s 43 0], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0]], [.s 33 1, .s 33 1]⟩,
    ⟨-4, 0, 8, 4, [[.s 44 0, .s 44 0], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.s 20 0, .s 20 0]], [.s 20 0, .s 20 0]⟩,
    ⟨-4, 0, 9, 6, [[.s 45 0, .s 45 0], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.s 21 0, .s 21 0]], [.s 35 1, .s 35 1]⟩,
    ⟨-4, 0, 10, 5, [[.s 46 0, .s 46 0], [.s 47 0, .s 47 0], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.s 22 0, .s 22 0]], [.s 32 2, .s 32 2]⟩,
    ⟨-4, 0, 11, 5, [[.s 47 0, .s 47 0], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 22 1, .s 22 1]⟩,
    ⟨-5, 0, 0, 12, [[.s 48 0, .s 48 0], [.s 49 0, .s 49 0], [.f ⟨27, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.s 24 0, .s 24 0]], [.s 49 2, .s 49 2]⟩,
    ⟨-5, 0, 1, 10, [[.s 49 0, .s 49 0], [.s 39 0, .s 39 0], [.s 24 0, .s 24 0], [.s 25 0, .s 25 0]], [.s 39 1, .s 39 1]⟩,
    ⟨-5, 0, 2, 7, [[.s 50 0, .s 50 0], [.s 53 0, .s 53 0], [.s 41 0, .s 41 0], [.f ⟨25, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 12, 0, 0, 0, 1, 0, 0, 0⟩], [.s 26 0, .s 26 0]], [.s 41 1, .s 41 1]⟩,
    ⟨-5, 0, 3, 9, [[.s 51 0, .s 51 0], [.s 37 0, .s 37 0], [.s 40 0, .s 40 0], [.s 27 0, .s 27 0], [.s 28 0, .s 28 0]], [.s 27 0, .s 27 0]⟩,
    ⟨-5, 0, 4, 9, [[.s 51 0, .s 51 0], [.s 52 0, .s 52 0], [.s 55 0, .s 55 0], [.s 39 0, .s 39 0], [.s 43 0, .s 43 0], [.s 28 0, .s 28 0]], [.s 43 1, .s 43 1]⟩,
    ⟨-5, 0, 5, 6, [[.s 53 0, .s 53 0], [.s 38 0, .s 38 0], [.s 42 0, .s 42 0], [.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 30 0, .s 30 0]], [.s 29 0, .s 29 0]⟩,
    ⟨-5, 0, 6, 6, [[.s 53 0, .s 53 0], [.s 54 0, .s 54 0], [.s 41 0, .s 41 0], [.s 44 0, .s 44 0], [.s 30 0, .s 30 0]], [.s 44 1, .s 44 1]⟩,
    ⟨-5, 0, 7, 8, [[.s 55 0, .s 55 0], [.s 40 0, .s 40 0], [.s 45 0, .s 45 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0]], [.s 45 1, .s 45 1]⟩,
    ⟨-5, 0, 8, 5, [[.s 56 0, .s 56 0], [.s 42 0, .s 42 0], [.s 46 0, .s 46 0], [.s 32 0, .s 32 0]], [.s 32 0, .s 32 0]⟩,
    ⟨-5, 0, 9, 7, [[.s 57 0, .s 57 0], [.s 43 0, .s 43 0], [.s 47 0, .s 47 0], [.s 33 0, .s 33 0]], [.s 47 1, .s 47 1]⟩,
    ⟨-5, 0, 10, 6, [[.s 58 0, .s 58 0], [.s 59 0, .s 59 0], [.s 44 0, .s 44 0], [.s 47 0, .s 47 0], [.s 34 0, .s 34 0]], [.s 44 2, .s 44 2]⟩,
    ⟨-5, 0, 11, 6, [[.s 59 0, .s 59 0], [.s 45 0, .s 45 0], [.s 46 0, .s 46 0], [.s 34 0, .s 34 0], [.s 35 0, .s 35 0]], [.s 34 1, .s 34 1]⟩,
    ⟨-6, 0, 0, 13, [[.s 60 0, .s 60 0], [.s 61 0, .s 61 0], [.f ⟨28, 134, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 134, 1, 0, 1, 0, 0, 0, 0⟩], [.s 36 0, .s 36 0]], [.s 61 2, .s 61 2]⟩,
    ⟨-6, 0, 1, 11, [[.s 61 0, .s 61 0], [.s 51 0, .s 51 0], [.s 36 0, .s 36 0], [.s 37 0, .s 37 0]], [.s 51 1, .s 51 1]⟩,
    ⟨-6, 0, 2, 8, [[.s 62 0, .s 62 0], [.s 65 0, .s 65 0], [.s 53 0, .s 53 0], [.f ⟨25, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 0, 0, 0, 0, 1, 0, 0, 0⟩], [.s 38 0, .s 38 0]], [.s 53 1, .s 53 1]⟩,
    ⟨-6, 0, 3, 10, [[.s 63 0, .s 63 0], [.s 49 0, .s 49 0], [.s 52 0, .s 52 0], [.s 39 0, .s 39 0], [.s 40 0, .s 40 0]], [.s 39 0, .s 39 0]⟩,
    ⟨-6, 0, 4, 10, [[.s 63 0, .s 63 0], [.s 64 0, .s 64 0], [.s 67 0, .s 67 0], [.s 51 0, .s 51 0], [.s 55 0, .s 55 0], [.s 40 0, .s 40 0]], [.s 55 1, .s 55 1]⟩,
    ⟨-6, 0, 5, 7, [[.s 65 0, .s 65 0], [.s 50 0, .s 50 0], [.s 54 0, .s 54 0], [.s 38 0, .s 38 0], [.s 41 0, .s 41 0], [.s 42 0, .s 42 0]], [.s 41 0, .s 41 0]⟩,
    ⟨-6, 0, 6, 7, [[.s 65 0, .s 65 0], [.s 66 0, .s 66 0], [.s 53 0, .s 53 0], [.s 56 0, .s 56 0], [.s 42 0, .s 42 0]], [.s 56 1, .s 56 1]⟩,
    ⟨-6, 0, 7, 9, [[.s 67 0, .s 67 0], [.s 52 0, .s 52 0], [.s 57 0, .s 57 0], [.s 40 0, .s 40 0], [.s 43 0, .s 43 0]], [.s 57 1, .s 57 1]⟩,
    ⟨-6, 0, 8, 6, [[.s 68 0, .s 68 0], [.s 54 0, .s 54 0], [.s 58 0, .s 58 0], [.s 44 0, .s 44 0]], [.s 44 0, .s 44 0]⟩,
    ⟨-6, 0, 9, 8, [[.s 69 0, .s 69 0], [.s 55 0, .s 55 0], [.s 59 0, .s 59 0], [.s 45 0, .s 45 0]], [.s 59 1, .s 59 1]⟩,
    ⟨-6, 0, 10, 7, [[.s 70 0, .s 70 0], [.s 71 0, .s 71 0], [.s 56 0, .s 56 0], [.s 59 0, .s 59 0], [.s 46 0, .s 46 0]], [.s 56 2, .s 56 2]⟩,
    ⟨-6, 0, 11, 7, [[.s 71 0, .s 71 0], [.s 57 0, .s 57 0], [.s 58 0, .s 58 0], [.s 46 0, .s 46 0], [.s 47 0, .s 47 0]], [.s 46 1, .s 46 1]⟩,
    ⟨-7, 0, 0, 14, [[.s 72 0, .s 72 0], [.s 73 0, .s 73 0], [.f ⟨28, 122, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 122, 1, 0, 1, 0, 0, 0, 0⟩], [.s 48 0, .s 48 0]], [.s 73 2, .s 73 2]⟩,
    ⟨-7, 0, 1, 12, [[.s 73 0, .s 73 0], [.s 63 0, .s 63 0], [.s 48 0, .s 48 0], [.s 49 0, .s 49 0]], [.s 63 1, .s 63 1]⟩,
    ⟨-7, 0, 2, 9, [[.s 74 0, .s 74 0], [.s 77 0, .s 77 0], [.s 65 0, .s 65 0], [.f ⟨26, 132, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 132, 0, 0, 0, 1, 0, 1, 0⟩], [.s 50 0, .s 50 0]], [.s 65 1, .s 65 1]⟩,
    ⟨-7, 0, 3, 11, [[.s 75 0, .s 75 0], [.s 61 0, .s 61 0], [.s 64 0, .s 64 0], [.s 51 0, .s 51 0], [.s 52 0, .s 52 0]], [.s 51 0, .s 51 0]⟩,
    ⟨-7, 0, 4, 11, [[.s 75 0, .s 75 0], [.s 76 0, .s 76 0], [.s 79 0, .s 79 0], [.s 63 0, .s 63 0], [.s 67 0, .s 67 0], [.s 52 0, .s 52 0]], [.s 67 1, .s 67 1]⟩,
    ⟨-7, 0, 5, 8, [[.s 77 0, .s 77 0], [.s 62 0, .s 62 0], [.s 66 0, .s 66 0], [.s 50 0, .s 50 0], [.s 53 0, .s 53 0], [.s 54 0, .s 54 0]], [.s 53 0, .s 53 0]⟩,
    ⟨-7, 0, 6, 8, [[.s 77 0, .s 77 0], [.s 78 0, .s 78 0], [.s 65 0, .s 65 0], [.s 68 0, .s 68 0], [.s 54 0, .s 54 0]], [.s 68 1, .s 68 1]⟩,
    ⟨-7, 0, 7, 10, [[.s 79 0, .s 79 0], [.s 64 0, .s 64 0], [.s 69 0, .s 69 0], [.s 52 0, .s 52 0], [.s 55 0, .s 55 0]], [.s 69 1, .s 69 1]⟩,
    ⟨-7, 0, 8, 7, [[.s 80 0, .s 80 0], [.s 66 0, .s 66 0], [.s 70 0, .s 70 0], [.s 56 0, .s 56 0]], [.s 56 0, .s 56 0]⟩,
    ⟨-7, 0, 9, 9, [[.s 81 0, .s 81 0], [.s 67 0, .s 67 0], [.s 71 0, .s 71 0], [.s 57 0, .s 57 0]], [.s 71 1, .s 71 1]⟩,
    ⟨-7, 0, 10, 8, [[.s 82 0, .s 82 0], [.s 83 0, .s 83 0], [.s 68 0, .s 68 0], [.s 71 0, .s 71 0], [.s 58 0, .s 58 0]], [.s 68 2, .s 68 2]⟩,
    ⟨-7, 0, 11, 8, [[.s 83 0, .s 83 0], [.s 69 0, .s 69 0], [.s 70 0, .s 70 0], [.s 58 0, .s 58 0], [.s 59 0, .s 59 0]], [.s 58 1, .s 58 1]⟩,
    ⟨-8, 0, 0, 15, [[.s 84 0, .s 84 0], [.s 85 0, .s 85 0], [.f ⟨28, 110, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 110, 1, 0, 1, 0, 0, 0, 0⟩], [.s 60 0, .s 60 0]], [.s 85 2, .s 85 2]⟩,
    ⟨-8, 0, 1, 13, [[.s 85 0, .s 85 0], [.s 75 0, .s 75 0], [.s 60 0, .s 60 0], [.s 61 0, .s 61 0]], [.s 75 1, .s 75 1]⟩,
    ⟨-8, 0, 2, 10, [[.s 86 0, .s 86 0], [.s 89 0, .s 89 0], [.s 77 0, .s 77 0], [.f ⟨26, 120, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 120, 0, 0, 0, 1, 0, 1, 0⟩], [.s 62 0, .s 62 0]], [.s 77 1, .s 77 1]⟩,
    ⟨-8, 0, 3, 12, [[.s 87 0, .s 87 0], [.s 73 0, .s 73 0], [.s 76 0, .s 76 0], [.s 63 0, .s 63 0], [.s 64 0, .s 64 0]], [.s 63 0, .s 63 0]⟩,
    ⟨-8, 0, 4, 12, [[.s 87 0, .s 87 0], [.s 88 0, .s 88 0], [.s 91 0, .s 91 0], [.s 75 0, .s 75 0], [.s 79 0, .s 79 0], [.s 64 0, .s 64 0]], [.s 79 1, .s 79 1]⟩,
    ⟨-8, 0, 5, 9, [[.s 89 0, .s 89 0], [.s 74 0, .s 74 0], [.s 78 0, .s 78 0], [.s 62 0, .s 62 0], [.s 65 0, .s 65 0], [.s 66 0, .s 66 0]], [.s 65 0, .s 65 0]⟩,
    ⟨-8, 0, 6, 9, [[.s 89 0, .s 89 0], [.s 90 0, .s 90 0], [.s 77 0, .s 77 0], [.s 80 0, .s 80 0], [.s 66 0, .s 66 0]], [.s 80 1, .s 80 1]⟩,
    ⟨-8, 0, 7, 11, [[.s 91 0, .s 91 0], [.s 76 0, .s 76 0], [.s 81 0, .s 81 0], [.s 64 0, .s 64 0], [.s 67 0, .s 67 0]], [.s 81 1, .s 81 1]⟩,
    ⟨-8, 0, 8, 8, [[.s 92 0, .s 92 0], [.s 78 0, .s 78 0], [.s 82 0, .s 82 0], [.s 68 0, .s 68 0]], [.s 68 0, .s 68 0]⟩,
    ⟨-8, 0, 9, 10, [[.s 93 0, .s 93 0], [.s 79 0, .s 79 0], [.s 83 0, .s 83 0], [.s 69 0, .s 69 0]], [.s 83 1, .s 83 1]⟩,
    ⟨-8, 0, 10, 9, [[.s 94 0, .s 94 0], [.s 95 0, .s 95 0], [.s 80 0, .s 80 0], [.s 83 0, .s 83 0], [.s 70 0, .s 70 0]], [.s 80 2, .s 80 2]⟩,
    ⟨-8, 0, 11, 9, [[.s 95 0, .s 95 0], [.s 81 0, .s 81 0], [.s 82 0, .s 82 0], [.s 70 0, .s 70 0], [.s 71 0, .s 71 0]], [.s 70 1, .s 70 1]⟩,
    ⟨-9, 0, 0, 16, [[.s 96 0, .s 96 0], [.s 97 0, .s 97 0], [.f ⟨28, 98, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 98, 1, 0, 1, 0, 0, 0, 0⟩], [.s 72 0, .s 72 0]], [.s 97 2, .s 97 2]⟩,
    ⟨-9, 0, 1, 14, [[.s 97 0, .s 97 0], [.s 87 0, .s 87 0], [.s 72 0, .s 72 0], [.s 73 0, .s 73 0]], [.s 87 1, .s 87 1]⟩,
    ⟨-9, 0, 2, 11, [[.s 98 0, .s 98 0], [.s 101 0, .s 101 0], [.s 89 0, .s 89 0], [.f ⟨26, 108, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 108, 0, 0, 0, 1, 0, 1, 0⟩], [.s 74 0, .s 74 0]], [.s 89 1, .s 89 1]⟩,
    ⟨-9, 0, 3, 13, [[.s 99 0, .s 99 0], [.s 85 0, .s 85 0], [.s 88 0, .s 88 0], [.s 75 0, .s 75 0], [.s 76 0, .s 76 0]], [.s 75 0, .s 75 0]⟩,
    ⟨-9, 0, 4, 13, [[.s 99 0, .s 99 0], [.s 100 0, .s 100 0], [.s 103 0, .s 103 0], [.s 87 0, .s 87 0], [.s 91 0, .s 91 0], [.s 76 0, .s 76 0]], [.s 91 1, .s 91 1]⟩,
    ⟨-9, 0, 5, 10, [[.s 101 0, .s 101 0], [.s 86 0, .s 86 0], [.s 90 0, .s 90 0], [.s 74 0, .s 74 0], [.s 77 0, .s 77 0], [.s 78 0, .s 78 0]], [.s 77 0, .s 77 0]⟩,
    ⟨-9, 0, 6, 10, [[.s 101 0, .s 101 0], [.s 102 0, .s 102 0], [.s 89 0, .s 89 0], [.s 92 0, .s 92 0], [.s 78 0, .s 78 0]], [.s 92 1, .s 92 1]⟩,
    ⟨-9, 0, 7, 12, [[.s 103 0, .s 103 0], [.s 88 0, .s 88 0], [.s 93 0, .s 93 0], [.s 76 0, .s 76 0], [.s 79 0, .s 79 0]], [.s 93 1, .s 93 1]⟩,
    ⟨-9, 0, 8, 9, [[.s 104 0, .s 104 0], [.s 90 0, .s 90 0], [.s 94 0, .s 94 0], [.s 80 0, .s 80 0]], [.s 80 0, .s 80 0]⟩,
    ⟨-9, 0, 9, 11, [[.s 105 0, .s 105 0], [.s 91 0, .s 91 0], [.s 95 0, .s 95 0], [.s 81 0, .s 81 0]], [.s 95 1, .s 95 1]⟩,
    ⟨-9, 0, 10, 10, [[.s 106 0, .s 106 0], [.s 107 0, .s 107 0], [.s 92 0, .s 92 0], [.s 95 0, .s 95 0], [.s 82 0, .s 82 0]], [.s 92 2, .s 92 2]⟩,
    ⟨-9, 0, 11, 10, [[.s 107 0, .s 107 0], [.s 93 0, .s 93 0], [.s 94 0, .s 94 0], [.s 82 0, .s 82 0], [.s 83 0, .s 83 0]], [.s 82 1, .s 82 1]⟩,
    ⟨-10, 0, 0, 17, [[.s 108 0, .s 108 0], [.s 109 0, .s 109 0], [.f ⟨28, 86, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 86, 1, 0, 1, 0, 0, 0, 0⟩], [.s 84 0, .s 84 0]], [.s 109 2, .s 109 2]⟩,
    ⟨-10, 0, 1, 15, [[.s 109 0, .s 109 0], [.s 99 0, .s 99 0], [.s 84 0, .s 84 0], [.s 85 0, .s 85 0]], [.s 99 1, .s 99 1]⟩,
    ⟨-10, 0, 2, 12, [[.s 110 0, .s 110 0], [.s 113 0, .s 113 0], [.s 101 0, .s 101 0], [.f ⟨26, 96, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 96, 0, 0, 0, 1, 0, 1, 0⟩], [.s 86 0, .s 86 0]], [.s 101 1, .s 101 1]⟩,
    ⟨-10, 0, 3, 14, [[.s 111 0, .s 111 0], [.s 97 0, .s 97 0], [.s 100 0, .s 100 0], [.s 87 0, .s 87 0], [.s 88 0, .s 88 0]], [.s 87 0, .s 87 0]⟩,
    ⟨-10, 0, 4, 14, [[.s 111 0, .s 111 0], [.s 112 0, .s 112 0], [.s 115 0, .s 115 0], [.s 99 0, .s 99 0], [.s 103 0, .s 103 0], [.s 88 0, .s 88 0]], [.s 103 1, .s 103 1]⟩,
    ⟨-10, 0, 5, 11, [[.s 113 0, .s 113 0], [.s 98 0, .s 98 0], [.s 102 0, .s 102 0], [.s 86 0, .s 86 0], [.s 89 0, .s 89 0], [.s 90 0, .s 90 0]], [.s 89 0, .s 89 0]⟩,
    ⟨-10, 0, 6, 11, [[.s 113 0, .s 113 0], [.s 114 0, .s 114 0], [.s 101 0, .s 101 0], [.s 104 0, .s 104 0], [.s 90 0, .s 90 0]], [.s 104 1, .s 104 1]⟩,
    ⟨-10, 0, 7, 13, [[.s 115 0, .s 115 0], [.s 100 0, .s 100 0], [.s 105 0, .s 105 0], [.s 88 0, .s 88 0], [.s 91 0, .s 91 0]], [.s 105 1, .s 105 1]⟩,
    ⟨-10, 0, 8, 10, [[.s 116 0, .s 116 0], [.s 102 0, .s 102 0], [.s 106 0, .s 106 0], [.s 92 0, .s 92 0]], [.s 92 0, .s 92 0]⟩,
    ⟨-10, 0, 9, 12, [[.s 117 0, .s 117 0], [.s 103 0, .s 103 0], [.s 107 0, .s 107 0], [.s 93 0, .s 93 0]], [.s 107 1, .s 107 1]⟩,
    ⟨-10, 0, 10, 11, [[.s 118 0, .s 118 0], [.s 119 0, .s 119 0], [.s 104 0, .s 104 0], [.s 107 0, .s 107 0], [.s 94 0, .s 94 0]], [.s 104 2, .s 104 2]⟩,
    ⟨-10, 0, 11, 11, [[.s 119 0, .s 119 0], [.s 105 0, .s 105 0], [.s 106 0, .s 106 0], [.s 94 0, .s 94 0], [.s 95 0, .s 95 0]], [.s 94 1, .s 94 1]⟩,
    ⟨-11, 0, 0, 18, [[.s 120 0, .s 120 0], [.s 121 0, .s 121 0], [.f ⟨28, 74, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 74, 1, 0, 1, 0, 0, 0, 0⟩], [.s 96 0, .s 96 0]], [.s 121 2, .s 121 2]⟩,
    ⟨-11, 0, 1, 16, [[.s 121 0, .s 121 0], [.s 111 0, .s 111 0], [.s 96 0, .s 96 0], [.s 97 0, .s 97 0]], [.s 111 1, .s 111 1]⟩,
    ⟨-11, 0, 2, 13, [[.s 122 0, .s 122 0], [.s 125 0, .s 125 0], [.s 113 0, .s 113 0], [.f ⟨26, 84, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 84, 0, 0, 0, 1, 0, 1, 0⟩], [.s 98 0, .s 98 0]], [.s 113 1, .s 113 1]⟩,
    ⟨-11, 0, 3, 15, [[.s 123 0, .s 123 0], [.s 109 0, .s 109 0], [.s 112 0, .s 112 0], [.s 99 0, .s 99 0], [.s 100 0, .s 100 0]], [.s 99 0, .s 99 0]⟩,
    ⟨-11, 0, 4, 15, [[.s 123 0, .s 123 0], [.s 124 0, .s 124 0], [.s 127 0, .s 127 0], [.s 111 0, .s 111 0], [.s 115 0, .s 115 0], [.s 100 0, .s 100 0]], [.s 115 1, .s 115 1]⟩,
    ⟨-11, 0, 5, 12, [[.s 125 0, .s 125 0], [.s 110 0, .s 110 0], [.s 114 0, .s 114 0], [.s 98 0, .s 98 0], [.s 101 0, .s 101 0], [.s 102 0, .s 102 0]], [.s 101 0, .s 101 0]⟩,
    ⟨-11, 0, 6, 12, [[.s 125 0, .s 125 0], [.s 126 0, .s 126 0], [.s 113 0, .s 113 0], [.s 116 0, .s 116 0], [.s 102 0, .s 102 0]], [.s 116 1, .s 116 1]⟩,
    ⟨-11, 0, 7, 14, [[.s 127 0, .s 127 0], [.s 112 0, .s 112 0], [.s 117 0, .s 117 0], [.s 100 0, .s 100 0], [.s 103 0, .s 103 0]], [.s 117 1, .s 117 1]⟩,
    ⟨-11, 0, 8, 11, [[.s 128 0, .s 128 0], [.s 114 0, .s 114 0], [.s 118 0, .s 118 0], [.s 104 0, .s 104 0]], [.s 104 0, .s 104 0]⟩,
    ⟨-11, 0, 9, 13, [[.s 129 0, .s 129 0], [.s 115 0, .s 115 0], [.s 119 0, .s 119 0], [.s 105 0, .s 105 0]], [.s 119 1, .s 119 1]⟩,
    ⟨-11, 0, 10, 12, [[.s 130 0, .s 130 0], [.s 131 0, .s 131 0], [.s 116 0, .s 116 0], [.s 119 0, .s 119 0], [.s 106 0, .s 106 0]], [.s 116 2, .s 116 2]⟩,
    ⟨-11, 0, 11, 12, [[.s 131 0, .s 131 0], [.s 117 0, .s 117 0], [.s 118 0, .s 118 0], [.s 106 0, .s 106 0], [.s 107 0, .s 107 0]], [.s 106 1, .s 106 1]⟩,
    ⟨-12, 0, 0, 19, [[.s 132 0, .s 132 0], [.s 133 0, .s 133 0], [.f ⟨28, 62, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 62, 1, 0, 1, 0, 0, 0, 0⟩], [.s 108 0, .s 108 0]], [.s 133 2, .s 133 2]⟩,
    ⟨-12, 0, 1, 17, [[.s 133 0, .s 133 0], [.s 123 0, .s 123 0], [.s 108 0, .s 108 0], [.s 109 0, .s 109 0]], [.s 123 1, .s 123 1]⟩,
    ⟨-12, 0, 2, 14, [[.s 134 0, .s 134 0], [.s 137 0, .s 137 0], [.s 125 0, .s 125 0], [.f ⟨26, 72, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 72, 0, 0, 0, 1, 0, 1, 0⟩], [.s 110 0, .s 110 0]], [.s 125 1, .s 125 1]⟩,
    ⟨-12, 0, 3, 16, [[.s 135 0, .s 135 0], [.s 121 0, .s 121 0], [.s 124 0, .s 124 0], [.s 111 0, .s 111 0], [.s 112 0, .s 112 0]], [.s 111 0, .s 111 0]⟩,
    ⟨-12, 0, 4, 16, [[.s 135 0, .s 135 0], [.s 136 0, .s 136 0], [.s 139 0, .s 139 0], [.s 123 0, .s 123 0], [.s 127 0, .s 127 0], [.s 112 0, .s 112 0]], [.s 127 1, .s 127 1]⟩,
    ⟨-12, 0, 5, 13, [[.s 137 0, .s 137 0], [.s 122 0, .s 122 0], [.s 126 0, .s 126 0], [.s 110 0, .s 110 0], [.s 113 0, .s 113 0], [.s 114 0, .s 114 0]], [.s 113 0, .s 113 0]⟩,
    ⟨-12, 0, 6, 13, [[.s 137 0, .s 137 0], [.s 138 0, .s 138 0], [.s 125 0, .s 125 0], [.s 128 0, .s 128 0], [.s 114 0, .s 114 0]], [.s 128 1, .s 128 1]⟩,
    ⟨-12, 0, 7, 15, [[.s 139 0, .s 139 0], [.s 124 0, .s 124 0], [.s 129 0, .s 129 0], [.s 112 0, .s 112 0], [.s 115 0, .s 115 0]], [.s 129 1, .s 129 1]⟩,
    ⟨-12, 0, 8, 12, [[.s 140 0, .s 140 0], [.s 126 0, .s 126 0], [.s 130 0, .s 130 0], [.s 116 0, .s 116 0]], [.s 116 0, .s 116 0]⟩,
    ⟨-12, 0, 9, 14, [[.s 141 0, .s 141 0], [.s 127 0, .s 127 0], [.s 131 0, .s 131 0], [.s 117 0, .s 117 0]], [.s 131 1, .s 131 1]⟩,
    ⟨-12, 0, 10, 13, [[.s 142 0, .s 142 0], [.s 143 0, .s 143 0], [.s 128 0, .s 128 0], [.s 131 0, .s 131 0], [.s 118 0, .s 118 0]], [.s 128 2, .s 128 2]⟩,
    ⟨-12, 0, 11, 13, [[.s 143 0, .s 143 0], [.s 129 0, .s 129 0], [.s 130 0, .s 130 0], [.s 118 0, .s 118 0], [.s 119 0, .s 119 0]], [.s 118 1, .s 118 1]⟩,
    ⟨-13, 0, 0, 20, [[.s 0 0, .s 0 0], [.s 1 0, .s 1 0], [.f ⟨28, 50, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 50, 1, 0, 1, 0, 0, 0, 0⟩], [.s 120 0, .s 120 0]], [.s 1 2, .s 1 2]⟩,
    ⟨-13, 0, 1, 18, [[.s 1 0, .s 1 0], [.s 135 0, .s 135 0], [.s 120 0, .s 120 0], [.s 121 0, .s 121 0]], [.s 135 1, .s 135 1]⟩,
    ⟨-13, 0, 2, 15, [[.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 137 0, .s 137 0], [.f ⟨26, 60, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 60, 0, 0, 0, 1, 0, 1, 0⟩], [.s 122 0, .s 122 0]], [.s 137 1, .s 137 1]⟩,
    ⟨-13, 0, 3, 17, [[.s 3 0, .s 3 0], [.s 133 0, .s 133 0], [.s 136 0, .s 136 0], [.s 123 0, .s 123 0], [.s 124 0, .s 124 0]], [.s 123 0, .s 123 0]⟩,
    ⟨-13, 0, 4, 17, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 135 0, .s 135 0], [.s 139 0, .s 139 0], [.s 124 0, .s 124 0]], [.s 139 1, .s 139 1]⟩,
    ⟨-13, 0, 5, 14, [[.s 5 0, .s 5 0], [.s 134 0, .s 134 0], [.s 138 0, .s 138 0], [.s 122 0, .s 122 0], [.s 125 0, .s 125 0], [.s 126 0, .s 126 0]], [.s 125 0, .s 125 0]⟩,
    ⟨-13, 0, 6, 14, [[.s 5 0, .s 5 0], [.s 6 0, .s 6 0], [.s 137 0, .s 137 0], [.s 140 0, .s 140 0], [.s 126 0, .s 126 0]], [.s 140 1, .s 140 1]⟩,
    ⟨-13, 0, 7, 16, [[.s 7 0, .s 7 0], [.s 136 0, .s 136 0], [.s 141 0, .s 141 0], [.s 124 0, .s 124 0], [.s 127 0, .s 127 0]], [.s 141 1, .s 141 1]⟩,
    ⟨-13, 0, 8, 13, [[.s 8 0, .s 8 0], [.s 138 0, .s 138 0], [.s 142 0, .s 142 0], [.s 128 0, .s 128 0]], [.s 128 0, .s 128 0]⟩,
    ⟨-13, 0, 9, 15, [[.s 9 0, .s 9 0], [.s 139 0, .s 139 0], [.s 143 0, .s 143 0], [.s 129 0, .s 129 0]], [.s 143 1, .s 143 1]⟩,
    ⟨-13, 0, 10, 14, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 140 0, .s 140 0], [.s 143 0, .s 143 0], [.s 130 0, .s 130 0]], [.s 140 2, .s 140 2]⟩,
    ⟨-13, 0, 11, 14, [[.s 11 0, .s 11 0], [.s 141 0, .s 141 0], [.s 142 0, .s 142 0], [.s 130 0, .s 130 0], [.s 131 0, .s 131 0]], [.s 130 1, .s 130 1]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, -3, 1), (1, -2, 1), (1, 3, -3), (-1, 2, -3)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, -1, 0, 20, [[.f ⟨14, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨16, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.s 12 0]], [.f ⟨14, 25, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, -1, 1, 19, [[.f ⟨14, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 12 0], [.s 13 0]], [.s 3 1]⟩,
    ⟨0, -1, 2, 9, [[.f ⟨14, 26, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.s 14 0]], [.f ⟨0, 0, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨0, -1, 3, 18, [[.f ⟨14, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 4 0], [.s 15 0], [.s 16 0]], [.s 4 3]⟩,
    ⟨0, -1, 4, 17, [[.f ⟨14, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 28, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 31, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 7 0], [.s 16 0]], [.f ⟨14, 31, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, -1, 5, 10, [[.f ⟨14, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 6 0], [.s 14 0], [.s 17 0], [.s 18 0]], [.s 2 2]⟩,
    ⟨0, -1, 6, 11, [[.f ⟨14, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 30, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.s 8 0], [.s 18 0]], [.f ⟨14, 29, 0, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨0, -1, 7, 16, [[.f ⟨14, 31, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 9 0], [.s 16 0], [.s 19 0]], [.s 9 1]⟩,
    ⟨0, -1, 8, 12, [[.f ⟨14, 32, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 10 0], [.s 20 0]], [.s 6 3]⟩,
    ⟨0, -1, 9, 15, [[.f ⟨14, 33, 0, 0, 0, 0, 0, 0, 0⟩], [.s 7 0], [.s 11 0], [.s 21 0]], [.s 11 1]⟩,
    ⟨0, -1, 10, 13, [[.f ⟨14, 34, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨14, 35, 0, 0, 0, 0, 0, 0, 0⟩], [.s 8 0], [.s 11 0], [.s 22 0]], [.s 8 2]⟩,
    ⟨0, -1, 11, 14, [[.f ⟨14, 35, 0, 0, 0, 0, 0, 0, 0⟩], [.s 9 0], [.s 10 0], [.s 22 0], [.s 23 0]], [.s 10 3]⟩,
    ⟨1, -1, 0, 20, [[.s 0 0], [.s 1 0], [.f ⟨16, 26, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 0, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 1 2]⟩,
    ⟨1, -1, 1, 19, [[.s 1 0], [.s 15 0], [.f ⟨15, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 1, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 15 1]⟩,
    ⟨1, -1, 2, 9, [[.s 2 0], [.s 5 0], [.s 17 0], [.f ⟨5, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨5, 0, 0, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨1, -1, 3, 18, [[.s 3 0], [.s 13 0], [.s 16 0], [.f ⟨15, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 16 3]⟩,
    ⟨1, -1, 4, 17, [[.s 3 0], [.s 4 0], [.s 7 0], [.s 15 0], [.s 19 0], [.f ⟨15, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 7 3]⟩,
    ⟨1, -1, 5, 10, [[.s 5 0], [.s 14 0], [.s 18 0], [.f ⟨15, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 14 2]⟩,
    ⟨1, -1, 6, 11, [[.s 5 0], [.s 6 0], [.s 17 0], [.s 20 0], [.f ⟨15, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 5 5]⟩,
    ⟨1, -1, 7, 16, [[.s 7 0], [.s 16 0], [.s 21 0], [.f ⟨15, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 7, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 21 1]⟩,
    ⟨1, -1, 8, 12, [[.s 8 0], [.s 18 0], [.s 22 0], [.f ⟨15, 8, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 18 3]⟩,
    ⟨1, -1, 9, 15, [[.s 9 0], [.s 19 0], [.s 23 0], [.f ⟨15, 9, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 23 1]⟩,
    ⟨1, -1, 10, 13, [[.s 10 0], [.s 11 0], [.s 20 0], [.s 23 0], [.f ⟨15, 10, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 20 2]⟩,
    ⟨1, -1, 11, 14, [[.s 11 0], [.s 21 0], [.s 22 0], [.f ⟨15, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 11, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 22 3]⟩]⟩,
  ⟨1, -2, -1, 0, 0, [(-1, -3, 4), (1, -2, 1), (-1, 2, -3)], -1, -3, 4, 5, 0, 0, 0, 0,
   [⟨-2, -2, 0, 32, [[.s 24 0, .s 24 0], [.s 25 0, .s 25 0], [.f ⟨16, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨16, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.s 12 0, .s 12 0]], [.s 25 2, .s 25 2]⟩,
    ⟨-2, -2, 1, 31, [[.s 25 0, .s 25 0], [.s 3 0, .s 3 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0]], [.s 3 1, .s 3 1]⟩,
    ⟨-2, -2, 2, 21, [[.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 5 0, .s 5 0], [.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.s 14 0, .s 14 0]], [.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨2, 0, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-2, -2, 3, 30, [[.s 27 0, .s 27 0], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0]], [.s 4 3, .s 4 3]⟩,
    ⟨-2, -2, 4, 29, [[.s 27 0, .s 27 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 16 0, .s 16 0]], [.s 31 3, .s 31 3]⟩,
    ⟨-2, -2, 5, 22, [[.s 29 0, .s 29 0], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 18 0, .s 18 0]], [.s 2 2, .s 2 2]⟩,
    ⟨-2, -2, 6, 23, [[.s 29 0, .s 29 0], [.s 30 0, .s 30 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 18 0, .s 18 0]], [.s 29 5, .s 29 5]⟩,
    ⟨-2, -2, 7, 28, [[.s 31 0, .s 31 0], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0]], [.s 9 1, .s 9 1]⟩,
    ⟨-2, -2, 8, 24, [[.s 32 0, .s 32 0], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.s 20 0, .s 20 0]], [.s 6 3, .s 6 3]⟩,
    ⟨-2, -2, 9, 27, [[.s 33 0, .s 33 0], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.s 21 0, .s 21 0]], [.s 11 1, .s 11 1]⟩,
    ⟨-2, -2, 10, 25, [[.s 34 0, .s 34 0], [.s 35 0, .s 35 0], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 8 2, .s 8 2]⟩,
    ⟨-2, -2, 11, 26, [[.s 35 0, .s 35 0], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 10 3, .s 10 3]⟩,
    ⟨-1, -2, 0, 32, [[.s 0 0, .s 0 0], [.s 1 0, .s 1 0], [.f ⟨16, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨16, 26, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨16, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 0, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 1 2, .s 1 2]⟩,
    ⟨-1, -2, 1, 31, [[.s 1 0, .s 1 0], [.s 15 0, .s 15 0], [.f ⟨16, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 1, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 15 1, .s 15 1]⟩,
    ⟨-1, -2, 2, 21, [[.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.s 24 0, .s 24 0], [.f ⟨16, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 24 2, .s 24 2]⟩,
    ⟨-1, -2, 3, 30, [[.s 3 0, .s 3 0], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.f ⟨16, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 3, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 4, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 16 3, .s 16 3]⟩,
    ⟨-1, -2, 4, 29, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.f ⟨16, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 4, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 7 3, .s 7 3]⟩,
    ⟨-1, -2, 5, 22, [[.s 5 0, .s 5 0], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.f ⟨16, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 6, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 14 2, .s 14 2]⟩,
    ⟨-1, -2, 6, 23, [[.s 5 0, .s 5 0], [.s 6 0, .s 6 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.f ⟨16, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 6, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 5 5, .s 5 5]⟩,
    ⟨-1, -2, 7, 28, [[.s 7 0, .s 7 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.f ⟨16, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 4, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 7, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 21 1, .s 21 1]⟩,
    ⟨-1, -2, 8, 24, [[.s 8 0, .s 8 0], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.f ⟨16, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 8, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 18 3, .s 18 3]⟩,
    ⟨-1, -2, 9, 27, [[.s 9 0, .s 9 0], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.f ⟨16, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 9, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 23 1, .s 23 1]⟩,
    ⟨-1, -2, 10, 25, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.f ⟨16, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 10, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 20 2, .s 20 2]⟩,
    ⟨-1, -2, 11, 26, [[.s 11 0, .s 11 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨16, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨16, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 11, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 22 3, .s 22 3]⟩,
    ⟨-1, -1, 0, 20, [[.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.s 14 0, .s 14 0], [.f ⟨13, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0]], [.f ⟨1, 1, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨2, 1, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-1, -1, 1, 19, [[.f ⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.s 27 0, .s 27 0], [.f ⟨13, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨13, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 1 0]], [.s 27 1, .s 27 1]⟩,
    ⟨-1, -1, 2, 9, [[.f ⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.s 29 0, .s 29 0], [.f ⟨11, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨27, 24, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨13, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0]], [.f ⟨11, 0, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨27, 24, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-1, -1, 3, 18, [[.f ⟨1, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.f ⟨13, 3, 0, 0, 0, 0, 0, 0, 0⟩, .s 3 0], [.f ⟨13, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 4 0]], [.s 28 3, .s 28 3]⟩,
    ⟨-1, -1, 4, 17, [[.f ⟨1, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 4, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 7, 1, 0, 0, 0, 0, 0, 0⟩], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.f ⟨13, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 4 0]], [.f ⟨1, 7, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨2, 7, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-1, -1, 5, 10, [[.f ⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.f ⟨13, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0], [.f ⟨13, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 5 0], [.f ⟨13, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 6 0]], [.s 26 2, .s 26 2]⟩,
    ⟨-1, -1, 6, 11, [[.f ⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 6, 1, 0, 0, 0, 0, 0, 0⟩], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.f ⟨13, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 6 0]], [.f ⟨1, 5, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨2, 5, 1, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨-1, -1, 7, 16, [[.f ⟨1, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 7, 1, 0, 0, 0, 0, 0, 0⟩], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.f ⟨13, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 4 0], [.f ⟨13, 7, 0, 0, 0, 0, 0, 0, 0⟩, .s 7 0]], [.s 33 1, .s 33 1]⟩,
    ⟨-1, -1, 8, 12, [[.f ⟨1, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 8, 1, 0, 0, 0, 0, 0, 0⟩], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.f ⟨13, 8, 0, 0, 0, 0, 0, 0, 0⟩, .s 8 0]], [.s 30 3, .s 30 3]⟩,
    ⟨-1, -1, 9, 15, [[.f ⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.f ⟨13, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 9 0]], [.s 35 1, .s 35 1]⟩,
    ⟨-1, -1, 10, 13, [[.f ⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.f ⟨13, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 10 0]], [.s 32 2, .s 32 2]⟩,
    ⟨-1, -1, 11, 14, [[.f ⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.f ⟨13, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 10 0], [.f ⟨13, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 11 0]], [.s 34 3, .s 34 3]⟩]⟩,
  ⟨1, 3, -1, 0, 0, [(1, -2, 4), (-1, -3, 1), (1, 3, -3)], 1, -2, 4, 5, 0, 0, 0, 0,
   [⟨2, -1, 0, 20, [[.f ⟨13, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 24 0], [.f ⟨13, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 25 0], [.f ⟨16, 50, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 50, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 0, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨13, 13, 0, 0, 0, 0, 0, 0, 2⟩, .s 25 2]⟩,
    ⟨2, -1, 1, 19, [[.f ⟨13, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 25 0], [.s 3 0, .s 3 0], [.f ⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 1, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 3 1, .s 3 1]⟩,
    ⟨2, -1, 2, 9, [[.f ⟨13, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 26 0], [.f ⟨13, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 29 0], [.s 5 0, .s 5 0], [.f ⟨6, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 12, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 2, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨6, 0, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨17, 12, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨2, -1, 3, 18, [[.f ⟨13, 15, 0, 0, 0, 0, 0, 0, 0⟩, .s 27 0], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.f ⟨3, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 4, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 4 3, .s 4 3]⟩,
    ⟨2, -1, 4, 17, [[.f ⟨13, 15, 0, 0, 0, 0, 0, 0, 0⟩, .s 27 0], [.f ⟨13, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 28 0], [.f ⟨13, 19, 0, 0, 0, 0, 0, 0, 0⟩, .s 31 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.f ⟨3, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 4, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨13, 19, 0, 0, 0, 0, 0, 0, 3⟩, .s 31 3]⟩,
    ⟨2, -1, 5, 10, [[.f ⟨13, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 29 0], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 6, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 2 2, .s 2 2]⟩,
    ⟨2, -1, 6, 11, [[.f ⟨13, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 29 0], [.f ⟨13, 18, 0, 0, 0, 0, 0, 0, 0⟩, .s 30 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.f ⟨3, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 6, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨13, 17, 0, 0, 0, 0, 0, 0, 5⟩, .s 29 5]⟩,
    ⟨2, -1, 7, 16, [[.f ⟨13, 19, 0, 0, 0, 0, 0, 0, 0⟩, .s 31 0], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.f ⟨3, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 4, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 7, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 9 1, .s 9 1]⟩,
    ⟨2, -1, 8, 12, [[.f ⟨13, 20, 0, 0, 0, 0, 0, 0, 0⟩, .s 32 0], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.f ⟨3, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 8, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 6 3, .s 6 3]⟩,
    ⟨2, -1, 9, 15, [[.f ⟨13, 21, 0, 0, 0, 0, 0, 0, 0⟩, .s 33 0], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.f ⟨3, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 9, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 11 1, .s 11 1]⟩,
    ⟨2, -1, 10, 13, [[.f ⟨13, 22, 0, 0, 0, 0, 0, 0, 0⟩, .s 34 0], [.f ⟨13, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 35 0], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.f ⟨3, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 10, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 8 2, .s 8 2]⟩,
    ⟨2, -1, 11, 14, [[.f ⟨13, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 35 0], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.f ⟨3, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 11, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 10 3, .s 10 3]⟩,
    ⟨3, -2, 0, 32, [[.f ⟨16, 48, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 48, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨16, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 49, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨16, 2, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨16, 2, 0, 0, 0, 1, 0, 2, 0⟩], [.s 24 0, .s 24 0]], [.f ⟨16, 49, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨16, 49, 0, 0, 0, 1, 0, 1, 2⟩]⟩,
    ⟨3, -2, 1, 31, [[.f ⟨16, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 49, 0, 0, 0, 1, 0, 1, 0⟩], [.s 15 0, .s 15 0], [.s 24 0, .s 24 0], [.s 25 0, .s 25 0]], [.s 15 1, .s 15 1]⟩,
    ⟨3, -2, 2, 21, [[.f ⟨16, 50, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 50, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨16, 53, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 53, 0, 0, 0, 1, 0, 1, 0⟩], [.s 17 0, .s 17 0], [.f ⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.s 26 0, .s 26 0]], [.f ⟨3, 0, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨4, 0, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨3, -2, 3, 30, [[.f ⟨16, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 51, 0, 0, 0, 1, 0, 1, 0⟩], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.s 27 0, .s 27 0], [.s 28 0, .s 28 0]], [.s 16 3, .s 16 3]⟩,
    ⟨3, -2, 4, 29, [[.f ⟨16, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 51, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨16, 52, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 52, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨16, 55, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 55, 0, 0, 0, 1, 0, 1, 0⟩], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.s 28 0, .s 28 0]], [.f ⟨16, 55, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨16, 55, 0, 0, 0, 1, 0, 1, 3⟩]⟩,
    ⟨3, -2, 5, 22, [[.f ⟨16, 53, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 53, 0, 0, 0, 1, 0, 1, 0⟩], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 30 0, .s 30 0]], [.s 14 2, .s 14 2]⟩,
    ⟨3, -2, 6, 23, [[.f ⟨16, 53, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 53, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨16, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 54, 0, 0, 0, 1, 0, 1, 0⟩], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 30 0, .s 30 0]], [.f ⟨16, 53, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨16, 53, 0, 0, 0, 1, 0, 1, 5⟩]⟩,
    ⟨3, -2, 7, 28, [[.f ⟨16, 55, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 55, 0, 0, 0, 1, 0, 1, 0⟩], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0]], [.s 21 1, .s 21 1]⟩,
    ⟨3, -2, 8, 24, [[.f ⟨16, 56, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 56, 0, 0, 0, 1, 0, 1, 0⟩], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.s 32 0, .s 32 0]], [.s 18 3, .s 18 3]⟩,
    ⟨3, -2, 9, 27, [[.f ⟨16, 57, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 57, 0, 0, 0, 1, 0, 1, 0⟩], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.s 33 0, .s 33 0]], [.s 23 1, .s 23 1]⟩,
    ⟨3, -2, 10, 25, [[.f ⟨16, 58, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 58, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨16, 59, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 59, 0, 0, 0, 1, 0, 1, 0⟩], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.s 34 0, .s 34 0]], [.s 20 2, .s 20 2]⟩,
    ⟨3, -2, 11, 26, [[.f ⟨16, 59, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨16, 59, 0, 0, 0, 1, 0, 1, 0⟩], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 34 0, .s 34 0], [.s 35 0, .s 35 0]], [.s 22 3, .s 22 3]⟩,
    ⟨4, -2, 0, 32, [[.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.f ⟨16, 26, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨16, 26, 0, 0, 0, 1, 0, 2, 0⟩], [.s 0 0, .s 0 0]], [.s 13 2, .s 13 2]⟩,
    ⟨4, -2, 1, 31, [[.s 13 0, .s 13 0], [.s 27 0, .s 27 0], [.s 0 0, .s 0 0], [.s 1 0, .s 1 0]], [.s 27 1, .s 27 1]⟩,
    ⟨4, -2, 2, 21, [[.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 29 0, .s 29 0], [.f ⟨17, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0]], [.f ⟨17, 0, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨17, 0, 1, 0, 1, 0, 0, 0, 2⟩]⟩,
    ⟨4, -2, 3, 30, [[.s 15 0, .s 15 0], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.s 3 0, .s 3 0], [.s 4 0, .s 4 0]], [.s 28 3, .s 28 3]⟩,
    ⟨4, -2, 4, 29, [[.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.s 4 0, .s 4 0]], [.s 19 3, .s 19 3]⟩,
    ⟨4, -2, 5, 22, [[.s 17 0, .s 17 0], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 6 0, .s 6 0]], [.s 26 2, .s 26 2]⟩,
    ⟨4, -2, 6, 23, [[.s 17 0, .s 17 0], [.s 18 0, .s 18 0], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.s 6 0, .s 6 0]], [.s 17 5, .s 17 5]⟩,
    ⟨4, -2, 7, 28, [[.s 19 0, .s 19 0], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0]], [.s 33 1, .s 33 1]⟩,
    ⟨4, -2, 8, 24, [[.s 20 0, .s 20 0], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.s 8 0, .s 8 0]], [.s 30 3, .s 30 3]⟩,
    ⟨4, -2, 9, 27, [[.s 21 0, .s 21 0], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.s 9 0, .s 9 0]], [.s 35 1, .s 35 1]⟩,
    ⟨4, -2, 10, 25, [[.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.s 10 0, .s 10 0]], [.s 32 2, .s 32 2]⟩,
    ⟨4, -2, 11, 26, [[.s 23 0, .s 23 0], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0]], [.s 34 3, .s 34 3]⟩]⟩,
  ⟨2, -2, -1, 3, -1, [(-1, -3, 4), (1, -2, 4)], -1, -3, 4, 5, 1, -2, 4, 5,
   [⟨0, -2, 0, 32, [[.f ⟨14, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 36 0, .s 36 0], [.f ⟨14, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 37 0, .s 37 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.f ⟨14, 13, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨14, 13, 1, 0, 1, 0, 0, 0, 2⟩, .s 37 2, .s 37 2]⟩,
    ⟨0, -2, 1, 31, [[.f ⟨14, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 37 0, .s 37 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 3 1, .s 3 1, .s 3 1, .s 3 1]⟩,
    ⟨0, -2, 2, 21, [[.f ⟨14, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 38 0, .s 38 0], [.f ⟨14, 17, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 17, 1, 0, 1, 0, 0, 0, 0⟩, .s 41 0, .s 41 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.f ⟨13, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 0, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨15, 12, 0, 1, 0, 0, 0, 0, 0⟩, .s 12 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0]], [.f ⟨13, 0, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨14, 0, 1, 0, 0, 0, 0, 0, 2⟩, .f ⟨15, 12, 0, 1, 0, 0, 0, 0, 2⟩, .s 12 2]⟩,
    ⟨0, -2, 3, 30, [[.f ⟨14, 15, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 15, 1, 0, 1, 0, 0, 0, 0⟩, .s 39 0, .s 39 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 4 3, .s 4 3, .s 4 3, .s 4 3]⟩,
    ⟨0, -2, 4, 29, [[.f ⟨14, 15, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 15, 1, 0, 1, 0, 0, 0, 0⟩, .s 39 0, .s 39 0], [.f ⟨14, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 40 0, .s 40 0], [.f ⟨14, 19, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 19, 1, 0, 1, 0, 0, 0, 0⟩, .s 43 0, .s 43 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.f ⟨14, 19, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨14, 19, 1, 0, 1, 0, 0, 0, 3⟩, .s 43 3, .s 43 3]⟩,
    ⟨0, -2, 5, 22, [[.f ⟨14, 17, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 17, 1, 0, 1, 0, 0, 0, 0⟩, .s 41 0, .s 41 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 2 2, .s 2 2, .s 2 2, .s 2 2]⟩,
    ⟨0, -2, 6, 23, [[.f ⟨14, 17, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 17, 1, 0, 1, 0, 0, 0, 0⟩, .s 41 0, .s 41 0], [.f ⟨14, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 18, 1, 0, 1, 0, 0, 0, 0⟩, .s 42 0, .s 42 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.f ⟨14, 17, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨14, 17, 1, 0, 1, 0, 0, 0, 5⟩, .s 41 5, .s 41 5]⟩,
    ⟨0, -2, 7, 28, [[.f ⟨14, 19, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 19, 1, 0, 1, 0, 0, 0, 0⟩, .s 43 0, .s 43 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 9 1, .s 9 1, .s 9 1, .s 9 1]⟩,
    ⟨0, -2, 8, 24, [[.f ⟨14, 20, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 20, 1, 0, 1, 0, 0, 0, 0⟩, .s 44 0, .s 44 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0]], [.s 6 3, .s 6 3, .s 6 3, .s 6 3]⟩,
    ⟨0, -2, 9, 27, [[.f ⟨14, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 21, 1, 0, 1, 0, 0, 0, 0⟩, .s 45 0, .s 45 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0]], [.s 11 1, .s 11 1, .s 11 1, .s 11 1]⟩,
    ⟨0, -2, 10, 25, [[.f ⟨14, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 22, 1, 0, 1, 0, 0, 0, 0⟩, .s 46 0, .s 46 0], [.f ⟨14, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 47 0, .s 47 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0]], [.s 8 2, .s 8 2, .s 8 2, .s 8 2]⟩,
    ⟨0, -2, 11, 26, [[.f ⟨14, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 47 0, .s 47 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0]], [.s 10 3, .s 10 3, .s 10 3, .s 10 3]⟩,
    ⟨1, -3, 0, 44, [[.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.s 49 2, .s 49 2, .s 49 2, .s 49 2]⟩,
    ⟨1, -3, 1, 43, [[.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0]], [.s 15 1, .s 15 1, .s 15 1, .s 15 1]⟩,
    ⟨1, -3, 2, 33, [[.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.s 24 2, .s 24 2, .s 24 2, .s 24 2]⟩,
    ⟨1, -3, 3, 42, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 16 3, .s 16 3, .s 16 3, .s 16 3]⟩,
    ⟨1, -3, 4, 41, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 55 3, .s 55 3, .s 55 3, .s 55 3]⟩,
    ⟨1, -3, 5, 34, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 14 2, .s 14 2, .s 14 2, .s 14 2]⟩,
    ⟨1, -3, 6, 35, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 53 5, .s 53 5, .s 53 5, .s 53 5]⟩,
    ⟨1, -3, 7, 40, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 21 1, .s 21 1, .s 21 1, .s 21 1]⟩,
    ⟨1, -3, 8, 36, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 18 3, .s 18 3, .s 18 3, .s 18 3]⟩,
    ⟨1, -3, 9, 39, [[.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 23 1, .s 23 1, .s 23 1, .s 23 1]⟩,
    ⟨1, -3, 10, 37, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0]], [.s 20 2, .s 20 2, .s 20 2, .s 20 2]⟩,
    ⟨1, -3, 11, 38, [[.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 22 3, .s 22 3, .s 22 3, .s 22 3]⟩,
    ⟨1, -2, 0, 32, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.s 1 2, .s 1 2, .s 1 2, .s 1 2]⟩,
    ⟨1, -2, 1, 31, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 27 1, .s 27 1, .s 27 1, .s 27 1]⟩,
    ⟨1, -2, 2, 21, [[.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.f ⟨13, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨14, 12, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨15, 24, 0, 1, 0, 0, 0, 0, 0⟩, .s 36 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.f ⟨13, 12, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨14, 12, 1, 0, 0, 0, 0, 0, 2⟩, .f ⟨15, 24, 0, 1, 0, 0, 0, 0, 2⟩, .s 36 2]⟩,
    ⟨1, -2, 3, 30, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 28 3, .s 28 3, .s 28 3, .s 28 3]⟩,
    ⟨1, -2, 4, 29, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 7 3, .s 7 3, .s 7 3, .s 7 3]⟩,
    ⟨1, -2, 5, 22, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 26 2, .s 26 2, .s 26 2, .s 26 2]⟩,
    ⟨1, -2, 6, 23, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 5 5, .s 5 5, .s 5 5, .s 5 5]⟩,
    ⟨1, -2, 7, 28, [[.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0]], [.s 33 1, .s 33 1, .s 33 1, .s 33 1]⟩,
    ⟨1, -2, 8, 24, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0]], [.s 30 3, .s 30 3, .s 30 3, .s 30 3]⟩,
    ⟨1, -2, 9, 27, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 35 1, .s 35 1, .s 35 1, .s 35 1]⟩,
    ⟨1, -2, 10, 25, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0]], [.s 32 2, .s 32 2, .s 32 2, .s 32 2]⟩,
    ⟨1, -2, 11, 26, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0]], [.s 34 3, .s 34 3, .s 34 3, .s 34 3]⟩,
    ⟨2, -3, 0, 44, [[.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0]], [.s 13 2, .s 13 2, .s 13 2, .s 13 2]⟩,
    ⟨2, -3, 1, 43, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.s 39 1, .s 39 1, .s 39 1, .s 39 1]⟩,
    ⟨2, -3, 2, 33, [[.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 48 2, .s 48 2, .s 48 2, .s 48 2]⟩,
    ⟨2, -3, 3, 42, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]], [.s 40 3, .s 40 3, .s 40 3, .s 40 3]⟩,
    ⟨2, -3, 4, 41, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]], [.s 19 3, .s 19 3, .s 19 3, .s 19 3]⟩,
    ⟨2, -3, 5, 34, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]], [.s 38 2, .s 38 2, .s 38 2, .s 38 2]⟩,
    ⟨2, -3, 6, 35, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]], [.s 17 5, .s 17 5, .s 17 5, .s 17 5]⟩,
    ⟨2, -3, 7, 40, [[.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0]], [.s 45 1, .s 45 1, .s 45 1, .s 45 1]⟩,
    ⟨2, -3, 8, 36, [[.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0]], [.s 42 3, .s 42 3, .s 42 3, .s 42 3]⟩,
    ⟨2, -3, 9, 39, [[.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0]], [.s 47 1, .s 47 1, .s 47 1, .s 47 1]⟩,
    ⟨2, -3, 10, 37, [[.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.s 44 2, .s 44 2, .s 44 2, .s 44 2]⟩,
    ⟨2, -3, 11, 38, [[.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0]], [.s 46 3, .s 46 3, .s 46 3, .s 46 3]⟩,
    ⟨2, -2, 0, 32, [[.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.f ⟨15, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 12 0, .f ⟨15, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 12 0]], [.s 25 2, .s 25 2, .s 25 2, .s 25 2]⟩,
    ⟨2, -2, 1, 31, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.f ⟨15, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 12 0, .f ⟨15, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 12 0], [.f ⟨15, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 13 0, .f ⟨15, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 13 0]], [.s 51 1, .s 51 1, .s 51 1, .s 51 1]⟩,
    ⟨2, -2, 2, 21, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.f ⟨15, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨15, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨15, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 14 0, .f ⟨15, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 14 0]], [.f ⟨15, 0, 0, 0, 0, 0, 0, 0, 2⟩, .s 0 2, .f ⟨15, 0, 0, 1, 1, 0, 0, 0, 2⟩, .s 0 2]⟩,
    ⟨2, -2, 3, 30, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.f ⟨15, 15, 0, 0, 0, 0, 0, 0, 0⟩, .s 15 0, .f ⟨15, 15, 0, 1, 1, 0, 0, 0, 0⟩, .s 15 0], [.f ⟨15, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 16 0, .f ⟨15, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 16 0]], [.s 52 3, .s 52 3, .s 52 3, .s 52 3]⟩,
    ⟨2, -2, 4, 29, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.f ⟨15, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 16 0, .f ⟨15, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 16 0]], [.s 31 3, .s 31 3, .s 31 3, .s 31 3]⟩,
    ⟨2, -2, 5, 22, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.f ⟨15, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 14 0, .f ⟨15, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 14 0], [.f ⟨15, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 17 0, .f ⟨15, 17, 0, 1, 1, 0, 0, 0, 0⟩, .s 17 0], [.f ⟨15, 18, 0, 0, 0, 0, 0, 0, 0⟩, .s 18 0, .f ⟨15, 18, 0, 1, 1, 0, 0, 0, 0⟩, .s 18 0]], [.s 50 2, .s 50 2, .s 50 2, .s 50 2]⟩,
    ⟨2, -2, 6, 23, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.f ⟨15, 18, 0, 0, 0, 0, 0, 0, 0⟩, .s 18 0, .f ⟨15, 18, 0, 1, 1, 0, 0, 0, 0⟩, .s 18 0]], [.s 29 5, .s 29 5, .s 29 5, .s 29 5]⟩,
    ⟨2, -2, 7, 28, [[.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.f ⟨15, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 16 0, .f ⟨15, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 16 0], [.f ⟨15, 19, 0, 0, 0, 0, 0, 0, 0⟩, .s 19 0, .f ⟨15, 19, 0, 1, 1, 0, 0, 0, 0⟩, .s 19 0]], [.s 57 1, .s 57 1, .s 57 1, .s 57 1]⟩,
    ⟨2, -2, 8, 24, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.f ⟨15, 20, 0, 0, 0, 0, 0, 0, 0⟩, .s 20 0, .f ⟨15, 20, 0, 1, 1, 0, 0, 0, 0⟩, .s 20 0]], [.s 54 3, .s 54 3, .s 54 3, .s 54 3]⟩,
    ⟨2, -2, 9, 27, [[.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.f ⟨15, 21, 0, 0, 0, 0, 0, 0, 0⟩, .s 21 0, .f ⟨15, 21, 0, 1, 1, 0, 0, 0, 0⟩, .s 21 0]], [.s 59 1, .s 59 1, .s 59 1, .s 59 1]⟩,
    ⟨2, -2, 10, 25, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.f ⟨15, 22, 0, 0, 0, 0, 0, 0, 0⟩, .s 22 0, .f ⟨15, 22, 0, 1, 1, 0, 0, 0, 0⟩, .s 22 0]], [.s 56 2, .s 56 2, .s 56 2, .s 56 2]⟩,
    ⟨2, -2, 11, 26, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.f ⟨15, 22, 0, 0, 0, 0, 0, 0, 0⟩, .s 22 0, .f ⟨15, 22, 0, 1, 1, 0, 0, 0, 0⟩, .s 22 0], [.f ⟨15, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 23 0, .f ⟨15, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 23 0]], [.s 58 3, .s 58 3, .s 58 3, .s 58 3]⟩]⟩,
  ⟨1, 3, -1, 0, 0, [(0, -12, 4), (1, 3, 1), (-1, -3, -3)], 0, -12, 4, 12, 0, 0, 0, 0,
   [⟨4, -1, 0, 20, [[.f ⟨3, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨15, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨15, 26, 1, 0, 1, 0, 0, 0, 0⟩], [.s 12 0, .s 12 0]], [.f ⟨3, 1, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨4, 1, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨4, -1, 1, 19, [[.f ⟨3, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0]], [.s 3 1, .s 3 1]⟩,
    ⟨4, -1, 2, 11, [[.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.f ⟨6, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.s 14 0, .s 14 0]], [.f ⟨3, 2, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨4, 2, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨4, -1, 3, 18, [[.f ⟨3, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0]], [.s 4 3, .s 4 3]⟩,
    ⟨4, -1, 4, 17, [[.f ⟨3, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 4, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 7, 1, 0, 0, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 16 0, .s 16 0]], [.f ⟨3, 7, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨4, 7, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨4, -1, 5, 12, [[.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 18 0, .s 18 0]], [.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨4, 5, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨4, -1, 6, 12, [[.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 6, 1, 0, 0, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 18 0, .s 18 0]], [.f ⟨3, 5, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨4, 5, 1, 0, 0, 0, 0, 0, 5⟩]⟩,
    ⟨4, -1, 7, 17, [[.f ⟨3, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 7, 1, 0, 0, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0]], [.f ⟨3, 7, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨4, 7, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨4, -1, 8, 13, [[.f ⟨3, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 8, 1, 0, 0, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.s 20 0, .s 20 0]], [.f ⟨3, 8, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨4, 8, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨4, -1, 9, 16, [[.f ⟨3, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.s 21 0, .s 21 0]], [.f ⟨3, 9, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨4, 9, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨4, -1, 10, 14, [[.f ⟨3, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨3, 10, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨4, 10, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨4, -1, 11, 15, [[.f ⟨3, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.f ⟨3, 11, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨4, 11, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨5, -1, 0, 20, [[.s 0 0, .s 0 0], [.s 1 0, .s 1 0], [.f ⟨15, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨15, 2, 1, 0, 2, 0, 0, 0, 0⟩], [.s 24 0, .s 24 0]], [.s 1 2, .s 1 2]⟩,
    ⟨5, -1, 1, 20, [[.s 1 0, .s 1 0], [.s 15 0, .s 15 0], [.s 24 0, .s 24 0], [.s 25 0, .s 25 0]], [.s 1 3, .s 1 3]⟩,
    ⟨5, -1, 2, 12, [[.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.f ⟨6, 36, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 12, 1, 0, 0, 0, 0, 0, 0⟩], [.s 26 0, .s 26 0]], [.s 2 4, .s 2 4]⟩,
    ⟨5, -1, 3, 19, [[.s 3 0, .s 3 0], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.s 27 0, .s 27 0], [.s 28 0, .s 28 0]], [.s 3 3, .s 3 3]⟩,
    ⟨5, -1, 4, 18, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.s 28 0, .s 28 0]], [.s 4 5, .s 4 5]⟩,
    ⟨5, -1, 5, 13, [[.s 5 0, .s 5 0], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 30 0, .s 30 0]], [.s 5 4, .s 5 4]⟩,
    ⟨5, -1, 6, 13, [[.s 5 0, .s 5 0], [.s 6 0, .s 6 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 30 0, .s 30 0]], [.s 5 5, .s 5 5]⟩,
    ⟨5, -1, 7, 18, [[.s 7 0, .s 7 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0]], [.s 7 4, .s 7 4]⟩,
    ⟨5, -1, 8, 14, [[.s 8 0, .s 8 0], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.s 32 0, .s 32 0]], [.s 8 3, .s 8 3]⟩,
    ⟨5, -1, 9, 17, [[.s 9 0, .s 9 0], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.s 33 0, .s 33 0]], [.s 9 3, .s 9 3]⟩,
    ⟨5, -1, 10, 15, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.s 34 0, .s 34 0]], [.s 10 4, .s 10 4]⟩,
    ⟨5, -1, 11, 16, [[.s 11 0, .s 11 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 34 0, .s 34 0], [.s 35 0, .s 35 0]], [.s 11 4, .s 11 4]⟩,
    ⟨6, -1, 0, 21, [[.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.f ⟨4, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨4, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 0, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 12 3, .s 12 3]⟩,
    ⟨6, -1, 1, 21, [[.s 13 0, .s 13 0], [.s 27 0, .s 27 0], [.f ⟨18, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 1, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 13 3, .s 13 3]⟩,
    ⟨6, -1, 2, 13, [[.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 29 0, .s 29 0], [.f ⟨6, 48, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 24, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨18, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 2, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 14 4, .s 14 4]⟩,
    ⟨6, -1, 3, 20, [[.s 15 0, .s 15 0], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.f ⟨18, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 3, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 4, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 15 3, .s 15 3]⟩,
    ⟨6, -1, 4, 19, [[.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.f ⟨18, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 4, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 16 5, .s 16 5]⟩,
    ⟨6, -1, 5, 14, [[.s 17 0, .s 17 0], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.f ⟨18, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 5, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 6, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 17 4, .s 17 4]⟩,
    ⟨6, -1, 6, 14, [[.s 17 0, .s 17 0], [.s 18 0, .s 18 0], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.f ⟨18, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 6, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 17 5, .s 17 5]⟩,
    ⟨6, -1, 7, 19, [[.s 19 0, .s 19 0], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.f ⟨18, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 4, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 7, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 19 4, .s 19 4]⟩,
    ⟨6, -1, 8, 15, [[.s 20 0, .s 20 0], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.f ⟨18, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 8, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 20 3, .s 20 3]⟩,
    ⟨6, -1, 9, 18, [[.s 21 0, .s 21 0], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.f ⟨18, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 9, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 21 3, .s 21 3]⟩,
    ⟨6, -1, 10, 16, [[.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.f ⟨18, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 10, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 22 4, .s 22 4]⟩,
    ⟨6, -1, 11, 17, [[.s 23 0, .s 23 0], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.f ⟨18, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 10, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨18, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨18, 11, 1, 0, 1, 0, 0, 0, 0⟩]], [.s 23 4, .s 23 4]⟩]⟩,
  ⟨2, 3, -1, 12, 0, [(0, -12, 4), (1, 3, 4)], 0, -12, 4, 12, 1, 3, 4, 12,
   [⟨7, -1, 0, 22, [[.f ⟨17, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 24, 1, 0, 1, 0, 0, 0, 0⟩, .s 132 0, .s 132 0], [.f ⟨17, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 133 0, .s 133 0], [.f ⟨17, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 2, 1, 0, 2, 0, 0, 0, 0⟩, .s 110 0, .s 110 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0]], [.f ⟨17, 24, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨17, 24, 1, 0, 1, 0, 0, 0, 3⟩, .s 132 3, .s 132 3]⟩,
    ⟨7, -1, 1, 22, [[.f ⟨17, 25, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 25, 1, 0, 1, 0, 0, 0, 0⟩, .s 133 0, .s 133 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0]], [.f ⟨17, 25, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨17, 25, 1, 0, 1, 0, 0, 0, 3⟩, .s 133 3, .s 133 3]⟩,
    ⟨7, -1, 2, 14, [[.f ⟨17, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 26, 1, 0, 1, 0, 0, 0, 0⟩, .s 134 0, .s 134 0], [.f ⟨17, 29, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 29, 1, 0, 1, 0, 0, 0, 0⟩, .s 137 0, .s 137 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.f ⟨6, 60, 0, 0, 0, 0, 0, 0, 0⟩, .s 36 0, .f ⟨6, 60, 0, 1, 1, 0, 0, 0, 0⟩, .s 36 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.f ⟨17, 26, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨17, 26, 1, 0, 1, 0, 0, 0, 4⟩, .s 134 4, .s 134 4]⟩,
    ⟨7, -1, 3, 21, [[.f ⟨17, 27, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 27, 1, 0, 1, 0, 0, 0, 0⟩, .s 135 0, .s 135 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]], [.f ⟨17, 27, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨17, 27, 1, 0, 1, 0, 0, 0, 3⟩, .s 135 3, .s 135 3]⟩,
    ⟨7, -1, 4, 20, [[.f ⟨17, 27, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 27, 1, 0, 1, 0, 0, 0, 0⟩, .s 135 0, .s 135 0], [.f ⟨17, 28, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 28, 1, 0, 1, 0, 0, 0, 0⟩, .s 136 0, .s 136 0], [.f ⟨17, 31, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 31, 1, 0, 1, 0, 0, 0, 0⟩, .s 139 0, .s 139 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]], [.f ⟨17, 28, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨17, 28, 1, 0, 1, 0, 0, 0, 5⟩, .s 136 5, .s 136 5]⟩,
    ⟨7, -1, 5, 15, [[.f ⟨17, 29, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 29, 1, 0, 1, 0, 0, 0, 0⟩, .s 137 0, .s 137 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨17, 29, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨17, 29, 1, 0, 1, 0, 0, 0, 4⟩, .s 137 4, .s 137 4]⟩,
    ⟨7, -1, 6, 15, [[.f ⟨17, 29, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 29, 1, 0, 1, 0, 0, 0, 0⟩, .s 137 0, .s 137 0], [.f ⟨17, 30, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 30, 1, 0, 1, 0, 0, 0, 0⟩, .s 138 0, .s 138 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨17, 29, 0, 0, 0, 0, 0, 0, 5⟩, .f ⟨17, 29, 1, 0, 1, 0, 0, 0, 5⟩, .s 137 5, .s 137 5]⟩,
    ⟨7, -1, 7, 20, [[.f ⟨17, 31, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 31, 1, 0, 1, 0, 0, 0, 0⟩, .s 139 0, .s 139 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.f ⟨17, 31, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨17, 31, 1, 0, 1, 0, 0, 0, 4⟩, .s 139 4, .s 139 4]⟩,
    ⟨7, -1, 8, 16, [[.f ⟨17, 32, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 32, 1, 0, 1, 0, 0, 0, 0⟩, .s 140 0, .s 140 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0]], [.f ⟨17, 32, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨17, 32, 1, 0, 1, 0, 0, 0, 3⟩, .s 140 3, .s 140 3]⟩,
    ⟨7, -1, 9, 19, [[.f ⟨17, 33, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 33, 1, 0, 1, 0, 0, 0, 0⟩, .s 141 0, .s 141 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.f ⟨17, 33, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨17, 33, 1, 0, 1, 0, 0, 0, 3⟩, .s 141 3, .s 141 3]⟩,
    ⟨7, -1, 10, 17, [[.f ⟨17, 34, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 34, 1, 0, 1, 0, 0, 0, 0⟩, .s 142 0, .s 142 0], [.f ⟨17, 35, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 35, 1, 0, 1, 0, 0, 0, 0⟩, .s 143 0, .s 143 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.f ⟨17, 34, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨17, 34, 1, 0, 1, 0, 0, 0, 4⟩, .s 142 4, .s 142 4]⟩,
    ⟨7, -1, 11, 18, [[.f ⟨17, 35, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨17, 35, 1, 0, 1, 0, 0, 0, 0⟩, .s 143 0, .s 143 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.f ⟨17, 35, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨17, 35, 1, 0, 1, 0, 0, 0, 4⟩, .s 143 4, .s 143 4]⟩,
    ⟨8, -1, 0, 23, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.f ⟨17, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 14, 1, 0, 2, 0, 0, 0, 0⟩, .s 122 0, .s 122 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 0 3, .s 0 3, .s 0 3, .s 0 3]⟩,
    ⟨8, -1, 1, 23, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 1 3, .s 1 3, .s 1 3, .s 1 3]⟩,
    ⟨8, -1, 2, 15, [[.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.f ⟨6, 72, 0, 0, 0, 0, 0, 0, 0⟩, .s 48 0, .f ⟨6, 72, 0, 1, 1, 0, 0, 0, 0⟩, .s 48 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0]], [.s 2 4, .s 2 4, .s 2 4, .s 2 4]⟩,
    ⟨8, -1, 3, 22, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 3 3, .s 3 3, .s 3 3, .s 3 3]⟩,
    ⟨8, -1, 4, 21, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 4 5, .s 4 5, .s 4 5, .s 4 5]⟩,
    ⟨8, -1, 5, 16, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 5 4, .s 5 4, .s 5 4, .s 5 4]⟩,
    ⟨8, -1, 6, 16, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 5 5, .s 5 5, .s 5 5, .s 5 5]⟩,
    ⟨8, -1, 7, 21, [[.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 7 4, .s 7 4, .s 7 4, .s 7 4]⟩,
    ⟨8, -1, 8, 17, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0]], [.s 8 3, .s 8 3, .s 8 3, .s 8 3]⟩,
    ⟨8, -1, 9, 20, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0]], [.s 9 3, .s 9 3, .s 9 3, .s 9 3]⟩,
    ⟨8, -1, 10, 18, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0]], [.s 10 4, .s 10 4, .s 10 4, .s 10 4]⟩,
    ⟨8, -1, 11, 19, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0]], [.s 11 4, .s 11 4, .s 11 4, .s 11 4]⟩,
    ⟨9, -1, 0, 24, [[.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.f ⟨17, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨17, 26, 1, 0, 2, 0, 0, 0, 0⟩, .s 134 0, .s 134 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.s 12 3, .s 12 3, .s 12 3, .s 12 3]⟩,
    ⟨9, -1, 1, 24, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0]], [.s 13 3, .s 13 3, .s 13 3, .s 13 3]⟩,
    ⟨9, -1, 2, 16, [[.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.f ⟨6, 84, 0, 0, 0, 0, 0, 0, 0⟩, .s 60 0, .f ⟨6, 84, 0, 1, 1, 0, 0, 0, 0⟩, .s 60 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.s 14 4, .s 14 4, .s 14 4, .s 14 4]⟩,
    ⟨9, -1, 3, 23, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 15 3, .s 15 3, .s 15 3, .s 15 3]⟩,
    ⟨9, -1, 4, 22, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 16 5, .s 16 5, .s 16 5, .s 16 5]⟩,
    ⟨9, -1, 5, 17, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 17 4, .s 17 4, .s 17 4, .s 17 4]⟩,
    ⟨9, -1, 6, 17, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 17 5, .s 17 5, .s 17 5, .s 17 5]⟩,
    ⟨9, -1, 7, 22, [[.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 19 4, .s 19 4, .s 19 4, .s 19 4]⟩,
    ⟨9, -1, 8, 18, [[.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 20 3, .s 20 3, .s 20 3, .s 20 3]⟩,
    ⟨9, -1, 9, 21, [[.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 21 3, .s 21 3, .s 21 3, .s 21 3]⟩,
    ⟨9, -1, 10, 19, [[.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0]], [.s 22 4, .s 22 4, .s 22 4, .s 22 4]⟩,
    ⟨9, -1, 11, 20, [[.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 23 4, .s 23 4, .s 23 4, .s 23 4]⟩,
    ⟨10, -1, 0, 25, [[.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.s 24 3, .s 24 3, .s 24 3, .s 24 3]⟩,
    ⟨10, -1, 1, 25, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 25 3, .s 25 3, .s 25 3, .s 25 3]⟩,
    ⟨10, -1, 2, 17, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.f ⟨6, 96, 0, 0, 0, 0, 0, 0, 0⟩, .s 72 0, .f ⟨6, 96, 0, 1, 1, 0, 0, 0, 0⟩, .s 72 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 26 4, .s 26 4, .s 26 4, .s 26 4]⟩,
    ⟨10, -1, 3, 24, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 27 3, .s 27 3, .s 27 3, .s 27 3]⟩,
    ⟨10, -1, 4, 23, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 28 5, .s 28 5, .s 28 5, .s 28 5]⟩,
    ⟨10, -1, 5, 18, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 29 4, .s 29 4, .s 29 4, .s 29 4]⟩,
    ⟨10, -1, 6, 18, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 29 5, .s 29 5, .s 29 5, .s 29 5]⟩,
    ⟨10, -1, 7, 23, [[.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0]], [.s 31 4, .s 31 4, .s 31 4, .s 31 4]⟩,
    ⟨10, -1, 8, 19, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0]], [.s 32 3, .s 32 3, .s 32 3, .s 32 3]⟩,
    ⟨10, -1, 9, 22, [[.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 33 3, .s 33 3, .s 33 3, .s 33 3]⟩,
    ⟨10, -1, 10, 20, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0]], [.s 34 4, .s 34 4, .s 34 4, .s 34 4]⟩,
    ⟨10, -1, 11, 21, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0]], [.s 35 4, .s 35 4, .s 35 4, .s 35 4]⟩,
    ⟨11, -1, 0, 26, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0]], [.s 36 3, .s 36 3, .s 36 3, .s 36 3]⟩,
    ⟨11, -1, 1, 26, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0]], [.s 37 3, .s 37 3, .s 37 3, .s 37 3]⟩,
    ⟨11, -1, 2, 18, [[.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.f ⟨6, 108, 0, 0, 0, 0, 0, 0, 0⟩, .s 84 0, .f ⟨6, 108, 0, 1, 1, 0, 0, 0, 0⟩, .s 84 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.s 38 4, .s 38 4, .s 38 4, .s 38 4]⟩,
    ⟨11, -1, 3, 25, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 39 3, .s 39 3, .s 39 3, .s 39 3]⟩,
    ⟨11, -1, 4, 24, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 40 5, .s 40 5, .s 40 5, .s 40 5]⟩,
    ⟨11, -1, 5, 19, [[.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 41 4, .s 41 4, .s 41 4, .s 41 4]⟩,
    ⟨11, -1, 6, 19, [[.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 41 5, .s 41 5, .s 41 5, .s 41 5]⟩,
    ⟨11, -1, 7, 24, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 43 4, .s 43 4, .s 43 4, .s 43 4]⟩,
    ⟨11, -1, 8, 20, [[.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0]], [.s 44 3, .s 44 3, .s 44 3, .s 44 3]⟩,
    ⟨11, -1, 9, 23, [[.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 45 3, .s 45 3, .s 45 3, .s 45 3]⟩,
    ⟨11, -1, 10, 21, [[.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 46 4, .s 46 4, .s 46 4, .s 46 4]⟩,
    ⟨11, -1, 11, 22, [[.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 47 4, .s 47 4, .s 47 4, .s 47 4]⟩,
    ⟨12, -1, 0, 27, [[.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0]], [.s 48 3, .s 48 3, .s 48 3, .s 48 3]⟩,
    ⟨12, -1, 1, 27, [[.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 49 3, .s 49 3, .s 49 3, .s 49 3]⟩,
    ⟨12, -1, 2, 19, [[.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.f ⟨6, 120, 0, 0, 0, 0, 0, 0, 0⟩, .s 96 0, .f ⟨6, 120, 0, 1, 1, 0, 0, 0, 0⟩, .s 96 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.s 50 4, .s 50 4, .s 50 4, .s 50 4]⟩,
    ⟨12, -1, 3, 26, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 51 3, .s 51 3, .s 51 3, .s 51 3]⟩,
    ⟨12, -1, 4, 25, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 52 5, .s 52 5, .s 52 5, .s 52 5]⟩,
    ⟨12, -1, 5, 20, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0]], [.s 53 4, .s 53 4, .s 53 4, .s 53 4]⟩,
    ⟨12, -1, 6, 20, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0]], [.s 53 5, .s 53 5, .s 53 5, .s 53 5]⟩,
    ⟨12, -1, 7, 25, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0]], [.s 55 4, .s 55 4, .s 55 4, .s 55 4]⟩,
    ⟨12, -1, 8, 21, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0]], [.s 56 3, .s 56 3, .s 56 3, .s 56 3]⟩,
    ⟨12, -1, 9, 24, [[.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0]], [.s 57 3, .s 57 3, .s 57 3, .s 57 3]⟩,
    ⟨12, -1, 10, 22, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0]], [.s 58 4, .s 58 4, .s 58 4, .s 58 4]⟩,
    ⟨12, -1, 11, 23, [[.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0]], [.s 59 4, .s 59 4, .s 59 4, .s 59 4]⟩,
    ⟨13, -1, 0, 28, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0]], [.s 60 3, .s 60 3, .s 60 3, .s 60 3]⟩,
    ⟨13, -1, 1, 28, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0]], [.s 61 3, .s 61 3, .s 61 3, .s 61 3]⟩,
    ⟨13, -1, 2, 20, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.f ⟨6, 132, 0, 0, 0, 0, 0, 0, 0⟩, .s 108 0, .f ⟨6, 132, 0, 1, 1, 0, 0, 0, 0⟩, .s 108 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0]], [.s 62 4, .s 62 4, .s 62 4, .s 62 4]⟩,
    ⟨13, -1, 3, 27, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0]], [.s 63 3, .s 63 3, .s 63 3, .s 63 3]⟩,
    ⟨13, -1, 4, 26, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0]], [.s 64 5, .s 64 5, .s 64 5, .s 64 5]⟩,
    ⟨13, -1, 5, 21, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0]], [.s 65 4, .s 65 4, .s 65 4, .s 65 4]⟩,
    ⟨13, -1, 6, 21, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0]], [.s 65 5, .s 65 5, .s 65 5, .s 65 5]⟩,
    ⟨13, -1, 7, 26, [[.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0]], [.s 67 4, .s 67 4, .s 67 4, .s 67 4]⟩,
    ⟨13, -1, 8, 22, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0]], [.s 68 3, .s 68 3, .s 68 3, .s 68 3]⟩,
    ⟨13, -1, 9, 25, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0]], [.s 69 3, .s 69 3, .s 69 3, .s 69 3]⟩,
    ⟨13, -1, 10, 23, [[.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0]], [.s 70 4, .s 70 4, .s 70 4, .s 70 4]⟩,
    ⟨13, -1, 11, 24, [[.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0]], [.s 71 4, .s 71 4, .s 71 4, .s 71 4]⟩,
    ⟨14, -1, 0, 29, [[.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0]], [.s 72 3, .s 72 3, .s 72 3, .s 72 3]⟩,
    ⟨14, -1, 1, 29, [[.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0]], [.s 73 3, .s 73 3, .s 73 3, .s 73 3]⟩,
    ⟨14, -1, 2, 21, [[.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.f ⟨6, 0, 0, 0, 1, 0, 0, 0, 0⟩, .s 120 0, .f ⟨6, 0, 0, 1, 2, 0, 0, 0, 0⟩, .s 120 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0]], [.s 74 4, .s 74 4, .s 74 4, .s 74 4]⟩,
    ⟨14, -1, 3, 28, [[.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0]], [.s 75 3, .s 75 3, .s 75 3, .s 75 3]⟩,
    ⟨14, -1, 4, 27, [[.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0]], [.s 76 5, .s 76 5, .s 76 5, .s 76 5]⟩,
    ⟨14, -1, 5, 22, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0]], [.s 77 4, .s 77 4, .s 77 4, .s 77 4]⟩,
    ⟨14, -1, 6, 22, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0]], [.s 77 5, .s 77 5, .s 77 5, .s 77 5]⟩,
    ⟨14, -1, 7, 27, [[.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0]], [.s 79 4, .s 79 4, .s 79 4, .s 79 4]⟩,
    ⟨14, -1, 8, 23, [[.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0]], [.s 80 3, .s 80 3, .s 80 3, .s 80 3]⟩,
    ⟨14, -1, 9, 26, [[.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0]], [.s 81 3, .s 81 3, .s 81 3, .s 81 3]⟩,
    ⟨14, -1, 10, 24, [[.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0]], [.s 82 4, .s 82 4, .s 82 4, .s 82 4]⟩,
    ⟨14, -1, 11, 25, [[.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0]], [.s 83 4, .s 83 4, .s 83 4, .s 83 4]⟩,
    ⟨15, -1, 0, 30, [[.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0]], [.s 84 3, .s 84 3, .s 84 3, .s 84 3]⟩,
    ⟨15, -1, 1, 30, [[.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0]], [.s 85 3, .s 85 3, .s 85 3, .s 85 3]⟩,
    ⟨15, -1, 2, 22, [[.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.f ⟨6, 12, 0, 0, 1, 0, 0, 0, 0⟩, .s 132 0, .f ⟨6, 12, 0, 1, 2, 0, 0, 0, 0⟩, .s 132 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0]], [.s 86 4, .s 86 4, .s 86 4, .s 86 4]⟩,
    ⟨15, -1, 3, 29, [[.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0]], [.s 87 3, .s 87 3, .s 87 3, .s 87 3]⟩,
    ⟨15, -1, 4, 28, [[.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0]], [.s 88 5, .s 88 5, .s 88 5, .s 88 5]⟩,
    ⟨15, -1, 5, 23, [[.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0]], [.s 89 4, .s 89 4, .s 89 4, .s 89 4]⟩,
    ⟨15, -1, 6, 23, [[.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0]], [.s 89 5, .s 89 5, .s 89 5, .s 89 5]⟩,
    ⟨15, -1, 7, 28, [[.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0]], [.s 91 4, .s 91 4, .s 91 4, .s 91 4]⟩,
    ⟨15, -1, 8, 24, [[.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0]], [.s 92 3, .s 92 3, .s 92 3, .s 92 3]⟩,
    ⟨15, -1, 9, 27, [[.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0]], [.s 93 3, .s 93 3, .s 93 3, .s 93 3]⟩,
    ⟨15, -1, 10, 25, [[.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0]], [.s 94 4, .s 94 4, .s 94 4, .s 94 4]⟩,
    ⟨15, -1, 11, 26, [[.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0]], [.s 95 4, .s 95 4, .s 95 4, .s 95 4]⟩,
    ⟨16, -1, 0, 31, [[.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 120 0, .s 120 0, .s 120 0, .s 120 0]], [.s 96 3, .s 96 3, .s 96 3, .s 96 3]⟩,
    ⟨16, -1, 1, 31, [[.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 120 0, .s 120 0, .s 120 0, .s 120 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0]], [.s 97 3, .s 97 3, .s 97 3, .s 97 3]⟩,
    ⟨16, -1, 2, 23, [[.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.f ⟨6, 24, 0, 0, 1, 0, 0, 0, 0⟩, .s 0 0, .f ⟨6, 24, 0, 1, 2, 0, 0, 0, 0⟩, .s 0 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0]], [.s 98 4, .s 98 4, .s 98 4, .s 98 4]⟩,
    ⟨16, -1, 3, 30, [[.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0]], [.s 99 3, .s 99 3, .s 99 3, .s 99 3]⟩,
    ⟨16, -1, 4, 29, [[.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0]], [.s 100 5, .s 100 5, .s 100 5, .s 100 5]⟩,
    ⟨16, -1, 5, 24, [[.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0]], [.s 101 4, .s 101 4, .s 101 4, .s 101 4]⟩,
    ⟨16, -1, 6, 24, [[.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0]], [.s 101 5, .s 101 5, .s 101 5, .s 101 5]⟩,
    ⟨16, -1, 7, 29, [[.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0]], [.s 103 4, .s 103 4, .s 103 4, .s 103 4]⟩,
    ⟨16, -1, 8, 25, [[.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0]], [.s 104 3, .s 104 3, .s 104 3, .s 104 3]⟩,
    ⟨16, -1, 9, 28, [[.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0]], [.s 105 3, .s 105 3, .s 105 3, .s 105 3]⟩,
    ⟨16, -1, 10, 26, [[.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0]], [.s 106 4, .s 106 4, .s 106 4, .s 106 4]⟩,
    ⟨16, -1, 11, 27, [[.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0]], [.s 107 4, .s 107 4, .s 107 4, .s 107 4]⟩,
    ⟨17, -1, 0, 32, [[.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 132 0, .s 132 0, .s 132 0, .s 132 0]], [.s 108 3, .s 108 3, .s 108 3, .s 108 3]⟩,
    ⟨17, -1, 1, 32, [[.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 132 0, .s 132 0, .s 132 0, .s 132 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0]], [.s 109 3, .s 109 3, .s 109 3, .s 109 3]⟩,
    ⟨17, -1, 2, 24, [[.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.f ⟨6, 36, 0, 0, 1, 0, 0, 0, 0⟩, .s 12 0, .f ⟨6, 36, 0, 1, 2, 0, 0, 0, 0⟩, .s 12 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0]], [.s 110 4, .s 110 4, .s 110 4, .s 110 4]⟩,
    ⟨17, -1, 3, 31, [[.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0]], [.s 111 3, .s 111 3, .s 111 3, .s 111 3]⟩,
    ⟨17, -1, 4, 30, [[.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0]], [.s 112 5, .s 112 5, .s 112 5, .s 112 5]⟩,
    ⟨17, -1, 5, 25, [[.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0]], [.s 113 4, .s 113 4, .s 113 4, .s 113 4]⟩,
    ⟨17, -1, 6, 25, [[.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0]], [.s 113 5, .s 113 5, .s 113 5, .s 113 5]⟩,
    ⟨17, -1, 7, 30, [[.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0]], [.s 115 4, .s 115 4, .s 115 4, .s 115 4]⟩,
    ⟨17, -1, 8, 26, [[.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0]], [.s 116 3, .s 116 3, .s 116 3, .s 116 3]⟩,
    ⟨17, -1, 9, 29, [[.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0]], [.s 117 3, .s 117 3, .s 117 3, .s 117 3]⟩,
    ⟨17, -1, 10, 27, [[.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0]], [.s 118 4, .s 118 4, .s 118 4, .s 118 4]⟩,
    ⟨17, -1, 11, 28, [[.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0]], [.s 119 4, .s 119 4, .s 119 4, .s 119 4]⟩,
    ⟨18, -1, 0, 33, [[.s 120 0, .s 120 0, .s 120 0, .s 120 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0]], [.s 120 3, .s 120 3, .s 120 3, .s 120 3]⟩,
    ⟨18, -1, 1, 33, [[.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.s 121 3, .s 121 3, .s 121 3, .s 121 3]⟩,
    ⟨18, -1, 2, 25, [[.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.f ⟨6, 48, 0, 0, 1, 0, 0, 0, 0⟩, .s 24 0, .f ⟨6, 48, 0, 1, 2, 0, 0, 0, 0⟩, .s 24 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 122 4, .s 122 4, .s 122 4, .s 122 4]⟩,
    ⟨18, -1, 3, 32, [[.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]], [.s 123 3, .s 123 3, .s 123 3, .s 123 3]⟩,
    ⟨18, -1, 4, 31, [[.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]], [.s 124 5, .s 124 5, .s 124 5, .s 124 5]⟩,
    ⟨18, -1, 5, 26, [[.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]], [.s 125 4, .s 125 4, .s 125 4, .s 125 4]⟩,
    ⟨18, -1, 6, 26, [[.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]], [.s 125 5, .s 125 5, .s 125 5, .s 125 5]⟩,
    ⟨18, -1, 7, 31, [[.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0]], [.s 127 4, .s 127 4, .s 127 4, .s 127 4]⟩,
    ⟨18, -1, 8, 27, [[.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0]], [.s 128 3, .s 128 3, .s 128 3, .s 128 3]⟩,
    ⟨18, -1, 9, 30, [[.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0]], [.s 129 3, .s 129 3, .s 129 3, .s 129 3]⟩,
    ⟨18, -1, 10, 28, [[.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.s 130 4, .s 130 4, .s 130 4, .s 130 4]⟩,
    ⟨18, -1, 11, 29, [[.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0]], [.s 131 4, .s 131 4, .s 131 4, .s 131 4]⟩]⟩,
  ⟨1, 2, 1, 0, 0, [(0, 12, 4), (1, -2, 1), (-1, 2, -3)], 0, 12, 4, 12, 0, 0, 0, 0,
   [⟨3, 1, 0, 6, [[.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨6, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 26 0], [.s 12 0, .s 12 0]], [.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨8, 0, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨3, 1, 1, 8, [[.f ⟨7, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0]], [.f ⟨7, 1, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨8, 1, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨3, 1, 2, 15, [[.f ⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.f ⟨22, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨22, 0, 1, 0, 2, 0, 0, 0, 0⟩], [.s 14 0, .s 14 0]], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨8, 5, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨3, 1, 3, 9, [[.f ⟨7, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0]], [.f ⟨7, 3, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨8, 3, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨3, 1, 4, 9, [[.f ⟨7, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 4, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 7, 1, 0, 0, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 16 0, .s 16 0]], [.f ⟨7, 3, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨8, 3, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨3, 1, 5, 15, [[.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 18 0, .s 18 0]], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨8, 5, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨3, 1, 6, 14, [[.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 6, 1, 0, 0, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 18 0, .s 18 0]], [.f ⟨7, 6, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨8, 6, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨3, 1, 7, 10, [[.f ⟨7, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 7, 1, 0, 0, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0]], [.f ⟨7, 7, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨8, 7, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨3, 1, 8, 13, [[.f ⟨7, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 8, 1, 0, 0, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.s 20 0, .s 20 0]], [.f ⟨7, 8, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨8, 8, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨3, 1, 9, 11, [[.f ⟨7, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.s 21 0, .s 21 0]], [.f ⟨7, 9, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨8, 9, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨3, 1, 10, 12, [[.f ⟨7, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.f ⟨7, 10, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨8, 10, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨3, 1, 11, 12, [[.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨8, 11, 1, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨4, 1, 0, 7, [[.s 0 0, .s 0 0], [.s 1 0, .s 1 0], [.f ⟨6, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 2, 0, 0, 0, 1, 0, 0, 0⟩], [.s 24 0, .s 24 0]], [.s 0 3, .s 0 3]⟩,
    ⟨4, 1, 1, 9, [[.s 1 0, .s 1 0], [.s 15 0, .s 15 0], [.s 24 0, .s 24 0], [.s 25 0, .s 25 0]], [.s 1 3, .s 1 3]⟩,
    ⟨4, 1, 2, 16, [[.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.f ⟨8, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 26 0, .s 26 0]], [.s 2 4, .s 2 4]⟩,
    ⟨4, 1, 3, 10, [[.s 3 0, .s 3 0], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.s 27 0, .s 27 0], [.s 28 0, .s 28 0]], [.s 3 3, .s 3 3]⟩,
    ⟨4, 1, 4, 10, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.s 28 0, .s 28 0]], [.s 3 4, .s 3 4]⟩,
    ⟨4, 1, 5, 16, [[.s 5 0, .s 5 0], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 30 0, .s 30 0]], [.s 5 4, .s 5 4]⟩,
    ⟨4, 1, 6, 15, [[.s 5 0, .s 5 0], [.s 6 0, .s 6 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 30 0, .s 30 0]], [.s 6 4, .s 6 4]⟩,
    ⟨4, 1, 7, 11, [[.s 7 0, .s 7 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0]], [.s 7 4, .s 7 4]⟩,
    ⟨4, 1, 8, 14, [[.s 8 0, .s 8 0], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.s 32 0, .s 32 0]], [.s 8 3, .s 8 3]⟩,
    ⟨4, 1, 9, 12, [[.s 9 0, .s 9 0], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.s 33 0, .s 33 0]], [.s 9 3, .s 9 3]⟩,
    ⟨4, 1, 10, 13, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.s 34 0, .s 34 0]], [.s 10 4, .s 10 4]⟩,
    ⟨4, 1, 11, 13, [[.s 11 0, .s 11 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 34 0, .s 34 0], [.s 35 0, .s 35 0]], [.s 11 4, .s 11 4]⟩,
    ⟨5, 1, 0, 8, [[.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.f ⟨6, 38, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 14, 0, 0, 0, 1, 0, 0, 0⟩], [.f ⟨20, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 0, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 12 3, .s 12 3]⟩,
    ⟨5, 1, 1, 10, [[.s 13 0, .s 13 0], [.s 27 0, .s 27 0], [.f ⟨20, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 0, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨20, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 1, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 13 3, .s 13 3]⟩,
    ⟨5, 1, 2, 17, [[.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 29 0, .s 29 0], [.s 0 0, .s 0 0], [.f ⟨20, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 2, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 14 4, .s 14 4]⟩,
    ⟨5, 1, 3, 11, [[.s 15 0, .s 15 0], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.f ⟨20, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 3, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨20, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 4, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 15 3, .s 15 3]⟩,
    ⟨5, 1, 4, 11, [[.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.f ⟨20, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 4, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 15 4, .s 15 4]⟩,
    ⟨5, 1, 5, 17, [[.s 17 0, .s 17 0], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.f ⟨20, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 2, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨20, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 5, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨20, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 6, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 17 4, .s 17 4]⟩,
    ⟨5, 1, 6, 16, [[.s 17 0, .s 17 0], [.s 18 0, .s 18 0], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.f ⟨20, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 6, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 18 4, .s 18 4]⟩,
    ⟨5, 1, 7, 12, [[.s 19 0, .s 19 0], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.f ⟨20, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 4, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨20, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 7, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 19 4, .s 19 4]⟩,
    ⟨5, 1, 8, 15, [[.s 20 0, .s 20 0], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.f ⟨20, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 8, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 20 3, .s 20 3]⟩,
    ⟨5, 1, 9, 13, [[.s 21 0, .s 21 0], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.f ⟨20, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 9, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 21 3, .s 21 3]⟩,
    ⟨5, 1, 10, 14, [[.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.f ⟨20, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 10, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 22 4, .s 22 4]⟩,
    ⟨5, 1, 11, 14, [[.s 23 0, .s 23 0], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.f ⟨20, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 10, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨20, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨20, 11, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 23 4, .s 23 4]⟩]⟩,
  ⟨2, 12, 0, 2, 1, [(1, -2, 4), (0, 12, 4)], 1, -2, 4, 12, 0, 12, 4, 12,
   [⟨6, 1, 0, 9, [[.f ⟨19, 24, 0, 0, 0, 0, 0, 0, 0⟩, .s 132 0, .f ⟨19, 24, 0, 1, 1, 0, 0, 0, 0⟩, .s 132 0], [.f ⟨19, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 133 0, .f ⟨19, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 133 0], [.f ⟨6, 50, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 50, 1, 0, 1, 0, 0, 0, 0⟩, .s 26 0, .s 26 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0]], [.f ⟨19, 24, 0, 0, 0, 0, 0, 0, 3⟩, .s 132 3, .f ⟨19, 24, 0, 1, 1, 0, 0, 0, 3⟩, .s 132 3]⟩,
    ⟨6, 1, 1, 11, [[.f ⟨19, 25, 0, 0, 0, 0, 0, 0, 0⟩, .s 133 0, .f ⟨19, 25, 0, 1, 1, 0, 0, 0, 0⟩, .s 133 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0]], [.f ⟨19, 25, 0, 0, 0, 0, 0, 0, 3⟩, .s 133 3, .f ⟨19, 25, 0, 1, 1, 0, 0, 0, 3⟩, .s 133 3]⟩,
    ⟨6, 1, 2, 18, [[.f ⟨19, 26, 0, 0, 0, 0, 0, 0, 0⟩, .s 134 0, .f ⟨19, 26, 0, 1, 1, 0, 0, 0, 0⟩, .s 134 0], [.f ⟨19, 29, 0, 0, 0, 0, 0, 0, 0⟩, .s 137 0, .f ⟨19, 29, 0, 1, 1, 0, 0, 0, 0⟩, .s 137 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.f ⟨19, 12, 0, 0, 1, 0, 0, 0, 0⟩, .s 120 0, .f ⟨19, 12, 0, 1, 2, 0, 0, 0, 0⟩, .s 120 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.f ⟨19, 26, 0, 0, 0, 0, 0, 0, 4⟩, .s 134 4, .f ⟨19, 26, 0, 1, 1, 0, 0, 0, 4⟩, .s 134 4]⟩,
    ⟨6, 1, 3, 12, [[.f ⟨19, 27, 0, 0, 0, 0, 0, 0, 0⟩, .s 135 0, .f ⟨19, 27, 0, 1, 1, 0, 0, 0, 0⟩, .s 135 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]], [.f ⟨19, 27, 0, 0, 0, 0, 0, 0, 3⟩, .s 135 3, .f ⟨19, 27, 0, 1, 1, 0, 0, 0, 3⟩, .s 135 3]⟩,
    ⟨6, 1, 4, 12, [[.f ⟨19, 27, 0, 0, 0, 0, 0, 0, 0⟩, .s 135 0, .f ⟨19, 27, 0, 1, 1, 0, 0, 0, 0⟩, .s 135 0], [.f ⟨19, 28, 0, 0, 0, 0, 0, 0, 0⟩, .s 136 0, .f ⟨19, 28, 0, 1, 1, 0, 0, 0, 0⟩, .s 136 0], [.f ⟨19, 31, 0, 0, 0, 0, 0, 0, 0⟩, .s 139 0, .f ⟨19, 31, 0, 1, 1, 0, 0, 0, 0⟩, .s 139 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]], [.f ⟨19, 27, 0, 0, 0, 0, 0, 0, 4⟩, .s 135 4, .f ⟨19, 27, 0, 1, 1, 0, 0, 0, 4⟩, .s 135 4]⟩,
    ⟨6, 1, 5, 18, [[.f ⟨19, 29, 0, 0, 0, 0, 0, 0, 0⟩, .s 137 0, .f ⟨19, 29, 0, 1, 1, 0, 0, 0, 0⟩, .s 137 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨19, 29, 0, 0, 0, 0, 0, 0, 4⟩, .s 137 4, .f ⟨19, 29, 0, 1, 1, 0, 0, 0, 4⟩, .s 137 4]⟩,
    ⟨6, 1, 6, 17, [[.f ⟨19, 29, 0, 0, 0, 0, 0, 0, 0⟩, .s 137 0, .f ⟨19, 29, 0, 1, 1, 0, 0, 0, 0⟩, .s 137 0], [.f ⟨19, 30, 0, 0, 0, 0, 0, 0, 0⟩, .s 138 0, .f ⟨19, 30, 0, 1, 1, 0, 0, 0, 0⟩, .s 138 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.f ⟨19, 30, 0, 0, 0, 0, 0, 0, 4⟩, .s 138 4, .f ⟨19, 30, 0, 1, 1, 0, 0, 0, 4⟩, .s 138 4]⟩,
    ⟨6, 1, 7, 13, [[.f ⟨19, 31, 0, 0, 0, 0, 0, 0, 0⟩, .s 139 0, .f ⟨19, 31, 0, 1, 1, 0, 0, 0, 0⟩, .s 139 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.f ⟨19, 31, 0, 0, 0, 0, 0, 0, 4⟩, .s 139 4, .f ⟨19, 31, 0, 1, 1, 0, 0, 0, 4⟩, .s 139 4]⟩,
    ⟨6, 1, 8, 16, [[.f ⟨19, 32, 0, 0, 0, 0, 0, 0, 0⟩, .s 140 0, .f ⟨19, 32, 0, 1, 1, 0, 0, 0, 0⟩, .s 140 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0]], [.f ⟨19, 32, 0, 0, 0, 0, 0, 0, 3⟩, .s 140 3, .f ⟨19, 32, 0, 1, 1, 0, 0, 0, 3⟩, .s 140 3]⟩,
    ⟨6, 1, 9, 14, [[.f ⟨19, 33, 0, 0, 0, 0, 0, 0, 0⟩, .s 141 0, .f ⟨19, 33, 0, 1, 1, 0, 0, 0, 0⟩, .s 141 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.f ⟨19, 33, 0, 0, 0, 0, 0, 0, 3⟩, .s 141 3, .f ⟨19, 33, 0, 1, 1, 0, 0, 0, 3⟩, .s 141 3]⟩,
    ⟨6, 1, 10, 15, [[.f ⟨19, 34, 0, 0, 0, 0, 0, 0, 0⟩, .s 142 0, .f ⟨19, 34, 0, 1, 1, 0, 0, 0, 0⟩, .s 142 0], [.f ⟨19, 35, 0, 0, 0, 0, 0, 0, 0⟩, .s 143 0, .f ⟨19, 35, 0, 1, 1, 0, 0, 0, 0⟩, .s 143 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.f ⟨19, 34, 0, 0, 0, 0, 0, 0, 4⟩, .s 142 4, .f ⟨19, 34, 0, 1, 1, 0, 0, 0, 4⟩, .s 142 4]⟩,
    ⟨6, 1, 11, 15, [[.f ⟨19, 35, 0, 0, 0, 0, 0, 0, 0⟩, .s 143 0, .f ⟨19, 35, 0, 1, 1, 0, 0, 0, 0⟩, .s 143 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.f ⟨19, 35, 0, 0, 0, 0, 0, 0, 4⟩, .s 143 4, .f ⟨19, 35, 0, 1, 1, 0, 0, 0, 4⟩, .s 143 4]⟩,
    ⟨7, 1, 0, 10, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.f ⟨6, 62, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 62, 1, 0, 1, 0, 0, 0, 0⟩, .s 38 0, .s 38 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 0 3, .s 0 3, .s 0 3, .s 0 3]⟩,
    ⟨7, 1, 1, 12, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 1 3, .s 1 3, .s 1 3, .s 1 3]⟩,
    ⟨7, 1, 2, 19, [[.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.f ⟨19, 24, 0, 0, 1, 0, 0, 0, 0⟩, .s 132 0, .f ⟨19, 24, 0, 1, 2, 0, 0, 0, 0⟩, .s 132 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0]], [.s 2 4, .s 2 4, .s 2 4, .s 2 4]⟩,
    ⟨7, 1, 3, 13, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 3 3, .s 3 3, .s 3 3, .s 3 3]⟩,
    ⟨7, 1, 4, 13, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 3 4, .s 3 4, .s 3 4, .s 3 4]⟩,
    ⟨7, 1, 5, 19, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 5 4, .s 5 4, .s 5 4, .s 5 4]⟩,
    ⟨7, 1, 6, 18, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 6 4, .s 6 4, .s 6 4, .s 6 4]⟩,
    ⟨7, 1, 7, 14, [[.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 7 4, .s 7 4, .s 7 4, .s 7 4]⟩,
    ⟨7, 1, 8, 17, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0]], [.s 8 3, .s 8 3, .s 8 3, .s 8 3]⟩,
    ⟨7, 1, 9, 15, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0]], [.s 9 3, .s 9 3, .s 9 3, .s 9 3]⟩,
    ⟨7, 1, 10, 16, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0]], [.s 10 4, .s 10 4, .s 10 4, .s 10 4]⟩,
    ⟨7, 1, 11, 16, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0]], [.s 11 4, .s 11 4, .s 11 4, .s 11 4]⟩,
    ⟨8, 1, 0, 11, [[.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.f ⟨6, 74, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 74, 1, 0, 1, 0, 0, 0, 0⟩, .s 50 0, .s 50 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.s 12 3, .s 12 3, .s 12 3, .s 12 3]⟩,
    ⟨8, 1, 1, 13, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0]], [.s 13 3, .s 13 3, .s 13 3, .s 13 3]⟩,
    ⟨8, 1, 2, 20, [[.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.s 14 4, .s 14 4, .s 14 4, .s 14 4]⟩,
    ⟨8, 1, 3, 14, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 15 3, .s 15 3, .s 15 3, .s 15 3]⟩,
    ⟨8, 1, 4, 14, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 15 4, .s 15 4, .s 15 4, .s 15 4]⟩,
    ⟨8, 1, 5, 20, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 17 4, .s 17 4, .s 17 4, .s 17 4]⟩,
    ⟨8, 1, 6, 19, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 18 4, .s 18 4, .s 18 4, .s 18 4]⟩,
    ⟨8, 1, 7, 15, [[.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 19 4, .s 19 4, .s 19 4, .s 19 4]⟩,
    ⟨8, 1, 8, 18, [[.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 20 3, .s 20 3, .s 20 3, .s 20 3]⟩,
    ⟨8, 1, 9, 16, [[.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 21 3, .s 21 3, .s 21 3, .s 21 3]⟩,
    ⟨8, 1, 10, 17, [[.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0]], [.s 22 4, .s 22 4, .s 22 4, .s 22 4]⟩,
    ⟨8, 1, 11, 17, [[.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 23 4, .s 23 4, .s 23 4, .s 23 4]⟩,
    ⟨9, 1, 0, 12, [[.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.f ⟨6, 86, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 86, 1, 0, 1, 0, 0, 0, 0⟩, .s 62 0, .s 62 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.s 24 3, .s 24 3, .s 24 3, .s 24 3]⟩,
    ⟨9, 1, 1, 14, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 25 3, .s 25 3, .s 25 3, .s 25 3]⟩,
    ⟨9, 1, 2, 21, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 26 4, .s 26 4, .s 26 4, .s 26 4]⟩,
    ⟨9, 1, 3, 15, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 27 3, .s 27 3, .s 27 3, .s 27 3]⟩,
    ⟨9, 1, 4, 15, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 27 4, .s 27 4, .s 27 4, .s 27 4]⟩,
    ⟨9, 1, 5, 21, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 29 4, .s 29 4, .s 29 4, .s 29 4]⟩,
    ⟨9, 1, 6, 20, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 30 4, .s 30 4, .s 30 4, .s 30 4]⟩,
    ⟨9, 1, 7, 16, [[.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0]], [.s 31 4, .s 31 4, .s 31 4, .s 31 4]⟩,
    ⟨9, 1, 8, 19, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0]], [.s 32 3, .s 32 3, .s 32 3, .s 32 3]⟩,
    ⟨9, 1, 9, 17, [[.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 33 3, .s 33 3, .s 33 3, .s 33 3]⟩,
    ⟨9, 1, 10, 18, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0]], [.s 34 4, .s 34 4, .s 34 4, .s 34 4]⟩,
    ⟨9, 1, 11, 18, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0]], [.s 35 4, .s 35 4, .s 35 4, .s 35 4]⟩,
    ⟨10, 1, 0, 13, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.f ⟨6, 98, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 98, 1, 0, 1, 0, 0, 0, 0⟩, .s 74 0, .s 74 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0]], [.s 36 3, .s 36 3, .s 36 3, .s 36 3]⟩,
    ⟨10, 1, 1, 15, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0]], [.s 37 3, .s 37 3, .s 37 3, .s 37 3]⟩,
    ⟨10, 1, 2, 22, [[.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.s 38 4, .s 38 4, .s 38 4, .s 38 4]⟩,
    ⟨10, 1, 3, 16, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 39 3, .s 39 3, .s 39 3, .s 39 3]⟩,
    ⟨10, 1, 4, 16, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 39 4, .s 39 4, .s 39 4, .s 39 4]⟩,
    ⟨10, 1, 5, 22, [[.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 41 4, .s 41 4, .s 41 4, .s 41 4]⟩,
    ⟨10, 1, 6, 21, [[.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 42 4, .s 42 4, .s 42 4, .s 42 4]⟩,
    ⟨10, 1, 7, 17, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 43 4, .s 43 4, .s 43 4, .s 43 4]⟩,
    ⟨10, 1, 8, 20, [[.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0]], [.s 44 3, .s 44 3, .s 44 3, .s 44 3]⟩,
    ⟨10, 1, 9, 18, [[.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 45 3, .s 45 3, .s 45 3, .s 45 3]⟩,
    ⟨10, 1, 10, 19, [[.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 46 4, .s 46 4, .s 46 4, .s 46 4]⟩,
    ⟨10, 1, 11, 19, [[.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 47 4, .s 47 4, .s 47 4, .s 47 4]⟩,
    ⟨11, 1, 0, 14, [[.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.f ⟨6, 110, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 110, 1, 0, 1, 0, 0, 0, 0⟩, .s 86 0, .s 86 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0]], [.s 48 3, .s 48 3, .s 48 3, .s 48 3]⟩,
    ⟨11, 1, 1, 16, [[.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 49 3, .s 49 3, .s 49 3, .s 49 3]⟩,
    ⟨11, 1, 2, 23, [[.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.s 50 4, .s 50 4, .s 50 4, .s 50 4]⟩,
    ⟨11, 1, 3, 17, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 51 3, .s 51 3, .s 51 3, .s 51 3]⟩,
    ⟨11, 1, 4, 17, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 51 4, .s 51 4, .s 51 4, .s 51 4]⟩,
    ⟨11, 1, 5, 23, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0]], [.s 53 4, .s 53 4, .s 53 4, .s 53 4]⟩,
    ⟨11, 1, 6, 22, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0]], [.s 54 4, .s 54 4, .s 54 4, .s 54 4]⟩,
    ⟨11, 1, 7, 18, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0]], [.s 55 4, .s 55 4, .s 55 4, .s 55 4]⟩,
    ⟨11, 1, 8, 21, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0]], [.s 56 3, .s 56 3, .s 56 3, .s 56 3]⟩,
    ⟨11, 1, 9, 19, [[.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0]], [.s 57 3, .s 57 3, .s 57 3, .s 57 3]⟩,
    ⟨11, 1, 10, 20, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0]], [.s 58 4, .s 58 4, .s 58 4, .s 58 4]⟩,
    ⟨11, 1, 11, 20, [[.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0]], [.s 59 4, .s 59 4, .s 59 4, .s 59 4]⟩,
    ⟨12, 1, 0, 15, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.f ⟨6, 122, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 122, 1, 0, 1, 0, 0, 0, 0⟩, .s 98 0, .s 98 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0]], [.s 60 3, .s 60 3, .s 60 3, .s 60 3]⟩,
    ⟨12, 1, 1, 17, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0]], [.s 61 3, .s 61 3, .s 61 3, .s 61 3]⟩,
    ⟨12, 1, 2, 24, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0]], [.s 62 4, .s 62 4, .s 62 4, .s 62 4]⟩,
    ⟨12, 1, 3, 18, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0]], [.s 63 3, .s 63 3, .s 63 3, .s 63 3]⟩,
    ⟨12, 1, 4, 18, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0]], [.s 63 4, .s 63 4, .s 63 4, .s 63 4]⟩,
    ⟨12, 1, 5, 24, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0]], [.s 65 4, .s 65 4, .s 65 4, .s 65 4]⟩,
    ⟨12, 1, 6, 23, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0]], [.s 66 4, .s 66 4, .s 66 4, .s 66 4]⟩,
    ⟨12, 1, 7, 19, [[.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0]], [.s 67 4, .s 67 4, .s 67 4, .s 67 4]⟩,
    ⟨12, 1, 8, 22, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0]], [.s 68 3, .s 68 3, .s 68 3, .s 68 3]⟩,
    ⟨12, 1, 9, 20, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0]], [.s 69 3, .s 69 3, .s 69 3, .s 69 3]⟩,
    ⟨12, 1, 10, 21, [[.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0]], [.s 70 4, .s 70 4, .s 70 4, .s 70 4]⟩,
    ⟨12, 1, 11, 21, [[.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0]], [.s 71 4, .s 71 4, .s 71 4, .s 71 4]⟩,
    ⟨13, 1, 0, 16, [[.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.f ⟨6, 134, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨6, 134, 1, 0, 1, 0, 0, 0, 0⟩, .s 110 0, .s 110 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0]], [.s 72 3, .s 72 3, .s 72 3, .s 72 3]⟩,
    ⟨13, 1, 1, 18, [[.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0]], [.s 73 3, .s 73 3, .s 73 3, .s 73 3]⟩,
    ⟨13, 1, 2, 25, [[.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0]], [.s 74 4, .s 74 4, .s 74 4, .s 74 4]⟩,
    ⟨13, 1, 3, 19, [[.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0]], [.s 75 3, .s 75 3, .s 75 3, .s 75 3]⟩,
    ⟨13, 1, 4, 19, [[.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0]], [.s 75 4, .s 75 4, .s 75 4, .s 75 4]⟩,
    ⟨13, 1, 5, 25, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0]], [.s 77 4, .s 77 4, .s 77 4, .s 77 4]⟩,
    ⟨13, 1, 6, 24, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0]], [.s 78 4, .s 78 4, .s 78 4, .s 78 4]⟩,
    ⟨13, 1, 7, 20, [[.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0]], [.s 79 4, .s 79 4, .s 79 4, .s 79 4]⟩,
    ⟨13, 1, 8, 23, [[.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0]], [.s 80 3, .s 80 3, .s 80 3, .s 80 3]⟩,
    ⟨13, 1, 9, 21, [[.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0]], [.s 81 3, .s 81 3, .s 81 3, .s 81 3]⟩,
    ⟨13, 1, 10, 22, [[.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0]], [.s 82 4, .s 82 4, .s 82 4, .s 82 4]⟩,
    ⟨13, 1, 11, 22, [[.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0]], [.s 83 4, .s 83 4, .s 83 4, .s 83 4]⟩,
    ⟨14, 1, 0, 17, [[.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.f ⟨6, 2, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 2, 1, 0, 2, 0, 0, 0, 0⟩, .s 122 0, .s 122 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0]], [.s 84 3, .s 84 3, .s 84 3, .s 84 3]⟩,
    ⟨14, 1, 1, 19, [[.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0]], [.s 85 3, .s 85 3, .s 85 3, .s 85 3]⟩,
    ⟨14, 1, 2, 26, [[.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0]], [.s 86 4, .s 86 4, .s 86 4, .s 86 4]⟩,
    ⟨14, 1, 3, 20, [[.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0]], [.s 87 3, .s 87 3, .s 87 3, .s 87 3]⟩,
    ⟨14, 1, 4, 20, [[.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0]], [.s 87 4, .s 87 4, .s 87 4, .s 87 4]⟩,
    ⟨14, 1, 5, 26, [[.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0]], [.s 89 4, .s 89 4, .s 89 4, .s 89 4]⟩,
    ⟨14, 1, 6, 25, [[.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0]], [.s 90 4, .s 90 4, .s 90 4, .s 90 4]⟩,
    ⟨14, 1, 7, 21, [[.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0]], [.s 91 4, .s 91 4, .s 91 4, .s 91 4]⟩,
    ⟨14, 1, 8, 24, [[.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0]], [.s 92 3, .s 92 3, .s 92 3, .s 92 3]⟩,
    ⟨14, 1, 9, 22, [[.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0]], [.s 93 3, .s 93 3, .s 93 3, .s 93 3]⟩,
    ⟨14, 1, 10, 23, [[.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0]], [.s 94 4, .s 94 4, .s 94 4, .s 94 4]⟩,
    ⟨14, 1, 11, 23, [[.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0]], [.s 95 4, .s 95 4, .s 95 4, .s 95 4]⟩,
    ⟨15, 1, 0, 18, [[.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.f ⟨6, 14, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 14, 1, 0, 2, 0, 0, 0, 0⟩, .s 134 0, .s 134 0], [.s 120 0, .s 120 0, .s 120 0, .s 120 0]], [.s 96 3, .s 96 3, .s 96 3, .s 96 3]⟩,
    ⟨15, 1, 1, 20, [[.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 120 0, .s 120 0, .s 120 0, .s 120 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0]], [.s 97 3, .s 97 3, .s 97 3, .s 97 3]⟩,
    ⟨15, 1, 2, 27, [[.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0]], [.s 98 4, .s 98 4, .s 98 4, .s 98 4]⟩,
    ⟨15, 1, 3, 21, [[.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0]], [.s 99 3, .s 99 3, .s 99 3, .s 99 3]⟩,
    ⟨15, 1, 4, 21, [[.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0]], [.s 99 4, .s 99 4, .s 99 4, .s 99 4]⟩,
    ⟨15, 1, 5, 27, [[.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0]], [.s 101 4, .s 101 4, .s 101 4, .s 101 4]⟩,
    ⟨15, 1, 6, 26, [[.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0]], [.s 102 4, .s 102 4, .s 102 4, .s 102 4]⟩,
    ⟨15, 1, 7, 22, [[.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0]], [.s 103 4, .s 103 4, .s 103 4, .s 103 4]⟩,
    ⟨15, 1, 8, 25, [[.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0]], [.s 104 3, .s 104 3, .s 104 3, .s 104 3]⟩,
    ⟨15, 1, 9, 23, [[.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0]], [.s 105 3, .s 105 3, .s 105 3, .s 105 3]⟩,
    ⟨15, 1, 10, 24, [[.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0]], [.s 106 4, .s 106 4, .s 106 4, .s 106 4]⟩,
    ⟨15, 1, 11, 24, [[.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0]], [.s 107 4, .s 107 4, .s 107 4, .s 107 4]⟩,
    ⟨16, 1, 0, 19, [[.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.f ⟨6, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 26, 1, 0, 2, 0, 0, 0, 0⟩, .s 2 0, .s 2 0], [.s 132 0, .s 132 0, .s 132 0, .s 132 0]], [.s 108 3, .s 108 3, .s 108 3, .s 108 3]⟩,
    ⟨16, 1, 1, 21, [[.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 132 0, .s 132 0, .s 132 0, .s 132 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0]], [.s 109 3, .s 109 3, .s 109 3, .s 109 3]⟩,
    ⟨16, 1, 2, 28, [[.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0]], [.s 110 4, .s 110 4, .s 110 4, .s 110 4]⟩,
    ⟨16, 1, 3, 22, [[.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0]], [.s 111 3, .s 111 3, .s 111 3, .s 111 3]⟩,
    ⟨16, 1, 4, 22, [[.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0]], [.s 111 4, .s 111 4, .s 111 4, .s 111 4]⟩,
    ⟨16, 1, 5, 28, [[.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0]], [.s 113 4, .s 113 4, .s 113 4, .s 113 4]⟩,
    ⟨16, 1, 6, 27, [[.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0]], [.s 114 4, .s 114 4, .s 114 4, .s 114 4]⟩,
    ⟨16, 1, 7, 23, [[.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0]], [.s 115 4, .s 115 4, .s 115 4, .s 115 4]⟩,
    ⟨16, 1, 8, 26, [[.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0]], [.s 116 3, .s 116 3, .s 116 3, .s 116 3]⟩,
    ⟨16, 1, 9, 24, [[.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0]], [.s 117 3, .s 117 3, .s 117 3, .s 117 3]⟩,
    ⟨16, 1, 10, 25, [[.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0]], [.s 118 4, .s 118 4, .s 118 4, .s 118 4]⟩,
    ⟨16, 1, 11, 25, [[.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0]], [.s 119 4, .s 119 4, .s 119 4, .s 119 4]⟩,
    ⟨17, 1, 0, 20, [[.s 120 0, .s 120 0, .s 120 0, .s 120 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.f ⟨6, 38, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨6, 38, 1, 0, 2, 0, 0, 0, 0⟩, .s 14 0, .s 14 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0]], [.s 120 3, .s 120 3, .s 120 3, .s 120 3]⟩,
    ⟨17, 1, 1, 22, [[.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.s 121 3, .s 121 3, .s 121 3, .s 121 3]⟩,
    ⟨17, 1, 2, 29, [[.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 122 4, .s 122 4, .s 122 4, .s 122 4]⟩,
    ⟨17, 1, 3, 23, [[.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]], [.s 123 3, .s 123 3, .s 123 3, .s 123 3]⟩,
    ⟨17, 1, 4, 23, [[.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]], [.s 123 4, .s 123 4, .s 123 4, .s 123 4]⟩,
    ⟨17, 1, 5, 29, [[.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]], [.s 125 4, .s 125 4, .s 125 4, .s 125 4]⟩,
    ⟨17, 1, 6, 28, [[.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]], [.s 126 4, .s 126 4, .s 126 4, .s 126 4]⟩,
    ⟨17, 1, 7, 24, [[.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0]], [.s 127 4, .s 127 4, .s 127 4, .s 127 4]⟩,
    ⟨17, 1, 8, 27, [[.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0]], [.s 128 3, .s 128 3, .s 128 3, .s 128 3]⟩,
    ⟨17, 1, 9, 25, [[.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0]], [.s 129 3, .s 129 3, .s 129 3, .s 129 3]⟩,
    ⟨17, 1, 10, 26, [[.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.s 130 4, .s 130 4, .s 130 4, .s 130 4]⟩,
    ⟨17, 1, 11, 26, [[.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0]], [.s 131 4, .s 131 4, .s 131 4, .s 131 4]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 3, 1), (-1, 2, 1), (-1, -3, -3), (1, -2, -3)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, 1, 0, 4, [[.f ⟨23, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.s 12 0]], [.f ⟨11, 2, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 1, 1, 5, [[.f ⟨23, 25, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 12 0], [.s 13 0]], [.s 12 1]⟩,
    ⟨-1, 1, 2, 15, [[.f ⟨23, 26, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.f ⟨24, 24, 0, 0, 0, 0, 0, 0, 0⟩], [.s 14 0]], [.f ⟨23, 29, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 1, 3, 6, [[.f ⟨23, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.s 1 0], [.s 4 0], [.s 15 0], [.s 16 0]], [.s 1 1]⟩,
    ⟨-1, 1, 4, 7, [[.f ⟨23, 27, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 28, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 31, 0, 0, 0, 0, 0, 0, 0⟩], [.s 3 0], [.s 7 0], [.s 16 0]], [.f ⟨23, 27, 0, 0, 0, 0, 0, 0, 4⟩]⟩,
    ⟨-1, 1, 5, 14, [[.f ⟨23, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.s 2 0], [.s 6 0], [.s 14 0], [.s 17 0], [.s 18 0]], [.s 6 2]⟩,
    ⟨-1, 1, 6, 13, [[.f ⟨23, 29, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 30, 0, 0, 0, 0, 0, 0, 0⟩], [.s 5 0], [.s 8 0], [.s 18 0]], [.s 8 1]⟩,
    ⟨-1, 1, 7, 8, [[.f ⟨23, 31, 0, 0, 0, 0, 0, 0, 0⟩], [.s 4 0], [.s 9 0], [.s 16 0], [.s 19 0]], [.s 4 4]⟩,
    ⟨-1, 1, 8, 12, [[.f ⟨23, 32, 0, 0, 0, 0, 0, 0, 0⟩], [.s 6 0], [.s 10 0], [.s 20 0]], [.s 10 2]⟩,
    ⟨-1, 1, 9, 9, [[.f ⟨23, 33, 0, 0, 0, 0, 0, 0, 0⟩], [.s 7 0], [.s 11 0], [.s 21 0]], [.s 7 2]⟩,
    ⟨-1, 1, 10, 11, [[.f ⟨23, 34, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨23, 35, 0, 0, 0, 0, 0, 0, 0⟩], [.s 8 0], [.s 11 0], [.s 22 0]], [.f ⟨23, 35, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-1, 1, 11, 10, [[.f ⟨23, 35, 0, 0, 0, 0, 0, 0, 0⟩], [.s 9 0], [.s 10 0], [.s 22 0], [.s 23 0]], [.s 9 2]⟩,
    ⟨0, 1, 0, 4, [[.s 0 0], [.s 1 0], [.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨0, 2, 0, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨0, 1, 1, 5, [[.s 1 0], [.s 15 0], [.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 1, 0, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨22, 0, 0, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨0, 1, 2, 15, [[.s 2 0], [.s 5 0], [.s 17 0], [.f ⟨24, 48, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 2, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 5 3]⟩,
    ⟨0, 1, 3, 6, [[.s 3 0], [.s 13 0], [.s 16 0], [.f ⟨22, 3, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 13 1]⟩,
    ⟨0, 1, 4, 7, [[.s 3 0], [.s 4 0], [.s 7 0], [.s 15 0], [.s 19 0], [.f ⟨22, 4, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 3 4]⟩,
    ⟨0, 1, 5, 14, [[.s 5 0], [.s 14 0], [.s 18 0], [.f ⟨22, 2, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 5, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 18 2]⟩,
    ⟨0, 1, 6, 13, [[.s 5 0], [.s 6 0], [.s 17 0], [.s 20 0], [.f ⟨22, 6, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 20 1]⟩,
    ⟨0, 1, 7, 8, [[.s 7 0], [.s 16 0], [.s 21 0], [.f ⟨22, 4, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 7, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 16 4]⟩,
    ⟨0, 1, 8, 12, [[.s 8 0], [.s 18 0], [.s 22 0], [.f ⟨22, 8, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 22 2]⟩,
    ⟨0, 1, 9, 9, [[.s 9 0], [.s 19 0], [.s 23 0], [.f ⟨22, 9, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 19 2]⟩,
    ⟨0, 1, 10, 11, [[.s 10 0], [.s 11 0], [.s 20 0], [.s 23 0], [.f ⟨22, 10, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 11 3]⟩,
    ⟨0, 1, 11, 10, [[.s 11 0], [.s 21 0], [.s 22 0], [.f ⟨22, 10, 0, 0, 0, 0, 0, 0, 0⟩], [.f ⟨22, 11, 0, 0, 0, 0, 0, 0, 0⟩]], [.s 21 2]⟩]⟩,
  ⟨1, 2, 1, 0, 0, [(1, 3, 4), (-1, 2, 1), (1, -2, -3)], 1, 3, 4, 5, 0, 0, 0, 0,
   [⟨1, 1, 0, 4, [[.f ⟨21, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 24 0], [.f ⟨21, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 25 0], [.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨19, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 0, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨5, 2, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨19, 2, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨1, 1, 1, 6, [[.f ⟨21, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 25 0], [.s 3 0, .s 3 0], [.f ⟨7, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 1, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨21, 13, 0, 0, 0, 0, 0, 0, 3⟩, .s 25 3]⟩,
    ⟨1, 1, 2, 15, [[.f ⟨21, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 26 0], [.f ⟨21, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 29 0], [.s 5 0, .s 5 0], [.s 12 0, .s 12 0], [.f ⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 2, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨21, 17, 0, 0, 0, 0, 0, 0, 3⟩, .s 29 3]⟩,
    ⟨1, 1, 3, 7, [[.f ⟨21, 15, 0, 0, 0, 0, 0, 0, 0⟩, .s 27 0], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.f ⟨7, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 4, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨21, 15, 0, 0, 0, 0, 0, 0, 3⟩, .s 27 3]⟩,
    ⟨1, 1, 4, 7, [[.f ⟨21, 15, 0, 0, 0, 0, 0, 0, 0⟩, .s 27 0], [.f ⟨21, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 28 0], [.f ⟨21, 19, 0, 0, 0, 0, 0, 0, 0⟩, .s 31 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.f ⟨7, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 4, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨21, 15, 0, 0, 0, 0, 0, 0, 4⟩, .s 27 4]⟩,
    ⟨1, 1, 5, 14, [[.f ⟨21, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 29 0], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.f ⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 6, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 6 2, .s 6 2]⟩,
    ⟨1, 1, 6, 13, [[.f ⟨21, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 29 0], [.f ⟨21, 18, 0, 0, 0, 0, 0, 0, 0⟩, .s 30 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.f ⟨7, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 6, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 8 1, .s 8 1]⟩,
    ⟨1, 1, 7, 8, [[.f ⟨21, 19, 0, 0, 0, 0, 0, 0, 0⟩, .s 31 0], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.f ⟨7, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 4, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 7, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 4 4, .s 4 4]⟩,
    ⟨1, 1, 8, 12, [[.f ⟨21, 20, 0, 0, 0, 0, 0, 0, 0⟩, .s 32 0], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.f ⟨7, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 8, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 10 2, .s 10 2]⟩,
    ⟨1, 1, 9, 9, [[.f ⟨21, 21, 0, 0, 0, 0, 0, 0, 0⟩, .s 33 0], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.f ⟨7, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 9, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 7 2, .s 7 2]⟩,
    ⟨1, 1, 10, 11, [[.f ⟨21, 22, 0, 0, 0, 0, 0, 0, 0⟩, .s 34 0], [.f ⟨21, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 35 0], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.f ⟨7, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 10, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨21, 23, 0, 0, 0, 0, 0, 0, 3⟩, .s 35 3]⟩,
    ⟨1, 1, 11, 10, [[.f ⟨21, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 35 0], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.f ⟨7, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨7, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 11, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 9 2, .s 9 2]⟩,
    ⟨1, 2, 0, 16, [[.f ⟨24, 48, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 48, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 49, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 24 0, .s 24 0]], [.s 2 3, .s 2 3]⟩,
    ⟨1, 2, 1, 17, [[.f ⟨24, 49, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 49, 1, 0, 1, 0, 0, 0, 0⟩], [.s 15 0, .s 15 0], [.s 24 0, .s 24 0], [.s 25 0, .s 25 0]], [.s 24 1, .s 24 1]⟩,
    ⟨1, 2, 2, 27, [[.f ⟨24, 50, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 50, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 53, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 53, 1, 0, 1, 0, 0, 0, 0⟩], [.s 17 0, .s 17 0], [.f ⟨24, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨24, 24, 1, 0, 2, 0, 0, 0, 0⟩], [.s 26 0, .s 26 0]], [.f ⟨24, 53, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨24, 53, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, 2, 3, 18, [[.f ⟨24, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 51, 1, 0, 1, 0, 0, 0, 0⟩], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.s 27 0, .s 27 0], [.s 28 0, .s 28 0]], [.s 13 1, .s 13 1]⟩,
    ⟨1, 2, 4, 19, [[.f ⟨24, 51, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 51, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 52, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 52, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 55, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 55, 1, 0, 1, 0, 0, 0, 0⟩], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.s 28 0, .s 28 0]], [.f ⟨24, 51, 0, 0, 0, 0, 0, 0, 4⟩, .f ⟨24, 51, 1, 0, 1, 0, 0, 0, 4⟩]⟩,
    ⟨1, 2, 5, 26, [[.f ⟨24, 53, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 53, 1, 0, 1, 0, 0, 0, 0⟩], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 30 0, .s 30 0]], [.s 18 2, .s 18 2]⟩,
    ⟨1, 2, 6, 25, [[.f ⟨24, 53, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 53, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 54, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 54, 1, 0, 1, 0, 0, 0, 0⟩], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 30 0, .s 30 0]], [.s 20 1, .s 20 1]⟩,
    ⟨1, 2, 7, 20, [[.f ⟨24, 55, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 55, 1, 0, 1, 0, 0, 0, 0⟩], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0]], [.s 16 4, .s 16 4]⟩,
    ⟨1, 2, 8, 24, [[.f ⟨24, 56, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 56, 1, 0, 1, 0, 0, 0, 0⟩], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.s 32 0, .s 32 0]], [.s 22 2, .s 22 2]⟩,
    ⟨1, 2, 9, 21, [[.f ⟨24, 57, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 57, 1, 0, 1, 0, 0, 0, 0⟩], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.s 33 0, .s 33 0]], [.s 19 2, .s 19 2]⟩,
    ⟨1, 2, 10, 23, [[.f ⟨24, 58, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 58, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨24, 59, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 59, 1, 0, 1, 0, 0, 0, 0⟩], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.s 34 0, .s 34 0]], [.f ⟨24, 59, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨24, 59, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨1, 2, 11, 22, [[.f ⟨24, 59, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 59, 1, 0, 1, 0, 0, 0, 0⟩], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 34 0, .s 34 0], [.s 35 0, .s 35 0]], [.s 21 2, .s 21 2]⟩,
    ⟨2, 2, 0, 16, [[.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.f ⟨7, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨8, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.s 0 0, .s 0 0]], [.f ⟨7, 2, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨8, 2, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨2, 2, 1, 17, [[.s 13 0, .s 13 0], [.s 27 0, .s 27 0], [.s 0 0, .s 0 0], [.s 1 0, .s 1 0]], [.s 0 1, .s 0 1]⟩,
    ⟨2, 2, 2, 27, [[.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 29 0, .s 29 0], [.f ⟨24, 48, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨24, 48, 1, 0, 2, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0]], [.s 17 3, .s 17 3]⟩,
    ⟨2, 2, 3, 18, [[.s 15 0, .s 15 0], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.s 3 0, .s 3 0], [.s 4 0, .s 4 0]], [.s 25 1, .s 25 1]⟩,
    ⟨2, 2, 4, 19, [[.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.s 4 0, .s 4 0]], [.s 15 4, .s 15 4]⟩,
    ⟨2, 2, 5, 26, [[.s 17 0, .s 17 0], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 6 0, .s 6 0]], [.s 30 2, .s 30 2]⟩,
    ⟨2, 2, 6, 25, [[.s 17 0, .s 17 0], [.s 18 0, .s 18 0], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.s 6 0, .s 6 0]], [.s 32 1, .s 32 1]⟩,
    ⟨2, 2, 7, 20, [[.s 19 0, .s 19 0], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0]], [.s 28 4, .s 28 4]⟩,
    ⟨2, 2, 8, 24, [[.s 20 0, .s 20 0], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.s 8 0, .s 8 0]], [.s 34 2, .s 34 2]⟩,
    ⟨2, 2, 9, 21, [[.s 21 0, .s 21 0], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.s 9 0, .s 9 0]], [.s 31 2, .s 31 2]⟩,
    ⟨2, 2, 10, 23, [[.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.s 10 0, .s 10 0]], [.s 23 3, .s 23 3]⟩,
    ⟨2, 2, 11, 22, [[.s 23 0, .s 23 0], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.s 10 0, .s 10 0], [.s 11 0, .s 11 0]], [.s 33 2, .s 33 2]⟩]⟩,
  ⟨1, -3, 1, 0, 0, [(-1, 2, 4), (1, 3, 1), (-1, -3, -3)], -1, 2, 4, 5, 0, 0, 0, 0,
   [⟨-4, 2, 0, 16, [[.s 24 0, .s 24 0], [.s 25 0, .s 25 0], [.f ⟨25, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 26, 1, 0, 1, 0, 0, 0, 0⟩], [.s 12 0, .s 12 0]], [.f ⟨25, 26, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨25, 26, 1, 0, 1, 0, 0, 0, 3⟩]⟩,
    ⟨-4, 2, 1, 17, [[.s 25 0, .s 25 0], [.s 3 0, .s 3 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0]], [.s 12 1, .s 12 1]⟩,
    ⟨-4, 2, 2, 27, [[.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 5 0, .s 5 0], [.f ⟨24, 24, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨24, 24, 0, 0, 0, 1, 0, 2, 0⟩], [.s 14 0, .s 14 0]], [.s 29 3, .s 29 3]⟩,
    ⟨-4, 2, 3, 18, [[.s 27 0, .s 27 0], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0]], [.s 1 1, .s 1 1]⟩,
    ⟨-4, 2, 4, 19, [[.s 27 0, .s 27 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 16 0, .s 16 0]], [.s 27 4, .s 27 4]⟩,
    ⟨-4, 2, 5, 26, [[.s 29 0, .s 29 0], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 18 0, .s 18 0]], [.s 6 2, .s 6 2]⟩,
    ⟨-4, 2, 6, 25, [[.s 29 0, .s 29 0], [.s 30 0, .s 30 0], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 18 0, .s 18 0]], [.s 8 1, .s 8 1]⟩,
    ⟨-4, 2, 7, 20, [[.s 31 0, .s 31 0], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0]], [.s 4 4, .s 4 4]⟩,
    ⟨-4, 2, 8, 24, [[.s 32 0, .s 32 0], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.s 20 0, .s 20 0]], [.s 10 2, .s 10 2]⟩,
    ⟨-4, 2, 9, 21, [[.s 33 0, .s 33 0], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.s 21 0, .s 21 0]], [.s 7 2, .s 7 2]⟩,
    ⟨-4, 2, 10, 23, [[.s 34 0, .s 34 0], [.s 35 0, .s 35 0], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 35 3, .s 35 3]⟩,
    ⟨-4, 2, 11, 22, [[.s 35 0, .s 35 0], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 9 2, .s 9 2]⟩,
    ⟨-3, 2, 0, 16, [[.s 0 0, .s 0 0], [.s 1 0, .s 1 0], [.f ⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨24, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 0, 0, 0, 0, 1, 0, 1, 0⟩]], [.f ⟨9, 2, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨10, 2, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-3, 2, 1, 17, [[.s 1 0, .s 1 0], [.s 15 0, .s 15 0], [.f ⟨24, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 0, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨24, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 1, 0, 0, 0, 1, 0, 1, 0⟩]], [.f ⟨24, 0, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨24, 0, 0, 0, 0, 1, 0, 1, 1⟩]⟩,
    ⟨-3, 2, 2, 27, [[.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.f ⟨24, 48, 0, 0, 0, 0, 0, 1, 0⟩, .f ⟨24, 48, 0, 0, 0, 1, 0, 2, 0⟩], [.f ⟨24, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 2, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 5 3, .s 5 3]⟩,
    ⟨-3, 2, 3, 18, [[.s 3 0, .s 3 0], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.f ⟨24, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 3, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨24, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 4, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 13 1, .s 13 1]⟩,
    ⟨-3, 2, 4, 19, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.f ⟨24, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 4, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 3 4, .s 3 4]⟩,
    ⟨-3, 2, 5, 26, [[.s 5 0, .s 5 0], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.f ⟨24, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 2, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨24, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 5, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨24, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 6, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 18 2, .s 18 2]⟩,
    ⟨-3, 2, 6, 25, [[.s 5 0, .s 5 0], [.s 6 0, .s 6 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.f ⟨24, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 6, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 20 1, .s 20 1]⟩,
    ⟨-3, 2, 7, 20, [[.s 7 0, .s 7 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.f ⟨24, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 4, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨24, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 7, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 16 4, .s 16 4]⟩,
    ⟨-3, 2, 8, 24, [[.s 8 0, .s 8 0], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.f ⟨24, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 8, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 22 2, .s 22 2]⟩,
    ⟨-3, 2, 9, 21, [[.s 9 0, .s 9 0], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.f ⟨24, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 9, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 19 2, .s 19 2]⟩,
    ⟨-3, 2, 10, 23, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.f ⟨24, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 10, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 11 3, .s 11 3]⟩,
    ⟨-3, 2, 11, 22, [[.s 11 0, .s 11 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.f ⟨24, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 10, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨24, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 11, 0, 0, 0, 1, 0, 1, 0⟩]], [.s 21 2, .s 21 2]⟩,
    ⟨-2, 1, 0, 5, [[.f ⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨12, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 14, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨21, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0]], [.f ⟨12, 2, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨25, 14, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-2, 1, 1, 5, [[.f ⟨9, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 1, 1, 0, 0, 0, 0, 0, 0⟩], [.s 27 0, .s 27 0], [.f ⟨21, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨21, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 1 0]], [.f ⟨21, 0, 0, 0, 0, 0, 0, 0, 1⟩, .s 0 1]⟩,
    ⟨-2, 1, 2, 15, [[.f ⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.s 29 0, .s 29 0], [.f ⟨24, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨24, 0, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨21, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0]], [.f ⟨9, 5, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨10, 5, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-2, 1, 3, 6, [[.f ⟨9, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.f ⟨21, 3, 0, 0, 0, 0, 0, 0, 0⟩, .s 3 0], [.f ⟨21, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 4 0]], [.s 25 1, .s 25 1]⟩,
    ⟨-2, 1, 4, 7, [[.f ⟨9, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 4, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 7, 1, 0, 0, 0, 0, 0, 0⟩], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.f ⟨21, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 4 0]], [.s 27 2, .s 27 2]⟩,
    ⟨-2, 1, 5, 14, [[.f ⟨9, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.f ⟨21, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0], [.f ⟨21, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 5 0], [.f ⟨21, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 6 0]], [.s 30 2, .s 30 2]⟩,
    ⟨-2, 1, 6, 13, [[.f ⟨9, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 6, 1, 0, 0, 0, 0, 0, 0⟩], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.f ⟨21, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 6 0]], [.s 32 1, .s 32 1]⟩,
    ⟨-2, 1, 7, 8, [[.f ⟨9, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 7, 1, 0, 0, 0, 0, 0, 0⟩], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.f ⟨21, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 4 0], [.f ⟨21, 7, 0, 0, 0, 0, 0, 0, 0⟩, .s 7 0]], [.s 28 4, .s 28 4]⟩,
    ⟨-2, 1, 8, 12, [[.f ⟨9, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 8, 1, 0, 0, 0, 0, 0, 0⟩], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.f ⟨21, 8, 0, 0, 0, 0, 0, 0, 0⟩, .s 8 0]], [.s 34 2, .s 34 2]⟩,
    ⟨-2, 1, 9, 9, [[.f ⟨9, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 9, 1, 0, 0, 0, 0, 0, 0⟩], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.f ⟨21, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 9 0]], [.s 31 2, .s 31 2]⟩,
    ⟨-2, 1, 10, 11, [[.f ⟨9, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.f ⟨21, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 10 0]], [.f ⟨9, 11, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨10, 11, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-2, 1, 11, 10, [[.f ⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 11, 1, 0, 0, 0, 0, 0, 0⟩], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.f ⟨21, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 10 0], [.f ⟨21, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 11 0]], [.s 33 2, .s 33 2]⟩]⟩,
  ⟨2, 2, 1, -3, 1, [(1, 3, 4), (-1, 2, 4)], 1, 3, 4, 5, -1, 2, 4, 5,
   [⟨-2, 2, 0, 16, [[.f ⟨23, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 36 0, .f ⟨23, 12, 0, 1, 1, 0, 0, 0, 0⟩, .s 36 0], [.f ⟨23, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 37 0, .f ⟨23, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 37 0], [.f ⟨23, 26, 0, 0, 0, 0, 0, 0, 0⟩, .s 50 0, .f ⟨23, 26, 0, 1, 1, 0, 0, 0, 0⟩, .s 50 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.f ⟨23, 26, 0, 0, 0, 0, 0, 0, 3⟩, .s 50 3, .f ⟨23, 26, 0, 1, 1, 0, 0, 0, 3⟩, .s 50 3]⟩,
    ⟨-2, 2, 1, 17, [[.f ⟨23, 13, 0, 0, 0, 0, 0, 0, 0⟩, .s 37 0, .f ⟨23, 13, 0, 1, 1, 0, 0, 0, 0⟩, .s 37 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 24 1, .s 24 1, .s 24 1, .s 24 1]⟩,
    ⟨-2, 2, 2, 27, [[.f ⟨23, 14, 0, 0, 0, 0, 0, 0, 0⟩, .s 38 0, .f ⟨23, 14, 0, 1, 1, 0, 0, 0, 0⟩, .s 38 0], [.f ⟨23, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 41 0, .f ⟨23, 17, 0, 1, 1, 0, 0, 0, 0⟩, .s 41 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0]], [.f ⟨23, 17, 0, 0, 0, 0, 0, 0, 3⟩, .s 41 3, .f ⟨23, 17, 0, 1, 1, 0, 0, 0, 3⟩, .s 41 3]⟩,
    ⟨-2, 2, 3, 18, [[.f ⟨23, 15, 0, 0, 0, 0, 0, 0, 0⟩, .s 39 0, .f ⟨23, 15, 0, 1, 1, 0, 0, 0, 0⟩, .s 39 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 1 1, .s 1 1, .s 1 1, .s 1 1]⟩,
    ⟨-2, 2, 4, 19, [[.f ⟨23, 15, 0, 0, 0, 0, 0, 0, 0⟩, .s 39 0, .f ⟨23, 15, 0, 1, 1, 0, 0, 0, 0⟩, .s 39 0], [.f ⟨23, 16, 0, 0, 0, 0, 0, 0, 0⟩, .s 40 0, .f ⟨23, 16, 0, 1, 1, 0, 0, 0, 0⟩, .s 40 0], [.f ⟨23, 19, 0, 0, 0, 0, 0, 0, 0⟩, .s 43 0, .f ⟨23, 19, 0, 1, 1, 0, 0, 0, 0⟩, .s 43 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.f ⟨23, 15, 0, 0, 0, 0, 0, 0, 4⟩, .s 39 4, .f ⟨23, 15, 0, 1, 1, 0, 0, 0, 4⟩, .s 39 4]⟩,
    ⟨-2, 2, 5, 26, [[.f ⟨23, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 41 0, .f ⟨23, 17, 0, 1, 1, 0, 0, 0, 0⟩, .s 41 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 6 2, .s 6 2, .s 6 2, .s 6 2]⟩,
    ⟨-2, 2, 6, 25, [[.f ⟨23, 17, 0, 0, 0, 0, 0, 0, 0⟩, .s 41 0, .f ⟨23, 17, 0, 1, 1, 0, 0, 0, 0⟩, .s 41 0], [.f ⟨23, 18, 0, 0, 0, 0, 0, 0, 0⟩, .s 42 0, .f ⟨23, 18, 0, 1, 1, 0, 0, 0, 0⟩, .s 42 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 8 1, .s 8 1, .s 8 1, .s 8 1]⟩,
    ⟨-2, 2, 7, 20, [[.f ⟨23, 19, 0, 0, 0, 0, 0, 0, 0⟩, .s 43 0, .f ⟨23, 19, 0, 1, 1, 0, 0, 0, 0⟩, .s 43 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 4 4, .s 4 4, .s 4 4, .s 4 4]⟩,
    ⟨-2, 2, 8, 24, [[.f ⟨23, 20, 0, 0, 0, 0, 0, 0, 0⟩, .s 44 0, .f ⟨23, 20, 0, 1, 1, 0, 0, 0, 0⟩, .s 44 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0]], [.s 10 2, .s 10 2, .s 10 2, .s 10 2]⟩,
    ⟨-2, 2, 9, 21, [[.f ⟨23, 21, 0, 0, 0, 0, 0, 0, 0⟩, .s 45 0, .f ⟨23, 21, 0, 1, 1, 0, 0, 0, 0⟩, .s 45 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0]], [.s 7 2, .s 7 2, .s 7 2, .s 7 2]⟩,
    ⟨-2, 2, 10, 23, [[.f ⟨23, 22, 0, 0, 0, 0, 0, 0, 0⟩, .s 46 0, .f ⟨23, 22, 0, 1, 1, 0, 0, 0, 0⟩, .s 46 0], [.f ⟨23, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 47 0, .f ⟨23, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 47 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0]], [.f ⟨23, 23, 0, 0, 0, 0, 0, 0, 3⟩, .s 47 3, .f ⟨23, 23, 0, 1, 1, 0, 0, 0, 3⟩, .s 47 3]⟩,
    ⟨-2, 2, 11, 22, [[.f ⟨23, 23, 0, 0, 0, 0, 0, 0, 0⟩, .s 47 0, .f ⟨23, 23, 0, 1, 1, 0, 0, 0, 0⟩, .s 47 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0]], [.s 9 2, .s 9 2, .s 9 2, .s 9 2]⟩,
    ⟨-2, 3, 0, 28, [[.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.s 2 3, .s 2 3, .s 2 3, .s 2 3]⟩,
    ⟨-2, 3, 1, 29, [[.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0]], [.s 36 1, .s 36 1, .s 36 1, .s 36 1]⟩,
    ⟨-2, 3, 2, 39, [[.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.s 53 3, .s 53 3, .s 53 3, .s 53 3]⟩,
    ⟨-2, 3, 3, 30, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 13 1, .s 13 1, .s 13 1, .s 13 1]⟩,
    ⟨-2, 3, 4, 31, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 51 4, .s 51 4, .s 51 4, .s 51 4]⟩,
    ⟨-2, 3, 5, 38, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 18 2, .s 18 2, .s 18 2, .s 18 2]⟩,
    ⟨-2, 3, 6, 37, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 20 1, .s 20 1, .s 20 1, .s 20 1]⟩,
    ⟨-2, 3, 7, 32, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 16 4, .s 16 4, .s 16 4, .s 16 4]⟩,
    ⟨-2, 3, 8, 36, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 22 2, .s 22 2, .s 22 2, .s 22 2]⟩,
    ⟨-2, 3, 9, 33, [[.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 19 2, .s 19 2, .s 19 2, .s 19 2]⟩,
    ⟨-2, 3, 10, 35, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0]], [.s 59 3, .s 59 3, .s 59 3, .s 59 3]⟩,
    ⟨-2, 3, 11, 34, [[.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 21 2, .s 21 2, .s 21 2, .s 21 2]⟩,
    ⟨-1, 2, 0, 16, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.f ⟨21, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 14, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨23, 2, 0, 1, 0, 0, 0, 0, 0⟩, .s 14 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.f ⟨21, 2, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨22, 14, 1, 0, 0, 0, 0, 0, 3⟩, .f ⟨23, 2, 0, 1, 0, 0, 0, 0, 3⟩, .s 14 3]⟩,
    ⟨-1, 2, 1, 17, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 48 1, .s 48 1, .s 48 1, .s 48 1]⟩,
    ⟨-1, 2, 2, 27, [[.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 5 3, .s 5 3, .s 5 3, .s 5 3]⟩,
    ⟨-1, 2, 3, 18, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 25 1, .s 25 1, .s 25 1, .s 25 1]⟩,
    ⟨-1, 2, 4, 19, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 3 4, .s 3 4, .s 3 4, .s 3 4]⟩,
    ⟨-1, 2, 5, 26, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 30 2, .s 30 2, .s 30 2, .s 30 2]⟩,
    ⟨-1, 2, 6, 25, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 32 1, .s 32 1, .s 32 1, .s 32 1]⟩,
    ⟨-1, 2, 7, 20, [[.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0]], [.s 28 4, .s 28 4, .s 28 4, .s 28 4]⟩,
    ⟨-1, 2, 8, 24, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0]], [.s 34 2, .s 34 2, .s 34 2, .s 34 2]⟩,
    ⟨-1, 2, 9, 21, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 31 2, .s 31 2, .s 31 2, .s 31 2]⟩,
    ⟨-1, 2, 10, 23, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0]], [.s 11 3, .s 11 3, .s 11 3, .s 11 3]⟩,
    ⟨-1, 2, 11, 22, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0]], [.s 33 2, .s 33 2, .s 33 2, .s 33 2]⟩,
    ⟨-1, 3, 0, 28, [[.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0]], [.s 26 3, .s 26 3, .s 26 3, .s 26 3]⟩,
    ⟨-1, 3, 1, 29, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0]], [.s 0 1, .s 0 1, .s 0 1, .s 0 1]⟩,
    ⟨-1, 3, 2, 39, [[.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0]], [.s 17 3, .s 17 3, .s 17 3, .s 17 3]⟩,
    ⟨-1, 3, 3, 30, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]], [.s 37 1, .s 37 1, .s 37 1, .s 37 1]⟩,
    ⟨-1, 3, 4, 31, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0]], [.s 15 4, .s 15 4, .s 15 4, .s 15 4]⟩,
    ⟨-1, 3, 5, 38, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]], [.s 42 2, .s 42 2, .s 42 2, .s 42 2]⟩,
    ⟨-1, 3, 6, 37, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0]], [.s 44 1, .s 44 1, .s 44 1, .s 44 1]⟩,
    ⟨-1, 3, 7, 32, [[.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0]], [.s 40 4, .s 40 4, .s 40 4, .s 40 4]⟩,
    ⟨-1, 3, 8, 36, [[.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0]], [.s 46 2, .s 46 2, .s 46 2, .s 46 2]⟩,
    ⟨-1, 3, 9, 33, [[.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0]], [.s 43 2, .s 43 2, .s 43 2, .s 43 2]⟩,
    ⟨-1, 3, 10, 35, [[.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0]], [.s 23 3, .s 23 3, .s 23 3, .s 23 3]⟩,
    ⟨-1, 3, 11, 34, [[.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0]], [.s 45 2, .s 45 2, .s 45 2, .s 45 2]⟩,
    ⟨0, 2, 0, 16, [[.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.f ⟨21, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 26, 1, 0, 0, 0, 0, 0, 0⟩, .f ⟨23, 14, 0, 1, 0, 0, 0, 0, 0⟩, .s 38 0], [.f ⟨22, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 12 0, .s 12 0]], [.f ⟨21, 14, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨22, 26, 1, 0, 0, 0, 0, 0, 3⟩, .f ⟨23, 14, 0, 1, 0, 0, 0, 0, 3⟩, .s 38 3]⟩,
    ⟨0, 2, 1, 17, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.f ⟨22, 12, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 12, 1, 0, 1, 0, 0, 0, 0⟩, .s 12 0, .s 12 0], [.f ⟨22, 13, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 13, 1, 0, 1, 0, 0, 0, 0⟩, .s 13 0, .s 13 0]], [.f ⟨22, 12, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨22, 12, 1, 0, 1, 0, 0, 0, 1⟩, .s 12 1, .s 12 1]⟩,
    ⟨0, 2, 2, 27, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.f ⟨22, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 14 0, .s 14 0]], [.s 29 3, .s 29 3, .s 29 3, .s 29 3]⟩,
    ⟨0, 2, 3, 18, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.f ⟨22, 15, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 15, 1, 0, 1, 0, 0, 0, 0⟩, .s 15 0, .s 15 0], [.f ⟨22, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 16 0, .s 16 0]], [.s 49 1, .s 49 1, .s 49 1, .s 49 1]⟩,
    ⟨0, 2, 4, 19, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.f ⟨22, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 16 0, .s 16 0]], [.s 27 4, .s 27 4, .s 27 4, .s 27 4]⟩,
    ⟨0, 2, 5, 26, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.f ⟨22, 14, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 14, 1, 0, 1, 0, 0, 0, 0⟩, .s 14 0, .s 14 0], [.f ⟨22, 17, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 17, 1, 0, 1, 0, 0, 0, 0⟩, .s 17 0, .s 17 0], [.f ⟨22, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 18, 1, 0, 1, 0, 0, 0, 0⟩, .s 18 0, .s 18 0]], [.s 54 2, .s 54 2, .s 54 2, .s 54 2]⟩,
    ⟨0, 2, 6, 25, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.f ⟨22, 18, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 18, 1, 0, 1, 0, 0, 0, 0⟩, .s 18 0, .s 18 0]], [.s 56 1, .s 56 1, .s 56 1, .s 56 1]⟩,
    ⟨0, 2, 7, 20, [[.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.f ⟨22, 16, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 16, 1, 0, 1, 0, 0, 0, 0⟩, .s 16 0, .s 16 0], [.f ⟨22, 19, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 19, 1, 0, 1, 0, 0, 0, 0⟩, .s 19 0, .s 19 0]], [.s 52 4, .s 52 4, .s 52 4, .s 52 4]⟩,
    ⟨0, 2, 8, 24, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.f ⟨22, 20, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 20, 1, 0, 1, 0, 0, 0, 0⟩, .s 20 0, .s 20 0]], [.s 58 2, .s 58 2, .s 58 2, .s 58 2]⟩,
    ⟨0, 2, 9, 21, [[.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.f ⟨22, 21, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 21, 1, 0, 1, 0, 0, 0, 0⟩, .s 21 0, .s 21 0]], [.s 55 2, .s 55 2, .s 55 2, .s 55 2]⟩,
    ⟨0, 2, 10, 23, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.f ⟨22, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 22, 1, 0, 1, 0, 0, 0, 0⟩, .s 22 0, .s 22 0]], [.s 35 3, .s 35 3, .s 35 3, .s 35 3]⟩,
    ⟨0, 2, 11, 22, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.f ⟨22, 22, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 22, 1, 0, 1, 0, 0, 0, 0⟩, .s 22 0, .s 22 0], [.f ⟨22, 23, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨22, 23, 1, 0, 1, 0, 0, 0, 0⟩, .s 23 0, .s 23 0]], [.s 57 2, .s 57 2, .s 57 2, .s 57 2]⟩]⟩,
  ⟨1, -3, 1, 0, 0, [(0, 12, 4), (-1, -3, 1), (1, 3, -3)], 0, 12, 4, 12, 0, 0, 0, 0,
   [⟨-6, 1, 0, 9, [[.f ⟨26, 132, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 132, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 133, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 133, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨12, 50, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 110, 1, 0, 0, 0, 0, 0, 0⟩], [.s 12 0, .s 12 0]], [.f ⟨12, 50, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨26, 110, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-6, 1, 1, 9, [[.f ⟨26, 133, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 133, 1, 0, 1, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0]], [.s 12 1, .s 12 1]⟩,
    ⟨-6, 1, 2, 17, [[.f ⟨26, 134, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 134, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 137, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 137, 1, 0, 1, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.f ⟨10, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.s 14 0, .s 14 0]], [.s 5 1, .s 5 1]⟩,
    ⟨-6, 1, 3, 10, [[.f ⟨26, 135, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 135, 1, 0, 1, 0, 0, 0, 0⟩], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0]], [.s 1 1, .s 1 1]⟩,
    ⟨-6, 1, 4, 11, [[.f ⟨26, 135, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 135, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 136, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 136, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 139, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 139, 1, 0, 1, 0, 0, 0, 0⟩], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 16 0, .s 16 0]], [.s 3 2, .s 3 2]⟩,
    ⟨-6, 1, 5, 16, [[.f ⟨26, 137, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 137, 1, 0, 1, 0, 0, 0, 0⟩], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 18 0, .s 18 0]], [.s 17 0, .s 17 0]⟩,
    ⟨-6, 1, 6, 16, [[.f ⟨26, 137, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 137, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 138, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 138, 1, 0, 1, 0, 0, 0, 0⟩], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 18 0, .s 18 0]], [.s 8 1, .s 8 1]⟩,
    ⟨-6, 1, 7, 11, [[.f ⟨26, 139, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 139, 1, 0, 1, 0, 0, 0, 0⟩], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0]], [.s 16 2, .s 16 2]⟩,
    ⟨-6, 1, 8, 15, [[.f ⟨26, 140, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 140, 1, 0, 1, 0, 0, 0, 0⟩], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.s 20 0, .s 20 0]], [.s 10 2, .s 10 2]⟩,
    ⟨-6, 1, 9, 12, [[.f ⟨26, 141, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 141, 1, 0, 1, 0, 0, 0, 0⟩], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.s 21 0, .s 21 0]], [.s 7 2, .s 7 2]⟩,
    ⟨-6, 1, 10, 14, [[.f ⟨26, 142, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 142, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨26, 143, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 143, 1, 0, 1, 0, 0, 0, 0⟩], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 11 2, .s 11 2]⟩,
    ⟨-6, 1, 11, 13, [[.f ⟨26, 143, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 143, 1, 0, 1, 0, 0, 0, 0⟩], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 9 2, .s 9 2]⟩,
    ⟨-5, 1, 0, 8, [[.s 0 0, .s 0 0], [.s 1 0, .s 1 0], [.f ⟨12, 38, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 122, 1, 0, 0, 0, 0, 0, 0⟩], [.s 24 0, .s 24 0]], [.f ⟨12, 38, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨26, 122, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-5, 1, 1, 8, [[.s 1 0, .s 1 0], [.s 15 0, .s 15 0], [.s 24 0, .s 24 0], [.s 25 0, .s 25 0]], [.s 24 1, .s 24 1]⟩,
    ⟨-5, 1, 2, 16, [[.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.f ⟨23, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨23, 24, 1, 0, 2, 0, 0, 0, 0⟩], [.s 26 0, .s 26 0]], [.s 17 1, .s 17 1]⟩,
    ⟨-5, 1, 3, 9, [[.s 3 0, .s 3 0], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.s 27 0, .s 27 0], [.s 28 0, .s 28 0]], [.s 13 1, .s 13 1]⟩,
    ⟨-5, 1, 4, 10, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.s 28 0, .s 28 0]], [.s 15 2, .s 15 2]⟩,
    ⟨-5, 1, 5, 15, [[.s 5 0, .s 5 0], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 30 0, .s 30 0]], [.s 29 0, .s 29 0]⟩,
    ⟨-5, 1, 6, 15, [[.s 5 0, .s 5 0], [.s 6 0, .s 6 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 30 0, .s 30 0]], [.s 20 1, .s 20 1]⟩,
    ⟨-5, 1, 7, 10, [[.s 7 0, .s 7 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0]], [.s 28 2, .s 28 2]⟩,
    ⟨-5, 1, 8, 14, [[.s 8 0, .s 8 0], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.s 32 0, .s 32 0]], [.s 22 2, .s 22 2]⟩,
    ⟨-5, 1, 9, 11, [[.s 9 0, .s 9 0], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.s 33 0, .s 33 0]], [.s 19 2, .s 19 2]⟩,
    ⟨-5, 1, 10, 13, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.s 34 0, .s 34 0]], [.s 23 2, .s 23 2]⟩,
    ⟨-5, 1, 11, 12, [[.s 11 0, .s 11 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 34 0, .s 34 0], [.s 35 0, .s 35 0]], [.s 21 2, .s 21 2]⟩,
    ⟨-4, 1, 0, 7, [[.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.f ⟨12, 26, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨26, 134, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 0, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨12, 26, 0, 0, 0, 0, 0, 0, 3⟩, .f ⟨26, 134, 1, 0, 0, 0, 0, 0, 3⟩]⟩,
    ⟨-4, 1, 1, 7, [[.s 13 0, .s 13 0], [.s 27 0, .s 27 0], [.f ⟨9, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 1, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨9, 0, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨10, 0, 1, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨-4, 1, 2, 15, [[.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 29 0, .s 29 0], [.f ⟨23, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨23, 0, 1, 0, 1, 0, 0, 0, 0⟩], [.f ⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 2, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 29 1, .s 29 1]⟩,
    ⟨-4, 1, 3, 8, [[.s 15 0, .s 15 0], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.f ⟨9, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 4, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 25 1, .s 25 1]⟩,
    ⟨-4, 1, 4, 9, [[.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.f ⟨9, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 4, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 27 2, .s 27 2]⟩,
    ⟨-4, 1, 5, 14, [[.s 17 0, .s 17 0], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.f ⟨9, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 6, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨9, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 6, 1, 0, 0, 0, 0, 0, 0⟩]⟩,
    ⟨-4, 1, 6, 14, [[.s 17 0, .s 17 0], [.s 18 0, .s 18 0], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.f ⟨9, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 6, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 32 1, .s 32 1]⟩,
    ⟨-4, 1, 7, 9, [[.s 19 0, .s 19 0], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.f ⟨9, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 4, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 7, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨9, 4, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨10, 4, 1, 0, 0, 0, 0, 0, 2⟩]⟩,
    ⟨-4, 1, 8, 13, [[.s 20 0, .s 20 0], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.f ⟨9, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 8, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 34 2, .s 34 2]⟩,
    ⟨-4, 1, 9, 10, [[.s 21 0, .s 21 0], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.f ⟨9, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 9, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 31 2, .s 31 2]⟩,
    ⟨-4, 1, 10, 12, [[.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.f ⟨9, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 10, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 35 2, .s 35 2]⟩,
    ⟨-4, 1, 11, 11, [[.s 23 0, .s 23 0], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.f ⟨9, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨9, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨10, 11, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 33 2, .s 33 2]⟩]⟩,
  ⟨2, -3, 1, -12, 0, [(0, 12, 4), (-1, -3, 4)], 0, 12, 4, 12, -1, -3, 4, 12,
   [⟨-18, 1, 0, 21, [[.s 132 0, .s 132 0, .s 132 0, .s 132 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0], [.f ⟨12, 50, 0, 0, 1, 0, 0, 0, 0⟩, .s 110 0, .f ⟨12, 50, 0, 1, 2, 0, 0, 0, 0⟩, .s 110 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0]], [.f ⟨12, 50, 0, 0, 1, 0, 0, 0, 3⟩, .s 110 3, .f ⟨12, 50, 0, 1, 2, 0, 0, 0, 3⟩, .s 110 3]⟩,
    ⟨-18, 1, 1, 21, [[.s 133 0, .s 133 0, .s 133 0, .s 133 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0]], [.s 12 1, .s 12 1, .s 12 1, .s 12 1]⟩,
    ⟨-18, 1, 2, 29, [[.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.s 5 1, .s 5 1, .s 5 1, .s 5 1]⟩,
    ⟨-18, 1, 3, 22, [[.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]], [.s 1 1, .s 1 1, .s 1 1, .s 1 1]⟩,
    ⟨-18, 1, 4, 23, [[.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]], [.s 3 2, .s 3 2, .s 3 2, .s 3 2]⟩,
    ⟨-18, 1, 5, 28, [[.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 17 0, .s 17 0, .s 17 0, .s 17 0]⟩,
    ⟨-18, 1, 6, 28, [[.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 8 1, .s 8 1, .s 8 1, .s 8 1]⟩,
    ⟨-18, 1, 7, 23, [[.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 16 2, .s 16 2, .s 16 2, .s 16 2]⟩,
    ⟨-18, 1, 8, 27, [[.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0]], [.s 10 2, .s 10 2, .s 10 2, .s 10 2]⟩,
    ⟨-18, 1, 9, 24, [[.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.s 7 2, .s 7 2, .s 7 2, .s 7 2]⟩,
    ⟨-18, 1, 10, 26, [[.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.s 11 2, .s 11 2, .s 11 2, .s 11 2]⟩,
    ⟨-18, 1, 11, 25, [[.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 9 2, .s 9 2, .s 9 2, .s 9 2]⟩,
    ⟨-17, 1, 0, 20, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.f ⟨12, 38, 0, 0, 1, 0, 0, 0, 0⟩, .s 122 0, .f ⟨12, 38, 0, 1, 2, 0, 0, 0, 0⟩, .s 122 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.f ⟨12, 38, 0, 0, 1, 0, 0, 0, 3⟩, .s 122 3, .f ⟨12, 38, 0, 1, 2, 0, 0, 0, 3⟩, .s 122 3]⟩,
    ⟨-17, 1, 1, 20, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 24 1, .s 24 1, .s 24 1, .s 24 1]⟩,
    ⟨-17, 1, 2, 28, [[.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0]], [.s 17 1, .s 17 1, .s 17 1, .s 17 1]⟩,
    ⟨-17, 1, 3, 21, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 13 1, .s 13 1, .s 13 1, .s 13 1]⟩,
    ⟨-17, 1, 4, 22, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 15 2, .s 15 2, .s 15 2, .s 15 2]⟩,
    ⟨-17, 1, 5, 27, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 29 0, .s 29 0, .s 29 0, .s 29 0]⟩,
    ⟨-17, 1, 6, 27, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 20 1, .s 20 1, .s 20 1, .s 20 1]⟩,
    ⟨-17, 1, 7, 22, [[.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 28 2, .s 28 2, .s 28 2, .s 28 2]⟩,
    ⟨-17, 1, 8, 26, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0]], [.s 22 2, .s 22 2, .s 22 2, .s 22 2]⟩,
    ⟨-17, 1, 9, 23, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0]], [.s 19 2, .s 19 2, .s 19 2, .s 19 2]⟩,
    ⟨-17, 1, 10, 25, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0]], [.s 23 2, .s 23 2, .s 23 2, .s 23 2]⟩,
    ⟨-17, 1, 11, 24, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0]], [.s 21 2, .s 21 2, .s 21 2, .s 21 2]⟩,
    ⟨-16, 1, 0, 19, [[.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.f ⟨12, 26, 0, 0, 1, 0, 0, 0, 0⟩, .s 134 0, .f ⟨12, 26, 0, 1, 2, 0, 0, 0, 0⟩, .s 134 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.f ⟨12, 26, 0, 0, 1, 0, 0, 0, 3⟩, .s 134 3, .f ⟨12, 26, 0, 1, 2, 0, 0, 0, 3⟩, .s 134 3]⟩,
    ⟨-16, 1, 1, 19, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0]], [.s 36 1, .s 36 1, .s 36 1, .s 36 1]⟩,
    ⟨-16, 1, 2, 27, [[.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.s 29 1, .s 29 1, .s 29 1, .s 29 1]⟩,
    ⟨-16, 1, 3, 20, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 25 1, .s 25 1, .s 25 1, .s 25 1]⟩,
    ⟨-16, 1, 4, 21, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 27 2, .s 27 2, .s 27 2, .s 27 2]⟩,
    ⟨-16, 1, 5, 26, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 41 0, .s 41 0, .s 41 0, .s 41 0]⟩,
    ⟨-16, 1, 6, 26, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 32 1, .s 32 1, .s 32 1, .s 32 1]⟩,
    ⟨-16, 1, 7, 21, [[.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 40 2, .s 40 2, .s 40 2, .s 40 2]⟩,
    ⟨-16, 1, 8, 25, [[.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 34 2, .s 34 2, .s 34 2, .s 34 2]⟩,
    ⟨-16, 1, 9, 22, [[.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 31 2, .s 31 2, .s 31 2, .s 31 2]⟩,
    ⟨-16, 1, 10, 24, [[.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0]], [.s 35 2, .s 35 2, .s 35 2, .s 35 2]⟩,
    ⟨-16, 1, 11, 23, [[.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 33 2, .s 33 2, .s 33 2, .s 33 2]⟩,
    ⟨-15, 1, 0, 18, [[.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.f ⟨12, 14, 0, 0, 1, 0, 0, 0, 0⟩, .s 2 0, .f ⟨12, 14, 0, 1, 2, 0, 0, 0, 0⟩, .s 2 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.f ⟨12, 14, 0, 0, 1, 0, 0, 0, 3⟩, .s 2 3, .f ⟨12, 14, 0, 1, 2, 0, 0, 0, 3⟩, .s 2 3]⟩,
    ⟨-15, 1, 1, 18, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 48 1, .s 48 1, .s 48 1, .s 48 1]⟩,
    ⟨-15, 1, 2, 26, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.s 41 1, .s 41 1, .s 41 1, .s 41 1]⟩,
    ⟨-15, 1, 3, 19, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 37 1, .s 37 1, .s 37 1, .s 37 1]⟩,
    ⟨-15, 1, 4, 20, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 39 2, .s 39 2, .s 39 2, .s 39 2]⟩,
    ⟨-15, 1, 5, 25, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 53 0, .s 53 0, .s 53 0, .s 53 0]⟩,
    ⟨-15, 1, 6, 25, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 44 1, .s 44 1, .s 44 1, .s 44 1]⟩,
    ⟨-15, 1, 7, 20, [[.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0]], [.s 52 2, .s 52 2, .s 52 2, .s 52 2]⟩,
    ⟨-15, 1, 8, 24, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0]], [.s 46 2, .s 46 2, .s 46 2, .s 46 2]⟩,
    ⟨-15, 1, 9, 21, [[.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 43 2, .s 43 2, .s 43 2, .s 43 2]⟩,
    ⟨-15, 1, 10, 23, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0]], [.s 47 2, .s 47 2, .s 47 2, .s 47 2]⟩,
    ⟨-15, 1, 11, 22, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0]], [.s 45 2, .s 45 2, .s 45 2, .s 45 2]⟩,
    ⟨-14, 1, 0, 17, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.f ⟨12, 2, 0, 0, 1, 0, 0, 0, 0⟩, .s 14 0, .f ⟨12, 2, 0, 1, 2, 0, 0, 0, 0⟩, .s 14 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0]], [.f ⟨12, 2, 0, 0, 1, 0, 0, 0, 3⟩, .s 14 3, .f ⟨12, 2, 0, 1, 2, 0, 0, 0, 3⟩, .s 14 3]⟩,
    ⟨-14, 1, 1, 17, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0]], [.s 60 1, .s 60 1, .s 60 1, .s 60 1]⟩,
    ⟨-14, 1, 2, 25, [[.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.s 53 1, .s 53 1, .s 53 1, .s 53 1]⟩,
    ⟨-14, 1, 3, 18, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 49 1, .s 49 1, .s 49 1, .s 49 1]⟩,
    ⟨-14, 1, 4, 19, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 51 2, .s 51 2, .s 51 2, .s 51 2]⟩,
    ⟨-14, 1, 5, 24, [[.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 65 0, .s 65 0, .s 65 0, .s 65 0]⟩,
    ⟨-14, 1, 6, 24, [[.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 56 1, .s 56 1, .s 56 1, .s 56 1]⟩,
    ⟨-14, 1, 7, 19, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 64 2, .s 64 2, .s 64 2, .s 64 2]⟩,
    ⟨-14, 1, 8, 23, [[.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0]], [.s 58 2, .s 58 2, .s 58 2, .s 58 2]⟩,
    ⟨-14, 1, 9, 20, [[.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 55 2, .s 55 2, .s 55 2, .s 55 2]⟩,
    ⟨-14, 1, 10, 22, [[.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 59 2, .s 59 2, .s 59 2, .s 59 2]⟩,
    ⟨-14, 1, 11, 21, [[.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 57 2, .s 57 2, .s 57 2, .s 57 2]⟩,
    ⟨-13, 1, 0, 16, [[.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.f ⟨12, 134, 0, 0, 0, 0, 0, 0, 0⟩, .s 26 0, .f ⟨12, 134, 0, 1, 1, 0, 0, 0, 0⟩, .s 26 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0]], [.f ⟨12, 134, 0, 0, 0, 0, 0, 0, 3⟩, .s 26 3, .f ⟨12, 134, 0, 1, 1, 0, 0, 0, 3⟩, .s 26 3]⟩,
    ⟨-13, 1, 1, 16, [[.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 72 1, .s 72 1, .s 72 1, .s 72 1]⟩,
    ⟨-13, 1, 2, 24, [[.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.s 65 1, .s 65 1, .s 65 1, .s 65 1]⟩,
    ⟨-13, 1, 3, 17, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 61 1, .s 61 1, .s 61 1, .s 61 1]⟩,
    ⟨-13, 1, 4, 18, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 63 2, .s 63 2, .s 63 2, .s 63 2]⟩,
    ⟨-13, 1, 5, 23, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0]], [.s 77 0, .s 77 0, .s 77 0, .s 77 0]⟩,
    ⟨-13, 1, 6, 23, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0]], [.s 68 1, .s 68 1, .s 68 1, .s 68 1]⟩,
    ⟨-13, 1, 7, 18, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0]], [.s 76 2, .s 76 2, .s 76 2, .s 76 2]⟩,
    ⟨-13, 1, 8, 22, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0]], [.s 70 2, .s 70 2, .s 70 2, .s 70 2]⟩,
    ⟨-13, 1, 9, 19, [[.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0]], [.s 67 2, .s 67 2, .s 67 2, .s 67 2]⟩,
    ⟨-13, 1, 10, 21, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0]], [.s 71 2, .s 71 2, .s 71 2, .s 71 2]⟩,
    ⟨-13, 1, 11, 20, [[.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0]], [.s 69 2, .s 69 2, .s 69 2, .s 69 2]⟩,
    ⟨-12, 1, 0, 15, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.f ⟨12, 122, 0, 0, 0, 0, 0, 0, 0⟩, .s 38 0, .f ⟨12, 122, 0, 1, 1, 0, 0, 0, 0⟩, .s 38 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0]], [.f ⟨12, 122, 0, 0, 0, 0, 0, 0, 3⟩, .s 38 3, .f ⟨12, 122, 0, 1, 1, 0, 0, 0, 3⟩, .s 38 3]⟩,
    ⟨-12, 1, 1, 15, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0]], [.s 84 1, .s 84 1, .s 84 1, .s 84 1]⟩,
    ⟨-12, 1, 2, 23, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0]], [.s 77 1, .s 77 1, .s 77 1, .s 77 1]⟩,
    ⟨-12, 1, 3, 16, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0]], [.s 73 1, .s 73 1, .s 73 1, .s 73 1]⟩,
    ⟨-12, 1, 4, 17, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0]], [.s 75 2, .s 75 2, .s 75 2, .s 75 2]⟩,
    ⟨-12, 1, 5, 22, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0]], [.s 89 0, .s 89 0, .s 89 0, .s 89 0]⟩,
    ⟨-12, 1, 6, 22, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0]], [.s 80 1, .s 80 1, .s 80 1, .s 80 1]⟩,
    ⟨-12, 1, 7, 17, [[.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0]], [.s 88 2, .s 88 2, .s 88 2, .s 88 2]⟩,
    ⟨-12, 1, 8, 21, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0]], [.s 82 2, .s 82 2, .s 82 2, .s 82 2]⟩,
    ⟨-12, 1, 9, 18, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0]], [.s 79 2, .s 79 2, .s 79 2, .s 79 2]⟩,
    ⟨-12, 1, 10, 20, [[.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0]], [.s 83 2, .s 83 2, .s 83 2, .s 83 2]⟩,
    ⟨-12, 1, 11, 19, [[.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0]], [.s 81 2, .s 81 2, .s 81 2, .s 81 2]⟩,
    ⟨-11, 1, 0, 14, [[.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.f ⟨12, 110, 0, 0, 0, 0, 0, 0, 0⟩, .s 50 0, .f ⟨12, 110, 0, 1, 1, 0, 0, 0, 0⟩, .s 50 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0]], [.f ⟨12, 110, 0, 0, 0, 0, 0, 0, 3⟩, .s 50 3, .f ⟨12, 110, 0, 1, 1, 0, 0, 0, 3⟩, .s 50 3]⟩,
    ⟨-11, 1, 1, 14, [[.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0]], [.s 96 1, .s 96 1, .s 96 1, .s 96 1]⟩,
    ⟨-11, 1, 2, 22, [[.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 120 0, .s 120 0, .s 120 0, .s 120 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0]], [.s 89 1, .s 89 1, .s 89 1, .s 89 1]⟩,
    ⟨-11, 1, 3, 15, [[.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0]], [.s 85 1, .s 85 1, .s 85 1, .s 85 1]⟩,
    ⟨-11, 1, 4, 16, [[.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0]], [.s 87 2, .s 87 2, .s 87 2, .s 87 2]⟩,
    ⟨-11, 1, 5, 21, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0]], [.s 101 0, .s 101 0, .s 101 0, .s 101 0]⟩,
    ⟨-11, 1, 6, 21, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0]], [.s 92 1, .s 92 1, .s 92 1, .s 92 1]⟩,
    ⟨-11, 1, 7, 16, [[.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0]], [.s 100 2, .s 100 2, .s 100 2, .s 100 2]⟩,
    ⟨-11, 1, 8, 20, [[.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0]], [.s 94 2, .s 94 2, .s 94 2, .s 94 2]⟩,
    ⟨-11, 1, 9, 17, [[.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0]], [.s 91 2, .s 91 2, .s 91 2, .s 91 2]⟩,
    ⟨-11, 1, 10, 19, [[.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0]], [.s 95 2, .s 95 2, .s 95 2, .s 95 2]⟩,
    ⟨-11, 1, 11, 18, [[.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0]], [.s 93 2, .s 93 2, .s 93 2, .s 93 2]⟩,
    ⟨-10, 1, 0, 13, [[.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.f ⟨12, 98, 0, 0, 0, 0, 0, 0, 0⟩, .s 62 0, .f ⟨12, 98, 0, 1, 1, 0, 0, 0, 0⟩, .s 62 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0]], [.f ⟨12, 98, 0, 0, 0, 0, 0, 0, 3⟩, .s 62 3, .f ⟨12, 98, 0, 1, 1, 0, 0, 0, 3⟩, .s 62 3]⟩,
    ⟨-10, 1, 1, 13, [[.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0]], [.s 108 1, .s 108 1, .s 108 1, .s 108 1]⟩,
    ⟨-10, 1, 2, 21, [[.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 132 0, .s 132 0, .s 132 0, .s 132 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0]], [.s 101 1, .s 101 1, .s 101 1, .s 101 1]⟩,
    ⟨-10, 1, 3, 14, [[.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0]], [.s 97 1, .s 97 1, .s 97 1, .s 97 1]⟩,
    ⟨-10, 1, 4, 15, [[.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0]], [.s 99 2, .s 99 2, .s 99 2, .s 99 2]⟩,
    ⟨-10, 1, 5, 20, [[.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0]], [.s 113 0, .s 113 0, .s 113 0, .s 113 0]⟩,
    ⟨-10, 1, 6, 20, [[.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0]], [.s 104 1, .s 104 1, .s 104 1, .s 104 1]⟩,
    ⟨-10, 1, 7, 15, [[.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0]], [.s 112 2, .s 112 2, .s 112 2, .s 112 2]⟩,
    ⟨-10, 1, 8, 19, [[.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0]], [.s 106 2, .s 106 2, .s 106 2, .s 106 2]⟩,
    ⟨-10, 1, 9, 16, [[.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0]], [.s 103 2, .s 103 2, .s 103 2, .s 103 2]⟩,
    ⟨-10, 1, 10, 18, [[.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0]], [.s 107 2, .s 107 2, .s 107 2, .s 107 2]⟩,
    ⟨-10, 1, 11, 17, [[.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0]], [.s 105 2, .s 105 2, .s 105 2, .s 105 2]⟩,
    ⟨-9, 1, 0, 12, [[.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.f ⟨12, 86, 0, 0, 0, 0, 0, 0, 0⟩, .s 74 0, .f ⟨12, 86, 0, 1, 1, 0, 0, 0, 0⟩, .s 74 0], [.s 120 0, .s 120 0, .s 120 0, .s 120 0]], [.f ⟨12, 86, 0, 0, 0, 0, 0, 0, 3⟩, .s 74 3, .f ⟨12, 86, 0, 1, 1, 0, 0, 0, 3⟩, .s 74 3]⟩,
    ⟨-9, 1, 1, 12, [[.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 120 0, .s 120 0, .s 120 0, .s 120 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0]], [.s 120 1, .s 120 1, .s 120 1, .s 120 1]⟩,
    ⟨-9, 1, 2, 20, [[.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.f ⟨25, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 0, 1, 0, 2, 0, 0, 0, 0⟩, .s 0 0, .s 0 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0]], [.s 113 1, .s 113 1, .s 113 1, .s 113 1]⟩,
    ⟨-9, 1, 3, 13, [[.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0]], [.s 109 1, .s 109 1, .s 109 1, .s 109 1]⟩,
    ⟨-9, 1, 4, 14, [[.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0]], [.s 111 2, .s 111 2, .s 111 2, .s 111 2]⟩,
    ⟨-9, 1, 5, 19, [[.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0]], [.s 125 0, .s 125 0, .s 125 0, .s 125 0]⟩,
    ⟨-9, 1, 6, 19, [[.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0]], [.s 116 1, .s 116 1, .s 116 1, .s 116 1]⟩,
    ⟨-9, 1, 7, 14, [[.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0]], [.s 124 2, .s 124 2, .s 124 2, .s 124 2]⟩,
    ⟨-9, 1, 8, 18, [[.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0]], [.s 118 2, .s 118 2, .s 118 2, .s 118 2]⟩,
    ⟨-9, 1, 9, 15, [[.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0]], [.s 115 2, .s 115 2, .s 115 2, .s 115 2]⟩,
    ⟨-9, 1, 10, 17, [[.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0]], [.s 119 2, .s 119 2, .s 119 2, .s 119 2]⟩,
    ⟨-9, 1, 11, 16, [[.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0]], [.s 117 2, .s 117 2, .s 117 2, .s 117 2]⟩,
    ⟨-8, 1, 0, 11, [[.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.f ⟨12, 74, 0, 0, 0, 0, 0, 0, 0⟩, .s 86 0, .f ⟨12, 74, 0, 1, 1, 0, 0, 0, 0⟩, .s 86 0], [.s 132 0, .s 132 0, .s 132 0, .s 132 0]], [.f ⟨12, 74, 0, 0, 0, 0, 0, 0, 3⟩, .s 86 3, .f ⟨12, 74, 0, 1, 1, 0, 0, 0, 3⟩, .s 86 3]⟩,
    ⟨-8, 1, 1, 11, [[.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 132 0, .s 132 0, .s 132 0, .s 132 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0]], [.s 132 1, .s 132 1, .s 132 1, .s 132 1]⟩,
    ⟨-8, 1, 2, 19, [[.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.f ⟨25, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 12, 1, 0, 2, 0, 0, 0, 0⟩, .s 12 0, .s 12 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0]], [.s 125 1, .s 125 1, .s 125 1, .s 125 1]⟩,
    ⟨-8, 1, 3, 12, [[.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0]], [.s 121 1, .s 121 1, .s 121 1, .s 121 1]⟩,
    ⟨-8, 1, 4, 13, [[.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0]], [.s 123 2, .s 123 2, .s 123 2, .s 123 2]⟩,
    ⟨-8, 1, 5, 18, [[.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0]], [.s 137 0, .s 137 0, .s 137 0, .s 137 0]⟩,
    ⟨-8, 1, 6, 18, [[.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0]], [.s 128 1, .s 128 1, .s 128 1, .s 128 1]⟩,
    ⟨-8, 1, 7, 13, [[.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0]], [.s 136 2, .s 136 2, .s 136 2, .s 136 2]⟩,
    ⟨-8, 1, 8, 17, [[.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0]], [.s 130 2, .s 130 2, .s 130 2, .s 130 2]⟩,
    ⟨-8, 1, 9, 14, [[.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0]], [.s 127 2, .s 127 2, .s 127 2, .s 127 2]⟩,
    ⟨-8, 1, 10, 16, [[.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0]], [.s 131 2, .s 131 2, .s 131 2, .s 131 2]⟩,
    ⟨-8, 1, 11, 15, [[.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0]], [.s 129 2, .s 129 2, .s 129 2, .s 129 2]⟩,
    ⟨-7, 1, 0, 10, [[.s 120 0, .s 120 0, .s 120 0, .s 120 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.f ⟨12, 62, 0, 0, 0, 0, 0, 0, 0⟩, .s 98 0, .f ⟨12, 62, 0, 1, 1, 0, 0, 0, 0⟩, .s 98 0], [.f ⟨25, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 0 0, .s 0 0]], [.f ⟨12, 62, 0, 0, 0, 0, 0, 0, 3⟩, .s 98 3, .f ⟨12, 62, 0, 1, 1, 0, 0, 0, 3⟩, .s 98 3]⟩,
    ⟨-7, 1, 1, 10, [[.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.f ⟨25, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 0, 1, 0, 1, 0, 0, 0, 0⟩, .s 0 0, .s 0 0], [.f ⟨25, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 1, 1, 0, 1, 0, 0, 0, 0⟩, .s 1 0, .s 1 0]], [.f ⟨25, 0, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨25, 0, 1, 0, 1, 0, 0, 0, 1⟩, .s 0 1, .s 0 1]⟩,
    ⟨-7, 1, 2, 18, [[.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.f ⟨25, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨25, 24, 1, 0, 2, 0, 0, 0, 0⟩, .s 24 0, .s 24 0], [.f ⟨25, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 2 0, .s 2 0]], [.s 137 1, .s 137 1, .s 137 1, .s 137 1]⟩,
    ⟨-7, 1, 3, 11, [[.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.f ⟨25, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 3, 1, 0, 1, 0, 0, 0, 0⟩, .s 3 0, .s 3 0], [.f ⟨25, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 4, 1, 0, 1, 0, 0, 0, 0⟩, .s 4 0, .s 4 0]], [.s 133 1, .s 133 1, .s 133 1, .s 133 1]⟩,
    ⟨-7, 1, 4, 12, [[.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.f ⟨25, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 4, 1, 0, 1, 0, 0, 0, 0⟩, .s 4 0, .s 4 0]], [.s 135 2, .s 135 2, .s 135 2, .s 135 2]⟩,
    ⟨-7, 1, 5, 17, [[.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.f ⟨25, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 2, 1, 0, 1, 0, 0, 0, 0⟩, .s 2 0, .s 2 0], [.f ⟨25, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 5 0, .s 5 0], [.f ⟨25, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 6, 1, 0, 1, 0, 0, 0, 0⟩, .s 6 0, .s 6 0]], [.f ⟨25, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 5, 1, 0, 1, 0, 0, 0, 0⟩, .s 5 0, .s 5 0]⟩,
    ⟨-7, 1, 6, 17, [[.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.f ⟨25, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 6, 1, 0, 1, 0, 0, 0, 0⟩, .s 6 0, .s 6 0]], [.s 140 1, .s 140 1, .s 140 1, .s 140 1]⟩,
    ⟨-7, 1, 7, 12, [[.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.f ⟨25, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 4, 1, 0, 1, 0, 0, 0, 0⟩, .s 4 0, .s 4 0], [.f ⟨25, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 7, 1, 0, 1, 0, 0, 0, 0⟩, .s 7 0, .s 7 0]], [.f ⟨25, 4, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨25, 4, 1, 0, 1, 0, 0, 0, 2⟩, .s 4 2, .s 4 2]⟩,
    ⟨-7, 1, 8, 16, [[.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.f ⟨25, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 8, 1, 0, 1, 0, 0, 0, 0⟩, .s 8 0, .s 8 0]], [.s 142 2, .s 142 2, .s 142 2, .s 142 2]⟩,
    ⟨-7, 1, 9, 13, [[.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.f ⟨25, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 9, 1, 0, 1, 0, 0, 0, 0⟩, .s 9 0, .s 9 0]], [.s 139 2, .s 139 2, .s 139 2, .s 139 2]⟩,
    ⟨-7, 1, 10, 15, [[.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.f ⟨25, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 10, 1, 0, 1, 0, 0, 0, 0⟩, .s 10 0, .s 10 0]], [.s 143 2, .s 143 2, .s 143 2, .s 143 2]⟩,
    ⟨-7, 1, 11, 14, [[.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.f ⟨25, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 10, 1, 0, 1, 0, 0, 0, 0⟩, .s 10 0, .s 10 0], [.f ⟨25, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨25, 11, 1, 0, 1, 0, 0, 0, 0⟩, .s 11 0, .s 11 0]], [.s 141 2, .s 141 2, .s 141 2, .s 141 2]⟩]⟩,
  ⟨1, -2, -1, 0, 0, [(0, -12, 4), (-1, 2, 1), (1, -2, -3)], 0, -12, 4, 12, 0, 0, 0, 0,
   [⟨-5, -1, 0, 22, [[.f ⟨28, 132, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 132, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨28, 133, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 133, 0, 0, 0, 1, 0, 1, 0⟩], [.s 26 0, .s 26 0], [.s 12 0, .s 12 0]], [.f ⟨28, 133, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨28, 133, 0, 0, 0, 1, 0, 1, 2⟩]⟩,
    ⟨-5, -1, 1, 20, [[.f ⟨28, 133, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 133, 0, 0, 0, 1, 0, 1, 0⟩], [.s 3 0, .s 3 0], [.s 12 0, .s 12 0], [.s 13 0, .s 13 0]], [.s 3 1, .s 3 1]⟩,
    ⟨-5, -1, 2, 13, [[.f ⟨28, 134, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 134, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨28, 137, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 137, 0, 0, 0, 1, 0, 1, 0⟩], [.s 5 0, .s 5 0], [.f ⟨12, 36, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 120, 0, 0, 0, 1, 0, 0, 0⟩], [.s 14 0, .s 14 0]], [.f ⟨12, 36, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨28, 120, 0, 0, 0, 1, 0, 0, 2⟩]⟩,
    ⟨-5, -1, 3, 19, [[.f ⟨28, 135, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 135, 0, 0, 0, 1, 0, 1, 0⟩], [.s 1 0, .s 1 0], [.s 4 0, .s 4 0], [.s 15 0, .s 15 0], [.s 16 0, .s 16 0]], [.s 15 0, .s 15 0]⟩,
    ⟨-5, -1, 4, 19, [[.f ⟨28, 135, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 135, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨28, 136, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 136, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨28, 139, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 139, 0, 0, 0, 1, 0, 1, 0⟩], [.s 3 0, .s 3 0], [.s 7 0, .s 7 0], [.s 16 0, .s 16 0]], [.s 7 1, .s 7 1]⟩,
    ⟨-5, -1, 5, 13, [[.f ⟨28, 137, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 137, 0, 0, 0, 1, 0, 1, 0⟩], [.s 2 0, .s 2 0], [.s 6 0, .s 6 0], [.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 18 0, .s 18 0]], [.s 14 1, .s 14 1]⟩,
    ⟨-5, -1, 6, 14, [[.f ⟨28, 137, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 137, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨28, 138, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 138, 0, 0, 0, 1, 0, 1, 0⟩], [.s 5 0, .s 5 0], [.s 8 0, .s 8 0], [.s 18 0, .s 18 0]], [.s 5 2, .s 5 2]⟩,
    ⟨-5, -1, 7, 18, [[.f ⟨28, 139, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 139, 0, 0, 0, 1, 0, 1, 0⟩], [.s 4 0, .s 4 0], [.s 9 0, .s 9 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0]], [.s 9 1, .s 9 1]⟩,
    ⟨-5, -1, 8, 15, [[.f ⟨28, 140, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 140, 0, 0, 0, 1, 0, 1, 0⟩], [.s 6 0, .s 6 0], [.s 10 0, .s 10 0], [.s 20 0, .s 20 0]], [.s 6 3, .s 6 3]⟩,
    ⟨-5, -1, 9, 17, [[.f ⟨28, 141, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 141, 0, 0, 0, 1, 0, 1, 0⟩], [.s 7 0, .s 7 0], [.s 11 0, .s 11 0], [.s 21 0, .s 21 0]], [.s 11 1, .s 11 1]⟩,
    ⟨-5, -1, 10, 16, [[.f ⟨28, 142, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 142, 0, 0, 0, 1, 0, 1, 0⟩], [.f ⟨28, 143, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 143, 0, 0, 0, 1, 0, 1, 0⟩], [.s 8 0, .s 8 0], [.s 11 0, .s 11 0], [.s 22 0, .s 22 0]], [.s 8 2, .s 8 2]⟩,
    ⟨-5, -1, 11, 16, [[.f ⟨28, 143, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 143, 0, 0, 0, 1, 0, 1, 0⟩], [.s 9 0, .s 9 0], [.s 10 0, .s 10 0], [.s 22 0, .s 22 0], [.s 23 0, .s 23 0]], [.s 22 1, .s 22 1]⟩,
    ⟨-4, -1, 0, 21, [[.s 0 0, .s 0 0], [.s 1 0, .s 1 0], [.f ⟨2, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 2, 1, 0, 1, 0, 0, 0, 0⟩], [.s 24 0, .s 24 0]], [.s 1 2, .s 1 2]⟩,
    ⟨-4, -1, 1, 19, [[.s 1 0, .s 1 0], [.s 15 0, .s 15 0], [.s 24 0, .s 24 0], [.s 25 0, .s 25 0]], [.s 15 1, .s 15 1]⟩,
    ⟨-4, -1, 2, 12, [[.s 2 0, .s 2 0], [.s 5 0, .s 5 0], [.s 17 0, .s 17 0], [.f ⟨12, 24, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨28, 132, 0, 0, 0, 1, 0, 0, 0⟩], [.s 26 0, .s 26 0]], [.f ⟨12, 24, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨28, 132, 0, 0, 0, 1, 0, 0, 2⟩]⟩,
    ⟨-4, -1, 3, 18, [[.s 3 0, .s 3 0], [.s 13 0, .s 13 0], [.s 16 0, .s 16 0], [.s 27 0, .s 27 0], [.s 28 0, .s 28 0]], [.s 28 0, .s 28 0]⟩,
    ⟨-4, -1, 4, 18, [[.s 3 0, .s 3 0], [.s 4 0, .s 4 0], [.s 7 0, .s 7 0], [.s 15 0, .s 15 0], [.s 19 0, .s 19 0], [.s 28 0, .s 28 0]], [.s 19 1, .s 19 1]⟩,
    ⟨-4, -1, 5, 12, [[.s 5 0, .s 5 0], [.s 14 0, .s 14 0], [.s 18 0, .s 18 0], [.s 26 0, .s 26 0], [.s 29 0, .s 29 0], [.s 30 0, .s 30 0]], [.s 26 1, .s 26 1]⟩,
    ⟨-4, -1, 6, 13, [[.s 5 0, .s 5 0], [.s 6 0, .s 6 0], [.s 17 0, .s 17 0], [.s 20 0, .s 20 0], [.s 30 0, .s 30 0]], [.s 17 2, .s 17 2]⟩,
    ⟨-4, -1, 7, 17, [[.s 7 0, .s 7 0], [.s 16 0, .s 16 0], [.s 21 0, .s 21 0], [.s 28 0, .s 28 0], [.s 31 0, .s 31 0]], [.s 21 1, .s 21 1]⟩,
    ⟨-4, -1, 8, 14, [[.s 8 0, .s 8 0], [.s 18 0, .s 18 0], [.s 22 0, .s 22 0], [.s 32 0, .s 32 0]], [.s 18 3, .s 18 3]⟩,
    ⟨-4, -1, 9, 16, [[.s 9 0, .s 9 0], [.s 19 0, .s 19 0], [.s 23 0, .s 23 0], [.s 33 0, .s 33 0]], [.s 23 1, .s 23 1]⟩,
    ⟨-4, -1, 10, 15, [[.s 10 0, .s 10 0], [.s 11 0, .s 11 0], [.s 20 0, .s 20 0], [.s 23 0, .s 23 0], [.s 34 0, .s 34 0]], [.s 20 2, .s 20 2]⟩,
    ⟨-4, -1, 11, 15, [[.s 11 0, .s 11 0], [.s 21 0, .s 21 0], [.s 22 0, .s 22 0], [.s 34 0, .s 34 0], [.s 35 0, .s 35 0]], [.s 34 1, .s 34 1]⟩,
    ⟨-3, -1, 0, 20, [[.s 12 0, .s 12 0], [.s 13 0, .s 13 0], [.f ⟨14, 26, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨14, 26, 1, 0, 2, 0, 0, 0, 0⟩], [.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 0, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 13 2, .s 13 2]⟩,
    ⟨-3, -1, 1, 19, [[.s 13 0, .s 13 0], [.s 27 0, .s 27 0], [.f ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 0, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 1, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 1, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 27 1, .s 27 1]⟩,
    ⟨-3, -1, 2, 11, [[.s 14 0, .s 14 0], [.s 17 0, .s 17 0], [.s 29 0, .s 29 0], [.f ⟨12, 12, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 2, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨12, 12, 0, 0, 0, 0, 0, 0, 2⟩, .s 0 2]⟩,
    ⟨-3, -1, 3, 18, [[.s 15 0, .s 15 0], [.s 25 0, .s 25 0], [.s 28 0, .s 28 0], [.f ⟨1, 3, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 3, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 4, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 28 3, .s 28 3]⟩,
    ⟨-3, -1, 4, 17, [[.s 15 0, .s 15 0], [.s 16 0, .s 16 0], [.s 19 0, .s 19 0], [.s 27 0, .s 27 0], [.s 31 0, .s 31 0], [.f ⟨1, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 4, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 31 1, .s 31 1]⟩,
    ⟨-3, -1, 5, 11, [[.s 17 0, .s 17 0], [.s 26 0, .s 26 0], [.s 30 0, .s 30 0], [.f ⟨1, 2, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 2, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 5, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 5, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 6, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨1, 2, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨2, 2, 1, 0, 0, 0, 0, 0, 1⟩]⟩,
    ⟨-3, -1, 6, 12, [[.s 17 0, .s 17 0], [.s 18 0, .s 18 0], [.s 29 0, .s 29 0], [.s 32 0, .s 32 0], [.f ⟨1, 6, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 6, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 29 2, .s 29 2]⟩,
    ⟨-3, -1, 7, 16, [[.s 19 0, .s 19 0], [.s 28 0, .s 28 0], [.s 33 0, .s 33 0], [.f ⟨1, 4, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 4, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 7, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 7, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 33 1, .s 33 1]⟩,
    ⟨-3, -1, 8, 13, [[.s 20 0, .s 20 0], [.s 30 0, .s 30 0], [.s 34 0, .s 34 0], [.f ⟨1, 8, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 8, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 30 3, .s 30 3]⟩,
    ⟨-3, -1, 9, 15, [[.s 21 0, .s 21 0], [.s 31 0, .s 31 0], [.s 35 0, .s 35 0], [.f ⟨1, 9, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 9, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 35 1, .s 35 1]⟩,
    ⟨-3, -1, 10, 14, [[.s 22 0, .s 22 0], [.s 23 0, .s 23 0], [.s 32 0, .s 32 0], [.s 35 0, .s 35 0], [.f ⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 10, 1, 0, 0, 0, 0, 0, 0⟩]], [.s 32 2, .s 32 2]⟩,
    ⟨-3, -1, 11, 14, [[.s 23 0, .s 23 0], [.s 33 0, .s 33 0], [.s 34 0, .s 34 0], [.f ⟨1, 10, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 10, 1, 0, 0, 0, 0, 0, 0⟩], [.f ⟨1, 11, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨2, 11, 1, 0, 0, 0, 0, 0, 0⟩]], [.f ⟨1, 10, 0, 0, 0, 0, 0, 0, 1⟩, .f ⟨2, 10, 1, 0, 0, 0, 0, 0, 1⟩]⟩]⟩,
  ⟨2, -12, 0, -2, -1, [(-1, 2, 4), (0, -12, 4)], -1, 2, 4, 12, 0, -12, 4, 12,
   [⟨-17, -1, 0, 34, [[.s 132 0, .s 132 0, .s 132 0, .s 132 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0]], [.s 133 2, .s 133 2, .s 133 2, .s 133 2]⟩,
    ⟨-17, -1, 1, 32, [[.s 133 0, .s 133 0, .s 133 0, .s 133 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0]], [.s 3 1, .s 3 1, .s 3 1, .s 3 1]⟩,
    ⟨-17, -1, 2, 25, [[.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.f ⟨12, 36, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨12, 36, 1, 0, 2, 0, 0, 0, 0⟩, .s 120 0, .s 120 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0]], [.f ⟨12, 36, 0, 0, 1, 0, 0, 0, 2⟩, .f ⟨12, 36, 1, 0, 2, 0, 0, 0, 2⟩, .s 120 2, .s 120 2]⟩,
    ⟨-17, -1, 3, 31, [[.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]], [.s 15 0, .s 15 0, .s 15 0, .s 15 0]⟩,
    ⟨-17, -1, 4, 31, [[.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0]], [.s 7 1, .s 7 1, .s 7 1, .s 7 1]⟩,
    ⟨-17, -1, 5, 25, [[.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 14 1, .s 14 1, .s 14 1, .s 14 1]⟩,
    ⟨-17, -1, 6, 26, [[.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0]], [.s 5 2, .s 5 2, .s 5 2, .s 5 2]⟩,
    ⟨-17, -1, 7, 30, [[.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0]], [.s 9 1, .s 9 1, .s 9 1, .s 9 1]⟩,
    ⟨-17, -1, 8, 27, [[.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0]], [.s 6 3, .s 6 3, .s 6 3, .s 6 3]⟩,
    ⟨-17, -1, 9, 29, [[.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0]], [.s 11 1, .s 11 1, .s 11 1, .s 11 1]⟩,
    ⟨-17, -1, 10, 28, [[.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0]], [.s 8 2, .s 8 2, .s 8 2, .s 8 2]⟩,
    ⟨-17, -1, 11, 28, [[.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0]], [.s 22 1, .s 22 1, .s 22 1, .s 22 1]⟩,
    ⟨-16, -1, 0, 33, [[.s 0 0, .s 0 0, .s 0 0, .s 0 0], [.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0]], [.s 1 2, .s 1 2, .s 1 2, .s 1 2]⟩,
    ⟨-16, -1, 1, 31, [[.s 1 0, .s 1 0, .s 1 0, .s 1 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0]], [.s 15 1, .s 15 1, .s 15 1, .s 15 1]⟩,
    ⟨-16, -1, 2, 24, [[.s 2 0, .s 2 0, .s 2 0, .s 2 0], [.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.f ⟨12, 24, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨12, 24, 1, 0, 2, 0, 0, 0, 0⟩, .s 132 0, .s 132 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0]], [.f ⟨12, 24, 0, 0, 1, 0, 0, 0, 2⟩, .f ⟨12, 24, 1, 0, 2, 0, 0, 0, 2⟩, .s 132 2, .s 132 2]⟩,
    ⟨-16, -1, 3, 30, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 27 0, .s 27 0, .s 27 0, .s 27 0]⟩,
    ⟨-16, -1, 4, 30, [[.s 3 0, .s 3 0, .s 3 0, .s 3 0], [.s 4 0, .s 4 0, .s 4 0, .s 4 0], [.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0]], [.s 19 1, .s 19 1, .s 19 1, .s 19 1]⟩,
    ⟨-16, -1, 5, 24, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 26 1, .s 26 1, .s 26 1, .s 26 1]⟩,
    ⟨-16, -1, 6, 25, [[.s 5 0, .s 5 0, .s 5 0, .s 5 0], [.s 6 0, .s 6 0, .s 6 0, .s 6 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0]], [.s 17 2, .s 17 2, .s 17 2, .s 17 2]⟩,
    ⟨-16, -1, 7, 29, [[.s 7 0, .s 7 0, .s 7 0, .s 7 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0]], [.s 21 1, .s 21 1, .s 21 1, .s 21 1]⟩,
    ⟨-16, -1, 8, 26, [[.s 8 0, .s 8 0, .s 8 0, .s 8 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0]], [.s 18 3, .s 18 3, .s 18 3, .s 18 3]⟩,
    ⟨-16, -1, 9, 28, [[.s 9 0, .s 9 0, .s 9 0, .s 9 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0]], [.s 23 1, .s 23 1, .s 23 1, .s 23 1]⟩,
    ⟨-16, -1, 10, 27, [[.s 10 0, .s 10 0, .s 10 0, .s 10 0], [.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0]], [.s 20 2, .s 20 2, .s 20 2, .s 20 2]⟩,
    ⟨-16, -1, 11, 27, [[.s 11 0, .s 11 0, .s 11 0, .s 11 0], [.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0]], [.s 34 1, .s 34 1, .s 34 1, .s 34 1]⟩,
    ⟨-15, -1, 0, 32, [[.s 12 0, .s 12 0, .s 12 0, .s 12 0], [.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0]], [.s 13 2, .s 13 2, .s 13 2, .s 13 2]⟩,
    ⟨-15, -1, 1, 30, [[.s 13 0, .s 13 0, .s 13 0, .s 13 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0]], [.s 27 1, .s 27 1, .s 27 1, .s 27 1]⟩,
    ⟨-15, -1, 2, 23, [[.s 14 0, .s 14 0, .s 14 0, .s 14 0], [.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.f ⟨12, 12, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨12, 12, 1, 0, 2, 0, 0, 0, 0⟩, .s 0 0, .s 0 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0]], [.f ⟨12, 12, 0, 0, 1, 0, 0, 0, 2⟩, .f ⟨12, 12, 1, 0, 2, 0, 0, 0, 2⟩, .s 0 2, .s 0 2]⟩,
    ⟨-15, -1, 3, 29, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 39 0, .s 39 0, .s 39 0, .s 39 0]⟩,
    ⟨-15, -1, 4, 29, [[.s 15 0, .s 15 0, .s 15 0, .s 15 0], [.s 16 0, .s 16 0, .s 16 0, .s 16 0], [.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0]], [.s 31 1, .s 31 1, .s 31 1, .s 31 1]⟩,
    ⟨-15, -1, 5, 23, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 38 1, .s 38 1, .s 38 1, .s 38 1]⟩,
    ⟨-15, -1, 6, 24, [[.s 17 0, .s 17 0, .s 17 0, .s 17 0], [.s 18 0, .s 18 0, .s 18 0, .s 18 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0]], [.s 29 2, .s 29 2, .s 29 2, .s 29 2]⟩,
    ⟨-15, -1, 7, 28, [[.s 19 0, .s 19 0, .s 19 0, .s 19 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0]], [.s 33 1, .s 33 1, .s 33 1, .s 33 1]⟩,
    ⟨-15, -1, 8, 25, [[.s 20 0, .s 20 0, .s 20 0, .s 20 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0]], [.s 30 3, .s 30 3, .s 30 3, .s 30 3]⟩,
    ⟨-15, -1, 9, 27, [[.s 21 0, .s 21 0, .s 21 0, .s 21 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0]], [.s 35 1, .s 35 1, .s 35 1, .s 35 1]⟩,
    ⟨-15, -1, 10, 26, [[.s 22 0, .s 22 0, .s 22 0, .s 22 0], [.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0]], [.s 32 2, .s 32 2, .s 32 2, .s 32 2]⟩,
    ⟨-15, -1, 11, 26, [[.s 23 0, .s 23 0, .s 23 0, .s 23 0], [.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0]], [.s 46 1, .s 46 1, .s 46 1, .s 46 1]⟩,
    ⟨-14, -1, 0, 31, [[.s 24 0, .s 24 0, .s 24 0, .s 24 0], [.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0]], [.s 25 2, .s 25 2, .s 25 2, .s 25 2]⟩,
    ⟨-14, -1, 1, 29, [[.s 25 0, .s 25 0, .s 25 0, .s 25 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0]], [.s 39 1, .s 39 1, .s 39 1, .s 39 1]⟩,
    ⟨-14, -1, 2, 22, [[.s 26 0, .s 26 0, .s 26 0, .s 26 0], [.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.f ⟨12, 0, 0, 0, 1, 0, 0, 0, 0⟩, .f ⟨12, 0, 1, 0, 2, 0, 0, 0, 0⟩, .s 12 0, .s 12 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0]], [.f ⟨12, 0, 0, 0, 1, 0, 0, 0, 2⟩, .f ⟨12, 0, 1, 0, 2, 0, 0, 0, 2⟩, .s 12 2, .s 12 2]⟩,
    ⟨-14, -1, 3, 28, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 51 0, .s 51 0, .s 51 0, .s 51 0]⟩,
    ⟨-14, -1, 4, 28, [[.s 27 0, .s 27 0, .s 27 0, .s 27 0], [.s 28 0, .s 28 0, .s 28 0, .s 28 0], [.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0]], [.s 43 1, .s 43 1, .s 43 1, .s 43 1]⟩,
    ⟨-14, -1, 5, 22, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 50 1, .s 50 1, .s 50 1, .s 50 1]⟩,
    ⟨-14, -1, 6, 23, [[.s 29 0, .s 29 0, .s 29 0, .s 29 0], [.s 30 0, .s 30 0, .s 30 0, .s 30 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0]], [.s 41 2, .s 41 2, .s 41 2, .s 41 2]⟩,
    ⟨-14, -1, 7, 27, [[.s 31 0, .s 31 0, .s 31 0, .s 31 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0]], [.s 45 1, .s 45 1, .s 45 1, .s 45 1]⟩,
    ⟨-14, -1, 8, 24, [[.s 32 0, .s 32 0, .s 32 0, .s 32 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0]], [.s 42 3, .s 42 3, .s 42 3, .s 42 3]⟩,
    ⟨-14, -1, 9, 26, [[.s 33 0, .s 33 0, .s 33 0, .s 33 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0]], [.s 47 1, .s 47 1, .s 47 1, .s 47 1]⟩,
    ⟨-14, -1, 10, 25, [[.s 34 0, .s 34 0, .s 34 0, .s 34 0], [.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0]], [.s 44 2, .s 44 2, .s 44 2, .s 44 2]⟩,
    ⟨-14, -1, 11, 25, [[.s 35 0, .s 35 0, .s 35 0, .s 35 0], [.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0]], [.s 58 1, .s 58 1, .s 58 1, .s 58 1]⟩,
    ⟨-13, -1, 0, 30, [[.s 36 0, .s 36 0, .s 36 0, .s 36 0], [.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0]], [.s 37 2, .s 37 2, .s 37 2, .s 37 2]⟩,
    ⟨-13, -1, 1, 28, [[.s 37 0, .s 37 0, .s 37 0, .s 37 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0]], [.s 51 1, .s 51 1, .s 51 1, .s 51 1]⟩,
    ⟨-13, -1, 2, 21, [[.s 38 0, .s 38 0, .s 38 0, .s 38 0], [.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.f ⟨12, 132, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 132, 1, 0, 1, 0, 0, 0, 0⟩, .s 24 0, .s 24 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0]], [.f ⟨12, 132, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨12, 132, 1, 0, 1, 0, 0, 0, 2⟩, .s 24 2, .s 24 2]⟩,
    ⟨-13, -1, 3, 27, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 63 0, .s 63 0, .s 63 0, .s 63 0]⟩,
    ⟨-13, -1, 4, 27, [[.s 39 0, .s 39 0, .s 39 0, .s 39 0], [.s 40 0, .s 40 0, .s 40 0, .s 40 0], [.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0]], [.s 55 1, .s 55 1, .s 55 1, .s 55 1]⟩,
    ⟨-13, -1, 5, 21, [[.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 62 1, .s 62 1, .s 62 1, .s 62 1]⟩,
    ⟨-13, -1, 6, 22, [[.s 41 0, .s 41 0, .s 41 0, .s 41 0], [.s 42 0, .s 42 0, .s 42 0, .s 42 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0]], [.s 53 2, .s 53 2, .s 53 2, .s 53 2]⟩,
    ⟨-13, -1, 7, 26, [[.s 43 0, .s 43 0, .s 43 0, .s 43 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0]], [.s 57 1, .s 57 1, .s 57 1, .s 57 1]⟩,
    ⟨-13, -1, 8, 23, [[.s 44 0, .s 44 0, .s 44 0, .s 44 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0]], [.s 54 3, .s 54 3, .s 54 3, .s 54 3]⟩,
    ⟨-13, -1, 9, 25, [[.s 45 0, .s 45 0, .s 45 0, .s 45 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0]], [.s 59 1, .s 59 1, .s 59 1, .s 59 1]⟩,
    ⟨-13, -1, 10, 24, [[.s 46 0, .s 46 0, .s 46 0, .s 46 0], [.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0]], [.s 56 2, .s 56 2, .s 56 2, .s 56 2]⟩,
    ⟨-13, -1, 11, 24, [[.s 47 0, .s 47 0, .s 47 0, .s 47 0], [.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0]], [.s 70 1, .s 70 1, .s 70 1, .s 70 1]⟩,
    ⟨-12, -1, 0, 29, [[.s 48 0, .s 48 0, .s 48 0, .s 48 0], [.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0]], [.s 49 2, .s 49 2, .s 49 2, .s 49 2]⟩,
    ⟨-12, -1, 1, 27, [[.s 49 0, .s 49 0, .s 49 0, .s 49 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0]], [.s 63 1, .s 63 1, .s 63 1, .s 63 1]⟩,
    ⟨-12, -1, 2, 20, [[.s 50 0, .s 50 0, .s 50 0, .s 50 0], [.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.f ⟨12, 120, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 120, 1, 0, 1, 0, 0, 0, 0⟩, .s 36 0, .s 36 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0]], [.f ⟨12, 120, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨12, 120, 1, 0, 1, 0, 0, 0, 2⟩, .s 36 2, .s 36 2]⟩,
    ⟨-12, -1, 3, 26, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 75 0, .s 75 0, .s 75 0, .s 75 0]⟩,
    ⟨-12, -1, 4, 26, [[.s 51 0, .s 51 0, .s 51 0, .s 51 0], [.s 52 0, .s 52 0, .s 52 0, .s 52 0], [.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0]], [.s 67 1, .s 67 1, .s 67 1, .s 67 1]⟩,
    ⟨-12, -1, 5, 20, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0]], [.s 74 1, .s 74 1, .s 74 1, .s 74 1]⟩,
    ⟨-12, -1, 6, 21, [[.s 53 0, .s 53 0, .s 53 0, .s 53 0], [.s 54 0, .s 54 0, .s 54 0, .s 54 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0]], [.s 65 2, .s 65 2, .s 65 2, .s 65 2]⟩,
    ⟨-12, -1, 7, 25, [[.s 55 0, .s 55 0, .s 55 0, .s 55 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0]], [.s 69 1, .s 69 1, .s 69 1, .s 69 1]⟩,
    ⟨-12, -1, 8, 22, [[.s 56 0, .s 56 0, .s 56 0, .s 56 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0]], [.s 66 3, .s 66 3, .s 66 3, .s 66 3]⟩,
    ⟨-12, -1, 9, 24, [[.s 57 0, .s 57 0, .s 57 0, .s 57 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0]], [.s 71 1, .s 71 1, .s 71 1, .s 71 1]⟩,
    ⟨-12, -1, 10, 23, [[.s 58 0, .s 58 0, .s 58 0, .s 58 0], [.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0]], [.s 68 2, .s 68 2, .s 68 2, .s 68 2]⟩,
    ⟨-12, -1, 11, 23, [[.s 59 0, .s 59 0, .s 59 0, .s 59 0], [.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0]], [.s 82 1, .s 82 1, .s 82 1, .s 82 1]⟩,
    ⟨-11, -1, 0, 28, [[.s 60 0, .s 60 0, .s 60 0, .s 60 0], [.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0]], [.s 61 2, .s 61 2, .s 61 2, .s 61 2]⟩,
    ⟨-11, -1, 1, 26, [[.s 61 0, .s 61 0, .s 61 0, .s 61 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0]], [.s 75 1, .s 75 1, .s 75 1, .s 75 1]⟩,
    ⟨-11, -1, 2, 19, [[.s 62 0, .s 62 0, .s 62 0, .s 62 0], [.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.f ⟨12, 108, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 108, 1, 0, 1, 0, 0, 0, 0⟩, .s 48 0, .s 48 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0]], [.f ⟨12, 108, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨12, 108, 1, 0, 1, 0, 0, 0, 2⟩, .s 48 2, .s 48 2]⟩,
    ⟨-11, -1, 3, 25, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0]], [.s 87 0, .s 87 0, .s 87 0, .s 87 0]⟩,
    ⟨-11, -1, 4, 25, [[.s 63 0, .s 63 0, .s 63 0, .s 63 0], [.s 64 0, .s 64 0, .s 64 0, .s 64 0], [.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0]], [.s 79 1, .s 79 1, .s 79 1, .s 79 1]⟩,
    ⟨-11, -1, 5, 19, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0]], [.s 86 1, .s 86 1, .s 86 1, .s 86 1]⟩,
    ⟨-11, -1, 6, 20, [[.s 65 0, .s 65 0, .s 65 0, .s 65 0], [.s 66 0, .s 66 0, .s 66 0, .s 66 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0]], [.s 77 2, .s 77 2, .s 77 2, .s 77 2]⟩,
    ⟨-11, -1, 7, 24, [[.s 67 0, .s 67 0, .s 67 0, .s 67 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0]], [.s 81 1, .s 81 1, .s 81 1, .s 81 1]⟩,
    ⟨-11, -1, 8, 21, [[.s 68 0, .s 68 0, .s 68 0, .s 68 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0]], [.s 78 3, .s 78 3, .s 78 3, .s 78 3]⟩,
    ⟨-11, -1, 9, 23, [[.s 69 0, .s 69 0, .s 69 0, .s 69 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0]], [.s 83 1, .s 83 1, .s 83 1, .s 83 1]⟩,
    ⟨-11, -1, 10, 22, [[.s 70 0, .s 70 0, .s 70 0, .s 70 0], [.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0]], [.s 80 2, .s 80 2, .s 80 2, .s 80 2]⟩,
    ⟨-11, -1, 11, 22, [[.s 71 0, .s 71 0, .s 71 0, .s 71 0], [.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0]], [.s 94 1, .s 94 1, .s 94 1, .s 94 1]⟩,
    ⟨-10, -1, 0, 27, [[.s 72 0, .s 72 0, .s 72 0, .s 72 0], [.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0]], [.s 73 2, .s 73 2, .s 73 2, .s 73 2]⟩,
    ⟨-10, -1, 1, 25, [[.s 73 0, .s 73 0, .s 73 0, .s 73 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0]], [.s 87 1, .s 87 1, .s 87 1, .s 87 1]⟩,
    ⟨-10, -1, 2, 18, [[.s 74 0, .s 74 0, .s 74 0, .s 74 0], [.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.f ⟨12, 96, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 96, 1, 0, 1, 0, 0, 0, 0⟩, .s 60 0, .s 60 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0]], [.f ⟨12, 96, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨12, 96, 1, 0, 1, 0, 0, 0, 2⟩, .s 60 2, .s 60 2]⟩,
    ⟨-10, -1, 3, 24, [[.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0]], [.s 99 0, .s 99 0, .s 99 0, .s 99 0]⟩,
    ⟨-10, -1, 4, 24, [[.s 75 0, .s 75 0, .s 75 0, .s 75 0], [.s 76 0, .s 76 0, .s 76 0, .s 76 0], [.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0]], [.s 91 1, .s 91 1, .s 91 1, .s 91 1]⟩,
    ⟨-10, -1, 5, 18, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0]], [.s 98 1, .s 98 1, .s 98 1, .s 98 1]⟩,
    ⟨-10, -1, 6, 19, [[.s 77 0, .s 77 0, .s 77 0, .s 77 0], [.s 78 0, .s 78 0, .s 78 0, .s 78 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0]], [.s 89 2, .s 89 2, .s 89 2, .s 89 2]⟩,
    ⟨-10, -1, 7, 23, [[.s 79 0, .s 79 0, .s 79 0, .s 79 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0]], [.s 93 1, .s 93 1, .s 93 1, .s 93 1]⟩,
    ⟨-10, -1, 8, 20, [[.s 80 0, .s 80 0, .s 80 0, .s 80 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0]], [.s 90 3, .s 90 3, .s 90 3, .s 90 3]⟩,
    ⟨-10, -1, 9, 22, [[.s 81 0, .s 81 0, .s 81 0, .s 81 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0]], [.s 95 1, .s 95 1, .s 95 1, .s 95 1]⟩,
    ⟨-10, -1, 10, 21, [[.s 82 0, .s 82 0, .s 82 0, .s 82 0], [.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0]], [.s 92 2, .s 92 2, .s 92 2, .s 92 2]⟩,
    ⟨-10, -1, 11, 21, [[.s 83 0, .s 83 0, .s 83 0, .s 83 0], [.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0]], [.s 106 1, .s 106 1, .s 106 1, .s 106 1]⟩,
    ⟨-9, -1, 0, 26, [[.s 84 0, .s 84 0, .s 84 0, .s 84 0], [.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0]], [.s 85 2, .s 85 2, .s 85 2, .s 85 2]⟩,
    ⟨-9, -1, 1, 24, [[.s 85 0, .s 85 0, .s 85 0, .s 85 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0]], [.s 99 1, .s 99 1, .s 99 1, .s 99 1]⟩,
    ⟨-9, -1, 2, 17, [[.s 86 0, .s 86 0, .s 86 0, .s 86 0], [.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.f ⟨12, 84, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 84, 1, 0, 1, 0, 0, 0, 0⟩, .s 72 0, .s 72 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0]], [.f ⟨12, 84, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨12, 84, 1, 0, 1, 0, 0, 0, 2⟩, .s 72 2, .s 72 2]⟩,
    ⟨-9, -1, 3, 23, [[.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0]], [.s 111 0, .s 111 0, .s 111 0, .s 111 0]⟩,
    ⟨-9, -1, 4, 23, [[.s 87 0, .s 87 0, .s 87 0, .s 87 0], [.s 88 0, .s 88 0, .s 88 0, .s 88 0], [.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0]], [.s 103 1, .s 103 1, .s 103 1, .s 103 1]⟩,
    ⟨-9, -1, 5, 17, [[.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0]], [.s 110 1, .s 110 1, .s 110 1, .s 110 1]⟩,
    ⟨-9, -1, 6, 18, [[.s 89 0, .s 89 0, .s 89 0, .s 89 0], [.s 90 0, .s 90 0, .s 90 0, .s 90 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0]], [.s 101 2, .s 101 2, .s 101 2, .s 101 2]⟩,
    ⟨-9, -1, 7, 22, [[.s 91 0, .s 91 0, .s 91 0, .s 91 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0]], [.s 105 1, .s 105 1, .s 105 1, .s 105 1]⟩,
    ⟨-9, -1, 8, 19, [[.s 92 0, .s 92 0, .s 92 0, .s 92 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0]], [.s 102 3, .s 102 3, .s 102 3, .s 102 3]⟩,
    ⟨-9, -1, 9, 21, [[.s 93 0, .s 93 0, .s 93 0, .s 93 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0]], [.s 107 1, .s 107 1, .s 107 1, .s 107 1]⟩,
    ⟨-9, -1, 10, 20, [[.s 94 0, .s 94 0, .s 94 0, .s 94 0], [.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0]], [.s 104 2, .s 104 2, .s 104 2, .s 104 2]⟩,
    ⟨-9, -1, 11, 20, [[.s 95 0, .s 95 0, .s 95 0, .s 95 0], [.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0]], [.s 118 1, .s 118 1, .s 118 1, .s 118 1]⟩,
    ⟨-8, -1, 0, 25, [[.s 96 0, .s 96 0, .s 96 0, .s 96 0], [.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 120 0, .s 120 0, .s 120 0, .s 120 0]], [.s 97 2, .s 97 2, .s 97 2, .s 97 2]⟩,
    ⟨-8, -1, 1, 23, [[.s 97 0, .s 97 0, .s 97 0, .s 97 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 120 0, .s 120 0, .s 120 0, .s 120 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0]], [.s 111 1, .s 111 1, .s 111 1, .s 111 1]⟩,
    ⟨-8, -1, 2, 16, [[.s 98 0, .s 98 0, .s 98 0, .s 98 0], [.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.f ⟨12, 72, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 72, 1, 0, 1, 0, 0, 0, 0⟩, .s 84 0, .s 84 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0]], [.f ⟨12, 72, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨12, 72, 1, 0, 1, 0, 0, 0, 2⟩, .s 84 2, .s 84 2]⟩,
    ⟨-8, -1, 3, 22, [[.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0]], [.s 123 0, .s 123 0, .s 123 0, .s 123 0]⟩,
    ⟨-8, -1, 4, 22, [[.s 99 0, .s 99 0, .s 99 0, .s 99 0], [.s 100 0, .s 100 0, .s 100 0, .s 100 0], [.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0]], [.s 115 1, .s 115 1, .s 115 1, .s 115 1]⟩,
    ⟨-8, -1, 5, 16, [[.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0]], [.s 122 1, .s 122 1, .s 122 1, .s 122 1]⟩,
    ⟨-8, -1, 6, 17, [[.s 101 0, .s 101 0, .s 101 0, .s 101 0], [.s 102 0, .s 102 0, .s 102 0, .s 102 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0]], [.s 113 2, .s 113 2, .s 113 2, .s 113 2]⟩,
    ⟨-8, -1, 7, 21, [[.s 103 0, .s 103 0, .s 103 0, .s 103 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0]], [.s 117 1, .s 117 1, .s 117 1, .s 117 1]⟩,
    ⟨-8, -1, 8, 18, [[.s 104 0, .s 104 0, .s 104 0, .s 104 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0]], [.s 114 3, .s 114 3, .s 114 3, .s 114 3]⟩,
    ⟨-8, -1, 9, 20, [[.s 105 0, .s 105 0, .s 105 0, .s 105 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0]], [.s 119 1, .s 119 1, .s 119 1, .s 119 1]⟩,
    ⟨-8, -1, 10, 19, [[.s 106 0, .s 106 0, .s 106 0, .s 106 0], [.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0]], [.s 116 2, .s 116 2, .s 116 2, .s 116 2]⟩,
    ⟨-8, -1, 11, 19, [[.s 107 0, .s 107 0, .s 107 0, .s 107 0], [.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0]], [.s 130 1, .s 130 1, .s 130 1, .s 130 1]⟩,
    ⟨-7, -1, 0, 24, [[.s 108 0, .s 108 0, .s 108 0, .s 108 0], [.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.f ⟨27, 2, 0, 0, 1, 0, 0, 0, 0⟩, .s 2 0, .f ⟨27, 2, 0, 1, 2, 0, 0, 0, 0⟩, .s 2 0], [.s 132 0, .s 132 0, .s 132 0, .s 132 0]], [.s 109 2, .s 109 2, .s 109 2, .s 109 2]⟩,
    ⟨-7, -1, 1, 22, [[.s 109 0, .s 109 0, .s 109 0, .s 109 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 132 0, .s 132 0, .s 132 0, .s 132 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0]], [.s 123 1, .s 123 1, .s 123 1, .s 123 1]⟩,
    ⟨-7, -1, 2, 15, [[.s 110 0, .s 110 0, .s 110 0, .s 110 0], [.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.f ⟨12, 60, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 60, 1, 0, 1, 0, 0, 0, 0⟩, .s 96 0, .s 96 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0]], [.f ⟨12, 60, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨12, 60, 1, 0, 1, 0, 0, 0, 2⟩, .s 96 2, .s 96 2]⟩,
    ⟨-7, -1, 3, 21, [[.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0]], [.s 135 0, .s 135 0, .s 135 0, .s 135 0]⟩,
    ⟨-7, -1, 4, 21, [[.s 111 0, .s 111 0, .s 111 0, .s 111 0], [.s 112 0, .s 112 0, .s 112 0, .s 112 0], [.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0]], [.s 127 1, .s 127 1, .s 127 1, .s 127 1]⟩,
    ⟨-7, -1, 5, 15, [[.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0]], [.s 134 1, .s 134 1, .s 134 1, .s 134 1]⟩,
    ⟨-7, -1, 6, 16, [[.s 113 0, .s 113 0, .s 113 0, .s 113 0], [.s 114 0, .s 114 0, .s 114 0, .s 114 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0]], [.s 125 2, .s 125 2, .s 125 2, .s 125 2]⟩,
    ⟨-7, -1, 7, 20, [[.s 115 0, .s 115 0, .s 115 0, .s 115 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0]], [.s 129 1, .s 129 1, .s 129 1, .s 129 1]⟩,
    ⟨-7, -1, 8, 17, [[.s 116 0, .s 116 0, .s 116 0, .s 116 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0]], [.s 126 3, .s 126 3, .s 126 3, .s 126 3]⟩,
    ⟨-7, -1, 9, 19, [[.s 117 0, .s 117 0, .s 117 0, .s 117 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0]], [.s 131 1, .s 131 1, .s 131 1, .s 131 1]⟩,
    ⟨-7, -1, 10, 18, [[.s 118 0, .s 118 0, .s 118 0, .s 118 0], [.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0]], [.s 128 2, .s 128 2, .s 128 2, .s 128 2]⟩,
    ⟨-7, -1, 11, 18, [[.s 119 0, .s 119 0, .s 119 0, .s 119 0], [.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0]], [.s 142 1, .s 142 1, .s 142 1, .s 142 1]⟩,
    ⟨-6, -1, 0, 23, [[.s 120 0, .s 120 0, .s 120 0, .s 120 0], [.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.f ⟨27, 14, 0, 0, 1, 0, 0, 0, 0⟩, .s 14 0, .f ⟨27, 14, 0, 1, 2, 0, 0, 0, 0⟩, .s 14 0], [.f ⟨27, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨27, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0]], [.s 121 2, .s 121 2, .s 121 2, .s 121 2]⟩,
    ⟨-6, -1, 1, 21, [[.s 121 0, .s 121 0, .s 121 0, .s 121 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.f ⟨27, 0, 0, 0, 0, 0, 0, 0, 0⟩, .s 0 0, .f ⟨27, 0, 0, 1, 1, 0, 0, 0, 0⟩, .s 0 0], [.f ⟨27, 1, 0, 0, 0, 0, 0, 0, 0⟩, .s 1 0, .f ⟨27, 1, 0, 1, 1, 0, 0, 0, 0⟩, .s 1 0]], [.s 135 1, .s 135 1, .s 135 1, .s 135 1]⟩,
    ⟨-6, -1, 2, 14, [[.s 122 0, .s 122 0, .s 122 0, .s 122 0], [.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.f ⟨12, 48, 0, 0, 0, 0, 0, 0, 0⟩, .f ⟨12, 48, 1, 0, 1, 0, 0, 0, 0⟩, .s 108 0, .s 108 0], [.f ⟨27, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0, .f ⟨27, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 2 0]], [.f ⟨12, 48, 0, 0, 0, 0, 0, 0, 2⟩, .f ⟨12, 48, 1, 0, 1, 0, 0, 0, 2⟩, .s 108 2, .s 108 2]⟩,
    ⟨-6, -1, 3, 20, [[.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 133 0, .s 133 0, .s 133 0, .s 133 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.f ⟨27, 3, 0, 0, 0, 0, 0, 0, 0⟩, .s 3 0, .f ⟨27, 3, 0, 1, 1, 0, 0, 0, 0⟩, .s 3 0], [.f ⟨27, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 4 0, .f ⟨27, 4, 0, 1, 1, 0, 0, 0, 0⟩, .s 4 0]], [.f ⟨27, 3, 0, 0, 0, 0, 0, 0, 0⟩, .s 3 0, .f ⟨27, 3, 0, 1, 1, 0, 0, 0, 0⟩, .s 3 0]⟩,
    ⟨-6, -1, 4, 20, [[.s 123 0, .s 123 0, .s 123 0, .s 123 0], [.s 124 0, .s 124 0, .s 124 0, .s 124 0], [.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 135 0, .s 135 0, .s 135 0, .s 135 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.f ⟨27, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 4 0, .f ⟨27, 4, 0, 1, 1, 0, 0, 0, 0⟩, .s 4 0]], [.s 139 1, .s 139 1, .s 139 1, .s 139 1]⟩,
    ⟨-6, -1, 5, 14, [[.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 134 0, .s 134 0, .s 134 0, .s 134 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.f ⟨27, 2, 0, 0, 0, 0, 0, 0, 0⟩, .s 2 0, .f ⟨27, 2, 0, 1, 1, 0, 0, 0, 0⟩, .s 2 0], [.f ⟨27, 5, 0, 0, 0, 0, 0, 0, 0⟩, .s 5 0, .f ⟨27, 5, 0, 1, 1, 0, 0, 0, 0⟩, .s 5 0], [.f ⟨27, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 6 0, .f ⟨27, 6, 0, 1, 1, 0, 0, 0, 0⟩, .s 6 0]], [.f ⟨27, 2, 0, 0, 0, 0, 0, 0, 1⟩, .s 2 1, .f ⟨27, 2, 0, 1, 1, 0, 0, 0, 1⟩, .s 2 1]⟩,
    ⟨-6, -1, 6, 15, [[.s 125 0, .s 125 0, .s 125 0, .s 125 0], [.s 126 0, .s 126 0, .s 126 0, .s 126 0], [.s 137 0, .s 137 0, .s 137 0, .s 137 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.f ⟨27, 6, 0, 0, 0, 0, 0, 0, 0⟩, .s 6 0, .f ⟨27, 6, 0, 1, 1, 0, 0, 0, 0⟩, .s 6 0]], [.s 137 2, .s 137 2, .s 137 2, .s 137 2]⟩,
    ⟨-6, -1, 7, 19, [[.s 127 0, .s 127 0, .s 127 0, .s 127 0], [.s 136 0, .s 136 0, .s 136 0, .s 136 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.f ⟨27, 4, 0, 0, 0, 0, 0, 0, 0⟩, .s 4 0, .f ⟨27, 4, 0, 1, 1, 0, 0, 0, 0⟩, .s 4 0], [.f ⟨27, 7, 0, 0, 0, 0, 0, 0, 0⟩, .s 7 0, .f ⟨27, 7, 0, 1, 1, 0, 0, 0, 0⟩, .s 7 0]], [.s 141 1, .s 141 1, .s 141 1, .s 141 1]⟩,
    ⟨-6, -1, 8, 16, [[.s 128 0, .s 128 0, .s 128 0, .s 128 0], [.s 138 0, .s 138 0, .s 138 0, .s 138 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.f ⟨27, 8, 0, 0, 0, 0, 0, 0, 0⟩, .s 8 0, .f ⟨27, 8, 0, 1, 1, 0, 0, 0, 0⟩, .s 8 0]], [.s 138 3, .s 138 3, .s 138 3, .s 138 3]⟩,
    ⟨-6, -1, 9, 18, [[.s 129 0, .s 129 0, .s 129 0, .s 129 0], [.s 139 0, .s 139 0, .s 139 0, .s 139 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.f ⟨27, 9, 0, 0, 0, 0, 0, 0, 0⟩, .s 9 0, .f ⟨27, 9, 0, 1, 1, 0, 0, 0, 0⟩, .s 9 0]], [.s 143 1, .s 143 1, .s 143 1, .s 143 1]⟩,
    ⟨-6, -1, 10, 17, [[.s 130 0, .s 130 0, .s 130 0, .s 130 0], [.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 140 0, .s 140 0, .s 140 0, .s 140 0], [.s 143 0, .s 143 0, .s 143 0, .s 143 0], [.f ⟨27, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 10 0, .f ⟨27, 10, 0, 1, 1, 0, 0, 0, 0⟩, .s 10 0]], [.s 140 2, .s 140 2, .s 140 2, .s 140 2]⟩,
    ⟨-6, -1, 11, 17, [[.s 131 0, .s 131 0, .s 131 0, .s 131 0], [.s 141 0, .s 141 0, .s 141 0, .s 141 0], [.s 142 0, .s 142 0, .s 142 0, .s 142 0], [.f ⟨27, 10, 0, 0, 0, 0, 0, 0, 0⟩, .s 10 0, .f ⟨27, 10, 0, 1, 1, 0, 0, 0, 0⟩, .s 10 0], [.f ⟨27, 11, 0, 0, 0, 0, 0, 0, 0⟩, .s 11 0, .f ⟨27, 11, 0, 1, 1, 0, 0, 0, 0⟩, .s 11 0]], [.f ⟨27, 10, 0, 0, 0, 0, 0, 0, 1⟩, .s 10 1, .f ⟨27, 10, 0, 1, 1, 0, 0, 0, 1⟩, .s 10 1]⟩]⟩]

set_option maxRecDepth 100000 in
def certsData : List (List (List (Bool × ℕ × ℕ))) := [
  [[], [(false, 0, 2), (false, 2, 1), (true, 2, 1)], [(false, 0, 2), (false, 2, 1), (true, 2, 1)], [(false, 1, 3), (false, 2, 1), (true, 2, 1)], [(false, 1, 3), (false, 2, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 1, 2), (false, 3, 1), (true, 2, 1)], [(false, 1, 2), (false, 3, 1), (true, 2, 1)], [(false, 0, 3), (false, 3, 1), (true, 2, 1)], [(false, 0, 3), (false, 3, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 3), (true, 0, 1)], [(false, 0, 1), (false, 2, 3), (true, 0, 1)], [(false, 0, 1), (false, 2, 3), (true, 1, 1)], [(false, 0, 1), (false, 2, 3), (true, 0, 1)], [(false, 2, 12), (true, 0, 1)], [(false, 2, 12), (true, 0, 1)], [(false, 3, 12), (true, 0, 1)], [(false, 3, 12), (true, 1, 1)], [(false, 0, 1), (false, 3, 2), (true, 1, 1)], [(false, 0, 1), (false, 3, 2), (true, 1, 1)], [(false, 0, 1), (false, 3, 2), (true, 0, 1)], [(false, 0, 1), (false, 3, 2), (true, 1, 1)], [(false, 3, 12), (true, 0, 1)], [(false, 3, 12), (true, 0, 1)], [(false, 2, 12), (true, 0, 1)], [(false, 2, 12), (true, 1, 1)]],
  [[(false, 0, 2), (false, 2, 1), (true, 2, 5)], [], [(false, 3, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 2), (false, 2, 1), (true, 0, 5)], [(false, 0, 2), (false, 2, 1), (true, 0, 5)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 2), (false, 2, 1), (true, 1, 5)], [(false, 0, 2), (false, 2, 1), (true, 1, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 24), (false, 2, 12), (true, 0, 5)], [(false, 0, 24), (false, 2, 12), (true, 0, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 2), (false, 2, 1), (true, 2, 5)], [(false, 2, 1), (true, 3, 1)], [], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 2), (false, 2, 1), (true, 0, 5)], [(false, 0, 2), (false, 2, 1), (true, 0, 5)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 2), (false, 2, 1), (true, 1, 5)], [(false, 0, 2), (false, 2, 1), (true, 1, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 24), (false, 2, 12), (true, 0, 5)], [(false, 0, 24), (false, 2, 12), (true, 0, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 2, 3), (true, 1, 10)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [], [(false, 3, 1), (true, 2, 1)], [(false, 1, 3), (false, 2, 1), (true, 0, 10)], [(false, 1, 3), (false, 2, 1), (true, 0, 10)], [(false, 1, 1), (false, 2, 1), (true, 0, 2)], [(false, 1, 1), (false, 2, 1), (true, 0, 2)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 3), (true, 2, 10)], [(false, 0, 1), (false, 2, 3), (true, 2, 10)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 18), (false, 2, 6), (true, 0, 5)], [(false, 1, 18), (false, 2, 6), (true, 1, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (true, 0, 5), (true, 1, 12)], [(false, 0, 12), (true, 0, 12), (true, 1, 5)]],
  [[(false, 0, 1), (false, 2, 3), (true, 1, 10)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [(false, 2, 1), (true, 3, 1)], [], [(false, 0, 1), (false, 2, 3), (true, 3, 10)], [(false, 1, 3), (false, 2, 1), (true, 0, 10)], [(false, 0, 1), (false, 2, 1), (true, 3, 2)], [(false, 1, 1), (false, 2, 1), (true, 0, 2)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 3), (true, 2, 10)], [(false, 0, 1), (false, 2, 3), (true, 2, 10)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 18), (false, 2, 6), (true, 0, 5)], [(false, 1, 18), (false, 2, 6), (true, 1, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (true, 0, 5), (true, 1, 12)], [(false, 0, 12), (true, 0, 12), (true, 1, 5)]],
  [[(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 2), (true, 2, 1)], [(false, 0, 1), (false, 2, 2), (true, 2, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [], [(false, 3, 1), (true, 2, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 1, 12), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 0, 12), (true, 1, 1)]],
  [[(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 2), (true, 2, 1)], [(false, 0, 1), (false, 2, 2), (true, 2, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 2, 1), (true, 3, 1)], [], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 1, 12), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 0, 12), (true, 1, 1)]],
  [[(false, 0, 2), (false, 2, 1), (true, 3, 5)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 2), (false, 2, 1), (true, 1, 5)], [(false, 0, 2), (false, 2, 1), (true, 1, 5)], [], [(false, 3, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 2), (false, 2, 1), (true, 0, 5)], [(false, 0, 2), (false, 2, 1), (true, 0, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 24), (false, 2, 12), (true, 0, 5)], [(false, 0, 24), (false, 2, 12), (true, 0, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 2), (false, 2, 1), (true, 3, 5)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 2), (false, 2, 1), (true, 1, 5)], [(false, 0, 2), (false, 2, 1), (true, 1, 5)], [(false, 2, 1), (true, 3, 1)], [], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 1), (false, 2, 1), (true, 0, 1)], [(false, 0, 2), (false, 2, 1), (true, 0, 5)], [(false, 0, 2), (false, 2, 1), (true, 0, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 24), (false, 2, 12), (true, 0, 5)], [(false, 0, 24), (false, 2, 12), (true, 0, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 0, 1), (false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 2, 3), (true, 0, 10)], [(false, 1, 1), (false, 2, 1), (true, 0, 2)], [(false, 1, 1), (false, 2, 1), (true, 0, 2)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 3), (true, 2, 10)], [(false, 0, 1), (false, 2, 3), (true, 2, 10)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [], [(false, 3, 1), (true, 2, 1)], [(false, 1, 3), (false, 2, 1), (true, 0, 10)], [(false, 1, 3), (false, 2, 1), (true, 0, 10)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (true, 0, 5), (true, 1, 12)], [(false, 0, 12), (true, 0, 12), (true, 1, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 18), (false, 2, 6), (true, 0, 5)], [(false, 1, 18), (false, 2, 6), (true, 1, 5)]],
  [[(false, 0, 1), (false, 2, 3), (true, 0, 10)], [(false, 0, 1), (false, 2, 1), (true, 3, 2)], [(false, 1, 1), (false, 2, 1), (true, 0, 2)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 3), (true, 2, 10)], [(false, 0, 1), (false, 2, 3), (true, 2, 10)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [(false, 0, 1), (false, 2, 1), (true, 2, 2)], [(false, 2, 1), (true, 3, 1)], [], [(false, 0, 1), (false, 2, 3), (true, 3, 10)], [(false, 1, 3), (false, 2, 1), (true, 0, 10)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (true, 0, 5), (true, 1, 12)], [(false, 0, 12), (true, 0, 12), (true, 1, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 18), (false, 2, 6), (true, 0, 5)], [(false, 1, 18), (false, 2, 6), (true, 1, 5)]],
  [[(false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 2), (true, 2, 1)], [(false, 0, 1), (false, 2, 2), (true, 2, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [], [(false, 3, 1), (true, 2, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 0, 12), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 1, 12), (true, 1, 1)]],
  [[(false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 2, 1), (true, 2, 1)], [(false, 0, 1), (false, 2, 2), (true, 2, 1)], [(false, 0, 1), (false, 2, 2), (true, 2, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 2, 1), (true, 3, 1)], [], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 2), (false, 2, 1), (true, 0, 1)], [(false, 1, 2), (false, 2, 1), (true, 1, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 0, 12), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 3), (false, 2, 1), (true, 1, 1)], [(false, 0, 3), (false, 2, 1), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 0, 12), (true, 0, 1)], [(false, 1, 12), (true, 0, 1)], [(false, 1, 12), (true, 1, 1)]],
  [[(false, 0, 1), (false, 1, 1), (true, 2, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [], [(false, 2, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 3, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 1), (true, 2, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 2, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 1), (true, 2, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 12), (true, 1, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 1), (true, 2, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 12), (true, 1, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)]],
  [[(false, 0, 1), (true, 2, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 12)], [(false, 0, 1), (true, 1, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)]],
  [[(false, 0, 1), (true, 2, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 12)], [(false, 0, 1), (true, 1, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)]],
  [[(false, 0, 1), (true, 3, 12)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 1), (true, 1, 12)], [(false, 0, 1), (true, 1, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 1, 1), (true, 3, 12)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 1, 1), (true, 1, 12)], [(false, 1, 1), (true, 1, 12)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 12), (false, 1, 5), (true, 0, 12)], [(false, 0, 12), (false, 1, 5), (true, 0, 12)], [(false, 1, 1), (true, 0, 12)], [(false, 1, 1), (true, 0, 12)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 0, 12), (false, 1, 5), (true, 0, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 1), (true, 3, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 2, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 3, 1), (true, 0, 1)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 3, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 1), (true, 3, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 2, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 2, 1), (true, 0, 1)]],
  [[(false, 0, 1), (false, 1, 1), (true, 3, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 2, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 12), (true, 1, 5)]],
  [[(false, 0, 1), (false, 1, 1), (true, 3, 5)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 0, 1), (false, 1, 1), (true, 1, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (false, 1, 1), (true, 0, 5)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 12), (true, 0, 5)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 12), (true, 1, 5)]],
  [[(false, 0, 1), (true, 3, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 12)], [(false, 0, 1), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 2, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 0, 1), (true, 3, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 12)], [(false, 0, 1), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 1), (true, 0, 12)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 1, 1), (true, 2, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 2, 1)], [], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)]],
  [[(false, 0, 1), (true, 2, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 1), (true, 0, 12)], [(false, 0, 1), (true, 0, 12)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 1), (true, 1, 12)], [(false, 0, 1), (true, 1, 12)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 1, 1)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 5), (false, 1, 12), (true, 1, 12)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 0, 5), (false, 1, 12), (true, 0, 12)], [(false, 2, 1), (true, 0, 1)], [(false, 2, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [], [(false, 2, 1), (true, 0, 1)]],
  [[(false, 1, 1), (true, 2, 12)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 12), (false, 1, 5), (true, 0, 12)], [(false, 0, 12), (false, 1, 5), (true, 0, 12)], [(false, 1, 1), (true, 0, 12)], [(false, 1, 1), (true, 0, 12)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 1, 1), (true, 1, 12)], [(false, 1, 1), (true, 1, 12)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 0, 1), (true, 1, 1)], [(false, 0, 1), (true, 0, 1)], [(false, 0, 1), (true, 3, 1)], [(false, 0, 1), (true, 2, 1)], [(false, 0, 12), (false, 1, 5), (true, 1, 12)], [(false, 0, 12), (false, 1, 5), (true, 0, 12)], [(false, 1, 1), (true, 0, 1)], [(false, 1, 1), (true, 0, 1)], [(false, 0, 1), (true, 2, 1)], []]]

def cfg : GalCert.Cfg 12 := ⟨adj, (0, 0, 8), 12, regsData, certsData, 0, 8⟩

set_option maxRecDepth 100000 in
theorem hc : cfg.check = true := by decide +kernel

theorem hV : cfg.vbound 44 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

theorem hrec : ∀ k, (([(1, 7), (-1, 6), (1, 5), (-2, 4), (1, 3), (-1, 2), (1, 1)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide) (by decide +kernel)

theorem hgfw : ∀ n < 44 + 2 * cfg.L, ((GalCert.csOf [1, -1, 1, -2, 1, -1, 1]).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

theorem hsmall : ∀ n < 7, GalCert.conv a [1, -1, 1, -2, 1, -1, 1] n = ([1, 3, 7, 7, 7, 3, 1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P310440

open PowerSeries OMA.S_oeis_a310440 in
theorem OMA.solution : type_of% @OMA.S_oeis_a310440.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    have h := P310440.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 7 - 1 = k + 6 by omega,
      show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 3 = k + 4 by omega,
      show k + 7 - 4 = k + 3 by omega,
      show k + 7 - 5 = k + 2 by omega,
      show k + 7 - 6 = k + 1 by omega,
      P310440.ha (k + 7) (by omega),
      P310440.ha (k + 6) (by omega),
      P310440.ha (k + 5) (by omega),
      P310440.ha (k + 4) (by omega),
      P310440.ha (k + 3) (by omega),
      P310440.ha (k + 2) (by omega),
      P310440.ha (k + 1) (by omega)]
    linarith
  · have hD : ((X - 1)^2*(X^2 + 1)*(X^2 + X + 1) : PowerSeries ℤ) = GalCert.polyOf [1, -1, 1, -2, 1, -1, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (X^6 + 3*X^5 + 7*X^4 + 7*X^3 + 7*X^2 + 3*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 3, 7, 7, 7, 3, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from P310440.hc P310440.hV a P310440.ha _ _ 7 (by decide) (by decide) P310440.hgfw P310440.hsmall
