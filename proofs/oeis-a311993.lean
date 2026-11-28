import OMAStatements.S_oeis_a311993
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A311993.

Method: an explicit distance certificate. Every vertex outside the origin cell lies on one of the
rays through the vertices of the growth polygon or in one of the open cones between them, and is
written as base + k T + j U with a base from a finite list. The certificate gives the distance of
each code as v + L (k + j). A Boolean checker, evaluated by the kernel, verifies that every
neighbour of a coded vertex has a code of value at most one more, that every coded vertex other
than the base vertex has a neighbour of value exactly one less, and that codes are injective. So
the ball of radius n is the image of the codes of value at most n, and the coordination sequence
is a sum of explicit quasi-linear counts, which satisfies both conjectures.
The certificate data was produced by a script written with the help of an AI agent (Claude Code).
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

structure Base (m : ℕ) where
  x : ℤ
  y : ℤ
  i : Fin m
  v : ℕ
  out : List (List Tgt)
  pred : List Tgt

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

def ci (k j : ℕ) : ℕ := (if k = 0 then 0 else 1) + (if j = 0 then 0 else 2)
def kkOf (c : ℕ) : ℕ := c % 2
def jjOf (c : ℕ) : ℕ := c / 2

def okBase (r b : ℕ) : Bool :=
  let R := C.reg r
  let B := C.bas r b
  okZone R B && okCoord R B && decide (R.kind ≤ 2) &&
  (!decide (B.v = 0) || decide (C.dec r b 0 0 = C.x0)) &&
  (List.range (C.adj B.i).length).all (fun e => (List.range (ncases R.kind)).all (fun c =>
    C.okOut R B ((C.adj B.i).getD e edflt) (kkOf c) (jjOf c) ((B.out.getD e []).getD c Tgt.dflt))) &&
  (List.range (ncases R.kind)).all (fun c =>
    (decide (kkOf c = 0 ∧ jjOf c = 0 ∧ B.v = 0)) || C.okPred R B (kkOf c) (jjOf c) (B.pred.getD c Tgt.dflt)) &&
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
        (((C.bas r b).out.getD e []).getD c Tgt.dflt) = true) ∧
    (∀ c < ncases (C.reg r).kind, (kkOf c = 0 ∧ jjOf c = 0 ∧ (C.bas r b).v = 0) ∨
      C.okPred (C.reg r) (C.bas r b) (kkOf c) (jjOf c) ((C.bas r b).pred.getD c Tgt.dflt) = true) ∧
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
  set t := ((C.bas r b).out.getD e []).getD (ci k j) Tgt.dflt
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
  rw [kk_ci, jj_ci] at h
  rcases h with ⟨h1, h2, h3⟩ | h
  · exfalso
    unfold val at hpos
    split_ifs at h1 h2 with hk0 hj0 <;> simp_all
  set t := (C.bas r b).pred.getD (ci k j) Tgt.dflt
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
  have := cert_sum x y ((C.certs.getD r1 []).getD r2 []) (fun s i => C.testOf r1 s r2 i) (by
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

namespace GalCert

def csOfS (l : List ℤ) (s : ℕ) : List (ℤ × ℕ) :=
  (List.range l.length).map fun i => (l.getD i 0, l.length - i + s)

theorem csOfS_pos (l : List ℤ) (s : ℕ) : ∀ p ∈ csOfS l s, 1 ≤ p.2 := by
  intro p hp
  unfold csOfS at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [List.mem_range] at hi
  simp only
  omega

namespace Cfg
variable {m : ℕ} [NeZero m] {C : Cfg m}

theorem gf_from2 (hc : C.check = true) {V : ℕ} (hV : C.vbound V = true) (a : ℕ → ℤ)
    (ha : ∀ n, 1 ≤ n → a n = C.A n) (dl pl : List ℤ) (s M : ℕ) (hM : dl.length + s ≤ M)
    (hP : pl.length ≤ M)
    (hw : ∀ n < V + 2 * C.L, ((csOfS dl s).map fun p => p.1 * (C.A (n + p.2) : ℤ)).sum = 0)
    (hsmall : ∀ n < M, conv a dl n = pl.getD n 0) :
    PowerSeries.mk a * polyOf dl = polyOf pl := by
  apply gf_of_conv
  intro n
  rcases Nat.lt_or_ge n M with h | h
  · exact hsmall n h
  · obtain ⟨k, rfl⟩ : ∃ k, n = (k + s) + dl.length := ⟨n - s - dl.length, by omega⟩
    rw [List.getD_eq_default _ _ (by omega), conv_cs]
    have hz := lin_zero hc hV (csOfS dl s) (csOfS_pos dl s) hw k
    unfold csOfS at hz
    rw [List.map_map] at hz
    refine Eq.trans ?_ hz
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [ha _ (by omega), show k + s + dl.length - i = k + (dl.length - i + s) by omega]

end Cfg
end GalCert


namespace P311993
open OMA.S_oeis_a311993

/-- A packed target code (mixed radix). -/
def tg (n : ℕ) : GalCert.Tgt := ⟨n % 13, n / 13 % 81, n / 1053 % 2, n / 2106 % 2, n / 4212 % 3, n / 12636 % 2, n / 25272 % 2, n / 50544 % 3, n / 151632⟩

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 9) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 1,
      [[tg 6], [tg 150], [tg 13], [tg 3]],
      [tg 151645]⟩,
    ⟨0, 0, 1, 0,
      [[tg 19], [tg 0], [tg 39], [tg 16]],
      [tg 0]⟩,
    ⟨0, 0, 2, 7,
      [[tg 32], [tg 52], [tg 10], [tg 29]],
      [tg 151684]⟩,
    ⟨0, 0, 3, 1,
      [[tg 45], [tg 13], [tg 65], [tg 42]],
      [tg 303277]⟩,
    ⟨0, 0, 4, 6,
      [[tg 58], [tg 26], [tg 78], [tg 55]],
      [tg 303342]⟩,
    ⟨0, 0, 5, 2,
      [[tg 71], [tg 97], [tg 39], [tg 91], [tg 68]],
      [tg 303303]⟩,
    ⟨0, 0, 6, 5,
      [[tg 84], [tg 110], [tg 52], [tg 104], [tg 81]],
      [tg 455006]⟩,
    ⟨0, 0, 7, 3,
      [[tg 97], [tg 65], [tg 104], [tg 68], [tg 94]],
      [tg 454961]⟩,
    ⟨0, 0, 8, 4,
      [[tg 110], [tg 78], [tg 91], [tg 81], [tg 107]],
      [tg 303355]⟩]⟩,
  ⟨1, -1, -1, 0, 0, [(1, -1, 0), (-1, 1, 0), (-1, -1, 2)], -1, -1, 2, 2, 0, 0, 0, 0,
   [⟨-1, -1, 0, 10,
      [[tg 948, tg 64128], [tg 4362, tg 9627], [tg 14, tg 5279], [tg 124, tg 5389]],
      [tg 151646, tg 156911]⟩,
    ⟨-1, -1, 1, 9,
      [[tg 961, tg 64141], [tg 1, tg 5266], [tg 40, tg 5305], [tg 137, tg 5402]],
      [tg 151672, tg 156937]⟩,
    ⟨-1, -1, 2, 3,
      [[tg 974, tg 64154], [tg 53, tg 5318], [tg 6, tg 13584], [tg 150, tg 5415]],
      [tg 151638, tg 165216]⟩,
    ⟨-1, -1, 3, 8,
      [[tg 987, tg 64167], [tg 14, tg 5279], [tg 66, tg 5331], [tg 163, tg 5428]],
      [tg 303330, tg 308595]⟩,
    ⟨-1, -1, 4, 4,
      [[tg 1000, tg 64180], [tg 27, tg 5292], [tg 79, tg 5344], [tg 176, tg 5441]],
      [tg 151659, tg 156924]⟩,
    ⟨-1, -1, 5, 7,
      [[tg 1013, tg 64193], [tg 1039, tg 64219], [tg 40, tg 5305], [tg 92, tg 5357], [tg 189, tg 5454]],
      [tg 151724, tg 156989]⟩,
    ⟨-1, -1, 6, 5,
      [[tg 1026, tg 64206], [tg 1052, tg 64232], [tg 53, tg 5318], [tg 105, tg 5370], [tg 202, tg 5467]],
      [tg 303317, tg 308582]⟩,
    ⟨-1, -1, 7, 6,
      [[tg 1039, tg 64219], [tg 66, tg 5331], [tg 105, tg 5370], [tg 189, tg 5454], [tg 215, tg 5480]],
      [tg 303369, tg 308634]⟩,
    ⟨-1, -1, 8, 5,
      [[tg 1052, tg 64232], [tg 79, tg 5344], [tg 92, tg 5357], [tg 202, tg 5467], [tg 228, tg 5493]],
      [tg 151834, tg 157099]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 2)], 1, -1, 2, 2, 0, 0, 0, 0,
   [⟨1, -1, 0, 10,
      [[tg 124, tg 63304], [tg 50694, tg 113874], [tg 15, tg 5280], [tg 8, tg 5273]],
      [tg 151647, tg 156912]⟩,
    ⟨1, -1, 1, 9,
      [[tg 137, tg 63317], [tg 2, tg 5267], [tg 41, tg 5306], [tg 21, tg 5286]],
      [tg 151673, tg 156938]⟩,
    ⟨1, -1, 2, 3,
      [[tg 150, tg 63330], [tg 54, tg 5319], [tg 3, tg 1061], [tg 34, tg 5299]],
      [tg 455046, tg 518226]⟩,
    ⟨1, -1, 3, 8,
      [[tg 163, tg 63343], [tg 15, tg 5280], [tg 67, tg 5332], [tg 47, tg 5312]],
      [tg 303331, tg 308596]⟩,
    ⟨1, -1, 4, 4,
      [[tg 176, tg 63356], [tg 28, tg 5293], [tg 80, tg 5345], [tg 60, tg 5325]],
      [tg 455072, tg 518252]⟩,
    ⟨1, -1, 5, 7,
      [[tg 189, tg 63369], [tg 215, tg 63395], [tg 41, tg 5306], [tg 93, tg 5358], [tg 73, tg 5338]],
      [tg 455111, tg 518291]⟩,
    ⟨1, -1, 6, 5,
      [[tg 202, tg 63382], [tg 228, tg 63408], [tg 54, tg 5319], [tg 106, tg 5371], [tg 86, tg 5351]],
      [tg 606730, tg 669910]⟩,
    ⟨1, -1, 7, 7,
      [[tg 215, tg 63395], [tg 67, tg 5332], [tg 106, tg 5371], [tg 73, tg 5338], [tg 99, tg 5364]],
      [tg 606743, tg 669923]⟩,
    ⟨1, -1, 8, 6,
      [[tg 228, tg 63408], [tg 80, tg 5345], [tg 93, tg 5358], [tg 86, tg 5351], [tg 112, tg 5377]],
      [tg 606756, tg 669936]⟩]⟩,
  ⟨1, 9, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 1)], 1, 0, 1, 9, 0, 0, 0, 0,
   [⟨1, 0, 0, 2,
      [[tg 0, tg 1992], [tg 28, tg 13606], [tg 16, tg 5281], [tg 120, tg 5385]],
      [tg 454896, tg 456888]⟩,
    ⟨1, 0, 1, 1,
      [[tg 13, tg 2005], [tg 3, tg 5268], [tg 42, tg 5307], [tg 133, tg 5398]],
      [tg 454909, tg 456901]⟩,
    ⟨1, 0, 2, 7,
      [[tg 26, tg 2018], [tg 55, tg 5320], [tg 4, tg 1998], [tg 146, tg 5411]],
      [tg 151687, tg 456914]⟩,
    ⟨1, 0, 3, 2,
      [[tg 39, tg 2031], [tg 16, tg 5281], [tg 68, tg 5333], [tg 159, tg 5424]],
      [tg 454935, tg 456927]⟩,
    ⟨1, 0, 4, 6,
      [[tg 52, tg 2044], [tg 29, tg 5294], [tg 81, tg 5346], [tg 172, tg 5437]],
      [tg 303345, tg 456940]⟩,
    ⟨1, 0, 5, 3,
      [[tg 65, tg 2057], [tg 91, tg 2083], [tg 42, tg 5307], [tg 94, tg 5359], [tg 185, tg 5450]],
      [tg 606593, tg 608585]⟩,
    ⟨1, 0, 6, 5,
      [[tg 78, tg 2070], [tg 104, tg 2096], [tg 55, tg 5320], [tg 107, tg 5372], [tg 198, tg 5463]],
      [tg 455000, tg 608598]⟩,
    ⟨1, 0, 7, 4,
      [[tg 91, tg 2083], [tg 68, tg 5333], [tg 107, tg 5372], [tg 185, tg 5450], [tg 211, tg 5476]],
      [tg 606619, tg 608611]⟩,
    ⟨1, 0, 8, 5,
      [[tg 104, tg 2096], [tg 81, tg 5346], [tg 94, tg 5359], [tg 198, tg 5463], [tg 224, tg 5489]],
      [tg 606632, tg 608624]⟩,
    ⟨2, 0, 0, 3,
      [[tg 3, tg 5268], [tg 34, tg 63214], [tg 133, tg 5398], [tg 237, tg 5502]],
      [tg 454899, tg 460164]⟩,
    ⟨2, 0, 1, 2,
      [[tg 16, tg 5281], [tg 120, tg 5385], [tg 159, tg 5424], [tg 250, tg 5515]],
      [tg 454912, tg 460177]⟩,
    ⟨2, 0, 2, 8,
      [[tg 29, tg 5294], [tg 172, tg 5437], [tg 9, tg 5274], [tg 263, tg 5528]],
      [tg 454925, tg 460190]⟩,
    ⟨2, 0, 3, 3,
      [[tg 42, tg 5307], [tg 133, tg 5398], [tg 185, tg 5450], [tg 276, tg 5541]],
      [tg 454938, tg 460203]⟩,
    ⟨2, 0, 4, 7,
      [[tg 55, tg 5320], [tg 146, tg 5411], [tg 198, tg 5463], [tg 289, tg 5554]],
      [tg 454951, tg 460216]⟩,
    ⟨2, 0, 5, 4,
      [[tg 68, tg 5333], [tg 94, tg 5359], [tg 159, tg 5424], [tg 211, tg 5476], [tg 302, tg 5567]],
      [tg 606596, tg 611861]⟩,
    ⟨2, 0, 6, 6,
      [[tg 81, tg 5346], [tg 107, tg 5372], [tg 172, tg 5437], [tg 224, tg 5489], [tg 315, tg 5580]],
      [tg 606609, tg 611874]⟩,
    ⟨2, 0, 7, 5,
      [[tg 94, tg 5359], [tg 185, tg 5450], [tg 224, tg 5489], [tg 302, tg 5567], [tg 328, tg 5593]],
      [tg 606622, tg 611887]⟩,
    ⟨2, 0, 8, 6,
      [[tg 107, tg 5372], [tg 198, tg 5463], [tg 211, tg 5476], [tg 315, tg 5580], [tg 341, tg 5606]],
      [tg 606635, tg 611900]⟩,
    ⟨3, 0, 0, 4,
      [[tg 120, tg 5385], [tg 151, tg 63331], [tg 250, tg 5515], [tg 354, tg 5619]],
      [tg 455016, tg 460281]⟩,
    ⟨3, 0, 1, 3,
      [[tg 133, tg 5398], [tg 237, tg 5502], [tg 276, tg 5541], [tg 367, tg 5632]],
      [tg 455029, tg 460294]⟩,
    ⟨3, 0, 2, 9,
      [[tg 146, tg 5411], [tg 289, tg 5554], [tg 126, tg 5391], [tg 380, tg 5645]],
      [tg 455042, tg 460307]⟩,
    ⟨3, 0, 3, 4,
      [[tg 159, tg 5424], [tg 250, tg 5515], [tg 302, tg 5567], [tg 393, tg 5658]],
      [tg 455055, tg 460320]⟩,
    ⟨3, 0, 4, 8,
      [[tg 172, tg 5437], [tg 263, tg 5528], [tg 315, tg 5580], [tg 406, tg 5671]],
      [tg 455068, tg 460333]⟩,
    ⟨3, 0, 5, 5,
      [[tg 185, tg 5450], [tg 211, tg 5476], [tg 276, tg 5541], [tg 328, tg 5593], [tg 419, tg 5684]],
      [tg 606713, tg 611978]⟩,
    ⟨3, 0, 6, 7,
      [[tg 198, tg 5463], [tg 224, tg 5489], [tg 289, tg 5554], [tg 341, tg 5606], [tg 432, tg 5697]],
      [tg 606726, tg 611991]⟩,
    ⟨3, 0, 7, 6,
      [[tg 211, tg 5476], [tg 302, tg 5567], [tg 341, tg 5606], [tg 419, tg 5684], [tg 445, tg 5710]],
      [tg 606739, tg 612004]⟩,
    ⟨3, 0, 8, 7,
      [[tg 224, tg 5489], [tg 315, tg 5580], [tg 328, tg 5593], [tg 432, tg 5697], [tg 458, tg 5723]],
      [tg 606752, tg 612017]⟩,
    ⟨4, 0, 0, 5,
      [[tg 237, tg 5502], [tg 268, tg 63448], [tg 367, tg 5632], [tg 471, tg 5736]],
      [tg 455133, tg 460398]⟩,
    ⟨4, 0, 1, 4,
      [[tg 250, tg 5515], [tg 354, tg 5619], [tg 393, tg 5658], [tg 484, tg 5749]],
      [tg 455146, tg 460411]⟩,
    ⟨4, 0, 2, 10,
      [[tg 263, tg 5528], [tg 406, tg 5671], [tg 243, tg 5508], [tg 497, tg 5762]],
      [tg 455159, tg 460424]⟩,
    ⟨4, 0, 3, 5,
      [[tg 276, tg 5541], [tg 367, tg 5632], [tg 419, tg 5684], [tg 510, tg 5775]],
      [tg 455172, tg 460437]⟩,
    ⟨4, 0, 4, 9,
      [[tg 289, tg 5554], [tg 380, tg 5645], [tg 432, tg 5697], [tg 523, tg 5788]],
      [tg 455185, tg 460450]⟩,
    ⟨4, 0, 5, 6,
      [[tg 302, tg 5567], [tg 328, tg 5593], [tg 393, tg 5658], [tg 445, tg 5710], [tg 536, tg 5801]],
      [tg 606830, tg 612095]⟩,
    ⟨4, 0, 6, 8,
      [[tg 315, tg 5580], [tg 341, tg 5606], [tg 406, tg 5671], [tg 458, tg 5723], [tg 549, tg 5814]],
      [tg 606843, tg 612108]⟩,
    ⟨4, 0, 7, 7,
      [[tg 328, tg 5593], [tg 419, tg 5684], [tg 458, tg 5723], [tg 536, tg 5801], [tg 562, tg 5827]],
      [tg 606856, tg 612121]⟩,
    ⟨4, 0, 8, 8,
      [[tg 341, tg 5606], [tg 432, tg 5697], [tg 445, tg 5710], [tg 549, tg 5814], [tg 575, tg 5840]],
      [tg 606869, tg 612134]⟩,
    ⟨5, 0, 0, 6,
      [[tg 354, tg 5619], [tg 385, tg 63565], [tg 484, tg 5749], [tg 588, tg 5853]],
      [tg 455250, tg 460515]⟩,
    ⟨5, 0, 1, 5,
      [[tg 367, tg 5632], [tg 471, tg 5736], [tg 510, tg 5775], [tg 601, tg 5866]],
      [tg 455263, tg 460528]⟩,
    ⟨5, 0, 2, 11,
      [[tg 380, tg 5645], [tg 523, tg 5788], [tg 360, tg 5625], [tg 614, tg 5879]],
      [tg 455276, tg 460541]⟩,
    ⟨5, 0, 3, 6,
      [[tg 393, tg 5658], [tg 484, tg 5749], [tg 536, tg 5801], [tg 627, tg 5892]],
      [tg 455289, tg 460554]⟩,
    ⟨5, 0, 4, 10,
      [[tg 406, tg 5671], [tg 497, tg 5762], [tg 549, tg 5814], [tg 640, tg 5905]],
      [tg 455302, tg 460567]⟩,
    ⟨5, 0, 5, 7,
      [[tg 419, tg 5684], [tg 445, tg 5710], [tg 510, tg 5775], [tg 562, tg 5827], [tg 653, tg 5918]],
      [tg 606947, tg 612212]⟩,
    ⟨5, 0, 6, 9,
      [[tg 432, tg 5697], [tg 458, tg 5723], [tg 523, tg 5788], [tg 575, tg 5840], [tg 666, tg 5931]],
      [tg 606960, tg 612225]⟩,
    ⟨5, 0, 7, 8,
      [[tg 445, tg 5710], [tg 536, tg 5801], [tg 575, tg 5840], [tg 653, tg 5918], [tg 679, tg 5944]],
      [tg 606973, tg 612238]⟩,
    ⟨5, 0, 8, 9,
      [[tg 458, tg 5723], [tg 549, tg 5814], [tg 562, tg 5827], [tg 666, tg 5931], [tg 692, tg 5957]],
      [tg 606986, tg 612251]⟩,
    ⟨6, 0, 0, 7,
      [[tg 471, tg 5736], [tg 502, tg 63682], [tg 601, tg 5866], [tg 705, tg 5970]],
      [tg 455367, tg 460632]⟩,
    ⟨6, 0, 1, 6,
      [[tg 484, tg 5749], [tg 588, tg 5853], [tg 627, tg 5892], [tg 718, tg 5983]],
      [tg 455380, tg 460645]⟩,
    ⟨6, 0, 2, 12,
      [[tg 497, tg 5762], [tg 640, tg 5905], [tg 477, tg 5742], [tg 731, tg 5996]],
      [tg 455393, tg 460658]⟩,
    ⟨6, 0, 3, 7,
      [[tg 510, tg 5775], [tg 601, tg 5866], [tg 653, tg 5918], [tg 744, tg 6009]],
      [tg 455406, tg 460671]⟩,
    ⟨6, 0, 4, 11,
      [[tg 523, tg 5788], [tg 614, tg 5879], [tg 666, tg 5931], [tg 757, tg 6022]],
      [tg 455419, tg 460684]⟩,
    ⟨6, 0, 5, 8,
      [[tg 536, tg 5801], [tg 562, tg 5827], [tg 627, tg 5892], [tg 679, tg 5944], [tg 770, tg 6035]],
      [tg 607064, tg 612329]⟩,
    ⟨6, 0, 6, 10,
      [[tg 549, tg 5814], [tg 575, tg 5840], [tg 640, tg 5905], [tg 692, tg 5957], [tg 783, tg 6048]],
      [tg 607077, tg 612342]⟩,
    ⟨6, 0, 7, 9,
      [[tg 562, tg 5827], [tg 653, tg 5918], [tg 692, tg 5957], [tg 770, tg 6035], [tg 796, tg 6061]],
      [tg 607090, tg 612355]⟩,
    ⟨6, 0, 8, 10,
      [[tg 575, tg 5840], [tg 666, tg 5931], [tg 679, tg 5944], [tg 783, tg 6048], [tg 809, tg 6074]],
      [tg 607103, tg 612368]⟩,
    ⟨7, 0, 0, 8,
      [[tg 588, tg 5853], [tg 619, tg 63799], [tg 718, tg 5983], [tg 822, tg 6087]],
      [tg 455484, tg 460749]⟩,
    ⟨7, 0, 1, 7,
      [[tg 601, tg 5866], [tg 705, tg 5970], [tg 744, tg 6009], [tg 835, tg 6100]],
      [tg 455497, tg 460762]⟩,
    ⟨7, 0, 2, 13,
      [[tg 614, tg 5879], [tg 757, tg 6022], [tg 594, tg 5859], [tg 848, tg 6113]],
      [tg 455510, tg 460775]⟩,
    ⟨7, 0, 3, 8,
      [[tg 627, tg 5892], [tg 718, tg 5983], [tg 770, tg 6035], [tg 861, tg 6126]],
      [tg 455523, tg 460788]⟩,
    ⟨7, 0, 4, 12,
      [[tg 640, tg 5905], [tg 731, tg 5996], [tg 783, tg 6048], [tg 874, tg 6139]],
      [tg 455536, tg 460801]⟩,
    ⟨7, 0, 5, 9,
      [[tg 653, tg 5918], [tg 679, tg 5944], [tg 744, tg 6009], [tg 796, tg 6061], [tg 887, tg 6152]],
      [tg 607181, tg 612446]⟩,
    ⟨7, 0, 6, 11,
      [[tg 666, tg 5931], [tg 692, tg 5957], [tg 757, tg 6022], [tg 809, tg 6074], [tg 900, tg 6165]],
      [tg 607194, tg 612459]⟩,
    ⟨7, 0, 7, 10,
      [[tg 679, tg 5944], [tg 770, tg 6035], [tg 809, tg 6074], [tg 887, tg 6152], [tg 913, tg 6178]],
      [tg 607207, tg 612472]⟩,
    ⟨7, 0, 8, 11,
      [[tg 692, tg 5957], [tg 783, tg 6048], [tg 796, tg 6061], [tg 900, tg 6165], [tg 926, tg 6191]],
      [tg 607220, tg 612485]⟩,
    ⟨8, 0, 0, 9,
      [[tg 705, tg 5970], [tg 736, tg 63916], [tg 835, tg 6100], [tg 939, tg 6204]],
      [tg 455601, tg 460866]⟩,
    ⟨8, 0, 1, 8,
      [[tg 718, tg 5983], [tg 822, tg 6087], [tg 861, tg 6126], [tg 952, tg 6217]],
      [tg 455614, tg 460879]⟩,
    ⟨8, 0, 2, 14,
      [[tg 731, tg 5996], [tg 874, tg 6139], [tg 711, tg 5976], [tg 965, tg 6230]],
      [tg 455627, tg 460892]⟩,
    ⟨8, 0, 3, 9,
      [[tg 744, tg 6009], [tg 835, tg 6100], [tg 887, tg 6152], [tg 978, tg 6243]],
      [tg 455640, tg 460905]⟩,
    ⟨8, 0, 4, 13,
      [[tg 757, tg 6022], [tg 848, tg 6113], [tg 900, tg 6165], [tg 991, tg 6256]],
      [tg 455653, tg 460918]⟩,
    ⟨8, 0, 5, 10,
      [[tg 770, tg 6035], [tg 796, tg 6061], [tg 861, tg 6126], [tg 913, tg 6178], [tg 1004, tg 6269]],
      [tg 607298, tg 612563]⟩,
    ⟨8, 0, 6, 12,
      [[tg 783, tg 6048], [tg 809, tg 6074], [tg 874, tg 6139], [tg 926, tg 6191], [tg 1017, tg 6282]],
      [tg 607311, tg 612576]⟩,
    ⟨8, 0, 7, 11,
      [[tg 796, tg 6061], [tg 887, tg 6152], [tg 926, tg 6191], [tg 1004, tg 6269], [tg 1030, tg 6295]],
      [tg 607324, tg 612589]⟩,
    ⟨8, 0, 8, 12,
      [[tg 809, tg 6074], [tg 900, tg 6165], [tg 913, tg 6178], [tg 1017, tg 6282], [tg 1043, tg 6308]],
      [tg 607337, tg 612602]⟩,
    ⟨9, 0, 0, 10,
      [[tg 822, tg 6087], [tg 853, tg 64033], [tg 952, tg 6217], [tg 4215, tg 9480]],
      [tg 455718, tg 460983]⟩,
    ⟨9, 0, 1, 9,
      [[tg 835, tg 6100], [tg 939, tg 6204], [tg 978, tg 6243], [tg 4228, tg 9493]],
      [tg 455731, tg 460996]⟩,
    ⟨9, 0, 2, 15,
      [[tg 848, tg 6113], [tg 991, tg 6256], [tg 828, tg 6093], [tg 4241, tg 9506]],
      [tg 455744, tg 461009]⟩,
    ⟨9, 0, 3, 10,
      [[tg 861, tg 6126], [tg 952, tg 6217], [tg 1004, tg 6269], [tg 4254, tg 9519]],
      [tg 455757, tg 461022]⟩,
    ⟨9, 0, 4, 14,
      [[tg 874, tg 6139], [tg 965, tg 6230], [tg 1017, tg 6282], [tg 4267, tg 9532]],
      [tg 455770, tg 461035]⟩,
    ⟨9, 0, 5, 11,
      [[tg 887, tg 6152], [tg 913, tg 6178], [tg 978, tg 6243], [tg 1030, tg 6295], [tg 4280, tg 9545]],
      [tg 607415, tg 612680]⟩,
    ⟨9, 0, 6, 13,
      [[tg 900, tg 6165], [tg 926, tg 6191], [tg 991, tg 6256], [tg 1043, tg 6308], [tg 4293, tg 9558]],
      [tg 607428, tg 612693]⟩,
    ⟨9, 0, 7, 12,
      [[tg 913, tg 6178], [tg 1004, tg 6269], [tg 1043, tg 6308], [tg 4280, tg 9545], [tg 4306, tg 9571]],
      [tg 607441, tg 612706]⟩,
    ⟨9, 0, 8, 13,
      [[tg 926, tg 6191], [tg 1017, tg 6282], [tg 1030, tg 6295], [tg 4293, tg 9558], [tg 4319, tg 9584]],
      [tg 607454, tg 612719]⟩]⟩,
  ⟨1, 1, 1, 0, 0, [(-1, 1, 0), (1, -1, 0), (1, 1, 2)], 1, 1, 2, 2, 0, 0, 0, 0,
   [⟨1, 1, 0, 8,
      [[tg 10, tg 5275], [tg 29, tg 12671], [tg 17, tg 5282], [tg 9, tg 63189]],
      [tg 303293, tg 315935]⟩,
    ⟨1, 1, 1, 9,
      [[tg 23, tg 5288], [tg 4, tg 5269], [tg 43, tg 5308], [tg 22, tg 63202]],
      [tg 303268, tg 308533]⟩,
    ⟨1, 1, 2, 16,
      [[tg 36, tg 5301], [tg 56, tg 5321], [tg 4222, tg 9487], [tg 35, tg 63215]],
      [tg 151688, tg 156953]⟩,
    ⟨1, 1, 3, 10,
      [[tg 49, tg 5314], [tg 17, tg 5282], [tg 69, tg 5334], [tg 48, tg 63228]],
      [tg 303281, tg 308546]⟩,
    ⟨1, 1, 4, 15,
      [[tg 62, tg 5327], [tg 30, tg 5295], [tg 82, tg 5347], [tg 61, tg 63241]],
      [tg 303346, tg 308611]⟩,
    ⟨1, 1, 5, 11,
      [[tg 75, tg 5340], [tg 101, tg 5366], [tg 43, tg 5308], [tg 95, tg 5360], [tg 74, tg 63254]],
      [tg 303307, tg 308572]⟩,
    ⟨1, 1, 6, 14,
      [[tg 88, tg 5353], [tg 114, tg 5379], [tg 56, tg 5321], [tg 108, tg 5373], [tg 87, tg 63267]],
      [tg 455010, tg 460275]⟩,
    ⟨1, 1, 7, 12,
      [[tg 101, tg 5366], [tg 69, tg 5334], [tg 108, tg 5373], [tg 74, tg 63254], [tg 100, tg 63280]],
      [tg 454965, tg 460230]⟩,
    ⟨1, 1, 8, 13,
      [[tg 114, tg 5379], [tg 82, tg 5347], [tg 95, tg 5360], [tg 87, tg 63267], [tg 113, tg 63293]],
      [tg 303359, tg 308624]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 2)], -1, 1, 2, 2, 0, 0, 0, 0,
   [⟨-1, 1, 0, 8,
      [[tg 947, tg 6212], [tg 32, tg 2026], [tg 18, tg 5283], [tg 10, tg 63190]],
      [tg 303296, tg 305290]⟩,
    ⟨-1, 1, 1, 9,
      [[tg 960, tg 6225], [tg 5, tg 5270], [tg 44, tg 5309], [tg 23, tg 63203]],
      [tg 303269, tg 308534]⟩,
    ⟨-1, 1, 2, 16,
      [[tg 973, tg 6238], [tg 57, tg 5322], [tg 50554, tg 113734], [tg 36, tg 63216]],
      [tg 151689, tg 156954]⟩,
    ⟨-1, 1, 3, 10,
      [[tg 986, tg 6251], [tg 18, tg 5283], [tg 70, tg 5335], [tg 49, tg 63229]],
      [tg 303282, tg 308547]⟩,
    ⟨-1, 1, 4, 15,
      [[tg 999, tg 6264], [tg 31, tg 5296], [tg 83, tg 5348], [tg 62, tg 63242]],
      [tg 303347, tg 308612]⟩,
    ⟨-1, 1, 5, 11,
      [[tg 1012, tg 6277], [tg 1038, tg 6303], [tg 44, tg 5309], [tg 96, tg 5361], [tg 75, tg 63255]],
      [tg 303308, tg 308573]⟩,
    ⟨-1, 1, 6, 14,
      [[tg 1025, tg 6290], [tg 1051, tg 6316], [tg 57, tg 5322], [tg 109, tg 5374], [tg 88, tg 63268]],
      [tg 455947, tg 461212]⟩,
    ⟨-1, 1, 7, 12,
      [[tg 1038, tg 6303], [tg 70, tg 5335], [tg 109, tg 5374], [tg 75, tg 63255], [tg 101, tg 63281]],
      [tg 454966, tg 460231]⟩,
    ⟨-1, 1, 8, 13,
      [[tg 1051, tg 6316], [tg 83, tg 5348], [tg 96, tg 5361], [tg 88, tg 63268], [tg 114, tg 63294]],
      [tg 303360, tg 308625]⟩]⟩,
  ⟨1, -9, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 1)], -1, 0, 1, 9, 0, 0, 0, 0,
   [⟨-1, 0, 0, 2,
      [[tg 123, tg 5388], [tg 27, tg 1091], [tg 19, tg 5284], [tg 0, tg 1995]],
      [tg 151651, tg 156916]⟩,
    ⟨-1, 0, 1, 1,
      [[tg 136, tg 5401], [tg 6, tg 5271], [tg 45, tg 5310], [tg 13, tg 2008]],
      [tg 13, tg 2008]⟩,
    ⟨-1, 0, 2, 7,
      [[tg 149, tg 5414], [tg 58, tg 5323], [tg 5, tg 12647], [tg 26, tg 2021]],
      [tg 151690, tg 156955]⟩,
    ⟨-1, 0, 3, 2,
      [[tg 162, tg 5427], [tg 19, tg 5284], [tg 71, tg 5336], [tg 39, tg 2034]],
      [tg 303283, tg 308548]⟩,
    ⟨-1, 0, 4, 6,
      [[tg 175, tg 5440], [tg 32, tg 5297], [tg 84, tg 5349], [tg 52, tg 2047]],
      [tg 303348, tg 308613]⟩,
    ⟨-1, 0, 5, 3,
      [[tg 188, tg 5453], [tg 214, tg 5479], [tg 45, tg 5310], [tg 97, tg 5362], [tg 65, tg 2060]],
      [tg 303309, tg 308574]⟩,
    ⟨-1, 0, 6, 5,
      [[tg 201, tg 5466], [tg 227, tg 5492], [tg 58, tg 5323], [tg 110, tg 5375], [tg 78, tg 2073]],
      [tg 151742, tg 157007]⟩,
    ⟨-1, 0, 7, 3,
      [[tg 214, tg 5479], [tg 71, tg 5336], [tg 110, tg 5375], [tg 65, tg 2060], [tg 91, tg 2086]],
      [tg 151697, tg 153692]⟩,
    ⟨-1, 0, 8, 4,
      [[tg 227, tg 5492], [tg 84, tg 5349], [tg 97, tg 5362], [tg 78, tg 2073], [tg 104, tg 2099]],
      [tg 303361, tg 308626]⟩,
    ⟨-2, 0, 0, 3,
      [[tg 240, tg 5505], [tg 974, tg 6239], [tg 136, tg 5401], [tg 6, tg 5271]],
      [tg 151768, tg 157033]⟩,
    ⟨-2, 0, 1, 2,
      [[tg 253, tg 5518], [tg 123, tg 5388], [tg 162, tg 5427], [tg 19, tg 5284]],
      [tg 19, tg 5284]⟩,
    ⟨-2, 0, 2, 8,
      [[tg 266, tg 5531], [tg 175, tg 5440], [tg 947, tg 64127], [tg 32, tg 5297]],
      [tg 151807, tg 157072]⟩,
    ⟨-2, 0, 3, 3,
      [[tg 279, tg 5544], [tg 136, tg 5401], [tg 188, tg 5453], [tg 45, tg 5310]],
      [tg 303400, tg 308665]⟩,
    ⟨-2, 0, 4, 7,
      [[tg 292, tg 5557], [tg 149, tg 5414], [tg 201, tg 5466], [tg 58, tg 5323]],
      [tg 303465, tg 308730]⟩,
    ⟨-2, 0, 5, 4,
      [[tg 305, tg 5570], [tg 331, tg 5596], [tg 162, tg 5427], [tg 214, tg 5479], [tg 71, tg 5336]],
      [tg 303426, tg 308691]⟩,
    ⟨-2, 0, 6, 6,
      [[tg 318, tg 5583], [tg 344, tg 5609], [tg 175, tg 5440], [tg 227, tg 5492], [tg 84, tg 5349]],
      [tg 151859, tg 157124]⟩,
    ⟨-2, 0, 7, 4,
      [[tg 331, tg 5596], [tg 188, tg 5453], [tg 227, tg 5492], [tg 71, tg 5336], [tg 97, tg 5362]],
      [tg 151703, tg 156968]⟩,
    ⟨-2, 0, 8, 5,
      [[tg 344, tg 5609], [tg 201, tg 5466], [tg 214, tg 5479], [tg 84, tg 5349], [tg 110, tg 5375]],
      [tg 303478, tg 308743]⟩,
    ⟨-3, 0, 0, 4,
      [[tg 357, tg 5622], [tg 857, tg 6122], [tg 253, tg 5518], [tg 123, tg 5388]],
      [tg 151885, tg 157150]⟩,
    ⟨-3, 0, 1, 3,
      [[tg 370, tg 5635], [tg 240, tg 5505], [tg 279, tg 5544], [tg 136, tg 5401]],
      [tg 136, tg 5401]⟩,
    ⟨-3, 0, 2, 9,
      [[tg 383, tg 5648], [tg 292, tg 5557], [tg 830, tg 64010], [tg 149, tg 5414]],
      [tg 151924, tg 157189]⟩,
    ⟨-3, 0, 3, 4,
      [[tg 396, tg 5661], [tg 253, tg 5518], [tg 305, tg 5570], [tg 162, tg 5427]],
      [tg 303517, tg 308782]⟩,
    ⟨-3, 0, 4, 8,
      [[tg 409, tg 5674], [tg 266, tg 5531], [tg 318, tg 5583], [tg 175, tg 5440]],
      [tg 303582, tg 308847]⟩,
    ⟨-3, 0, 5, 5,
      [[tg 422, tg 5687], [tg 448, tg 5713], [tg 279, tg 5544], [tg 331, tg 5596], [tg 188, tg 5453]],
      [tg 303543, tg 308808]⟩,
    ⟨-3, 0, 6, 7,
      [[tg 435, tg 5700], [tg 461, tg 5726], [tg 292, tg 5557], [tg 344, tg 5609], [tg 201, tg 5466]],
      [tg 151976, tg 157241]⟩,
    ⟨-3, 0, 7, 5,
      [[tg 448, tg 5713], [tg 305, tg 5570], [tg 344, tg 5609], [tg 188, tg 5453], [tg 214, tg 5479]],
      [tg 151820, tg 157085]⟩,
    ⟨-3, 0, 8, 6,
      [[tg 461, tg 5726], [tg 318, tg 5583], [tg 331, tg 5596], [tg 201, tg 5466], [tg 227, tg 5492]],
      [tg 303595, tg 308860]⟩,
    ⟨-4, 0, 0, 5,
      [[tg 474, tg 5739], [tg 740, tg 6005], [tg 370, tg 5635], [tg 240, tg 5505]],
      [tg 152002, tg 157267]⟩,
    ⟨-4, 0, 1, 4,
      [[tg 487, tg 5752], [tg 357, tg 5622], [tg 396, tg 5661], [tg 253, tg 5518]],
      [tg 253, tg 5518]⟩,
    ⟨-4, 0, 2, 10,
      [[tg 500, tg 5765], [tg 409, tg 5674], [tg 713, tg 63893], [tg 266, tg 5531]],
      [tg 152041, tg 157306]⟩,
    ⟨-4, 0, 3, 5,
      [[tg 513, tg 5778], [tg 370, tg 5635], [tg 422, tg 5687], [tg 279, tg 5544]],
      [tg 303634, tg 308899]⟩,
    ⟨-4, 0, 4, 9,
      [[tg 526, tg 5791], [tg 383, tg 5648], [tg 435, tg 5700], [tg 292, tg 5557]],
      [tg 303699, tg 308964]⟩,
    ⟨-4, 0, 5, 6,
      [[tg 539, tg 5804], [tg 565, tg 5830], [tg 396, tg 5661], [tg 448, tg 5713], [tg 305, tg 5570]],
      [tg 303660, tg 308925]⟩,
    ⟨-4, 0, 6, 8,
      [[tg 552, tg 5817], [tg 578, tg 5843], [tg 409, tg 5674], [tg 461, tg 5726], [tg 318, tg 5583]],
      [tg 152093, tg 157358]⟩,
    ⟨-4, 0, 7, 6,
      [[tg 565, tg 5830], [tg 422, tg 5687], [tg 461, tg 5726], [tg 305, tg 5570], [tg 331, tg 5596]],
      [tg 151937, tg 157202]⟩,
    ⟨-4, 0, 8, 7,
      [[tg 578, tg 5843], [tg 435, tg 5700], [tg 448, tg 5713], [tg 318, tg 5583], [tg 344, tg 5609]],
      [tg 303712, tg 308977]⟩,
    ⟨-5, 0, 0, 6,
      [[tg 591, tg 5856], [tg 623, tg 5888], [tg 487, tg 5752], [tg 357, tg 5622]],
      [tg 152119, tg 157384]⟩,
    ⟨-5, 0, 1, 5,
      [[tg 604, tg 5869], [tg 474, tg 5739], [tg 513, tg 5778], [tg 370, tg 5635]],
      [tg 370, tg 5635]⟩,
    ⟨-5, 0, 2, 11,
      [[tg 617, tg 5882], [tg 526, tg 5791], [tg 596, tg 63776], [tg 383, tg 5648]],
      [tg 152158, tg 157423]⟩,
    ⟨-5, 0, 3, 6,
      [[tg 630, tg 5895], [tg 487, tg 5752], [tg 539, tg 5804], [tg 396, tg 5661]],
      [tg 303751, tg 309016]⟩,
    ⟨-5, 0, 4, 10,
      [[tg 643, tg 5908], [tg 500, tg 5765], [tg 552, tg 5817], [tg 409, tg 5674]],
      [tg 303816, tg 309081]⟩,
    ⟨-5, 0, 5, 7,
      [[tg 656, tg 5921], [tg 682, tg 5947], [tg 513, tg 5778], [tg 565, tg 5830], [tg 422, tg 5687]],
      [tg 303777, tg 309042]⟩,
    ⟨-5, 0, 6, 9,
      [[tg 669, tg 5934], [tg 695, tg 5960], [tg 526, tg 5791], [tg 578, tg 5843], [tg 435, tg 5700]],
      [tg 152210, tg 157475]⟩,
    ⟨-5, 0, 7, 7,
      [[tg 682, tg 5947], [tg 539, tg 5804], [tg 578, tg 5843], [tg 422, tg 5687], [tg 448, tg 5713]],
      [tg 152054, tg 157319]⟩,
    ⟨-5, 0, 8, 8,
      [[tg 695, tg 5960], [tg 552, tg 5817], [tg 565, tg 5830], [tg 435, tg 5700], [tg 461, tg 5726]],
      [tg 303829, tg 309094]⟩,
    ⟨-6, 0, 0, 7,
      [[tg 708, tg 5973], [tg 506, tg 5771], [tg 604, tg 5869], [tg 474, tg 5739]],
      [tg 152236, tg 157501]⟩,
    ⟨-6, 0, 1, 6,
      [[tg 721, tg 5986], [tg 591, tg 5856], [tg 630, tg 5895], [tg 487, tg 5752]],
      [tg 487, tg 5752]⟩,
    ⟨-6, 0, 2, 12,
      [[tg 734, tg 5999], [tg 643, tg 5908], [tg 479, tg 63659], [tg 500, tg 5765]],
      [tg 152275, tg 157540]⟩,
    ⟨-6, 0, 3, 7,
      [[tg 747, tg 6012], [tg 604, tg 5869], [tg 656, tg 5921], [tg 513, tg 5778]],
      [tg 303868, tg 309133]⟩,
    ⟨-6, 0, 4, 11,
      [[tg 760, tg 6025], [tg 617, tg 5882], [tg 669, tg 5934], [tg 526, tg 5791]],
      [tg 303933, tg 309198]⟩,
    ⟨-6, 0, 5, 8,
      [[tg 773, tg 6038], [tg 799, tg 6064], [tg 630, tg 5895], [tg 682, tg 5947], [tg 539, tg 5804]],
      [tg 303894, tg 309159]⟩,
    ⟨-6, 0, 6, 10,
      [[tg 786, tg 6051], [tg 812, tg 6077], [tg 643, tg 5908], [tg 695, tg 5960], [tg 552, tg 5817]],
      [tg 152327, tg 157592]⟩,
    ⟨-6, 0, 7, 8,
      [[tg 799, tg 6064], [tg 656, tg 5921], [tg 695, tg 5960], [tg 539, tg 5804], [tg 565, tg 5830]],
      [tg 152171, tg 157436]⟩,
    ⟨-6, 0, 8, 9,
      [[tg 812, tg 6077], [tg 669, tg 5934], [tg 682, tg 5947], [tg 552, tg 5817], [tg 578, tg 5843]],
      [tg 303946, tg 309211]⟩,
    ⟨-7, 0, 0, 8,
      [[tg 825, tg 6090], [tg 389, tg 5654], [tg 721, tg 5986], [tg 591, tg 5856]],
      [tg 152353, tg 157618]⟩,
    ⟨-7, 0, 1, 7,
      [[tg 838, tg 6103], [tg 708, tg 5973], [tg 747, tg 6012], [tg 604, tg 5869]],
      [tg 604, tg 5869]⟩,
    ⟨-7, 0, 2, 13,
      [[tg 851, tg 6116], [tg 760, tg 6025], [tg 362, tg 63542], [tg 617, tg 5882]],
      [tg 152392, tg 157657]⟩,
    ⟨-7, 0, 3, 8,
      [[tg 864, tg 6129], [tg 721, tg 5986], [tg 773, tg 6038], [tg 630, tg 5895]],
      [tg 303985, tg 309250]⟩,
    ⟨-7, 0, 4, 12,
      [[tg 877, tg 6142], [tg 734, tg 5999], [tg 786, tg 6051], [tg 643, tg 5908]],
      [tg 304050, tg 309315]⟩,
    ⟨-7, 0, 5, 9,
      [[tg 890, tg 6155], [tg 916, tg 6181], [tg 747, tg 6012], [tg 799, tg 6064], [tg 656, tg 5921]],
      [tg 304011, tg 309276]⟩,
    ⟨-7, 0, 6, 11,
      [[tg 903, tg 6168], [tg 929, tg 6194], [tg 760, tg 6025], [tg 812, tg 6077], [tg 669, tg 5934]],
      [tg 152444, tg 157709]⟩,
    ⟨-7, 0, 7, 9,
      [[tg 916, tg 6181], [tg 773, tg 6038], [tg 812, tg 6077], [tg 656, tg 5921], [tg 682, tg 5947]],
      [tg 152288, tg 157553]⟩,
    ⟨-7, 0, 8, 10,
      [[tg 929, tg 6194], [tg 786, tg 6051], [tg 799, tg 6064], [tg 669, tg 5934], [tg 695, tg 5960]],
      [tg 304063, tg 309328]⟩,
    ⟨-8, 0, 0, 9,
      [[tg 942, tg 6207], [tg 272, tg 5537], [tg 838, tg 6103], [tg 708, tg 5973]],
      [tg 152470, tg 157735]⟩,
    ⟨-8, 0, 1, 8,
      [[tg 955, tg 6220], [tg 825, tg 6090], [tg 864, tg 6129], [tg 721, tg 5986]],
      [tg 721, tg 5986]⟩,
    ⟨-8, 0, 2, 14,
      [[tg 968, tg 6233], [tg 877, tg 6142], [tg 245, tg 63425], [tg 734, tg 5999]],
      [tg 152509, tg 157774]⟩,
    ⟨-8, 0, 3, 9,
      [[tg 981, tg 6246], [tg 838, tg 6103], [tg 890, tg 6155], [tg 747, tg 6012]],
      [tg 304102, tg 309367]⟩,
    ⟨-8, 0, 4, 13,
      [[tg 994, tg 6259], [tg 851, tg 6116], [tg 903, tg 6168], [tg 760, tg 6025]],
      [tg 304167, tg 309432]⟩,
    ⟨-8, 0, 5, 10,
      [[tg 1007, tg 6272], [tg 1033, tg 6298], [tg 864, tg 6129], [tg 916, tg 6181], [tg 773, tg 6038]],
      [tg 304128, tg 309393]⟩,
    ⟨-8, 0, 6, 12,
      [[tg 1020, tg 6285], [tg 1046, tg 6311], [tg 877, tg 6142], [tg 929, tg 6194], [tg 786, tg 6051]],
      [tg 152561, tg 157826]⟩,
    ⟨-8, 0, 7, 10,
      [[tg 1033, tg 6298], [tg 890, tg 6155], [tg 929, tg 6194], [tg 773, tg 6038], [tg 799, tg 6064]],
      [tg 152405, tg 157670]⟩,
    ⟨-8, 0, 8, 11,
      [[tg 1046, tg 6311], [tg 903, tg 6168], [tg 916, tg 6181], [tg 786, tg 6051], [tg 812, tg 6077]],
      [tg 304180, tg 309445]⟩,
    ⟨-9, 0, 0, 10,
      [[tg 4218, tg 9483], [tg 155, tg 5420], [tg 955, tg 6220], [tg 825, tg 6090]],
      [tg 152587, tg 157852]⟩,
    ⟨-9, 0, 1, 9,
      [[tg 4231, tg 9496], [tg 942, tg 6207], [tg 981, tg 6246], [tg 838, tg 6103]],
      [tg 838, tg 6103]⟩,
    ⟨-9, 0, 2, 15,
      [[tg 4244, tg 9509], [tg 994, tg 6259], [tg 128, tg 63308], [tg 851, tg 6116]],
      [tg 152626, tg 157891]⟩,
    ⟨-9, 0, 3, 10,
      [[tg 4257, tg 9522], [tg 955, tg 6220], [tg 1007, tg 6272], [tg 864, tg 6129]],
      [tg 304219, tg 309484]⟩,
    ⟨-9, 0, 4, 14,
      [[tg 4270, tg 9535], [tg 968, tg 6233], [tg 1020, tg 6285], [tg 877, tg 6142]],
      [tg 304284, tg 309549]⟩,
    ⟨-9, 0, 5, 11,
      [[tg 4283, tg 9548], [tg 4309, tg 9574], [tg 981, tg 6246], [tg 1033, tg 6298], [tg 890, tg 6155]],
      [tg 304245, tg 309510]⟩,
    ⟨-9, 0, 6, 13,
      [[tg 4296, tg 9561], [tg 4322, tg 9587], [tg 994, tg 6259], [tg 1046, tg 6311], [tg 903, tg 6168]],
      [tg 152678, tg 157943]⟩,
    ⟨-9, 0, 7, 11,
      [[tg 4309, tg 9574], [tg 1007, tg 6272], [tg 1046, tg 6311], [tg 890, tg 6155], [tg 916, tg 6181]],
      [tg 152522, tg 157787]⟩,
    ⟨-9, 0, 8, 12,
      [[tg 4322, tg 9587], [tg 1020, tg 6285], [tg 1033, tg 6298], [tg 903, tg 6168], [tg 929, tg 6194]],
      [tg 304297, tg 309562]⟩]⟩,
  ⟨2, -1, -1, 1, -1, [(-1, -1, 1), (1, -1, 1)], -1, -1, 1, 2, 1, -1, 1, 2,
   [⟨0, -2, 0, 19,
      [[tg 4336, tg 9601, tg 80152, tg 85417], [tg 54906, tg 60171, tg 130722, tg 135987], [tg 20, tg 5285, tg 75836, tg 81101], [tg 50668, tg 55933, tg 126484, tg 131749]],
      [tg 151652, tg 156917, tg 227468, tg 232733]⟩,
    ⟨0, -2, 1, 18,
      [[tg 4349, tg 9614, tg 80165, tg 85430], [tg 7, tg 5272, tg 75823, tg 81088], [tg 46, tg 5311, tg 75862, tg 81127], [tg 50681, tg 55946, tg 126497, tg 131762]],
      [tg 151678, tg 156943, tg 227494, tg 232759]⟩,
    ⟨0, -2, 2, 11,
      [[tg 4362, tg 9627, tg 80178, tg 85443], [tg 59, tg 5324, tg 75875, tg 81140], [tg 124, tg 5389, tg 75940, tg 81205], [tg 50694, tg 55959, tg 126510, tg 131775]],
      [tg 151756, tg 157021, tg 227572, tg 232837]⟩,
    ⟨0, -2, 3, 17,
      [[tg 4375, tg 9640, tg 80191, tg 85456], [tg 20, tg 5285, tg 75836, tg 81101], [tg 72, tg 5337, tg 75888, tg 81153], [tg 50707, tg 55972, tg 126523, tg 131788]],
      [tg 303336, tg 308601, tg 379152, tg 384417]⟩,
    ⟨0, -2, 4, 12,
      [[tg 4388, tg 9653, tg 80204, tg 85469], [tg 33, tg 5298, tg 75849, tg 81114], [tg 85, tg 5350, tg 75901, tg 81166], [tg 50720, tg 55985, tg 126536, tg 131801]],
      [tg 151665, tg 156930, tg 227481, tg 232746]⟩,
    ⟨0, -2, 5, 16,
      [[tg 4401, tg 9666, tg 80217, tg 85482], [tg 4427, tg 9692, tg 80243, tg 85508], [tg 46, tg 5311, tg 75862, tg 81127], [tg 98, tg 5363, tg 75914, tg 81179], [tg 50733, tg 55998, tg 126549, tg 131814]],
      [tg 459323, tg 464588, tg 535139, tg 540404]⟩,
    ⟨0, -2, 6, 13,
      [[tg 4414, tg 9679, tg 80230, tg 85495], [tg 4440, tg 9705, tg 80256, tg 85521], [tg 59, tg 5324, tg 75875, tg 81140], [tg 111, tg 5376, tg 75927, tg 81192], [tg 50746, tg 56011, tg 126562, tg 131827]],
      [tg 303323, tg 308588, tg 379139, tg 384404]⟩,
    ⟨0, -2, 7, 15,
      [[tg 4427, tg 9692, tg 80243, tg 85508], [tg 72, tg 5337, tg 75888, tg 81153], [tg 111, tg 5376, tg 75927, tg 81192], [tg 50733, tg 55998, tg 126549, tg 131814], [tg 50759, tg 56024, tg 126575, tg 131840]],
      [tg 303375, tg 308640, tg 379191, tg 384456]⟩,
    ⟨0, -2, 8, 14,
      [[tg 4440, tg 9705, tg 80256, tg 85521], [tg 85, tg 5350, tg 75901, tg 81166], [tg 98, tg 5363, tg 75914, tg 81179], [tg 50746, tg 56011, tg 126562, tg 131827], [tg 50772, tg 56037, tg 126588, tg 131853]],
      [tg 454981, tg 460246, tg 530797, tg 536062]⟩,
    ⟨0, -1, 0, 10,
      [[tg 1, tg 5266, tg 25279, tg 30544], [tg 33, tg 5298, tg 75849, tg 81114], [tg 137, tg 5402, tg 75953, tg 81218], [tg 2, tg 1060, tg 6320, tg 76876]],
      [tg 151769, tg 157034, tg 227585, tg 232850]⟩,
    ⟨0, -1, 1, 9,
      [[tg 14, tg 5279, tg 25292, tg 30557], [tg 124, tg 5389, tg 75940, tg 81205], [tg 163, tg 5428, tg 75979, tg 81244], [tg 15, tg 1073, tg 6333, tg 76889]],
      [tg 151795, tg 157060, tg 227611, tg 232876]⟩,
    ⟨0, -1, 2, 2,
      [[tg 27, tg 5292, tg 25305, tg 30570], [tg 176, tg 5441, tg 75992, tg 81257], [tg 0, tg 1054, tg 2108, tg 26332], [tg 28, tg 1086, tg 6346, tg 76902]],
      [tg 151632, tg 152686, tg 153740, tg 177964]⟩,
    ⟨0, -1, 3, 8,
      [[tg 40, tg 5305, tg 25318, tg 30583], [tg 137, tg 5402, tg 75953, tg 81218], [tg 189, tg 5454, tg 76005, tg 81270], [tg 41, tg 1099, tg 6359, tg 76915]],
      [tg 303453, tg 308718, tg 379269, tg 384534]⟩,
    ⟨0, -1, 4, 3,
      [[tg 53, tg 5318, tg 25331, tg 30596], [tg 150, tg 5415, tg 75966, tg 81231], [tg 202, tg 5467, tg 76018, tg 81283], [tg 54, tg 1112, tg 6372, tg 76928]],
      [tg 151782, tg 157047, tg 227598, tg 232863]⟩,
    ⟨0, -1, 5, 7,
      [[tg 66, tg 5331, tg 25344, tg 30609], [tg 92, tg 5357, tg 25370, tg 30635], [tg 163, tg 5428, tg 75979, tg 81244], [tg 215, tg 5480, tg 76031, tg 81296], [tg 67, tg 1125, tg 6385, tg 76941]],
      [tg 454988, tg 460253, tg 480266, tg 485531]⟩,
    ⟨0, -1, 6, 4,
      [[tg 79, tg 5344, tg 25357, tg 30622], [tg 105, tg 5370, tg 25383, tg 30648], [tg 176, tg 5441, tg 75992, tg 81257], [tg 228, tg 5493, tg 76044, tg 81309], [tg 80, tg 1138, tg 6398, tg 76954]],
      [tg 303440, tg 308705, tg 379256, tg 384521]⟩,
    ⟨0, -1, 7, 6,
      [[tg 92, tg 5357, tg 25370, tg 30635], [tg 189, tg 5454, tg 76005, tg 81270], [tg 228, tg 5493, tg 76044, tg 81309], [tg 67, tg 1125, tg 6385, tg 76941], [tg 93, tg 1151, tg 6411, tg 76967]],
      [tg 303492, tg 308757, tg 379308, tg 384573]⟩,
    ⟨0, -1, 8, 5,
      [[tg 105, tg 5370, tg 25383, tg 30648], [tg 202, tg 5467, tg 76018, tg 81283], [tg 215, tg 5480, tg 76031, tg 81296], [tg 80, tg 1138, tg 6398, tg 76954], [tg 106, tg 1164, tg 6424, tg 76980]],
      [tg 455098, tg 460363, tg 530914, tg 536179]⟩]⟩,
  ⟨2, 1, -1, 9, 0, [(0, -9, 1), (1, 1, 1)], 0, -9, 1, 9, 1, 1, 1, 9,
   [⟨2, -1, 0, 11,
      [[tg 2, tg 5267, tg 26216, tg 31481], [tg 4240, tg 9505, tg 30454, tg 35719], [tg 21, tg 5286, tg 75837, tg 81102], [tg 125, tg 5390, tg 75941, tg 81206]],
      [tg 454898, tg 460163, tg 481112, tg 486377]⟩,
    ⟨2, -1, 1, 10,
      [[tg 15, tg 5280, tg 26229, tg 31494], [tg 8, tg 5273, tg 75824, tg 81089], [tg 47, tg 5312, tg 75863, tg 81128], [tg 138, tg 5403, tg 75954, tg 81219]],
      [tg 454911, tg 460176, tg 481125, tg 486390]⟩,
    ⟨2, -1, 2, 4,
      [[tg 28, tg 5293, tg 26242, tg 31507], [tg 60, tg 5325, tg 75876, tg 81141], [tg 120, tg 1178, tg 6438, tg 76994], [tg 151, tg 5416, tg 75967, tg 81232]],
      [tg 454924, tg 460189, tg 481138, tg 486403]⟩,
    ⟨2, -1, 3, 9,
      [[tg 41, tg 5306, tg 26255, tg 31520], [tg 21, tg 5286, tg 75837, tg 81102], [tg 73, tg 5338, tg 75889, tg 81154], [tg 164, tg 5429, tg 75980, tg 81245]],
      [tg 454937, tg 460202, tg 481151, tg 486416]⟩,
    ⟨2, -1, 4, 5,
      [[tg 54, tg 5319, tg 26268, tg 31533], [tg 34, tg 5299, tg 75850, tg 81115], [tg 86, tg 5351, tg 75902, tg 81167], [tg 177, tg 5442, tg 75993, tg 81258]],
      [tg 454950, tg 460215, tg 481164, tg 486429]⟩,
    ⟨2, -1, 5, 8,
      [[tg 67, tg 5332, tg 26281, tg 31546], [tg 93, tg 5358, tg 26307, tg 31572], [tg 47, tg 5312, tg 75863, tg 81128], [tg 99, tg 5364, tg 75915, tg 81180], [tg 190, tg 5455, tg 76006, tg 81271]],
      [tg 606595, tg 611860, tg 632809, tg 638074]⟩,
    ⟨2, -1, 6, 6,
      [[tg 80, tg 5345, tg 26294, tg 31559], [tg 106, tg 5371, tg 26320, tg 31585], [tg 60, tg 5325, tg 75876, tg 81141], [tg 112, tg 5377, tg 75928, tg 81193], [tg 203, tg 5468, tg 76019, tg 81284]],
      [tg 606608, tg 611873, tg 632822, tg 638087]⟩,
    ⟨2, -1, 7, 8,
      [[tg 93, tg 5358, tg 26307, tg 31572], [tg 73, tg 5338, tg 75889, tg 81154], [tg 112, tg 5377, tg 75928, tg 81193], [tg 190, tg 5455, tg 76006, tg 81271], [tg 216, tg 5481, tg 76032, tg 81297]],
      [tg 606621, tg 611886, tg 632835, tg 638100]⟩,
    ⟨2, -1, 8, 7,
      [[tg 106, tg 5371, tg 26320, tg 31585], [tg 86, tg 5351, tg 75902, tg 81167], [tg 99, tg 5364, tg 75915, tg 81180], [tg 203, tg 5468, tg 76019, tg 81284], [tg 229, tg 5494, tg 76045, tg 81310]],
      [tg 606634, tg 611899, tg 632848, tg 638113]⟩,
    ⟨3, -1, 0, 12,
      [[tg 8, tg 5273, tg 75824, tg 81089], [tg 4246, tg 9511, tg 80062, tg 85327], [tg 138, tg 5403, tg 75954, tg 81219], [tg 242, tg 5507, tg 76058, tg 81323]],
      [tg 454904, tg 460169, tg 530720, tg 535985]⟩,
    ⟨3, -1, 1, 11,
      [[tg 21, tg 5286, tg 75837, tg 81102], [tg 125, tg 5390, tg 75941, tg 81206], [tg 164, tg 5429, tg 75980, tg 81245], [tg 255, tg 5520, tg 76071, tg 81336]],
      [tg 454917, tg 460182, tg 530733, tg 535998]⟩,
    ⟨3, -1, 2, 5,
      [[tg 34, tg 5299, tg 75850, tg 81115], [tg 177, tg 5442, tg 75993, tg 81258], [tg 237, tg 1295, tg 6555, tg 77111], [tg 268, tg 5533, tg 76084, tg 81349]],
      [tg 454930, tg 460195, tg 530746, tg 536011]⟩,
    ⟨3, -1, 3, 10,
      [[tg 47, tg 5312, tg 75863, tg 81128], [tg 138, tg 5403, tg 75954, tg 81219], [tg 190, tg 5455, tg 76006, tg 81271], [tg 281, tg 5546, tg 76097, tg 81362]],
      [tg 454943, tg 460208, tg 530759, tg 536024]⟩,
    ⟨3, -1, 4, 6,
      [[tg 60, tg 5325, tg 75876, tg 81141], [tg 151, tg 5416, tg 75967, tg 81232], [tg 203, tg 5468, tg 76019, tg 81284], [tg 294, tg 5559, tg 76110, tg 81375]],
      [tg 454956, tg 460221, tg 530772, tg 536037]⟩,
    ⟨3, -1, 5, 9,
      [[tg 73, tg 5338, tg 75889, tg 81154], [tg 99, tg 5364, tg 75915, tg 81180], [tg 164, tg 5429, tg 75980, tg 81245], [tg 216, tg 5481, tg 76032, tg 81297], [tg 307, tg 5572, tg 76123, tg 81388]],
      [tg 606601, tg 611866, tg 682417, tg 687682]⟩,
    ⟨3, -1, 6, 7,
      [[tg 86, tg 5351, tg 75902, tg 81167], [tg 112, tg 5377, tg 75928, tg 81193], [tg 177, tg 5442, tg 75993, tg 81258], [tg 229, tg 5494, tg 76045, tg 81310], [tg 320, tg 5585, tg 76136, tg 81401]],
      [tg 606614, tg 611879, tg 682430, tg 687695]⟩,
    ⟨3, -1, 7, 9,
      [[tg 99, tg 5364, tg 75915, tg 81180], [tg 190, tg 5455, tg 76006, tg 81271], [tg 229, tg 5494, tg 76045, tg 81310], [tg 307, tg 5572, tg 76123, tg 81388], [tg 333, tg 5598, tg 76149, tg 81414]],
      [tg 606627, tg 611892, tg 682443, tg 687708]⟩,
    ⟨3, -1, 8, 8,
      [[tg 112, tg 5377, tg 75928, tg 81193], [tg 203, tg 5468, tg 76019, tg 81284], [tg 216, tg 5481, tg 76032, tg 81297], [tg 320, tg 5585, tg 76136, tg 81401], [tg 346, tg 5611, tg 76162, tg 81427]],
      [tg 606640, tg 611905, tg 682456, tg 687721]⟩,
    ⟨4, -1, 0, 13,
      [[tg 125, tg 5390, tg 75941, tg 81206], [tg 4363, tg 9628, tg 80179, tg 85444], [tg 255, tg 5520, tg 76071, tg 81336], [tg 359, tg 5624, tg 76175, tg 81440]],
      [tg 455021, tg 460286, tg 530837, tg 536102]⟩,
    ⟨4, -1, 1, 12,
      [[tg 138, tg 5403, tg 75954, tg 81219], [tg 242, tg 5507, tg 76058, tg 81323], [tg 281, tg 5546, tg 76097, tg 81362], [tg 372, tg 5637, tg 76188, tg 81453]],
      [tg 455034, tg 460299, tg 530850, tg 536115]⟩,
    ⟨4, -1, 2, 6,
      [[tg 151, tg 5416, tg 75967, tg 81232], [tg 294, tg 5559, tg 76110, tg 81375], [tg 354, tg 1412, tg 6672, tg 77228], [tg 385, tg 5650, tg 76201, tg 81466]],
      [tg 455047, tg 460312, tg 530863, tg 536128]⟩,
    ⟨4, -1, 3, 11,
      [[tg 164, tg 5429, tg 75980, tg 81245], [tg 255, tg 5520, tg 76071, tg 81336], [tg 307, tg 5572, tg 76123, tg 81388], [tg 398, tg 5663, tg 76214, tg 81479]],
      [tg 455060, tg 460325, tg 530876, tg 536141]⟩,
    ⟨4, -1, 4, 7,
      [[tg 177, tg 5442, tg 75993, tg 81258], [tg 268, tg 5533, tg 76084, tg 81349], [tg 320, tg 5585, tg 76136, tg 81401], [tg 411, tg 5676, tg 76227, tg 81492]],
      [tg 455073, tg 460338, tg 530889, tg 536154]⟩,
    ⟨4, -1, 5, 10,
      [[tg 190, tg 5455, tg 76006, tg 81271], [tg 216, tg 5481, tg 76032, tg 81297], [tg 281, tg 5546, tg 76097, tg 81362], [tg 333, tg 5598, tg 76149, tg 81414], [tg 424, tg 5689, tg 76240, tg 81505]],
      [tg 606718, tg 611983, tg 682534, tg 687799]⟩,
    ⟨4, -1, 6, 8,
      [[tg 203, tg 5468, tg 76019, tg 81284], [tg 229, tg 5494, tg 76045, tg 81310], [tg 294, tg 5559, tg 76110, tg 81375], [tg 346, tg 5611, tg 76162, tg 81427], [tg 437, tg 5702, tg 76253, tg 81518]],
      [tg 606731, tg 611996, tg 682547, tg 687812]⟩,
    ⟨4, -1, 7, 10,
      [[tg 216, tg 5481, tg 76032, tg 81297], [tg 307, tg 5572, tg 76123, tg 81388], [tg 346, tg 5611, tg 76162, tg 81427], [tg 424, tg 5689, tg 76240, tg 81505], [tg 450, tg 5715, tg 76266, tg 81531]],
      [tg 606744, tg 612009, tg 682560, tg 687825]⟩,
    ⟨4, -1, 8, 9,
      [[tg 229, tg 5494, tg 76045, tg 81310], [tg 320, tg 5585, tg 76136, tg 81401], [tg 333, tg 5598, tg 76149, tg 81414], [tg 437, tg 5702, tg 76253, tg 81518], [tg 463, tg 5728, tg 76279, tg 81544]],
      [tg 606757, tg 612022, tg 682573, tg 687838]⟩,
    ⟨5, -1, 0, 14,
      [[tg 242, tg 5507, tg 76058, tg 81323], [tg 4480, tg 9745, tg 80296, tg 85561], [tg 372, tg 5637, tg 76188, tg 81453], [tg 476, tg 5741, tg 76292, tg 81557]],
      [tg 455138, tg 460403, tg 530954, tg 536219]⟩,
    ⟨5, -1, 1, 13,
      [[tg 255, tg 5520, tg 76071, tg 81336], [tg 359, tg 5624, tg 76175, tg 81440], [tg 398, tg 5663, tg 76214, tg 81479], [tg 489, tg 5754, tg 76305, tg 81570]],
      [tg 455151, tg 460416, tg 530967, tg 536232]⟩,
    ⟨5, -1, 2, 7,
      [[tg 268, tg 5533, tg 76084, tg 81349], [tg 411, tg 5676, tg 76227, tg 81492], [tg 471, tg 1529, tg 6789, tg 77345], [tg 502, tg 5767, tg 76318, tg 81583]],
      [tg 455164, tg 460429, tg 530980, tg 536245]⟩,
    ⟨5, -1, 3, 12,
      [[tg 281, tg 5546, tg 76097, tg 81362], [tg 372, tg 5637, tg 76188, tg 81453], [tg 424, tg 5689, tg 76240, tg 81505], [tg 515, tg 5780, tg 76331, tg 81596]],
      [tg 455177, tg 460442, tg 530993, tg 536258]⟩,
    ⟨5, -1, 4, 8,
      [[tg 294, tg 5559, tg 76110, tg 81375], [tg 385, tg 5650, tg 76201, tg 81466], [tg 437, tg 5702, tg 76253, tg 81518], [tg 528, tg 5793, tg 76344, tg 81609]],
      [tg 455190, tg 460455, tg 531006, tg 536271]⟩,
    ⟨5, -1, 5, 11,
      [[tg 307, tg 5572, tg 76123, tg 81388], [tg 333, tg 5598, tg 76149, tg 81414], [tg 398, tg 5663, tg 76214, tg 81479], [tg 450, tg 5715, tg 76266, tg 81531], [tg 541, tg 5806, tg 76357, tg 81622]],
      [tg 606835, tg 612100, tg 682651, tg 687916]⟩,
    ⟨5, -1, 6, 9,
      [[tg 320, tg 5585, tg 76136, tg 81401], [tg 346, tg 5611, tg 76162, tg 81427], [tg 411, tg 5676, tg 76227, tg 81492], [tg 463, tg 5728, tg 76279, tg 81544], [tg 554, tg 5819, tg 76370, tg 81635]],
      [tg 606848, tg 612113, tg 682664, tg 687929]⟩,
    ⟨5, -1, 7, 11,
      [[tg 333, tg 5598, tg 76149, tg 81414], [tg 424, tg 5689, tg 76240, tg 81505], [tg 463, tg 5728, tg 76279, tg 81544], [tg 541, tg 5806, tg 76357, tg 81622], [tg 567, tg 5832, tg 76383, tg 81648]],
      [tg 606861, tg 612126, tg 682677, tg 687942]⟩,
    ⟨5, -1, 8, 10,
      [[tg 346, tg 5611, tg 76162, tg 81427], [tg 437, tg 5702, tg 76253, tg 81518], [tg 450, tg 5715, tg 76266, tg 81531], [tg 554, tg 5819, tg 76370, tg 81635], [tg 580, tg 5845, tg 76396, tg 81661]],
      [tg 606874, tg 612139, tg 682690, tg 687955]⟩,
    ⟨6, -1, 0, 15,
      [[tg 359, tg 5624, tg 76175, tg 81440], [tg 4597, tg 9862, tg 80413, tg 85678], [tg 489, tg 5754, tg 76305, tg 81570], [tg 593, tg 5858, tg 76409, tg 81674]],
      [tg 455255, tg 460520, tg 531071, tg 536336]⟩,
    ⟨6, -1, 1, 14,
      [[tg 372, tg 5637, tg 76188, tg 81453], [tg 476, tg 5741, tg 76292, tg 81557], [tg 515, tg 5780, tg 76331, tg 81596], [tg 606, tg 5871, tg 76422, tg 81687]],
      [tg 455268, tg 460533, tg 531084, tg 536349]⟩,
    ⟨6, -1, 2, 8,
      [[tg 385, tg 5650, tg 76201, tg 81466], [tg 528, tg 5793, tg 76344, tg 81609], [tg 588, tg 1646, tg 6906, tg 77462], [tg 619, tg 5884, tg 76435, tg 81700]],
      [tg 455281, tg 460546, tg 531097, tg 536362]⟩,
    ⟨6, -1, 3, 13,
      [[tg 398, tg 5663, tg 76214, tg 81479], [tg 489, tg 5754, tg 76305, tg 81570], [tg 541, tg 5806, tg 76357, tg 81622], [tg 632, tg 5897, tg 76448, tg 81713]],
      [tg 455294, tg 460559, tg 531110, tg 536375]⟩,
    ⟨6, -1, 4, 9,
      [[tg 411, tg 5676, tg 76227, tg 81492], [tg 502, tg 5767, tg 76318, tg 81583], [tg 554, tg 5819, tg 76370, tg 81635], [tg 645, tg 5910, tg 76461, tg 81726]],
      [tg 455307, tg 460572, tg 531123, tg 536388]⟩,
    ⟨6, -1, 5, 12,
      [[tg 424, tg 5689, tg 76240, tg 81505], [tg 450, tg 5715, tg 76266, tg 81531], [tg 515, tg 5780, tg 76331, tg 81596], [tg 567, tg 5832, tg 76383, tg 81648], [tg 658, tg 5923, tg 76474, tg 81739]],
      [tg 606952, tg 612217, tg 682768, tg 688033]⟩,
    ⟨6, -1, 6, 10,
      [[tg 437, tg 5702, tg 76253, tg 81518], [tg 463, tg 5728, tg 76279, tg 81544], [tg 528, tg 5793, tg 76344, tg 81609], [tg 580, tg 5845, tg 76396, tg 81661], [tg 671, tg 5936, tg 76487, tg 81752]],
      [tg 606965, tg 612230, tg 682781, tg 688046]⟩,
    ⟨6, -1, 7, 12,
      [[tg 450, tg 5715, tg 76266, tg 81531], [tg 541, tg 5806, tg 76357, tg 81622], [tg 580, tg 5845, tg 76396, tg 81661], [tg 658, tg 5923, tg 76474, tg 81739], [tg 684, tg 5949, tg 76500, tg 81765]],
      [tg 606978, tg 612243, tg 682794, tg 688059]⟩,
    ⟨6, -1, 8, 11,
      [[tg 463, tg 5728, tg 76279, tg 81544], [tg 554, tg 5819, tg 76370, tg 81635], [tg 567, tg 5832, tg 76383, tg 81648], [tg 671, tg 5936, tg 76487, tg 81752], [tg 697, tg 5962, tg 76513, tg 81778]],
      [tg 606991, tg 612256, tg 682807, tg 688072]⟩,
    ⟨7, -1, 0, 16,
      [[tg 476, tg 5741, tg 76292, tg 81557], [tg 4714, tg 9979, tg 80530, tg 85795], [tg 606, tg 5871, tg 76422, tg 81687], [tg 710, tg 5975, tg 76526, tg 81791]],
      [tg 455372, tg 460637, tg 531188, tg 536453]⟩,
    ⟨7, -1, 1, 15,
      [[tg 489, tg 5754, tg 76305, tg 81570], [tg 593, tg 5858, tg 76409, tg 81674], [tg 632, tg 5897, tg 76448, tg 81713], [tg 723, tg 5988, tg 76539, tg 81804]],
      [tg 455385, tg 460650, tg 531201, tg 536466]⟩,
    ⟨7, -1, 2, 9,
      [[tg 502, tg 5767, tg 76318, tg 81583], [tg 645, tg 5910, tg 76461, tg 81726], [tg 705, tg 1763, tg 7023, tg 77579], [tg 736, tg 6001, tg 76552, tg 81817]],
      [tg 455398, tg 460663, tg 531214, tg 536479]⟩,
    ⟨7, -1, 3, 14,
      [[tg 515, tg 5780, tg 76331, tg 81596], [tg 606, tg 5871, tg 76422, tg 81687], [tg 658, tg 5923, tg 76474, tg 81739], [tg 749, tg 6014, tg 76565, tg 81830]],
      [tg 455411, tg 460676, tg 531227, tg 536492]⟩,
    ⟨7, -1, 4, 10,
      [[tg 528, tg 5793, tg 76344, tg 81609], [tg 619, tg 5884, tg 76435, tg 81700], [tg 671, tg 5936, tg 76487, tg 81752], [tg 762, tg 6027, tg 76578, tg 81843]],
      [tg 455424, tg 460689, tg 531240, tg 536505]⟩,
    ⟨7, -1, 5, 13,
      [[tg 541, tg 5806, tg 76357, tg 81622], [tg 567, tg 5832, tg 76383, tg 81648], [tg 632, tg 5897, tg 76448, tg 81713], [tg 684, tg 5949, tg 76500, tg 81765], [tg 775, tg 6040, tg 76591, tg 81856]],
      [tg 607069, tg 612334, tg 682885, tg 688150]⟩,
    ⟨7, -1, 6, 11,
      [[tg 554, tg 5819, tg 76370, tg 81635], [tg 580, tg 5845, tg 76396, tg 81661], [tg 645, tg 5910, tg 76461, tg 81726], [tg 697, tg 5962, tg 76513, tg 81778], [tg 788, tg 6053, tg 76604, tg 81869]],
      [tg 607082, tg 612347, tg 682898, tg 688163]⟩,
    ⟨7, -1, 7, 13,
      [[tg 567, tg 5832, tg 76383, tg 81648], [tg 658, tg 5923, tg 76474, tg 81739], [tg 697, tg 5962, tg 76513, tg 81778], [tg 775, tg 6040, tg 76591, tg 81856], [tg 801, tg 6066, tg 76617, tg 81882]],
      [tg 607095, tg 612360, tg 682911, tg 688176]⟩,
    ⟨7, -1, 8, 12,
      [[tg 580, tg 5845, tg 76396, tg 81661], [tg 671, tg 5936, tg 76487, tg 81752], [tg 684, tg 5949, tg 76500, tg 81765], [tg 788, tg 6053, tg 76604, tg 81869], [tg 814, tg 6079, tg 76630, tg 81895]],
      [tg 607108, tg 612373, tg 682924, tg 688189]⟩,
    ⟨8, -1, 0, 17,
      [[tg 593, tg 5858, tg 76409, tg 81674], [tg 4831, tg 10096, tg 80647, tg 85912], [tg 723, tg 5988, tg 76539, tg 81804], [tg 827, tg 6092, tg 76643, tg 81908]],
      [tg 455489, tg 460754, tg 531305, tg 536570]⟩,
    ⟨8, -1, 1, 16,
      [[tg 606, tg 5871, tg 76422, tg 81687], [tg 710, tg 5975, tg 76526, tg 81791], [tg 749, tg 6014, tg 76565, tg 81830], [tg 840, tg 6105, tg 76656, tg 81921]],
      [tg 455502, tg 460767, tg 531318, tg 536583]⟩,
    ⟨8, -1, 2, 10,
      [[tg 619, tg 5884, tg 76435, tg 81700], [tg 762, tg 6027, tg 76578, tg 81843], [tg 822, tg 1880, tg 7140, tg 77696], [tg 853, tg 6118, tg 76669, tg 81934]],
      [tg 455515, tg 460780, tg 531331, tg 536596]⟩,
    ⟨8, -1, 3, 15,
      [[tg 632, tg 5897, tg 76448, tg 81713], [tg 723, tg 5988, tg 76539, tg 81804], [tg 775, tg 6040, tg 76591, tg 81856], [tg 866, tg 6131, tg 76682, tg 81947]],
      [tg 455528, tg 460793, tg 531344, tg 536609]⟩,
    ⟨8, -1, 4, 11,
      [[tg 645, tg 5910, tg 76461, tg 81726], [tg 736, tg 6001, tg 76552, tg 81817], [tg 788, tg 6053, tg 76604, tg 81869], [tg 879, tg 6144, tg 76695, tg 81960]],
      [tg 455541, tg 460806, tg 531357, tg 536622]⟩,
    ⟨8, -1, 5, 14,
      [[tg 658, tg 5923, tg 76474, tg 81739], [tg 684, tg 5949, tg 76500, tg 81765], [tg 749, tg 6014, tg 76565, tg 81830], [tg 801, tg 6066, tg 76617, tg 81882], [tg 892, tg 6157, tg 76708, tg 81973]],
      [tg 607186, tg 612451, tg 683002, tg 688267]⟩,
    ⟨8, -1, 6, 12,
      [[tg 671, tg 5936, tg 76487, tg 81752], [tg 697, tg 5962, tg 76513, tg 81778], [tg 762, tg 6027, tg 76578, tg 81843], [tg 814, tg 6079, tg 76630, tg 81895], [tg 905, tg 6170, tg 76721, tg 81986]],
      [tg 607199, tg 612464, tg 683015, tg 688280]⟩,
    ⟨8, -1, 7, 14,
      [[tg 684, tg 5949, tg 76500, tg 81765], [tg 775, tg 6040, tg 76591, tg 81856], [tg 814, tg 6079, tg 76630, tg 81895], [tg 892, tg 6157, tg 76708, tg 81973], [tg 918, tg 6183, tg 76734, tg 81999]],
      [tg 607212, tg 612477, tg 683028, tg 688293]⟩,
    ⟨8, -1, 8, 13,
      [[tg 697, tg 5962, tg 76513, tg 81778], [tg 788, tg 6053, tg 76604, tg 81869], [tg 801, tg 6066, tg 76617, tg 81882], [tg 905, tg 6170, tg 76721, tg 81986], [tg 931, tg 6196, tg 76747, tg 82012]],
      [tg 607225, tg 612490, tg 683041, tg 688306]⟩,
    ⟨9, -1, 0, 18,
      [[tg 710, tg 5975, tg 76526, tg 81791], [tg 4948, tg 10213, tg 80764, tg 86029], [tg 840, tg 6105, tg 76656, tg 81921], [tg 944, tg 6209, tg 76760, tg 82025]],
      [tg 455606, tg 460871, tg 531422, tg 536687]⟩,
    ⟨9, -1, 1, 17,
      [[tg 723, tg 5988, tg 76539, tg 81804], [tg 827, tg 6092, tg 76643, tg 81908], [tg 866, tg 6131, tg 76682, tg 81947], [tg 957, tg 6222, tg 76773, tg 82038]],
      [tg 455619, tg 460884, tg 531435, tg 536700]⟩,
    ⟨9, -1, 2, 11,
      [[tg 736, tg 6001, tg 76552, tg 81817], [tg 879, tg 6144, tg 76695, tg 81960], [tg 939, tg 1997, tg 7257, tg 77813], [tg 970, tg 6235, tg 76786, tg 82051]],
      [tg 455632, tg 460897, tg 531448, tg 536713]⟩,
    ⟨9, -1, 3, 16,
      [[tg 749, tg 6014, tg 76565, tg 81830], [tg 840, tg 6105, tg 76656, tg 81921], [tg 892, tg 6157, tg 76708, tg 81973], [tg 983, tg 6248, tg 76799, tg 82064]],
      [tg 455645, tg 460910, tg 531461, tg 536726]⟩,
    ⟨9, -1, 4, 12,
      [[tg 762, tg 6027, tg 76578, tg 81843], [tg 853, tg 6118, tg 76669, tg 81934], [tg 905, tg 6170, tg 76721, tg 81986], [tg 996, tg 6261, tg 76812, tg 82077]],
      [tg 455658, tg 460923, tg 531474, tg 536739]⟩,
    ⟨9, -1, 5, 15,
      [[tg 775, tg 6040, tg 76591, tg 81856], [tg 801, tg 6066, tg 76617, tg 81882], [tg 866, tg 6131, tg 76682, tg 81947], [tg 918, tg 6183, tg 76734, tg 81999], [tg 1009, tg 6274, tg 76825, tg 82090]],
      [tg 607303, tg 612568, tg 683119, tg 688384]⟩,
    ⟨9, -1, 6, 13,
      [[tg 788, tg 6053, tg 76604, tg 81869], [tg 814, tg 6079, tg 76630, tg 81895], [tg 879, tg 6144, tg 76695, tg 81960], [tg 931, tg 6196, tg 76747, tg 82012], [tg 1022, tg 6287, tg 76838, tg 82103]],
      [tg 607316, tg 612581, tg 683132, tg 688397]⟩,
    ⟨9, -1, 7, 15,
      [[tg 801, tg 6066, tg 76617, tg 81882], [tg 892, tg 6157, tg 76708, tg 81973], [tg 931, tg 6196, tg 76747, tg 82012], [tg 1009, tg 6274, tg 76825, tg 82090], [tg 1035, tg 6300, tg 76851, tg 82116]],
      [tg 607329, tg 612594, tg 683145, tg 688410]⟩,
    ⟨9, -1, 8, 14,
      [[tg 814, tg 6079, tg 76630, tg 81895], [tg 905, tg 6170, tg 76721, tg 81986], [tg 918, tg 6183, tg 76734, tg 81999], [tg 1022, tg 6287, tg 76838, tg 82103], [tg 1048, tg 6313, tg 76864, tg 82129]],
      [tg 607342, tg 612607, tg 683158, tg 688423]⟩,
    ⟨10, -1, 0, 19,
      [[tg 827, tg 6092, tg 76643, tg 81908], [tg 5065, tg 10330, tg 80881, tg 86146], [tg 957, tg 6222, tg 76773, tg 82038], [tg 50552, tg 55817, tg 126368, tg 131633]],
      [tg 455723, tg 460988, tg 531539, tg 536804]⟩,
    ⟨10, -1, 1, 18,
      [[tg 840, tg 6105, tg 76656, tg 81921], [tg 944, tg 6209, tg 76760, tg 82025], [tg 983, tg 6248, tg 76799, tg 82064], [tg 50565, tg 55830, tg 126381, tg 131646]],
      [tg 455736, tg 461001, tg 531552, tg 536817]⟩,
    ⟨10, -1, 2, 12,
      [[tg 853, tg 6118, tg 76669, tg 81934], [tg 996, tg 6261, tg 76812, tg 82077], [tg 4215, tg 51605, tg 10533, tg 127421], [tg 50578, tg 55843, tg 126394, tg 131659]],
      [tg 455749, tg 461014, tg 531565, tg 536830]⟩,
    ⟨10, -1, 3, 17,
      [[tg 866, tg 6131, tg 76682, tg 81947], [tg 957, tg 6222, tg 76773, tg 82038], [tg 1009, tg 6274, tg 76825, tg 82090], [tg 50591, tg 55856, tg 126407, tg 131672]],
      [tg 455762, tg 461027, tg 531578, tg 536843]⟩,
    ⟨10, -1, 4, 13,
      [[tg 879, tg 6144, tg 76695, tg 81960], [tg 970, tg 6235, tg 76786, tg 82051], [tg 1022, tg 6287, tg 76838, tg 82103], [tg 50604, tg 55869, tg 126420, tg 131685]],
      [tg 455775, tg 461040, tg 531591, tg 536856]⟩,
    ⟨10, -1, 5, 16,
      [[tg 892, tg 6157, tg 76708, tg 81973], [tg 918, tg 6183, tg 76734, tg 81999], [tg 983, tg 6248, tg 76799, tg 82064], [tg 1035, tg 6300, tg 76851, tg 82116], [tg 50617, tg 55882, tg 126433, tg 131698]],
      [tg 607420, tg 612685, tg 683236, tg 688501]⟩,
    ⟨10, -1, 6, 14,
      [[tg 905, tg 6170, tg 76721, tg 81986], [tg 931, tg 6196, tg 76747, tg 82012], [tg 996, tg 6261, tg 76812, tg 82077], [tg 1048, tg 6313, tg 76864, tg 82129], [tg 50630, tg 55895, tg 126446, tg 131711]],
      [tg 607433, tg 612698, tg 683249, tg 688514]⟩,
    ⟨10, -1, 7, 16,
      [[tg 918, tg 6183, tg 76734, tg 81999], [tg 1009, tg 6274, tg 76825, tg 82090], [tg 1048, tg 6313, tg 76864, tg 82129], [tg 50617, tg 55882, tg 126433, tg 131698], [tg 50643, tg 55908, tg 126459, tg 131724]],
      [tg 607446, tg 612711, tg 683262, tg 688527]⟩,
    ⟨10, -1, 8, 15,
      [[tg 931, tg 6196, tg 76747, tg 82012], [tg 1022, tg 6287, tg 76838, tg 82103], [tg 1035, tg 6300, tg 76851, tg 82116], [tg 50630, tg 55895, tg 126446, tg 131711], [tg 50656, tg 55921, tg 126472, tg 131737]],
      [tg 607459, tg 612724, tg 683275, tg 688540]⟩]⟩,
  ⟨2, 9, 0, 1, 1, [(1, -1, 1), (0, 9, 1)], 1, -1, 1, 9, 0, 9, 1, 9,
   [⟨2, 1, 0, 9,
      [[tg 4, tg 1998, tg 6322, tg 77814], [tg 146, tg 5411, tg 25424, tg 30689], [tg 22, tg 5287, tg 75838, tg 81103], [tg 126, tg 5391, tg 75942, tg 81207]],
      [tg 454900, tg 456894, tg 461218, tg 532710]⟩,
    ⟨2, 1, 1, 10,
      [[tg 17, tg 2011, tg 6335, tg 77827], [tg 9, tg 5274, tg 75825, tg 81090], [tg 48, tg 5313, tg 75864, tg 81129], [tg 139, tg 5404, tg 75955, tg 81220]],
      [tg 454913, tg 456907, tg 461231, tg 532723]⟩,
    ⟨2, 1, 2, 16,
      [[tg 30, tg 2024, tg 6348, tg 77840], [tg 61, tg 5326, tg 75877, tg 81142], [tg 4216, tg 52542, tg 10534, tg 128358], [tg 152, tg 5417, tg 75968, tg 81233]],
      [tg 151693, tg 456920, tg 227509, tg 532736]⟩,
    ⟨2, 1, 3, 11,
      [[tg 43, tg 2037, tg 6361, tg 77853], [tg 22, tg 5287, tg 75838, tg 81103], [tg 74, tg 5339, tg 75890, tg 81155], [tg 165, tg 5430, tg 75981, tg 81246]],
      [tg 454939, tg 456933, tg 461257, tg 532749]⟩,
    ⟨2, 1, 4, 15,
      [[tg 56, tg 2050, tg 6374, tg 77866], [tg 35, tg 5300, tg 75851, tg 81116], [tg 87, tg 5352, tg 75903, tg 81168], [tg 178, tg 5443, tg 75994, tg 81259]],
      [tg 303351, tg 456946, tg 379167, tg 532762]⟩,
    ⟨2, 1, 5, 12,
      [[tg 69, tg 2063, tg 6387, tg 77879], [tg 95, tg 2089, tg 6413, tg 77905], [tg 48, tg 5313, tg 75864, tg 81129], [tg 100, tg 5365, tg 75916, tg 81181], [tg 191, tg 5456, tg 76007, tg 81272]],
      [tg 606597, tg 608591, tg 612915, tg 684407]⟩,
    ⟨2, 1, 6, 14,
      [[tg 82, tg 2076, tg 6400, tg 77892], [tg 108, tg 2102, tg 6426, tg 77918], [tg 61, tg 5326, tg 75877, tg 81142], [tg 113, tg 5378, tg 75929, tg 81194], [tg 204, tg 5469, tg 76020, tg 81285]],
      [tg 455004, tg 608604, tg 461322, tg 684420]⟩,
    ⟨2, 1, 7, 13,
      [[tg 95, tg 2089, tg 6413, tg 77905], [tg 74, tg 5339, tg 75890, tg 81155], [tg 113, tg 5378, tg 75929, tg 81194], [tg 191, tg 5456, tg 76007, tg 81272], [tg 217, tg 5482, tg 76033, tg 81298]],
      [tg 606623, tg 608617, tg 612941, tg 684433]⟩,
    ⟨2, 1, 8, 14,
      [[tg 108, tg 2102, tg 6426, tg 77918], [tg 87, tg 5352, tg 75903, tg 81168], [tg 100, tg 5365, tg 75916, tg 81181], [tg 204, tg 5469, tg 76020, tg 81285], [tg 230, tg 5495, tg 76046, tg 81311]],
      [tg 606636, tg 608630, tg 612954, tg 684446]⟩,
    ⟨3, 1, 0, 10,
      [[tg 9, tg 5274, tg 75825, tg 81090], [tg 263, tg 5528, tg 25541, tg 30806], [tg 139, tg 5404, tg 75955, tg 81220], [tg 243, tg 5508, tg 76059, tg 81324]],
      [tg 454905, tg 460170, tg 530721, tg 535986]⟩,
    ⟨3, 1, 1, 11,
      [[tg 22, tg 5287, tg 75838, tg 81103], [tg 126, tg 5391, tg 75942, tg 81207], [tg 165, tg 5430, tg 75981, tg 81246], [tg 256, tg 5521, tg 76072, tg 81337]],
      [tg 454918, tg 460183, tg 530734, tg 535999]⟩,
    ⟨3, 1, 2, 17,
      [[tg 35, tg 5300, tg 75851, tg 81116], [tg 178, tg 5443, tg 75994, tg 81259], [tg 50553, tg 55818, tg 126369, tg 131634], [tg 269, tg 5534, tg 76085, tg 81350]],
      [tg 454931, tg 460196, tg 530747, tg 536012]⟩,
    ⟨3, 1, 3, 12,
      [[tg 48, tg 5313, tg 75864, tg 81129], [tg 139, tg 5404, tg 75955, tg 81220], [tg 191, tg 5456, tg 76007, tg 81272], [tg 282, tg 5547, tg 76098, tg 81363]],
      [tg 454944, tg 460209, tg 530760, tg 536025]⟩,
    ⟨3, 1, 4, 16,
      [[tg 61, tg 5326, tg 75877, tg 81142], [tg 152, tg 5417, tg 75968, tg 81233], [tg 204, tg 5469, tg 76020, tg 81285], [tg 295, tg 5560, tg 76111, tg 81376]],
      [tg 454957, tg 460222, tg 530773, tg 536038]⟩,
    ⟨3, 1, 5, 13,
      [[tg 74, tg 5339, tg 75890, tg 81155], [tg 100, tg 5365, tg 75916, tg 81181], [tg 165, tg 5430, tg 75981, tg 81246], [tg 217, tg 5482, tg 76033, tg 81298], [tg 308, tg 5573, tg 76124, tg 81389]],
      [tg 606602, tg 611867, tg 682418, tg 687683]⟩,
    ⟨3, 1, 6, 15,
      [[tg 87, tg 5352, tg 75903, tg 81168], [tg 113, tg 5378, tg 75929, tg 81194], [tg 178, tg 5443, tg 75994, tg 81259], [tg 230, tg 5495, tg 76046, tg 81311], [tg 321, tg 5586, tg 76137, tg 81402]],
      [tg 606615, tg 611880, tg 682431, tg 687696]⟩,
    ⟨3, 1, 7, 14,
      [[tg 100, tg 5365, tg 75916, tg 81181], [tg 191, tg 5456, tg 76007, tg 81272], [tg 230, tg 5495, tg 76046, tg 81311], [tg 308, tg 5573, tg 76124, tg 81389], [tg 334, tg 5599, tg 76150, tg 81415]],
      [tg 606628, tg 611893, tg 682444, tg 687709]⟩,
    ⟨3, 1, 8, 15,
      [[tg 113, tg 5378, tg 75929, tg 81194], [tg 204, tg 5469, tg 76020, tg 81285], [tg 217, tg 5482, tg 76033, tg 81298], [tg 321, tg 5586, tg 76137, tg 81402], [tg 347, tg 5612, tg 76163, tg 81428]],
      [tg 606641, tg 611906, tg 682457, tg 687722]⟩,
    ⟨4, 1, 0, 11,
      [[tg 126, tg 5391, tg 75942, tg 81207], [tg 380, tg 5645, tg 25658, tg 30923], [tg 256, tg 5521, tg 76072, tg 81337], [tg 360, tg 5625, tg 76176, tg 81441]],
      [tg 455022, tg 460287, tg 530838, tg 536103]⟩,
    ⟨4, 1, 1, 12,
      [[tg 139, tg 5404, tg 75955, tg 81220], [tg 243, tg 5508, tg 76059, tg 81324], [tg 282, tg 5547, tg 76098, tg 81363], [tg 373, tg 5638, tg 76189, tg 81454]],
      [tg 455035, tg 460300, tg 530851, tg 536116]⟩,
    ⟨4, 1, 2, 18,
      [[tg 152, tg 5417, tg 75968, tg 81233], [tg 295, tg 5560, tg 76111, tg 81376], [tg 50670, tg 55935, tg 126486, tg 131751], [tg 386, tg 5651, tg 76202, tg 81467]],
      [tg 455048, tg 460313, tg 530864, tg 536129]⟩,
    ⟨4, 1, 3, 13,
      [[tg 165, tg 5430, tg 75981, tg 81246], [tg 256, tg 5521, tg 76072, tg 81337], [tg 308, tg 5573, tg 76124, tg 81389], [tg 399, tg 5664, tg 76215, tg 81480]],
      [tg 455061, tg 460326, tg 530877, tg 536142]⟩,
    ⟨4, 1, 4, 17,
      [[tg 178, tg 5443, tg 75994, tg 81259], [tg 269, tg 5534, tg 76085, tg 81350], [tg 321, tg 5586, tg 76137, tg 81402], [tg 412, tg 5677, tg 76228, tg 81493]],
      [tg 455074, tg 460339, tg 530890, tg 536155]⟩,
    ⟨4, 1, 5, 14,
      [[tg 191, tg 5456, tg 76007, tg 81272], [tg 217, tg 5482, tg 76033, tg 81298], [tg 282, tg 5547, tg 76098, tg 81363], [tg 334, tg 5599, tg 76150, tg 81415], [tg 425, tg 5690, tg 76241, tg 81506]],
      [tg 606719, tg 611984, tg 682535, tg 687800]⟩,
    ⟨4, 1, 6, 16,
      [[tg 204, tg 5469, tg 76020, tg 81285], [tg 230, tg 5495, tg 76046, tg 81311], [tg 295, tg 5560, tg 76111, tg 81376], [tg 347, tg 5612, tg 76163, tg 81428], [tg 438, tg 5703, tg 76254, tg 81519]],
      [tg 606732, tg 611997, tg 682548, tg 687813]⟩,
    ⟨4, 1, 7, 15,
      [[tg 217, tg 5482, tg 76033, tg 81298], [tg 308, tg 5573, tg 76124, tg 81389], [tg 347, tg 5612, tg 76163, tg 81428], [tg 425, tg 5690, tg 76241, tg 81506], [tg 451, tg 5716, tg 76267, tg 81532]],
      [tg 606745, tg 612010, tg 682561, tg 687826]⟩,
    ⟨4, 1, 8, 16,
      [[tg 230, tg 5495, tg 76046, tg 81311], [tg 321, tg 5586, tg 76137, tg 81402], [tg 334, tg 5599, tg 76150, tg 81415], [tg 438, tg 5703, tg 76254, tg 81519], [tg 464, tg 5729, tg 76280, tg 81545]],
      [tg 606758, tg 612023, tg 682574, tg 687839]⟩,
    ⟨5, 1, 0, 12,
      [[tg 243, tg 5508, tg 76059, tg 81324], [tg 497, tg 5762, tg 25775, tg 31040], [tg 373, tg 5638, tg 76189, tg 81454], [tg 477, tg 5742, tg 76293, tg 81558]],
      [tg 455139, tg 460404, tg 530955, tg 536220]⟩,
    ⟨5, 1, 1, 13,
      [[tg 256, tg 5521, tg 76072, tg 81337], [tg 360, tg 5625, tg 76176, tg 81441], [tg 399, tg 5664, tg 76215, tg 81480], [tg 490, tg 5755, tg 76306, tg 81571]],
      [tg 455152, tg 460417, tg 530968, tg 536233]⟩,
    ⟨5, 1, 2, 19,
      [[tg 269, tg 5534, tg 76085, tg 81350], [tg 412, tg 5677, tg 76228, tg 81493], [tg 50787, tg 56052, tg 126603, tg 131868], [tg 503, tg 5768, tg 76319, tg 81584]],
      [tg 455165, tg 460430, tg 530981, tg 536246]⟩,
    ⟨5, 1, 3, 14,
      [[tg 282, tg 5547, tg 76098, tg 81363], [tg 373, tg 5638, tg 76189, tg 81454], [tg 425, tg 5690, tg 76241, tg 81506], [tg 516, tg 5781, tg 76332, tg 81597]],
      [tg 455178, tg 460443, tg 530994, tg 536259]⟩,
    ⟨5, 1, 4, 18,
      [[tg 295, tg 5560, tg 76111, tg 81376], [tg 386, tg 5651, tg 76202, tg 81467], [tg 438, tg 5703, tg 76254, tg 81519], [tg 529, tg 5794, tg 76345, tg 81610]],
      [tg 455191, tg 460456, tg 531007, tg 536272]⟩,
    ⟨5, 1, 5, 15,
      [[tg 308, tg 5573, tg 76124, tg 81389], [tg 334, tg 5599, tg 76150, tg 81415], [tg 399, tg 5664, tg 76215, tg 81480], [tg 451, tg 5716, tg 76267, tg 81532], [tg 542, tg 5807, tg 76358, tg 81623]],
      [tg 606836, tg 612101, tg 682652, tg 687917]⟩,
    ⟨5, 1, 6, 17,
      [[tg 321, tg 5586, tg 76137, tg 81402], [tg 347, tg 5612, tg 76163, tg 81428], [tg 412, tg 5677, tg 76228, tg 81493], [tg 464, tg 5729, tg 76280, tg 81545], [tg 555, tg 5820, tg 76371, tg 81636]],
      [tg 606849, tg 612114, tg 682665, tg 687930]⟩,
    ⟨5, 1, 7, 16,
      [[tg 334, tg 5599, tg 76150, tg 81415], [tg 425, tg 5690, tg 76241, tg 81506], [tg 464, tg 5729, tg 76280, tg 81545], [tg 542, tg 5807, tg 76358, tg 81623], [tg 568, tg 5833, tg 76384, tg 81649]],
      [tg 606862, tg 612127, tg 682678, tg 687943]⟩,
    ⟨5, 1, 8, 17,
      [[tg 347, tg 5612, tg 76163, tg 81428], [tg 438, tg 5703, tg 76254, tg 81519], [tg 451, tg 5716, tg 76267, tg 81532], [tg 555, tg 5820, tg 76371, tg 81636], [tg 581, tg 5846, tg 76397, tg 81662]],
      [tg 606875, tg 612140, tg 682691, tg 687956]⟩,
    ⟨6, 1, 0, 13,
      [[tg 360, tg 5625, tg 76176, tg 81441], [tg 614, tg 5879, tg 25892, tg 31157], [tg 490, tg 5755, tg 76306, tg 81571], [tg 594, tg 5859, tg 76410, tg 81675]],
      [tg 455256, tg 460521, tg 531072, tg 536337]⟩,
    ⟨6, 1, 1, 14,
      [[tg 373, tg 5638, tg 76189, tg 81454], [tg 477, tg 5742, tg 76293, tg 81558], [tg 516, tg 5781, tg 76332, tg 81597], [tg 607, tg 5872, tg 76423, tg 81688]],
      [tg 455269, tg 460534, tg 531085, tg 536350]⟩,
    ⟨6, 1, 2, 20,
      [[tg 386, tg 5651, tg 76202, tg 81467], [tg 529, tg 5794, tg 76345, tg 81610], [tg 50904, tg 56169, tg 126720, tg 131985], [tg 620, tg 5885, tg 76436, tg 81701]],
      [tg 455282, tg 460547, tg 531098, tg 536363]⟩,
    ⟨6, 1, 3, 15,
      [[tg 399, tg 5664, tg 76215, tg 81480], [tg 490, tg 5755, tg 76306, tg 81571], [tg 542, tg 5807, tg 76358, tg 81623], [tg 633, tg 5898, tg 76449, tg 81714]],
      [tg 455295, tg 460560, tg 531111, tg 536376]⟩,
    ⟨6, 1, 4, 19,
      [[tg 412, tg 5677, tg 76228, tg 81493], [tg 503, tg 5768, tg 76319, tg 81584], [tg 555, tg 5820, tg 76371, tg 81636], [tg 646, tg 5911, tg 76462, tg 81727]],
      [tg 455308, tg 460573, tg 531124, tg 536389]⟩,
    ⟨6, 1, 5, 16,
      [[tg 425, tg 5690, tg 76241, tg 81506], [tg 451, tg 5716, tg 76267, tg 81532], [tg 516, tg 5781, tg 76332, tg 81597], [tg 568, tg 5833, tg 76384, tg 81649], [tg 659, tg 5924, tg 76475, tg 81740]],
      [tg 606953, tg 612218, tg 682769, tg 688034]⟩,
    ⟨6, 1, 6, 18,
      [[tg 438, tg 5703, tg 76254, tg 81519], [tg 464, tg 5729, tg 76280, tg 81545], [tg 529, tg 5794, tg 76345, tg 81610], [tg 581, tg 5846, tg 76397, tg 81662], [tg 672, tg 5937, tg 76488, tg 81753]],
      [tg 606966, tg 612231, tg 682782, tg 688047]⟩,
    ⟨6, 1, 7, 17,
      [[tg 451, tg 5716, tg 76267, tg 81532], [tg 542, tg 5807, tg 76358, tg 81623], [tg 581, tg 5846, tg 76397, tg 81662], [tg 659, tg 5924, tg 76475, tg 81740], [tg 685, tg 5950, tg 76501, tg 81766]],
      [tg 606979, tg 612244, tg 682795, tg 688060]⟩,
    ⟨6, 1, 8, 18,
      [[tg 464, tg 5729, tg 76280, tg 81545], [tg 555, tg 5820, tg 76371, tg 81636], [tg 568, tg 5833, tg 76384, tg 81649], [tg 672, tg 5937, tg 76488, tg 81753], [tg 698, tg 5963, tg 76514, tg 81779]],
      [tg 606992, tg 612257, tg 682808, tg 688073]⟩,
    ⟨7, 1, 0, 14,
      [[tg 477, tg 5742, tg 76293, tg 81558], [tg 731, tg 5996, tg 26009, tg 31274], [tg 607, tg 5872, tg 76423, tg 81688], [tg 711, tg 5976, tg 76527, tg 81792]],
      [tg 455373, tg 460638, tg 531189, tg 536454]⟩,
    ⟨7, 1, 1, 15,
      [[tg 490, tg 5755, tg 76306, tg 81571], [tg 594, tg 5859, tg 76410, tg 81675], [tg 633, tg 5898, tg 76449, tg 81714], [tg 724, tg 5989, tg 76540, tg 81805]],
      [tg 455386, tg 460651, tg 531202, tg 536467]⟩,
    ⟨7, 1, 2, 21,
      [[tg 503, tg 5768, tg 76319, tg 81584], [tg 646, tg 5911, tg 76462, tg 81727], [tg 51021, tg 56286, tg 126837, tg 132102], [tg 737, tg 6002, tg 76553, tg 81818]],
      [tg 455399, tg 460664, tg 531215, tg 536480]⟩,
    ⟨7, 1, 3, 16,
      [[tg 516, tg 5781, tg 76332, tg 81597], [tg 607, tg 5872, tg 76423, tg 81688], [tg 659, tg 5924, tg 76475, tg 81740], [tg 750, tg 6015, tg 76566, tg 81831]],
      [tg 455412, tg 460677, tg 531228, tg 536493]⟩,
    ⟨7, 1, 4, 20,
      [[tg 529, tg 5794, tg 76345, tg 81610], [tg 620, tg 5885, tg 76436, tg 81701], [tg 672, tg 5937, tg 76488, tg 81753], [tg 763, tg 6028, tg 76579, tg 81844]],
      [tg 455425, tg 460690, tg 531241, tg 536506]⟩,
    ⟨7, 1, 5, 17,
      [[tg 542, tg 5807, tg 76358, tg 81623], [tg 568, tg 5833, tg 76384, tg 81649], [tg 633, tg 5898, tg 76449, tg 81714], [tg 685, tg 5950, tg 76501, tg 81766], [tg 776, tg 6041, tg 76592, tg 81857]],
      [tg 607070, tg 612335, tg 682886, tg 688151]⟩,
    ⟨7, 1, 6, 19,
      [[tg 555, tg 5820, tg 76371, tg 81636], [tg 581, tg 5846, tg 76397, tg 81662], [tg 646, tg 5911, tg 76462, tg 81727], [tg 698, tg 5963, tg 76514, tg 81779], [tg 789, tg 6054, tg 76605, tg 81870]],
      [tg 607083, tg 612348, tg 682899, tg 688164]⟩,
    ⟨7, 1, 7, 18,
      [[tg 568, tg 5833, tg 76384, tg 81649], [tg 659, tg 5924, tg 76475, tg 81740], [tg 698, tg 5963, tg 76514, tg 81779], [tg 776, tg 6041, tg 76592, tg 81857], [tg 802, tg 6067, tg 76618, tg 81883]],
      [tg 607096, tg 612361, tg 682912, tg 688177]⟩,
    ⟨7, 1, 8, 19,
      [[tg 581, tg 5846, tg 76397, tg 81662], [tg 672, tg 5937, tg 76488, tg 81753], [tg 685, tg 5950, tg 76501, tg 81766], [tg 789, tg 6054, tg 76605, tg 81870], [tg 815, tg 6080, tg 76631, tg 81896]],
      [tg 607109, tg 612374, tg 682925, tg 688190]⟩,
    ⟨8, 1, 0, 15,
      [[tg 594, tg 5859, tg 76410, tg 81675], [tg 848, tg 6113, tg 26126, tg 31391], [tg 724, tg 5989, tg 76540, tg 81805], [tg 828, tg 6093, tg 76644, tg 81909]],
      [tg 455490, tg 460755, tg 531306, tg 536571]⟩,
    ⟨8, 1, 1, 16,
      [[tg 607, tg 5872, tg 76423, tg 81688], [tg 711, tg 5976, tg 76527, tg 81792], [tg 750, tg 6015, tg 76566, tg 81831], [tg 841, tg 6106, tg 76657, tg 81922]],
      [tg 455503, tg 460768, tg 531319, tg 536584]⟩,
    ⟨8, 1, 2, 22,
      [[tg 620, tg 5885, tg 76436, tg 81701], [tg 763, tg 6028, tg 76579, tg 81844], [tg 51138, tg 56403, tg 126954, tg 132219], [tg 854, tg 6119, tg 76670, tg 81935]],
      [tg 455516, tg 460781, tg 531332, tg 536597]⟩,
    ⟨8, 1, 3, 17,
      [[tg 633, tg 5898, tg 76449, tg 81714], [tg 724, tg 5989, tg 76540, tg 81805], [tg 776, tg 6041, tg 76592, tg 81857], [tg 867, tg 6132, tg 76683, tg 81948]],
      [tg 455529, tg 460794, tg 531345, tg 536610]⟩,
    ⟨8, 1, 4, 21,
      [[tg 646, tg 5911, tg 76462, tg 81727], [tg 737, tg 6002, tg 76553, tg 81818], [tg 789, tg 6054, tg 76605, tg 81870], [tg 880, tg 6145, tg 76696, tg 81961]],
      [tg 455542, tg 460807, tg 531358, tg 536623]⟩,
    ⟨8, 1, 5, 18,
      [[tg 659, tg 5924, tg 76475, tg 81740], [tg 685, tg 5950, tg 76501, tg 81766], [tg 750, tg 6015, tg 76566, tg 81831], [tg 802, tg 6067, tg 76618, tg 81883], [tg 893, tg 6158, tg 76709, tg 81974]],
      [tg 607187, tg 612452, tg 683003, tg 688268]⟩,
    ⟨8, 1, 6, 20,
      [[tg 672, tg 5937, tg 76488, tg 81753], [tg 698, tg 5963, tg 76514, tg 81779], [tg 763, tg 6028, tg 76579, tg 81844], [tg 815, tg 6080, tg 76631, tg 81896], [tg 906, tg 6171, tg 76722, tg 81987]],
      [tg 607200, tg 612465, tg 683016, tg 688281]⟩,
    ⟨8, 1, 7, 19,
      [[tg 685, tg 5950, tg 76501, tg 81766], [tg 776, tg 6041, tg 76592, tg 81857], [tg 815, tg 6080, tg 76631, tg 81896], [tg 893, tg 6158, tg 76709, tg 81974], [tg 919, tg 6184, tg 76735, tg 82000]],
      [tg 607213, tg 612478, tg 683029, tg 688294]⟩,
    ⟨8, 1, 8, 20,
      [[tg 698, tg 5963, tg 76514, tg 81779], [tg 789, tg 6054, tg 76605, tg 81870], [tg 802, tg 6067, tg 76618, tg 81883], [tg 906, tg 6171, tg 76722, tg 81987], [tg 932, tg 6197, tg 76748, tg 82013]],
      [tg 607226, tg 612491, tg 683042, tg 688307]⟩,
    ⟨9, 1, 0, 16,
      [[tg 711, tg 5976, tg 76527, tg 81792], [tg 965, tg 6230, tg 26243, tg 31508], [tg 841, tg 6106, tg 76657, tg 81922], [tg 945, tg 6210, tg 76761, tg 82026]],
      [tg 455607, tg 460872, tg 531423, tg 536688]⟩,
    ⟨9, 1, 1, 17,
      [[tg 724, tg 5989, tg 76540, tg 81805], [tg 828, tg 6093, tg 76644, tg 81909], [tg 867, tg 6132, tg 76683, tg 81948], [tg 958, tg 6223, tg 76774, tg 82039]],
      [tg 455620, tg 460885, tg 531436, tg 536701]⟩,
    ⟨9, 1, 2, 23,
      [[tg 737, tg 6002, tg 76553, tg 81818], [tg 880, tg 6145, tg 76696, tg 81961], [tg 51255, tg 56520, tg 127071, tg 132336], [tg 971, tg 6236, tg 76787, tg 82052]],
      [tg 455633, tg 460898, tg 531449, tg 536714]⟩,
    ⟨9, 1, 3, 18,
      [[tg 750, tg 6015, tg 76566, tg 81831], [tg 841, tg 6106, tg 76657, tg 81922], [tg 893, tg 6158, tg 76709, tg 81974], [tg 984, tg 6249, tg 76800, tg 82065]],
      [tg 455646, tg 460911, tg 531462, tg 536727]⟩,
    ⟨9, 1, 4, 22,
      [[tg 763, tg 6028, tg 76579, tg 81844], [tg 854, tg 6119, tg 76670, tg 81935], [tg 906, tg 6171, tg 76722, tg 81987], [tg 997, tg 6262, tg 76813, tg 82078]],
      [tg 455659, tg 460924, tg 531475, tg 536740]⟩,
    ⟨9, 1, 5, 19,
      [[tg 776, tg 6041, tg 76592, tg 81857], [tg 802, tg 6067, tg 76618, tg 81883], [tg 867, tg 6132, tg 76683, tg 81948], [tg 919, tg 6184, tg 76735, tg 82000], [tg 1010, tg 6275, tg 76826, tg 82091]],
      [tg 607304, tg 612569, tg 683120, tg 688385]⟩,
    ⟨9, 1, 6, 21,
      [[tg 789, tg 6054, tg 76605, tg 81870], [tg 815, tg 6080, tg 76631, tg 81896], [tg 880, tg 6145, tg 76696, tg 81961], [tg 932, tg 6197, tg 76748, tg 82013], [tg 1023, tg 6288, tg 76839, tg 82104]],
      [tg 607317, tg 612582, tg 683133, tg 688398]⟩,
    ⟨9, 1, 7, 20,
      [[tg 802, tg 6067, tg 76618, tg 81883], [tg 893, tg 6158, tg 76709, tg 81974], [tg 932, tg 6197, tg 76748, tg 82013], [tg 1010, tg 6275, tg 76826, tg 82091], [tg 1036, tg 6301, tg 76852, tg 82117]],
      [tg 607330, tg 612595, tg 683146, tg 688411]⟩,
    ⟨9, 1, 8, 21,
      [[tg 815, tg 6080, tg 76631, tg 81896], [tg 906, tg 6171, tg 76722, tg 81987], [tg 919, tg 6184, tg 76735, tg 82000], [tg 1023, tg 6288, tg 76839, tg 82104], [tg 1049, tg 6314, tg 76865, tg 82130]],
      [tg 607343, tg 612608, tg 683159, tg 688424]⟩,
    ⟨10, 1, 0, 17,
      [[tg 828, tg 6093, tg 76644, tg 81909], [tg 4241, tg 9506, tg 29519, tg 34784], [tg 958, tg 6223, tg 76774, tg 82039], [tg 4221, tg 9486, tg 80037, tg 85302]],
      [tg 455724, tg 460989, tg 531540, tg 536805]⟩,
    ⟨10, 1, 1, 18,
      [[tg 841, tg 6106, tg 76657, tg 81922], [tg 945, tg 6210, tg 76761, tg 82026], [tg 984, tg 6249, tg 76800, tg 82065], [tg 4234, tg 9499, tg 80050, tg 85315]],
      [tg 455737, tg 461002, tg 531553, tg 536818]⟩,
    ⟨10, 1, 2, 24,
      [[tg 854, tg 6119, tg 76670, tg 81935], [tg 997, tg 6262, tg 76813, tg 82078], [tg 51372, tg 56637, tg 127188, tg 132453], [tg 4247, tg 9512, tg 80063, tg 85328]],
      [tg 455750, tg 461015, tg 531566, tg 536831]⟩,
    ⟨10, 1, 3, 19,
      [[tg 867, tg 6132, tg 76683, tg 81948], [tg 958, tg 6223, tg 76774, tg 82039], [tg 1010, tg 6275, tg 76826, tg 82091], [tg 4260, tg 9525, tg 80076, tg 85341]],
      [tg 455763, tg 461028, tg 531579, tg 536844]⟩,
    ⟨10, 1, 4, 23,
      [[tg 880, tg 6145, tg 76696, tg 81961], [tg 971, tg 6236, tg 76787, tg 82052], [tg 1023, tg 6288, tg 76839, tg 82104], [tg 4273, tg 9538, tg 80089, tg 85354]],
      [tg 455776, tg 461041, tg 531592, tg 536857]⟩,
    ⟨10, 1, 5, 20,
      [[tg 893, tg 6158, tg 76709, tg 81974], [tg 919, tg 6184, tg 76735, tg 82000], [tg 984, tg 6249, tg 76800, tg 82065], [tg 1036, tg 6301, tg 76852, tg 82117], [tg 4286, tg 9551, tg 80102, tg 85367]],
      [tg 607421, tg 612686, tg 683237, tg 688502]⟩,
    ⟨10, 1, 6, 22,
      [[tg 906, tg 6171, tg 76722, tg 81987], [tg 932, tg 6197, tg 76748, tg 82013], [tg 997, tg 6262, tg 76813, tg 82078], [tg 1049, tg 6314, tg 76865, tg 82130], [tg 4299, tg 9564, tg 80115, tg 85380]],
      [tg 607434, tg 612699, tg 683250, tg 688515]⟩,
    ⟨10, 1, 7, 21,
      [[tg 919, tg 6184, tg 76735, tg 82000], [tg 1010, tg 6275, tg 76826, tg 82091], [tg 1049, tg 6314, tg 76865, tg 82130], [tg 4286, tg 9551, tg 80102, tg 85367], [tg 4312, tg 9577, tg 80128, tg 85393]],
      [tg 607447, tg 612712, tg 683263, tg 688528]⟩,
    ⟨10, 1, 8, 22,
      [[tg 932, tg 6197, tg 76748, tg 82013], [tg 1023, tg 6288, tg 76839, tg 82104], [tg 1036, tg 6301, tg 76852, tg 82117], [tg 4299, tg 9564, tg 80115, tg 85380], [tg 4325, tg 9590, tg 80141, tg 85406]],
      [tg 607460, tg 612725, tg 683276, tg 688541]⟩]⟩,
  ⟨2, 1, 1, -1, 1, [(1, 1, 1), (-1, 1, 1)], 1, 1, 1, 2, -1, 1, 1, 2,
   [⟨0, 1, 0, 8,
      [[tg 5, tg 1180, tg 6323, tg 76996], [tg 26, tg 1083, tg 2137, tg 26478], [tg 23, tg 5288, tg 75839, tg 81104], [tg 4, tg 5269, tg 25399, tg 30664]],
      [tg 303290, tg 304347, tg 305401, tg 329742]⟩,
    ⟨0, 1, 1, 9,
      [[tg 18, tg 1193, tg 6336, tg 77009], [tg 10, tg 5275, tg 75826, tg 81091], [tg 49, tg 5314, tg 75865, tg 81130], [tg 17, tg 5282, tg 25412, tg 30677]],
      [tg 303274, tg 308539, tg 379090, tg 384355]⟩,
    ⟨0, 1, 2, 16,
      [[tg 31, tg 1206, tg 6349, tg 77022], [tg 62, tg 5327, tg 75878, tg 81143], [tg 127, tg 5392, tg 75943, tg 81208], [tg 30, tg 5295, tg 25425, tg 30690]],
      [tg 151694, tg 156959, tg 227510, tg 232775]⟩,
    ⟨0, 1, 3, 10,
      [[tg 44, tg 1219, tg 6362, tg 77035], [tg 23, tg 5288, tg 75839, tg 81104], [tg 75, tg 5340, tg 75891, tg 81156], [tg 43, tg 5308, tg 25438, tg 30703]],
      [tg 303287, tg 308552, tg 379103, tg 384368]⟩,
    ⟨0, 1, 4, 15,
      [[tg 57, tg 1232, tg 6375, tg 77048], [tg 36, tg 5301, tg 75852, tg 81117], [tg 88, tg 5353, tg 75904, tg 81169], [tg 56, tg 5321, tg 25451, tg 30716]],
      [tg 303352, tg 308617, tg 379168, tg 384433]⟩,
    ⟨0, 1, 5, 11,
      [[tg 70, tg 1245, tg 6388, tg 77061], [tg 96, tg 1271, tg 6414, tg 77087], [tg 49, tg 5314, tg 75865, tg 81130], [tg 101, tg 5366, tg 75917, tg 81182], [tg 69, tg 5334, tg 25464, tg 30729]],
      [tg 303313, tg 308578, tg 379129, tg 384394]⟩,
    ⟨0, 1, 6, 14,
      [[tg 83, tg 1258, tg 6401, tg 77074], [tg 109, tg 1284, tg 6427, tg 77100], [tg 62, tg 5327, tg 75878, tg 81143], [tg 114, tg 5379, tg 75930, tg 81195], [tg 82, tg 5347, tg 25477, tg 30742]],
      [tg 455005, tg 456180, tg 461323, tg 531996]⟩,
    ⟨0, 1, 7, 12,
      [[tg 96, tg 1271, tg 6414, tg 77087], [tg 75, tg 5340, tg 75891, tg 81156], [tg 114, tg 5379, tg 75930, tg 81195], [tg 69, tg 5334, tg 25464, tg 30729], [tg 95, tg 5360, tg 25490, tg 30755]],
      [tg 454971, tg 460236, tg 530787, tg 536052]⟩,
    ⟨0, 1, 8, 13,
      [[tg 109, tg 1284, tg 6427, tg 77100], [tg 88, tg 5353, tg 75904, tg 81169], [tg 101, tg 5366, tg 75917, tg 81182], [tg 82, tg 5347, tg 25477, tg 30742], [tg 108, tg 5373, tg 25503, tg 30768]],
      [tg 303365, tg 308630, tg 379181, tg 384446]⟩,
    ⟨0, 2, 0, 17,
      [[tg 50554, tg 55819, tg 126370, tg 131635], [tg 36, tg 5301, tg 75852, tg 81117], [tg 140, tg 5405, tg 75956, tg 81221], [tg 4222, tg 9487, tg 80038, tg 85303]],
      [tg 303300, tg 308565, tg 379116, tg 384381]⟩,
    ⟨0, 2, 1, 18,
      [[tg 50567, tg 55832, tg 126383, tg 131648], [tg 127, tg 5392, tg 75943, tg 81208], [tg 166, tg 5431, tg 75982, tg 81247], [tg 4235, tg 9500, tg 80051, tg 85316]],
      [tg 303391, tg 308656, tg 379207, tg 384472]⟩,
    ⟨0, 2, 2, 25,
      [[tg 50580, tg 55845, tg 126396, tg 131661], [tg 179, tg 5444, tg 75995, tg 81260], [tg 54766, tg 60031, tg 130582, tg 135847], [tg 4248, tg 9513, tg 80064, tg 85329]],
      [tg 151811, tg 157076, tg 227627, tg 232892]⟩,
    ⟨0, 2, 3, 19,
      [[tg 50593, tg 55858, tg 126409, tg 131674], [tg 140, tg 5405, tg 75956, tg 81221], [tg 192, tg 5457, tg 76008, tg 81273], [tg 4261, tg 9526, tg 80077, tg 85342]],
      [tg 303404, tg 308669, tg 379220, tg 384485]⟩,
    ⟨0, 2, 4, 24,
      [[tg 50606, tg 55871, tg 126422, tg 131687], [tg 153, tg 5418, tg 75969, tg 81234], [tg 205, tg 5470, tg 76021, tg 81286], [tg 4274, tg 9539, tg 80090, tg 85355]],
      [tg 303469, tg 308734, tg 379285, tg 384550]⟩,
    ⟨0, 2, 5, 20,
      [[tg 50619, tg 55884, tg 126435, tg 131700], [tg 50645, tg 55910, tg 126461, tg 131726], [tg 166, tg 5431, tg 75982, tg 81247], [tg 218, tg 5483, tg 76034, tg 81299], [tg 4287, tg 9552, tg 80103, tg 85368]],
      [tg 303430, tg 308695, tg 379246, tg 384511]⟩,
    ⟨0, 2, 6, 23,
      [[tg 50632, tg 55897, tg 126448, tg 131713], [tg 50658, tg 55923, tg 126474, tg 131739], [tg 179, tg 5444, tg 75995, tg 81260], [tg 231, tg 5496, tg 76047, tg 81312], [tg 4300, tg 9565, tg 80116, tg 85381]],
      [tg 505554, tg 510819, tg 581370, tg 586635]⟩,
    ⟨0, 2, 7, 21,
      [[tg 50645, tg 55910, tg 126461, tg 131726], [tg 192, tg 5457, tg 76008, tg 81273], [tg 231, tg 5496, tg 76047, tg 81312], [tg 4287, tg 9552, tg 80103, tg 85368], [tg 4313, tg 9578, tg 80129, tg 85394]],
      [tg 455088, tg 460353, tg 530904, tg 536169]⟩,
    ⟨0, 2, 8, 22,
      [[tg 50658, tg 55923, tg 126474, tg 131739], [tg 205, tg 5470, tg 76021, tg 81286], [tg 218, tg 5483, tg 76034, tg 81299], [tg 4300, tg 9565, tg 80116, tg 85381], [tg 4326, tg 9591, tg 80142, tg 85407]],
      [tg 303482, tg 308747, tg 379298, tg 384563]⟩]⟩,
  ⟨2, -1, 1, -9, 0, [(0, 9, 1), (-1, -1, 1)], 0, 9, 1, 9, -1, -1, 1, 9,
   [⟨-10, 1, 0, 17,
      [[tg 51491, tg 56756, tg 127307, tg 132572], [tg 4244, tg 52570, tg 10562, tg 128386], [tg 24, tg 5289, tg 75840, tg 81105], [tg 128, tg 5393, tg 75944, tg 81209]],
      [tg 307508, tg 355834, tg 313826, tg 431650]⟩,
    ⟨-10, 1, 1, 18,
      [[tg 51504, tg 56769, tg 127320, tg 132585], [tg 11, tg 5276, tg 75827, tg 81092], [tg 50, tg 5315, tg 75866, tg 81131], [tg 141, tg 5406, tg 75957, tg 81222]],
      [tg 303275, tg 308540, tg 379091, tg 384356]⟩,
    ⟨-10, 1, 2, 24,
      [[tg 51517, tg 56782, tg 127333, tg 132598], [tg 63, tg 5328, tg 75879, tg 81144], [tg 4340, tg 9605, tg 80156, tg 85421], [tg 154, tg 5419, tg 75970, tg 81235]],
      [tg 151695, tg 156960, tg 227511, tg 232776]⟩,
    ⟨-10, 1, 3, 19,
      [[tg 51530, tg 56795, tg 127346, tg 132611], [tg 24, tg 5289, tg 75840, tg 81105], [tg 76, tg 5341, tg 75892, tg 81157], [tg 167, tg 5432, tg 75983, tg 81248]],
      [tg 303288, tg 308553, tg 379104, tg 384369]⟩,
    ⟨-10, 1, 4, 23,
      [[tg 51543, tg 56808, tg 127359, tg 132624], [tg 37, tg 5302, tg 75853, tg 81118], [tg 89, tg 5354, tg 75905, tg 81170], [tg 180, tg 5445, tg 75996, tg 81261]],
      [tg 303353, tg 308618, tg 379169, tg 384434]⟩,
    ⟨-10, 1, 5, 20,
      [[tg 51556, tg 56821, tg 127372, tg 132637], [tg 51582, tg 56847, tg 127398, tg 132663], [tg 50, tg 5315, tg 75866, tg 81131], [tg 102, tg 5367, tg 75918, tg 81183], [tg 193, tg 5458, tg 76009, tg 81274]],
      [tg 303314, tg 308579, tg 379130, tg 384395]⟩,
    ⟨-10, 1, 6, 22,
      [[tg 51569, tg 56834, tg 127385, tg 132650], [tg 51595, tg 56860, tg 127411, tg 132676], [tg 63, tg 5328, tg 75879, tg 81144], [tg 115, tg 5380, tg 75931, tg 81196], [tg 206, tg 5471, tg 76022, tg 81287]],
      [tg 151747, tg 157012, tg 227563, tg 232828]⟩,
    ⟨-10, 1, 7, 20,
      [[tg 51582, tg 56847, tg 127398, tg 132663], [tg 76, tg 5341, tg 75892, tg 81157], [tg 115, tg 5380, tg 75931, tg 81196], [tg 193, tg 5458, tg 76009, tg 81274], [tg 219, tg 5484, tg 76035, tg 81300]],
      [tg 151825, tg 157090, tg 227641, tg 232906]⟩,
    ⟨-10, 1, 8, 21,
      [[tg 51595, tg 56860, tg 127411, tg 132676], [tg 89, tg 5354, tg 75905, tg 81170], [tg 102, tg 5367, tg 75918, tg 81183], [tg 206, tg 5471, tg 76022, tg 81287], [tg 232, tg 5497, tg 76048, tg 81313]],
      [tg 303366, tg 308631, tg 379182, tg 384447]⟩,
    ⟨-9, 1, 0, 16,
      [[tg 11, tg 5276, tg 75827, tg 81092], [tg 968, tg 1090, tg 7286, tg 76906], [tg 141, tg 5406, tg 75957, tg 81222], [tg 245, tg 5510, tg 76061, tg 81326]],
      [tg 304232, tg 304354, tg 310550, tg 380170]⟩,
    ⟨-9, 1, 1, 17,
      [[tg 24, tg 5289, tg 75840, tg 81105], [tg 128, tg 5393, tg 75944, tg 81209], [tg 167, tg 5432, tg 75983, tg 81248], [tg 258, tg 5523, tg 76074, tg 81339]],
      [tg 303392, tg 308657, tg 379208, tg 384473]⟩,
    ⟨-9, 1, 2, 23,
      [[tg 37, tg 5302, tg 75853, tg 81118], [tg 180, tg 5445, tg 75996, tg 81261], [tg 4457, tg 9722, tg 80273, tg 85538], [tg 271, tg 5536, tg 76087, tg 81352]],
      [tg 151812, tg 157077, tg 227628, tg 232893]⟩,
    ⟨-9, 1, 3, 18,
      [[tg 50, tg 5315, tg 75866, tg 81131], [tg 141, tg 5406, tg 75957, tg 81222], [tg 193, tg 5458, tg 76009, tg 81274], [tg 284, tg 5549, tg 76100, tg 81365]],
      [tg 303405, tg 308670, tg 379221, tg 384486]⟩,
    ⟨-9, 1, 4, 22,
      [[tg 63, tg 5328, tg 75879, tg 81144], [tg 154, tg 5419, tg 75970, tg 81235], [tg 206, tg 5471, tg 76022, tg 81287], [tg 297, tg 5562, tg 76113, tg 81378]],
      [tg 303470, tg 308735, tg 379286, tg 384551]⟩,
    ⟨-9, 1, 5, 19,
      [[tg 76, tg 5341, tg 75892, tg 81157], [tg 102, tg 5367, tg 75918, tg 81183], [tg 167, tg 5432, tg 75983, tg 81248], [tg 219, tg 5484, tg 76035, tg 81300], [tg 310, tg 5575, tg 76126, tg 81391]],
      [tg 303431, tg 308696, tg 379247, tg 384512]⟩,
    ⟨-9, 1, 6, 21,
      [[tg 89, tg 5354, tg 75905, tg 81170], [tg 115, tg 5380, tg 75931, tg 81196], [tg 180, tg 5445, tg 75996, tg 81261], [tg 232, tg 5497, tg 76048, tg 81313], [tg 323, tg 5588, tg 76139, tg 81404]],
      [tg 151864, tg 157129, tg 227680, tg 232945]⟩,
    ⟨-9, 1, 7, 19,
      [[tg 102, tg 5367, tg 75918, tg 81183], [tg 193, tg 5458, tg 76009, tg 81274], [tg 232, tg 5497, tg 76048, tg 81313], [tg 310, tg 5575, tg 76126, tg 81391], [tg 336, tg 5601, tg 76152, tg 81417]],
      [tg 151942, tg 157207, tg 227758, tg 233023]⟩,
    ⟨-9, 1, 8, 20,
      [[tg 115, tg 5380, tg 75931, tg 81196], [tg 206, tg 5471, tg 76022, tg 81287], [tg 219, tg 5484, tg 76035, tg 81300], [tg 323, tg 5588, tg 76139, tg 81404], [tg 349, tg 5614, tg 76165, tg 81430]],
      [tg 303483, tg 308748, tg 379299, tg 384564]⟩,
    ⟨-8, 1, 0, 15,
      [[tg 128, tg 5393, tg 75944, tg 81209], [tg 851, tg 1207, tg 7169, tg 77023], [tg 258, tg 5523, tg 76074, tg 81339], [tg 362, tg 5627, tg 76178, tg 81443]],
      [tg 304115, tg 304471, tg 310433, tg 380287]⟩,
    ⟨-8, 1, 1, 16,
      [[tg 141, tg 5406, tg 75957, tg 81222], [tg 245, tg 5510, tg 76061, tg 81326], [tg 284, tg 5549, tg 76100, tg 81365], [tg 375, tg 5640, tg 76191, tg 81456]],
      [tg 303509, tg 308774, tg 379325, tg 384590]⟩,
    ⟨-8, 1, 2, 22,
      [[tg 154, tg 5419, tg 75970, tg 81235], [tg 297, tg 5562, tg 76113, tg 81378], [tg 4574, tg 9839, tg 80390, tg 85655], [tg 388, tg 5653, tg 76204, tg 81469]],
      [tg 151929, tg 157194, tg 227745, tg 233010]⟩,
    ⟨-8, 1, 3, 17,
      [[tg 167, tg 5432, tg 75983, tg 81248], [tg 258, tg 5523, tg 76074, tg 81339], [tg 310, tg 5575, tg 76126, tg 81391], [tg 401, tg 5666, tg 76217, tg 81482]],
      [tg 303522, tg 308787, tg 379338, tg 384603]⟩,
    ⟨-8, 1, 4, 21,
      [[tg 180, tg 5445, tg 75996, tg 81261], [tg 271, tg 5536, tg 76087, tg 81352], [tg 323, tg 5588, tg 76139, tg 81404], [tg 414, tg 5679, tg 76230, tg 81495]],
      [tg 303587, tg 308852, tg 379403, tg 384668]⟩,
    ⟨-8, 1, 5, 18,
      [[tg 193, tg 5458, tg 76009, tg 81274], [tg 219, tg 5484, tg 76035, tg 81300], [tg 284, tg 5549, tg 76100, tg 81365], [tg 336, tg 5601, tg 76152, tg 81417], [tg 427, tg 5692, tg 76243, tg 81508]],
      [tg 303548, tg 308813, tg 379364, tg 384629]⟩,
    ⟨-8, 1, 6, 20,
      [[tg 206, tg 5471, tg 76022, tg 81287], [tg 232, tg 5497, tg 76048, tg 81313], [tg 297, tg 5562, tg 76113, tg 81378], [tg 349, tg 5614, tg 76165, tg 81430], [tg 440, tg 5705, tg 76256, tg 81521]],
      [tg 151981, tg 157246, tg 227797, tg 233062]⟩,
    ⟨-8, 1, 7, 18,
      [[tg 219, tg 5484, tg 76035, tg 81300], [tg 310, tg 5575, tg 76126, tg 81391], [tg 349, tg 5614, tg 76165, tg 81430], [tg 427, tg 5692, tg 76243, tg 81508], [tg 453, tg 5718, tg 76269, tg 81534]],
      [tg 152059, tg 157324, tg 227875, tg 233140]⟩,
    ⟨-8, 1, 8, 19,
      [[tg 232, tg 5497, tg 76048, tg 81313], [tg 323, tg 5588, tg 76139, tg 81404], [tg 336, tg 5601, tg 76152, tg 81417], [tg 440, tg 5705, tg 76256, tg 81521], [tg 466, tg 5731, tg 76282, tg 81547]],
      [tg 303600, tg 308865, tg 379416, tg 384681]⟩,
    ⟨-7, 1, 0, 14,
      [[tg 245, tg 5510, tg 76061, tg 81326], [tg 734, tg 1324, tg 7052, tg 77140], [tg 375, tg 5640, tg 76191, tg 81456], [tg 479, tg 5744, tg 76295, tg 81560]],
      [tg 303998, tg 304588, tg 310316, tg 380404]⟩,
    ⟨-7, 1, 1, 15,
      [[tg 258, tg 5523, tg 76074, tg 81339], [tg 362, tg 5627, tg 76178, tg 81443], [tg 401, tg 5666, tg 76217, tg 81482], [tg 492, tg 5757, tg 76308, tg 81573]],
      [tg 303626, tg 308891, tg 379442, tg 384707]⟩,
    ⟨-7, 1, 2, 21,
      [[tg 271, tg 5536, tg 76087, tg 81352], [tg 414, tg 5679, tg 76230, tg 81495], [tg 4691, tg 9956, tg 80507, tg 85772], [tg 505, tg 5770, tg 76321, tg 81586]],
      [tg 152046, tg 157311, tg 227862, tg 233127]⟩,
    ⟨-7, 1, 3, 16,
      [[tg 284, tg 5549, tg 76100, tg 81365], [tg 375, tg 5640, tg 76191, tg 81456], [tg 427, tg 5692, tg 76243, tg 81508], [tg 518, tg 5783, tg 76334, tg 81599]],
      [tg 303639, tg 308904, tg 379455, tg 384720]⟩,
    ⟨-7, 1, 4, 20,
      [[tg 297, tg 5562, tg 76113, tg 81378], [tg 388, tg 5653, tg 76204, tg 81469], [tg 440, tg 5705, tg 76256, tg 81521], [tg 531, tg 5796, tg 76347, tg 81612]],
      [tg 303704, tg 308969, tg 379520, tg 384785]⟩,
    ⟨-7, 1, 5, 17,
      [[tg 310, tg 5575, tg 76126, tg 81391], [tg 336, tg 5601, tg 76152, tg 81417], [tg 401, tg 5666, tg 76217, tg 81482], [tg 453, tg 5718, tg 76269, tg 81534], [tg 544, tg 5809, tg 76360, tg 81625]],
      [tg 303665, tg 308930, tg 379481, tg 384746]⟩,
    ⟨-7, 1, 6, 19,
      [[tg 323, tg 5588, tg 76139, tg 81404], [tg 349, tg 5614, tg 76165, tg 81430], [tg 414, tg 5679, tg 76230, tg 81495], [tg 466, tg 5731, tg 76282, tg 81547], [tg 557, tg 5822, tg 76373, tg 81638]],
      [tg 152098, tg 157363, tg 227914, tg 233179]⟩,
    ⟨-7, 1, 7, 17,
      [[tg 336, tg 5601, tg 76152, tg 81417], [tg 427, tg 5692, tg 76243, tg 81508], [tg 466, tg 5731, tg 76282, tg 81547], [tg 544, tg 5809, tg 76360, tg 81625], [tg 570, tg 5835, tg 76386, tg 81651]],
      [tg 152176, tg 157441, tg 227992, tg 233257]⟩,
    ⟨-7, 1, 8, 18,
      [[tg 349, tg 5614, tg 76165, tg 81430], [tg 440, tg 5705, tg 76256, tg 81521], [tg 453, tg 5718, tg 76269, tg 81534], [tg 557, tg 5822, tg 76373, tg 81638], [tg 583, tg 5848, tg 76399, tg 81664]],
      [tg 303717, tg 308982, tg 379533, tg 384798]⟩,
    ⟨-6, 1, 0, 13,
      [[tg 362, tg 5627, tg 76178, tg 81443], [tg 617, tg 1441, tg 6935, tg 77257], [tg 492, tg 5757, tg 76308, tg 81573], [tg 596, tg 5861, tg 76412, tg 81677]],
      [tg 303881, tg 304705, tg 310199, tg 380521]⟩,
    ⟨-6, 1, 1, 14,
      [[tg 375, tg 5640, tg 76191, tg 81456], [tg 479, tg 5744, tg 76295, tg 81560], [tg 518, tg 5783, tg 76334, tg 81599], [tg 609, tg 5874, tg 76425, tg 81690]],
      [tg 303743, tg 309008, tg 379559, tg 384824]⟩,
    ⟨-6, 1, 2, 20,
      [[tg 388, tg 5653, tg 76204, tg 81469], [tg 531, tg 5796, tg 76347, tg 81612], [tg 4808, tg 10073, tg 80624, tg 85889], [tg 622, tg 5887, tg 76438, tg 81703]],
      [tg 152163, tg 157428, tg 227979, tg 233244]⟩,
    ⟨-6, 1, 3, 15,
      [[tg 401, tg 5666, tg 76217, tg 81482], [tg 492, tg 5757, tg 76308, tg 81573], [tg 544, tg 5809, tg 76360, tg 81625], [tg 635, tg 5900, tg 76451, tg 81716]],
      [tg 303756, tg 309021, tg 379572, tg 384837]⟩,
    ⟨-6, 1, 4, 19,
      [[tg 414, tg 5679, tg 76230, tg 81495], [tg 505, tg 5770, tg 76321, tg 81586], [tg 557, tg 5822, tg 76373, tg 81638], [tg 648, tg 5913, tg 76464, tg 81729]],
      [tg 303821, tg 309086, tg 379637, tg 384902]⟩,
    ⟨-6, 1, 5, 16,
      [[tg 427, tg 5692, tg 76243, tg 81508], [tg 453, tg 5718, tg 76269, tg 81534], [tg 518, tg 5783, tg 76334, tg 81599], [tg 570, tg 5835, tg 76386, tg 81651], [tg 661, tg 5926, tg 76477, tg 81742]],
      [tg 303782, tg 309047, tg 379598, tg 384863]⟩,
    ⟨-6, 1, 6, 18,
      [[tg 440, tg 5705, tg 76256, tg 81521], [tg 466, tg 5731, tg 76282, tg 81547], [tg 531, tg 5796, tg 76347, tg 81612], [tg 583, tg 5848, tg 76399, tg 81664], [tg 674, tg 5939, tg 76490, tg 81755]],
      [tg 152215, tg 157480, tg 228031, tg 233296]⟩,
    ⟨-6, 1, 7, 16,
      [[tg 453, tg 5718, tg 76269, tg 81534], [tg 544, tg 5809, tg 76360, tg 81625], [tg 583, tg 5848, tg 76399, tg 81664], [tg 661, tg 5926, tg 76477, tg 81742], [tg 687, tg 5952, tg 76503, tg 81768]],
      [tg 152293, tg 157558, tg 228109, tg 233374]⟩,
    ⟨-6, 1, 8, 17,
      [[tg 466, tg 5731, tg 76282, tg 81547], [tg 557, tg 5822, tg 76373, tg 81638], [tg 570, tg 5835, tg 76386, tg 81651], [tg 674, tg 5939, tg 76490, tg 81755], [tg 700, tg 5965, tg 76516, tg 81781]],
      [tg 303834, tg 309099, tg 379650, tg 384915]⟩,
    ⟨-5, 1, 0, 12,
      [[tg 479, tg 5744, tg 76295, tg 81560], [tg 500, tg 1558, tg 6818, tg 77374], [tg 609, tg 5874, tg 76425, tg 81690], [tg 713, tg 5978, tg 76529, tg 81794]],
      [tg 303764, tg 304822, tg 310082, tg 380638]⟩,
    ⟨-5, 1, 1, 13,
      [[tg 492, tg 5757, tg 76308, tg 81573], [tg 596, tg 5861, tg 76412, tg 81677], [tg 635, tg 5900, tg 76451, tg 81716], [tg 726, tg 5991, tg 76542, tg 81807]],
      [tg 303860, tg 309125, tg 379676, tg 384941]⟩,
    ⟨-5, 1, 2, 19,
      [[tg 505, tg 5770, tg 76321, tg 81586], [tg 648, tg 5913, tg 76464, tg 81729], [tg 4925, tg 10190, tg 80741, tg 86006], [tg 739, tg 6004, tg 76555, tg 81820]],
      [tg 152280, tg 157545, tg 228096, tg 233361]⟩,
    ⟨-5, 1, 3, 14,
      [[tg 518, tg 5783, tg 76334, tg 81599], [tg 609, tg 5874, tg 76425, tg 81690], [tg 661, tg 5926, tg 76477, tg 81742], [tg 752, tg 6017, tg 76568, tg 81833]],
      [tg 303873, tg 309138, tg 379689, tg 384954]⟩,
    ⟨-5, 1, 4, 18,
      [[tg 531, tg 5796, tg 76347, tg 81612], [tg 622, tg 5887, tg 76438, tg 81703], [tg 674, tg 5939, tg 76490, tg 81755], [tg 765, tg 6030, tg 76581, tg 81846]],
      [tg 303938, tg 309203, tg 379754, tg 385019]⟩,
    ⟨-5, 1, 5, 15,
      [[tg 544, tg 5809, tg 76360, tg 81625], [tg 570, tg 5835, tg 76386, tg 81651], [tg 635, tg 5900, tg 76451, tg 81716], [tg 687, tg 5952, tg 76503, tg 81768], [tg 778, tg 6043, tg 76594, tg 81859]],
      [tg 303899, tg 309164, tg 379715, tg 384980]⟩,
    ⟨-5, 1, 6, 17,
      [[tg 557, tg 5822, tg 76373, tg 81638], [tg 583, tg 5848, tg 76399, tg 81664], [tg 648, tg 5913, tg 76464, tg 81729], [tg 700, tg 5965, tg 76516, tg 81781], [tg 791, tg 6056, tg 76607, tg 81872]],
      [tg 152332, tg 157597, tg 228148, tg 233413]⟩,
    ⟨-5, 1, 7, 15,
      [[tg 570, tg 5835, tg 76386, tg 81651], [tg 661, tg 5926, tg 76477, tg 81742], [tg 700, tg 5965, tg 76516, tg 81781], [tg 778, tg 6043, tg 76594, tg 81859], [tg 804, tg 6069, tg 76620, tg 81885]],
      [tg 152410, tg 157675, tg 228226, tg 233491]⟩,
    ⟨-5, 1, 8, 16,
      [[tg 583, tg 5848, tg 76399, tg 81664], [tg 674, tg 5939, tg 76490, tg 81755], [tg 687, tg 5952, tg 76503, tg 81768], [tg 791, tg 6056, tg 76607, tg 81872], [tg 817, tg 6082, tg 76633, tg 81898]],
      [tg 303951, tg 309216, tg 379767, tg 385032]⟩,
    ⟨-4, 1, 0, 11,
      [[tg 596, tg 5861, tg 76412, tg 81677], [tg 383, tg 1675, tg 6701, tg 77491], [tg 726, tg 5991, tg 76542, tg 81807], [tg 830, tg 6095, tg 76646, tg 81911]],
      [tg 303647, tg 304939, tg 309965, tg 380755]⟩,
    ⟨-4, 1, 1, 12,
      [[tg 609, tg 5874, tg 76425, tg 81690], [tg 713, tg 5978, tg 76529, tg 81794], [tg 752, tg 6017, tg 76568, tg 81833], [tg 843, tg 6108, tg 76659, tg 81924]],
      [tg 303977, tg 309242, tg 379793, tg 385058]⟩,
    ⟨-4, 1, 2, 18,
      [[tg 622, tg 5887, tg 76438, tg 81703], [tg 765, tg 6030, tg 76581, tg 81846], [tg 5042, tg 10307, tg 80858, tg 86123], [tg 856, tg 6121, tg 76672, tg 81937]],
      [tg 152397, tg 157662, tg 228213, tg 233478]⟩,
    ⟨-4, 1, 3, 13,
      [[tg 635, tg 5900, tg 76451, tg 81716], [tg 726, tg 5991, tg 76542, tg 81807], [tg 778, tg 6043, tg 76594, tg 81859], [tg 869, tg 6134, tg 76685, tg 81950]],
      [tg 303990, tg 309255, tg 379806, tg 385071]⟩,
    ⟨-4, 1, 4, 17,
      [[tg 648, tg 5913, tg 76464, tg 81729], [tg 739, tg 6004, tg 76555, tg 81820], [tg 791, tg 6056, tg 76607, tg 81872], [tg 882, tg 6147, tg 76698, tg 81963]],
      [tg 304055, tg 309320, tg 379871, tg 385136]⟩,
    ⟨-4, 1, 5, 14,
      [[tg 661, tg 5926, tg 76477, tg 81742], [tg 687, tg 5952, tg 76503, tg 81768], [tg 752, tg 6017, tg 76568, tg 81833], [tg 804, tg 6069, tg 76620, tg 81885], [tg 895, tg 6160, tg 76711, tg 81976]],
      [tg 304016, tg 309281, tg 379832, tg 385097]⟩,
    ⟨-4, 1, 6, 16,
      [[tg 674, tg 5939, tg 76490, tg 81755], [tg 700, tg 5965, tg 76516, tg 81781], [tg 765, tg 6030, tg 76581, tg 81846], [tg 817, tg 6082, tg 76633, tg 81898], [tg 908, tg 6173, tg 76724, tg 81989]],
      [tg 152449, tg 157714, tg 228265, tg 233530]⟩,
    ⟨-4, 1, 7, 14,
      [[tg 687, tg 5952, tg 76503, tg 81768], [tg 778, tg 6043, tg 76594, tg 81859], [tg 817, tg 6082, tg 76633, tg 81898], [tg 895, tg 6160, tg 76711, tg 81976], [tg 921, tg 6186, tg 76737, tg 82002]],
      [tg 152527, tg 157792, tg 228343, tg 233608]⟩,
    ⟨-4, 1, 8, 15,
      [[tg 700, tg 5965, tg 76516, tg 81781], [tg 791, tg 6056, tg 76607, tg 81872], [tg 804, tg 6069, tg 76620, tg 81885], [tg 908, tg 6173, tg 76724, tg 81989], [tg 934, tg 6199, tg 76750, tg 82015]],
      [tg 304068, tg 309333, tg 379884, tg 385149]⟩,
    ⟨-3, 1, 0, 10,
      [[tg 713, tg 5978, tg 76529, tg 81794], [tg 266, tg 1792, tg 6584, tg 77608], [tg 843, tg 6108, tg 76659, tg 81924], [tg 947, tg 6212, tg 76763, tg 82028]],
      [tg 303530, tg 305056, tg 309848, tg 380872]⟩,
    ⟨-3, 1, 1, 11,
      [[tg 726, tg 5991, tg 76542, tg 81807], [tg 830, tg 6095, tg 76646, tg 81911], [tg 869, tg 6134, tg 76685, tg 81950], [tg 960, tg 6225, tg 76776, tg 82041]],
      [tg 304094, tg 309359, tg 379910, tg 385175]⟩,
    ⟨-3, 1, 2, 17,
      [[tg 739, tg 6004, tg 76555, tg 81820], [tg 882, tg 6147, tg 76698, tg 81963], [tg 5159, tg 10424, tg 80975, tg 86240], [tg 973, tg 6238, tg 76789, tg 82054]],
      [tg 152514, tg 157779, tg 228330, tg 233595]⟩,
    ⟨-3, 1, 3, 12,
      [[tg 752, tg 6017, tg 76568, tg 81833], [tg 843, tg 6108, tg 76659, tg 81924], [tg 895, tg 6160, tg 76711, tg 81976], [tg 986, tg 6251, tg 76802, tg 82067]],
      [tg 304107, tg 309372, tg 379923, tg 385188]⟩,
    ⟨-3, 1, 4, 16,
      [[tg 765, tg 6030, tg 76581, tg 81846], [tg 856, tg 6121, tg 76672, tg 81937], [tg 908, tg 6173, tg 76724, tg 81989], [tg 999, tg 6264, tg 76815, tg 82080]],
      [tg 304172, tg 309437, tg 379988, tg 385253]⟩,
    ⟨-3, 1, 5, 13,
      [[tg 778, tg 6043, tg 76594, tg 81859], [tg 804, tg 6069, tg 76620, tg 81885], [tg 869, tg 6134, tg 76685, tg 81950], [tg 921, tg 6186, tg 76737, tg 82002], [tg 1012, tg 6277, tg 76828, tg 82093]],
      [tg 304133, tg 309398, tg 379949, tg 385214]⟩,
    ⟨-3, 1, 6, 15,
      [[tg 791, tg 6056, tg 76607, tg 81872], [tg 817, tg 6082, tg 76633, tg 81898], [tg 882, tg 6147, tg 76698, tg 81963], [tg 934, tg 6199, tg 76750, tg 82015], [tg 1025, tg 6290, tg 76841, tg 82106]],
      [tg 152566, tg 157831, tg 228382, tg 233647]⟩,
    ⟨-3, 1, 7, 13,
      [[tg 804, tg 6069, tg 76620, tg 81885], [tg 895, tg 6160, tg 76711, tg 81976], [tg 934, tg 6199, tg 76750, tg 82015], [tg 1012, tg 6277, tg 76828, tg 82093], [tg 1038, tg 6303, tg 76854, tg 82119]],
      [tg 152644, tg 157909, tg 228460, tg 233725]⟩,
    ⟨-3, 1, 8, 14,
      [[tg 817, tg 6082, tg 76633, tg 81898], [tg 908, tg 6173, tg 76724, tg 81989], [tg 921, tg 6186, tg 76737, tg 82002], [tg 1025, tg 6290, tg 76841, tg 82106], [tg 1051, tg 6316, tg 76867, tg 82132]],
      [tg 304185, tg 309450, tg 380001, tg 385266]⟩,
    ⟨-2, 1, 0, 9,
      [[tg 830, tg 6095, tg 76646, tg 81911], [tg 149, tg 1909, tg 6467, tg 77725], [tg 960, tg 6225, tg 76776, tg 82041], [tg 5, tg 5270, tg 25283, tg 30548]],
      [tg 303413, tg 305173, tg 309731, tg 380989]⟩,
    ⟨-2, 1, 1, 10,
      [[tg 843, tg 6108, tg 76659, tg 81924], [tg 947, tg 6212, tg 76763, tg 82028], [tg 986, tg 6251, tg 76802, tg 82067], [tg 18, tg 5283, tg 25296, tg 30561]],
      [tg 304211, tg 309476, tg 380027, tg 385292]⟩,
    ⟨-2, 1, 2, 16,
      [[tg 856, tg 6121, tg 76672, tg 81937], [tg 999, tg 6264, tg 76815, tg 82080], [tg 4217, tg 9482, tg 29495, tg 34760], [tg 31, tg 5296, tg 25309, tg 30574]],
      [tg 152631, tg 157896, tg 228447, tg 233712]⟩,
    ⟨-2, 1, 3, 11,
      [[tg 869, tg 6134, tg 76685, tg 81950], [tg 960, tg 6225, tg 76776, tg 82041], [tg 1012, tg 6277, tg 76828, tg 82093], [tg 44, tg 5309, tg 25322, tg 30587]],
      [tg 304224, tg 309489, tg 380040, tg 385305]⟩,
    ⟨-2, 1, 4, 15,
      [[tg 882, tg 6147, tg 76698, tg 81963], [tg 973, tg 6238, tg 76789, tg 82054], [tg 1025, tg 6290, tg 76841, tg 82106], [tg 57, tg 5322, tg 25335, tg 30600]],
      [tg 304289, tg 309554, tg 380105, tg 385370]⟩,
    ⟨-2, 1, 5, 12,
      [[tg 895, tg 6160, tg 76711, tg 81976], [tg 921, tg 6186, tg 76737, tg 82002], [tg 986, tg 6251, tg 76802, tg 82067], [tg 1038, tg 6303, tg 76854, tg 82119], [tg 70, tg 5335, tg 25348, tg 30613]],
      [tg 304250, tg 309515, tg 380066, tg 385331]⟩,
    ⟨-2, 1, 6, 14,
      [[tg 908, tg 6173, tg 76724, tg 81989], [tg 934, tg 6199, tg 76750, tg 82015], [tg 999, tg 6264, tg 76815, tg 82080], [tg 1051, tg 6316, tg 76867, tg 82132], [tg 83, tg 5348, tg 25361, tg 30626]],
      [tg 152683, tg 157948, tg 228499, tg 233764]⟩,
    ⟨-2, 1, 7, 12,
      [[tg 921, tg 6186, tg 76737, tg 82002], [tg 1012, tg 6277, tg 76828, tg 82093], [tg 1051, tg 6316, tg 76867, tg 82132], [tg 70, tg 5335, tg 25348, tg 30613], [tg 96, tg 5361, tg 25374, tg 30639]],
      [tg 151702, tg 156967, tg 176980, tg 182245]⟩,
    ⟨-2, 1, 8, 13,
      [[tg 934, tg 6199, tg 76750, tg 82015], [tg 1025, tg 6290, tg 76841, tg 82106], [tg 1038, tg 6303, tg 76854, tg 82119], [tg 83, tg 5348, tg 25361, tg 30626], [tg 109, tg 5374, tg 25387, tg 30652]],
      [tg 304302, tg 309567, tg 380118, tg 385383]⟩]⟩,
  ⟨2, -9, 0, -1, -1, [(-1, 1, 1), (0, -9, 1)], -1, 1, 1, 9, 0, -9, 1, 9,
   [⟨-10, -1, 0, 19,
      [[tg 5160, tg 10425, tg 80976, tg 86241], [tg 50699, tg 55964, tg 126515, tg 131780], [tg 25, tg 5290, tg 75841, tg 81106], [tg 129, tg 5394, tg 75945, tg 81210]],
      [tg 151657, tg 156922, tg 227473, tg 232738]⟩,
    ⟨-10, -1, 1, 18,
      [[tg 5173, tg 10438, tg 80989, tg 86254], [tg 12, tg 5277, tg 75828, tg 81093], [tg 51, tg 5316, tg 75867, tg 81132], [tg 142, tg 5407, tg 75958, tg 81223]],
      [tg 151683, tg 156948, tg 227499, tg 232764]⟩,
    ⟨-10, -1, 2, 12,
      [[tg 5186, tg 10451, tg 81002, tg 86267], [tg 64, tg 5329, tg 75880, tg 81145], [tg 4218, tg 9483, tg 30432, tg 35697], [tg 155, tg 5420, tg 75971, tg 81236]],
      [tg 155850, tg 161115, tg 182064, tg 187329]⟩,
    ⟨-10, -1, 3, 17,
      [[tg 5199, tg 10464, tg 81015, tg 86280], [tg 25, tg 5290, tg 75841, tg 81106], [tg 77, tg 5342, tg 75893, tg 81158], [tg 168, tg 5433, tg 75984, tg 81249]],
      [tg 303341, tg 308606, tg 379157, tg 384422]⟩,
    ⟨-10, -1, 4, 13,
      [[tg 5212, tg 10477, tg 81028, tg 86293], [tg 38, tg 5303, tg 75854, tg 81119], [tg 90, tg 5355, tg 75906, tg 81171], [tg 181, tg 5446, tg 75997, tg 81262]],
      [tg 151670, tg 156935, tg 227486, tg 232751]⟩,
    ⟨-10, -1, 5, 16,
      [[tg 5225, tg 10490, tg 81041, tg 86306], [tg 5251, tg 10516, tg 81067, tg 86332], [tg 51, tg 5316, tg 75867, tg 81132], [tg 103, tg 5368, tg 75919, tg 81184], [tg 194, tg 5459, tg 76010, tg 81275]],
      [tg 151735, tg 157000, tg 227551, tg 232816]⟩,
    ⟨-10, -1, 6, 14,
      [[tg 5238, tg 10503, tg 81054, tg 86319], [tg 5264, tg 10529, tg 81080, tg 86345], [tg 64, tg 5329, tg 75880, tg 81145], [tg 116, tg 5381, tg 75932, tg 81197], [tg 207, tg 5472, tg 76023, tg 81288]],
      [tg 303328, tg 308593, tg 379144, tg 384409]⟩,
    ⟨-10, -1, 7, 15,
      [[tg 5251, tg 10516, tg 81067, tg 86332], [tg 77, tg 5342, tg 75893, tg 81158], [tg 116, tg 5381, tg 75932, tg 81197], [tg 194, tg 5459, tg 76010, tg 81275], [tg 220, tg 5485, tg 76036, tg 81301]],
      [tg 303380, tg 308645, tg 379196, tg 384461]⟩,
    ⟨-10, -1, 8, 14,
      [[tg 5264, tg 10529, tg 81080, tg 86345], [tg 90, tg 5355, tg 75906, tg 81171], [tg 103, tg 5368, tg 75919, tg 81184], [tg 207, tg 5472, tg 76023, tg 81288], [tg 233, tg 5498, tg 76049, tg 81314]],
      [tg 151839, tg 157104, tg 227655, tg 232920]⟩,
    ⟨-9, -1, 0, 18,
      [[tg 12, tg 5277, tg 75828, tg 81093], [tg 50816, tg 56081, tg 126632, tg 131897], [tg 142, tg 5407, tg 75958, tg 81223], [tg 246, tg 5511, tg 76062, tg 81327]],
      [tg 151774, tg 157039, tg 227590, tg 232855]⟩,
    ⟨-9, -1, 1, 17,
      [[tg 25, tg 5290, tg 75841, tg 81106], [tg 129, tg 5394, tg 75945, tg 81210], [tg 168, tg 5433, tg 75984, tg 81249], [tg 259, tg 5524, tg 76075, tg 81340]],
      [tg 151800, tg 157065, tg 227616, tg 232881]⟩,
    ⟨-9, -1, 2, 11,
      [[tg 38, tg 5303, tg 75854, tg 81119], [tg 181, tg 5446, tg 75997, tg 81262], [tg 942, tg 6207, tg 25284, tg 30549], [tg 272, tg 5537, tg 76088, tg 81353]],
      [tg 152574, tg 157839, tg 176916, tg 182181]⟩,
    ⟨-9, -1, 3, 16,
      [[tg 51, tg 5316, tg 75867, tg 81132], [tg 142, tg 5407, tg 75958, tg 81223], [tg 194, tg 5459, tg 76010, tg 81275], [tg 285, tg 5550, tg 76101, tg 81366]],
      [tg 303458, tg 308723, tg 379274, tg 384539]⟩,
    ⟨-9, -1, 4, 12,
      [[tg 64, tg 5329, tg 75880, tg 81145], [tg 155, tg 5420, tg 75971, tg 81236], [tg 207, tg 5472, tg 76023, tg 81288], [tg 298, tg 5563, tg 76114, tg 81379]],
      [tg 151787, tg 157052, tg 227603, tg 232868]⟩,
    ⟨-9, -1, 5, 15,
      [[tg 77, tg 5342, tg 75893, tg 81158], [tg 103, tg 5368, tg 75919, tg 81184], [tg 168, tg 5433, tg 75984, tg 81249], [tg 220, tg 5485, tg 76036, tg 81301], [tg 311, tg 5576, tg 76127, tg 81392]],
      [tg 151852, tg 157117, tg 227668, tg 232933]⟩,
    ⟨-9, -1, 6, 13,
      [[tg 90, tg 5355, tg 75906, tg 81171], [tg 116, tg 5381, tg 75932, tg 81197], [tg 181, tg 5446, tg 75997, tg 81262], [tg 233, tg 5498, tg 76049, tg 81314], [tg 324, tg 5589, tg 76140, tg 81405]],
      [tg 303445, tg 308710, tg 379261, tg 384526]⟩,
    ⟨-9, -1, 7, 14,
      [[tg 103, tg 5368, tg 75919, tg 81184], [tg 194, tg 5459, tg 76010, tg 81275], [tg 233, tg 5498, tg 76049, tg 81314], [tg 311, tg 5576, tg 76127, tg 81392], [tg 337, tg 5602, tg 76153, tg 81418]],
      [tg 303497, tg 308762, tg 379313, tg 384578]⟩,
    ⟨-9, -1, 8, 13,
      [[tg 116, tg 5381, tg 75932, tg 81197], [tg 207, tg 5472, tg 76023, tg 81288], [tg 220, tg 5485, tg 76036, tg 81301], [tg 324, tg 5589, tg 76140, tg 81405], [tg 350, tg 5615, tg 76166, tg 81431]],
      [tg 151956, tg 157221, tg 227772, tg 233037]⟩,
    ⟨-8, -1, 0, 17,
      [[tg 129, tg 5394, tg 75945, tg 81210], [tg 50933, tg 56198, tg 126749, tg 132014], [tg 259, tg 5524, tg 76075, tg 81340], [tg 363, tg 5628, tg 76179, tg 81444]],
      [tg 151891, tg 157156, tg 227707, tg 232972]⟩,
    ⟨-8, -1, 1, 16,
      [[tg 142, tg 5407, tg 75958, tg 81223], [tg 246, tg 5511, tg 76062, tg 81327], [tg 285, tg 5550, tg 76101, tg 81366], [tg 376, tg 5641, tg 76192, tg 81457]],
      [tg 151917, tg 157182, tg 227733, tg 232998]⟩,
    ⟨-8, -1, 2, 10,
      [[tg 155, tg 5420, tg 75971, tg 81236], [tg 298, tg 5563, tg 76114, tg 81379], [tg 825, tg 6090, tg 25401, tg 30666], [tg 389, tg 5654, tg 76205, tg 81470]],
      [tg 152457, tg 157722, tg 177033, tg 182298]⟩,
    ⟨-8, -1, 3, 15,
      [[tg 168, tg 5433, tg 75984, tg 81249], [tg 259, tg 5524, tg 76075, tg 81340], [tg 311, tg 5576, tg 76127, tg 81392], [tg 402, tg 5667, tg 76218, tg 81483]],
      [tg 303575, tg 308840, tg 379391, tg 384656]⟩,
    ⟨-8, -1, 4, 11,
      [[tg 181, tg 5446, tg 75997, tg 81262], [tg 272, tg 5537, tg 76088, tg 81353], [tg 324, tg 5589, tg 76140, tg 81405], [tg 415, tg 5680, tg 76231, tg 81496]],
      [tg 151904, tg 157169, tg 227720, tg 232985]⟩,
    ⟨-8, -1, 5, 14,
      [[tg 194, tg 5459, tg 76010, tg 81275], [tg 220, tg 5485, tg 76036, tg 81301], [tg 285, tg 5550, tg 76101, tg 81366], [tg 337, tg 5602, tg 76153, tg 81418], [tg 428, tg 5693, tg 76244, tg 81509]],
      [tg 151969, tg 157234, tg 227785, tg 233050]⟩,
    ⟨-8, -1, 6, 12,
      [[tg 207, tg 5472, tg 76023, tg 81288], [tg 233, tg 5498, tg 76049, tg 81314], [tg 298, tg 5563, tg 76114, tg 81379], [tg 350, tg 5615, tg 76166, tg 81431], [tg 441, tg 5706, tg 76257, tg 81522]],
      [tg 303562, tg 308827, tg 379378, tg 384643]⟩,
    ⟨-8, -1, 7, 13,
      [[tg 220, tg 5485, tg 76036, tg 81301], [tg 311, tg 5576, tg 76127, tg 81392], [tg 350, tg 5615, tg 76166, tg 81431], [tg 428, tg 5693, tg 76244, tg 81509], [tg 454, tg 5719, tg 76270, tg 81535]],
      [tg 303614, tg 308879, tg 379430, tg 384695]⟩,
    ⟨-8, -1, 8, 12,
      [[tg 233, tg 5498, tg 76049, tg 81314], [tg 324, tg 5589, tg 76140, tg 81405], [tg 337, tg 5602, tg 76153, tg 81418], [tg 441, tg 5706, tg 76257, tg 81522], [tg 467, tg 5732, tg 76283, tg 81548]],
      [tg 152073, tg 157338, tg 227889, tg 233154]⟩,
    ⟨-7, -1, 0, 16,
      [[tg 246, tg 5511, tg 76062, tg 81327], [tg 51050, tg 56315, tg 126866, tg 132131], [tg 376, tg 5641, tg 76192, tg 81457], [tg 480, tg 5745, tg 76296, tg 81561]],
      [tg 152008, tg 157273, tg 227824, tg 233089]⟩,
    ⟨-7, -1, 1, 15,
      [[tg 259, tg 5524, tg 76075, tg 81340], [tg 363, tg 5628, tg 76179, tg 81444], [tg 402, tg 5667, tg 76218, tg 81483], [tg 493, tg 5758, tg 76309, tg 81574]],
      [tg 152034, tg 157299, tg 227850, tg 233115]⟩,
    ⟨-7, -1, 2, 9,
      [[tg 272, tg 5537, tg 76088, tg 81353], [tg 415, tg 5680, tg 76231, tg 81496], [tg 708, tg 5973, tg 25518, tg 30783], [tg 506, tg 5771, tg 76322, tg 81587]],
      [tg 152340, tg 157605, tg 177150, tg 182415]⟩,
    ⟨-7, -1, 3, 14,
      [[tg 285, tg 5550, tg 76101, tg 81366], [tg 376, tg 5641, tg 76192, tg 81457], [tg 428, tg 5693, tg 76244, tg 81509], [tg 519, tg 5784, tg 76335, tg 81600]],
      [tg 303692, tg 308957, tg 379508, tg 384773]⟩,
    ⟨-7, -1, 4, 10,
      [[tg 298, tg 5563, tg 76114, tg 81379], [tg 389, tg 5654, tg 76205, tg 81470], [tg 441, tg 5706, tg 76257, tg 81522], [tg 532, tg 5797, tg 76348, tg 81613]],
      [tg 152021, tg 157286, tg 227837, tg 233102]⟩,
    ⟨-7, -1, 5, 13,
      [[tg 311, tg 5576, tg 76127, tg 81392], [tg 337, tg 5602, tg 76153, tg 81418], [tg 402, tg 5667, tg 76218, tg 81483], [tg 454, tg 5719, tg 76270, tg 81535], [tg 545, tg 5810, tg 76361, tg 81626]],
      [tg 152086, tg 157351, tg 227902, tg 233167]⟩,
    ⟨-7, -1, 6, 11,
      [[tg 324, tg 5589, tg 76140, tg 81405], [tg 350, tg 5615, tg 76166, tg 81431], [tg 415, tg 5680, tg 76231, tg 81496], [tg 467, tg 5732, tg 76283, tg 81548], [tg 558, tg 5823, tg 76374, tg 81639]],
      [tg 303679, tg 308944, tg 379495, tg 384760]⟩,
    ⟨-7, -1, 7, 12,
      [[tg 337, tg 5602, tg 76153, tg 81418], [tg 428, tg 5693, tg 76244, tg 81509], [tg 467, tg 5732, tg 76283, tg 81548], [tg 545, tg 5810, tg 76361, tg 81626], [tg 571, tg 5836, tg 76387, tg 81652]],
      [tg 303731, tg 308996, tg 379547, tg 384812]⟩,
    ⟨-7, -1, 8, 11,
      [[tg 350, tg 5615, tg 76166, tg 81431], [tg 441, tg 5706, tg 76257, tg 81522], [tg 454, tg 5719, tg 76270, tg 81535], [tg 558, tg 5823, tg 76374, tg 81639], [tg 584, tg 5849, tg 76400, tg 81665]],
      [tg 152190, tg 157455, tg 228006, tg 233271]⟩,
    ⟨-6, -1, 0, 15,
      [[tg 363, tg 5628, tg 76179, tg 81444], [tg 51167, tg 56432, tg 126983, tg 132248], [tg 493, tg 5758, tg 76309, tg 81574], [tg 597, tg 5862, tg 76413, tg 81678]],
      [tg 152125, tg 157390, tg 227941, tg 233206]⟩,
    ⟨-6, -1, 1, 14,
      [[tg 376, tg 5641, tg 76192, tg 81457], [tg 480, tg 5745, tg 76296, tg 81561], [tg 519, tg 5784, tg 76335, tg 81600], [tg 610, tg 5875, tg 76426, tg 81691]],
      [tg 152151, tg 157416, tg 227967, tg 233232]⟩,
    ⟨-6, -1, 2, 8,
      [[tg 389, tg 5654, tg 76205, tg 81470], [tg 532, tg 5797, tg 76348, tg 81613], [tg 591, tg 5856, tg 25635, tg 30900], [tg 623, tg 5888, tg 76439, tg 81704]],
      [tg 152223, tg 157488, tg 177267, tg 182532]⟩,
    ⟨-6, -1, 3, 13,
      [[tg 402, tg 5667, tg 76218, tg 81483], [tg 493, tg 5758, tg 76309, tg 81574], [tg 545, tg 5810, tg 76361, tg 81626], [tg 636, tg 5901, tg 76452, tg 81717]],
      [tg 303809, tg 309074, tg 379625, tg 384890]⟩,
    ⟨-6, -1, 4, 9,
      [[tg 415, tg 5680, tg 76231, tg 81496], [tg 506, tg 5771, tg 76322, tg 81587], [tg 558, tg 5823, tg 76374, tg 81639], [tg 649, tg 5914, tg 76465, tg 81730]],
      [tg 152138, tg 157403, tg 227954, tg 233219]⟩,
    ⟨-6, -1, 5, 12,
      [[tg 428, tg 5693, tg 76244, tg 81509], [tg 454, tg 5719, tg 76270, tg 81535], [tg 519, tg 5784, tg 76335, tg 81600], [tg 571, tg 5836, tg 76387, tg 81652], [tg 662, tg 5927, tg 76478, tg 81743]],
      [tg 152203, tg 157468, tg 228019, tg 233284]⟩,
    ⟨-6, -1, 6, 10,
      [[tg 441, tg 5706, tg 76257, tg 81522], [tg 467, tg 5732, tg 76283, tg 81548], [tg 532, tg 5797, tg 76348, tg 81613], [tg 584, tg 5849, tg 76400, tg 81665], [tg 675, tg 5940, tg 76491, tg 81756]],
      [tg 303796, tg 309061, tg 379612, tg 384877]⟩,
    ⟨-6, -1, 7, 11,
      [[tg 454, tg 5719, tg 76270, tg 81535], [tg 545, tg 5810, tg 76361, tg 81626], [tg 584, tg 5849, tg 76400, tg 81665], [tg 662, tg 5927, tg 76478, tg 81743], [tg 688, tg 5953, tg 76504, tg 81769]],
      [tg 303848, tg 309113, tg 379664, tg 384929]⟩,
    ⟨-6, -1, 8, 10,
      [[tg 467, tg 5732, tg 76283, tg 81548], [tg 558, tg 5823, tg 76374, tg 81639], [tg 571, tg 5836, tg 76387, tg 81652], [tg 675, tg 5940, tg 76491, tg 81756], [tg 701, tg 5966, tg 76517, tg 81782]],
      [tg 152307, tg 157572, tg 228123, tg 233388]⟩,
    ⟨-5, -1, 0, 14,
      [[tg 480, tg 5745, tg 76296, tg 81561], [tg 51284, tg 56549, tg 127100, tg 132365], [tg 610, tg 5875, tg 76426, tg 81691], [tg 714, tg 5979, tg 76530, tg 81795]],
      [tg 152242, tg 157507, tg 228058, tg 233323]⟩,
    ⟨-5, -1, 1, 13,
      [[tg 493, tg 5758, tg 76309, tg 81574], [tg 597, tg 5862, tg 76413, tg 81678], [tg 636, tg 5901, tg 76452, tg 81717], [tg 727, tg 5992, tg 76543, tg 81808]],
      [tg 152268, tg 157533, tg 228084, tg 233349]⟩,
    ⟨-5, -1, 2, 7,
      [[tg 506, tg 5771, tg 76322, tg 81587], [tg 649, tg 5914, tg 76465, tg 81730], [tg 474, tg 5739, tg 25752, tg 31017], [tg 740, tg 6005, tg 76556, tg 81821]],
      [tg 152106, tg 157371, tg 177384, tg 182649]⟩,
    ⟨-5, -1, 3, 12,
      [[tg 519, tg 5784, tg 76335, tg 81600], [tg 610, tg 5875, tg 76426, tg 81691], [tg 662, tg 5927, tg 76478, tg 81743], [tg 753, tg 6018, tg 76569, tg 81834]],
      [tg 303926, tg 309191, tg 379742, tg 385007]⟩,
    ⟨-5, -1, 4, 8,
      [[tg 532, tg 5797, tg 76348, tg 81613], [tg 623, tg 5888, tg 76439, tg 81704], [tg 675, tg 5940, tg 76491, tg 81756], [tg 766, tg 6031, tg 76582, tg 81847]],
      [tg 152255, tg 157520, tg 228071, tg 233336]⟩,
    ⟨-5, -1, 5, 11,
      [[tg 545, tg 5810, tg 76361, tg 81626], [tg 571, tg 5836, tg 76387, tg 81652], [tg 636, tg 5901, tg 76452, tg 81717], [tg 688, tg 5953, tg 76504, tg 81769], [tg 779, tg 6044, tg 76595, tg 81860]],
      [tg 152320, tg 157585, tg 228136, tg 233401]⟩,
    ⟨-5, -1, 6, 9,
      [[tg 558, tg 5823, tg 76374, tg 81639], [tg 584, tg 5849, tg 76400, tg 81665], [tg 649, tg 5914, tg 76465, tg 81730], [tg 701, tg 5966, tg 76517, tg 81782], [tg 792, tg 6057, tg 76608, tg 81873]],
      [tg 303913, tg 309178, tg 379729, tg 384994]⟩,
    ⟨-5, -1, 7, 10,
      [[tg 571, tg 5836, tg 76387, tg 81652], [tg 662, tg 5927, tg 76478, tg 81743], [tg 701, tg 5966, tg 76517, tg 81782], [tg 779, tg 6044, tg 76595, tg 81860], [tg 805, tg 6070, tg 76621, tg 81886]],
      [tg 303965, tg 309230, tg 379781, tg 385046]⟩,
    ⟨-5, -1, 8, 9,
      [[tg 584, tg 5849, tg 76400, tg 81665], [tg 675, tg 5940, tg 76491, tg 81756], [tg 688, tg 5953, tg 76504, tg 81769], [tg 792, tg 6057, tg 76608, tg 81873], [tg 818, tg 6083, tg 76634, tg 81899]],
      [tg 152424, tg 157689, tg 228240, tg 233505]⟩,
    ⟨-4, -1, 0, 13,
      [[tg 597, tg 5862, tg 76413, tg 81678], [tg 51401, tg 56666, tg 127217, tg 132482], [tg 727, tg 5992, tg 76543, tg 81808], [tg 831, tg 6096, tg 76647, tg 81912]],
      [tg 152359, tg 157624, tg 228175, tg 233440]⟩,
    ⟨-4, -1, 1, 12,
      [[tg 610, tg 5875, tg 76426, tg 81691], [tg 714, tg 5979, tg 76530, tg 81795], [tg 753, tg 6018, tg 76569, tg 81834], [tg 844, tg 6109, tg 76660, tg 81925]],
      [tg 152385, tg 157650, tg 228201, tg 233466]⟩,
    ⟨-4, -1, 2, 6,
      [[tg 623, tg 5888, tg 76439, tg 81704], [tg 766, tg 6031, tg 76582, tg 81847], [tg 357, tg 5622, tg 25869, tg 31134], [tg 857, tg 6122, tg 76673, tg 81938]],
      [tg 151989, tg 157254, tg 177501, tg 182766]⟩,
    ⟨-4, -1, 3, 11,
      [[tg 636, tg 5901, tg 76452, tg 81717], [tg 727, tg 5992, tg 76543, tg 81808], [tg 779, tg 6044, tg 76595, tg 81860], [tg 870, tg 6135, tg 76686, tg 81951]],
      [tg 304043, tg 309308, tg 379859, tg 385124]⟩,
    ⟨-4, -1, 4, 7,
      [[tg 649, tg 5914, tg 76465, tg 81730], [tg 740, tg 6005, tg 76556, tg 81821], [tg 792, tg 6057, tg 76608, tg 81873], [tg 883, tg 6148, tg 76699, tg 81964]],
      [tg 152372, tg 157637, tg 228188, tg 233453]⟩,
    ⟨-4, -1, 5, 10,
      [[tg 662, tg 5927, tg 76478, tg 81743], [tg 688, tg 5953, tg 76504, tg 81769], [tg 753, tg 6018, tg 76569, tg 81834], [tg 805, tg 6070, tg 76621, tg 81886], [tg 896, tg 6161, tg 76712, tg 81977]],
      [tg 152437, tg 157702, tg 228253, tg 233518]⟩,
    ⟨-4, -1, 6, 8,
      [[tg 675, tg 5940, tg 76491, tg 81756], [tg 701, tg 5966, tg 76517, tg 81782], [tg 766, tg 6031, tg 76582, tg 81847], [tg 818, tg 6083, tg 76634, tg 81899], [tg 909, tg 6174, tg 76725, tg 81990]],
      [tg 304030, tg 309295, tg 379846, tg 385111]⟩,
    ⟨-4, -1, 7, 9,
      [[tg 688, tg 5953, tg 76504, tg 81769], [tg 779, tg 6044, tg 76595, tg 81860], [tg 818, tg 6083, tg 76634, tg 81899], [tg 896, tg 6161, tg 76712, tg 81977], [tg 922, tg 6187, tg 76738, tg 82003]],
      [tg 304082, tg 309347, tg 379898, tg 385163]⟩,
    ⟨-4, -1, 8, 8,
      [[tg 701, tg 5966, tg 76517, tg 81782], [tg 792, tg 6057, tg 76608, tg 81873], [tg 805, tg 6070, tg 76621, tg 81886], [tg 909, tg 6174, tg 76725, tg 81990], [tg 935, tg 6200, tg 76751, tg 82016]],
      [tg 152541, tg 157806, tg 228357, tg 233622]⟩,
    ⟨-3, -1, 0, 12,
      [[tg 714, tg 5979, tg 76530, tg 81795], [tg 51518, tg 56783, tg 127334, tg 132599], [tg 844, tg 6109, tg 76660, tg 81925], [tg 948, tg 6213, tg 76764, tg 82029]],
      [tg 152476, tg 157741, tg 228292, tg 233557]⟩,
    ⟨-3, -1, 1, 11,
      [[tg 727, tg 5992, tg 76543, tg 81808], [tg 831, tg 6096, tg 76647, tg 81912], [tg 870, tg 6135, tg 76686, tg 81951], [tg 961, tg 6226, tg 76777, tg 82042]],
      [tg 152502, tg 157767, tg 228318, tg 233583]⟩,
    ⟨-3, -1, 2, 5,
      [[tg 740, tg 6005, tg 76556, tg 81821], [tg 883, tg 6148, tg 76699, tg 81964], [tg 240, tg 5505, tg 25986, tg 31251], [tg 974, tg 6239, tg 76790, tg 82055]],
      [tg 151872, tg 157137, tg 177618, tg 182883]⟩,
    ⟨-3, -1, 3, 10,
      [[tg 753, tg 6018, tg 76569, tg 81834], [tg 844, tg 6109, tg 76660, tg 81925], [tg 896, tg 6161, tg 76712, tg 81977], [tg 987, tg 6252, tg 76803, tg 82068]],
      [tg 304160, tg 309425, tg 379976, tg 385241]⟩,
    ⟨-3, -1, 4, 6,
      [[tg 766, tg 6031, tg 76582, tg 81847], [tg 857, tg 6122, tg 76673, tg 81938], [tg 909, tg 6174, tg 76725, tg 81990], [tg 1000, tg 6265, tg 76816, tg 82081]],
      [tg 152489, tg 157754, tg 228305, tg 233570]⟩,
    ⟨-3, -1, 5, 9,
      [[tg 779, tg 6044, tg 76595, tg 81860], [tg 805, tg 6070, tg 76621, tg 81886], [tg 870, tg 6135, tg 76686, tg 81951], [tg 922, tg 6187, tg 76738, tg 82003], [tg 1013, tg 6278, tg 76829, tg 82094]],
      [tg 152554, tg 157819, tg 228370, tg 233635]⟩,
    ⟨-3, -1, 6, 7,
      [[tg 792, tg 6057, tg 76608, tg 81873], [tg 818, tg 6083, tg 76634, tg 81899], [tg 883, tg 6148, tg 76699, tg 81964], [tg 935, tg 6200, tg 76751, tg 82016], [tg 1026, tg 6291, tg 76842, tg 82107]],
      [tg 304147, tg 309412, tg 379963, tg 385228]⟩,
    ⟨-3, -1, 7, 8,
      [[tg 805, tg 6070, tg 76621, tg 81886], [tg 896, tg 6161, tg 76712, tg 81977], [tg 935, tg 6200, tg 76751, tg 82016], [tg 1013, tg 6278, tg 76829, tg 82094], [tg 1039, tg 6304, tg 76855, tg 82120]],
      [tg 304199, tg 309464, tg 380015, tg 385280]⟩,
    ⟨-3, -1, 8, 7,
      [[tg 818, tg 6083, tg 76634, tg 81899], [tg 909, tg 6174, tg 76725, tg 81990], [tg 922, tg 6187, tg 76738, tg 82003], [tg 1026, tg 6291, tg 76842, tg 82107], [tg 1052, tg 6317, tg 76868, tg 82133]],
      [tg 152658, tg 157923, tg 228474, tg 233739]⟩,
    ⟨-2, -1, 0, 11,
      [[tg 831, tg 6096, tg 76647, tg 81912], [tg 4239, tg 51635, tg 10557, tg 127451], [tg 961, tg 6226, tg 76777, tg 82042], [tg 1, tg 1065, tg 6319, tg 76881]],
      [tg 152593, tg 157858, tg 228409, tg 233674]⟩,
    ⟨-2, -1, 1, 10,
      [[tg 844, tg 6109, tg 76660, tg 81925], [tg 948, tg 6213, tg 76764, tg 82029], [tg 987, tg 6252, tg 76803, tg 82068], [tg 14, tg 1078, tg 6332, tg 76894]],
      [tg 152619, tg 157884, tg 228435, tg 233700]⟩,
    ⟨-2, -1, 2, 4,
      [[tg 857, tg 6122, tg 76673, tg 81938], [tg 1000, tg 6265, tg 76816, tg 82081], [tg 123, tg 5388, tg 26103, tg 31368], [tg 27, tg 1091, tg 6345, tg 76907]],
      [tg 151755, tg 157020, tg 177735, tg 183000]⟩,
    ⟨-2, -1, 3, 9,
      [[tg 870, tg 6135, tg 76686, tg 81951], [tg 961, tg 6226, tg 76777, tg 82042], [tg 1013, tg 6278, tg 76829, tg 82094], [tg 40, tg 1104, tg 6358, tg 76920]],
      [tg 304277, tg 309542, tg 380093, tg 385358]⟩,
    ⟨-2, -1, 4, 5,
      [[tg 883, tg 6148, tg 76699, tg 81964], [tg 974, tg 6239, tg 76790, tg 82055], [tg 1026, tg 6291, tg 76842, tg 82107], [tg 53, tg 1117, tg 6371, tg 76933]],
      [tg 152606, tg 157871, tg 228422, tg 233687]⟩,
    ⟨-2, -1, 5, 8,
      [[tg 896, tg 6161, tg 76712, tg 81977], [tg 922, tg 6187, tg 76738, tg 82003], [tg 987, tg 6252, tg 76803, tg 82068], [tg 1039, tg 6304, tg 76855, tg 82120], [tg 66, tg 1130, tg 6384, tg 76946]],
      [tg 152671, tg 157936, tg 228487, tg 233752]⟩,
    ⟨-2, -1, 6, 6,
      [[tg 909, tg 6174, tg 76725, tg 81990], [tg 935, tg 6200, tg 76751, tg 82016], [tg 1000, tg 6265, tg 76816, tg 82081], [tg 1052, tg 6317, tg 76868, tg 82133], [tg 79, tg 1143, tg 6397, tg 76959]],
      [tg 304264, tg 309529, tg 380080, tg 385345]⟩,
    ⟨-2, -1, 7, 7,
      [[tg 922, tg 6187, tg 76738, tg 82003], [tg 1013, tg 6278, tg 76829, tg 82094], [tg 1052, tg 6317, tg 76868, tg 82133], [tg 66, tg 1130, tg 6384, tg 76946], [tg 92, tg 1156, tg 6410, tg 76972]],
      [tg 304316, tg 309581, tg 380132, tg 385397]⟩,
    ⟨-2, -1, 8, 6,
      [[tg 935, tg 6200, tg 76751, tg 82016], [tg 1026, tg 6291, tg 76842, tg 82107], [tg 1039, tg 6304, tg 76855, tg 82120], [tg 79, tg 1143, tg 6397, tg 76959], [tg 105, tg 1169, tg 6423, tg 76985]],
      [tg 151711, tg 152775, tg 158029, tg 228591]⟩]⟩]

/-- A packed certificate entry: side bit, test index, coefficient. -/
def cc (n : ℕ) : Bool × ℕ × ℕ := (n % 2 == 1, n / 2 % 8, n / 16)

set_option maxRecDepth 100000 in
def certsData : List (List (List (Bool × ℕ × ℕ))) := [
  [[],[cc 16,cc 20,cc 21],[cc 18,cc 20,cc 21],[cc 18,cc 21],[cc 18,cc 22,cc 21],[cc 16,cc 22,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 17],[cc 148,cc 17],[cc 150,cc 19],[cc 16,cc 22,cc 19],[cc 150,cc 17],[cc 148,cc 19]],
  [[cc 16,cc 20,cc 37],[],[cc 18,cc 21],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 35],[cc 18,cc 19],[cc 20,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 144,cc 148,cc 33],[cc 16,cc 17]],
  [[cc 16,cc 20,cc 35],[cc 16,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 17],[cc 18,cc 19],[cc 146,cc 148,cc 35],[cc 18,cc 17],[cc 16,cc 19],[cc 20,cc 17]],
  [[cc 20,cc 19],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 19],[],[cc 18,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 17],[cc 144,cc 17],[cc 146,cc 19],[cc 18,cc 20,cc 19],[cc 146,cc 17],[cc 144,cc 19]],
  [[cc 16,cc 20,cc 39],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 35],[],[cc 18,cc 21],[cc 16,cc 20,cc 33],[cc 16,cc 19],[cc 144,cc 148,cc 33],[cc 16,cc 17],[cc 18,cc 19],[cc 20,cc 19],[cc 18,cc 17]],
  [[cc 16,cc 20,cc 33],[cc 18,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 17],[cc 16,cc 19],[cc 20,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 146,cc 148,cc 35]],
  [[cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 19],[],[cc 18,cc 20,cc 19],[cc 146,cc 17],[cc 144,cc 19],[cc 16,cc 20,cc 17],[cc 144,cc 17],[cc 146,cc 19]],
  [[cc 16,cc 18,cc 37],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 33],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 18,cc 35],[],[cc 16,cc 19],[cc 144,cc 146,cc 35],[cc 16,cc 17],[cc 144,cc 146,cc 33],[cc 18,cc 17]],
  [[cc 16,cc 149],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 145],[cc 32,cc 146,cc 145],[cc 18,cc 17],[cc 16,cc 147],[cc 18,cc 17],[],[cc 16,cc 19],[cc 32,cc 146,cc 147],[cc 16,cc 17],[cc 32,cc 146,cc 145]],
  [[cc 18,cc 151],[cc 16,cc 19],[cc 144,cc 34,cc 147],[cc 18,cc 147],[cc 16,cc 17],[cc 16,cc 21],[cc 18,cc 145],[cc 144,cc 34,cc 145],[cc 18,cc 17],[],[cc 16,cc 19],[cc 144,cc 34,cc 147],[cc 16,cc 17]],
  [[cc 16,cc 18,cc 39],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 18,cc 35],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 33],[cc 16,cc 17],[cc 144,cc 146,cc 33],[cc 18,cc 17],[],[cc 16,cc 19],[cc 144,cc 146,cc 35]],
  [[cc 16,cc 151],[cc 32,cc 146,cc 145],[cc 18,cc 17],[cc 16,cc 147],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 145],[cc 32,cc 146,cc 147],[cc 16,cc 17],[cc 32,cc 146,cc 145],[cc 18,cc 17],[],[cc 16,cc 19]],
  [[cc 18,cc 149],[cc 16,cc 17],[cc 16,cc 21],[cc 18,cc 145],[cc 16,cc 19],[cc 144,cc 34,cc 147],[cc 18,cc 147],[cc 16,cc 19],[cc 144,cc 34,cc 147],[cc 16,cc 17],[cc 144,cc 34,cc 145],[cc 18,cc 17],[]]]

def cfg : GalCert.Cfg 9 := ⟨adj, (0, 0, 1), 9, regsData, certsData, 0, 1⟩

set_option maxHeartbeats 4000000 in
theorem hc : cfg.check = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem hV : cfg.vbound 25 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

set_option maxHeartbeats 4000000 in
theorem hrec : ∀ k, (([(1, 11), (-1, 10), (-1, 2), (1, 1)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide) (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem hgfw : ∀ n < 25 + 2 * cfg.L, ((GalCert.csOfS [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] 0).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem hsmall : ∀ n < 11, GalCert.conv a [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] n = ([1, 3, 4, 5, 4, 6, 4, 5, 4, 3, 1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P311993

open PowerSeries OMA.S_oeis_a311993 in
theorem OMA.solution : type_of% @OMA.S_oeis_a311993.main := by
  refine ⟨?_, ?_⟩
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
  · have hD : (X^10 - X^9 - X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (X^10 + 3*X^9 + 4*X^8 + 5*X^7 + 4*X^6 + 6*X^5 + 4*X^4 + 5*X^3 + 4*X^2 + 3*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 3, 4, 5, 4, 6, 4, 5, 4, 3, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from2 P311993.hc P311993.hV a P311993.ha _ _ 0 11 (by decide) (by decide) P311993.hgfw P311993.hsmall
