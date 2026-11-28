import OMAStatements.S_oeis_a312932
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A312932.

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


namespace P312932
open OMA.S_oeis_a312932

/-- A packed target code (mixed radix). -/
def tg (n : ℕ) : GalCert.Tgt := ⟨n % 13, n / 13 % 81, n / 1053 % 2, n / 2106 % 2, n / 4212 % 3, n / 12636 % 2, n / 25272 % 2, n / 50544 % 3, n / 151632⟩

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 9) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 4,
      [[tg 6], [tg 163], [tg 13], [tg 3]],
      [tg 151645]⟩,
    ⟨0, 0, 1, 3,
      [[tg 19], [tg 0], [tg 26], [tg 16]],
      [tg 303290]⟩,
    ⟨0, 0, 2, 2,
      [[tg 32], [tg 58], [tg 13], [tg 52], [tg 29]],
      [tg 151684]⟩,
    ⟨0, 0, 3, 4,
      [[tg 45], [tg 71], [tg 65], [tg 10], [tg 42]],
      [tg 151697]⟩,
    ⟨0, 0, 4, 1,
      [[tg 58], [tg 26], [tg 78], [tg 29], [tg 55]],
      [tg 151710]⟩,
    ⟨0, 0, 5, 3,
      [[tg 71], [tg 39], [tg 91], [tg 42], [tg 68]],
      [tg 151723]⟩,
    ⟨0, 0, 6, 0,
      [[tg 84], [tg 52], [tg 104], [tg 81]],
      [tg 0]⟩,
    ⟨0, 0, 7, 2,
      [[tg 97], [tg 65], [tg 104], [tg 94]],
      [tg 303368]⟩,
    ⟨0, 0, 8, 1,
      [[tg 110], [tg 78], [tg 91], [tg 107]],
      [tg 303342]⟩]⟩,
  ⟨1, -1, -1, 0, 0, [(1, -1, 0), (-1, 1, 0), (-1, -1, 2)], -1, -1, 2, 2, 0, 0, 0, 0,
   [⟨-1, -1, 0, 13,
      [[tg 948, tg 64128], [tg 4375, tg 9640], [tg 14, tg 5279], [tg 124, tg 5389]],
      [tg 151646, tg 156911]⟩,
    ⟨-1, -1, 1, 12,
      [[tg 961, tg 64141], [tg 1, tg 5266], [tg 27, tg 5292], [tg 137, tg 5402]],
      [tg 303291, tg 308556]⟩,
    ⟨-1, -1, 2, 11,
      [[tg 974, tg 64154], [tg 1000, tg 64180], [tg 14, tg 5279], [tg 53, tg 5318], [tg 150, tg 5415]],
      [tg 151685, tg 156950]⟩,
    ⟨-1, -1, 3, 6,
      [[tg 987, tg 64167], [tg 1013, tg 64193], [tg 66, tg 5331], [tg 6, tg 13584], [tg 163, tg 5428]],
      [tg 151638, tg 165216]⟩,
    ⟨-1, -1, 4, 10,
      [[tg 1000, tg 64180], [tg 27, tg 5292], [tg 79, tg 5344], [tg 150, tg 5415], [tg 176, tg 5441]],
      [tg 151711, tg 156976]⟩,
    ⟨-1, -1, 5, 6,
      [[tg 1013, tg 64193], [tg 40, tg 5305], [tg 92, tg 5357], [tg 163, tg 5428], [tg 189, tg 5454]],
      [tg 151795, tg 157060]⟩,
    ⟨-1, -1, 6, 9,
      [[tg 1026, tg 64206], [tg 53, tg 5318], [tg 105, tg 5370], [tg 202, tg 5467]],
      [tg 151737, tg 157002]⟩,
    ⟨-1, -1, 7, 7,
      [[tg 1039, tg 64219], [tg 66, tg 5331], [tg 105, tg 5370], [tg 215, tg 5480]],
      [tg 303330, tg 308595]⟩,
    ⟨-1, -1, 8, 8,
      [[tg 1052, tg 64232], [tg 79, tg 5344], [tg 92, tg 5357], [tg 228, tg 5493]],
      [tg 303356, tg 308621]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 2)], 1, -1, 2, 2, 0, 0, 0, 0,
   [⟨1, -1, 0, 13,
      [[tg 124, tg 63304], [tg 50707, tg 113887], [tg 15, tg 5280], [tg 8, tg 5273]],
      [tg 151647, tg 156912]⟩,
    ⟨1, -1, 1, 12,
      [[tg 137, tg 63317], [tg 2, tg 5267], [tg 28, tg 5293], [tg 21, tg 5286]],
      [tg 303292, tg 308557]⟩,
    ⟨1, -1, 2, 11,
      [[tg 150, tg 63330], [tg 176, tg 63356], [tg 15, tg 5280], [tg 54, tg 5319], [tg 34, tg 5299]],
      [tg 455072, tg 518252]⟩,
    ⟨1, -1, 3, 5,
      [[tg 163, tg 63343], [tg 189, tg 63369], [tg 67, tg 5332], [tg 3, tg 1061], [tg 47, tg 5312]],
      [tg 151635, tg 152693]⟩,
    ⟨1, -1, 4, 10,
      [[tg 176, tg 63356], [tg 28, tg 5293], [tg 80, tg 5345], [tg 34, tg 5299], [tg 60, tg 5325]],
      [tg 151712, tg 156977]⟩,
    ⟨1, -1, 5, 6,
      [[tg 189, tg 63369], [tg 41, tg 5306], [tg 93, tg 5358], [tg 47, tg 5312], [tg 73, tg 5338]],
      [tg 303305, tg 308570]⟩,
    ⟨1, -1, 6, 9,
      [[tg 202, tg 63382], [tg 54, tg 5319], [tg 106, tg 5371], [tg 86, tg 5351]],
      [tg 151738, tg 157003]⟩,
    ⟨1, -1, 7, 7,
      [[tg 215, tg 63395], [tg 67, tg 5332], [tg 106, tg 5371], [tg 99, tg 5364]],
      [tg 303331, tg 308596]⟩,
    ⟨1, -1, 8, 8,
      [[tg 228, tg 63408], [tg 80, tg 5345], [tg 93, tg 5358], [tg 112, tg 5377]],
      [tg 303357, tg 308622]⟩]⟩,
  ⟨1, 9, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 1)], 1, 0, 1, 9, 0, 0, 0, 0,
   [⟨1, 0, 0, 4,
      [[tg 0, tg 1992], [tg 41, tg 13619], [tg 16, tg 5281], [tg 120, tg 5385]],
      [tg 151648, tg 456888]⟩,
    ⟨1, 0, 1, 3,
      [[tg 13, tg 2005], [tg 3, tg 5268], [tg 29, tg 5294], [tg 133, tg 5398]],
      [tg 303293, tg 456901]⟩,
    ⟨1, 0, 2, 2,
      [[tg 26, tg 2018], [tg 52, tg 2044], [tg 16, tg 5281], [tg 55, tg 5320], [tg 146, tg 5411]],
      [tg 454948, tg 608546]⟩,
    ⟨1, 0, 3, 4,
      [[tg 39, tg 2031], [tg 65, tg 2057], [tg 68, tg 5333], [tg 4, tg 1998], [tg 159, tg 5424]],
      [tg 454961, tg 608559]⟩,
    ⟨1, 0, 4, 2,
      [[tg 52, tg 2044], [tg 29, tg 5294], [tg 81, tg 5346], [tg 146, tg 5411], [tg 172, tg 5437]],
      [tg 606580, tg 608572]⟩,
    ⟨1, 0, 5, 4,
      [[tg 65, tg 2057], [tg 42, tg 5307], [tg 94, tg 5359], [tg 159, tg 5424], [tg 185, tg 5450]],
      [tg 606593, tg 608585]⟩,
    ⟨1, 0, 6, 1,
      [[tg 78, tg 2070], [tg 55, tg 5320], [tg 107, tg 5372], [tg 198, tg 5463]],
      [tg 454974, tg 456966]⟩,
    ⟨1, 0, 7, 3,
      [[tg 91, tg 2083], [tg 68, tg 5333], [tg 107, tg 5372], [tg 211, tg 5476]],
      [tg 454987, tg 456979]⟩,
    ⟨1, 0, 8, 2,
      [[tg 104, tg 2096], [tg 81, tg 5346], [tg 94, tg 5359], [tg 224, tg 5489]],
      [tg 455000, tg 456992]⟩,
    ⟨2, 0, 0, 5,
      [[tg 3, tg 5268], [tg 47, tg 63227], [tg 133, tg 5398], [tg 237, tg 5502]],
      [tg 454899, tg 460164]⟩,
    ⟨2, 0, 1, 4,
      [[tg 16, tg 5281], [tg 120, tg 5385], [tg 146, tg 5411], [tg 250, tg 5515]],
      [tg 454912, tg 460177]⟩,
    ⟨2, 0, 2, 3,
      [[tg 29, tg 5294], [tg 55, tg 5320], [tg 133, tg 5398], [tg 172, tg 5437], [tg 263, tg 5528]],
      [tg 606557, tg 611822]⟩,
    ⟨2, 0, 3, 5,
      [[tg 42, tg 5307], [tg 68, tg 5333], [tg 185, tg 5450], [tg 9, tg 5274], [tg 276, tg 5541]],
      [tg 606570, tg 611835]⟩,
    ⟨2, 0, 4, 3,
      [[tg 55, tg 5320], [tg 146, tg 5411], [tg 198, tg 5463], [tg 263, tg 5528], [tg 289, tg 5554]],
      [tg 606583, tg 611848]⟩,
    ⟨2, 0, 5, 5,
      [[tg 68, tg 5333], [tg 159, tg 5424], [tg 211, tg 5476], [tg 276, tg 5541], [tg 302, tg 5567]],
      [tg 606596, tg 611861]⟩,
    ⟨2, 0, 6, 2,
      [[tg 81, tg 5346], [tg 172, tg 5437], [tg 224, tg 5489], [tg 315, tg 5580]],
      [tg 454977, tg 460242]⟩,
    ⟨2, 0, 7, 4,
      [[tg 94, tg 5359], [tg 185, tg 5450], [tg 224, tg 5489], [tg 328, tg 5593]],
      [tg 454990, tg 460255]⟩,
    ⟨2, 0, 8, 3,
      [[tg 107, tg 5372], [tg 198, tg 5463], [tg 211, tg 5476], [tg 341, tg 5606]],
      [tg 455003, tg 460268]⟩,
    ⟨3, 0, 0, 6,
      [[tg 120, tg 5385], [tg 164, tg 63344], [tg 250, tg 5515], [tg 354, tg 5619]],
      [tg 455016, tg 460281]⟩,
    ⟨3, 0, 1, 5,
      [[tg 133, tg 5398], [tg 237, tg 5502], [tg 263, tg 5528], [tg 367, tg 5632]],
      [tg 455029, tg 460294]⟩,
    ⟨3, 0, 2, 4,
      [[tg 146, tg 5411], [tg 172, tg 5437], [tg 250, tg 5515], [tg 289, tg 5554], [tg 380, tg 5645]],
      [tg 606674, tg 611939]⟩,
    ⟨3, 0, 3, 6,
      [[tg 159, tg 5424], [tg 185, tg 5450], [tg 302, tg 5567], [tg 126, tg 5391], [tg 393, tg 5658]],
      [tg 606687, tg 611952]⟩,
    ⟨3, 0, 4, 4,
      [[tg 172, tg 5437], [tg 263, tg 5528], [tg 315, tg 5580], [tg 380, tg 5645], [tg 406, tg 5671]],
      [tg 606700, tg 611965]⟩,
    ⟨3, 0, 5, 6,
      [[tg 185, tg 5450], [tg 276, tg 5541], [tg 328, tg 5593], [tg 393, tg 5658], [tg 419, tg 5684]],
      [tg 606713, tg 611978]⟩,
    ⟨3, 0, 6, 3,
      [[tg 198, tg 5463], [tg 289, tg 5554], [tg 341, tg 5606], [tg 432, tg 5697]],
      [tg 455094, tg 460359]⟩,
    ⟨3, 0, 7, 5,
      [[tg 211, tg 5476], [tg 302, tg 5567], [tg 341, tg 5606], [tg 445, tg 5710]],
      [tg 455107, tg 460372]⟩,
    ⟨3, 0, 8, 4,
      [[tg 224, tg 5489], [tg 315, tg 5580], [tg 328, tg 5593], [tg 458, tg 5723]],
      [tg 455120, tg 460385]⟩,
    ⟨4, 0, 0, 7,
      [[tg 237, tg 5502], [tg 281, tg 63461], [tg 367, tg 5632], [tg 471, tg 5736]],
      [tg 455133, tg 460398]⟩,
    ⟨4, 0, 1, 6,
      [[tg 250, tg 5515], [tg 354, tg 5619], [tg 380, tg 5645], [tg 484, tg 5749]],
      [tg 455146, tg 460411]⟩,
    ⟨4, 0, 2, 5,
      [[tg 263, tg 5528], [tg 289, tg 5554], [tg 367, tg 5632], [tg 406, tg 5671], [tg 497, tg 5762]],
      [tg 606791, tg 612056]⟩,
    ⟨4, 0, 3, 7,
      [[tg 276, tg 5541], [tg 302, tg 5567], [tg 419, tg 5684], [tg 243, tg 5508], [tg 510, tg 5775]],
      [tg 606804, tg 612069]⟩,
    ⟨4, 0, 4, 5,
      [[tg 289, tg 5554], [tg 380, tg 5645], [tg 432, tg 5697], [tg 497, tg 5762], [tg 523, tg 5788]],
      [tg 606817, tg 612082]⟩,
    ⟨4, 0, 5, 7,
      [[tg 302, tg 5567], [tg 393, tg 5658], [tg 445, tg 5710], [tg 510, tg 5775], [tg 536, tg 5801]],
      [tg 606830, tg 612095]⟩,
    ⟨4, 0, 6, 4,
      [[tg 315, tg 5580], [tg 406, tg 5671], [tg 458, tg 5723], [tg 549, tg 5814]],
      [tg 455211, tg 460476]⟩,
    ⟨4, 0, 7, 6,
      [[tg 328, tg 5593], [tg 419, tg 5684], [tg 458, tg 5723], [tg 562, tg 5827]],
      [tg 455224, tg 460489]⟩,
    ⟨4, 0, 8, 5,
      [[tg 341, tg 5606], [tg 432, tg 5697], [tg 445, tg 5710], [tg 575, tg 5840]],
      [tg 455237, tg 460502]⟩,
    ⟨5, 0, 0, 8,
      [[tg 354, tg 5619], [tg 398, tg 63578], [tg 484, tg 5749], [tg 588, tg 5853]],
      [tg 455250, tg 460515]⟩,
    ⟨5, 0, 1, 7,
      [[tg 367, tg 5632], [tg 471, tg 5736], [tg 497, tg 5762], [tg 601, tg 5866]],
      [tg 455263, tg 460528]⟩,
    ⟨5, 0, 2, 6,
      [[tg 380, tg 5645], [tg 406, tg 5671], [tg 484, tg 5749], [tg 523, tg 5788], [tg 614, tg 5879]],
      [tg 606908, tg 612173]⟩,
    ⟨5, 0, 3, 8,
      [[tg 393, tg 5658], [tg 419, tg 5684], [tg 536, tg 5801], [tg 360, tg 5625], [tg 627, tg 5892]],
      [tg 606921, tg 612186]⟩,
    ⟨5, 0, 4, 6,
      [[tg 406, tg 5671], [tg 497, tg 5762], [tg 549, tg 5814], [tg 614, tg 5879], [tg 640, tg 5905]],
      [tg 606934, tg 612199]⟩,
    ⟨5, 0, 5, 8,
      [[tg 419, tg 5684], [tg 510, tg 5775], [tg 562, tg 5827], [tg 627, tg 5892], [tg 653, tg 5918]],
      [tg 606947, tg 612212]⟩,
    ⟨5, 0, 6, 5,
      [[tg 432, tg 5697], [tg 523, tg 5788], [tg 575, tg 5840], [tg 666, tg 5931]],
      [tg 455328, tg 460593]⟩,
    ⟨5, 0, 7, 7,
      [[tg 445, tg 5710], [tg 536, tg 5801], [tg 575, tg 5840], [tg 679, tg 5944]],
      [tg 455341, tg 460606]⟩,
    ⟨5, 0, 8, 6,
      [[tg 458, tg 5723], [tg 549, tg 5814], [tg 562, tg 5827], [tg 692, tg 5957]],
      [tg 455354, tg 460619]⟩,
    ⟨6, 0, 0, 9,
      [[tg 471, tg 5736], [tg 515, tg 63695], [tg 601, tg 5866], [tg 705, tg 5970]],
      [tg 455367, tg 460632]⟩,
    ⟨6, 0, 1, 8,
      [[tg 484, tg 5749], [tg 588, tg 5853], [tg 614, tg 5879], [tg 718, tg 5983]],
      [tg 455380, tg 460645]⟩,
    ⟨6, 0, 2, 7,
      [[tg 497, tg 5762], [tg 523, tg 5788], [tg 601, tg 5866], [tg 640, tg 5905], [tg 731, tg 5996]],
      [tg 607025, tg 612290]⟩,
    ⟨6, 0, 3, 9,
      [[tg 510, tg 5775], [tg 536, tg 5801], [tg 653, tg 5918], [tg 477, tg 5742], [tg 744, tg 6009]],
      [tg 607038, tg 612303]⟩,
    ⟨6, 0, 4, 7,
      [[tg 523, tg 5788], [tg 614, tg 5879], [tg 666, tg 5931], [tg 731, tg 5996], [tg 757, tg 6022]],
      [tg 607051, tg 612316]⟩,
    ⟨6, 0, 5, 9,
      [[tg 536, tg 5801], [tg 627, tg 5892], [tg 679, tg 5944], [tg 744, tg 6009], [tg 770, tg 6035]],
      [tg 607064, tg 612329]⟩,
    ⟨6, 0, 6, 6,
      [[tg 549, tg 5814], [tg 640, tg 5905], [tg 692, tg 5957], [tg 783, tg 6048]],
      [tg 455445, tg 460710]⟩,
    ⟨6, 0, 7, 8,
      [[tg 562, tg 5827], [tg 653, tg 5918], [tg 692, tg 5957], [tg 796, tg 6061]],
      [tg 455458, tg 460723]⟩,
    ⟨6, 0, 8, 7,
      [[tg 575, tg 5840], [tg 666, tg 5931], [tg 679, tg 5944], [tg 809, tg 6074]],
      [tg 455471, tg 460736]⟩,
    ⟨7, 0, 0, 10,
      [[tg 588, tg 5853], [tg 632, tg 63812], [tg 718, tg 5983], [tg 822, tg 6087]],
      [tg 455484, tg 460749]⟩,
    ⟨7, 0, 1, 9,
      [[tg 601, tg 5866], [tg 705, tg 5970], [tg 731, tg 5996], [tg 835, tg 6100]],
      [tg 455497, tg 460762]⟩,
    ⟨7, 0, 2, 8,
      [[tg 614, tg 5879], [tg 640, tg 5905], [tg 718, tg 5983], [tg 757, tg 6022], [tg 848, tg 6113]],
      [tg 607142, tg 612407]⟩,
    ⟨7, 0, 3, 10,
      [[tg 627, tg 5892], [tg 653, tg 5918], [tg 770, tg 6035], [tg 594, tg 5859], [tg 861, tg 6126]],
      [tg 607155, tg 612420]⟩,
    ⟨7, 0, 4, 8,
      [[tg 640, tg 5905], [tg 731, tg 5996], [tg 783, tg 6048], [tg 848, tg 6113], [tg 874, tg 6139]],
      [tg 607168, tg 612433]⟩,
    ⟨7, 0, 5, 10,
      [[tg 653, tg 5918], [tg 744, tg 6009], [tg 796, tg 6061], [tg 861, tg 6126], [tg 887, tg 6152]],
      [tg 607181, tg 612446]⟩,
    ⟨7, 0, 6, 7,
      [[tg 666, tg 5931], [tg 757, tg 6022], [tg 809, tg 6074], [tg 900, tg 6165]],
      [tg 455562, tg 460827]⟩,
    ⟨7, 0, 7, 9,
      [[tg 679, tg 5944], [tg 770, tg 6035], [tg 809, tg 6074], [tg 913, tg 6178]],
      [tg 455575, tg 460840]⟩,
    ⟨7, 0, 8, 8,
      [[tg 692, tg 5957], [tg 783, tg 6048], [tg 796, tg 6061], [tg 926, tg 6191]],
      [tg 455588, tg 460853]⟩,
    ⟨8, 0, 0, 11,
      [[tg 705, tg 5970], [tg 749, tg 63929], [tg 835, tg 6100], [tg 939, tg 6204]],
      [tg 455601, tg 460866]⟩,
    ⟨8, 0, 1, 10,
      [[tg 718, tg 5983], [tg 822, tg 6087], [tg 848, tg 6113], [tg 952, tg 6217]],
      [tg 455614, tg 460879]⟩,
    ⟨8, 0, 2, 9,
      [[tg 731, tg 5996], [tg 757, tg 6022], [tg 835, tg 6100], [tg 874, tg 6139], [tg 965, tg 6230]],
      [tg 607259, tg 612524]⟩,
    ⟨8, 0, 3, 11,
      [[tg 744, tg 6009], [tg 770, tg 6035], [tg 887, tg 6152], [tg 711, tg 5976], [tg 978, tg 6243]],
      [tg 607272, tg 612537]⟩,
    ⟨8, 0, 4, 9,
      [[tg 757, tg 6022], [tg 848, tg 6113], [tg 900, tg 6165], [tg 965, tg 6230], [tg 991, tg 6256]],
      [tg 607285, tg 612550]⟩,
    ⟨8, 0, 5, 11,
      [[tg 770, tg 6035], [tg 861, tg 6126], [tg 913, tg 6178], [tg 978, tg 6243], [tg 1004, tg 6269]],
      [tg 607298, tg 612563]⟩,
    ⟨8, 0, 6, 8,
      [[tg 783, tg 6048], [tg 874, tg 6139], [tg 926, tg 6191], [tg 1017, tg 6282]],
      [tg 455679, tg 460944]⟩,
    ⟨8, 0, 7, 10,
      [[tg 796, tg 6061], [tg 887, tg 6152], [tg 926, tg 6191], [tg 1030, tg 6295]],
      [tg 455692, tg 460957]⟩,
    ⟨8, 0, 8, 9,
      [[tg 809, tg 6074], [tg 900, tg 6165], [tg 913, tg 6178], [tg 1043, tg 6308]],
      [tg 455705, tg 460970]⟩,
    ⟨9, 0, 0, 12,
      [[tg 822, tg 6087], [tg 866, tg 64046], [tg 952, tg 6217], [tg 4215, tg 9480]],
      [tg 455718, tg 460983]⟩,
    ⟨9, 0, 1, 11,
      [[tg 835, tg 6100], [tg 939, tg 6204], [tg 965, tg 6230], [tg 4228, tg 9493]],
      [tg 455731, tg 460996]⟩,
    ⟨9, 0, 2, 10,
      [[tg 848, tg 6113], [tg 874, tg 6139], [tg 952, tg 6217], [tg 991, tg 6256], [tg 4241, tg 9506]],
      [tg 607376, tg 612641]⟩,
    ⟨9, 0, 3, 12,
      [[tg 861, tg 6126], [tg 887, tg 6152], [tg 1004, tg 6269], [tg 828, tg 6093], [tg 4254, tg 9519]],
      [tg 607389, tg 612654]⟩,
    ⟨9, 0, 4, 10,
      [[tg 874, tg 6139], [tg 965, tg 6230], [tg 1017, tg 6282], [tg 4241, tg 9506], [tg 4267, tg 9532]],
      [tg 607402, tg 612667]⟩,
    ⟨9, 0, 5, 12,
      [[tg 887, tg 6152], [tg 978, tg 6243], [tg 1030, tg 6295], [tg 4254, tg 9519], [tg 4280, tg 9545]],
      [tg 607415, tg 612680]⟩,
    ⟨9, 0, 6, 9,
      [[tg 900, tg 6165], [tg 991, tg 6256], [tg 1043, tg 6308], [tg 4293, tg 9558]],
      [tg 455796, tg 461061]⟩,
    ⟨9, 0, 7, 11,
      [[tg 913, tg 6178], [tg 1004, tg 6269], [tg 1043, tg 6308], [tg 4306, tg 9571]],
      [tg 455809, tg 461074]⟩,
    ⟨9, 0, 8, 10,
      [[tg 926, tg 6191], [tg 1017, tg 6282], [tg 1030, tg 6295], [tg 4319, tg 9584]],
      [tg 455822, tg 461087]⟩]⟩,
  ⟨1, 1, 1, 0, 0, [(-1, 1, 0), (1, -1, 0), (1, 1, 2)], 1, 1, 2, 2, 0, 0, 0, 0,
   [⟨1, 1, 0, 5,
      [[tg 10, tg 5275], [tg 42, tg 12684], [tg 17, tg 5282], [tg 9, tg 63189]],
      [tg 454938, tg 467580]⟩,
    ⟨1, 1, 1, 6,
      [[tg 23, tg 5288], [tg 4, tg 5269], [tg 30, tg 5295], [tg 22, tg 63202]],
      [tg 303268, tg 308533]⟩,
    ⟨1, 1, 2, 7,
      [[tg 36, tg 5301], [tg 62, tg 5327], [tg 17, tg 5282], [tg 56, tg 5321], [tg 35, tg 63215]],
      [tg 303281, tg 308546]⟩,
    ⟨1, 1, 3, 13,
      [[tg 49, tg 5314], [tg 75, tg 5340], [tg 69, tg 5334], [tg 4222, tg 9487], [tg 48, tg 63228]],
      [tg 454971, tg 460236]⟩,
    ⟨1, 1, 4, 8,
      [[tg 62, tg 5327], [tg 30, tg 5295], [tg 82, tg 5347], [tg 35, tg 63215], [tg 61, tg 63241]],
      [tg 454926, tg 460191]⟩,
    ⟨1, 1, 5, 12,
      [[tg 75, tg 5340], [tg 43, tg 5308], [tg 95, tg 5360], [tg 48, tg 63228], [tg 74, tg 63254]],
      [tg 151727, tg 156992]⟩,
    ⟨1, 1, 6, 9,
      [[tg 88, tg 5353], [tg 56, tg 5321], [tg 108, tg 5373], [tg 87, tg 63267]],
      [tg 303320, tg 308585]⟩,
    ⟨1, 1, 7, 11,
      [[tg 101, tg 5366], [tg 69, tg 5334], [tg 108, tg 5373], [tg 100, tg 63280]],
      [tg 303372, tg 308637]⟩,
    ⟨1, 1, 8, 10,
      [[tg 114, tg 5379], [tg 82, tg 5347], [tg 95, tg 5360], [tg 113, tg 63293]],
      [tg 303346, tg 308611]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 2)], -1, 1, 2, 2, 0, 0, 0, 0,
   [⟨-1, 1, 0, 6,
      [[tg 947, tg 6212], [tg 45, tg 2039], [tg 18, tg 5283], [tg 10, tg 63190]],
      [tg 454941, tg 456935]⟩,
    ⟨-1, 1, 1, 7,
      [[tg 960, tg 6225], [tg 5, tg 5270], [tg 31, tg 5296], [tg 23, tg 63203]],
      [tg 303269, tg 308534]⟩,
    ⟨-1, 1, 2, 8,
      [[tg 973, tg 6238], [tg 999, tg 6264], [tg 18, tg 5283], [tg 57, tg 5322], [tg 36, tg 63216]],
      [tg 303282, tg 308547]⟩,
    ⟨-1, 1, 3, 13,
      [[tg 986, tg 6251], [tg 1012, tg 6277], [tg 70, tg 5335], [tg 50554, tg 113734], [tg 49, tg 63229]],
      [tg 151702, tg 156967]⟩,
    ⟨-1, 1, 4, 8,
      [[tg 999, tg 6264], [tg 31, tg 5296], [tg 83, tg 5348], [tg 36, tg 63216], [tg 62, tg 63242]],
      [tg 151668, tg 214848]⟩,
    ⟨-1, 1, 5, 12,
      [[tg 1012, tg 6277], [tg 44, tg 5309], [tg 96, tg 5361], [tg 49, tg 63229], [tg 75, tg 63255]],
      [tg 151728, tg 156993]⟩,
    ⟨-1, 1, 6, 9,
      [[tg 1025, tg 6290], [tg 57, tg 5322], [tg 109, tg 5374], [tg 88, tg 63268]],
      [tg 303321, tg 308586]⟩,
    ⟨-1, 1, 7, 11,
      [[tg 1038, tg 6303], [tg 70, tg 5335], [tg 109, tg 5374], [tg 101, tg 63281]],
      [tg 303373, tg 308638]⟩,
    ⟨-1, 1, 8, 10,
      [[tg 1051, tg 6316], [tg 83, tg 5348], [tg 96, tg 5361], [tg 114, tg 63294]],
      [tg 303347, tg 308612]⟩]⟩,
  ⟨1, -9, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 1)], -1, 0, 1, 9, 0, 0, 0, 0,
   [⟨-1, 0, 0, 5,
      [[tg 123, tg 5388], [tg 40, tg 1104], [tg 19, tg 5284], [tg 0, tg 1995]],
      [tg 151651, tg 156916]⟩,
    ⟨-1, 0, 1, 4,
      [[tg 136, tg 5401], [tg 6, tg 5271], [tg 32, tg 5297], [tg 13, tg 2008]],
      [tg 303296, tg 308561]⟩,
    ⟨-1, 0, 2, 3,
      [[tg 149, tg 5414], [tg 175, tg 5440], [tg 19, tg 5284], [tg 58, tg 5323], [tg 26, tg 2021]],
      [tg 151690, tg 156955]⟩,
    ⟨-1, 0, 3, 5,
      [[tg 162, tg 5427], [tg 188, tg 5453], [tg 71, tg 5336], [tg 5, tg 12647], [tg 39, tg 2034]],
      [tg 151703, tg 156968]⟩,
    ⟨-1, 0, 4, 2,
      [[tg 175, tg 5440], [tg 32, tg 5297], [tg 84, tg 5349], [tg 26, tg 2021], [tg 52, tg 2047]],
      [tg 151716, tg 156981]⟩,
    ⟨-1, 0, 5, 4,
      [[tg 188, tg 5453], [tg 45, tg 5310], [tg 97, tg 5362], [tg 39, tg 2034], [tg 65, tg 2060]],
      [tg 151729, tg 156994]⟩,
    ⟨-1, 0, 6, 1,
      [[tg 201, tg 5466], [tg 58, tg 5323], [tg 110, tg 5375], [tg 78, tg 2073]],
      [tg 78, tg 2073]⟩,
    ⟨-1, 0, 7, 3,
      [[tg 214, tg 5479], [tg 71, tg 5336], [tg 110, tg 5375], [tg 91, tg 2086]],
      [tg 303374, tg 308639]⟩,
    ⟨-1, 0, 8, 2,
      [[tg 227, tg 5492], [tg 84, tg 5349], [tg 97, tg 5362], [tg 104, tg 2099]],
      [tg 303348, tg 308613]⟩,
    ⟨-2, 0, 0, 6,
      [[tg 240, tg 5505], [tg 987, tg 6252], [tg 136, tg 5401], [tg 6, tg 5271]],
      [tg 151768, tg 157033]⟩,
    ⟨-2, 0, 1, 5,
      [[tg 253, tg 5518], [tg 123, tg 5388], [tg 149, tg 5414], [tg 19, tg 5284]],
      [tg 303413, tg 308678]⟩,
    ⟨-2, 0, 2, 4,
      [[tg 266, tg 5531], [tg 292, tg 5557], [tg 136, tg 5401], [tg 175, tg 5440], [tg 32, tg 5297]],
      [tg 151807, tg 157072]⟩,
    ⟨-2, 0, 3, 6,
      [[tg 279, tg 5544], [tg 305, tg 5570], [tg 188, tg 5453], [tg 947, tg 64127], [tg 45, tg 5310]],
      [tg 151820, tg 157085]⟩,
    ⟨-2, 0, 4, 3,
      [[tg 292, tg 5557], [tg 149, tg 5414], [tg 201, tg 5466], [tg 32, tg 5297], [tg 58, tg 5323]],
      [tg 151833, tg 157098]⟩,
    ⟨-2, 0, 5, 5,
      [[tg 305, tg 5570], [tg 162, tg 5427], [tg 214, tg 5479], [tg 45, tg 5310], [tg 71, tg 5336]],
      [tg 151846, tg 157111]⟩,
    ⟨-2, 0, 6, 2,
      [[tg 318, tg 5583], [tg 175, tg 5440], [tg 227, tg 5492], [tg 84, tg 5349]],
      [tg 84, tg 5349]⟩,
    ⟨-2, 0, 7, 4,
      [[tg 331, tg 5596], [tg 188, tg 5453], [tg 227, tg 5492], [tg 97, tg 5362]],
      [tg 303491, tg 308756]⟩,
    ⟨-2, 0, 8, 3,
      [[tg 344, tg 5609], [tg 201, tg 5466], [tg 214, tg 5479], [tg 110, tg 5375]],
      [tg 303465, tg 308730]⟩,
    ⟨-3, 0, 0, 7,
      [[tg 357, tg 5622], [tg 870, tg 6135], [tg 253, tg 5518], [tg 123, tg 5388]],
      [tg 151885, tg 157150]⟩,
    ⟨-3, 0, 1, 6,
      [[tg 370, tg 5635], [tg 240, tg 5505], [tg 266, tg 5531], [tg 136, tg 5401]],
      [tg 303530, tg 308795]⟩,
    ⟨-3, 0, 2, 5,
      [[tg 383, tg 5648], [tg 409, tg 5674], [tg 253, tg 5518], [tg 292, tg 5557], [tg 149, tg 5414]],
      [tg 151924, tg 157189]⟩,
    ⟨-3, 0, 3, 7,
      [[tg 396, tg 5661], [tg 422, tg 5687], [tg 305, tg 5570], [tg 830, tg 64010], [tg 162, tg 5427]],
      [tg 151937, tg 157202]⟩,
    ⟨-3, 0, 4, 4,
      [[tg 409, tg 5674], [tg 266, tg 5531], [tg 318, tg 5583], [tg 149, tg 5414], [tg 175, tg 5440]],
      [tg 151950, tg 157215]⟩,
    ⟨-3, 0, 5, 6,
      [[tg 422, tg 5687], [tg 279, tg 5544], [tg 331, tg 5596], [tg 162, tg 5427], [tg 188, tg 5453]],
      [tg 151963, tg 157228]⟩,
    ⟨-3, 0, 6, 3,
      [[tg 435, tg 5700], [tg 292, tg 5557], [tg 344, tg 5609], [tg 201, tg 5466]],
      [tg 201, tg 5466]⟩,
    ⟨-3, 0, 7, 5,
      [[tg 448, tg 5713], [tg 305, tg 5570], [tg 344, tg 5609], [tg 214, tg 5479]],
      [tg 303608, tg 308873]⟩,
    ⟨-3, 0, 8, 4,
      [[tg 461, tg 5726], [tg 318, tg 5583], [tg 331, tg 5596], [tg 227, tg 5492]],
      [tg 303582, tg 308847]⟩,
    ⟨-4, 0, 0, 8,
      [[tg 474, tg 5739], [tg 753, tg 6018], [tg 370, tg 5635], [tg 240, tg 5505]],
      [tg 152002, tg 157267]⟩,
    ⟨-4, 0, 1, 7,
      [[tg 487, tg 5752], [tg 357, tg 5622], [tg 383, tg 5648], [tg 253, tg 5518]],
      [tg 303647, tg 308912]⟩,
    ⟨-4, 0, 2, 6,
      [[tg 500, tg 5765], [tg 526, tg 5791], [tg 370, tg 5635], [tg 409, tg 5674], [tg 266, tg 5531]],
      [tg 152041, tg 157306]⟩,
    ⟨-4, 0, 3, 8,
      [[tg 513, tg 5778], [tg 539, tg 5804], [tg 422, tg 5687], [tg 713, tg 63893], [tg 279, tg 5544]],
      [tg 152054, tg 157319]⟩,
    ⟨-4, 0, 4, 5,
      [[tg 526, tg 5791], [tg 383, tg 5648], [tg 435, tg 5700], [tg 266, tg 5531], [tg 292, tg 5557]],
      [tg 152067, tg 157332]⟩,
    ⟨-4, 0, 5, 7,
      [[tg 539, tg 5804], [tg 396, tg 5661], [tg 448, tg 5713], [tg 279, tg 5544], [tg 305, tg 5570]],
      [tg 152080, tg 157345]⟩,
    ⟨-4, 0, 6, 4,
      [[tg 552, tg 5817], [tg 409, tg 5674], [tg 461, tg 5726], [tg 318, tg 5583]],
      [tg 318, tg 5583]⟩,
    ⟨-4, 0, 7, 6,
      [[tg 565, tg 5830], [tg 422, tg 5687], [tg 461, tg 5726], [tg 331, tg 5596]],
      [tg 303725, tg 308990]⟩,
    ⟨-4, 0, 8, 5,
      [[tg 578, tg 5843], [tg 435, tg 5700], [tg 448, tg 5713], [tg 344, tg 5609]],
      [tg 303699, tg 308964]⟩,
    ⟨-5, 0, 0, 9,
      [[tg 591, tg 5856], [tg 636, tg 5901], [tg 487, tg 5752], [tg 357, tg 5622]],
      [tg 152119, tg 157384]⟩,
    ⟨-5, 0, 1, 8,
      [[tg 604, tg 5869], [tg 474, tg 5739], [tg 500, tg 5765], [tg 370, tg 5635]],
      [tg 303764, tg 309029]⟩,
    ⟨-5, 0, 2, 7,
      [[tg 617, tg 5882], [tg 643, tg 5908], [tg 487, tg 5752], [tg 526, tg 5791], [tg 383, tg 5648]],
      [tg 152158, tg 157423]⟩,
    ⟨-5, 0, 3, 9,
      [[tg 630, tg 5895], [tg 656, tg 5921], [tg 539, tg 5804], [tg 596, tg 63776], [tg 396, tg 5661]],
      [tg 152171, tg 157436]⟩,
    ⟨-5, 0, 4, 6,
      [[tg 643, tg 5908], [tg 500, tg 5765], [tg 552, tg 5817], [tg 383, tg 5648], [tg 409, tg 5674]],
      [tg 152184, tg 157449]⟩,
    ⟨-5, 0, 5, 8,
      [[tg 656, tg 5921], [tg 513, tg 5778], [tg 565, tg 5830], [tg 396, tg 5661], [tg 422, tg 5687]],
      [tg 152197, tg 157462]⟩,
    ⟨-5, 0, 6, 5,
      [[tg 669, tg 5934], [tg 526, tg 5791], [tg 578, tg 5843], [tg 435, tg 5700]],
      [tg 435, tg 5700]⟩,
    ⟨-5, 0, 7, 7,
      [[tg 682, tg 5947], [tg 539, tg 5804], [tg 578, tg 5843], [tg 448, tg 5713]],
      [tg 303842, tg 309107]⟩,
    ⟨-5, 0, 8, 6,
      [[tg 695, tg 5960], [tg 552, tg 5817], [tg 565, tg 5830], [tg 461, tg 5726]],
      [tg 303816, tg 309081]⟩,
    ⟨-6, 0, 0, 10,
      [[tg 708, tg 5973], [tg 519, tg 5784], [tg 604, tg 5869], [tg 474, tg 5739]],
      [tg 152236, tg 157501]⟩,
    ⟨-6, 0, 1, 9,
      [[tg 721, tg 5986], [tg 591, tg 5856], [tg 617, tg 5882], [tg 487, tg 5752]],
      [tg 303881, tg 309146]⟩,
    ⟨-6, 0, 2, 8,
      [[tg 734, tg 5999], [tg 760, tg 6025], [tg 604, tg 5869], [tg 643, tg 5908], [tg 500, tg 5765]],
      [tg 152275, tg 157540]⟩,
    ⟨-6, 0, 3, 10,
      [[tg 747, tg 6012], [tg 773, tg 6038], [tg 656, tg 5921], [tg 479, tg 63659], [tg 513, tg 5778]],
      [tg 152288, tg 157553]⟩,
    ⟨-6, 0, 4, 7,
      [[tg 760, tg 6025], [tg 617, tg 5882], [tg 669, tg 5934], [tg 500, tg 5765], [tg 526, tg 5791]],
      [tg 152301, tg 157566]⟩,
    ⟨-6, 0, 5, 9,
      [[tg 773, tg 6038], [tg 630, tg 5895], [tg 682, tg 5947], [tg 513, tg 5778], [tg 539, tg 5804]],
      [tg 152314, tg 157579]⟩,
    ⟨-6, 0, 6, 6,
      [[tg 786, tg 6051], [tg 643, tg 5908], [tg 695, tg 5960], [tg 552, tg 5817]],
      [tg 552, tg 5817]⟩,
    ⟨-6, 0, 7, 8,
      [[tg 799, tg 6064], [tg 656, tg 5921], [tg 695, tg 5960], [tg 565, tg 5830]],
      [tg 303959, tg 309224]⟩,
    ⟨-6, 0, 8, 7,
      [[tg 812, tg 6077], [tg 669, tg 5934], [tg 682, tg 5947], [tg 578, tg 5843]],
      [tg 303933, tg 309198]⟩,
    ⟨-7, 0, 0, 11,
      [[tg 825, tg 6090], [tg 402, tg 5667], [tg 721, tg 5986], [tg 591, tg 5856]],
      [tg 152353, tg 157618]⟩,
    ⟨-7, 0, 1, 10,
      [[tg 838, tg 6103], [tg 708, tg 5973], [tg 734, tg 5999], [tg 604, tg 5869]],
      [tg 303998, tg 309263]⟩,
    ⟨-7, 0, 2, 9,
      [[tg 851, tg 6116], [tg 877, tg 6142], [tg 721, tg 5986], [tg 760, tg 6025], [tg 617, tg 5882]],
      [tg 152392, tg 157657]⟩,
    ⟨-7, 0, 3, 11,
      [[tg 864, tg 6129], [tg 890, tg 6155], [tg 773, tg 6038], [tg 362, tg 63542], [tg 630, tg 5895]],
      [tg 152405, tg 157670]⟩,
    ⟨-7, 0, 4, 8,
      [[tg 877, tg 6142], [tg 734, tg 5999], [tg 786, tg 6051], [tg 617, tg 5882], [tg 643, tg 5908]],
      [tg 152418, tg 157683]⟩,
    ⟨-7, 0, 5, 10,
      [[tg 890, tg 6155], [tg 747, tg 6012], [tg 799, tg 6064], [tg 630, tg 5895], [tg 656, tg 5921]],
      [tg 152431, tg 157696]⟩,
    ⟨-7, 0, 6, 7,
      [[tg 903, tg 6168], [tg 760, tg 6025], [tg 812, tg 6077], [tg 669, tg 5934]],
      [tg 669, tg 5934]⟩,
    ⟨-7, 0, 7, 9,
      [[tg 916, tg 6181], [tg 773, tg 6038], [tg 812, tg 6077], [tg 682, tg 5947]],
      [tg 304076, tg 309341]⟩,
    ⟨-7, 0, 8, 8,
      [[tg 929, tg 6194], [tg 786, tg 6051], [tg 799, tg 6064], [tg 695, tg 5960]],
      [tg 304050, tg 309315]⟩,
    ⟨-8, 0, 0, 12,
      [[tg 942, tg 6207], [tg 285, tg 5550], [tg 838, tg 6103], [tg 708, tg 5973]],
      [tg 152470, tg 157735]⟩,
    ⟨-8, 0, 1, 11,
      [[tg 955, tg 6220], [tg 825, tg 6090], [tg 851, tg 6116], [tg 721, tg 5986]],
      [tg 304115, tg 309380]⟩,
    ⟨-8, 0, 2, 10,
      [[tg 968, tg 6233], [tg 994, tg 6259], [tg 838, tg 6103], [tg 877, tg 6142], [tg 734, tg 5999]],
      [tg 152509, tg 157774]⟩,
    ⟨-8, 0, 3, 12,
      [[tg 981, tg 6246], [tg 1007, tg 6272], [tg 890, tg 6155], [tg 245, tg 63425], [tg 747, tg 6012]],
      [tg 152522, tg 157787]⟩,
    ⟨-8, 0, 4, 9,
      [[tg 994, tg 6259], [tg 851, tg 6116], [tg 903, tg 6168], [tg 734, tg 5999], [tg 760, tg 6025]],
      [tg 152535, tg 157800]⟩,
    ⟨-8, 0, 5, 11,
      [[tg 1007, tg 6272], [tg 864, tg 6129], [tg 916, tg 6181], [tg 747, tg 6012], [tg 773, tg 6038]],
      [tg 152548, tg 157813]⟩,
    ⟨-8, 0, 6, 8,
      [[tg 1020, tg 6285], [tg 877, tg 6142], [tg 929, tg 6194], [tg 786, tg 6051]],
      [tg 786, tg 6051]⟩,
    ⟨-8, 0, 7, 10,
      [[tg 1033, tg 6298], [tg 890, tg 6155], [tg 929, tg 6194], [tg 799, tg 6064]],
      [tg 304193, tg 309458]⟩,
    ⟨-8, 0, 8, 9,
      [[tg 1046, tg 6311], [tg 903, tg 6168], [tg 916, tg 6181], [tg 812, tg 6077]],
      [tg 304167, tg 309432]⟩,
    ⟨-9, 0, 0, 13,
      [[tg 4218, tg 9483], [tg 168, tg 5433], [tg 955, tg 6220], [tg 825, tg 6090]],
      [tg 152587, tg 157852]⟩,
    ⟨-9, 0, 1, 12,
      [[tg 4231, tg 9496], [tg 942, tg 6207], [tg 968, tg 6233], [tg 838, tg 6103]],
      [tg 304232, tg 309497]⟩,
    ⟨-9, 0, 2, 11,
      [[tg 4244, tg 9509], [tg 4270, tg 9535], [tg 955, tg 6220], [tg 994, tg 6259], [tg 851, tg 6116]],
      [tg 152626, tg 157891]⟩,
    ⟨-9, 0, 3, 13,
      [[tg 4257, tg 9522], [tg 4283, tg 9548], [tg 1007, tg 6272], [tg 128, tg 63308], [tg 864, tg 6129]],
      [tg 152639, tg 157904]⟩,
    ⟨-9, 0, 4, 10,
      [[tg 4270, tg 9535], [tg 968, tg 6233], [tg 1020, tg 6285], [tg 851, tg 6116], [tg 877, tg 6142]],
      [tg 152652, tg 157917]⟩,
    ⟨-9, 0, 5, 12,
      [[tg 4283, tg 9548], [tg 981, tg 6246], [tg 1033, tg 6298], [tg 864, tg 6129], [tg 890, tg 6155]],
      [tg 152665, tg 157930]⟩,
    ⟨-9, 0, 6, 9,
      [[tg 4296, tg 9561], [tg 994, tg 6259], [tg 1046, tg 6311], [tg 903, tg 6168]],
      [tg 903, tg 6168]⟩,
    ⟨-9, 0, 7, 11,
      [[tg 4309, tg 9574], [tg 1007, tg 6272], [tg 1046, tg 6311], [tg 916, tg 6181]],
      [tg 304310, tg 309575]⟩,
    ⟨-9, 0, 8, 10,
      [[tg 4322, tg 9587], [tg 1020, tg 6285], [tg 1033, tg 6298], [tg 929, tg 6194]],
      [tg 304284, tg 309549]⟩]⟩,
  ⟨2, -1, -1, 1, -1, [(-1, -1, 1), (1, -1, 1)], -1, -1, 1, 2, 1, -1, 1, 2,
   [⟨0, -2, 0, 22,
      [[tg 4336, tg 9601, tg 80152, tg 85417], [tg 54919, tg 60184, tg 130735, tg 136000], [tg 20, tg 5285, tg 75836, tg 81101], [tg 50668, tg 55933, tg 126484, tg 131749]],
      [tg 151652, tg 156917, tg 227468, tg 232733]⟩,
    ⟨0, -2, 1, 21,
      [[tg 4349, tg 9614, tg 80165, tg 85430], [tg 7, tg 5272, tg 75823, tg 81088], [tg 33, tg 5298, tg 75849, tg 81114], [tg 50681, tg 55946, tg 126497, tg 131762]],
      [tg 303297, tg 308562, tg 379113, tg 384378]⟩,
    ⟨0, -2, 2, 20,
      [[tg 4362, tg 9627, tg 80178, tg 85443], [tg 4388, tg 9653, tg 80204, tg 85469], [tg 20, tg 5285, tg 75836, tg 81101], [tg 59, tg 5324, tg 75875, tg 81140], [tg 50694, tg 55959, tg 126510, tg 131775]],
      [tg 459284, tg 464549, tg 535100, tg 540365]⟩,
    ⟨0, -2, 3, 14,
      [[tg 4375, tg 9640, tg 80191, tg 85456], [tg 4401, tg 9666, tg 80217, tg 85482], [tg 72, tg 5337, tg 75888, tg 81153], [tg 124, tg 5389, tg 75940, tg 81205], [tg 50707, tg 55972, tg 126523, tg 131788]],
      [tg 151756, tg 157021, tg 227572, tg 232837]⟩,
    ⟨0, -2, 4, 19,
      [[tg 4388, tg 9653, tg 80204, tg 85469], [tg 33, tg 5298, tg 75849, tg 81114], [tg 85, tg 5350, tg 75901, tg 81166], [tg 50694, tg 55959, tg 126510, tg 131775], [tg 50720, tg 55985, tg 126536, tg 131801]],
      [tg 151717, tg 156982, tg 227533, tg 232798]⟩,
    ⟨0, -2, 5, 15,
      [[tg 4401, tg 9666, tg 80217, tg 85482], [tg 46, tg 5311, tg 75862, tg 81127], [tg 98, tg 5363, tg 75914, tg 81179], [tg 50707, tg 55972, tg 126523, tg 131788], [tg 50733, tg 55998, tg 126549, tg 131814]],
      [tg 303310, tg 308575, tg 379126, tg 384391]⟩,
    ⟨0, -2, 6, 18,
      [[tg 4414, tg 9679, tg 80230, tg 85495], [tg 59, tg 5324, tg 75875, tg 81140], [tg 111, tg 5376, tg 75927, tg 81192], [tg 50746, tg 56011, tg 126562, tg 131827]],
      [tg 151743, tg 157008, tg 227559, tg 232824]⟩,
    ⟨0, -2, 7, 16,
      [[tg 4427, tg 9692, tg 80243, tg 85508], [tg 72, tg 5337, tg 75888, tg 81153], [tg 111, tg 5376, tg 75927, tg 81192], [tg 50759, tg 56024, tg 126575, tg 131840]],
      [tg 303336, tg 308601, tg 379152, tg 384417]⟩,
    ⟨0, -2, 8, 17,
      [[tg 4440, tg 9705, tg 80256, tg 85521], [tg 85, tg 5350, tg 75901, tg 81166], [tg 98, tg 5363, tg 75914, tg 81179], [tg 50772, tg 56037, tg 126588, tg 131853]],
      [tg 303362, tg 308627, tg 379178, tg 384443]⟩,
    ⟨0, -1, 0, 13,
      [[tg 1, tg 5266, tg 25279, tg 30544], [tg 46, tg 5311, tg 75862, tg 81127], [tg 137, tg 5402, tg 75953, tg 81218], [tg 2, tg 1060, tg 6320, tg 76876]],
      [tg 151769, tg 157034, tg 227585, tg 232850]⟩,
    ⟨0, -1, 1, 12,
      [[tg 14, tg 5279, tg 25292, tg 30557], [tg 124, tg 5389, tg 75940, tg 81205], [tg 150, tg 5415, tg 75966, tg 81231], [tg 15, tg 1073, tg 6333, tg 76889]],
      [tg 303414, tg 308679, tg 379230, tg 384495]⟩,
    ⟨0, -1, 2, 11,
      [[tg 27, tg 5292, tg 25305, tg 30570], [tg 53, tg 5318, tg 25331, tg 30596], [tg 137, tg 5402, tg 75953, tg 81218], [tg 176, tg 5441, tg 75992, tg 81257], [tg 28, tg 1086, tg 6346, tg 76902]],
      [tg 454949, tg 460214, tg 480227, tg 485492]⟩,
    ⟨0, -1, 3, 5,
      [[tg 40, tg 5305, tg 25318, tg 30583], [tg 66, tg 5331, tg 25344, tg 30609], [tg 189, tg 5454, tg 76005, tg 81270], [tg 0, tg 1054, tg 2108, tg 26332], [tg 41, tg 1099, tg 6359, tg 76915]],
      [tg 151632, tg 152686, tg 153740, tg 177964]⟩,
    ⟨0, -1, 4, 10,
      [[tg 53, tg 5318, tg 25331, tg 30596], [tg 150, tg 5415, tg 75966, tg 81231], [tg 202, tg 5467, tg 76018, tg 81283], [tg 28, tg 1086, tg 6346, tg 76902], [tg 54, tg 1112, tg 6372, tg 76928]],
      [tg 151834, tg 157099, tg 227650, tg 232915]⟩,
    ⟨0, -1, 5, 6,
      [[tg 66, tg 5331, tg 25344, tg 30609], [tg 163, tg 5428, tg 75979, tg 81244], [tg 215, tg 5480, tg 76031, tg 81296], [tg 41, tg 1099, tg 6359, tg 76915], [tg 67, tg 1125, tg 6385, tg 76941]],
      [tg 303427, tg 308692, tg 379243, tg 384508]⟩,
    ⟨0, -1, 6, 9,
      [[tg 79, tg 5344, tg 25357, tg 30622], [tg 176, tg 5441, tg 75992, tg 81257], [tg 228, tg 5493, tg 76044, tg 81309], [tg 80, tg 1138, tg 6398, tg 76954]],
      [tg 151860, tg 157125, tg 227676, tg 232941]⟩,
    ⟨0, -1, 7, 7,
      [[tg 92, tg 5357, tg 25370, tg 30635], [tg 189, tg 5454, tg 76005, tg 81270], [tg 228, tg 5493, tg 76044, tg 81309], [tg 93, tg 1151, tg 6411, tg 76967]],
      [tg 303453, tg 308718, tg 379269, tg 384534]⟩,
    ⟨0, -1, 8, 8,
      [[tg 105, tg 5370, tg 25383, tg 30648], [tg 202, tg 5467, tg 76018, tg 81283], [tg 215, tg 5480, tg 76031, tg 81296], [tg 106, tg 1164, tg 6424, tg 76980]],
      [tg 303479, tg 308744, tg 379295, tg 384560]⟩]⟩,
  ⟨2, 1, -1, 9, 0, [(0, -9, 1), (1, 1, 1)], 0, -9, 1, 9, 1, 1, 1, 9,
   [⟨2, -1, 0, 13,
      [[tg 2, tg 5267, tg 26216, tg 31481], [tg 4253, tg 9518, tg 30467, tg 35732], [tg 21, tg 5286, tg 75837, tg 81102], [tg 125, tg 5390, tg 75941, tg 81206]],
      [tg 151653, tg 156918, tg 481112, tg 486377]⟩,
    ⟨2, -1, 1, 12,
      [[tg 15, tg 5280, tg 26229, tg 31494], [tg 8, tg 5273, tg 75824, tg 81089], [tg 34, tg 5299, tg 75850, tg 81115], [tg 138, tg 5403, tg 75954, tg 81219]],
      [tg 303298, tg 308563, tg 481125, tg 486390]⟩,
    ⟨2, -1, 2, 11,
      [[tg 28, tg 5293, tg 26242, tg 31507], [tg 54, tg 5319, tg 26268, tg 31533], [tg 21, tg 5286, tg 75837, tg 81102], [tg 60, tg 5325, tg 75876, tg 81141], [tg 151, tg 5416, tg 75967, tg 81232]],
      [tg 454950, tg 460215, tg 632770, tg 638035]⟩,
    ⟨2, -1, 3, 6,
      [[tg 41, tg 5306, tg 26255, tg 31520], [tg 67, tg 5332, tg 26281, tg 31546], [tg 73, tg 5338, tg 75889, tg 81154], [tg 120, tg 1178, tg 6438, tg 76994], [tg 164, tg 5429, tg 75980, tg 81245]],
      [tg 606569, tg 611834, tg 632783, tg 638048]⟩,
    ⟨2, -1, 4, 11,
      [[tg 54, tg 5319, tg 26268, tg 31533], [tg 34, tg 5299, tg 75850, tg 81115], [tg 86, tg 5351, tg 75902, tg 81167], [tg 151, tg 5416, tg 75967, tg 81232], [tg 177, tg 5442, tg 75993, tg 81258]],
      [tg 606582, tg 611847, tg 632796, tg 638061]⟩,
    ⟨2, -1, 5, 7,
      [[tg 67, tg 5332, tg 26281, tg 31546], [tg 47, tg 5312, tg 75863, tg 81128], [tg 99, tg 5364, tg 75915, tg 81180], [tg 164, tg 5429, tg 75980, tg 81245], [tg 190, tg 5455, tg 76006, tg 81271]],
      [tg 606595, tg 611860, tg 632809, tg 638074]⟩,
    ⟨2, -1, 6, 10,
      [[tg 80, tg 5345, tg 26294, tg 31559], [tg 60, tg 5325, tg 75876, tg 81141], [tg 112, tg 5377, tg 75928, tg 81193], [tg 203, tg 5468, tg 76019, tg 81284]],
      [tg 454976, tg 460241, tg 481190, tg 486455]⟩,
    ⟨2, -1, 7, 8,
      [[tg 93, tg 5358, tg 26307, tg 31572], [tg 73, tg 5338, tg 75889, tg 81154], [tg 112, tg 5377, tg 75928, tg 81193], [tg 216, tg 5481, tg 76032, tg 81297]],
      [tg 454989, tg 460254, tg 481203, tg 486468]⟩,
    ⟨2, -1, 8, 9,
      [[tg 106, tg 5371, tg 26320, tg 31585], [tg 86, tg 5351, tg 75902, tg 81167], [tg 99, tg 5364, tg 75915, tg 81180], [tg 229, tg 5494, tg 76045, tg 81310]],
      [tg 455002, tg 460267, tg 481216, tg 486481]⟩,
    ⟨3, -1, 0, 14,
      [[tg 8, tg 5273, tg 75824, tg 81089], [tg 4259, tg 9524, tg 80075, tg 85340], [tg 138, tg 5403, tg 75954, tg 81219], [tg 242, tg 5507, tg 76058, tg 81323]],
      [tg 454904, tg 460169, tg 530720, tg 535985]⟩,
    ⟨3, -1, 1, 13,
      [[tg 21, tg 5286, tg 75837, tg 81102], [tg 125, tg 5390, tg 75941, tg 81206], [tg 151, tg 5416, tg 75967, tg 81232], [tg 255, tg 5520, tg 76071, tg 81336]],
      [tg 454917, tg 460182, tg 530733, tg 535998]⟩,
    ⟨3, -1, 2, 12,
      [[tg 34, tg 5299, tg 75850, tg 81115], [tg 60, tg 5325, tg 75876, tg 81141], [tg 138, tg 5403, tg 75954, tg 81219], [tg 177, tg 5442, tg 75993, tg 81258], [tg 268, tg 5533, tg 76084, tg 81349]],
      [tg 606562, tg 611827, tg 682378, tg 687643]⟩,
    ⟨3, -1, 3, 7,
      [[tg 47, tg 5312, tg 75863, tg 81128], [tg 73, tg 5338, tg 75889, tg 81154], [tg 190, tg 5455, tg 76006, tg 81271], [tg 237, tg 1295, tg 6555, tg 77111], [tg 281, tg 5546, tg 76097, tg 81362]],
      [tg 606575, tg 611840, tg 682391, tg 687656]⟩,
    ⟨3, -1, 4, 12,
      [[tg 60, tg 5325, tg 75876, tg 81141], [tg 151, tg 5416, tg 75967, tg 81232], [tg 203, tg 5468, tg 76019, tg 81284], [tg 268, tg 5533, tg 76084, tg 81349], [tg 294, tg 5559, tg 76110, tg 81375]],
      [tg 606588, tg 611853, tg 682404, tg 687669]⟩,
    ⟨3, -1, 5, 8,
      [[tg 73, tg 5338, tg 75889, tg 81154], [tg 164, tg 5429, tg 75980, tg 81245], [tg 216, tg 5481, tg 76032, tg 81297], [tg 281, tg 5546, tg 76097, tg 81362], [tg 307, tg 5572, tg 76123, tg 81388]],
      [tg 606601, tg 611866, tg 682417, tg 687682]⟩,
    ⟨3, -1, 6, 11,
      [[tg 86, tg 5351, tg 75902, tg 81167], [tg 177, tg 5442, tg 75993, tg 81258], [tg 229, tg 5494, tg 76045, tg 81310], [tg 320, tg 5585, tg 76136, tg 81401]],
      [tg 454982, tg 460247, tg 530798, tg 536063]⟩,
    ⟨3, -1, 7, 9,
      [[tg 99, tg 5364, tg 75915, tg 81180], [tg 190, tg 5455, tg 76006, tg 81271], [tg 229, tg 5494, tg 76045, tg 81310], [tg 333, tg 5598, tg 76149, tg 81414]],
      [tg 454995, tg 460260, tg 530811, tg 536076]⟩,
    ⟨3, -1, 8, 10,
      [[tg 112, tg 5377, tg 75928, tg 81193], [tg 203, tg 5468, tg 76019, tg 81284], [tg 216, tg 5481, tg 76032, tg 81297], [tg 346, tg 5611, tg 76162, tg 81427]],
      [tg 455008, tg 460273, tg 530824, tg 536089]⟩,
    ⟨4, -1, 0, 15,
      [[tg 125, tg 5390, tg 75941, tg 81206], [tg 4376, tg 9641, tg 80192, tg 85457], [tg 255, tg 5520, tg 76071, tg 81336], [tg 359, tg 5624, tg 76175, tg 81440]],
      [tg 455021, tg 460286, tg 530837, tg 536102]⟩,
    ⟨4, -1, 1, 14,
      [[tg 138, tg 5403, tg 75954, tg 81219], [tg 242, tg 5507, tg 76058, tg 81323], [tg 268, tg 5533, tg 76084, tg 81349], [tg 372, tg 5637, tg 76188, tg 81453]],
      [tg 455034, tg 460299, tg 530850, tg 536115]⟩,
    ⟨4, -1, 2, 13,
      [[tg 151, tg 5416, tg 75967, tg 81232], [tg 177, tg 5442, tg 75993, tg 81258], [tg 255, tg 5520, tg 76071, tg 81336], [tg 294, tg 5559, tg 76110, tg 81375], [tg 385, tg 5650, tg 76201, tg 81466]],
      [tg 606679, tg 611944, tg 682495, tg 687760]⟩,
    ⟨4, -1, 3, 8,
      [[tg 164, tg 5429, tg 75980, tg 81245], [tg 190, tg 5455, tg 76006, tg 81271], [tg 307, tg 5572, tg 76123, tg 81388], [tg 354, tg 1412, tg 6672, tg 77228], [tg 398, tg 5663, tg 76214, tg 81479]],
      [tg 606692, tg 611957, tg 682508, tg 687773]⟩,
    ⟨4, -1, 4, 13,
      [[tg 177, tg 5442, tg 75993, tg 81258], [tg 268, tg 5533, tg 76084, tg 81349], [tg 320, tg 5585, tg 76136, tg 81401], [tg 385, tg 5650, tg 76201, tg 81466], [tg 411, tg 5676, tg 76227, tg 81492]],
      [tg 606705, tg 611970, tg 682521, tg 687786]⟩,
    ⟨4, -1, 5, 9,
      [[tg 190, tg 5455, tg 76006, tg 81271], [tg 281, tg 5546, tg 76097, tg 81362], [tg 333, tg 5598, tg 76149, tg 81414], [tg 398, tg 5663, tg 76214, tg 81479], [tg 424, tg 5689, tg 76240, tg 81505]],
      [tg 606718, tg 611983, tg 682534, tg 687799]⟩,
    ⟨4, -1, 6, 12,
      [[tg 203, tg 5468, tg 76019, tg 81284], [tg 294, tg 5559, tg 76110, tg 81375], [tg 346, tg 5611, tg 76162, tg 81427], [tg 437, tg 5702, tg 76253, tg 81518]],
      [tg 455099, tg 460364, tg 530915, tg 536180]⟩,
    ⟨4, -1, 7, 10,
      [[tg 216, tg 5481, tg 76032, tg 81297], [tg 307, tg 5572, tg 76123, tg 81388], [tg 346, tg 5611, tg 76162, tg 81427], [tg 450, tg 5715, tg 76266, tg 81531]],
      [tg 455112, tg 460377, tg 530928, tg 536193]⟩,
    ⟨4, -1, 8, 11,
      [[tg 229, tg 5494, tg 76045, tg 81310], [tg 320, tg 5585, tg 76136, tg 81401], [tg 333, tg 5598, tg 76149, tg 81414], [tg 463, tg 5728, tg 76279, tg 81544]],
      [tg 455125, tg 460390, tg 530941, tg 536206]⟩,
    ⟨5, -1, 0, 16,
      [[tg 242, tg 5507, tg 76058, tg 81323], [tg 4493, tg 9758, tg 80309, tg 85574], [tg 372, tg 5637, tg 76188, tg 81453], [tg 476, tg 5741, tg 76292, tg 81557]],
      [tg 455138, tg 460403, tg 530954, tg 536219]⟩,
    ⟨5, -1, 1, 15,
      [[tg 255, tg 5520, tg 76071, tg 81336], [tg 359, tg 5624, tg 76175, tg 81440], [tg 385, tg 5650, tg 76201, tg 81466], [tg 489, tg 5754, tg 76305, tg 81570]],
      [tg 455151, tg 460416, tg 530967, tg 536232]⟩,
    ⟨5, -1, 2, 14,
      [[tg 268, tg 5533, tg 76084, tg 81349], [tg 294, tg 5559, tg 76110, tg 81375], [tg 372, tg 5637, tg 76188, tg 81453], [tg 411, tg 5676, tg 76227, tg 81492], [tg 502, tg 5767, tg 76318, tg 81583]],
      [tg 606796, tg 612061, tg 682612, tg 687877]⟩,
    ⟨5, -1, 3, 9,
      [[tg 281, tg 5546, tg 76097, tg 81362], [tg 307, tg 5572, tg 76123, tg 81388], [tg 424, tg 5689, tg 76240, tg 81505], [tg 471, tg 1529, tg 6789, tg 77345], [tg 515, tg 5780, tg 76331, tg 81596]],
      [tg 606809, tg 612074, tg 682625, tg 687890]⟩,
    ⟨5, -1, 4, 14,
      [[tg 294, tg 5559, tg 76110, tg 81375], [tg 385, tg 5650, tg 76201, tg 81466], [tg 437, tg 5702, tg 76253, tg 81518], [tg 502, tg 5767, tg 76318, tg 81583], [tg 528, tg 5793, tg 76344, tg 81609]],
      [tg 606822, tg 612087, tg 682638, tg 687903]⟩,
    ⟨5, -1, 5, 10,
      [[tg 307, tg 5572, tg 76123, tg 81388], [tg 398, tg 5663, tg 76214, tg 81479], [tg 450, tg 5715, tg 76266, tg 81531], [tg 515, tg 5780, tg 76331, tg 81596], [tg 541, tg 5806, tg 76357, tg 81622]],
      [tg 606835, tg 612100, tg 682651, tg 687916]⟩,
    ⟨5, -1, 6, 13,
      [[tg 320, tg 5585, tg 76136, tg 81401], [tg 411, tg 5676, tg 76227, tg 81492], [tg 463, tg 5728, tg 76279, tg 81544], [tg 554, tg 5819, tg 76370, tg 81635]],
      [tg 455216, tg 460481, tg 531032, tg 536297]⟩,
    ⟨5, -1, 7, 11,
      [[tg 333, tg 5598, tg 76149, tg 81414], [tg 424, tg 5689, tg 76240, tg 81505], [tg 463, tg 5728, tg 76279, tg 81544], [tg 567, tg 5832, tg 76383, tg 81648]],
      [tg 455229, tg 460494, tg 531045, tg 536310]⟩,
    ⟨5, -1, 8, 12,
      [[tg 346, tg 5611, tg 76162, tg 81427], [tg 437, tg 5702, tg 76253, tg 81518], [tg 450, tg 5715, tg 76266, tg 81531], [tg 580, tg 5845, tg 76396, tg 81661]],
      [tg 455242, tg 460507, tg 531058, tg 536323]⟩,
    ⟨6, -1, 0, 17,
      [[tg 359, tg 5624, tg 76175, tg 81440], [tg 4610, tg 9875, tg 80426, tg 85691], [tg 489, tg 5754, tg 76305, tg 81570], [tg 593, tg 5858, tg 76409, tg 81674]],
      [tg 455255, tg 460520, tg 531071, tg 536336]⟩,
    ⟨6, -1, 1, 16,
      [[tg 372, tg 5637, tg 76188, tg 81453], [tg 476, tg 5741, tg 76292, tg 81557], [tg 502, tg 5767, tg 76318, tg 81583], [tg 606, tg 5871, tg 76422, tg 81687]],
      [tg 455268, tg 460533, tg 531084, tg 536349]⟩,
    ⟨6, -1, 2, 15,
      [[tg 385, tg 5650, tg 76201, tg 81466], [tg 411, tg 5676, tg 76227, tg 81492], [tg 489, tg 5754, tg 76305, tg 81570], [tg 528, tg 5793, tg 76344, tg 81609], [tg 619, tg 5884, tg 76435, tg 81700]],
      [tg 606913, tg 612178, tg 682729, tg 687994]⟩,
    ⟨6, -1, 3, 10,
      [[tg 398, tg 5663, tg 76214, tg 81479], [tg 424, tg 5689, tg 76240, tg 81505], [tg 541, tg 5806, tg 76357, tg 81622], [tg 588, tg 1646, tg 6906, tg 77462], [tg 632, tg 5897, tg 76448, tg 81713]],
      [tg 606926, tg 612191, tg 682742, tg 688007]⟩,
    ⟨6, -1, 4, 15,
      [[tg 411, tg 5676, tg 76227, tg 81492], [tg 502, tg 5767, tg 76318, tg 81583], [tg 554, tg 5819, tg 76370, tg 81635], [tg 619, tg 5884, tg 76435, tg 81700], [tg 645, tg 5910, tg 76461, tg 81726]],
      [tg 606939, tg 612204, tg 682755, tg 688020]⟩,
    ⟨6, -1, 5, 11,
      [[tg 424, tg 5689, tg 76240, tg 81505], [tg 515, tg 5780, tg 76331, tg 81596], [tg 567, tg 5832, tg 76383, tg 81648], [tg 632, tg 5897, tg 76448, tg 81713], [tg 658, tg 5923, tg 76474, tg 81739]],
      [tg 606952, tg 612217, tg 682768, tg 688033]⟩,
    ⟨6, -1, 6, 14,
      [[tg 437, tg 5702, tg 76253, tg 81518], [tg 528, tg 5793, tg 76344, tg 81609], [tg 580, tg 5845, tg 76396, tg 81661], [tg 671, tg 5936, tg 76487, tg 81752]],
      [tg 455333, tg 460598, tg 531149, tg 536414]⟩,
    ⟨6, -1, 7, 12,
      [[tg 450, tg 5715, tg 76266, tg 81531], [tg 541, tg 5806, tg 76357, tg 81622], [tg 580, tg 5845, tg 76396, tg 81661], [tg 684, tg 5949, tg 76500, tg 81765]],
      [tg 455346, tg 460611, tg 531162, tg 536427]⟩,
    ⟨6, -1, 8, 13,
      [[tg 463, tg 5728, tg 76279, tg 81544], [tg 554, tg 5819, tg 76370, tg 81635], [tg 567, tg 5832, tg 76383, tg 81648], [tg 697, tg 5962, tg 76513, tg 81778]],
      [tg 455359, tg 460624, tg 531175, tg 536440]⟩,
    ⟨7, -1, 0, 18,
      [[tg 476, tg 5741, tg 76292, tg 81557], [tg 4727, tg 9992, tg 80543, tg 85808], [tg 606, tg 5871, tg 76422, tg 81687], [tg 710, tg 5975, tg 76526, tg 81791]],
      [tg 455372, tg 460637, tg 531188, tg 536453]⟩,
    ⟨7, -1, 1, 17,
      [[tg 489, tg 5754, tg 76305, tg 81570], [tg 593, tg 5858, tg 76409, tg 81674], [tg 619, tg 5884, tg 76435, tg 81700], [tg 723, tg 5988, tg 76539, tg 81804]],
      [tg 455385, tg 460650, tg 531201, tg 536466]⟩,
    ⟨7, -1, 2, 16,
      [[tg 502, tg 5767, tg 76318, tg 81583], [tg 528, tg 5793, tg 76344, tg 81609], [tg 606, tg 5871, tg 76422, tg 81687], [tg 645, tg 5910, tg 76461, tg 81726], [tg 736, tg 6001, tg 76552, tg 81817]],
      [tg 607030, tg 612295, tg 682846, tg 688111]⟩,
    ⟨7, -1, 3, 11,
      [[tg 515, tg 5780, tg 76331, tg 81596], [tg 541, tg 5806, tg 76357, tg 81622], [tg 658, tg 5923, tg 76474, tg 81739], [tg 705, tg 1763, tg 7023, tg 77579], [tg 749, tg 6014, tg 76565, tg 81830]],
      [tg 607043, tg 612308, tg 682859, tg 688124]⟩,
    ⟨7, -1, 4, 16,
      [[tg 528, tg 5793, tg 76344, tg 81609], [tg 619, tg 5884, tg 76435, tg 81700], [tg 671, tg 5936, tg 76487, tg 81752], [tg 736, tg 6001, tg 76552, tg 81817], [tg 762, tg 6027, tg 76578, tg 81843]],
      [tg 607056, tg 612321, tg 682872, tg 688137]⟩,
    ⟨7, -1, 5, 12,
      [[tg 541, tg 5806, tg 76357, tg 81622], [tg 632, tg 5897, tg 76448, tg 81713], [tg 684, tg 5949, tg 76500, tg 81765], [tg 749, tg 6014, tg 76565, tg 81830], [tg 775, tg 6040, tg 76591, tg 81856]],
      [tg 607069, tg 612334, tg 682885, tg 688150]⟩,
    ⟨7, -1, 6, 15,
      [[tg 554, tg 5819, tg 76370, tg 81635], [tg 645, tg 5910, tg 76461, tg 81726], [tg 697, tg 5962, tg 76513, tg 81778], [tg 788, tg 6053, tg 76604, tg 81869]],
      [tg 455450, tg 460715, tg 531266, tg 536531]⟩,
    ⟨7, -1, 7, 13,
      [[tg 567, tg 5832, tg 76383, tg 81648], [tg 658, tg 5923, tg 76474, tg 81739], [tg 697, tg 5962, tg 76513, tg 81778], [tg 801, tg 6066, tg 76617, tg 81882]],
      [tg 455463, tg 460728, tg 531279, tg 536544]⟩,
    ⟨7, -1, 8, 14,
      [[tg 580, tg 5845, tg 76396, tg 81661], [tg 671, tg 5936, tg 76487, tg 81752], [tg 684, tg 5949, tg 76500, tg 81765], [tg 814, tg 6079, tg 76630, tg 81895]],
      [tg 455476, tg 460741, tg 531292, tg 536557]⟩,
    ⟨8, -1, 0, 19,
      [[tg 593, tg 5858, tg 76409, tg 81674], [tg 4844, tg 10109, tg 80660, tg 85925], [tg 723, tg 5988, tg 76539, tg 81804], [tg 827, tg 6092, tg 76643, tg 81908]],
      [tg 455489, tg 460754, tg 531305, tg 536570]⟩,
    ⟨8, -1, 1, 18,
      [[tg 606, tg 5871, tg 76422, tg 81687], [tg 710, tg 5975, tg 76526, tg 81791], [tg 736, tg 6001, tg 76552, tg 81817], [tg 840, tg 6105, tg 76656, tg 81921]],
      [tg 455502, tg 460767, tg 531318, tg 536583]⟩,
    ⟨8, -1, 2, 17,
      [[tg 619, tg 5884, tg 76435, tg 81700], [tg 645, tg 5910, tg 76461, tg 81726], [tg 723, tg 5988, tg 76539, tg 81804], [tg 762, tg 6027, tg 76578, tg 81843], [tg 853, tg 6118, tg 76669, tg 81934]],
      [tg 607147, tg 612412, tg 682963, tg 688228]⟩,
    ⟨8, -1, 3, 12,
      [[tg 632, tg 5897, tg 76448, tg 81713], [tg 658, tg 5923, tg 76474, tg 81739], [tg 775, tg 6040, tg 76591, tg 81856], [tg 822, tg 1880, tg 7140, tg 77696], [tg 866, tg 6131, tg 76682, tg 81947]],
      [tg 607160, tg 612425, tg 682976, tg 688241]⟩,
    ⟨8, -1, 4, 17,
      [[tg 645, tg 5910, tg 76461, tg 81726], [tg 736, tg 6001, tg 76552, tg 81817], [tg 788, tg 6053, tg 76604, tg 81869], [tg 853, tg 6118, tg 76669, tg 81934], [tg 879, tg 6144, tg 76695, tg 81960]],
      [tg 607173, tg 612438, tg 682989, tg 688254]⟩,
    ⟨8, -1, 5, 13,
      [[tg 658, tg 5923, tg 76474, tg 81739], [tg 749, tg 6014, tg 76565, tg 81830], [tg 801, tg 6066, tg 76617, tg 81882], [tg 866, tg 6131, tg 76682, tg 81947], [tg 892, tg 6157, tg 76708, tg 81973]],
      [tg 607186, tg 612451, tg 683002, tg 688267]⟩,
    ⟨8, -1, 6, 16,
      [[tg 671, tg 5936, tg 76487, tg 81752], [tg 762, tg 6027, tg 76578, tg 81843], [tg 814, tg 6079, tg 76630, tg 81895], [tg 905, tg 6170, tg 76721, tg 81986]],
      [tg 455567, tg 460832, tg 531383, tg 536648]⟩,
    ⟨8, -1, 7, 14,
      [[tg 684, tg 5949, tg 76500, tg 81765], [tg 775, tg 6040, tg 76591, tg 81856], [tg 814, tg 6079, tg 76630, tg 81895], [tg 918, tg 6183, tg 76734, tg 81999]],
      [tg 455580, tg 460845, tg 531396, tg 536661]⟩,
    ⟨8, -1, 8, 15,
      [[tg 697, tg 5962, tg 76513, tg 81778], [tg 788, tg 6053, tg 76604, tg 81869], [tg 801, tg 6066, tg 76617, tg 81882], [tg 931, tg 6196, tg 76747, tg 82012]],
      [tg 455593, tg 460858, tg 531409, tg 536674]⟩,
    ⟨9, -1, 0, 20,
      [[tg 710, tg 5975, tg 76526, tg 81791], [tg 4961, tg 10226, tg 80777, tg 86042], [tg 840, tg 6105, tg 76656, tg 81921], [tg 944, tg 6209, tg 76760, tg 82025]],
      [tg 455606, tg 460871, tg 531422, tg 536687]⟩,
    ⟨9, -1, 1, 19,
      [[tg 723, tg 5988, tg 76539, tg 81804], [tg 827, tg 6092, tg 76643, tg 81908], [tg 853, tg 6118, tg 76669, tg 81934], [tg 957, tg 6222, tg 76773, tg 82038]],
      [tg 455619, tg 460884, tg 531435, tg 536700]⟩,
    ⟨9, -1, 2, 18,
      [[tg 736, tg 6001, tg 76552, tg 81817], [tg 762, tg 6027, tg 76578, tg 81843], [tg 840, tg 6105, tg 76656, tg 81921], [tg 879, tg 6144, tg 76695, tg 81960], [tg 970, tg 6235, tg 76786, tg 82051]],
      [tg 607264, tg 612529, tg 683080, tg 688345]⟩,
    ⟨9, -1, 3, 13,
      [[tg 749, tg 6014, tg 76565, tg 81830], [tg 775, tg 6040, tg 76591, tg 81856], [tg 892, tg 6157, tg 76708, tg 81973], [tg 939, tg 1997, tg 7257, tg 77813], [tg 983, tg 6248, tg 76799, tg 82064]],
      [tg 607277, tg 612542, tg 683093, tg 688358]⟩,
    ⟨9, -1, 4, 18,
      [[tg 762, tg 6027, tg 76578, tg 81843], [tg 853, tg 6118, tg 76669, tg 81934], [tg 905, tg 6170, tg 76721, tg 81986], [tg 970, tg 6235, tg 76786, tg 82051], [tg 996, tg 6261, tg 76812, tg 82077]],
      [tg 607290, tg 612555, tg 683106, tg 688371]⟩,
    ⟨9, -1, 5, 14,
      [[tg 775, tg 6040, tg 76591, tg 81856], [tg 866, tg 6131, tg 76682, tg 81947], [tg 918, tg 6183, tg 76734, tg 81999], [tg 983, tg 6248, tg 76799, tg 82064], [tg 1009, tg 6274, tg 76825, tg 82090]],
      [tg 607303, tg 612568, tg 683119, tg 688384]⟩,
    ⟨9, -1, 6, 17,
      [[tg 788, tg 6053, tg 76604, tg 81869], [tg 879, tg 6144, tg 76695, tg 81960], [tg 931, tg 6196, tg 76747, tg 82012], [tg 1022, tg 6287, tg 76838, tg 82103]],
      [tg 455684, tg 460949, tg 531500, tg 536765]⟩,
    ⟨9, -1, 7, 15,
      [[tg 801, tg 6066, tg 76617, tg 81882], [tg 892, tg 6157, tg 76708, tg 81973], [tg 931, tg 6196, tg 76747, tg 82012], [tg 1035, tg 6300, tg 76851, tg 82116]],
      [tg 455697, tg 460962, tg 531513, tg 536778]⟩,
    ⟨9, -1, 8, 16,
      [[tg 814, tg 6079, tg 76630, tg 81895], [tg 905, tg 6170, tg 76721, tg 81986], [tg 918, tg 6183, tg 76734, tg 81999], [tg 1048, tg 6313, tg 76864, tg 82129]],
      [tg 455710, tg 460975, tg 531526, tg 536791]⟩,
    ⟨10, -1, 0, 21,
      [[tg 827, tg 6092, tg 76643, tg 81908], [tg 5078, tg 10343, tg 80894, tg 86159], [tg 957, tg 6222, tg 76773, tg 82038], [tg 50552, tg 55817, tg 126368, tg 131633]],
      [tg 455723, tg 460988, tg 531539, tg 536804]⟩,
    ⟨10, -1, 1, 20,
      [[tg 840, tg 6105, tg 76656, tg 81921], [tg 944, tg 6209, tg 76760, tg 82025], [tg 970, tg 6235, tg 76786, tg 82051], [tg 50565, tg 55830, tg 126381, tg 131646]],
      [tg 455736, tg 461001, tg 531552, tg 536817]⟩,
    ⟨10, -1, 2, 19,
      [[tg 853, tg 6118, tg 76669, tg 81934], [tg 879, tg 6144, tg 76695, tg 81960], [tg 957, tg 6222, tg 76773, tg 82038], [tg 996, tg 6261, tg 76812, tg 82077], [tg 50578, tg 55843, tg 126394, tg 131659]],
      [tg 607381, tg 612646, tg 683197, tg 688462]⟩,
    ⟨10, -1, 3, 14,
      [[tg 866, tg 6131, tg 76682, tg 81947], [tg 892, tg 6157, tg 76708, tg 81973], [tg 1009, tg 6274, tg 76825, tg 82090], [tg 4215, tg 51605, tg 10533, tg 127421], [tg 50591, tg 55856, tg 126407, tg 131672]],
      [tg 607394, tg 612659, tg 683210, tg 688475]⟩,
    ⟨10, -1, 4, 19,
      [[tg 879, tg 6144, tg 76695, tg 81960], [tg 970, tg 6235, tg 76786, tg 82051], [tg 1022, tg 6287, tg 76838, tg 82103], [tg 50578, tg 55843, tg 126394, tg 131659], [tg 50604, tg 55869, tg 126420, tg 131685]],
      [tg 607407, tg 612672, tg 683223, tg 688488]⟩,
    ⟨10, -1, 5, 15,
      [[tg 892, tg 6157, tg 76708, tg 81973], [tg 983, tg 6248, tg 76799, tg 82064], [tg 1035, tg 6300, tg 76851, tg 82116], [tg 50591, tg 55856, tg 126407, tg 131672], [tg 50617, tg 55882, tg 126433, tg 131698]],
      [tg 607420, tg 612685, tg 683236, tg 688501]⟩,
    ⟨10, -1, 6, 18,
      [[tg 905, tg 6170, tg 76721, tg 81986], [tg 996, tg 6261, tg 76812, tg 82077], [tg 1048, tg 6313, tg 76864, tg 82129], [tg 50630, tg 55895, tg 126446, tg 131711]],
      [tg 455801, tg 461066, tg 531617, tg 536882]⟩,
    ⟨10, -1, 7, 16,
      [[tg 918, tg 6183, tg 76734, tg 81999], [tg 1009, tg 6274, tg 76825, tg 82090], [tg 1048, tg 6313, tg 76864, tg 82129], [tg 50643, tg 55908, tg 126459, tg 131724]],
      [tg 455814, tg 461079, tg 531630, tg 536895]⟩,
    ⟨10, -1, 8, 17,
      [[tg 931, tg 6196, tg 76747, tg 82012], [tg 1022, tg 6287, tg 76838, tg 82103], [tg 1035, tg 6300, tg 76851, tg 82116], [tg 50656, tg 55921, tg 126472, tg 131737]],
      [tg 455827, tg 461092, tg 531643, tg 536908]⟩]⟩,
  ⟨2, 9, 0, 1, 1, [(1, -1, 1), (0, 9, 1)], 1, -1, 1, 9, 0, 9, 1, 9,
   [⟨2, 1, 0, 6,
      [[tg 4, tg 1998, tg 6322, tg 77814], [tg 159, tg 5424, tg 25437, tg 30702], [tg 22, tg 5287, tg 75838, tg 81103], [tg 126, tg 5391, tg 75942, tg 81207]],
      [tg 454900, tg 456894, tg 461218, tg 532710]⟩,
    ⟨2, 1, 1, 7,
      [[tg 17, tg 2011, tg 6335, tg 77827], [tg 9, tg 5274, tg 75825, tg 81090], [tg 35, tg 5300, tg 75851, tg 81116], [tg 139, tg 5404, tg 75955, tg 81220]],
      [tg 454913, tg 456907, tg 461231, tg 532723]⟩,
    ⟨2, 1, 2, 8,
      [[tg 30, tg 2024, tg 6348, tg 77840], [tg 56, tg 2050, tg 6374, tg 77866], [tg 22, tg 5287, tg 75838, tg 81103], [tg 61, tg 5326, tg 75877, tg 81142], [tg 152, tg 5417, tg 75968, tg 81233]],
      [tg 606558, tg 608552, tg 612876, tg 684368]⟩,
    ⟨2, 1, 3, 13,
      [[tg 43, tg 2037, tg 6361, tg 77853], [tg 69, tg 2063, tg 6387, tg 77879], [tg 74, tg 5339, tg 75890, tg 81155], [tg 4216, tg 52542, tg 10534, tg 128358], [tg 165, tg 5430, tg 75981, tg 81246]],
      [tg 454965, tg 608565, tg 461283, tg 684381]⟩,
    ⟨2, 1, 4, 9,
      [[tg 56, tg 2050, tg 6374, tg 77866], [tg 35, tg 5300, tg 75851, tg 81116], [tg 87, tg 5352, tg 75903, tg 81168], [tg 152, tg 5417, tg 75968, tg 81233], [tg 178, tg 5443, tg 75994, tg 81259]],
      [tg 606584, tg 608578, tg 612902, tg 684394]⟩,
    ⟨2, 1, 5, 13,
      [[tg 69, tg 2063, tg 6387, tg 77879], [tg 48, tg 5313, tg 75864, tg 81129], [tg 100, tg 5365, tg 75916, tg 81181], [tg 165, tg 5430, tg 75981, tg 81246], [tg 191, tg 5456, tg 76007, tg 81272]],
      [tg 606597, tg 608591, tg 612915, tg 684407]⟩,
    ⟨2, 1, 6, 10,
      [[tg 82, tg 2076, tg 6400, tg 77892], [tg 61, tg 5326, tg 75877, tg 81142], [tg 113, tg 5378, tg 75929, tg 81194], [tg 204, tg 5469, tg 76020, tg 81285]],
      [tg 454978, tg 456972, tg 461296, tg 532788]⟩,
    ⟨2, 1, 7, 12,
      [[tg 95, tg 2089, tg 6413, tg 77905], [tg 74, tg 5339, tg 75890, tg 81155], [tg 113, tg 5378, tg 75929, tg 81194], [tg 217, tg 5482, tg 76033, tg 81298]],
      [tg 454991, tg 456985, tg 461309, tg 532801]⟩,
    ⟨2, 1, 8, 11,
      [[tg 108, tg 2102, tg 6426, tg 77918], [tg 87, tg 5352, tg 75903, tg 81168], [tg 100, tg 5365, tg 75916, tg 81181], [tg 230, tg 5495, tg 76046, tg 81311]],
      [tg 455004, tg 456998, tg 461322, tg 532814]⟩,
    ⟨3, 1, 0, 7,
      [[tg 9, tg 5274, tg 75825, tg 81090], [tg 276, tg 5541, tg 25554, tg 30819], [tg 139, tg 5404, tg 75955, tg 81220], [tg 243, tg 5508, tg 76059, tg 81324]],
      [tg 454905, tg 460170, tg 530721, tg 535986]⟩,
    ⟨3, 1, 1, 8,
      [[tg 22, tg 5287, tg 75838, tg 81103], [tg 126, tg 5391, tg 75942, tg 81207], [tg 152, tg 5417, tg 75968, tg 81233], [tg 256, tg 5521, tg 76072, tg 81337]],
      [tg 454918, tg 460183, tg 530734, tg 535999]⟩,
    ⟨3, 1, 2, 9,
      [[tg 35, tg 5300, tg 75851, tg 81116], [tg 61, tg 5326, tg 75877, tg 81142], [tg 139, tg 5404, tg 75955, tg 81220], [tg 178, tg 5443, tg 75994, tg 81259], [tg 269, tg 5534, tg 76085, tg 81350]],
      [tg 606563, tg 611828, tg 682379, tg 687644]⟩,
    ⟨3, 1, 3, 14,
      [[tg 48, tg 5313, tg 75864, tg 81129], [tg 74, tg 5339, tg 75890, tg 81155], [tg 191, tg 5456, tg 76007, tg 81272], [tg 50553, tg 55818, tg 126369, tg 131634], [tg 282, tg 5547, tg 76098, tg 81363]],
      [tg 606576, tg 611841, tg 682392, tg 687657]⟩,
    ⟨3, 1, 4, 10,
      [[tg 61, tg 5326, tg 75877, tg 81142], [tg 152, tg 5417, tg 75968, tg 81233], [tg 204, tg 5469, tg 76020, tg 81285], [tg 269, tg 5534, tg 76085, tg 81350], [tg 295, tg 5560, tg 76111, tg 81376]],
      [tg 606589, tg 611854, tg 682405, tg 687670]⟩,
    ⟨3, 1, 5, 14,
      [[tg 74, tg 5339, tg 75890, tg 81155], [tg 165, tg 5430, tg 75981, tg 81246], [tg 217, tg 5482, tg 76033, tg 81298], [tg 282, tg 5547, tg 76098, tg 81363], [tg 308, tg 5573, tg 76124, tg 81389]],
      [tg 606602, tg 611867, tg 682418, tg 687683]⟩,
    ⟨3, 1, 6, 11,
      [[tg 87, tg 5352, tg 75903, tg 81168], [tg 178, tg 5443, tg 75994, tg 81259], [tg 230, tg 5495, tg 76046, tg 81311], [tg 321, tg 5586, tg 76137, tg 81402]],
      [tg 454983, tg 460248, tg 530799, tg 536064]⟩,
    ⟨3, 1, 7, 13,
      [[tg 100, tg 5365, tg 75916, tg 81181], [tg 191, tg 5456, tg 76007, tg 81272], [tg 230, tg 5495, tg 76046, tg 81311], [tg 334, tg 5599, tg 76150, tg 81415]],
      [tg 454996, tg 460261, tg 530812, tg 536077]⟩,
    ⟨3, 1, 8, 12,
      [[tg 113, tg 5378, tg 75929, tg 81194], [tg 204, tg 5469, tg 76020, tg 81285], [tg 217, tg 5482, tg 76033, tg 81298], [tg 347, tg 5612, tg 76163, tg 81428]],
      [tg 455009, tg 460274, tg 530825, tg 536090]⟩,
    ⟨4, 1, 0, 8,
      [[tg 126, tg 5391, tg 75942, tg 81207], [tg 393, tg 5658, tg 25671, tg 30936], [tg 256, tg 5521, tg 76072, tg 81337], [tg 360, tg 5625, tg 76176, tg 81441]],
      [tg 455022, tg 460287, tg 530838, tg 536103]⟩,
    ⟨4, 1, 1, 9,
      [[tg 139, tg 5404, tg 75955, tg 81220], [tg 243, tg 5508, tg 76059, tg 81324], [tg 269, tg 5534, tg 76085, tg 81350], [tg 373, tg 5638, tg 76189, tg 81454]],
      [tg 455035, tg 460300, tg 530851, tg 536116]⟩,
    ⟨4, 1, 2, 10,
      [[tg 152, tg 5417, tg 75968, tg 81233], [tg 178, tg 5443, tg 75994, tg 81259], [tg 256, tg 5521, tg 76072, tg 81337], [tg 295, tg 5560, tg 76111, tg 81376], [tg 386, tg 5651, tg 76202, tg 81467]],
      [tg 606680, tg 611945, tg 682496, tg 687761]⟩,
    ⟨4, 1, 3, 15,
      [[tg 165, tg 5430, tg 75981, tg 81246], [tg 191, tg 5456, tg 76007, tg 81272], [tg 308, tg 5573, tg 76124, tg 81389], [tg 50670, tg 55935, tg 126486, tg 131751], [tg 399, tg 5664, tg 76215, tg 81480]],
      [tg 606693, tg 611958, tg 682509, tg 687774]⟩,
    ⟨4, 1, 4, 11,
      [[tg 178, tg 5443, tg 75994, tg 81259], [tg 269, tg 5534, tg 76085, tg 81350], [tg 321, tg 5586, tg 76137, tg 81402], [tg 386, tg 5651, tg 76202, tg 81467], [tg 412, tg 5677, tg 76228, tg 81493]],
      [tg 606706, tg 611971, tg 682522, tg 687787]⟩,
    ⟨4, 1, 5, 15,
      [[tg 191, tg 5456, tg 76007, tg 81272], [tg 282, tg 5547, tg 76098, tg 81363], [tg 334, tg 5599, tg 76150, tg 81415], [tg 399, tg 5664, tg 76215, tg 81480], [tg 425, tg 5690, tg 76241, tg 81506]],
      [tg 606719, tg 611984, tg 682535, tg 687800]⟩,
    ⟨4, 1, 6, 12,
      [[tg 204, tg 5469, tg 76020, tg 81285], [tg 295, tg 5560, tg 76111, tg 81376], [tg 347, tg 5612, tg 76163, tg 81428], [tg 438, tg 5703, tg 76254, tg 81519]],
      [tg 455100, tg 460365, tg 530916, tg 536181]⟩,
    ⟨4, 1, 7, 14,
      [[tg 217, tg 5482, tg 76033, tg 81298], [tg 308, tg 5573, tg 76124, tg 81389], [tg 347, tg 5612, tg 76163, tg 81428], [tg 451, tg 5716, tg 76267, tg 81532]],
      [tg 455113, tg 460378, tg 530929, tg 536194]⟩,
    ⟨4, 1, 8, 13,
      [[tg 230, tg 5495, tg 76046, tg 81311], [tg 321, tg 5586, tg 76137, tg 81402], [tg 334, tg 5599, tg 76150, tg 81415], [tg 464, tg 5729, tg 76280, tg 81545]],
      [tg 455126, tg 460391, tg 530942, tg 536207]⟩,
    ⟨5, 1, 0, 9,
      [[tg 243, tg 5508, tg 76059, tg 81324], [tg 510, tg 5775, tg 25788, tg 31053], [tg 373, tg 5638, tg 76189, tg 81454], [tg 477, tg 5742, tg 76293, tg 81558]],
      [tg 455139, tg 460404, tg 530955, tg 536220]⟩,
    ⟨5, 1, 1, 10,
      [[tg 256, tg 5521, tg 76072, tg 81337], [tg 360, tg 5625, tg 76176, tg 81441], [tg 386, tg 5651, tg 76202, tg 81467], [tg 490, tg 5755, tg 76306, tg 81571]],
      [tg 455152, tg 460417, tg 530968, tg 536233]⟩,
    ⟨5, 1, 2, 11,
      [[tg 269, tg 5534, tg 76085, tg 81350], [tg 295, tg 5560, tg 76111, tg 81376], [tg 373, tg 5638, tg 76189, tg 81454], [tg 412, tg 5677, tg 76228, tg 81493], [tg 503, tg 5768, tg 76319, tg 81584]],
      [tg 606797, tg 612062, tg 682613, tg 687878]⟩,
    ⟨5, 1, 3, 16,
      [[tg 282, tg 5547, tg 76098, tg 81363], [tg 308, tg 5573, tg 76124, tg 81389], [tg 425, tg 5690, tg 76241, tg 81506], [tg 50787, tg 56052, tg 126603, tg 131868], [tg 516, tg 5781, tg 76332, tg 81597]],
      [tg 606810, tg 612075, tg 682626, tg 687891]⟩,
    ⟨5, 1, 4, 12,
      [[tg 295, tg 5560, tg 76111, tg 81376], [tg 386, tg 5651, tg 76202, tg 81467], [tg 438, tg 5703, tg 76254, tg 81519], [tg 503, tg 5768, tg 76319, tg 81584], [tg 529, tg 5794, tg 76345, tg 81610]],
      [tg 606823, tg 612088, tg 682639, tg 687904]⟩,
    ⟨5, 1, 5, 16,
      [[tg 308, tg 5573, tg 76124, tg 81389], [tg 399, tg 5664, tg 76215, tg 81480], [tg 451, tg 5716, tg 76267, tg 81532], [tg 516, tg 5781, tg 76332, tg 81597], [tg 542, tg 5807, tg 76358, tg 81623]],
      [tg 606836, tg 612101, tg 682652, tg 687917]⟩,
    ⟨5, 1, 6, 13,
      [[tg 321, tg 5586, tg 76137, tg 81402], [tg 412, tg 5677, tg 76228, tg 81493], [tg 464, tg 5729, tg 76280, tg 81545], [tg 555, tg 5820, tg 76371, tg 81636]],
      [tg 455217, tg 460482, tg 531033, tg 536298]⟩,
    ⟨5, 1, 7, 15,
      [[tg 334, tg 5599, tg 76150, tg 81415], [tg 425, tg 5690, tg 76241, tg 81506], [tg 464, tg 5729, tg 76280, tg 81545], [tg 568, tg 5833, tg 76384, tg 81649]],
      [tg 455230, tg 460495, tg 531046, tg 536311]⟩,
    ⟨5, 1, 8, 14,
      [[tg 347, tg 5612, tg 76163, tg 81428], [tg 438, tg 5703, tg 76254, tg 81519], [tg 451, tg 5716, tg 76267, tg 81532], [tg 581, tg 5846, tg 76397, tg 81662]],
      [tg 455243, tg 460508, tg 531059, tg 536324]⟩,
    ⟨6, 1, 0, 10,
      [[tg 360, tg 5625, tg 76176, tg 81441], [tg 627, tg 5892, tg 25905, tg 31170], [tg 490, tg 5755, tg 76306, tg 81571], [tg 594, tg 5859, tg 76410, tg 81675]],
      [tg 455256, tg 460521, tg 531072, tg 536337]⟩,
    ⟨6, 1, 1, 11,
      [[tg 373, tg 5638, tg 76189, tg 81454], [tg 477, tg 5742, tg 76293, tg 81558], [tg 503, tg 5768, tg 76319, tg 81584], [tg 607, tg 5872, tg 76423, tg 81688]],
      [tg 455269, tg 460534, tg 531085, tg 536350]⟩,
    ⟨6, 1, 2, 12,
      [[tg 386, tg 5651, tg 76202, tg 81467], [tg 412, tg 5677, tg 76228, tg 81493], [tg 490, tg 5755, tg 76306, tg 81571], [tg 529, tg 5794, tg 76345, tg 81610], [tg 620, tg 5885, tg 76436, tg 81701]],
      [tg 606914, tg 612179, tg 682730, tg 687995]⟩,
    ⟨6, 1, 3, 17,
      [[tg 399, tg 5664, tg 76215, tg 81480], [tg 425, tg 5690, tg 76241, tg 81506], [tg 542, tg 5807, tg 76358, tg 81623], [tg 50904, tg 56169, tg 126720, tg 131985], [tg 633, tg 5898, tg 76449, tg 81714]],
      [tg 606927, tg 612192, tg 682743, tg 688008]⟩,
    ⟨6, 1, 4, 13,
      [[tg 412, tg 5677, tg 76228, tg 81493], [tg 503, tg 5768, tg 76319, tg 81584], [tg 555, tg 5820, tg 76371, tg 81636], [tg 620, tg 5885, tg 76436, tg 81701], [tg 646, tg 5911, tg 76462, tg 81727]],
      [tg 606940, tg 612205, tg 682756, tg 688021]⟩,
    ⟨6, 1, 5, 17,
      [[tg 425, tg 5690, tg 76241, tg 81506], [tg 516, tg 5781, tg 76332, tg 81597], [tg 568, tg 5833, tg 76384, tg 81649], [tg 633, tg 5898, tg 76449, tg 81714], [tg 659, tg 5924, tg 76475, tg 81740]],
      [tg 606953, tg 612218, tg 682769, tg 688034]⟩,
    ⟨6, 1, 6, 14,
      [[tg 438, tg 5703, tg 76254, tg 81519], [tg 529, tg 5794, tg 76345, tg 81610], [tg 581, tg 5846, tg 76397, tg 81662], [tg 672, tg 5937, tg 76488, tg 81753]],
      [tg 455334, tg 460599, tg 531150, tg 536415]⟩,
    ⟨6, 1, 7, 16,
      [[tg 451, tg 5716, tg 76267, tg 81532], [tg 542, tg 5807, tg 76358, tg 81623], [tg 581, tg 5846, tg 76397, tg 81662], [tg 685, tg 5950, tg 76501, tg 81766]],
      [tg 455347, tg 460612, tg 531163, tg 536428]⟩,
    ⟨6, 1, 8, 15,
      [[tg 464, tg 5729, tg 76280, tg 81545], [tg 555, tg 5820, tg 76371, tg 81636], [tg 568, tg 5833, tg 76384, tg 81649], [tg 698, tg 5963, tg 76514, tg 81779]],
      [tg 455360, tg 460625, tg 531176, tg 536441]⟩,
    ⟨7, 1, 0, 11,
      [[tg 477, tg 5742, tg 76293, tg 81558], [tg 744, tg 6009, tg 26022, tg 31287], [tg 607, tg 5872, tg 76423, tg 81688], [tg 711, tg 5976, tg 76527, tg 81792]],
      [tg 455373, tg 460638, tg 531189, tg 536454]⟩,
    ⟨7, 1, 1, 12,
      [[tg 490, tg 5755, tg 76306, tg 81571], [tg 594, tg 5859, tg 76410, tg 81675], [tg 620, tg 5885, tg 76436, tg 81701], [tg 724, tg 5989, tg 76540, tg 81805]],
      [tg 455386, tg 460651, tg 531202, tg 536467]⟩,
    ⟨7, 1, 2, 13,
      [[tg 503, tg 5768, tg 76319, tg 81584], [tg 529, tg 5794, tg 76345, tg 81610], [tg 607, tg 5872, tg 76423, tg 81688], [tg 646, tg 5911, tg 76462, tg 81727], [tg 737, tg 6002, tg 76553, tg 81818]],
      [tg 607031, tg 612296, tg 682847, tg 688112]⟩,
    ⟨7, 1, 3, 18,
      [[tg 516, tg 5781, tg 76332, tg 81597], [tg 542, tg 5807, tg 76358, tg 81623], [tg 659, tg 5924, tg 76475, tg 81740], [tg 51021, tg 56286, tg 126837, tg 132102], [tg 750, tg 6015, tg 76566, tg 81831]],
      [tg 607044, tg 612309, tg 682860, tg 688125]⟩,
    ⟨7, 1, 4, 14,
      [[tg 529, tg 5794, tg 76345, tg 81610], [tg 620, tg 5885, tg 76436, tg 81701], [tg 672, tg 5937, tg 76488, tg 81753], [tg 737, tg 6002, tg 76553, tg 81818], [tg 763, tg 6028, tg 76579, tg 81844]],
      [tg 607057, tg 612322, tg 682873, tg 688138]⟩,
    ⟨7, 1, 5, 18,
      [[tg 542, tg 5807, tg 76358, tg 81623], [tg 633, tg 5898, tg 76449, tg 81714], [tg 685, tg 5950, tg 76501, tg 81766], [tg 750, tg 6015, tg 76566, tg 81831], [tg 776, tg 6041, tg 76592, tg 81857]],
      [tg 607070, tg 612335, tg 682886, tg 688151]⟩,
    ⟨7, 1, 6, 15,
      [[tg 555, tg 5820, tg 76371, tg 81636], [tg 646, tg 5911, tg 76462, tg 81727], [tg 698, tg 5963, tg 76514, tg 81779], [tg 789, tg 6054, tg 76605, tg 81870]],
      [tg 455451, tg 460716, tg 531267, tg 536532]⟩,
    ⟨7, 1, 7, 17,
      [[tg 568, tg 5833, tg 76384, tg 81649], [tg 659, tg 5924, tg 76475, tg 81740], [tg 698, tg 5963, tg 76514, tg 81779], [tg 802, tg 6067, tg 76618, tg 81883]],
      [tg 455464, tg 460729, tg 531280, tg 536545]⟩,
    ⟨7, 1, 8, 16,
      [[tg 581, tg 5846, tg 76397, tg 81662], [tg 672, tg 5937, tg 76488, tg 81753], [tg 685, tg 5950, tg 76501, tg 81766], [tg 815, tg 6080, tg 76631, tg 81896]],
      [tg 455477, tg 460742, tg 531293, tg 536558]⟩,
    ⟨8, 1, 0, 12,
      [[tg 594, tg 5859, tg 76410, tg 81675], [tg 861, tg 6126, tg 26139, tg 31404], [tg 724, tg 5989, tg 76540, tg 81805], [tg 828, tg 6093, tg 76644, tg 81909]],
      [tg 455490, tg 460755, tg 531306, tg 536571]⟩,
    ⟨8, 1, 1, 13,
      [[tg 607, tg 5872, tg 76423, tg 81688], [tg 711, tg 5976, tg 76527, tg 81792], [tg 737, tg 6002, tg 76553, tg 81818], [tg 841, tg 6106, tg 76657, tg 81922]],
      [tg 455503, tg 460768, tg 531319, tg 536584]⟩,
    ⟨8, 1, 2, 14,
      [[tg 620, tg 5885, tg 76436, tg 81701], [tg 646, tg 5911, tg 76462, tg 81727], [tg 724, tg 5989, tg 76540, tg 81805], [tg 763, tg 6028, tg 76579, tg 81844], [tg 854, tg 6119, tg 76670, tg 81935]],
      [tg 607148, tg 612413, tg 682964, tg 688229]⟩,
    ⟨8, 1, 3, 19,
      [[tg 633, tg 5898, tg 76449, tg 81714], [tg 659, tg 5924, tg 76475, tg 81740], [tg 776, tg 6041, tg 76592, tg 81857], [tg 51138, tg 56403, tg 126954, tg 132219], [tg 867, tg 6132, tg 76683, tg 81948]],
      [tg 607161, tg 612426, tg 682977, tg 688242]⟩,
    ⟨8, 1, 4, 15,
      [[tg 646, tg 5911, tg 76462, tg 81727], [tg 737, tg 6002, tg 76553, tg 81818], [tg 789, tg 6054, tg 76605, tg 81870], [tg 854, tg 6119, tg 76670, tg 81935], [tg 880, tg 6145, tg 76696, tg 81961]],
      [tg 607174, tg 612439, tg 682990, tg 688255]⟩,
    ⟨8, 1, 5, 19,
      [[tg 659, tg 5924, tg 76475, tg 81740], [tg 750, tg 6015, tg 76566, tg 81831], [tg 802, tg 6067, tg 76618, tg 81883], [tg 867, tg 6132, tg 76683, tg 81948], [tg 893, tg 6158, tg 76709, tg 81974]],
      [tg 607187, tg 612452, tg 683003, tg 688268]⟩,
    ⟨8, 1, 6, 16,
      [[tg 672, tg 5937, tg 76488, tg 81753], [tg 763, tg 6028, tg 76579, tg 81844], [tg 815, tg 6080, tg 76631, tg 81896], [tg 906, tg 6171, tg 76722, tg 81987]],
      [tg 455568, tg 460833, tg 531384, tg 536649]⟩,
    ⟨8, 1, 7, 18,
      [[tg 685, tg 5950, tg 76501, tg 81766], [tg 776, tg 6041, tg 76592, tg 81857], [tg 815, tg 6080, tg 76631, tg 81896], [tg 919, tg 6184, tg 76735, tg 82000]],
      [tg 455581, tg 460846, tg 531397, tg 536662]⟩,
    ⟨8, 1, 8, 17,
      [[tg 698, tg 5963, tg 76514, tg 81779], [tg 789, tg 6054, tg 76605, tg 81870], [tg 802, tg 6067, tg 76618, tg 81883], [tg 932, tg 6197, tg 76748, tg 82013]],
      [tg 455594, tg 460859, tg 531410, tg 536675]⟩,
    ⟨9, 1, 0, 13,
      [[tg 711, tg 5976, tg 76527, tg 81792], [tg 978, tg 6243, tg 26256, tg 31521], [tg 841, tg 6106, tg 76657, tg 81922], [tg 945, tg 6210, tg 76761, tg 82026]],
      [tg 455607, tg 460872, tg 531423, tg 536688]⟩,
    ⟨9, 1, 1, 14,
      [[tg 724, tg 5989, tg 76540, tg 81805], [tg 828, tg 6093, tg 76644, tg 81909], [tg 854, tg 6119, tg 76670, tg 81935], [tg 958, tg 6223, tg 76774, tg 82039]],
      [tg 455620, tg 460885, tg 531436, tg 536701]⟩,
    ⟨9, 1, 2, 15,
      [[tg 737, tg 6002, tg 76553, tg 81818], [tg 763, tg 6028, tg 76579, tg 81844], [tg 841, tg 6106, tg 76657, tg 81922], [tg 880, tg 6145, tg 76696, tg 81961], [tg 971, tg 6236, tg 76787, tg 82052]],
      [tg 607265, tg 612530, tg 683081, tg 688346]⟩,
    ⟨9, 1, 3, 20,
      [[tg 750, tg 6015, tg 76566, tg 81831], [tg 776, tg 6041, tg 76592, tg 81857], [tg 893, tg 6158, tg 76709, tg 81974], [tg 51255, tg 56520, tg 127071, tg 132336], [tg 984, tg 6249, tg 76800, tg 82065]],
      [tg 607278, tg 612543, tg 683094, tg 688359]⟩,
    ⟨9, 1, 4, 16,
      [[tg 763, tg 6028, tg 76579, tg 81844], [tg 854, tg 6119, tg 76670, tg 81935], [tg 906, tg 6171, tg 76722, tg 81987], [tg 971, tg 6236, tg 76787, tg 82052], [tg 997, tg 6262, tg 76813, tg 82078]],
      [tg 607291, tg 612556, tg 683107, tg 688372]⟩,
    ⟨9, 1, 5, 20,
      [[tg 776, tg 6041, tg 76592, tg 81857], [tg 867, tg 6132, tg 76683, tg 81948], [tg 919, tg 6184, tg 76735, tg 82000], [tg 984, tg 6249, tg 76800, tg 82065], [tg 1010, tg 6275, tg 76826, tg 82091]],
      [tg 607304, tg 612569, tg 683120, tg 688385]⟩,
    ⟨9, 1, 6, 17,
      [[tg 789, tg 6054, tg 76605, tg 81870], [tg 880, tg 6145, tg 76696, tg 81961], [tg 932, tg 6197, tg 76748, tg 82013], [tg 1023, tg 6288, tg 76839, tg 82104]],
      [tg 455685, tg 460950, tg 531501, tg 536766]⟩,
    ⟨9, 1, 7, 19,
      [[tg 802, tg 6067, tg 76618, tg 81883], [tg 893, tg 6158, tg 76709, tg 81974], [tg 932, tg 6197, tg 76748, tg 82013], [tg 1036, tg 6301, tg 76852, tg 82117]],
      [tg 455698, tg 460963, tg 531514, tg 536779]⟩,
    ⟨9, 1, 8, 18,
      [[tg 815, tg 6080, tg 76631, tg 81896], [tg 906, tg 6171, tg 76722, tg 81987], [tg 919, tg 6184, tg 76735, tg 82000], [tg 1049, tg 6314, tg 76865, tg 82130]],
      [tg 455711, tg 460976, tg 531527, tg 536792]⟩,
    ⟨10, 1, 0, 14,
      [[tg 828, tg 6093, tg 76644, tg 81909], [tg 4254, tg 9519, tg 29532, tg 34797], [tg 958, tg 6223, tg 76774, tg 82039], [tg 4221, tg 9486, tg 80037, tg 85302]],
      [tg 455724, tg 460989, tg 531540, tg 536805]⟩,
    ⟨10, 1, 1, 15,
      [[tg 841, tg 6106, tg 76657, tg 81922], [tg 945, tg 6210, tg 76761, tg 82026], [tg 971, tg 6236, tg 76787, tg 82052], [tg 4234, tg 9499, tg 80050, tg 85315]],
      [tg 455737, tg 461002, tg 531553, tg 536818]⟩,
    ⟨10, 1, 2, 16,
      [[tg 854, tg 6119, tg 76670, tg 81935], [tg 880, tg 6145, tg 76696, tg 81961], [tg 958, tg 6223, tg 76774, tg 82039], [tg 997, tg 6262, tg 76813, tg 82078], [tg 4247, tg 9512, tg 80063, tg 85328]],
      [tg 607382, tg 612647, tg 683198, tg 688463]⟩,
    ⟨10, 1, 3, 21,
      [[tg 867, tg 6132, tg 76683, tg 81948], [tg 893, tg 6158, tg 76709, tg 81974], [tg 1010, tg 6275, tg 76826, tg 82091], [tg 51372, tg 56637, tg 127188, tg 132453], [tg 4260, tg 9525, tg 80076, tg 85341]],
      [tg 607395, tg 612660, tg 683211, tg 688476]⟩,
    ⟨10, 1, 4, 17,
      [[tg 880, tg 6145, tg 76696, tg 81961], [tg 971, tg 6236, tg 76787, tg 82052], [tg 1023, tg 6288, tg 76839, tg 82104], [tg 4247, tg 9512, tg 80063, tg 85328], [tg 4273, tg 9538, tg 80089, tg 85354]],
      [tg 607408, tg 612673, tg 683224, tg 688489]⟩,
    ⟨10, 1, 5, 21,
      [[tg 893, tg 6158, tg 76709, tg 81974], [tg 984, tg 6249, tg 76800, tg 82065], [tg 1036, tg 6301, tg 76852, tg 82117], [tg 4260, tg 9525, tg 80076, tg 85341], [tg 4286, tg 9551, tg 80102, tg 85367]],
      [tg 607421, tg 612686, tg 683237, tg 688502]⟩,
    ⟨10, 1, 6, 18,
      [[tg 906, tg 6171, tg 76722, tg 81987], [tg 997, tg 6262, tg 76813, tg 82078], [tg 1049, tg 6314, tg 76865, tg 82130], [tg 4299, tg 9564, tg 80115, tg 85380]],
      [tg 455802, tg 461067, tg 531618, tg 536883]⟩,
    ⟨10, 1, 7, 20,
      [[tg 919, tg 6184, tg 76735, tg 82000], [tg 1010, tg 6275, tg 76826, tg 82091], [tg 1049, tg 6314, tg 76865, tg 82130], [tg 4312, tg 9577, tg 80128, tg 85393]],
      [tg 455815, tg 461080, tg 531631, tg 536896]⟩,
    ⟨10, 1, 8, 19,
      [[tg 932, tg 6197, tg 76748, tg 82013], [tg 1023, tg 6288, tg 76839, tg 82104], [tg 1036, tg 6301, tg 76852, tg 82117], [tg 4325, tg 9590, tg 80141, tg 85406]],
      [tg 455828, tg 461093, tg 531644, tg 536909]⟩]⟩,
  ⟨2, 1, 1, -1, 1, [(1, 1, 1), (-1, 1, 1)], 1, 1, 1, 2, -1, 1, 1, 2,
   [⟨0, 1, 0, 5,
      [[tg 5, tg 1180, tg 6323, tg 76996], [tg 39, tg 1096, tg 2150, tg 26491], [tg 23, tg 5288, tg 75839, tg 81104], [tg 4, tg 5269, tg 25399, tg 30664]],
      [tg 454935, tg 455992, tg 457046, tg 481387]⟩,
    ⟨0, 1, 1, 6,
      [[tg 18, tg 1193, tg 6336, tg 77009], [tg 10, tg 5275, tg 75826, tg 81091], [tg 36, tg 5301, tg 75852, tg 81117], [tg 17, tg 5282, tg 25412, tg 30677]],
      [tg 303274, tg 308539, tg 379090, tg 384355]⟩,
    ⟨0, 1, 2, 7,
      [[tg 31, tg 1206, tg 6349, tg 77022], [tg 57, tg 1232, tg 6375, tg 77048], [tg 23, tg 5288, tg 75839, tg 81104], [tg 62, tg 5327, tg 75878, tg 81143], [tg 30, tg 5295, tg 25425, tg 30690]],
      [tg 303287, tg 308552, tg 379103, tg 384368]⟩,
    ⟨0, 1, 3, 13,
      [[tg 44, tg 1219, tg 6362, tg 77035], [tg 70, tg 1245, tg 6388, tg 77061], [tg 75, tg 5340, tg 75891, tg 81156], [tg 127, tg 5392, tg 75943, tg 81208], [tg 43, tg 5308, tg 25438, tg 30703]],
      [tg 454966, tg 456141, tg 461284, tg 531957]⟩,
    ⟨0, 1, 4, 8,
      [[tg 57, tg 1232, tg 6375, tg 77048], [tg 36, tg 5301, tg 75852, tg 81117], [tg 88, tg 5353, tg 75904, tg 81169], [tg 30, tg 5295, tg 25425, tg 30690], [tg 56, tg 5321, tg 25451, tg 30716]],
      [tg 454932, tg 460197, tg 530748, tg 536013]⟩,
    ⟨0, 1, 5, 12,
      [[tg 70, tg 1245, tg 6388, tg 77061], [tg 49, tg 5314, tg 75865, tg 81130], [tg 101, tg 5366, tg 75917, tg 81182], [tg 43, tg 5308, tg 25438, tg 30703], [tg 69, tg 5334, tg 25464, tg 30729]],
      [tg 151733, tg 156998, tg 227549, tg 232814]⟩,
    ⟨0, 1, 6, 9,
      [[tg 83, tg 1258, tg 6401, tg 77074], [tg 62, tg 5327, tg 75878, tg 81143], [tg 114, tg 5379, tg 75930, tg 81195], [tg 82, tg 5347, tg 25477, tg 30742]],
      [tg 303326, tg 308591, tg 379142, tg 384407]⟩,
    ⟨0, 1, 7, 11,
      [[tg 96, tg 1271, tg 6414, tg 77087], [tg 75, tg 5340, tg 75891, tg 81156], [tg 114, tg 5379, tg 75930, tg 81195], [tg 95, tg 5360, tg 25490, tg 30755]],
      [tg 303378, tg 308643, tg 379194, tg 384459]⟩,
    ⟨0, 1, 8, 10,
      [[tg 109, tg 1284, tg 6427, tg 77100], [tg 88, tg 5353, tg 75904, tg 81169], [tg 101, tg 5366, tg 75917, tg 81182], [tg 108, tg 5373, tg 25503, tg 30768]],
      [tg 303352, tg 308617, tg 379168, tg 384433]⟩,
    ⟨0, 2, 0, 14,
      [[tg 50554, tg 55819, tg 126370, tg 131635], [tg 49, tg 5314, tg 75865, tg 81130], [tg 140, tg 5405, tg 75956, tg 81221], [tg 4222, tg 9487, tg 80038, tg 85303]],
      [tg 454945, tg 460210, tg 530761, tg 536026]⟩,
    ⟨0, 2, 1, 15,
      [[tg 50567, tg 55832, tg 126383, tg 131648], [tg 127, tg 5392, tg 75943, tg 81208], [tg 153, tg 5418, tg 75969, tg 81234], [tg 4235, tg 9500, tg 80051, tg 85316]],
      [tg 303391, tg 308656, tg 379207, tg 384472]⟩,
    ⟨0, 2, 2, 16,
      [[tg 50580, tg 55845, tg 126396, tg 131661], [tg 50606, tg 55871, tg 126422, tg 131687], [tg 140, tg 5405, tg 75956, tg 81221], [tg 179, tg 5444, tg 75995, tg 81260], [tg 4248, tg 9513, tg 80064, tg 85329]],
      [tg 303404, tg 308669, tg 379220, tg 384485]⟩,
    ⟨0, 2, 3, 22,
      [[tg 50593, tg 55858, tg 126409, tg 131674], [tg 50619, tg 55884, tg 126435, tg 131700], [tg 192, tg 5457, tg 76008, tg 81273], [tg 54766, tg 60031, tg 130582, tg 135847], [tg 4261, tg 9526, tg 80077, tg 85342]],
      [tg 505515, tg 510780, tg 581331, tg 586596]⟩,
    ⟨0, 2, 4, 17,
      [[tg 50606, tg 55871, tg 126422, tg 131687], [tg 153, tg 5418, tg 75969, tg 81234], [tg 205, tg 5470, tg 76021, tg 81286], [tg 4248, tg 9513, tg 80064, tg 85329], [tg 4274, tg 9539, tg 80090, tg 85355]],
      [tg 455049, tg 460314, tg 530865, tg 536130]⟩,
    ⟨0, 2, 5, 21,
      [[tg 50619, tg 55884, tg 126435, tg 131700], [tg 166, tg 5431, tg 75982, tg 81247], [tg 218, tg 5483, tg 76034, tg 81299], [tg 4261, tg 9526, tg 80077, tg 85342], [tg 4287, tg 9552, tg 80103, tg 85368]],
      [tg 151850, tg 157115, tg 227666, tg 232931]⟩,
    ⟨0, 2, 6, 18,
      [[tg 50632, tg 55897, tg 126448, tg 131713], [tg 179, tg 5444, tg 75995, tg 81260], [tg 231, tg 5496, tg 76047, tg 81312], [tg 4300, tg 9565, tg 80116, tg 85381]],
      [tg 303443, tg 308708, tg 379259, tg 384524]⟩,
    ⟨0, 2, 7, 20,
      [[tg 50645, tg 55910, tg 126461, tg 131726], [tg 192, tg 5457, tg 76008, tg 81273], [tg 231, tg 5496, tg 76047, tg 81312], [tg 4313, tg 9578, tg 80129, tg 85394]],
      [tg 303495, tg 308760, tg 379311, tg 384576]⟩,
    ⟨0, 2, 8, 19,
      [[tg 50658, tg 55923, tg 126474, tg 131739], [tg 205, tg 5470, tg 76021, tg 81286], [tg 218, tg 5483, tg 76034, tg 81299], [tg 4326, tg 9591, tg 80142, tg 85407]],
      [tg 303469, tg 308734, tg 379285, tg 384550]⟩]⟩,
  ⟨2, -1, 1, -9, 0, [(0, 9, 1), (-1, -1, 1)], 0, 9, 1, 9, -1, -1, 1, 9,
   [⟨-10, 1, 0, 15,
      [[tg 51491, tg 56756, tg 127307, tg 132572], [tg 4257, tg 52583, tg 10575, tg 128399], [tg 24, tg 5289, tg 75840, tg 81105], [tg 128, tg 5393, tg 75944, tg 81209]],
      [tg 459153, tg 507479, tg 465471, tg 583295]⟩,
    ⟨-10, 1, 1, 16,
      [[tg 51504, tg 56769, tg 127320, tg 132585], [tg 11, tg 5276, tg 75827, tg 81092], [tg 37, tg 5302, tg 75853, tg 81118], [tg 141, tg 5406, tg 75957, tg 81222]],
      [tg 303275, tg 308540, tg 379091, tg 384356]⟩,
    ⟨-10, 1, 2, 17,
      [[tg 51517, tg 56782, tg 127333, tg 132598], [tg 51543, tg 56808, tg 127359, tg 132624], [tg 24, tg 5289, tg 75840, tg 81105], [tg 63, tg 5328, tg 75879, tg 81144], [tg 154, tg 5419, tg 75970, tg 81235]],
      [tg 303288, tg 308553, tg 379104, tg 384369]⟩,
    ⟨-10, 1, 3, 22,
      [[tg 51530, tg 56795, tg 127346, tg 132611], [tg 51556, tg 56821, tg 127372, tg 132637], [tg 76, tg 5341, tg 75892, tg 81157], [tg 4340, tg 9605, tg 80156, tg 85421], [tg 167, tg 5432, tg 75983, tg 81248]],
      [tg 151708, tg 156973, tg 227524, tg 232789]⟩,
    ⟨-10, 1, 4, 17,
      [[tg 51543, tg 56808, tg 127359, tg 132624], [tg 37, tg 5302, tg 75853, tg 81118], [tg 89, tg 5354, tg 75905, tg 81170], [tg 154, tg 5419, tg 75970, tg 81235], [tg 180, tg 5445, tg 75996, tg 81261]],
      [tg 151786, tg 157051, tg 227602, tg 232867]⟩,
    ⟨-10, 1, 5, 21,
      [[tg 51556, tg 56821, tg 127372, tg 132637], [tg 50, tg 5315, tg 75866, tg 81131], [tg 102, tg 5367, tg 75918, tg 81183], [tg 167, tg 5432, tg 75983, tg 81248], [tg 193, tg 5458, tg 76009, tg 81274]],
      [tg 151734, tg 156999, tg 227550, tg 232815]⟩,
    ⟨-10, 1, 6, 18,
      [[tg 51569, tg 56834, tg 127385, tg 132650], [tg 63, tg 5328, tg 75879, tg 81144], [tg 115, tg 5380, tg 75931, tg 81196], [tg 206, tg 5471, tg 76022, tg 81287]],
      [tg 303327, tg 308592, tg 379143, tg 384408]⟩,
    ⟨-10, 1, 7, 20,
      [[tg 51582, tg 56847, tg 127398, tg 132663], [tg 76, tg 5341, tg 75892, tg 81157], [tg 115, tg 5380, tg 75931, tg 81196], [tg 219, tg 5484, tg 76035, tg 81300]],
      [tg 303379, tg 308644, tg 379195, tg 384460]⟩,
    ⟨-10, 1, 8, 19,
      [[tg 51595, tg 56860, tg 127411, tg 132676], [tg 89, tg 5354, tg 75905, tg 81170], [tg 102, tg 5367, tg 75918, tg 81183], [tg 232, tg 5497, tg 76048, tg 81313]],
      [tg 303353, tg 308618, tg 379169, tg 384434]⟩,
    ⟨-9, 1, 0, 14,
      [[tg 11, tg 5276, tg 75827, tg 81092], [tg 981, tg 1103, tg 7299, tg 76919], [tg 141, tg 5406, tg 75957, tg 81222], [tg 245, tg 5510, tg 76061, tg 81326]],
      [tg 455877, tg 455999, tg 462195, tg 531815]⟩,
    ⟨-9, 1, 1, 15,
      [[tg 24, tg 5289, tg 75840, tg 81105], [tg 128, tg 5393, tg 75944, tg 81209], [tg 154, tg 5419, tg 75970, tg 81235], [tg 258, tg 5523, tg 76074, tg 81339]],
      [tg 303392, tg 308657, tg 379208, tg 384473]⟩,
    ⟨-9, 1, 2, 16,
      [[tg 37, tg 5302, tg 75853, tg 81118], [tg 63, tg 5328, tg 75879, tg 81144], [tg 141, tg 5406, tg 75957, tg 81222], [tg 180, tg 5445, tg 75996, tg 81261], [tg 271, tg 5536, tg 76087, tg 81352]],
      [tg 303405, tg 308670, tg 379221, tg 384486]⟩,
    ⟨-9, 1, 3, 21,
      [[tg 50, tg 5315, tg 75866, tg 81131], [tg 76, tg 5341, tg 75892, tg 81157], [tg 193, tg 5458, tg 76009, tg 81274], [tg 4457, tg 9722, tg 80273, tg 85538], [tg 284, tg 5549, tg 76100, tg 81365]],
      [tg 151825, tg 157090, tg 227641, tg 232906]⟩,
    ⟨-9, 1, 4, 16,
      [[tg 63, tg 5328, tg 75879, tg 81144], [tg 154, tg 5419, tg 75970, tg 81235], [tg 206, tg 5471, tg 76022, tg 81287], [tg 271, tg 5536, tg 76087, tg 81352], [tg 297, tg 5562, tg 76113, tg 81378]],
      [tg 151903, tg 157168, tg 227719, tg 232984]⟩,
    ⟨-9, 1, 5, 20,
      [[tg 76, tg 5341, tg 75892, tg 81157], [tg 167, tg 5432, tg 75983, tg 81248], [tg 219, tg 5484, tg 76035, tg 81300], [tg 284, tg 5549, tg 76100, tg 81365], [tg 310, tg 5575, tg 76126, tg 81391]],
      [tg 151851, tg 157116, tg 227667, tg 232932]⟩,
    ⟨-9, 1, 6, 17,
      [[tg 89, tg 5354, tg 75905, tg 81170], [tg 180, tg 5445, tg 75996, tg 81261], [tg 232, tg 5497, tg 76048, tg 81313], [tg 323, tg 5588, tg 76139, tg 81404]],
      [tg 303444, tg 308709, tg 379260, tg 384525]⟩,
    ⟨-9, 1, 7, 19,
      [[tg 102, tg 5367, tg 75918, tg 81183], [tg 193, tg 5458, tg 76009, tg 81274], [tg 232, tg 5497, tg 76048, tg 81313], [tg 336, tg 5601, tg 76152, tg 81417]],
      [tg 303496, tg 308761, tg 379312, tg 384577]⟩,
    ⟨-9, 1, 8, 18,
      [[tg 115, tg 5380, tg 75931, tg 81196], [tg 206, tg 5471, tg 76022, tg 81287], [tg 219, tg 5484, tg 76035, tg 81300], [tg 349, tg 5614, tg 76165, tg 81430]],
      [tg 303470, tg 308735, tg 379286, tg 384551]⟩,
    ⟨-8, 1, 0, 13,
      [[tg 128, tg 5393, tg 75944, tg 81209], [tg 864, tg 1220, tg 7182, tg 77036], [tg 258, tg 5523, tg 76074, tg 81339], [tg 362, tg 5627, tg 76178, tg 81443]],
      [tg 455760, tg 456116, tg 462078, tg 531932]⟩,
    ⟨-8, 1, 1, 14,
      [[tg 141, tg 5406, tg 75957, tg 81222], [tg 245, tg 5510, tg 76061, tg 81326], [tg 271, tg 5536, tg 76087, tg 81352], [tg 375, tg 5640, tg 76191, tg 81456]],
      [tg 303509, tg 308774, tg 379325, tg 384590]⟩,
    ⟨-8, 1, 2, 15,
      [[tg 154, tg 5419, tg 75970, tg 81235], [tg 180, tg 5445, tg 75996, tg 81261], [tg 258, tg 5523, tg 76074, tg 81339], [tg 297, tg 5562, tg 76113, tg 81378], [tg 388, tg 5653, tg 76204, tg 81469]],
      [tg 303522, tg 308787, tg 379338, tg 384603]⟩,
    ⟨-8, 1, 3, 20,
      [[tg 167, tg 5432, tg 75983, tg 81248], [tg 193, tg 5458, tg 76009, tg 81274], [tg 310, tg 5575, tg 76126, tg 81391], [tg 4574, tg 9839, tg 80390, tg 85655], [tg 401, tg 5666, tg 76217, tg 81482]],
      [tg 151942, tg 157207, tg 227758, tg 233023]⟩,
    ⟨-8, 1, 4, 15,
      [[tg 180, tg 5445, tg 75996, tg 81261], [tg 271, tg 5536, tg 76087, tg 81352], [tg 323, tg 5588, tg 76139, tg 81404], [tg 388, tg 5653, tg 76204, tg 81469], [tg 414, tg 5679, tg 76230, tg 81495]],
      [tg 152020, tg 157285, tg 227836, tg 233101]⟩,
    ⟨-8, 1, 5, 19,
      [[tg 193, tg 5458, tg 76009, tg 81274], [tg 284, tg 5549, tg 76100, tg 81365], [tg 336, tg 5601, tg 76152, tg 81417], [tg 401, tg 5666, tg 76217, tg 81482], [tg 427, tg 5692, tg 76243, tg 81508]],
      [tg 151968, tg 157233, tg 227784, tg 233049]⟩,
    ⟨-8, 1, 6, 16,
      [[tg 206, tg 5471, tg 76022, tg 81287], [tg 297, tg 5562, tg 76113, tg 81378], [tg 349, tg 5614, tg 76165, tg 81430], [tg 440, tg 5705, tg 76256, tg 81521]],
      [tg 303561, tg 308826, tg 379377, tg 384642]⟩,
    ⟨-8, 1, 7, 18,
      [[tg 219, tg 5484, tg 76035, tg 81300], [tg 310, tg 5575, tg 76126, tg 81391], [tg 349, tg 5614, tg 76165, tg 81430], [tg 453, tg 5718, tg 76269, tg 81534]],
      [tg 303613, tg 308878, tg 379429, tg 384694]⟩,
    ⟨-8, 1, 8, 17,
      [[tg 232, tg 5497, tg 76048, tg 81313], [tg 323, tg 5588, tg 76139, tg 81404], [tg 336, tg 5601, tg 76152, tg 81417], [tg 466, tg 5731, tg 76282, tg 81547]],
      [tg 303587, tg 308852, tg 379403, tg 384668]⟩,
    ⟨-7, 1, 0, 12,
      [[tg 245, tg 5510, tg 76061, tg 81326], [tg 747, tg 1337, tg 7065, tg 77153], [tg 375, tg 5640, tg 76191, tg 81456], [tg 479, tg 5744, tg 76295, tg 81560]],
      [tg 455643, tg 456233, tg 461961, tg 532049]⟩,
    ⟨-7, 1, 1, 13,
      [[tg 258, tg 5523, tg 76074, tg 81339], [tg 362, tg 5627, tg 76178, tg 81443], [tg 388, tg 5653, tg 76204, tg 81469], [tg 492, tg 5757, tg 76308, tg 81573]],
      [tg 303626, tg 308891, tg 379442, tg 384707]⟩,
    ⟨-7, 1, 2, 14,
      [[tg 271, tg 5536, tg 76087, tg 81352], [tg 297, tg 5562, tg 76113, tg 81378], [tg 375, tg 5640, tg 76191, tg 81456], [tg 414, tg 5679, tg 76230, tg 81495], [tg 505, tg 5770, tg 76321, tg 81586]],
      [tg 303639, tg 308904, tg 379455, tg 384720]⟩,
    ⟨-7, 1, 3, 19,
      [[tg 284, tg 5549, tg 76100, tg 81365], [tg 310, tg 5575, tg 76126, tg 81391], [tg 427, tg 5692, tg 76243, tg 81508], [tg 4691, tg 9956, tg 80507, tg 85772], [tg 518, tg 5783, tg 76334, tg 81599]],
      [tg 152059, tg 157324, tg 227875, tg 233140]⟩,
    ⟨-7, 1, 4, 14,
      [[tg 297, tg 5562, tg 76113, tg 81378], [tg 388, tg 5653, tg 76204, tg 81469], [tg 440, tg 5705, tg 76256, tg 81521], [tg 505, tg 5770, tg 76321, tg 81586], [tg 531, tg 5796, tg 76347, tg 81612]],
      [tg 152137, tg 157402, tg 227953, tg 233218]⟩,
    ⟨-7, 1, 5, 18,
      [[tg 310, tg 5575, tg 76126, tg 81391], [tg 401, tg 5666, tg 76217, tg 81482], [tg 453, tg 5718, tg 76269, tg 81534], [tg 518, tg 5783, tg 76334, tg 81599], [tg 544, tg 5809, tg 76360, tg 81625]],
      [tg 152085, tg 157350, tg 227901, tg 233166]⟩,
    ⟨-7, 1, 6, 15,
      [[tg 323, tg 5588, tg 76139, tg 81404], [tg 414, tg 5679, tg 76230, tg 81495], [tg 466, tg 5731, tg 76282, tg 81547], [tg 557, tg 5822, tg 76373, tg 81638]],
      [tg 303678, tg 308943, tg 379494, tg 384759]⟩,
    ⟨-7, 1, 7, 17,
      [[tg 336, tg 5601, tg 76152, tg 81417], [tg 427, tg 5692, tg 76243, tg 81508], [tg 466, tg 5731, tg 76282, tg 81547], [tg 570, tg 5835, tg 76386, tg 81651]],
      [tg 303730, tg 308995, tg 379546, tg 384811]⟩,
    ⟨-7, 1, 8, 16,
      [[tg 349, tg 5614, tg 76165, tg 81430], [tg 440, tg 5705, tg 76256, tg 81521], [tg 453, tg 5718, tg 76269, tg 81534], [tg 583, tg 5848, tg 76399, tg 81664]],
      [tg 303704, tg 308969, tg 379520, tg 384785]⟩,
    ⟨-6, 1, 0, 11,
      [[tg 362, tg 5627, tg 76178, tg 81443], [tg 630, tg 1454, tg 6948, tg 77270], [tg 492, tg 5757, tg 76308, tg 81573], [tg 596, tg 5861, tg 76412, tg 81677]],
      [tg 455526, tg 456350, tg 461844, tg 532166]⟩,
    ⟨-6, 1, 1, 12,
      [[tg 375, tg 5640, tg 76191, tg 81456], [tg 479, tg 5744, tg 76295, tg 81560], [tg 505, tg 5770, tg 76321, tg 81586], [tg 609, tg 5874, tg 76425, tg 81690]],
      [tg 303743, tg 309008, tg 379559, tg 384824]⟩,
    ⟨-6, 1, 2, 13,
      [[tg 388, tg 5653, tg 76204, tg 81469], [tg 414, tg 5679, tg 76230, tg 81495], [tg 492, tg 5757, tg 76308, tg 81573], [tg 531, tg 5796, tg 76347, tg 81612], [tg 622, tg 5887, tg 76438, tg 81703]],
      [tg 303756, tg 309021, tg 379572, tg 384837]⟩,
    ⟨-6, 1, 3, 18,
      [[tg 401, tg 5666, tg 76217, tg 81482], [tg 427, tg 5692, tg 76243, tg 81508], [tg 544, tg 5809, tg 76360, tg 81625], [tg 4808, tg 10073, tg 80624, tg 85889], [tg 635, tg 5900, tg 76451, tg 81716]],
      [tg 152176, tg 157441, tg 227992, tg 233257]⟩,
    ⟨-6, 1, 4, 13,
      [[tg 414, tg 5679, tg 76230, tg 81495], [tg 505, tg 5770, tg 76321, tg 81586], [tg 557, tg 5822, tg 76373, tg 81638], [tg 622, tg 5887, tg 76438, tg 81703], [tg 648, tg 5913, tg 76464, tg 81729]],
      [tg 152254, tg 157519, tg 228070, tg 233335]⟩,
    ⟨-6, 1, 5, 17,
      [[tg 427, tg 5692, tg 76243, tg 81508], [tg 518, tg 5783, tg 76334, tg 81599], [tg 570, tg 5835, tg 76386, tg 81651], [tg 635, tg 5900, tg 76451, tg 81716], [tg 661, tg 5926, tg 76477, tg 81742]],
      [tg 152202, tg 157467, tg 228018, tg 233283]⟩,
    ⟨-6, 1, 6, 14,
      [[tg 440, tg 5705, tg 76256, tg 81521], [tg 531, tg 5796, tg 76347, tg 81612], [tg 583, tg 5848, tg 76399, tg 81664], [tg 674, tg 5939, tg 76490, tg 81755]],
      [tg 303795, tg 309060, tg 379611, tg 384876]⟩,
    ⟨-6, 1, 7, 16,
      [[tg 453, tg 5718, tg 76269, tg 81534], [tg 544, tg 5809, tg 76360, tg 81625], [tg 583, tg 5848, tg 76399, tg 81664], [tg 687, tg 5952, tg 76503, tg 81768]],
      [tg 303847, tg 309112, tg 379663, tg 384928]⟩,
    ⟨-6, 1, 8, 15,
      [[tg 466, tg 5731, tg 76282, tg 81547], [tg 557, tg 5822, tg 76373, tg 81638], [tg 570, tg 5835, tg 76386, tg 81651], [tg 700, tg 5965, tg 76516, tg 81781]],
      [tg 303821, tg 309086, tg 379637, tg 384902]⟩,
    ⟨-5, 1, 0, 10,
      [[tg 479, tg 5744, tg 76295, tg 81560], [tg 513, tg 1571, tg 6831, tg 77387], [tg 609, tg 5874, tg 76425, tg 81690], [tg 713, tg 5978, tg 76529, tg 81794]],
      [tg 455409, tg 456467, tg 461727, tg 532283]⟩,
    ⟨-5, 1, 1, 11,
      [[tg 492, tg 5757, tg 76308, tg 81573], [tg 596, tg 5861, tg 76412, tg 81677], [tg 622, tg 5887, tg 76438, tg 81703], [tg 726, tg 5991, tg 76542, tg 81807]],
      [tg 303860, tg 309125, tg 379676, tg 384941]⟩,
    ⟨-5, 1, 2, 12,
      [[tg 505, tg 5770, tg 76321, tg 81586], [tg 531, tg 5796, tg 76347, tg 81612], [tg 609, tg 5874, tg 76425, tg 81690], [tg 648, tg 5913, tg 76464, tg 81729], [tg 739, tg 6004, tg 76555, tg 81820]],
      [tg 303873, tg 309138, tg 379689, tg 384954]⟩,
    ⟨-5, 1, 3, 17,
      [[tg 518, tg 5783, tg 76334, tg 81599], [tg 544, tg 5809, tg 76360, tg 81625], [tg 661, tg 5926, tg 76477, tg 81742], [tg 4925, tg 10190, tg 80741, tg 86006], [tg 752, tg 6017, tg 76568, tg 81833]],
      [tg 152293, tg 157558, tg 228109, tg 233374]⟩,
    ⟨-5, 1, 4, 12,
      [[tg 531, tg 5796, tg 76347, tg 81612], [tg 622, tg 5887, tg 76438, tg 81703], [tg 674, tg 5939, tg 76490, tg 81755], [tg 739, tg 6004, tg 76555, tg 81820], [tg 765, tg 6030, tg 76581, tg 81846]],
      [tg 152371, tg 157636, tg 228187, tg 233452]⟩,
    ⟨-5, 1, 5, 16,
      [[tg 544, tg 5809, tg 76360, tg 81625], [tg 635, tg 5900, tg 76451, tg 81716], [tg 687, tg 5952, tg 76503, tg 81768], [tg 752, tg 6017, tg 76568, tg 81833], [tg 778, tg 6043, tg 76594, tg 81859]],
      [tg 152319, tg 157584, tg 228135, tg 233400]⟩,
    ⟨-5, 1, 6, 13,
      [[tg 557, tg 5822, tg 76373, tg 81638], [tg 648, tg 5913, tg 76464, tg 81729], [tg 700, tg 5965, tg 76516, tg 81781], [tg 791, tg 6056, tg 76607, tg 81872]],
      [tg 303912, tg 309177, tg 379728, tg 384993]⟩,
    ⟨-5, 1, 7, 15,
      [[tg 570, tg 5835, tg 76386, tg 81651], [tg 661, tg 5926, tg 76477, tg 81742], [tg 700, tg 5965, tg 76516, tg 81781], [tg 804, tg 6069, tg 76620, tg 81885]],
      [tg 303964, tg 309229, tg 379780, tg 385045]⟩,
    ⟨-5, 1, 8, 14,
      [[tg 583, tg 5848, tg 76399, tg 81664], [tg 674, tg 5939, tg 76490, tg 81755], [tg 687, tg 5952, tg 76503, tg 81768], [tg 817, tg 6082, tg 76633, tg 81898]],
      [tg 303938, tg 309203, tg 379754, tg 385019]⟩,
    ⟨-4, 1, 0, 9,
      [[tg 596, tg 5861, tg 76412, tg 81677], [tg 396, tg 1688, tg 6714, tg 77504], [tg 726, tg 5991, tg 76542, tg 81807], [tg 830, tg 6095, tg 76646, tg 81911]],
      [tg 455292, tg 456584, tg 461610, tg 532400]⟩,
    ⟨-4, 1, 1, 10,
      [[tg 609, tg 5874, tg 76425, tg 81690], [tg 713, tg 5978, tg 76529, tg 81794], [tg 739, tg 6004, tg 76555, tg 81820], [tg 843, tg 6108, tg 76659, tg 81924]],
      [tg 303977, tg 309242, tg 379793, tg 385058]⟩,
    ⟨-4, 1, 2, 11,
      [[tg 622, tg 5887, tg 76438, tg 81703], [tg 648, tg 5913, tg 76464, tg 81729], [tg 726, tg 5991, tg 76542, tg 81807], [tg 765, tg 6030, tg 76581, tg 81846], [tg 856, tg 6121, tg 76672, tg 81937]],
      [tg 303990, tg 309255, tg 379806, tg 385071]⟩,
    ⟨-4, 1, 3, 16,
      [[tg 635, tg 5900, tg 76451, tg 81716], [tg 661, tg 5926, tg 76477, tg 81742], [tg 778, tg 6043, tg 76594, tg 81859], [tg 5042, tg 10307, tg 80858, tg 86123], [tg 869, tg 6134, tg 76685, tg 81950]],
      [tg 152410, tg 157675, tg 228226, tg 233491]⟩,
    ⟨-4, 1, 4, 11,
      [[tg 648, tg 5913, tg 76464, tg 81729], [tg 739, tg 6004, tg 76555, tg 81820], [tg 791, tg 6056, tg 76607, tg 81872], [tg 856, tg 6121, tg 76672, tg 81937], [tg 882, tg 6147, tg 76698, tg 81963]],
      [tg 152488, tg 157753, tg 228304, tg 233569]⟩,
    ⟨-4, 1, 5, 15,
      [[tg 661, tg 5926, tg 76477, tg 81742], [tg 752, tg 6017, tg 76568, tg 81833], [tg 804, tg 6069, tg 76620, tg 81885], [tg 869, tg 6134, tg 76685, tg 81950], [tg 895, tg 6160, tg 76711, tg 81976]],
      [tg 152436, tg 157701, tg 228252, tg 233517]⟩,
    ⟨-4, 1, 6, 12,
      [[tg 674, tg 5939, tg 76490, tg 81755], [tg 765, tg 6030, tg 76581, tg 81846], [tg 817, tg 6082, tg 76633, tg 81898], [tg 908, tg 6173, tg 76724, tg 81989]],
      [tg 304029, tg 309294, tg 379845, tg 385110]⟩,
    ⟨-4, 1, 7, 14,
      [[tg 687, tg 5952, tg 76503, tg 81768], [tg 778, tg 6043, tg 76594, tg 81859], [tg 817, tg 6082, tg 76633, tg 81898], [tg 921, tg 6186, tg 76737, tg 82002]],
      [tg 304081, tg 309346, tg 379897, tg 385162]⟩,
    ⟨-4, 1, 8, 13,
      [[tg 700, tg 5965, tg 76516, tg 81781], [tg 791, tg 6056, tg 76607, tg 81872], [tg 804, tg 6069, tg 76620, tg 81885], [tg 934, tg 6199, tg 76750, tg 82015]],
      [tg 304055, tg 309320, tg 379871, tg 385136]⟩,
    ⟨-3, 1, 0, 8,
      [[tg 713, tg 5978, tg 76529, tg 81794], [tg 279, tg 1805, tg 6597, tg 77621], [tg 843, tg 6108, tg 76659, tg 81924], [tg 947, tg 6212, tg 76763, tg 82028]],
      [tg 455175, tg 456701, tg 461493, tg 532517]⟩,
    ⟨-3, 1, 1, 9,
      [[tg 726, tg 5991, tg 76542, tg 81807], [tg 830, tg 6095, tg 76646, tg 81911], [tg 856, tg 6121, tg 76672, tg 81937], [tg 960, tg 6225, tg 76776, tg 82041]],
      [tg 304094, tg 309359, tg 379910, tg 385175]⟩,
    ⟨-3, 1, 2, 10,
      [[tg 739, tg 6004, tg 76555, tg 81820], [tg 765, tg 6030, tg 76581, tg 81846], [tg 843, tg 6108, tg 76659, tg 81924], [tg 882, tg 6147, tg 76698, tg 81963], [tg 973, tg 6238, tg 76789, tg 82054]],
      [tg 304107, tg 309372, tg 379923, tg 385188]⟩,
    ⟨-3, 1, 3, 15,
      [[tg 752, tg 6017, tg 76568, tg 81833], [tg 778, tg 6043, tg 76594, tg 81859], [tg 895, tg 6160, tg 76711, tg 81976], [tg 5159, tg 10424, tg 80975, tg 86240], [tg 986, tg 6251, tg 76802, tg 82067]],
      [tg 152527, tg 157792, tg 228343, tg 233608]⟩,
    ⟨-3, 1, 4, 10,
      [[tg 765, tg 6030, tg 76581, tg 81846], [tg 856, tg 6121, tg 76672, tg 81937], [tg 908, tg 6173, tg 76724, tg 81989], [tg 973, tg 6238, tg 76789, tg 82054], [tg 999, tg 6264, tg 76815, tg 82080]],
      [tg 152605, tg 157870, tg 228421, tg 233686]⟩,
    ⟨-3, 1, 5, 14,
      [[tg 778, tg 6043, tg 76594, tg 81859], [tg 869, tg 6134, tg 76685, tg 81950], [tg 921, tg 6186, tg 76737, tg 82002], [tg 986, tg 6251, tg 76802, tg 82067], [tg 1012, tg 6277, tg 76828, tg 82093]],
      [tg 152553, tg 157818, tg 228369, tg 233634]⟩,
    ⟨-3, 1, 6, 11,
      [[tg 791, tg 6056, tg 76607, tg 81872], [tg 882, tg 6147, tg 76698, tg 81963], [tg 934, tg 6199, tg 76750, tg 82015], [tg 1025, tg 6290, tg 76841, tg 82106]],
      [tg 304146, tg 309411, tg 379962, tg 385227]⟩,
    ⟨-3, 1, 7, 13,
      [[tg 804, tg 6069, tg 76620, tg 81885], [tg 895, tg 6160, tg 76711, tg 81976], [tg 934, tg 6199, tg 76750, tg 82015], [tg 1038, tg 6303, tg 76854, tg 82119]],
      [tg 304198, tg 309463, tg 380014, tg 385279]⟩,
    ⟨-3, 1, 8, 12,
      [[tg 817, tg 6082, tg 76633, tg 81898], [tg 908, tg 6173, tg 76724, tg 81989], [tg 921, tg 6186, tg 76737, tg 82002], [tg 1051, tg 6316, tg 76867, tg 82132]],
      [tg 304172, tg 309437, tg 379988, tg 385253]⟩,
    ⟨-2, 1, 0, 7,
      [[tg 830, tg 6095, tg 76646, tg 81911], [tg 162, tg 1922, tg 6480, tg 77738], [tg 960, tg 6225, tg 76776, tg 82041], [tg 5, tg 5270, tg 25283, tg 30548]],
      [tg 455058, tg 456818, tg 461376, tg 532634]⟩,
    ⟨-2, 1, 1, 8,
      [[tg 843, tg 6108, tg 76659, tg 81924], [tg 947, tg 6212, tg 76763, tg 82028], [tg 973, tg 6238, tg 76789, tg 82054], [tg 18, tg 5283, tg 25296, tg 30561]],
      [tg 304211, tg 309476, tg 380027, tg 385292]⟩,
    ⟨-2, 1, 2, 9,
      [[tg 856, tg 6121, tg 76672, tg 81937], [tg 882, tg 6147, tg 76698, tg 81963], [tg 960, tg 6225, tg 76776, tg 82041], [tg 999, tg 6264, tg 76815, tg 82080], [tg 31, tg 5296, tg 25309, tg 30574]],
      [tg 304224, tg 309489, tg 380040, tg 385305]⟩,
    ⟨-2, 1, 3, 14,
      [[tg 869, tg 6134, tg 76685, tg 81950], [tg 895, tg 6160, tg 76711, tg 81976], [tg 1012, tg 6277, tg 76828, tg 82093], [tg 4217, tg 9482, tg 29495, tg 34760], [tg 44, tg 5309, tg 25322, tg 30587]],
      [tg 152644, tg 157909, tg 228460, tg 233725]⟩,
    ⟨-2, 1, 4, 9,
      [[tg 882, tg 6147, tg 76698, tg 81963], [tg 973, tg 6238, tg 76789, tg 82054], [tg 1025, tg 6290, tg 76841, tg 82106], [tg 31, tg 5296, tg 25309, tg 30574], [tg 57, tg 5322, tg 25335, tg 30600]],
      [tg 151663, tg 156928, tg 176941, tg 182206]⟩,
    ⟨-2, 1, 5, 13,
      [[tg 895, tg 6160, tg 76711, tg 81976], [tg 986, tg 6251, tg 76802, tg 82067], [tg 1038, tg 6303, tg 76854, tg 82119], [tg 44, tg 5309, tg 25322, tg 30587], [tg 70, tg 5335, tg 25348, tg 30613]],
      [tg 152670, tg 157935, tg 228486, tg 233751]⟩,
    ⟨-2, 1, 6, 10,
      [[tg 908, tg 6173, tg 76724, tg 81989], [tg 999, tg 6264, tg 76815, tg 82080], [tg 1051, tg 6316, tg 76867, tg 82132], [tg 83, tg 5348, tg 25361, tg 30626]],
      [tg 304263, tg 309528, tg 380079, tg 385344]⟩,
    ⟨-2, 1, 7, 12,
      [[tg 921, tg 6186, tg 76737, tg 82002], [tg 1012, tg 6277, tg 76828, tg 82093], [tg 1051, tg 6316, tg 76867, tg 82132], [tg 96, tg 5361, tg 25374, tg 30639]],
      [tg 304315, tg 309580, tg 380131, tg 385396]⟩,
    ⟨-2, 1, 8, 11,
      [[tg 934, tg 6199, tg 76750, tg 82015], [tg 1025, tg 6290, tg 76841, tg 82106], [tg 1038, tg 6303, tg 76854, tg 82119], [tg 109, tg 5374, tg 25387, tg 30652]],
      [tg 304289, tg 309554, tg 380105, tg 385370]⟩]⟩,
  ⟨2, -9, 0, -1, -1, [(-1, 1, 1), (0, -9, 1)], -1, 1, 1, 9, 0, -9, 1, 9,
   [⟨-10, -1, 0, 22,
      [[tg 5160, tg 10425, tg 80976, tg 86241], [tg 50712, tg 55977, tg 126528, tg 131793], [tg 25, tg 5290, tg 75841, tg 81106], [tg 129, tg 5394, tg 75945, tg 81210]],
      [tg 151657, tg 156922, tg 227473, tg 232738]⟩,
    ⟨-10, -1, 1, 21,
      [[tg 5173, tg 10438, tg 80989, tg 86254], [tg 12, tg 5277, tg 75828, tg 81093], [tg 38, tg 5303, tg 75854, tg 81119], [tg 142, tg 5407, tg 75958, tg 81223]],
      [tg 303302, tg 308567, tg 379118, tg 384383]⟩,
    ⟨-10, -1, 2, 20,
      [[tg 5186, tg 10451, tg 81002, tg 86267], [tg 5212, tg 10477, tg 81028, tg 86293], [tg 25, tg 5290, tg 75841, tg 81106], [tg 64, tg 5329, tg 75880, tg 81145], [tg 155, tg 5420, tg 75971, tg 81236]],
      [tg 151696, tg 156961, tg 227512, tg 232777]⟩,
    ⟨-10, -1, 3, 15,
      [[tg 5199, tg 10464, tg 81015, tg 86280], [tg 5225, tg 10490, tg 81041, tg 86306], [tg 77, tg 5342, tg 75893, tg 81158], [tg 4218, tg 9483, tg 30432, tg 35697], [tg 168, tg 5433, tg 75984, tg 81249]],
      [tg 155850, tg 161115, tg 182064, tg 187329]⟩,
    ⟨-10, -1, 4, 19,
      [[tg 5212, tg 10477, tg 81028, tg 86293], [tg 38, tg 5303, tg 75854, tg 81119], [tg 90, tg 5355, tg 75906, tg 81171], [tg 155, tg 5420, tg 75971, tg 81236], [tg 181, tg 5446, tg 75997, tg 81262]],
      [tg 151722, tg 156987, tg 227538, tg 232803]⟩,
    ⟨-10, -1, 5, 15,
      [[tg 5225, tg 10490, tg 81041, tg 86306], [tg 51, tg 5316, tg 75867, tg 81132], [tg 103, tg 5368, tg 75919, tg 81184], [tg 168, tg 5433, tg 75984, tg 81249], [tg 194, tg 5459, tg 76010, tg 81275]],
      [tg 151800, tg 157065, tg 227616, tg 232881]⟩,
    ⟨-10, -1, 6, 18,
      [[tg 5238, tg 10503, tg 81054, tg 86319], [tg 64, tg 5329, tg 75880, tg 81145], [tg 116, tg 5381, tg 75932, tg 81197], [tg 207, tg 5472, tg 76023, tg 81288]],
      [tg 151748, tg 157013, tg 227564, tg 232829]⟩,
    ⟨-10, -1, 7, 16,
      [[tg 5251, tg 10516, tg 81067, tg 86332], [tg 77, tg 5342, tg 75893, tg 81158], [tg 116, tg 5381, tg 75932, tg 81197], [tg 220, tg 5485, tg 76036, tg 81301]],
      [tg 303341, tg 308606, tg 379157, tg 384422]⟩,
    ⟨-10, -1, 8, 17,
      [[tg 5264, tg 10529, tg 81080, tg 86345], [tg 90, tg 5355, tg 75906, tg 81171], [tg 103, tg 5368, tg 75919, tg 81184], [tg 233, tg 5498, tg 76049, tg 81314]],
      [tg 303367, tg 308632, tg 379183, tg 384448]⟩,
    ⟨-9, -1, 0, 21,
      [[tg 12, tg 5277, tg 75828, tg 81093], [tg 50829, tg 56094, tg 126645, tg 131910], [tg 142, tg 5407, tg 75958, tg 81223], [tg 246, tg 5511, tg 76062, tg 81327]],
      [tg 151774, tg 157039, tg 227590, tg 232855]⟩,
    ⟨-9, -1, 1, 20,
      [[tg 25, tg 5290, tg 75841, tg 81106], [tg 129, tg 5394, tg 75945, tg 81210], [tg 155, tg 5420, tg 75971, tg 81236], [tg 259, tg 5524, tg 76075, tg 81340]],
      [tg 303419, tg 308684, tg 379235, tg 384500]⟩,
    ⟨-9, -1, 2, 19,
      [[tg 38, tg 5303, tg 75854, tg 81119], [tg 64, tg 5329, tg 75880, tg 81145], [tg 142, tg 5407, tg 75958, tg 81223], [tg 181, tg 5446, tg 75997, tg 81262], [tg 272, tg 5537, tg 76088, tg 81353]],
      [tg 151813, tg 157078, tg 227629, tg 232894]⟩,
    ⟨-9, -1, 3, 14,
      [[tg 51, tg 5316, tg 75867, tg 81132], [tg 77, tg 5342, tg 75893, tg 81158], [tg 194, tg 5459, tg 76010, tg 81275], [tg 942, tg 6207, tg 25284, tg 30549], [tg 285, tg 5550, tg 76101, tg 81366]],
      [tg 152574, tg 157839, tg 176916, tg 182181]⟩,
    ⟨-9, -1, 4, 18,
      [[tg 64, tg 5329, tg 75880, tg 81145], [tg 155, tg 5420, tg 75971, tg 81236], [tg 207, tg 5472, tg 76023, tg 81288], [tg 272, tg 5537, tg 76088, tg 81353], [tg 298, tg 5563, tg 76114, tg 81379]],
      [tg 151839, tg 157104, tg 227655, tg 232920]⟩,
    ⟨-9, -1, 5, 14,
      [[tg 77, tg 5342, tg 75893, tg 81158], [tg 168, tg 5433, tg 75984, tg 81249], [tg 220, tg 5485, tg 76036, tg 81301], [tg 285, tg 5550, tg 76101, tg 81366], [tg 311, tg 5576, tg 76127, tg 81392]],
      [tg 151917, tg 157182, tg 227733, tg 232998]⟩,
    ⟨-9, -1, 6, 17,
      [[tg 90, tg 5355, tg 75906, tg 81171], [tg 181, tg 5446, tg 75997, tg 81262], [tg 233, tg 5498, tg 76049, tg 81314], [tg 324, tg 5589, tg 76140, tg 81405]],
      [tg 151865, tg 157130, tg 227681, tg 232946]⟩,
    ⟨-9, -1, 7, 15,
      [[tg 103, tg 5368, tg 75919, tg 81184], [tg 194, tg 5459, tg 76010, tg 81275], [tg 233, tg 5498, tg 76049, tg 81314], [tg 337, tg 5602, tg 76153, tg 81418]],
      [tg 303458, tg 308723, tg 379274, tg 384539]⟩,
    ⟨-9, -1, 8, 16,
      [[tg 116, tg 5381, tg 75932, tg 81197], [tg 207, tg 5472, tg 76023, tg 81288], [tg 220, tg 5485, tg 76036, tg 81301], [tg 350, tg 5615, tg 76166, tg 81431]],
      [tg 303484, tg 308749, tg 379300, tg 384565]⟩,
    ⟨-8, -1, 0, 20,
      [[tg 129, tg 5394, tg 75945, tg 81210], [tg 50946, tg 56211, tg 126762, tg 132027], [tg 259, tg 5524, tg 76075, tg 81340], [tg 363, tg 5628, tg 76179, tg 81444]],
      [tg 151891, tg 157156, tg 227707, tg 232972]⟩,
    ⟨-8, -1, 1, 19,
      [[tg 142, tg 5407, tg 75958, tg 81223], [tg 246, tg 5511, tg 76062, tg 81327], [tg 272, tg 5537, tg 76088, tg 81353], [tg 376, tg 5641, tg 76192, tg 81457]],
      [tg 303536, tg 308801, tg 379352, tg 384617]⟩,
    ⟨-8, -1, 2, 18,
      [[tg 155, tg 5420, tg 75971, tg 81236], [tg 181, tg 5446, tg 75997, tg 81262], [tg 259, tg 5524, tg 76075, tg 81340], [tg 298, tg 5563, tg 76114, tg 81379], [tg 389, tg 5654, tg 76205, tg 81470]],
      [tg 151930, tg 157195, tg 227746, tg 233011]⟩,
    ⟨-8, -1, 3, 13,
      [[tg 168, tg 5433, tg 75984, tg 81249], [tg 194, tg 5459, tg 76010, tg 81275], [tg 311, tg 5576, tg 76127, tg 81392], [tg 825, tg 6090, tg 25401, tg 30666], [tg 402, tg 5667, tg 76218, tg 81483]],
      [tg 152457, tg 157722, tg 177033, tg 182298]⟩,
    ⟨-8, -1, 4, 17,
      [[tg 181, tg 5446, tg 75997, tg 81262], [tg 272, tg 5537, tg 76088, tg 81353], [tg 324, tg 5589, tg 76140, tg 81405], [tg 389, tg 5654, tg 76205, tg 81470], [tg 415, tg 5680, tg 76231, tg 81496]],
      [tg 151956, tg 157221, tg 227772, tg 233037]⟩,
    ⟨-8, -1, 5, 13,
      [[tg 194, tg 5459, tg 76010, tg 81275], [tg 285, tg 5550, tg 76101, tg 81366], [tg 337, tg 5602, tg 76153, tg 81418], [tg 402, tg 5667, tg 76218, tg 81483], [tg 428, tg 5693, tg 76244, tg 81509]],
      [tg 152034, tg 157299, tg 227850, tg 233115]⟩,
    ⟨-8, -1, 6, 16,
      [[tg 207, tg 5472, tg 76023, tg 81288], [tg 298, tg 5563, tg 76114, tg 81379], [tg 350, tg 5615, tg 76166, tg 81431], [tg 441, tg 5706, tg 76257, tg 81522]],
      [tg 151982, tg 157247, tg 227798, tg 233063]⟩,
    ⟨-8, -1, 7, 14,
      [[tg 220, tg 5485, tg 76036, tg 81301], [tg 311, tg 5576, tg 76127, tg 81392], [tg 350, tg 5615, tg 76166, tg 81431], [tg 454, tg 5719, tg 76270, tg 81535]],
      [tg 303575, tg 308840, tg 379391, tg 384656]⟩,
    ⟨-8, -1, 8, 15,
      [[tg 233, tg 5498, tg 76049, tg 81314], [tg 324, tg 5589, tg 76140, tg 81405], [tg 337, tg 5602, tg 76153, tg 81418], [tg 467, tg 5732, tg 76283, tg 81548]],
      [tg 303601, tg 308866, tg 379417, tg 384682]⟩,
    ⟨-7, -1, 0, 19,
      [[tg 246, tg 5511, tg 76062, tg 81327], [tg 51063, tg 56328, tg 126879, tg 132144], [tg 376, tg 5641, tg 76192, tg 81457], [tg 480, tg 5745, tg 76296, tg 81561]],
      [tg 152008, tg 157273, tg 227824, tg 233089]⟩,
    ⟨-7, -1, 1, 18,
      [[tg 259, tg 5524, tg 76075, tg 81340], [tg 363, tg 5628, tg 76179, tg 81444], [tg 389, tg 5654, tg 76205, tg 81470], [tg 493, tg 5758, tg 76309, tg 81574]],
      [tg 303653, tg 308918, tg 379469, tg 384734]⟩,
    ⟨-7, -1, 2, 17,
      [[tg 272, tg 5537, tg 76088, tg 81353], [tg 298, tg 5563, tg 76114, tg 81379], [tg 376, tg 5641, tg 76192, tg 81457], [tg 415, tg 5680, tg 76231, tg 81496], [tg 506, tg 5771, tg 76322, tg 81587]],
      [tg 152047, tg 157312, tg 227863, tg 233128]⟩,
    ⟨-7, -1, 3, 12,
      [[tg 285, tg 5550, tg 76101, tg 81366], [tg 311, tg 5576, tg 76127, tg 81392], [tg 428, tg 5693, tg 76244, tg 81509], [tg 708, tg 5973, tg 25518, tg 30783], [tg 519, tg 5784, tg 76335, tg 81600]],
      [tg 152340, tg 157605, tg 177150, tg 182415]⟩,
    ⟨-7, -1, 4, 16,
      [[tg 298, tg 5563, tg 76114, tg 81379], [tg 389, tg 5654, tg 76205, tg 81470], [tg 441, tg 5706, tg 76257, tg 81522], [tg 506, tg 5771, tg 76322, tg 81587], [tg 532, tg 5797, tg 76348, tg 81613]],
      [tg 152073, tg 157338, tg 227889, tg 233154]⟩,
    ⟨-7, -1, 5, 12,
      [[tg 311, tg 5576, tg 76127, tg 81392], [tg 402, tg 5667, tg 76218, tg 81483], [tg 454, tg 5719, tg 76270, tg 81535], [tg 519, tg 5784, tg 76335, tg 81600], [tg 545, tg 5810, tg 76361, tg 81626]],
      [tg 152151, tg 157416, tg 227967, tg 233232]⟩,
    ⟨-7, -1, 6, 15,
      [[tg 324, tg 5589, tg 76140, tg 81405], [tg 415, tg 5680, tg 76231, tg 81496], [tg 467, tg 5732, tg 76283, tg 81548], [tg 558, tg 5823, tg 76374, tg 81639]],
      [tg 152099, tg 157364, tg 227915, tg 233180]⟩,
    ⟨-7, -1, 7, 13,
      [[tg 337, tg 5602, tg 76153, tg 81418], [tg 428, tg 5693, tg 76244, tg 81509], [tg 467, tg 5732, tg 76283, tg 81548], [tg 571, tg 5836, tg 76387, tg 81652]],
      [tg 303692, tg 308957, tg 379508, tg 384773]⟩,
    ⟨-7, -1, 8, 14,
      [[tg 350, tg 5615, tg 76166, tg 81431], [tg 441, tg 5706, tg 76257, tg 81522], [tg 454, tg 5719, tg 76270, tg 81535], [tg 584, tg 5849, tg 76400, tg 81665]],
      [tg 303718, tg 308983, tg 379534, tg 384799]⟩,
    ⟨-6, -1, 0, 18,
      [[tg 363, tg 5628, tg 76179, tg 81444], [tg 51180, tg 56445, tg 126996, tg 132261], [tg 493, tg 5758, tg 76309, tg 81574], [tg 597, tg 5862, tg 76413, tg 81678]],
      [tg 152125, tg 157390, tg 227941, tg 233206]⟩,
    ⟨-6, -1, 1, 17,
      [[tg 376, tg 5641, tg 76192, tg 81457], [tg 480, tg 5745, tg 76296, tg 81561], [tg 506, tg 5771, tg 76322, tg 81587], [tg 610, tg 5875, tg 76426, tg 81691]],
      [tg 303770, tg 309035, tg 379586, tg 384851]⟩,
    ⟨-6, -1, 2, 16,
      [[tg 389, tg 5654, tg 76205, tg 81470], [tg 415, tg 5680, tg 76231, tg 81496], [tg 493, tg 5758, tg 76309, tg 81574], [tg 532, tg 5797, tg 76348, tg 81613], [tg 623, tg 5888, tg 76439, tg 81704]],
      [tg 152164, tg 157429, tg 227980, tg 233245]⟩,
    ⟨-6, -1, 3, 11,
      [[tg 402, tg 5667, tg 76218, tg 81483], [tg 428, tg 5693, tg 76244, tg 81509], [tg 545, tg 5810, tg 76361, tg 81626], [tg 591, tg 5856, tg 25635, tg 30900], [tg 636, tg 5901, tg 76452, tg 81717]],
      [tg 152223, tg 157488, tg 177267, tg 182532]⟩,
    ⟨-6, -1, 4, 15,
      [[tg 415, tg 5680, tg 76231, tg 81496], [tg 506, tg 5771, tg 76322, tg 81587], [tg 558, tg 5823, tg 76374, tg 81639], [tg 623, tg 5888, tg 76439, tg 81704], [tg 649, tg 5914, tg 76465, tg 81730]],
      [tg 152190, tg 157455, tg 228006, tg 233271]⟩,
    ⟨-6, -1, 5, 11,
      [[tg 428, tg 5693, tg 76244, tg 81509], [tg 519, tg 5784, tg 76335, tg 81600], [tg 571, tg 5836, tg 76387, tg 81652], [tg 636, tg 5901, tg 76452, tg 81717], [tg 662, tg 5927, tg 76478, tg 81743]],
      [tg 152268, tg 157533, tg 228084, tg 233349]⟩,
    ⟨-6, -1, 6, 14,
      [[tg 441, tg 5706, tg 76257, tg 81522], [tg 532, tg 5797, tg 76348, tg 81613], [tg 584, tg 5849, tg 76400, tg 81665], [tg 675, tg 5940, tg 76491, tg 81756]],
      [tg 152216, tg 157481, tg 228032, tg 233297]⟩,
    ⟨-6, -1, 7, 12,
      [[tg 454, tg 5719, tg 76270, tg 81535], [tg 545, tg 5810, tg 76361, tg 81626], [tg 584, tg 5849, tg 76400, tg 81665], [tg 688, tg 5953, tg 76504, tg 81769]],
      [tg 303809, tg 309074, tg 379625, tg 384890]⟩,
    ⟨-6, -1, 8, 13,
      [[tg 467, tg 5732, tg 76283, tg 81548], [tg 558, tg 5823, tg 76374, tg 81639], [tg 571, tg 5836, tg 76387, tg 81652], [tg 701, tg 5966, tg 76517, tg 81782]],
      [tg 303835, tg 309100, tg 379651, tg 384916]⟩,
    ⟨-5, -1, 0, 17,
      [[tg 480, tg 5745, tg 76296, tg 81561], [tg 51297, tg 56562, tg 127113, tg 132378], [tg 610, tg 5875, tg 76426, tg 81691], [tg 714, tg 5979, tg 76530, tg 81795]],
      [tg 152242, tg 157507, tg 228058, tg 233323]⟩,
    ⟨-5, -1, 1, 16,
      [[tg 493, tg 5758, tg 76309, tg 81574], [tg 597, tg 5862, tg 76413, tg 81678], [tg 623, tg 5888, tg 76439, tg 81704], [tg 727, tg 5992, tg 76543, tg 81808]],
      [tg 303887, tg 309152, tg 379703, tg 384968]⟩,
    ⟨-5, -1, 2, 15,
      [[tg 506, tg 5771, tg 76322, tg 81587], [tg 532, tg 5797, tg 76348, tg 81613], [tg 610, tg 5875, tg 76426, tg 81691], [tg 649, tg 5914, tg 76465, tg 81730], [tg 740, tg 6005, tg 76556, tg 81821]],
      [tg 152281, tg 157546, tg 228097, tg 233362]⟩,
    ⟨-5, -1, 3, 10,
      [[tg 519, tg 5784, tg 76335, tg 81600], [tg 545, tg 5810, tg 76361, tg 81626], [tg 662, tg 5927, tg 76478, tg 81743], [tg 474, tg 5739, tg 25752, tg 31017], [tg 753, tg 6018, tg 76569, tg 81834]],
      [tg 152106, tg 157371, tg 177384, tg 182649]⟩,
    ⟨-5, -1, 4, 14,
      [[tg 532, tg 5797, tg 76348, tg 81613], [tg 623, tg 5888, tg 76439, tg 81704], [tg 675, tg 5940, tg 76491, tg 81756], [tg 740, tg 6005, tg 76556, tg 81821], [tg 766, tg 6031, tg 76582, tg 81847]],
      [tg 152307, tg 157572, tg 228123, tg 233388]⟩,
    ⟨-5, -1, 5, 10,
      [[tg 545, tg 5810, tg 76361, tg 81626], [tg 636, tg 5901, tg 76452, tg 81717], [tg 688, tg 5953, tg 76504, tg 81769], [tg 753, tg 6018, tg 76569, tg 81834], [tg 779, tg 6044, tg 76595, tg 81860]],
      [tg 152385, tg 157650, tg 228201, tg 233466]⟩,
    ⟨-5, -1, 6, 13,
      [[tg 558, tg 5823, tg 76374, tg 81639], [tg 649, tg 5914, tg 76465, tg 81730], [tg 701, tg 5966, tg 76517, tg 81782], [tg 792, tg 6057, tg 76608, tg 81873]],
      [tg 152333, tg 157598, tg 228149, tg 233414]⟩,
    ⟨-5, -1, 7, 11,
      [[tg 571, tg 5836, tg 76387, tg 81652], [tg 662, tg 5927, tg 76478, tg 81743], [tg 701, tg 5966, tg 76517, tg 81782], [tg 805, tg 6070, tg 76621, tg 81886]],
      [tg 303926, tg 309191, tg 379742, tg 385007]⟩,
    ⟨-5, -1, 8, 12,
      [[tg 584, tg 5849, tg 76400, tg 81665], [tg 675, tg 5940, tg 76491, tg 81756], [tg 688, tg 5953, tg 76504, tg 81769], [tg 818, tg 6083, tg 76634, tg 81899]],
      [tg 303952, tg 309217, tg 379768, tg 385033]⟩,
    ⟨-4, -1, 0, 16,
      [[tg 597, tg 5862, tg 76413, tg 81678], [tg 51414, tg 56679, tg 127230, tg 132495], [tg 727, tg 5992, tg 76543, tg 81808], [tg 831, tg 6096, tg 76647, tg 81912]],
      [tg 152359, tg 157624, tg 228175, tg 233440]⟩,
    ⟨-4, -1, 1, 15,
      [[tg 610, tg 5875, tg 76426, tg 81691], [tg 714, tg 5979, tg 76530, tg 81795], [tg 740, tg 6005, tg 76556, tg 81821], [tg 844, tg 6109, tg 76660, tg 81925]],
      [tg 304004, tg 309269, tg 379820, tg 385085]⟩,
    ⟨-4, -1, 2, 14,
      [[tg 623, tg 5888, tg 76439, tg 81704], [tg 649, tg 5914, tg 76465, tg 81730], [tg 727, tg 5992, tg 76543, tg 81808], [tg 766, tg 6031, tg 76582, tg 81847], [tg 857, tg 6122, tg 76673, tg 81938]],
      [tg 152398, tg 157663, tg 228214, tg 233479]⟩,
    ⟨-4, -1, 3, 9,
      [[tg 636, tg 5901, tg 76452, tg 81717], [tg 662, tg 5927, tg 76478, tg 81743], [tg 779, tg 6044, tg 76595, tg 81860], [tg 357, tg 5622, tg 25869, tg 31134], [tg 870, tg 6135, tg 76686, tg 81951]],
      [tg 151989, tg 157254, tg 177501, tg 182766]⟩,
    ⟨-4, -1, 4, 13,
      [[tg 649, tg 5914, tg 76465, tg 81730], [tg 740, tg 6005, tg 76556, tg 81821], [tg 792, tg 6057, tg 76608, tg 81873], [tg 857, tg 6122, tg 76673, tg 81938], [tg 883, tg 6148, tg 76699, tg 81964]],
      [tg 152424, tg 157689, tg 228240, tg 233505]⟩,
    ⟨-4, -1, 5, 9,
      [[tg 662, tg 5927, tg 76478, tg 81743], [tg 753, tg 6018, tg 76569, tg 81834], [tg 805, tg 6070, tg 76621, tg 81886], [tg 870, tg 6135, tg 76686, tg 81951], [tg 896, tg 6161, tg 76712, tg 81977]],
      [tg 152502, tg 157767, tg 228318, tg 233583]⟩,
    ⟨-4, -1, 6, 12,
      [[tg 675, tg 5940, tg 76491, tg 81756], [tg 766, tg 6031, tg 76582, tg 81847], [tg 818, tg 6083, tg 76634, tg 81899], [tg 909, tg 6174, tg 76725, tg 81990]],
      [tg 152450, tg 157715, tg 228266, tg 233531]⟩,
    ⟨-4, -1, 7, 10,
      [[tg 688, tg 5953, tg 76504, tg 81769], [tg 779, tg 6044, tg 76595, tg 81860], [tg 818, tg 6083, tg 76634, tg 81899], [tg 922, tg 6187, tg 76738, tg 82003]],
      [tg 304043, tg 309308, tg 379859, tg 385124]⟩,
    ⟨-4, -1, 8, 11,
      [[tg 701, tg 5966, tg 76517, tg 81782], [tg 792, tg 6057, tg 76608, tg 81873], [tg 805, tg 6070, tg 76621, tg 81886], [tg 935, tg 6200, tg 76751, tg 82016]],
      [tg 304069, tg 309334, tg 379885, tg 385150]⟩,
    ⟨-3, -1, 0, 15,
      [[tg 714, tg 5979, tg 76530, tg 81795], [tg 51531, tg 56796, tg 127347, tg 132612], [tg 844, tg 6109, tg 76660, tg 81925], [tg 948, tg 6213, tg 76764, tg 82029]],
      [tg 152476, tg 157741, tg 228292, tg 233557]⟩,
    ⟨-3, -1, 1, 14,
      [[tg 727, tg 5992, tg 76543, tg 81808], [tg 831, tg 6096, tg 76647, tg 81912], [tg 857, tg 6122, tg 76673, tg 81938], [tg 961, tg 6226, tg 76777, tg 82042]],
      [tg 304121, tg 309386, tg 379937, tg 385202]⟩,
    ⟨-3, -1, 2, 13,
      [[tg 740, tg 6005, tg 76556, tg 81821], [tg 766, tg 6031, tg 76582, tg 81847], [tg 844, tg 6109, tg 76660, tg 81925], [tg 883, tg 6148, tg 76699, tg 81964], [tg 974, tg 6239, tg 76790, tg 82055]],
      [tg 152515, tg 157780, tg 228331, tg 233596]⟩,
    ⟨-3, -1, 3, 8,
      [[tg 753, tg 6018, tg 76569, tg 81834], [tg 779, tg 6044, tg 76595, tg 81860], [tg 896, tg 6161, tg 76712, tg 81977], [tg 240, tg 5505, tg 25986, tg 31251], [tg 987, tg 6252, tg 76803, tg 82068]],
      [tg 151872, tg 157137, tg 177618, tg 182883]⟩,
    ⟨-3, -1, 4, 12,
      [[tg 766, tg 6031, tg 76582, tg 81847], [tg 857, tg 6122, tg 76673, tg 81938], [tg 909, tg 6174, tg 76725, tg 81990], [tg 974, tg 6239, tg 76790, tg 82055], [tg 1000, tg 6265, tg 76816, tg 82081]],
      [tg 152541, tg 157806, tg 228357, tg 233622]⟩,
    ⟨-3, -1, 5, 8,
      [[tg 779, tg 6044, tg 76595, tg 81860], [tg 870, tg 6135, tg 76686, tg 81951], [tg 922, tg 6187, tg 76738, tg 82003], [tg 987, tg 6252, tg 76803, tg 82068], [tg 1013, tg 6278, tg 76829, tg 82094]],
      [tg 152619, tg 157884, tg 228435, tg 233700]⟩,
    ⟨-3, -1, 6, 11,
      [[tg 792, tg 6057, tg 76608, tg 81873], [tg 883, tg 6148, tg 76699, tg 81964], [tg 935, tg 6200, tg 76751, tg 82016], [tg 1026, tg 6291, tg 76842, tg 82107]],
      [tg 152567, tg 157832, tg 228383, tg 233648]⟩,
    ⟨-3, -1, 7, 9,
      [[tg 805, tg 6070, tg 76621, tg 81886], [tg 896, tg 6161, tg 76712, tg 81977], [tg 935, tg 6200, tg 76751, tg 82016], [tg 1039, tg 6304, tg 76855, tg 82120]],
      [tg 304160, tg 309425, tg 379976, tg 385241]⟩,
    ⟨-3, -1, 8, 10,
      [[tg 818, tg 6083, tg 76634, tg 81899], [tg 909, tg 6174, tg 76725, tg 81990], [tg 922, tg 6187, tg 76738, tg 82003], [tg 1052, tg 6317, tg 76868, tg 82133]],
      [tg 304186, tg 309451, tg 380002, tg 385267]⟩,
    ⟨-2, -1, 0, 14,
      [[tg 831, tg 6096, tg 76647, tg 81912], [tg 4252, tg 51648, tg 10570, tg 127464], [tg 961, tg 6226, tg 76777, tg 82042], [tg 1, tg 1065, tg 6319, tg 76881]],
      [tg 152593, tg 157858, tg 228409, tg 233674]⟩,
    ⟨-2, -1, 1, 13,
      [[tg 844, tg 6109, tg 76660, tg 81925], [tg 948, tg 6213, tg 76764, tg 82029], [tg 974, tg 6239, tg 76790, tg 82055], [tg 14, tg 1078, tg 6332, tg 76894]],
      [tg 304238, tg 309503, tg 380054, tg 385319]⟩,
    ⟨-2, -1, 2, 12,
      [[tg 857, tg 6122, tg 76673, tg 81938], [tg 883, tg 6148, tg 76699, tg 81964], [tg 961, tg 6226, tg 76777, tg 82042], [tg 1000, tg 6265, tg 76816, tg 82081], [tg 27, tg 1091, tg 6345, tg 76907]],
      [tg 152632, tg 157897, tg 228448, tg 233713]⟩,
    ⟨-2, -1, 3, 7,
      [[tg 870, tg 6135, tg 76686, tg 81951], [tg 896, tg 6161, tg 76712, tg 81977], [tg 1013, tg 6278, tg 76829, tg 82094], [tg 123, tg 5388, tg 26103, tg 31368], [tg 40, tg 1104, tg 6358, tg 76920]],
      [tg 151755, tg 157020, tg 177735, tg 183000]⟩,
    ⟨-2, -1, 4, 11,
      [[tg 883, tg 6148, tg 76699, tg 81964], [tg 974, tg 6239, tg 76790, tg 82055], [tg 1026, tg 6291, tg 76842, tg 82107], [tg 27, tg 1091, tg 6345, tg 76907], [tg 53, tg 1117, tg 6371, tg 76933]],
      [tg 152658, tg 157923, tg 228474, tg 233739]⟩,
    ⟨-2, -1, 5, 7,
      [[tg 896, tg 6161, tg 76712, tg 81977], [tg 987, tg 6252, tg 76803, tg 82068], [tg 1039, tg 6304, tg 76855, tg 82120], [tg 40, tg 1104, tg 6358, tg 76920], [tg 66, tg 1130, tg 6384, tg 76946]],
      [tg 151672, tg 152736, tg 157990, tg 228552]⟩,
    ⟨-2, -1, 6, 10,
      [[tg 909, tg 6174, tg 76725, tg 81990], [tg 1000, tg 6265, tg 76816, tg 82081], [tg 1052, tg 6317, tg 76868, tg 82133], [tg 79, tg 1143, tg 6397, tg 76959]],
      [tg 152684, tg 157949, tg 228500, tg 233765]⟩,
    ⟨-2, -1, 7, 8,
      [[tg 922, tg 6187, tg 76738, tg 82003], [tg 1013, tg 6278, tg 76829, tg 82094], [tg 1052, tg 6317, tg 76868, tg 82133], [tg 92, tg 1156, tg 6410, tg 76972]],
      [tg 304277, tg 309542, tg 380093, tg 385358]⟩,
    ⟨-2, -1, 8, 9,
      [[tg 935, tg 6200, tg 76751, tg 82016], [tg 1026, tg 6291, tg 76842, tg 82107], [tg 1039, tg 6304, tg 76855, tg 82120], [tg 105, tg 1169, tg 6423, tg 76985]],
      [tg 304303, tg 309568, tg 380119, tg 385384]⟩]⟩]

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

def cfg : GalCert.Cfg 9 := ⟨adj, (0, 0, 6), 9, regsData, certsData, 0, 6⟩

set_option maxHeartbeats 4000000 in
theorem hc : cfg.check = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem hV : cfg.vbound 22 = true := by decide +kernel

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
theorem hgfw : ∀ n < 22 + 2 * cfg.L, ((GalCert.csOfS [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] 0).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem hsmall : ∀ n < 11, GalCert.conv a [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] n = ([1, 3, 5, 4, 5, 4, 5, 4, 5, 3, 1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P312932

open PowerSeries OMA.S_oeis_a312932 in
theorem OMA.solution : type_of% @OMA.S_oeis_a312932.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    have h := P312932.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 11 - 1 = k + 10 by omega,
      show k + 11 - 9 = k + 2 by omega,
      show k + 11 - 10 = k + 1 by omega,
      P312932.ha (k + 11) (by omega),
      P312932.ha (k + 10) (by omega),
      P312932.ha (k + 2) (by omega),
      P312932.ha (k + 1) (by omega)]
    linarith
  · have hD : (X^10 - X^9 - X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (X^10 + 3*X^9 + 5*X^8 + 4*X^7 + 5*X^6 + 4*X^5 + 5*X^4 + 4*X^3 + 5*X^2 + 3*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 3, 5, 4, 5, 4, 5, 4, 5, 3, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from2 P312932.hc P312932.hV a P312932.ha _ _ 0 11 (by decide) (by decide) P312932.hgfw P312932.hsmall
