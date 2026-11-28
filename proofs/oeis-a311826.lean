import OMAStatements.S_oeis_a311826
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A311826.

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


namespace P311826
open OMA.S_oeis_a311826

/-- A packed target code (mixed radix). -/
def tg (n : ℕ) : GalCert.Tgt := ⟨n % 29, n / 29 % 32, n / 928 % 2, n / 1856 % 2, n / 3712 % 3, n / 11136 % 2, n / 22272 % 2, n / 44544 % 3, n / 133632⟩

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 16) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 5,
      [[tg 99], [tg 128], [tg 205], [tg 29]],
      [tg 267363]⟩,
    ⟨0, 0, 1, 4,
      [[tg 234], [tg 0], [tg 58], [tg 116]],
      [tg 133690]⟩,
    ⟨0, 0, 2, 3,
      [[tg 99], [tg 29], [tg 145], [tg 174]],
      [tg 133806]⟩,
    ⟨0, 0, 3, 4,
      [[tg 145], [tg 261], [tg 6], [tg 64]],
      [tg 133777]⟩,
    ⟨0, 0, 4, 4,
      [[tg 321], [tg 29], [tg 145], [tg 6]],
      [tg 267409]⟩,
    ⟨0, 0, 5, 3,
      [[tg 58], [tg 87], [tg 116], [tg 290]],
      [tg 290]⟩,
    ⟨0, 0, 6, 2,
      [[tg 273], [tg 58], [tg 290], [tg 377]],
      [tg 377]⟩,
    ⟨0, 0, 7, 1,
      [[tg 331], [tg 232], [tg 348], [tg 8]],
      [tg 267612]⟩,
    ⟨0, 0, 8, 2,
      [[tg 203], [tg 319], [tg 435], [tg 37]],
      [tg 133835]⟩,
    ⟨0, 0, 9, 3,
      [[tg 87], [tg 290], [tg 406], [tg 180]],
      [tg 267554]⟩,
    ⟨0, 0, 10, 2,
      [[tg 145], [tg 174], [tg 261], [tg 377], [tg 406]],
      [tg 134009]⟩,
    ⟨0, 0, 11, 3,
      [[tg 232], [tg 435], [tg 124], [tg 209], [tg 354]],
      [tg 133864]⟩,
    ⟨0, 0, 12, 0,
      [[tg 331], [tg 447], [tg 203], [tg 377]],
      [tg 0]⟩,
    ⟨0, 0, 13, 1,
      [[tg 174], [tg 290], [tg 348], [tg 406]],
      [tg 401244]⟩,
    ⟨0, 0, 14, 2,
      [[tg 261], [tg 290], [tg 377], [tg 435]],
      [tg 401273]⟩,
    ⟨0, 0, 15, 3,
      [[tg 232], [tg 319], [tg 406], [tg 354]],
      [tg 267496]⟩]⟩,
  ⟨1, 0, -1, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, -1, 2)], 0, -1, 2, 1, 0, 0, 0, 0,
   [⟨0, -2, 0, 17,
      [[tg 3827, tg 8467], [tg 3856, tg 8496], [tg 3916, tg 8556], [tg 30, tg 4670]],
      [tg 271091, tg 275731]⟩,
    ⟨0, -2, 1, 17,
      [[tg 3945, tg 8585], [tg 1, tg 4641], [tg 59, tg 4699], [tg 117, tg 4757]],
      [tg 133691, tg 138331]⟩,
    ⟨0, -2, 2, 16,
      [[tg 3827, tg 8467], [tg 30, tg 4670], [tg 146, tg 4786], [tg 175, tg 4815]],
      [tg 146, tg 4786]⟩,
    ⟨0, -2, 3, 15,
      [[tg 146, tg 4786], [tg 262, tg 4902], [tg 16, tg 942], [tg 74, tg 1000]],
      [tg 262, tg 4902]⟩,
    ⟨0, -2, 4, 16,
      [[tg 4032, tg 8672], [tg 30, tg 4670], [tg 146, tg 4786], [tg 16, tg 942]],
      [tg 267410, tg 272050]⟩,
    ⟨0, -2, 5, 15,
      [[tg 59, tg 4699], [tg 88, tg 4728], [tg 117, tg 4757], [tg 291, tg 4931]],
      [tg 291, tg 4931]⟩,
    ⟨0, -2, 6, 15,
      [[tg 4001, tg 8641], [tg 59, tg 4699], [tg 291, tg 4931], [tg 378, tg 5018]],
      [tg 133923, tg 138563]⟩,
    ⟨0, -2, 7, 12,
      [[tg 4059, tg 8699], [tg 233, tg 4873], [tg 349, tg 4989], [tg 2, tg 929]],
      [tg 267266, tg 268193]⟩,
    ⟨0, -2, 8, 12,
      [[tg 204, tg 4844], [tg 320, tg 4960], [tg 436, tg 5076], [tg 31, tg 958]],
      [tg 320, tg 4960]⟩,
    ⟨0, -2, 9, 14,
      [[tg 88, tg 4728], [tg 291, tg 4931], [tg 407, tg 5047], [tg 190, tg 1116]],
      [tg 407, tg 5047]⟩,
    ⟨0, -2, 10, 14,
      [[tg 146, tg 4786], [tg 175, tg 4815], [tg 262, tg 4902], [tg 378, tg 5018], [tg 407, tg 5047]],
      [tg 134039, tg 138679]⟩,
    ⟨0, -2, 11, 11,
      [[tg 233, tg 4873], [tg 436, tg 5076], [tg 118, tg 1045], [tg 219, tg 1145], [tg 364, tg 1290]],
      [tg 118, tg 1045]⟩,
    ⟨0, -2, 12, 13,
      [[tg 4059, tg 8699], [tg 4175, tg 8815], [tg 204, tg 4844], [tg 378, tg 5018]],
      [tg 538587, tg 543227]⟩,
    ⟨0, -2, 13, 14,
      [[tg 175, tg 4815], [tg 291, tg 4931], [tg 349, tg 4989], [tg 407, tg 5047]],
      [tg 401245, tg 405885]⟩,
    ⟨0, -2, 14, 13,
      [[tg 262, tg 4902], [tg 291, tg 4931], [tg 378, tg 5018], [tg 436, tg 5076]],
      [tg 267700, tg 272340]⟩,
    ⟨0, -2, 15, 12,
      [[tg 233, tg 4873], [tg 320, tg 4960], [tg 407, tg 5047], [tg 364, tg 1290]],
      [tg 133952, tg 138592]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, -1, 1), (0, 1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, -1, 0, 11,
      [[tg 115], [tg 144], [tg 204], [tg 31]],
      [tg 267379]⟩,
    ⟨0, -1, 1, 11,
      [[tg 233], [tg 2], [tg 60], [tg 118]],
      [tg 133692]⟩,
    ⟨0, -1, 2, 10,
      [[tg 115], [tg 31], [tg 147], [tg 176]],
      [tg 147]⟩,
    ⟨0, -1, 3, 9,
      [[tg 147], [tg 263], [tg 4], [tg 62]],
      [tg 263]⟩,
    ⟨0, -1, 4, 10,
      [[tg 320], [tg 31], [tg 147], [tg 4]],
      [tg 267411]⟩,
    ⟨0, -1, 5, 9,
      [[tg 60], [tg 89], [tg 118], [tg 292]],
      [tg 292]⟩,
    ⟨0, -1, 6, 9,
      [[tg 289], [tg 60], [tg 292], [tg 379]],
      [tg 133924]⟩,
    ⟨0, -1, 7, 6,
      [[tg 347], [tg 234], [tg 350], [tg 0]],
      [tg 234]⟩,
    ⟨0, -1, 8, 5,
      [[tg 205], [tg 321], [tg 437], [tg 29]],
      [tg 29]⟩,
    ⟨0, -1, 9, 8,
      [[tg 89], [tg 292], [tg 408], [tg 178]],
      [tg 408]⟩,
    ⟨0, -1, 10, 8,
      [[tg 147], [tg 176], [tg 263], [tg 379], [tg 408]],
      [tg 134040]⟩,
    ⟨0, -1, 11, 5,
      [[tg 234], [tg 437], [tg 116], [tg 207], [tg 352]],
      [tg 116]⟩,
    ⟨0, -1, 12, 7,
      [[tg 347], [tg 463], [tg 205], [tg 379]],
      [tg 534875]⟩,
    ⟨0, -1, 13, 8,
      [[tg 176], [tg 292], [tg 350], [tg 408]],
      [tg 401246]⟩,
    ⟨0, -1, 14, 7,
      [[tg 263], [tg 292], [tg 379], [tg 437]],
      [tg 267701]⟩,
    ⟨0, -1, 15, 6,
      [[tg 234], [tg 321], [tg 408], [tg 352]],
      [tg 267498]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 4)], 1, -1, 4, 2, 0, 0, 0, 0,
   [⟨2, -2, 0, 16,
      [[tg 103, tg 1030], [tg 132, tg 1059], [tg 218, tg 4858], [tg 32, tg 4672]],
      [tg 267367, tg 268294]⟩,
    ⟨2, -2, 1, 16,
      [[tg 247, tg 4887], [tg 3, tg 4643], [tg 61, tg 4701], [tg 119, tg 4759]],
      [tg 133693, tg 138333]⟩,
    ⟨2, -2, 2, 15,
      [[tg 103, tg 1030], [tg 32, tg 4672], [tg 148, tg 4788], [tg 177, tg 4817]],
      [tg 133809, tg 138449]⟩,
    ⟨2, -2, 3, 16,
      [[tg 148, tg 4788], [tg 264, tg 4904], [tg 3730, tg 8370], [tg 3788, tg 8428]],
      [tg 133780, tg 138420]⟩,
    ⟨2, -2, 4, 16,
      [[tg 334, tg 4974], [tg 32, tg 4672], [tg 148, tg 4788], [tg 3730, tg 8370]],
      [tg 267412, tg 272052]⟩,
    ⟨2, -2, 5, 15,
      [[tg 61, tg 4701], [tg 90, tg 4730], [tg 119, tg 4759], [tg 293, tg 4933]],
      [tg 293, tg 4933]⟩,
    ⟨2, -2, 6, 14,
      [[tg 277, tg 1204], [tg 61, tg 4701], [tg 293, tg 4933], [tg 380, tg 5020]],
      [tg 380, tg 5020]⟩,
    ⟨2, -2, 7, 12,
      [[tg 335, tg 1262], [tg 235, tg 4875], [tg 351, tg 4991], [tg 18, tg 4658]],
      [tg 401231, tg 402158]⟩,
    ⟨2, -2, 8, 13,
      [[tg 206, tg 4846], [tg 322, tg 4962], [tg 438, tg 5078], [tg 47, tg 4687]],
      [tg 133838, tg 138478]⟩,
    ⟨2, -2, 9, 15,
      [[tg 90, tg 4730], [tg 293, tg 4933], [tg 409, tg 5049], [tg 3904, tg 8544]],
      [tg 267557, tg 272197]⟩,
    ⟨2, -2, 10, 14,
      [[tg 148, tg 4788], [tg 177, tg 4817], [tg 264, tg 4904], [tg 380, tg 5020], [tg 409, tg 5049]],
      [tg 134012, tg 138652]⟩,
    ⟨2, -2, 11, 14,
      [[tg 235, tg 4875], [tg 438, tg 5078], [tg 134, tg 4774], [tg 3933, tg 8573], [tg 4078, tg 8718]],
      [tg 133867, tg 138507]⟩,
    ⟨2, -2, 12, 12,
      [[tg 335, tg 1262], [tg 451, tg 1378], [tg 206, tg 4846], [tg 380, tg 5020]],
      [tg 534863, tg 535790]⟩,
    ⟨2, -2, 13, 13,
      [[tg 177, tg 4817], [tg 293, tg 4933], [tg 351, tg 4991], [tg 409, tg 5049]],
      [tg 401247, tg 405887]⟩,
    ⟨2, -2, 14, 14,
      [[tg 264, tg 4904], [tg 293, tg 4933], [tg 380, tg 5020], [tg 438, tg 5078]],
      [tg 401276, tg 405916]⟩,
    ⟨2, -2, 15, 14,
      [[tg 235, tg 4875], [tg 322, tg 4962], [tg 409, tg 5049], [tg 4078, tg 8718]],
      [tg 267499, tg 272139]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 2), (-1, 1, -2)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, -1, 0, 10,
      [[tg 89], [tg 118], [tg 219], [tg 33]],
      [tg 267353]⟩,
    ⟨1, -1, 1, 10,
      [[tg 248], [tg 4], [tg 62], [tg 120]],
      [tg 133694]⟩,
    ⟨1, -1, 2, 9,
      [[tg 89], [tg 33], [tg 149], [tg 178]],
      [tg 133810]⟩,
    ⟨1, -1, 3, 10,
      [[tg 149], [tg 265], [tg 18], [tg 76]],
      [tg 133781]⟩,
    ⟨1, -1, 4, 10,
      [[tg 335], [tg 33], [tg 149], [tg 18]],
      [tg 267413]⟩,
    ⟨1, -1, 5, 9,
      [[tg 62], [tg 91], [tg 120], [tg 294]],
      [tg 294]⟩,
    ⟨1, -1, 6, 8,
      [[tg 263], [tg 62], [tg 294], [tg 381]],
      [tg 381]⟩,
    ⟨1, -1, 7, 6,
      [[tg 321], [tg 236], [tg 352], [tg 6]],
      [tg 401217]⟩,
    ⟨1, -1, 8, 7,
      [[tg 207], [tg 323], [tg 439], [tg 35]],
      [tg 133839]⟩,
    ⟨1, -1, 9, 9,
      [[tg 91], [tg 294], [tg 410], [tg 192]],
      [tg 267558]⟩,
    ⟨1, -1, 10, 8,
      [[tg 149], [tg 178], [tg 265], [tg 381], [tg 410]],
      [tg 134013]⟩,
    ⟨1, -1, 11, 8,
      [[tg 236], [tg 439], [tg 122], [tg 221], [tg 366]],
      [tg 133868]⟩,
    ⟨1, -1, 12, 6,
      [[tg 321], [tg 437], [tg 207], [tg 381]],
      [tg 534849]⟩,
    ⟨1, -1, 13, 7,
      [[tg 178], [tg 294], [tg 352], [tg 410]],
      [tg 401248]⟩,
    ⟨1, -1, 14, 8,
      [[tg 265], [tg 294], [tg 381], [tg 439]],
      [tg 401277]⟩,
    ⟨1, -1, 15, 8,
      [[tg 236], [tg 323], [tg 410], [tg 366]],
      [tg 267500]⟩]⟩,
  ⟨1, 2, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 3)], 1, 0, 3, 2, 0, 0, 0, 0,
   [⟨3, 0, 0, 11,
      [[tg 557, tg 1484], [tg 586, tg 1513], [tg 220, tg 55900], [tg 34, tg 4674]],
      [tg 267821, tg 268748]⟩,
    ⟨3, 0, 1, 12,
      [[tg 249, tg 55929], [tg 5, tg 4645], [tg 63, tg 4703], [tg 121, tg 4761]],
      [tg 400901, tg 405541]⟩,
    ⟨3, 0, 2, 11,
      [[tg 557, tg 1484], [tg 34, tg 4674], [tg 150, tg 4790], [tg 179, tg 4819]],
      [tg 401453, tg 402380]⟩,
    ⟨3, 0, 3, 13,
      [[tg 150, tg 4790], [tg 266, tg 4906], [tg 469, tg 5109], [tg 527, tg 5167]],
      [tg 133782, tg 138422]⟩,
    ⟨3, 0, 4, 13,
      [[tg 336, tg 56016], [tg 34, tg 4674], [tg 150, tg 4790], [tg 469, tg 5109]],
      [tg 400930, tg 405570]⟩,
    ⟨3, 0, 5, 12,
      [[tg 63, tg 4703], [tg 92, tg 4732], [tg 121, tg 4761], [tg 295, tg 4935]],
      [tg 267327, tg 271967]⟩,
    ⟨3, 0, 6, 10,
      [[tg 731, tg 1658], [tg 63, tg 4703], [tg 295, tg 4935], [tg 382, tg 5022]],
      [tg 401627, tg 402554]⟩,
    ⟨3, 0, 7, 10,
      [[tg 789, tg 1716], [tg 237, tg 4877], [tg 353, tg 4993], [tg 483, tg 5123]],
      [tg 401685, tg 402612]⟩,
    ⟨3, 0, 8, 11,
      [[tg 208, tg 4848], [tg 324, tg 4964], [tg 440, tg 5080], [tg 512, tg 5152]],
      [tg 133840, tg 138480]⟩,
    ⟨3, 0, 9, 12,
      [[tg 92, tg 4732], [tg 295, tg 4935], [tg 411, tg 5051], [tg 643, tg 5283]],
      [tg 267559, tg 272199]⟩,
    ⟨3, 0, 10, 11,
      [[tg 150, tg 4790], [tg 179, tg 4819], [tg 266, tg 4906], [tg 382, tg 5022], [tg 411, tg 5051]],
      [tg 267443, tg 272083]⟩,
    ⟨3, 0, 11, 12,
      [[tg 237, tg 4877], [tg 440, tg 5080], [tg 599, tg 5239], [tg 672, tg 5312], [tg 817, tg 5457]],
      [tg 133869, tg 138509]⟩,
    ⟨3, 0, 12, 10,
      [[tg 789, tg 1716], [tg 905, tg 1832], [tg 208, tg 4848], [tg 382, tg 5022]],
      [tg 535317, tg 536244]⟩,
    ⟨3, 0, 13, 11,
      [[tg 179, tg 4819], [tg 295, tg 4935], [tg 353, tg 4993], [tg 411, tg 5051]],
      [tg 401075, tg 405715]⟩,
    ⟨3, 0, 14, 12,
      [[tg 266, tg 4906], [tg 295, tg 4935], [tg 382, tg 5022], [tg 440, tg 5080]],
      [tg 534823, tg 539463]⟩,
    ⟨3, 0, 15, 12,
      [[tg 237, tg 4877], [tg 324, tg 4964], [tg 411, tg 5051], [tg 817, tg 5457]],
      [tg 267501, tg 272141]⟩,
    ⟨4, 0, 0, 14,
      [[tg 92, tg 4732], [tg 121, tg 4761], [tg 684, tg 56364], [tg 498, tg 5138]],
      [tg 267356, tg 271996]⟩,
    ⟨4, 0, 1, 15,
      [[tg 713, tg 56393], [tg 469, tg 5109], [tg 527, tg 5167], [tg 585, tg 5225]],
      [tg 401365, tg 406005]⟩,
    ⟨4, 0, 2, 14,
      [[tg 92, tg 4732], [tg 498, tg 5138], [tg 614, tg 5254], [tg 643, tg 5283]],
      [tg 400988, tg 405628]⟩,
    ⟨4, 0, 3, 16,
      [[tg 614, tg 5254], [tg 730, tg 5370], [tg 3717, tg 8357], [tg 3775, tg 8415]],
      [tg 134246, tg 138886]⟩,
    ⟨4, 0, 4, 16,
      [[tg 800, tg 56480], [tg 498, tg 5138], [tg 614, tg 5254], [tg 3717, tg 8357]],
      [tg 401394, tg 406034]⟩,
    ⟨4, 0, 5, 15,
      [[tg 527, tg 5167], [tg 556, tg 5196], [tg 585, tg 5225], [tg 759, tg 5399]],
      [tg 267791, tg 272431]⟩,
    ⟨4, 0, 6, 13,
      [[tg 266, tg 4906], [tg 527, tg 5167], [tg 759, tg 5399], [tg 846, tg 5486]],
      [tg 401162, tg 405802]⟩,
    ⟨4, 0, 7, 13,
      [[tg 324, tg 4964], [tg 701, tg 5341], [tg 817, tg 5457], [tg 3731, tg 8371]],
      [tg 401220, tg 405860]⟩,
    ⟨4, 0, 8, 14,
      [[tg 672, tg 5312], [tg 788, tg 5428], [tg 904, tg 5544], [tg 3760, tg 8400]],
      [tg 134304, tg 138944]⟩,
    ⟨4, 0, 9, 15,
      [[tg 556, tg 5196], [tg 759, tg 5399], [tg 875, tg 5515], [tg 3891, tg 8531]],
      [tg 268023, tg 272663]⟩,
    ⟨4, 0, 10, 14,
      [[tg 614, tg 5254], [tg 643, tg 5283], [tg 730, tg 5370], [tg 846, tg 5486], [tg 875, tg 5515]],
      [tg 267907, tg 272547]⟩,
    ⟨4, 0, 11, 15,
      [[tg 701, tg 5341], [tg 904, tg 5544], [tg 3847, tg 8487], [tg 3920, tg 8560], [tg 4065, tg 8705]],
      [tg 134333, tg 138973]⟩,
    ⟨4, 0, 12, 13,
      [[tg 324, tg 4964], [tg 440, tg 5080], [tg 672, tg 5312], [tg 846, tg 5486]],
      [tg 534852, tg 539492]⟩,
    ⟨4, 0, 13, 14,
      [[tg 643, tg 5283], [tg 759, tg 5399], [tg 817, tg 5457], [tg 875, tg 5515]],
      [tg 401539, tg 406179]⟩,
    ⟨4, 0, 14, 15,
      [[tg 730, tg 5370], [tg 759, tg 5399], [tg 846, tg 5486], [tg 904, tg 5544]],
      [tg 535287, tg 539927]⟩,
    ⟨4, 0, 15, 15,
      [[tg 701, tg 5341], [tg 788, tg 5428], [tg 875, tg 5515], [tg 4065, tg 8705]],
      [tg 267965, tg 272605]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 1), (-1, 0, -2)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, 0, 0, 5,
      [[tg 87], [tg 116], [tg 207], [tg 35]],
      [tg 267351]⟩,
    ⟨1, 0, 1, 6,
      [[tg 236], [tg 6], [tg 64], [tg 122]],
      [tg 400902]⟩,
    ⟨1, 0, 2, 5,
      [[tg 87], [tg 35], [tg 151], [tg 180]],
      [tg 400983]⟩,
    ⟨1, 0, 3, 7,
      [[tg 151], [tg 267], [tg 470], [tg 528]],
      [tg 133783]⟩,
    ⟨1, 0, 4, 7,
      [[tg 323], [tg 35], [tg 151], [tg 470]],
      [tg 400931]⟩,
    ⟨1, 0, 5, 6,
      [[tg 64], [tg 93], [tg 122], [tg 296]],
      [tg 267328]⟩,
    ⟨1, 0, 6, 4,
      [[tg 261], [tg 64], [tg 296], [tg 383]],
      [tg 401157]⟩,
    ⟨1, 0, 7, 4,
      [[tg 319], [tg 238], [tg 354], [tg 20]],
      [tg 401215]⟩,
    ⟨1, 0, 8, 5,
      [[tg 209], [tg 325], [tg 441], [tg 49]],
      [tg 133841]⟩,
    ⟨1, 0, 9, 6,
      [[tg 93], [tg 296], [tg 412], [tg 644]],
      [tg 267560]⟩,
    ⟨1, 0, 10, 5,
      [[tg 151], [tg 180], [tg 267], [tg 383], [tg 412]],
      [tg 267444]⟩,
    ⟨1, 0, 11, 6,
      [[tg 238], [tg 441], [tg 136], [tg 673], [tg 818]],
      [tg 133870]⟩,
    ⟨1, 0, 12, 4,
      [[tg 319], [tg 435], [tg 209], [tg 383]],
      [tg 534847]⟩,
    ⟨1, 0, 13, 5,
      [[tg 180], [tg 296], [tg 354], [tg 412]],
      [tg 401076]⟩,
    ⟨1, 0, 14, 6,
      [[tg 267], [tg 296], [tg 383], [tg 441]],
      [tg 534824]⟩,
    ⟨1, 0, 15, 6,
      [[tg 238], [tg 325], [tg 412], [tg 818]],
      [tg 267502]⟩,
    ⟨2, 0, 0, 8,
      [[tg 93], [tg 122], [tg 221], [tg 499]],
      [tg 267357]⟩,
    ⟨2, 0, 1, 9,
      [[tg 250], [tg 470], [tg 528], [tg 586]],
      [tg 401366]⟩,
    ⟨2, 0, 2, 8,
      [[tg 93], [tg 499], [tg 615], [tg 644]],
      [tg 400989]⟩,
    ⟨2, 0, 3, 10,
      [[tg 615], [tg 731], [tg 5], [tg 63]],
      [tg 134247]⟩,
    ⟨2, 0, 4, 10,
      [[tg 337], [tg 499], [tg 615], [tg 5]],
      [tg 401395]⟩,
    ⟨2, 0, 5, 9,
      [[tg 528], [tg 557], [tg 586], [tg 760]],
      [tg 267792]⟩,
    ⟨2, 0, 6, 7,
      [[tg 267], [tg 528], [tg 760], [tg 847]],
      [tg 401163]⟩,
    ⟨2, 0, 7, 7,
      [[tg 325], [tg 702], [tg 818], [tg 19]],
      [tg 401221]⟩,
    ⟨2, 0, 8, 8,
      [[tg 673], [tg 789], [tg 905], [tg 48]],
      [tg 134305]⟩,
    ⟨2, 0, 9, 9,
      [[tg 557], [tg 760], [tg 876], [tg 179]],
      [tg 268024]⟩,
    ⟨2, 0, 10, 8,
      [[tg 615], [tg 644], [tg 731], [tg 847], [tg 876]],
      [tg 267908]⟩,
    ⟨2, 0, 11, 9,
      [[tg 702], [tg 905], [tg 135], [tg 208], [tg 353]],
      [tg 134334]⟩,
    ⟨2, 0, 12, 7,
      [[tg 325], [tg 441], [tg 673], [tg 847]],
      [tg 534853]⟩,
    ⟨2, 0, 13, 8,
      [[tg 644], [tg 760], [tg 818], [tg 876]],
      [tg 401540]⟩,
    ⟨2, 0, 14, 9,
      [[tg 731], [tg 760], [tg 847], [tg 905]],
      [tg 535288]⟩,
    ⟨2, 0, 15, 9,
      [[tg 702], [tg 789], [tg 876], [tg 353]],
      [tg 267966]⟩]⟩,
  ⟨1, 0, 1, 0, 0, [(-1, 0, 0), (1, 0, 0), (0, 1, 2)], 0, 1, 2, 1, 0, 0, 0, 0,
   [⟨0, 2, 0, 9,
      [[tg 111, tg 1037], [tg 140, tg 1066], [tg 211, tg 1138], [tg 36, tg 4676]],
      [tg 401036, tg 401962]⟩,
    ⟨0, 2, 1, 10,
      [[tg 240, tg 1167], [tg 7, tg 4647], [tg 65, tg 4705], [tg 123, tg 4763]],
      [tg 401136, tg 402063]⟩,
    ⟨0, 2, 2, 11,
      [[tg 111, tg 1037], [tg 36, tg 4676], [tg 152, tg 4792], [tg 181, tg 4821]],
      [tg 401007, tg 401933]⟩,
    ⟨0, 2, 3, 12,
      [[tg 152, tg 4792], [tg 268, tg 4908], [tg 3732, tg 8372], [tg 3790, tg 8430]],
      [tg 133784, tg 138424]⟩,
    ⟨0, 2, 4, 10,
      [[tg 327, tg 1254], [tg 36, tg 4676], [tg 152, tg 4792], [tg 3732, tg 8372]],
      [tg 267591, tg 268518]⟩,
    ⟨0, 2, 5, 11,
      [[tg 65, tg 4705], [tg 94, tg 4734], [tg 123, tg 4763], [tg 297, tg 4937]],
      [tg 267387, tg 272027]⟩,
    ⟨0, 2, 6, 12,
      [[tg 285, tg 1211], [tg 65, tg 4705], [tg 297, tg 4937], [tg 384, tg 5024]],
      [tg 401181, tg 402107]⟩,
    ⟨0, 2, 7, 14,
      [[tg 343, tg 1269], [tg 239, tg 4879], [tg 355, tg 4995], [tg 3719, tg 8359]],
      [tg 401239, tg 402165]⟩,
    ⟨0, 2, 8, 15,
      [[tg 210, tg 4850], [tg 326, tg 4966], [tg 442, tg 5082], [tg 3748, tg 8388]],
      [tg 133842, tg 138482]⟩,
    ⟨0, 2, 9, 13,
      [[tg 94, tg 4734], [tg 297, tg 4937], [tg 413, tg 5053], [tg 3906, tg 8546]],
      [tg 133726, tg 138366]⟩,
    ⟨0, 2, 10, 12,
      [[tg 152, tg 4792], [tg 181, tg 4821], [tg 268, tg 4908], [tg 384, tg 5024], [tg 413, tg 5053]],
      [tg 401048, tg 405688]⟩,
    ⟨0, 2, 11, 15,
      [[tg 239, tg 4879], [tg 442, tg 5082], [tg 3835, tg 8475], [tg 3935, tg 8575], [tg 4080, tg 8720]],
      [tg 134074, tg 138714]⟩,
    ⟨0, 2, 12, 13,
      [[tg 343, tg 1269], [tg 459, tg 1385], [tg 210, tg 4850], [tg 384, tg 5024]],
      [tg 401355, tg 402281]⟩,
    ⟨0, 2, 13, 13,
      [[tg 181, tg 4821], [tg 297, tg 4937], [tg 355, tg 4995], [tg 413, tg 5053]],
      [tg 401077, tg 405717]⟩,
    ⟨0, 2, 14, 13,
      [[tg 268, tg 4908], [tg 297, tg 4937], [tg 384, tg 5024], [tg 442, tg 5082]],
      [tg 534825, tg 539465]⟩,
    ⟨0, 2, 15, 14,
      [[tg 239, tg 4879], [tg 326, tg 4966], [tg 413, tg 5053], [tg 4080, tg 8720]],
      [tg 401309, tg 405949]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, 0, 0), (1, 0, 0), (0, 1, 1), (0, -1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 1, 0, 2,
      [[tg 97], [tg 126], [tg 203], [tg 37]],
      [tg 401099]⟩,
    ⟨0, 1, 1, 3,
      [[tg 232], [tg 8], [tg 66], [tg 124]],
      [tg 401128]⟩,
    ⟨0, 1, 2, 4,
      [[tg 97], [tg 37], [tg 153], [tg 182]],
      [tg 400993]⟩,
    ⟨0, 1, 3, 6,
      [[tg 153], [tg 269], [tg 20], [tg 78]],
      [tg 133785]⟩,
    ⟨0, 1, 4, 4,
      [[tg 319], [tg 37], [tg 153], [tg 20]],
      [tg 267583]⟩,
    ⟨0, 1, 5, 5,
      [[tg 66], [tg 95], [tg 124], [tg 298]],
      [tg 267330]⟩,
    ⟨0, 1, 6, 5,
      [[tg 271], [tg 66], [tg 298], [tg 385]],
      [tg 401167]⟩,
    ⟨0, 1, 7, 8,
      [[tg 329], [tg 240], [tg 356], [tg 7]],
      [tg 401225]⟩,
    ⟨0, 1, 8, 9,
      [[tg 211], [tg 327], [tg 443], [tg 36]],
      [tg 133843]⟩,
    ⟨0, 1, 9, 7,
      [[tg 95], [tg 298], [tg 414], [tg 194]],
      [tg 133727]⟩,
    ⟨0, 1, 10, 6,
      [[tg 153], [tg 182], [tg 269], [tg 385], [tg 414]],
      [tg 401049]⟩,
    ⟨0, 1, 11, 9,
      [[tg 240], [tg 443], [tg 123], [tg 223], [tg 368]],
      [tg 134075]⟩,
    ⟨0, 1, 12, 7,
      [[tg 329], [tg 445], [tg 211], [tg 385]],
      [tg 401341]⟩,
    ⟨0, 1, 13, 6,
      [[tg 182], [tg 298], [tg 356], [tg 414]],
      [tg 401078]⟩,
    ⟨0, 1, 14, 7,
      [[tg 269], [tg 298], [tg 385], [tg 443]],
      [tg 534826]⟩,
    ⟨0, 1, 15, 8,
      [[tg 240], [tg 327], [tg 414], [tg 368]],
      [tg 401310]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 4)], -1, 1, 4, 2, 0, 0, 0, 0,
   [⟨-2, 2, 0, 10,
      [[tg 3825, tg 8465], [tg 3854, tg 8494], [tg 229, tg 4869], [tg 38, tg 4678]],
      [tg 401125, tg 405765]⟩,
    ⟨-2, 2, 1, 9,
      [[tg 258, tg 4898], [tg 9, tg 4649], [tg 67, tg 4707], [tg 125, tg 4765]],
      [tg 401154, tg 405794]⟩,
    ⟨-2, 2, 2, 10,
      [[tg 3825, tg 8465], [tg 38, tg 4678], [tg 154, tg 4794], [tg 183, tg 4823]],
      [tg 267302, tg 271942]⟩,
    ⟨-2, 2, 3, 9,
      [[tg 154, tg 4794], [tg 270, tg 4910], [tg 24, tg 951], [tg 82, tg 1009]],
      [tg 24, tg 951]⟩,
    ⟨-2, 2, 4, 8,
      [[tg 345, tg 4985], [tg 38, tg 4678], [tg 154, tg 4794], [tg 24, tg 951]],
      [tg 267609, tg 272249]⟩,
    ⟨-2, 2, 5, 9,
      [[tg 67, tg 4707], [tg 96, tg 4736], [tg 125, tg 4765], [tg 299, tg 4939]],
      [tg 267389, tg 272029]⟩,
    ⟨-2, 2, 6, 11,
      [[tg 3999, tg 8639], [tg 67, tg 4707], [tg 299, tg 4939], [tg 386, tg 5026]],
      [tg 400963, tg 405603]⟩,
    ⟨-2, 2, 7, 13,
      [[tg 4057, tg 8697], [tg 241, tg 4881], [tg 357, tg 4997], [tg 23, tg 4663]],
      [tg 267621, tg 272261]⟩,
    ⟨-2, 2, 8, 13,
      [[tg 212, tg 4852], [tg 328, tg 4968], [tg 444, tg 5084], [tg 52, tg 4692]],
      [tg 444, tg 5084]⟩,
    ⟨-2, 2, 9, 10,
      [[tg 96, tg 4736], [tg 299, tg 4939], [tg 415, tg 5055], [tg 198, tg 1125]],
      [tg 133728, tg 138368]⟩,
    ⟨-2, 2, 10, 10,
      [[tg 154, tg 4794], [tg 183, tg 4823], [tg 270, tg 4910], [tg 386, tg 5026], [tg 415, tg 5055]],
      [tg 401050, tg 405690]⟩,
    ⟨-2, 2, 11, 13,
      [[tg 241, tg 4881], [tg 444, tg 5084], [tg 139, tg 4779], [tg 227, tg 1154], [tg 372, tg 1299]],
      [tg 134076, tg 138716]⟩,
    ⟨-2, 2, 12, 12,
      [[tg 4057, tg 8697], [tg 4173, tg 8813], [tg 212, tg 4852], [tg 386, tg 5026]],
      [tg 267650, tg 272290]⟩,
    ⟨-2, 2, 13, 11,
      [[tg 183, tg 4823], [tg 299, tg 4939], [tg 357, tg 4997], [tg 415, tg 5055]],
      [tg 401195, tg 405835]⟩,
    ⟨-2, 2, 14, 11,
      [[tg 270, tg 4910], [tg 299, tg 4939], [tg 386, tg 5026], [tg 444, tg 5084]],
      [tg 267534, tg 272174]⟩,
    ⟨-2, 2, 15, 12,
      [[tg 241, tg 4881], [tg 328, tg 4968], [tg 415, tg 5055], [tg 372, tg 1299]],
      [tg 401311, tg 405951]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 2), (1, -1, -2)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, 1, 0, 4,
      [[tg 113], [tg 142], [tg 215], [tg 39]],
      [tg 401111]⟩,
    ⟨-1, 1, 1, 3,
      [[tg 244], [tg 10], [tg 68], [tg 126]],
      [tg 401140]⟩,
    ⟨-1, 1, 2, 4,
      [[tg 113], [tg 39], [tg 155], [tg 184]],
      [tg 267303]⟩,
    ⟨-1, 1, 3, 3,
      [[tg 155], [tg 271], [tg 8], [tg 66]],
      [tg 8]⟩,
    ⟨-1, 1, 4, 2,
      [[tg 331], [tg 39], [tg 155], [tg 8]],
      [tg 267595]⟩,
    ⟨-1, 1, 5, 3,
      [[tg 68], [tg 97], [tg 126], [tg 300]],
      [tg 267390]⟩,
    ⟨-1, 1, 6, 5,
      [[tg 287], [tg 68], [tg 300], [tg 387]],
      [tg 400964]⟩,
    ⟨-1, 1, 7, 7,
      [[tg 345], [tg 242], [tg 358], [tg 24]],
      [tg 267622]⟩,
    ⟨-1, 1, 8, 7,
      [[tg 213], [tg 329], [tg 445], [tg 53]],
      [tg 445]⟩,
    ⟨-1, 1, 9, 4,
      [[tg 97], [tg 300], [tg 416], [tg 182]],
      [tg 133729]⟩,
    ⟨-1, 1, 10, 4,
      [[tg 155], [tg 184], [tg 271], [tg 387], [tg 416]],
      [tg 401051]⟩,
    ⟨-1, 1, 11, 7,
      [[tg 242], [tg 445], [tg 140], [tg 211], [tg 356]],
      [tg 134077]⟩,
    ⟨-1, 1, 12, 6,
      [[tg 345], [tg 461], [tg 213], [tg 387]],
      [tg 267651]⟩,
    ⟨-1, 1, 13, 5,
      [[tg 184], [tg 300], [tg 358], [tg 416]],
      [tg 401196]⟩,
    ⟨-1, 1, 14, 5,
      [[tg 271], [tg 300], [tg 387], [tg 445]],
      [tg 267535]⟩,
    ⟨-1, 1, 15, 6,
      [[tg 242], [tg 329], [tg 416], [tg 356]],
      [tg 401312]⟩]⟩,
  ⟨1, -2, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 3)], -1, 0, 3, 2, 0, 0, 0, 0,
   [⟨-3, 0, 0, 13,
      [[tg 562, tg 5202], [tg 591, tg 5231], [tg 230, tg 4870], [tg 40, tg 4680]],
      [tg 267826, tg 272466]⟩,
    ⟨-3, 0, 1, 12,
      [[tg 259, tg 4899], [tg 11, tg 4651], [tg 69, tg 4709], [tg 127, tg 4767]],
      [tg 133701, tg 138341]⟩,
    ⟨-3, 0, 2, 11,
      [[tg 562, tg 5202], [tg 40, tg 4680], [tg 156, tg 4796], [tg 185, tg 4825]],
      [tg 156, tg 4796]⟩,
    ⟨-3, 0, 3, 9,
      [[tg 156, tg 4796], [tg 272, tg 4912], [tg 476, tg 1403], [tg 534, tg 1461]],
      [tg 272, tg 4912]⟩,
    ⟨-3, 0, 4, 11,
      [[tg 346, tg 4986], [tg 40, tg 4680], [tg 156, tg 4796], [tg 476, tg 1403]],
      [tg 267420, tg 272060]⟩,
    ⟨-3, 0, 5, 10,
      [[tg 69, tg 4709], [tg 98, tg 4738], [tg 127, tg 4767], [tg 301, tg 4941]],
      [tg 98, tg 4738]⟩,
    ⟨-3, 0, 6, 10,
      [[tg 736, tg 5376], [tg 69, tg 4709], [tg 301, tg 4941], [tg 388, tg 5028]],
      [tg 133933, tg 138573]⟩,
    ⟨-3, 0, 7, 9,
      [[tg 794, tg 5434], [tg 243, tg 4883], [tg 359, tg 4999], [tg 489, tg 56169]],
      [tg 243, tg 4883]⟩,
    ⟨-3, 0, 8, 8,
      [[tg 214, tg 4854], [tg 330, tg 4970], [tg 446, tg 5086], [tg 518, tg 56198]],
      [tg 330, tg 4970]⟩,
    ⟨-3, 0, 9, 8,
      [[tg 98, tg 4738], [tg 301, tg 4941], [tg 417, tg 5057], [tg 650, tg 1577]],
      [tg 650, tg 1577]⟩,
    ⟨-3, 0, 10, 9,
      [[tg 156, tg 4796], [tg 185, tg 4825], [tg 272, tg 4912], [tg 388, tg 5028], [tg 417, tg 5057]],
      [tg 133904, tg 138544]⟩,
    ⟨-3, 0, 11, 7,
      [[tg 243, tg 4883], [tg 446, tg 5086], [tg 605, tg 56285], [tg 679, tg 1606], [tg 824, tg 1751]],
      [tg 679, tg 1606]⟩,
    ⟨-3, 0, 12, 10,
      [[tg 794, tg 5434], [tg 910, tg 5550], [tg 214, tg 4854], [tg 388, tg 5028]],
      [tg 267478, tg 272118]⟩,
    ⟨-3, 0, 13, 10,
      [[tg 185, tg 4825], [tg 301, tg 4941], [tg 359, tg 4999], [tg 417, tg 5057]],
      [tg 401197, tg 405837]⟩,
    ⟨-3, 0, 14, 9,
      [[tg 272, tg 4912], [tg 301, tg 4941], [tg 388, tg 5028], [tg 446, tg 5086]],
      [tg 267536, tg 272176]⟩,
    ⟨-3, 0, 15, 8,
      [[tg 243, tg 4883], [tg 330, tg 4970], [tg 417, tg 5057], [tg 824, tg 1751]],
      [tg 133962, tg 138602]⟩,
    ⟨-4, 0, 0, 16,
      [[tg 3810, tg 8450], [tg 3839, tg 8479], [tg 4406, tg 9046], [tg 504, tg 5144]],
      [tg 271074, tg 275714]⟩,
    ⟨-4, 0, 1, 15,
      [[tg 4435, tg 9075], [tg 475, tg 5115], [tg 533, tg 5173], [tg 591, tg 5231]],
      [tg 134165, tg 138805]⟩,
    ⟨-4, 0, 2, 14,
      [[tg 3810, tg 8450], [tg 504, tg 5144], [tg 620, tg 5260], [tg 649, tg 5289]],
      [tg 620, tg 5260]⟩,
    ⟨-4, 0, 3, 12,
      [[tg 620, tg 5260], [tg 736, tg 5376], [tg 11, tg 4651], [tg 69, tg 4709]],
      [tg 736, tg 5376]⟩,
    ⟨-4, 0, 4, 14,
      [[tg 4522, tg 9162], [tg 504, tg 5144], [tg 620, tg 5260], [tg 11, tg 4651]],
      [tg 267884, tg 272524]⟩,
    ⟨-4, 0, 5, 13,
      [[tg 533, tg 5173], [tg 562, tg 5202], [tg 591, tg 5231], [tg 765, tg 5405]],
      [tg 562, tg 5202]⟩,
    ⟨-4, 0, 6, 13,
      [[tg 3984, tg 8624], [tg 533, tg 5173], [tg 765, tg 5405], [tg 852, tg 5492]],
      [tg 134397, tg 139037]⟩,
    ⟨-4, 0, 7, 12,
      [[tg 4042, tg 8682], [tg 707, tg 5347], [tg 823, tg 5463], [tg 25, tg 55705]],
      [tg 707, tg 5347]⟩,
    ⟨-4, 0, 8, 11,
      [[tg 678, tg 5318], [tg 794, tg 5434], [tg 910, tg 5550], [tg 54, tg 55734]],
      [tg 794, tg 5434]⟩,
    ⟨-4, 0, 9, 11,
      [[tg 562, tg 5202], [tg 765, tg 5405], [tg 881, tg 5521], [tg 185, tg 4825]],
      [tg 185, tg 4825]⟩,
    ⟨-4, 0, 10, 12,
      [[tg 620, tg 5260], [tg 649, tg 5289], [tg 736, tg 5376], [tg 852, tg 5492], [tg 881, tg 5521]],
      [tg 134368, tg 139008]⟩,
    ⟨-4, 0, 11, 10,
      [[tg 707, tg 5347], [tg 910, tg 5550], [tg 141, tg 55821], [tg 214, tg 4854], [tg 359, tg 4999]],
      [tg 214, tg 4854]⟩,
    ⟨-4, 0, 12, 13,
      [[tg 4042, tg 8682], [tg 4158, tg 8798], [tg 678, tg 5318], [tg 852, tg 5492]],
      [tg 267942, tg 272582]⟩,
    ⟨-4, 0, 13, 13,
      [[tg 649, tg 5289], [tg 765, tg 5405], [tg 823, tg 5463], [tg 881, tg 5521]],
      [tg 401661, tg 406301]⟩,
    ⟨-4, 0, 14, 12,
      [[tg 736, tg 5376], [tg 765, tg 5405], [tg 852, tg 5492], [tg 910, tg 5550]],
      [tg 268000, tg 272640]⟩,
    ⟨-4, 0, 15, 11,
      [[tg 707, tg 5347], [tg 794, tg 5434], [tg 881, tg 5521], [tg 359, tg 4999]],
      [tg 134426, tg 139066]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 1), (1, 0, -2)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, 0, 0, 7,
      [[tg 563], [tg 592], [tg 231], [tg 41]],
      [tg 267827]⟩,
    ⟨-1, 0, 1, 6,
      [[tg 260], [tg 12], [tg 70], [tg 128]],
      [tg 133702]⟩,
    ⟨-1, 0, 2, 5,
      [[tg 563], [tg 41], [tg 157], [tg 186]],
      [tg 157]⟩,
    ⟨-1, 0, 3, 4,
      [[tg 157], [tg 273], [tg 0], [tg 58]],
      [tg 273]⟩,
    ⟨-1, 0, 4, 5,
      [[tg 347], [tg 41], [tg 157], [tg 0]],
      [tg 267421]⟩,
    ⟨-1, 0, 5, 4,
      [[tg 70], [tg 99], [tg 128], [tg 302]],
      [tg 302]⟩,
    ⟨-1, 0, 6, 4,
      [[tg 737], [tg 70], [tg 302], [tg 389]],
      [tg 133934]⟩,
    ⟨-1, 0, 7, 3,
      [[tg 795], [tg 244], [tg 360], [tg 10]],
      [tg 244]⟩,
    ⟨-1, 0, 8, 2,
      [[tg 215], [tg 331], [tg 447], [tg 39]],
      [tg 331]⟩,
    ⟨-1, 0, 9, 3,
      [[tg 99], [tg 302], [tg 418], [tg 174]],
      [tg 418]⟩,
    ⟨-1, 0, 10, 3,
      [[tg 157], [tg 186], [tg 273], [tg 389], [tg 418]],
      [tg 134050]⟩,
    ⟨-1, 0, 11, 1,
      [[tg 244], [tg 447], [tg 126], [tg 203], [tg 348]],
      [tg 348]⟩,
    ⟨-1, 0, 12, 4,
      [[tg 795], [tg 911], [tg 215], [tg 389]],
      [tg 267479]⟩,
    ⟨-1, 0, 13, 3,
      [[tg 186], [tg 302], [tg 360], [tg 418]],
      [tg 267682]⟩,
    ⟨-1, 0, 14, 2,
      [[tg 273], [tg 302], [tg 389], [tg 447]],
      [tg 267711]⟩,
    ⟨-1, 0, 15, 1,
      [[tg 244], [tg 331], [tg 418], [tg 348]],
      [tg 133980]⟩,
    ⟨-2, 0, 0, 10,
      [[tg 98], [tg 127], [tg 694], [tg 505]],
      [tg 267362]⟩,
    ⟨-2, 0, 1, 9,
      [[tg 723], [tg 476], [tg 534], [tg 592]],
      [tg 134166]⟩,
    ⟨-2, 0, 2, 8,
      [[tg 98], [tg 505], [tg 621], [tg 650]],
      [tg 621]⟩,
    ⟨-2, 0, 3, 6,
      [[tg 621], [tg 737], [tg 12], [tg 70]],
      [tg 737]⟩,
    ⟨-2, 0, 4, 8,
      [[tg 810], [tg 505], [tg 621], [tg 12]],
      [tg 267885]⟩,
    ⟨-2, 0, 5, 7,
      [[tg 534], [tg 563], [tg 592], [tg 766]],
      [tg 563]⟩,
    ⟨-2, 0, 6, 7,
      [[tg 272], [tg 534], [tg 766], [tg 853]],
      [tg 134398]⟩,
    ⟨-2, 0, 7, 6,
      [[tg 330], [tg 708], [tg 824], [tg 26]],
      [tg 708]⟩,
    ⟨-2, 0, 8, 5,
      [[tg 679], [tg 795], [tg 911], [tg 55]],
      [tg 795]⟩,
    ⟨-2, 0, 9, 5,
      [[tg 563], [tg 766], [tg 882], [tg 186]],
      [tg 186]⟩,
    ⟨-2, 0, 10, 6,
      [[tg 621], [tg 650], [tg 737], [tg 853], [tg 882]],
      [tg 134369]⟩,
    ⟨-2, 0, 11, 4,
      [[tg 708], [tg 911], [tg 142], [tg 215], [tg 360]],
      [tg 215]⟩,
    ⟨-2, 0, 12, 7,
      [[tg 330], [tg 446], [tg 679], [tg 853]],
      [tg 267943]⟩,
    ⟨-2, 0, 13, 7,
      [[tg 650], [tg 766], [tg 824], [tg 882]],
      [tg 401662]⟩,
    ⟨-2, 0, 14, 6,
      [[tg 737], [tg 766], [tg 853], [tg 911]],
      [tg 268001]⟩,
    ⟨-2, 0, 15, 5,
      [[tg 708], [tg 795], [tg 882], [tg 360]],
      [tg 134427]⟩]⟩,
  ⟨2, 0, -1, 1, -1, [(-1, -1, 2), (1, 0, 2)], -1, -1, 2, 1, 1, 0, 2, 1,
   [⟨2, -4, 0, 28,
      [[tg 3813, tg 8453, tg 26084, tg 30724], [tg 3842, tg 8482, tg 26113, tg 30753], [tg 3928, tg 8568, tg 70744, tg 75384], [tg 42, tg 4682, tg 66858, tg 71498]],
      [tg 271077, tg 275717, tg 293348, tg 297988]⟩,
    ⟨2, -4, 1, 28,
      [[tg 3957, tg 8597, tg 70773, tg 75413], [tg 13, tg 4653, tg 66829, tg 71469], [tg 71, tg 4711, tg 66887, tg 71527], [tg 129, tg 4769, tg 66945, tg 71585]],
      [tg 133703, tg 138343, tg 200519, tg 205159]⟩,
    ⟨2, -4, 2, 27,
      [[tg 3813, tg 8453, tg 26084, tg 30724], [tg 42, tg 4682, tg 66858, tg 71498], [tg 158, tg 4798, tg 66974, tg 71614], [tg 187, tg 4827, tg 67003, tg 71643]],
      [tg 133819, tg 138459, tg 200635, tg 205275]⟩,
    ⟨2, -4, 3, 27,
      [[tg 158, tg 4798, tg 66974, tg 71614], [tg 274, tg 4914, tg 67090, tg 71730], [tg 3727, tg 45485, tg 9295, tg 112301], [tg 3785, tg 45543, tg 9353, tg 112359]],
      [tg 274, tg 4914, tg 67090, tg 71730]⟩,
    ⟨2, -4, 4, 28,
      [[tg 4044, tg 8684, tg 70860, tg 75500], [tg 42, tg 4682, tg 66858, tg 71498], [tg 158, tg 4798, tg 66974, tg 71614], [tg 3727, tg 45485, tg 9295, tg 112301]],
      [tg 267422, tg 272062, tg 334238, tg 338878]⟩,
    ⟨2, -4, 5, 27,
      [[tg 71, tg 4711, tg 66887, tg 71527], [tg 100, tg 4740, tg 66916, tg 71556], [tg 129, tg 4769, tg 66945, tg 71585], [tg 303, tg 4943, tg 67119, tg 71759]],
      [tg 303, tg 4943, tg 67119, tg 71759]⟩,
    ⟨2, -4, 6, 26,
      [[tg 3987, tg 8627, tg 26258, tg 30898], [tg 71, tg 4711, tg 66887, tg 71527], [tg 303, tg 4943, tg 67119, tg 71759], [tg 390, tg 5030, tg 67206, tg 71846]],
      [tg 390, tg 5030, tg 67206, tg 71846]⟩,
    ⟨2, -4, 7, 23,
      [[tg 4045, tg 8685, tg 26316, tg 30956], [tg 245, tg 4885, tg 67061, tg 71701], [tg 361, tg 5001, tg 67177, tg 71817], [tg 15, tg 941, tg 5583, tg 67757]],
      [tg 267279, tg 268205, tg 272847, tg 335021]⟩,
    ⟨2, -4, 8, 23,
      [[tg 216, tg 4856, tg 67032, tg 71672], [tg 332, tg 4972, tg 67148, tg 71788], [tg 448, tg 5088, tg 67264, tg 71904], [tg 44, tg 970, tg 5612, tg 67786]],
      [tg 44, tg 970, tg 5612, tg 67786]⟩,
    ⟨2, -4, 9, 26,
      [[tg 100, tg 4740, tg 66916, tg 71556], [tg 303, tg 4943, tg 67119, tg 71759], [tg 419, tg 5059, tg 67235, tg 71875], [tg 3901, tg 45659, tg 9469, tg 112475]],
      [tg 419, tg 5059, tg 67235, tg 71875]⟩,
    ⟨2, -4, 10, 26,
      [[tg 158, tg 4798, tg 66974, tg 71614], [tg 187, tg 4827, tg 67003, tg 71643], [tg 274, tg 4914, tg 67090, tg 71730], [tg 390, tg 5030, tg 67206, tg 71846], [tg 419, tg 5059, tg 67235, tg 71875]],
      [tg 134022, tg 138662, tg 200838, tg 205478]⟩,
    ⟨2, -4, 11, 23,
      [[tg 245, tg 4885, tg 67061, tg 71701], [tg 448, tg 5088, tg 67264, tg 71904], [tg 131, tg 1057, tg 5699, tg 67873], [tg 3930, tg 45688, tg 9498, tg 112504], [tg 4075, tg 45833, tg 9643, tg 112649]],
      [tg 131, tg 1057, tg 5699, tg 67873]⟩,
    ⟨2, -4, 12, 24,
      [[tg 4045, tg 8685, tg 26316, tg 30956], [tg 4161, tg 8801, tg 26432, tg 31072], [tg 216, tg 4856, tg 67032, tg 71672], [tg 390, tg 5030, tg 67206, tg 71846]],
      [tg 538573, tg 543213, tg 560844, tg 565484]⟩,
    ⟨2, -4, 13, 25,
      [[tg 187, tg 4827, tg 67003, tg 71643], [tg 303, tg 4943, tg 67119, tg 71759], [tg 361, tg 5001, tg 67177, tg 71817], [tg 419, tg 5059, tg 67235, tg 71875]],
      [tg 401257, tg 405897, tg 468073, tg 472713]⟩,
    ⟨2, -4, 14, 25,
      [[tg 274, tg 4914, tg 67090, tg 71730], [tg 303, tg 4943, tg 67119, tg 71759], [tg 390, tg 5030, tg 67206, tg 71846], [tg 448, tg 5088, tg 67264, tg 71904]],
      [tg 267712, tg 272352, tg 334528, tg 339168]⟩,
    ⟨2, -4, 15, 24,
      [[tg 245, tg 4885, tg 67061, tg 71701], [tg 332, tg 4972, tg 67148, tg 71788], [tg 419, tg 5059, tg 67235, tg 71875], [tg 4075, tg 45833, tg 9643, tg 112649]],
      [tg 267509, tg 272149, tg 334325, tg 338965]⟩]⟩,
  ⟨1, 0, -1, 0, 0, [(-1, -1, 2), (1, 0, 1), (-1, 0, -1)], -1, -1, 2, 1, 0, 0, 0, 0,
   [⟨1, -3, 0, 22,
      [[tg 3800, tg 8440], [tg 3829, tg 8469], [tg 3929, tg 8569], [tg 43, tg 4683]],
      [tg 271064, tg 275704]⟩,
    ⟨1, -3, 1, 22,
      [[tg 3958, tg 8598], [tg 14, tg 4654], [tg 72, tg 4712], [tg 130, tg 4770]],
      [tg 133704, tg 138344]⟩,
    ⟨1, -3, 2, 21,
      [[tg 3800, tg 8440], [tg 43, tg 4683], [tg 159, tg 4799], [tg 188, tg 4828]],
      [tg 133820, tg 138460]⟩,
    ⟨1, -3, 3, 21,
      [[tg 159, tg 4799], [tg 275, tg 4915], [tg 15, tg 941], [tg 73, tg 999]],
      [tg 275, tg 4915]⟩,
    ⟨1, -3, 4, 22,
      [[tg 4045, tg 8685], [tg 43, tg 4683], [tg 159, tg 4799], [tg 15, tg 941]],
      [tg 267423, tg 272063]⟩,
    ⟨1, -3, 5, 21,
      [[tg 72, tg 4712], [tg 101, tg 4741], [tg 130, tg 4770], [tg 304, tg 4944]],
      [tg 304, tg 4944]⟩,
    ⟨1, -3, 6, 20,
      [[tg 3974, tg 8614], [tg 72, tg 4712], [tg 304, tg 4944], [tg 391, tg 5031]],
      [tg 391, tg 5031]⟩,
    ⟨1, -3, 7, 17,
      [[tg 4032, tg 8672], [tg 246, tg 4886], [tg 362, tg 5002], [tg 16, tg 942]],
      [tg 267280, tg 268206]⟩,
    ⟨1, -3, 8, 17,
      [[tg 217, tg 4857], [tg 333, tg 4973], [tg 449, tg 5089], [tg 45, tg 971]],
      [tg 45, tg 971]⟩,
    ⟨1, -3, 9, 20,
      [[tg 101, tg 4741], [tg 304, tg 4944], [tg 420, tg 5060], [tg 189, tg 1115]],
      [tg 420, tg 5060]⟩,
    ⟨1, -3, 10, 20,
      [[tg 159, tg 4799], [tg 188, tg 4828], [tg 275, tg 4915], [tg 391, tg 5031], [tg 420, tg 5060]],
      [tg 134023, tg 138663]⟩,
    ⟨1, -3, 11, 17,
      [[tg 246, tg 4886], [tg 449, tg 5089], [tg 132, tg 1058], [tg 218, tg 1144], [tg 363, tg 1289]],
      [tg 132, tg 1058]⟩,
    ⟨1, -3, 12, 18,
      [[tg 4032, tg 8672], [tg 4148, tg 8788], [tg 217, tg 4857], [tg 391, tg 5031]],
      [tg 538560, tg 543200]⟩,
    ⟨1, -3, 13, 19,
      [[tg 188, tg 4828], [tg 304, tg 4944], [tg 362, tg 5002], [tg 420, tg 5060]],
      [tg 401258, tg 405898]⟩,
    ⟨1, -3, 14, 19,
      [[tg 275, tg 4915], [tg 304, tg 4944], [tg 391, tg 5031], [tg 449, tg 5089]],
      [tg 267713, tg 272353]⟩,
    ⟨1, -3, 15, 18,
      [[tg 246, tg 4886], [tg 333, tg 4973], [tg 420, tg 5060], [tg 363, tg 1289]],
      [tg 267510, tg 272150]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 0, 2), (-1, -1, 1), (1, 1, -1)], 1, 0, 2, 1, 0, 0, 0, 0,
   [⟨2, -3, 0, 22,
      [[tg 101, tg 11236], [tg 130, tg 11265], [tg 216, tg 55896], [tg 44, tg 4684]],
      [tg 267365, tg 278500]⟩,
    ⟨2, -3, 1, 22,
      [[tg 245, tg 55925], [tg 15, tg 4655], [tg 73, tg 4713], [tg 131, tg 4771]],
      [tg 133705, tg 138345]⟩,
    ⟨2, -3, 2, 21,
      [[tg 101, tg 11236], [tg 44, tg 4684], [tg 160, tg 4800], [tg 189, tg 4829]],
      [tg 133821, tg 138461]⟩,
    ⟨2, -3, 3, 21,
      [[tg 160, tg 4800], [tg 276, tg 4916], [tg 3715, tg 8355], [tg 3773, tg 8413]],
      [tg 276, tg 4916]⟩,
    ⟨2, -3, 4, 22,
      [[tg 332, tg 56012], [tg 44, tg 4684], [tg 160, tg 4800], [tg 3715, tg 8355]],
      [tg 267424, tg 272064]⟩,
    ⟨2, -3, 5, 21,
      [[tg 73, tg 4713], [tg 102, tg 4742], [tg 131, tg 4771], [tg 305, tg 4945]],
      [tg 305, tg 4945]⟩,
    ⟨2, -3, 6, 20,
      [[tg 275, tg 11410], [tg 73, tg 4713], [tg 305, tg 4945], [tg 392, tg 5032]],
      [tg 392, tg 5032]⟩,
    ⟨2, -3, 7, 17,
      [[tg 333, tg 11468], [tg 247, tg 4887], [tg 363, tg 5003], [tg 3, tg 4643]],
      [tg 267267, tg 271907]⟩,
    ⟨2, -3, 8, 17,
      [[tg 218, tg 4858], [tg 334, tg 4974], [tg 450, tg 5090], [tg 32, tg 4672]],
      [tg 32, tg 4672]⟩,
    ⟨2, -3, 9, 20,
      [[tg 102, tg 4742], [tg 305, tg 4945], [tg 421, tg 5061], [tg 3889, tg 8529]],
      [tg 421, tg 5061]⟩,
    ⟨2, -3, 10, 20,
      [[tg 160, tg 4800], [tg 189, tg 4829], [tg 276, tg 4916], [tg 392, tg 5032], [tg 421, tg 5061]],
      [tg 134024, tg 138664]⟩,
    ⟨2, -3, 11, 17,
      [[tg 247, tg 4887], [tg 450, tg 5090], [tg 119, tg 4759], [tg 3918, tg 8558], [tg 4063, tg 8703]],
      [tg 119, tg 4759]⟩,
    ⟨2, -3, 12, 18,
      [[tg 333, tg 11468], [tg 449, tg 11584], [tg 218, tg 4858], [tg 392, tg 5032]],
      [tg 534861, tg 545996]⟩,
    ⟨2, -3, 13, 19,
      [[tg 189, tg 4829], [tg 305, tg 4945], [tg 363, tg 5003], [tg 421, tg 5061]],
      [tg 401259, tg 405899]⟩,
    ⟨2, -3, 14, 19,
      [[tg 276, tg 4916], [tg 305, tg 4945], [tg 392, tg 5032], [tg 450, tg 5090]],
      [tg 267714, tg 272354]⟩,
    ⟨2, -3, 15, 18,
      [[tg 247, tg 4887], [tg 334, tg 4974], [tg 421, tg 5061], [tg 4063, tg 8703]],
      [tg 267511, tg 272151]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, -1, 1), (1, 1, -1), (1, 0, 1), (-1, 0, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, -2, 0, 16,
      [[tg 88], [tg 117], [tg 217], [tg 45]],
      [tg 267352]⟩,
    ⟨1, -2, 1, 16,
      [[tg 246], [tg 16], [tg 74], [tg 132]],
      [tg 133706]⟩,
    ⟨1, -2, 2, 15,
      [[tg 88], [tg 45], [tg 161], [tg 190]],
      [tg 133822]⟩,
    ⟨1, -2, 3, 15,
      [[tg 161], [tg 277], [tg 3], [tg 61]],
      [tg 277]⟩,
    ⟨1, -2, 4, 16,
      [[tg 333], [tg 45], [tg 161], [tg 3]],
      [tg 267425]⟩,
    ⟨1, -2, 5, 15,
      [[tg 74], [tg 103], [tg 132], [tg 306]],
      [tg 306]⟩,
    ⟨1, -2, 6, 14,
      [[tg 262], [tg 74], [tg 306], [tg 393]],
      [tg 393]⟩,
    ⟨1, -2, 7, 11,
      [[tg 320], [tg 248], [tg 364], [tg 4]],
      [tg 267268]⟩,
    ⟨1, -2, 8, 11,
      [[tg 219], [tg 335], [tg 451], [tg 33]],
      [tg 33]⟩,
    ⟨1, -2, 9, 14,
      [[tg 103], [tg 306], [tg 422], [tg 177]],
      [tg 422]⟩,
    ⟨1, -2, 10, 14,
      [[tg 161], [tg 190], [tg 277], [tg 393], [tg 422]],
      [tg 134025]⟩,
    ⟨1, -2, 11, 11,
      [[tg 248], [tg 451], [tg 120], [tg 206], [tg 351]],
      [tg 120]⟩,
    ⟨1, -2, 12, 12,
      [[tg 320], [tg 436], [tg 219], [tg 393]],
      [tg 534848]⟩,
    ⟨1, -2, 13, 13,
      [[tg 190], [tg 306], [tg 364], [tg 422]],
      [tg 401260]⟩,
    ⟨1, -2, 14, 13,
      [[tg 277], [tg 306], [tg 393], [tg 451]],
      [tg 267715]⟩,
    ⟨1, -2, 15, 12,
      [[tg 248], [tg 335], [tg 422], [tg 351]],
      [tg 267512]⟩]⟩,
  ⟨2, 1, -1, 2, 0, [(0, -2, 2), (1, 1, 2)], 0, -2, 2, 2, 1, 1, 2, 2,
   [⟨3, -1, 0, 14,
      [[tg 105, tg 4745, tg 22840, tg 27480], [tg 134, tg 4774, tg 22869, tg 27509], [tg 3933, tg 8573, tg 26668, tg 31308], [tg 46, tg 4686, tg 66862, tg 71502]],
      [tg 267369, tg 272009, tg 290104, tg 294744]⟩,
    ⟨3, -1, 1, 15,
      [[tg 3962, tg 8602, tg 26697, tg 31337], [tg 17, tg 4657, tg 66833, tg 71473], [tg 75, tg 4715, tg 66891, tg 71531], [tg 133, tg 4773, tg 66949, tg 71589]],
      [tg 400913, tg 405553, tg 467729, tg 472369]⟩,
    ⟨3, -1, 2, 14,
      [[tg 105, tg 4745, tg 22840, tg 27480], [tg 46, tg 4686, tg 66862, tg 71502], [tg 162, tg 4802, tg 66978, tg 71618], [tg 191, tg 4831, tg 67007, tg 71647]],
      [tg 401001, tg 405641, tg 423736, tg 428376]⟩,
    ⟨3, -1, 3, 16,
      [[tg 162, tg 4802, tg 66978, tg 71618], [tg 278, tg 4918, tg 67094, tg 71734], [tg 481, tg 5121, tg 67297, tg 71937], [tg 539, tg 5179, tg 67355, tg 71995]],
      [tg 133794, tg 138434, tg 200610, tg 205250]⟩,
    ⟨3, -1, 4, 16,
      [[tg 4049, tg 8689, tg 26784, tg 31424], [tg 46, tg 4686, tg 66862, tg 71502], [tg 162, tg 4802, tg 66978, tg 71618], [tg 481, tg 5121, tg 67297, tg 71937]],
      [tg 400942, tg 405582, tg 467758, tg 472398]⟩,
    ⟨3, -1, 5, 15,
      [[tg 75, tg 4715, tg 66891, tg 71531], [tg 104, tg 4744, tg 66920, tg 71560], [tg 133, tg 4773, tg 66949, tg 71589], [tg 307, tg 4947, tg 67123, tg 71763]],
      [tg 267339, tg 271979, tg 334155, tg 338795]⟩,
    ⟨3, -1, 6, 13,
      [[tg 279, tg 4919, tg 23014, tg 27654], [tg 75, tg 4715, tg 66891, tg 71531], [tg 307, tg 4947, tg 67123, tg 71763], [tg 394, tg 5034, tg 67210, tg 71850]],
      [tg 401175, tg 405815, tg 423910, tg 428550]⟩,
    ⟨3, -1, 7, 12,
      [[tg 337, tg 4977, tg 23072, tg 27712], [tg 249, tg 4889, tg 67065, tg 71705], [tg 365, tg 5005, tg 67181, tg 71821], [tg 5, tg 1409, tg 5573, tg 68225]],
      [tg 401233, tg 405873, tg 423968, tg 428608]⟩,
    ⟨3, -1, 8, 13,
      [[tg 220, tg 4860, tg 67036, tg 71676], [tg 336, tg 4976, tg 67152, tg 71792], [tg 452, tg 5092, tg 67268, tg 71908], [tg 34, tg 1438, tg 5602, tg 68254]],
      [tg 133852, tg 138492, tg 200668, tg 205308]⟩,
    ⟨3, -1, 9, 15,
      [[tg 104, tg 4744, tg 66920, tg 71560], [tg 307, tg 4947, tg 67123, tg 71763], [tg 423, tg 5063, tg 67239, tg 71879], [tg 655, tg 5295, tg 67471, tg 72111]],
      [tg 267571, tg 272211, tg 334387, tg 339027]⟩,
    ⟨3, -1, 10, 14,
      [[tg 162, tg 4802, tg 66978, tg 71618], [tg 191, tg 4831, tg 67007, tg 71647], [tg 278, tg 4918, tg 67094, tg 71734], [tg 394, tg 5034, tg 67210, tg 71850], [tg 423, tg 5063, tg 67239, tg 71879]],
      [tg 267455, tg 272095, tg 334271, tg 338911]⟩,
    ⟨3, -1, 11, 14,
      [[tg 249, tg 4889, tg 67065, tg 71705], [tg 452, tg 5092, tg 67268, tg 71908], [tg 121, tg 1525, tg 5689, tg 68341], [tg 684, tg 5324, tg 67500, tg 72140], [tg 829, tg 5469, tg 67645, tg 72285]],
      [tg 133881, tg 138521, tg 200697, tg 205337]⟩,
    ⟨3, -1, 12, 12,
      [[tg 337, tg 4977, tg 23072, tg 27712], [tg 453, tg 5093, tg 23188, tg 27828], [tg 220, tg 4860, tg 67036, tg 71676], [tg 394, tg 5034, tg 67210, tg 71850]],
      [tg 534865, tg 539505, tg 557600, tg 562240]⟩,
    ⟨3, -1, 13, 13,
      [[tg 191, tg 4831, tg 67007, tg 71647], [tg 307, tg 4947, tg 67123, tg 71763], [tg 365, tg 5005, tg 67181, tg 71821], [tg 423, tg 5063, tg 67239, tg 71879]],
      [tg 401261, tg 405901, tg 468077, tg 472717]⟩,
    ⟨3, -1, 14, 14,
      [[tg 278, tg 4918, tg 67094, tg 71734], [tg 307, tg 4947, tg 67123, tg 71763], [tg 394, tg 5034, tg 67210, tg 71850], [tg 452, tg 5092, tg 67268, tg 71908]],
      [tg 401290, tg 405930, tg 468106, tg 472746]⟩,
    ⟨3, -1, 15, 14,
      [[tg 249, tg 4889, tg 67065, tg 71705], [tg 336, tg 4976, tg 67152, tg 71792], [tg 423, tg 5063, tg 67239, tg 71879], [tg 829, tg 5469, tg 67645, tg 72285]],
      [tg 267513, tg 272153, tg 334329, tg 338969]⟩,
    ⟨4, -1, 0, 17,
      [[tg 104, tg 4744, tg 66920, tg 71560], [tg 133, tg 4773, tg 66949, tg 71589], [tg 3932, tg 8572, tg 70748, tg 75388], [tg 510, tg 5150, tg 67326, tg 71966]],
      [tg 267368, tg 272008, tg 334184, tg 338824]⟩,
    ⟨4, -1, 1, 18,
      [[tg 3961, tg 8601, tg 70777, tg 75417], [tg 481, tg 5121, tg 67297, tg 71937], [tg 539, tg 5179, tg 67355, tg 71995], [tg 597, tg 5237, tg 67413, tg 72053]],
      [tg 401377, tg 406017, tg 468193, tg 472833]⟩,
    ⟨4, -1, 2, 17,
      [[tg 104, tg 4744, tg 66920, tg 71560], [tg 510, tg 5150, tg 67326, tg 71966], [tg 626, tg 5266, tg 67442, tg 72082], [tg 655, tg 5295, tg 67471, tg 72111]],
      [tg 401000, tg 405640, tg 467816, tg 472456]⟩,
    ⟨4, -1, 3, 19,
      [[tg 626, tg 5266, tg 67442, tg 72082], [tg 742, tg 5382, tg 67558, tg 72198], [tg 44561, tg 49201, tg 111377, tg 116017], [tg 44619, tg 49259, tg 111435, tg 116075]],
      [tg 134258, tg 138898, tg 201074, tg 205714]⟩,
    ⟨4, -1, 4, 19,
      [[tg 4048, tg 8688, tg 70864, tg 75504], [tg 510, tg 5150, tg 67326, tg 71966], [tg 626, tg 5266, tg 67442, tg 72082], [tg 44561, tg 49201, tg 111377, tg 116017]],
      [tg 401406, tg 406046, tg 468222, tg 472862]⟩,
    ⟨4, -1, 5, 18,
      [[tg 539, tg 5179, tg 67355, tg 71995], [tg 568, tg 5208, tg 67384, tg 72024], [tg 597, tg 5237, tg 67413, tg 72053], [tg 771, tg 5411, tg 67587, tg 72227]],
      [tg 267803, tg 272443, tg 334619, tg 339259]⟩,
    ⟨4, -1, 6, 16,
      [[tg 278, tg 4918, tg 67094, tg 71734], [tg 539, tg 5179, tg 67355, tg 71995], [tg 771, tg 5411, tg 67587, tg 72227], [tg 858, tg 5498, tg 67674, tg 72314]],
      [tg 401174, tg 405814, tg 467990, tg 472630]⟩,
    ⟨4, -1, 7, 15,
      [[tg 336, tg 4976, tg 67152, tg 71792], [tg 713, tg 5353, tg 67529, tg 72169], [tg 829, tg 5469, tg 67645, tg 72285], [tg 469, tg 45489, tg 6037, tg 112305]],
      [tg 401232, tg 405872, tg 468048, tg 472688]⟩,
    ⟨4, -1, 8, 16,
      [[tg 684, tg 5324, tg 67500, tg 72140], [tg 800, tg 5440, tg 67616, tg 72256], [tg 916, tg 5556, tg 67732, tg 72372], [tg 498, tg 45518, tg 6066, tg 112334]],
      [tg 134316, tg 138956, tg 201132, tg 205772]⟩,
    ⟨4, -1, 9, 18,
      [[tg 568, tg 5208, tg 67384, tg 72024], [tg 771, tg 5411, tg 67587, tg 72227], [tg 887, tg 5527, tg 67703, tg 72343], [tg 44735, tg 49375, tg 111551, tg 116191]],
      [tg 268035, tg 272675, tg 334851, tg 339491]⟩,
    ⟨4, -1, 10, 17,
      [[tg 626, tg 5266, tg 67442, tg 72082], [tg 655, tg 5295, tg 67471, tg 72111], [tg 742, tg 5382, tg 67558, tg 72198], [tg 858, tg 5498, tg 67674, tg 72314], [tg 887, tg 5527, tg 67703, tg 72343]],
      [tg 267919, tg 272559, tg 334735, tg 339375]⟩,
    ⟨4, -1, 11, 17,
      [[tg 713, tg 5353, tg 67529, tg 72169], [tg 916, tg 5556, tg 67732, tg 72372], [tg 585, tg 45605, tg 6153, tg 112421], [tg 44764, tg 49404, tg 111580, tg 116220], [tg 44909, tg 49549, tg 111725, tg 116365]],
      [tg 134345, tg 138985, tg 201161, tg 205801]⟩,
    ⟨4, -1, 12, 15,
      [[tg 336, tg 4976, tg 67152, tg 71792], [tg 452, tg 5092, tg 67268, tg 71908], [tg 684, tg 5324, tg 67500, tg 72140], [tg 858, tg 5498, tg 67674, tg 72314]],
      [tg 534864, tg 539504, tg 601680, tg 606320]⟩,
    ⟨4, -1, 13, 16,
      [[tg 655, tg 5295, tg 67471, tg 72111], [tg 771, tg 5411, tg 67587, tg 72227], [tg 829, tg 5469, tg 67645, tg 72285], [tg 887, tg 5527, tg 67703, tg 72343]],
      [tg 401725, tg 406365, tg 468541, tg 473181]⟩,
    ⟨4, -1, 14, 17,
      [[tg 742, tg 5382, tg 67558, tg 72198], [tg 771, tg 5411, tg 67587, tg 72227], [tg 858, tg 5498, tg 67674, tg 72314], [tg 916, tg 5556, tg 67732, tg 72372]],
      [tg 401754, tg 406394, tg 468570, tg 473210]⟩,
    ⟨4, -1, 15, 17,
      [[tg 713, tg 5353, tg 67529, tg 72169], [tg 800, tg 5440, tg 67616, tg 72256], [tg 887, tg 5527, tg 67703, tg 72343], [tg 44909, tg 49549, tg 111725, tg 116365]],
      [tg 267977, tg 272617, tg 334793, tg 339433]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(0, -2, 2), (1, 1, 1), (-1, -1, -1)], 0, -2, 2, 2, 0, 0, 0, 0,
   [⟨2, -1, 0, 11,
      [[tg 91, tg 1018], [tg 120, tg 1047], [tg 206, tg 4846], [tg 47, tg 4687]],
      [tg 267355, tg 268282]⟩,
    ⟨2, -1, 1, 12,
      [[tg 235, tg 4875], [tg 18, tg 4658], [tg 76, tg 4716], [tg 134, tg 4774]],
      [tg 400914, tg 405554]⟩,
    ⟨2, -1, 2, 11,
      [[tg 91, tg 1018], [tg 47, tg 4687], [tg 163, tg 4803], [tg 192, tg 4832]],
      [tg 400987, tg 401914]⟩,
    ⟨2, -1, 3, 13,
      [[tg 163, tg 4803], [tg 279, tg 4919], [tg 17, tg 4657], [tg 75, tg 4715]],
      [tg 133795, tg 138435]⟩,
    ⟨2, -1, 4, 13,
      [[tg 322, tg 4962], [tg 47, tg 4687], [tg 163, tg 4803], [tg 17, tg 4657]],
      [tg 400943, tg 405583]⟩,
    ⟨2, -1, 5, 12,
      [[tg 76, tg 4716], [tg 105, tg 4745], [tg 134, tg 4774], [tg 308, tg 4948]],
      [tg 267340, tg 271980]⟩,
    ⟨2, -1, 6, 10,
      [[tg 265, tg 1192], [tg 76, tg 4716], [tg 308, tg 4948], [tg 395, tg 5035]],
      [tg 401161, tg 402088]⟩,
    ⟨2, -1, 7, 9,
      [[tg 323, tg 1250], [tg 250, tg 4890], [tg 366, tg 5006], [tg 470, tg 945]],
      [tg 401219, tg 402146]⟩,
    ⟨2, -1, 8, 10,
      [[tg 221, tg 4861], [tg 337, tg 4977], [tg 453, tg 5093], [tg 499, tg 974]],
      [tg 133853, tg 138493]⟩,
    ⟨2, -1, 9, 12,
      [[tg 105, tg 4745], [tg 308, tg 4948], [tg 424, tg 5064], [tg 191, tg 4831]],
      [tg 267572, tg 272212]⟩,
    ⟨2, -1, 10, 11,
      [[tg 163, tg 4803], [tg 192, tg 4832], [tg 279, tg 4919], [tg 395, tg 5035], [tg 424, tg 5064]],
      [tg 267456, tg 272096]⟩,
    ⟨2, -1, 11, 11,
      [[tg 250, tg 4890], [tg 453, tg 5093], [tg 586, tg 1061], [tg 220, tg 4860], [tg 365, tg 5005]],
      [tg 133882, tg 138522]⟩,
    ⟨2, -1, 12, 9,
      [[tg 323, tg 1250], [tg 439, tg 1366], [tg 221, tg 4861], [tg 395, tg 5035]],
      [tg 534851, tg 535778]⟩,
    ⟨2, -1, 13, 10,
      [[tg 192, tg 4832], [tg 308, tg 4948], [tg 366, tg 5006], [tg 424, tg 5064]],
      [tg 401262, tg 405902]⟩,
    ⟨2, -1, 14, 11,
      [[tg 279, tg 4919], [tg 308, tg 4948], [tg 395, tg 5035], [tg 453, tg 5093]],
      [tg 401291, tg 405931]⟩,
    ⟨2, -1, 15, 11,
      [[tg 250, tg 4890], [tg 337, tg 4977], [tg 424, tg 5064], [tg 365, tg 5005]],
      [tg 267514, tg 272154]⟩]⟩,
  ⟨2, 2, 0, 0, 1, [(1, 0, 2), (0, 2, 2)], 1, 0, 2, 2, 0, 2, 2, 2,
   [⟨2, 1, 0, 8,
      [[tg 107, tg 1498, tg 5675, tg 68314], [tg 136, tg 1527, tg 5704, tg 68343], [tg 673, tg 1600, tg 22494, tg 27134], [tg 48, tg 4688, tg 66864, tg 71504]],
      [tg 401032, tg 402423, tg 406600, tg 469239]⟩,
    ⟨2, 1, 1, 9,
      [[tg 702, tg 1629, tg 22523, tg 27163], [tg 19, tg 4659, tg 66835, tg 71475], [tg 77, tg 4717, tg 66893, tg 71533], [tg 135, tg 4775, tg 66951, tg 71591]],
      [tg 401598, tg 402525, tg 423419, tg 428059]⟩,
    ⟨2, 1, 2, 10,
      [[tg 107, tg 1498, tg 5675, tg 68314], [tg 48, tg 4688, tg 66864, tg 71504], [tg 164, tg 4804, tg 66980, tg 71620], [tg 193, tg 4833, tg 67009, tg 71649]],
      [tg 401003, tg 402394, tg 406571, tg 469210]⟩,
    ⟨2, 1, 3, 12,
      [[tg 164, tg 4804, tg 66980, tg 71620], [tg 280, tg 4920, tg 67096, tg 71736], [tg 483, tg 5123, tg 67299, tg 71939], [tg 541, tg 5181, tg 67357, tg 71997]],
      [tg 133796, tg 138436, tg 200612, tg 205252]⟩,
    ⟨2, 1, 4, 10,
      [[tg 789, tg 1716, tg 22610, tg 27250], [tg 48, tg 4688, tg 66864, tg 71504], [tg 164, tg 4804, tg 66980, tg 71620], [tg 483, tg 5123, tg 67299, tg 71939]],
      [tg 268053, tg 268980, tg 289874, tg 294514]⟩,
    ⟨2, 1, 5, 11,
      [[tg 77, tg 4717, tg 66893, tg 71533], [tg 106, tg 4746, tg 66922, tg 71562], [tg 135, tg 4775, tg 66951, tg 71591], [tg 309, tg 4949, tg 67125, tg 71765]],
      [tg 267341, tg 271981, tg 334157, tg 338797]⟩,
    ⟨2, 1, 6, 11,
      [[tg 281, tg 1672, tg 5849, tg 68488], [tg 77, tg 4717, tg 66893, tg 71533], [tg 309, tg 4949, tg 67125, tg 71765], [tg 396, tg 5036, tg 67212, tg 71852]],
      [tg 401177, tg 402568, tg 406745, tg 469384]⟩,
    ⟨2, 1, 7, 13,
      [[tg 339, tg 1730, tg 5907, tg 68546], [tg 251, tg 4891, tg 67067, tg 71707], [tg 367, tg 5007, tg 67183, tg 71823], [tg 44563, tg 49203, tg 111379, tg 116019]],
      [tg 401235, tg 402626, tg 406803, tg 469442]⟩,
    ⟨2, 1, 8, 14,
      [[tg 222, tg 4862, tg 67038, tg 71678], [tg 338, tg 4978, tg 67154, tg 71794], [tg 454, tg 5094, tg 67270, tg 71910], [tg 44592, tg 49232, tg 111408, tg 116048]],
      [tg 133854, tg 138494, tg 200670, tg 205310]⟩,
    ⟨2, 1, 9, 13,
      [[tg 106, tg 4746, tg 66922, tg 71562], [tg 309, tg 4949, tg 67125, tg 71765], [tg 425, tg 5065, tg 67241, tg 71881], [tg 657, tg 5297, tg 67473, tg 72113]],
      [tg 133738, tg 138378, tg 200554, tg 205194]⟩,
    ⟨2, 1, 10, 12,
      [[tg 164, tg 4804, tg 66980, tg 71620], [tg 193, tg 4833, tg 67009, tg 71649], [tg 280, tg 4920, tg 67096, tg 71736], [tg 396, tg 5036, tg 67212, tg 71852], [tg 425, tg 5065, tg 67241, tg 71881]],
      [tg 401060, tg 405700, tg 467876, tg 472516]⟩,
    ⟨2, 1, 11, 15,
      [[tg 251, tg 4891, tg 67067, tg 71707], [tg 454, tg 5094, tg 67270, tg 71910], [tg 44679, tg 49319, tg 111495, tg 116135], [tg 686, tg 5326, tg 67502, tg 72142], [tg 831, tg 5471, tg 67647, tg 72287]],
      [tg 133883, tg 138523, tg 200699, tg 205339]⟩,
    ⟨2, 1, 12, 12,
      [[tg 339, tg 1730, tg 5907, tg 68546], [tg 455, tg 1846, tg 6023, tg 68662], [tg 222, tg 4862, tg 67038, tg 71678], [tg 396, tg 5036, tg 67212, tg 71852]],
      [tg 401351, tg 402742, tg 406919, tg 469558]⟩,
    ⟨2, 1, 13, 12,
      [[tg 193, tg 4833, tg 67009, tg 71649], [tg 309, tg 4949, tg 67125, tg 71765], [tg 367, tg 5007, tg 67183, tg 71823], [tg 425, tg 5065, tg 67241, tg 71881]],
      [tg 401089, tg 405729, tg 467905, tg 472545]⟩,
    ⟨2, 1, 14, 13,
      [[tg 280, tg 4920, tg 67096, tg 71736], [tg 309, tg 4949, tg 67125, tg 71765], [tg 396, tg 5036, tg 67212, tg 71852], [tg 454, tg 5094, tg 67270, tg 71910]],
      [tg 534837, tg 539477, tg 601653, tg 606293]⟩,
    ⟨2, 1, 15, 14,
      [[tg 251, tg 4891, tg 67067, tg 71707], [tg 338, tg 4978, tg 67154, tg 71794], [tg 425, tg 5065, tg 67241, tg 71881], [tg 831, tg 5471, tg 67647, tg 72287]],
      [tg 401321, tg 405961, tg 468137, tg 472777]⟩,
    ⟨3, 1, 0, 11,
      [[tg 106, tg 4746, tg 66922, tg 71562], [tg 135, tg 4775, tg 66951, tg 71591], [tg 208, tg 4848, tg 22958, tg 27598], [tg 512, tg 5152, tg 67328, tg 71968]],
      [tg 401031, tg 405671, tg 467847, tg 472487]⟩,
    ⟨3, 1, 1, 12,
      [[tg 237, tg 4877, tg 22987, tg 27627], [tg 483, tg 5123, tg 67299, tg 71939], [tg 541, tg 5181, tg 67357, tg 71997], [tg 599, tg 5239, tg 67415, tg 72055]],
      [tg 401133, tg 405773, tg 423883, tg 428523]⟩,
    ⟨3, 1, 2, 13,
      [[tg 106, tg 4746, tg 66922, tg 71562], [tg 512, tg 5152, tg 67328, tg 71968], [tg 628, tg 5268, tg 67444, tg 72084], [tg 657, tg 5297, tg 67473, tg 72113]],
      [tg 401002, tg 405642, tg 467818, tg 472458]⟩,
    ⟨3, 1, 3, 15,
      [[tg 628, tg 5268, tg 67444, tg 72084], [tg 744, tg 5384, tg 67560, tg 72200], [tg 3731, tg 8371, tg 70547, tg 75187], [tg 3789, tg 8429, tg 70605, tg 75245]],
      [tg 134260, tg 138900, tg 201076, tg 205716]⟩,
    ⟨3, 1, 4, 13,
      [[tg 324, tg 4964, tg 23074, tg 27714], [tg 512, tg 5152, tg 67328, tg 71968], [tg 628, tg 5268, tg 67444, tg 72084], [tg 3731, tg 8371, tg 70547, tg 75187]],
      [tg 267588, tg 272228, tg 290338, tg 294978]⟩,
    ⟨3, 1, 5, 14,
      [[tg 541, tg 5181, tg 67357, tg 71997], [tg 570, tg 5210, tg 67386, tg 72026], [tg 599, tg 5239, tg 67415, tg 72055], [tg 773, tg 5413, tg 67589, tg 72229]],
      [tg 267805, tg 272445, tg 334621, tg 339261]⟩,
    ⟨3, 1, 6, 14,
      [[tg 280, tg 4920, tg 67096, tg 71736], [tg 541, tg 5181, tg 67357, tg 71997], [tg 773, tg 5413, tg 67589, tg 72229], [tg 860, tg 5500, tg 67676, tg 72316]],
      [tg 401176, tg 405816, tg 467992, tg 472632]⟩,
    ⟨3, 1, 7, 16,
      [[tg 338, tg 4978, tg 67154, tg 71794], [tg 715, tg 5355, tg 67531, tg 72171], [tg 831, tg 5471, tg 67647, tg 72287], [tg 45027, tg 49667, tg 111843, tg 116483]],
      [tg 401234, tg 405874, tg 468050, tg 472690]⟩,
    ⟨3, 1, 8, 17,
      [[tg 686, tg 5326, tg 67502, tg 72142], [tg 802, tg 5442, tg 67618, tg 72258], [tg 918, tg 5558, tg 67734, tg 72374], [tg 45056, tg 49696, tg 111872, tg 116512]],
      [tg 134318, tg 138958, tg 201134, tg 205774]⟩,
    ⟨3, 1, 9, 16,
      [[tg 570, tg 5210, tg 67386, tg 72026], [tg 773, tg 5413, tg 67589, tg 72229], [tg 889, tg 5529, tg 67705, tg 72345], [tg 3905, tg 8545, tg 70721, tg 75361]],
      [tg 134202, tg 138842, tg 201018, tg 205658]⟩,
    ⟨3, 1, 10, 15,
      [[tg 628, tg 5268, tg 67444, tg 72084], [tg 657, tg 5297, tg 67473, tg 72113], [tg 744, tg 5384, tg 67560, tg 72200], [tg 860, tg 5500, tg 67676, tg 72316], [tg 889, tg 5529, tg 67705, tg 72345]],
      [tg 401524, tg 406164, tg 468340, tg 472980]⟩,
    ⟨3, 1, 11, 18,
      [[tg 715, tg 5355, tg 67531, tg 72171], [tg 918, tg 5558, tg 67734, tg 72374], [tg 45143, tg 49783, tg 111959, tg 116599], [tg 3934, tg 8574, tg 70750, tg 75390], [tg 4079, tg 8719, tg 70895, tg 75535]],
      [tg 134347, tg 138987, tg 201163, tg 205803]⟩,
    ⟨3, 1, 12, 15,
      [[tg 338, tg 4978, tg 67154, tg 71794], [tg 454, tg 5094, tg 67270, tg 71910], [tg 686, tg 5326, tg 67502, tg 72142], [tg 860, tg 5500, tg 67676, tg 72316]],
      [tg 401350, tg 405990, tg 468166, tg 472806]⟩,
    ⟨3, 1, 13, 15,
      [[tg 657, tg 5297, tg 67473, tg 72113], [tg 773, tg 5413, tg 67589, tg 72229], [tg 831, tg 5471, tg 67647, tg 72287], [tg 889, tg 5529, tg 67705, tg 72345]],
      [tg 401553, tg 406193, tg 468369, tg 473009]⟩,
    ⟨3, 1, 14, 16,
      [[tg 744, tg 5384, tg 67560, tg 72200], [tg 773, tg 5413, tg 67589, tg 72229], [tg 860, tg 5500, tg 67676, tg 72316], [tg 918, tg 5558, tg 67734, tg 72374]],
      [tg 535301, tg 539941, tg 602117, tg 606757]⟩,
    ⟨3, 1, 15, 17,
      [[tg 715, tg 5355, tg 67531, tg 72171], [tg 802, tg 5442, tg 67618, tg 72258], [tg 889, tg 5529, tg 67705, tg 72345], [tg 4079, tg 8719, tg 70895, tg 75535]],
      [tg 401785, tg 406425, tg 468601, tg 473241]⟩]⟩,
  ⟨1, 0, 1, 0, 0, [(0, 2, 2), (1, 0, 1), (-1, 0, -1)], 0, 2, 2, 2, 0, 0, 0, 0,
   [⟨1, 1, 0, 5,
      [[tg 95, tg 1022], [tg 124, tg 1051], [tg 209, tg 1151], [tg 49, tg 4689]],
      [tg 401020, tg 401947]⟩,
    ⟨1, 1, 1, 6,
      [[tg 238, tg 1180], [tg 20, tg 4660], [tg 78, tg 4718], [tg 136, tg 4776]],
      [tg 401134, tg 402076]⟩,
    ⟨1, 1, 2, 7,
      [[tg 95, tg 1022], [tg 49, tg 4689], [tg 165, tg 4805], [tg 194, tg 4834]],
      [tg 400991, tg 401918]⟩,
    ⟨1, 1, 3, 9,
      [[tg 165, tg 4805], [tg 281, tg 4921], [tg 19, tg 55699], [tg 77, tg 55757]],
      [tg 133797, tg 138437]⟩,
    ⟨1, 1, 4, 7,
      [[tg 325, tg 1267], [tg 49, tg 4689], [tg 165, tg 4805], [tg 19, tg 55699]],
      [tg 267589, tg 268531]⟩,
    ⟨1, 1, 5, 8,
      [[tg 78, tg 4718], [tg 107, tg 4747], [tg 136, tg 4776], [tg 310, tg 4950]],
      [tg 267342, tg 271982]⟩,
    ⟨1, 1, 6, 8,
      [[tg 269, tg 1196], [tg 78, tg 4718], [tg 310, tg 4950], [tg 397, tg 5037]],
      [tg 401165, tg 402092]⟩,
    ⟨1, 1, 7, 10,
      [[tg 327, tg 1254], [tg 252, tg 4892], [tg 368, tg 5008], [tg 3732, tg 8372]],
      [tg 401223, tg 402150]⟩,
    ⟨1, 1, 8, 11,
      [[tg 223, tg 4863], [tg 339, tg 4979], [tg 455, tg 5095], [tg 3761, tg 8401]],
      [tg 133855, tg 138495]⟩,
    ⟨1, 1, 9, 10,
      [[tg 107, tg 4747], [tg 310, tg 4950], [tg 426, tg 5066], [tg 193, tg 55873]],
      [tg 133739, tg 138379]⟩,
    ⟨1, 1, 10, 9,
      [[tg 165, tg 4805], [tg 194, tg 4834], [tg 281, tg 4921], [tg 397, tg 5037], [tg 426, tg 5066]],
      [tg 401061, tg 405701]⟩,
    ⟨1, 1, 11, 12,
      [[tg 252, tg 4892], [tg 455, tg 5095], [tg 3848, tg 8488], [tg 222, tg 55902], [tg 367, tg 56047]],
      [tg 133884, tg 138524]⟩,
    ⟨1, 1, 12, 9,
      [[tg 327, tg 1254], [tg 443, tg 1370], [tg 223, tg 4863], [tg 397, tg 5037]],
      [tg 401339, tg 402266]⟩,
    ⟨1, 1, 13, 9,
      [[tg 194, tg 4834], [tg 310, tg 4950], [tg 368, tg 5008], [tg 426, tg 5066]],
      [tg 401090, tg 405730]⟩,
    ⟨1, 1, 14, 10,
      [[tg 281, tg 4921], [tg 310, tg 4950], [tg 397, tg 5037], [tg 455, tg 5095]],
      [tg 534838, tg 539478]⟩,
    ⟨1, 1, 15, 11,
      [[tg 252, tg 4892], [tg 339, tg 4979], [tg 426, tg 5066], [tg 367, tg 56047]],
      [tg 401322, tg 405962]⟩]⟩,
  ⟨2, 0, 1, -1, 1, [(1, 1, 2), (-1, 0, 2)], 1, 1, 2, 1, -1, 0, 2, 1,
   [⟨-2, 4, 0, 20,
      [[tg 3822, tg 45580, tg 9390, tg 112396], [tg 3851, tg 45609, tg 9419, tg 112425], [tg 226, tg 1152, tg 5794, tg 67968], [tg 50, tg 4690, tg 66866, tg 71506]],
      [tg 401122, tg 402048, tg 406690, tg 468864]⟩,
    ⟨-2, 4, 1, 20,
      [[tg 255, tg 1181, tg 5823, tg 67997], [tg 21, tg 4661, tg 66837, tg 71477], [tg 79, tg 4719, tg 66895, tg 71535], [tg 137, tg 4777, tg 66953, tg 71593]],
      [tg 401151, tg 402077, tg 406719, tg 468893]⟩,
    ⟨-2, 4, 2, 21,
      [[tg 3822, tg 45580, tg 9390, tg 112396], [tg 50, tg 4690, tg 66866, tg 71506], [tg 166, tg 4806, tg 66982, tg 71622], [tg 195, tg 4835, tg 67011, tg 71651]],
      [tg 267314, tg 271954, tg 334130, tg 338770]⟩,
    ⟨-2, 4, 3, 21,
      [[tg 166, tg 4806, tg 66982, tg 71622], [tg 282, tg 4922, tg 67098, tg 71738], [tg 3734, tg 8374, tg 26005, tg 30645], [tg 3792, tg 8432, tg 26063, tg 30703]],
      [tg 3734, tg 8374, tg 26005, tg 30645]⟩,
    ⟨-2, 4, 4, 20,
      [[tg 342, tg 1268, tg 5910, tg 68084], [tg 50, tg 4690, tg 66866, tg 71506], [tg 166, tg 4806, tg 66982, tg 71622], [tg 3734, tg 8374, tg 26005, tg 30645]],
      [tg 267606, tg 268532, tg 273174, tg 335348]⟩,
    ⟨-2, 4, 5, 21,
      [[tg 79, tg 4719, tg 66895, tg 71535], [tg 108, tg 4748, tg 66924, tg 71564], [tg 137, tg 4777, tg 66953, tg 71593], [tg 311, tg 4951, tg 67127, tg 71767]],
      [tg 267401, tg 272041, tg 334217, tg 338857]⟩,
    ⟨-2, 4, 6, 22,
      [[tg 3996, tg 45754, tg 9564, tg 112570], [tg 79, tg 4719, tg 66895, tg 71535], [tg 311, tg 4951, tg 67127, tg 71767], [tg 398, tg 5038, tg 67214, tg 71854]],
      [tg 400975, tg 405615, tg 467791, tg 472431]⟩,
    ⟨-2, 4, 7, 25,
      [[tg 4054, tg 45812, tg 9622, tg 112628], [tg 253, tg 4893, tg 67069, tg 71709], [tg 369, tg 5009, tg 67185, tg 71825], [tg 3733, tg 8373, tg 70549, tg 75189]],
      [tg 267633, tg 272273, tg 334449, tg 339089]⟩,
    ⟨-2, 4, 8, 25,
      [[tg 224, tg 4864, tg 67040, tg 71680], [tg 340, tg 4980, tg 67156, tg 71796], [tg 456, tg 5096, tg 67272, tg 71912], [tg 3762, tg 8402, tg 70578, tg 75218]],
      [tg 456, tg 5096, tg 67272, tg 71912]⟩,
    ⟨-2, 4, 9, 22,
      [[tg 108, tg 4748, tg 66924, tg 71564], [tg 311, tg 4951, tg 67127, tg 71767], [tg 427, tg 5067, tg 67243, tg 71883], [tg 3908, tg 8548, tg 26179, tg 30819]],
      [tg 133740, tg 138380, tg 200556, tg 205196]⟩,
    ⟨-2, 4, 10, 22,
      [[tg 166, tg 4806, tg 66982, tg 71622], [tg 195, tg 4835, tg 67011, tg 71651], [tg 282, tg 4922, tg 67098, tg 71738], [tg 398, tg 5038, tg 67214, tg 71854], [tg 427, tg 5067, tg 67243, tg 71883]],
      [tg 401062, tg 405702, tg 467878, tg 472518]⟩,
    ⟨-2, 4, 11, 25,
      [[tg 253, tg 4893, tg 67069, tg 71709], [tg 456, tg 5096, tg 67272, tg 71912], [tg 3849, tg 8489, tg 70665, tg 75305], [tg 3937, tg 8577, tg 26208, tg 30848], [tg 4082, tg 8722, tg 26353, tg 30993]],
      [tg 134088, tg 138728, tg 200904, tg 205544]⟩,
    ⟨-2, 4, 12, 24,
      [[tg 4054, tg 45812, tg 9622, tg 112628], [tg 4170, tg 45928, tg 9738, tg 112744], [tg 224, tg 4864, tg 67040, tg 71680], [tg 398, tg 5038, tg 67214, tg 71854]],
      [tg 267662, tg 272302, tg 334478, tg 339118]⟩,
    ⟨-2, 4, 13, 23,
      [[tg 195, tg 4835, tg 67011, tg 71651], [tg 311, tg 4951, tg 67127, tg 71767], [tg 369, tg 5009, tg 67185, tg 71825], [tg 427, tg 5067, tg 67243, tg 71883]],
      [tg 401091, tg 405731, tg 467907, tg 472547]⟩,
    ⟨-2, 4, 14, 23,
      [[tg 282, tg 4922, tg 67098, tg 71738], [tg 311, tg 4951, tg 67127, tg 71767], [tg 398, tg 5038, tg 67214, tg 71854], [tg 456, tg 5096, tg 67272, tg 71912]],
      [tg 267546, tg 272186, tg 334362, tg 339002]⟩,
    ⟨-2, 4, 15, 24,
      [[tg 253, tg 4893, tg 67069, tg 71709], [tg 340, tg 4980, tg 67156, tg 71796], [tg 427, tg 5067, tg 67243, tg 71883], [tg 4082, tg 8722, tg 26353, tg 30993]],
      [tg 401323, tg 405963, tg 468139, tg 472779]⟩]⟩,
  ⟨1, 0, 1, 0, 0, [(1, 1, 2), (-1, 0, 1), (1, 0, -1)], 1, 1, 2, 1, 0, 0, 0, 0,
   [⟨-1, 3, 0, 14,
      [[tg 110, tg 1036], [tg 139, tg 1065], [tg 227, tg 1153], [tg 51, tg 4691]],
      [tg 401123, tg 402049]⟩,
    ⟨-1, 3, 1, 14,
      [[tg 256, tg 1182], [tg 22, tg 4662], [tg 80, tg 4720], [tg 138, tg 4778]],
      [tg 401152, tg 402078]⟩,
    ⟨-1, 3, 2, 15,
      [[tg 110, tg 1036], [tg 51, tg 4691], [tg 167, tg 4807], [tg 196, tg 4836]],
      [tg 267315, tg 271955]⟩,
    ⟨-1, 3, 3, 16,
      [[tg 167, tg 4807], [tg 283, tg 4923], [tg 3719, tg 8359], [tg 3777, tg 8417]],
      [tg 133799, tg 138439]⟩,
    ⟨-1, 3, 4, 14,
      [[tg 343, tg 1269], [tg 51, tg 4691], [tg 167, tg 4807], [tg 3719, tg 8359]],
      [tg 267607, tg 268533]⟩,
    ⟨-1, 3, 5, 15,
      [[tg 80, tg 4720], [tg 109, tg 4749], [tg 138, tg 4778], [tg 312, tg 4952]],
      [tg 267402, tg 272042]⟩,
    ⟨-1, 3, 6, 16,
      [[tg 284, tg 1210], [tg 80, tg 4720], [tg 312, tg 4952], [tg 399, tg 5039]],
      [tg 400976, tg 405616]⟩,
    ⟨-1, 3, 7, 19,
      [[tg 342, tg 1268], [tg 254, tg 4894], [tg 370, tg 5010], [tg 3734, tg 8374]],
      [tg 267634, tg 272274]⟩,
    ⟨-1, 3, 8, 19,
      [[tg 225, tg 4865], [tg 341, tg 4981], [tg 457, tg 5097], [tg 3763, tg 8403]],
      [tg 457, tg 5097]⟩,
    ⟨-1, 3, 9, 17,
      [[tg 109, tg 4749], [tg 312, tg 4952], [tg 428, tg 5068], [tg 3893, tg 8533]],
      [tg 133741, tg 138381]⟩,
    ⟨-1, 3, 10, 16,
      [[tg 167, tg 4807], [tg 196, tg 4836], [tg 283, tg 4923], [tg 399, tg 5039], [tg 428, tg 5068]],
      [tg 401063, tg 405703]⟩,
    ⟨-1, 3, 11, 19,
      [[tg 254, tg 4894], [tg 457, tg 5097], [tg 3850, tg 8490], [tg 3922, tg 8562], [tg 4067, tg 8707]],
      [tg 134089, tg 138729]⟩,
    ⟨-1, 3, 12, 18,
      [[tg 342, tg 1268], [tg 458, tg 1384], [tg 225, tg 4865], [tg 399, tg 5039]],
      [tg 267663, tg 272303]⟩,
    ⟨-1, 3, 13, 17,
      [[tg 196, tg 4836], [tg 312, tg 4952], [tg 370, tg 5010], [tg 428, tg 5068]],
      [tg 401092, tg 405732]⟩,
    ⟨-1, 3, 14, 17,
      [[tg 283, tg 4923], [tg 312, tg 4952], [tg 399, tg 5039], [tg 457, tg 5097]],
      [tg 534840, tg 539480]⟩,
    ⟨-1, 3, 15, 18,
      [[tg 254, tg 4894], [tg 341, tg 4981], [tg 428, tg 5068], [tg 4067, tg 8707]],
      [tg 401324, tg 405964]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, 0, 2), (1, 1, 1), (-1, -1, -1)], -1, 0, 2, 1, 0, 0, 0, 0,
   [⟨-2, 3, 0, 14,
      [[tg 3808, tg 8448], [tg 3837, tg 8477], [tg 212, tg 4852], [tg 52, tg 4692]],
      [tg 401108, tg 405748]⟩,
    ⟨-2, 3, 1, 14,
      [[tg 241, tg 4881], [tg 23, tg 4663], [tg 81, tg 4721], [tg 139, tg 4779]],
      [tg 401137, tg 405777]⟩,
    ⟨-2, 3, 2, 15,
      [[tg 3808, tg 8448], [tg 52, tg 4692], [tg 168, tg 4808], [tg 197, tg 4837]],
      [tg 267316, tg 271956]⟩,
    ⟨-2, 3, 3, 15,
      [[tg 168, tg 4808], [tg 284, tg 4924], [tg 22, tg 11157], [tg 80, tg 11215]],
      [tg 22, tg 11157]⟩,
    ⟨-2, 3, 4, 14,
      [[tg 328, tg 4968], [tg 52, tg 4692], [tg 168, tg 4808], [tg 22, tg 11157]],
      [tg 267592, tg 272232]⟩,
    ⟨-2, 3, 5, 15,
      [[tg 81, tg 4721], [tg 110, tg 4750], [tg 139, tg 4779], [tg 313, tg 4953]],
      [tg 267403, tg 272043]⟩,
    ⟨-2, 3, 6, 16,
      [[tg 3982, tg 8622], [tg 81, tg 4721], [tg 313, tg 4953], [tg 400, tg 5040]],
      [tg 400977, tg 405617]⟩,
    ⟨-2, 3, 7, 19,
      [[tg 4040, tg 8680], [tg 255, tg 4895], [tg 371, tg 5011], [tg 21, tg 55701]],
      [tg 267635, tg 272275]⟩,
    ⟨-2, 3, 8, 19,
      [[tg 226, tg 4866], [tg 342, tg 4982], [tg 458, tg 5098], [tg 50, tg 55730]],
      [tg 458, tg 5098]⟩,
    ⟨-2, 3, 9, 16,
      [[tg 110, tg 4750], [tg 313, tg 4953], [tg 429, tg 5069], [tg 196, tg 11331]],
      [tg 133742, tg 138382]⟩,
    ⟨-2, 3, 10, 16,
      [[tg 168, tg 4808], [tg 197, tg 4837], [tg 284, tg 4924], [tg 400, tg 5040], [tg 429, tg 5069]],
      [tg 401064, tg 405704]⟩,
    ⟨-2, 3, 11, 19,
      [[tg 255, tg 4895], [tg 458, tg 5098], [tg 137, tg 55817], [tg 225, tg 11360], [tg 370, tg 11505]],
      [tg 134090, tg 138730]⟩,
    ⟨-2, 3, 12, 18,
      [[tg 4040, tg 8680], [tg 4156, tg 8796], [tg 226, tg 4866], [tg 400, tg 5040]],
      [tg 267664, tg 272304]⟩,
    ⟨-2, 3, 13, 17,
      [[tg 197, tg 4837], [tg 313, tg 4953], [tg 371, tg 5011], [tg 429, tg 5069]],
      [tg 401093, tg 405733]⟩,
    ⟨-2, 3, 14, 17,
      [[tg 284, tg 4924], [tg 313, tg 4953], [tg 400, tg 5040], [tg 458, tg 5098]],
      [tg 267548, tg 272188]⟩,
    ⟨-2, 3, 15, 18,
      [[tg 255, tg 4895], [tg 342, tg 4982], [tg 429, tg 5069], [tg 370, tg 11505]],
      [tg 401325, tg 405965]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 1, 1), (-1, -1, -1), (-1, 0, 1), (1, 0, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, 2, 0, 8,
      [[tg 96], [tg 125], [tg 213], [tg 53]],
      [tg 401109]⟩,
    ⟨-1, 2, 1, 8,
      [[tg 242], [tg 24], [tg 82], [tg 140]],
      [tg 401138]⟩,
    ⟨-1, 2, 2, 9,
      [[tg 96], [tg 53], [tg 169], [tg 198]],
      [tg 267317]⟩,
    ⟨-1, 2, 3, 10,
      [[tg 169], [tg 285], [tg 7], [tg 65]],
      [tg 133801]⟩,
    ⟨-1, 2, 4, 8,
      [[tg 329], [tg 53], [tg 169], [tg 7]],
      [tg 267593]⟩,
    ⟨-1, 2, 5, 9,
      [[tg 82], [tg 111], [tg 140], [tg 314]],
      [tg 267404]⟩,
    ⟨-1, 2, 6, 10,
      [[tg 270], [tg 82], [tg 314], [tg 401]],
      [tg 400978]⟩,
    ⟨-1, 2, 7, 13,
      [[tg 328], [tg 256], [tg 372], [tg 22]],
      [tg 267636]⟩,
    ⟨-1, 2, 8, 13,
      [[tg 227], [tg 343], [tg 459], [tg 51]],
      [tg 459]⟩,
    ⟨-1, 2, 9, 11,
      [[tg 111], [tg 314], [tg 430], [tg 181]],
      [tg 133743]⟩,
    ⟨-1, 2, 10, 10,
      [[tg 169], [tg 198], [tg 285], [tg 401], [tg 430]],
      [tg 401065]⟩,
    ⟨-1, 2, 11, 13,
      [[tg 256], [tg 459], [tg 138], [tg 210], [tg 355]],
      [tg 134091]⟩,
    ⟨-1, 2, 12, 12,
      [[tg 328], [tg 444], [tg 227], [tg 401]],
      [tg 267665]⟩,
    ⟨-1, 2, 13, 11,
      [[tg 198], [tg 314], [tg 372], [tg 430]],
      [tg 401094]⟩,
    ⟨-1, 2, 14, 11,
      [[tg 285], [tg 314], [tg 401], [tg 459]],
      [tg 534842]⟩,
    ⟨-1, 2, 15, 12,
      [[tg 256], [tg 343], [tg 430], [tg 355]],
      [tg 401326]⟩]⟩,
  ⟨2, -1, 1, -2, 0, [(0, 2, 2), (-1, -1, 2)], 0, 2, 2, 2, -1, -1, 2, 2,
   [⟨-4, 1, 0, 13,
      [[tg 45120, tg 49760, tg 111936, tg 116576], [tg 45149, tg 49789, tg 111965, tg 116605], [tg 678, tg 46164, tg 6246, tg 112980], [tg 54, tg 4694, tg 66870, tg 71510]],
      [tg 401574, tg 447060, tg 407142, tg 513876]⟩,
    ⟨-4, 1, 1, 12,
      [[tg 707, tg 46193, tg 6275, tg 113009], [tg 25, tg 4665, tg 66841, tg 71481], [tg 83, tg 4723, tg 66899, tg 71539], [tg 141, tg 4781, tg 66957, tg 71597]],
      [tg 401603, tg 447089, tg 407171, tg 513905]⟩,
    ⟨-4, 1, 2, 13,
      [[tg 45120, tg 49760, tg 111936, tg 116576], [tg 54, tg 4694, tg 66870, tg 71510], [tg 170, tg 4810, tg 66986, tg 71626], [tg 199, tg 4839, tg 67015, tg 71655]],
      [tg 267318, tg 271958, tg 334134, tg 338774]⟩,
    ⟨-4, 1, 3, 11,
      [[tg 170, tg 4810, tg 66986, tg 71626], [tg 286, tg 4926, tg 67102, tg 71742], [tg 489, tg 5129, tg 67305, tg 71945], [tg 547, tg 5187, tg 67363, tg 72003]],
      [tg 489, tg 5129, tg 67305, tg 71945]⟩,
    ⟨-4, 1, 4, 11,
      [[tg 794, tg 46280, tg 6362, tg 113096], [tg 54, tg 4694, tg 66870, tg 71510], [tg 170, tg 4810, tg 66986, tg 71626], [tg 489, tg 5129, tg 67305, tg 71945]],
      [tg 268058, tg 313544, tg 273626, tg 380360]⟩,
    ⟨-4, 1, 5, 12,
      [[tg 83, tg 4723, tg 66899, tg 71539], [tg 112, tg 4752, tg 66928, tg 71568], [tg 141, tg 4781, tg 66957, tg 71597], [tg 315, tg 4955, tg 67131, tg 71771]],
      [tg 112, tg 4752, tg 66928, tg 71568]⟩,
    ⟨-4, 1, 6, 14,
      [[tg 45294, tg 49934, tg 112110, tg 116750], [tg 83, tg 4723, tg 66899, tg 71539], [tg 315, tg 4955, tg 67131, tg 71771], [tg 402, tg 5042, tg 67218, tg 71858]],
      [tg 400979, tg 405619, tg 467795, tg 472435]⟩,
    ⟨-4, 1, 7, 15,
      [[tg 45352, tg 49992, tg 112168, tg 116808], [tg 257, tg 4897, tg 67073, tg 71713], [tg 373, tg 5013, tg 67189, tg 71829], [tg 4201, tg 8841, tg 71017, tg 75657]],
      [tg 257, tg 4897, tg 67073, tg 71713]⟩,
    ⟨-4, 1, 8, 14,
      [[tg 228, tg 4868, tg 67044, tg 71684], [tg 344, tg 4984, tg 67160, tg 71800], [tg 460, tg 5100, tg 67276, tg 71916], [tg 4230, tg 8870, tg 71046, tg 75686]],
      [tg 344, tg 4984, tg 67160, tg 71800]⟩,
    ⟨-4, 1, 9, 12,
      [[tg 112, tg 4752, tg 66928, tg 71568], [tg 315, tg 4955, tg 67131, tg 71771], [tg 431, tg 5071, tg 67247, tg 71887], [tg 663, tg 5303, tg 67479, tg 72119]],
      [tg 133744, tg 138384, tg 200560, tg 205200]⟩,
    ⟨-4, 1, 10, 13,
      [[tg 170, tg 4810, tg 66986, tg 71626], [tg 199, tg 4839, tg 67015, tg 71655], [tg 286, tg 4926, tg 67102, tg 71742], [tg 402, tg 5042, tg 67218, tg 71858], [tg 431, tg 5071, tg 67247, tg 71887]],
      [tg 401066, tg 405706, tg 467882, tg 472522]⟩,
    ⟨-4, 1, 11, 13,
      [[tg 257, tg 4897, tg 67073, tg 71713], [tg 460, tg 5100, tg 67276, tg 71916], [tg 4317, tg 8957, tg 71133, tg 75773], [tg 692, tg 5332, tg 67508, tg 72148], [tg 837, tg 5477, tg 67653, tg 72293]],
      [tg 692, tg 5332, tg 67508, tg 72148]⟩,
    ⟨-4, 1, 12, 15,
      [[tg 45352, tg 49992, tg 112168, tg 116808], [tg 45468, tg 50108, tg 112284, tg 116924], [tg 228, tg 4868, tg 67044, tg 71684], [tg 402, tg 5042, tg 67218, tg 71858]],
      [tg 267666, tg 272306, tg 334482, tg 339122]⟩,
    ⟨-4, 1, 13, 14,
      [[tg 199, tg 4839, tg 67015, tg 71655], [tg 315, tg 4955, tg 67131, tg 71771], [tg 373, tg 5013, tg 67189, tg 71829], [tg 431, tg 5071, tg 67247, tg 71887]],
      [tg 401211, tg 405851, tg 468027, tg 472667]⟩,
    ⟨-4, 1, 14, 13,
      [[tg 286, tg 4926, tg 67102, tg 71742], [tg 315, tg 4955, tg 67131, tg 71771], [tg 402, tg 5042, tg 67218, tg 71858], [tg 460, tg 5100, tg 67276, tg 71916]],
      [tg 267550, tg 272190, tg 334366, tg 339006]⟩,
    ⟨-4, 1, 15, 13,
      [[tg 257, tg 4897, tg 67073, tg 71713], [tg 344, tg 4984, tg 67160, tg 71800], [tg 431, tg 5071, tg 67247, tg 71887], [tg 837, tg 5477, tg 67653, tg 72293]],
      [tg 134469, tg 139109, tg 201285, tg 205925]⟩,
    ⟨-3, 1, 0, 10,
      [[tg 112, tg 4752, tg 66928, tg 71568], [tg 141, tg 4781, tg 66957, tg 71597], [tg 214, tg 1156, tg 5782, tg 67972], [tg 518, tg 5158, tg 67334, tg 71974]],
      [tg 401110, tg 402052, tg 406678, tg 468868]⟩,
    ⟨-3, 1, 1, 9,
      [[tg 243, tg 1185, tg 5811, tg 68001], [tg 489, tg 5129, tg 67305, tg 71945], [tg 547, tg 5187, tg 67363, tg 72003], [tg 605, tg 5245, tg 67421, tg 72061]],
      [tg 401139, tg 402081, tg 406707, tg 468897]⟩,
    ⟨-3, 1, 2, 10,
      [[tg 112, tg 4752, tg 66928, tg 71568], [tg 518, tg 5158, tg 67334, tg 71974], [tg 634, tg 5274, tg 67450, tg 72090], [tg 663, tg 5303, tg 67479, tg 72119]],
      [tg 267782, tg 272422, tg 334598, tg 339238]⟩,
    ⟨-3, 1, 3, 8,
      [[tg 634, tg 5274, tg 67450, tg 72090], [tg 750, tg 5390, tg 67566, tg 72206], [tg 26, tg 4666, tg 22297, tg 26937], [tg 84, tg 4724, tg 22355, tg 26995]],
      [tg 26, tg 4666, tg 22297, tg 26937]⟩,
    ⟨-3, 1, 4, 8,
      [[tg 330, tg 1272, tg 5898, tg 68088], [tg 518, tg 5158, tg 67334, tg 71974], [tg 634, tg 5274, tg 67450, tg 72090], [tg 26, tg 4666, tg 22297, tg 26937]],
      [tg 267594, tg 268536, tg 273162, tg 335352]⟩,
    ⟨-3, 1, 5, 9,
      [[tg 547, tg 5187, tg 67363, tg 72003], [tg 576, tg 5216, tg 67392, tg 72032], [tg 605, tg 5245, tg 67421, tg 72061], [tg 779, tg 5419, tg 67595, tg 72235]],
      [tg 576, tg 5216, tg 67392, tg 72032]⟩,
    ⟨-3, 1, 6, 11,
      [[tg 286, tg 4926, tg 67102, tg 71742], [tg 547, tg 5187, tg 67363, tg 72003], [tg 779, tg 5419, tg 67595, tg 72235], [tg 866, tg 5506, tg 67682, tg 72322]],
      [tg 401443, tg 406083, tg 468259, tg 472899]⟩,
    ⟨-3, 1, 7, 12,
      [[tg 344, tg 4984, tg 67160, tg 71800], [tg 721, tg 5361, tg 67537, tg 72177], [tg 837, tg 5477, tg 67653, tg 72293], [tg 3738, tg 8378, tg 26009, tg 30649]],
      [tg 721, tg 5361, tg 67537, tg 72177]⟩,
    ⟨-3, 1, 8, 11,
      [[tg 692, tg 5332, tg 67508, tg 72148], [tg 808, tg 5448, tg 67624, tg 72264], [tg 924, tg 5564, tg 67740, tg 72380], [tg 3767, tg 8407, tg 26038, tg 30678]],
      [tg 808, tg 5448, tg 67624, tg 72264]⟩,
    ⟨-3, 1, 9, 9,
      [[tg 576, tg 5216, tg 67392, tg 72032], [tg 779, tg 5419, tg 67595, tg 72235], [tg 895, tg 5535, tg 67711, tg 72351], [tg 200, tg 4840, tg 22471, tg 27111]],
      [tg 134208, tg 138848, tg 201024, tg 205664]⟩,
    ⟨-3, 1, 10, 10,
      [[tg 634, tg 5274, tg 67450, tg 72090], [tg 663, tg 5303, tg 67479, tg 72119], [tg 750, tg 5390, tg 67566, tg 72206], [tg 866, tg 5506, tg 67682, tg 72322], [tg 895, tg 5535, tg 67711, tg 72351]],
      [tg 401530, tg 406170, tg 468346, tg 472986]⟩,
    ⟨-3, 1, 11, 10,
      [[tg 721, tg 5361, tg 67537, tg 72177], [tg 924, tg 5564, tg 67740, tg 72380], [tg 3854, tg 8494, tg 26125, tg 30765], [tg 229, tg 4869, tg 22500, tg 27140], [tg 374, tg 5014, tg 22645, tg 27285]],
      [tg 229, tg 4869, tg 22500, tg 27140]⟩,
    ⟨-3, 1, 12, 12,
      [[tg 344, tg 4984, tg 67160, tg 71800], [tg 460, tg 5100, tg 67276, tg 71916], [tg 692, tg 5332, tg 67508, tg 72148], [tg 866, tg 5506, tg 67682, tg 72322]],
      [tg 268130, tg 272770, tg 334946, tg 339586]⟩,
    ⟨-3, 1, 13, 11,
      [[tg 663, tg 5303, tg 67479, tg 72119], [tg 779, tg 5419, tg 67595, tg 72235], [tg 837, tg 5477, tg 67653, tg 72293], [tg 895, tg 5535, tg 67711, tg 72351]],
      [tg 401675, tg 406315, tg 468491, tg 473131]⟩,
    ⟨-3, 1, 14, 10,
      [[tg 750, tg 5390, tg 67566, tg 72206], [tg 779, tg 5419, tg 67595, tg 72235], [tg 866, tg 5506, tg 67682, tg 72322], [tg 924, tg 5564, tg 67740, tg 72380]],
      [tg 268014, tg 272654, tg 334830, tg 339470]⟩,
    ⟨-3, 1, 15, 10,
      [[tg 721, tg 5361, tg 67537, tg 72177], [tg 808, tg 5448, tg 67624, tg 72264], [tg 895, tg 5535, tg 67711, tg 72351], [tg 374, tg 5014, tg 22645, tg 27285]],
      [tg 134006, tg 138646, tg 156277, tg 160917]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(0, 2, 2), (-1, -1, 1), (1, 1, -1)], 0, 2, 2, 2, 0, 0, 0, 0,
   [⟨-2, 1, 0, 7,
      [[tg 576, tg 5216], [tg 605, tg 5245], [tg 679, tg 1620], [tg 55, tg 4695]],
      [tg 401575, tg 402516]⟩,
    ⟨-2, 1, 1, 6,
      [[tg 708, tg 1649], [tg 26, tg 4666], [tg 84, tg 4724], [tg 142, tg 4782]],
      [tg 401604, tg 402545]⟩,
    ⟨-2, 1, 2, 7,
      [[tg 576, tg 5216], [tg 55, tg 4695], [tg 171, tg 4811], [tg 200, tg 4840]],
      [tg 267319, tg 271959]⟩,
    ⟨-2, 1, 3, 5,
      [[tg 171, tg 4811], [tg 287, tg 4927], [tg 10, tg 937], [tg 68, tg 995]],
      [tg 10, tg 937]⟩,
    ⟨-2, 1, 4, 5,
      [[tg 795, tg 1736], [tg 55, tg 4695], [tg 171, tg 4811], [tg 10, tg 937]],
      [tg 268059, tg 269000]⟩,
    ⟨-2, 1, 5, 6,
      [[tg 84, tg 4724], [tg 113, tg 4753], [tg 142, tg 4782], [tg 316, tg 4956]],
      [tg 113, tg 4753]⟩,
    ⟨-2, 1, 6, 8,
      [[tg 750, tg 5390], [tg 84, tg 4724], [tg 316, tg 4956], [tg 403, tg 5043]],
      [tg 400980, tg 405620]⟩,
    ⟨-2, 1, 7, 9,
      [[tg 808, tg 5448], [tg 258, tg 4898], [tg 374, tg 5014], [tg 9, tg 4649]],
      [tg 258, tg 4898]⟩,
    ⟨-2, 1, 8, 8,
      [[tg 229, tg 4869], [tg 345, tg 4985], [tg 461, tg 5101], [tg 38, tg 4678]],
      [tg 345, tg 4985]⟩,
    ⟨-2, 1, 9, 6,
      [[tg 113, tg 4753], [tg 316, tg 4956], [tg 432, tg 5072], [tg 184, tg 1111]],
      [tg 133745, tg 138385]⟩,
    ⟨-2, 1, 10, 7,
      [[tg 171, tg 4811], [tg 200, tg 4840], [tg 287, tg 4927], [tg 403, tg 5043], [tg 432, tg 5072]],
      [tg 401067, tg 405707]⟩,
    ⟨-2, 1, 11, 7,
      [[tg 258, tg 4898], [tg 461, tg 5101], [tg 125, tg 4765], [tg 213, tg 1140], [tg 358, tg 1285]],
      [tg 358, tg 1285]⟩,
    ⟨-2, 1, 12, 9,
      [[tg 808, tg 5448], [tg 924, tg 5564], [tg 229, tg 4869], [tg 403, tg 5043]],
      [tg 267667, tg 272307]⟩,
    ⟨-2, 1, 13, 8,
      [[tg 200, tg 4840], [tg 316, tg 4956], [tg 374, tg 5014], [tg 432, tg 5072]],
      [tg 401212, tg 405852]⟩,
    ⟨-2, 1, 14, 7,
      [[tg 287, tg 4927], [tg 316, tg 4956], [tg 403, tg 5043], [tg 461, tg 5101]],
      [tg 267551, tg 272191]⟩,
    ⟨-2, 1, 15, 7,
      [[tg 258, tg 4898], [tg 345, tg 4985], [tg 432, tg 5072], [tg 358, tg 1285]],
      [tg 133990, tg 134917]⟩]⟩,
  ⟨2, -2, 0, 0, -1, [(-1, 0, 2), (0, -2, 2)], -1, 0, 2, 2, 0, -2, 2, 2,
   [⟨-3, -1, 0, 19,
      [[tg 4290, tg 8930, tg 71106, tg 75746], [tg 4319, tg 8959, tg 71135, tg 75775], [tg 44774, tg 49414, tg 111590, tg 116230], [tg 56, tg 4696, tg 66872, tg 71512]],
      [tg 271554, tg 276194, tg 338370, tg 343010]⟩,
    ⟨-3, -1, 1, 18,
      [[tg 44803, tg 49443, tg 111619, tg 116259], [tg 27, tg 4667, tg 66843, tg 71483], [tg 85, tg 4725, tg 66901, tg 71541], [tg 143, tg 4783, tg 66959, tg 71599]],
      [tg 133717, tg 138357, tg 200533, tg 205173]⟩,
    ⟨-3, -1, 2, 17,
      [[tg 4290, tg 8930, tg 71106, tg 75746], [tg 56, tg 4696, tg 66872, tg 71512], [tg 172, tg 4812, tg 66988, tg 71628], [tg 201, tg 4841, tg 67017, tg 71657]],
      [tg 172, tg 4812, tg 66988, tg 71628]⟩,
    ⟨-3, -1, 3, 15,
      [[tg 172, tg 4812, tg 66988, tg 71628], [tg 288, tg 4928, tg 67104, tg 71744], [tg 491, tg 5131, tg 67307, tg 71947], [tg 549, tg 5189, tg 67365, tg 72005]],
      [tg 288, tg 4928, tg 67104, tg 71744]⟩,
    ⟨-3, -1, 4, 17,
      [[tg 44890, tg 49530, tg 111706, tg 116346], [tg 56, tg 4696, tg 66872, tg 71512], [tg 172, tg 4812, tg 66988, tg 71628], [tg 491, tg 5131, tg 67307, tg 71947]],
      [tg 267436, tg 272076, tg 334252, tg 338892]⟩,
    ⟨-3, -1, 5, 16,
      [[tg 85, tg 4725, tg 66901, tg 71541], [tg 114, tg 4754, tg 66930, tg 71570], [tg 143, tg 4783, tg 66959, tg 71599], [tg 317, tg 4957, tg 67133, tg 71773]],
      [tg 114, tg 4754, tg 66930, tg 71570]⟩,
    ⟨-3, -1, 6, 16,
      [[tg 4464, tg 9104, tg 71280, tg 75920], [tg 85, tg 4725, tg 66901, tg 71541], [tg 317, tg 4957, tg 67133, tg 71773], [tg 404, tg 5044, tg 67220, tg 71860]],
      [tg 133949, tg 138589, tg 200765, tg 205405]⟩,
    ⟨-3, -1, 7, 14,
      [[tg 4522, tg 9162, tg 71338, tg 75978], [tg 259, tg 4899, tg 67075, tg 71715], [tg 375, tg 5015, tg 67191, tg 71831], [tg 11, tg 4651, tg 22299, tg 26939]],
      [tg 259, tg 4899, tg 67075, tg 71715]⟩,
    ⟨-3, -1, 8, 13,
      [[tg 230, tg 4870, tg 67046, tg 71686], [tg 346, tg 4986, tg 67162, tg 71802], [tg 462, tg 5102, tg 67278, tg 71918], [tg 40, tg 4680, tg 22328, tg 26968]],
      [tg 346, tg 4986, tg 67162, tg 71802]⟩,
    ⟨-3, -1, 9, 14,
      [[tg 114, tg 4754, tg 66930, tg 71570], [tg 317, tg 4957, tg 67133, tg 71773], [tg 433, tg 5073, tg 67249, tg 71889], [tg 665, tg 5305, tg 67481, tg 72121]],
      [tg 665, tg 5305, tg 67481, tg 72121]⟩,
    ⟨-3, -1, 10, 15,
      [[tg 172, tg 4812, tg 66988, tg 71628], [tg 201, tg 4841, tg 67017, tg 71657], [tg 288, tg 4928, tg 67104, tg 71744], [tg 404, tg 5044, tg 67220, tg 71860], [tg 433, tg 5073, tg 67249, tg 71889]],
      [tg 133920, tg 138560, tg 200736, tg 205376]⟩,
    ⟨-3, -1, 11, 12,
      [[tg 259, tg 4899, tg 67075, tg 71715], [tg 462, tg 5102, tg 67278, tg 71918], [tg 127, tg 4767, tg 22415, tg 27055], [tg 694, tg 5334, tg 67510, tg 72150], [tg 839, tg 5479, tg 67655, tg 72295]],
      [tg 127, tg 4767, tg 22415, tg 27055]⟩,
    ⟨-3, -1, 12, 15,
      [[tg 4522, tg 9162, tg 71338, tg 75978], [tg 4638, tg 9278, tg 71454, tg 76094], [tg 230, tg 4870, tg 67046, tg 71686], [tg 404, tg 5044, tg 67220, tg 71860]],
      [tg 267494, tg 272134, tg 334310, tg 338950]⟩,
    ⟨-3, -1, 13, 15,
      [[tg 201, tg 4841, tg 67017, tg 71657], [tg 317, tg 4957, tg 67133, tg 71773], [tg 375, tg 5015, tg 67191, tg 71831], [tg 433, tg 5073, tg 67249, tg 71889]],
      [tg 267697, tg 272337, tg 334513, tg 339153]⟩,
    ⟨-3, -1, 14, 14,
      [[tg 288, tg 4928, tg 67104, tg 71744], [tg 317, tg 4957, tg 67133, tg 71773], [tg 404, tg 5044, tg 67220, tg 71860], [tg 462, tg 5102, tg 67278, tg 71918]],
      [tg 267726, tg 272366, tg 334542, tg 339182]⟩,
    ⟨-3, -1, 15, 13,
      [[tg 259, tg 4899, tg 67075, tg 71715], [tg 346, tg 4986, tg 67162, tg 71802], [tg 433, tg 5073, tg 67249, tg 71889], [tg 839, tg 5479, tg 67655, tg 72295]],
      [tg 133978, tg 138618, tg 200794, tg 205434]⟩,
    ⟨-2, -1, 0, 16,
      [[tg 114, tg 4754, tg 66930, tg 71570], [tg 143, tg 4783, tg 66959, tg 71599], [tg 45238, tg 49878, tg 112054, tg 116694], [tg 520, tg 5160, tg 67336, tg 71976]],
      [tg 267378, tg 272018, tg 334194, tg 338834]⟩,
    ⟨-2, -1, 1, 15,
      [[tg 45267, tg 49907, tg 112083, tg 116723], [tg 491, tg 5131, tg 67307, tg 71947], [tg 549, tg 5189, tg 67365, tg 72005], [tg 607, tg 5247, tg 67423, tg 72063]],
      [tg 134181, tg 138821, tg 200997, tg 205637]⟩,
    ⟨-2, -1, 2, 14,
      [[tg 114, tg 4754, tg 66930, tg 71570], [tg 520, tg 5160, tg 67336, tg 71976], [tg 636, tg 5276, tg 67452, tg 72092], [tg 665, tg 5305, tg 67481, tg 72121]],
      [tg 636, tg 5276, tg 67452, tg 72092]⟩,
    ⟨-2, -1, 3, 12,
      [[tg 636, tg 5276, tg 67452, tg 72092], [tg 752, tg 5392, tg 67568, tg 72208], [tg 28, tg 955, tg 5596, tg 67771], [tg 86, tg 1013, tg 5654, tg 67829]],
      [tg 752, tg 5392, tg 67568, tg 72208]⟩,
    ⟨-2, -1, 4, 14,
      [[tg 45354, tg 49994, tg 112170, tg 116810], [tg 520, tg 5160, tg 67336, tg 71976], [tg 636, tg 5276, tg 67452, tg 72092], [tg 28, tg 955, tg 5596, tg 67771]],
      [tg 267900, tg 272540, tg 334716, tg 339356]⟩,
    ⟨-2, -1, 5, 13,
      [[tg 549, tg 5189, tg 67365, tg 72005], [tg 578, tg 5218, tg 67394, tg 72034], [tg 607, tg 5247, tg 67423, tg 72063], [tg 781, tg 5421, tg 67597, tg 72237]],
      [tg 578, tg 5218, tg 67394, tg 72034]⟩,
    ⟨-2, -1, 6, 13,
      [[tg 288, tg 4928, tg 67104, tg 71744], [tg 549, tg 5189, tg 67365, tg 72005], [tg 781, tg 5421, tg 67597, tg 72237], [tg 868, tg 5508, tg 67684, tg 72324]],
      [tg 134413, tg 139053, tg 201229, tg 205869]⟩,
    ⟨-2, -1, 7, 11,
      [[tg 346, tg 4986, tg 67162, tg 71802], [tg 723, tg 5363, tg 67539, tg 72179], [tg 839, tg 5479, tg 67655, tg 72295], [tg 476, tg 1403, tg 22763, tg 27403]],
      [tg 723, tg 5363, tg 67539, tg 72179]⟩,
    ⟨-2, -1, 8, 10,
      [[tg 694, tg 5334, tg 67510, tg 72150], [tg 810, tg 5450, tg 67626, tg 72266], [tg 926, tg 5566, tg 67742, tg 72382], [tg 505, tg 1432, tg 22792, tg 27432]],
      [tg 810, tg 5450, tg 67626, tg 72266]⟩,
    ⟨-2, -1, 9, 11,
      [[tg 578, tg 5218, tg 67394, tg 72034], [tg 781, tg 5421, tg 67597, tg 72237], [tg 897, tg 5537, tg 67713, tg 72353], [tg 202, tg 1129, tg 5770, tg 67945]],
      [tg 202, tg 1129, tg 5770, tg 67945]⟩,
    ⟨-2, -1, 10, 12,
      [[tg 636, tg 5276, tg 67452, tg 72092], [tg 665, tg 5305, tg 67481, tg 72121], [tg 752, tg 5392, tg 67568, tg 72208], [tg 868, tg 5508, tg 67684, tg 72324], [tg 897, tg 5537, tg 67713, tg 72353]],
      [tg 134384, tg 139024, tg 201200, tg 205840]⟩,
    ⟨-2, -1, 11, 9,
      [[tg 723, tg 5363, tg 67539, tg 72179], [tg 926, tg 5566, tg 67742, tg 72382], [tg 592, tg 1519, tg 22879, tg 27519], [tg 231, tg 1158, tg 5799, tg 67974], [tg 376, tg 1303, tg 5944, tg 68119]],
      [tg 592, tg 1519, tg 22879, tg 27519]⟩,
    ⟨-2, -1, 12, 12,
      [[tg 346, tg 4986, tg 67162, tg 71802], [tg 462, tg 5102, tg 67278, tg 71918], [tg 694, tg 5334, tg 67510, tg 72150], [tg 868, tg 5508, tg 67684, tg 72324]],
      [tg 267958, tg 272598, tg 334774, tg 339414]⟩,
    ⟨-2, -1, 13, 12,
      [[tg 665, tg 5305, tg 67481, tg 72121], [tg 781, tg 5421, tg 67597, tg 72237], [tg 839, tg 5479, tg 67655, tg 72295], [tg 897, tg 5537, tg 67713, tg 72353]],
      [tg 268161, tg 272801, tg 334977, tg 339617]⟩,
    ⟨-2, -1, 14, 11,
      [[tg 752, tg 5392, tg 67568, tg 72208], [tg 781, tg 5421, tg 67597, tg 72237], [tg 868, tg 5508, tg 67684, tg 72324], [tg 926, tg 5566, tg 67742, tg 72382]],
      [tg 268190, tg 272830, tg 335006, tg 339646]⟩,
    ⟨-2, -1, 15, 10,
      [[tg 723, tg 5363, tg 67539, tg 72179], [tg 810, tg 5450, tg 67626, tg 72266], [tg 897, tg 5537, tg 67713, tg 72353], [tg 376, tg 1303, tg 5944, tg 68119]],
      [tg 134442, tg 139082, tg 201258, tg 205898]⟩]⟩,
  ⟨1, 0, -1, 0, 0, [(0, -2, 2), (-1, 0, 1), (1, 0, -1)], 0, -2, 2, 2, 0, 0, 0, 0,
   [⟨-1, -1, 0, 13,
      [[tg 578, tg 56258], [tg 607, tg 56287], [tg 3943, tg 8583], [tg 57, tg 4697]],
      [tg 267842, tg 323522]⟩,
    ⟨-1, -1, 1, 12,
      [[tg 3972, tg 8612], [tg 28, tg 4668], [tg 86, tg 4726], [tg 144, tg 4784]],
      [tg 133718, tg 138358]⟩,
    ⟨-1, -1, 2, 11,
      [[tg 578, tg 56258], [tg 57, tg 4697], [tg 173, tg 4813], [tg 202, tg 4842]],
      [tg 173, tg 4813]⟩,
    ⟨-1, -1, 3, 10,
      [[tg 173, tg 4813], [tg 289, tg 4929], [tg 2, tg 929], [tg 60, tg 987]],
      [tg 289, tg 4929]⟩,
    ⟨-1, -1, 4, 11,
      [[tg 4059, tg 8699], [tg 57, tg 4697], [tg 173, tg 4813], [tg 2, tg 929]],
      [tg 267437, tg 272077]⟩,
    ⟨-1, -1, 5, 10,
      [[tg 86, tg 4726], [tg 115, tg 4755], [tg 144, tg 4784], [tg 318, tg 4958]],
      [tg 318, tg 4958]⟩,
    ⟨-1, -1, 6, 10,
      [[tg 752, tg 56432], [tg 86, tg 4726], [tg 318, tg 4958], [tg 405, tg 5045]],
      [tg 133950, tg 138590]⟩,
    ⟨-1, -1, 7, 8,
      [[tg 810, tg 56490], [tg 260, tg 4900], [tg 376, tg 5016], [tg 12, tg 956]],
      [tg 260, tg 4900]⟩,
    ⟨-1, -1, 8, 7,
      [[tg 231, tg 4871], [tg 347, tg 4987], [tg 463, tg 5103], [tg 41, tg 985]],
      [tg 347, tg 4987]⟩,
    ⟨-1, -1, 9, 9,
      [[tg 115, tg 4755], [tg 318, tg 4958], [tg 434, tg 5074], [tg 176, tg 1103]],
      [tg 434, tg 5074]⟩,
    ⟨-1, -1, 10, 9,
      [[tg 173, tg 4813], [tg 202, tg 4842], [tg 289, tg 4929], [tg 405, tg 5045], [tg 434, tg 5074]],
      [tg 134066, tg 138706]⟩,
    ⟨-1, -1, 11, 6,
      [[tg 260, tg 4900], [tg 463, tg 5103], [tg 128, tg 1072], [tg 205, tg 1132], [tg 350, tg 1277]],
      [tg 128, tg 1072]⟩,
    ⟨-1, -1, 12, 9,
      [[tg 810, tg 56490], [tg 926, tg 56606], [tg 231, tg 4871], [tg 405, tg 5045]],
      [tg 267495, tg 272135]⟩,
    ⟨-1, -1, 13, 9,
      [[tg 202, tg 4842], [tg 318, tg 4958], [tg 376, tg 5016], [tg 434, tg 5074]],
      [tg 267698, tg 272338]⟩,
    ⟨-1, -1, 14, 8,
      [[tg 289, tg 4929], [tg 318, tg 4958], [tg 405, tg 5045], [tg 463, tg 5103]],
      [tg 267727, tg 272367]⟩,
    ⟨-1, -1, 15, 7,
      [[tg 260, tg 4900], [tg 347, tg 4987], [tg 434, tg 5074], [tg 350, tg 1277]],
      [tg 133979, tg 138619]⟩]⟩]

/-- A packed certificate entry: side bit, test index, coefficient. -/
def cc (n : ℕ) : Bool × ℕ × ℕ := (n % 2 == 1, n / 2 % 8, n / 16)

set_option maxRecDepth 100000 in
def certsData : List (List (List (Bool × ℕ × ℕ))) := [
  [[],[cc 20,cc 21],[cc 20,cc 21],[cc 18,cc 20,cc 21],[cc 18,cc 20,cc 21],[cc 18,cc 21],[cc 18,cc 21],[cc 22,cc 21],[cc 22,cc 21],[cc 16,cc 22,cc 21],[cc 16,cc 22,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 36,cc 17],[cc 36,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 38,cc 17],[cc 38,cc 17],[cc 16,cc 17],[cc 16,cc 19]],
  [[cc 20,cc 21],[],[cc 20,cc 23],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 19],[cc 18,cc 20,cc 19],[cc 18,cc 17],[cc 18,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 36,cc 17],[cc 36,cc 17],[cc 16,cc 17],[cc 16,cc 19]],
  [[cc 20,cc 21],[cc 22,cc 21],[],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 19],[cc 18,cc 20,cc 19],[cc 18,cc 17],[cc 18,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 36,cc 17],[cc 36,cc 17],[cc 16,cc 17],[cc 16,cc 19]],
  [[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[],[cc 20,cc 23],[cc 18,cc 20,cc 33],[cc 18,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 37],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 20,cc 19],[cc 16,cc 20,cc 37],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 35]],
  [[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[cc 22,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 37],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 20,cc 19],[cc 18,cc 20,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 35]],
  [[cc 20,cc 19],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[],[cc 20,cc 23],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 19],[cc 20,cc 23],[cc 32,cc 17],[cc 32,cc 17],[cc 34,cc 19],[cc 34,cc 17],[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 17],[cc 20,cc 21],[cc 34,cc 17],[cc 34,cc 17],[cc 32,cc 19],[cc 32,cc 17]],
  [[cc 20,cc 19],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[cc 22,cc 21],[],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 17],[cc 32,cc 17],[cc 32,cc 17],[cc 34,cc 19],[cc 34,cc 17],[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 17],[cc 20,cc 21],[cc 34,cc 17],[cc 34,cc 17],[cc 32,cc 19],[cc 32,cc 17]],
  [[cc 20,cc 23],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[],[cc 20,cc 23],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 36,cc 17],[cc 36,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 19],[cc 18,cc 20,cc 19],[cc 18,cc 17],[cc 18,cc 19]],
  [[cc 20,cc 23],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 22,cc 21],[],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 36,cc 17],[cc 36,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 19],[cc 18,cc 20,cc 19],[cc 18,cc 17],[cc 18,cc 19]],
  [[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[],[cc 20,cc 23],[cc 18,cc 20,cc 33],[cc 18,cc 20,cc 33],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 35],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 20,cc 19],[cc 16,cc 20,cc 37]],
  [[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[cc 22,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 20,cc 33],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 35],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 20,cc 19],[cc 18,cc 20,cc 17]],
  [[cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[],[cc 20,cc 23],[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 17],[cc 20,cc 21],[cc 34,cc 17],[cc 34,cc 17],[cc 32,cc 19],[cc 32,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 19],[cc 20,cc 23],[cc 32,cc 17],[cc 32,cc 17],[cc 34,cc 19],[cc 34,cc 17]],
  [[cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[cc 22,cc 21],[],[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 17],[cc 20,cc 21],[cc 34,cc 17],[cc 34,cc 17],[cc 32,cc 19],[cc 32,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 17],[cc 32,cc 17],[cc 32,cc 17],[cc 34,cc 19],[cc 34,cc 17]],
  [[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 21],[cc 18,cc 21],[],[cc 18,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 32,cc 34,cc 19],[cc 18,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 32,cc 34,cc 17],[cc 16,cc 21],[cc 18,cc 17],[cc 18,cc 19]],
  [[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 20,cc 21],[cc 16,cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 21],[cc 18,cc 21],[cc 20,cc 19],[],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 20,cc 17],[cc 32,cc 34,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 32,cc 34,cc 17],[cc 16,cc 21],[cc 18,cc 17],[cc 18,cc 19]],
  [[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 21],[cc 20,cc 17],[cc 16,cc 21],[],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 32,cc 34,cc 19],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 19],[cc 32,cc 34,cc 17],[cc 16,cc 17],[cc 16,cc 19]],
  [[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 22,cc 21],[cc 16,cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 20,cc 21],[cc 20,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 22,cc 17],[],[cc 16,cc 19],[cc 16,cc 19],[cc 22,cc 17],[cc 32,cc 36,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 32,cc 36,cc 17],[cc 20,cc 17],[cc 20,cc 19]],
  [[cc 16,cc 37],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 33],[cc 16,cc 33],[cc 16,cc 37],[cc 16,cc 37],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 35],[cc 16,cc 35],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[],[cc 18,cc 21],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 34,cc 35]],
  [[cc 16,cc 37],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 33],[cc 16,cc 33],[cc 16,cc 37],[cc 16,cc 37],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 35],[cc 16,cc 35],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 20,cc 19],[],[cc 16,cc 19],[cc 16,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 34,cc 37],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 34,cc 35]],
  [[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 32,cc 18,cc 35],[cc 32,cc 18,cc 35],[cc 18,cc 35],[cc 18,cc 35],[cc 16,cc 17],[cc 16,cc 17],[cc 32,cc 18,cc 33],[cc 32,cc 18,cc 33],[cc 16,cc 21],[cc 16,cc 21],[cc 32,cc 18,cc 33],[cc 16,cc 21],[cc 32,cc 18,cc 35],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 32,cc 18,cc 35],[cc 32,cc 18,cc 35],[cc 16,cc 17],[cc 16,cc 19]],
  [[cc 16,cc 39],[cc 16,cc 37],[cc 16,cc 37],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 16,cc 35],[cc 16,cc 35],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 34,cc 33],[cc 16,cc 33],[cc 16,cc 33],[cc 20,cc 19],[cc 16,cc 34,cc 33],[cc 20,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 17],[cc 16,cc 17],[cc 20,cc 17],[],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 21],[cc 18,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 32,cc 34,cc 17],[cc 16,cc 21],[cc 18,cc 17],[cc 18,cc 19],[],[cc 18,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 32,cc 34,cc 19],[cc 18,cc 21]],
  [[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 21],[cc 18,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 20,cc 21],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 32,cc 34,cc 17],[cc 16,cc 21],[cc 18,cc 17],[cc 18,cc 19],[cc 20,cc 19],[],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 20,cc 17],[cc 32,cc 34,cc 17]],
  [[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 19],[cc 32,cc 34,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 20,cc 17],[cc 16,cc 21],[],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 32,cc 34,cc 19],[cc 16,cc 21]],
  [[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 20,cc 21],[cc 20,cc 21],[cc 20,cc 19],[cc 20,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 22,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 32,cc 36,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 22,cc 17],[],[cc 16,cc 19],[cc 16,cc 19],[cc 22,cc 17],[cc 32,cc 36,cc 17]],
  [[cc 16,cc 39],[cc 16,cc 37],[cc 16,cc 37],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 35],[cc 16,cc 35],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 33],[cc 16,cc 33],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 34,cc 35],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[],[cc 18,cc 21],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 16,cc 39],[cc 16,cc 37],[cc 16,cc 37],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 35],[cc 16,cc 35],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 33],[cc 16,cc 33],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 34,cc 37],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 34,cc 35],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 20,cc 19],[],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 32,cc 18,cc 33],[cc 32,cc 18,cc 33],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 32,cc 18,cc 35],[cc 32,cc 18,cc 35],[cc 18,cc 35],[cc 18,cc 35],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 32,cc 18,cc 35],[cc 32,cc 18,cc 35],[cc 16,cc 17],[cc 16,cc 19],[cc 32,cc 18,cc 33],[cc 16,cc 21],[cc 32,cc 18,cc 35],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[],[cc 16,cc 21]],
  [[cc 16,cc 37],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 34,cc 33],[cc 16,cc 33],[cc 16,cc 33],[cc 16,cc 37],[cc 16,cc 37],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 16,cc 35],[cc 16,cc 35],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 16,cc 34,cc 35],[cc 16,cc 34,cc 35],[cc 16,cc 19],[cc 16,cc 17],[cc 20,cc 19],[cc 16,cc 34,cc 33],[cc 20,cc 17],[cc 16,cc 34,cc 33],[cc 16,cc 17],[cc 16,cc 17],[cc 20,cc 17],[]]]

def cfg : GalCert.Cfg 16 := ⟨adj, (0, 0, 12), 6, regsData, certsData, 0, 12⟩

set_option maxHeartbeats 4000000 in
theorem hc : cfg.check = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem hV : cfg.vbound 28 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

set_option maxHeartbeats 4000000 in
theorem hrec : ∀ k, (([(1, 19), (-1, 18), (1, 17), (-1, 16), (1, 15), (-1, 14), (-1, 13), (1, 12), (-1, 11), (1, 10), (-1, 9), (1, 8)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide) (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem hgfw : ∀ n < 28 + 2 * cfg.L, ((GalCert.csOfS [1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1] 7).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem hsmall : ∀ n < 19, GalCert.conv a [1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1] n = ([1, 3, 5, 8, 9, 12, 11, 12, 6, 10, 1, 5, -2, 2, -1, 0, -1, 0, -1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P311826

open PowerSeries OMA.S_oeis_a311826 in
theorem OMA.solution : type_of% @OMA.S_oeis_a311826.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 19 := ⟨n - 19, by omega⟩
    have h := P311826.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 19 - 1 = k + 18 by omega,
      show k + 19 - 2 = k + 17 by omega,
      show k + 19 - 3 = k + 16 by omega,
      show k + 19 - 4 = k + 15 by omega,
      show k + 19 - 5 = k + 14 by omega,
      show k + 19 - 6 = k + 13 by omega,
      show k + 19 - 7 = k + 12 by omega,
      show k + 19 - 8 = k + 11 by omega,
      show k + 19 - 9 = k + 10 by omega,
      show k + 19 - 10 = k + 9 by omega,
      show k + 19 - 11 = k + 8 by omega,
      P311826.ha (k + 19) (by omega),
      P311826.ha (k + 18) (by omega),
      P311826.ha (k + 17) (by omega),
      P311826.ha (k + 16) (by omega),
      P311826.ha (k + 15) (by omega),
      P311826.ha (k + 14) (by omega),
      P311826.ha (k + 13) (by omega),
      P311826.ha (k + 12) (by omega),
      P311826.ha (k + 11) (by omega),
      P311826.ha (k + 10) (by omega),
      P311826.ha (k + 9) (by omega),
      P311826.ha (k + 8) (by omega)]
    linarith
  · have hD : ((X - 1)^2*(X + 1)*(X^2 - X + 1)^2*(X^2 + X + 1)^2 : PowerSeries ℤ) = GalCert.polyOf [1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (-X^18 - X^16 - X^14 + 2*X^13 - 2*X^12 + 5*X^11 + X^10 + 10*X^9 + 6*X^8 + 12*X^7 + 11*X^6 + 12*X^5 + 9*X^4 + 8*X^3 + 5*X^2 + 3*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 3, 5, 8, 9, 12, 11, 12, 6, 10, 1, 5, -2, 2, -1, 0, -1, 0, -1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from2 P311826.hc P311826.hV a P311826.ha _ _ 7 19 (by decide) (by decide) P311826.hgfw P311826.hsmall
