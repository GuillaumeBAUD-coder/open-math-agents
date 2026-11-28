import OMAStatements.S_oeis_a313321
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A313321.

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


namespace P313321
open OMA.S_oeis_a313321

/-- A packed target code (mixed radix). -/
def tg (n : ℕ) : GalCert.Tgt := ⟨n % 37, n / 37 % 13, n / 481 % 2, n / 962 % 2, n / 1924 % 3, n / 5772 % 2, n / 11544 % 2, n / 23088 % 3, n / 69264⟩

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 13) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 0,
      [[tg 37], [tg 111], [tg 378], [tg 415]],
      [tg 0]⟩,
    ⟨0, 0, 1, 1,
      [[tg 0], [tg 111], [tg 265], [tg 339]],
      [tg 0]⟩,
    ⟨0, 0, 2, 3,
      [[tg 158], [tg 222], [tg 259], [tg 193]],
      [tg 222]⟩,
    ⟨0, 0, 3, 1,
      [[tg 0], [tg 37], [tg 222], [tg 296]],
      [tg 69264]⟩,
    ⟨0, 0, 4, 3,
      [[tg 296], [tg 370], [tg 78], [tg 191]],
      [tg 69560]⟩,
    ⟨0, 0, 5, 5,
      [[tg 160], [tg 76], [tg 333], [tg 407]],
      [tg 69597]⟩,
    ⟨0, 0, 6, 2,
      [[tg 74], [tg 111], [tg 259], [tg 296], [tg 444]],
      [tg 138639]⟩,
    ⟨0, 0, 7, 3,
      [[tg 49], [tg 74], [tg 222], [tg 333], [tg 444]],
      [tg 138750]⟩,
    ⟨0, 0, 8, 2,
      [[tg 111], [tg 148], [tg 222], [tg 370], [tg 444]],
      [tg 207903]⟩,
    ⟨0, 0, 9, 4,
      [[tg 49], [tg 185], [tg 259], [tg 407], [tg 444]],
      [tg 208051]⟩,
    ⟨0, 0, 10, 3,
      [[tg 2], [tg 148], [tg 296], [tg 407], [tg 444]],
      [tg 208088]⟩,
    ⟨0, 0, 11, 4,
      [[tg 2], [tg 185], [tg 333], [tg 370], [tg 444]],
      [tg 208162]⟩,
    ⟨0, 0, 12, 3,
      [[tg 222], [tg 259], [tg 296], [tg 333], [tg 370], [tg 407]],
      [tg 277278]⟩]⟩,
  ⟨1, 0, -1, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, -1, 2)], 0, -1, 2, 1, 0, 0, 0, 0,
   [⟨0, -2, 0, 8,
      [[tg 38, tg 2443], [tg 112, tg 2517], [tg 372, tg 852], [tg 409, tg 889]],
      [tg 372, tg 852]⟩,
    ⟨0, -2, 1, 9,
      [[tg 1, tg 2406], [tg 112, tg 2517], [tg 275, tg 754], [tg 349, tg 828]],
      [tg 1, tg 2406]⟩,
    ⟨0, -2, 2, 10,
      [[tg 184, tg 664], [tg 223, tg 2628], [tg 260, tg 2665], [tg 187, tg 667]],
      [tg 69451, tg 69931]⟩,
    ⟨0, -2, 3, 9,
      [[tg 1, tg 2406], [tg 38, tg 2443], [tg 223, tg 2628], [tg 297, tg 2702]],
      [tg 69265, tg 71670]⟩,
    ⟨0, -2, 4, 11,
      [[tg 297, tg 2702], [tg 371, tg 2776], [tg 88, tg 2493], [tg 201, tg 680]],
      [tg 69561, tg 71966]⟩,
    ⟨0, -2, 5, 13,
      [[tg 183, tg 2588], [tg 1999, tg 4404], [tg 334, tg 2739], [tg 408, tg 2813]],
      [tg 69598, tg 72003]⟩,
    ⟨0, -2, 6, 10,
      [[tg 75, tg 2480], [tg 112, tg 2517], [tg 260, tg 2665], [tg 297, tg 2702], [tg 445, tg 2850]],
      [tg 138640, tg 141045]⟩,
    ⟨0, -2, 7, 11,
      [[tg 72, tg 2477], [tg 75, tg 2480], [tg 223, tg 2628], [tg 334, tg 2739], [tg 445, tg 2850]],
      [tg 138603, tg 141008]⟩,
    ⟨0, -2, 8, 10,
      [[tg 112, tg 2517], [tg 149, tg 2554], [tg 223, tg 2628], [tg 371, tg 2776], [tg 445, tg 2850]],
      [tg 207904, tg 210309]⟩,
    ⟨0, -2, 9, 12,
      [[tg 72, tg 2477], [tg 186, tg 2591], [tg 260, tg 2665], [tg 408, tg 2813], [tg 445, tg 2850]],
      [tg 208052, tg 210457]⟩,
    ⟨0, -2, 10, 11,
      [[tg 1925, tg 4330], [tg 149, tg 2554], [tg 297, tg 2702], [tg 408, tg 2813], [tg 445, tg 2850]],
      [tg 208089, tg 210494]⟩,
    ⟨0, -2, 11, 12,
      [[tg 1925, tg 4330], [tg 186, tg 2591], [tg 334, tg 2739], [tg 371, tg 2776], [tg 445, tg 2850]],
      [tg 208163, tg 210568]⟩,
    ⟨0, -2, 12, 11,
      [[tg 223, tg 2628], [tg 260, tg 2665], [tg 297, tg 2702], [tg 334, tg 2739], [tg 371, tg 2776], [tg 408, tg 2813]],
      [tg 277279, tg 279684]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, -1, 1), (0, 1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, -1, 0, 4,
      [[tg 39], [tg 113], [tg 370], [tg 407]],
      [tg 370]⟩,
    ⟨0, -1, 1, 5,
      [[tg 2], [tg 113], [tg 263], [tg 337]],
      [tg 2]⟩,
    ⟨0, -1, 2, 6,
      [[tg 160], [tg 224], [tg 261], [tg 185]],
      [tg 69449]⟩,
    ⟨0, -1, 3, 5,
      [[tg 2], [tg 39], [tg 224], [tg 298]],
      [tg 69266]⟩,
    ⟨0, -1, 4, 7,
      [[tg 298], [tg 372], [tg 90], [tg 189]],
      [tg 69562]⟩,
    ⟨0, -1, 5, 9,
      [[tg 184], [tg 75], [tg 335], [tg 409]],
      [tg 69599]⟩,
    ⟨0, -1, 6, 6,
      [[tg 76], [tg 113], [tg 261], [tg 298], [tg 446]],
      [tg 138641]⟩,
    ⟨0, -1, 7, 7,
      [[tg 73], [tg 76], [tg 224], [tg 335], [tg 446]],
      [tg 138604]⟩,
    ⟨0, -1, 8, 6,
      [[tg 113], [tg 150], [tg 224], [tg 372], [tg 446]],
      [tg 207905]⟩,
    ⟨0, -1, 9, 8,
      [[tg 73], [tg 187], [tg 261], [tg 409], [tg 446]],
      [tg 208053]⟩,
    ⟨0, -1, 10, 7,
      [[tg 1], [tg 150], [tg 298], [tg 409], [tg 446]],
      [tg 208090]⟩,
    ⟨0, -1, 11, 8,
      [[tg 1], [tg 187], [tg 335], [tg 372], [tg 446]],
      [tg 208164]⟩,
    ⟨0, -1, 12, 7,
      [[tg 224], [tg 261], [tg 298], [tg 335], [tg 372], [tg 409]],
      [tg 277280]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 4)], 1, -1, 4, 2, 0, 0, 0, 0,
   [⟨2, -2, 0, 8,
      [[tg 40, tg 2445], [tg 114, tg 2519], [tg 390, tg 869], [tg 427, tg 906]],
      [tg 427, tg 906]⟩,
    ⟨2, -2, 1, 9,
      [[tg 3, tg 2408], [tg 114, tg 2519], [tg 277, tg 2682], [tg 351, tg 2756]],
      [tg 3, tg 2408]⟩,
    ⟨2, -2, 2, 8,
      [[tg 152, tg 632], [tg 225, tg 2630], [tg 262, tg 2667], [tg 205, tg 684]],
      [tg 138680, tg 139160]⟩,
    ⟨2, -2, 3, 9,
      [[tg 3, tg 2408], [tg 40, tg 2445], [tg 225, tg 2630], [tg 299, tg 2704]],
      [tg 69267, tg 71672]⟩,
    ⟨2, -2, 4, 11,
      [[tg 299, tg 2704], [tg 373, tg 2778], [tg 2001, tg 4406], [tg 203, tg 2608]],
      [tg 69563, tg 71968]⟩,
    ⟨2, -2, 5, 11,
      [[tg 164, tg 644], [tg 89, tg 2494], [tg 336, tg 2741], [tg 410, tg 2815]],
      [tg 69600, tg 72005]⟩,
    ⟨2, -2, 6, 9,
      [[tg 77, tg 2482], [tg 114, tg 2519], [tg 262, tg 2667], [tg 299, tg 2704], [tg 447, tg 2852]],
      [tg 69341, tg 71746]⟩,
    ⟨2, -2, 7, 9,
      [[tg 53, tg 533], [tg 77, tg 2482], [tg 225, tg 2630], [tg 336, tg 2741], [tg 447, tg 2852]],
      [tg 138605, tg 141010]⟩,
    ⟨2, -2, 8, 10,
      [[tg 114, tg 2519], [tg 151, tg 2556], [tg 225, tg 2630], [tg 373, tg 2778], [tg 447, tg 2852]],
      [tg 207906, tg 210311]⟩,
    ⟨2, -2, 9, 10,
      [[tg 53, tg 533], [tg 188, tg 2593], [tg 262, tg 2667], [tg 410, tg 2815], [tg 447, tg 2852]],
      [tg 207845, tg 208325]⟩,
    ⟨2, -2, 10, 11,
      [[tg 15, tg 2420], [tg 151, tg 2556], [tg 299, tg 2704], [tg 410, tg 2815], [tg 447, tg 2852]],
      [tg 208091, tg 210496]⟩,
    ⟨2, -2, 11, 11,
      [[tg 15, tg 2420], [tg 188, tg 2593], [tg 336, tg 2741], [tg 373, tg 2778], [tg 447, tg 2852]],
      [tg 208128, tg 210533]⟩,
    ⟨2, -2, 12, 10,
      [[tg 225, tg 2630], [tg 262, tg 2667], [tg 299, tg 2704], [tg 336, tg 2741], [tg 373, tg 2778], [tg 410, tg 2815]],
      [tg 277281, tg 279686]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 2), (-1, 1, -2)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, -1, 0, 4,
      [[tg 41], [tg 115], [tg 376], [tg 413]],
      [tg 413]⟩,
    ⟨1, -1, 1, 5,
      [[tg 4], [tg 115], [tg 279], [tg 353]],
      [tg 4]⟩,
    ⟨1, -1, 2, 4,
      [[tg 148], [tg 226], [tg 263], [tg 191]],
      [tg 138676]⟩,
    ⟨1, -1, 3, 5,
      [[tg 4], [tg 41], [tg 226], [tg 300]],
      [tg 69268]⟩,
    ⟨1, -1, 4, 7,
      [[tg 300], [tg 374], [tg 77], [tg 205]],
      [tg 69564]⟩,
    ⟨1, -1, 5, 7,
      [[tg 150], [tg 90], [tg 337], [tg 411]],
      [tg 69601]⟩,
    ⟨1, -1, 6, 5,
      [[tg 78], [tg 115], [tg 263], [tg 300], [tg 448]],
      [tg 69342]⟩,
    ⟨1, -1, 7, 5,
      [[tg 39], [tg 78], [tg 226], [tg 337], [tg 448]],
      [tg 138606]⟩,
    ⟨1, -1, 8, 6,
      [[tg 115], [tg 152], [tg 226], [tg 374], [tg 448]],
      [tg 207907]⟩,
    ⟨1, -1, 9, 6,
      [[tg 39], [tg 189], [tg 263], [tg 411], [tg 448]],
      [tg 207831]⟩,
    ⟨1, -1, 10, 7,
      [[tg 16], [tg 152], [tg 300], [tg 411], [tg 448]],
      [tg 208092]⟩,
    ⟨1, -1, 11, 7,
      [[tg 16], [tg 189], [tg 337], [tg 374], [tg 448]],
      [tg 208129]⟩,
    ⟨1, -1, 12, 6,
      [[tg 226], [tg 263], [tg 300], [tg 337], [tg 374], [tg 411]],
      [tg 277282]⟩]⟩,
  ⟨1, 1, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 2)], 1, 0, 2, 1, 0, 0, 0, 0,
   [⟨2, 0, 0, 9,
      [[tg 42, tg 2447], [tg 116, tg 2521], [tg 392, tg 2797], [tg 429, tg 2834]],
      [tg 116, tg 2521]⟩,
    ⟨2, 0, 1, 9,
      [[tg 5, tg 2410], [tg 116, tg 2521], [tg 2188, tg 4593], [tg 2262, tg 4667]],
      [tg 69380, tg 71785]⟩,
    ⟨2, 0, 2, 7,
      [[tg 172, tg 651], [tg 227, tg 2632], [tg 264, tg 2669], [tg 207, tg 2612]],
      [tg 138700, tg 139179]⟩,
    ⟨2, 0, 3, 8,
      [[tg 5, tg 2410], [tg 42, tg 2447], [tg 227, tg 2632], [tg 301, tg 2706]],
      [tg 69491, tg 71896]⟩,
    ⟨2, 0, 4, 9,
      [[tg 301, tg 2706], [tg 375, tg 2780], [tg 93, tg 2498], [tg 2114, tg 4519]],
      [tg 69565, tg 71970]⟩,
    ⟨2, 0, 5, 6,
      [[tg 154, tg 634], [tg 94, tg 574], [tg 338, tg 2743], [tg 412, tg 2817]],
      [tg 207946, tg 208426]⟩,
    ⟨2, 0, 6, 7,
      [[tg 79, tg 2484], [tg 116, tg 2521], [tg 264, tg 2669], [tg 301, tg 2706], [tg 449, tg 2854]],
      [tg 138792, tg 141197]⟩,
    ⟨2, 0, 7, 6,
      [[tg 43, tg 523], [tg 79, tg 2484], [tg 227, tg 2632], [tg 338, tg 2743], [tg 449, tg 2854]],
      [tg 138571, tg 139051]⟩,
    ⟨2, 0, 8, 8,
      [[tg 116, tg 2521], [tg 153, tg 2558], [tg 227, tg 2632], [tg 375, tg 2780], [tg 449, tg 2854]],
      [tg 208019, tg 210424]⟩,
    ⟨2, 0, 9, 6,
      [[tg 43, tg 523], [tg 190, tg 2595], [tg 264, tg 2669], [tg 412, tg 2817], [tg 449, tg 2854]],
      [tg 207835, tg 208315]⟩,
    ⟨2, 0, 10, 8,
      [[tg 20, tg 500], [tg 153, tg 2558], [tg 301, tg 2706], [tg 412, tg 2817], [tg 449, tg 2854]],
      [tg 208204, tg 210609]⟩,
    ⟨2, 0, 11, 7,
      [[tg 20, tg 500], [tg 190, tg 2595], [tg 338, tg 2743], [tg 375, tg 2780], [tg 449, tg 2854]],
      [tg 207982, tg 210387]⟩,
    ⟨2, 0, 12, 7,
      [[tg 227, tg 2632], [tg 264, tg 2669], [tg 301, tg 2706], [tg 338, tg 2743], [tg 375, tg 2780], [tg 412, tg 2817]],
      [tg 277320, tg 279725]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 1), (-1, 0, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, 0, 0, 5,
      [[tg 43], [tg 117], [tg 394], [tg 431]],
      [tg 117]⟩,
    ⟨1, 0, 1, 5,
      [[tg 6], [tg 117], [tg 264], [tg 338]],
      [tg 69381]⟩,
    ⟨1, 0, 2, 3,
      [[tg 156], [tg 228], [tg 265], [tg 209]],
      [tg 138684]⟩,
    ⟨1, 0, 3, 4,
      [[tg 6], [tg 43], [tg 228], [tg 302]],
      [tg 69492]⟩,
    ⟨1, 0, 4, 5,
      [[tg 302], [tg 376], [tg 94], [tg 190]],
      [tg 69566]⟩,
    ⟨1, 0, 5, 3,
      [[tg 148], [tg 78], [tg 339], [tg 413]],
      [tg 69603]⟩,
    ⟨1, 0, 6, 3,
      [[tg 80], [tg 117], [tg 265], [tg 302], [tg 450]],
      [tg 138793]⟩,
    ⟨1, 0, 7, 2,
      [[tg 37], [tg 80], [tg 228], [tg 339], [tg 450]],
      [tg 138565]⟩,
    ⟨1, 0, 8, 4,
      [[tg 117], [tg 154], [tg 228], [tg 376], [tg 450]],
      [tg 208020]⟩,
    ⟨1, 0, 9, 2,
      [[tg 37], [tg 191], [tg 265], [tg 413], [tg 450]],
      [tg 207829]⟩,
    ⟨1, 0, 10, 4,
      [[tg 4], [tg 154], [tg 302], [tg 413], [tg 450]],
      [tg 208205]⟩,
    ⟨1, 0, 11, 3,
      [[tg 4], [tg 191], [tg 339], [tg 376], [tg 450]],
      [tg 208131]⟩,
    ⟨1, 0, 12, 3,
      [[tg 228], [tg 265], [tg 302], [tg 339], [tg 376], [tg 413]],
      [tg 277321]⟩]⟩,
  ⟨1, 0, 1, 0, 0, [(-1, 0, 0), (1, 0, 0), (0, 1, 2)], 0, 1, 2, 1, 0, 0, 0, 0,
   [⟨0, 2, 0, 8,
      [[tg 44, tg 2449], [tg 118, tg 2523], [tg 2301, tg 4706], [tg 2338, tg 4743]],
      [tg 118, tg 2523]⟩,
    ⟨0, 2, 1, 8,
      [[tg 7, tg 2412], [tg 118, tg 2523], [tg 282, tg 2687], [tg 356, tg 2761]],
      [tg 69382, tg 71787]⟩,
    ⟨0, 2, 2, 8,
      [[tg 174, tg 2579], [tg 229, tg 2634], [tg 266, tg 2671], [tg 2116, tg 4521]],
      [tg 229, tg 2634]⟩,
    ⟨0, 2, 3, 7,
      [[tg 7, tg 2412], [tg 44, tg 2449], [tg 229, tg 2634], [tg 303, tg 2708]],
      [tg 303, tg 2708]⟩,
    ⟨0, 2, 4, 6,
      [[tg 303, tg 2708], [tg 377, tg 2782], [tg 98, tg 578], [tg 208, tg 2613]],
      [tg 69641, tg 72046]⟩,
    ⟨0, 2, 5, 5,
      [[tg 176, tg 655], [tg 82, tg 562], [tg 340, tg 2745], [tg 414, tg 2819]],
      [tg 207874, tg 208354]⟩,
    ⟨0, 2, 6, 7,
      [[tg 81, tg 2486], [tg 118, tg 2523], [tg 266, tg 2671], [tg 303, tg 2708], [tg 451, tg 2856]],
      [tg 138831, tg 141236]⟩,
    ⟨0, 2, 7, 7,
      [[tg 65, tg 544], [tg 81, tg 2486], [tg 229, tg 2634], [tg 340, tg 2745], [tg 451, tg 2856]],
      [tg 138868, tg 141273]⟩,
    ⟨0, 2, 8, 6,
      [[tg 118, tg 2523], [tg 155, tg 2560], [tg 229, tg 2634], [tg 377, tg 2782], [tg 451, tg 2856]],
      [tg 138905, tg 141310]⟩,
    ⟨0, 2, 9, 6,
      [[tg 65, tg 544], [tg 192, tg 2597], [tg 266, tg 2671], [tg 414, tg 2819], [tg 451, tg 2856]],
      [tg 138720, tg 141125]⟩,
    ⟨0, 2, 10, 5,
      [[tg 8, tg 488], [tg 155, tg 2560], [tg 303, tg 2708], [tg 414, tg 2819], [tg 451, tg 2856]],
      [tg 138536, tg 139016]⟩,
    ⟨0, 2, 11, 5,
      [[tg 8, tg 488], [tg 192, tg 2597], [tg 340, tg 2745], [tg 377, tg 2782], [tg 451, tg 2856]],
      [tg 207800, tg 208280]⟩,
    ⟨0, 2, 12, 6,
      [[tg 229, tg 2634], [tg 266, tg 2671], [tg 303, tg 2708], [tg 340, tg 2745], [tg 377, tg 2782], [tg 414, tg 2819]],
      [tg 277433, tg 279838]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, 0, 0), (1, 0, 0), (0, 1, 1), (0, -1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 1, 0, 4,
      [[tg 45], [tg 119], [tg 377], [tg 414]],
      [tg 119]⟩,
    ⟨0, 1, 1, 4,
      [[tg 8], [tg 119], [tg 283], [tg 357]],
      [tg 69383]⟩,
    ⟨0, 1, 2, 4,
      [[tg 176], [tg 230], [tg 267], [tg 192]],
      [tg 230]⟩,
    ⟨0, 1, 3, 3,
      [[tg 8], [tg 45], [tg 230], [tg 304]],
      [tg 304]⟩,
    ⟨0, 1, 4, 2,
      [[tg 304], [tg 378], [tg 80], [tg 209]],
      [tg 69642]⟩,
    ⟨0, 1, 5, 2,
      [[tg 158], [tg 74], [tg 341], [tg 415]],
      [tg 69679]⟩,
    ⟨0, 1, 6, 3,
      [[tg 82], [tg 119], [tg 267], [tg 304], [tg 452]],
      [tg 138832]⟩,
    ⟨0, 1, 7, 3,
      [[tg 47], [tg 82], [tg 230], [tg 341], [tg 452]],
      [tg 138869]⟩,
    ⟨0, 1, 8, 2,
      [[tg 119], [tg 156], [tg 230], [tg 378], [tg 452]],
      [tg 138906]⟩,
    ⟨0, 1, 9, 2,
      [[tg 47], [tg 193], [tg 267], [tg 415], [tg 452]],
      [tg 138943]⟩,
    ⟨0, 1, 10, 1,
      [[tg 0], [tg 156], [tg 304], [tg 415], [tg 452]],
      [tg 138528]⟩,
    ⟨0, 1, 11, 1,
      [[tg 0], [tg 193], [tg 341], [tg 378], [tg 452]],
      [tg 207792]⟩,
    ⟨0, 1, 12, 2,
      [[tg 230], [tg 267], [tg 304], [tg 341], [tg 378], [tg 415]],
      [tg 277434]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 4)], -1, 1, 4, 2, 0, 0, 0, 0,
   [⟨-2, 2, 0, 8,
      [[tg 46, tg 2451], [tg 120, tg 2525], [tg 397, tg 2802], [tg 434, tg 2839]],
      [tg 46, tg 2451]⟩,
    ⟨-2, 2, 1, 7,
      [[tg 9, tg 2414], [tg 120, tg 2525], [tg 287, tg 767], [tg 361, tg 841]],
      [tg 361, tg 841]⟩,
    ⟨-2, 2, 2, 10,
      [[tg 2081, tg 4486], [tg 231, tg 2636], [tg 268, tg 2673], [tg 212, tg 2617]],
      [tg 231, tg 2636]⟩,
    ⟨-2, 2, 3, 8,
      [[tg 9, tg 2414], [tg 46, tg 2451], [tg 231, tg 2636], [tg 305, tg 2710]],
      [tg 69310, tg 71715]⟩,
    ⟨-2, 2, 4, 7,
      [[tg 305, tg 2710], [tg 379, tg 2784], [tg 84, tg 564], [tg 213, tg 693]],
      [tg 84, tg 564]⟩,
    ⟨-2, 2, 5, 10,
      [[tg 178, tg 2583], [tg 106, tg 585], [tg 342, tg 2747], [tg 416, tg 2821]],
      [tg 69680, tg 72085]⟩,
    ⟨-2, 2, 6, 9,
      [[tg 83, tg 2488], [tg 120, tg 2525], [tg 268, tg 2673], [tg 305, tg 2710], [tg 453, tg 2858]],
      [tg 138648, tg 141053]⟩,
    ⟨-2, 2, 7, 10,
      [[tg 67, tg 2472], [tg 83, tg 2488], [tg 231, tg 2636], [tg 342, tg 2747], [tg 453, tg 2858]],
      [tg 138759, tg 141164]⟩,
    ⟨-2, 2, 8, 8,
      [[tg 120, tg 2525], [tg 157, tg 2562], [tg 231, tg 2636], [tg 379, tg 2784], [tg 453, tg 2858]],
      [tg 157, tg 2562]⟩,
    ⟨-2, 2, 9, 10,
      [[tg 67, tg 2472], [tg 194, tg 2599], [tg 268, tg 2673], [tg 416, tg 2821], [tg 453, tg 2858]],
      [tg 138944, tg 141349]⟩,
    ⟨-2, 2, 10, 8,
      [[tg 32, tg 511], [tg 157, tg 2562], [tg 305, tg 2710], [tg 416, tg 2821], [tg 453, tg 2858]],
      [tg 69421, tg 71826]⟩,
    ⟨-2, 2, 11, 9,
      [[tg 32, tg 511], [tg 194, tg 2599], [tg 342, tg 2747], [tg 379, tg 2784], [tg 453, tg 2858]],
      [tg 207824, tg 208303]⟩,
    ⟨-2, 2, 12, 9,
      [[tg 231, tg 2636], [tg 268, tg 2673], [tg 305, tg 2710], [tg 342, tg 2747], [tg 379, tg 2784], [tg 416, tg 2821]],
      [tg 277361, tg 279766]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 2), (1, -1, -2)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, 1, 0, 4,
      [[tg 47], [tg 121], [tg 398], [tg 435]],
      [tg 47]⟩,
    ⟨-1, 1, 1, 3,
      [[tg 10], [tg 121], [tg 267], [tg 341]],
      [tg 341]⟩,
    ⟨-1, 1, 2, 6,
      [[tg 157], [tg 232], [tg 269], [tg 213]],
      [tg 232]⟩,
    ⟨-1, 1, 3, 4,
      [[tg 10], [tg 47], [tg 232], [tg 306]],
      [tg 69311]⟩,
    ⟨-1, 1, 4, 3,
      [[tg 306], [tg 380], [tg 74], [tg 193]],
      [tg 193]⟩,
    ⟨-1, 1, 5, 6,
      [[tg 180], [tg 86], [tg 343], [tg 417]],
      [tg 69681]⟩,
    ⟨-1, 1, 6, 5,
      [[tg 84], [tg 121], [tg 269], [tg 306], [tg 454]],
      [tg 138649]⟩,
    ⟨-1, 1, 7, 6,
      [[tg 69], [tg 84], [tg 232], [tg 343], [tg 454]],
      [tg 138760]⟩,
    ⟨-1, 1, 8, 4,
      [[tg 121], [tg 158], [tg 232], [tg 380], [tg 454]],
      [tg 158]⟩,
    ⟨-1, 1, 9, 6,
      [[tg 69], [tg 195], [tg 269], [tg 417], [tg 454]],
      [tg 138945]⟩,
    ⟨-1, 1, 10, 4,
      [[tg 12], [tg 158], [tg 306], [tg 417], [tg 454]],
      [tg 69422]⟩,
    ⟨-1, 1, 11, 5,
      [[tg 12], [tg 195], [tg 343], [tg 380], [tg 454]],
      [tg 208172]⟩,
    ⟨-1, 1, 12, 5,
      [[tg 232], [tg 269], [tg 306], [tg 343], [tg 380], [tg 417]],
      [tg 277362]⟩]⟩,
  ⟨1, -1, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 2)], -1, 0, 2, 1, 0, 0, 0, 0,
   [⟨-2, 0, 0, 9,
      [[tg 48, tg 2453], [tg 122, tg 2527], [tg 402, tg 882], [tg 439, tg 919]],
      [tg 48, tg 2453]⟩,
    ⟨-2, 0, 1, 8,
      [[tg 11, tg 2416], [tg 122, tg 2527], [tg 271, tg 751], [tg 345, tg 825]],
      [tg 271, tg 751]⟩,
    ⟨-2, 0, 2, 11,
      [[tg 179, tg 2584], [tg 233, tg 2638], [tg 270, tg 2675], [tg 217, tg 697]],
      [tg 233, tg 2638]⟩,
    ⟨-2, 0, 3, 9,
      [[tg 11, tg 2416], [tg 48, tg 2453], [tg 233, tg 2638], [tg 307, tg 2712]],
      [tg 69312, tg 71717]⟩,
    ⟨-2, 0, 4, 10,
      [[tg 307, tg 2712], [tg 381, tg 2786], [tg 110, tg 589], [tg 197, tg 677]],
      [tg 197, tg 677]⟩,
    ⟨-2, 0, 5, 13,
      [[tg 2083, tg 4488], [tg 108, tg 2513], [tg 344, tg 2749], [tg 418, tg 2823]],
      [tg 69608, tg 72013]⟩,
    ⟨-2, 0, 6, 10,
      [[tg 85, tg 2490], [tg 122, tg 2527], [tg 270, tg 2675], [tg 307, tg 2712], [tg 455, tg 2860]],
      [tg 138650, tg 141055]⟩,
    ⟨-2, 0, 7, 11,
      [[tg 1972, tg 4377], [tg 85, tg 2490], [tg 233, tg 2638], [tg 344, tg 2749], [tg 455, tg 2860]],
      [tg 138761, tg 141166]⟩,
    ⟨-2, 0, 8, 10,
      [[tg 122, tg 2527], [tg 159, tg 2564], [tg 233, tg 2638], [tg 381, tg 2786], [tg 455, tg 2860]],
      [tg 207914, tg 210319]⟩,
    ⟨-2, 0, 9, 12,
      [[tg 1972, tg 4377], [tg 196, tg 2601], [tg 270, tg 2675], [tg 418, tg 2823], [tg 455, tg 2860]],
      [tg 208062, tg 210467]⟩,
    ⟨-2, 0, 10, 11,
      [[tg 34, tg 2439], [tg 159, tg 2564], [tg 307, tg 2712], [tg 418, tg 2823], [tg 455, tg 2860]],
      [tg 69423, tg 71828]⟩,
    ⟨-2, 0, 11, 12,
      [[tg 34, tg 2439], [tg 196, tg 2601], [tg 344, tg 2749], [tg 381, tg 2786], [tg 455, tg 2860]],
      [tg 208173, tg 210578]⟩,
    ⟨-2, 0, 12, 11,
      [[tg 233, tg 2638], [tg 270, tg 2675], [tg 307, tg 2712], [tg 344, tg 2749], [tg 381, tg 2786], [tg 418, tg 2823]],
      [tg 277289, tg 279694]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 1), (1, 0, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, 0, 0, 5,
      [[tg 49], [tg 123], [tg 380], [tg 417]],
      [tg 49]⟩,
    ⟨-1, 0, 1, 4,
      [[tg 12], [tg 123], [tg 259], [tg 333]],
      [tg 259]⟩,
    ⟨-1, 0, 2, 7,
      [[tg 180], [tg 234], [tg 271], [tg 195]],
      [tg 234]⟩,
    ⟨-1, 0, 3, 5,
      [[tg 12], [tg 49], [tg 234], [tg 308]],
      [tg 69313]⟩,
    ⟨-1, 0, 4, 6,
      [[tg 308], [tg 382], [tg 76], [tg 185]],
      [tg 185]⟩,
    ⟨-1, 0, 5, 9,
      [[tg 159], [tg 110], [tg 345], [tg 419]],
      [tg 69609]⟩,
    ⟨-1, 0, 6, 6,
      [[tg 86], [tg 123], [tg 271], [tg 308], [tg 456]],
      [tg 138651]⟩,
    ⟨-1, 0, 7, 7,
      [[tg 48], [tg 86], [tg 234], [tg 345], [tg 456]],
      [tg 138762]⟩,
    ⟨-1, 0, 8, 6,
      [[tg 123], [tg 160], [tg 234], [tg 382], [tg 456]],
      [tg 207915]⟩,
    ⟨-1, 0, 9, 8,
      [[tg 48], [tg 197], [tg 271], [tg 419], [tg 456]],
      [tg 208063]⟩,
    ⟨-1, 0, 10, 7,
      [[tg 36], [tg 160], [tg 308], [tg 419], [tg 456]],
      [tg 69424]⟩,
    ⟨-1, 0, 11, 8,
      [[tg 36], [tg 197], [tg 345], [tg 382], [tg 456]],
      [tg 208174]⟩,
    ⟨-1, 0, 12, 7,
      [[tg 234], [tg 271], [tg 308], [tg 345], [tg 382], [tg 419]],
      [tg 277290]⟩]⟩,
  ⟨2, 0, -1, 1, -1, [(-1, -1, 2), (1, 0, 2)], -1, -1, 2, 1, 1, 0, 2, 1,
   [⟨2, -4, 0, 16,
      [[tg 50, tg 2455, tg 34682, tg 37087], [tg 124, tg 2529, tg 34756, tg 37161], [tg 385, tg 864, tg 3271, tg 35496], [tg 422, tg 901, tg 3308, tg 35533]],
      [tg 385, tg 864, tg 3271, tg 35496]⟩,
    ⟨2, -4, 1, 17,
      [[tg 13, tg 2418, tg 34645, tg 37050], [tg 124, tg 2529, tg 34756, tg 37161], [tg 2198, tg 23841, tg 5084, tg 58473], [tg 2272, tg 23915, tg 5158, tg 58547]],
      [tg 13, tg 2418, tg 34645, tg 37050]⟩,
    ⟨2, -4, 2, 16,
      [[tg 162, tg 2567, tg 11705, tg 14110], [tg 235, tg 2640, tg 34867, tg 37272], [tg 272, tg 2677, tg 34904, tg 37309], [tg 200, tg 679, tg 3086, tg 35311]],
      [tg 138690, tg 141095, tg 150233, tg 152638]⟩,
    ⟨2, -4, 3, 17,
      [[tg 13, tg 2418, tg 34645, tg 37050], [tg 50, tg 2455, tg 34682, tg 37087], [tg 235, tg 2640, tg 34867, tg 37272], [tg 309, tg 2714, tg 34941, tg 37346]],
      [tg 69277, tg 71682, tg 103909, tg 106314]⟩,
    ⟨2, -4, 4, 19,
      [[tg 309, tg 2714, tg 34941, tg 37346], [tg 383, tg 2788, tg 35015, tg 37420], [tg 23175, tg 25580, tg 57807, tg 60212], [tg 2124, tg 23767, tg 5010, tg 58399]],
      [tg 69573, tg 71978, tg 104205, tg 106610]⟩,
    ⟨2, -4, 5, 19,
      [[tg 2086, tg 4491, tg 13629, tg 16034], [tg 2011, tg 4416, tg 36643, tg 39048], [tg 346, tg 2751, tg 34978, tg 37383], [tg 420, tg 2825, tg 35052, tg 37457]],
      [tg 69610, tg 72015, tg 104242, tg 106647]⟩,
    ⟨2, -4, 6, 17,
      [[tg 87, tg 2492, tg 34719, tg 37124], [tg 124, tg 2529, tg 34756, tg 37161], [tg 272, tg 2677, tg 34904, tg 37309], [tg 309, tg 2714, tg 34941, tg 37346], [tg 457, tg 2862, tg 35089, tg 37494]],
      [tg 69351, tg 71756, tg 103983, tg 106388]⟩,
    ⟨2, -4, 7, 17,
      [[tg 1975, tg 4380, tg 13518, tg 15923], [tg 87, tg 2492, tg 34719, tg 37124], [tg 235, tg 2640, tg 34867, tg 37272], [tg 346, tg 2751, tg 34978, tg 37383], [tg 457, tg 2862, tg 35089, tg 37494]],
      [tg 138615, tg 141020, tg 173247, tg 175652]⟩,
    ⟨2, -4, 8, 18,
      [[tg 124, tg 2529, tg 34756, tg 37161], [tg 161, tg 2566, tg 34793, tg 37198], [tg 235, tg 2640, tg 34867, tg 37272], [tg 383, tg 2788, tg 35015, tg 37420], [tg 457, tg 2862, tg 35089, tg 37494]],
      [tg 207916, tg 210321, tg 242548, tg 244953]⟩,
    ⟨2, -4, 9, 18,
      [[tg 1975, tg 4380, tg 13518, tg 15923], [tg 198, tg 2603, tg 34830, tg 37235], [tg 272, tg 2677, tg 34904, tg 37309], [tg 420, tg 2825, tg 35052, tg 37457], [tg 457, tg 2862, tg 35089, tg 37494]],
      [tg 209767, tg 212172, tg 221310, tg 223715]⟩,
    ⟨2, -4, 10, 19,
      [[tg 1937, tg 4342, tg 36569, tg 38974], [tg 161, tg 2566, tg 34793, tg 37198], [tg 309, tg 2714, tg 34941, tg 37346], [tg 420, tg 2825, tg 35052, tg 37457], [tg 457, tg 2862, tg 35089, tg 37494]],
      [tg 208101, tg 210506, tg 242733, tg 245138]⟩,
    ⟨2, -4, 11, 19,
      [[tg 1937, tg 4342, tg 36569, tg 38974], [tg 198, tg 2603, tg 34830, tg 37235], [tg 346, tg 2751, tg 34978, tg 37383], [tg 383, tg 2788, tg 35015, tg 37420], [tg 457, tg 2862, tg 35089, tg 37494]],
      [tg 208138, tg 210543, tg 242770, tg 245175]⟩,
    ⟨2, -4, 12, 18,
      [[tg 235, tg 2640, tg 34867, tg 37272], [tg 272, tg 2677, tg 34904, tg 37309], [tg 309, tg 2714, tg 34941, tg 37346], [tg 346, tg 2751, tg 34978, tg 37383], [tg 383, tg 2788, tg 35015, tg 37420], [tg 420, tg 2825, tg 35052, tg 37457]],
      [tg 277291, tg 279696, tg 311923, tg 314328]⟩]⟩,
  ⟨1, 0, -1, 0, 0, [(-1, -1, 2), (1, 0, 1), (-1, 0, -1)], -1, -1, 2, 1, 0, 0, 0, 0,
   [⟨1, -3, 0, 12,
      [[tg 51, tg 2456], [tg 125, tg 2530], [tg 386, tg 865], [tg 423, tg 902]],
      [tg 386, tg 865]⟩,
    ⟨1, -3, 1, 13,
      [[tg 14, tg 2419], [tg 125, tg 2530], [tg 274, tg 753], [tg 348, tg 827]],
      [tg 14, tg 2419]⟩,
    ⟨1, -3, 2, 12,
      [[tg 149, tg 2554], [tg 236, tg 2641], [tg 273, tg 2678], [tg 201, tg 680]],
      [tg 138677, tg 141082]⟩,
    ⟨1, -3, 3, 13,
      [[tg 14, tg 2419], [tg 51, tg 2456], [tg 236, tg 2641], [tg 310, tg 2715]],
      [tg 69278, tg 71683]⟩,
    ⟨1, -3, 4, 15,
      [[tg 310, tg 2715], [tg 384, tg 2789], [tg 87, tg 2492], [tg 200, tg 679]],
      [tg 69574, tg 71979]⟩,
    ⟨1, -3, 5, 15,
      [[tg 2073, tg 4478], [tg 2012, tg 4417], [tg 347, tg 2752], [tg 421, tg 2826]],
      [tg 69611, tg 72016]⟩,
    ⟨1, -3, 6, 13,
      [[tg 88, tg 2493], [tg 125, tg 2530], [tg 273, tg 2678], [tg 310, tg 2715], [tg 458, tg 2863]],
      [tg 69352, tg 71757]⟩,
    ⟨1, -3, 7, 13,
      [[tg 1962, tg 4367], [tg 88, tg 2493], [tg 236, tg 2641], [tg 347, tg 2752], [tg 458, tg 2863]],
      [tg 138616, tg 141021]⟩,
    ⟨1, -3, 8, 14,
      [[tg 125, tg 2530], [tg 162, tg 2567], [tg 236, tg 2641], [tg 384, tg 2789], [tg 458, tg 2863]],
      [tg 207917, tg 210322]⟩,
    ⟨1, -3, 9, 14,
      [[tg 1962, tg 4367], [tg 199, tg 2604], [tg 273, tg 2678], [tg 421, tg 2826], [tg 458, tg 2863]],
      [tg 209754, tg 212159]⟩,
    ⟨1, -3, 10, 15,
      [[tg 1938, tg 4343], [tg 162, tg 2567], [tg 310, tg 2715], [tg 421, tg 2826], [tg 458, tg 2863]],
      [tg 208102, tg 210507]⟩,
    ⟨1, -3, 11, 15,
      [[tg 1938, tg 4343], [tg 199, tg 2604], [tg 347, tg 2752], [tg 384, tg 2789], [tg 458, tg 2863]],
      [tg 208139, tg 210544]⟩,
    ⟨1, -3, 12, 14,
      [[tg 236, tg 2641], [tg 273, tg 2678], [tg 310, tg 2715], [tg 347, tg 2752], [tg 384, tg 2789], [tg 421, tg 2826]],
      [tg 277292, tg 279697]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 0, 2), (-1, -1, 1), (1, 1, -1)], 1, 0, 2, 1, 0, 0, 0, 0,
   [⟨2, -3, 0, 12,
      [[tg 52, tg 2457], [tg 126, tg 2531], [tg 373, tg 2778], [tg 410, tg 2815]],
      [tg 373, tg 2778]⟩,
    ⟨2, -3, 1, 13,
      [[tg 15, tg 2420], [tg 126, tg 2531], [tg 2186, tg 4591], [tg 2260, tg 4665]],
      [tg 15, tg 2420]⟩,
    ⟨2, -3, 2, 12,
      [[tg 164, tg 644], [tg 237, tg 2642], [tg 274, tg 2679], [tg 188, tg 2593]],
      [tg 138692, tg 139172]⟩,
    ⟨2, -3, 3, 13,
      [[tg 15, tg 2420], [tg 52, tg 2457], [tg 237, tg 2642], [tg 311, tg 2716]],
      [tg 69279, tg 71684]⟩,
    ⟨2, -3, 4, 15,
      [[tg 311, tg 2716], [tg 385, tg 2790], [tg 2013, tg 4418], [tg 2112, tg 4517]],
      [tg 69575, tg 71980]⟩,
    ⟨2, -3, 5, 15,
      [[tg 162, tg 5933], [tg 87, tg 28947], [tg 348, tg 2753], [tg 422, tg 2827]],
      [tg 69612, tg 72017]⟩,
    ⟨2, -3, 6, 13,
      [[tg 89, tg 2494], [tg 126, tg 2531], [tg 274, tg 2679], [tg 311, tg 2716], [tg 459, tg 2864]],
      [tg 69353, tg 71758]⟩,
    ⟨2, -3, 7, 13,
      [[tg 51, tg 5822], [tg 89, tg 2494], [tg 237, tg 2642], [tg 348, tg 2753], [tg 459, tg 2864]],
      [tg 138617, tg 141022]⟩,
    ⟨2, -3, 8, 14,
      [[tg 126, tg 2531], [tg 163, tg 2568], [tg 237, tg 2642], [tg 385, tg 2790], [tg 459, tg 2864]],
      [tg 207918, tg 210323]⟩,
    ⟨2, -3, 9, 14,
      [[tg 51, tg 5822], [tg 200, tg 2605], [tg 274, tg 2679], [tg 422, tg 2827], [tg 459, tg 2864]],
      [tg 207843, tg 213614]⟩,
    ⟨2, -3, 10, 15,
      [[tg 13, tg 28873], [tg 163, tg 2568], [tg 311, tg 2716], [tg 422, tg 2827], [tg 459, tg 2864]],
      [tg 208103, tg 210508]⟩,
    ⟨2, -3, 11, 15,
      [[tg 13, tg 28873], [tg 200, tg 2605], [tg 348, tg 2753], [tg 385, tg 2790], [tg 459, tg 2864]],
      [tg 208140, tg 210545]⟩,
    ⟨2, -3, 12, 14,
      [[tg 237, tg 2642], [tg 274, tg 2679], [tg 311, tg 2716], [tg 348, tg 2753], [tg 385, tg 2790], [tg 422, tg 2827]],
      [tg 277293, tg 279698]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, -1, 1), (1, 1, -1), (1, 0, 1), (-1, 0, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, -2, 0, 8,
      [[tg 53], [tg 127], [tg 374], [tg 411]],
      [tg 374]⟩,
    ⟨1, -2, 1, 9,
      [[tg 16], [tg 127], [tg 262], [tg 336]],
      [tg 16]⟩,
    ⟨1, -2, 2, 8,
      [[tg 150], [tg 238], [tg 275], [tg 189]],
      [tg 138678]⟩,
    ⟨1, -2, 3, 9,
      [[tg 16], [tg 53], [tg 238], [tg 312]],
      [tg 69280]⟩,
    ⟨1, -2, 4, 11,
      [[tg 312], [tg 386], [tg 89], [tg 188]],
      [tg 69576]⟩,
    ⟨1, -2, 5, 11,
      [[tg 149], [tg 88], [tg 349], [tg 423]],
      [tg 69613]⟩,
    ⟨1, -2, 6, 9,
      [[tg 90], [tg 127], [tg 275], [tg 312], [tg 460]],
      [tg 69354]⟩,
    ⟨1, -2, 7, 9,
      [[tg 38], [tg 90], [tg 238], [tg 349], [tg 460]],
      [tg 138618]⟩,
    ⟨1, -2, 8, 10,
      [[tg 127], [tg 164], [tg 238], [tg 386], [tg 460]],
      [tg 207919]⟩,
    ⟨1, -2, 9, 10,
      [[tg 38], [tg 201], [tg 275], [tg 423], [tg 460]],
      [tg 207830]⟩,
    ⟨1, -2, 10, 11,
      [[tg 14], [tg 164], [tg 312], [tg 423], [tg 460]],
      [tg 208104]⟩,
    ⟨1, -2, 11, 11,
      [[tg 14], [tg 201], [tg 349], [tg 386], [tg 460]],
      [tg 208141]⟩,
    ⟨1, -2, 12, 10,
      [[tg 238], [tg 275], [tg 312], [tg 349], [tg 386], [tg 423]],
      [tg 277294]⟩]⟩,
  ⟨2, 1, -1, 1, 0, [(0, -1, 2), (1, 1, 2)], 0, -1, 2, 1, 1, 1, 2, 1,
   [⟨4, -2, 0, 16,
      [[tg 54, tg 2459, tg 34686, tg 37091], [tg 128, tg 2533, tg 34760, tg 37165], [tg 2313, tg 23956, tg 5199, tg 58588], [tg 2350, tg 23993, tg 5236, tg 58625]],
      [tg 2350, tg 23993, tg 5236, tg 58625]⟩,
    ⟨4, -2, 1, 17,
      [[tg 17, tg 2422, tg 34649, tg 37054], [tg 128, tg 2533, tg 34760, tg 37165], [tg 23364, tg 25769, tg 57996, tg 60401], [tg 23438, tg 25843, tg 58070, tg 60475]],
      [tg 17, tg 2422, tg 34649, tg 37054]⟩,
    ⟨4, -2, 2, 14,
      [[tg 167, tg 646, tg 3053, tg 35278], [tg 239, tg 2644, tg 34871, tg 37276], [tg 276, tg 2681, tg 34908, tg 37313], [tg 2128, tg 23771, tg 5014, tg 58403]],
      [tg 138695, tg 139174, tg 141581, tg 173806]⟩,
    ⟨4, -2, 3, 16,
      [[tg 17, tg 2422, tg 34649, tg 37054], [tg 54, tg 2459, tg 34686, tg 37091], [tg 239, tg 2644, tg 34871, tg 37276], [tg 313, tg 2718, tg 34945, tg 37350]],
      [tg 69503, tg 71908, tg 104135, tg 106540]⟩,
    ⟨4, -2, 4, 17,
      [[tg 313, tg 2718, tg 34945, tg 37350], [tg 387, tg 2792, tg 35019, tg 37424], [tg 2015, tg 4420, tg 36647, tg 39052], [tg 23290, tg 25695, tg 57922, tg 60327]],
      [tg 69577, tg 71982, tg 104209, tg 106614]⟩,
    ⟨4, -2, 5, 14,
      [[tg 166, tg 2571, tg 11709, tg 14114], [tg 2016, tg 4421, tg 13559, tg 15964], [tg 350, tg 2755, tg 34982, tg 37387], [tg 424, tg 2829, tg 35056, tg 37461]],
      [tg 207958, tg 210363, tg 219501, tg 221906]⟩,
    ⟨4, -2, 6, 15,
      [[tg 91, tg 2496, tg 34723, tg 37128], [tg 128, tg 2533, tg 34760, tg 37165], [tg 276, tg 2681, tg 34908, tg 37313], [tg 313, tg 2718, tg 34945, tg 37350], [tg 461, tg 2866, tg 35093, tg 37498]],
      [tg 69355, tg 71760, tg 103987, tg 106392]⟩,
    ⟨4, -2, 7, 14,
      [[tg 55, tg 2460, tg 11598, tg 14003], [tg 91, tg 2496, tg 34723, tg 37128], [tg 239, tg 2644, tg 34871, tg 37276], [tg 350, tg 2755, tg 34982, tg 37387], [tg 461, tg 2866, tg 35093, tg 37498]],
      [tg 138583, tg 140988, tg 150126, tg 152531]⟩,
    ⟨4, -2, 8, 16,
      [[tg 128, tg 2533, tg 34760, tg 37165], [tg 165, tg 2570, tg 34797, tg 37202], [tg 239, tg 2644, tg 34871, tg 37276], [tg 387, tg 2792, tg 35019, tg 37424], [tg 461, tg 2866, tg 35093, tg 37498]],
      [tg 208031, tg 210436, tg 242663, tg 245068]⟩,
    ⟨4, -2, 9, 14,
      [[tg 55, tg 2460, tg 11598, tg 14003], [tg 202, tg 2607, tg 34834, tg 37239], [tg 276, tg 2681, tg 34908, tg 37313], [tg 424, tg 2829, tg 35056, tg 37461], [tg 461, tg 2866, tg 35093, tg 37498]],
      [tg 207847, tg 210252, tg 219390, tg 221795]⟩,
    ⟨4, -2, 10, 16,
      [[tg 1942, tg 4347, tg 13485, tg 15890], [tg 165, tg 2570, tg 34797, tg 37202], [tg 313, tg 2718, tg 34945, tg 37350], [tg 424, tg 2829, tg 35056, tg 37461], [tg 461, tg 2866, tg 35093, tg 37498]],
      [tg 208216, tg 210621, tg 242848, tg 245253]⟩,
    ⟨4, -2, 11, 15,
      [[tg 1942, tg 4347, tg 13485, tg 15890], [tg 202, tg 2607, tg 34834, tg 37239], [tg 350, tg 2755, tg 34982, tg 37387], [tg 387, tg 2792, tg 35019, tg 37424], [tg 461, tg 2866, tg 35093, tg 37498]],
      [tg 207994, tg 210399, tg 242626, tg 245031]⟩,
    ⟨4, -2, 12, 15,
      [[tg 239, tg 2644, tg 34871, tg 37276], [tg 276, tg 2681, tg 34908, tg 37313], [tg 313, tg 2718, tg 34945, tg 37350], [tg 350, tg 2755, tg 34982, tg 37387], [tg 387, tg 2792, tg 35019, tg 37424], [tg 424, tg 2829, tg 35056, tg 37461]],
      [tg 277332, tg 279737, tg 311964, tg 314369]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(0, -1, 2), (1, 1, 1), (-1, -1, -1)], 0, -1, 2, 1, 0, 0, 0, 0,
   [⟨3, -2, 0, 12,
      [[tg 55, tg 2460], [tg 129, tg 2534], [tg 389, tg 868], [tg 426, tg 905]],
      [tg 426, tg 905]⟩,
    ⟨3, -2, 1, 13,
      [[tg 18, tg 2423], [tg 129, tg 2534], [tg 276, tg 2681], [tg 350, tg 2755]],
      [tg 18, tg 2423]⟩,
    ⟨3, -2, 2, 10,
      [[tg 168, tg 647], [tg 240, tg 2645], [tg 277, tg 2682], [tg 204, tg 683]],
      [tg 138696, tg 139175]⟩,
    ⟨3, -2, 3, 12,
      [[tg 18, tg 2423], [tg 55, tg 2460], [tg 240, tg 2645], [tg 314, tg 2719]],
      [tg 69504, tg 71909]⟩,
    ⟨3, -2, 4, 13,
      [[tg 314, tg 2719], [tg 388, tg 2793], [tg 2016, tg 4421], [tg 202, tg 2607]],
      [tg 69578, tg 71983]⟩,
    ⟨3, -2, 5, 11,
      [[tg 151, tg 2556], [tg 2001, tg 4406], [tg 351, tg 2756], [tg 425, tg 2830]],
      [tg 69615, tg 72020]⟩,
    ⟨3, -2, 6, 11,
      [[tg 92, tg 2497], [tg 129, tg 2534], [tg 277, tg 2682], [tg 314, tg 2719], [tg 462, tg 2867]],
      [tg 69356, tg 71761]⟩,
    ⟨3, -2, 7, 10,
      [[tg 40, tg 2445], [tg 92, tg 2497], [tg 240, tg 2645], [tg 351, tg 2756], [tg 462, tg 2867]],
      [tg 138568, tg 140973]⟩,
    ⟨3, -2, 8, 12,
      [[tg 129, tg 2534], [tg 166, tg 2571], [tg 240, tg 2645], [tg 388, tg 2793], [tg 462, tg 2867]],
      [tg 208032, tg 210437]⟩,
    ⟨3, -2, 9, 10,
      [[tg 40, tg 2445], [tg 203, tg 2608], [tg 277, tg 2682], [tg 425, tg 2830], [tg 462, tg 2867]],
      [tg 207832, tg 210237]⟩,
    ⟨3, -2, 10, 12,
      [[tg 1927, tg 4332], [tg 166, tg 2571], [tg 314, tg 2719], [tg 425, tg 2830], [tg 462, tg 2867]],
      [tg 208217, tg 210622]⟩,
    ⟨3, -2, 11, 11,
      [[tg 1927, tg 4332], [tg 203, tg 2608], [tg 351, tg 2756], [tg 388, tg 2793], [tg 462, tg 2867]],
      [tg 208143, tg 210548]⟩,
    ⟨3, -2, 12, 11,
      [[tg 240, tg 2645], [tg 277, tg 2682], [tg 314, tg 2719], [tg 351, tg 2756], [tg 388, tg 2793], [tg 425, tg 2830]],
      [tg 277333, tg 279738]⟩]⟩,
  ⟨1, 1, 0, 0, 0, [(1, 1, 2), (0, -1, 1), (0, 1, -1)], 1, 1, 2, 1, 0, 0, 0, 0,
   [⟨3, -1, 0, 12,
      [[tg 56, tg 2461], [tg 130, tg 2535], [tg 2299, tg 4704], [tg 2336, tg 4741]],
      [tg 2336, tg 4741]⟩,
    ⟨3, -1, 1, 13,
      [[tg 19, tg 2424], [tg 130, tg 2535], [tg 2202, tg 4607], [tg 2276, tg 4681]],
      [tg 19, tg 2424]⟩,
    ⟨3, -1, 2, 10,
      [[tg 153, tg 2558], [tg 241, tg 2646], [tg 278, tg 2683], [tg 2114, tg 4519]],
      [tg 138681, tg 141086]⟩,
    ⟨3, -1, 3, 12,
      [[tg 19, tg 2424], [tg 56, tg 2461], [tg 241, tg 2646], [tg 315, tg 2720]],
      [tg 69505, tg 71910]⟩,
    ⟨3, -1, 4, 13,
      [[tg 315, tg 2720], [tg 389, tg 2794], [tg 91, tg 28951], [tg 2128, tg 4533]],
      [tg 69579, tg 71984]⟩,
    ⟨3, -1, 5, 10,
      [[tg 168, tg 648], [tg 92, tg 5863], [tg 352, tg 2757], [tg 426, tg 2831]],
      [tg 207960, tg 208440]⟩,
    ⟨3, -1, 6, 11,
      [[tg 93, tg 2498], [tg 130, tg 2535], [tg 278, tg 2683], [tg 315, tg 2720], [tg 463, tg 2868]],
      [tg 69357, tg 71762]⟩,
    ⟨3, -1, 7, 10,
      [[tg 57, tg 537], [tg 93, tg 2498], [tg 241, tg 2646], [tg 352, tg 2757], [tg 463, tg 2868]],
      [tg 138585, tg 139065]⟩,
    ⟨3, -1, 8, 12,
      [[tg 130, tg 2535], [tg 167, tg 2572], [tg 241, tg 2646], [tg 389, tg 2794], [tg 463, tg 2868]],
      [tg 208033, tg 210438]⟩,
    ⟨3, -1, 9, 10,
      [[tg 57, tg 537], [tg 204, tg 2609], [tg 278, tg 2683], [tg 426, tg 2831], [tg 463, tg 2868]],
      [tg 207849, tg 208329]⟩,
    ⟨3, -1, 10, 12,
      [[tg 18, tg 5789], [tg 167, tg 2572], [tg 315, tg 2720], [tg 426, tg 2831], [tg 463, tg 2868]],
      [tg 208218, tg 210623]⟩,
    ⟨3, -1, 11, 11,
      [[tg 18, tg 5789], [tg 204, tg 2609], [tg 352, tg 2757], [tg 389, tg 2794], [tg 463, tg 2868]],
      [tg 207996, tg 210401]⟩,
    ⟨3, -1, 12, 11,
      [[tg 241, tg 2646], [tg 278, tg 2683], [tg 315, tg 2720], [tg 352, tg 2757], [tg 389, tg 2794], [tg 426, tg 2831]],
      [tg 277334, tg 279739]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(0, -1, 1), (0, 1, -1), (1, 1, 1), (-1, -1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨2, -1, 0, 8,
      [[tg 57], [tg 131], [tg 375], [tg 412]],
      [tg 412]⟩,
    ⟨2, -1, 1, 9,
      [[tg 20], [tg 131], [tg 278], [tg 352]],
      [tg 20]⟩,
    ⟨2, -1, 2, 6,
      [[tg 154], [tg 242], [tg 279], [tg 190]],
      [tg 138682]⟩,
    ⟨2, -1, 3, 8,
      [[tg 20], [tg 57], [tg 242], [tg 316]],
      [tg 69506]⟩,
    ⟨2, -1, 4, 9,
      [[tg 316], [tg 390], [tg 92], [tg 204]],
      [tg 69580]⟩,
    ⟨2, -1, 5, 7,
      [[tg 152], [tg 77], [tg 353], [tg 427]],
      [tg 69617]⟩,
    ⟨2, -1, 6, 7,
      [[tg 94], [tg 131], [tg 279], [tg 316], [tg 464]],
      [tg 69358]⟩,
    ⟨2, -1, 7, 6,
      [[tg 41], [tg 94], [tg 242], [tg 353], [tg 464]],
      [tg 138569]⟩,
    ⟨2, -1, 8, 8,
      [[tg 131], [tg 168], [tg 242], [tg 390], [tg 464]],
      [tg 208034]⟩,
    ⟨2, -1, 9, 6,
      [[tg 41], [tg 205], [tg 279], [tg 427], [tg 464]],
      [tg 207833]⟩,
    ⟨2, -1, 10, 8,
      [[tg 3], [tg 168], [tg 316], [tg 427], [tg 464]],
      [tg 208219]⟩,
    ⟨2, -1, 11, 7,
      [[tg 3], [tg 205], [tg 353], [tg 390], [tg 464]],
      [tg 208145]⟩,
    ⟨2, -1, 12, 7,
      [[tg 242], [tg 279], [tg 316], [tg 353], [tg 390], [tg 427]],
      [tg 277335]⟩]⟩,
  ⟨2, 1, 0, 0, 1, [(1, 0, 2), (0, 1, 2)], 1, 0, 2, 1, 0, 1, 2, 1,
   [⟨2, 2, 0, 16,
      [[tg 58, tg 2463, tg 34690, tg 37095], [tg 132, tg 2537, tg 34764, tg 37169], [tg 23479, tg 25884, tg 58111, tg 60516], [tg 23516, tg 25921, tg 58148, tg 60553]],
      [tg 132, tg 2537, tg 34764, tg 37169]⟩,
    ⟨2, 2, 1, 16,
      [[tg 21, tg 2426, tg 34653, tg 37058], [tg 132, tg 2537, tg 34764, tg 37169], [tg 2204, tg 4609, tg 36836, tg 39241], [tg 2278, tg 4683, tg 36910, tg 39315]],
      [tg 69396, tg 71801, tg 104028, tg 106433]⟩,
    ⟨2, 2, 2, 14,
      [[tg 2095, tg 23738, tg 4981, tg 58370], [tg 243, tg 2648, tg 34875, tg 37280], [tg 280, tg 2685, tg 34912, tg 37317], [tg 23294, tg 25699, tg 57926, tg 60331]],
      [tg 69544, tg 71949, tg 104176, tg 106581]⟩,
    ⟨2, 2, 3, 15,
      [[tg 21, tg 2426, tg 34653, tg 37058], [tg 58, tg 2463, tg 34690, tg 37095], [tg 243, tg 2648, tg 34875, tg 37280], [tg 317, tg 2722, tg 34949, tg 37354]],
      [tg 69507, tg 71912, tg 104139, tg 106544]⟩,
    ⟨2, 2, 4, 14,
      [[tg 317, tg 2722, tg 34949, tg 37354], [tg 391, tg 2796, tg 35023, tg 37428], [tg 2020, tg 4425, tg 13563, tg 15968], [tg 2130, tg 4535, tg 36762, tg 39167]],
      [tg 69655, tg 72060, tg 104287, tg 106692]⟩,
    ⟨2, 2, 5, 11,
      [[tg 171, tg 650, tg 3057, tg 35282], [tg 96, tg 2501, tg 11639, tg 14044], [tg 354, tg 2759, tg 34986, tg 37391], [tg 428, tg 2833, tg 35060, tg 37465]],
      [tg 207963, tg 208442, tg 210849, tg 243074]⟩,
    ⟨2, 2, 6, 14,
      [[tg 95, tg 2500, tg 34727, tg 37132], [tg 132, tg 2537, tg 34764, tg 37169], [tg 280, tg 2685, tg 34912, tg 37317], [tg 317, tg 2722, tg 34949, tg 37354], [tg 465, tg 2870, tg 35097, tg 37502]],
      [tg 138808, tg 141213, tg 173440, tg 175845]⟩,
    ⟨2, 2, 7, 13,
      [[tg 60, tg 539, tg 2946, tg 35171], [tg 95, tg 2500, tg 34727, tg 37132], [tg 243, tg 2648, tg 34875, tg 37280], [tg 354, tg 2759, tg 34986, tg 37391], [tg 465, tg 2870, tg 35097, tg 37502]],
      [tg 138588, tg 139067, tg 141474, tg 173699]⟩,
    ⟨2, 2, 8, 14,
      [[tg 132, tg 2537, tg 34764, tg 37169], [tg 169, tg 2574, tg 34801, tg 37206], [tg 243, tg 2648, tg 34875, tg 37280], [tg 391, tg 2796, tg 35023, tg 37428], [tg 465, tg 2870, tg 35097, tg 37502]],
      [tg 138919, tg 141324, tg 173551, tg 175956]⟩,
    ⟨2, 2, 9, 12,
      [[tg 60, tg 539, tg 2946, tg 35171], [tg 206, tg 2611, tg 34838, tg 37243], [tg 280, tg 2685, tg 34912, tg 37317], [tg 428, tg 2833, tg 35060, tg 37465], [tg 465, tg 2870, tg 35097, tg 37502]],
      [tg 138734, tg 141139, tg 173366, tg 175771]⟩,
    ⟨2, 2, 10, 13,
      [[tg 22, tg 2427, tg 11565, tg 13970], [tg 169, tg 2574, tg 34801, tg 37206], [tg 317, tg 2722, tg 34949, tg 37354], [tg 428, tg 2833, tg 35060, tg 37465], [tg 465, tg 2870, tg 35097, tg 37502]],
      [tg 138550, tg 140955, tg 150093, tg 152498]⟩,
    ⟨2, 2, 11, 12,
      [[tg 22, tg 2427, tg 11565, tg 13970], [tg 206, tg 2611, tg 34838, tg 37243], [tg 354, tg 2759, tg 34986, tg 37391], [tg 391, tg 2796, tg 35023, tg 37428], [tg 465, tg 2870, tg 35097, tg 37502]],
      [tg 207998, tg 210403, tg 242630, tg 245035]⟩,
    ⟨2, 2, 12, 13,
      [[tg 243, tg 2648, tg 34875, tg 37280], [tg 280, tg 2685, tg 34912, tg 37317], [tg 317, tg 2722, tg 34949, tg 37354], [tg 354, tg 2759, tg 34986, tg 37391], [tg 391, tg 2796, tg 35023, tg 37428], [tg 428, tg 2833, tg 35060, tg 37465]],
      [tg 277410, tg 279815, tg 312042, tg 314447]⟩]⟩,
  ⟨1, 1, 0, 0, 0, [(1, 0, 2), (0, 1, 1), (0, -1, -1)], 1, 0, 2, 1, 0, 0, 0, 0,
   [⟨2, 1, 0, 12,
      [[tg 59, tg 2464], [tg 133, tg 2538], [tg 391, tg 2796], [tg 428, tg 2833]],
      [tg 133, tg 2538]⟩,
    ⟨2, 1, 1, 12,
      [[tg 22, tg 2427], [tg 133, tg 2538], [tg 2205, tg 4610], [tg 2279, tg 4684]],
      [tg 69397, tg 71802]⟩,
    ⟨2, 1, 2, 10,
      [[tg 171, tg 650], [tg 244, tg 2649], [tg 281, tg 2686], [tg 206, tg 2611]],
      [tg 69545, tg 71950]⟩,
    ⟨2, 1, 3, 11,
      [[tg 22, tg 2427], [tg 59, tg 2464], [tg 244, tg 2649], [tg 318, tg 2723]],
      [tg 69508, tg 71913]⟩,
    ⟨2, 1, 4, 10,
      [[tg 318, tg 2723], [tg 392, tg 2797], [tg 2003, tg 4408], [tg 2131, tg 4536]],
      [tg 69656, tg 72061]⟩,
    ⟨2, 1, 5, 7,
      [[tg 172, tg 651], [tg 79, tg 2484], [tg 355, tg 2760], [tg 429, tg 2834]],
      [tg 207964, tg 208443]⟩,
    ⟨2, 1, 6, 10,
      [[tg 96, tg 2501], [tg 133, tg 2538], [tg 281, tg 2686], [tg 318, tg 2723], [tg 466, tg 2871]],
      [tg 138809, tg 141214]⟩,
    ⟨2, 1, 7, 9,
      [[tg 61, tg 540], [tg 96, tg 2501], [tg 244, tg 2649], [tg 355, tg 2760], [tg 466, tg 2871]],
      [tg 138589, tg 139068]⟩,
    ⟨2, 1, 8, 10,
      [[tg 133, tg 2538], [tg 170, tg 2575], [tg 244, tg 2649], [tg 392, tg 2797], [tg 466, tg 2871]],
      [tg 138920, tg 141325]⟩,
    ⟨2, 1, 9, 8,
      [[tg 61, tg 540], [tg 207, tg 2612], [tg 281, tg 2686], [tg 429, tg 2834], [tg 466, tg 2871]],
      [tg 138735, tg 141140]⟩,
    ⟨2, 1, 10, 9,
      [[tg 5, tg 2410], [tg 170, tg 2575], [tg 318, tg 2723], [tg 429, tg 2834], [tg 466, tg 2871]],
      [tg 208221, tg 210626]⟩,
    ⟨2, 1, 11, 8,
      [[tg 5, tg 2410], [tg 207, tg 2612], [tg 355, tg 2760], [tg 392, tg 2797], [tg 466, tg 2871]],
      [tg 207999, tg 210404]⟩,
    ⟨2, 1, 12, 9,
      [[tg 244, tg 2649], [tg 281, tg 2686], [tg 318, tg 2723], [tg 355, tg 2760], [tg 392, tg 2797], [tg 429, tg 2834]],
      [tg 277411, tg 279816]⟩]⟩,
  ⟨1, 0, 1, 0, 0, [(0, 1, 2), (1, 0, 1), (-1, 0, -1)], 0, 1, 2, 1, 0, 0, 0, 0,
   [⟨1, 2, 0, 12,
      [[tg 60, tg 2465], [tg 134, tg 2539], [tg 2317, tg 4722], [tg 2354, tg 4759]],
      [tg 134, tg 2539]⟩,
    ⟨1, 2, 1, 12,
      [[tg 23, tg 2428], [tg 134, tg 2539], [tg 280, tg 29140], [tg 354, tg 29214]],
      [tg 69398, tg 71803]⟩,
    ⟨1, 2, 2, 10,
      [[tg 2079, tg 4484], [tg 245, tg 2650], [tg 282, tg 2687], [tg 2132, tg 4537]],
      [tg 69546, tg 71951]⟩,
    ⟨1, 2, 3, 11,
      [[tg 23, tg 2428], [tg 60, tg 2465], [tg 245, tg 2650], [tg 319, tg 2724]],
      [tg 69509, tg 71914]⟩,
    ⟨1, 2, 4, 10,
      [[tg 319, tg 2724], [tg 393, tg 2798], [tg 96, tg 5867], [tg 206, tg 29066]],
      [tg 69657, tg 72062]⟩,
    ⟨1, 2, 5, 7,
      [[tg 155, tg 2560], [tg 98, tg 578], [tg 356, tg 2761], [tg 430, tg 2835]],
      [tg 207947, tg 210352]⟩,
    ⟨1, 2, 6, 10,
      [[tg 97, tg 2502], [tg 134, tg 2539], [tg 282, tg 2687], [tg 319, tg 2724], [tg 467, tg 2872]],
      [tg 138810, tg 141215]⟩,
    ⟨1, 2, 7, 9,
      [[tg 44, tg 2449], [tg 97, tg 2502], [tg 245, tg 2650], [tg 356, tg 2761], [tg 467, tg 2872]],
      [tg 138572, tg 140977]⟩,
    ⟨1, 2, 8, 10,
      [[tg 134, tg 2539], [tg 171, tg 2576], [tg 245, tg 2650], [tg 393, tg 2798], [tg 467, tg 2872]],
      [tg 138921, tg 141326]⟩,
    ⟨1, 2, 9, 8,
      [[tg 44, tg 2449], [tg 208, tg 2613], [tg 282, tg 2687], [tg 430, tg 2835], [tg 467, tg 2872]],
      [tg 138736, tg 141141]⟩,
    ⟨1, 2, 10, 9,
      [[tg 24, tg 504], [tg 171, tg 2576], [tg 319, tg 2724], [tg 430, tg 2835], [tg 467, tg 2872]],
      [tg 138552, tg 139032]⟩,
    ⟨1, 2, 11, 8,
      [[tg 24, tg 504], [tg 208, tg 2613], [tg 356, tg 2761], [tg 393, tg 2798], [tg 467, tg 2872]],
      [tg 208000, tg 210405]⟩,
    ⟨1, 2, 12, 9,
      [[tg 245, tg 2650], [tg 282, tg 2687], [tg 319, tg 2724], [tg 356, tg 2761], [tg 393, tg 2798], [tg 430, tg 2835]],
      [tg 277412, tg 279817]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 0, 1), (-1, 0, -1), (0, 1, 1), (0, -1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨1, 1, 0, 8,
      [[tg 61], [tg 135], [tg 393], [tg 430]],
      [tg 135]⟩,
    ⟨1, 1, 1, 8,
      [[tg 24], [tg 135], [tg 281], [tg 355]],
      [tg 69399]⟩,
    ⟨1, 1, 2, 6,
      [[tg 155], [tg 246], [tg 283], [tg 208]],
      [tg 69547]⟩,
    ⟨1, 1, 3, 7,
      [[tg 24], [tg 61], [tg 246], [tg 320]],
      [tg 69510]⟩,
    ⟨1, 1, 4, 6,
      [[tg 320], [tg 394], [tg 79], [tg 207]],
      [tg 69658]⟩,
    ⟨1, 1, 5, 3,
      [[tg 156], [tg 80], [tg 357], [tg 431]],
      [tg 207948]⟩,
    ⟨1, 1, 6, 6,
      [[tg 98], [tg 135], [tg 283], [tg 320], [tg 468]],
      [tg 138811]⟩,
    ⟨1, 1, 7, 5,
      [[tg 45], [tg 98], [tg 246], [tg 357], [tg 468]],
      [tg 138573]⟩,
    ⟨1, 1, 8, 6,
      [[tg 135], [tg 172], [tg 246], [tg 394], [tg 468]],
      [tg 138922]⟩,
    ⟨1, 1, 9, 4,
      [[tg 45], [tg 209], [tg 283], [tg 431], [tg 468]],
      [tg 138737]⟩,
    ⟨1, 1, 10, 5,
      [[tg 6], [tg 172], [tg 320], [tg 431], [tg 468]],
      [tg 208223]⟩,
    ⟨1, 1, 11, 4,
      [[tg 6], [tg 209], [tg 357], [tg 394], [tg 468]],
      [tg 208001]⟩,
    ⟨1, 1, 12, 5,
      [[tg 246], [tg 283], [tg 320], [tg 357], [tg 394], [tg 431]],
      [tg 277413]⟩]⟩,
  ⟨2, 0, 1, -1, 1, [(1, 1, 2), (-1, 0, 2)], 1, 1, 2, 1, -1, 0, 2, 1,
   [⟨-2, 4, 0, 16,
      [[tg 62, tg 2467, tg 34694, tg 37099], [tg 136, tg 2541, tg 34768, tg 37173], [tg 2319, tg 4724, tg 36951, tg 39356], [tg 2356, tg 4761, tg 36988, tg 39393]],
      [tg 62, tg 2467, tg 34694, tg 37099]⟩,
    ⟨-2, 4, 1, 15,
      [[tg 25, tg 2430, tg 34657, tg 37062], [tg 136, tg 2541, tg 34768, tg 37173], [tg 2209, tg 4614, tg 13752, tg 16157], [tg 2283, tg 4688, tg 13826, tg 16231]],
      [tg 2283, tg 4688, tg 13826, tg 16231]⟩,
    ⟨-2, 4, 2, 16,
      [[tg 23261, tg 25666, tg 57893, tg 60298], [tg 247, tg 2652, tg 34879, tg 37284], [tg 284, tg 2689, tg 34916, tg 37321], [tg 2134, tg 4539, tg 36766, tg 39171]],
      [tg 247, tg 2652, tg 34879, tg 37284]⟩,
    ⟨-2, 4, 3, 15,
      [[tg 25, tg 2430, tg 34657, tg 37062], [tg 62, tg 2467, tg 34694, tg 37099], [tg 247, tg 2652, tg 34879, tg 37284], [tg 321, tg 2726, tg 34953, tg 37358]],
      [tg 321, tg 2726, tg 34953, tg 37358]⟩,
    ⟨-2, 4, 4, 13,
      [[tg 321, tg 2726, tg 34953, tg 37358], [tg 395, tg 2800, tg 35027, tg 37432], [tg 100, tg 2505, tg 11643, tg 14048], [tg 2135, tg 4540, tg 13678, tg 16083]],
      [tg 100, tg 2505, tg 11643, tg 14048]⟩,
    ⟨-2, 4, 5, 13,
      [[tg 2099, tg 23742, tg 4985, tg 58374], [tg 101, tg 580, tg 2987, tg 35212], [tg 358, tg 2763, tg 34990, tg 37395], [tg 432, tg 2837, tg 35064, tg 37469]],
      [tg 207893, tg 208372, tg 210779, tg 243004]⟩,
    ⟨-2, 4, 6, 15,
      [[tg 99, tg 2504, tg 34731, tg 37136], [tg 136, tg 2541, tg 34768, tg 37173], [tg 284, tg 2689, tg 34916, tg 37321], [tg 321, tg 2726, tg 34953, tg 37358], [tg 469, tg 2874, tg 35101, tg 37506]],
      [tg 138849, tg 141254, tg 173481, tg 175886]⟩,
    ⟨-2, 4, 7, 15,
      [[tg 1988, tg 23631, tg 4874, tg 58263], [tg 99, tg 2504, tg 34731, tg 37136], [tg 247, tg 2652, tg 34879, tg 37284], [tg 358, tg 2763, tg 34990, tg 37395], [tg 469, tg 2874, tg 35101, tg 37506]],
      [tg 138886, tg 141291, tg 173518, tg 175923]⟩,
    ⟨-2, 4, 8, 14,
      [[tg 136, tg 2541, tg 34768, tg 37173], [tg 173, tg 2578, tg 34805, tg 37210], [tg 247, tg 2652, tg 34879, tg 37284], [tg 395, tg 2800, tg 35027, tg 37432], [tg 469, tg 2874, tg 35101, tg 37506]],
      [tg 173, tg 2578, tg 34805, tg 37210]⟩,
    ⟨-2, 4, 9, 14,
      [[tg 1988, tg 23631, tg 4874, tg 58263], [tg 210, tg 2615, tg 34842, tg 37247], [tg 284, tg 2689, tg 34916, tg 37321], [tg 432, tg 2837, tg 35064, tg 37469], [tg 469, tg 2874, tg 35101, tg 37506]],
      [tg 138738, tg 141143, tg 173370, tg 175775]⟩,
    ⟨-2, 4, 10, 13,
      [[tg 27, tg 506, tg 2913, tg 35138], [tg 173, tg 2578, tg 34805, tg 37210], [tg 321, tg 2726, tg 34953, tg 37358], [tg 432, tg 2837, tg 35064, tg 37469], [tg 469, tg 2874, tg 35101, tg 37506]],
      [tg 138555, tg 139034, tg 141441, tg 173666]⟩,
    ⟨-2, 4, 11, 13,
      [[tg 27, tg 506, tg 2913, tg 35138], [tg 210, tg 2615, tg 34842, tg 37247], [tg 358, tg 2763, tg 34990, tg 37395], [tg 395, tg 2800, tg 35027, tg 37432], [tg 469, tg 2874, tg 35101, tg 37506]],
      [tg 207819, tg 208298, tg 210705, tg 242930]⟩,
    ⟨-2, 4, 12, 14,
      [[tg 247, tg 2652, tg 34879, tg 37284], [tg 284, tg 2689, tg 34916, tg 37321], [tg 321, tg 2726, tg 34953, tg 37358], [tg 358, tg 2763, tg 34990, tg 37395], [tg 395, tg 2800, tg 35027, tg 37432], [tg 432, tg 2837, tg 35064, tg 37469]],
      [tg 277451, tg 279856, tg 312083, tg 314488]⟩]⟩,
  ⟨1, 0, 1, 0, 0, [(1, 1, 2), (-1, 0, 1), (1, 0, -1)], 1, 1, 2, 1, 0, 0, 0, 0,
   [⟨-1, 3, 0, 12,
      [[tg 63, tg 2468], [tg 137, tg 2542], [tg 2320, tg 4725], [tg 2357, tg 4762]],
      [tg 63, tg 2468]⟩,
    ⟨-1, 3, 1, 11,
      [[tg 26, tg 2431], [tg 137, tg 2542], [tg 2190, tg 4595], [tg 2264, tg 4669]],
      [tg 2264, tg 4669]⟩,
    ⟨-1, 3, 2, 12,
      [[tg 173, tg 2578], [tg 248, tg 2653], [tg 285, tg 2690], [tg 2135, tg 4540]],
      [tg 248, tg 2653]⟩,
    ⟨-1, 3, 3, 11,
      [[tg 26, tg 2431], [tg 63, tg 2468], [tg 248, tg 2653], [tg 322, tg 2727]],
      [tg 322, tg 2727]⟩,
    ⟨-1, 3, 4, 9,
      [[tg 322, tg 2727], [tg 396, tg 2801], [tg 81, tg 2486], [tg 2116, tg 4521]],
      [tg 81, tg 2486]⟩,
    ⟨-1, 3, 5, 9,
      [[tg 175, tg 654], [tg 102, tg 581], [tg 359, tg 2764], [tg 433, tg 2838]],
      [tg 207894, tg 208373]⟩,
    ⟨-1, 3, 6, 11,
      [[tg 100, tg 2505], [tg 137, tg 2542], [tg 285, tg 2690], [tg 322, tg 2727], [tg 470, tg 2875]],
      [tg 138850, tg 141255]⟩,
    ⟨-1, 3, 7, 11,
      [[tg 64, tg 543], [tg 100, tg 2505], [tg 248, tg 2653], [tg 359, tg 2764], [tg 470, tg 2875]],
      [tg 138887, tg 141292]⟩,
    ⟨-1, 3, 8, 10,
      [[tg 137, tg 2542], [tg 174, tg 2579], [tg 248, tg 2653], [tg 396, tg 2801], [tg 470, tg 2875]],
      [tg 174, tg 2579]⟩,
    ⟨-1, 3, 9, 10,
      [[tg 64, tg 543], [tg 211, tg 2616], [tg 285, tg 2690], [tg 433, tg 2838], [tg 470, tg 2875]],
      [tg 138739, tg 141144]⟩,
    ⟨-1, 3, 10, 9,
      [[tg 28, tg 507], [tg 174, tg 2579], [tg 322, tg 2727], [tg 433, tg 2838], [tg 470, tg 2875]],
      [tg 138556, tg 139035]⟩,
    ⟨-1, 3, 11, 9,
      [[tg 28, tg 507], [tg 211, tg 2616], [tg 359, tg 2764], [tg 396, tg 2801], [tg 470, tg 2875]],
      [tg 207820, tg 208299]⟩,
    ⟨-1, 3, 12, 10,
      [[tg 248, tg 2653], [tg 285, tg 2690], [tg 322, tg 2727], [tg 359, tg 2764], [tg 396, tg 2801], [tg 433, tg 2838]],
      [tg 277452, tg 279857]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, 0, 2), (1, 1, 1), (-1, -1, -1)], -1, 0, 2, 1, 0, 0, 0, 0,
   [⟨-2, 3, 0, 12,
      [[tg 64, tg 2469], [tg 138, tg 2543], [tg 395, tg 29255], [tg 432, tg 29292]],
      [tg 64, tg 2469]⟩,
    ⟨-2, 3, 1, 11,
      [[tg 27, tg 2432], [tg 138, tg 2543], [tg 285, tg 6056], [tg 359, tg 6130]],
      [tg 359, tg 6130]⟩,
    ⟨-2, 3, 2, 12,
      [[tg 2099, tg 4504], [tg 249, tg 2654], [tg 286, tg 2691], [tg 210, tg 29070]],
      [tg 249, tg 2654]⟩,
    ⟨-2, 3, 3, 11,
      [[tg 27, tg 2432], [tg 64, tg 2469], [tg 249, tg 2654], [tg 323, tg 2728]],
      [tg 323, tg 2728]⟩,
    ⟨-2, 3, 4, 9,
      [[tg 323, tg 2728], [tg 397, tg 2802], [tg 102, tg 582], [tg 211, tg 5982]],
      [tg 102, tg 582]⟩,
    ⟨-2, 3, 5, 10,
      [[tg 2081, tg 4486], [tg 83, tg 2488], [tg 360, tg 2765], [tg 434, tg 2839]],
      [tg 69698, tg 72103]⟩,
    ⟨-2, 3, 6, 11,
      [[tg 101, tg 2506], [tg 138, tg 2543], [tg 286, tg 2691], [tg 323, tg 2728], [tg 471, tg 2876]],
      [tg 138851, tg 141256]⟩,
    ⟨-2, 3, 7, 11,
      [[tg 1970, tg 4375], [tg 101, tg 2506], [tg 249, tg 2654], [tg 360, tg 2765], [tg 471, tg 2876]],
      [tg 138888, tg 141293]⟩,
    ⟨-2, 3, 8, 10,
      [[tg 138, tg 2543], [tg 175, tg 2580], [tg 249, tg 2654], [tg 397, tg 2802], [tg 471, tg 2876]],
      [tg 175, tg 2580]⟩,
    ⟨-2, 3, 9, 10,
      [[tg 1970, tg 4375], [tg 212, tg 2617], [tg 286, tg 2691], [tg 434, tg 2839], [tg 471, tg 2876]],
      [tg 138962, tg 141367]⟩,
    ⟨-2, 3, 10, 9,
      [[tg 9, tg 2414], [tg 175, tg 2580], [tg 323, tg 2728], [tg 434, tg 2839], [tg 471, tg 2876]],
      [tg 138537, tg 140942]⟩,
    ⟨-2, 3, 11, 9,
      [[tg 9, tg 2414], [tg 212, tg 2617], [tg 360, tg 2765], [tg 397, tg 2802], [tg 471, tg 2876]],
      [tg 207801, tg 210206]⟩,
    ⟨-2, 3, 12, 10,
      [[tg 249, tg 2654], [tg 286, tg 2691], [tg 323, tg 2728], [tg 360, tg 2765], [tg 397, tg 2802], [tg 434, tg 2839]],
      [tg 277453, tg 279858]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(1, 1, 1), (-1, -1, -1), (-1, 0, 1), (1, 0, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, 2, 0, 8,
      [[tg 65], [tg 139], [tg 396], [tg 433]],
      [tg 65]⟩,
    ⟨-1, 2, 1, 7,
      [[tg 28], [tg 139], [tg 266], [tg 340]],
      [tg 340]⟩,
    ⟨-1, 2, 2, 8,
      [[tg 175], [tg 250], [tg 287], [tg 211]],
      [tg 250]⟩,
    ⟨-1, 2, 3, 7,
      [[tg 28], [tg 65], [tg 250], [tg 324]],
      [tg 324]⟩,
    ⟨-1, 2, 4, 5,
      [[tg 324], [tg 398], [tg 82], [tg 192]],
      [tg 82]⟩,
    ⟨-1, 2, 5, 6,
      [[tg 157], [tg 84], [tg 361], [tg 435]],
      [tg 69699]⟩,
    ⟨-1, 2, 6, 7,
      [[tg 102], [tg 139], [tg 287], [tg 324], [tg 472]],
      [tg 138852]⟩,
    ⟨-1, 2, 7, 7,
      [[tg 46], [tg 102], [tg 250], [tg 361], [tg 472]],
      [tg 138889]⟩,
    ⟨-1, 2, 8, 6,
      [[tg 139], [tg 176], [tg 250], [tg 398], [tg 472]],
      [tg 176]⟩,
    ⟨-1, 2, 9, 6,
      [[tg 46], [tg 213], [tg 287], [tg 435], [tg 472]],
      [tg 138963]⟩,
    ⟨-1, 2, 10, 5,
      [[tg 10], [tg 176], [tg 324], [tg 435], [tg 472]],
      [tg 138538]⟩,
    ⟨-1, 2, 11, 5,
      [[tg 10], [tg 213], [tg 361], [tg 398], [tg 472]],
      [tg 207802]⟩,
    ⟨-1, 2, 12, 6,
      [[tg 250], [tg 287], [tg 324], [tg 361], [tg 398], [tg 435]],
      [tg 277454]⟩]⟩,
  ⟨2, -1, 1, -1, 0, [(0, 1, 2), (-1, -1, 2)], 0, 1, 2, 1, -1, -1, 2, 1,
   [⟨-4, 2, 0, 16,
      [[tg 66, tg 2471, tg 34698, tg 37103], [tg 140, tg 2545, tg 34772, tg 37177], [tg 2324, tg 4729, tg 13867, tg 16272], [tg 2361, tg 4766, tg 13904, tg 16309]],
      [tg 66, tg 2471, tg 34698, tg 37103]⟩,
    ⟨-4, 2, 1, 15,
      [[tg 29, tg 2434, tg 34661, tg 37066], [tg 140, tg 2545, tg 34772, tg 37177], [tg 289, tg 2694, tg 11832, tg 14237], [tg 363, tg 2768, tg 11906, tg 14311]],
      [tg 289, tg 2694, tg 11832, tg 14237]⟩,
    ⟨-4, 2, 2, 18,
      [[tg 2101, tg 4506, tg 36733, tg 39138], [tg 251, tg 2656, tg 34883, tg 37288], [tg 288, tg 2693, tg 34920, tg 37325], [tg 2139, tg 4544, tg 13682, tg 16087]],
      [tg 251, tg 2656, tg 34883, tg 37288]⟩,
    ⟨-4, 2, 3, 16,
      [[tg 29, tg 2434, tg 34661, tg 37066], [tg 66, tg 2471, tg 34698, tg 37103], [tg 251, tg 2656, tg 34883, tg 37288], [tg 325, tg 2730, tg 34957, tg 37362]],
      [tg 69330, tg 71735, tg 103962, tg 106367]⟩,
    ⟨-4, 2, 4, 15,
      [[tg 325, tg 2730, tg 34957, tg 37362], [tg 399, tg 2804, tg 35031, tg 37436], [tg 105, tg 584, tg 2991, tg 35216], [tg 215, tg 2620, tg 11758, tg 14163]],
      [tg 105, tg 584, tg 2991, tg 35216]⟩,
    ⟨-4, 2, 5, 18,
      [[tg 23265, tg 25670, tg 57897, tg 60302], [tg 2029, tg 23672, tg 4915, tg 58304], [tg 362, tg 2767, tg 34994, tg 37399], [tg 436, tg 2841, tg 35068, tg 37473]],
      [tg 69700, tg 72105, tg 104332, tg 106737]⟩,
    ⟨-4, 2, 6, 17,
      [[tg 103, tg 2508, tg 34735, tg 37140], [tg 140, tg 2545, tg 34772, tg 37177], [tg 288, tg 2693, tg 34920, tg 37325], [tg 325, tg 2730, tg 34957, tg 37362], [tg 473, tg 2878, tg 35105, tg 37510]],
      [tg 138668, tg 141073, tg 173300, tg 175705]⟩,
    ⟨-4, 2, 7, 18,
      [[tg 23154, tg 25559, tg 57786, tg 60191], [tg 103, tg 2508, tg 34735, tg 37140], [tg 251, tg 2656, tg 34883, tg 37288], [tg 362, tg 2767, tg 34994, tg 37399], [tg 473, tg 2878, tg 35105, tg 37510]],
      [tg 138779, tg 141184, tg 173411, tg 175816]⟩,
    ⟨-4, 2, 8, 16,
      [[tg 140, tg 2545, tg 34772, tg 37177], [tg 177, tg 2582, tg 34809, tg 37214], [tg 251, tg 2656, tg 34883, tg 37288], [tg 399, tg 2804, tg 35031, tg 37436], [tg 473, tg 2878, tg 35105, tg 37510]],
      [tg 177, tg 2582, tg 34809, tg 37214]⟩,
    ⟨-4, 2, 9, 18,
      [[tg 23154, tg 25559, tg 57786, tg 60191], [tg 214, tg 2619, tg 34846, tg 37251], [tg 288, tg 2693, tg 34920, tg 37325], [tg 436, tg 2841, tg 35068, tg 37473], [tg 473, tg 2878, tg 35105, tg 37510]],
      [tg 138964, tg 141369, tg 173596, tg 176001]⟩,
    ⟨-4, 2, 10, 16,
      [[tg 1955, tg 23598, tg 4841, tg 58230], [tg 177, tg 2582, tg 34809, tg 37214], [tg 325, tg 2730, tg 34957, tg 37362], [tg 436, tg 2841, tg 35068, tg 37473], [tg 473, tg 2878, tg 35105, tg 37510]],
      [tg 69441, tg 71846, tg 104073, tg 106478]⟩,
    ⟨-4, 2, 11, 17,
      [[tg 1955, tg 23598, tg 4841, tg 58230], [tg 214, tg 2619, tg 34846, tg 37251], [tg 362, tg 2767, tg 34994, tg 37399], [tg 399, tg 2804, tg 35031, tg 37436], [tg 473, tg 2878, tg 35105, tg 37510]],
      [tg 209747, tg 231390, tg 212633, tg 266022]⟩,
    ⟨-4, 2, 12, 17,
      [[tg 251, tg 2656, tg 34883, tg 37288], [tg 288, tg 2693, tg 34920, tg 37325], [tg 325, tg 2730, tg 34957, tg 37362], [tg 362, tg 2767, tg 34994, tg 37399], [tg 399, tg 2804, tg 35031, tg 37436], [tg 436, tg 2841, tg 35068, tg 37473]],
      [tg 277381, tg 279786, tg 312013, tg 314418]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(0, 1, 2), (-1, -1, 1), (1, 1, -1)], 0, 1, 2, 1, 0, 0, 0, 0,
   [⟨-3, 2, 0, 12,
      [[tg 67, tg 2472], [tg 141, tg 2546], [tg 2303, tg 4708], [tg 2340, tg 4745]],
      [tg 67, tg 2472]⟩,
    ⟨-3, 2, 1, 11,
      [[tg 30, tg 2435], [tg 141, tg 2546], [tg 268, tg 2673], [tg 342, tg 2747]],
      [tg 268, tg 2673]⟩,
    ⟨-3, 2, 2, 14,
      [[tg 2102, tg 4507], [tg 252, tg 2657], [tg 289, tg 2694], [tg 2118, tg 4523]],
      [tg 252, tg 2657]⟩,
    ⟨-3, 2, 3, 12,
      [[tg 30, tg 2435], [tg 67, tg 2472], [tg 252, tg 2657], [tg 326, tg 2731]],
      [tg 69331, tg 71736]⟩,
    ⟨-3, 2, 4, 11,
      [[tg 326, tg 2731], [tg 400, tg 2805], [tg 106, tg 585], [tg 194, tg 2599]],
      [tg 106, tg 585]⟩,
    ⟨-3, 2, 5, 14,
      [[tg 177, tg 2582], [tg 105, tg 584], [tg 363, tg 2768], [tg 437, tg 2842]],
      [tg 69701, tg 72106]⟩,
    ⟨-3, 2, 6, 13,
      [[tg 104, tg 2509], [tg 141, tg 2546], [tg 289, tg 2694], [tg 326, tg 2731], [tg 474, tg 2879]],
      [tg 138669, tg 141074]⟩,
    ⟨-3, 2, 7, 14,
      [[tg 66, tg 2471], [tg 104, tg 2509], [tg 252, tg 2657], [tg 363, tg 2768], [tg 474, tg 2879]],
      [tg 138780, tg 141185]⟩,
    ⟨-3, 2, 8, 12,
      [[tg 141, tg 2546], [tg 178, tg 2583], [tg 252, tg 2657], [tg 400, tg 2805], [tg 474, tg 2879]],
      [tg 178, tg 2583]⟩,
    ⟨-3, 2, 9, 14,
      [[tg 66, tg 2471], [tg 215, tg 2620], [tg 289, tg 2694], [tg 437, tg 2842], [tg 474, tg 2879]],
      [tg 138965, tg 141370]⟩,
    ⟨-3, 2, 10, 12,
      [[tg 31, tg 510], [tg 178, tg 2583], [tg 326, tg 2731], [tg 437, tg 2842], [tg 474, tg 2879]],
      [tg 69442, tg 71847]⟩,
    ⟨-3, 2, 11, 13,
      [[tg 31, tg 510], [tg 215, tg 2620], [tg 363, tg 2768], [tg 400, tg 2805], [tg 474, tg 2879]],
      [tg 207823, tg 208302]⟩,
    ⟨-3, 2, 12, 13,
      [[tg 252, tg 2657], [tg 289, tg 2694], [tg 326, tg 2731], [tg 363, tg 2768], [tg 400, tg 2805], [tg 437, tg 2842]],
      [tg 277382, tg 279787]⟩]⟩,
  ⟨1, -1, 0, 0, 0, [(-1, -1, 2), (0, 1, 1), (0, -1, -1)], -1, -1, 2, 1, 0, 0, 0, 0,
   [⟨-3, 1, 0, 12,
      [[tg 68, tg 2473], [tg 142, tg 2547], [tg 400, tg 6171], [tg 437, tg 6208]],
      [tg 68, tg 2473]⟩,
    ⟨-3, 1, 1, 11,
      [[tg 31, tg 2436], [tg 142, tg 2547], [tg 291, tg 771], [tg 365, tg 845]],
      [tg 291, tg 771]⟩,
    ⟨-3, 1, 2, 14,
      [[tg 177, tg 29037], [tg 253, tg 2658], [tg 290, tg 2695], [tg 215, tg 5986]],
      [tg 253, tg 2658]⟩,
    ⟨-3, 1, 3, 12,
      [[tg 31, tg 2436], [tg 68, tg 2473], [tg 253, tg 2658], [tg 327, tg 2732]],
      [tg 69332, tg 71737]⟩,
    ⟨-3, 1, 4, 11,
      [[tg 327, tg 2732], [tg 401, tg 2806], [tg 85, tg 2490], [tg 217, tg 697]],
      [tg 217, tg 697]⟩,
    ⟨-3, 1, 5, 14,
      [[tg 2103, tg 4508], [tg 2009, tg 4414], [tg 364, tg 2769], [tg 438, tg 2843]],
      [tg 69702, tg 72107]⟩,
    ⟨-3, 1, 6, 13,
      [[tg 105, tg 2510], [tg 142, tg 2547], [tg 290, tg 2695], [tg 327, tg 2732], [tg 475, tg 2880]],
      [tg 138670, tg 141075]⟩,
    ⟨-3, 1, 7, 14,
      [[tg 1992, tg 4397], [tg 105, tg 2510], [tg 253, tg 2658], [tg 364, tg 2769], [tg 475, tg 2880]],
      [tg 138781, tg 141186]⟩,
    ⟨-3, 1, 8, 12,
      [[tg 142, tg 2547], [tg 179, tg 2584], [tg 253, tg 2658], [tg 401, tg 2806], [tg 475, tg 2880]],
      [tg 179, tg 2584]⟩,
    ⟨-3, 1, 9, 14,
      [[tg 1992, tg 4397], [tg 216, tg 2621], [tg 290, tg 2695], [tg 438, tg 2843], [tg 475, tg 2880]],
      [tg 138966, tg 141371]⟩,
    ⟨-3, 1, 10, 12,
      [[tg 1935, tg 4340], [tg 179, tg 2584], [tg 327, tg 2732], [tg 438, tg 2843], [tg 475, tg 2880]],
      [tg 69443, tg 71848]⟩,
    ⟨-3, 1, 11, 13,
      [[tg 1935, tg 4340], [tg 216, tg 2621], [tg 364, tg 2769], [tg 401, tg 2806], [tg 475, tg 2880]],
      [tg 208193, tg 210598]⟩,
    ⟨-3, 1, 12, 13,
      [[tg 253, tg 2658], [tg 290, tg 2695], [tg 327, tg 2732], [tg 364, tg 2769], [tg 401, tg 2806], [tg 438, tg 2843]],
      [tg 277383, tg 279788]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(0, 1, 1), (0, -1, -1), (-1, -1, 1), (1, 1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-2, 1, 0, 8,
      [[tg 69], [tg 143], [tg 379], [tg 416]],
      [tg 69]⟩,
    ⟨-2, 1, 1, 7,
      [[tg 32], [tg 143], [tg 269], [tg 343]],
      [tg 269]⟩,
    ⟨-2, 1, 2, 10,
      [[tg 178], [tg 254], [tg 291], [tg 194]],
      [tg 254]⟩,
    ⟨-2, 1, 3, 8,
      [[tg 32], [tg 69], [tg 254], [tg 328]],
      [tg 69333]⟩,
    ⟨-2, 1, 4, 7,
      [[tg 328], [tg 402], [tg 86], [tg 195]],
      [tg 195]⟩,
    ⟨-2, 1, 5, 10,
      [[tg 179], [tg 85], [tg 365], [tg 439]],
      [tg 69703]⟩,
    ⟨-2, 1, 6, 9,
      [[tg 106], [tg 143], [tg 291], [tg 328], [tg 476]],
      [tg 138671]⟩,
    ⟨-2, 1, 7, 10,
      [[tg 68], [tg 106], [tg 254], [tg 365], [tg 476]],
      [tg 138782]⟩,
    ⟨-2, 1, 8, 8,
      [[tg 143], [tg 180], [tg 254], [tg 402], [tg 476]],
      [tg 180]⟩,
    ⟨-2, 1, 9, 10,
      [[tg 68], [tg 217], [tg 291], [tg 439], [tg 476]],
      [tg 138967]⟩,
    ⟨-2, 1, 10, 8,
      [[tg 11], [tg 180], [tg 328], [tg 439], [tg 476]],
      [tg 69444]⟩,
    ⟨-2, 1, 11, 9,
      [[tg 11], [tg 217], [tg 365], [tg 402], [tg 476]],
      [tg 208194]⟩,
    ⟨-2, 1, 12, 9,
      [[tg 254], [tg 291], [tg 328], [tg 365], [tg 402], [tg 439]],
      [tg 277384]⟩]⟩,
  ⟨2, -1, 0, 0, -1, [(-1, 0, 2), (0, -1, 2)], -1, 0, 2, 1, 0, -1, 2, 1,
   [⟨-2, -2, 0, 16,
      [[tg 70, tg 2475, tg 34702, tg 37107], [tg 144, tg 2549, tg 34776, tg 37181], [tg 404, tg 2809, tg 11947, tg 14352], [tg 441, tg 2846, tg 11984, tg 14389]],
      [tg 404, tg 2809, tg 11947, tg 14352]⟩,
    ⟨-2, -2, 1, 16,
      [[tg 33, tg 2438, tg 34665, tg 37070], [tg 144, tg 2549, tg 34776, tg 37181], [tg 294, tg 773, tg 3180, tg 35405], [tg 368, tg 847, tg 3254, tg 35479]],
      [tg 294, tg 773, tg 3180, tg 35405]⟩,
    ⟨-2, -2, 2, 18,
      [[tg 2106, tg 4511, tg 13649, tg 16054], [tg 255, tg 2660, tg 34887, tg 37292], [tg 292, tg 2697, tg 34924, tg 37329], [tg 219, tg 2624, tg 11762, tg 14167]],
      [tg 69483, tg 71888, tg 81026, tg 83431]⟩,
    ⟨-2, -2, 3, 17,
      [[tg 33, tg 2438, tg 34665, tg 37070], [tg 70, tg 2475, tg 34702, tg 37107], [tg 255, tg 2660, tg 34887, tg 37292], [tg 329, tg 2734, tg 34961, tg 37366]],
      [tg 69297, tg 71702, tg 103929, tg 106334]⟩,
    ⟨-2, -2, 4, 18,
      [[tg 329, tg 2734, tg 34961, tg 37366], [tg 403, tg 2808, tg 35035, tg 37440], [tg 2033, tg 23676, tg 4919, tg 58308], [tg 220, tg 699, tg 3106, tg 35331]],
      [tg 220, tg 699, tg 3106, tg 35331]⟩,
    ⟨-2, -2, 5, 21,
      [[tg 2105, tg 4510, tg 36737, tg 39142], [tg 23195, tg 25600, tg 57827, tg 60232], [tg 366, tg 2771, tg 34998, tg 37403], [tg 440, tg 2845, tg 35072, tg 37477]],
      [tg 69630, tg 72035, tg 104262, tg 106667]⟩,
    ⟨-2, -2, 6, 18,
      [[tg 107, tg 2512, tg 34739, tg 37144], [tg 144, tg 2549, tg 34776, tg 37181], [tg 292, tg 2697, tg 34924, tg 37329], [tg 329, tg 2734, tg 34961, tg 37366], [tg 477, tg 2882, tg 35109, tg 37514]],
      [tg 138672, tg 141077, tg 173304, tg 175709]⟩,
    ⟨-2, -2, 7, 19,
      [[tg 1994, tg 4399, tg 36626, tg 39031], [tg 107, tg 2512, tg 34739, tg 37144], [tg 255, tg 2660, tg 34887, tg 37292], [tg 366, tg 2771, tg 34998, tg 37403], [tg 477, tg 2882, tg 35109, tg 37514]],
      [tg 138635, tg 141040, tg 173267, tg 175672]⟩,
    ⟨-2, -2, 8, 18,
      [[tg 144, tg 2549, tg 34776, tg 37181], [tg 181, tg 2586, tg 34813, tg 37218], [tg 255, tg 2660, tg 34887, tg 37292], [tg 403, tg 2808, tg 35035, tg 37440], [tg 477, tg 2882, tg 35109, tg 37514]],
      [tg 207936, tg 210341, tg 242568, tg 244973]⟩,
    ⟨-2, -2, 9, 20,
      [[tg 1994, tg 4399, tg 36626, tg 39031], [tg 218, tg 2623, tg 34850, tg 37255], [tg 292, tg 2697, tg 34924, tg 37329], [tg 440, tg 2845, tg 35072, tg 37477], [tg 477, tg 2882, tg 35109, tg 37514]],
      [tg 208084, tg 210489, tg 242716, tg 245121]⟩,
    ⟨-2, -2, 10, 19,
      [[tg 23121, tg 25526, tg 57753, tg 60158], [tg 181, tg 2586, tg 34813, tg 37218], [tg 329, tg 2734, tg 34961, tg 37366], [tg 440, tg 2845, tg 35072, tg 37477], [tg 477, tg 2882, tg 35109, tg 37514]],
      [tg 69445, tg 71850, tg 104077, tg 106482]⟩,
    ⟨-2, -2, 11, 20,
      [[tg 23121, tg 25526, tg 57753, tg 60158], [tg 218, tg 2623, tg 34850, tg 37255], [tg 366, tg 2771, tg 34998, tg 37403], [tg 403, tg 2808, tg 35035, tg 37440], [tg 477, tg 2882, tg 35109, tg 37514]],
      [tg 208195, tg 210600, tg 242827, tg 245232]⟩,
    ⟨-2, -2, 12, 19,
      [[tg 255, tg 2660, tg 34887, tg 37292], [tg 292, tg 2697, tg 34924, tg 37329], [tg 329, tg 2734, tg 34961, tg 37366], [tg 366, tg 2771, tg 34998, tg 37403], [tg 403, tg 2808, tg 35035, tg 37440], [tg 440, tg 2845, tg 35072, tg 37477]],
      [tg 277311, tg 279716, tg 311943, tg 314348]⟩]⟩,
  ⟨1, -1, 0, 0, 0, [(-1, 0, 2), (0, -1, 1), (0, 1, -1)], -1, 0, 2, 1, 0, 0, 0, 0,
   [⟨-2, -1, 0, 12,
      [[tg 71, tg 2476], [tg 145, tg 2550], [tg 381, tg 2786], [tg 418, tg 2823]],
      [tg 381, tg 2786]⟩,
    ⟨-2, -1, 1, 12,
      [[tg 34, tg 2439], [tg 145, tg 2550], [tg 295, tg 774], [tg 369, tg 848]],
      [tg 295, tg 774]⟩,
    ⟨-2, -1, 2, 14,
      [[tg 2083, tg 4488], [tg 256, tg 2661], [tg 293, tg 2698], [tg 196, tg 2601]],
      [tg 69460, tg 71865]⟩,
    ⟨-2, -1, 3, 13,
      [[tg 34, tg 2439], [tg 71, tg 2476], [tg 256, tg 2661], [tg 330, tg 2735]],
      [tg 69298, tg 71703]⟩,
    ⟨-2, -1, 4, 14,
      [[tg 330, tg 2735], [tg 404, tg 2809], [tg 109, tg 588], [tg 221, tg 700]],
      [tg 221, tg 700]⟩,
    ⟨-2, -1, 5, 17,
      [[tg 2106, tg 4511], [tg 107, tg 2512], [tg 367, tg 2772], [tg 441, tg 2846]],
      [tg 69631, tg 72036]⟩,
    ⟨-2, -1, 6, 14,
      [[tg 108, tg 2513], [tg 145, tg 2550], [tg 293, tg 2698], [tg 330, tg 2735], [tg 478, tg 2883]],
      [tg 138673, tg 141078]⟩,
    ⟨-2, -1, 7, 15,
      [[tg 1995, tg 4400], [tg 108, tg 2513], [tg 256, tg 2661], [tg 367, tg 2772], [tg 478, tg 2883]],
      [tg 138636, tg 141041]⟩,
    ⟨-2, -1, 8, 14,
      [[tg 145, tg 2550], [tg 182, tg 2587], [tg 256, tg 2661], [tg 404, tg 2809], [tg 478, tg 2883]],
      [tg 207937, tg 210342]⟩,
    ⟨-2, -1, 9, 16,
      [[tg 1995, tg 4400], [tg 219, tg 2624], [tg 293, tg 2698], [tg 441, tg 2846], [tg 478, tg 2883]],
      [tg 208085, tg 210490]⟩,
    ⟨-2, -1, 10, 15,
      [[tg 33, tg 2438], [tg 182, tg 2587], [tg 330, tg 2735], [tg 441, tg 2846], [tg 478, tg 2883]],
      [tg 69446, tg 71851]⟩,
    ⟨-2, -1, 11, 16,
      [[tg 33, tg 2438], [tg 219, tg 2624], [tg 367, tg 2772], [tg 404, tg 2809], [tg 478, tg 2883]],
      [tg 208196, tg 210601]⟩,
    ⟨-2, -1, 12, 15,
      [[tg 256, tg 2661], [tg 293, tg 2698], [tg 330, tg 2735], [tg 367, tg 2772], [tg 404, tg 2809], [tg 441, tg 2846]],
      [tg 277312, tg 279717]⟩]⟩,
  ⟨1, 0, -1, 0, 0, [(0, -1, 2), (-1, 0, 1), (1, 0, -1)], 0, -1, 2, 1, 0, 0, 0, 0,
   [⟨-1, -2, 0, 12,
      [[tg 72, tg 2477], [tg 146, tg 2551], [tg 406, tg 886], [tg 443, tg 923]],
      [tg 406, tg 886]⟩,
    ⟨-1, -2, 1, 12,
      [[tg 35, tg 2440], [tg 146, tg 2551], [tg 260, tg 2665], [tg 334, tg 2739]],
      [tg 260, tg 2665]⟩,
    ⟨-1, -2, 2, 14,
      [[tg 182, tg 5953], [tg 257, tg 2662], [tg 294, tg 2699], [tg 221, tg 701]],
      [tg 69485, tg 69965]⟩,
    ⟨-1, -2, 3, 13,
      [[tg 35, tg 2440], [tg 72, tg 2477], [tg 257, tg 2662], [tg 331, tg 2736]],
      [tg 69299, tg 71704]⟩,
    ⟨-1, -2, 4, 14,
      [[tg 331, tg 2736], [tg 405, tg 2810], [tg 1999, tg 4404], [tg 186, tg 2591]],
      [tg 186, tg 2591]⟩,
    ⟨-1, -2, 5, 17,
      [[tg 181, tg 29041], [tg 2033, tg 4438], [tg 368, tg 2773], [tg 442, tg 2847]],
      [tg 69632, tg 72037]⟩,
    ⟨-1, -2, 6, 14,
      [[tg 109, tg 2514], [tg 146, tg 2551], [tg 294, tg 2699], [tg 331, tg 2736], [tg 479, tg 2884]],
      [tg 138674, tg 141079]⟩,
    ⟨-1, -2, 7, 15,
      [[tg 70, tg 28930], [tg 109, tg 2514], [tg 257, tg 2662], [tg 368, tg 2773], [tg 479, tg 2884]],
      [tg 138637, tg 141042]⟩,
    ⟨-1, -2, 8, 14,
      [[tg 146, tg 2551], [tg 183, tg 2588], [tg 257, tg 2662], [tg 405, tg 2810], [tg 479, tg 2884]],
      [tg 207938, tg 210343]⟩,
    ⟨-1, -2, 9, 16,
      [[tg 70, tg 28930], [tg 220, tg 2625], [tg 294, tg 2699], [tg 442, tg 2847], [tg 479, tg 2884]],
      [tg 208086, tg 210491]⟩,
    ⟨-1, -2, 10, 15,
      [[tg 1959, tg 4364], [tg 183, tg 2588], [tg 331, tg 2736], [tg 442, tg 2847], [tg 479, tg 2884]],
      [tg 69447, tg 71852]⟩,
    ⟨-1, -2, 11, 16,
      [[tg 1959, tg 4364], [tg 220, tg 2625], [tg 368, tg 2773], [tg 405, tg 2810], [tg 479, tg 2884]],
      [tg 208197, tg 210602]⟩,
    ⟨-1, -2, 12, 15,
      [[tg 257, tg 2662], [tg 294, tg 2699], [tg 331, tg 2736], [tg 368, tg 2773], [tg 405, tg 2810], [tg 442, tg 2847]],
      [tg 277313, tg 279718]⟩]⟩,
  ⟨0, 0, 0, 0, 0, [(-1, 0, 1), (1, 0, -1), (0, -1, 1), (0, 1, -1)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨-1, -1, 0, 8,
      [[tg 73], [tg 147], [tg 382], [tg 419]],
      [tg 382]⟩,
    ⟨-1, -1, 1, 8,
      [[tg 36], [tg 147], [tg 261], [tg 335]],
      [tg 261]⟩,
    ⟨-1, -1, 2, 10,
      [[tg 159], [tg 258], [tg 295], [tg 197]],
      [tg 69461]⟩,
    ⟨-1, -1, 3, 9,
      [[tg 36], [tg 73], [tg 258], [tg 332]],
      [tg 69300]⟩,
    ⟨-1, -1, 4, 10,
      [[tg 332], [tg 406], [tg 75], [tg 187]],
      [tg 187]⟩,
    ⟨-1, -1, 5, 13,
      [[tg 182], [tg 109], [tg 369], [tg 443]],
      [tg 69633]⟩,
    ⟨-1, -1, 6, 10,
      [[tg 110], [tg 147], [tg 295], [tg 332], [tg 480]],
      [tg 138675]⟩,
    ⟨-1, -1, 7, 11,
      [[tg 71], [tg 110], [tg 258], [tg 369], [tg 480]],
      [tg 138638]⟩,
    ⟨-1, -1, 8, 10,
      [[tg 147], [tg 184], [tg 258], [tg 406], [tg 480]],
      [tg 207939]⟩,
    ⟨-1, -1, 9, 12,
      [[tg 71], [tg 221], [tg 295], [tg 443], [tg 480]],
      [tg 208087]⟩,
    ⟨-1, -1, 10, 11,
      [[tg 35], [tg 184], [tg 332], [tg 443], [tg 480]],
      [tg 69448]⟩,
    ⟨-1, -1, 11, 12,
      [[tg 35], [tg 221], [tg 369], [tg 406], [tg 480]],
      [tg 208198]⟩,
    ⟨-1, -1, 12, 11,
      [[tg 258], [tg 295], [tg 332], [tg 369], [tg 406], [tg 443]],
      [tg 277314]⟩]⟩]

/-- A packed certificate entry: side bit, test index, coefficient. -/
def cc (n : ℕ) : Bool × ℕ × ℕ := (n % 2 == 1, n / 2 % 8, n / 16)

set_option maxRecDepth 100000 in
def certsData : List (List (List (Bool × ℕ × ℕ))) := [
  [[],[cc 20,cc 21],[cc 20,cc 21],[cc 18,cc 20,cc 21],[cc 18,cc 20,cc 21],[cc 18,cc 21],[cc 18,cc 21],[cc 22,cc 21],[cc 22,cc 21],[cc 16,cc 22,cc 21],[cc 16,cc 22,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 22,cc 17],[cc 22,cc 17],[cc 22,cc 19],[cc 22,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 20,cc 21],[],[cc 20,cc 23],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 19],[cc 18,cc 20,cc 19],[cc 20,cc 21],[cc 20,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 20,cc 21],[cc 22,cc 21],[],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 22,cc 17],[cc 22,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[],[cc 20,cc 23],[cc 18,cc 20,cc 33],[cc 16,cc 20,cc 39],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 37],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 35],[cc 18,cc 20,cc 35],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 35],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 33]],
  [[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[cc 22,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 37],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 35],[cc 18,cc 20,cc 35],[cc 18,cc 20,cc 33],[cc 18,cc 20,cc 37],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 33]],
  [[cc 20,cc 19],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[],[cc 20,cc 23],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 19],[cc 20,cc 23],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 17],[cc 20,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21]],
  [[cc 20,cc 19],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[cc 22,cc 21],[],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 20,cc 21],[cc 22,cc 19],[cc 16,cc 20,cc 17],[cc 22,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 17],[cc 20,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21]],
  [[cc 20,cc 23],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[],[cc 20,cc 23],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 19],[cc 18,cc 20,cc 19],[cc 20,cc 21],[cc 20,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17]],
  [[cc 20,cc 23],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 22,cc 21],[],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 22,cc 17],[cc 22,cc 17],[cc 18,cc 20,cc 17],[cc 18,cc 20,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17]],
  [[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[],[cc 20,cc 23],[cc 18,cc 20,cc 33],[cc 16,cc 20,cc 39],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 33],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 35],[cc 18,cc 20,cc 35],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 35]],
  [[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 37],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 35],[cc 22,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 20,cc 33],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 33],[cc 16,cc 20,cc 35],[cc 16,cc 20,cc 33],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 20,cc 35],[cc 18,cc 20,cc 35],[cc 18,cc 20,cc 33],[cc 18,cc 20,cc 37]],
  [[cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[],[cc 20,cc 23],[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 17],[cc 20,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 19],[cc 20,cc 23],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21]],
  [[cc 20,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[cc 22,cc 21],[],[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 17],[cc 20,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 22,cc 19],[cc 16,cc 20,cc 17],[cc 22,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21]],
  [[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 18,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 21],[cc 18,cc 21],[],[cc 18,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17]],
  [[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 20,cc 21],[cc 16,cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 21],[cc 18,cc 21],[cc 20,cc 19],[],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17]],
  [[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 23],[cc 16,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 21],[cc 20,cc 17],[cc 16,cc 21],[],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 19],[cc 16,cc 18,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 22,cc 21],[cc 16,cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 20,cc 21],[cc 20,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 22,cc 17],[],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 22,cc 17],[cc 22,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 16,cc 20,cc 17],[cc 18,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17]],
  [[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[],[cc 18,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23]],
  [[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 20,cc 19],[],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23]],
  [[cc 18,cc 21],[cc 20,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 20,cc 17],[cc 16,cc 21],[],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 19],[cc 16,cc 18,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17]],
  [[cc 16,cc 21],[cc 18,cc 21],[cc 16,cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 22,cc 17],[],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 22,cc 17],[cc 22,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 16,cc 20,cc 17],[cc 18,cc 17],[cc 16,cc 20,cc 17]],
  [[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 23],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[],[cc 18,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 23],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 20,cc 19],[],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 16,cc 23],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 17],[cc 16,cc 23],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 20,cc 19],[cc 16,cc 18,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 20,cc 17],[cc 16,cc 21],[],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21]],
  [[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[cc 18,cc 21],[cc 20,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 19],[cc 16,cc 20,cc 17],[cc 18,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 22,cc 17],[],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 22,cc 17],[cc 22,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17]],
  [[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 21],[cc 18,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 18,cc 23],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[],[cc 18,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 21],[cc 18,cc 19]],
  [[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 21],[cc 18,cc 21],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 20,cc 21],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 20,cc 19],[],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 21]],
  [[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 23],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 19],[cc 16,cc 18,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 20,cc 17],[cc 16,cc 21],[],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 19]],
  [[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 20,cc 21],[cc 20,cc 21],[cc 20,cc 19],[cc 20,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 22,cc 21],[cc 16,cc 20,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 16,cc 20,cc 17],[cc 18,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 22,cc 17],[],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 22,cc 17],[cc 22,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 21]],
  [[cc 16,cc 23],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[],[cc 18,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21]],
  [[cc 16,cc 23],[cc 16,cc 21],[cc 16,cc 21],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 20,cc 19],[],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21]],
  [[cc 18,cc 23],[cc 18,cc 21],[cc 18,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 18,cc 19],[cc 20,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 17],[cc 18,cc 17],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 19],[cc 16,cc 18,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 20,cc 17],[cc 16,cc 21],[],[cc 16,cc 23],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21]],
  [[cc 16,cc 23],[cc 16,cc 21],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 21],[cc 16,cc 20,cc 19],[cc 20,cc 19],[cc 20,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 22,cc 17],[cc 22,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 16,cc 20,cc 17],[cc 18,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 22,cc 17],[],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21]],
  [[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 23],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[],[cc 18,cc 21],[cc 16,cc 21],[cc 16,cc 19]],
  [[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 18,cc 19],[cc 16,cc 23],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 23],[cc 18,cc 17],[cc 18,cc 17],[cc 18,cc 19],[cc 18,cc 17],[cc 20,cc 19],[],[cc 16,cc 21],[cc 16,cc 19]],
  [[cc 16,cc 21],[cc 18,cc 17],[cc 16,cc 23],[cc 16,cc 18,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 18,cc 19],[cc 18,cc 19],[cc 18,cc 17],[cc 18,cc 21],[cc 16,cc 18,cc 19],[cc 16,cc 18,cc 19],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 20,cc 19],[cc 16,cc 18,cc 17],[cc 20,cc 17],[cc 16,cc 18,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 20,cc 17],[cc 16,cc 21],[],[cc 16,cc 23]],
  [[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 21],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 20,cc 19],[cc 16,cc 20,cc 19],[cc 18,cc 21],[cc 20,cc 19],[cc 16,cc 19],[cc 16,cc 19],[cc 16,cc 17],[cc 16,cc 21],[cc 22,cc 17],[cc 22,cc 17],[cc 16,cc 20,cc 17],[cc 16,cc 20,cc 21],[cc 16,cc 17],[cc 16,cc 17],[cc 16,cc 19],[cc 16,cc 17],[cc 18,cc 19],[cc 16,cc 20,cc 17],[cc 18,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 17],[cc 20,cc 19],[cc 20,cc 17],[cc 18,cc 17],[cc 18,cc 17],[cc 22,cc 17],[]]]

def cfg : GalCert.Cfg 13 := ⟨adj, (0, 0, 0), 4, regsData, certsData, 0, 0⟩

theorem hc : cfg.check = true := by decide +kernel

theorem hV : cfg.vbound 21 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

theorem hrec : ∀ k, (([(1, 10), (-2, 6), (1, 2)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide) (by decide +kernel)

theorem hgfw : ∀ n < 21 + 2 * cfg.L, ((GalCert.csOfS [1, 0, 0, 0, -2, 0, 0, 0, 1] 1).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

theorem hsmall : ∀ n < 10, GalCert.conv a [1, 0, 0, 0, -2, 0, 0, 0, 1] n = ([1, 4, 9, 16, 16, 16, 13, 2, 3, -2] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P313321

open PowerSeries OMA.S_oeis_a313321 in
theorem OMA.solution : type_of% @OMA.S_oeis_a313321.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have h := P313321.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 10 - 4 = k + 6 by omega,
      show k + 10 - 8 = k + 2 by omega,
      P313321.ha (k + 10) (by omega),
      P313321.ha (k + 6) (by omega),
      P313321.ha (k + 2) (by omega)]
    linarith
  · have hD : (X^8 - 2*X^4 + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 0, 0, 0, -2, 0, 0, 0, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : (-2*X^9 + 3*X^8 + 2*X^7 + 13*X^6 + 16*X^5 + 16*X^4 + 16*X^3 + 9*X^2 + 4*X + 1 : PowerSeries ℤ) = GalCert.polyOf [1, 4, 9, 16, 16, 16, 13, 2, 3, -2] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from2 P313321.hc P313321.hV a P313321.ha _ _ 1 10 (by decide) (by decide) P313321.hgfw P313321.hsmall
