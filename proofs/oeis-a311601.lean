import OMAStatements.S_oeis_a311601
import Mathlib

/-!
Proof of the conjectured recurrence and generating function for A311601.

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


namespace P311601
open OMA.S_oeis_a311601

/-- A packed target code (mixed radix). -/
def tg (n : ℕ) : GalCert.Tgt := ⟨n % 13, n / 13 % 100, n / 1300 % 2, n / 2600 % 2, n / 5200 % 3, n / 15600 % 2, n / 31200 % 2, n / 62400 % 3, n / 187200⟩

set_option maxRecDepth 100000 in
def regsData : List (GalCert.Region 10) := [
  ⟨0, 0, 0, 0, 0, [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)], 0, 0, 0, 0, 0, 0, 0, 0,
   [⟨0, 0, 0, 0,
      [[tg 6], [tg 163], [tg 13], [tg 3]],
      [tg 0]⟩,
    ⟨0, 0, 1, 1,
      [[tg 19], [tg 0], [tg 39], [tg 16]],
      [tg 374400]⟩,
    ⟨0, 0, 2, 9,
      [[tg 32], [tg 52], [tg 10], [tg 29]],
      [tg 187252]⟩,
    ⟨0, 0, 3, 2,
      [[tg 45], [tg 13], [tg 65], [tg 42]],
      [tg 374413]⟩,
    ⟨0, 0, 4, 8,
      [[tg 58], [tg 26], [tg 78], [tg 55]],
      [tg 374478]⟩,
    ⟨0, 0, 5, 3,
      [[tg 71], [tg 97], [tg 39], [tg 91], [tg 68]],
      [tg 374439]⟩,
    ⟨0, 0, 6, 7,
      [[tg 84], [tg 110], [tg 52], [tg 104], [tg 81]],
      [tg 561710]⟩,
    ⟨0, 0, 7, 4,
      [[tg 97], [tg 65], [tg 117], [tg 68], [tg 94]],
      [tg 561665]⟩,
    ⟨0, 0, 8, 6,
      [[tg 110], [tg 78], [tg 117], [tg 81], [tg 107]],
      [tg 374517]⟩,
    ⟨0, 0, 9, 5,
      [[tg 123], [tg 91], [tg 104], [tg 120]],
      [tg 374491]⟩]⟩,
  ⟨1, -1, -1, 0, 0, [(1, -1, 0), (-1, 1, 0), (-1, -1, 2)], -1, -1, 2, 2, 0, 0, 0, 0,
   [⟨-1, -1, 0, 10,
      [[tg 1182, tg 79182], [tg 5363, tg 11863], [tg 14, tg 6514], [tg 137, tg 6637]],
      [tg 187214, tg 193714]⟩,
    ⟨-1, -1, 1, 9,
      [[tg 1195, tg 79195], [tg 1, tg 6501], [tg 40, tg 6540], [tg 150, tg 6650]],
      [tg 187240, tg 193740]⟩,
    ⟨-1, -1, 2, 2,
      [[tg 1208, tg 79208], [tg 53, tg 6553], [tg 6, tg 16782], [tg 163, tg 6663]],
      [tg 187206, tg 203982]⟩,
    ⟨-1, -1, 3, 8,
      [[tg 1221, tg 79221], [tg 14, tg 6514], [tg 66, tg 6566], [tg 176, tg 6676]],
      [tg 374466, tg 380966]⟩,
    ⟨-1, -1, 4, 3,
      [[tg 1234, tg 79234], [tg 27, tg 6527], [tg 79, tg 6579], [tg 189, tg 6689]],
      [tg 187227, tg 193727]⟩,
    ⟨-1, -1, 5, 7,
      [[tg 1247, tg 79247], [tg 1273, tg 79273], [tg 40, tg 6540], [tg 92, tg 6592], [tg 202, tg 6702]],
      [tg 187292, tg 193792]⟩,
    ⟨-1, -1, 6, 4,
      [[tg 1260, tg 79260], [tg 1286, tg 79286], [tg 53, tg 6553], [tg 105, tg 6605], [tg 215, tg 6715]],
      [tg 374453, tg 380953]⟩,
    ⟨-1, -1, 7, 6,
      [[tg 1273, tg 79273], [tg 66, tg 6566], [tg 118, tg 6618], [tg 202, tg 6702], [tg 228, tg 6728]],
      [tg 187318, tg 193818]⟩,
    ⟨-1, -1, 8, 4,
      [[tg 1286, tg 79286], [tg 79, tg 6579], [tg 118, tg 6618], [tg 215, tg 6715], [tg 241, tg 6741]],
      [tg 187415, tg 193915]⟩,
    ⟨-1, -1, 9, 5,
      [[tg 1299, tg 79299], [tg 92, tg 6592], [tg 105, tg 6605], [tg 254, tg 6754]],
      [tg 374505, tg 381005]⟩]⟩,
  ⟨1, 1, -1, 0, 0, [(1, 1, 0), (-1, -1, 0), (1, -1, 2)], 1, -1, 2, 2, 0, 0, 0, 0,
   [⟨1, -1, 0, 10,
      [[tg 137, tg 78137], [tg 62563, tg 140563], [tg 15, tg 6515], [tg 8, tg 6508]],
      [tg 187215, tg 193715]⟩,
    ⟨1, -1, 1, 9,
      [[tg 150, tg 78150], [tg 2, tg 6502], [tg 41, tg 6541], [tg 21, tg 6521]],
      [tg 187241, tg 193741]⟩,
    ⟨1, -1, 2, 2,
      [[tg 163, tg 78163], [tg 54, tg 6554], [tg 3, tg 1308], [tg 34, tg 6534]],
      [tg 561763, tg 639763]⟩,
    ⟨1, -1, 3, 8,
      [[tg 176, tg 78176], [tg 15, tg 6515], [tg 67, tg 6567], [tg 47, tg 6547]],
      [tg 374467, tg 380967]⟩,
    ⟨1, -1, 4, 3,
      [[tg 189, tg 78189], [tg 28, tg 6528], [tg 80, tg 6580], [tg 60, tg 6560]],
      [tg 561789, tg 639789]⟩,
    ⟨1, -1, 5, 7,
      [[tg 202, tg 78202], [tg 228, tg 78228], [tg 41, tg 6541], [tg 93, tg 6593], [tg 73, tg 6573]],
      [tg 561828, tg 639828]⟩,
    ⟨1, -1, 6, 4,
      [[tg 215, tg 78215], [tg 241, tg 78241], [tg 54, tg 6554], [tg 106, tg 6606], [tg 86, tg 6586]],
      [tg 749015, tg 827015]⟩,
    ⟨1, -1, 7, 7,
      [[tg 228, tg 78228], [tg 67, tg 6567], [tg 119, tg 6619], [tg 73, tg 6573], [tg 99, tg 6599]],
      [tg 749028, tg 827028]⟩,
    ⟨1, -1, 8, 5,
      [[tg 241, tg 78241], [tg 80, tg 6580], [tg 119, tg 6619], [tg 86, tg 6586], [tg 112, tg 6612]],
      [tg 749041, tg 827041]⟩,
    ⟨1, -1, 9, 6,
      [[tg 254, tg 78254], [tg 93, tg 6593], [tg 106, tg 6606], [tg 125, tg 6625]],
      [tg 561854, tg 639854]⟩]⟩,
  ⟨1, 10, 0, 0, 0, [(0, 1, 0), (0, -1, 0), (1, 0, 1)], 1, 0, 1, 10, 0, 0, 0, 0,
   [⟨1, 0, 0, 1,
      [[tg 0, tg 2473], [tg 28, tg 16804], [tg 16, tg 6516], [tg 133, tg 6633]],
      [tg 561600, tg 564073]⟩,
    ⟨1, 0, 1, 2,
      [[tg 13, tg 2486], [tg 3, tg 6503], [tg 42, tg 6542], [tg 146, tg 6646]],
      [tg 561613, tg 564086]⟩,
    ⟨1, 0, 2, 9,
      [[tg 26, tg 2499], [tg 55, tg 6555], [tg 4, tg 2479], [tg 159, tg 6659]],
      [tg 187255, tg 564099]⟩,
    ⟨1, 0, 3, 3,
      [[tg 39, tg 2512], [tg 16, tg 6516], [tg 68, tg 6568], [tg 172, tg 6672]],
      [tg 561639, tg 564112]⟩,
    ⟨1, 0, 4, 8,
      [[tg 52, tg 2525], [tg 29, tg 6529], [tg 81, tg 6581], [tg 185, tg 6685]],
      [tg 374481, tg 564125]⟩,
    ⟨1, 0, 5, 4,
      [[tg 65, tg 2538], [tg 91, tg 2564], [tg 42, tg 6542], [tg 94, tg 6594], [tg 198, tg 6698]],
      [tg 748865, tg 751338]⟩,
    ⟨1, 0, 6, 7,
      [[tg 78, tg 2551], [tg 104, tg 2577], [tg 55, tg 6555], [tg 107, tg 6607], [tg 211, tg 6711]],
      [tg 561704, tg 751351]⟩,
    ⟨1, 0, 7, 5,
      [[tg 91, tg 2564], [tg 68, tg 6568], [tg 120, tg 6620], [tg 198, tg 6698], [tg 224, tg 6724]],
      [tg 748891, tg 751364]⟩,
    ⟨1, 0, 8, 7,
      [[tg 104, tg 2577], [tg 81, tg 6581], [tg 120, tg 6620], [tg 211, tg 6711], [tg 237, tg 6737]],
      [tg 748904, tg 751377]⟩,
    ⟨1, 0, 9, 6,
      [[tg 117, tg 2590], [tg 94, tg 6594], [tg 107, tg 6607], [tg 250, tg 6750]],
      [tg 561717, tg 564190]⟩,
    ⟨2, 0, 0, 2,
      [[tg 3, tg 6503], [tg 34, tg 78034], [tg 146, tg 6646], [tg 263, tg 6763]],
      [tg 561603, tg 568103]⟩,
    ⟨2, 0, 1, 3,
      [[tg 16, tg 6516], [tg 133, tg 6633], [tg 172, tg 6672], [tg 276, tg 6776]],
      [tg 561616, tg 568116]⟩,
    ⟨2, 0, 2, 10,
      [[tg 29, tg 6529], [tg 185, tg 6685], [tg 9, tg 6509], [tg 289, tg 6789]],
      [tg 561629, tg 568129]⟩,
    ⟨2, 0, 3, 4,
      [[tg 42, tg 6542], [tg 146, tg 6646], [tg 198, tg 6698], [tg 302, tg 6802]],
      [tg 561642, tg 568142]⟩,
    ⟨2, 0, 4, 9,
      [[tg 55, tg 6555], [tg 159, tg 6659], [tg 211, tg 6711], [tg 315, tg 6815]],
      [tg 561655, tg 568155]⟩,
    ⟨2, 0, 5, 5,
      [[tg 68, tg 6568], [tg 94, tg 6594], [tg 172, tg 6672], [tg 224, tg 6724], [tg 328, tg 6828]],
      [tg 748868, tg 755368]⟩,
    ⟨2, 0, 6, 8,
      [[tg 81, tg 6581], [tg 107, tg 6607], [tg 185, tg 6685], [tg 237, tg 6737], [tg 341, tg 6841]],
      [tg 748881, tg 755381]⟩,
    ⟨2, 0, 7, 6,
      [[tg 94, tg 6594], [tg 198, tg 6698], [tg 250, tg 6750], [tg 328, tg 6828], [tg 354, tg 6854]],
      [tg 748894, tg 755394]⟩,
    ⟨2, 0, 8, 8,
      [[tg 107, tg 6607], [tg 211, tg 6711], [tg 250, tg 6750], [tg 341, tg 6841], [tg 367, tg 6867]],
      [tg 748907, tg 755407]⟩,
    ⟨2, 0, 9, 7,
      [[tg 120, tg 6620], [tg 224, tg 6724], [tg 237, tg 6737], [tg 380, tg 6880]],
      [tg 561720, tg 568220]⟩,
    ⟨3, 0, 0, 3,
      [[tg 133, tg 6633], [tg 164, tg 78164], [tg 276, tg 6776], [tg 393, tg 6893]],
      [tg 561733, tg 568233]⟩,
    ⟨3, 0, 1, 4,
      [[tg 146, tg 6646], [tg 263, tg 6763], [tg 302, tg 6802], [tg 406, tg 6906]],
      [tg 561746, tg 568246]⟩,
    ⟨3, 0, 2, 11,
      [[tg 159, tg 6659], [tg 315, tg 6815], [tg 139, tg 6639], [tg 419, tg 6919]],
      [tg 561759, tg 568259]⟩,
    ⟨3, 0, 3, 5,
      [[tg 172, tg 6672], [tg 276, tg 6776], [tg 328, tg 6828], [tg 432, tg 6932]],
      [tg 561772, tg 568272]⟩,
    ⟨3, 0, 4, 10,
      [[tg 185, tg 6685], [tg 289, tg 6789], [tg 341, tg 6841], [tg 445, tg 6945]],
      [tg 561785, tg 568285]⟩,
    ⟨3, 0, 5, 6,
      [[tg 198, tg 6698], [tg 224, tg 6724], [tg 302, tg 6802], [tg 354, tg 6854], [tg 458, tg 6958]],
      [tg 748998, tg 755498]⟩,
    ⟨3, 0, 6, 9,
      [[tg 211, tg 6711], [tg 237, tg 6737], [tg 315, tg 6815], [tg 367, tg 6867], [tg 471, tg 6971]],
      [tg 749011, tg 755511]⟩,
    ⟨3, 0, 7, 7,
      [[tg 224, tg 6724], [tg 328, tg 6828], [tg 380, tg 6880], [tg 458, tg 6958], [tg 484, tg 6984]],
      [tg 749024, tg 755524]⟩,
    ⟨3, 0, 8, 9,
      [[tg 237, tg 6737], [tg 341, tg 6841], [tg 380, tg 6880], [tg 471, tg 6971], [tg 497, tg 6997]],
      [tg 749037, tg 755537]⟩,
    ⟨3, 0, 9, 8,
      [[tg 250, tg 6750], [tg 354, tg 6854], [tg 367, tg 6867], [tg 510, tg 7010]],
      [tg 561850, tg 568350]⟩,
    ⟨4, 0, 0, 4,
      [[tg 263, tg 6763], [tg 294, tg 78294], [tg 406, tg 6906], [tg 523, tg 7023]],
      [tg 561863, tg 568363]⟩,
    ⟨4, 0, 1, 5,
      [[tg 276, tg 6776], [tg 393, tg 6893], [tg 432, tg 6932], [tg 536, tg 7036]],
      [tg 561876, tg 568376]⟩,
    ⟨4, 0, 2, 12,
      [[tg 289, tg 6789], [tg 445, tg 6945], [tg 269, tg 6769], [tg 549, tg 7049]],
      [tg 561889, tg 568389]⟩,
    ⟨4, 0, 3, 6,
      [[tg 302, tg 6802], [tg 406, tg 6906], [tg 458, tg 6958], [tg 562, tg 7062]],
      [tg 561902, tg 568402]⟩,
    ⟨4, 0, 4, 11,
      [[tg 315, tg 6815], [tg 419, tg 6919], [tg 471, tg 6971], [tg 575, tg 7075]],
      [tg 561915, tg 568415]⟩,
    ⟨4, 0, 5, 7,
      [[tg 328, tg 6828], [tg 354, tg 6854], [tg 432, tg 6932], [tg 484, tg 6984], [tg 588, tg 7088]],
      [tg 749128, tg 755628]⟩,
    ⟨4, 0, 6, 10,
      [[tg 341, tg 6841], [tg 367, tg 6867], [tg 445, tg 6945], [tg 497, tg 6997], [tg 601, tg 7101]],
      [tg 749141, tg 755641]⟩,
    ⟨4, 0, 7, 8,
      [[tg 354, tg 6854], [tg 458, tg 6958], [tg 510, tg 7010], [tg 588, tg 7088], [tg 614, tg 7114]],
      [tg 749154, tg 755654]⟩,
    ⟨4, 0, 8, 10,
      [[tg 367, tg 6867], [tg 471, tg 6971], [tg 510, tg 7010], [tg 601, tg 7101], [tg 627, tg 7127]],
      [tg 749167, tg 755667]⟩,
    ⟨4, 0, 9, 9,
      [[tg 380, tg 6880], [tg 484, tg 6984], [tg 497, tg 6997], [tg 640, tg 7140]],
      [tg 561980, tg 568480]⟩,
    ⟨5, 0, 0, 5,
      [[tg 393, tg 6893], [tg 424, tg 78424], [tg 536, tg 7036], [tg 653, tg 7153]],
      [tg 561993, tg 568493]⟩,
    ⟨5, 0, 1, 6,
      [[tg 406, tg 6906], [tg 523, tg 7023], [tg 562, tg 7062], [tg 666, tg 7166]],
      [tg 562006, tg 568506]⟩,
    ⟨5, 0, 2, 13,
      [[tg 419, tg 6919], [tg 575, tg 7075], [tg 399, tg 6899], [tg 679, tg 7179]],
      [tg 562019, tg 568519]⟩,
    ⟨5, 0, 3, 7,
      [[tg 432, tg 6932], [tg 536, tg 7036], [tg 588, tg 7088], [tg 692, tg 7192]],
      [tg 562032, tg 568532]⟩,
    ⟨5, 0, 4, 12,
      [[tg 445, tg 6945], [tg 549, tg 7049], [tg 601, tg 7101], [tg 705, tg 7205]],
      [tg 562045, tg 568545]⟩,
    ⟨5, 0, 5, 8,
      [[tg 458, tg 6958], [tg 484, tg 6984], [tg 562, tg 7062], [tg 614, tg 7114], [tg 718, tg 7218]],
      [tg 749258, tg 755758]⟩,
    ⟨5, 0, 6, 11,
      [[tg 471, tg 6971], [tg 497, tg 6997], [tg 575, tg 7075], [tg 627, tg 7127], [tg 731, tg 7231]],
      [tg 749271, tg 755771]⟩,
    ⟨5, 0, 7, 9,
      [[tg 484, tg 6984], [tg 588, tg 7088], [tg 640, tg 7140], [tg 718, tg 7218], [tg 744, tg 7244]],
      [tg 749284, tg 755784]⟩,
    ⟨5, 0, 8, 11,
      [[tg 497, tg 6997], [tg 601, tg 7101], [tg 640, tg 7140], [tg 731, tg 7231], [tg 757, tg 7257]],
      [tg 749297, tg 755797]⟩,
    ⟨5, 0, 9, 10,
      [[tg 510, tg 7010], [tg 614, tg 7114], [tg 627, tg 7127], [tg 770, tg 7270]],
      [tg 562110, tg 568610]⟩,
    ⟨6, 0, 0, 6,
      [[tg 523, tg 7023], [tg 554, tg 78554], [tg 666, tg 7166], [tg 783, tg 7283]],
      [tg 562123, tg 568623]⟩,
    ⟨6, 0, 1, 7,
      [[tg 536, tg 7036], [tg 653, tg 7153], [tg 692, tg 7192], [tg 796, tg 7296]],
      [tg 562136, tg 568636]⟩,
    ⟨6, 0, 2, 14,
      [[tg 549, tg 7049], [tg 705, tg 7205], [tg 529, tg 7029], [tg 809, tg 7309]],
      [tg 562149, tg 568649]⟩,
    ⟨6, 0, 3, 8,
      [[tg 562, tg 7062], [tg 666, tg 7166], [tg 718, tg 7218], [tg 822, tg 7322]],
      [tg 562162, tg 568662]⟩,
    ⟨6, 0, 4, 13,
      [[tg 575, tg 7075], [tg 679, tg 7179], [tg 731, tg 7231], [tg 835, tg 7335]],
      [tg 562175, tg 568675]⟩,
    ⟨6, 0, 5, 9,
      [[tg 588, tg 7088], [tg 614, tg 7114], [tg 692, tg 7192], [tg 744, tg 7244], [tg 848, tg 7348]],
      [tg 749388, tg 755888]⟩,
    ⟨6, 0, 6, 12,
      [[tg 601, tg 7101], [tg 627, tg 7127], [tg 705, tg 7205], [tg 757, tg 7257], [tg 861, tg 7361]],
      [tg 749401, tg 755901]⟩,
    ⟨6, 0, 7, 10,
      [[tg 614, tg 7114], [tg 718, tg 7218], [tg 770, tg 7270], [tg 848, tg 7348], [tg 874, tg 7374]],
      [tg 749414, tg 755914]⟩,
    ⟨6, 0, 8, 12,
      [[tg 627, tg 7127], [tg 731, tg 7231], [tg 770, tg 7270], [tg 861, tg 7361], [tg 887, tg 7387]],
      [tg 749427, tg 755927]⟩,
    ⟨6, 0, 9, 11,
      [[tg 640, tg 7140], [tg 744, tg 7244], [tg 757, tg 7257], [tg 900, tg 7400]],
      [tg 562240, tg 568740]⟩,
    ⟨7, 0, 0, 7,
      [[tg 653, tg 7153], [tg 684, tg 78684], [tg 796, tg 7296], [tg 913, tg 7413]],
      [tg 562253, tg 568753]⟩,
    ⟨7, 0, 1, 8,
      [[tg 666, tg 7166], [tg 783, tg 7283], [tg 822, tg 7322], [tg 926, tg 7426]],
      [tg 562266, tg 568766]⟩,
    ⟨7, 0, 2, 15,
      [[tg 679, tg 7179], [tg 835, tg 7335], [tg 659, tg 7159], [tg 939, tg 7439]],
      [tg 562279, tg 568779]⟩,
    ⟨7, 0, 3, 9,
      [[tg 692, tg 7192], [tg 796, tg 7296], [tg 848, tg 7348], [tg 952, tg 7452]],
      [tg 562292, tg 568792]⟩,
    ⟨7, 0, 4, 14,
      [[tg 705, tg 7205], [tg 809, tg 7309], [tg 861, tg 7361], [tg 965, tg 7465]],
      [tg 562305, tg 568805]⟩,
    ⟨7, 0, 5, 10,
      [[tg 718, tg 7218], [tg 744, tg 7244], [tg 822, tg 7322], [tg 874, tg 7374], [tg 978, tg 7478]],
      [tg 749518, tg 756018]⟩,
    ⟨7, 0, 6, 13,
      [[tg 731, tg 7231], [tg 757, tg 7257], [tg 835, tg 7335], [tg 887, tg 7387], [tg 991, tg 7491]],
      [tg 749531, tg 756031]⟩,
    ⟨7, 0, 7, 11,
      [[tg 744, tg 7244], [tg 848, tg 7348], [tg 900, tg 7400], [tg 978, tg 7478], [tg 1004, tg 7504]],
      [tg 749544, tg 756044]⟩,
    ⟨7, 0, 8, 13,
      [[tg 757, tg 7257], [tg 861, tg 7361], [tg 900, tg 7400], [tg 991, tg 7491], [tg 1017, tg 7517]],
      [tg 749557, tg 756057]⟩,
    ⟨7, 0, 9, 12,
      [[tg 770, tg 7270], [tg 874, tg 7374], [tg 887, tg 7387], [tg 1030, tg 7530]],
      [tg 562370, tg 568870]⟩,
    ⟨8, 0, 0, 8,
      [[tg 783, tg 7283], [tg 814, tg 78814], [tg 926, tg 7426], [tg 1043, tg 7543]],
      [tg 562383, tg 568883]⟩,
    ⟨8, 0, 1, 9,
      [[tg 796, tg 7296], [tg 913, tg 7413], [tg 952, tg 7452], [tg 1056, tg 7556]],
      [tg 562396, tg 568896]⟩,
    ⟨8, 0, 2, 16,
      [[tg 809, tg 7309], [tg 965, tg 7465], [tg 789, tg 7289], [tg 1069, tg 7569]],
      [tg 562409, tg 568909]⟩,
    ⟨8, 0, 3, 10,
      [[tg 822, tg 7322], [tg 926, tg 7426], [tg 978, tg 7478], [tg 1082, tg 7582]],
      [tg 562422, tg 568922]⟩,
    ⟨8, 0, 4, 15,
      [[tg 835, tg 7335], [tg 939, tg 7439], [tg 991, tg 7491], [tg 1095, tg 7595]],
      [tg 562435, tg 568935]⟩,
    ⟨8, 0, 5, 11,
      [[tg 848, tg 7348], [tg 874, tg 7374], [tg 952, tg 7452], [tg 1004, tg 7504], [tg 1108, tg 7608]],
      [tg 749648, tg 756148]⟩,
    ⟨8, 0, 6, 14,
      [[tg 861, tg 7361], [tg 887, tg 7387], [tg 965, tg 7465], [tg 1017, tg 7517], [tg 1121, tg 7621]],
      [tg 749661, tg 756161]⟩,
    ⟨8, 0, 7, 12,
      [[tg 874, tg 7374], [tg 978, tg 7478], [tg 1030, tg 7530], [tg 1108, tg 7608], [tg 1134, tg 7634]],
      [tg 749674, tg 756174]⟩,
    ⟨8, 0, 8, 14,
      [[tg 887, tg 7387], [tg 991, tg 7491], [tg 1030, tg 7530], [tg 1121, tg 7621], [tg 1147, tg 7647]],
      [tg 749687, tg 756187]⟩,
    ⟨8, 0, 9, 13,
      [[tg 900, tg 7400], [tg 1004, tg 7504], [tg 1017, tg 7517], [tg 1160, tg 7660]],
      [tg 562500, tg 569000]⟩,
    ⟨9, 0, 0, 9,
      [[tg 913, tg 7413], [tg 944, tg 78944], [tg 1056, tg 7556], [tg 1173, tg 7673]],
      [tg 562513, tg 569013]⟩,
    ⟨9, 0, 1, 10,
      [[tg 926, tg 7426], [tg 1043, tg 7543], [tg 1082, tg 7582], [tg 1186, tg 7686]],
      [tg 562526, tg 569026]⟩,
    ⟨9, 0, 2, 17,
      [[tg 939, tg 7439], [tg 1095, tg 7595], [tg 919, tg 7419], [tg 1199, tg 7699]],
      [tg 562539, tg 569039]⟩,
    ⟨9, 0, 3, 11,
      [[tg 952, tg 7452], [tg 1056, tg 7556], [tg 1108, tg 7608], [tg 1212, tg 7712]],
      [tg 562552, tg 569052]⟩,
    ⟨9, 0, 4, 16,
      [[tg 965, tg 7465], [tg 1069, tg 7569], [tg 1121, tg 7621], [tg 1225, tg 7725]],
      [tg 562565, tg 569065]⟩,
    ⟨9, 0, 5, 12,
      [[tg 978, tg 7478], [tg 1004, tg 7504], [tg 1082, tg 7582], [tg 1134, tg 7634], [tg 1238, tg 7738]],
      [tg 749778, tg 756278]⟩,
    ⟨9, 0, 6, 15,
      [[tg 991, tg 7491], [tg 1017, tg 7517], [tg 1095, tg 7595], [tg 1147, tg 7647], [tg 1251, tg 7751]],
      [tg 749791, tg 756291]⟩,
    ⟨9, 0, 7, 13,
      [[tg 1004, tg 7504], [tg 1108, tg 7608], [tg 1160, tg 7660], [tg 1238, tg 7738], [tg 1264, tg 7764]],
      [tg 749804, tg 756304]⟩,
    ⟨9, 0, 8, 15,
      [[tg 1017, tg 7517], [tg 1121, tg 7621], [tg 1160, tg 7660], [tg 1251, tg 7751], [tg 1277, tg 7777]],
      [tg 749817, tg 756317]⟩,
    ⟨9, 0, 9, 14,
      [[tg 1030, tg 7530], [tg 1134, tg 7634], [tg 1147, tg 7647], [tg 1290, tg 7790]],
      [tg 562630, tg 569130]⟩,
    ⟨10, 0, 0, 10,
      [[tg 1043, tg 7543], [tg 1074, tg 79074], [tg 1186, tg 7686], [tg 5203, tg 11703]],
      [tg 562643, tg 569143]⟩,
    ⟨10, 0, 1, 11,
      [[tg 1056, tg 7556], [tg 1173, tg 7673], [tg 1212, tg 7712], [tg 5216, tg 11716]],
      [tg 562656, tg 569156]⟩,
    ⟨10, 0, 2, 18,
      [[tg 1069, tg 7569], [tg 1225, tg 7725], [tg 1049, tg 7549], [tg 5229, tg 11729]],
      [tg 562669, tg 569169]⟩,
    ⟨10, 0, 3, 12,
      [[tg 1082, tg 7582], [tg 1186, tg 7686], [tg 1238, tg 7738], [tg 5242, tg 11742]],
      [tg 562682, tg 569182]⟩,
    ⟨10, 0, 4, 17,
      [[tg 1095, tg 7595], [tg 1199, tg 7699], [tg 1251, tg 7751], [tg 5255, tg 11755]],
      [tg 562695, tg 569195]⟩,
    ⟨10, 0, 5, 13,
      [[tg 1108, tg 7608], [tg 1134, tg 7634], [tg 1212, tg 7712], [tg 1264, tg 7764], [tg 5268, tg 11768]],
      [tg 749908, tg 756408]⟩,
    ⟨10, 0, 6, 16,
      [[tg 1121, tg 7621], [tg 1147, tg 7647], [tg 1225, tg 7725], [tg 1277, tg 7777], [tg 5281, tg 11781]],
      [tg 749921, tg 756421]⟩,
    ⟨10, 0, 7, 14,
      [[tg 1134, tg 7634], [tg 1238, tg 7738], [tg 1290, tg 7790], [tg 5268, tg 11768], [tg 5294, tg 11794]],
      [tg 749934, tg 756434]⟩,
    ⟨10, 0, 8, 16,
      [[tg 1147, tg 7647], [tg 1251, tg 7751], [tg 1290, tg 7790], [tg 5281, tg 11781], [tg 5307, tg 11807]],
      [tg 749947, tg 756447]⟩,
    ⟨10, 0, 9, 15,
      [[tg 1160, tg 7660], [tg 1264, tg 7764], [tg 1277, tg 7777], [tg 5320, tg 11820]],
      [tg 562760, tg 569260]⟩]⟩,
  ⟨1, 1, 1, 0, 0, [(-1, 1, 0), (1, -1, 0), (1, 1, 2)], 1, 1, 2, 2, 0, 0, 0, 0,
   [⟨1, 1, 0, 10,
      [[tg 10, tg 6510], [tg 29, tg 15635], [tg 17, tg 6517], [tg 9, tg 78009]],
      [tg 374429, tg 390035]⟩,
    ⟨1, 1, 1, 11,
      [[tg 23, tg 6523], [tg 4, tg 6504], [tg 43, tg 6543], [tg 22, tg 78022]],
      [tg 374404, tg 380904]⟩,
    ⟨1, 1, 2, 19,
      [[tg 36, tg 6536], [tg 56, tg 6556], [tg 5210, tg 11710], [tg 35, tg 78035]],
      [tg 187256, tg 193756]⟩,
    ⟨1, 1, 3, 12,
      [[tg 49, tg 6549], [tg 17, tg 6517], [tg 69, tg 6569], [tg 48, tg 78048]],
      [tg 374417, tg 380917]⟩,
    ⟨1, 1, 4, 18,
      [[tg 62, tg 6562], [tg 30, tg 6530], [tg 82, tg 6582], [tg 61, tg 78061]],
      [tg 374482, tg 380982]⟩,
    ⟨1, 1, 5, 13,
      [[tg 75, tg 6575], [tg 101, tg 6601], [tg 43, tg 6543], [tg 95, tg 6595], [tg 74, tg 78074]],
      [tg 374443, tg 380943]⟩,
    ⟨1, 1, 6, 17,
      [[tg 88, tg 6588], [tg 114, tg 6614], [tg 56, tg 6556], [tg 108, tg 6608], [tg 87, tg 78087]],
      [tg 561714, tg 568214]⟩,
    ⟨1, 1, 7, 14,
      [[tg 101, tg 6601], [tg 69, tg 6569], [tg 121, tg 6621], [tg 74, tg 78074], [tg 100, tg 78100]],
      [tg 561669, tg 568169]⟩,
    ⟨1, 1, 8, 16,
      [[tg 114, tg 6614], [tg 82, tg 6582], [tg 121, tg 6621], [tg 87, tg 78087], [tg 113, tg 78113]],
      [tg 374521, tg 381021]⟩,
    ⟨1, 1, 9, 15,
      [[tg 127, tg 6627], [tg 95, tg 6595], [tg 108, tg 6608], [tg 126, tg 78126]],
      [tg 374495, tg 380995]⟩]⟩,
  ⟨1, -1, 1, 0, 0, [(-1, -1, 0), (1, 1, 0), (-1, 1, 2)], -1, 1, 2, 2, 0, 0, 0, 0,
   [⟨-1, 1, 0, 10,
      [[tg 1181, tg 7681], [tg 32, tg 2507], [tg 18, tg 6518], [tg 10, tg 78010]],
      [tg 374432, tg 376907]⟩,
    ⟨-1, 1, 1, 11,
      [[tg 1194, tg 7694], [tg 5, tg 6505], [tg 44, tg 6544], [tg 23, tg 78023]],
      [tg 374405, tg 380905]⟩,
    ⟨-1, 1, 2, 19,
      [[tg 1207, tg 7707], [tg 57, tg 6557], [tg 62410, tg 140410], [tg 36, tg 78036]],
      [tg 187257, tg 193757]⟩,
    ⟨-1, 1, 3, 12,
      [[tg 1220, tg 7720], [tg 18, tg 6518], [tg 70, tg 6570], [tg 49, tg 78049]],
      [tg 374418, tg 380918]⟩,
    ⟨-1, 1, 4, 18,
      [[tg 1233, tg 7733], [tg 31, tg 6531], [tg 83, tg 6583], [tg 62, tg 78062]],
      [tg 374483, tg 380983]⟩,
    ⟨-1, 1, 5, 13,
      [[tg 1246, tg 7746], [tg 1272, tg 7772], [tg 44, tg 6544], [tg 96, tg 6596], [tg 75, tg 78075]],
      [tg 374444, tg 380944]⟩,
    ⟨-1, 1, 6, 17,
      [[tg 1259, tg 7759], [tg 1285, tg 7785], [tg 57, tg 6557], [tg 109, tg 6609], [tg 88, tg 78088]],
      [tg 562885, tg 569385]⟩,
    ⟨-1, 1, 7, 14,
      [[tg 1272, tg 7772], [tg 70, tg 6570], [tg 122, tg 6622], [tg 75, tg 78075], [tg 101, tg 78101]],
      [tg 561670, tg 568170]⟩,
    ⟨-1, 1, 8, 16,
      [[tg 1285, tg 7785], [tg 83, tg 6583], [tg 122, tg 6622], [tg 88, tg 78088], [tg 114, tg 78114]],
      [tg 374522, tg 381022]⟩,
    ⟨-1, 1, 9, 15,
      [[tg 1298, tg 7798], [tg 96, tg 6596], [tg 109, tg 6609], [tg 127, tg 78127]],
      [tg 374496, tg 380996]⟩]⟩,
  ⟨1, -10, 0, 0, 0, [(0, -1, 0), (0, 1, 0), (-1, 0, 1)], -1, 0, 1, 10, 0, 0, 0, 0,
   [⟨-1, 0, 0, 1,
      [[tg 136, tg 6636], [tg 27, tg 1338], [tg 19, tg 6519], [tg 0, tg 2476]],
      [tg 0, tg 2476]⟩,
    ⟨-1, 0, 1, 2,
      [[tg 149, tg 6649], [tg 6, tg 6506], [tg 45, tg 6545], [tg 13, tg 2489]],
      [tg 374406, tg 380906]⟩,
    ⟨-1, 0, 2, 9,
      [[tg 162, tg 6662], [tg 58, tg 6558], [tg 5, tg 15611], [tg 26, tg 2502]],
      [tg 187258, tg 193758]⟩,
    ⟨-1, 0, 3, 3,
      [[tg 175, tg 6675], [tg 19, tg 6519], [tg 71, tg 6571], [tg 39, tg 2515]],
      [tg 374419, tg 380919]⟩,
    ⟨-1, 0, 4, 8,
      [[tg 188, tg 6688], [tg 32, tg 6532], [tg 84, tg 6584], [tg 52, tg 2528]],
      [tg 374484, tg 380984]⟩,
    ⟨-1, 0, 5, 4,
      [[tg 201, tg 6701], [tg 227, tg 6727], [tg 45, tg 6545], [tg 97, tg 6597], [tg 65, tg 2541]],
      [tg 374445, tg 380945]⟩,
    ⟨-1, 0, 6, 7,
      [[tg 214, tg 6714], [tg 240, tg 6740], [tg 58, tg 6558], [tg 110, tg 6610], [tg 78, tg 2554]],
      [tg 187310, tg 193810]⟩,
    ⟨-1, 0, 7, 4,
      [[tg 227, tg 6727], [tg 71, tg 6571], [tg 123, tg 6623], [tg 65, tg 2541], [tg 91, tg 2567]],
      [tg 187265, tg 189741]⟩,
    ⟨-1, 0, 8, 6,
      [[tg 240, tg 6740], [tg 84, tg 6584], [tg 123, tg 6623], [tg 78, tg 2554], [tg 104, tg 2580]],
      [tg 374523, tg 381023]⟩,
    ⟨-1, 0, 9, 5,
      [[tg 253, tg 6753], [tg 97, tg 6597], [tg 110, tg 6610], [tg 117, tg 2593]],
      [tg 374497, tg 380997]⟩,
    ⟨-2, 0, 0, 2,
      [[tg 266, tg 6766], [tg 1208, tg 7708], [tg 149, tg 6649], [tg 6, tg 6506]],
      [tg 6, tg 6506]⟩,
    ⟨-2, 0, 1, 3,
      [[tg 279, tg 6779], [tg 136, tg 6636], [tg 175, tg 6675], [tg 19, tg 6519]],
      [tg 374536, tg 381036]⟩,
    ⟨-2, 0, 2, 10,
      [[tg 292, tg 6792], [tg 188, tg 6688], [tg 1181, tg 79181], [tg 32, tg 6532]],
      [tg 187388, tg 193888]⟩,
    ⟨-2, 0, 3, 4,
      [[tg 305, tg 6805], [tg 149, tg 6649], [tg 201, tg 6701], [tg 45, tg 6545]],
      [tg 374549, tg 381049]⟩,
    ⟨-2, 0, 4, 9,
      [[tg 318, tg 6818], [tg 162, tg 6662], [tg 214, tg 6714], [tg 58, tg 6558]],
      [tg 374614, tg 381114]⟩,
    ⟨-2, 0, 5, 5,
      [[tg 331, tg 6831], [tg 357, tg 6857], [tg 175, tg 6675], [tg 227, tg 6727], [tg 71, tg 6571]],
      [tg 374575, tg 381075]⟩,
    ⟨-2, 0, 6, 8,
      [[tg 344, tg 6844], [tg 370, tg 6870], [tg 188, tg 6688], [tg 240, tg 6740], [tg 84, tg 6584]],
      [tg 187440, tg 193940]⟩,
    ⟨-2, 0, 7, 5,
      [[tg 357, tg 6857], [tg 201, tg 6701], [tg 253, tg 6753], [tg 71, tg 6571], [tg 97, tg 6597]],
      [tg 187271, tg 193771]⟩,
    ⟨-2, 0, 8, 7,
      [[tg 370, tg 6870], [tg 214, tg 6714], [tg 253, tg 6753], [tg 84, tg 6584], [tg 110, tg 6610]],
      [tg 374653, tg 381153]⟩,
    ⟨-2, 0, 9, 6,
      [[tg 383, tg 6883], [tg 227, tg 6727], [tg 240, tg 6740], [tg 123, tg 6623]],
      [tg 374627, tg 381127]⟩,
    ⟨-3, 0, 0, 3,
      [[tg 396, tg 6896], [tg 1078, tg 7578], [tg 279, tg 6779], [tg 136, tg 6636]],
      [tg 136, tg 6636]⟩,
    ⟨-3, 0, 1, 4,
      [[tg 409, tg 6909], [tg 266, tg 6766], [tg 305, tg 6805], [tg 149, tg 6649]],
      [tg 374666, tg 381166]⟩,
    ⟨-3, 0, 2, 11,
      [[tg 422, tg 6922], [tg 318, tg 6818], [tg 1051, tg 79051], [tg 162, tg 6662]],
      [tg 187518, tg 194018]⟩,
    ⟨-3, 0, 3, 5,
      [[tg 435, tg 6935], [tg 279, tg 6779], [tg 331, tg 6831], [tg 175, tg 6675]],
      [tg 374679, tg 381179]⟩,
    ⟨-3, 0, 4, 10,
      [[tg 448, tg 6948], [tg 292, tg 6792], [tg 344, tg 6844], [tg 188, tg 6688]],
      [tg 374744, tg 381244]⟩,
    ⟨-3, 0, 5, 6,
      [[tg 461, tg 6961], [tg 487, tg 6987], [tg 305, tg 6805], [tg 357, tg 6857], [tg 201, tg 6701]],
      [tg 374705, tg 381205]⟩,
    ⟨-3, 0, 6, 9,
      [[tg 474, tg 6974], [tg 500, tg 7000], [tg 318, tg 6818], [tg 370, tg 6870], [tg 214, tg 6714]],
      [tg 187570, tg 194070]⟩,
    ⟨-3, 0, 7, 6,
      [[tg 487, tg 6987], [tg 331, tg 6831], [tg 383, tg 6883], [tg 201, tg 6701], [tg 227, tg 6727]],
      [tg 187401, tg 193901]⟩,
    ⟨-3, 0, 8, 8,
      [[tg 500, tg 7000], [tg 344, tg 6844], [tg 383, tg 6883], [tg 214, tg 6714], [tg 240, tg 6740]],
      [tg 374783, tg 381283]⟩,
    ⟨-3, 0, 9, 7,
      [[tg 513, tg 7013], [tg 357, tg 6857], [tg 370, tg 6870], [tg 253, tg 6753]],
      [tg 374757, tg 381257]⟩,
    ⟨-4, 0, 0, 4,
      [[tg 526, tg 7026], [tg 948, tg 7448], [tg 409, tg 6909], [tg 266, tg 6766]],
      [tg 266, tg 6766]⟩,
    ⟨-4, 0, 1, 5,
      [[tg 539, tg 7039], [tg 396, tg 6896], [tg 435, tg 6935], [tg 279, tg 6779]],
      [tg 374796, tg 381296]⟩,
    ⟨-4, 0, 2, 12,
      [[tg 552, tg 7052], [tg 448, tg 6948], [tg 921, tg 78921], [tg 292, tg 6792]],
      [tg 187648, tg 194148]⟩,
    ⟨-4, 0, 3, 6,
      [[tg 565, tg 7065], [tg 409, tg 6909], [tg 461, tg 6961], [tg 305, tg 6805]],
      [tg 374809, tg 381309]⟩,
    ⟨-4, 0, 4, 11,
      [[tg 578, tg 7078], [tg 422, tg 6922], [tg 474, tg 6974], [tg 318, tg 6818]],
      [tg 374874, tg 381374]⟩,
    ⟨-4, 0, 5, 7,
      [[tg 591, tg 7091], [tg 617, tg 7117], [tg 435, tg 6935], [tg 487, tg 6987], [tg 331, tg 6831]],
      [tg 374835, tg 381335]⟩,
    ⟨-4, 0, 6, 10,
      [[tg 604, tg 7104], [tg 630, tg 7130], [tg 448, tg 6948], [tg 500, tg 7000], [tg 344, tg 6844]],
      [tg 187700, tg 194200]⟩,
    ⟨-4, 0, 7, 7,
      [[tg 617, tg 7117], [tg 461, tg 6961], [tg 513, tg 7013], [tg 331, tg 6831], [tg 357, tg 6857]],
      [tg 187531, tg 194031]⟩,
    ⟨-4, 0, 8, 9,
      [[tg 630, tg 7130], [tg 474, tg 6974], [tg 513, tg 7013], [tg 344, tg 6844], [tg 370, tg 6870]],
      [tg 374913, tg 381413]⟩,
    ⟨-4, 0, 9, 8,
      [[tg 643, tg 7143], [tg 487, tg 6987], [tg 500, tg 7000], [tg 383, tg 6883]],
      [tg 374887, tg 381387]⟩,
    ⟨-5, 0, 0, 5,
      [[tg 656, tg 7156], [tg 818, tg 7318], [tg 539, tg 7039], [tg 396, tg 6896]],
      [tg 396, tg 6896]⟩,
    ⟨-5, 0, 1, 6,
      [[tg 669, tg 7169], [tg 526, tg 7026], [tg 565, tg 7065], [tg 409, tg 6909]],
      [tg 374926, tg 381426]⟩,
    ⟨-5, 0, 2, 13,
      [[tg 682, tg 7182], [tg 578, tg 7078], [tg 791, tg 78791], [tg 422, tg 6922]],
      [tg 187778, tg 194278]⟩,
    ⟨-5, 0, 3, 7,
      [[tg 695, tg 7195], [tg 539, tg 7039], [tg 591, tg 7091], [tg 435, tg 6935]],
      [tg 374939, tg 381439]⟩,
    ⟨-5, 0, 4, 12,
      [[tg 708, tg 7208], [tg 552, tg 7052], [tg 604, tg 7104], [tg 448, tg 6948]],
      [tg 375004, tg 381504]⟩,
    ⟨-5, 0, 5, 8,
      [[tg 721, tg 7221], [tg 747, tg 7247], [tg 565, tg 7065], [tg 617, tg 7117], [tg 461, tg 6961]],
      [tg 374965, tg 381465]⟩,
    ⟨-5, 0, 6, 11,
      [[tg 734, tg 7234], [tg 760, tg 7260], [tg 578, tg 7078], [tg 630, tg 7130], [tg 474, tg 6974]],
      [tg 187830, tg 194330]⟩,
    ⟨-5, 0, 7, 8,
      [[tg 747, tg 7247], [tg 591, tg 7091], [tg 643, tg 7143], [tg 461, tg 6961], [tg 487, tg 6987]],
      [tg 187661, tg 194161]⟩,
    ⟨-5, 0, 8, 10,
      [[tg 760, tg 7260], [tg 604, tg 7104], [tg 643, tg 7143], [tg 474, tg 6974], [tg 500, tg 7000]],
      [tg 375043, tg 381543]⟩,
    ⟨-5, 0, 9, 9,
      [[tg 773, tg 7273], [tg 617, tg 7117], [tg 630, tg 7130], [tg 513, tg 7013]],
      [tg 375017, tg 381517]⟩,
    ⟨-6, 0, 0, 6,
      [[tg 786, tg 7286], [tg 688, tg 7188], [tg 669, tg 7169], [tg 526, tg 7026]],
      [tg 526, tg 7026]⟩,
    ⟨-6, 0, 1, 7,
      [[tg 799, tg 7299], [tg 656, tg 7156], [tg 695, tg 7195], [tg 539, tg 7039]],
      [tg 375056, tg 381556]⟩,
    ⟨-6, 0, 2, 14,
      [[tg 812, tg 7312], [tg 708, tg 7208], [tg 661, tg 78661], [tg 552, tg 7052]],
      [tg 187908, tg 194408]⟩,
    ⟨-6, 0, 3, 8,
      [[tg 825, tg 7325], [tg 669, tg 7169], [tg 721, tg 7221], [tg 565, tg 7065]],
      [tg 375069, tg 381569]⟩,
    ⟨-6, 0, 4, 13,
      [[tg 838, tg 7338], [tg 682, tg 7182], [tg 734, tg 7234], [tg 578, tg 7078]],
      [tg 375134, tg 381634]⟩,
    ⟨-6, 0, 5, 9,
      [[tg 851, tg 7351], [tg 877, tg 7377], [tg 695, tg 7195], [tg 747, tg 7247], [tg 591, tg 7091]],
      [tg 375095, tg 381595]⟩,
    ⟨-6, 0, 6, 12,
      [[tg 864, tg 7364], [tg 890, tg 7390], [tg 708, tg 7208], [tg 760, tg 7260], [tg 604, tg 7104]],
      [tg 187960, tg 194460]⟩,
    ⟨-6, 0, 7, 9,
      [[tg 877, tg 7377], [tg 721, tg 7221], [tg 773, tg 7273], [tg 591, tg 7091], [tg 617, tg 7117]],
      [tg 187791, tg 194291]⟩,
    ⟨-6, 0, 8, 11,
      [[tg 890, tg 7390], [tg 734, tg 7234], [tg 773, tg 7273], [tg 604, tg 7104], [tg 630, tg 7130]],
      [tg 375173, tg 381673]⟩,
    ⟨-6, 0, 9, 10,
      [[tg 903, tg 7403], [tg 747, tg 7247], [tg 760, tg 7260], [tg 643, tg 7143]],
      [tg 375147, tg 381647]⟩,
    ⟨-7, 0, 0, 7,
      [[tg 916, tg 7416], [tg 558, tg 7058], [tg 799, tg 7299], [tg 656, tg 7156]],
      [tg 656, tg 7156]⟩,
    ⟨-7, 0, 1, 8,
      [[tg 929, tg 7429], [tg 786, tg 7286], [tg 825, tg 7325], [tg 669, tg 7169]],
      [tg 375186, tg 381686]⟩,
    ⟨-7, 0, 2, 15,
      [[tg 942, tg 7442], [tg 838, tg 7338], [tg 531, tg 78531], [tg 682, tg 7182]],
      [tg 188038, tg 194538]⟩,
    ⟨-7, 0, 3, 9,
      [[tg 955, tg 7455], [tg 799, tg 7299], [tg 851, tg 7351], [tg 695, tg 7195]],
      [tg 375199, tg 381699]⟩,
    ⟨-7, 0, 4, 14,
      [[tg 968, tg 7468], [tg 812, tg 7312], [tg 864, tg 7364], [tg 708, tg 7208]],
      [tg 375264, tg 381764]⟩,
    ⟨-7, 0, 5, 10,
      [[tg 981, tg 7481], [tg 1007, tg 7507], [tg 825, tg 7325], [tg 877, tg 7377], [tg 721, tg 7221]],
      [tg 375225, tg 381725]⟩,
    ⟨-7, 0, 6, 13,
      [[tg 994, tg 7494], [tg 1020, tg 7520], [tg 838, tg 7338], [tg 890, tg 7390], [tg 734, tg 7234]],
      [tg 188090, tg 194590]⟩,
    ⟨-7, 0, 7, 10,
      [[tg 1007, tg 7507], [tg 851, tg 7351], [tg 903, tg 7403], [tg 721, tg 7221], [tg 747, tg 7247]],
      [tg 187921, tg 194421]⟩,
    ⟨-7, 0, 8, 12,
      [[tg 1020, tg 7520], [tg 864, tg 7364], [tg 903, tg 7403], [tg 734, tg 7234], [tg 760, tg 7260]],
      [tg 375303, tg 381803]⟩,
    ⟨-7, 0, 9, 11,
      [[tg 1033, tg 7533], [tg 877, tg 7377], [tg 890, tg 7390], [tg 773, tg 7273]],
      [tg 375277, tg 381777]⟩,
    ⟨-8, 0, 0, 8,
      [[tg 1046, tg 7546], [tg 428, tg 6928], [tg 929, tg 7429], [tg 786, tg 7286]],
      [tg 786, tg 7286]⟩,
    ⟨-8, 0, 1, 9,
      [[tg 1059, tg 7559], [tg 916, tg 7416], [tg 955, tg 7455], [tg 799, tg 7299]],
      [tg 375316, tg 381816]⟩,
    ⟨-8, 0, 2, 16,
      [[tg 1072, tg 7572], [tg 968, tg 7468], [tg 401, tg 78401], [tg 812, tg 7312]],
      [tg 188168, tg 194668]⟩,
    ⟨-8, 0, 3, 10,
      [[tg 1085, tg 7585], [tg 929, tg 7429], [tg 981, tg 7481], [tg 825, tg 7325]],
      [tg 375329, tg 381829]⟩,
    ⟨-8, 0, 4, 15,
      [[tg 1098, tg 7598], [tg 942, tg 7442], [tg 994, tg 7494], [tg 838, tg 7338]],
      [tg 375394, tg 381894]⟩,
    ⟨-8, 0, 5, 11,
      [[tg 1111, tg 7611], [tg 1137, tg 7637], [tg 955, tg 7455], [tg 1007, tg 7507], [tg 851, tg 7351]],
      [tg 375355, tg 381855]⟩,
    ⟨-8, 0, 6, 14,
      [[tg 1124, tg 7624], [tg 1150, tg 7650], [tg 968, tg 7468], [tg 1020, tg 7520], [tg 864, tg 7364]],
      [tg 188220, tg 194720]⟩,
    ⟨-8, 0, 7, 11,
      [[tg 1137, tg 7637], [tg 981, tg 7481], [tg 1033, tg 7533], [tg 851, tg 7351], [tg 877, tg 7377]],
      [tg 188051, tg 194551]⟩,
    ⟨-8, 0, 8, 13,
      [[tg 1150, tg 7650], [tg 994, tg 7494], [tg 1033, tg 7533], [tg 864, tg 7364], [tg 890, tg 7390]],
      [tg 375433, tg 381933]⟩,
    ⟨-8, 0, 9, 12,
      [[tg 1163, tg 7663], [tg 1007, tg 7507], [tg 1020, tg 7520], [tg 903, tg 7403]],
      [tg 375407, tg 381907]⟩,
    ⟨-9, 0, 0, 9,
      [[tg 1176, tg 7676], [tg 298, tg 6798], [tg 1059, tg 7559], [tg 916, tg 7416]],
      [tg 916, tg 7416]⟩,
    ⟨-9, 0, 1, 10,
      [[tg 1189, tg 7689], [tg 1046, tg 7546], [tg 1085, tg 7585], [tg 929, tg 7429]],
      [tg 375446, tg 381946]⟩,
    ⟨-9, 0, 2, 17,
      [[tg 1202, tg 7702], [tg 1098, tg 7598], [tg 271, tg 78271], [tg 942, tg 7442]],
      [tg 188298, tg 194798]⟩,
    ⟨-9, 0, 3, 11,
      [[tg 1215, tg 7715], [tg 1059, tg 7559], [tg 1111, tg 7611], [tg 955, tg 7455]],
      [tg 375459, tg 381959]⟩,
    ⟨-9, 0, 4, 16,
      [[tg 1228, tg 7728], [tg 1072, tg 7572], [tg 1124, tg 7624], [tg 968, tg 7468]],
      [tg 375524, tg 382024]⟩,
    ⟨-9, 0, 5, 12,
      [[tg 1241, tg 7741], [tg 1267, tg 7767], [tg 1085, tg 7585], [tg 1137, tg 7637], [tg 981, tg 7481]],
      [tg 375485, tg 381985]⟩,
    ⟨-9, 0, 6, 15,
      [[tg 1254, tg 7754], [tg 1280, tg 7780], [tg 1098, tg 7598], [tg 1150, tg 7650], [tg 994, tg 7494]],
      [tg 188350, tg 194850]⟩,
    ⟨-9, 0, 7, 12,
      [[tg 1267, tg 7767], [tg 1111, tg 7611], [tg 1163, tg 7663], [tg 981, tg 7481], [tg 1007, tg 7507]],
      [tg 188181, tg 194681]⟩,
    ⟨-9, 0, 8, 14,
      [[tg 1280, tg 7780], [tg 1124, tg 7624], [tg 1163, tg 7663], [tg 994, tg 7494], [tg 1020, tg 7520]],
      [tg 375563, tg 382063]⟩,
    ⟨-9, 0, 9, 13,
      [[tg 1293, tg 7793], [tg 1137, tg 7637], [tg 1150, tg 7650], [tg 1033, tg 7533]],
      [tg 375537, tg 382037]⟩,
    ⟨-10, 0, 0, 10,
      [[tg 5206, tg 11706], [tg 168, tg 6668], [tg 1189, tg 7689], [tg 1046, tg 7546]],
      [tg 1046, tg 7546]⟩,
    ⟨-10, 0, 1, 11,
      [[tg 5219, tg 11719], [tg 1176, tg 7676], [tg 1215, tg 7715], [tg 1059, tg 7559]],
      [tg 375576, tg 382076]⟩,
    ⟨-10, 0, 2, 18,
      [[tg 5232, tg 11732], [tg 1228, tg 7728], [tg 141, tg 78141], [tg 1072, tg 7572]],
      [tg 188428, tg 194928]⟩,
    ⟨-10, 0, 3, 12,
      [[tg 5245, tg 11745], [tg 1189, tg 7689], [tg 1241, tg 7741], [tg 1085, tg 7585]],
      [tg 375589, tg 382089]⟩,
    ⟨-10, 0, 4, 17,
      [[tg 5258, tg 11758], [tg 1202, tg 7702], [tg 1254, tg 7754], [tg 1098, tg 7598]],
      [tg 375654, tg 382154]⟩,
    ⟨-10, 0, 5, 13,
      [[tg 5271, tg 11771], [tg 5297, tg 11797], [tg 1215, tg 7715], [tg 1267, tg 7767], [tg 1111, tg 7611]],
      [tg 375615, tg 382115]⟩,
    ⟨-10, 0, 6, 16,
      [[tg 5284, tg 11784], [tg 5310, tg 11810], [tg 1228, tg 7728], [tg 1280, tg 7780], [tg 1124, tg 7624]],
      [tg 188480, tg 194980]⟩,
    ⟨-10, 0, 7, 13,
      [[tg 5297, tg 11797], [tg 1241, tg 7741], [tg 1293, tg 7793], [tg 1111, tg 7611], [tg 1137, tg 7637]],
      [tg 188311, tg 194811]⟩,
    ⟨-10, 0, 8, 15,
      [[tg 5310, tg 11810], [tg 1254, tg 7754], [tg 1293, tg 7793], [tg 1124, tg 7624], [tg 1150, tg 7650]],
      [tg 375693, tg 382193]⟩,
    ⟨-10, 0, 9, 14,
      [[tg 5323, tg 11823], [tg 1267, tg 7767], [tg 1280, tg 7780], [tg 1163, tg 7663]],
      [tg 375667, tg 382167]⟩]⟩,
  ⟨2, -1, -1, 1, -1, [(-1, -1, 1), (1, -1, 1)], -1, -1, 1, 2, 1, -1, 1, 2,
   [⟨0, -2, 0, 20,
      [[tg 5337, tg 11837, tg 98937, tg 105437], [tg 67763, tg 74263, tg 161363, tg 167863], [tg 20, tg 6520, tg 93620, tg 100120], [tg 62537, tg 69037, tg 156137, tg 162637]],
      [tg 187220, tg 193720, tg 280820, tg 287320]⟩,
    ⟨0, -2, 1, 19,
      [[tg 5350, tg 11850, tg 98950, tg 105450], [tg 7, tg 6507, tg 93607, tg 100107], [tg 46, tg 6546, tg 93646, tg 100146], [tg 62550, tg 69050, tg 156150, tg 162650]],
      [tg 187246, tg 193746, tg 280846, tg 287346]⟩,
    ⟨0, -2, 2, 11,
      [[tg 5363, tg 11863, tg 98963, tg 105463], [tg 59, tg 6559, tg 93659, tg 100159], [tg 137, tg 6637, tg 93737, tg 100237], [tg 62563, tg 69063, tg 156163, tg 162663]],
      [tg 187337, tg 193837, tg 280937, tg 287437]⟩,
    ⟨0, -2, 3, 18,
      [[tg 5376, tg 11876, tg 98976, tg 105476], [tg 20, tg 6520, tg 93620, tg 100120], [tg 72, tg 6572, tg 93672, tg 100172], [tg 62576, tg 69076, tg 156176, tg 162676]],
      [tg 374472, tg 380972, tg 468072, tg 474572]⟩,
    ⟨0, -2, 4, 12,
      [[tg 5389, tg 11889, tg 98989, tg 105489], [tg 33, tg 6533, tg 93633, tg 100133], [tg 85, tg 6585, tg 93685, tg 100185], [tg 62589, tg 69089, tg 156189, tg 162689]],
      [tg 187233, tg 193733, tg 280833, tg 287333]⟩,
    ⟨0, -2, 5, 17,
      [[tg 5402, tg 11902, tg 99002, tg 105502], [tg 5428, tg 11928, tg 99028, tg 105528], [tg 46, tg 6546, tg 93646, tg 100146], [tg 98, tg 6598, tg 93698, tg 100198], [tg 62602, tg 69102, tg 156202, tg 162702]],
      [tg 567028, tg 573528, tg 660628, tg 667128]⟩,
    ⟨0, -2, 6, 13,
      [[tg 5415, tg 11915, tg 99015, tg 105515], [tg 5441, tg 11941, tg 99041, tg 105541], [tg 59, tg 6559, tg 93659, tg 100159], [tg 111, tg 6611, tg 93711, tg 100211], [tg 62615, tg 69115, tg 156215, tg 162715]],
      [tg 374459, tg 380959, tg 468059, tg 474559]⟩,
    ⟨0, -2, 7, 16,
      [[tg 5428, tg 11928, tg 99028, tg 105528], [tg 72, tg 6572, tg 93672, tg 100172], [tg 124, tg 6624, tg 93724, tg 100224], [tg 62602, tg 69102, tg 156202, tg 162702], [tg 62628, tg 69128, tg 156228, tg 162728]],
      [tg 187324, tg 193824, tg 280924, tg 287424]⟩,
    ⟨0, -2, 8, 14,
      [[tg 5441, tg 11941, tg 99041, tg 105541], [tg 85, tg 6585, tg 93685, tg 100185], [tg 124, tg 6624, tg 93724, tg 100224], [tg 62615, tg 69115, tg 156215, tg 162715], [tg 62641, tg 69141, tg 156241, tg 162741]],
      [tg 561685, tg 568185, tg 655285, tg 661785]⟩,
    ⟨0, -2, 9, 15,
      [[tg 5454, tg 11954, tg 99054, tg 105554], [tg 98, tg 6598, tg 93698, tg 100198], [tg 111, tg 6611, tg 93711, tg 100211], [tg 62654, tg 69154, tg 156254, tg 162754]],
      [tg 374511, tg 381011, tg 468111, tg 474611]⟩,
    ⟨0, -1, 0, 10,
      [[tg 1, tg 6501, tg 31207, tg 37707], [tg 33, tg 6533, tg 93633, tg 100133], [tg 150, tg 6650, tg 93750, tg 100250], [tg 2, tg 1307, tg 7802, tg 94907]],
      [tg 187350, tg 193850, tg 280950, tg 287450]⟩,
    ⟨0, -1, 1, 9,
      [[tg 14, tg 6514, tg 31220, tg 37720], [tg 137, tg 6637, tg 93737, tg 100237], [tg 176, tg 6676, tg 93776, tg 100276], [tg 15, tg 1320, tg 7815, tg 94920]],
      [tg 187376, tg 193876, tg 280976, tg 287476]⟩,
    ⟨0, -1, 2, 1,
      [[tg 27, tg 6527, tg 31233, tg 37733], [tg 189, tg 6689, tg 93789, tg 100289], [tg 0, tg 1301, tg 2602, tg 32507], [tg 28, tg 1333, tg 7828, tg 94933]],
      [tg 187200, tg 188501, tg 189802, tg 219707]⟩,
    ⟨0, -1, 3, 8,
      [[tg 40, tg 6540, tg 31246, tg 37746], [tg 150, tg 6650, tg 93750, tg 100250], [tg 202, tg 6702, tg 93802, tg 100302], [tg 41, tg 1346, tg 7841, tg 94946]],
      [tg 374602, tg 381102, tg 468202, tg 474702]⟩,
    ⟨0, -1, 4, 2,
      [[tg 53, tg 6553, tg 31259, tg 37759], [tg 163, tg 6663, tg 93763, tg 100263], [tg 215, tg 6715, tg 93815, tg 100315], [tg 54, tg 1359, tg 7854, tg 94959]],
      [tg 187363, tg 193863, tg 280963, tg 287463]⟩,
    ⟨0, -1, 5, 7,
      [[tg 66, tg 6566, tg 31272, tg 37772], [tg 92, tg 6592, tg 31298, tg 37798], [tg 176, tg 6676, tg 93776, tg 100276], [tg 228, tg 6728, tg 93828, tg 100328], [tg 67, tg 1372, tg 7867, tg 94972]],
      [tg 561692, tg 568192, tg 592898, tg 599398]⟩,
    ⟨0, -1, 6, 3,
      [[tg 79, tg 6579, tg 31285, tg 37785], [tg 105, tg 6605, tg 31311, tg 37811], [tg 189, tg 6689, tg 93789, tg 100289], [tg 241, tg 6741, tg 93841, tg 100341], [tg 80, tg 1385, tg 7880, tg 94985]],
      [tg 374589, tg 381089, tg 468189, tg 474689]⟩,
    ⟨0, -1, 7, 6,
      [[tg 92, tg 6592, tg 31298, tg 37798], [tg 202, tg 6702, tg 93802, tg 100302], [tg 254, tg 6754, tg 93854, tg 100354], [tg 67, tg 1372, tg 7867, tg 94972], [tg 93, tg 1398, tg 7893, tg 94998]],
      [tg 187454, tg 193954, tg 281054, tg 287554]⟩,
    ⟨0, -1, 8, 4,
      [[tg 105, tg 6605, tg 31311, tg 37811], [tg 215, tg 6715, tg 93815, tg 100315], [tg 254, tg 6754, tg 93854, tg 100354], [tg 80, tg 1385, tg 7880, tg 94985], [tg 106, tg 1411, tg 7906, tg 95011]],
      [tg 561815, tg 568315, tg 655415, tg 661915]⟩,
    ⟨0, -1, 9, 5,
      [[tg 118, tg 6618, tg 31324, tg 37824], [tg 228, tg 6728, tg 93828, tg 100328], [tg 241, tg 6741, tg 93841, tg 100341], [tg 119, tg 1424, tg 7919, tg 95024]],
      [tg 374641, tg 381141, tg 468241, tg 474741]⟩]⟩,
  ⟨2, 1, -1, 10, 0, [(0, -10, 1), (1, 1, 1)], 0, -10, 1, 10, 1, 1, 1, 10,
   [⟨2, -1, 0, 11,
      [[tg 2, tg 6502, tg 32378, tg 38878], [tg 5228, tg 11728, tg 37604, tg 44104], [tg 21, tg 6521, tg 93621, tg 100121], [tg 138, tg 6638, tg 93738, tg 100238]],
      [tg 561602, tg 568102, tg 593978, tg 600478]⟩,
    ⟨2, -1, 1, 10,
      [[tg 15, tg 6515, tg 32391, tg 38891], [tg 8, tg 6508, tg 93608, tg 100108], [tg 47, tg 6547, tg 93647, tg 100147], [tg 151, tg 6651, tg 93751, tg 100251]],
      [tg 561615, tg 568115, tg 593991, tg 600491]⟩,
    ⟨2, -1, 2, 3,
      [[tg 28, tg 6528, tg 32404, tg 38904], [tg 60, tg 6560, tg 93660, tg 100160], [tg 133, tg 1438, tg 7933, tg 95038], [tg 164, tg 6664, tg 93764, tg 100264]],
      [tg 561628, tg 568128, tg 594004, tg 600504]⟩,
    ⟨2, -1, 3, 9,
      [[tg 41, tg 6541, tg 32417, tg 38917], [tg 21, tg 6521, tg 93621, tg 100121], [tg 73, tg 6573, tg 93673, tg 100173], [tg 177, tg 6677, tg 93777, tg 100277]],
      [tg 561641, tg 568141, tg 594017, tg 600517]⟩,
    ⟨2, -1, 4, 4,
      [[tg 54, tg 6554, tg 32430, tg 38930], [tg 34, tg 6534, tg 93634, tg 100134], [tg 86, tg 6586, tg 93686, tg 100186], [tg 190, tg 6690, tg 93790, tg 100290]],
      [tg 561654, tg 568154, tg 594030, tg 600530]⟩,
    ⟨2, -1, 5, 8,
      [[tg 67, tg 6567, tg 32443, tg 38943], [tg 93, tg 6593, tg 32469, tg 38969], [tg 47, tg 6547, tg 93647, tg 100147], [tg 99, tg 6599, tg 93699, tg 100199], [tg 203, tg 6703, tg 93803, tg 100303]],
      [tg 748867, tg 755367, tg 781243, tg 787743]⟩,
    ⟨2, -1, 6, 5,
      [[tg 80, tg 6580, tg 32456, tg 38956], [tg 106, tg 6606, tg 32482, tg 38982], [tg 60, tg 6560, tg 93660, tg 100160], [tg 112, tg 6612, tg 93712, tg 100212], [tg 216, tg 6716, tg 93816, tg 100316]],
      [tg 748880, tg 755380, tg 781256, tg 787756]⟩,
    ⟨2, -1, 7, 8,
      [[tg 93, tg 6593, tg 32469, tg 38969], [tg 73, tg 6573, tg 93673, tg 100173], [tg 125, tg 6625, tg 93725, tg 100225], [tg 203, tg 6703, tg 93803, tg 100303], [tg 229, tg 6729, tg 93829, tg 100329]],
      [tg 748893, tg 755393, tg 781269, tg 787769]⟩,
    ⟨2, -1, 8, 6,
      [[tg 106, tg 6606, tg 32482, tg 38982], [tg 86, tg 6586, tg 93686, tg 100186], [tg 125, tg 6625, tg 93725, tg 100225], [tg 216, tg 6716, tg 93816, tg 100316], [tg 242, tg 6742, tg 93842, tg 100342]],
      [tg 748906, tg 755406, tg 781282, tg 787782]⟩,
    ⟨2, -1, 9, 7,
      [[tg 119, tg 6619, tg 32495, tg 38995], [tg 99, tg 6599, tg 93699, tg 100199], [tg 112, tg 6612, tg 93712, tg 100212], [tg 255, tg 6755, tg 93855, tg 100355]],
      [tg 561719, tg 568219, tg 594095, tg 600595]⟩,
    ⟨3, -1, 0, 12,
      [[tg 8, tg 6508, tg 93608, tg 100108], [tg 5234, tg 11734, tg 98834, tg 105334], [tg 151, tg 6651, tg 93751, tg 100251], [tg 268, tg 6768, tg 93868, tg 100368]],
      [tg 561608, tg 568108, tg 655208, tg 661708]⟩,
    ⟨3, -1, 1, 11,
      [[tg 21, tg 6521, tg 93621, tg 100121], [tg 138, tg 6638, tg 93738, tg 100238], [tg 177, tg 6677, tg 93777, tg 100277], [tg 281, tg 6781, tg 93881, tg 100381]],
      [tg 561621, tg 568121, tg 655221, tg 661721]⟩,
    ⟨3, -1, 2, 4,
      [[tg 34, tg 6534, tg 93634, tg 100134], [tg 190, tg 6690, tg 93790, tg 100290], [tg 263, tg 1568, tg 8063, tg 95168], [tg 294, tg 6794, tg 93894, tg 100394]],
      [tg 561634, tg 568134, tg 655234, tg 661734]⟩,
    ⟨3, -1, 3, 10,
      [[tg 47, tg 6547, tg 93647, tg 100147], [tg 151, tg 6651, tg 93751, tg 100251], [tg 203, tg 6703, tg 93803, tg 100303], [tg 307, tg 6807, tg 93907, tg 100407]],
      [tg 561647, tg 568147, tg 655247, tg 661747]⟩,
    ⟨3, -1, 4, 5,
      [[tg 60, tg 6560, tg 93660, tg 100160], [tg 164, tg 6664, tg 93764, tg 100264], [tg 216, tg 6716, tg 93816, tg 100316], [tg 320, tg 6820, tg 93920, tg 100420]],
      [tg 561660, tg 568160, tg 655260, tg 661760]⟩,
    ⟨3, -1, 5, 9,
      [[tg 73, tg 6573, tg 93673, tg 100173], [tg 99, tg 6599, tg 93699, tg 100199], [tg 177, tg 6677, tg 93777, tg 100277], [tg 229, tg 6729, tg 93829, tg 100329], [tg 333, tg 6833, tg 93933, tg 100433]],
      [tg 748873, tg 755373, tg 842473, tg 848973]⟩,
    ⟨3, -1, 6, 6,
      [[tg 86, tg 6586, tg 93686, tg 100186], [tg 112, tg 6612, tg 93712, tg 100212], [tg 190, tg 6690, tg 93790, tg 100290], [tg 242, tg 6742, tg 93842, tg 100342], [tg 346, tg 6846, tg 93946, tg 100446]],
      [tg 748886, tg 755386, tg 842486, tg 848986]⟩,
    ⟨3, -1, 7, 9,
      [[tg 99, tg 6599, tg 93699, tg 100199], [tg 203, tg 6703, tg 93803, tg 100303], [tg 255, tg 6755, tg 93855, tg 100355], [tg 333, tg 6833, tg 93933, tg 100433], [tg 359, tg 6859, tg 93959, tg 100459]],
      [tg 748899, tg 755399, tg 842499, tg 848999]⟩,
    ⟨3, -1, 8, 7,
      [[tg 112, tg 6612, tg 93712, tg 100212], [tg 216, tg 6716, tg 93816, tg 100316], [tg 255, tg 6755, tg 93855, tg 100355], [tg 346, tg 6846, tg 93946, tg 100446], [tg 372, tg 6872, tg 93972, tg 100472]],
      [tg 748912, tg 755412, tg 842512, tg 849012]⟩,
    ⟨3, -1, 9, 8,
      [[tg 125, tg 6625, tg 93725, tg 100225], [tg 229, tg 6729, tg 93829, tg 100329], [tg 242, tg 6742, tg 93842, tg 100342], [tg 385, tg 6885, tg 93985, tg 100485]],
      [tg 561725, tg 568225, tg 655325, tg 661825]⟩,
    ⟨4, -1, 0, 13,
      [[tg 138, tg 6638, tg 93738, tg 100238], [tg 5364, tg 11864, tg 98964, tg 105464], [tg 281, tg 6781, tg 93881, tg 100381], [tg 398, tg 6898, tg 93998, tg 100498]],
      [tg 561738, tg 568238, tg 655338, tg 661838]⟩,
    ⟨4, -1, 1, 12,
      [[tg 151, tg 6651, tg 93751, tg 100251], [tg 268, tg 6768, tg 93868, tg 100368], [tg 307, tg 6807, tg 93907, tg 100407], [tg 411, tg 6911, tg 94011, tg 100511]],
      [tg 561751, tg 568251, tg 655351, tg 661851]⟩,
    ⟨4, -1, 2, 5,
      [[tg 164, tg 6664, tg 93764, tg 100264], [tg 320, tg 6820, tg 93920, tg 100420], [tg 393, tg 1698, tg 8193, tg 95298], [tg 424, tg 6924, tg 94024, tg 100524]],
      [tg 561764, tg 568264, tg 655364, tg 661864]⟩,
    ⟨4, -1, 3, 11,
      [[tg 177, tg 6677, tg 93777, tg 100277], [tg 281, tg 6781, tg 93881, tg 100381], [tg 333, tg 6833, tg 93933, tg 100433], [tg 437, tg 6937, tg 94037, tg 100537]],
      [tg 561777, tg 568277, tg 655377, tg 661877]⟩,
    ⟨4, -1, 4, 6,
      [[tg 190, tg 6690, tg 93790, tg 100290], [tg 294, tg 6794, tg 93894, tg 100394], [tg 346, tg 6846, tg 93946, tg 100446], [tg 450, tg 6950, tg 94050, tg 100550]],
      [tg 561790, tg 568290, tg 655390, tg 661890]⟩,
    ⟨4, -1, 5, 10,
      [[tg 203, tg 6703, tg 93803, tg 100303], [tg 229, tg 6729, tg 93829, tg 100329], [tg 307, tg 6807, tg 93907, tg 100407], [tg 359, tg 6859, tg 93959, tg 100459], [tg 463, tg 6963, tg 94063, tg 100563]],
      [tg 749003, tg 755503, tg 842603, tg 849103]⟩,
    ⟨4, -1, 6, 7,
      [[tg 216, tg 6716, tg 93816, tg 100316], [tg 242, tg 6742, tg 93842, tg 100342], [tg 320, tg 6820, tg 93920, tg 100420], [tg 372, tg 6872, tg 93972, tg 100472], [tg 476, tg 6976, tg 94076, tg 100576]],
      [tg 749016, tg 755516, tg 842616, tg 849116]⟩,
    ⟨4, -1, 7, 10,
      [[tg 229, tg 6729, tg 93829, tg 100329], [tg 333, tg 6833, tg 93933, tg 100433], [tg 385, tg 6885, tg 93985, tg 100485], [tg 463, tg 6963, tg 94063, tg 100563], [tg 489, tg 6989, tg 94089, tg 100589]],
      [tg 749029, tg 755529, tg 842629, tg 849129]⟩,
    ⟨4, -1, 8, 8,
      [[tg 242, tg 6742, tg 93842, tg 100342], [tg 346, tg 6846, tg 93946, tg 100446], [tg 385, tg 6885, tg 93985, tg 100485], [tg 476, tg 6976, tg 94076, tg 100576], [tg 502, tg 7002, tg 94102, tg 100602]],
      [tg 749042, tg 755542, tg 842642, tg 849142]⟩,
    ⟨4, -1, 9, 9,
      [[tg 255, tg 6755, tg 93855, tg 100355], [tg 359, tg 6859, tg 93959, tg 100459], [tg 372, tg 6872, tg 93972, tg 100472], [tg 515, tg 7015, tg 94115, tg 100615]],
      [tg 561855, tg 568355, tg 655455, tg 661955]⟩,
    ⟨5, -1, 0, 14,
      [[tg 268, tg 6768, tg 93868, tg 100368], [tg 5494, tg 11994, tg 99094, tg 105594], [tg 411, tg 6911, tg 94011, tg 100511], [tg 528, tg 7028, tg 94128, tg 100628]],
      [tg 561868, tg 568368, tg 655468, tg 661968]⟩,
    ⟨5, -1, 1, 13,
      [[tg 281, tg 6781, tg 93881, tg 100381], [tg 398, tg 6898, tg 93998, tg 100498], [tg 437, tg 6937, tg 94037, tg 100537], [tg 541, tg 7041, tg 94141, tg 100641]],
      [tg 561881, tg 568381, tg 655481, tg 661981]⟩,
    ⟨5, -1, 2, 6,
      [[tg 294, tg 6794, tg 93894, tg 100394], [tg 450, tg 6950, tg 94050, tg 100550], [tg 523, tg 1828, tg 8323, tg 95428], [tg 554, tg 7054, tg 94154, tg 100654]],
      [tg 561894, tg 568394, tg 655494, tg 661994]⟩,
    ⟨5, -1, 3, 12,
      [[tg 307, tg 6807, tg 93907, tg 100407], [tg 411, tg 6911, tg 94011, tg 100511], [tg 463, tg 6963, tg 94063, tg 100563], [tg 567, tg 7067, tg 94167, tg 100667]],
      [tg 561907, tg 568407, tg 655507, tg 662007]⟩,
    ⟨5, -1, 4, 7,
      [[tg 320, tg 6820, tg 93920, tg 100420], [tg 424, tg 6924, tg 94024, tg 100524], [tg 476, tg 6976, tg 94076, tg 100576], [tg 580, tg 7080, tg 94180, tg 100680]],
      [tg 561920, tg 568420, tg 655520, tg 662020]⟩,
    ⟨5, -1, 5, 11,
      [[tg 333, tg 6833, tg 93933, tg 100433], [tg 359, tg 6859, tg 93959, tg 100459], [tg 437, tg 6937, tg 94037, tg 100537], [tg 489, tg 6989, tg 94089, tg 100589], [tg 593, tg 7093, tg 94193, tg 100693]],
      [tg 749133, tg 755633, tg 842733, tg 849233]⟩,
    ⟨5, -1, 6, 8,
      [[tg 346, tg 6846, tg 93946, tg 100446], [tg 372, tg 6872, tg 93972, tg 100472], [tg 450, tg 6950, tg 94050, tg 100550], [tg 502, tg 7002, tg 94102, tg 100602], [tg 606, tg 7106, tg 94206, tg 100706]],
      [tg 749146, tg 755646, tg 842746, tg 849246]⟩,
    ⟨5, -1, 7, 11,
      [[tg 359, tg 6859, tg 93959, tg 100459], [tg 463, tg 6963, tg 94063, tg 100563], [tg 515, tg 7015, tg 94115, tg 100615], [tg 593, tg 7093, tg 94193, tg 100693], [tg 619, tg 7119, tg 94219, tg 100719]],
      [tg 749159, tg 755659, tg 842759, tg 849259]⟩,
    ⟨5, -1, 8, 9,
      [[tg 372, tg 6872, tg 93972, tg 100472], [tg 476, tg 6976, tg 94076, tg 100576], [tg 515, tg 7015, tg 94115, tg 100615], [tg 606, tg 7106, tg 94206, tg 100706], [tg 632, tg 7132, tg 94232, tg 100732]],
      [tg 749172, tg 755672, tg 842772, tg 849272]⟩,
    ⟨5, -1, 9, 10,
      [[tg 385, tg 6885, tg 93985, tg 100485], [tg 489, tg 6989, tg 94089, tg 100589], [tg 502, tg 7002, tg 94102, tg 100602], [tg 645, tg 7145, tg 94245, tg 100745]],
      [tg 561985, tg 568485, tg 655585, tg 662085]⟩,
    ⟨6, -1, 0, 15,
      [[tg 398, tg 6898, tg 93998, tg 100498], [tg 5624, tg 12124, tg 99224, tg 105724], [tg 541, tg 7041, tg 94141, tg 100641], [tg 658, tg 7158, tg 94258, tg 100758]],
      [tg 561998, tg 568498, tg 655598, tg 662098]⟩,
    ⟨6, -1, 1, 14,
      [[tg 411, tg 6911, tg 94011, tg 100511], [tg 528, tg 7028, tg 94128, tg 100628], [tg 567, tg 7067, tg 94167, tg 100667], [tg 671, tg 7171, tg 94271, tg 100771]],
      [tg 562011, tg 568511, tg 655611, tg 662111]⟩,
    ⟨6, -1, 2, 7,
      [[tg 424, tg 6924, tg 94024, tg 100524], [tg 580, tg 7080, tg 94180, tg 100680], [tg 653, tg 1958, tg 8453, tg 95558], [tg 684, tg 7184, tg 94284, tg 100784]],
      [tg 562024, tg 568524, tg 655624, tg 662124]⟩,
    ⟨6, -1, 3, 13,
      [[tg 437, tg 6937, tg 94037, tg 100537], [tg 541, tg 7041, tg 94141, tg 100641], [tg 593, tg 7093, tg 94193, tg 100693], [tg 697, tg 7197, tg 94297, tg 100797]],
      [tg 562037, tg 568537, tg 655637, tg 662137]⟩,
    ⟨6, -1, 4, 8,
      [[tg 450, tg 6950, tg 94050, tg 100550], [tg 554, tg 7054, tg 94154, tg 100654], [tg 606, tg 7106, tg 94206, tg 100706], [tg 710, tg 7210, tg 94310, tg 100810]],
      [tg 562050, tg 568550, tg 655650, tg 662150]⟩,
    ⟨6, -1, 5, 12,
      [[tg 463, tg 6963, tg 94063, tg 100563], [tg 489, tg 6989, tg 94089, tg 100589], [tg 567, tg 7067, tg 94167, tg 100667], [tg 619, tg 7119, tg 94219, tg 100719], [tg 723, tg 7223, tg 94323, tg 100823]],
      [tg 749263, tg 755763, tg 842863, tg 849363]⟩,
    ⟨6, -1, 6, 9,
      [[tg 476, tg 6976, tg 94076, tg 100576], [tg 502, tg 7002, tg 94102, tg 100602], [tg 580, tg 7080, tg 94180, tg 100680], [tg 632, tg 7132, tg 94232, tg 100732], [tg 736, tg 7236, tg 94336, tg 100836]],
      [tg 749276, tg 755776, tg 842876, tg 849376]⟩,
    ⟨6, -1, 7, 12,
      [[tg 489, tg 6989, tg 94089, tg 100589], [tg 593, tg 7093, tg 94193, tg 100693], [tg 645, tg 7145, tg 94245, tg 100745], [tg 723, tg 7223, tg 94323, tg 100823], [tg 749, tg 7249, tg 94349, tg 100849]],
      [tg 749289, tg 755789, tg 842889, tg 849389]⟩,
    ⟨6, -1, 8, 10,
      [[tg 502, tg 7002, tg 94102, tg 100602], [tg 606, tg 7106, tg 94206, tg 100706], [tg 645, tg 7145, tg 94245, tg 100745], [tg 736, tg 7236, tg 94336, tg 100836], [tg 762, tg 7262, tg 94362, tg 100862]],
      [tg 749302, tg 755802, tg 842902, tg 849402]⟩,
    ⟨6, -1, 9, 11,
      [[tg 515, tg 7015, tg 94115, tg 100615], [tg 619, tg 7119, tg 94219, tg 100719], [tg 632, tg 7132, tg 94232, tg 100732], [tg 775, tg 7275, tg 94375, tg 100875]],
      [tg 562115, tg 568615, tg 655715, tg 662215]⟩,
    ⟨7, -1, 0, 16,
      [[tg 528, tg 7028, tg 94128, tg 100628], [tg 5754, tg 12254, tg 99354, tg 105854], [tg 671, tg 7171, tg 94271, tg 100771], [tg 788, tg 7288, tg 94388, tg 100888]],
      [tg 562128, tg 568628, tg 655728, tg 662228]⟩,
    ⟨7, -1, 1, 15,
      [[tg 541, tg 7041, tg 94141, tg 100641], [tg 658, tg 7158, tg 94258, tg 100758], [tg 697, tg 7197, tg 94297, tg 100797], [tg 801, tg 7301, tg 94401, tg 100901]],
      [tg 562141, tg 568641, tg 655741, tg 662241]⟩,
    ⟨7, -1, 2, 8,
      [[tg 554, tg 7054, tg 94154, tg 100654], [tg 710, tg 7210, tg 94310, tg 100810], [tg 783, tg 2088, tg 8583, tg 95688], [tg 814, tg 7314, tg 94414, tg 100914]],
      [tg 562154, tg 568654, tg 655754, tg 662254]⟩,
    ⟨7, -1, 3, 14,
      [[tg 567, tg 7067, tg 94167, tg 100667], [tg 671, tg 7171, tg 94271, tg 100771], [tg 723, tg 7223, tg 94323, tg 100823], [tg 827, tg 7327, tg 94427, tg 100927]],
      [tg 562167, tg 568667, tg 655767, tg 662267]⟩,
    ⟨7, -1, 4, 9,
      [[tg 580, tg 7080, tg 94180, tg 100680], [tg 684, tg 7184, tg 94284, tg 100784], [tg 736, tg 7236, tg 94336, tg 100836], [tg 840, tg 7340, tg 94440, tg 100940]],
      [tg 562180, tg 568680, tg 655780, tg 662280]⟩,
    ⟨7, -1, 5, 13,
      [[tg 593, tg 7093, tg 94193, tg 100693], [tg 619, tg 7119, tg 94219, tg 100719], [tg 697, tg 7197, tg 94297, tg 100797], [tg 749, tg 7249, tg 94349, tg 100849], [tg 853, tg 7353, tg 94453, tg 100953]],
      [tg 749393, tg 755893, tg 842993, tg 849493]⟩,
    ⟨7, -1, 6, 10,
      [[tg 606, tg 7106, tg 94206, tg 100706], [tg 632, tg 7132, tg 94232, tg 100732], [tg 710, tg 7210, tg 94310, tg 100810], [tg 762, tg 7262, tg 94362, tg 100862], [tg 866, tg 7366, tg 94466, tg 100966]],
      [tg 749406, tg 755906, tg 843006, tg 849506]⟩,
    ⟨7, -1, 7, 13,
      [[tg 619, tg 7119, tg 94219, tg 100719], [tg 723, tg 7223, tg 94323, tg 100823], [tg 775, tg 7275, tg 94375, tg 100875], [tg 853, tg 7353, tg 94453, tg 100953], [tg 879, tg 7379, tg 94479, tg 100979]],
      [tg 749419, tg 755919, tg 843019, tg 849519]⟩,
    ⟨7, -1, 8, 11,
      [[tg 632, tg 7132, tg 94232, tg 100732], [tg 736, tg 7236, tg 94336, tg 100836], [tg 775, tg 7275, tg 94375, tg 100875], [tg 866, tg 7366, tg 94466, tg 100966], [tg 892, tg 7392, tg 94492, tg 100992]],
      [tg 749432, tg 755932, tg 843032, tg 849532]⟩,
    ⟨7, -1, 9, 12,
      [[tg 645, tg 7145, tg 94245, tg 100745], [tg 749, tg 7249, tg 94349, tg 100849], [tg 762, tg 7262, tg 94362, tg 100862], [tg 905, tg 7405, tg 94505, tg 101005]],
      [tg 562245, tg 568745, tg 655845, tg 662345]⟩,
    ⟨8, -1, 0, 17,
      [[tg 658, tg 7158, tg 94258, tg 100758], [tg 5884, tg 12384, tg 99484, tg 105984], [tg 801, tg 7301, tg 94401, tg 100901], [tg 918, tg 7418, tg 94518, tg 101018]],
      [tg 562258, tg 568758, tg 655858, tg 662358]⟩,
    ⟨8, -1, 1, 16,
      [[tg 671, tg 7171, tg 94271, tg 100771], [tg 788, tg 7288, tg 94388, tg 100888], [tg 827, tg 7327, tg 94427, tg 100927], [tg 931, tg 7431, tg 94531, tg 101031]],
      [tg 562271, tg 568771, tg 655871, tg 662371]⟩,
    ⟨8, -1, 2, 9,
      [[tg 684, tg 7184, tg 94284, tg 100784], [tg 840, tg 7340, tg 94440, tg 100940], [tg 913, tg 2218, tg 8713, tg 95818], [tg 944, tg 7444, tg 94544, tg 101044]],
      [tg 562284, tg 568784, tg 655884, tg 662384]⟩,
    ⟨8, -1, 3, 15,
      [[tg 697, tg 7197, tg 94297, tg 100797], [tg 801, tg 7301, tg 94401, tg 100901], [tg 853, tg 7353, tg 94453, tg 100953], [tg 957, tg 7457, tg 94557, tg 101057]],
      [tg 562297, tg 568797, tg 655897, tg 662397]⟩,
    ⟨8, -1, 4, 10,
      [[tg 710, tg 7210, tg 94310, tg 100810], [tg 814, tg 7314, tg 94414, tg 100914], [tg 866, tg 7366, tg 94466, tg 100966], [tg 970, tg 7470, tg 94570, tg 101070]],
      [tg 562310, tg 568810, tg 655910, tg 662410]⟩,
    ⟨8, -1, 5, 14,
      [[tg 723, tg 7223, tg 94323, tg 100823], [tg 749, tg 7249, tg 94349, tg 100849], [tg 827, tg 7327, tg 94427, tg 100927], [tg 879, tg 7379, tg 94479, tg 100979], [tg 983, tg 7483, tg 94583, tg 101083]],
      [tg 749523, tg 756023, tg 843123, tg 849623]⟩,
    ⟨8, -1, 6, 11,
      [[tg 736, tg 7236, tg 94336, tg 100836], [tg 762, tg 7262, tg 94362, tg 100862], [tg 840, tg 7340, tg 94440, tg 100940], [tg 892, tg 7392, tg 94492, tg 100992], [tg 996, tg 7496, tg 94596, tg 101096]],
      [tg 749536, tg 756036, tg 843136, tg 849636]⟩,
    ⟨8, -1, 7, 14,
      [[tg 749, tg 7249, tg 94349, tg 100849], [tg 853, tg 7353, tg 94453, tg 100953], [tg 905, tg 7405, tg 94505, tg 101005], [tg 983, tg 7483, tg 94583, tg 101083], [tg 1009, tg 7509, tg 94609, tg 101109]],
      [tg 749549, tg 756049, tg 843149, tg 849649]⟩,
    ⟨8, -1, 8, 12,
      [[tg 762, tg 7262, tg 94362, tg 100862], [tg 866, tg 7366, tg 94466, tg 100966], [tg 905, tg 7405, tg 94505, tg 101005], [tg 996, tg 7496, tg 94596, tg 101096], [tg 1022, tg 7522, tg 94622, tg 101122]],
      [tg 749562, tg 756062, tg 843162, tg 849662]⟩,
    ⟨8, -1, 9, 13,
      [[tg 775, tg 7275, tg 94375, tg 100875], [tg 879, tg 7379, tg 94479, tg 100979], [tg 892, tg 7392, tg 94492, tg 100992], [tg 1035, tg 7535, tg 94635, tg 101135]],
      [tg 562375, tg 568875, tg 655975, tg 662475]⟩,
    ⟨9, -1, 0, 18,
      [[tg 788, tg 7288, tg 94388, tg 100888], [tg 6014, tg 12514, tg 99614, tg 106114], [tg 931, tg 7431, tg 94531, tg 101031], [tg 1048, tg 7548, tg 94648, tg 101148]],
      [tg 562388, tg 568888, tg 655988, tg 662488]⟩,
    ⟨9, -1, 1, 17,
      [[tg 801, tg 7301, tg 94401, tg 100901], [tg 918, tg 7418, tg 94518, tg 101018], [tg 957, tg 7457, tg 94557, tg 101057], [tg 1061, tg 7561, tg 94661, tg 101161]],
      [tg 562401, tg 568901, tg 656001, tg 662501]⟩,
    ⟨9, -1, 2, 10,
      [[tg 814, tg 7314, tg 94414, tg 100914], [tg 970, tg 7470, tg 94570, tg 101070], [tg 1043, tg 2348, tg 8843, tg 95948], [tg 1074, tg 7574, tg 94674, tg 101174]],
      [tg 562414, tg 568914, tg 656014, tg 662514]⟩,
    ⟨9, -1, 3, 16,
      [[tg 827, tg 7327, tg 94427, tg 100927], [tg 931, tg 7431, tg 94531, tg 101031], [tg 983, tg 7483, tg 94583, tg 101083], [tg 1087, tg 7587, tg 94687, tg 101187]],
      [tg 562427, tg 568927, tg 656027, tg 662527]⟩,
    ⟨9, -1, 4, 11,
      [[tg 840, tg 7340, tg 94440, tg 100940], [tg 944, tg 7444, tg 94544, tg 101044], [tg 996, tg 7496, tg 94596, tg 101096], [tg 1100, tg 7600, tg 94700, tg 101200]],
      [tg 562440, tg 568940, tg 656040, tg 662540]⟩,
    ⟨9, -1, 5, 15,
      [[tg 853, tg 7353, tg 94453, tg 100953], [tg 879, tg 7379, tg 94479, tg 100979], [tg 957, tg 7457, tg 94557, tg 101057], [tg 1009, tg 7509, tg 94609, tg 101109], [tg 1113, tg 7613, tg 94713, tg 101213]],
      [tg 749653, tg 756153, tg 843253, tg 849753]⟩,
    ⟨9, -1, 6, 12,
      [[tg 866, tg 7366, tg 94466, tg 100966], [tg 892, tg 7392, tg 94492, tg 100992], [tg 970, tg 7470, tg 94570, tg 101070], [tg 1022, tg 7522, tg 94622, tg 101122], [tg 1126, tg 7626, tg 94726, tg 101226]],
      [tg 749666, tg 756166, tg 843266, tg 849766]⟩,
    ⟨9, -1, 7, 15,
      [[tg 879, tg 7379, tg 94479, tg 100979], [tg 983, tg 7483, tg 94583, tg 101083], [tg 1035, tg 7535, tg 94635, tg 101135], [tg 1113, tg 7613, tg 94713, tg 101213], [tg 1139, tg 7639, tg 94739, tg 101239]],
      [tg 749679, tg 756179, tg 843279, tg 849779]⟩,
    ⟨9, -1, 8, 13,
      [[tg 892, tg 7392, tg 94492, tg 100992], [tg 996, tg 7496, tg 94596, tg 101096], [tg 1035, tg 7535, tg 94635, tg 101135], [tg 1126, tg 7626, tg 94726, tg 101226], [tg 1152, tg 7652, tg 94752, tg 101252]],
      [tg 749692, tg 756192, tg 843292, tg 849792]⟩,
    ⟨9, -1, 9, 14,
      [[tg 905, tg 7405, tg 94505, tg 101005], [tg 1009, tg 7509, tg 94609, tg 101109], [tg 1022, tg 7522, tg 94622, tg 101122], [tg 1165, tg 7665, tg 94765, tg 101265]],
      [tg 562505, tg 569005, tg 656105, tg 662605]⟩,
    ⟨10, -1, 0, 19,
      [[tg 918, tg 7418, tg 94518, tg 101018], [tg 6144, tg 12644, tg 99744, tg 106244], [tg 1061, tg 7561, tg 94661, tg 101161], [tg 1178, tg 7678, tg 94778, tg 101278]],
      [tg 562518, tg 569018, tg 656118, tg 662618]⟩,
    ⟨10, -1, 1, 18,
      [[tg 931, tg 7431, tg 94531, tg 101031], [tg 1048, tg 7548, tg 94648, tg 101148], [tg 1087, tg 7587, tg 94687, tg 101187], [tg 1191, tg 7691, tg 94791, tg 101291]],
      [tg 562531, tg 569031, tg 656131, tg 662631]⟩,
    ⟨10, -1, 2, 11,
      [[tg 944, tg 7444, tg 94544, tg 101044], [tg 1100, tg 7600, tg 94700, tg 101200], [tg 1173, tg 2478, tg 8973, tg 96078], [tg 1204, tg 7704, tg 94804, tg 101304]],
      [tg 562544, tg 569044, tg 656144, tg 662644]⟩,
    ⟨10, -1, 3, 17,
      [[tg 957, tg 7457, tg 94557, tg 101057], [tg 1061, tg 7561, tg 94661, tg 101161], [tg 1113, tg 7613, tg 94713, tg 101213], [tg 1217, tg 7717, tg 94817, tg 101317]],
      [tg 562557, tg 569057, tg 656157, tg 662657]⟩,
    ⟨10, -1, 4, 12,
      [[tg 970, tg 7470, tg 94570, tg 101070], [tg 1074, tg 7574, tg 94674, tg 101174], [tg 1126, tg 7626, tg 94726, tg 101226], [tg 1230, tg 7730, tg 94830, tg 101330]],
      [tg 562570, tg 569070, tg 656170, tg 662670]⟩,
    ⟨10, -1, 5, 16,
      [[tg 983, tg 7483, tg 94583, tg 101083], [tg 1009, tg 7509, tg 94609, tg 101109], [tg 1087, tg 7587, tg 94687, tg 101187], [tg 1139, tg 7639, tg 94739, tg 101239], [tg 1243, tg 7743, tg 94843, tg 101343]],
      [tg 749783, tg 756283, tg 843383, tg 849883]⟩,
    ⟨10, -1, 6, 13,
      [[tg 996, tg 7496, tg 94596, tg 101096], [tg 1022, tg 7522, tg 94622, tg 101122], [tg 1100, tg 7600, tg 94700, tg 101200], [tg 1152, tg 7652, tg 94752, tg 101252], [tg 1256, tg 7756, tg 94856, tg 101356]],
      [tg 749796, tg 756296, tg 843396, tg 849896]⟩,
    ⟨10, -1, 7, 16,
      [[tg 1009, tg 7509, tg 94609, tg 101109], [tg 1113, tg 7613, tg 94713, tg 101213], [tg 1165, tg 7665, tg 94765, tg 101265], [tg 1243, tg 7743, tg 94843, tg 101343], [tg 1269, tg 7769, tg 94869, tg 101369]],
      [tg 749809, tg 756309, tg 843409, tg 849909]⟩,
    ⟨10, -1, 8, 14,
      [[tg 1022, tg 7522, tg 94622, tg 101122], [tg 1126, tg 7626, tg 94726, tg 101226], [tg 1165, tg 7665, tg 94765, tg 101265], [tg 1256, tg 7756, tg 94856, tg 101356], [tg 1282, tg 7782, tg 94882, tg 101382]],
      [tg 749822, tg 756322, tg 843422, tg 849922]⟩,
    ⟨10, -1, 9, 15,
      [[tg 1035, tg 7535, tg 94635, tg 101135], [tg 1139, tg 7639, tg 94739, tg 101239], [tg 1152, tg 7652, tg 94752, tg 101252], [tg 1295, tg 7795, tg 94895, tg 101395]],
      [tg 562635, tg 569135, tg 656235, tg 662735]⟩,
    ⟨11, -1, 0, 20,
      [[tg 1048, tg 7548, tg 94648, tg 101148], [tg 6274, tg 12774, tg 99874, tg 106374], [tg 1191, tg 7691, tg 94791, tg 101291], [tg 62408, tg 68908, tg 156008, tg 162508]],
      [tg 562648, tg 569148, tg 656248, tg 662748]⟩,
    ⟨11, -1, 1, 19,
      [[tg 1061, tg 7561, tg 94661, tg 101161], [tg 1178, tg 7678, tg 94778, tg 101278], [tg 1217, tg 7717, tg 94817, tg 101317], [tg 62421, tg 68921, tg 156021, tg 162521]],
      [tg 562661, tg 569161, tg 656261, tg 662761]⟩,
    ⟨11, -1, 2, 12,
      [[tg 1074, tg 7574, tg 94674, tg 101174], [tg 1230, tg 7730, tg 94830, tg 101330], [tg 5203, tg 63708, tg 13003, tg 157308], [tg 62434, tg 68934, tg 156034, tg 162534]],
      [tg 562674, tg 569174, tg 656274, tg 662774]⟩,
    ⟨11, -1, 3, 18,
      [[tg 1087, tg 7587, tg 94687, tg 101187], [tg 1191, tg 7691, tg 94791, tg 101291], [tg 1243, tg 7743, tg 94843, tg 101343], [tg 62447, tg 68947, tg 156047, tg 162547]],
      [tg 562687, tg 569187, tg 656287, tg 662787]⟩,
    ⟨11, -1, 4, 13,
      [[tg 1100, tg 7600, tg 94700, tg 101200], [tg 1204, tg 7704, tg 94804, tg 101304], [tg 1256, tg 7756, tg 94856, tg 101356], [tg 62460, tg 68960, tg 156060, tg 162560]],
      [tg 562700, tg 569200, tg 656300, tg 662800]⟩,
    ⟨11, -1, 5, 17,
      [[tg 1113, tg 7613, tg 94713, tg 101213], [tg 1139, tg 7639, tg 94739, tg 101239], [tg 1217, tg 7717, tg 94817, tg 101317], [tg 1269, tg 7769, tg 94869, tg 101369], [tg 62473, tg 68973, tg 156073, tg 162573]],
      [tg 749913, tg 756413, tg 843513, tg 850013]⟩,
    ⟨11, -1, 6, 14,
      [[tg 1126, tg 7626, tg 94726, tg 101226], [tg 1152, tg 7652, tg 94752, tg 101252], [tg 1230, tg 7730, tg 94830, tg 101330], [tg 1282, tg 7782, tg 94882, tg 101382], [tg 62486, tg 68986, tg 156086, tg 162586]],
      [tg 749926, tg 756426, tg 843526, tg 850026]⟩,
    ⟨11, -1, 7, 17,
      [[tg 1139, tg 7639, tg 94739, tg 101239], [tg 1243, tg 7743, tg 94843, tg 101343], [tg 1295, tg 7795, tg 94895, tg 101395], [tg 62473, tg 68973, tg 156073, tg 162573], [tg 62499, tg 68999, tg 156099, tg 162599]],
      [tg 749939, tg 756439, tg 843539, tg 850039]⟩,
    ⟨11, -1, 8, 15,
      [[tg 1152, tg 7652, tg 94752, tg 101252], [tg 1256, tg 7756, tg 94856, tg 101356], [tg 1295, tg 7795, tg 94895, tg 101395], [tg 62486, tg 68986, tg 156086, tg 162586], [tg 62512, tg 69012, tg 156112, tg 162612]],
      [tg 749952, tg 756452, tg 843552, tg 850052]⟩,
    ⟨11, -1, 9, 16,
      [[tg 1165, tg 7665, tg 94765, tg 101265], [tg 1269, tg 7769, tg 94869, tg 101369], [tg 1282, tg 7782, tg 94882, tg 101382], [tg 62525, tg 69025, tg 156125, tg 162625]],
      [tg 562765, tg 569265, tg 656365, tg 662865]⟩]⟩,
  ⟨2, 10, 0, 1, 1, [(1, -1, 1), (0, 10, 1)], 1, -1, 1, 10, 0, 10, 1, 10,
   [⟨2, 1, 0, 11,
      [[tg 4, tg 2479, tg 7804, tg 96079], [tg 159, tg 6659, tg 31365, tg 37865], [tg 22, tg 6522, tg 93622, tg 100122], [tg 139, tg 6639, tg 93739, tg 100239]],
      [tg 561604, tg 564079, tg 569404, tg 657679]⟩,
    ⟨2, 1, 1, 12,
      [[tg 17, tg 2492, tg 7817, tg 96092], [tg 9, tg 6509, tg 93609, tg 100109], [tg 48, tg 6548, tg 93648, tg 100148], [tg 152, tg 6652, tg 93752, tg 100252]],
      [tg 561617, tg 564092, tg 569417, tg 657692]⟩,
    ⟨2, 1, 2, 19,
      [[tg 30, tg 2505, tg 7830, tg 96105], [tg 61, tg 6561, tg 93661, tg 100161], [tg 5204, tg 64879, tg 13004, tg 158479], [tg 165, tg 6665, tg 93765, tg 100265]],
      [tg 187261, tg 564105, tg 280861, tg 657705]⟩,
    ⟨2, 1, 3, 13,
      [[tg 43, tg 2518, tg 7843, tg 96118], [tg 22, tg 6522, tg 93622, tg 100122], [tg 74, tg 6574, tg 93674, tg 100174], [tg 178, tg 6678, tg 93778, tg 100278]],
      [tg 561643, tg 564118, tg 569443, tg 657718]⟩,
    ⟨2, 1, 4, 18,
      [[tg 56, tg 2531, tg 7856, tg 96131], [tg 35, tg 6535, tg 93635, tg 100135], [tg 87, tg 6587, tg 93687, tg 100187], [tg 191, tg 6691, tg 93791, tg 100291]],
      [tg 374487, tg 564131, tg 468087, tg 657731]⟩,
    ⟨2, 1, 5, 14,
      [[tg 69, tg 2544, tg 7869, tg 96144], [tg 95, tg 2570, tg 7895, tg 96170], [tg 48, tg 6548, tg 93648, tg 100148], [tg 100, tg 6600, tg 93700, tg 100200], [tg 204, tg 6704, tg 93804, tg 100304]],
      [tg 748869, tg 751344, tg 756669, tg 844944]⟩,
    ⟨2, 1, 6, 17,
      [[tg 82, tg 2557, tg 7882, tg 96157], [tg 108, tg 2583, tg 7908, tg 96183], [tg 61, tg 6561, tg 93661, tg 100161], [tg 113, tg 6613, tg 93713, tg 100213], [tg 217, tg 6717, tg 93817, tg 100317]],
      [tg 561708, tg 751357, tg 569508, tg 844957]⟩,
    ⟨2, 1, 7, 15,
      [[tg 95, tg 2570, tg 7895, tg 96170], [tg 74, tg 6574, tg 93674, tg 100174], [tg 126, tg 6626, tg 93726, tg 100226], [tg 204, tg 6704, tg 93804, tg 100304], [tg 230, tg 6730, tg 93830, tg 100330]],
      [tg 748895, tg 751370, tg 756695, tg 844970]⟩,
    ⟨2, 1, 8, 17,
      [[tg 108, tg 2583, tg 7908, tg 96183], [tg 87, tg 6587, tg 93687, tg 100187], [tg 126, tg 6626, tg 93726, tg 100226], [tg 217, tg 6717, tg 93817, tg 100317], [tg 243, tg 6743, tg 93843, tg 100343]],
      [tg 748908, tg 751383, tg 756708, tg 844983]⟩,
    ⟨2, 1, 9, 16,
      [[tg 121, tg 2596, tg 7921, tg 96196], [tg 100, tg 6600, tg 93700, tg 100200], [tg 113, tg 6613, tg 93713, tg 100213], [tg 256, tg 6756, tg 93856, tg 100356]],
      [tg 561721, tg 564196, tg 569521, tg 657796]⟩,
    ⟨3, 1, 0, 12,
      [[tg 9, tg 6509, tg 93609, tg 100109], [tg 289, tg 6789, tg 31495, tg 37995], [tg 152, tg 6652, tg 93752, tg 100252], [tg 269, tg 6769, tg 93869, tg 100369]],
      [tg 561609, tg 568109, tg 655209, tg 661709]⟩,
    ⟨3, 1, 1, 13,
      [[tg 22, tg 6522, tg 93622, tg 100122], [tg 139, tg 6639, tg 93739, tg 100239], [tg 178, tg 6678, tg 93778, tg 100278], [tg 282, tg 6782, tg 93882, tg 100382]],
      [tg 561622, tg 568122, tg 655222, tg 661722]⟩,
    ⟨3, 1, 2, 20,
      [[tg 35, tg 6535, tg 93635, tg 100135], [tg 191, tg 6691, tg 93791, tg 100291], [tg 62409, tg 68909, tg 156009, tg 162509], [tg 295, tg 6795, tg 93895, tg 100395]],
      [tg 561635, tg 568135, tg 655235, tg 661735]⟩,
    ⟨3, 1, 3, 14,
      [[tg 48, tg 6548, tg 93648, tg 100148], [tg 152, tg 6652, tg 93752, tg 100252], [tg 204, tg 6704, tg 93804, tg 100304], [tg 308, tg 6808, tg 93908, tg 100408]],
      [tg 561648, tg 568148, tg 655248, tg 661748]⟩,
    ⟨3, 1, 4, 19,
      [[tg 61, tg 6561, tg 93661, tg 100161], [tg 165, tg 6665, tg 93765, tg 100265], [tg 217, tg 6717, tg 93817, tg 100317], [tg 321, tg 6821, tg 93921, tg 100421]],
      [tg 561661, tg 568161, tg 655261, tg 661761]⟩,
    ⟨3, 1, 5, 15,
      [[tg 74, tg 6574, tg 93674, tg 100174], [tg 100, tg 6600, tg 93700, tg 100200], [tg 178, tg 6678, tg 93778, tg 100278], [tg 230, tg 6730, tg 93830, tg 100330], [tg 334, tg 6834, tg 93934, tg 100434]],
      [tg 748874, tg 755374, tg 842474, tg 848974]⟩,
    ⟨3, 1, 6, 18,
      [[tg 87, tg 6587, tg 93687, tg 100187], [tg 113, tg 6613, tg 93713, tg 100213], [tg 191, tg 6691, tg 93791, tg 100291], [tg 243, tg 6743, tg 93843, tg 100343], [tg 347, tg 6847, tg 93947, tg 100447]],
      [tg 748887, tg 755387, tg 842487, tg 848987]⟩,
    ⟨3, 1, 7, 16,
      [[tg 100, tg 6600, tg 93700, tg 100200], [tg 204, tg 6704, tg 93804, tg 100304], [tg 256, tg 6756, tg 93856, tg 100356], [tg 334, tg 6834, tg 93934, tg 100434], [tg 360, tg 6860, tg 93960, tg 100460]],
      [tg 748900, tg 755400, tg 842500, tg 849000]⟩,
    ⟨3, 1, 8, 18,
      [[tg 113, tg 6613, tg 93713, tg 100213], [tg 217, tg 6717, tg 93817, tg 100317], [tg 256, tg 6756, tg 93856, tg 100356], [tg 347, tg 6847, tg 93947, tg 100447], [tg 373, tg 6873, tg 93973, tg 100473]],
      [tg 748913, tg 755413, tg 842513, tg 849013]⟩,
    ⟨3, 1, 9, 17,
      [[tg 126, tg 6626, tg 93726, tg 100226], [tg 230, tg 6730, tg 93830, tg 100330], [tg 243, tg 6743, tg 93843, tg 100343], [tg 386, tg 6886, tg 93986, tg 100486]],
      [tg 561726, tg 568226, tg 655326, tg 661826]⟩,
    ⟨4, 1, 0, 13,
      [[tg 139, tg 6639, tg 93739, tg 100239], [tg 419, tg 6919, tg 31625, tg 38125], [tg 282, tg 6782, tg 93882, tg 100382], [tg 399, tg 6899, tg 93999, tg 100499]],
      [tg 561739, tg 568239, tg 655339, tg 661839]⟩,
    ⟨4, 1, 1, 14,
      [[tg 152, tg 6652, tg 93752, tg 100252], [tg 269, tg 6769, tg 93869, tg 100369], [tg 308, tg 6808, tg 93908, tg 100408], [tg 412, tg 6912, tg 94012, tg 100512]],
      [tg 561752, tg 568252, tg 655352, tg 661852]⟩,
    ⟨4, 1, 2, 21,
      [[tg 165, tg 6665, tg 93765, tg 100265], [tg 321, tg 6821, tg 93921, tg 100421], [tg 62539, tg 69039, tg 156139, tg 162639], [tg 425, tg 6925, tg 94025, tg 100525]],
      [tg 561765, tg 568265, tg 655365, tg 661865]⟩,
    ⟨4, 1, 3, 15,
      [[tg 178, tg 6678, tg 93778, tg 100278], [tg 282, tg 6782, tg 93882, tg 100382], [tg 334, tg 6834, tg 93934, tg 100434], [tg 438, tg 6938, tg 94038, tg 100538]],
      [tg 561778, tg 568278, tg 655378, tg 661878]⟩,
    ⟨4, 1, 4, 20,
      [[tg 191, tg 6691, tg 93791, tg 100291], [tg 295, tg 6795, tg 93895, tg 100395], [tg 347, tg 6847, tg 93947, tg 100447], [tg 451, tg 6951, tg 94051, tg 100551]],
      [tg 561791, tg 568291, tg 655391, tg 661891]⟩,
    ⟨4, 1, 5, 16,
      [[tg 204, tg 6704, tg 93804, tg 100304], [tg 230, tg 6730, tg 93830, tg 100330], [tg 308, tg 6808, tg 93908, tg 100408], [tg 360, tg 6860, tg 93960, tg 100460], [tg 464, tg 6964, tg 94064, tg 100564]],
      [tg 749004, tg 755504, tg 842604, tg 849104]⟩,
    ⟨4, 1, 6, 19,
      [[tg 217, tg 6717, tg 93817, tg 100317], [tg 243, tg 6743, tg 93843, tg 100343], [tg 321, tg 6821, tg 93921, tg 100421], [tg 373, tg 6873, tg 93973, tg 100473], [tg 477, tg 6977, tg 94077, tg 100577]],
      [tg 749017, tg 755517, tg 842617, tg 849117]⟩,
    ⟨4, 1, 7, 17,
      [[tg 230, tg 6730, tg 93830, tg 100330], [tg 334, tg 6834, tg 93934, tg 100434], [tg 386, tg 6886, tg 93986, tg 100486], [tg 464, tg 6964, tg 94064, tg 100564], [tg 490, tg 6990, tg 94090, tg 100590]],
      [tg 749030, tg 755530, tg 842630, tg 849130]⟩,
    ⟨4, 1, 8, 19,
      [[tg 243, tg 6743, tg 93843, tg 100343], [tg 347, tg 6847, tg 93947, tg 100447], [tg 386, tg 6886, tg 93986, tg 100486], [tg 477, tg 6977, tg 94077, tg 100577], [tg 503, tg 7003, tg 94103, tg 100603]],
      [tg 749043, tg 755543, tg 842643, tg 849143]⟩,
    ⟨4, 1, 9, 18,
      [[tg 256, tg 6756, tg 93856, tg 100356], [tg 360, tg 6860, tg 93960, tg 100460], [tg 373, tg 6873, tg 93973, tg 100473], [tg 516, tg 7016, tg 94116, tg 100616]],
      [tg 561856, tg 568356, tg 655456, tg 661956]⟩,
    ⟨5, 1, 0, 14,
      [[tg 269, tg 6769, tg 93869, tg 100369], [tg 549, tg 7049, tg 31755, tg 38255], [tg 412, tg 6912, tg 94012, tg 100512], [tg 529, tg 7029, tg 94129, tg 100629]],
      [tg 561869, tg 568369, tg 655469, tg 661969]⟩,
    ⟨5, 1, 1, 15,
      [[tg 282, tg 6782, tg 93882, tg 100382], [tg 399, tg 6899, tg 93999, tg 100499], [tg 438, tg 6938, tg 94038, tg 100538], [tg 542, tg 7042, tg 94142, tg 100642]],
      [tg 561882, tg 568382, tg 655482, tg 661982]⟩,
    ⟨5, 1, 2, 22,
      [[tg 295, tg 6795, tg 93895, tg 100395], [tg 451, tg 6951, tg 94051, tg 100551], [tg 62669, tg 69169, tg 156269, tg 162769], [tg 555, tg 7055, tg 94155, tg 100655]],
      [tg 561895, tg 568395, tg 655495, tg 661995]⟩,
    ⟨5, 1, 3, 16,
      [[tg 308, tg 6808, tg 93908, tg 100408], [tg 412, tg 6912, tg 94012, tg 100512], [tg 464, tg 6964, tg 94064, tg 100564], [tg 568, tg 7068, tg 94168, tg 100668]],
      [tg 561908, tg 568408, tg 655508, tg 662008]⟩,
    ⟨5, 1, 4, 21,
      [[tg 321, tg 6821, tg 93921, tg 100421], [tg 425, tg 6925, tg 94025, tg 100525], [tg 477, tg 6977, tg 94077, tg 100577], [tg 581, tg 7081, tg 94181, tg 100681]],
      [tg 561921, tg 568421, tg 655521, tg 662021]⟩,
    ⟨5, 1, 5, 17,
      [[tg 334, tg 6834, tg 93934, tg 100434], [tg 360, tg 6860, tg 93960, tg 100460], [tg 438, tg 6938, tg 94038, tg 100538], [tg 490, tg 6990, tg 94090, tg 100590], [tg 594, tg 7094, tg 94194, tg 100694]],
      [tg 749134, tg 755634, tg 842734, tg 849234]⟩,
    ⟨5, 1, 6, 20,
      [[tg 347, tg 6847, tg 93947, tg 100447], [tg 373, tg 6873, tg 93973, tg 100473], [tg 451, tg 6951, tg 94051, tg 100551], [tg 503, tg 7003, tg 94103, tg 100603], [tg 607, tg 7107, tg 94207, tg 100707]],
      [tg 749147, tg 755647, tg 842747, tg 849247]⟩,
    ⟨5, 1, 7, 18,
      [[tg 360, tg 6860, tg 93960, tg 100460], [tg 464, tg 6964, tg 94064, tg 100564], [tg 516, tg 7016, tg 94116, tg 100616], [tg 594, tg 7094, tg 94194, tg 100694], [tg 620, tg 7120, tg 94220, tg 100720]],
      [tg 749160, tg 755660, tg 842760, tg 849260]⟩,
    ⟨5, 1, 8, 20,
      [[tg 373, tg 6873, tg 93973, tg 100473], [tg 477, tg 6977, tg 94077, tg 100577], [tg 516, tg 7016, tg 94116, tg 100616], [tg 607, tg 7107, tg 94207, tg 100707], [tg 633, tg 7133, tg 94233, tg 100733]],
      [tg 749173, tg 755673, tg 842773, tg 849273]⟩,
    ⟨5, 1, 9, 19,
      [[tg 386, tg 6886, tg 93986, tg 100486], [tg 490, tg 6990, tg 94090, tg 100590], [tg 503, tg 7003, tg 94103, tg 100603], [tg 646, tg 7146, tg 94246, tg 100746]],
      [tg 561986, tg 568486, tg 655586, tg 662086]⟩,
    ⟨6, 1, 0, 15,
      [[tg 399, tg 6899, tg 93999, tg 100499], [tg 679, tg 7179, tg 31885, tg 38385], [tg 542, tg 7042, tg 94142, tg 100642], [tg 659, tg 7159, tg 94259, tg 100759]],
      [tg 561999, tg 568499, tg 655599, tg 662099]⟩,
    ⟨6, 1, 1, 16,
      [[tg 412, tg 6912, tg 94012, tg 100512], [tg 529, tg 7029, tg 94129, tg 100629], [tg 568, tg 7068, tg 94168, tg 100668], [tg 672, tg 7172, tg 94272, tg 100772]],
      [tg 562012, tg 568512, tg 655612, tg 662112]⟩,
    ⟨6, 1, 2, 23,
      [[tg 425, tg 6925, tg 94025, tg 100525], [tg 581, tg 7081, tg 94181, tg 100681], [tg 62799, tg 69299, tg 156399, tg 162899], [tg 685, tg 7185, tg 94285, tg 100785]],
      [tg 562025, tg 568525, tg 655625, tg 662125]⟩,
    ⟨6, 1, 3, 17,
      [[tg 438, tg 6938, tg 94038, tg 100538], [tg 542, tg 7042, tg 94142, tg 100642], [tg 594, tg 7094, tg 94194, tg 100694], [tg 698, tg 7198, tg 94298, tg 100798]],
      [tg 562038, tg 568538, tg 655638, tg 662138]⟩,
    ⟨6, 1, 4, 22,
      [[tg 451, tg 6951, tg 94051, tg 100551], [tg 555, tg 7055, tg 94155, tg 100655], [tg 607, tg 7107, tg 94207, tg 100707], [tg 711, tg 7211, tg 94311, tg 100811]],
      [tg 562051, tg 568551, tg 655651, tg 662151]⟩,
    ⟨6, 1, 5, 18,
      [[tg 464, tg 6964, tg 94064, tg 100564], [tg 490, tg 6990, tg 94090, tg 100590], [tg 568, tg 7068, tg 94168, tg 100668], [tg 620, tg 7120, tg 94220, tg 100720], [tg 724, tg 7224, tg 94324, tg 100824]],
      [tg 749264, tg 755764, tg 842864, tg 849364]⟩,
    ⟨6, 1, 6, 21,
      [[tg 477, tg 6977, tg 94077, tg 100577], [tg 503, tg 7003, tg 94103, tg 100603], [tg 581, tg 7081, tg 94181, tg 100681], [tg 633, tg 7133, tg 94233, tg 100733], [tg 737, tg 7237, tg 94337, tg 100837]],
      [tg 749277, tg 755777, tg 842877, tg 849377]⟩,
    ⟨6, 1, 7, 19,
      [[tg 490, tg 6990, tg 94090, tg 100590], [tg 594, tg 7094, tg 94194, tg 100694], [tg 646, tg 7146, tg 94246, tg 100746], [tg 724, tg 7224, tg 94324, tg 100824], [tg 750, tg 7250, tg 94350, tg 100850]],
      [tg 749290, tg 755790, tg 842890, tg 849390]⟩,
    ⟨6, 1, 8, 21,
      [[tg 503, tg 7003, tg 94103, tg 100603], [tg 607, tg 7107, tg 94207, tg 100707], [tg 646, tg 7146, tg 94246, tg 100746], [tg 737, tg 7237, tg 94337, tg 100837], [tg 763, tg 7263, tg 94363, tg 100863]],
      [tg 749303, tg 755803, tg 842903, tg 849403]⟩,
    ⟨6, 1, 9, 20,
      [[tg 516, tg 7016, tg 94116, tg 100616], [tg 620, tg 7120, tg 94220, tg 100720], [tg 633, tg 7133, tg 94233, tg 100733], [tg 776, tg 7276, tg 94376, tg 100876]],
      [tg 562116, tg 568616, tg 655716, tg 662216]⟩,
    ⟨7, 1, 0, 16,
      [[tg 529, tg 7029, tg 94129, tg 100629], [tg 809, tg 7309, tg 32015, tg 38515], [tg 672, tg 7172, tg 94272, tg 100772], [tg 789, tg 7289, tg 94389, tg 100889]],
      [tg 562129, tg 568629, tg 655729, tg 662229]⟩,
    ⟨7, 1, 1, 17,
      [[tg 542, tg 7042, tg 94142, tg 100642], [tg 659, tg 7159, tg 94259, tg 100759], [tg 698, tg 7198, tg 94298, tg 100798], [tg 802, tg 7302, tg 94402, tg 100902]],
      [tg 562142, tg 568642, tg 655742, tg 662242]⟩,
    ⟨7, 1, 2, 24,
      [[tg 555, tg 7055, tg 94155, tg 100655], [tg 711, tg 7211, tg 94311, tg 100811], [tg 62929, tg 69429, tg 156529, tg 163029], [tg 815, tg 7315, tg 94415, tg 100915]],
      [tg 562155, tg 568655, tg 655755, tg 662255]⟩,
    ⟨7, 1, 3, 18,
      [[tg 568, tg 7068, tg 94168, tg 100668], [tg 672, tg 7172, tg 94272, tg 100772], [tg 724, tg 7224, tg 94324, tg 100824], [tg 828, tg 7328, tg 94428, tg 100928]],
      [tg 562168, tg 568668, tg 655768, tg 662268]⟩,
    ⟨7, 1, 4, 23,
      [[tg 581, tg 7081, tg 94181, tg 100681], [tg 685, tg 7185, tg 94285, tg 100785], [tg 737, tg 7237, tg 94337, tg 100837], [tg 841, tg 7341, tg 94441, tg 100941]],
      [tg 562181, tg 568681, tg 655781, tg 662281]⟩,
    ⟨7, 1, 5, 19,
      [[tg 594, tg 7094, tg 94194, tg 100694], [tg 620, tg 7120, tg 94220, tg 100720], [tg 698, tg 7198, tg 94298, tg 100798], [tg 750, tg 7250, tg 94350, tg 100850], [tg 854, tg 7354, tg 94454, tg 100954]],
      [tg 749394, tg 755894, tg 842994, tg 849494]⟩,
    ⟨7, 1, 6, 22,
      [[tg 607, tg 7107, tg 94207, tg 100707], [tg 633, tg 7133, tg 94233, tg 100733], [tg 711, tg 7211, tg 94311, tg 100811], [tg 763, tg 7263, tg 94363, tg 100863], [tg 867, tg 7367, tg 94467, tg 100967]],
      [tg 749407, tg 755907, tg 843007, tg 849507]⟩,
    ⟨7, 1, 7, 20,
      [[tg 620, tg 7120, tg 94220, tg 100720], [tg 724, tg 7224, tg 94324, tg 100824], [tg 776, tg 7276, tg 94376, tg 100876], [tg 854, tg 7354, tg 94454, tg 100954], [tg 880, tg 7380, tg 94480, tg 100980]],
      [tg 749420, tg 755920, tg 843020, tg 849520]⟩,
    ⟨7, 1, 8, 22,
      [[tg 633, tg 7133, tg 94233, tg 100733], [tg 737, tg 7237, tg 94337, tg 100837], [tg 776, tg 7276, tg 94376, tg 100876], [tg 867, tg 7367, tg 94467, tg 100967], [tg 893, tg 7393, tg 94493, tg 100993]],
      [tg 749433, tg 755933, tg 843033, tg 849533]⟩,
    ⟨7, 1, 9, 21,
      [[tg 646, tg 7146, tg 94246, tg 100746], [tg 750, tg 7250, tg 94350, tg 100850], [tg 763, tg 7263, tg 94363, tg 100863], [tg 906, tg 7406, tg 94506, tg 101006]],
      [tg 562246, tg 568746, tg 655846, tg 662346]⟩,
    ⟨8, 1, 0, 17,
      [[tg 659, tg 7159, tg 94259, tg 100759], [tg 939, tg 7439, tg 32145, tg 38645], [tg 802, tg 7302, tg 94402, tg 100902], [tg 919, tg 7419, tg 94519, tg 101019]],
      [tg 562259, tg 568759, tg 655859, tg 662359]⟩,
    ⟨8, 1, 1, 18,
      [[tg 672, tg 7172, tg 94272, tg 100772], [tg 789, tg 7289, tg 94389, tg 100889], [tg 828, tg 7328, tg 94428, tg 100928], [tg 932, tg 7432, tg 94532, tg 101032]],
      [tg 562272, tg 568772, tg 655872, tg 662372]⟩,
    ⟨8, 1, 2, 25,
      [[tg 685, tg 7185, tg 94285, tg 100785], [tg 841, tg 7341, tg 94441, tg 100941], [tg 63059, tg 69559, tg 156659, tg 163159], [tg 945, tg 7445, tg 94545, tg 101045]],
      [tg 562285, tg 568785, tg 655885, tg 662385]⟩,
    ⟨8, 1, 3, 19,
      [[tg 698, tg 7198, tg 94298, tg 100798], [tg 802, tg 7302, tg 94402, tg 100902], [tg 854, tg 7354, tg 94454, tg 100954], [tg 958, tg 7458, tg 94558, tg 101058]],
      [tg 562298, tg 568798, tg 655898, tg 662398]⟩,
    ⟨8, 1, 4, 24,
      [[tg 711, tg 7211, tg 94311, tg 100811], [tg 815, tg 7315, tg 94415, tg 100915], [tg 867, tg 7367, tg 94467, tg 100967], [tg 971, tg 7471, tg 94571, tg 101071]],
      [tg 562311, tg 568811, tg 655911, tg 662411]⟩,
    ⟨8, 1, 5, 20,
      [[tg 724, tg 7224, tg 94324, tg 100824], [tg 750, tg 7250, tg 94350, tg 100850], [tg 828, tg 7328, tg 94428, tg 100928], [tg 880, tg 7380, tg 94480, tg 100980], [tg 984, tg 7484, tg 94584, tg 101084]],
      [tg 749524, tg 756024, tg 843124, tg 849624]⟩,
    ⟨8, 1, 6, 23,
      [[tg 737, tg 7237, tg 94337, tg 100837], [tg 763, tg 7263, tg 94363, tg 100863], [tg 841, tg 7341, tg 94441, tg 100941], [tg 893, tg 7393, tg 94493, tg 100993], [tg 997, tg 7497, tg 94597, tg 101097]],
      [tg 749537, tg 756037, tg 843137, tg 849637]⟩,
    ⟨8, 1, 7, 21,
      [[tg 750, tg 7250, tg 94350, tg 100850], [tg 854, tg 7354, tg 94454, tg 100954], [tg 906, tg 7406, tg 94506, tg 101006], [tg 984, tg 7484, tg 94584, tg 101084], [tg 1010, tg 7510, tg 94610, tg 101110]],
      [tg 749550, tg 756050, tg 843150, tg 849650]⟩,
    ⟨8, 1, 8, 23,
      [[tg 763, tg 7263, tg 94363, tg 100863], [tg 867, tg 7367, tg 94467, tg 100967], [tg 906, tg 7406, tg 94506, tg 101006], [tg 997, tg 7497, tg 94597, tg 101097], [tg 1023, tg 7523, tg 94623, tg 101123]],
      [tg 749563, tg 756063, tg 843163, tg 849663]⟩,
    ⟨8, 1, 9, 22,
      [[tg 776, tg 7276, tg 94376, tg 100876], [tg 880, tg 7380, tg 94480, tg 100980], [tg 893, tg 7393, tg 94493, tg 100993], [tg 1036, tg 7536, tg 94636, tg 101136]],
      [tg 562376, tg 568876, tg 655976, tg 662476]⟩,
    ⟨9, 1, 0, 18,
      [[tg 789, tg 7289, tg 94389, tg 100889], [tg 1069, tg 7569, tg 32275, tg 38775], [tg 932, tg 7432, tg 94532, tg 101032], [tg 1049, tg 7549, tg 94649, tg 101149]],
      [tg 562389, tg 568889, tg 655989, tg 662489]⟩,
    ⟨9, 1, 1, 19,
      [[tg 802, tg 7302, tg 94402, tg 100902], [tg 919, tg 7419, tg 94519, tg 101019], [tg 958, tg 7458, tg 94558, tg 101058], [tg 1062, tg 7562, tg 94662, tg 101162]],
      [tg 562402, tg 568902, tg 656002, tg 662502]⟩,
    ⟨9, 1, 2, 26,
      [[tg 815, tg 7315, tg 94415, tg 100915], [tg 971, tg 7471, tg 94571, tg 101071], [tg 63189, tg 69689, tg 156789, tg 163289], [tg 1075, tg 7575, tg 94675, tg 101175]],
      [tg 562415, tg 568915, tg 656015, tg 662515]⟩,
    ⟨9, 1, 3, 20,
      [[tg 828, tg 7328, tg 94428, tg 100928], [tg 932, tg 7432, tg 94532, tg 101032], [tg 984, tg 7484, tg 94584, tg 101084], [tg 1088, tg 7588, tg 94688, tg 101188]],
      [tg 562428, tg 568928, tg 656028, tg 662528]⟩,
    ⟨9, 1, 4, 25,
      [[tg 841, tg 7341, tg 94441, tg 100941], [tg 945, tg 7445, tg 94545, tg 101045], [tg 997, tg 7497, tg 94597, tg 101097], [tg 1101, tg 7601, tg 94701, tg 101201]],
      [tg 562441, tg 568941, tg 656041, tg 662541]⟩,
    ⟨9, 1, 5, 21,
      [[tg 854, tg 7354, tg 94454, tg 100954], [tg 880, tg 7380, tg 94480, tg 100980], [tg 958, tg 7458, tg 94558, tg 101058], [tg 1010, tg 7510, tg 94610, tg 101110], [tg 1114, tg 7614, tg 94714, tg 101214]],
      [tg 749654, tg 756154, tg 843254, tg 849754]⟩,
    ⟨9, 1, 6, 24,
      [[tg 867, tg 7367, tg 94467, tg 100967], [tg 893, tg 7393, tg 94493, tg 100993], [tg 971, tg 7471, tg 94571, tg 101071], [tg 1023, tg 7523, tg 94623, tg 101123], [tg 1127, tg 7627, tg 94727, tg 101227]],
      [tg 749667, tg 756167, tg 843267, tg 849767]⟩,
    ⟨9, 1, 7, 22,
      [[tg 880, tg 7380, tg 94480, tg 100980], [tg 984, tg 7484, tg 94584, tg 101084], [tg 1036, tg 7536, tg 94636, tg 101136], [tg 1114, tg 7614, tg 94714, tg 101214], [tg 1140, tg 7640, tg 94740, tg 101240]],
      [tg 749680, tg 756180, tg 843280, tg 849780]⟩,
    ⟨9, 1, 8, 24,
      [[tg 893, tg 7393, tg 94493, tg 100993], [tg 997, tg 7497, tg 94597, tg 101097], [tg 1036, tg 7536, tg 94636, tg 101136], [tg 1127, tg 7627, tg 94727, tg 101227], [tg 1153, tg 7653, tg 94753, tg 101253]],
      [tg 749693, tg 756193, tg 843293, tg 849793]⟩,
    ⟨9, 1, 9, 23,
      [[tg 906, tg 7406, tg 94506, tg 101006], [tg 1010, tg 7510, tg 94610, tg 101110], [tg 1023, tg 7523, tg 94623, tg 101123], [tg 1166, tg 7666, tg 94766, tg 101266]],
      [tg 562506, tg 569006, tg 656106, tg 662606]⟩,
    ⟨10, 1, 0, 19,
      [[tg 919, tg 7419, tg 94519, tg 101019], [tg 1199, tg 7699, tg 32405, tg 38905], [tg 1062, tg 7562, tg 94662, tg 101162], [tg 1179, tg 7679, tg 94779, tg 101279]],
      [tg 562519, tg 569019, tg 656119, tg 662619]⟩,
    ⟨10, 1, 1, 20,
      [[tg 932, tg 7432, tg 94532, tg 101032], [tg 1049, tg 7549, tg 94649, tg 101149], [tg 1088, tg 7588, tg 94688, tg 101188], [tg 1192, tg 7692, tg 94792, tg 101292]],
      [tg 562532, tg 569032, tg 656132, tg 662632]⟩,
    ⟨10, 1, 2, 27,
      [[tg 945, tg 7445, tg 94545, tg 101045], [tg 1101, tg 7601, tg 94701, tg 101201], [tg 63319, tg 69819, tg 156919, tg 163419], [tg 1205, tg 7705, tg 94805, tg 101305]],
      [tg 562545, tg 569045, tg 656145, tg 662645]⟩,
    ⟨10, 1, 3, 21,
      [[tg 958, tg 7458, tg 94558, tg 101058], [tg 1062, tg 7562, tg 94662, tg 101162], [tg 1114, tg 7614, tg 94714, tg 101214], [tg 1218, tg 7718, tg 94818, tg 101318]],
      [tg 562558, tg 569058, tg 656158, tg 662658]⟩,
    ⟨10, 1, 4, 26,
      [[tg 971, tg 7471, tg 94571, tg 101071], [tg 1075, tg 7575, tg 94675, tg 101175], [tg 1127, tg 7627, tg 94727, tg 101227], [tg 1231, tg 7731, tg 94831, tg 101331]],
      [tg 562571, tg 569071, tg 656171, tg 662671]⟩,
    ⟨10, 1, 5, 22,
      [[tg 984, tg 7484, tg 94584, tg 101084], [tg 1010, tg 7510, tg 94610, tg 101110], [tg 1088, tg 7588, tg 94688, tg 101188], [tg 1140, tg 7640, tg 94740, tg 101240], [tg 1244, tg 7744, tg 94844, tg 101344]],
      [tg 749784, tg 756284, tg 843384, tg 849884]⟩,
    ⟨10, 1, 6, 25,
      [[tg 997, tg 7497, tg 94597, tg 101097], [tg 1023, tg 7523, tg 94623, tg 101123], [tg 1101, tg 7601, tg 94701, tg 101201], [tg 1153, tg 7653, tg 94753, tg 101253], [tg 1257, tg 7757, tg 94857, tg 101357]],
      [tg 749797, tg 756297, tg 843397, tg 849897]⟩,
    ⟨10, 1, 7, 23,
      [[tg 1010, tg 7510, tg 94610, tg 101110], [tg 1114, tg 7614, tg 94714, tg 101214], [tg 1166, tg 7666, tg 94766, tg 101266], [tg 1244, tg 7744, tg 94844, tg 101344], [tg 1270, tg 7770, tg 94870, tg 101370]],
      [tg 749810, tg 756310, tg 843410, tg 849910]⟩,
    ⟨10, 1, 8, 25,
      [[tg 1023, tg 7523, tg 94623, tg 101123], [tg 1127, tg 7627, tg 94727, tg 101227], [tg 1166, tg 7666, tg 94766, tg 101266], [tg 1257, tg 7757, tg 94857, tg 101357], [tg 1283, tg 7783, tg 94883, tg 101383]],
      [tg 749823, tg 756323, tg 843423, tg 849923]⟩,
    ⟨10, 1, 9, 24,
      [[tg 1036, tg 7536, tg 94636, tg 101136], [tg 1140, tg 7640, tg 94740, tg 101240], [tg 1153, tg 7653, tg 94753, tg 101253], [tg 1296, tg 7796, tg 94896, tg 101396]],
      [tg 562636, tg 569136, tg 656236, tg 662736]⟩,
    ⟨11, 1, 0, 20,
      [[tg 1049, tg 7549, tg 94649, tg 101149], [tg 5229, tg 11729, tg 36435, tg 42935], [tg 1192, tg 7692, tg 94792, tg 101292], [tg 5209, tg 11709, tg 98809, tg 105309]],
      [tg 562649, tg 569149, tg 656249, tg 662749]⟩,
    ⟨11, 1, 1, 21,
      [[tg 1062, tg 7562, tg 94662, tg 101162], [tg 1179, tg 7679, tg 94779, tg 101279], [tg 1218, tg 7718, tg 94818, tg 101318], [tg 5222, tg 11722, tg 98822, tg 105322]],
      [tg 562662, tg 569162, tg 656262, tg 662762]⟩,
    ⟨11, 1, 2, 28,
      [[tg 1075, tg 7575, tg 94675, tg 101175], [tg 1231, tg 7731, tg 94831, tg 101331], [tg 63449, tg 69949, tg 157049, tg 163549], [tg 5235, tg 11735, tg 98835, tg 105335]],
      [tg 562675, tg 569175, tg 656275, tg 662775]⟩,
    ⟨11, 1, 3, 22,
      [[tg 1088, tg 7588, tg 94688, tg 101188], [tg 1192, tg 7692, tg 94792, tg 101292], [tg 1244, tg 7744, tg 94844, tg 101344], [tg 5248, tg 11748, tg 98848, tg 105348]],
      [tg 562688, tg 569188, tg 656288, tg 662788]⟩,
    ⟨11, 1, 4, 27,
      [[tg 1101, tg 7601, tg 94701, tg 101201], [tg 1205, tg 7705, tg 94805, tg 101305], [tg 1257, tg 7757, tg 94857, tg 101357], [tg 5261, tg 11761, tg 98861, tg 105361]],
      [tg 562701, tg 569201, tg 656301, tg 662801]⟩,
    ⟨11, 1, 5, 23,
      [[tg 1114, tg 7614, tg 94714, tg 101214], [tg 1140, tg 7640, tg 94740, tg 101240], [tg 1218, tg 7718, tg 94818, tg 101318], [tg 1270, tg 7770, tg 94870, tg 101370], [tg 5274, tg 11774, tg 98874, tg 105374]],
      [tg 749914, tg 756414, tg 843514, tg 850014]⟩,
    ⟨11, 1, 6, 26,
      [[tg 1127, tg 7627, tg 94727, tg 101227], [tg 1153, tg 7653, tg 94753, tg 101253], [tg 1231, tg 7731, tg 94831, tg 101331], [tg 1283, tg 7783, tg 94883, tg 101383], [tg 5287, tg 11787, tg 98887, tg 105387]],
      [tg 749927, tg 756427, tg 843527, tg 850027]⟩,
    ⟨11, 1, 7, 24,
      [[tg 1140, tg 7640, tg 94740, tg 101240], [tg 1244, tg 7744, tg 94844, tg 101344], [tg 1296, tg 7796, tg 94896, tg 101396], [tg 5274, tg 11774, tg 98874, tg 105374], [tg 5300, tg 11800, tg 98900, tg 105400]],
      [tg 749940, tg 756440, tg 843540, tg 850040]⟩,
    ⟨11, 1, 8, 26,
      [[tg 1153, tg 7653, tg 94753, tg 101253], [tg 1257, tg 7757, tg 94857, tg 101357], [tg 1296, tg 7796, tg 94896, tg 101396], [tg 5287, tg 11787, tg 98887, tg 105387], [tg 5313, tg 11813, tg 98913, tg 105413]],
      [tg 749953, tg 756453, tg 843553, tg 850053]⟩,
    ⟨11, 1, 9, 25,
      [[tg 1166, tg 7666, tg 94766, tg 101266], [tg 1270, tg 7770, tg 94870, tg 101370], [tg 1283, tg 7783, tg 94883, tg 101383], [tg 5326, tg 11826, tg 98926, tg 105426]],
      [tg 562766, tg 569266, tg 656366, tg 662866]⟩]⟩,
  ⟨2, 1, 1, -1, 1, [(1, 1, 1), (-1, 1, 1)], 1, 1, 1, 2, -1, 1, 1, 2,
   [⟨0, 1, 0, 10,
      [[tg 5, tg 1440, tg 7805, tg 95040], [tg 26, tg 1330, tg 2631, tg 32666], [tg 23, tg 6523, tg 93623, tg 100123], [tg 4, tg 6504, tg 31340, tg 37840]],
      [tg 374426, tg 375730, tg 377031, tg 407066]⟩,
    ⟨0, 1, 1, 11,
      [[tg 18, tg 1453, tg 7818, tg 95053], [tg 10, tg 6510, tg 93610, tg 100110], [tg 49, tg 6549, tg 93649, tg 100149], [tg 17, tg 6517, tg 31353, tg 37853]],
      [tg 374410, tg 380910, tg 468010, tg 474510]⟩,
    ⟨0, 1, 2, 19,
      [[tg 31, tg 1466, tg 7831, tg 95066], [tg 62, tg 6562, tg 93662, tg 100162], [tg 140, tg 6640, tg 93740, tg 100240], [tg 30, tg 6530, tg 31366, tg 37866]],
      [tg 187262, tg 193762, tg 280862, tg 287362]⟩,
    ⟨0, 1, 3, 12,
      [[tg 44, tg 1479, tg 7844, tg 95079], [tg 23, tg 6523, tg 93623, tg 100123], [tg 75, tg 6575, tg 93675, tg 100175], [tg 43, tg 6543, tg 31379, tg 37879]],
      [tg 374423, tg 380923, tg 468023, tg 474523]⟩,
    ⟨0, 1, 4, 18,
      [[tg 57, tg 1492, tg 7857, tg 95092], [tg 36, tg 6536, tg 93636, tg 100136], [tg 88, tg 6588, tg 93688, tg 100188], [tg 56, tg 6556, tg 31392, tg 37892]],
      [tg 374488, tg 380988, tg 468088, tg 474588]⟩,
    ⟨0, 1, 5, 13,
      [[tg 70, tg 1505, tg 7870, tg 95105], [tg 96, tg 1531, tg 7896, tg 95131], [tg 49, tg 6549, tg 93649, tg 100149], [tg 101, tg 6601, tg 93701, tg 100201], [tg 69, tg 6569, tg 31405, tg 37905]],
      [tg 374449, tg 380949, tg 468049, tg 474549]⟩,
    ⟨0, 1, 6, 17,
      [[tg 83, tg 1518, tg 7883, tg 95118], [tg 109, tg 1544, tg 7909, tg 95144], [tg 62, tg 6562, tg 93662, tg 100162], [tg 114, tg 6614, tg 93714, tg 100214], [tg 82, tg 6582, tg 31418, tg 37918]],
      [tg 561709, tg 563144, tg 569509, tg 656744]⟩,
    ⟨0, 1, 7, 14,
      [[tg 96, tg 1531, tg 7896, tg 95131], [tg 75, tg 6575, tg 93675, tg 100175], [tg 127, tg 6627, tg 93727, tg 100227], [tg 69, tg 6569, tg 31405, tg 37905], [tg 95, tg 6595, tg 31431, tg 37931]],
      [tg 561675, tg 568175, tg 655275, tg 661775]⟩,
    ⟨0, 1, 8, 16,
      [[tg 109, tg 1544, tg 7909, tg 95144], [tg 88, tg 6588, tg 93688, tg 100188], [tg 127, tg 6627, tg 93727, tg 100227], [tg 82, tg 6582, tg 31418, tg 37918], [tg 108, tg 6608, tg 31444, tg 37944]],
      [tg 374527, tg 381027, tg 468127, tg 474627]⟩,
    ⟨0, 1, 9, 15,
      [[tg 122, tg 1557, tg 7922, tg 95157], [tg 101, tg 6601, tg 93701, tg 100201], [tg 114, tg 6614, tg 93714, tg 100214], [tg 121, tg 6621, tg 31457, tg 37957]],
      [tg 374501, tg 381001, tg 468101, tg 474601]⟩,
    ⟨0, 2, 0, 20,
      [[tg 62410, tg 68910, tg 156010, tg 162510], [tg 36, tg 6536, tg 93636, tg 100136], [tg 153, tg 6653, tg 93753, tg 100253], [tg 5210, tg 11710, tg 98810, tg 105310]],
      [tg 374436, tg 380936, tg 468036, tg 474536]⟩,
    ⟨0, 2, 1, 21,
      [[tg 62423, tg 68923, tg 156023, tg 162523], [tg 140, tg 6640, tg 93740, tg 100240], [tg 179, tg 6679, tg 93779, tg 100279], [tg 5223, tg 11723, tg 98823, tg 105323]],
      [tg 374540, tg 381040, tg 468140, tg 474640]⟩,
    ⟨0, 2, 2, 29,
      [[tg 62436, tg 68936, tg 156036, tg 162536], [tg 192, tg 6692, tg 93792, tg 100292], [tg 67610, tg 74110, tg 161210, tg 167710], [tg 5236, tg 11736, tg 98836, tg 105336]],
      [tg 187392, tg 193892, tg 280992, tg 287492]⟩,
    ⟨0, 2, 3, 22,
      [[tg 62449, tg 68949, tg 156049, tg 162549], [tg 153, tg 6653, tg 93753, tg 100253], [tg 205, tg 6705, tg 93805, tg 100305], [tg 5249, tg 11749, tg 98849, tg 105349]],
      [tg 374553, tg 381053, tg 468153, tg 474653]⟩,
    ⟨0, 2, 4, 28,
      [[tg 62462, tg 68962, tg 156062, tg 162562], [tg 166, tg 6666, tg 93766, tg 100266], [tg 218, tg 6718, tg 93818, tg 100318], [tg 5262, tg 11762, tg 98862, tg 105362]],
      [tg 374618, tg 381118, tg 468218, tg 474718]⟩,
    ⟨0, 2, 5, 23,
      [[tg 62475, tg 68975, tg 156075, tg 162575], [tg 62501, tg 69001, tg 156101, tg 162601], [tg 179, tg 6679, tg 93779, tg 100279], [tg 231, tg 6731, tg 93831, tg 100331], [tg 5275, tg 11775, tg 98875, tg 105375]],
      [tg 374579, tg 381079, tg 468179, tg 474679]⟩,
    ⟨0, 2, 6, 27,
      [[tg 62488, tg 68988, tg 156088, tg 162588], [tg 62514, tg 69014, tg 156114, tg 162614], [tg 192, tg 6692, tg 93792, tg 100292], [tg 244, tg 6744, tg 93844, tg 100344], [tg 5288, tg 11788, tg 98888, tg 105388]],
      [tg 624114, tg 630614, tg 717714, tg 724214]⟩,
    ⟨0, 2, 7, 24,
      [[tg 62501, tg 69001, tg 156101, tg 162601], [tg 205, tg 6705, tg 93805, tg 100305], [tg 257, tg 6757, tg 93857, tg 100357], [tg 5275, tg 11775, tg 98875, tg 105375], [tg 5301, tg 11801, tg 98901, tg 105401]],
      [tg 561805, tg 568305, tg 655405, tg 661905]⟩,
    ⟨0, 2, 8, 26,
      [[tg 62514, tg 69014, tg 156114, tg 162614], [tg 218, tg 6718, tg 93818, tg 100318], [tg 257, tg 6757, tg 93857, tg 100357], [tg 5288, tg 11788, tg 98888, tg 105388], [tg 5314, tg 11814, tg 98914, tg 105414]],
      [tg 374657, tg 381157, tg 468257, tg 474757]⟩,
    ⟨0, 2, 9, 25,
      [[tg 62527, tg 69027, tg 156127, tg 162627], [tg 231, tg 6731, tg 93831, tg 100331], [tg 244, tg 6744, tg 93844, tg 100344], [tg 5327, tg 11827, tg 98927, tg 105427]],
      [tg 374631, tg 381131, tg 468231, tg 474731]⟩]⟩,
  ⟨2, -1, 1, -10, 0, [(0, 10, 1), (-1, -1, 1)], 0, 10, 1, 10, -1, -1, 1, 10,
   [⟨-11, 1, 0, 20,
      [[tg 63581, tg 70081, tg 157181, tg 163681], [tg 5232, tg 64907, tg 13032, tg 158507], [tg 24, tg 6524, tg 93624, tg 100124], [tg 141, tg 6641, tg 93741, tg 100241]],
      [tg 379632, tg 439307, tg 387432, tg 532907]⟩,
    ⟨-11, 1, 1, 21,
      [[tg 63594, tg 70094, tg 157194, tg 163694], [tg 11, tg 6511, tg 93611, tg 100111], [tg 50, tg 6550, tg 93650, tg 100150], [tg 154, tg 6654, tg 93754, tg 100254]],
      [tg 374411, tg 380911, tg 468011, tg 474511]⟩,
    ⟨-11, 1, 2, 28,
      [[tg 63607, tg 70107, tg 157207, tg 163707], [tg 63, tg 6563, tg 93663, tg 100163], [tg 5341, tg 11841, tg 98941, tg 105441], [tg 167, tg 6667, tg 93767, tg 100267]],
      [tg 187263, tg 193763, tg 280863, tg 287363]⟩,
    ⟨-11, 1, 3, 22,
      [[tg 63620, tg 70120, tg 157220, tg 163720], [tg 24, tg 6524, tg 93624, tg 100124], [tg 76, tg 6576, tg 93676, tg 100176], [tg 180, tg 6680, tg 93780, tg 100280]],
      [tg 374424, tg 380924, tg 468024, tg 474524]⟩,
    ⟨-11, 1, 4, 27,
      [[tg 63633, tg 70133, tg 157233, tg 163733], [tg 37, tg 6537, tg 93637, tg 100137], [tg 89, tg 6589, tg 93689, tg 100189], [tg 193, tg 6693, tg 93793, tg 100293]],
      [tg 374489, tg 380989, tg 468089, tg 474589]⟩,
    ⟨-11, 1, 5, 23,
      [[tg 63646, tg 70146, tg 157246, tg 163746], [tg 63672, tg 70172, tg 157272, tg 163772], [tg 50, tg 6550, tg 93650, tg 100150], [tg 102, tg 6602, tg 93702, tg 100202], [tg 206, tg 6706, tg 93806, tg 100306]],
      [tg 374450, tg 380950, tg 468050, tg 474550]⟩,
    ⟨-11, 1, 6, 26,
      [[tg 63659, tg 70159, tg 157259, tg 163759], [tg 63685, tg 70185, tg 157285, tg 163785], [tg 63, tg 6563, tg 93663, tg 100163], [tg 115, tg 6615, tg 93715, tg 100215], [tg 219, tg 6719, tg 93819, tg 100319]],
      [tg 187315, tg 193815, tg 280915, tg 287415]⟩,
    ⟨-11, 1, 7, 23,
      [[tg 63672, tg 70172, tg 157272, tg 163772], [tg 76, tg 6576, tg 93676, tg 100176], [tg 128, tg 6628, tg 93728, tg 100228], [tg 206, tg 6706, tg 93806, tg 100306], [tg 232, tg 6732, tg 93832, tg 100332]],
      [tg 187406, tg 193906, tg 281006, tg 287506]⟩,
    ⟨-11, 1, 8, 25,
      [[tg 63685, tg 70185, tg 157285, tg 163785], [tg 89, tg 6589, tg 93689, tg 100189], [tg 128, tg 6628, tg 93728, tg 100228], [tg 219, tg 6719, tg 93819, tg 100319], [tg 245, tg 6745, tg 93845, tg 100345]],
      [tg 374528, tg 381028, tg 468128, tg 474628]⟩,
    ⟨-11, 1, 9, 24,
      [[tg 63698, tg 70198, tg 157298, tg 163798], [tg 102, tg 6602, tg 93702, tg 100202], [tg 115, tg 6615, tg 93715, tg 100215], [tg 258, tg 6758, tg 93858, tg 100358]],
      [tg 374502, tg 381002, tg 468102, tg 474602]⟩,
    ⟨-10, 1, 0, 19,
      [[tg 11, tg 6511, tg 93611, tg 100111], [tg 1202, tg 1337, tg 9002, tg 94937], [tg 154, tg 6654, tg 93754, tg 100254], [tg 271, tg 6771, tg 93871, tg 100371]],
      [tg 375602, tg 375737, tg 383402, tg 469337]⟩,
    ⟨-10, 1, 1, 20,
      [[tg 24, tg 6524, tg 93624, tg 100124], [tg 141, tg 6641, tg 93741, tg 100241], [tg 180, tg 6680, tg 93780, tg 100280], [tg 284, tg 6784, tg 93884, tg 100384]],
      [tg 374541, tg 381041, tg 468141, tg 474641]⟩,
    ⟨-10, 1, 2, 27,
      [[tg 37, tg 6537, tg 93637, tg 100137], [tg 193, tg 6693, tg 93793, tg 100293], [tg 5471, tg 11971, tg 99071, tg 105571], [tg 297, tg 6797, tg 93897, tg 100397]],
      [tg 187393, tg 193893, tg 280993, tg 287493]⟩,
    ⟨-10, 1, 3, 21,
      [[tg 50, tg 6550, tg 93650, tg 100150], [tg 154, tg 6654, tg 93754, tg 100254], [tg 206, tg 6706, tg 93806, tg 100306], [tg 310, tg 6810, tg 93910, tg 100410]],
      [tg 374554, tg 381054, tg 468154, tg 474654]⟩,
    ⟨-10, 1, 4, 26,
      [[tg 63, tg 6563, tg 93663, tg 100163], [tg 167, tg 6667, tg 93767, tg 100267], [tg 219, tg 6719, tg 93819, tg 100319], [tg 323, tg 6823, tg 93923, tg 100423]],
      [tg 374619, tg 381119, tg 468219, tg 474719]⟩,
    ⟨-10, 1, 5, 22,
      [[tg 76, tg 6576, tg 93676, tg 100176], [tg 102, tg 6602, tg 93702, tg 100202], [tg 180, tg 6680, tg 93780, tg 100280], [tg 232, tg 6732, tg 93832, tg 100332], [tg 336, tg 6836, tg 93936, tg 100436]],
      [tg 374580, tg 381080, tg 468180, tg 474680]⟩,
    ⟨-10, 1, 6, 25,
      [[tg 89, tg 6589, tg 93689, tg 100189], [tg 115, tg 6615, tg 93715, tg 100215], [tg 193, tg 6693, tg 93793, tg 100293], [tg 245, tg 6745, tg 93845, tg 100345], [tg 349, tg 6849, tg 93949, tg 100449]],
      [tg 187445, tg 193945, tg 281045, tg 287545]⟩,
    ⟨-10, 1, 7, 22,
      [[tg 102, tg 6602, tg 93702, tg 100202], [tg 206, tg 6706, tg 93806, tg 100306], [tg 258, tg 6758, tg 93858, tg 100358], [tg 336, tg 6836, tg 93936, tg 100436], [tg 362, tg 6862, tg 93962, tg 100462]],
      [tg 187536, tg 194036, tg 281136, tg 287636]⟩,
    ⟨-10, 1, 8, 24,
      [[tg 115, tg 6615, tg 93715, tg 100215], [tg 219, tg 6719, tg 93819, tg 100319], [tg 258, tg 6758, tg 93858, tg 100358], [tg 349, tg 6849, tg 93949, tg 100449], [tg 375, tg 6875, tg 93975, tg 100475]],
      [tg 374658, tg 381158, tg 468258, tg 474758]⟩,
    ⟨-10, 1, 9, 23,
      [[tg 128, tg 6628, tg 93728, tg 100228], [tg 232, tg 6732, tg 93832, tg 100332], [tg 245, tg 6745, tg 93845, tg 100345], [tg 388, tg 6888, tg 93988, tg 100488]],
      [tg 374632, tg 381132, tg 468232, tg 474732]⟩,
    ⟨-9, 1, 0, 18,
      [[tg 141, tg 6641, tg 93741, tg 100241], [tg 1072, tg 1467, tg 8872, tg 95067], [tg 284, tg 6784, tg 93884, tg 100384], [tg 401, tg 6901, tg 94001, tg 100501]],
      [tg 375472, tg 375867, tg 383272, tg 469467]⟩,
    ⟨-9, 1, 1, 19,
      [[tg 154, tg 6654, tg 93754, tg 100254], [tg 271, tg 6771, tg 93871, tg 100371], [tg 310, tg 6810, tg 93910, tg 100410], [tg 414, tg 6914, tg 94014, tg 100514]],
      [tg 374671, tg 381171, tg 468271, tg 474771]⟩,
    ⟨-9, 1, 2, 26,
      [[tg 167, tg 6667, tg 93767, tg 100267], [tg 323, tg 6823, tg 93923, tg 100423], [tg 5601, tg 12101, tg 99201, tg 105701], [tg 427, tg 6927, tg 94027, tg 100527]],
      [tg 187523, tg 194023, tg 281123, tg 287623]⟩,
    ⟨-9, 1, 3, 20,
      [[tg 180, tg 6680, tg 93780, tg 100280], [tg 284, tg 6784, tg 93884, tg 100384], [tg 336, tg 6836, tg 93936, tg 100436], [tg 440, tg 6940, tg 94040, tg 100540]],
      [tg 374684, tg 381184, tg 468284, tg 474784]⟩,
    ⟨-9, 1, 4, 25,
      [[tg 193, tg 6693, tg 93793, tg 100293], [tg 297, tg 6797, tg 93897, tg 100397], [tg 349, tg 6849, tg 93949, tg 100449], [tg 453, tg 6953, tg 94053, tg 100553]],
      [tg 374749, tg 381249, tg 468349, tg 474849]⟩,
    ⟨-9, 1, 5, 21,
      [[tg 206, tg 6706, tg 93806, tg 100306], [tg 232, tg 6732, tg 93832, tg 100332], [tg 310, tg 6810, tg 93910, tg 100410], [tg 362, tg 6862, tg 93962, tg 100462], [tg 466, tg 6966, tg 94066, tg 100566]],
      [tg 374710, tg 381210, tg 468310, tg 474810]⟩,
    ⟨-9, 1, 6, 24,
      [[tg 219, tg 6719, tg 93819, tg 100319], [tg 245, tg 6745, tg 93845, tg 100345], [tg 323, tg 6823, tg 93923, tg 100423], [tg 375, tg 6875, tg 93975, tg 100475], [tg 479, tg 6979, tg 94079, tg 100579]],
      [tg 187575, tg 194075, tg 281175, tg 287675]⟩,
    ⟨-9, 1, 7, 21,
      [[tg 232, tg 6732, tg 93832, tg 100332], [tg 336, tg 6836, tg 93936, tg 100436], [tg 388, tg 6888, tg 93988, tg 100488], [tg 466, tg 6966, tg 94066, tg 100566], [tg 492, tg 6992, tg 94092, tg 100592]],
      [tg 187666, tg 194166, tg 281266, tg 287766]⟩,
    ⟨-9, 1, 8, 23,
      [[tg 245, tg 6745, tg 93845, tg 100345], [tg 349, tg 6849, tg 93949, tg 100449], [tg 388, tg 6888, tg 93988, tg 100488], [tg 479, tg 6979, tg 94079, tg 100579], [tg 505, tg 7005, tg 94105, tg 100605]],
      [tg 374788, tg 381288, tg 468388, tg 474888]⟩,
    ⟨-9, 1, 9, 22,
      [[tg 258, tg 6758, tg 93858, tg 100358], [tg 362, tg 6862, tg 93962, tg 100462], [tg 375, tg 6875, tg 93975, tg 100475], [tg 518, tg 7018, tg 94118, tg 100618]],
      [tg 374762, tg 381262, tg 468362, tg 474862]⟩,
    ⟨-8, 1, 0, 17,
      [[tg 271, tg 6771, tg 93871, tg 100371], [tg 942, tg 1597, tg 8742, tg 95197], [tg 414, tg 6914, tg 94014, tg 100514], [tg 531, tg 7031, tg 94131, tg 100631]],
      [tg 375342, tg 375997, tg 383142, tg 469597]⟩,
    ⟨-8, 1, 1, 18,
      [[tg 284, tg 6784, tg 93884, tg 100384], [tg 401, tg 6901, tg 94001, tg 100501], [tg 440, tg 6940, tg 94040, tg 100540], [tg 544, tg 7044, tg 94144, tg 100644]],
      [tg 374801, tg 381301, tg 468401, tg 474901]⟩,
    ⟨-8, 1, 2, 25,
      [[tg 297, tg 6797, tg 93897, tg 100397], [tg 453, tg 6953, tg 94053, tg 100553], [tg 5731, tg 12231, tg 99331, tg 105831], [tg 557, tg 7057, tg 94157, tg 100657]],
      [tg 187653, tg 194153, tg 281253, tg 287753]⟩,
    ⟨-8, 1, 3, 19,
      [[tg 310, tg 6810, tg 93910, tg 100410], [tg 414, tg 6914, tg 94014, tg 100514], [tg 466, tg 6966, tg 94066, tg 100566], [tg 570, tg 7070, tg 94170, tg 100670]],
      [tg 374814, tg 381314, tg 468414, tg 474914]⟩,
    ⟨-8, 1, 4, 24,
      [[tg 323, tg 6823, tg 93923, tg 100423], [tg 427, tg 6927, tg 94027, tg 100527], [tg 479, tg 6979, tg 94079, tg 100579], [tg 583, tg 7083, tg 94183, tg 100683]],
      [tg 374879, tg 381379, tg 468479, tg 474979]⟩,
    ⟨-8, 1, 5, 20,
      [[tg 336, tg 6836, tg 93936, tg 100436], [tg 362, tg 6862, tg 93962, tg 100462], [tg 440, tg 6940, tg 94040, tg 100540], [tg 492, tg 6992, tg 94092, tg 100592], [tg 596, tg 7096, tg 94196, tg 100696]],
      [tg 374840, tg 381340, tg 468440, tg 474940]⟩,
    ⟨-8, 1, 6, 23,
      [[tg 349, tg 6849, tg 93949, tg 100449], [tg 375, tg 6875, tg 93975, tg 100475], [tg 453, tg 6953, tg 94053, tg 100553], [tg 505, tg 7005, tg 94105, tg 100605], [tg 609, tg 7109, tg 94209, tg 100709]],
      [tg 187705, tg 194205, tg 281305, tg 287805]⟩,
    ⟨-8, 1, 7, 20,
      [[tg 362, tg 6862, tg 93962, tg 100462], [tg 466, tg 6966, tg 94066, tg 100566], [tg 518, tg 7018, tg 94118, tg 100618], [tg 596, tg 7096, tg 94196, tg 100696], [tg 622, tg 7122, tg 94222, tg 100722]],
      [tg 187796, tg 194296, tg 281396, tg 287896]⟩,
    ⟨-8, 1, 8, 22,
      [[tg 375, tg 6875, tg 93975, tg 100475], [tg 479, tg 6979, tg 94079, tg 100579], [tg 518, tg 7018, tg 94118, tg 100618], [tg 609, tg 7109, tg 94209, tg 100709], [tg 635, tg 7135, tg 94235, tg 100735]],
      [tg 374918, tg 381418, tg 468518, tg 475018]⟩,
    ⟨-8, 1, 9, 21,
      [[tg 388, tg 6888, tg 93988, tg 100488], [tg 492, tg 6992, tg 94092, tg 100592], [tg 505, tg 7005, tg 94105, tg 100605], [tg 648, tg 7148, tg 94248, tg 100748]],
      [tg 374892, tg 381392, tg 468492, tg 474992]⟩,
    ⟨-7, 1, 0, 16,
      [[tg 401, tg 6901, tg 94001, tg 100501], [tg 812, tg 1727, tg 8612, tg 95327], [tg 544, tg 7044, tg 94144, tg 100644], [tg 661, tg 7161, tg 94261, tg 100761]],
      [tg 375212, tg 376127, tg 383012, tg 469727]⟩,
    ⟨-7, 1, 1, 17,
      [[tg 414, tg 6914, tg 94014, tg 100514], [tg 531, tg 7031, tg 94131, tg 100631], [tg 570, tg 7070, tg 94170, tg 100670], [tg 674, tg 7174, tg 94274, tg 100774]],
      [tg 374931, tg 381431, tg 468531, tg 475031]⟩,
    ⟨-7, 1, 2, 24,
      [[tg 427, tg 6927, tg 94027, tg 100527], [tg 583, tg 7083, tg 94183, tg 100683], [tg 5861, tg 12361, tg 99461, tg 105961], [tg 687, tg 7187, tg 94287, tg 100787]],
      [tg 187783, tg 194283, tg 281383, tg 287883]⟩,
    ⟨-7, 1, 3, 18,
      [[tg 440, tg 6940, tg 94040, tg 100540], [tg 544, tg 7044, tg 94144, tg 100644], [tg 596, tg 7096, tg 94196, tg 100696], [tg 700, tg 7200, tg 94300, tg 100800]],
      [tg 374944, tg 381444, tg 468544, tg 475044]⟩,
    ⟨-7, 1, 4, 23,
      [[tg 453, tg 6953, tg 94053, tg 100553], [tg 557, tg 7057, tg 94157, tg 100657], [tg 609, tg 7109, tg 94209, tg 100709], [tg 713, tg 7213, tg 94313, tg 100813]],
      [tg 375009, tg 381509, tg 468609, tg 475109]⟩,
    ⟨-7, 1, 5, 19,
      [[tg 466, tg 6966, tg 94066, tg 100566], [tg 492, tg 6992, tg 94092, tg 100592], [tg 570, tg 7070, tg 94170, tg 100670], [tg 622, tg 7122, tg 94222, tg 100722], [tg 726, tg 7226, tg 94326, tg 100826]],
      [tg 374970, tg 381470, tg 468570, tg 475070]⟩,
    ⟨-7, 1, 6, 22,
      [[tg 479, tg 6979, tg 94079, tg 100579], [tg 505, tg 7005, tg 94105, tg 100605], [tg 583, tg 7083, tg 94183, tg 100683], [tg 635, tg 7135, tg 94235, tg 100735], [tg 739, tg 7239, tg 94339, tg 100839]],
      [tg 187835, tg 194335, tg 281435, tg 287935]⟩,
    ⟨-7, 1, 7, 19,
      [[tg 492, tg 6992, tg 94092, tg 100592], [tg 596, tg 7096, tg 94196, tg 100696], [tg 648, tg 7148, tg 94248, tg 100748], [tg 726, tg 7226, tg 94326, tg 100826], [tg 752, tg 7252, tg 94352, tg 100852]],
      [tg 187926, tg 194426, tg 281526, tg 288026]⟩,
    ⟨-7, 1, 8, 21,
      [[tg 505, tg 7005, tg 94105, tg 100605], [tg 609, tg 7109, tg 94209, tg 100709], [tg 648, tg 7148, tg 94248, tg 100748], [tg 739, tg 7239, tg 94339, tg 100839], [tg 765, tg 7265, tg 94365, tg 100865]],
      [tg 375048, tg 381548, tg 468648, tg 475148]⟩,
    ⟨-7, 1, 9, 20,
      [[tg 518, tg 7018, tg 94118, tg 100618], [tg 622, tg 7122, tg 94222, tg 100722], [tg 635, tg 7135, tg 94235, tg 100735], [tg 778, tg 7278, tg 94378, tg 100878]],
      [tg 375022, tg 381522, tg 468622, tg 475122]⟩,
    ⟨-6, 1, 0, 15,
      [[tg 531, tg 7031, tg 94131, tg 100631], [tg 682, tg 1857, tg 8482, tg 95457], [tg 674, tg 7174, tg 94274, tg 100774], [tg 791, tg 7291, tg 94391, tg 100891]],
      [tg 375082, tg 376257, tg 382882, tg 469857]⟩,
    ⟨-6, 1, 1, 16,
      [[tg 544, tg 7044, tg 94144, tg 100644], [tg 661, tg 7161, tg 94261, tg 100761], [tg 700, tg 7200, tg 94300, tg 100800], [tg 804, tg 7304, tg 94404, tg 100904]],
      [tg 375061, tg 381561, tg 468661, tg 475161]⟩,
    ⟨-6, 1, 2, 23,
      [[tg 557, tg 7057, tg 94157, tg 100657], [tg 713, tg 7213, tg 94313, tg 100813], [tg 5991, tg 12491, tg 99591, tg 106091], [tg 817, tg 7317, tg 94417, tg 100917]],
      [tg 187913, tg 194413, tg 281513, tg 288013]⟩,
    ⟨-6, 1, 3, 17,
      [[tg 570, tg 7070, tg 94170, tg 100670], [tg 674, tg 7174, tg 94274, tg 100774], [tg 726, tg 7226, tg 94326, tg 100826], [tg 830, tg 7330, tg 94430, tg 100930]],
      [tg 375074, tg 381574, tg 468674, tg 475174]⟩,
    ⟨-6, 1, 4, 22,
      [[tg 583, tg 7083, tg 94183, tg 100683], [tg 687, tg 7187, tg 94287, tg 100787], [tg 739, tg 7239, tg 94339, tg 100839], [tg 843, tg 7343, tg 94443, tg 100943]],
      [tg 375139, tg 381639, tg 468739, tg 475239]⟩,
    ⟨-6, 1, 5, 18,
      [[tg 596, tg 7096, tg 94196, tg 100696], [tg 622, tg 7122, tg 94222, tg 100722], [tg 700, tg 7200, tg 94300, tg 100800], [tg 752, tg 7252, tg 94352, tg 100852], [tg 856, tg 7356, tg 94456, tg 100956]],
      [tg 375100, tg 381600, tg 468700, tg 475200]⟩,
    ⟨-6, 1, 6, 21,
      [[tg 609, tg 7109, tg 94209, tg 100709], [tg 635, tg 7135, tg 94235, tg 100735], [tg 713, tg 7213, tg 94313, tg 100813], [tg 765, tg 7265, tg 94365, tg 100865], [tg 869, tg 7369, tg 94469, tg 100969]],
      [tg 187965, tg 194465, tg 281565, tg 288065]⟩,
    ⟨-6, 1, 7, 18,
      [[tg 622, tg 7122, tg 94222, tg 100722], [tg 726, tg 7226, tg 94326, tg 100826], [tg 778, tg 7278, tg 94378, tg 100878], [tg 856, tg 7356, tg 94456, tg 100956], [tg 882, tg 7382, tg 94482, tg 100982]],
      [tg 188056, tg 194556, tg 281656, tg 288156]⟩,
    ⟨-6, 1, 8, 20,
      [[tg 635, tg 7135, tg 94235, tg 100735], [tg 739, tg 7239, tg 94339, tg 100839], [tg 778, tg 7278, tg 94378, tg 100878], [tg 869, tg 7369, tg 94469, tg 100969], [tg 895, tg 7395, tg 94495, tg 100995]],
      [tg 375178, tg 381678, tg 468778, tg 475278]⟩,
    ⟨-6, 1, 9, 19,
      [[tg 648, tg 7148, tg 94248, tg 100748], [tg 752, tg 7252, tg 94352, tg 100852], [tg 765, tg 7265, tg 94365, tg 100865], [tg 908, tg 7408, tg 94508, tg 101008]],
      [tg 375152, tg 381652, tg 468752, tg 475252]⟩,
    ⟨-5, 1, 0, 14,
      [[tg 661, tg 7161, tg 94261, tg 100761], [tg 552, tg 1987, tg 8352, tg 95587], [tg 804, tg 7304, tg 94404, tg 100904], [tg 921, tg 7421, tg 94521, tg 101021]],
      [tg 374952, tg 376387, tg 382752, tg 469987]⟩,
    ⟨-5, 1, 1, 15,
      [[tg 674, tg 7174, tg 94274, tg 100774], [tg 791, tg 7291, tg 94391, tg 100891], [tg 830, tg 7330, tg 94430, tg 100930], [tg 934, tg 7434, tg 94534, tg 101034]],
      [tg 375191, tg 381691, tg 468791, tg 475291]⟩,
    ⟨-5, 1, 2, 22,
      [[tg 687, tg 7187, tg 94287, tg 100787], [tg 843, tg 7343, tg 94443, tg 100943], [tg 6121, tg 12621, tg 99721, tg 106221], [tg 947, tg 7447, tg 94547, tg 101047]],
      [tg 188043, tg 194543, tg 281643, tg 288143]⟩,
    ⟨-5, 1, 3, 16,
      [[tg 700, tg 7200, tg 94300, tg 100800], [tg 804, tg 7304, tg 94404, tg 100904], [tg 856, tg 7356, tg 94456, tg 100956], [tg 960, tg 7460, tg 94560, tg 101060]],
      [tg 375204, tg 381704, tg 468804, tg 475304]⟩,
    ⟨-5, 1, 4, 21,
      [[tg 713, tg 7213, tg 94313, tg 100813], [tg 817, tg 7317, tg 94417, tg 100917], [tg 869, tg 7369, tg 94469, tg 100969], [tg 973, tg 7473, tg 94573, tg 101073]],
      [tg 375269, tg 381769, tg 468869, tg 475369]⟩,
    ⟨-5, 1, 5, 17,
      [[tg 726, tg 7226, tg 94326, tg 100826], [tg 752, tg 7252, tg 94352, tg 100852], [tg 830, tg 7330, tg 94430, tg 100930], [tg 882, tg 7382, tg 94482, tg 100982], [tg 986, tg 7486, tg 94586, tg 101086]],
      [tg 375230, tg 381730, tg 468830, tg 475330]⟩,
    ⟨-5, 1, 6, 20,
      [[tg 739, tg 7239, tg 94339, tg 100839], [tg 765, tg 7265, tg 94365, tg 100865], [tg 843, tg 7343, tg 94443, tg 100943], [tg 895, tg 7395, tg 94495, tg 100995], [tg 999, tg 7499, tg 94599, tg 101099]],
      [tg 188095, tg 194595, tg 281695, tg 288195]⟩,
    ⟨-5, 1, 7, 17,
      [[tg 752, tg 7252, tg 94352, tg 100852], [tg 856, tg 7356, tg 94456, tg 100956], [tg 908, tg 7408, tg 94508, tg 101008], [tg 986, tg 7486, tg 94586, tg 101086], [tg 1012, tg 7512, tg 94612, tg 101112]],
      [tg 188186, tg 194686, tg 281786, tg 288286]⟩,
    ⟨-5, 1, 8, 19,
      [[tg 765, tg 7265, tg 94365, tg 100865], [tg 869, tg 7369, tg 94469, tg 100969], [tg 908, tg 7408, tg 94508, tg 101008], [tg 999, tg 7499, tg 94599, tg 101099], [tg 1025, tg 7525, tg 94625, tg 101125]],
      [tg 375308, tg 381808, tg 468908, tg 475408]⟩,
    ⟨-5, 1, 9, 18,
      [[tg 778, tg 7278, tg 94378, tg 100878], [tg 882, tg 7382, tg 94482, tg 100982], [tg 895, tg 7395, tg 94495, tg 100995], [tg 1038, tg 7538, tg 94638, tg 101138]],
      [tg 375282, tg 381782, tg 468882, tg 475382]⟩,
    ⟨-4, 1, 0, 13,
      [[tg 791, tg 7291, tg 94391, tg 100891], [tg 422, tg 2117, tg 8222, tg 95717], [tg 934, tg 7434, tg 94534, tg 101034], [tg 1051, tg 7551, tg 94651, tg 101151]],
      [tg 374822, tg 376517, tg 382622, tg 470117]⟩,
    ⟨-4, 1, 1, 14,
      [[tg 804, tg 7304, tg 94404, tg 100904], [tg 921, tg 7421, tg 94521, tg 101021], [tg 960, tg 7460, tg 94560, tg 101060], [tg 1064, tg 7564, tg 94664, tg 101164]],
      [tg 375321, tg 381821, tg 468921, tg 475421]⟩,
    ⟨-4, 1, 2, 21,
      [[tg 817, tg 7317, tg 94417, tg 100917], [tg 973, tg 7473, tg 94573, tg 101073], [tg 6251, tg 12751, tg 99851, tg 106351], [tg 1077, tg 7577, tg 94677, tg 101177]],
      [tg 188173, tg 194673, tg 281773, tg 288273]⟩,
    ⟨-4, 1, 3, 15,
      [[tg 830, tg 7330, tg 94430, tg 100930], [tg 934, tg 7434, tg 94534, tg 101034], [tg 986, tg 7486, tg 94586, tg 101086], [tg 1090, tg 7590, tg 94690, tg 101190]],
      [tg 375334, tg 381834, tg 468934, tg 475434]⟩,
    ⟨-4, 1, 4, 20,
      [[tg 843, tg 7343, tg 94443, tg 100943], [tg 947, tg 7447, tg 94547, tg 101047], [tg 999, tg 7499, tg 94599, tg 101099], [tg 1103, tg 7603, tg 94703, tg 101203]],
      [tg 375399, tg 381899, tg 468999, tg 475499]⟩,
    ⟨-4, 1, 5, 16,
      [[tg 856, tg 7356, tg 94456, tg 100956], [tg 882, tg 7382, tg 94482, tg 100982], [tg 960, tg 7460, tg 94560, tg 101060], [tg 1012, tg 7512, tg 94612, tg 101112], [tg 1116, tg 7616, tg 94716, tg 101216]],
      [tg 375360, tg 381860, tg 468960, tg 475460]⟩,
    ⟨-4, 1, 6, 19,
      [[tg 869, tg 7369, tg 94469, tg 100969], [tg 895, tg 7395, tg 94495, tg 100995], [tg 973, tg 7473, tg 94573, tg 101073], [tg 1025, tg 7525, tg 94625, tg 101125], [tg 1129, tg 7629, tg 94729, tg 101229]],
      [tg 188225, tg 194725, tg 281825, tg 288325]⟩,
    ⟨-4, 1, 7, 16,
      [[tg 882, tg 7382, tg 94482, tg 100982], [tg 986, tg 7486, tg 94586, tg 101086], [tg 1038, tg 7538, tg 94638, tg 101138], [tg 1116, tg 7616, tg 94716, tg 101216], [tg 1142, tg 7642, tg 94742, tg 101242]],
      [tg 188316, tg 194816, tg 281916, tg 288416]⟩,
    ⟨-4, 1, 8, 18,
      [[tg 895, tg 7395, tg 94495, tg 100995], [tg 999, tg 7499, tg 94599, tg 101099], [tg 1038, tg 7538, tg 94638, tg 101138], [tg 1129, tg 7629, tg 94729, tg 101229], [tg 1155, tg 7655, tg 94755, tg 101255]],
      [tg 375438, tg 381938, tg 469038, tg 475538]⟩,
    ⟨-4, 1, 9, 17,
      [[tg 908, tg 7408, tg 94508, tg 101008], [tg 1012, tg 7512, tg 94612, tg 101112], [tg 1025, tg 7525, tg 94625, tg 101125], [tg 1168, tg 7668, tg 94768, tg 101268]],
      [tg 375412, tg 381912, tg 469012, tg 475512]⟩,
    ⟨-3, 1, 0, 12,
      [[tg 921, tg 7421, tg 94521, tg 101021], [tg 292, tg 2247, tg 8092, tg 95847], [tg 1064, tg 7564, tg 94664, tg 101164], [tg 1181, tg 7681, tg 94781, tg 101281]],
      [tg 374692, tg 376647, tg 382492, tg 470247]⟩,
    ⟨-3, 1, 1, 13,
      [[tg 934, tg 7434, tg 94534, tg 101034], [tg 1051, tg 7551, tg 94651, tg 101151], [tg 1090, tg 7590, tg 94690, tg 101190], [tg 1194, tg 7694, tg 94794, tg 101294]],
      [tg 375451, tg 381951, tg 469051, tg 475551]⟩,
    ⟨-3, 1, 2, 20,
      [[tg 947, tg 7447, tg 94547, tg 101047], [tg 1103, tg 7603, tg 94703, tg 101203], [tg 6381, tg 12881, tg 99981, tg 106481], [tg 1207, tg 7707, tg 94807, tg 101307]],
      [tg 188303, tg 194803, tg 281903, tg 288403]⟩,
    ⟨-3, 1, 3, 14,
      [[tg 960, tg 7460, tg 94560, tg 101060], [tg 1064, tg 7564, tg 94664, tg 101164], [tg 1116, tg 7616, tg 94716, tg 101216], [tg 1220, tg 7720, tg 94820, tg 101320]],
      [tg 375464, tg 381964, tg 469064, tg 475564]⟩,
    ⟨-3, 1, 4, 19,
      [[tg 973, tg 7473, tg 94573, tg 101073], [tg 1077, tg 7577, tg 94677, tg 101177], [tg 1129, tg 7629, tg 94729, tg 101229], [tg 1233, tg 7733, tg 94833, tg 101333]],
      [tg 375529, tg 382029, tg 469129, tg 475629]⟩,
    ⟨-3, 1, 5, 15,
      [[tg 986, tg 7486, tg 94586, tg 101086], [tg 1012, tg 7512, tg 94612, tg 101112], [tg 1090, tg 7590, tg 94690, tg 101190], [tg 1142, tg 7642, tg 94742, tg 101242], [tg 1246, tg 7746, tg 94846, tg 101346]],
      [tg 375490, tg 381990, tg 469090, tg 475590]⟩,
    ⟨-3, 1, 6, 18,
      [[tg 999, tg 7499, tg 94599, tg 101099], [tg 1025, tg 7525, tg 94625, tg 101125], [tg 1103, tg 7603, tg 94703, tg 101203], [tg 1155, tg 7655, tg 94755, tg 101255], [tg 1259, tg 7759, tg 94859, tg 101359]],
      [tg 188355, tg 194855, tg 281955, tg 288455]⟩,
    ⟨-3, 1, 7, 15,
      [[tg 1012, tg 7512, tg 94612, tg 101112], [tg 1116, tg 7616, tg 94716, tg 101216], [tg 1168, tg 7668, tg 94768, tg 101268], [tg 1246, tg 7746, tg 94846, tg 101346], [tg 1272, tg 7772, tg 94872, tg 101372]],
      [tg 188446, tg 194946, tg 282046, tg 288546]⟩,
    ⟨-3, 1, 8, 17,
      [[tg 1025, tg 7525, tg 94625, tg 101125], [tg 1129, tg 7629, tg 94729, tg 101229], [tg 1168, tg 7668, tg 94768, tg 101268], [tg 1259, tg 7759, tg 94859, tg 101359], [tg 1285, tg 7785, tg 94885, tg 101385]],
      [tg 375568, tg 382068, tg 469168, tg 475668]⟩,
    ⟨-3, 1, 9, 16,
      [[tg 1038, tg 7538, tg 94638, tg 101138], [tg 1142, tg 7642, tg 94742, tg 101242], [tg 1155, tg 7655, tg 94755, tg 101255], [tg 1298, tg 7798, tg 94898, tg 101398]],
      [tg 375542, tg 382042, tg 469142, tg 475642]⟩,
    ⟨-2, 1, 0, 11,
      [[tg 1051, tg 7551, tg 94651, tg 101151], [tg 162, tg 2377, tg 7962, tg 95977], [tg 1194, tg 7694, tg 94794, tg 101294], [tg 5, tg 6505, tg 31211, tg 37711]],
      [tg 374562, tg 376777, tg 382362, tg 470377]⟩,
    ⟨-2, 1, 1, 12,
      [[tg 1064, tg 7564, tg 94664, tg 101164], [tg 1181, tg 7681, tg 94781, tg 101281], [tg 1220, tg 7720, tg 94820, tg 101320], [tg 18, tg 6518, tg 31224, tg 37724]],
      [tg 375581, tg 382081, tg 469181, tg 475681]⟩,
    ⟨-2, 1, 2, 19,
      [[tg 1077, tg 7577, tg 94677, tg 101177], [tg 1233, tg 7733, tg 94833, tg 101333], [tg 5205, tg 11705, tg 36411, tg 42911], [tg 31, tg 6531, tg 31237, tg 37737]],
      [tg 188433, tg 194933, tg 282033, tg 288533]⟩,
    ⟨-2, 1, 3, 13,
      [[tg 1090, tg 7590, tg 94690, tg 101190], [tg 1194, tg 7694, tg 94794, tg 101294], [tg 1246, tg 7746, tg 94846, tg 101346], [tg 44, tg 6544, tg 31250, tg 37750]],
      [tg 375594, tg 382094, tg 469194, tg 475694]⟩,
    ⟨-2, 1, 4, 18,
      [[tg 1103, tg 7603, tg 94703, tg 101203], [tg 1207, tg 7707, tg 94807, tg 101307], [tg 1259, tg 7759, tg 94859, tg 101359], [tg 57, tg 6557, tg 31263, tg 37763]],
      [tg 375659, tg 382159, tg 469259, tg 475759]⟩,
    ⟨-2, 1, 5, 14,
      [[tg 1116, tg 7616, tg 94716, tg 101216], [tg 1142, tg 7642, tg 94742, tg 101242], [tg 1220, tg 7720, tg 94820, tg 101320], [tg 1272, tg 7772, tg 94872, tg 101372], [tg 70, tg 6570, tg 31276, tg 37776]],
      [tg 375620, tg 382120, tg 469220, tg 475720]⟩,
    ⟨-2, 1, 6, 17,
      [[tg 1129, tg 7629, tg 94729, tg 101229], [tg 1155, tg 7655, tg 94755, tg 101255], [tg 1233, tg 7733, tg 94833, tg 101333], [tg 1285, tg 7785, tg 94885, tg 101385], [tg 83, tg 6583, tg 31289, tg 37789]],
      [tg 188485, tg 194985, tg 282085, tg 288585]⟩,
    ⟨-2, 1, 7, 14,
      [[tg 1142, tg 7642, tg 94742, tg 101242], [tg 1246, tg 7746, tg 94846, tg 101346], [tg 1298, tg 7798, tg 94898, tg 101398], [tg 70, tg 6570, tg 31276, tg 37776], [tg 96, tg 6596, tg 31302, tg 37802]],
      [tg 187270, tg 193770, tg 218476, tg 224976]⟩,
    ⟨-2, 1, 8, 16,
      [[tg 1155, tg 7655, tg 94755, tg 101255], [tg 1259, tg 7759, tg 94859, tg 101359], [tg 1298, tg 7798, tg 94898, tg 101398], [tg 83, tg 6583, tg 31289, tg 37789], [tg 109, tg 6609, tg 31315, tg 37815]],
      [tg 375698, tg 382198, tg 469298, tg 475798]⟩,
    ⟨-2, 1, 9, 15,
      [[tg 1168, tg 7668, tg 94768, tg 101268], [tg 1272, tg 7772, tg 94872, tg 101372], [tg 1285, tg 7785, tg 94885, tg 101385], [tg 122, tg 6622, tg 31328, tg 37828]],
      [tg 375672, tg 382172, tg 469272, tg 475772]⟩]⟩,
  ⟨2, -10, 0, -1, -1, [(-1, 1, 1), (0, -10, 1)], -1, 1, 1, 10, 0, -10, 1, 10,
   [⟨-11, -1, 0, 20,
      [[tg 6382, tg 12882, tg 99982, tg 106482], [tg 62568, tg 69068, tg 156168, tg 162668], [tg 25, tg 6525, tg 93625, tg 100125], [tg 142, tg 6642, tg 93742, tg 100242]],
      [tg 187225, tg 193725, tg 280825, tg 287325]⟩,
    ⟨-11, -1, 1, 19,
      [[tg 6395, tg 12895, tg 99995, tg 106495], [tg 12, tg 6512, tg 93612, tg 100112], [tg 51, tg 6551, tg 93651, tg 100151], [tg 155, tg 6655, tg 93755, tg 100255]],
      [tg 187251, tg 193751, tg 280851, tg 287351]⟩,
    ⟨-11, -1, 2, 12,
      [[tg 6408, tg 12908, tg 100008, tg 106508], [tg 64, tg 6564, tg 93664, tg 100164], [tg 5206, tg 11706, tg 37582, tg 44082], [tg 168, tg 6668, tg 93768, tg 100268]],
      [tg 192406, tg 198906, tg 224782, tg 231282]⟩,
    ⟨-11, -1, 3, 18,
      [[tg 6421, tg 12921, tg 100021, tg 106521], [tg 25, tg 6525, tg 93625, tg 100125], [tg 77, tg 6577, tg 93677, tg 100177], [tg 181, tg 6681, tg 93781, tg 100281]],
      [tg 374477, tg 380977, tg 468077, tg 474577]⟩,
    ⟨-11, -1, 4, 13,
      [[tg 6434, tg 12934, tg 100034, tg 106534], [tg 38, tg 6538, tg 93638, tg 100138], [tg 90, tg 6590, tg 93690, tg 100190], [tg 194, tg 6694, tg 93794, tg 100294]],
      [tg 187238, tg 193738, tg 280838, tg 287338]⟩,
    ⟨-11, -1, 5, 17,
      [[tg 6447, tg 12947, tg 100047, tg 106547], [tg 6473, tg 12973, tg 100073, tg 106573], [tg 51, tg 6551, tg 93651, tg 100151], [tg 103, tg 6603, tg 93703, tg 100203], [tg 207, tg 6707, tg 93807, tg 100307]],
      [tg 187303, tg 193803, tg 280903, tg 287403]⟩,
    ⟨-11, -1, 6, 14,
      [[tg 6460, tg 12960, tg 100060, tg 106560], [tg 6486, tg 12986, tg 100086, tg 106586], [tg 64, tg 6564, tg 93664, tg 100164], [tg 116, tg 6616, tg 93716, tg 100216], [tg 220, tg 6720, tg 93820, tg 100320]],
      [tg 374464, tg 380964, tg 468064, tg 474564]⟩,
    ⟨-11, -1, 7, 16,
      [[tg 6473, tg 12973, tg 100073, tg 106573], [tg 77, tg 6577, tg 93677, tg 100177], [tg 129, tg 6629, tg 93729, tg 100229], [tg 207, tg 6707, tg 93807, tg 100307], [tg 233, tg 6733, tg 93833, tg 100333]],
      [tg 187329, tg 193829, tg 280929, tg 287429]⟩,
    ⟨-11, -1, 8, 14,
      [[tg 6486, tg 12986, tg 100086, tg 106586], [tg 90, tg 6590, tg 93690, tg 100190], [tg 129, tg 6629, tg 93729, tg 100229], [tg 220, tg 6720, tg 93820, tg 100320], [tg 246, tg 6746, tg 93846, tg 100346]],
      [tg 187420, tg 193920, tg 281020, tg 287520]⟩,
    ⟨-11, -1, 9, 15,
      [[tg 6499, tg 12999, tg 100099, tg 106599], [tg 103, tg 6603, tg 93703, tg 100203], [tg 116, tg 6616, tg 93716, tg 100216], [tg 259, tg 6759, tg 93859, tg 100359]],
      [tg 374516, tg 381016, tg 468116, tg 474616]⟩,
    ⟨-10, -1, 0, 19,
      [[tg 12, tg 6512, tg 93612, tg 100112], [tg 62698, tg 69198, tg 156298, tg 162798], [tg 155, tg 6655, tg 93755, tg 100255], [tg 272, tg 6772, tg 93872, tg 100372]],
      [tg 187355, tg 193855, tg 280955, tg 287455]⟩,
    ⟨-10, -1, 1, 18,
      [[tg 25, tg 6525, tg 93625, tg 100125], [tg 142, tg 6642, tg 93742, tg 100242], [tg 181, tg 6681, tg 93781, tg 100281], [tg 285, tg 6785, tg 93885, tg 100385]],
      [tg 187381, tg 193881, tg 280981, tg 287481]⟩,
    ⟨-10, -1, 2, 11,
      [[tg 38, tg 6538, tg 93638, tg 100138], [tg 194, tg 6694, tg 93794, tg 100294], [tg 1176, tg 7676, tg 31212, tg 37712], [tg 298, tg 6798, tg 93898, tg 100398]],
      [tg 188376, tg 194876, tg 218412, tg 224912]⟩,
    ⟨-10, -1, 3, 17,
      [[tg 51, tg 6551, tg 93651, tg 100151], [tg 155, tg 6655, tg 93755, tg 100255], [tg 207, tg 6707, tg 93807, tg 100307], [tg 311, tg 6811, tg 93911, tg 100411]],
      [tg 374607, tg 381107, tg 468207, tg 474707]⟩,
    ⟨-10, -1, 4, 12,
      [[tg 64, tg 6564, tg 93664, tg 100164], [tg 168, tg 6668, tg 93768, tg 100268], [tg 220, tg 6720, tg 93820, tg 100320], [tg 324, tg 6824, tg 93924, tg 100424]],
      [tg 187368, tg 193868, tg 280968, tg 287468]⟩,
    ⟨-10, -1, 5, 16,
      [[tg 77, tg 6577, tg 93677, tg 100177], [tg 103, tg 6603, tg 93703, tg 100203], [tg 181, tg 6681, tg 93781, tg 100281], [tg 233, tg 6733, tg 93833, tg 100333], [tg 337, tg 6837, tg 93937, tg 100437]],
      [tg 187433, tg 193933, tg 281033, tg 287533]⟩,
    ⟨-10, -1, 6, 13,
      [[tg 90, tg 6590, tg 93690, tg 100190], [tg 116, tg 6616, tg 93716, tg 100216], [tg 194, tg 6694, tg 93794, tg 100294], [tg 246, tg 6746, tg 93846, tg 100346], [tg 350, tg 6850, tg 93950, tg 100450]],
      [tg 374594, tg 381094, tg 468194, tg 474694]⟩,
    ⟨-10, -1, 7, 15,
      [[tg 103, tg 6603, tg 93703, tg 100203], [tg 207, tg 6707, tg 93807, tg 100307], [tg 259, tg 6759, tg 93859, tg 100359], [tg 337, tg 6837, tg 93937, tg 100437], [tg 363, tg 6863, tg 93963, tg 100463]],
      [tg 187459, tg 193959, tg 281059, tg 287559]⟩,
    ⟨-10, -1, 8, 13,
      [[tg 116, tg 6616, tg 93716, tg 100216], [tg 220, tg 6720, tg 93820, tg 100320], [tg 259, tg 6759, tg 93859, tg 100359], [tg 350, tg 6850, tg 93950, tg 100450], [tg 376, tg 6876, tg 93976, tg 100476]],
      [tg 187550, tg 194050, tg 281150, tg 287650]⟩,
    ⟨-10, -1, 9, 14,
      [[tg 129, tg 6629, tg 93729, tg 100229], [tg 233, tg 6733, tg 93833, tg 100333], [tg 246, tg 6746, tg 93846, tg 100346], [tg 389, tg 6889, tg 93989, tg 100489]],
      [tg 374646, tg 381146, tg 468246, tg 474746]⟩,
    ⟨-9, -1, 0, 18,
      [[tg 142, tg 6642, tg 93742, tg 100242], [tg 62828, tg 69328, tg 156428, tg 162928], [tg 285, tg 6785, tg 93885, tg 100385], [tg 402, tg 6902, tg 94002, tg 100502]],
      [tg 187485, tg 193985, tg 281085, tg 287585]⟩,
    ⟨-9, -1, 1, 17,
      [[tg 155, tg 6655, tg 93755, tg 100255], [tg 272, tg 6772, tg 93872, tg 100372], [tg 311, tg 6811, tg 93911, tg 100411], [tg 415, tg 6915, tg 94015, tg 100515]],
      [tg 187511, tg 194011, tg 281111, tg 287611]⟩,
    ⟨-9, -1, 2, 10,
      [[tg 168, tg 6668, tg 93768, tg 100268], [tg 324, tg 6824, tg 93924, tg 100424], [tg 1046, tg 7546, tg 31342, tg 37842], [tg 428, tg 6928, tg 94028, tg 100528]],
      [tg 188246, tg 194746, tg 218542, tg 225042]⟩,
    ⟨-9, -1, 3, 16,
      [[tg 181, tg 6681, tg 93781, tg 100281], [tg 285, tg 6785, tg 93885, tg 100385], [tg 337, tg 6837, tg 93937, tg 100437], [tg 441, tg 6941, tg 94041, tg 100541]],
      [tg 374737, tg 381237, tg 468337, tg 474837]⟩,
    ⟨-9, -1, 4, 11,
      [[tg 194, tg 6694, tg 93794, tg 100294], [tg 298, tg 6798, tg 93898, tg 100398], [tg 350, tg 6850, tg 93950, tg 100450], [tg 454, tg 6954, tg 94054, tg 100554]],
      [tg 187498, tg 193998, tg 281098, tg 287598]⟩,
    ⟨-9, -1, 5, 15,
      [[tg 207, tg 6707, tg 93807, tg 100307], [tg 233, tg 6733, tg 93833, tg 100333], [tg 311, tg 6811, tg 93911, tg 100411], [tg 363, tg 6863, tg 93963, tg 100463], [tg 467, tg 6967, tg 94067, tg 100567]],
      [tg 187563, tg 194063, tg 281163, tg 287663]⟩,
    ⟨-9, -1, 6, 12,
      [[tg 220, tg 6720, tg 93820, tg 100320], [tg 246, tg 6746, tg 93846, tg 100346], [tg 324, tg 6824, tg 93924, tg 100424], [tg 376, tg 6876, tg 93976, tg 100476], [tg 480, tg 6980, tg 94080, tg 100580]],
      [tg 374724, tg 381224, tg 468324, tg 474824]⟩,
    ⟨-9, -1, 7, 14,
      [[tg 233, tg 6733, tg 93833, tg 100333], [tg 337, tg 6837, tg 93937, tg 100437], [tg 389, tg 6889, tg 93989, tg 100489], [tg 467, tg 6967, tg 94067, tg 100567], [tg 493, tg 6993, tg 94093, tg 100593]],
      [tg 187589, tg 194089, tg 281189, tg 287689]⟩,
    ⟨-9, -1, 8, 12,
      [[tg 246, tg 6746, tg 93846, tg 100346], [tg 350, tg 6850, tg 93950, tg 100450], [tg 389, tg 6889, tg 93989, tg 100489], [tg 480, tg 6980, tg 94080, tg 100580], [tg 506, tg 7006, tg 94106, tg 100606]],
      [tg 187680, tg 194180, tg 281280, tg 287780]⟩,
    ⟨-9, -1, 9, 13,
      [[tg 259, tg 6759, tg 93859, tg 100359], [tg 363, tg 6863, tg 93963, tg 100463], [tg 376, tg 6876, tg 93976, tg 100476], [tg 519, tg 7019, tg 94119, tg 100619]],
      [tg 374776, tg 381276, tg 468376, tg 474876]⟩,
    ⟨-8, -1, 0, 17,
      [[tg 272, tg 6772, tg 93872, tg 100372], [tg 62958, tg 69458, tg 156558, tg 163058], [tg 415, tg 6915, tg 94015, tg 100515], [tg 532, tg 7032, tg 94132, tg 100632]],
      [tg 187615, tg 194115, tg 281215, tg 287715]⟩,
    ⟨-8, -1, 1, 16,
      [[tg 285, tg 6785, tg 93885, tg 100385], [tg 402, tg 6902, tg 94002, tg 100502], [tg 441, tg 6941, tg 94041, tg 100541], [tg 545, tg 7045, tg 94145, tg 100645]],
      [tg 187641, tg 194141, tg 281241, tg 287741]⟩,
    ⟨-8, -1, 2, 9,
      [[tg 298, tg 6798, tg 93898, tg 100398], [tg 454, tg 6954, tg 94054, tg 100554], [tg 916, tg 7416, tg 31472, tg 37972], [tg 558, tg 7058, tg 94158, tg 100658]],
      [tg 188116, tg 194616, tg 218672, tg 225172]⟩,
    ⟨-8, -1, 3, 15,
      [[tg 311, tg 6811, tg 93911, tg 100411], [tg 415, tg 6915, tg 94015, tg 100515], [tg 467, tg 6967, tg 94067, tg 100567], [tg 571, tg 7071, tg 94171, tg 100671]],
      [tg 374867, tg 381367, tg 468467, tg 474967]⟩,
    ⟨-8, -1, 4, 10,
      [[tg 324, tg 6824, tg 93924, tg 100424], [tg 428, tg 6928, tg 94028, tg 100528], [tg 480, tg 6980, tg 94080, tg 100580], [tg 584, tg 7084, tg 94184, tg 100684]],
      [tg 187628, tg 194128, tg 281228, tg 287728]⟩,
    ⟨-8, -1, 5, 14,
      [[tg 337, tg 6837, tg 93937, tg 100437], [tg 363, tg 6863, tg 93963, tg 100463], [tg 441, tg 6941, tg 94041, tg 100541], [tg 493, tg 6993, tg 94093, tg 100593], [tg 597, tg 7097, tg 94197, tg 100697]],
      [tg 187693, tg 194193, tg 281293, tg 287793]⟩,
    ⟨-8, -1, 6, 11,
      [[tg 350, tg 6850, tg 93950, tg 100450], [tg 376, tg 6876, tg 93976, tg 100476], [tg 454, tg 6954, tg 94054, tg 100554], [tg 506, tg 7006, tg 94106, tg 100606], [tg 610, tg 7110, tg 94210, tg 100710]],
      [tg 374854, tg 381354, tg 468454, tg 474954]⟩,
    ⟨-8, -1, 7, 13,
      [[tg 363, tg 6863, tg 93963, tg 100463], [tg 467, tg 6967, tg 94067, tg 100567], [tg 519, tg 7019, tg 94119, tg 100619], [tg 597, tg 7097, tg 94197, tg 100697], [tg 623, tg 7123, tg 94223, tg 100723]],
      [tg 187719, tg 194219, tg 281319, tg 287819]⟩,
    ⟨-8, -1, 8, 11,
      [[tg 376, tg 6876, tg 93976, tg 100476], [tg 480, tg 6980, tg 94080, tg 100580], [tg 519, tg 7019, tg 94119, tg 100619], [tg 610, tg 7110, tg 94210, tg 100710], [tg 636, tg 7136, tg 94236, tg 100736]],
      [tg 187810, tg 194310, tg 281410, tg 287910]⟩,
    ⟨-8, -1, 9, 12,
      [[tg 389, tg 6889, tg 93989, tg 100489], [tg 493, tg 6993, tg 94093, tg 100593], [tg 506, tg 7006, tg 94106, tg 100606], [tg 649, tg 7149, tg 94249, tg 100749]],
      [tg 374906, tg 381406, tg 468506, tg 475006]⟩,
    ⟨-7, -1, 0, 16,
      [[tg 402, tg 6902, tg 94002, tg 100502], [tg 63088, tg 69588, tg 156688, tg 163188], [tg 545, tg 7045, tg 94145, tg 100645], [tg 662, tg 7162, tg 94262, tg 100762]],
      [tg 187745, tg 194245, tg 281345, tg 287845]⟩,
    ⟨-7, -1, 1, 15,
      [[tg 415, tg 6915, tg 94015, tg 100515], [tg 532, tg 7032, tg 94132, tg 100632], [tg 571, tg 7071, tg 94171, tg 100671], [tg 675, tg 7175, tg 94275, tg 100775]],
      [tg 187771, tg 194271, tg 281371, tg 287871]⟩,
    ⟨-7, -1, 2, 8,
      [[tg 428, tg 6928, tg 94028, tg 100528], [tg 584, tg 7084, tg 94184, tg 100684], [tg 786, tg 7286, tg 31602, tg 38102], [tg 688, tg 7188, tg 94288, tg 100788]],
      [tg 187986, tg 194486, tg 218802, tg 225302]⟩,
    ⟨-7, -1, 3, 14,
      [[tg 441, tg 6941, tg 94041, tg 100541], [tg 545, tg 7045, tg 94145, tg 100645], [tg 597, tg 7097, tg 94197, tg 100697], [tg 701, tg 7201, tg 94301, tg 100801]],
      [tg 374997, tg 381497, tg 468597, tg 475097]⟩,
    ⟨-7, -1, 4, 9,
      [[tg 454, tg 6954, tg 94054, tg 100554], [tg 558, tg 7058, tg 94158, tg 100658], [tg 610, tg 7110, tg 94210, tg 100710], [tg 714, tg 7214, tg 94314, tg 100814]],
      [tg 187758, tg 194258, tg 281358, tg 287858]⟩,
    ⟨-7, -1, 5, 13,
      [[tg 467, tg 6967, tg 94067, tg 100567], [tg 493, tg 6993, tg 94093, tg 100593], [tg 571, tg 7071, tg 94171, tg 100671], [tg 623, tg 7123, tg 94223, tg 100723], [tg 727, tg 7227, tg 94327, tg 100827]],
      [tg 187823, tg 194323, tg 281423, tg 287923]⟩,
    ⟨-7, -1, 6, 10,
      [[tg 480, tg 6980, tg 94080, tg 100580], [tg 506, tg 7006, tg 94106, tg 100606], [tg 584, tg 7084, tg 94184, tg 100684], [tg 636, tg 7136, tg 94236, tg 100736], [tg 740, tg 7240, tg 94340, tg 100840]],
      [tg 374984, tg 381484, tg 468584, tg 475084]⟩,
    ⟨-7, -1, 7, 12,
      [[tg 493, tg 6993, tg 94093, tg 100593], [tg 597, tg 7097, tg 94197, tg 100697], [tg 649, tg 7149, tg 94249, tg 100749], [tg 727, tg 7227, tg 94327, tg 100827], [tg 753, tg 7253, tg 94353, tg 100853]],
      [tg 187849, tg 194349, tg 281449, tg 287949]⟩,
    ⟨-7, -1, 8, 10,
      [[tg 506, tg 7006, tg 94106, tg 100606], [tg 610, tg 7110, tg 94210, tg 100710], [tg 649, tg 7149, tg 94249, tg 100749], [tg 740, tg 7240, tg 94340, tg 100840], [tg 766, tg 7266, tg 94366, tg 100866]],
      [tg 187940, tg 194440, tg 281540, tg 288040]⟩,
    ⟨-7, -1, 9, 11,
      [[tg 519, tg 7019, tg 94119, tg 100619], [tg 623, tg 7123, tg 94223, tg 100723], [tg 636, tg 7136, tg 94236, tg 100736], [tg 779, tg 7279, tg 94379, tg 100879]],
      [tg 375036, tg 381536, tg 468636, tg 475136]⟩,
    ⟨-6, -1, 0, 15,
      [[tg 532, tg 7032, tg 94132, tg 100632], [tg 63218, tg 69718, tg 156818, tg 163318], [tg 675, tg 7175, tg 94275, tg 100775], [tg 792, tg 7292, tg 94392, tg 100892]],
      [tg 187875, tg 194375, tg 281475, tg 287975]⟩,
    ⟨-6, -1, 1, 14,
      [[tg 545, tg 7045, tg 94145, tg 100645], [tg 662, tg 7162, tg 94262, tg 100762], [tg 701, tg 7201, tg 94301, tg 100801], [tg 805, tg 7305, tg 94405, tg 100905]],
      [tg 187901, tg 194401, tg 281501, tg 288001]⟩,
    ⟨-6, -1, 2, 7,
      [[tg 558, tg 7058, tg 94158, tg 100658], [tg 714, tg 7214, tg 94314, tg 100814], [tg 656, tg 7156, tg 31732, tg 38232], [tg 818, tg 7318, tg 94418, tg 100918]],
      [tg 187856, tg 194356, tg 218932, tg 225432]⟩,
    ⟨-6, -1, 3, 13,
      [[tg 571, tg 7071, tg 94171, tg 100671], [tg 675, tg 7175, tg 94275, tg 100775], [tg 727, tg 7227, tg 94327, tg 100827], [tg 831, tg 7331, tg 94431, tg 100931]],
      [tg 375127, tg 381627, tg 468727, tg 475227]⟩,
    ⟨-6, -1, 4, 8,
      [[tg 584, tg 7084, tg 94184, tg 100684], [tg 688, tg 7188, tg 94288, tg 100788], [tg 740, tg 7240, tg 94340, tg 100840], [tg 844, tg 7344, tg 94444, tg 100944]],
      [tg 187888, tg 194388, tg 281488, tg 287988]⟩,
    ⟨-6, -1, 5, 12,
      [[tg 597, tg 7097, tg 94197, tg 100697], [tg 623, tg 7123, tg 94223, tg 100723], [tg 701, tg 7201, tg 94301, tg 100801], [tg 753, tg 7253, tg 94353, tg 100853], [tg 857, tg 7357, tg 94457, tg 100957]],
      [tg 187953, tg 194453, tg 281553, tg 288053]⟩,
    ⟨-6, -1, 6, 9,
      [[tg 610, tg 7110, tg 94210, tg 100710], [tg 636, tg 7136, tg 94236, tg 100736], [tg 714, tg 7214, tg 94314, tg 100814], [tg 766, tg 7266, tg 94366, tg 100866], [tg 870, tg 7370, tg 94470, tg 100970]],
      [tg 375114, tg 381614, tg 468714, tg 475214]⟩,
    ⟨-6, -1, 7, 11,
      [[tg 623, tg 7123, tg 94223, tg 100723], [tg 727, tg 7227, tg 94327, tg 100827], [tg 779, tg 7279, tg 94379, tg 100879], [tg 857, tg 7357, tg 94457, tg 100957], [tg 883, tg 7383, tg 94483, tg 100983]],
      [tg 187979, tg 194479, tg 281579, tg 288079]⟩,
    ⟨-6, -1, 8, 9,
      [[tg 636, tg 7136, tg 94236, tg 100736], [tg 740, tg 7240, tg 94340, tg 100840], [tg 779, tg 7279, tg 94379, tg 100879], [tg 870, tg 7370, tg 94470, tg 100970], [tg 896, tg 7396, tg 94496, tg 100996]],
      [tg 188070, tg 194570, tg 281670, tg 288170]⟩,
    ⟨-6, -1, 9, 10,
      [[tg 649, tg 7149, tg 94249, tg 100749], [tg 753, tg 7253, tg 94353, tg 100853], [tg 766, tg 7266, tg 94366, tg 100866], [tg 909, tg 7409, tg 94509, tg 101009]],
      [tg 375166, tg 381666, tg 468766, tg 475266]⟩,
    ⟨-5, -1, 0, 14,
      [[tg 662, tg 7162, tg 94262, tg 100762], [tg 63348, tg 69848, tg 156948, tg 163448], [tg 805, tg 7305, tg 94405, tg 100905], [tg 922, tg 7422, tg 94522, tg 101022]],
      [tg 188005, tg 194505, tg 281605, tg 288105]⟩,
    ⟨-5, -1, 1, 13,
      [[tg 675, tg 7175, tg 94275, tg 100775], [tg 792, tg 7292, tg 94392, tg 100892], [tg 831, tg 7331, tg 94431, tg 100931], [tg 935, tg 7435, tg 94535, tg 101035]],
      [tg 188031, tg 194531, tg 281631, tg 288131]⟩,
    ⟨-5, -1, 2, 6,
      [[tg 688, tg 7188, tg 94288, tg 100788], [tg 844, tg 7344, tg 94444, tg 100944], [tg 526, tg 7026, tg 31862, tg 38362], [tg 948, tg 7448, tg 94548, tg 101048]],
      [tg 187726, tg 194226, tg 219062, tg 225562]⟩,
    ⟨-5, -1, 3, 12,
      [[tg 701, tg 7201, tg 94301, tg 100801], [tg 805, tg 7305, tg 94405, tg 100905], [tg 857, tg 7357, tg 94457, tg 100957], [tg 961, tg 7461, tg 94561, tg 101061]],
      [tg 375257, tg 381757, tg 468857, tg 475357]⟩,
    ⟨-5, -1, 4, 7,
      [[tg 714, tg 7214, tg 94314, tg 100814], [tg 818, tg 7318, tg 94418, tg 100918], [tg 870, tg 7370, tg 94470, tg 100970], [tg 974, tg 7474, tg 94574, tg 101074]],
      [tg 188018, tg 194518, tg 281618, tg 288118]⟩,
    ⟨-5, -1, 5, 11,
      [[tg 727, tg 7227, tg 94327, tg 100827], [tg 753, tg 7253, tg 94353, tg 100853], [tg 831, tg 7331, tg 94431, tg 100931], [tg 883, tg 7383, tg 94483, tg 100983], [tg 987, tg 7487, tg 94587, tg 101087]],
      [tg 188083, tg 194583, tg 281683, tg 288183]⟩,
    ⟨-5, -1, 6, 8,
      [[tg 740, tg 7240, tg 94340, tg 100840], [tg 766, tg 7266, tg 94366, tg 100866], [tg 844, tg 7344, tg 94444, tg 100944], [tg 896, tg 7396, tg 94496, tg 100996], [tg 1000, tg 7500, tg 94600, tg 101100]],
      [tg 375244, tg 381744, tg 468844, tg 475344]⟩,
    ⟨-5, -1, 7, 10,
      [[tg 753, tg 7253, tg 94353, tg 100853], [tg 857, tg 7357, tg 94457, tg 100957], [tg 909, tg 7409, tg 94509, tg 101009], [tg 987, tg 7487, tg 94587, tg 101087], [tg 1013, tg 7513, tg 94613, tg 101113]],
      [tg 188109, tg 194609, tg 281709, tg 288209]⟩,
    ⟨-5, -1, 8, 8,
      [[tg 766, tg 7266, tg 94366, tg 100866], [tg 870, tg 7370, tg 94470, tg 100970], [tg 909, tg 7409, tg 94509, tg 101009], [tg 1000, tg 7500, tg 94600, tg 101100], [tg 1026, tg 7526, tg 94626, tg 101126]],
      [tg 188200, tg 194700, tg 281800, tg 288300]⟩,
    ⟨-5, -1, 9, 9,
      [[tg 779, tg 7279, tg 94379, tg 100879], [tg 883, tg 7383, tg 94483, tg 100983], [tg 896, tg 7396, tg 94496, tg 100996], [tg 1039, tg 7539, tg 94639, tg 101139]],
      [tg 375296, tg 381796, tg 468896, tg 475396]⟩,
    ⟨-4, -1, 0, 13,
      [[tg 792, tg 7292, tg 94392, tg 100892], [tg 63478, tg 69978, tg 157078, tg 163578], [tg 935, tg 7435, tg 94535, tg 101035], [tg 1052, tg 7552, tg 94652, tg 101152]],
      [tg 188135, tg 194635, tg 281735, tg 288235]⟩,
    ⟨-4, -1, 1, 12,
      [[tg 805, tg 7305, tg 94405, tg 100905], [tg 922, tg 7422, tg 94522, tg 101022], [tg 961, tg 7461, tg 94561, tg 101061], [tg 1065, tg 7565, tg 94665, tg 101165]],
      [tg 188161, tg 194661, tg 281761, tg 288261]⟩,
    ⟨-4, -1, 2, 5,
      [[tg 818, tg 7318, tg 94418, tg 100918], [tg 974, tg 7474, tg 94574, tg 101074], [tg 396, tg 6896, tg 31992, tg 38492], [tg 1078, tg 7578, tg 94678, tg 101178]],
      [tg 187596, tg 194096, tg 219192, tg 225692]⟩,
    ⟨-4, -1, 3, 11,
      [[tg 831, tg 7331, tg 94431, tg 100931], [tg 935, tg 7435, tg 94535, tg 101035], [tg 987, tg 7487, tg 94587, tg 101087], [tg 1091, tg 7591, tg 94691, tg 101191]],
      [tg 375387, tg 381887, tg 468987, tg 475487]⟩,
    ⟨-4, -1, 4, 6,
      [[tg 844, tg 7344, tg 94444, tg 100944], [tg 948, tg 7448, tg 94548, tg 101048], [tg 1000, tg 7500, tg 94600, tg 101100], [tg 1104, tg 7604, tg 94704, tg 101204]],
      [tg 188148, tg 194648, tg 281748, tg 288248]⟩,
    ⟨-4, -1, 5, 10,
      [[tg 857, tg 7357, tg 94457, tg 100957], [tg 883, tg 7383, tg 94483, tg 100983], [tg 961, tg 7461, tg 94561, tg 101061], [tg 1013, tg 7513, tg 94613, tg 101113], [tg 1117, tg 7617, tg 94717, tg 101217]],
      [tg 188213, tg 194713, tg 281813, tg 288313]⟩,
    ⟨-4, -1, 6, 7,
      [[tg 870, tg 7370, tg 94470, tg 100970], [tg 896, tg 7396, tg 94496, tg 100996], [tg 974, tg 7474, tg 94574, tg 101074], [tg 1026, tg 7526, tg 94626, tg 101126], [tg 1130, tg 7630, tg 94730, tg 101230]],
      [tg 375374, tg 381874, tg 468974, tg 475474]⟩,
    ⟨-4, -1, 7, 9,
      [[tg 883, tg 7383, tg 94483, tg 100983], [tg 987, tg 7487, tg 94587, tg 101087], [tg 1039, tg 7539, tg 94639, tg 101139], [tg 1117, tg 7617, tg 94717, tg 101217], [tg 1143, tg 7643, tg 94743, tg 101243]],
      [tg 188239, tg 194739, tg 281839, tg 288339]⟩,
    ⟨-4, -1, 8, 7,
      [[tg 896, tg 7396, tg 94496, tg 100996], [tg 1000, tg 7500, tg 94600, tg 101100], [tg 1039, tg 7539, tg 94639, tg 101139], [tg 1130, tg 7630, tg 94730, tg 101230], [tg 1156, tg 7656, tg 94756, tg 101256]],
      [tg 188330, tg 194830, tg 281930, tg 288430]⟩,
    ⟨-4, -1, 9, 8,
      [[tg 909, tg 7409, tg 94509, tg 101009], [tg 1013, tg 7513, tg 94613, tg 101113], [tg 1026, tg 7526, tg 94626, tg 101126], [tg 1169, tg 7669, tg 94769, tg 101269]],
      [tg 375426, tg 381926, tg 469026, tg 475526]⟩,
    ⟨-3, -1, 0, 12,
      [[tg 922, tg 7422, tg 94522, tg 101022], [tg 63608, tg 70108, tg 157208, tg 163708], [tg 1065, tg 7565, tg 94665, tg 101165], [tg 1182, tg 7682, tg 94782, tg 101282]],
      [tg 188265, tg 194765, tg 281865, tg 288365]⟩,
    ⟨-3, -1, 1, 11,
      [[tg 935, tg 7435, tg 94535, tg 101035], [tg 1052, tg 7552, tg 94652, tg 101152], [tg 1091, tg 7591, tg 94691, tg 101191], [tg 1195, tg 7695, tg 94795, tg 101295]],
      [tg 188291, tg 194791, tg 281891, tg 288391]⟩,
    ⟨-3, -1, 2, 4,
      [[tg 948, tg 7448, tg 94548, tg 101048], [tg 1104, tg 7604, tg 94704, tg 101204], [tg 266, tg 6766, tg 32122, tg 38622], [tg 1208, tg 7708, tg 94808, tg 101308]],
      [tg 187466, tg 193966, tg 219322, tg 225822]⟩,
    ⟨-3, -1, 3, 10,
      [[tg 961, tg 7461, tg 94561, tg 101061], [tg 1065, tg 7565, tg 94665, tg 101165], [tg 1117, tg 7617, tg 94717, tg 101217], [tg 1221, tg 7721, tg 94821, tg 101321]],
      [tg 375517, tg 382017, tg 469117, tg 475617]⟩,
    ⟨-3, -1, 4, 5,
      [[tg 974, tg 7474, tg 94574, tg 101074], [tg 1078, tg 7578, tg 94678, tg 101178], [tg 1130, tg 7630, tg 94730, tg 101230], [tg 1234, tg 7734, tg 94834, tg 101334]],
      [tg 188278, tg 194778, tg 281878, tg 288378]⟩,
    ⟨-3, -1, 5, 9,
      [[tg 987, tg 7487, tg 94587, tg 101087], [tg 1013, tg 7513, tg 94613, tg 101113], [tg 1091, tg 7591, tg 94691, tg 101191], [tg 1143, tg 7643, tg 94743, tg 101243], [tg 1247, tg 7747, tg 94847, tg 101347]],
      [tg 188343, tg 194843, tg 281943, tg 288443]⟩,
    ⟨-3, -1, 6, 6,
      [[tg 1000, tg 7500, tg 94600, tg 101100], [tg 1026, tg 7526, tg 94626, tg 101126], [tg 1104, tg 7604, tg 94704, tg 101204], [tg 1156, tg 7656, tg 94756, tg 101256], [tg 1260, tg 7760, tg 94860, tg 101360]],
      [tg 375504, tg 382004, tg 469104, tg 475604]⟩,
    ⟨-3, -1, 7, 8,
      [[tg 1013, tg 7513, tg 94613, tg 101113], [tg 1117, tg 7617, tg 94717, tg 101217], [tg 1169, tg 7669, tg 94769, tg 101269], [tg 1247, tg 7747, tg 94847, tg 101347], [tg 1273, tg 7773, tg 94873, tg 101373]],
      [tg 188369, tg 194869, tg 281969, tg 288469]⟩,
    ⟨-3, -1, 8, 6,
      [[tg 1026, tg 7526, tg 94626, tg 101126], [tg 1130, tg 7630, tg 94730, tg 101230], [tg 1169, tg 7669, tg 94769, tg 101269], [tg 1260, tg 7760, tg 94860, tg 101360], [tg 1286, tg 7786, tg 94886, tg 101386]],
      [tg 188460, tg 194960, tg 282060, tg 288560]⟩,
    ⟨-3, -1, 9, 7,
      [[tg 1039, tg 7539, tg 94639, tg 101139], [tg 1143, tg 7643, tg 94743, tg 101243], [tg 1156, tg 7656, tg 94756, tg 101256], [tg 1299, tg 7799, tg 94899, tg 101399]],
      [tg 375556, tg 382056, tg 469156, tg 475656]⟩,
    ⟨-2, -1, 0, 11,
      [[tg 1052, tg 7552, tg 94652, tg 101152], [tg 5227, tg 63738, tg 13027, tg 157338], [tg 1195, tg 7695, tg 94795, tg 101295], [tg 1, tg 1312, tg 7801, tg 94912]],
      [tg 188395, tg 194895, tg 281995, tg 288495]⟩,
    ⟨-2, -1, 1, 10,
      [[tg 1065, tg 7565, tg 94665, tg 101165], [tg 1182, tg 7682, tg 94782, tg 101282], [tg 1221, tg 7721, tg 94821, tg 101321], [tg 14, tg 1325, tg 7814, tg 94925]],
      [tg 188421, tg 194921, tg 282021, tg 288521]⟩,
    ⟨-2, -1, 2, 3,
      [[tg 1078, tg 7578, tg 94678, tg 101178], [tg 1234, tg 7734, tg 94834, tg 101334], [tg 136, tg 6636, tg 32252, tg 38752], [tg 27, tg 1338, tg 7827, tg 94938]],
      [tg 187336, tg 193836, tg 219452, tg 225952]⟩,
    ⟨-2, -1, 3, 9,
      [[tg 1091, tg 7591, tg 94691, tg 101191], [tg 1195, tg 7695, tg 94795, tg 101295], [tg 1247, tg 7747, tg 94847, tg 101347], [tg 40, tg 1351, tg 7840, tg 94951]],
      [tg 375647, tg 382147, tg 469247, tg 475747]⟩,
    ⟨-2, -1, 4, 4,
      [[tg 1104, tg 7604, tg 94704, tg 101204], [tg 1208, tg 7708, tg 94808, tg 101308], [tg 1260, tg 7760, tg 94860, tg 101360], [tg 53, tg 1364, tg 7853, tg 94964]],
      [tg 188408, tg 194908, tg 282008, tg 288508]⟩,
    ⟨-2, -1, 5, 8,
      [[tg 1117, tg 7617, tg 94717, tg 101217], [tg 1143, tg 7643, tg 94743, tg 101243], [tg 1221, tg 7721, tg 94821, tg 101321], [tg 1273, tg 7773, tg 94873, tg 101373], [tg 66, tg 1377, tg 7866, tg 94977]],
      [tg 188473, tg 194973, tg 282073, tg 288573]⟩,
    ⟨-2, -1, 6, 5,
      [[tg 1130, tg 7630, tg 94730, tg 101230], [tg 1156, tg 7656, tg 94756, tg 101256], [tg 1234, tg 7734, tg 94834, tg 101334], [tg 1286, tg 7786, tg 94886, tg 101386], [tg 79, tg 1390, tg 7879, tg 94990]],
      [tg 375634, tg 382134, tg 469234, tg 475734]⟩,
    ⟨-2, -1, 7, 7,
      [[tg 1143, tg 7643, tg 94743, tg 101243], [tg 1247, tg 7747, tg 94847, tg 101347], [tg 1299, tg 7799, tg 94899, tg 101399], [tg 66, tg 1377, tg 7866, tg 94977], [tg 92, tg 1403, tg 7892, tg 95003]],
      [tg 188499, tg 194999, tg 282099, tg 288599]⟩,
    ⟨-2, -1, 8, 5,
      [[tg 1156, tg 7656, tg 94756, tg 101256], [tg 1260, tg 7760, tg 94860, tg 101360], [tg 1299, tg 7799, tg 94899, tg 101399], [tg 79, tg 1390, tg 7879, tg 94990], [tg 105, tg 1416, tg 7905, tg 95016]],
      [tg 187279, tg 188590, tg 195079, tg 282190]⟩,
    ⟨-2, -1, 9, 6,
      [[tg 1169, tg 7669, tg 94769, tg 101269], [tg 1273, tg 7773, tg 94873, tg 101373], [tg 1286, tg 7786, tg 94886, tg 101386], [tg 118, tg 1429, tg 7918, tg 95029]],
      [tg 375686, tg 382186, tg 469286, tg 475786]⟩]⟩]

/-- A packed certificate entry: side bit, test index, coefficient. -/
def cc (n : ℕ) : Bool × ℕ × ℕ := (n % 2 == 1, n / 2 % 8, n / 16)

set_option maxRecDepth 100000 in
def certsData : List (List (List (Bool × ℕ × ℕ))) := [
  [[],[cc 16,cc 20,cc 21],[cc 18,cc 20,cc 21],[cc 18,cc 21],[cc 18,cc 22,cc 21],[cc 16,cc 22,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 17],[cc 164,cc 17],[cc 166,cc 19],[cc 16,cc 22,cc 19],[cc 166,cc 17],[cc 164,cc 19]],
  [[cc 16,cc 20,cc 37],[],[cc 18,cc 21],[cc 16,cc 20,cc 33],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 35],[cc 18,cc 19],[cc 20,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 80,cc 84,cc 17],[cc 16,cc 17]],
  [[cc 16,cc 20,cc 35],[cc 16,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 17],[cc 18,cc 19],[cc 82,cc 84,cc 19],[cc 18,cc 17],[cc 16,cc 19],[cc 20,cc 17]],
  [[cc 20,cc 19],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 19],[],[cc 18,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 17],[cc 160,cc 17],[cc 162,cc 19],[cc 18,cc 20,cc 19],[cc 162,cc 17],[cc 160,cc 19]],
  [[cc 16,cc 20,cc 39],[cc 20,cc 21],[cc 16,cc 21],[cc 16,cc 20,cc 35],[],[cc 18,cc 21],[cc 16,cc 20,cc 33],[cc 16,cc 19],[cc 80,cc 84,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 20,cc 19],[cc 18,cc 17]],
  [[cc 16,cc 20,cc 33],[cc 18,cc 21],[cc 20,cc 21],[cc 16,cc 20,cc 37],[cc 16,cc 21],[],[cc 18,cc 20,cc 33],[cc 18,cc 17],[cc 16,cc 19],[cc 20,cc 17],[cc 16,cc 17],[cc 18,cc 19],[cc 82,cc 84,cc 19]],
  [[cc 20,cc 17],[cc 18,cc 20,cc 17],[cc 16,cc 20,cc 17],[cc 20,cc 21],[cc 16,cc 20,cc 21],[cc 16,cc 20,cc 19],[],[cc 18,cc 20,cc 19],[cc 162,cc 17],[cc 160,cc 19],[cc 16,cc 20,cc 17],[cc 160,cc 17],[cc 162,cc 19]],
  [[cc 16,cc 18,cc 37],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 33],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 18,cc 35],[],[cc 16,cc 19],[cc 80,cc 82,cc 19],[cc 16,cc 17],[cc 80,cc 82,cc 17],[cc 18,cc 17]],
  [[cc 16,cc 165],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 161],[cc 16,cc 82,cc 81],[cc 18,cc 17],[cc 16,cc 163],[cc 18,cc 17],[],[cc 16,cc 19],[cc 16,cc 82,cc 83],[cc 16,cc 17],[cc 16,cc 82,cc 81]],
  [[cc 18,cc 167],[cc 16,cc 19],[cc 80,cc 18,cc 83],[cc 18,cc 163],[cc 16,cc 17],[cc 16,cc 21],[cc 18,cc 161],[cc 80,cc 18,cc 81],[cc 18,cc 17],[],[cc 16,cc 19],[cc 80,cc 18,cc 83],[cc 16,cc 17]],
  [[cc 16,cc 18,cc 39],[cc 16,cc 21],[cc 16,cc 19],[cc 16,cc 18,cc 35],[cc 18,cc 19],[cc 16,cc 17],[cc 16,cc 18,cc 33],[cc 16,cc 17],[cc 80,cc 82,cc 17],[cc 18,cc 17],[],[cc 16,cc 19],[cc 80,cc 82,cc 19]],
  [[cc 16,cc 167],[cc 16,cc 82,cc 81],[cc 18,cc 17],[cc 16,cc 163],[cc 18,cc 21],[cc 18,cc 19],[cc 16,cc 161],[cc 16,cc 82,cc 83],[cc 16,cc 17],[cc 16,cc 82,cc 81],[cc 18,cc 17],[],[cc 16,cc 19]],
  [[cc 18,cc 165],[cc 16,cc 17],[cc 16,cc 21],[cc 18,cc 161],[cc 16,cc 19],[cc 80,cc 18,cc 83],[cc 18,cc 163],[cc 16,cc 19],[cc 80,cc 18,cc 83],[cc 16,cc 17],[cc 80,cc 18,cc 81],[cc 18,cc 17],[]]]

def cfg : GalCert.Cfg 10 := ⟨adj, (0, 0, 0), 10, regsData, certsData, 0, 0⟩

set_option maxHeartbeats 4000000 in
theorem hc : cfg.check = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem hV : cfg.vbound 29 = true := by decide +kernel

theorem hball : ∀ n, ball n = GalCert.ball cfg.adj cfg.x0 n
  | 0 => rfl
  | n + 1 => by rw [ball, GalCert.ball, hball n]; rfl

theorem ha (n : ℕ) (hn : 1 ≤ n) : a n = (cfg.A n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a, hball, hball]
  exact GalCert.Cfg.card_step hc k

set_option maxHeartbeats 4000000 in
theorem hrec : ∀ k, (([(1, 11), (-2, 10), (2, 9), (-2, 8), (2, 7), (-2, 6), (2, 5), (-2, 4), (2, 3), (-2, 2), (1, 1)] : List (ℤ × ℕ)).map fun p => p.1 * (cfg.A (k + p.2) : ℤ)).sum = 0 :=
  GalCert.Cfg.lin_zero hc hV _ (by decide) (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem hgfw : ∀ n < 29 + 2 * cfg.L, ((GalCert.csOfS [1, -2, 2, -2, 2, -2, 2, -2, 2, -2, 1] 0).map fun p => p.1 * (cfg.A (n + p.2) : ℤ)).sum = 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem hsmall : ∀ n < 11, GalCert.conv a [1, -2, 2, -2, 2, -2, 2, -2, 2, -2, 1] n = ([1, 2, 2, 2, 4, 0, 4, 2, 2, 2, 1] : List ℤ).getD n 0 := by
  have e : a = fun n => if n = 0 then 1 else (cfg.A n : ℤ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rfl
    · rw [if_neg (by omega)]; exact ha n h
  rw [e]
  decide +kernel

end P311601

open PowerSeries OMA.S_oeis_a311601 in
theorem OMA.solution : type_of% @OMA.S_oeis_a311601.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    have h := P311601.hrec k
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [show k + 11 - 1 = k + 10 by omega,
      show k + 11 - 2 = k + 9 by omega,
      show k + 11 - 3 = k + 8 by omega,
      show k + 11 - 4 = k + 7 by omega,
      show k + 11 - 5 = k + 6 by omega,
      show k + 11 - 6 = k + 5 by omega,
      show k + 11 - 7 = k + 4 by omega,
      show k + 11 - 8 = k + 3 by omega,
      show k + 11 - 9 = k + 2 by omega,
      show k + 11 - 10 = k + 1 by omega,
      P311601.ha (k + 11) (by omega),
      P311601.ha (k + 10) (by omega),
      P311601.ha (k + 9) (by omega),
      P311601.ha (k + 8) (by omega),
      P311601.ha (k + 7) (by omega),
      P311601.ha (k + 6) (by omega),
      P311601.ha (k + 5) (by omega),
      P311601.ha (k + 4) (by omega),
      P311601.ha (k + 3) (by omega),
      P311601.ha (k + 2) (by omega),
      P311601.ha (k + 1) (by omega)]
    linarith
  · have hD : ((X - 1)^2*(X^4 - X^3 + X^2 - X + 1)*(X^4 + X^3 + X^2 + X + 1) : PowerSeries ℤ) = GalCert.polyOf [1, -2, 2, -2, 2, -2, 2, -2, 2, -2, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    have hP : ((X^2 + 1)*(X^8 + 2*X^7 + X^6 + 3*X^4 + X^2 + 2*X + 1) : PowerSeries ℤ) = GalCert.polyOf [1, 2, 2, 2, 4, 0, 4, 2, 2, 2, 1] := by
      simp only [GalCert.polyOf, map_neg, map_one, map_zero, map_ofNat, map_intCast]; ring
    rw [hD, hP]
    exact GalCert.Cfg.gf_from2 P311601.hc P311601.hV a P311601.ha _ _ 0 11 (by decide) (by decide) P311601.hgfw P311601.hsmall
