import OMAStatements.S_oeis_a047926

/-!
Proof of OEIS A047926 conjecture:
For every n : Nat, the number of triples (x, y, z) with 0 < x <= y <= z and
x^2 + y^2 + z^2 = 3^(2*(n+1)) equals (3^(n+1) + 2*n + 1)/4.

Strategy:
1. Work in the Hurwitz integers HInt (coordinates (a, b, c, d)/2 of equal parity).
   Prove right Euclidean division, right GCD, existence and left-associate uniqueness
   of right divisors of norm 3^k for primitive elements, and deduce that there are
   96 * 3^(k-1) primitive Hurwitz integers of norm 3^k for k >= 1.
2. Map alpha |-> alpha * i * conj(alpha) onto primitive integer vectors (x, y, z)
   with x^2 + y^2 + z^2 = 3^(2k), showing surjectivity and 4-to-1 fibers, hence
   24 * 3^(k-1) primitive vectors and 12 * 3^k - 6 total signed vectors.
3. Count positive solutions to 2*x^2 + z^2 = 3^(2k) via unique factorization in
   Z[sqrt(-2)], obtaining exactly k solutions.
4. Remove vectors with a zero coordinate (6 vectors), divide by 8 sign choices, and
   partition positive vectors by equality pattern (0 with all three equal, 3k with
   two equal, remaining with three distinct).
-/

namespace A047926Proof

open Finset

-- ============================================================================
-- Section 1: Hurwitz integers
-- ============================================================================

private structure HInt where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  hab : 2 ∣ a - b
  hbc : 2 ∣ b - c
  hcd : 2 ∣ c - d

private lemma HInt.ext {x y : HInt} (ha : x.a = y.a) (hb : x.b = y.b)
    (hc : x.c = y.c) (hd : x.d = y.d) : x = y := by
  cases x; cases y; simp_all

private lemma hint_parity (x : HInt) :
    ∃ pa pb pc : ℤ, x.a = 2 * pa + x.d ∧ x.b = 2 * pb + x.d ∧ x.c = 2 * pc + x.d := by
  obtain ⟨k1, hk1⟩ := x.hab
  obtain ⟨k2, hk2⟩ := x.hbc
  obtain ⟨k3, hk3⟩ := x.hcd
  refine ⟨k1 + k2 + k3, k2 + k3, k3, ?_, ?_, ?_⟩ <;> omega

private instance : DecidableEq HInt := fun x y =>
  if h : x.a = y.a ∧ x.b = y.b ∧ x.c = y.c ∧ x.d = y.d then
    isTrue (HInt.ext h.1 h.2.1 h.2.2.1 h.2.2.2)
  else
    isFalse fun he => h ⟨congrArg HInt.a he, congrArg HInt.b he, congrArg HInt.c he, congrArg HInt.d he⟩

private def hzero : HInt := ⟨0, 0, 0, 0, by simp, by simp, by simp⟩
private def hone : HInt := ⟨2, 0, 0, 0, ⟨1, by ring⟩, by simp, by simp⟩
private def hqi : HInt := ⟨0, 2, 0, 0, ⟨-1, by ring⟩, ⟨1, by ring⟩, by simp⟩
private def hqj : HInt := ⟨0, 0, 2, 0, by simp, ⟨-1, by ring⟩, ⟨1, by ring⟩⟩
private def hqk : HInt := ⟨0, 0, 0, 2, by simp, by simp, ⟨-1, by ring⟩⟩
private def ofInt (n : ℤ) : HInt := ⟨2 * n, 0, 0, 0, ⟨n, by ring⟩, by simp, by simp⟩

private def hneg (x : HInt) : HInt :=
  ⟨-x.a, -x.b, -x.c, -x.d,
    by obtain ⟨k, hk⟩ := x.hab; exact ⟨-k, by omega⟩,
    by obtain ⟨k, hk⟩ := x.hbc; exact ⟨-k, by omega⟩,
    by obtain ⟨k, hk⟩ := x.hcd; exact ⟨-k, by omega⟩⟩

private def hadd (x y : HInt) : HInt :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d,
    by obtain ⟨k1, h1⟩ := x.hab; obtain ⟨k2, h2⟩ := y.hab; exact ⟨k1 + k2, by omega⟩,
    by obtain ⟨k1, h1⟩ := x.hbc; obtain ⟨k2, h2⟩ := y.hbc; exact ⟨k1 + k2, by omega⟩,
    by obtain ⟨k1, h1⟩ := x.hcd; obtain ⟨k2, h2⟩ := y.hcd; exact ⟨k1 + k2, by omega⟩⟩

private def hsub (x y : HInt) : HInt := hadd x (hneg y)

private def HInt.conj (x : HInt) : HInt :=
  ⟨x.a, -x.b, -x.c, -x.d,
    by obtain ⟨pa, pb, pc, ha, hb, hc⟩ := hint_parity x; exact ⟨pa + pb + x.d, by omega⟩,
    by obtain ⟨pa, pb, pc, ha, hb, hc⟩ := hint_parity x; exact ⟨pc - pb, by omega⟩,
    by obtain ⟨pa, pb, pc, ha, hb, hc⟩ := hint_parity x; exact ⟨-pc, by omega⟩⟩

private lemma hmul_div2 (x y : HInt) :
    2 ∣ (x.a * y.a - x.b * y.b - x.c * y.c - x.d * y.d) ∧
    2 ∣ (x.a * y.b + x.b * y.a + x.c * y.d - x.d * y.c) ∧
    2 ∣ (x.a * y.c - x.b * y.d + x.c * y.a + x.d * y.b) ∧
    2 ∣ (x.a * y.d + x.b * y.c - x.c * y.b + x.d * y.a) ∧
    4 ∣ ((x.a * y.a - x.b * y.b - x.c * y.c - x.d * y.d) -
         (x.a * y.b + x.b * y.a + x.c * y.d - x.d * y.c)) ∧
    4 ∣ ((x.a * y.b + x.b * y.a + x.c * y.d - x.d * y.c) -
         (x.a * y.c - x.b * y.d + x.c * y.a + x.d * y.b)) ∧
    4 ∣ ((x.a * y.c - x.b * y.d + x.c * y.a + x.d * y.b) -
         (x.a * y.d + x.b * y.c - x.c * y.b + x.d * y.a)) := by
  obtain ⟨pa, pb, pc, hxa, hxb, hxc⟩ := hint_parity x
  obtain ⟨qa, qb, qc, hya, hyb, hyc⟩ := hint_parity y
  rw [hxa, hxb, hxc, hya, hyb, hyc]
  refine ⟨⟨2 * pa * qa + pa * y.d + qa * x.d - 2 * pb * qb - pb * y.d - qb * x.d -
      2 * pc * qc - pc * y.d - qc * x.d - x.d * y.d, by ring⟩,
    ⟨2 * pa * qb + pa * y.d + 2 * qa * pb + qa * x.d + pb * y.d + qb * x.d +
      pc * y.d - qc * x.d + x.d * y.d, by ring⟩,
    ⟨2 * pa * qc + pa * y.d + 2 * qa * pc + qa * x.d - pb * y.d + qb * x.d +
      pc * y.d + qc * x.d + x.d * y.d, by ring⟩,
    ⟨pa * y.d + qa * x.d + 2 * pb * qc + pb * y.d - 2 * qb * pc - qb * x.d -
      pc * y.d + qc * x.d + x.d * y.d, by ring⟩,
    ⟨pa * qa - pa * qb - pb * qa - pb * qb - pb * y.d - pc * qc - pc * y.d - qb * x.d - x.d * y.d, by ring⟩,
    ⟨pa * qb - pa * qc + pb * qa + pb * y.d - pc * qa - qc * x.d, by ring⟩,
    ⟨pa * qc - pb * qc - pb * y.d + pc * qa + pc * qb + pc * y.d + qb * x.d, by ring⟩⟩

private def hmul (x y : HInt) : HInt :=
  let na := x.a * y.a - x.b * y.b - x.c * y.c - x.d * y.d
  let nb := x.a * y.b + x.b * y.a + x.c * y.d - x.d * y.c
  let nc := x.a * y.c - x.b * y.d + x.c * y.a + x.d * y.b
  let nd := x.a * y.d + x.b * y.c - x.c * y.b + x.d * y.a
  ⟨na / 2, nb / 2, nc / 2, nd / 2,
    by have h := hmul_div2 x y; obtain ⟨k, hk⟩ := h.2.2.2.2.1; exact ⟨k, by omega⟩,
    by have h := hmul_div2 x y; obtain ⟨k, hk⟩ := h.2.2.2.2.2.1; exact ⟨k, by omega⟩,
    by have h := hmul_div2 x y; obtain ⟨k, hk⟩ := h.2.2.2.2.2.2; exact ⟨k, by omega⟩⟩

private instance : Zero HInt := ⟨hzero⟩
private instance : One HInt := ⟨hone⟩
private instance : Neg HInt := ⟨hneg⟩
private instance : Add HInt := ⟨hadd⟩
private instance : Sub HInt := ⟨hsub⟩
private instance : Mul HInt := ⟨hmul⟩

@[simp] private lemma zero_a : (0 : HInt).a = 0 := rfl
@[simp] private lemma zero_b : (0 : HInt).b = 0 := rfl
@[simp] private lemma zero_c : (0 : HInt).c = 0 := rfl
@[simp] private lemma zero_d : (0 : HInt).d = 0 := rfl
@[simp] private lemma one_a : (1 : HInt).a = 2 := rfl
@[simp] private lemma one_b : (1 : HInt).b = 0 := rfl
@[simp] private lemma one_c : (1 : HInt).c = 0 := rfl
@[simp] private lemma one_d : (1 : HInt).d = 0 := rfl
@[simp] private lemma neg_a (x : HInt) : (-x).a = -x.a := rfl
@[simp] private lemma neg_b (x : HInt) : (-x).b = -x.b := rfl
@[simp] private lemma neg_c (x : HInt) : (-x).c = -x.c := rfl
@[simp] private lemma neg_d (x : HInt) : (-x).d = -x.d := rfl
@[simp] private lemma add_a (x y : HInt) : (x + y).a = x.a + y.a := rfl
@[simp] private lemma add_b (x y : HInt) : (x + y).b = x.b + y.b := rfl
@[simp] private lemma add_c (x y : HInt) : (x + y).c = x.c + y.c := rfl
@[simp] private lemma add_d (x y : HInt) : (x + y).d = x.d + y.d := rfl
@[simp] private lemma sub_a (x y : HInt) : (x - y).a = x.a - y.a := rfl
@[simp] private lemma sub_b (x y : HInt) : (x - y).b = x.b - y.b := rfl
@[simp] private lemma sub_c (x y : HInt) : (x - y).c = x.c - y.c := rfl
@[simp] private lemma sub_d (x y : HInt) : (x - y).d = x.d - y.d := rfl
@[simp] private lemma conj_a (x : HInt) : x.conj.a = x.a := rfl
@[simp] private lemma conj_b (x : HInt) : x.conj.b = -x.b := rfl
@[simp] private lemma conj_c (x : HInt) : x.conj.c = -x.c := rfl
@[simp] private lemma conj_d (x : HInt) : x.conj.d = -x.d := rfl
@[simp] private lemma ofInt_a (n : ℤ) : (ofInt n).a = 2 * n := rfl
@[simp] private lemma ofInt_b (n : ℤ) : (ofInt n).b = 0 := rfl
@[simp] private lemma ofInt_c (n : ℤ) : (ofInt n).c = 0 := rfl
@[simp] private lemma ofInt_d (n : ℤ) : (ofInt n).d = 0 := rfl

private lemma two_mul_a (x y : HInt) :
    2 * (x * y).a = x.a * y.a - x.b * y.b - x.c * y.c - x.d * y.d :=
  Int.mul_ediv_cancel' (hmul_div2 x y).1

private lemma two_mul_b (x y : HInt) :
    2 * (x * y).b = x.a * y.b + x.b * y.a + x.c * y.d - x.d * y.c :=
  Int.mul_ediv_cancel' (hmul_div2 x y).2.1

private lemma two_mul_c (x y : HInt) :
    2 * (x * y).c = x.a * y.c - x.b * y.d + x.c * y.a + x.d * y.b :=
  Int.mul_ediv_cancel' (hmul_div2 x y).2.2.1

private lemma two_mul_d (x y : HInt) :
    2 * (x * y).d = x.a * y.d + x.b * y.c - x.c * y.b + x.d * y.a :=
  Int.mul_ediv_cancel' (hmul_div2 x y).2.2.2.1

private lemma hint_ext4 {x y : HInt}
    (ha : 4 * x.a = 4 * y.a) (hb : 4 * x.b = 4 * y.b)
    (hc : 4 * x.c = 4 * y.c) (hd : 4 * x.d = 4 * y.d) : x = y := by
  apply HInt.ext <;> omega

private lemma hint_ext2 {x y : HInt}
    (ha : 2 * x.a = 2 * y.a) (hb : 2 * x.b = 2 * y.b)
    (hc : 2 * x.c = 2 * y.c) (hd : 2 * x.d = 2 * y.d) : x = y := by
  apply HInt.ext <;> omega

private lemma hmul_assoc (x y z : HInt) : (x * y) * z = x * (y * z) := by
  apply hint_ext4
  · rw [show 4 * ((x * y) * z).a = 2 * (2 * ((x * y) * z).a) by ring, two_mul_a]
    rw [show 4 * (x * (y * z)).a = 2 * (2 * (x * (y * z)).a) by ring, two_mul_a]
    simp only [mul_sub]
    rw [show 2 * ((x * y).a * z.a) = (2 * (x * y).a) * z.a by ring, two_mul_a]
    rw [show 2 * ((x * y).b * z.b) = (2 * (x * y).b) * z.b by ring, two_mul_b]
    rw [show 2 * ((x * y).c * z.c) = (2 * (x * y).c) * z.c by ring, two_mul_c]
    rw [show 2 * ((x * y).d * z.d) = (2 * (x * y).d) * z.d by ring, two_mul_d]
    rw [show 2 * (x.a * (y * z).a) = x.a * (2 * (y * z).a) by ring, two_mul_a]
    rw [show 2 * (x.b * (y * z).b) = x.b * (2 * (y * z).b) by ring, two_mul_b]
    rw [show 2 * (x.c * (y * z).c) = x.c * (2 * (y * z).c) by ring, two_mul_c]
    rw [show 2 * (x.d * (y * z).d) = x.d * (2 * (y * z).d) by ring, two_mul_d]
    ring
  · rw [show 4 * ((x * y) * z).b = 2 * (2 * ((x * y) * z).b) by ring, two_mul_b]
    rw [show 4 * (x * (y * z)).b = 2 * (2 * (x * (y * z)).b) by ring, two_mul_b]
    simp only [mul_sub, mul_add]
    rw [show 2 * ((x * y).a * z.b) = (2 * (x * y).a) * z.b by ring, two_mul_a]
    rw [show 2 * ((x * y).b * z.a) = (2 * (x * y).b) * z.a by ring, two_mul_b]
    rw [show 2 * ((x * y).c * z.d) = (2 * (x * y).c) * z.d by ring, two_mul_c]
    rw [show 2 * ((x * y).d * z.c) = (2 * (x * y).d) * z.c by ring, two_mul_d]
    rw [show 2 * (x.a * (y * z).b) = x.a * (2 * (y * z).b) by ring, two_mul_b]
    rw [show 2 * (x.b * (y * z).a) = x.b * (2 * (y * z).a) by ring, two_mul_a]
    rw [show 2 * (x.c * (y * z).d) = x.c * (2 * (y * z).d) by ring, two_mul_d]
    rw [show 2 * (x.d * (y * z).c) = x.d * (2 * (y * z).c) by ring, two_mul_c]
    ring
  · rw [show 4 * ((x * y) * z).c = 2 * (2 * ((x * y) * z).c) by ring, two_mul_c]
    rw [show 4 * (x * (y * z)).c = 2 * (2 * (x * (y * z)).c) by ring, two_mul_c]
    simp only [mul_sub, mul_add]
    rw [show 2 * ((x * y).a * z.c) = (2 * (x * y).a) * z.c by ring, two_mul_a]
    rw [show 2 * ((x * y).b * z.d) = (2 * (x * y).b) * z.d by ring, two_mul_b]
    rw [show 2 * ((x * y).c * z.a) = (2 * (x * y).c) * z.a by ring, two_mul_c]
    rw [show 2 * ((x * y).d * z.b) = (2 * (x * y).d) * z.b by ring, two_mul_d]
    rw [show 2 * (x.a * (y * z).c) = x.a * (2 * (y * z).c) by ring, two_mul_c]
    rw [show 2 * (x.b * (y * z).d) = x.b * (2 * (y * z).d) by ring, two_mul_d]
    rw [show 2 * (x.c * (y * z).a) = x.c * (2 * (y * z).a) by ring, two_mul_a]
    rw [show 2 * (x.d * (y * z).b) = x.d * (2 * (y * z).b) by ring, two_mul_b]
    ring
  · rw [show 4 * ((x * y) * z).d = 2 * (2 * ((x * y) * z).d) by ring, two_mul_d]
    rw [show 4 * (x * (y * z)).d = 2 * (2 * (x * (y * z)).d) by ring, two_mul_d]
    simp only [mul_sub, mul_add]
    rw [show 2 * ((x * y).a * z.d) = (2 * (x * y).a) * z.d by ring, two_mul_a]
    rw [show 2 * ((x * y).b * z.c) = (2 * (x * y).b) * z.c by ring, two_mul_b]
    rw [show 2 * ((x * y).c * z.b) = (2 * (x * y).c) * z.b by ring, two_mul_c]
    rw [show 2 * ((x * y).d * z.a) = (2 * (x * y).d) * z.a by ring, two_mul_d]
    rw [show 2 * (x.a * (y * z).d) = x.a * (2 * (y * z).d) by ring, two_mul_d]
    rw [show 2 * (x.b * (y * z).c) = x.b * (2 * (y * z).c) by ring, two_mul_c]
    rw [show 2 * (x.c * (y * z).b) = x.c * (2 * (y * z).b) by ring, two_mul_b]
    rw [show 2 * (x.d * (y * z).a) = x.d * (2 * (y * z).a) by ring, two_mul_a]
    ring

private lemma hone_mul (x : HInt) : 1 * x = x := by
  apply hint_ext2
  · rw [two_mul_a]; simp
  · rw [two_mul_b]; simp
  · rw [two_mul_c]; simp
  · rw [two_mul_d]; simp

private lemma hmul_one (x : HInt) : x * 1 = x := by
  apply hint_ext2
  · rw [two_mul_a]; simp; ring
  · rw [two_mul_b]; simp; ring
  · rw [two_mul_c]; simp; ring
  · rw [two_mul_d]; simp; ring

private lemma hzero_mul (x : HInt) : 0 * x = 0 := by
  apply hint_ext2
  · rw [two_mul_a]; simp
  · rw [two_mul_b]; simp
  · rw [two_mul_c]; simp
  · rw [two_mul_d]; simp

private lemma hmul_zero (x : HInt) : x * 0 = 0 := by
  apply hint_ext2
  · rw [two_mul_a]; simp
  · rw [two_mul_b]; simp
  · rw [two_mul_c]; simp
  · rw [two_mul_d]; simp

private lemma hleft_distrib (x y z : HInt) : x * (y + z) = x * y + x * z := by
  apply hint_ext2
  · have h2 : 2 * (x * y + x * z).a = 2 * (x * y).a + 2 * (x * z).a := by rw [add_a, mul_add]
    rw [two_mul_a, h2, two_mul_a, two_mul_a]; simp only [add_a, add_b, add_c, add_d]; ring
  · have h2 : 2 * (x * y + x * z).b = 2 * (x * y).b + 2 * (x * z).b := by rw [add_b, mul_add]
    rw [two_mul_b, h2, two_mul_b, two_mul_b]; simp only [add_a, add_b, add_c, add_d]; ring
  · have h2 : 2 * (x * y + x * z).c = 2 * (x * y).c + 2 * (x * z).c := by rw [add_c, mul_add]
    rw [two_mul_c, h2, two_mul_c, two_mul_c]; simp only [add_a, add_b, add_c, add_d]; ring
  · have h2 : 2 * (x * y + x * z).d = 2 * (x * y).d + 2 * (x * z).d := by rw [add_d, mul_add]
    rw [two_mul_d, h2, two_mul_d, two_mul_d]; simp only [add_a, add_b, add_c, add_d]; ring

private lemma hright_distrib (x y z : HInt) : (x + y) * z = x * z + y * z := by
  apply hint_ext2
  · have h2 : 2 * (x * z + y * z).a = 2 * (x * z).a + 2 * (y * z).a := by rw [add_a, mul_add]
    rw [two_mul_a, h2, two_mul_a, two_mul_a]; simp only [add_a, add_b, add_c, add_d]; ring
  · have h2 : 2 * (x * z + y * z).b = 2 * (x * z).b + 2 * (y * z).b := by rw [add_b, mul_add]
    rw [two_mul_b, h2, two_mul_b, two_mul_b]; simp only [add_a, add_b, add_c, add_d]; ring
  · have h2 : 2 * (x * z + y * z).c = 2 * (x * z).c + 2 * (y * z).c := by rw [add_c, mul_add]
    rw [two_mul_c, h2, two_mul_c, two_mul_c]; simp only [add_a, add_b, add_c, add_d]; ring
  · have h2 : 2 * (x * z + y * z).d = 2 * (x * z).d + 2 * (y * z).d := by rw [add_d, mul_add]
    rw [two_mul_d, h2, two_mul_d, two_mul_d]; simp only [add_a, add_b, add_c, add_d]; ring

private instance : Ring HInt where
  add := (· + ·)
  add_assoc a b c := by apply HInt.ext <;> simp <;> ring
  zero := 0
  zero_add a := by apply HInt.ext <;> simp
  add_zero a := by apply HInt.ext <;> simp
  nsmul := nsmulRec
  neg := (-·)
  zsmul := zsmulRec
  neg_add_cancel a := by apply HInt.ext <;> simp
  add_comm a b := by apply HInt.ext <;> simp <;> ring
  sub := (· - ·)
  sub_eq_add_neg a b := rfl
  mul := (· * ·)
  mul_assoc := hmul_assoc
  one := 1
  one_mul := hone_mul
  mul_one := hmul_one
  zero_mul := hzero_mul
  mul_zero := hmul_zero
  left_distrib := hleft_distrib
  right_distrib := hright_distrib

private lemma ofInt_one : ofInt 1 = 1 := rfl
private lemma ofInt_zero : ofInt 0 = 0 := rfl

private lemma ofInt_mul (n : ℤ) (x : HInt) :
    ofInt n * x = ⟨n * x.a, n * x.b, n * x.c, n * x.d,
      by obtain ⟨k, hk⟩ := x.hab; exact ⟨n * k, by linear_combination n * hk⟩,
      by obtain ⟨k, hk⟩ := x.hbc; exact ⟨n * k, by linear_combination n * hk⟩,
      by obtain ⟨k, hk⟩ := x.hcd; exact ⟨n * k, by linear_combination n * hk⟩⟩ := by
  apply hint_ext2
  · rw [two_mul_a]; simp; ring
  · rw [two_mul_b]; simp; ring
  · rw [two_mul_c]; simp; ring
  · rw [two_mul_d]; simp; ring

private lemma ofInt_mul_comm (n : ℤ) (x : HInt) : ofInt n * x = x * ofInt n := by
  apply hint_ext2
  · rw [two_mul_a, two_mul_a]; simp; ring
  · rw [two_mul_b, two_mul_b]; simp; ring
  · rw [two_mul_c, two_mul_c]; simp; ring
  · rw [two_mul_d, two_mul_d]; simp; ring

private lemma ofInt_mul_ofInt (m n : ℤ) : ofInt m * ofInt n = ofInt (m * n) := by
  rw [ofInt_mul]; apply HInt.ext <;> (simp; try ring)

private def norm4 (x : HInt) : ℤ := x.a ^ 2 + x.b ^ 2 + x.c ^ 2 + x.d ^ 2

private lemma four_dvd_norm4 (x : HInt) : 4 ∣ norm4 x := by
  obtain ⟨pa, pb, pc, ha, hb, hc⟩ := hint_parity x
  refine ⟨pa ^ 2 + pa * x.d + pb ^ 2 + pb * x.d + pc ^ 2 + pc * x.d + x.d ^ 2, ?_⟩
  simp only [norm4, ha, hb, hc]
  ring

private def norm (x : HInt) : ℤ := norm4 x / 4

private lemma four_mul_norm (x : HInt) : 4 * norm x = norm4 x :=
  Int.mul_ediv_cancel' (four_dvd_norm4 x)

private lemma norm_nonneg (x : HInt) : 0 ≤ norm x := by
  have h : 0 ≤ norm4 x := by unfold norm4; positivity
  have h4 := four_mul_norm x
  omega

private lemma norm_eq_zero_iff (x : HInt) : norm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h4 : norm4 x = 0 := by linarith [four_mul_norm x]
    unfold norm4 at h4
    have ha : x.a = 0 := by nlinarith
    have hb : x.b = 0 := by nlinarith
    have hc : x.c = 0 := by nlinarith
    have hd : x.d = 0 := by nlinarith
    exact HInt.ext ha hb hc hd
  · rintro rfl; simp [norm, norm4]

private lemma norm_conj (x : HInt) : norm x.conj = norm x := by
  have h : norm4 x.conj = norm4 x := by simp [norm4]
  linarith [four_mul_norm x.conj, four_mul_norm x]

private lemma mul_conj (x : HInt) : x * x.conj = ofInt (norm x) := by
  apply hint_ext2
  · rw [two_mul_a]; simp only [conj_a, conj_b, conj_c, conj_d, ofInt_a]
    linarith [four_mul_norm x, show norm4 x = x.a^2 + x.b^2 + x.c^2 + x.d^2 from rfl]
  · rw [two_mul_b]; simp; ring
  · rw [two_mul_c]; simp; ring
  · rw [two_mul_d]; simp; ring

private lemma conj_mul (x : HInt) : x.conj * x = ofInt (norm x) := by
  apply hint_ext2
  · rw [two_mul_a]; simp only [conj_a, conj_b, conj_c, conj_d, ofInt_a]
    linarith [four_mul_norm x, show norm4 x = x.a^2 + x.b^2 + x.c^2 + x.d^2 from rfl]
  · rw [two_mul_b]; simp; ring
  · rw [two_mul_c]; simp; ring
  · rw [two_mul_d]; simp; ring

private lemma conj_conj (x : HInt) : x.conj.conj = x := by
  apply HInt.ext <;> simp

private lemma conj_mul_eq (x y : HInt) : (x * y).conj = y.conj * x.conj := by
  apply hint_ext2
  · rw [conj_a, two_mul_a, two_mul_a]; simp; ring
  · rw [conj_b, mul_neg, two_mul_b, two_mul_b]; simp; ring
  · rw [conj_c, mul_neg, two_mul_c, two_mul_c]; simp; ring
  · rw [conj_d, mul_neg, two_mul_d, two_mul_d]; simp; ring

private lemma ofInt_inj {m n : ℤ} (h : ofInt m = ofInt n) : m = n := by
  have := congrArg HInt.a h
  simp only [ofInt_a] at this
  omega

private lemma norm_mul (x y : HInt) : norm (x * y) = norm x * norm y := by
  apply ofInt_inj
  rw [← mul_conj (x * y), conj_mul_eq, mul_assoc, ← mul_assoc y y.conj x.conj,
    mul_conj y, ofInt_mul_comm (norm y) x.conj, ← mul_assoc, mul_conj x, ofInt_mul_ofInt]

private lemma norm_ofInt (n : ℤ) : norm (ofInt n) = n ^ 2 := by
  have h := four_mul_norm (ofInt n)
  simp only [norm4, ofInt_a, ofInt_b, ofInt_c, ofInt_d] at h
  linarith

private lemma hmul_left_cancel {z x y : HInt} (hz : z ≠ 0) (h : z * x = z * y) : x = y := by
  have h0 : z * (x - y) = 0 := by rw [mul_sub, h, sub_self]
  have hn : norm z * norm (x - y) = 0 := by
    rw [← norm_mul, h0, (norm_eq_zero_iff 0).mpr rfl]
  have hzn : norm z ≠ 0 := fun e => hz ((norm_eq_zero_iff z).mp e)
  have hxy : norm (x - y) = 0 := (mul_eq_zero.mp hn).resolve_left hzn
  exact sub_eq_zero.mp ((norm_eq_zero_iff (x - y)).mp hxy)

private lemma hmul_right_cancel {z x y : HInt} (hz : z ≠ 0) (h : x * z = y * z) : x = y := by
  have h0 : (x - y) * z = 0 := by rw [sub_mul, h, sub_self]
  have hn : norm (x - y) * norm z = 0 := by
    rw [← norm_mul, h0, (norm_eq_zero_iff 0).mpr rfl]
  have hzn : norm z ≠ 0 := fun e => hz ((norm_eq_zero_iff z).mp e)
  have hxy : norm (x - y) = 0 := (mul_eq_zero.mp hn).resolve_right hzn
  exact sub_eq_zero.mp ((norm_eq_zero_iff (x - y)).mp hxy)

-- ============================================================================
-- Section 2: Right Euclidean division, GCD, and divisibility by 3
-- ============================================================================

private lemma round_rem_bounds (c N : ℤ) (hN : 0 < N) :
    -N ≤ c - 2 * N * ((c + N) / (2 * N)) ∧ c - 2 * N * ((c + N) / (2 * N)) < N := by
  have h2N : 0 < 2 * N := by omega
  have hmod1 : 0 ≤ (c + N) % (2 * N) := Int.emod_nonneg _ (by omega)
  have hmod2 : (c + N) % (2 * N) < 2 * N := Int.emod_lt_of_pos _ h2N
  have hdiv : 2 * N * ((c + N) / (2 * N)) + (c + N) % (2 * N) = c + N :=
    Int.mul_ediv_add_emod (c + N) (2 * N)
  omega

private lemma right_div_mod (x y : HInt) (hy : y ≠ 0) :
    ∃ q r : HInt, x = q * y + r ∧ norm r < norm y := by
  set N := norm y
  have hN : 0 < N := lt_of_le_of_ne (norm_nonneg y) (Ne.symm fun e => hy ((norm_eq_zero_iff y).mp e))
  set z := x * y.conj
  set ka := (z.a + N) / (2 * N)
  set kb := (z.b + N) / (2 * N)
  set kc := (z.c + N) / (2 * N)
  set kd := (z.d + N) / (2 * N)
  set ra := z.a - 2 * N * ka
  set rb := z.b - 2 * N * kb
  set rc := z.c - 2 * N * kc
  set rd := z.d - 2 * N * kd
  have ha_b := round_rem_bounds z.a N hN
  have hb_b := round_rem_bounds z.b N hN
  have hc_b := round_rem_bounds z.c N hN
  have hd_b := round_rem_bounds z.d N hN
  by_cases hall : ra = -N ∧ rb = -N ∧ rc = -N ∧ rd = -N
  · refine ⟨⟨2 * ka - 1, 2 * kb - 1, 2 * kc - 1, 2 * kd - 1,
      ⟨ka - kb, by ring⟩, ⟨kb - kc, by ring⟩, ⟨kc - kd, by ring⟩⟩, 0, ?_, ?_⟩
    · apply hmul_right_cancel (show y.conj ≠ 0 from fun e =>
        hy (by rw [← conj_conj y, e]; apply HInt.ext <;> simp))
      rw [add_zero, mul_assoc, mul_conj y, ← ofInt_mul_comm]
      rw [ofInt_mul]
      apply HInt.ext <;> dsimp <;> linarith [hall.1, hall.2.1, hall.2.2.1, hall.2.2.2]
    · simpa [norm, norm4] using hN
  · set q : HInt := ⟨2 * ka, 2 * kb, 2 * kc, 2 * kd,
      ⟨ka - kb, by ring⟩, ⟨kb - kc, by ring⟩, ⟨kc - kd, by ring⟩⟩
    refine ⟨q, x - q * y, by abel, ?_⟩
    have hsum : ra ^ 2 + rb ^ 2 + rc ^ 2 + rd ^ 2 < 4 * N ^ 2 := by
      have ha2 : ra ^ 2 ≤ N ^ 2 := by nlinarith [ha_b.1, ha_b.2]
      have hb2 : rb ^ 2 ≤ N ^ 2 := by nlinarith [hb_b.1, hb_b.2]
      have hc2 : rc ^ 2 ≤ N ^ 2 := by nlinarith [hc_b.1, hc_b.2]
      have hd2 : rd ^ 2 ≤ N ^ 2 := by nlinarith [hd_b.1, hd_b.2]
      by_cases hae : ra = -N
      · by_cases hbe : rb = -N
        · by_cases hce : rc = -N
          · have hde : rd ≠ -N := fun h => hall ⟨hae, hbe, hce, h⟩
            have h1 : -N < rd := lt_of_le_of_ne hd_b.1 (Ne.symm hde)
            have hdlt : rd ^ 2 < N ^ 2 := by nlinarith [hd_b.2]
            linarith
          · have h1 : -N < rc := lt_of_le_of_ne hc_b.1 (Ne.symm hce)
            have hclt : rc ^ 2 < N ^ 2 := by nlinarith [hc_b.2]
            linarith
        · have h1 : -N < rb := lt_of_le_of_ne hb_b.1 (Ne.symm hbe)
          have hblt : rb ^ 2 < N ^ 2 := by nlinarith [hb_b.2]
          linarith
      · have h1 : -N < ra := lt_of_le_of_ne ha_b.1 (Ne.symm hae)
        have halt : ra ^ 2 < N ^ 2 := by nlinarith [ha_b.2]
        linarith
    have hprod : (x - q * y) * y.conj = z - ofInt N * q := by
      rw [sub_mul, mul_assoc, mul_conj y, ofInt_mul_comm]
    have hnorm4 : norm4 ((x - q * y) * y.conj) = ra ^ 2 + rb ^ 2 + rc ^ 2 + rd ^ 2 := by
      rw [hprod]
      simp only [norm4, sub_a, sub_b, sub_c, sub_d, ofInt_mul]
      dsimp [q, ra, rb, rc, rd]
      ring
    have hmuln : 4 * (norm (x - q * y) * N) < 4 * (N * N) := by
      have hnc : norm y.conj = N := norm_conj y
      nth_rw 1 [← hnc]
      rw [← norm_mul, four_mul_norm, hnorm4]
      linarith [show N ^ 2 = N * N by ring]
    have hlt : norm (x - q * y) * N < N * N := by linarith
    exact lt_of_mul_lt_mul_right hlt (le_of_lt hN)

private lemma rgcd_aux (n : ℕ) : ∀ x y : HInt, (norm y).toNat ≤ n →
    ∃ g u v s t : HInt, x = u * g ∧ y = v * g ∧ s * x + t * y = g := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hle
    by_cases hy : y = 0
    · refine ⟨x, 1, 0, 1, 0, ?_, ?_, ?_⟩
      · rw [one_mul]
      · rw [zero_mul, hy]
      · rw [one_mul, zero_mul, add_zero]
    · obtain ⟨q, r, hqr, hrlt⟩ := right_div_mod x y hy
      have hr_nn : 0 ≤ norm r := norm_nonneg r
      have hy_nn : 0 ≤ norm y := norm_nonneg y
      have hrt : (norm r).toNat < n := by omega
      obtain ⟨g, u', v', s', t', hy_eq, hr_eq, hg_eq⟩ := ih (norm r).toNat hrt y r (le_refl _)
      refine ⟨g, q * u' + v', u', t', s' - t' * q, ?_, hy_eq, ?_⟩
      · rw [hqr, hy_eq, hr_eq, add_mul, mul_assoc]
      · have hrew : t' * (q * y + r) + (s' - t' * q) * y = s' * y + t' * r := by
          rw [mul_add, sub_mul, ← mul_assoc t' q y]; abel
        rw [hqr, hrew, hg_eq]

private lemma rgcd (x y : HInt) :
    ∃ g u v s t : HInt, x = u * g ∧ y = v * g ∧ s * x + t * y = g :=
  rgcd_aux (norm y).toNat x y (le_refl _)

private def div3 (x : HInt) : Prop :=
  3 ∣ x.a ∧ 3 ∣ x.b ∧ 3 ∣ x.c ∧ 3 ∣ x.d

private instance : DecidablePred div3 := fun x =>
  inferInstanceAs (Decidable (3 ∣ x.a ∧ 3 ∣ x.b ∧ 3 ∣ x.c ∧ 3 ∣ x.d))

private lemma div3_iff_exists (x : HInt) : div3 x ↔ ∃ y : HInt, x = ofInt 3 * y := by
  constructor
  · rintro ⟨⟨a', ha⟩, ⟨b', hb⟩, ⟨c', hc⟩, ⟨d', hd⟩⟩
    have hab : 2 ∣ a' - b' := by
      obtain ⟨k, hk⟩ := x.hab
      have : 3 * (a' - b') = 2 * k := by omega
      omega
    have hbc : 2 ∣ b' - c' := by
      obtain ⟨k, hk⟩ := x.hbc
      have : 3 * (b' - c') = 2 * k := by omega
      omega
    have hcd : 2 ∣ c' - d' := by
      obtain ⟨k, hk⟩ := x.hcd
      have : 3 * (c' - d') = 2 * k := by omega
      omega
    refine ⟨⟨a', b', c', d', hab, hbc, hcd⟩, ?_⟩
    rw [ofInt_mul]
    apply HInt.ext <;> dsimp <;> omega
  · rintro ⟨y, rfl⟩
    rw [ofInt_mul]
    exact ⟨⟨y.a, rfl⟩, ⟨y.b, rfl⟩, ⟨y.c, rfl⟩, ⟨y.d, rfl⟩⟩

private lemma div3_mul_left (x y : HInt) (hy : div3 y) : div3 (x * y) := by
  obtain ⟨z, rfl⟩ := (div3_iff_exists y).mp hy
  rw [← mul_assoc, ← ofInt_mul_comm 3 x, mul_assoc]
  exact (div3_iff_exists _).mpr ⟨x * z, rfl⟩

private lemma div3_mul_right (x y : HInt) (hx : div3 x) : div3 (x * y) := by
  obtain ⟨z, rfl⟩ := (div3_iff_exists x).mp hx
  rw [mul_assoc]
  exact (div3_iff_exists _).mpr ⟨z * y, rfl⟩

private lemma div3_conj {x : HInt} : div3 x.conj ↔ div3 x := by
  simp only [div3, conj_a, conj_b, conj_c, conj_d, dvd_neg]

private lemma nine_dvd_norm_of_div3 {x : HInt} (hx : div3 x) : 9 ∣ norm x := by
  obtain ⟨y, rfl⟩ := (div3_iff_exists x).mp hx
  rw [norm_mul, norm_ofInt]
  exact ⟨norm y, by ring⟩

private lemma not_three_dvd_norm_one_sub_div3 (z : HInt) (hz : div3 z) :
    ¬ (3 ∣ norm (1 - z)) := by
  obtain ⟨w, rfl⟩ := (div3_iff_exists z).mp hz
  have h4 := four_mul_norm (1 - ofInt 3 * w)
  rw [norm4, ofInt_mul] at h4
  dsimp at h4
  intro h3
  have h3' : (3 : ℤ) ∣ 4 * norm (1 - ofInt 3 * w) := dvd_mul_of_dvd_right h3 4
  rw [ofInt_mul] at h3'
  rw [h4] at h3'
  simp only [zero_sub] at h3'
  rw [show (2 - 3 * w.a) ^ 2 + (-(3 * w.b)) ^ 2 + (-(3 * w.c)) ^ 2 + (-(3 * w.d)) ^ 2 =
      (2 - 3 * w.a) ^ 2 + (-3 * w.b) ^ 2 + (-3 * w.c) ^ 2 + (-3 * w.d) ^ 2 by ring] at h3'
  have hmod : ((2 - 3 * w.a) ^ 2 + (-3 * w.b) ^ 2 + (-3 * w.c) ^ 2 + (-3 * w.d) ^ 2) % 3 = 1 := by
    have ha : (2 - 3 * w.a) ^ 2 = 4 - 12 * w.a + 9 * w.a ^ 2 := by ring
    have hrem : (4 - 12 * w.a + 9 * w.a ^ 2 + (-3 * w.b) ^ 2 + (-3 * w.c) ^ 2 + (-3 * w.d) ^ 2) =
        1 + 3 * (1 - 4 * w.a + 3 * w.a ^ 2 + 3 * w.b ^ 2 + 3 * w.c ^ 2 + 3 * w.d ^ 2) := by ring
    rw [ha, hrem]
    omega
  have h0 : ((2 - 3 * w.a) ^ 2 + (-3 * w.b) ^ 2 + (-3 * w.c) ^ 2 + (-3 * w.d) ^ 2) % 3 = 0 :=
    Int.emod_eq_zero_of_dvd h3'
  omega

private lemma ofInt_pow (m : ℤ) (k : ℕ) : (ofInt m) ^ k = ofInt (m ^ k) := by
  induction k with
  | zero => simp [ofInt_one]
  | succ k ih => rw [pow_succ, pow_succ, ih, ofInt_mul_ofInt]

private lemma exists_right_divisor_three_pow {v : HInt} {m k : ℕ}
    (hv : ¬ div3 v) (hm : (3 : ℤ) ^ m ∣ norm v) (_hk1 : 1 ≤ k) (hkm : k ≤ m) :
    ∃ g : HInt, (∃ u : HInt, v = u * g) ∧ norm g = (3 : ℤ) ^ k := by
  obtain ⟨g, u, c, s, t, hvg, hcg, hlin⟩ := rgcd v (ofInt (3 ^ k))
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg, mul_zero] at hcg
    have := congrArg HInt.a hcg
    simp only [ofInt_a, zero_a] at this
    have hpow : (3 : ℤ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    omega
  have hsu : s * u + t * c = 1 := by
    apply hmul_right_cancel hg0
    rw [add_mul, mul_assoc, ← hvg, mul_assoc, ← hcg, one_mul]
    exact hlin
  have hcgn : norm c * norm g = (3 : ℤ) ^ (2 * k) := by
    rw [← norm_mul, ← hcg, norm_ofInt, ← pow_mul]
    ring_nf
  have hgn_nn : 0 ≤ norm g := norm_nonneg g
  have hcn_nn : 0 ≤ norm c := norm_nonneg c
  have hdvd_nat : (norm g).toNat ∣ 3 ^ (2 * k) := by
    refine ⟨(norm c).toNat, ?_⟩
    zify
    rw [Int.toNat_of_nonneg hgn_nn, Int.toNat_of_nonneg hcn_nn]
    linarith
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd_nat
  have hgj : norm g = (3 : ℤ) ^ j := by
    have : ((norm g).toNat : ℤ) = ((3 ^ j : ℕ) : ℤ) := by exact_mod_cast hj
    rw [Int.toNat_of_nonneg hgn_nn] at this
    simpa using this
  by_cases hjk : j < k
  · have h3kj : (3 : ℤ) ^ k = (3 : ℤ) ^ (k - j) * (3 : ℤ) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt hjk)]
    have hc_eq : c = ofInt ((3 : ℤ) ^ (k - j)) * g.conj := by
      apply hmul_right_cancel (show g ≠ 0 from hg0)
      calc c * g = ofInt ((3 : ℤ) ^ k) := hcg.symm
      _ = ofInt ((3 : ℤ) ^ (k - j) * (3 : ℤ) ^ j) := by rw [h3kj]
      _ = ofInt ((3 : ℤ) ^ (k - j)) * ofInt (norm g) := by rw [ofInt_mul_ofInt, hgj]
      _ = ofInt ((3 : ℤ) ^ (k - j)) * (g.conj * g) := by rw [conj_mul g]
      _ = (ofInt ((3 : ℤ) ^ (k - j)) * g.conj) * g := by rw [mul_assoc]
    have hdivc : div3 c := by
      rw [hc_eq]
      have hkjs : k - j = (k - j - 1) + 1 := by omega
      rw [hkjs, pow_succ', ← ofInt_mul_ofInt, mul_assoc]
      exact (div3_iff_exists _).mpr ⟨ofInt ((3 : ℤ) ^ (k - j - 1)) * g.conj, rfl⟩
    have hdivtc : div3 (t * c) := div3_mul_left t c hdivc
    have hsu_eq : s * u = 1 - t * c := eq_sub_of_add_eq hsu
    have hnsu : ¬ (3 ∣ norm (s * u)) := by
      rw [hsu_eq]
      exact not_three_dvd_norm_one_sub_div3 (t * c) hdivtc
    have hun : (3 : ℤ) ^ (m - j) ∣ norm u := by
      have hvn : norm u * (3 : ℤ) ^ j = norm v := by rw [← hgj, ← norm_mul, ← hvg]
      obtain ⟨q, hq⟩ := hm
      have hmj : (3 : ℤ) ^ m = (3 : ℤ) ^ (m - j) * (3 : ℤ) ^ j := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      rw [hmj] at hq
      have hpos : (0 : ℤ) < (3 : ℤ) ^ j := by positivity
      refine ⟨q, ?_⟩
      nlinarith
    have h3u : 3 ∣ norm u := dvd_trans (dvd_pow_self 3 (by omega : m - j ≠ 0)) hun
    exact False.elim (hnsu (by rw [norm_mul]; exact dvd_mul_of_dvd_right h3u (norm s)))
  · by_cases hgt : k < j
    · have hcn : norm c = (3 : ℤ) ^ (2 * k - j) := by
        rw [hgj] at hcgn
        have h2kj : (3 : ℤ) ^ (2 * k) = (3 : ℤ) ^ (2 * k - j) * (3 : ℤ) ^ j := by
          rw [← pow_add, Nat.sub_add_cancel hjle]
        have hpos : (0 : ℤ) < (3 : ℤ) ^ j := by positivity
        nlinarith
      have hc0 : c ≠ 0 := by
        intro hc
        rw [hc, (norm_eq_zero_iff 0).mpr rfl] at hcn
        have hpos : (0 : ℤ) < (3 : ℤ) ^ (2 * k - j) := by positivity
        linarith
      have h2kj_lt : 2 * k - j < k := by omega
      have h3k_fac : (3 : ℤ) ^ k = (3 : ℤ) ^ (k - (2 * k - j)) * (3 : ℤ) ^ (2 * k - j) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      have hg_eq : ofInt ((3 : ℤ) ^ (2 * k - j)) * g =
          ofInt ((3 : ℤ) ^ (2 * k - j)) * (ofInt ((3 : ℤ) ^ (k - (2 * k - j))) * c.conj) := by
        calc
          ofInt ((3 : ℤ) ^ (2 * k - j)) * g = (c.conj * c) * g := by rw [conj_mul c, hcn]
          _ = c.conj * (c * g) := by rw [mul_assoc]
          _ = c.conj * ofInt ((3 : ℤ) ^ k) := by rw [← hcg]
          _ = ofInt ((3 : ℤ) ^ k) * c.conj := by rw [ofInt_mul_comm]
          _ = ofInt ((3 : ℤ) ^ (2 * k - j)) * (ofInt ((3 : ℤ) ^ (k - (2 * k - j))) * c.conj) := by
            rw [← mul_assoc, ofInt_mul_ofInt, mul_comm ((3 : ℤ) ^ (2 * k - j)), ← h3k_fac, ofInt_mul_comm]
      have hg_val : g = ofInt ((3 : ℤ) ^ (k - (2 * k - j))) * c.conj :=
        hmul_left_cancel (fun e => by
          have := congrArg HInt.a e
          simp only [ofInt_a, zero_a] at this
          have : (3 : ℤ) ^ (2 * k - j) ≠ 0 := pow_ne_zero _ (by norm_num)
          omega) hg_eq
      have hdivg : div3 g := by
        rw [hg_val]
        have hpos : k - (2 * k - j) = (k - (2 * k - j) - 1) + 1 := by omega
        rw [hpos, pow_succ', ← ofInt_mul_ofInt, mul_assoc]
        exact (div3_iff_exists _).mpr ⟨ofInt ((3 : ℤ) ^ (k - (2 * k - j) - 1)) * c.conj, rfl⟩
      exact False.elim (hv (by rw [hvg]; exact div3_mul_left u g hdivg))
    · have hjk_eq : j = k := by omega
      exact ⟨g, ⟨u, hvg⟩, by rw [hgj, hjk_eq]⟩

private lemma unique_right_divisor_three_pow {v g h : HInt} {k : ℕ}
    (hv : ¬ div3 v) (_hk1 : 1 ≤ k)
    (hg_div : ∃ u1 : HInt, v = u1 * g) (hgn : norm g = (3 : ℤ) ^ k)
    (hh_div : ∃ u2 : HInt, v = u2 * h) (hhn : norm h = (3 : ℤ) ^ k) :
    ∃ u : HInt, norm u = 1 ∧ g = u * h := by
  obtain ⟨g0, u0, c0, s0, t0, hvg0, hcg0, hlin0⟩ := rgcd v (ofInt (3 ^ k))
  have hg0_ne : g0 ≠ 0 := by
    intro e; rw [e, mul_zero] at hcg0
    have := congrArg HInt.a hcg0
    simp only [ofInt_a, zero_a] at this
    have : (3 : ℤ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    omega
  have h_all : ∀ x : HInt, (∃ u : HInt, v = u * x) → norm x = (3 : ℤ) ^ k →
      ∃ q : HInt, norm q = 1 ∧ g0 = q * x := by
    intro x ⟨ux, hux⟩ hxn
    have hx_ofInt : ofInt (3 ^ k) = x.conj * x := by rw [conj_mul, hxn]
    have hg0_eq : g0 = (s0 * ux + t0 * x.conj) * x := by
      calc g0 = s0 * v + t0 * ofInt (3 ^ k) := hlin0.symm
      _ = s0 * (ux * x) + t0 * (x.conj * x) := by rw [hux, hx_ofInt]
      _ = (s0 * ux + t0 * x.conj) * x := by rw [add_mul, mul_assoc, mul_assoc]
    set q := s0 * ux + t0 * x.conj
    have hgn0_le : norm g0 ∣ (3 : ℤ) ^ (2 * k) := by
      refine ⟨norm c0, ?_⟩
      rw [mul_comm (norm g0), ← norm_mul, ← hcg0, norm_ofInt, ← pow_mul, mul_comm k 2]
    have hq_norm : norm q * (3 : ℤ) ^ k = norm g0 := by
      rw [← hxn, ← norm_mul, ← hg0_eq]
    have hgn0_pos : 0 < norm g0 :=
      lt_of_le_of_ne (norm_nonneg g0) (Ne.symm fun e => hg0_ne ((norm_eq_zero_iff g0).mp e))
    have hq_nn : 0 ≤ norm q := norm_nonneg q
    have h3k_dvd : (3 : ℤ) ^ k ∣ norm g0 := ⟨norm q, by linarith⟩
    -- Either norm g0 = 3^k or norm g0 > 3^k; rule out > 3^k just as above
    have hgn0_nat : (norm g0).toNat ∣ 3 ^ (2 * k) := by
      obtain ⟨m0, hm0⟩ := hgn0_le
      refine ⟨m0.toNat, ?_⟩
      have h3pos : (0 : ℤ) < (3 : ℤ) ^ (2 * k) := by positivity
      have hm0_nn : 0 ≤ m0 := by nlinarith
      zify; rw [Int.toNat_of_nonneg (norm_nonneg g0), Int.toNat_of_nonneg hm0_nn]; exact hm0
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hgn0_nat
    have hgj : norm g0 = (3 : ℤ) ^ j := by
      have : ((norm g0).toNat : ℤ) = ((3 ^ j : ℕ) : ℤ) := by exact_mod_cast hj
      rw [Int.toNat_of_nonneg (norm_nonneg g0)] at this
      simpa using this
    have hj_ge : k ≤ j := by
      rw [hgj] at h3k_dvd
      by_contra hlt
      have h1 : j < k := not_le.mp hlt
      have : (3 : ℤ) ^ k ≤ (3 : ℤ) ^ j := Int.le_of_dvd (by positivity) h3k_dvd
      have : (3 : ℤ) ^ j < (3 : ℤ) ^ k := pow_lt_pow_right₀ (by norm_num) h1
      omega
    have hj_le : j ≤ k := by
      by_contra hgt
      have h1 : k < j := not_le.mp hgt
      have hcn : norm c0 = (3 : ℤ) ^ (2 * k - j) := by
        have hmulc : norm c0 * norm g0 = (3 : ℤ) ^ (2 * k) := by
          rw [← norm_mul, ← hcg0, norm_ofInt, ← pow_mul]; ring_nf
        rw [hgj] at hmulc
        have h2kj : (3 : ℤ) ^ (2 * k) = (3 : ℤ) ^ (2 * k - j) * (3 : ℤ) ^ j := by
          rw [← pow_add, Nat.sub_add_cancel hjle]
        have hpos : (0 : ℤ) < (3 : ℤ) ^ j := by positivity
        nlinarith
      have h3k_fac : (3 : ℤ) ^ k = (3 : ℤ) ^ (k - (2 * k - j)) * (3 : ℤ) ^ (2 * k - j) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      have hg_eq : ofInt ((3 : ℤ) ^ (2 * k - j)) * g0 =
          ofInt ((3 : ℤ) ^ (2 * k - j)) * (ofInt ((3 : ℤ) ^ (k - (2 * k - j))) * c0.conj) := by
        calc
          ofInt ((3 : ℤ) ^ (2 * k - j)) * g0 = (c0.conj * c0) * g0 := by rw [conj_mul c0, hcn]
          _ = c0.conj * (c0 * g0) := by rw [mul_assoc]
          _ = c0.conj * ofInt ((3 : ℤ) ^ k) := by rw [← hcg0]
          _ = ofInt ((3 : ℤ) ^ k) * c0.conj := by rw [ofInt_mul_comm]
          _ = ofInt ((3 : ℤ) ^ (2 * k - j)) * (ofInt ((3 : ℤ) ^ (k - (2 * k - j))) * c0.conj) := by
            rw [← mul_assoc, ofInt_mul_ofInt, mul_comm ((3 : ℤ) ^ (2 * k - j)), ← h3k_fac, ofInt_mul_comm]
      have hg_val : g0 = ofInt ((3 : ℤ) ^ (k - (2 * k - j))) * c0.conj :=
        hmul_left_cancel (fun e => by
          have := congrArg HInt.a e
          simp only [ofInt_a, zero_a] at this
          have : (3 : ℤ) ^ (2 * k - j) ≠ 0 := pow_ne_zero _ (by norm_num)
          omega) hg_eq
      have hdivg : div3 g0 := by
        rw [hg_val]
        have hpos : k - (2 * k - j) = (k - (2 * k - j) - 1) + 1 := by omega
        rw [hpos, pow_succ', ← ofInt_mul_ofInt, mul_assoc]
        exact (div3_iff_exists _).mpr ⟨ofInt ((3 : ℤ) ^ (k - (2 * k - j) - 1)) * c0.conj, rfl⟩
      exact hv (by rw [hvg0]; exact div3_mul_left u0 g0 hdivg)
    have hjk : j = k := by omega
    rw [hgj, hjk] at hq_norm
    have hpos : (0 : ℤ) < (3 : ℤ) ^ k := by positivity
    exact ⟨q, by nlinarith, hg0_eq⟩
  obtain ⟨q1, hq1n, hq1⟩ := h_all g hg_div hgn
  obtain ⟨q2, hq2n, hq2⟩ := h_all h hh_div hhn
  refine ⟨q1.conj * q2, ?_, ?_⟩
  · rw [norm_mul, norm_conj, hq1n, hq2n, mul_one]
  · have hg_eq : g = q1.conj * g0 := by rw [hq1, ← mul_assoc, conj_mul, hq1n, ofInt_one, one_mul]
    rw [hg_eq, hq2, ← mul_assoc]

-- ============================================================================
-- Section 3: Explicit units and norm-3 representatives S4
-- ============================================================================

private def mkEven (a b c d : ℤ) : HInt :=
  ⟨2 * a, 2 * b, 2 * c, 2 * d, ⟨a - b, by ring⟩, ⟨b - c, by ring⟩, ⟨c - d, by ring⟩⟩

private def mkOdd (a b c d : ℤ) : HInt :=
  ⟨2 * a + 1, 2 * b + 1, 2 * c + 1, 2 * d + 1,
    ⟨a - b, by ring⟩, ⟨b - c, by ring⟩, ⟨c - d, by ring⟩⟩

private def unitsList : List HInt :=
  [mkEven 1 0 0 0, mkEven (-1) 0 0 0,
   mkEven 0 1 0 0, mkEven 0 (-1) 0 0,
   mkEven 0 0 1 0, mkEven 0 0 (-1) 0,
   mkEven 0 0 0 1, mkEven 0 0 0 (-1),
   mkOdd 0 0 0 0, mkOdd 0 0 0 (-1),
   mkOdd 0 0 (-1) 0, mkOdd 0 0 (-1) (-1),
   mkOdd 0 (-1) 0 0, mkOdd 0 (-1) 0 (-1),
   mkOdd 0 (-1) (-1) 0, mkOdd 0 (-1) (-1) (-1),
   mkOdd (-1) 0 0 0, mkOdd (-1) 0 0 (-1),
   mkOdd (-1) 0 (-1) 0, mkOdd (-1) 0 (-1) (-1),
   mkOdd (-1) (-1) 0 0, mkOdd (-1) (-1) 0 (-1),
   mkOdd (-1) (-1) (-1) 0, mkOdd (-1) (-1) (-1) (-1)]

private def unitsFinset : Finset HInt := unitsList.toFinset

private lemma mem_unitsFinset_iff (u : HInt) : u ∈ unitsFinset ↔ norm u = 1 := by
  constructor
  · intro hu
    have hL : u ∈ unitsList := List.mem_toFinset.mp hu
    rcases (by simpa [unitsList] using hL :
      u = mkEven 1 0 0 0 ∨ u = mkEven (-1) 0 0 0 ∨
      u = mkEven 0 1 0 0 ∨ u = mkEven 0 (-1) 0 0 ∨
      u = mkEven 0 0 1 0 ∨ u = mkEven 0 0 (-1) 0 ∨
      u = mkEven 0 0 0 1 ∨ u = mkEven 0 0 0 (-1) ∨
      u = mkOdd 0 0 0 0 ∨ u = mkOdd 0 0 0 (-1) ∨
      u = mkOdd 0 0 (-1) 0 ∨ u = mkOdd 0 0 (-1) (-1) ∨
      u = mkOdd 0 (-1) 0 0 ∨ u = mkOdd 0 (-1) 0 (-1) ∨
      u = mkOdd 0 (-1) (-1) 0 ∨ u = mkOdd 0 (-1) (-1) (-1) ∨
      u = mkOdd (-1) 0 0 0 ∨ u = mkOdd (-1) 0 0 (-1) ∨
      u = mkOdd (-1) 0 (-1) 0 ∨ u = mkOdd (-1) 0 (-1) (-1) ∨
      u = mkOdd (-1) (-1) 0 0 ∨ u = mkOdd (-1) (-1) 0 (-1) ∨
      u = mkOdd (-1) (-1) (-1) 0 ∨ u = mkOdd (-1) (-1) (-1) (-1)) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [norm, norm4, mkEven, mkOdd]
  · intro hn
    have h4 : u.a ^ 2 + u.b ^ 2 + u.c ^ 2 + u.d ^ 2 = 4 := by
      linarith [four_mul_norm u, show norm4 u = u.a^2 + u.b^2 + u.c^2 + u.d^2 from rfl]
    have ha_b : -2 ≤ u.a ∧ u.a ≤ 2 := ⟨by nlinarith, by nlinarith⟩
    have hb_b : -2 ≤ u.b ∧ u.b ≤ 2 := ⟨by nlinarith, by nlinarith⟩
    have hc_b : -2 ≤ u.c ∧ u.c ≤ 2 := ⟨by nlinarith, by nlinarith⟩
    have hd_b : -2 ≤ u.d ∧ u.d ≤ 2 := ⟨by nlinarith, by nlinarith⟩
    obtain ⟨pa, pb, pc, hpa, hpb, hpc⟩ := hint_parity u
    unfold unitsFinset
    rw [List.mem_toFinset]
    by_cases heven : 2 ∣ u.d
    · obtain ⟨pd, hpd⟩ := heven
      have h4' : (pa + pd) ^ 2 + (pb + pd) ^ 2 + (pc + pd) ^ 2 + pd ^ 2 = 1 := by
        rw [hpa, hpb, hpc, hpd] at h4; linarith
      set x0 := pa + pd
      set x1 := pb + pd
      set x2 := pc + pd
      have h0b : -1 ≤ x0 ∧ x0 ≤ 1 := ⟨by nlinarith, by nlinarith⟩
      have h1b : -1 ≤ x1 ∧ x1 ≤ 1 := ⟨by nlinarith, by nlinarith⟩
      have h2b : -1 ≤ x2 ∧ x2 ≤ 1 := ⟨by nlinarith, by nlinarith⟩
      have h3b : -1 ≤ pd ∧ pd ≤ 1 := ⟨by nlinarith, by nlinarith⟩
      have heq : u = mkEven x0 x1 x2 pd := by
        apply HInt.ext <;> simp [mkEven, x0, x1, x2] <;> omega
      rw [heq]
      rcases (by omega : x0 = -1 ∨ x0 = 0 ∨ x0 = 1) with rx0 | rx0 | rx0 <;>
        rcases (by omega : x1 = -1 ∨ x1 = 0 ∨ x1 = 1) with rx1 | rx1 | rx1 <;>
        rcases (by omega : x2 = -1 ∨ x2 = 0 ∨ x2 = 1) with rx2 | rx2 | rx2 <;>
        rcases (by omega : pd = -1 ∨ pd = 0 ∨ pd = 1) with rpd | rpd | rpd
      all_goals
        simp only [rx0, rx1, rx2, rpd] at h4' ⊢
        first | decide | (exfalso; norm_num at h4')
    · have hodd_sq : ∀ z : ℤ, ¬ 2 ∣ z → 1 ≤ z ^ 2 := fun z hz => by
        have hnz : z ≤ -1 ∨ 1 ≤ z := by omega
        rcases hnz with h | h <;> nlinarith
      have h1 : 1 ≤ u.a ^ 2 := hodd_sq u.a (fun ⟨k, hk⟩ => heven ⟨k - pa, by omega⟩)
      have h2 : 1 ≤ u.b ^ 2 := hodd_sq u.b (fun ⟨k, hk⟩ => heven ⟨k - pb, by omega⟩)
      have h3 : 1 ≤ u.c ^ 2 := hodd_sq u.c (fun ⟨k, hk⟩ => heven ⟨k - pc, by omega⟩)
      have h4d : 1 ≤ u.d ^ 2 := hodd_sq u.d heven
      have hua1 : u.a = 1 ∨ u.a = -1 := by
        have : u.a ^ 2 = 1 := by linarith
        exact sq_eq_one_iff.mp this
      have hub1 : u.b = 1 ∨ u.b = -1 := by
        have : u.b ^ 2 = 1 := by linarith
        exact sq_eq_one_iff.mp this
      have huc1 : u.c = 1 ∨ u.c = -1 := by
        have : u.c ^ 2 = 1 := by linarith
        exact sq_eq_one_iff.mp this
      have hud1 : u.d = 1 ∨ u.d = -1 := by
        have : u.d ^ 2 = 1 := by linarith
        exact sq_eq_one_iff.mp this
      rcases hua1 with ra | ra <;> rcases hub1 with rb | rb <;>
        rcases huc1 with rc | rc <;> rcases hud1 with rd | rd <;>
        (have heq : u = mkOdd ((u.a - 1) / 2) ((u.b - 1) / 2) ((u.c - 1) / 2) ((u.d - 1) / 2) := by
          apply HInt.ext <;> simp [mkOdd, ra, rb, rc, rd]
         rw [heq]; simp [ra, rb, rc, rd]; decide)

private lemma unitsFinset_card : unitsFinset.card = 24 := by decide

private def p1 : HInt := mkEven 1 1 1 0
private def p2 : HInt := mkEven 1 1 (-1) 0
private def p3 : HInt := mkEven 1 (-1) 1 0
private def p4 : HInt := mkEven 1 (-1) (-1) 0

private def S4List : List HInt := [p1, p2, p3, p4]
private def S4 : Finset HInt := S4List.toFinset

private lemma S4_card : S4.card = 4 := by decide

private lemma S4_norm {p : HInt} (hp : p ∈ S4) : norm p = 3 := by
  have h : p = p1 ∨ p = p2 ∨ p = p3 ∨ p = p4 := by simpa [S4, S4List] using hp
  rcases h with rfl | rfl | rfl | rfl <;> simp [norm, norm4, p1, p2, p3, p4, mkEven]

private lemma S4_conj_mem {p : HInt} (hp : p ∈ S4) : p.conj ∈ S4 := by
  have h : p = p1 ∨ p = p2 ∨ p = p3 ∨ p = p4 := by simpa [S4, S4List] using hp
  rcases h with rfl | rfl | rfl | rfl
  · have : p1.conj = p4 := by apply HInt.ext <;> decide
    rw [this]; decide
  · have : p2.conj = p3 := by apply HInt.ext <;> decide
    rw [this]; decide
  · have : p3.conj = p2 := by apply HInt.ext <;> decide
    rw [this]; decide
  · have : p4.conj = p1 := by apply HInt.ext <;> decide
    rw [this]; decide

private lemma S4_div3_iff (p q : HInt) (hp : p ∈ S4) (hq : q ∈ S4) :
    div3 (p * q.conj) ↔ p = q := by
  have hp' : p = p1 ∨ p = p2 ∨ p = p3 ∨ p = p4 := by simpa [S4, S4List] using hp
  have hq' : q = p1 ∨ q = p2 ∨ q = p3 ∨ q = p4 := by simpa [S4, S4List] using hq
  rcases hp' with rfl | rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl | rfl <;> decide

private lemma norm_three_rep (g : HInt) (hg : norm g = 3) :
    ∃ u p : HInt, u ∈ unitsFinset ∧ p ∈ S4 ∧ g = u * p := by
  have hnot3 : ¬ div3 g := by
    intro hd
    have := nine_dvd_norm_of_div3 hd
    rw [hg] at this
    omega
  have h4 : g.a ^ 2 + g.b ^ 2 + g.c ^ 2 + g.d ^ 2 = 12 := by
    linarith [four_mul_norm g, show norm4 g = g.a^2 + g.b^2 + g.c^2 + g.d^2 from rfl]
  -- Actually let us check divisibility of 2 * (g * p.conj).* directly by cases on g.* % 3!
  have pick : ∃ p ∈ S4, div3 (g * p.conj) := by
    have ha3 : g.a % 3 = 0 ∨ g.a % 3 = 1 ∨ g.a % 3 = 2 := by omega
    have hb3 : g.b % 3 = 0 ∨ g.b % 3 = 1 ∨ g.b % 3 = 2 := by omega
    have hc3 : g.c % 3 = 0 ∨ g.c % 3 = 1 ∨ g.c % 3 = 2 := by omega
    have hd3 : g.d % 3 = 0 ∨ g.d % 3 = 1 ∨ g.d % 3 = 2 := by omega
    have hsq3 : 3 ∣ (g.a % 3) ^ 2 + (g.b % 3) ^ 2 + (g.c % 3) ^ 2 + (g.d % 3) ^ 2 := by
      have ha_e : g.a = 3 * (g.a / 3) + g.a % 3 := (Int.mul_ediv_add_emod g.a 3).symm
      have hb_e : g.b = 3 * (g.b / 3) + g.b % 3 := (Int.mul_ediv_add_emod g.b 3).symm
      have hc_e : g.c = 3 * (g.c / 3) + g.c % 3 := (Int.mul_ediv_add_emod g.c 3).symm
      have hd_e : g.d = 3 * (g.d / 3) + g.d % 3 := (Int.mul_ediv_add_emod g.d 3).symm
      have h12 : g.a ^ 2 + g.b ^ 2 + g.c ^ 2 + g.d ^ 2 =
          ((g.a % 3) ^ 2 + (g.b % 3) ^ 2 + (g.c % 3) ^ 2 + (g.d % 3) ^ 2) +
          3 * (2 * (g.a / 3) * (g.a % 3) + 3 * (g.a / 3) ^ 2 +
               2 * (g.b / 3) * (g.b % 3) + 3 * (g.b / 3) ^ 2 +
               2 * (g.c / 3) * (g.c % 3) + 3 * (g.c / 3) ^ 2 +
               2 * (g.d / 3) * (g.d % 3) + 3 * (g.d / 3) ^ 2) := by
        conv_lhs => rw [ha_e, hb_e, hc_e, hd_e]
        ring
      rw [h4] at h12
      exact ⟨4 - (2 * (g.a / 3) * (g.a % 3) + 3 * (g.a / 3) ^ 2 +
               2 * (g.b / 3) * (g.b % 3) + 3 * (g.b / 3) ^ 2 +
               2 * (g.c / 3) * (g.c % 3) + 3 * (g.c / 3) ^ 2 +
               2 * (g.d / 3) * (g.d % 3) + 3 * (g.d / 3) ^ 2), by linarith⟩
    have mod_mul_eq : ∀ (x : HInt) (p : HInt),
        (3 ∣ 2 * (x * p.conj).a ↔ 3 ∣ x.a * p.a + x.b * p.b + x.c * p.c + x.d * p.d) ∧
        (3 ∣ 2 * (x * p.conj).b ↔ 3 ∣ -x.a * p.b + x.b * p.a - x.c * p.d + x.d * p.c) ∧
        (3 ∣ 2 * (x * p.conj).c ↔ 3 ∣ -x.a * p.c + x.b * p.d + x.c * p.a - x.d * p.b) ∧
        (3 ∣ 2 * (x * p.conj).d ↔ 3 ∣ -x.a * p.d - x.b * p.c + x.c * p.b + x.d * p.a) := by
      intro x p
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show 2 * (x * p.conj).a = x.a * p.a + x.b * p.b + x.c * p.c + x.d * p.d by
          rw [two_mul_a]; simp only [conj_a, conj_b, conj_c, conj_d]; ring]
      · rw [show 2 * (x * p.conj).b = -x.a * p.b + x.b * p.a - x.c * p.d + x.d * p.c by
          rw [two_mul_b]; simp only [conj_a, conj_b, conj_c, conj_d]; ring]
      · rw [show 2 * (x * p.conj).c = -x.a * p.c + x.b * p.d + x.c * p.a - x.d * p.b by
          rw [two_mul_c]; simp only [conj_a, conj_b, conj_c, conj_d]; ring]
      · rw [show 2 * (x * p.conj).d = -x.a * p.d - x.b * p.c + x.c * p.b + x.d * p.a by
          rw [two_mul_d]; simp only [conj_a, conj_b, conj_c, conj_d]; ring]
    have dvd3_of_2 : ∀ z : ℤ, 3 ∣ 2 * z → 3 ∣ z := fun z hz => by omega
    have hdiv3_p : ∀ p : HInt,
        (3 ∣ g.a * p.a + g.b * p.b + g.c * p.c + g.d * p.d) →
        (3 ∣ -g.a * p.b + g.b * p.a - g.c * p.d + g.d * p.c) →
        (3 ∣ -g.a * p.c + g.b * p.d + g.c * p.a - g.d * p.b) →
        (3 ∣ -g.a * p.d - g.b * p.c + g.c * p.b + g.d * p.a) →
        div3 (g * p.conj) := by
      intro p h1 h2 h3 h4'
      have m := mod_mul_eq g p
      exact ⟨dvd3_of_2 _ (m.1.mpr h1), dvd3_of_2 _ (m.2.1.mpr h2),
             dvd3_of_2 _ (m.2.2.1.mpr h3), dvd3_of_2 _ (m.2.2.2.mpr h4')⟩
    have ha_e : g.a = 3 * (g.a / 3) + g.a % 3 := (Int.mul_ediv_add_emod g.a 3).symm
    have hb_e : g.b = 3 * (g.b / 3) + g.b % 3 := (Int.mul_ediv_add_emod g.b 3).symm
    have hc_e : g.c = 3 * (g.c / 3) + g.c % 3 := (Int.mul_ediv_add_emod g.c 3).symm
    have hd_e : g.d = 3 * (g.d / 3) + g.d % 3 := (Int.mul_ediv_add_emod g.d 3).symm
    rcases ha3 with ra | ra | ra <;> rcases hb3 with rb | rb | rb <;>
      rcases hc3 with rc | rc | rc <;> rcases hd3 with rd | rd | rd
    all_goals first
      | (exfalso; rw [ra, rb, rc, rd] at hsq3; omega)
      | (exfalso; apply hnot3; exact ⟨⟨g.a / 3, by omega⟩, ⟨g.b / 3, by omega⟩,
          ⟨g.c / 3, by omega⟩, ⟨g.d / 3, by omega⟩⟩)
      | (refine ⟨p1, by decide, hdiv3_p p1 ?_ ?_ ?_ ?_⟩ <;>
          simp only [p1, mkEven] <;> omega)
      | (refine ⟨p2, by decide, hdiv3_p p2 ?_ ?_ ?_ ?_⟩ <;>
          simp only [p2, mkEven] <;> omega)
      | (refine ⟨p3, by decide, hdiv3_p p3 ?_ ?_ ?_ ?_⟩ <;>
          simp only [p3, mkEven] <;> omega)
      | (refine ⟨p4, by decide, hdiv3_p p4 ?_ ?_ ?_ ?_⟩ <;>
          simp only [p4, mkEven] <;> omega)
  obtain ⟨p, hpS, hdiv⟩ := pick
  obtain ⟨u, hu⟩ := (div3_iff_exists _).mp hdiv
  have hun : norm u = 1 := by
    have h9 := congrArg norm hu
    rw [norm_mul, norm_conj, hg, S4_norm hpS, norm_mul, norm_ofInt] at h9
    linarith
  have hgp : g = u * p := by
    apply hmul_right_cancel (show ofInt 3 ≠ 0 from fun e => by
      have := congrArg HInt.a e; simp at this)
    calc g * ofInt 3 = g * (p.conj * p) := by rw [conj_mul, S4_norm hpS]
    _ = (g * p.conj) * p := by rw [mul_assoc]
    _ = (ofInt 3 * u) * p := by rw [hu]
    _ = u * (ofInt 3 * p) := by rw [ofInt_mul_comm, mul_assoc]
    _ = (u * p) * ofInt 3 := by rw [mul_assoc, ofInt_mul_comm 3 p, ← mul_assoc]
  exact ⟨u, p, (mem_unitsFinset_iff u).mpr hun, hpS, hgp⟩

-- ============================================================================
-- Section 4: Counting primitive Hurwitz integers PrimH k
-- ============================================================================

private noncomputable def ofTuple (t : ℤ × ℤ × ℤ × ℤ) : HInt :=
  if h : 2 ∣ t.1 - t.2.1 ∧ 2 ∣ t.2.1 - t.2.2.1 ∧ 2 ∣ t.2.2.1 - t.2.2.2 then
    ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, h.1, h.2.1, h.2.2⟩
  else 0

private noncomputable def boxH (B : ℤ) : Finset HInt :=
  (Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B).image ofTuple

private lemma mem_boxH {x : HInt} {B : ℤ} (hB : norm x ≤ B) : x ∈ boxH (2 * B + 1) := by
  have h4 := four_mul_norm x
  have hnn : 0 ≤ norm x := norm_nonneg x
  have hB0 : 0 ≤ B := le_trans hnn hB
  have hle_sq : norm4 x ≤ (2 * B + 1) ^ 2 := by nlinarith
  unfold norm4 at hle_sq
  have ha_sq : x.a ^ 2 ≤ (2 * B + 1) ^ 2 := by nlinarith [sq_nonneg x.b, sq_nonneg x.c, sq_nonneg x.d]
  have hb_sq : x.b ^ 2 ≤ (2 * B + 1) ^ 2 := by nlinarith [sq_nonneg x.a, sq_nonneg x.c, sq_nonneg x.d]
  have hc_sq : x.c ^ 2 ≤ (2 * B + 1) ^ 2 := by nlinarith [sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.d]
  have hd_sq : x.d ^ 2 ≤ (2 * B + 1) ^ 2 := by nlinarith [sq_nonneg x.a, sq_nonneg x.b, sq_nonneg x.c]
  have ha : -(2 * B + 1) ≤ x.a ∧ x.a ≤ 2 * B + 1 := ⟨by nlinarith, by nlinarith⟩
  have hb : -(2 * B + 1) ≤ x.b ∧ x.b ≤ 2 * B + 1 := ⟨by nlinarith, by nlinarith⟩
  have hc : -(2 * B + 1) ≤ x.c ∧ x.c ≤ 2 * B + 1 := ⟨by nlinarith, by nlinarith⟩
  have hd : -(2 * B + 1) ≤ x.d ∧ x.d ≤ 2 * B + 1 := ⟨by nlinarith, by nlinarith⟩
  rw [boxH, Finset.mem_image]
  refine ⟨(x.a, x.b, x.c, x.d), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨ha, hb, hc, hd⟩
  · simp only [ofTuple, dif_pos (⟨x.hab, x.hbc, x.hcd⟩ : 2 ∣ x.a - x.b ∧ 2 ∣ x.b - x.c ∧ 2 ∣ x.c - x.d)]

private noncomputable def PrimH (k : ℕ) : Finset HInt :=
  (boxH (2 * (3 : ℤ) ^ k + 1)).filter (fun x => norm x = (3 : ℤ) ^ k ∧ ¬ div3 x)

private lemma mem_PrimH {k : ℕ} {x : HInt} :
    x ∈ PrimH k ↔ norm x = (3 : ℤ) ^ k ∧ ¬ div3 x := by
  simp only [PrimH, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · rintro ⟨hn, hd⟩
    exact ⟨mem_boxH (le_of_eq hn), hn, hd⟩

private lemma PrimH_one_card : (PrimH 1).card = 96 := by
  have heq : PrimH 1 = (unitsFinset ×ˢ S4).image (fun p => p.1 * p.2) := by
    ext x
    rw [mem_PrimH, Finset.mem_image]
    constructor
    · rintro ⟨hn, _⟩
      obtain ⟨u, p, hu, hp, rfl⟩ := norm_three_rep x (by simpa using hn)
      exact ⟨(u, p), Finset.mem_product.mpr ⟨hu, hp⟩, rfl⟩
    · rintro ⟨⟨u, p⟩, hmem, rfl⟩
      rw [Finset.mem_product] at hmem
      have hun := (mem_unitsFinset_iff u).mp hmem.1
      have hpn := S4_norm hmem.2
      have hmn : norm (u * p) = (3 : ℤ) ^ 1 := by rw [norm_mul, hun, hpn]; ring
      refine ⟨hmn, fun hd => ?_⟩
      have h9 := nine_dvd_norm_of_div3 hd
      rw [hmn] at h9
      omega
  rw [heq, Finset.card_image_of_injOn]
  · rw [Finset.card_product, unitsFinset_card, S4_card]
  · rintro ⟨u1, p1'⟩ h1 ⟨u2, p2'⟩ h2 heq'
    simp only [Finset.mem_coe, Finset.mem_product] at h1 h2
    dsimp only at heq'
    have hmul3 : u1 * (p1' * p2'.conj) = ofInt 3 * u2 := by
      calc u1 * (p1' * p2'.conj) = (u1 * p1') * p2'.conj := by rw [mul_assoc]
      _ = (u2 * p2') * p2'.conj := by rw [heq']
      _ = u2 * (p2' * p2'.conj) := by rw [mul_assoc]
      _ = u2 * ofInt 3 := by rw [mul_conj, S4_norm h2.2]
      _ = ofInt 3 * u2 := by rw [ofInt_mul_comm]
    have hdiv3 : div3 (p1' * p2'.conj) := by
      have hu1_conj : u1.conj * u1 = 1 := by
        rw [conj_mul, (mem_unitsFinset_iff u1).mp h1.1, ofInt_one]
      have h2 : p1' * p2'.conj = ofInt 3 * (u1.conj * u2) := by
        calc p1' * p2'.conj = 1 * (p1' * p2'.conj) := by rw [one_mul]
        _ = (u1.conj * u1) * (p1' * p2'.conj) := by rw [hu1_conj]
        _ = u1.conj * (u1 * (p1' * p2'.conj)) := by rw [mul_assoc]
        _ = u1.conj * (ofInt 3 * u2) := by rw [hmul3]
        _ = ofInt 3 * (u1.conj * u2) := by rw [← mul_assoc, ← ofInt_mul_comm 3 u1.conj, mul_assoc]
      exact (div3_iff_exists _).mpr ⟨u1.conj * u2, h2⟩
    have hp_eq : p1' = p2' := (S4_div3_iff p1' p2' h1.2 h2.2).mp hdiv3
    subst hp_eq
    have hp_ne : p1' ≠ 0 := fun e => by
      have := S4_norm h1.2
      rw [e, (norm_eq_zero_iff 0).mpr rfl] at this
      omega
    have hu_eq : u1 = u2 := hmul_right_cancel hp_ne heq'
    exact Prod.ext hu_eq rfl

private lemma div3_mul_S4_iff {α p : HInt} (hp : p ∈ S4) :
    div3 (α * p) ↔ ∃ β : HInt, α = β * p.conj := by
  constructor
  · intro h
    obtain ⟨β, hβ⟩ := (div3_iff_exists _).mp h
    refine ⟨β, ?_⟩
    apply hmul_right_cancel (show ofInt 3 ≠ 0 from fun e => by
      have := congrArg HInt.a e; simp at this)
    calc α * ofInt 3 = α * (p * p.conj) := by rw [mul_conj, S4_norm hp]
    _ = (α * p) * p.conj := by rw [mul_assoc]
    _ = (ofInt 3 * β) * p.conj := by rw [hβ]
    _ = (β * p.conj) * ofInt 3 := by rw [ofInt_mul_comm, mul_assoc, ofInt_mul_comm, ← mul_assoc]
  · rintro ⟨β, rfl⟩
    rw [mul_assoc, conj_mul, S4_norm hp, ← ofInt_mul_comm]
    exact (div3_iff_exists _).mpr ⟨β, rfl⟩

private lemma PrimH_succ_card (k : ℕ) (hk : 1 ≤ k) :
    (PrimH (k + 1)).card = 3 * (PrimH k).card := by
  set extSet := (PrimH k ×ˢ S4).filter (fun z => ¬ div3 (z.1 * z.2))
  have himg : PrimH (k + 1) = extSet.image (fun z => z.1 * z.2) := by
    ext γ
    rw [mem_PrimH, Finset.mem_image]
    constructor
    · rintro ⟨hgn, hgdiv⟩
      have h3dvd : (3 : ℤ) ^ 1 ∣ norm γ := by
        rw [hgn, pow_one, pow_succ]
        exact ⟨(3 : ℤ) ^ k, by ring⟩
      obtain ⟨g, ⟨β, hβ⟩, hgn3⟩ := exists_right_divisor_three_pow hgdiv h3dvd (le_refl 1) (le_refl 1)
      obtain ⟨u, p, hu, hp, rfl⟩ := norm_three_rep g (by simpa using hgn3)
      refine ⟨(β * u, p), ?_, by rw [hβ, mul_assoc]⟩
      rw [Finset.mem_filter, Finset.mem_product, mem_PrimH]
      have hbu_norm : norm (β * u) = (3 : ℤ) ^ k := by
        have : norm (β * u) * 3 = (3 : ℤ) ^ (k + 1) := by
          calc norm (β * u) * 3 = norm (β * u) * norm p := by rw [S4_norm hp]
          _ = norm (β * u * p) := (norm_mul _ _).symm
          _ = norm γ := by rw [mul_assoc, ← hβ]
          _ = (3 : ℤ) ^ (k + 1) := hgn
        rw [pow_succ] at this
        linarith
      have hbu_div : ¬ div3 (β * u) := fun hd => by
        apply hgdiv
        rw [hβ, ← mul_assoc]
        exact div3_mul_right _ _ hd
      have hm_div : ¬ div3 ((β * u) * p) := by
        rwa [mul_assoc, ← hβ]
      exact ⟨⟨⟨hbu_norm, hbu_div⟩, hp⟩, hm_div⟩
    · rintro ⟨⟨α, p⟩, hmem, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product, mem_PrimH] at hmem
      have hnorm : norm (α * p) = (3 : ℤ) ^ (k + 1) := by
        rw [norm_mul, hmem.1.1.1, S4_norm hmem.1.2, pow_succ]
      exact ⟨hnorm, hmem.2⟩
  have hinj : Set.InjOn (fun z : HInt × HInt => z.1 * z.2) (extSet : Set (HInt × HInt)) := by
    rintro ⟨α1, p1'⟩ h1 ⟨α2, p2'⟩ h2 heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, mem_PrimH, extSet] at h1 h2
    dsimp only at heq
    set γ := α1 * p1'
    have hγ_div : ¬ div3 γ := h1.2
    obtain ⟨u, hun, hu_eq⟩ := unique_right_divisor_three_pow hγ_div (le_refl 1)
      ⟨α1, rfl⟩ (by simpa using S4_norm h1.1.2)
      ⟨α2, heq⟩ (by simpa using S4_norm h2.1.2)
    have hdiv_pq : div3 (p1' * p2'.conj) := by
      have : p1' * p2'.conj = ofInt 3 * (u * (1 : HInt)) := by
        rw [mul_one, hu_eq, mul_assoc, mul_conj p2', S4_norm h2.1.2, ofInt_mul_comm]
      exact (div3_iff_exists _).mpr ⟨u, by simpa using this⟩
    have hp_eq : p1' = p2' := (S4_div3_iff p1' p2' h1.1.2 h2.1.2).mp hdiv_pq
    subst hp_eq
    have hp_ne : p1' ≠ 0 := fun e => by
      have := S4_norm h1.1.2
      rw [e, (norm_eq_zero_iff 0).mpr rfl] at this
      omega
    exact Prod.ext (hmul_right_cancel hp_ne heq) rfl
  rw [himg, Finset.card_image_of_injOn hinj]
  -- Count extSet by fiber over PrimH k: each alpha in PrimH k has exactly 3 good p in S4
  have hsplit : extSet = (PrimH k).biUnion (fun α => (S4.filter (fun p => ¬ div3 (α * p))).map
      ⟨fun p => (α, p), fun a b h => (Prod.ext_iff.mp h).2⟩) := by
    ext ⟨α, p⟩
    simp only [extSet, Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hα, hp⟩, hnd⟩
      exact ⟨α, hα, p, ⟨hp, hnd⟩, rfl⟩
    · rintro ⟨α', hα', p', ⟨hp', hnd⟩, heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
      exact ⟨⟨hα', hp'⟩, hnd⟩
  rw [hsplit, Finset.card_biUnion]
  · have hfib : ∀ α ∈ PrimH k,
        ((S4.filter (fun p => ¬ div3 (α * p))).map
          ⟨fun p => (α, p), fun a b h => (Prod.ext_iff.mp h).2⟩).card = 3 := by
      intro α hα
      rw [Finset.card_map]
      rw [mem_PrimH] at hα
      have h3dvd : (3 : ℤ) ^ 1 ∣ norm α := by
        rw [hα.1, pow_one]
        exact dvd_pow_self 3 (by omega : k ≠ 0)
      obtain ⟨g, ⟨β, hβ⟩, hgn3⟩ := exists_right_divisor_three_pow hα.2 h3dvd (le_refl 1) (le_refl 1)
      obtain ⟨u, q, hu, hq, rfl⟩ := norm_three_rep g (by simpa using hgn3)
      have hq_conj_mem : q.conj ∈ S4 := S4_conj_mem hq
      have h_unique_bad : S4.filter (fun p => div3 (α * p)) = {q.conj} := by
        ext p
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hpS, hdivp⟩
          obtain ⟨β', hβ'⟩ := (div3_mul_S4_iff hpS).mp hdivp
          obtain ⟨w, hwn, hw_eq⟩ := unique_right_divisor_three_pow hα.2 (le_refl 1)
            ⟨β * u, by rw [hβ, mul_assoc]⟩ (by simpa using S4_norm hq)
            ⟨β', hβ'⟩ (by rw [norm_conj]; exact S4_norm hpS)
          have hdiv_qp : div3 (q * p) := by
            have : q * p = q * (p.conj).conj := by rw [conj_conj]
            rw [this, hw_eq, mul_assoc, mul_conj (p.conj), norm_conj, S4_norm hpS]
            rw [← ofInt_mul_comm]; exact (div3_iff_exists _).mpr ⟨w, rfl⟩
          have hqp_eq : q = p.conj := by
            rw [← conj_conj p] at hdiv_qp
            exact (S4_div3_iff q p.conj hq (S4_conj_mem hpS)).mp hdiv_qp
          have : p = q.conj := by rw [hqp_eq, conj_conj]
          exact this
        · rintro rfl
          refine ⟨hq_conj_mem, (div3_mul_S4_iff hq_conj_mem).mpr ⟨β * u, ?_⟩⟩
          rw [conj_conj, hβ, mul_assoc]
      have hcomp := Finset.card_filter_add_card_filter_not (s := S4) (p := fun p => div3 (α * p))
      rw [h_unique_bad, Finset.card_singleton, S4_card] at hcomp
      omega
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro α1 _ α2 _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_map] at h1 h2
    obtain ⟨_, _, he1⟩ := h1
    obtain ⟨_, _, he2⟩ := h2
    exact hne (((Prod.ext_iff.mp he1).1).trans ((Prod.ext_iff.mp he2).1).symm)

private lemma PrimH_card (k : ℕ) (hk : 1 ≤ k) : (PrimH k).card = 96 * 3 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using PrimH_one_card
  | succ k hk ih =>
    rw [PrimH_succ_card k hk, ih]
    rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ']
    ring

-- ============================================================================
-- Section 5: Mapping PrimH k to primitive integer vectors PrimVec k
-- ============================================================================

private noncomputable def AllVec (k : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(3 : ℤ) ^ k) ((3 : ℤ) ^ k) ×ˢ
   Finset.Icc (-(3 : ℤ) ^ k) ((3 : ℤ) ^ k) ×ˢ
   Finset.Icc (-(3 : ℤ) ^ k) ((3 : ℤ) ^ k)).filter
    (fun t => t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = (3 : ℤ) ^ (2 * k))

private noncomputable def PrimVec (k : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (AllVec k).filter (fun t => ¬ (3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2))

private lemma mem_AllVec {k : ℕ} {t : ℤ × ℤ × ℤ} :
    t ∈ AllVec k ↔ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = (3 : ℤ) ^ (2 * k) := by
  simp only [AllVec, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro heq
    have hsq : (3 : ℤ) ^ (2 * k) = ((3 : ℤ) ^ k) ^ 2 := by rw [← pow_mul]; ring_nf
    have hpos : (0 : ℤ) ≤ (3 : ℤ) ^ k := by positivity
    have heq' := heq
    rw [hsq] at heq'
    refine ⟨⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩,
      ⟨by nlinarith, by nlinarith⟩⟩, heq⟩

private lemma mem_PrimVec {k : ℕ} {t : ℤ × ℤ × ℤ} :
    t ∈ PrimVec k ↔ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = (3 : ℤ) ^ (2 * k) ∧
      ¬ (3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2) := by
  simp only [PrimVec, Finset.mem_filter, mem_AllVec]

private def HOfVec (t : ℤ × ℤ × ℤ) : HInt :=
  ⟨0, 2 * t.1, 2 * t.2.1, 2 * t.2.2,
    ⟨-t.1, by ring⟩, ⟨t.1 - t.2.1, by ring⟩, ⟨t.2.1 - t.2.2, by ring⟩⟩

private lemma HOfVec_norm (t : ℤ × ℤ × ℤ) :
    norm (HOfVec t) = t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 := by
  have h := four_mul_norm (HOfVec t)
  have h4 : norm4 (HOfVec t) = 4 * (t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2) := by
    dsimp [norm4, HOfVec]; ring
  rw [h4] at h
  linarith

private lemma HOfVec_conj (t : ℤ × ℤ × ℤ) : (HOfVec t).conj = -(HOfVec t) := by
  apply HInt.ext <;> simp [HOfVec]

private lemma HOfVec_div3 (t : ℤ × ℤ × ℤ) :
    div3 (HOfVec t) ↔ 3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2 := by
  simp only [div3, HOfVec, dvd_zero, true_and]
  omega

private lemma pure_img_of_a_zero (v : HInt) (ha : v.a = 0) :
    ∃ t : ℤ × ℤ × ℤ, v = HOfVec t := by
  obtain ⟨pa, pb, pc, hpa, hpb, hpc⟩ := hint_parity v
  have h2d : 2 ∣ v.d := ⟨-pa, by omega⟩
  have h2c : 2 ∣ v.c := by omega
  have h2b : 2 ∣ v.b := by omega
  refine ⟨(v.b / 2, v.c / 2, v.d / 2), ?_⟩
  apply HInt.ext <;> simp [HOfVec, ha] <;> omega

private def vecOfH (v : HInt) : ℤ × ℤ × ℤ := (v.b / 2, v.c / 2, v.d / 2)

private lemma vecOfH_HOfVec (t : ℤ × ℤ × ℤ) : vecOfH (HOfVec t) = t := by
  simp [vecOfH, HOfVec]

private lemma HOfVec_vecOfH {v : HInt} (ha : v.a = 0) : HOfVec (vecOfH v) = v := by
  obtain ⟨t, rfl⟩ := pure_img_of_a_zero v ha
  rw [vecOfH_HOfVec]

private def phi (α : HInt) : ℤ × ℤ × ℤ := vecOfH (α * hqi * α.conj)

private lemma phi_a_zero (α : HInt) : (α * hqi * α.conj).a = 0 := by
  have hconj : (α * hqi * α.conj).conj = -(α * hqi * α.conj) := by
    rw [conj_mul_eq, conj_mul_eq, conj_conj]
    have hqic : hqi.conj = -hqi := by apply HInt.ext <;> simp [hqi]
    rw [hqic]
    simp [mul_assoc]
  have ha := congrArg HInt.a hconj
  simp only [conj_a, neg_a] at ha
  omega

private lemma HOfVec_phi (α : HInt) : HOfVec (phi α) = α * hqi * α.conj :=
  HOfVec_vecOfH (phi_a_zero α)

private lemma sum_sq_div3 (u v : ℤ) (h : 3 ∣ u ^ 2 + v ^ 2) : 3 ∣ u ∧ 3 ∣ v := by
  have hu : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
  have hv : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
  have hmod : 3 ∣ (u % 3) ^ 2 + (v % 3) ^ 2 := by
    have hue : u = 3 * (u / 3) + u % 3 := (Int.mul_ediv_add_emod u 3).symm
    have hve : v = 3 * (v / 3) + v % 3 := (Int.mul_ediv_add_emod v 3).symm
    have h1 : u ^ 2 + v ^ 2 = (u % 3) ^ 2 + (v % 3) ^ 2 +
        3 * (2 * (u / 3) * (u % 3) + 3 * (u / 3) ^ 2 +
             2 * (v / 3) * (v % 3) + 3 * (v / 3) ^ 2) := by
      conv_lhs => rw [hue, hve]
      ring
    obtain ⟨m, hm⟩ := h
    exact ⟨m - (2 * (u / 3) * (u % 3) + 3 * (u / 3) ^ 2 +
             2 * (v / 3) * (v % 3) + 3 * (v / 3) ^ 2), by linarith⟩
  rcases hu with r1 | r1 | r1 <;> rcases hv with r2 | r2 | r2
  all_goals first
    | (rw [r1, r2] at hmod; omega)
    | exact ⟨Int.dvd_of_emod_eq_zero r1, Int.dvd_of_emod_eq_zero r2⟩

private lemma phi_coord1 (α : HInt) :
    4 * (phi α).1 = α.a ^ 2 + α.b ^ 2 - α.c ^ 2 - α.d ^ 2 := by
  have h1 := congrArg HInt.b (HOfVec_phi α)
  simp only [HOfVec, phi] at h1
  have h2 : 2 * (α * hqi * α.conj).b = 4 * (phi α).1 := by
    change 2 * (α * hqi * α.conj).b = 4 * ((α * hqi * α.conj).b / 2)
    have h4 : 2 * (HOfVec (phi α)).b = 2 * (α * hqi * α.conj).b := by rw [HOfVec_phi]
    simp only [HOfVec, phi] at h4
    omega
  have hexp : 4 * (α * hqi * α.conj).b = 2 * (α.a ^ 2 + α.b ^ 2 - α.c ^ 2 - α.d ^ 2) := by
    rw [show 4 * (α * hqi * α.conj).b = 2 * (2 * ((α * hqi) * α.conj).b) by ring, two_mul_b]
    simp only [mul_sub, mul_add, conj_a, conj_b, conj_c, conj_d]
    rw [show 2 * ((α * hqi).a * -α.b) = -(2 * (α * hqi).a) * α.b by ring, two_mul_a]
    rw [show 2 * ((α * hqi).b * α.a) = (2 * (α * hqi).b) * α.a by ring, two_mul_b]
    rw [show 2 * ((α * hqi).c * -α.d) = -(2 * (α * hqi).c) * α.d by ring, two_mul_c]
    rw [show 2 * ((α * hqi).d * -α.c) = -(2 * (α * hqi).d) * α.c by ring, two_mul_d]
    simp only [hqi]
    ring
  linarith

private lemma phi_mem_PrimVec {k : ℕ} (hk : 1 ≤ k) {α : HInt} (hα : α ∈ PrimH k) :
    phi α ∈ PrimVec k := by
  rw [mem_PrimH] at hα
  rw [mem_PrimVec]
  have hqn : norm hqi = 1 := by simp [norm, norm4, hqi]
  have hpn : norm (HOfVec (phi α)) = (3 : ℤ) ^ (2 * k) := by
    rw [HOfVec_phi, norm_mul, norm_mul, norm_conj, hqn, hα.1]
    rw [mul_one, ← pow_two, ← pow_mul]
    ring_nf
  rw [HOfVec_norm] at hpn
  refine ⟨hpn, fun ⟨hd1, _, _⟩ => hα.2 ?_⟩
  have h3n : 3 ∣ norm α := by
    rw [hα.1]
    exact dvd_pow_self 3 (by omega : k ≠ 0)
  have h4n := four_mul_norm α
  have hc1 := phi_coord1 α
  have hsum1 : 3 ∣ 2 * (α.a ^ 2 + α.b ^ 2) := by
    have : 2 * (α.a ^ 2 + α.b ^ 2) = 4 * norm α + 4 * (phi α).1 := by
      rw [h4n, norm4, hc1]; ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h3n 4) (dvd_mul_of_dvd_right hd1 4)
  have hsum2 : 3 ∣ 2 * (α.c ^ 2 + α.d ^ 2) := by
    have : 2 * (α.c ^ 2 + α.d ^ 2) = 4 * norm α - 4 * (phi α).1 := by
      rw [h4n, norm4, hc1]; ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right h3n 4) (dvd_mul_of_dvd_right hd1 4)
  have h1 := sum_sq_div3 α.a α.b (by omega)
  have h2 := sum_sq_div3 α.c α.d (by omega)
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

private lemma conj_unit_to_qi {u : HInt} (hun : norm u = 1) (hua : u.a = 0) :
    ∃ w : HInt, norm w = 1 ∧ w * hqi * w.conj = u := by
  have hu_mem := (mem_unitsFinset_iff u).mpr hun
  have hL : u ∈ unitsList := List.mem_toFinset.mp hu_mem
  rcases (by simpa [unitsList] using hL :
      u = mkEven 1 0 0 0 ∨ u = mkEven (-1) 0 0 0 ∨
      u = mkEven 0 1 0 0 ∨ u = mkEven 0 (-1) 0 0 ∨
      u = mkEven 0 0 1 0 ∨ u = mkEven 0 0 (-1) 0 ∨
      u = mkEven 0 0 0 1 ∨ u = mkEven 0 0 0 (-1) ∨
      u = mkOdd 0 0 0 0 ∨ u = mkOdd 0 0 0 (-1) ∨
      u = mkOdd 0 0 (-1) 0 ∨ u = mkOdd 0 0 (-1) (-1) ∨
      u = mkOdd 0 (-1) 0 0 ∨ u = mkOdd 0 (-1) 0 (-1) ∨
      u = mkOdd 0 (-1) (-1) 0 ∨ u = mkOdd 0 (-1) (-1) (-1) ∨
      u = mkOdd (-1) 0 0 0 ∨ u = mkOdd (-1) 0 0 (-1) ∨
      u = mkOdd (-1) 0 (-1) 0 ∨ u = mkOdd (-1) 0 (-1) (-1) ∨
      u = mkOdd (-1) (-1) 0 0 ∨ u = mkOdd (-1) (-1) 0 (-1) ∨
      u = mkOdd (-1) (-1) (-1) 0 ∨ u = mkOdd (-1) (-1) (-1) (-1)) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (try (exfalso; simp only [mkEven, mkOdd] at hua; omega))
  all_goals first
    | (refine ⟨1, by simp [norm, norm4]; try norm_num, ?_⟩; apply HInt.ext <;> decide)
    | (refine ⟨hqj, by simp [norm, norm4, hqj]; try norm_num, ?_⟩; apply HInt.ext <;> decide)
    | (refine ⟨mkOdd (-1) (-1) (-1) (-1), by simp [norm, norm4, mkOdd]; try norm_num, ?_⟩; apply HInt.ext <;> decide)
    | (refine ⟨mkOdd (-1) (-1) 0 0, by simp [norm, norm4, mkOdd]; try norm_num, ?_⟩; apply HInt.ext <;> decide)
    | (refine ⟨mkOdd (-1) (-1) 0 (-1), by simp [norm, norm4, mkOdd]; try norm_num, ?_⟩; apply HInt.ext <;> decide)
    | (refine ⟨mkOdd (-1) (-1) (-1) 0, by simp [norm, norm4, mkOdd]; try norm_num, ?_⟩; apply HInt.ext <;> decide)

private lemma phi_surj {k : ℕ} (hk : 1 ≤ k) {t : ℤ × ℤ × ℤ} (ht : t ∈ PrimVec k) :
    ∃ α ∈ PrimH k, phi α = t := by
  rw [mem_PrimVec] at ht
  set v := HOfVec t
  have hvn : norm v = (3 : ℤ) ^ (2 * k) := by rw [HOfVec_norm]; exact ht.1
  have hvdiv : ¬ div3 v := fun h => ht.2 ((HOfVec_div3 t).mp h)
  have h3kdvd : (3 : ℤ) ^ k ∣ norm v := by
    rw [hvn, two_mul, pow_add]; exact dvd_mul_right _ _
  obtain ⟨g, ⟨β, hβ⟩, hgn⟩ := exists_right_divisor_three_pow hvdiv h3kdvd hk (by omega)
  have hβn : norm β = (3 : ℤ) ^ k := by
    have hmuln : norm β * norm g = norm v := by rw [← norm_mul, ← hβ]
    rw [hgn, hvn, two_mul, pow_add] at hmuln
    have hpos : (0 : ℤ) < (3 : ℤ) ^ k := by positivity
    nlinarith
  have hvc : v.conj = -v := HOfVec_conj t
  have hβ_div : ∃ u2, v = u2 * β.conj := by
    refine ⟨-g.conj, ?_⟩
    have h1 := congrArg HInt.conj hβ
    rw [conj_mul_eq, hvc] at h1
    have h2 := congrArg Neg.neg h1
    simpa [neg_mul] using h2
  obtain ⟨w, hwn, hw_eq⟩ := unique_right_divisor_three_pow hvdiv hk
    ⟨β, hβ⟩ hgn hβ_div (by rw [norm_conj]; exact hβn)
  -- Wait: use g.conj as α, so β.conj = w * g means β = g.conj * w.conj
  set α := g.conj
  have hβ_eq : β = α * w := by
    have h1 : α = β * w.conj := by
      have := congrArg HInt.conj hw_eq
      rw [conj_mul_eq, conj_conj] at this
      exact this
    calc β = β * 1 := by rw [mul_one]
    _ = β * (w.conj * w) := by rw [conj_mul, hwn, ofInt_one]
    _ = (β * w.conj) * w := by rw [mul_assoc]
    _ = α * w := by rw [← h1]
  set u := w
  have hun : norm u = 1 := hwn
  have hv_eq : v = α * u * α.conj := by
    rw [hβ, hβ_eq]
    dsimp [α]
    rw [conj_conj]
  have hua : u.a = 0 := by
    have hmul_lr : α.conj * v * α = ofInt ((3 : ℤ) ^ (2 * k)) * u := by
      calc α.conj * v * α = (α.conj * α) * u * (α.conj * α) := by rw [hv_eq]; simp only [mul_assoc]
      _ = ofInt ((3 : ℤ) ^ k) * u * ofInt ((3 : ℤ) ^ k) := by rw [conj_mul α, norm_conj, hgn]
      _ = ofInt ((3 : ℤ) ^ k) * ofInt ((3 : ℤ) ^ k) * u := by rw [mul_assoc, ← ofInt_mul_comm ((3 : ℤ) ^ k) u, ← mul_assoc]
      _ = ofInt ((3 : ℤ) ^ (2 * k)) * u := by rw [ofInt_mul_ofInt, ← pow_add, ← two_mul]
    have hconj_lr : (α.conj * v * α).conj = -(α.conj * v * α) := by
      rw [conj_mul_eq, conj_mul_eq, conj_conj α, hvc]
      simp [mul_assoc]
    rw [hmul_lr] at hconj_lr
    have ha := congrArg HInt.a hconj_lr
    simp only [ofInt_mul, conj_a, neg_a] at ha
    have hpos : (0 : ℤ) < (3 : ℤ) ^ (2 * k) := by positivity
    nlinarith
  obtain ⟨w0, hw0n, hw0⟩ := conj_unit_to_qi hun hua
  refine ⟨α * w0, ?_, ?_⟩
  · rw [mem_PrimH]
    refine ⟨by rw [norm_mul, norm_conj, hgn, hw0n, mul_one], fun hd => ?_⟩
    apply hvdiv
    have hα_div : div3 α := by
      have : α = (α * w0) * w0.conj := by rw [mul_assoc, mul_conj, hw0n, ofInt_one, mul_one]
      rw [this]
      exact div3_mul_right _ _ hd
    have hg_div : div3 g := div3_conj.mp hα_div
    rw [hβ]
    exact div3_mul_left _ _ hg_div
  · rw [← vecOfH_HOfVec t, ← vecOfH_HOfVec (phi (α * w0))]
    congr 1
    rw [HOfVec_phi, conj_mul_eq]
    calc (α * w0) * hqi * (w0.conj * α.conj) = α * (w0 * hqi * w0.conj) * α.conj := by simp only [mul_assoc]
    _ = α * u * α.conj := by rw [hw0]
    _ = v := hv_eq.symm

private def stab4 : Finset HInt := {1, -1, hqi, -hqi}

private lemma stab4_card : stab4.card = 4 := by decide

private lemma stab4_mem_comm {w : HInt} :
    w ∈ stab4 ↔ norm w = 1 ∧ w * hqi = hqi * w := by
  constructor
  · intro hw
    have : w = 1 ∨ w = -1 ∨ w = hqi ∨ w = -hqi := by simpa [stab4] using hw
    rcases this with rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_⟩ <;>
      first | (simp [norm, norm4, hqi]) | (apply HInt.ext <;> decide)
  · rintro ⟨hwn, hcomm⟩
    have hwc : w.c = 0 ∧ w.d = 0 := by
      have hc := congrArg HInt.c hcomm
      have hd := congrArg HInt.d hcomm
      have h2c : 2 * (w * hqi).c = 2 * (hqi * w).c := by rw [hc]
      have h2d : 2 * (w * hqi).d = 2 * (hqi * w).d := by rw [hd]
      rw [two_mul_c, two_mul_c] at h2c
      rw [two_mul_d, two_mul_d] at h2d
      simp only [hqi] at h2c h2d
      omega
    have hw_mem := (mem_unitsFinset_iff w).mpr hwn
    have hL : w ∈ unitsList := List.mem_toFinset.mp hw_mem
    rcases (by simpa [unitsList] using hL :
      w = mkEven 1 0 0 0 ∨ w = mkEven (-1) 0 0 0 ∨
      w = mkEven 0 1 0 0 ∨ w = mkEven 0 (-1) 0 0 ∨
      w = mkEven 0 0 1 0 ∨ w = mkEven 0 0 (-1) 0 ∨
      w = mkEven 0 0 0 1 ∨ w = mkEven 0 0 0 (-1) ∨
      w = mkOdd 0 0 0 0 ∨ w = mkOdd 0 0 0 (-1) ∨
      w = mkOdd 0 0 (-1) 0 ∨ w = mkOdd 0 0 (-1) (-1) ∨
      w = mkOdd 0 (-1) 0 0 ∨ w = mkOdd 0 (-1) 0 (-1) ∨
      w = mkOdd 0 (-1) (-1) 0 ∨ w = mkOdd 0 (-1) (-1) (-1) ∨
      w = mkOdd (-1) 0 0 0 ∨ w = mkOdd (-1) 0 0 (-1) ∨
      w = mkOdd (-1) 0 (-1) 0 ∨ w = mkOdd (-1) 0 (-1) (-1) ∨
      w = mkOdd (-1) (-1) 0 0 ∨ w = mkOdd (-1) (-1) 0 (-1) ∨
      w = mkOdd (-1) (-1) (-1) 0 ∨ w = mkOdd (-1) (-1) (-1) (-1)) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (simp only [stab4, Finset.mem_insert, Finset.mem_singleton]; decide)
      | (exfalso; norm_num [mkEven, mkOdd] at hwc)

private lemma PrimVec_card (k : ℕ) (hk : 1 ≤ k) : (PrimVec k).card = 24 * 3 ^ (k - 1) := by
  have hmaps : ∀ α ∈ PrimH k, phi α ∈ PrimVec k := fun α hα => phi_mem_PrimVec hk hα
  have hfib_sum := Finset.card_eq_sum_card_fiberwise (f := phi) (s := PrimH k) (t := PrimVec k) hmaps
  have hfib_const : ∀ t ∈ PrimVec k, ((PrimH k).filter (fun α => phi α = t)).card = 4 := by
    intro t ht
    obtain ⟨α₀, hα₀, hphi₀⟩ := phi_surj hk ht
    have hα₀_prim := hα₀
    rw [mem_PrimH] at hα₀_prim
    have hα₀_ne : α₀ ≠ 0 := fun e => by
      have := hα₀_prim.1
      rw [e, (norm_eq_zero_iff 0).mpr rfl] at this
      have hpos : (0 : ℤ) < (3 : ℤ) ^ k := by positivity
      linarith
    have heq : (PrimH k).filter (fun α => phi α = t) = stab4.image (fun w => α₀ * w) := by
      ext α
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hα, hphi⟩
        rw [mem_PrimH] at hα
        set v := HOfVec t
        have hv_div : ¬ div3 v := fun hd => (mem_PrimVec.mp ht).2 ((HOfVec_div3 t).mp hd)
        have hv1 : v = (α₀ * hqi) * α₀.conj := by dsimp [v]; rw [← hphi₀, HOfVec_phi]
        have hv2 : v = (α * hqi) * α.conj := by dsimp [v]; rw [← hphi, HOfVec_phi]
        obtain ⟨u, hun, hu_eq⟩ := unique_right_divisor_three_pow hv_div hk
          ⟨α * hqi, hv2⟩ (by rw [norm_conj]; exact hα.1)
          ⟨α₀ * hqi, hv1⟩ (by rw [norm_conj]; exact hα₀_prim.1)
        set w := u.conj
        have hwn : norm w = 1 := by rw [norm_conj]; exact hun
        have hα_eq : α = α₀ * w := by
          have := congrArg HInt.conj hu_eq
          rw [conj_conj, conj_mul_eq, conj_conj] at this
          exact this
        have hcomm_conj : w * hqi * w.conj = hqi := by
          have hv_eq2 : α₀ * (w * hqi * w.conj) * α₀.conj = α₀ * hqi * α₀.conj := by
            calc α₀ * (w * hqi * w.conj) * α₀.conj
                = (α₀ * w) * hqi * (w.conj * α₀.conj) := by simp only [mul_assoc]
            _ = α * hqi * (α₀ * w).conj := by rw [conj_mul_eq, ← hα_eq]
            _ = α * hqi * α.conj := by rw [← hα_eq]
            _ = v := hv2.symm
            _ = α₀ * hqi * α₀.conj := hv1
          have hα₀c_ne : α₀.conj ≠ 0 := fun e => hα₀_ne (by rw [← conj_conj α₀, e]; apply HInt.ext <;> simp)
          have h1 := hmul_right_cancel hα₀c_ne hv_eq2
          exact hmul_left_cancel hα₀_ne h1
        have hcomm : w * hqi = hqi * w := by
          calc w * hqi = (w * hqi) * 1 := by rw [mul_one]
          _ = (w * hqi) * (w.conj * w) := by rw [conj_mul, hwn, ofInt_one]
          _ = (w * hqi * w.conj) * w := by simp only [mul_assoc]
          _ = hqi * w := by rw [hcomm_conj]
        exact ⟨w, stab4_mem_comm.mpr ⟨hwn, hcomm⟩, hα_eq.symm⟩
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨hwn, hcomm⟩ := stab4_mem_comm.mp hw
        refine ⟨mem_PrimH.mpr ⟨by rw [norm_mul, hα₀_prim.1, hwn, mul_one], fun hd => ?_⟩, ?_⟩
        · apply hα₀_prim.2
          have : α₀ = (α₀ * w) * w.conj := by rw [mul_assoc, mul_conj, hwn, ofInt_one, mul_one]
          rw [this]
          exact div3_mul_right _ _ hd
        · rw [← hphi₀, ← vecOfH_HOfVec (phi (α₀ * w)), ← vecOfH_HOfVec (phi α₀)]
          congr 1
          have h1 : HOfVec (phi (α₀ * w)) = HOfVec (phi α₀) := by
            rw [HOfVec_phi, HOfVec_phi, conj_mul_eq]
            calc (α₀ * w) * hqi * (w.conj * α₀.conj)
                = α₀ * (w * hqi * w.conj) * α₀.conj := by simp only [mul_assoc]
            _ = α₀ * (hqi * (w * w.conj)) * α₀.conj := by rw [hcomm, mul_assoc hqi w w.conj]
            _ = α₀ * hqi * α₀.conj := by rw [mul_conj, hwn, ofInt_one, mul_one]
          exact h1
    rw [heq, Finset.card_image_of_injOn]
    · exact stab4_card
    · intro w1 _ w2 _ h
      exact hmul_left_cancel hα₀_ne h
  rw [Finset.sum_congr rfl hfib_const, Finset.sum_const, smul_eq_mul, PrimH_card k hk] at hfib_sum
  omega

private lemma AllVec_zero_card : (AllVec 0).card = 6 := by
  have heq : AllVec 0 = ({(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)} :
      Finset (ℤ × ℤ × ℤ)) := by
    ext ⟨x, y, z⟩
    rw [mem_AllVec]
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, mul_zero, pow_zero]
    constructor
    · intro h
      have hx : -1 ≤ x ∧ x ≤ 1 := ⟨by nlinarith, by nlinarith⟩
      have hy : -1 ≤ y ∧ y ≤ 1 := ⟨by nlinarith, by nlinarith⟩
      have hz : -1 ≤ z ∧ z ≤ 1 := ⟨by nlinarith, by nlinarith⟩
      rcases (by omega : x = -1 ∨ x = 0 ∨ x = 1) with rfl | rfl | rfl <;>
        rcases (by omega : y = -1 ∨ y = 0 ∨ y = 1) with rfl | rfl | rfl <;>
        rcases (by omega : z = -1 ∨ z = 0 ∨ z = 1) with rfl | rfl | rfl <;>
        first | (norm_num at h; done) | decide
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num
  rw [heq]
  decide

private lemma AllVec_card (k : ℕ) : (AllVec k).card + 6 = 12 * 3 ^ k := by
  induction k with
  | zero => simp [AllVec_zero_card]
  | succ k ih =>
    have hsplit := Finset.card_filter_add_card_filter_not (s := AllVec (k + 1))
      (p := fun t => ¬ (3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2))
    have hdiv_eq : (AllVec (k + 1)).filter (fun t => ¬ ¬ (3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2)) =
        (AllVec k).image (fun t => (3 * t.1, 3 * t.2.1, 3 * t.2.2)) := by
      ext ⟨x, y, z⟩
      simp only [Finset.mem_filter, not_not, Finset.mem_image, mem_AllVec]
      constructor
      · rintro ⟨hsq, ⟨x', rfl⟩, ⟨y', rfl⟩, ⟨z', rfl⟩⟩
        refine ⟨(x', y', z'), ?_, rfl⟩
        have hpow : (3 : ℤ) ^ (2 * (k + 1)) = 9 * (3 : ℤ) ^ (2 * k) := by
          rw [mul_add, pow_add]; ring
        linarith
      · rintro ⟨⟨x', y', z'⟩, hsq, heq⟩
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        refine ⟨?_, ⟨x', rfl⟩, ⟨y', rfl⟩, ⟨z', rfl⟩⟩
        have hpow : (3 : ℤ) ^ (2 * (k + 1)) = 9 * (3 : ℤ) ^ (2 * k) := by
          rw [mul_add, pow_add]; ring
        linarith
    have hinj : Function.Injective (fun t : ℤ × ℤ × ℤ => (3 * t.1, 3 * t.2.1, 3 * t.2.2)) := by
      rintro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h
      simp only [Prod.mk.injEq] at h
      change 3 * a1 = 3 * a2 ∧ 3 * b1 = 3 * b2 ∧ 3 * c1 = 3 * c2 at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ : a1 = a2 ∧ b1 = b2 ∧ c1 = c2 := ⟨by omega, by omega, by omega⟩
      rfl
    have hcard_div : ((AllVec (k + 1)).filter (fun t => ¬ ¬ (3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2))).card =
        (AllVec k).card := by
      rw [hdiv_eq, Finset.card_image_of_injective _ hinj]
    have hprim_eq : (AllVec (k + 1)).filter (fun t => ¬ (3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2)) =
        PrimVec (k + 1) := rfl
    rw [hprim_eq, hcard_div, PrimVec_card (k + 1) (by omega)] at hsplit
    simp only [Nat.add_sub_cancel] at hsplit
    rw [← hsplit]
    have : 12 * 3 ^ (k + 1) = 24 * 3 ^ k + 12 * 3 ^ k := by rw [pow_succ]; ring
    omega

-- ============================================================================
-- Section 6: Counting positive solutions to 2*x^2 + z^2 = 3^(2k) via Z[sqrt(-2)]
-- ============================================================================

private structure Z2 where
  z : ℤ
  x : ℤ

private lemma Z2.ext {u v : Z2} (hz : u.z = v.z) (hx : u.x = v.x) : u = v := by
  cases u; cases v; simp_all

private instance : DecidableEq Z2 := fun u v =>
  if h : u.z = v.z ∧ u.x = v.x then isTrue (Z2.ext h.1 h.2)
  else isFalse fun e => h ⟨congrArg Z2.z e, congrArg Z2.x e⟩

private def Z2.norm (u : Z2) : ℤ := u.z ^ 2 + 2 * u.x ^ 2
private def Z2.one : Z2 := ⟨1, 0⟩
private def Z2.neg (u : Z2) : Z2 := ⟨-u.z, -u.x⟩
private def Z2.mul (u v : Z2) : Z2 := ⟨u.z * v.z - 2 * u.x * v.x, u.z * v.x + u.x * v.z⟩
private def Z2.pi : Z2 := ⟨1, 1⟩
private def Z2.piBar : Z2 := ⟨1, -1⟩

private def Z2.pow (u : Z2) : ℕ → Z2
  | 0 => Z2.one
  | m + 1 => Z2.mul (Z2.pow u m) u

private lemma Z2.norm_mul (u v : Z2) : (Z2.mul u v).norm = u.norm * v.norm := by
  simp only [Z2.norm, Z2.mul]
  ring

private lemma Z2.mul_neg_left (u v : Z2) : Z2.mul (Z2.neg u) v = Z2.neg (Z2.mul u v) := by
  apply Z2.ext <;> simp [Z2.neg, Z2.mul] <;> ring

private lemma Z2.mul_pi_piBar (u : Z2) :
    Z2.mul (Z2.mul u Z2.pi) Z2.piBar = ⟨3 * u.z, 3 * u.x⟩ := by
  apply Z2.ext <;> simp [Z2.mul, Z2.pi, Z2.piBar] <;> ring

private lemma Z2.mul_piBar_pi (u : Z2) :
    Z2.mul (Z2.mul u Z2.piBar) Z2.pi = ⟨3 * u.z, 3 * u.x⟩ := by
  apply Z2.ext <;> simp [Z2.mul, Z2.pi, Z2.piBar] <;> ring

private lemma three_dvd_sub_or_add (z x : ℤ) (h : 3 ∣ z ^ 2 + 2 * x ^ 2) :
    3 ∣ z - x ∨ 3 ∣ z + x := by
  have hz : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
  have hx : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  have hmod : 3 ∣ (z % 3) ^ 2 + 2 * (x % 3) ^ 2 := by
    have hze : z = 3 * (z / 3) + z % 3 := (Int.mul_ediv_add_emod z 3).symm
    have hxe : x = 3 * (x / 3) + x % 3 := (Int.mul_ediv_add_emod x 3).symm
    have h1 : z ^ 2 + 2 * x ^ 2 = (z % 3) ^ 2 + 2 * (x % 3) ^ 2 +
        3 * (2 * (z / 3) * (z % 3) + 3 * (z / 3) ^ 2 +
             4 * (x / 3) * (x % 3) + 6 * (x / 3) ^ 2) := by
      conv_lhs => rw [hze, hxe]
      ring
    obtain ⟨m, hm⟩ := h
    exact ⟨m - (2 * (z / 3) * (z % 3) + 3 * (z / 3) ^ 2 +
             4 * (x / 3) * (x % 3) + 6 * (x / 3) ^ 2), by linarith⟩
  rcases hz with r1 | r1 | r1 <;> rcases hx with r2 | r2 | r2
  all_goals first
    | (rw [r1, r2] at hmod; omega)
    | (left; omega)
    | (right; omega)

private lemma Z2.prim_pow_classification (m : ℕ) (hm : 1 ≤ m) :
    ∀ u : Z2, u.norm = (3 : ℤ) ^ m → ¬ (3 ∣ u.z ∧ 3 ∣ u.x) →
      u = Z2.pi.pow m ∨ u = Z2.neg (Z2.pi.pow m) ∨
      u = Z2.piBar.pow m ∨ u = Z2.neg (Z2.piBar.pow m) := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro u hun hnd
    simp only [Z2.norm, pow_one] at hun
    have hx : -1 ≤ u.x ∧ u.x ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    have hz : -2 ≤ u.z ∧ u.z ≤ 2 := ⟨by nlinarith, by nlinarith⟩
    rcases (by omega : u.x = -1 ∨ u.x = 0 ∨ u.x = 1) with hxv | hxv | hxv <;>
      rcases (by omega : u.z = -2 ∨ u.z = -1 ∨ u.z = 0 ∨ u.z = 1 ∨ u.z = 2) with hzv | hzv | hzv | hzv | hzv <;>
      simp only [hxv, hzv] at hun
    all_goals first
      | omega
      | (left; apply Z2.ext <;> (simp [Z2.pow, Z2.one, Z2.mul, Z2.pi, hzv, hxv]; done))
      | (right; left; apply Z2.ext <;> (simp [Z2.pow, Z2.one, Z2.mul, Z2.pi, Z2.neg, hzv, hxv]; done))
      | (right; right; left; apply Z2.ext <;> (simp [Z2.pow, Z2.one, Z2.mul, Z2.piBar, hzv, hxv]; done))
      | (right; right; right; apply Z2.ext <;> (simp [Z2.pow, Z2.one, Z2.mul, Z2.piBar, Z2.neg, hzv, hxv]; done))
  | succ m hm ih =>
    intro u hun hnd
    have h3dvd : 3 ∣ u.z ^ 2 + 2 * u.x ^ 2 := by
      rw [← Z2.norm.eq_def, hun, pow_succ]
      exact dvd_mul_left 3 _
    rcases three_dvd_sub_or_add u.z u.x h3dvd with hsub | hadd
    · set v : Z2 := ⟨(u.z + 2 * u.x) / 3, (u.x - u.z) / 3⟩
      have hv_mul : Z2.mul v Z2.pi = u := by
        have h1 : 3 ∣ u.z + 2 * u.x := by obtain ⟨k, hk⟩ := hsub; exact ⟨k + u.x, by linarith⟩
        have h2 : 3 ∣ u.x - u.z := by obtain ⟨k, hk⟩ := hsub; exact ⟨-k, by linarith⟩
        have e1 : 3 * v.z = u.z + 2 * u.x := Int.mul_ediv_cancel' h1
        have e2 : 3 * v.x = u.x - u.z := Int.mul_ediv_cancel' h2
        apply Z2.ext <;> dsimp [Z2.mul, Z2.pi] <;> omega
      have hvn : v.norm = (3 : ℤ) ^ m := by
        have hnm := Z2.norm_mul v Z2.pi
        rw [hv_mul, hun, pow_succ] at hnm
        have hpin : Z2.pi.norm = 3 := by simp [Z2.norm, Z2.pi]
        rw [hpin] at hnm
        linarith
      have hvnd : ¬ (3 ∣ v.z ∧ 3 ∣ v.x) := by
        rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        apply hnd
        rw [← hv_mul]
        simp only [Z2.mul, Z2.pi, ha, hb]
        exact ⟨⟨a - 2 * b, by ring⟩, ⟨a + b, by ring⟩⟩
      rcases ih v hvn hvnd with hv_eq | hv_eq | hv_eq | hv_eq
      · left; rw [← hv_mul, hv_eq]; rfl
      · right; left; rw [← hv_mul, hv_eq, Z2.mul_neg_left]; rfl
      · exfalso
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        rw [hv_eq, hk, Z2.pow, Z2.mul_piBar_pi] at hv_mul
        apply hnd
        rw [← hv_mul]
        exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
      · exfalso
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        rw [hv_eq, hk, Z2.pow, Z2.mul_neg_left, Z2.mul_piBar_pi] at hv_mul
        apply hnd
        rw [← hv_mul]
        simp only [Z2.neg]
        exact ⟨⟨-(Z2.piBar.pow k).z, by ring⟩, ⟨-(Z2.piBar.pow k).x, by ring⟩⟩
    · set v : Z2 := ⟨(u.z - 2 * u.x) / 3, (u.x + u.z) / 3⟩
      have hv_mul : Z2.mul v Z2.piBar = u := by
        have h1 : 3 ∣ u.z - 2 * u.x := by obtain ⟨k, hk⟩ := hadd; exact ⟨k - u.x, by linarith⟩
        have h2 : 3 ∣ u.x + u.z := by obtain ⟨k, hk⟩ := hadd; exact ⟨k, by linarith⟩
        have e1 : 3 * v.z = u.z - 2 * u.x := Int.mul_ediv_cancel' h1
        have e2 : 3 * v.x = u.x + u.z := Int.mul_ediv_cancel' h2
        apply Z2.ext <;> dsimp [Z2.mul, Z2.piBar] <;> omega
      have hvn : v.norm = (3 : ℤ) ^ m := by
        have hnm := Z2.norm_mul v Z2.piBar
        rw [hv_mul, hun, pow_succ] at hnm
        have hpin : Z2.piBar.norm = 3 := by simp [Z2.norm, Z2.piBar]
        rw [hpin] at hnm
        linarith
      have hvnd : ¬ (3 ∣ v.z ∧ 3 ∣ v.x) := by
        rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        apply hnd
        rw [← hv_mul]
        simp only [Z2.mul, Z2.piBar, ha, hb]
        exact ⟨⟨a + 2 * b, by ring⟩, ⟨b - a, by ring⟩⟩
      rcases ih v hvn hvnd with hv_eq | hv_eq | hv_eq | hv_eq
      · exfalso
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        rw [hv_eq, hk, Z2.pow, Z2.mul_pi_piBar] at hv_mul
        apply hnd
        rw [← hv_mul]
        exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
      · exfalso
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        rw [hv_eq, hk, Z2.pow, Z2.mul_neg_left, Z2.mul_pi_piBar] at hv_mul
        apply hnd
        rw [← hv_mul]
        simp only [Z2.neg]
        exact ⟨⟨-(Z2.pi.pow k).z, by ring⟩, ⟨-(Z2.pi.pow k).x, by ring⟩⟩
      · right; right; left; rw [← hv_mul, hv_eq]; rfl
      · right; right; right; rw [← hv_mul, hv_eq, Z2.mul_neg_left]; rfl

private lemma Z2.pi_pow_mod3 (m : ℕ) (hm : 1 ≤ m) :
    (Z2.pi.pow m).z % 3 = (Z2.pi.pow m).x % 3 ∧ (Z2.pi.pow m).z % 3 ≠ 0 := by
  induction m, hm using Nat.le_induction with
  | base => simp [Z2.pow, Z2.one, Z2.mul, Z2.pi]
  | succ m hm ih =>
    obtain ⟨h1, h2⟩ := ih
    have hz : (Z2.pi.pow (m + 1)).z = (Z2.pi.pow m).z - 2 * (Z2.pi.pow m).x := by
      change (Z2.pi.pow m).z * 1 - 2 * (Z2.pi.pow m).x * 1 = (Z2.pi.pow m).z - 2 * (Z2.pi.pow m).x
      ring
    have hx : (Z2.pi.pow (m + 1)).x = (Z2.pi.pow m).z + (Z2.pi.pow m).x := by
      change (Z2.pi.pow m).z * 1 + (Z2.pi.pow m).x * 1 = (Z2.pi.pow m).z + (Z2.pi.pow m).x
      ring
    rw [hz, hx]
    constructor <;> omega

private lemma Z2.pi_pow_norm (m : ℕ) : (Z2.pi.pow m).norm = (3 : ℤ) ^ m := by
  induction m with
  | zero => simp [Z2.pow, Z2.one, Z2.norm]
  | succ m ih =>
    rw [Z2.pow, Z2.norm_mul, ih, pow_succ]
    simp [Z2.norm, Z2.pi]

private lemma Z2.piBar_pow_eq (n : ℕ) :
    (Z2.piBar.pow n).z = (Z2.pi.pow n).z ∧ (Z2.piBar.pow n).x = -(Z2.pi.pow n).x := by
  induction n with
  | zero => simp [Z2.pow, Z2.one]
  | succ n ih =>
    rw [Z2.pow, Z2.pow, Z2.mul, Z2.mul, ih.1, ih.2]
    simp only [Z2.pi, Z2.piBar]
    exact ⟨by ring, by ring⟩

private lemma unique_prim_TwoSq (m : ℕ) (hm : 1 ≤ m) :
    ∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ¬ (3 ∣ p.1 ∧ 3 ∣ p.2) ∧
      2 * p.1 ^ 2 + p.2 ^ 2 = 3 ^ m := by
  set z0 := (Z2.pi.pow m).z
  set x0 := (Z2.pi.pow m).x
  have hmod := Z2.pi_pow_mod3 m hm
  have hz0_ne : z0 ≠ 0 := fun e => hmod.2 (by dsimp [z0] at e; rw [e]; norm_num)
  have hx0_ne : x0 ≠ 0 := fun e => hmod.2 (by dsimp [x0] at e; rw [e] at hmod; omega)
  have hnorm0 : z0 ^ 2 + 2 * x0 ^ 2 = (3 : ℤ) ^ m := Z2.pi_pow_norm m
  refine ⟨(x0.natAbs, z0.natAbs), ⟨Int.natAbs_pos.mpr hx0_ne, Int.natAbs_pos.mpr hz0_ne, ?_, ?_⟩, ?_⟩
  · rintro ⟨hd1, hd2⟩
    have : 3 ∣ z0 := Int.dvd_natAbs.mp (by exact_mod_cast hd2)
    omega
  · zify
    rw [sq_abs, sq_abs]
    linarith
  · rintro ⟨x, z⟩ ⟨hx, hz, hnd, heq⟩
    have hz_norm : (⟨(z : ℤ), (x : ℤ)⟩ : Z2).norm = (3 : ℤ) ^ m := by
      simp only [Z2.norm]
      zify at heq
      linarith
    have hndZ : ¬ (3 ∣ (z : ℤ) ∧ 3 ∣ (x : ℤ)) := fun ⟨h1, h2⟩ =>
      hnd ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
    rcases Z2.prim_pow_classification m hm ⟨z, x⟩ hz_norm hndZ with h | h | h | h
    · have hz_eq := congrArg Z2.z h
      have hx_eq := congrArg Z2.x h
      dsimp at hz_eq hx_eq
      have : z = z0.natAbs := by
        have : (z : ℤ) = z0 := hz_eq
        omega
      have : x = x0.natAbs := by
        have : (x : ℤ) = x0 := hx_eq
        omega
      exact Prod.ext ‹x = x0.natAbs› ‹z = z0.natAbs›
    · have hz_eq := congrArg Z2.z h
      have hx_eq := congrArg Z2.x h
      dsimp [Z2.neg] at hz_eq hx_eq
      have : z = z0.natAbs := by
        have : (z : ℤ) = -z0 := hz_eq
        omega
      have : x = x0.natAbs := by
        have : (x : ℤ) = -x0 := hx_eq
        omega
      exact Prod.ext ‹x = x0.natAbs› ‹z = z0.natAbs›
    · have hz_eq := congrArg Z2.z h
      have hx_eq := congrArg Z2.x h
      dsimp at hz_eq hx_eq
      rw [(Z2.piBar_pow_eq m).1] at hz_eq
      rw [(Z2.piBar_pow_eq m).2] at hx_eq
      have : z = z0.natAbs := by have : (z : ℤ) = z0 := hz_eq; omega
      have : x = x0.natAbs := by have : (x : ℤ) = -x0 := hx_eq; omega
      exact Prod.ext ‹x = x0.natAbs› ‹z = z0.natAbs›
    · have hz_eq := congrArg Z2.z h
      have hx_eq := congrArg Z2.x h
      dsimp [Z2.neg] at hz_eq hx_eq
      rw [(Z2.piBar_pow_eq m).1] at hz_eq
      rw [(Z2.piBar_pow_eq m).2, neg_neg] at hx_eq
      have : z = z0.natAbs := by have : (z : ℤ) = -z0 := hz_eq; omega
      have : x = x0.natAbs := by have : (x : ℤ) = x0 := hx_eq; omega
      exact Prod.ext ‹x = x0.natAbs› ‹z = z0.natAbs›

private def TwoSqPos (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 (3 ^ k) ×ˢ Finset.Icc 1 (3 ^ k)).filter
    (fun p => 2 * p.1 ^ 2 + p.2 ^ 2 = 3 ^ (2 * k))

private lemma mem_TwoSqPos {k : ℕ} {p : ℕ × ℕ} :
    p ∈ TwoSqPos k ↔ 0 < p.1 ∧ 0 < p.2 ∧ 2 * p.1 ^ 2 + p.2 ^ 2 = 3 ^ (2 * k) := by
  simp only [TwoSqPos, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun ⟨⟨⟨h1, _⟩, ⟨h2, _⟩⟩, heq⟩ => ⟨h1, h2, heq⟩
  · rintro ⟨h1, h2, heq⟩
    have hsq : 3 ^ (2 * k) = (3 ^ k) ^ 2 := by rw [← pow_mul]; ring_nf
    have h1le : p.1 ^ 2 ≤ (3 ^ k) ^ 2 := by nlinarith
    have h2le : p.2 ^ 2 ≤ (3 ^ k) ^ 2 := by nlinarith
    have hp1 : p.1 ≤ 3 ^ k := by
      by_contra hlt
      have : (3 ^ k) ^ 2 < p.1 ^ 2 := Nat.pow_lt_pow_left (not_le.mp hlt) (by norm_num)
      omega
    have hp2 : p.2 ≤ 3 ^ k := by
      by_contra hlt
      have : (3 ^ k) ^ 2 < p.2 ^ 2 := Nat.pow_lt_pow_left (not_le.mp hlt) (by norm_num)
      omega
    exact ⟨⟨⟨h1, hp1⟩, ⟨h2, hp2⟩⟩, heq⟩

private lemma twoSq_pow_decomp {x z k : ℕ} (hx : 0 < x) (hz : 0 < z)
    (heq : 2 * x ^ 2 + z ^ 2 = 3 ^ (2 * k)) :
    ∃ j < k, ∃ x' z' : ℕ, 0 < x' ∧ 0 < z' ∧ ¬ (3 ∣ x' ∧ 3 ∣ z') ∧
      2 * x' ^ 2 + z' ^ 2 = 3 ^ (2 * (k - j)) ∧ x = 3 ^ j * x' ∧ z = 3 ^ j * z' := by
  induction k generalizing x z with
  | zero =>
    simp only [mul_zero, pow_zero] at heq
    nlinarith
  | succ k ih =>
    by_cases hdiv : 3 ∣ x ∧ 3 ∣ z
    · obtain ⟨x1, rfl⟩ := hdiv.1
      obtain ⟨z1, rfl⟩ := hdiv.2
      have hheq : 2 * x1 ^ 2 + z1 ^ 2 = 3 ^ (2 * k) := by
        have hpow : 3 ^ (2 * (k + 1)) = 9 * 3 ^ (2 * k) := by rw [mul_add, pow_add]; ring
        linarith
      obtain ⟨j, hj, x', z', hx', hz', hnd, heq', rfl, rfl⟩ := ih (by omega) (by omega) hheq
      refine ⟨j + 1, by omega, x', z', hx', hz', hnd, ?_, ?_, ?_⟩
      · have : k + 1 - (j + 1) = k - j := by omega
        rw [this]; exact heq'
      · rw [pow_succ']; ring
      · rw [pow_succ']; ring
    · refine ⟨0, Nat.succ_pos k, x, z, hx, hz, hdiv, ?_, by simp, by simp⟩
      simpa using heq

private lemma TwoSqPos_card (k : ℕ) : (TwoSqPos k).card = k := by
  choose f hf_prop hf_uniq using fun j (hj : j ∈ Finset.range k) =>
    unique_prim_TwoSq (2 * (k - j)) (by rw [Finset.mem_range] at hj; omega)
  let g : (j : ℕ) → j ∈ Finset.range k → ℕ × ℕ := fun j hj =>
    (3 ^ j * (f j hj).1, 3 ^ j * (f j hj).2)
  have hbij : (Finset.range k).card = (TwoSqPos k).card := by
    refine Finset.card_bij g ?_ ?_ ?_
    · intro j hj
      have hj_lt : j < k := Finset.mem_range.mp hj
      obtain ⟨hx, hz, _, heq⟩ := hf_prop j hj
      rw [mem_TwoSqPos]
      refine ⟨mul_pos (by positivity) hx, mul_pos (by positivity) hz, ?_⟩
      dsimp [g]
      calc 2 * (3 ^ j * (f j hj).1) ^ 2 + (3 ^ j * (f j hj).2) ^ 2
          = 3 ^ (2 * j) * (2 * (f j hj).1 ^ 2 + (f j hj).2 ^ 2) := by
            rw [mul_pow, mul_pow, ← pow_mul, mul_comm j 2]; ring
      _ = 3 ^ (2 * j) * 3 ^ (2 * (k - j)) := by rw [heq]
      _ = 3 ^ (2 * j + 2 * (k - j)) := by rw [← pow_add]
      _ = 3 ^ (2 * k) := by rw [show 2 * j + 2 * (k - j) = 2 * k by omega]
    · intro j1 hj1 j2 hj2 heq
      dsimp [g] at heq
      obtain ⟨hx_eq, hz_eq⟩ := Prod.ext_iff.mp heq
      have hnot : ∀ a ha b hb, a < b →
          3 ^ a * (f a ha).1 = 3 ^ b * (f b hb).1 →
          3 ^ a * (f a ha).2 = 3 ^ b * (f b hb).2 → False := by
        intro a ha b hb hlt h1 h2
        have hba : b = a + (b - a) := by omega
        nth_rw 1 [hba] at h1
        nth_rw 1 [hba] at h2
        rw [pow_add, mul_assoc] at h1 h2
        have hpos : 0 < 3 ^ a := by positivity
        have hx1 : (f a ha).1 = 3 ^ (b - a) * (f b hb).1 := Nat.eq_of_mul_eq_mul_left hpos h1
        have hz1 : (f a ha).2 = 3 ^ (b - a) * (f b hb).2 := Nat.eq_of_mul_eq_mul_left hpos h2
        have h3a : 3 ∣ (f a ha).1 ∧ 3 ∣ (f a ha).2 := by
          rw [hx1, hz1]
          exact ⟨dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _,
                 dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _⟩
        exact (hf_prop a ha).2.2.1 h3a
      rcases lt_trichotomy j1 j2 with hlt | heq' | hgt
      · exact False.elim (hnot j1 hj1 j2 hj2 hlt hx_eq hz_eq)
      · exact heq'
      · exact False.elim (hnot j2 hj2 j1 hj1 hgt hx_eq.symm hz_eq.symm)
    · rintro ⟨x, z⟩ hp
      rw [mem_TwoSqPos] at hp
      obtain ⟨j, hj, x', z', hx', hz', hnd, heq', rfl, rfl⟩ :=
        twoSq_pow_decomp hp.1 hp.2.1 hp.2.2
      have hmem : j ∈ Finset.range k := Finset.mem_range.mpr hj
      refine ⟨j, hmem, ?_⟩
      have huniq := hf_uniq j hmem (x', z') ⟨hx', hz', hnd, heq'⟩
      dsimp [g]
      rw [← huniq]
  rw [← hbij, Finset.card_range]

-- ============================================================================
-- Section 7: Sign reduction, zero coordinates, equality patterns, final count
-- ============================================================================

private lemma two_sq_eq_pow_zero (k : ℕ) :
    ∀ x y : ℤ, x ^ 2 + y ^ 2 = (3 : ℤ) ^ (2 * k) → x = 0 ∨ y = 0 := by
  induction k with
  | zero =>
    intro x y h
    simp only [mul_zero, pow_zero] at h
    have hx : -1 ≤ x ∧ x ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    have hy : -1 ≤ y ∧ y ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    rcases (by omega : x = -1 ∨ x = 0 ∨ x = 1) with rfl | rfl | rfl <;>
      rcases (by omega : y = -1 ∨ y = 0 ∨ y = 1) with rfl | rfl | rfl <;>
      first | (norm_num at h; done) | decide
  | succ k ih =>
    intro x y h
    have h3 : 3 ∣ x ^ 2 + y ^ 2 := by
      rw [h, mul_add, pow_add]
      exact ⟨3 * (3 : ℤ) ^ (2 * k), by ring⟩
    obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩ := sum_sq_div3 x y h3
    have hpow : (3 : ℤ) ^ (2 * (k + 1)) = 9 * (3 : ℤ) ^ (2 * k) := by
      rw [mul_add, pow_add]; ring
    have h' : x' ^ 2 + y' ^ 2 = (3 : ℤ) ^ (2 * k) := by linarith
    rcases ih x' y' h' with rfl | rfl
    · left; ring
    · right; ring

private lemma noZeroVec_card (k : ℕ) :
    ((AllVec k).filter (fun t => t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0)).card + 12 = 12 * 3 ^ k := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := AllVec k)
    (p := fun t => t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0)
  set P := (3 : ℤ) ^ k
  have hP0 : P ≠ 0 := pow_ne_zero k (by norm_num)
  have hzero_set : (AllVec k).filter (fun t => ¬ (t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0)) =
      {(P, 0, 0), (-P, 0, 0), (0, P, 0), (0, -P, 0), (0, 0, P), (0, 0, -P)} := by
    ext ⟨x, y, z⟩
    simp only [Finset.mem_filter, mem_AllVec, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    have hsq : (3 : ℤ) ^ (2 * k) = P ^ 2 := by dsimp [P]; rw [← pow_mul]; ring_nf
    constructor
    · rintro ⟨heq, hnot⟩
      have h0 : x = 0 ∨ y = 0 ∨ z = 0 := by
        by_cases hx : x = 0; · exact Or.inl hx
        by_cases hy : y = 0; · exact Or.inr (Or.inl hy)
        by_cases hz : z = 0; · exact Or.inr (Or.inr hz)
        exact False.elim (hnot ⟨hx, hy, hz⟩)
      rcases h0 with rfl | rfl | rfl
      · simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add] at heq
        rcases two_sq_eq_pow_zero k y z heq with rfl | rfl
        · simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add] at heq; rw [hsq] at heq
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
        · simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at heq; rw [hsq] at heq
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
      · simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at heq
        rcases two_sq_eq_pow_zero k x z heq with rfl | rfl
        · simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add] at heq; rw [hsq] at heq
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
        · simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at heq; rw [hsq] at heq
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with rfl | rfl
          · exact Or.inl ⟨rfl, rfl, rfl⟩
          · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      · simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at heq
        rcases two_sq_eq_pow_zero k x y heq with rfl | rfl
        · simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add] at heq; rw [hsq] at heq
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
        · simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at heq; rw [hsq] at heq
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with rfl | rfl
          · exact Or.inl ⟨rfl, rfl, rfl⟩
          · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · exact ⟨by rw [hsq]; ring, fun h => h.2.1 rfl⟩
      · exact ⟨by rw [hsq]; ring, fun h => h.2.1 rfl⟩
      · exact ⟨by rw [hsq]; ring, fun h => h.1 rfl⟩
      · exact ⟨by rw [hsq]; ring, fun h => h.1 rfl⟩
      · exact ⟨by rw [hsq]; ring, fun h => h.1 rfl⟩
      · exact ⟨by rw [hsq]; ring, fun h => h.1 rfl⟩
  have hPneg : P ≠ -P := by omega
  have hzero_card : ((AllVec k).filter (fun t => ¬ (t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0))).card = 6 := by
    rw [hzero_set]
    rw [Finset.card_insert_of_notMem (by simp [Prod.mk.injEq, hP0, hPneg])]
    rw [Finset.card_insert_of_notMem (by simp [Prod.mk.injEq, hP0])]
    rw [Finset.card_insert_of_notMem (by simp [Prod.mk.injEq, hP0, hPneg])]
    rw [Finset.card_insert_of_notMem (by simp [Prod.mk.injEq, hP0])]
    rw [Finset.card_insert_of_notMem (by simp [Prod.mk.injEq]; omega)]
    rw [Finset.card_singleton]
  rw [hzero_card] at hsplit
  have hall := AllVec_card k
  omega

private def PosVec (k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 (3 ^ k) ×ˢ Finset.Icc 1 (3 ^ k) ×ˢ Finset.Icc 1 (3 ^ k)).filter
    (fun t => t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 3 ^ (2 * k))

private lemma mem_PosVec {k : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ PosVec k ↔ 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
      t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 3 ^ (2 * k) := by
  simp only [PosVec, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun ⟨⟨⟨h1, _⟩, ⟨h2, _⟩, ⟨h3, _⟩⟩, heq⟩ => ⟨h1, h2, h3, heq⟩
  · rintro ⟨h1, h2, h3, heq⟩
    have hsq : 3 ^ (2 * k) = (3 ^ k) ^ 2 := by rw [← pow_mul]; ring_nf
    have h1le : t.1 ≤ 3 ^ k := by
      by_contra hlt
      have : (3 ^ k) ^ 2 < t.1 ^ 2 := Nat.pow_lt_pow_left (not_le.mp hlt) (by norm_num)
      omega
    have h2le : t.2.1 ≤ 3 ^ k := by
      by_contra hlt
      have : (3 ^ k) ^ 2 < t.2.1 ^ 2 := Nat.pow_lt_pow_left (not_le.mp hlt) (by norm_num)
      omega
    have h3le : t.2.2 ≤ 3 ^ k := by
      by_contra hlt
      have : (3 ^ k) ^ 2 < t.2.2 ^ 2 := Nat.pow_lt_pow_left (not_le.mp hlt) (by norm_num)
      omega
    exact ⟨⟨⟨h1, h1le⟩, ⟨h2, h2le⟩, ⟨h3, h3le⟩⟩, heq⟩

private def signs8 : Finset (ℤ × ℤ × ℤ) :=
  {(1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1),
   (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1)}

private lemma signs8_card : signs8.card = 8 := by decide

private lemma PosVec_card (k : ℕ) : 2 * (PosVec k).card + 3 = 3 ^ (k + 1) := by
  set noZ := (AllVec k).filter (fun t => t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0)
  have heq : noZ = (PosVec k ×ˢ signs8).image
      (fun p => (p.2.1 * (p.1.1 : ℤ), p.2.2.1 * (p.1.2.1 : ℤ), p.2.2.2 * (p.1.2.2 : ℤ))) := by
    ext ⟨x, y, z⟩
    simp only [noZ, Finset.mem_filter, mem_AllVec, Finset.mem_image, Finset.mem_product,
      mem_PosVec]
    constructor
    · rintro ⟨hsq, hx, hy, hz⟩
      let sx : ℤ := if 0 < x then 1 else -1
      let sy : ℤ := if 0 < y then 1 else -1
      let sz : ℤ := if 0 < z then 1 else -1
      refine ⟨((x.natAbs, y.natAbs, z.natAbs), (sx, sy, sz)), ?_, ?_⟩
      · refine ⟨⟨Int.natAbs_pos.mpr hx, Int.natAbs_pos.mpr hy, Int.natAbs_pos.mpr hz, ?_⟩, ?_⟩
        · zify; rw [sq_abs, sq_abs, sq_abs]; exact hsq
        · have hs : ∀ u : ℤ, (if 0 < u then (1 : ℤ) else -1) = 1 ∨
              (if 0 < u then (1 : ℤ) else -1) = -1 := by intro u; split_ifs <;> simp
          rcases hs x with hx1 | hx1 <;> rcases hs y with hy1 | hy1 <;>
            rcases hs z with hz1 | hz1 <;> simp [sx, sy, sz, hx1, hy1, hz1] <;> decide
      · have hsgn : ∀ u : ℤ, (if 0 < u then (1 : ℤ) else -1) * (u.natAbs : ℤ) = u := by
          intro u; split_ifs with hu <;> omega
        exact Prod.ext (hsgn x) (Prod.ext (hsgn y) (hsgn z))
    · rintro ⟨⟨⟨a, b, c⟩, ⟨sx, sy, sz⟩⟩, ⟨⟨ha, hb, hc, hsq⟩, hs⟩, heq⟩
      try dsimp only at ha hb hc hsq heq
      change 0 < a at ha
      change 0 < b at hb
      change 0 < c at hc
      change a ^ 2 + b ^ 2 + c ^ 2 = 3 ^ (2 * k) at hsq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hs' : (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧ (sz = 1 ∨ sz = -1) := by
        have h : (sx, sy, sz) ∈ signs8 := hs
        simp only [signs8, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
      have hsqZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 = (3 : ℤ) ^ (2 * k) := by
        exact_mod_cast hsq
      rcases hs'.1 with rfl | rfl <;> rcases hs'.2.1 with rfl | rfl <;>
        rcases hs'.2.2 with rfl | rfl
      all_goals
        try dsimp only
        exact ⟨by simp only [one_mul, neg_mul, neg_sq]; exact hsqZ, by omega, by omega, by omega⟩
  have hinj : Set.InjOn
      (fun p : (ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ) =>
        (p.2.1 * (p.1.1 : ℤ), p.2.2.1 * (p.1.2.1 : ℤ), p.2.2.2 * (p.1.2.2 : ℤ)))
      ((PosVec k ×ˢ signs8 : Finset ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ))) :
        Set ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ))) := by
    rintro ⟨⟨a1, b1, c1⟩, ⟨sx1, sy1, sz1⟩⟩ h1 ⟨⟨a2, b2, c2⟩, ⟨sx2, sy2, sz2⟩⟩ h2 heq
    simp only [Finset.mem_coe, Finset.mem_product, mem_PosVec] at h1 h2
    have hcoord : ∀ s1 s2 : ℤ, (s1 = 1 ∨ s1 = -1) → (s2 = 1 ∨ s2 = -1) →
        ∀ u1 u2 : ℕ, 0 < u1 → 0 < u2 → s1 * (u1 : ℤ) = s2 * (u2 : ℤ) →
        s1 = s2 ∧ u1 = u2 := by
      intro s1 s2 hs1 hs2 u1 u2 hu1 hu2 heq'
      rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;> constructor <;> omega
    have hs1 : (sx1 = 1 ∨ sx1 = -1) ∧ (sy1 = 1 ∨ sy1 = -1) ∧ (sz1 = 1 ∨ sz1 = -1) := by
      have h : (sx1, sy1, sz1) ∈ signs8 := h1.2
      simp only [signs8, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
    have hs2 : (sx2 = 1 ∨ sx2 = -1) ∧ (sy2 = 1 ∨ sy2 = -1) ∧ (sz2 = 1 ∨ sz2 = -1) := by
      have h : (sx2, sy2, sz2) ∈ signs8 := h2.2
      simp only [signs8, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
    obtain ⟨e1, e2⟩ := Prod.ext_iff.mp heq
    obtain ⟨esx, ea⟩ := hcoord sx1 sx2 hs1.1 hs2.1 a1 a2 h1.1.1 h2.1.1 e1
    obtain ⟨esy, eb⟩ := hcoord sy1 sy2 hs1.2.1 hs2.2.1 b1 b2 h1.1.2.1 h2.1.2.1 (Prod.ext_iff.mp e2).1
    obtain ⟨esz, ec⟩ := hcoord sz1 sz2 hs1.2.2 hs2.2.2 c1 c2 h1.1.2.2.1 h2.1.2.2.1 (Prod.ext_iff.mp e2).2
    subst ea; subst eb; subst ec; subst esx; subst esy; subst esz; rfl
  have hnoZ := noZeroVec_card k
  have hcard : noZ.card = (PosVec k).card * 8 := by
    rw [heq, Finset.card_image_of_injOn hinj]
    rw [Finset.card_product, signs8_card]
  have hpow : 12 * 3 ^ k = 4 * 3 ^ (k + 1) := by rw [pow_succ]; ring
  rw [hpow] at hnoZ
  rw [hcard] at hnoZ
  omega

private lemma not_three_mul_sq_eq_pow (k x : ℕ) : 3 * x ^ 2 ≠ 3 ^ (2 * k) := by
  induction k generalizing x with
  | zero =>
    simp only [mul_zero, pow_zero]
    intro h
    rcases (by omega : x = 0 ∨ 1 ≤ x) with rfl | hx <;> nlinarith
  | succ k ih =>
    intro h
    have hpow : 3 ^ (2 * (k + 1)) = 9 * 3 ^ (2 * k) := by rw [mul_add, pow_add]; ring
    rw [hpow] at h
    have h3x2 : 3 ∣ x ^ 2 := ⟨3 ^ (2 * k), by linarith⟩
    have h3x : 3 ∣ x := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3x2
    obtain ⟨y, rfl⟩ := h3x
    have h' : 3 * y ^ 2 = 3 ^ (2 * k) := by linarith
    exact ih y h'

private def repsFinset (k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (PosVec k).filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)

private lemma coe_repsFinset (k : ℕ) :
    (repsFinset k : Set (ℕ × ℕ × ℕ)) = OMA.S_oeis_a047926.reps (3 ^ (2 * k)) := by
  ext t
  simp only [Finset.mem_coe, repsFinset, Finset.mem_filter, mem_PosVec, OMA.S_oeis_a047926.reps,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2, h3, hsq⟩, h12, h23⟩
    exact ⟨h1, h12, h23, hsq⟩
  · rintro ⟨h1, h12, h23, hsq⟩
    exact ⟨⟨h1, by omega, by omega, hsq⟩, h12, h23⟩

private def perm6 (i : Fin 6) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  match i with
  | ⟨0, _⟩ => (t.1, t.2.1, t.2.2)
  | ⟨1, _⟩ => (t.1, t.2.2, t.2.1)
  | ⟨2, _⟩ => (t.2.1, t.1, t.2.2)
  | ⟨3, _⟩ => (t.2.1, t.2.2, t.1)
  | ⟨4, _⟩ => (t.2.2, t.1, t.2.1)
  | ⟨5, _⟩ => (t.2.2, t.2.1, t.1)

private lemma repsFinset_card_rel (k : ℕ) :
    12 * (repsFinset k).card + 3 = 3 ^ (k + 1) + 6 * k := by
  set TwoEq := (PosVec k).filter (fun t => t.1 = t.2.1 ∨ t.2.1 = t.2.2 ∨ t.1 = t.2.2)
  set ThreeDist := (PosVec k).filter (fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)
  have hpos_split : TwoEq.card + ThreeDist.card = (PosVec k).card := by
    have h := Finset.card_filter_add_card_filter_not (s := PosVec k)
      (p := fun t => t.1 = t.2.1 ∨ t.2.1 = t.2.2 ∨ t.1 = t.2.2)
    have hnot : (PosVec k).filter (fun t => ¬ (t.1 = t.2.1 ∨ t.2.1 = t.2.2 ∨ t.1 = t.2.2)) =
        ThreeDist := by
      ext t; simp only [Finset.mem_filter, ThreeDist]; tauto
    rw [hnot] at h
    exact h
  have hno_all_eq : ∀ t ∈ PosVec k, ¬ (t.1 = t.2.1 ∧ t.2.1 = t.2.2) := by
    rintro ⟨x, y, z⟩ ht ⟨hxy, hyz⟩
    dsimp at hxy hyz
    subst hxy; subst hyz
    rw [mem_PosVec] at ht
    exact not_three_mul_sq_eq_pow k x (by linarith [ht.2.2.2])
  -- Count TwoEq = 3 * k via three disjoint copies of TwoSqPos k
  set E12 := (PosVec k).filter (fun t => t.1 = t.2.1)
  set E23 := (PosVec k).filter (fun t => t.2.1 = t.2.2)
  set E13 := (PosVec k).filter (fun t => t.1 = t.2.2)
  have hE12_card : E12.card = k := by
    have heq : E12 = (TwoSqPos k).image (fun p => (p.1, p.1, p.2)) := by
      ext ⟨x, y, z⟩
      simp only [E12, Finset.mem_filter, mem_PosVec, Finset.mem_image, mem_TwoSqPos,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hx, hy, hz, hsq⟩, he⟩
        subst he
        exact ⟨(x, z), ⟨hx, hz, by linarith⟩, rfl, rfl, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb, hsq⟩, rfl, rfl, rfl⟩
        exact ⟨⟨ha, ha, hb, by linarith⟩, rfl⟩
    rw [heq, Finset.card_image_of_injective _ (fun ⟨a1, b1⟩ ⟨a2, b2⟩ h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.2), TwoSqPos_card k]
  have hE23_card : E23.card = k := by
    have heq : E23 = (TwoSqPos k).image (fun p => (p.2, p.1, p.1)) := by
      ext ⟨x, y, z⟩
      simp only [E23, Finset.mem_filter, mem_PosVec, Finset.mem_image, mem_TwoSqPos,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hx, hy, hz, hsq⟩, he⟩
        subst he
        exact ⟨(y, x), ⟨hy, hx, by linarith⟩, rfl, rfl, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb, hsq⟩, rfl, rfl, rfl⟩
        exact ⟨⟨hb, ha, ha, by linarith⟩, rfl⟩
    rw [heq, Finset.card_image_of_injective _ (fun ⟨a1, b1⟩ ⟨a2, b2⟩ h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.1), TwoSqPos_card k]
  have hE13_card : E13.card = k := by
    have heq : E13 = (TwoSqPos k).image (fun p => (p.1, p.2, p.1)) := by
      ext ⟨x, y, z⟩
      simp only [E13, Finset.mem_filter, mem_PosVec, Finset.mem_image, mem_TwoSqPos,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hx, hy, hz, hsq⟩, he⟩
        subst he
        exact ⟨(x, y), ⟨hx, hy, by linarith⟩, rfl, rfl, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb, hsq⟩, rfl, rfl, rfl⟩
        exact ⟨⟨ha, hb, ha, by linarith⟩, rfl⟩
    rw [heq, Finset.card_image_of_injective _ (fun ⟨a1, b1⟩ ⟨a2, b2⟩ h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.1), TwoSqPos_card k]
  have hTwoEq_union : TwoEq = E12 ∪ E23 ∪ E13 := by
    ext t; simp only [TwoEq, E12, E23, E13, Finset.mem_union, Finset.mem_filter]; tauto
  have hdisj12 : Disjoint E12 E23 := Finset.disjoint_left.mpr fun t h1 h2 => by
    simp only [E12, E23, Finset.mem_filter] at h1 h2
    exact hno_all_eq t h1.1 ⟨h1.2, h2.2⟩
  have hdisj13 : Disjoint (E12 ∪ E23) E13 := Finset.disjoint_left.mpr fun t h1 h2 => by
    simp only [E12, E23, E13, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with ⟨ht, h12⟩ | ⟨ht, h23⟩
    · exact hno_all_eq t ht ⟨h12, by omega⟩
    · exact hno_all_eq t ht ⟨by omega, h23⟩
  have hTwoEq_card : TwoEq.card = 3 * k := by
    rw [hTwoEq_union, Finset.card_union_of_disjoint hdisj13,
      Finset.card_union_of_disjoint hdisj12, hE12_card, hE23_card, hE13_card]
    ring
  -- Split repsFinset k into TwoEq part (card k) and ThreeDist part
  set repsTwo := (repsFinset k).filter (fun t => t.1 = t.2.1 ∨ t.2.1 = t.2.2)
  set repsThree := (repsFinset k).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
  have hreps_split : repsTwo.card + repsThree.card = (repsFinset k).card := by
    have h := Finset.card_filter_add_card_filter_not (s := repsFinset k)
      (p := fun t => t.1 = t.2.1 ∨ t.2.1 = t.2.2)
    have hnot : (repsFinset k).filter (fun t => ¬ (t.1 = t.2.1 ∨ t.2.1 = t.2.2)) = repsThree := by
      ext ⟨x, y, z⟩
      simp only [Finset.mem_filter, repsFinset, repsThree]
      constructor
      · rintro ⟨⟨hm, h12, h23⟩, hne⟩; exact ⟨⟨hm, h12, h23⟩, by omega, by omega⟩
      · rintro ⟨hm, h12, h23⟩; exact ⟨hm, by omega⟩
    rw [hnot] at h
    exact h
  have hrepsTwo_card : repsTwo.card = k := by
    have heq : repsTwo = (TwoSqPos k).image (fun p => if p.1 < p.2 then (p.1, p.1, p.2) else (p.2, p.1, p.1)) := by
      ext ⟨x, y, z⟩
      simp only [repsTwo, Finset.mem_filter, repsFinset, mem_PosVec, Finset.mem_image,
        mem_TwoSqPos]
      constructor
      · rintro ⟨⟨⟨hx, hy, hz, hsq⟩, hxy, hyz⟩, hEq⟩
        have hne : ¬ (x = y ∧ y = z) := fun ⟨e1, e2⟩ =>
          not_three_mul_sq_eq_pow k x (by subst e1; subst e2; linarith)
        rcases hEq with rfl | rfl
        · have hxz : x < z := by omega
          refine ⟨(x, z), ⟨hx, hz, by linarith⟩, by simp [hxz]⟩
        · have hxy' : x < y := by omega
          have hnot : ¬ (y < x) := by omega
          refine ⟨(y, x), ⟨hy, hx, by linarith⟩, by simp [hnot]⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb, hsq⟩, hite⟩
        have hne : a ≠ b := fun e => by
          subst e; exact not_three_mul_sq_eq_pow k a (by linarith)
        dsimp only at hite
        split_ifs at hite with hab
        · simp only [Prod.mk.injEq] at hite
          obtain ⟨rfl, rfl, rfl⟩ := hite
          exact ⟨⟨⟨ha, ha, hb, by linarith⟩, le_refl _, le_of_lt hab⟩, Or.inl rfl⟩
        · simp only [Prod.mk.injEq] at hite
          obtain ⟨rfl, rfl, rfl⟩ := hite
          have hba : b < a := by omega
          exact ⟨⟨⟨hb, ha, ha, by linarith⟩, le_of_lt hba, le_refl _⟩, Or.inr rfl⟩
    have hinj : Set.InjOn
        (fun p : ℕ × ℕ => if p.1 < p.2 then (p.1, p.1, p.2) else (p.2, p.1, p.1))
        (TwoSqPos k : Set (ℕ × ℕ)) := by
      rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
      simp only [Finset.mem_coe, mem_TwoSqPos] at h1 h2
      have hne1 : a1 ≠ b1 := fun e => not_three_mul_sq_eq_pow k a1 (by subst e; linarith [h1.2.2])
      have hne2 : a2 ≠ b2 := fun e => not_three_mul_sq_eq_pow k a2 (by subst e; linarith [h2.2.2])
      dsimp only at heq
      split_ifs at heq with ha1 ha2 <;> simp only [Prod.mk.injEq] at heq
      · exact Prod.ext heq.1 heq.2.2
      · exfalso; obtain ⟨e1, e2, e3⟩ := heq; omega
      · exfalso; obtain ⟨e1, e2, e3⟩ := heq; omega
      · exact Prod.ext heq.2.1 heq.1
    rw [heq, Finset.card_image_of_injOn hinj, TwoSqPos_card k]
  -- Bijection Fin 6 x repsThree -> ThreeDist
  have hThreeDist_card : ThreeDist.card = 6 * repsThree.card := by
    have heq : ThreeDist = ((Finset.univ : Finset (Fin 6)) ×ˢ repsThree).image
        (fun p => perm6 p.1 p.2) := by
      ext ⟨x, y, z⟩
      simp only [ThreeDist, Finset.mem_filter, mem_PosVec, Finset.mem_image, Finset.mem_product,
        Finset.mem_univ, true_and, repsThree, repsFinset]
      constructor
      · rintro ⟨⟨hx, hy, hz, hsq⟩, hxy, hyz, hxz⟩
        rcases lt_or_gt_of_ne hxy with h12 | h21
        · rcases lt_or_gt_of_ne hyz with h23 | h32
          · refine ⟨(0, (x, y, z)), ⟨⟨⟨hx, hy, hz, hsq⟩, le_of_lt h12, le_of_lt h23⟩, h12, h23⟩, rfl⟩
          · rcases lt_or_gt_of_ne hxz with h13 | h31
            · refine ⟨(1, (x, z, y)), ⟨⟨⟨hx, hz, hy, by linarith⟩, le_of_lt h13, le_of_lt h32⟩, h13, h32⟩, rfl⟩
            · refine ⟨(3, (z, x, y)), ⟨⟨⟨hz, hx, hy, by linarith⟩, le_of_lt h31, le_of_lt h12⟩, h31, h12⟩, rfl⟩
        · rcases lt_or_gt_of_ne hxz with h13 | h31
          · refine ⟨(2, (y, x, z)), ⟨⟨⟨hy, hx, hz, by linarith⟩, le_of_lt h21, le_of_lt h13⟩, h21, h13⟩, rfl⟩
          · rcases lt_or_gt_of_ne hyz with h23 | h32
            · refine ⟨(4, (y, z, x)), ⟨⟨⟨hy, hz, hx, by linarith⟩, le_of_lt h23, le_of_lt h31⟩, h23, h31⟩, rfl⟩
            · refine ⟨(5, (z, y, x)), ⟨⟨⟨hz, hy, hx, by linarith⟩, le_of_lt h32, le_of_lt h21⟩, h32, h21⟩, rfl⟩
      · rintro ⟨⟨i, ⟨a, b, c⟩⟩, ⟨⟨⟨ha, hb, hc, hsq⟩, _, _⟩, hab, hbc⟩, heq⟩
        try dsimp only at ha hb hc hsq hab hbc heq
        change 0 < a at ha; change 0 < b at hb; change 0 < c at hc
        change a ^ 2 + b ^ 2 + c ^ 2 = 3 ^ (2 * k) at hsq
        change a < b at hab; change b < c at hbc
        change perm6 i (a, b, c) = (x, y, z) at heq
        fin_cases i <;> simp only [perm6, Prod.mk.injEq] at heq <;>
          obtain ⟨rfl, rfl, rfl⟩ := heq <;> refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> omega
    have hinj : Set.InjOn (fun p : Fin 6 × (ℕ × ℕ × ℕ) => perm6 p.1 p.2)
        (((Finset.univ : Finset (Fin 6)) ×ˢ repsThree : Finset (Fin 6 × (ℕ × ℕ × ℕ))) :
          Set (Fin 6 × (ℕ × ℕ × ℕ))) := by
      rintro ⟨i1, ⟨a1, b1, c1⟩⟩ h1 ⟨i2, ⟨a2, b2, c2⟩⟩ h2 heq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and,
        repsThree, Finset.mem_filter] at h1 h2
      obtain ⟨_, ha1, hb1⟩ := h1
      obtain ⟨_, ha2, hb2⟩ := h2
      fin_cases i1 <;> fin_cases i2 <;>
        simp only [perm6, Prod.mk.injEq] at heq <;>
        first | (obtain ⟨rfl, rfl, rfl⟩ := heq; rfl) | (exfalso; omega)
    rw [heq, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_fin]
  have hpos_card := PosVec_card k
  omega

theorem main_proof : ∀ n : ℕ,
    (OMA.S_oeis_a047926.reps (3 ^ (2 * (n + 1)))).ncard = OMA.S_oeis_a047926.a n := by
  intro n
  rw [← coe_repsFinset (n + 1), Set.ncard_coe_finset]
  have hrel := repsFinset_card_rel (n + 1)
  have hpow : 3 ^ (n + 1 + 1) = 3 * 3 ^ (n + 1) := by rw [pow_succ']
  rw [hpow] at hrel
  have hmul4 : 4 * (repsFinset (n + 1)).card = 3 ^ (n + 1) + 2 * n + 1 := by omega
  unfold OMA.S_oeis_a047926.a
  omega

end A047926Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a047926.main := A047926Proof.main_proof
